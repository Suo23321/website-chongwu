/* =====================================================
   爪小爱服务平台 - 主服务器
   Node.js + Express + SQLite
   ===================================================== */
require('dotenv').config();

const express = require('express');
const path    = require('path');
const fs      = require('fs');
const crypto  = require('crypto');
const bcrypt  = require('bcryptjs');
const jwt     = require('jsonwebtoken');
const initDB  = require('./database/init');
const { localAvatar, AVATAR_COUNT } = initDB;

/* ========== 公共安全/校验工具 ========== */
const PHONE_RE = /^1[3-9]\d{9}$/;                 // 中国大陆手机号
const NAME_RE  = /^[\u4e00-\u9fa5A-Za-z0-9·\-_ ]{2,20}$/; // 2-20 位中英文数字
const PWD_RE   = /^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)[A-Za-z\d@#$%^&*!?._-]{8,32}$/; // 8-32 位，同时含大写+小写+数字

function sanitizeText(s, max = 200) {
  if (typeof s !== 'string') return '';
  // 去除 < > 避免基础 XSS，限制长度
  return s.replace(/[<>]/g, '').slice(0, max).trim();
}
function maskPhone(p) {
  if (!p) return '';
  if (p.indexOf('*') >= 0) return p;  // 已掩码，直接返回
  return String(p).replace(/(\d{3})\d{4}(\d{4})/, '$1****$2');
}
/* 简易登记型防刷：同 IP 注册 >10次/10min 则拒 */
const regBuckets = new Map(); // ip -> [timestamps...]
function registerRateOk(ip) {
  const now = Date.now();
  const WIN = 10 * 60 * 1000;
  const arr = (regBuckets.get(ip) || []).filter(t => now - t < WIN);
  if (arr.length >= 10) return false;
  arr.push(now);
  regBuckets.set(ip, arr);
  return true;
}
function userOut(u) {
  if (!u) return u;
  const { password, id_card_masked, vaccine_img, ...rest } = u;
  // 敏感图片/实名数据不返回给非管理员，前端只能看到是否已提交
  return {
    ...rest,
    phone: maskPhone(u.phone),
    has_id_card: !!id_card_masked,
    has_vaccine: !!vaccine_img,
  };
}

/* 校验 data URI 图片：只允许 jpeg/png/webp，限制单张体积 */
const DATA_IMG_RE = /^data:image\/(jpeg|jpg|png|webp);base64,([A-Za-z0-9+/=]+)$/;
function validImage(s, maxBytes = 1_500_000) {
  if (typeof s !== 'string' || !s) return '';
  const m = s.match(DATA_IMG_RE);
  if (!m) return '';
  // base64 膨胀系数约 4/3
  const rawSize = Math.floor(m[2].length * 3 / 4);
  if (rawSize > maxBytes) return '';
  return s;
}
/* 身份证号真实校验（GB 11643-1999）
   1) 长度 18，前 17 位数字，末位数字或 X
   2) 省级行政区代码合法
   3) 出生日期合法（1900-01-01 到今天）
   4) 第 18 位校验码匹配（加权模 11）
*/
const ID_PROVINCE_CODES = new Set([
  '11','12','13','14','15','21','22','23','31','32','33','34','35','36','37',
  '41','42','43','44','45','46','50','51','52','53','54','61','62','63','64','65','71','81','82','91'
]);
function validateIdCard(id) {
  const s = String(id || '').trim().toUpperCase();
  if (!/^\d{17}[\dX]$/.test(s))               return { ok:false, msg:'身份证号必须是 18 位（末位可为 X）' };
  if (!ID_PROVINCE_CODES.has(s.slice(0, 2))) return { ok:false, msg:'身份证号省份代码不正确' };
  const y = +s.slice(6, 10), m = +s.slice(10, 12), d = +s.slice(12, 14);
  const birth = new Date(y, m - 1, d);
  const now   = new Date();
  if (birth.getFullYear() !== y || birth.getMonth() !== m - 1 || birth.getDate() !== d) {
    return { ok:false, msg:'身份证号出生日期不合法' };
  }
  if (y < 1900 || birth > now) return { ok:false, msg:'身份证号出生日期超出范围' };
  const W = [7,9,10,5,8,4,2,1,6,3,7,9,10,5,8,4,2];
  const CODE = '10X98765432';
  let sum = 0;
  for (let i = 0; i < 17; i++) sum += (+s[i]) * W[i];
  if (CODE[sum % 11] !== s[17]) return { ok:false, msg:'身份证号校验码不正确（第 18 位）' };
  return { ok:true, id:s };
}

/* 身份证号：只存后 4 位掩码（合规：不留明文，仅作提示"已实名") */
function maskIdCard(id) {
  const r = validateIdCard(id);
  if (!r.ok) return '';
  return r.id.slice(0, 4) + '**********' + r.id.slice(-4);
}
/* 协议文档加载：启动时扫描 public/legal/，读取 meta + 计算 SHA-256 */
const AGREEMENTS = {};  // { key: { version, title, path, sha256 } }
function loadAgreements() {
  const dir = path.join(__dirname, 'public', 'legal');
  if (!fs.existsSync(dir)) { console.warn('⚠️  协议目录不存在:', dir); return; }
  for (const file of fs.readdirSync(dir)) {
    if (!file.endsWith('.html')) continue;
    const full = path.join(dir, file);
    const content = fs.readFileSync(full, 'utf8');
    const keyM  = content.match(/<meta\s+name="agreement-key"\s+content="([^"]+)"/);
    const verM  = content.match(/<meta\s+name="agreement-version"\s+content="([^"]+)"/);
    const titM  = content.match(/<meta\s+name="agreement-title"\s+content="([^"]+)"/);
    if (!keyM || !verM) continue;
    const sha = crypto.createHash('sha256').update(content).digest('hex');
    AGREEMENTS[keyM[1]] = { key: keyM[1], version: verM[1], title: titM ? titM[1] : keyM[1], path: file, sha256: sha };
  }
  console.log(`📜 已加载 ${Object.keys(AGREEMENTS).length} 份协议:`,
    Object.values(AGREEMENTS).map(a => `${a.key}@${a.version}`).join(', '));
}
loadAgreements();

/* 性格/急救/驾驭品种 这种数组字段的白名单清洗 */
function sanitizeArray(arr, maxItems = 10, maxLen = 20) {
  if (!Array.isArray(arr)) return [];
  return arr.map(s => sanitizeText(s, maxLen)).filter(Boolean).slice(0, maxItems);
}

const app  = express();
const db   = initDB();
const PORT = process.env.PORT || 3000;
const ALLOW_MOCK_PAYMENTS = process.env.NODE_ENV !== 'production' || process.env.ALLOW_MOCK_PAYMENTS === '1';
const JWT_SECRET  = process.env.JWT_SECRET  || 'pawcare_dev_secret';
const ADMIN_PATH  = process.env.ADMIN_PATH  || 'pawcare-admin-2026'; // 隐藏路径
const OPEN_CITIES = ['北京', '上海', '深圳', '广州', '杭州'];
const OPEN_CITY_SET = new Set(OPEN_CITIES);

/* ── 中间件 ──
   用户可能上传身份证/疫苗证/环境照片（data URI），所以放宽到 12MB
   单张图片前端会压缩到 <1.5MB，6 张仍在余量内 */
app.use(express.json({ limit: '12mb' }));
app.use(express.urlencoded({ extended: true, limit: '12mb' }));

/* ── 前台静态文件 ──
   同时服务根目录 和 public/（public 优先命中，作为兼容旧路径）*/
const BLOCKED_STATIC_PATHS = [
  /^\/(?:admin|database|data|node_modules)(?:\/|$)/i,
  /^\/(?:server\.js|package(?:-lock)?\.json)$/i,
  /^\/\.(?:env|git|claude)(?:\/|$|[.\w-]*)/i,
];
app.use((req, res, next) => {
  if (BLOCKED_STATIC_PATHS.some(re => re.test(req.path))) {
    return res.status(404).send('Not found');
  }
  next();
});
app.use(express.static(path.join(__dirname, 'public'), { dotfiles: 'deny' }));

/* ── 角色定义 ──
   super    超级管理员（技术/IT）  ：全部权限
   operator 运营/审核员            ：服务者审核、订单、用户管理、内容编辑
   finance  财务管理员（老板）     ：财务报表 + 账号管理，不看运营详情
*/
const ROLE_NAMES = { super:'超级管理员', operator:'运营审核员', finance:'财务管理员' };

/* 权限矩阵：每个 scope 允许哪些角色 */
const PERMISSIONS = {
  any:      ['super','operator','finance'],  // 任何已登录角色
  operate:  ['super','operator'],            // 日常运营（服务者/预约/用户）
  content:  ['super','operator'],            // 内容编辑（服务配置/帮助/评价）
  finance:  ['super','finance'],             // 财务数据（finance 老板专属）
  accounts: ['super','finance'],             // 账号管理（老板管员工账号）
  'sitters:manage':   ['super','operator'],
  'kyc:review':       ['super','operator'],
  'orders:manage':    ['super','operator'],
  'users:manage':     ['super','operator'],
  'services:manage':  ['super','operator'],
  'reviews:moderate': ['super','operator'],
  'help:manage':      ['super','operator'],
  'finance:read':     ['super','finance'],
  'accounts:manage':  ['super','finance'],
  'messages:receive': ['super','operator','finance'],
  'messages:manage':  ['super','finance'],
};

const ADMIN_SCOPE_OPTIONS = {
  'sitters:manage':   { label: '服务者管理', group: 'operations' },
  'kyc:review':       { label: 'KYC 审核', group: 'operations' },
  'orders:manage':    { label: '订单/售后', group: 'support' },
  'users:manage':     { label: '用户管理', group: 'support' },
  'services:manage':  { label: '服务配置', group: 'content' },
  'reviews:moderate': { label: '评价内容', group: 'content' },
  'help:manage':      { label: '帮助中心', group: 'content' },
  'finance:read':     { label: '财务只读', group: 'finance' },
  'accounts:manage':  { label: '账号管理', group: 'system' },
  'messages:receive': { label: '消息接收', group: 'message' },
  'messages:manage':  { label: '消息配置', group: 'message' },
};
const ADMIN_NOTIFY_CHANNELS = {
  dingtalk: '钉钉',
  wecom: '企业微信',
  sms: '短信',
  email: '邮箱',
};
const ROLE_DEFAULT_SCOPES = {
  super: ['*'],
  finance: ['finance:read','accounts:manage','messages:receive'],
  operator: ['sitters:manage','kyc:review','orders:manage','users:manage','services:manage','reviews:moderate','help:manage','messages:receive'],
};

/* 解析 Token 基础中间件 */
function authenticate(req, res, next) {
  const auth = req.headers['authorization'] || '';
  const token = auth.startsWith('Bearer ') ? auth.slice(7) : null;
  if (!token) return res.status(401).json({ error: '未登录，请先登录管理后台' });
  try {
    req.admin = jwt.verify(token, JWT_SECRET);
    const currentAdmin = db.prepare('SELECT * FROM admins WHERE id=?').get(req.admin.id);
    if (!currentAdmin) return res.status(401).json({ error: '账号不存在，请重新登录' });
    if ((currentAdmin.status || 'active') !== 'active') {
      return res.status(403).json({ error: '账号已停用，请联系超级管理员' });
    }
    const profile = adminOut(currentAdmin);
    req.admin = {
      ...req.admin,
      role: profile.role,
      username: profile.username,
      scopes: profile.scopes,
      status: profile.status,
    };
    next();
  } catch {
    return res.status(401).json({ error: 'Token 已过期，请重新登录' });
  }
}

/* 权限校验工厂：requirePerm('operate') */
function requirePerm(scope) {
  return (req, res, next) => {
    authenticate(req, res, () => {
      const role = req.admin.role || 'admin';
      if (!(PERMISSIONS[scope] || []).includes(role)) {
        const roleName = ROLE_NAMES[role] || role;
        return res.status(403).json({ error: `[${roleName}] 无此操作权限` });
      }
      if (scope.includes(':')) {
        const scopes = Array.isArray(req.admin.scopes) ? req.admin.scopes : adminScopesForRole(role);
        if (!scopes.includes('*') && !scopes.includes(scope)) {
          return res.status(403).json({ error: `缺少细分权限：${ADMIN_SCOPE_OPTIONS[scope]?.label || scope}` });
        }
      }
      next();
    });
  };
}

/* 兼容旧代码的别名 */
const requireAdmin    = requirePerm('operate');   // 运营操作
const requireAnyRole  = requirePerm('any');       // 任意登录

/* ── JSON 字段解析帮助 ── */
function parseJSON(str, fallback = []) {
  try { return JSON.parse(str); } catch { return fallback; }
}
function sitterOut(s) {
  return {
    ...s,
    services: parseJSON(s.services),
    pets:     parseJSON(s.pets),
    photos:   parseJSON(s.photos),
    verified: !!s.verified,
    background_check: !!s.background_check,
    available: !!s.available,
  };
}
function svcOut(s) {
  return { ...s, features: parseJSON(s.features) };
}
function sanitizeAdminList(values, allowed, fallback = []) {
  if (!Array.isArray(values)) return fallback;
  const ok = new Set(allowed);
  return [...new Set(values.map(v => String(v || '').trim()).filter(v => v === '*' || ok.has(v)))];
}
function adminScopesForRole(role) {
  return ROLE_DEFAULT_SCOPES[role] || ROLE_DEFAULT_SCOPES.operator;
}
function adminOut(a) {
  const role = a.role || 'operator';
  return {
    id: a.id,
    username: a.username,
    display_name: a.display_name || '',
    department: a.department || '',
    role,
    scopes: parseJSON(a.scopes, adminScopesForRole(role)),
    notify_channels: parseJSON(a.notify_channels, []),
    status: a.status || 'active',
    created_at: a.created_at,
  };
}

/* =========================================================
   公开 API（前台使用，不需要登录）
   ========================================================= */

/* 获取服务者列表 */
app.get('/api/sitters', (req, res) => {
  const { city, district, service, pet, minPrice, maxPrice, minRating, verified, available } = req.query;
  if (city && !OPEN_CITY_SET.has(city)) {
    return res.json({ data: [], total: 0 });
  }
  let sql = 'SELECT * FROM sitters WHERE 1=1';
  const params = [];
  if (city)      { sql += ' AND city=?';           params.push(city); }
  else           { sql += ` AND city IN (${OPEN_CITIES.map(() => '?').join(',')})`; params.push(...OPEN_CITIES); }
  if (district)  { sql += ' AND district=?';       params.push(district); }
  if (minPrice)  { sql += ' AND price>=?';          params.push(+minPrice); }
  if (maxPrice)  { sql += ' AND price<=?';          params.push(+maxPrice); }
  if (minRating) { sql += ' AND rating>=?';         params.push(+minRating); }
  if (verified === '1') { sql += ' AND verified=1'; }
  if (available === '1') { sql += ' AND available=1'; }
  sql += ' ORDER BY rating DESC, review_count DESC';

  let rows = db.prepare(sql).all(...params).map(sitterOut);

  // 服务和宠物类型过滤（JSON字段，用 JS 过滤）
  if (service) rows = rows.filter(s => s.services.some(sv => sv.includes(service)));
  if (pet)     rows = rows.filter(s => s.pets.some(p => p.includes(pet)));

  res.json({ data: rows, total: rows.length });
});

/* 获取单个服务者 */
app.get('/api/sitters/:id', (req, res) => {
  const row = db.prepare('SELECT * FROM sitters WHERE id=?').get(req.params.id);
  if (!row) return res.status(404).json({ error: '服务者不存在' });
  if (row.city && !OPEN_CITY_SET.has(row.city)) return res.status(404).json({ error: '服务城市暂未开通' });
  // 附带该服务者的评价
  const reviews = db.prepare('SELECT * FROM reviews WHERE sitter_id=? ORDER BY id DESC').all(row.id);
  res.json({ data: { ...sitterOut(row), reviews } });
});

/* 服务者接单日历：未来 60 天哪些日期被占用 */
app.get('/api/sitters/:id/calendar', (req, res) => {
  const sid = +req.params.id;
  // 只看待确认/进行中/已完成的订单（已取消的不占用档期）
  const bookings = db.prepare(`
    SELECT start_date, end_date, status, owner_name, service_type
    FROM bookings
    WHERE sitter_id=? AND status IN ('待确认','进行中','已完成')
      AND start_date IS NOT NULL AND start_date != ''
  `).all(sid);

  // 展开日期范围
  const busyDays = {};
  const today = new Date(); today.setHours(0,0,0,0);
  const horizon = new Date(today); horizon.setDate(horizon.getDate() + 60);
  const pastLimit = new Date(today); pastLimit.setDate(pastLimit.getDate() - 30);

  bookings.forEach(b => {
    const start = new Date(b.start_date);
    const end = b.end_date ? new Date(b.end_date) : new Date(start);
    if (isNaN(start) || isNaN(end)) return;
    for (let d = new Date(start); d <= end; d.setDate(d.getDate()+1)) {
      if (d < pastLimit || d > horizon) continue;
      const key = d.toISOString().slice(0,10);
      if (!busyDays[key]) busyDays[key] = { count: 0, status: b.status };
      busyDays[key].count++;
      // 优先级：进行中 > 待确认 > 已完成
      const prio = { '进行中':3, '待确认':2, '已完成':1 };
      if ((prio[b.status]||0) > (prio[busyDays[key].status]||0)) busyDays[key].status = b.status;
    }
  });

  res.json({ data: { busyDays } });
});

/* 获取服务项目 */
app.get('/api/services', (req, res) => {
  const rows = db.prepare('SELECT * FROM services ORDER BY sort_order').all().map(svcOut);
  res.json({ data: rows });
});

/* 获取首页评价 */
app.get('/api/reviews', (req, res) => {
  const rows = db.prepare('SELECT * FROM reviews ORDER BY id DESC LIMIT 8').all();
  res.json({ data: rows });
});

/* 首页亮点：热门服务者 + 本周推荐 */
app.get('/api/highlights', (req, res) => {
  // 热门：按评价数排序（接单最多）
  const hot = db.prepare(`
    SELECT * FROM sitters
    WHERE available=1 AND verified=1 AND city IN (${OPEN_CITIES.map(() => '?').join(',')})
    ORDER BY review_count DESC, rating DESC
    LIMIT 4
  `).all(...OPEN_CITIES).map(sitterOut);

  // 本周推荐：高评分 + 有一定评价量，随机抽取，突出"精选"感
  const weekly = db.prepare(`
    SELECT * FROM sitters
    WHERE available=1 AND verified=1 AND rating >= 4.7 AND review_count >= 3 AND city IN (${OPEN_CITIES.map(() => '?').join(',')})
    ORDER BY (rating * 20 + review_count) DESC
    LIMIT 8
  `).all(...OPEN_CITIES).map(sitterOut);
  // 从前 8 名随机挑 3 位（每次刷新略有变化，营造"本周精选"感觉）
  const picks = weekly.sort(() => Math.random() - 0.5).slice(0, 3);

  res.json({ data: { hot, weekly: picks } });
});

/* 提交预约 */
app.post('/api/bookings', (req, res) => {
  const { sitter_id, sitter_name, sitter_avatar, owner_name, owner_phone,
          pet_name, breed, start_date, end_date, service_type, note, price } = req.body;
  if (!owner_name || !owner_phone || !start_date) {
    return res.status(400).json({ error: '请填写姓名、电话和开始日期' });
  }
  const result = db.prepare(`
    INSERT INTO bookings (sitter_id,sitter_name,sitter_avatar,owner_name,owner_phone,
      pet_name,breed,start_date,end_date,service_type,note,price)
    VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
  `).run(sitter_id||0, sitter_name||'', sitter_avatar||'', owner_name, owner_phone,
         pet_name||'', breed||'', start_date, end_date||'', service_type||'', note||'', price||0);
  res.json({ success: true, id: result.lastInsertRowid, message: '预约成功！服务者将在1小时内联系您 🎉' });
});

/* 注册用户（严格校验 + 密码哈希 + 头像索引 + 验证码 + 去重 + 频率限制）
   - 宠物主人：填写宠物信息 + 地址
   - 宠物服务者：同步在 sitters 表创建待审核档案
*/
app.post('/api/users/register', (req, res) => {
  const ip = req.ip || req.headers['x-forwarded-for'] || 'unknown';
  if (!registerRateOk(ip)) {
    return res.status(429).json({ error: '注册过于频繁，请稍后再试' });
  }

  let {
    name, phone, password, confirm_password, type, role,
    avatar_idx, avatar_upload,                          // 头像：图库索引 或 自定义上传
    captcha_a, captcha_b, captcha_answer, agree, agree_liability, // 多份协议
    id_card,                                            // 身份证号（只存掩码）
    // 主人扩展
    pet_name, pet_type, pet_breed, pet_age, pet_gender,
    address, vaccine_img, personality, vet_hospital, vet_phone,
    emergency_contact_name, emergency_contact_phone, medical_auth, medical_auth_limit, medical_auth_note,
    // 看护人扩展
    city, district, area_detail, services, years_experience, bio,
    env_photos, first_aid, insurance, zhima_score, breeds_handled
  } = req.body || {};

  // ============ 1) 基础校验 ============
  name     = sanitizeText(name, 20);
  phone    = String(phone || '').trim();
  password = String(password || '');
  confirm_password = String(confirm_password || '');
  // 兼容前端 role: 'owner'|'sitter' 与后端枚举
  const isSitter = (role === 'sitter') || (type === '宠物服务者');
  type     = isSitter ? '宠物服务者' : '宠物主人';
  avatar_idx = Math.max(0, Math.min(AVATAR_COUNT - 1, parseInt(avatar_idx, 10) || 0));
  // 头像：优先用户上传，其次图库；上传必须是合法 data URI 图片 ≤1.5MB
  const uploadedAvatar = validImage(avatar_upload, 1_500_000);
  const finalAvatar    = uploadedAvatar || localAvatar(avatar_idx);

  if (!name)                         return res.status(400).json({ error: '请填写姓名' });
  if (!NAME_RE.test(name))           return res.status(400).json({ error: '姓名仅支持中英文/数字，2–20 位' });
  if (!PHONE_RE.test(phone))         return res.status(400).json({ error: '请输入有效的 11 位手机号（1 开头）' });
  if (!PWD_RE.test(password))        return res.status(400).json({ error: '密码 8–32 位，须同时包含大写字母、小写字母和数字' });
  if (password !== confirm_password) return res.status(400).json({ error: '两次输入的密码不一致' });
  if (!agree)                        return res.status(400).json({ error: '请先阅读并同意《服务协议》与《隐私政策》' });

  // ============ 2) 人机验证 ============
  const a = parseInt(captcha_a, 10);
  const b = parseInt(captcha_b, 10);
  const answer = parseInt(captcha_answer, 10);
  if (!Number.isFinite(a) || !Number.isFinite(b) || !Number.isFinite(answer) || a + b !== answer) {
    return res.status(400).json({ error: '人机验证失败，请重新计算' });
  }

  // ============ 3) 角色专属字段校验 ============
  // 身份证号真实校验（加权校验码 + 省份 + 出生日期）
  //   宠物主人：选填；填写的须合法（首单前补齐即可）
  //   宠物服务者：必填；且必须合法（送 KYC 人工审核）
  let idCardMasked = '';
  if (type === '宠物服务者') {
    if (!id_card) return res.status(400).json({ error: '宠物服务者必须填写身份证号（用于 KYC 实名认证）' });
    const r = validateIdCard(id_card);
    if (!r.ok)    return res.status(400).json({ error: r.msg });
    idCardMasked  = maskIdCard(r.id);
  } else if (id_card) {
    const r = validateIdCard(id_card);
    if (!r.ok)    return res.status(400).json({ error: r.msg });
    idCardMasked  = maskIdCard(r.id);
  }

  if (type === '宠物主人') {
    pet_name    = sanitizeText(pet_name, 20);
    pet_type    = sanitizeText(pet_type, 20);
    pet_breed   = sanitizeText(pet_breed, 30);
    pet_age     = sanitizeText(pet_age, 10);
    pet_gender  = sanitizeText(pet_gender, 4);
    address     = sanitizeText(address, 100);
    vet_hospital= sanitizeText(vet_hospital, 60);
    vet_phone   = sanitizeText(vet_phone, 20);
    emergency_contact_name  = sanitizeText(emergency_contact_name, 20);
    emergency_contact_phone = sanitizeText(emergency_contact_phone, 20);
    medical_auth            = medical_auth ? 1 : 0;
    medical_auth_limit      = Math.max(0, Math.min(50000, parseInt(medical_auth_limit, 10) || 0));
    medical_auth_note       = sanitizeText(medical_auth_note, 60);
    personality = sanitizeArray(personality, 8, 10);
    vaccine_img = validImage(vaccine_img, 1_500_000);
    if (!pet_name || !pet_type) return res.status(400).json({ error: '请填写宠物名称和类型' });
    if (!address)               return res.status(400).json({ error: '请填写联系地址（至少城市+区县）' });
    if (!medical_auth)          return res.status(400).json({ error: '请先确认紧急医疗授权' });
  } else {
    city             = sanitizeText(city, 20);
    bio              = sanitizeText(bio, 500);
    insurance        = sanitizeText(insurance, 30);
    services         = sanitizeArray(services, 10, 20);
    first_aid        = sanitizeArray(first_aid, 8, 20);
    breeds_handled   = sanitizeArray(breeds_handled, 10, 20);
    years_experience = Math.max(0, Math.min(50, parseInt(years_experience, 10) || 0));
    zhima_score      = Math.max(0, Math.min(950, parseInt(zhima_score, 10) || 0));
    // 环境照最多 6 张，每张 1.5MB 以内
    env_photos = Array.isArray(env_photos)
      ? env_photos.map(p => validImage(p, 1_500_000)).filter(Boolean).slice(0, 6)
      : [];
    if (!city)                   return res.status(400).json({ error: '请选择所在城市' });
    if (!OPEN_CITY_SET.has(city)) return res.status(400).json({ error: '该城市暂未开通，目前仅支持北京、上海、深圳、广州、杭州' });
    if (services.length === 0)   return res.status(400).json({ error: '请至少勾选一项提供的服务' });
    if (!bio || bio.length < 10) return res.status(400).json({ error: '自我介绍至少 10 个字，方便客户了解您' });
    // 看护人法律协议：3 份协议必须全部签署
    const REQUIRED_AGREEMENTS = ['sitter_commitment', 'sitter_truthfulness', 'sitter_welfare'];
    const signed = Array.isArray(req.body.signed_agreements) ? req.body.signed_agreements : [];
    const missing = REQUIRED_AGREEMENTS.filter(k => !signed.includes(k));
    if (missing.length > 0) {
      const titles = missing.map(k => (AGREEMENTS[k] ? AGREEMENTS[k].title : k));
      return res.status(400).json({ error: `请先签署：《${titles.join('》、《')}》` });
    }
    // 协议文件必须已被服务器加载（避免前端声称签署但后端找不到对应文档）
    const notLoaded = REQUIRED_AGREEMENTS.filter(k => !AGREEMENTS[k]);
    if (notLoaded.length > 0) {
      return res.status(500).json({ error: '平台协议文档缺失，请联系管理员：' + notLoaded.join(',') });
    }
  }

  // ============ 4) 手机号去重 ============
  const masked = maskPhone(phone);
  const exists = db.prepare('SELECT id FROM users WHERE phone=? OR phone=?').get(phone, masked);
  if (exists) return res.status(409).json({ error: '该手机号已注册，请直接登录' });

  // ============ 5) 写库 ============
  const hash   = bcrypt.hashSync(password, 10);
  const avatar = finalAvatar;
  // KYC 状态机：
  //   宠物主人 → 若提交了身份证即 verified，否则 basic（自助流程，首单前补齐）
  //   宠物看护人 → 强制 pending（运营人工审核，驳回/补材料/通过）
  const kycStatus = isSitter
    ? 'pending'
    : (idCardMasked ? 'verified' : 'basic');

  // node:sqlite 不支持 db.transaction()，改用显式 BEGIN / COMMIT / ROLLBACK
  let newId;
  db.exec('BEGIN');
  try {
    const u = db.prepare(`
      INSERT INTO users
        (name,phone,password,type,avatar,status,
         pet_name,pet_type,pet_breed,address,
         pet_age,pet_gender,vaccine_img,personality,vet_hospital,vet_phone,
         emergency_contact_name,emergency_contact_phone,medical_auth,medical_auth_limit,medical_auth_note,
         id_card_masked,kyc_status)
      VALUES (?,?,?,?,?,?, ?,?,?,?, ?,?,?,?,?,?, ?,?,?,?,?, ?,?)
    `).run(
      name, phone, hash, type, avatar, '正常',
      type === '宠物主人' ? pet_name  : '',
      type === '宠物主人' ? pet_type  : '',
      type === '宠物主人' ? pet_breed : '',
      type === '宠物主人' ? address   : '',
      type === '宠物主人' ? (pet_age || '')    : '',
      type === '宠物主人' ? (pet_gender || '') : '',
      type === '宠物主人' ? (vaccine_img || '') : '',
      type === '宠物主人' ? JSON.stringify(personality || []) : '[]',
      type === '宠物主人' ? (vet_hospital || '') : '',
      type === '宠物主人' ? (vet_phone || '')   : '',
      type === '宠物主人' ? (emergency_contact_name || '')  : '',
      type === '宠物主人' ? (emergency_contact_phone || '') : '',
      type === '宠物主人' ? (medical_auth || 0)             : 0,
      type === '宠物主人' ? (medical_auth_limit || 0)       : 0,
      type === '宠物主人' ? (medical_auth_note || '')       : '',
      idCardMasked,
      kycStatus
    );

    newId = u.lastInsertRowid;

    // 服务者额外在 sitters 创建待审核档案 + 写入 kyc_applications 审批轨迹
    if (type === '宠物服务者') {
      // 拼装展示用 location 字符串：city·district·area_detail（按存在的部分拼接）
      const locParts = [city, district, area_detail].map(s => sanitizeText(s||'', 40)).filter(Boolean);
      const locationStr = locParts.length ? locParts.join('·') : (city ? city+'市' : '');
      db.prepare(`
        INSERT INTO sitters
          (name,avatar,location,city,district,area_detail,services,bio,years_experience,status,verified,available,
           env_photos,first_aid,insurance,zhima_score,breeds_handled,id_card_masked)
        VALUES (?,?,?,?,?,?,?,?,?,?,?,?, ?,?,?,?,?,?)
      `).run(
        name, avatar, locationStr, city||'', sanitizeText(district||'', 40), sanitizeText(area_detail||'', 80),
        JSON.stringify(services), bio, years_experience, '待审核', 0, 0,
        JSON.stringify(env_photos || []),
        JSON.stringify(first_aid  || []),
        insurance || '',
        zhima_score || 0,
        JSON.stringify(breeds_handled || []),
        idCardMasked
      );

      // 提交时间戳 + KYC 申请单（运营后台审核入口）
      db.prepare("UPDATE users SET kyc_submitted_at=datetime('now','localtime') WHERE id=?").run(newId);
      const snapshot = {
        city, district, area_detail, services, bio, years_experience, insurance, zhima_score,
        breeds_handled, first_aid, env_photos_count: (env_photos || []).length,
        has_id_card: !!idCardMasked
      };
      const appRes = db.prepare(`
        INSERT INTO kyc_applications (user_id, role, status, snapshot, created_at)
        VALUES (?, 'sitter', 'pending', ?, datetime('now','localtime'))
      `).run(newId, JSON.stringify(snapshot));
      db.prepare(`
        INSERT INTO kyc_review_log (application_id, user_id, actor_id, actor_name, action, old_status, new_status)
        VALUES (?, ?, 0, 'system', 'submitted', '', 'pending')
      `).run(appRes.lastInsertRowid, newId);

      // 记录协议签署日志（含 IP/UA/SHA-256，依据《电子签名法》第 14 条）
      signAgreementsForUser(newId, ['sitter_commitment', 'sitter_truthfulness', 'sitter_welfare'], req);
    }

    db.exec('COMMIT');
  } catch (err) {
    try { db.exec('ROLLBACK'); } catch (_) {}
    console.error('register tx failed:', err);
    return res.status(500).json({ error: '注册失败，请稍后重试' });
  }

  res.json({
    success: true,
    id: newId,
    kyc_status: kycStatus,
    message: type === '宠物服务者'
      ? '资料已提交，等待平台审核（一般 24 小时内出结果）📝'
      : '注册成功！欢迎加入爪小爱 🎉',
    user: { id: newId, name, phone: masked, type, avatar, kyc_status: kycStatus }
  });
});

/* ========== 前台用户 Token 工具（区别于 admin 的 JWT） ========== */
function issueUserToken(u) {
  return jwt.sign(
    { uid: u.id, name: u.name, type: u.type },
    JWT_SECRET,
    { expiresIn: '30d' }
  );
}
function userPublic(u) {
  return {
    id: u.id, name: u.name, phone: maskPhone(u.phone), type: u.type, avatar: u.avatar,
    kyc_status: u.kyc_status || 'basic',
    login_type: u.login_type || 'password',
    wx_nickname: u.wx_nickname || '',
    has_wx: !!u.wx_openid,
    has_phone_verified: !!u.phone_verified_at,
  };
}

/* 登录用户（前台，密码方式） */
app.post('/api/users/login', (req, res) => {
  const phone = String(req.body.phone || '').trim();
  const pwd   = String(req.body.password || '');
  if (!PHONE_RE.test(phone)) return res.status(400).json({ error: '请输入有效手机号' });
  const u = db.prepare('SELECT * FROM users WHERE phone=?').get(phone);
  if (!u || !u.password || !bcrypt.compareSync(pwd, u.password)) {
    return res.status(401).json({ error: '手机号或密码错误' });
  }
  if (u.status !== '正常') return res.status(403).json({ error: '账号已被封禁，请联系客服' });
  res.json({
    success: true,
    token: issueUserToken(u),
    user: userPublic(u)
  });
});

/* GET /api/users/me —— 用 token 取当前登录用户（供微信回调等场景使用） */
app.get('/api/users/me', (req, res) => {
  const m = /^Bearer\s+(.+)$/i.exec(req.headers.authorization || '');
  if (!m) return res.status(401).json({ error: '未登录' });
  try {
    const payload = jwt.verify(m[1], JWT_SECRET);
    const u = db.prepare('SELECT * FROM users WHERE id=?').get(payload.uid);
    if (!u) return res.status(401).json({ error: '账号不存在' });
    if (u.status !== '正常') return res.status(403).json({ error: '账号已被封禁' });
    res.json({ user: userPublic(u) });
  } catch (e) {
    return res.status(401).json({ error: 'token 无效或已过期' });
  }
});

/* GET /api/sitter/my-kyc —— 当前登录看护人自己查看 KYC 申请状态 + 审核轨迹 */
app.get('/api/sitter/my-kyc', (req, res) => {
  const m = /^Bearer\s+(.+)$/i.exec(req.headers.authorization || '');
  if (!m) return res.status(401).json({ error: '未登录' });
  let uid;
  try { uid = jwt.verify(m[1], JWT_SECRET).uid; }
  catch (e) { return res.status(401).json({ error: 'token 无效或已过期' }); }

  const u = db.prepare('SELECT * FROM users WHERE id=?').get(uid);
  if (!u) return res.status(404).json({ error: '账号不存在' });
  if (u.type !== 'sitter') return res.status(403).json({ error: '当前账号不是服务者' });

  // 最近一次 KYC 申请
  const app_ = db.prepare(`
    SELECT * FROM kyc_applications WHERE user_id=? ORDER BY id DESC LIMIT 1
  `).get(uid);
  if (!app_) return res.json({ application: null, logs: [], user: userPublic(u), sitter: null });

  // 审核日志（按时间正序）
  const logs = db.prepare(`
    SELECT id, action, old_status, new_status, reason_code, note, actor_name, created_at
    FROM kyc_review_log WHERE application_id=? ORDER BY id ASC
  `).all(app_.id);

  // 关联的 sitter 档案（若已有）
  const sitter = db.prepare('SELECT * FROM sitters WHERE name=? ORDER BY id DESC LIMIT 1').get(u.name);

  // snapshot 解析
  let snapshot = {};
  try { snapshot = JSON.parse(app_.snapshot || '{}'); } catch(e) {}

  res.json({
    user: userPublic(u),
    application: {
      id: app_.id,
      status: app_.status,
      role: app_.role,
      snapshot,
      reviewer_name: app_.reviewer_name,
      reject_code: app_.reject_code,
      reject_note: app_.reject_note,
      needs_more_note: app_.needs_more_note,
      claimed_at: app_.claimed_at,
      decided_at: app_.decided_at,
      created_at: app_.created_at,
    },
    logs,
    sitter: sitter ? { id: sitter.id, verified: !!sitter.verified, available: !!sitter.available, status: sitter.status } : null
  });
});

/* =========================================================
   短信验证码登录（dev 模式：固定 123456；生产：对接阿里云/腾讯云 SMS）
   ========================================================= */

const SMS_DEV_CODE = process.env.SMS_DEV_CODE || '123456';
const SMS_PROVIDER = process.env.SMS_PROVIDER || 'dev'; // dev | aliyun | tencent
const SMS_MAX_PER_DAY = 5;  // 同号码每天最多 5 条

function generateSmsCode() {
  if (SMS_PROVIDER === 'dev') return SMS_DEV_CODE;
  return String(Math.floor(100000 + Math.random() * 900000)); // 6 位数字
}

async function sendSmsViaProvider(phone, code) {
  if (SMS_PROVIDER === 'dev') {
    console.log(`📱 [DEV SMS] ${phone} → 验证码 ${code}（开发模式，固定 ${SMS_DEV_CODE}）`);
    return { ok: true };
  }
  // TODO 对接阿里云 SMS：
  //   const Core = require('@alicloud/pop-core');
  //   const client = new Core({ accessKeyId, accessKeySecret, endpoint, apiVersion });
  //   return client.request('SendSms', { PhoneNumbers: phone, SignName, TemplateCode, TemplateParam: JSON.stringify({code}) });
  console.warn(`⚠️ SMS_PROVIDER=${SMS_PROVIDER} 未实现，退回 dev 模式`);
  return { ok: true };
}

/* POST /api/auth/sms/send  —  下发验证码 */
app.post('/api/auth/sms/send', async (req, res) => {
  const phone = String(req.body.phone || '').trim();
  const scene = ['login','register','bind'].includes(req.body.scene) ? req.body.scene : 'login';
  if (!PHONE_RE.test(phone)) return res.status(400).json({ error: '请输入有效手机号' });

  // 同号码同场景 60 秒内只能发一次
  const recent = db.prepare(`
    SELECT created_at FROM sms_codes WHERE phone=? AND scene=?
    ORDER BY id DESC LIMIT 1
  `).get(phone, scene);
  if (recent) {
    const age = (Date.now() - new Date(recent.created_at.replace(' ','T')).getTime()) / 1000;
    if (age < 60) return res.status(429).json({ error: `请 ${Math.ceil(60 - age)} 秒后再试` });
  }
  // 同号码每天最多 5 条
  const dailyCount = db.prepare(`
    SELECT COUNT(*) as n FROM sms_codes WHERE phone=?
      AND date(created_at)=date('now','localtime')
  `).get(phone).n;
  if (dailyCount >= SMS_MAX_PER_DAY) {
    return res.status(429).json({ error: '当日短信次数已用完，请明天再试' });
  }

  const code = generateSmsCode();
  // 用"本地时间"字符串存入，与 sqlite datetime('now','localtime') 格式一致
  const d = new Date(Date.now() + 5 * 60 * 1000);
  const pad = n => String(n).padStart(2, '0');
  const expiresAt = `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
  db.prepare(`
    INSERT INTO sms_codes (phone, code, scene, expires_at)
    VALUES (?, ?, ?, ?)
  `).run(phone, code, scene, expiresAt);

  try { await sendSmsViaProvider(phone, code); } catch (e) { console.error(e); }

  res.json({
    success: true,
    message: SMS_PROVIDER === 'dev'
      ? `开发模式：验证码已生成（控制台可见，固定 ${SMS_DEV_CODE}）`
      : '验证码已发送，5 分钟内有效'
  });
});

/* POST /api/auth/sms/verify  —  验证码登录/注册（无账号自动创建宠物主人）*/
app.post('/api/auth/sms/verify', (req, res) => {
  const phone = String(req.body.phone || '').trim();
  const code  = String(req.body.code || '').trim();
  if (!PHONE_RE.test(phone)) return res.status(400).json({ error: '请输入有效手机号' });
  if (!/^\d{4,8}$/.test(code)) return res.status(400).json({ error: '验证码格式不正确' });

  // 取最新一条未使用的验证码
  const row = db.prepare(`
    SELECT * FROM sms_codes WHERE phone=? AND used=0
    ORDER BY id DESC LIMIT 1
  `).get(phone);
  if (!row) return res.status(400).json({ error: '验证码已过期或未发送' });
  if (new Date(row.expires_at.replace(' ','T')).getTime() < Date.now()) {
    return res.status(400).json({ error: '验证码已过期，请重新发送' });
  }
  if (row.code !== code) return res.status(400).json({ error: '验证码不正确' });

  // 标记已使用（一次性）
  db.prepare('UPDATE sms_codes SET used=1 WHERE id=?').run(row.id);

  // 查/建用户（无账号自动注册为宠物主人，kyc=basic）
  let u = db.prepare('SELECT * FROM users WHERE phone=?').get(phone);
  let isNew = false;
  if (!u) {
    const defaultName = '用户' + phone.slice(-4);
    const avatar = localAvatar(Math.floor(Math.random() * AVATAR_COUNT));
    const ins = db.prepare(`
      INSERT INTO users (name,phone,password,type,avatar,status,login_type,phone_verified_at,kyc_status)
      VALUES (?, ?, '', '宠物主人', ?, '正常', 'phone_code', datetime('now','localtime'), 'basic')
    `).run(defaultName, phone, avatar);
    u = db.prepare('SELECT * FROM users WHERE id=?').get(ins.lastInsertRowid);
    isNew = true;
  } else {
    db.prepare("UPDATE users SET phone_verified_at=datetime('now','localtime') WHERE id=?").run(u.id);
    u = db.prepare('SELECT * FROM users WHERE id=?').get(u.id);
  }
  if (u.status !== '正常') return res.status(403).json({ error: '账号已被封禁，请联系客服' });

  res.json({
    success: true,
    new_user: isNew,
    token: issueUserToken(u),
    user: userPublic(u),
    message: isNew ? '账号已创建，欢迎加入爪小爱 🐾' : '登录成功，欢迎回来'
  });
});

/* =========================================================
   微信登录（Web 网站应用 OAuth2）
   生产：需微信开放平台 App ID + App Secret
   沙盒：WX_SANDBOX=1 时跳过真微信接口，用前端伪造 openid 直接登录（仅开发联调）
   ========================================================= */

const WX_APP_ID     = process.env.WX_APP_ID     || '';
const WX_APP_SECRET = process.env.WX_APP_SECRET || '';
const WX_REDIRECT   = process.env.WX_REDIRECT_URI || ''; // 必须和微信开放平台配置一致
const WX_SANDBOX    = process.env.WX_SANDBOX === '1';    // 开发模式开关

function randomState() {
  return Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
}

/* GET /api/auth/wx/url  —  前端获取微信扫码登录 URL */
app.get('/api/auth/wx/url', (req, res) => {
  if (WX_SANDBOX) {
    return res.json({
      sandbox: true,
      message: '开发沙盒模式：无需真实微信扫码，请在登录弹窗选择"沙盒测试账号"',
    });
  }
  if (!WX_APP_ID || !WX_REDIRECT) {
    return res.status(503).json({
      error: '微信登录未配置：请在 .env 填写 WX_APP_ID / WX_APP_SECRET / WX_REDIRECT_URI',
    });
  }
  const state = randomState();
  db.prepare('INSERT INTO wx_login_states (state, scene) VALUES (?, ?)').run(state, 'login');
  // 微信开放平台扫码登录 URL
  const url =
    'https://open.weixin.qq.com/connect/qrconnect' +
    '?appid=' + encodeURIComponent(WX_APP_ID) +
    '&redirect_uri=' + encodeURIComponent(WX_REDIRECT) +
    '&response_type=code&scope=snsapi_login' +
    '&state=' + state + '#wechat_redirect';
  res.json({ url, state });
});

/* GET /api/auth/wx/callback  —  微信回调 */
app.get('/api/auth/wx/callback', async (req, res) => {
  const { code, state } = req.query;
  if (!code || !state) return res.status(400).send('参数错误');
  const stateRow = db.prepare('SELECT * FROM wx_login_states WHERE state=?').get(state);
  if (!stateRow || stateRow.used) return res.status(400).send('state 无效或已使用');
  db.prepare('UPDATE wx_login_states SET used=1 WHERE id=?').run(stateRow.id);

  if (!WX_APP_ID || !WX_APP_SECRET) {
    return res.status(503).send('微信登录未配置');
  }
  try {
    // 1) code → access_token + openid + unionid
    const tokenUrl =
      'https://api.weixin.qq.com/sns/oauth2/access_token' +
      '?appid='     + WX_APP_ID +
      '&secret='    + WX_APP_SECRET +
      '&code='      + code +
      '&grant_type=authorization_code';
    const tokenResp = await fetch(tokenUrl).then(r => r.json());
    if (tokenResp.errcode) throw new Error(tokenResp.errmsg || '微信接口错误');
    const { openid, unionid, access_token } = tokenResp;

    // 2) 拉取用户信息（昵称 + 头像）
    const infoUrl =
      'https://api.weixin.qq.com/sns/userinfo' +
      '?access_token=' + access_token + '&openid=' + openid;
    const info = await fetch(infoUrl).then(r => r.json());

    // 3) 查/建本地用户
    let u = db.prepare('SELECT * FROM users WHERE wx_openid=? OR wx_unionid=?').get(openid, unionid || '');
    if (!u) {
      const name = (info.nickname || '微信用户').slice(0, 20);
      const avatar = info.headimgurl || localAvatar(Math.floor(Math.random() * AVATAR_COUNT));
      const ins = db.prepare(`
        INSERT INTO users (name, phone, password, type, avatar, status, login_type, wx_openid, wx_unionid, wx_nickname, wx_avatar, kyc_status)
        VALUES (?, '', '', '宠物主人', ?, '正常', 'wx', ?, ?, ?, ?, 'basic')
      `).run(name, avatar, openid, unionid || '', info.nickname || '', info.headimgurl || '');
      u = db.prepare('SELECT * FROM users WHERE id=?').get(ins.lastInsertRowid);
    }
    const token = issueUserToken(u);

    // 4) 回跳到前端，把 token 作为 hash 传回（避免 referer 泄漏）
    res.redirect(`/index.html#wx_login=${token}`);
  } catch (err) {
    console.error('wx callback error:', err);
    res.status(500).send('微信登录失败，请返回重试');
  }
});

/* POST /api/auth/wx/sandbox  —  开发沙盒：模拟微信登录（仅 WX_SANDBOX=1 可用）*/
app.post('/api/auth/wx/sandbox', (req, res) => {
  if (!WX_SANDBOX) return res.status(403).json({ error: '沙盒模式未开启（WX_SANDBOX=1）' });
  const nickname = sanitizeText(req.body.nickname || '沙盒用户', 20);
  const openid   = 'SANDBOX_' + (req.body.openid || Math.random().toString(36).slice(2, 10));
  let u = db.prepare('SELECT * FROM users WHERE wx_openid=?').get(openid);
  if (!u) {
    const avatar = localAvatar(Math.floor(Math.random() * AVATAR_COUNT));
    const ins = db.prepare(`
      INSERT INTO users (name, phone, password, type, avatar, status, login_type, wx_openid, wx_nickname, kyc_status)
      VALUES (?, '', '', '宠物主人', ?, '正常', 'wx', ?, ?, 'basic')
    `).run(nickname, avatar, openid, nickname);
    u = db.prepare('SELECT * FROM users WHERE id=?').get(ins.lastInsertRowid);
  }
  res.json({ success: true, token: issueUserToken(u), user: userPublic(u) });
});

/* =========================================================
   管理后台：KYC 审批 API
   ========================================================= */

/* 驳回理由枚举（结构化，便于统计 Top 驳回原因） */
const REJECT_REASONS = {
  id_blur:       '身份证照片模糊不清',
  id_mismatch:   '身份证信息与手机号实名不一致',
  insurance_bad: '保险单过期或金额不达标（≥10 万/单）',
  env_photos:    '环境照片不完整或不真实（至少 6 张）',
  bio_short:     '自我介绍少于 50 字或与模板雷同',
  city_not_open: '所在城市暂未开通',
  age_limit:     '不满 18 岁不可注册看护人',
  other:         '其它（见备注）',
};

/* GET /api/admin/kyc/reject-reasons  —  拉枚举，前端生成下拉框 */
app.get('/api/admin/kyc/reject-reasons', requirePerm('kyc:review'), (req, res) => {
  res.json({ data: REJECT_REASONS });
});

/* GET /api/admin/kyc/applications  —  KYC 审核列表 */
app.get('/api/admin/kyc/applications', requirePerm('kyc:review'), (req, res) => {
  const status = req.query.status || '';
  const city   = req.query.city || '';
  const q      = req.query.q || '';
  const limit  = Math.max(1, Math.min(100, parseInt(req.query.limit, 10) || 50));
  const offset = Math.max(0, parseInt(req.query.offset, 10) || 0);

  let sql = `
    SELECT a.*, u.name as user_name, u.phone as user_phone, u.avatar as user_avatar,
           u.type as user_type, u.kyc_status as user_kyc,
           s.city as sitter_city
    FROM kyc_applications a
    LEFT JOIN users u ON u.id = a.user_id
    LEFT JOIN sitters s ON s.name = u.name AND s.city IS NOT NULL
    WHERE 1=1
  `;
  const params = [];
  if (status) { sql += ' AND a.status=?'; params.push(status); }
  if (city)   { sql += ' AND s.city=?';   params.push(city); }
  if (q) {
    sql += ' AND (u.name LIKE ? OR u.phone LIKE ?)';
    params.push('%' + q + '%', '%' + q + '%');
  }
  sql += ' ORDER BY a.created_at DESC LIMIT ? OFFSET ?';
  params.push(limit, offset);

  const rows = db.prepare(sql).all(...params).map(r => ({
    ...r,
    user_phone: maskPhone(r.user_phone),
    snapshot: parseJSON(r.snapshot, {}),
  }));

  // 汇总
  const counts = db.prepare(`
    SELECT status, COUNT(*) as n FROM kyc_applications GROUP BY status
  `).all().reduce((m, x) => { m[x.status] = x.n; return m; }, {});

  res.json({ data: rows, counts });
});

/* GET /api/admin/kyc/applications/:id  —  审核详情（含全部 KYC 材料 + 审批日志） */
app.get('/api/admin/kyc/applications/:id', requirePerm('kyc:review'), (req, res) => {
  const app_ = db.prepare('SELECT * FROM kyc_applications WHERE id=?').get(req.params.id);
  if (!app_) return res.status(404).json({ error: '申请不存在' });
  const u = db.prepare('SELECT * FROM users WHERE id=?').get(app_.user_id);
  const s = u ? db.prepare('SELECT * FROM sitters WHERE name=? ORDER BY id DESC LIMIT 1').get(u.name) : null;
  const logs = db.prepare(`
    SELECT * FROM kyc_review_log WHERE application_id=? ORDER BY id ASC
  `).all(app_.id);

  res.json({
    data: {
      application: { ...app_, snapshot: parseJSON(app_.snapshot, {}) },
      user: u ? {
        id: u.id, name: u.name, phone: maskPhone(u.phone), type: u.type, avatar: u.avatar,
        kyc_status: u.kyc_status, id_card_masked: u.id_card_masked,
        wx_nickname: u.wx_nickname, has_wx: !!u.wx_openid,
        login_type: u.login_type, created_at: u.created_at,
      } : null,
      sitter: s ? {
        id: s.id, city: s.city, bio: s.bio, services: parseJSON(s.services),
        env_photos: parseJSON(s.env_photos), first_aid: parseJSON(s.first_aid),
        breeds_handled: parseJSON(s.breeds_handled),
        insurance: s.insurance, zhima_score: s.zhima_score,
        years_experience: s.years_experience, verified: !!s.verified,
        available: !!s.available, status: s.status,
      } : null,
      logs,
    }
  });
});

/* 内部工具：记录审批动作 + 更新应用 + 更新用户 */
function writeReviewAction({ appId, userId, admin, action, oldStatus, newStatus, reasonCode='', note='' }) {
  db.prepare(`
    INSERT INTO kyc_review_log (application_id, user_id, actor_id, actor_name, action, old_status, new_status, reason_code, note)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
  `).run(appId, userId, admin.id || 0, admin.username || '', action, oldStatus, newStatus, reasonCode, note);
}

/* POST /api/admin/kyc/applications/:id/claim  —  审核员认领（防多人同审） */
app.post('/api/admin/kyc/applications/:id/claim', requirePerm('kyc:review'), (req, res) => {
  const app_ = db.prepare('SELECT * FROM kyc_applications WHERE id=?').get(req.params.id);
  if (!app_) return res.status(404).json({ error: '申请不存在' });
  if (app_.status !== 'pending' && app_.status !== 'needs_more') {
    return res.status(400).json({ error: '该申请不在待审状态' });
  }
  if (app_.reviewer_id && app_.reviewer_id !== req.admin.id) {
    return res.status(409).json({ error: '该申请已被其他审核员认领' });
  }
  db.prepare(`
    UPDATE kyc_applications
    SET reviewer_id=?, reviewer_name=?, claimed_at=datetime('now','localtime')
    WHERE id=?
  `).run(req.admin.id, req.admin.username, app_.id);
  writeReviewAction({
    appId: app_.id, userId: app_.user_id, admin: req.admin,
    action: 'claimed', oldStatus: app_.status, newStatus: app_.status,
  });
  res.json({ success: true });
});

/* POST /api/admin/kyc/applications/:id/approve  —  通过 */
app.post('/api/admin/kyc/applications/:id/approve', requirePerm('kyc:review'), (req, res) => {
  const app_ = db.prepare('SELECT * FROM kyc_applications WHERE id=?').get(req.params.id);
  if (!app_) return res.status(404).json({ error: '申请不存在' });
  if (app_.status === 'approved') return res.status(400).json({ error: '该申请已通过' });
  const note = sanitizeText(req.body.note || '', 200);
  db.exec('BEGIN');
  try {
    db.prepare(`
      UPDATE kyc_applications
      SET status='approved', reviewer_id=?, reviewer_name=?, decided_at=datetime('now','localtime')
      WHERE id=?
    `).run(req.admin.id, req.admin.username, app_.id);

    db.prepare(`
      UPDATE users
      SET kyc_status='verified', kyc_reviewer_id=?, kyc_reviewed_at=datetime('now','localtime'),
          kyc_reject_code='', kyc_reject_note=''
      WHERE id=?
    `).run(req.admin.id, app_.user_id);

    // 宠物看护人：同步 sitters 表上架
    if (app_.role === 'sitter') {
      const u = db.prepare('SELECT name FROM users WHERE id=?').get(app_.user_id);
      if (u) db.prepare("UPDATE sitters SET verified=1, available=1, status='已认证' WHERE name=?").run(u.name);
    }
    writeReviewAction({
      appId: app_.id, userId: app_.user_id, admin: req.admin,
      action: 'approved', oldStatus: app_.status, newStatus: 'approved', note,
    });
    db.exec('COMMIT');
  } catch (e) {
    try { db.exec('ROLLBACK'); } catch {}
    console.error(e);
    return res.status(500).json({ error: '审批失败，请重试' });
  }
  res.json({ success: true, message: '已通过，用户将收到通知' });
});

/* POST /api/admin/kyc/applications/:id/reject  —  驳回（必须传驳回码） */
app.post('/api/admin/kyc/applications/:id/reject', requirePerm('kyc:review'), (req, res) => {
  const app_ = db.prepare('SELECT * FROM kyc_applications WHERE id=?').get(req.params.id);
  if (!app_) return res.status(404).json({ error: '申请不存在' });
  const code = String(req.body.reason_code || '');
  const note = sanitizeText(req.body.note || '', 300);
  if (!REJECT_REASONS[code]) return res.status(400).json({ error: '请选择驳回理由' });
  if (code === 'other' && !note) return res.status(400).json({ error: '选择"其它"必须填写备注' });

  db.exec('BEGIN');
  try {
    db.prepare(`
      UPDATE kyc_applications
      SET status='rejected', reviewer_id=?, reviewer_name=?,
          reject_code=?, reject_note=?, decided_at=datetime('now','localtime')
      WHERE id=?
    `).run(req.admin.id, req.admin.username, code, note, app_.id);

    db.prepare(`
      UPDATE users
      SET kyc_status='rejected', kyc_reviewer_id=?, kyc_reviewed_at=datetime('now','localtime'),
          kyc_reject_code=?, kyc_reject_note=?
      WHERE id=?
    `).run(req.admin.id, code, note, app_.user_id);

    // 看护人被驳回 → 暂不下架 sitters，但标记 status 为"已驳回"供用户看到
    if (app_.role === 'sitter') {
      const u = db.prepare('SELECT name FROM users WHERE id=?').get(app_.user_id);
      if (u) db.prepare("UPDATE sitters SET verified=0, available=0, status='已驳回' WHERE name=?").run(u.name);
    }
    writeReviewAction({
      appId: app_.id, userId: app_.user_id, admin: req.admin,
      action: 'rejected', oldStatus: app_.status, newStatus: 'rejected',
      reasonCode: code, note,
    });
    db.exec('COMMIT');
  } catch (e) {
    try { db.exec('ROLLBACK'); } catch {}
    console.error(e);
    return res.status(500).json({ error: '操作失败，请重试' });
  }
  res.json({ success: true, message: '已驳回，用户将收到通知' });
});

/* POST /api/admin/kyc/applications/:id/needs-more  —  需补充材料 */
app.post('/api/admin/kyc/applications/:id/needs-more', requirePerm('kyc:review'), (req, res) => {
  const app_ = db.prepare('SELECT * FROM kyc_applications WHERE id=?').get(req.params.id);
  if (!app_) return res.status(404).json({ error: '申请不存在' });
  const note = sanitizeText(req.body.note || '', 300);
  if (!note) return res.status(400).json({ error: '请填写需要用户补充的内容' });

  db.prepare(`
    UPDATE kyc_applications
    SET status='needs_more', reviewer_id=?, reviewer_name=?, needs_more_note=?
    WHERE id=?
  `).run(req.admin.id, req.admin.username, note, app_.id);

  db.prepare(`
    UPDATE users SET kyc_status='needs_more', kyc_reject_note=? WHERE id=?
  `).run(note, app_.user_id);

  writeReviewAction({
    appId: app_.id, userId: app_.user_id, admin: req.admin,
    action: 'needs_more', oldStatus: app_.status, newStatus: 'needs_more', note,
  });

  res.json({ success: true, message: '已发送补材料通知' });
});

/* 申请成为服务者 */
app.post('/api/sitters/apply', (req, res) => {
  let { name, phone, city, services, bio, avatar_idx } = req.body || {};
  name  = sanitizeText(name, 20);
  phone = String(phone || '').trim();
  city  = sanitizeText(city, 20);
  bio   = sanitizeText(bio, 500);
  avatar_idx = Math.max(0, Math.min(AVATAR_COUNT - 1, parseInt(avatar_idx, 10) || 0));

  if (!name || !NAME_RE.test(name))
    return res.status(400).json({ error: '姓名仅支持中英文/数字，2–20 位' });
  if (!PHONE_RE.test(phone))
    return res.status(400).json({ error: '请输入有效的 11 位手机号' });

  const avatar = localAvatar(avatar_idx);
  const result = db.prepare(`
    INSERT INTO sitters (name,avatar,location,city,services,bio,status,available)
    VALUES (?,?,?,?,?,?,'待审核',0)
  `).run(name, avatar, (city||'')+'市', city||'', JSON.stringify(services||[]), bio);
  res.json({ success: true, id: result.lastInsertRowid, message: '申请已提交！我们将在24小时内联系您 🎉' });
});

/* 公开接口：取可选头像列表（data URI 数组），前端头像选择器用 */
app.get('/api/avatars', (req, res) => {
  const list = [];
  for (let i = 0; i < AVATAR_COUNT; i++) list.push({ idx: i, url: localAvatar(i) });
  res.json({ data: list });
});

/* 公开接口：商务合作 / 留言反馈统一进入后台消息中心 */
app.post('/api/inquiries', (req, res) => {
  const type = ['feedback','business'].includes(req.body.type) ? req.body.type : 'feedback';
  const category = sanitizeText(req.body.category || '', 40);
  const name = sanitizeText(req.body.name || '', 30);
  const contact = sanitizeText(req.body.contact || '', 80);
  const company = sanitizeText(req.body.company || '', 80);
  const orderNo = sanitizeText(req.body.order_no || '', 40);
  const content = sanitizeText(req.body.content || '', 1200);
  const source = sanitizeText(req.body.source || '', 80);

  if (!category) return res.status(400).json({ error: '请选择类型' });
  if (!name) return res.status(400).json({ error: '请填写联系人姓名' });
  if (!contact) return res.status(400).json({ error: '请填写联系方式' });
  if (!content) return res.status(400).json({ error: '请填写详细内容' });
  if (type === 'business' && !company) return res.status(400).json({ error: '请填写公司/品牌名称' });

  const priority = orderNo || category.includes('争议') || category.includes('退款') ? 'high' : 'normal';
  const r = db.prepare(`
    INSERT INTO inquiries (type,category,name,contact,company,order_no,content,source,status,priority)
    VALUES (?,?,?,?,?,?,?,?,'new',?)
  `).run(type, category, name, contact, company, orderNo, content, source, priority);
  res.json({
    success: true,
    id: r.lastInsertRowid,
    message: type === 'business'
      ? '合作申请已提交，BD 团队会在 3 个工作日内联系您'
      : '留言已提交，客服会在 24 小时内联系您',
  });
});

/* =========================================================
   管理员 API（需要 JWT）
   ========================================================= */

/* 管理员登录 */
app.post('/api/admin/login', (req, res) => {
  const { username, password } = req.body;
  if (!username || !password) return res.status(400).json({ error: '请输入账号和密码' });
  const admin = db.prepare('SELECT * FROM admins WHERE username=?').get(username);
  if (!admin || !bcrypt.compareSync(password, admin.password)) {
    return res.status(401).json({ error: '账号或密码错误' });
  }
  if ((admin.status || 'active') !== 'active') {
    return res.status(403).json({ error: '账号已停用，请联系超级管理员' });
  }
  const role = admin.role || 'admin';
  const profile = adminOut(admin);
  const token = jwt.sign(
    { id: admin.id, username: admin.username, role, scopes: profile.scopes },
    JWT_SECRET, { expiresIn: '12h' }
  );
  res.json({ success: true, token, username: admin.username, role, admin: profile, message: '登录成功' });
});

/* 修改管理员密码（支持 POST/PUT，支持两种字段名） */
function handlePasswordChange(req, res) {
  const oldPwd = req.body.oldPassword || req.body.old_password;
  const newPwd = req.body.newPassword || req.body.new_password;
  if (!oldPwd || !newPwd) return res.status(400).json({ error: '请填写旧密码和新密码' });
  if (newPwd.length < 8) return res.status(400).json({ error: '新密码至少8位' });
  const admin = db.prepare('SELECT * FROM admins WHERE id=?').get(req.admin.id);
  if (!bcrypt.compareSync(oldPwd, admin.password)) {
    return res.status(400).json({ error: '当前密码错误' });
  }
  db.prepare('UPDATE admins SET password=? WHERE id=?').run(bcrypt.hashSync(newPwd, 10), req.admin.id);
  res.json({ success: true, message: '密码修改成功' });
}
app.post('/api/admin/password', requireAnyRole, handlePasswordChange);
app.put('/api/admin/password',  requireAnyRole, handlePasswordChange);

/* 消息中心：商务合作 / 留言反馈 */
app.get('/api/admin/inquiries', requirePerm('messages:receive'), (req, res) => {
  const { type = '', status = '', q = '', page = 1, limit = 50 } = req.query;
  let sql = 'SELECT * FROM inquiries WHERE 1=1';
  const params = [];
  if (['feedback','business'].includes(type)) { sql += ' AND type=?'; params.push(type); }
  if (['new','contacted','processing','resolved','closed'].includes(status)) { sql += ' AND status=?'; params.push(status); }
  if (q) {
    sql += ' AND (name LIKE ? OR contact LIKE ? OR company LIKE ? OR order_no LIKE ? OR content LIKE ?)';
    const kw = `%${q}%`;
    params.push(kw, kw, kw, kw, kw);
  }
  const total = db.prepare(sql.replace('SELECT *', 'SELECT COUNT(*) as n')).get(...params).n;
  sql += " ORDER BY CASE priority WHEN 'high' THEN 0 ELSE 1 END, datetime(created_at) DESC LIMIT ? OFFSET ?";
  params.push(+limit, (+page - 1) * +limit);
  res.json({ data: { list: db.prepare(sql).all(...params), total, page: +page, pages: Math.ceil(total / +limit) || 1 } });
});

app.put('/api/admin/inquiries/:id', requirePerm('messages:receive'), (req, res) => {
  const row = db.prepare('SELECT * FROM inquiries WHERE id=?').get(req.params.id);
  if (!row) return res.status(404).json({ error: '消息不存在' });
  const status = ['new','contacted','processing','resolved','closed'].includes(req.body.status) ? req.body.status : row.status;
  const note = sanitizeText(req.body.note || row.note || '', 500);
  db.prepare(`
    UPDATE inquiries SET status=?, note=?, assignee=?, updated_at=datetime('now','localtime')
    WHERE id=?
  `).run(status, note, req.admin.username || '', row.id);
  res.json({ success: true, data: db.prepare('SELECT * FROM inquiries WHERE id=?').get(row.id) });
});

/* 统计数据 — admin 和 finance 都可访问 */
app.get('/api/admin/stats', requireAnyRole, (req, res) => {
  const sitters  = db.prepare("SELECT COUNT(*) as n FROM sitters WHERE status='已认证'").get().n;
  const pending  = db.prepare("SELECT COUNT(*) as n FROM sitters WHERE status='待审核'").get().n;
  const bookings = db.prepare('SELECT COUNT(*) as n FROM bookings').get().n;
  const users    = db.prepare('SELECT COUNT(*) as n FROM users').get().n;
  const revenue  = db.prepare('SELECT COALESCE(SUM(price),0) as r FROM bookings').get().r;
  const recentBk = db.prepare('SELECT * FROM bookings ORDER BY id DESC LIMIT 8').all();
  const pendingSitters = db.prepare("SELECT * FROM sitters WHERE status='待审核' ORDER BY id DESC").all().map(sitterOut);
  res.json({ data: { sitters, pending, bookings, users, revenue, recentBk, pendingSitters } });
});

/* 图表数据 — 基于真实数据库聚合 */
app.get('/api/admin/stats/charts', requireAnyRole, (req, res) => {
  // ── 近 7 日预约趋势 ──
  const last7Days = [];
  for (let i = 6; i >= 0; i--) {
    const d = new Date();
    d.setDate(d.getDate() - i);
    const dateStr = d.toISOString().slice(0, 10);
    const row = db.prepare(
      "SELECT COUNT(*) as count, COALESCE(SUM(price),0) as revenue FROM bookings WHERE DATE(created_at)=?"
    ).get(dateStr);
    last7Days.push({
      date: dateStr,
      label: ['日','一','二','三','四','五','六'][d.getDay()],
      count: row.count || 0,
      revenue: row.revenue || 0,
    });
  }

  // ── 近 30 日流水曲线 ──
  const last30Days = [];
  for (let i = 29; i >= 0; i--) {
    const d = new Date();
    d.setDate(d.getDate() - i);
    const dateStr = d.toISOString().slice(0, 10);
    const row = db.prepare(
      "SELECT COALESCE(SUM(price),0) as revenue, COUNT(*) as count FROM bookings WHERE DATE(created_at)=? AND status IN ('已完成','进行中')"
    ).get(dateStr);
    last30Days.push({
      date: dateStr,
      day: d.getDate(),
      revenue: row.revenue || 0,
      count: row.count || 0,
    });
  }

  // ── 服务类型分布 ──
  const svcRows = db.prepare(
    "SELECT service_type as name, COUNT(*) as count, COALESCE(SUM(price),0) as revenue FROM bookings WHERE service_type IS NOT NULL AND service_type != '' GROUP BY service_type ORDER BY count DESC"
  ).all();
  const svcTotal = svcRows.reduce((a, b) => a + b.count, 0) || 1;
  const serviceDistribution = svcRows.map(r => ({
    name: r.name,
    count: r.count,
    revenue: r.revenue,
    pct: Math.round((r.count / svcTotal) * 100),
  }));

  // ── 城市 TOP 5 ──
  const cityRows = db.prepare(`
    SELECT s.city as city, COUNT(b.id) as bookings, COALESCE(SUM(b.price),0) as revenue
    FROM bookings b LEFT JOIN sitters s ON s.id = b.sitter_id
    WHERE s.city IS NOT NULL AND s.city != ''
    GROUP BY s.city
    ORDER BY bookings DESC
    LIMIT 5
  `).all();

  // ── 订单状态分布 ──
  const statusRows = db.prepare(
    "SELECT status, COUNT(*) as count FROM bookings GROUP BY status"
  ).all();

  res.json({
    data: {
      last7Days,
      last30Days,
      serviceDistribution,
      cityTop5: cityRows,
      statusDistribution: statusRows,
    },
  });
});

/* ── 服务者管理 ── */
app.get('/api/admin/sitters', requirePerm('sitters:manage'), (req, res) => {
  const { city, status, q, page=1, limit=10 } = req.query;
  let sql = 'SELECT * FROM sitters WHERE 1=1';
  const params = [];
  if (city) {
    if (!OPEN_CITY_SET.has(city)) return res.json({ data: [], total: 0, page: +page });
    sql += ' AND city=?';
    params.push(city);
  } else {
    sql += ` AND city IN (${OPEN_CITIES.map(()=>'?').join(',')})`;
    params.push(...OPEN_CITIES);
  }
  if (status) { sql += ' AND status=?';            params.push(status); }
  if (q)      { sql += ' AND (name LIKE ? OR location LIKE ?)'; params.push('%'+q+'%','%'+q+'%'); }
  const total = db.prepare(sql.replace('SELECT *','SELECT COUNT(*) as n')+'').all(...params)[0]?.n || 0;
  sql += ' ORDER BY id DESC LIMIT ? OFFSET ?';
  params.push(+limit, (+page-1)*(+limit));
  const rows = db.prepare(sql).all(...params).map(sitterOut);
  res.json({ data: rows, total, page: +page });
});

/* 获取单个服务者（管理员用） */
app.get('/api/admin/sitters/:id', requirePerm('sitters:manage'), (req, res) => {
  const row = db.prepare('SELECT * FROM sitters WHERE id=?').get(req.params.id);
  if (!row) return res.status(404).json({ error: '服务者不存在' });
  res.json({ data: sitterOut(row) });
});

app.post('/api/admin/sitters', requirePerm('sitters:manage'), (req, res) => {
  const { name, city, price, years_experience, avatar, bio, services, status } = req.body;
  if (!name) return res.status(400).json({ error: '请填写姓名' });
  if (!OPEN_CITY_SET.has(city)) return res.status(400).json({ error: '该城市暂未开通，目前仅支持北京、上海、深圳、广州、杭州' });
  const result = db.prepare(`INSERT INTO sitters
    (name,avatar,location,city,price,years_experience,bio,services,status,verified,available)
    VALUES (?,?,?,?,?,?,?,?,?,?,?)`).run(
    name, avatar || localAvatar(Math.floor(Math.random()*AVATAR_COUNT)),
    (city||'')+'市', city||'', price||60, years_experience||0, bio||'',
    JSON.stringify(services||[]), status||'待审核',
    (status==='已认证')?1:0, (status==='已认证')?1:0
  );
  res.json({ success: true, id: result.lastInsertRowid });
});

/* 支持局部更新：只传 status 时仅更新状态，传完整字段时全量更新 */
app.put('/api/admin/sitters/:id', requirePerm('sitters:manage'), (req, res) => {
  const existing = db.prepare('SELECT * FROM sitters WHERE id=?').get(req.params.id);
  if (!existing) return res.status(404).json({ error: '服务者不存在' });

  const b = req.body;
  const name           = b.name           ?? existing.name;
  const city           = b.city           ?? existing.city;
  if (!OPEN_CITY_SET.has(city)) return res.status(400).json({ error: '该城市暂未开通，目前仅支持北京、上海、深圳、广州、杭州' });
  const price          = b.price          ?? existing.price;
  const years_exp      = b.years_experience ?? existing.years_experience;
  const avatar         = b.avatar         ?? existing.avatar;
  const bio            = b.bio            ?? existing.bio;
  const services       = b.services       != null ? JSON.stringify(b.services) : existing.services;
  const pets           = b.pets           != null ? JSON.stringify(b.pets)     : existing.pets;
  const status         = b.status         ?? existing.status;
  const response_time  = b.response_time  ?? existing.response_time;

  db.prepare(`UPDATE sitters SET
    name=?, city=?, location=?, price=?, years_experience=?, avatar=?, bio=?,
    services=?, pets=?, status=?, response_time=?,
    verified=?, available=?
    WHERE id=?`).run(
    name, city, city+'市', price, years_exp,
    avatar, bio, services, pets,
    status, response_time,
    (status==='已认证')?1:0, (status==='已认证')?1:0,
    req.params.id
  );
  res.json({ success: true });
});

app.delete('/api/admin/sitters/:id', requirePerm('sitters:manage'), (req, res) => {
  db.prepare('DELETE FROM sitters WHERE id=?').run(req.params.id);
  res.json({ success: true });
});

/* ── 预约管理 ── */
app.get('/api/admin/bookings', requirePerm('orders:manage'), (req, res) => {
  const { status, service, q, page=1, limit=20 } = req.query;
  let sql = 'SELECT * FROM bookings WHERE 1=1';
  const params = [];
  if (status)  { sql += ' AND status=?';               params.push(status); }
  if (service) { sql += ' AND service_type=?';         params.push(service); }
  if (q)       { sql += ' AND (owner_name LIKE ? OR sitter_name LIKE ? OR pet_name LIKE ?)'; params.push('%'+q+'%','%'+q+'%','%'+q+'%'); }
  const total = db.prepare(sql.replace('SELECT *','SELECT COUNT(*) as n')).all(...params)[0]?.n || 0;
  const pages = Math.ceil(total / +limit) || 1;
  sql += ' ORDER BY id DESC LIMIT ? OFFSET ?';
  params.push(+limit, (+page-1)*(+limit));
  const list = db.prepare(sql).all(...params);
  res.json({ data: { list, total, pages, page: +page } });
});

app.get('/api/admin/bookings/:id', requirePerm('orders:manage'), (req, res) => {
  const row = db.prepare('SELECT * FROM bookings WHERE id=?').get(req.params.id);
  if (!row) return res.status(404).json({ error: '预约不存在' });
  res.json({ data: row });
});

/* 本地时间字符串 'YYYY-MM-DD HH:mm:ss'（避免 toISOString 转成 UTC）*/
function localTimeStr(d) {
  const pad = n => String(n).padStart(2, '0');
  return `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
}

/* 订单完整详情：基础 + 服务者 + 时间线（系统事件 + 管理员备注 + 模拟沟通） */
app.get('/api/admin/bookings/:id/detail', requirePerm('orders:manage'), (req, res) => {
  const id = +req.params.id;
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '预约不存在' });

  // 关联服务者
  let sitter = null;
  if (b.sitter_id) {
    const row = db.prepare('SELECT id,name,avatar,city,location,rating,review_count,price,response_time,verified,services FROM sitters WHERE id=?').get(b.sitter_id);
    if (row) sitter = { ...row, services: parseJSON(row.services) };
  }

  // 数据库已存的事件
  const stored = db.prepare('SELECT * FROM booking_events WHERE booking_id=? ORDER BY id ASC').all(id);

  // 自动推断的系统事件（基于 created_at / status / start_date 等）
  const autoEvents = [];
  autoEvents.push({
    type: 'system', actor_role: 'system', actor: '系统',
    content: `用户 ${b.owner_name} 提交了预约请求`,
    new_status: '待确认',
    created_at: b.created_at,
  });
  if (['进行中','已完成','已取消'].includes(b.status)) {
    const t = new Date(b.created_at); t.setHours(t.getHours() + 1);
    autoEvents.push({
      type: 'system', actor_role: 'sitter', actor: b.sitter_name || '服务者',
      content: b.status === '已取消' ? '服务者查看了订单' : '服务者确认接单',
      new_status: b.status === '已取消' ? null : '进行中',
      created_at: localTimeStr(t),
    });
  }
  if (b.status === '已完成' && b.start_date) {
    autoEvents.push({
      type: 'system', actor_role: 'sitter', actor: b.sitter_name || '服务者',
      content: `服务开始，${b.pet_name || '宠物'} 已由服务者接走`,
      created_at: b.start_date + ' 09:00:00',
    });
    autoEvents.push({
      type: 'message', actor_role: 'sitter', actor: b.sitter_name || '服务者',
      content: `${b.pet_name || '宝贝'} 很乖，吃饭和玩耍都很正常，放心哦 🐾`,
      created_at: b.start_date + ' 14:30:00',
    });
    const endDate = b.end_date || b.start_date;
    autoEvents.push({
      type: 'system', actor_role: 'sitter', actor: b.sitter_name || '服务者',
      content: '服务完成，宠物已送回',
      new_status: '已完成',
      created_at: endDate + ' 18:00:00',
    });
  }
  if (b.status === '已取消') {
    const t = new Date(b.created_at); t.setHours(t.getHours() + 3);
    autoEvents.push({
      type: 'system', actor_role: 'owner', actor: b.owner_name,
      content: '用户取消了本次预约',
      new_status: '已取消',
      created_at: localTimeStr(t),
    });
  }
  if (b.status === '进行中' && b.start_date) {
    autoEvents.push({
      type: 'system', actor_role: 'sitter', actor: b.sitter_name || '服务者',
      content: '服务已开始，正在照料宠物',
      new_status: '进行中',
      created_at: b.start_date + ' 09:00:00',
    });
  }

  // 合并并按时间排序
  const events = [...autoEvents, ...stored].sort((a, b) =>
    String(a.created_at||'').localeCompare(String(b.created_at||''))
  );

  res.json({ data: { booking: b, sitter, events } });
});

/* 添加管理员备注/沟通记录 */
app.post('/api/admin/bookings/:id/notes', requirePerm('orders:manage'), (req, res) => {
  const id = +req.params.id;
  const content = (req.body.content || '').trim();
  if (!content) return res.status(400).json({ error: '内容不能为空' });
  if (content.length > 500) return res.status(400).json({ error: '内容最长 500 字' });

  const b = db.prepare('SELECT id FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '预约不存在' });

  db.prepare(`INSERT INTO booking_events (booking_id, type, actor, actor_role, content)
              VALUES (?, 'admin_note', ?, 'admin', ?)`)
    .run(id, req.admin.username, content);
  res.json({ success: true });
});

app.put('/api/admin/bookings/:id', requirePerm('orders:manage'), (req, res) => {
  const id = +req.params.id;
  const existing = db.prepare('SELECT status FROM bookings WHERE id=?').get(id);
  if (!existing) return res.status(404).json({ error: '预约不存在' });

  const newStatus = req.body.status;
  db.prepare('UPDATE bookings SET status=? WHERE id=?').run(newStatus, id);

  // 记录状态变更事件
  if (existing.status !== newStatus) {
    db.prepare(`INSERT INTO booking_events (booking_id, type, actor, actor_role, old_status, new_status, content)
                VALUES (?, 'system', ?, 'admin', ?, ?, ?)`)
      .run(id, req.admin.username, existing.status, newStatus,
           `管理员将订单状态从「${existing.status}」改为「${newStatus}」`);
  }

  res.json({ success: true });
});

app.delete('/api/admin/bookings/:id', requirePerm('orders:manage'), (req, res) => {
  db.prepare('DELETE FROM bookings WHERE id=?').run(req.params.id);
  res.json({ success: true });
});

/* ── 争议（担保交易售后）管理 ── */

/* GET /api/admin/disputes —— 争议列表（默认只看 OPEN） */
app.get('/api/admin/disputes', requirePerm('orders:manage'), (req, res) => {
  const { status='OPEN', page=1, limit=20 } = req.query;
  let sql = 'SELECT * FROM disputes WHERE 1=1';
  const params = [];
  if (status && status !== 'ALL') { sql += ' AND status=?'; params.push(status); }
  const total = db.prepare(sql.replace('SELECT *','SELECT COUNT(*) as n')).all(...params)[0]?.n || 0;
  const pages = Math.ceil(total / +limit) || 1;
  sql += ' ORDER BY id DESC LIMIT ? OFFSET ?';
  params.push(+limit, (+page-1)*(+limit));
  const rows = db.prepare(sql).all(...params);
  // 关联订单概要
  const list = rows.map(d => {
    const b = db.prepare('SELECT order_no, order_status, fund_status, sitter_name, pet_name, service_type, total_amount_cents, provider_income_cents FROM bookings WHERE id=?').get(d.order_id) || {};
    const owner = db.prepare('SELECT name FROM users WHERE id=?').get(d.user_id);
    const provider = d.provider_id ? db.prepare('SELECT name FROM users WHERE id=?').get(d.provider_id) : null;
    return {
      ...d,
      evidence_images: (()=>{ try { return JSON.parse(d.evidence_images); } catch(e) { return []; } })(),
      order_no: b.order_no || '',
      order_status: b.order_status || '',
      fund_status: b.fund_status || '',
      sitter_name: b.sitter_name || '',
      pet_name: b.pet_name || '',
      service_type: b.service_type || '',
      total_amount_yuan: centsToYuan(b.total_amount_cents || 0),
      provider_income_yuan: centsToYuan(b.provider_income_cents || 0),
      owner_name: owner ? owner.name : '',
      provider_name: provider ? provider.name : '',
    };
  });
  res.json({ data: { list, total, pages, page: +page } });
});

/* POST /api/admin/disputes/:id/resolve —— 平台裁决
   body: { result: 'full_refund' | 'reject_and_settle', admin_note }
   full_refund: 主人全额退款，订单 → CANCELLED，资金 → REFUNDED
   reject_and_settle: 驳回申诉，订单 → WAIT_REVIEW（若原为 WAIT_REVIEW/WAIT_OWNER_CONFIRM/IN_SERVICE），重启 T+1 冷静期
*/
app.post('/api/admin/disputes/:id/resolve', requirePerm('orders:manage'), (req, res) => {
  const id = +req.params.id;
  const d = db.prepare('SELECT * FROM disputes WHERE id=?').get(id);
  if (!d) return res.status(404).json({ error: '争议不存在' });
  if (d.status !== 'OPEN') return res.status(400).json({ error: '该争议已处理' });

  const result = String(req.body?.result || '');
  const adminNote = sanitizeText(req.body?.admin_note || '', 300);
  if (!['full_refund','reject_and_settle'].includes(result)) {
    return res.status(400).json({ error: '处理结果不合法' });
  }

  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(d.order_id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  if (b.order_status !== ORDER_STATUS.DISPUTE) {
    return res.status(400).json({ error: `订单当前状态 ${b.order_status}，不在争议中` });
  }

  const adminActor = req.admin?.username || 'admin';

  db.exec('BEGIN');
  try {
    if (result === 'full_refund') {
      // 订单 → CANCELLED, 资金 → REFUNDED
      const r = transitionOrder(d.order_id, ORDER_STATUS.CANCELLED, FUND_STATUS.REFUNDED,
        'cancel_reason=?, cancelled_at=?', [`平台裁决全额退款：${adminNote}`, nowISO()],
        adminActor, 'admin', `平台裁决：全额退款 ¥${centsToYuan(b.total_amount_cents || 0)}`);
      if (!r.ok) throw new Error(r.msg);
      db.prepare(`
        UPDATE payments SET refund_amount_cents=amount_cents, refund_status='REFUNDED', refunded_at=?
        WHERE order_id=? AND status='PAID'
      `).run(nowISO(), d.order_id);
      db.prepare("UPDATE settlements SET status='CANCELLED', updated_at=? WHERE order_id=?")
        .run(nowISO(), d.order_id);
      db.prepare(`
        UPDATE disputes SET status='RESOLVED', admin_result=?, admin_note=?, resolved_amount_cents=?, resolved_at=?
        WHERE id=?
      `).run('full_refund', adminNote, b.total_amount_cents || 0, nowISO(), id);
    } else {
      // 驳回：恢复到 WAIT_REVIEW，资金回 SETTLEMENT_PENDING，钱包重新 credit pending
      const availableAt = deltaISO(SETTLEMENT_COOL_MS);
      const r = transitionOrder(d.order_id, ORDER_STATUS.WAIT_REVIEW, FUND_STATUS.SETTLEMENT_PENDING,
        'wallet_available_at=?', [availableAt],
        adminActor, 'admin', `平台裁决：驳回申诉，重启 T+1 结算`);
      if (!r.ok) throw new Error(r.msg);

      // 钱包 pending 重新入账（之前被 walletDebitPending 扣掉）
      if (d.provider_id && b.provider_income_cents > 0) {
        walletCreditPending(d.provider_id, d.order_id, b.provider_income_cents,
          `订单 ${b.order_no || d.order_id} 争议驳回，恢复结算 ¥${centsToYuan(b.provider_income_cents)}`);
      }
      // 如果已有 settlement 记录，复活它
      const settle = db.prepare('SELECT id FROM settlements WHERE order_id=?').get(d.order_id);
      if (settle) {
        db.prepare("UPDATE settlements SET status='PENDING', available_at=?, updated_at=? WHERE order_id=?")
          .run(availableAt, nowISO(), d.order_id);
      } else {
        db.prepare(`
          INSERT INTO settlements (order_id, provider_id, settlement_amount_cents, platform_fee_cents, status, available_at)
          VALUES (?, ?, ?, ?, 'PENDING', ?)
        `).run(d.order_id, d.provider_id || 0, b.provider_income_cents || 0, b.platform_fee_cents || 0, availableAt);
      }
      db.prepare(`
        UPDATE disputes SET status='REJECTED', admin_result=?, admin_note=?, resolved_at=?
        WHERE id=?
      `).run('reject_and_settle', adminNote, nowISO(), id);
    }

    db.exec('COMMIT');
    res.json({ success: true, message: result === 'full_refund' ? '已执行全额退款' : '已驳回申诉，T+1 后自动结算' });
  } catch(e) {
    try { db.exec('ROLLBACK'); } catch(_) {}
    res.status(500).json({ error: e.message });
  }
});

/* ── 用户管理 ── */
app.get('/api/admin/users', requirePerm('users:manage'), (req, res) => {
  const { type, status, q, page=1, limit=20 } = req.query;
  let sql = 'SELECT * FROM users WHERE 1=1';
  const params = [];
  if (type)   { sql += ' AND type=?';    params.push(type); }
  if (status) { sql += ' AND status=?';  params.push(status); }
  if (q)      { sql += ' AND (name LIKE ? OR phone LIKE ?)'; params.push('%'+q+'%','%'+q+'%'); }
  const total = db.prepare(sql.replace('SELECT *','SELECT COUNT(*) as n')).all(...params)[0]?.n || 0;
  const pages = Math.ceil(total / +limit) || 1;
  sql += ' ORDER BY id DESC LIMIT ? OFFSET ?';
  params.push(+limit, (+page-1)*(+limit));
  const list = db.prepare(sql).all(...params).map(u => ({
    ...userOut(u),
    booking_count: u.type === '宠物服务者'
      ? (db.prepare('SELECT COUNT(*) as n FROM bookings WHERE sitter_name=?').get(u.name)?.n || 0)
      : (db.prepare('SELECT COUNT(*) as n FROM bookings WHERE owner_name=?').get(u.name)?.n || 0),
    pet_count: 0,
  }));
  res.json({ data: { list, total, pages, page: +page } });
});

app.get('/api/admin/users/:id', requirePerm('users:manage'), (req, res) => {
  const u = db.prepare('SELECT * FROM users WHERE id=?').get(req.params.id);
  if (!u) return res.status(404).json({ error: '用户不存在' });
  const booking_count = u.type === '宠物服务者'
    ? (db.prepare('SELECT COUNT(*) as n FROM bookings WHERE sitter_name=?').get(u.name)?.n || 0)
    : (db.prepare('SELECT COUNT(*) as n FROM bookings WHERE owner_name=?').get(u.name)?.n || 0);
  // 管理员视图：去除密码哈希 / 疫苗证图片原始字节，但保留所有合规审核字段（身份证掩码、紧急联系人、宠物信息等）
  const { password, vaccine_img, ...rest } = u;
  res.json({ data: {
    ...rest,
    has_vaccine: !!vaccine_img,
    booking_count,
    pet_count: 0,
  } });
});

/* 管理员重置用户头像：随机分配一张系统图库头像 */
app.post('/api/admin/users/:id/reset-avatar', requirePerm('users:manage'), (req, res) => {
  const u = db.prepare('SELECT id FROM users WHERE id=?').get(req.params.id);
  if (!u) return res.status(404).json({ error: '用户不存在' });
  const newAvatar = localAvatar(Math.floor(Math.random() * AVATAR_COUNT));
  db.prepare('UPDATE users SET avatar=? WHERE id=?').run(newAvatar, req.params.id);
  res.json({ success: true, avatar: newAvatar });
});

app.post('/api/admin/users', requirePerm('users:manage'), (req, res) => {
  const { name, phone, type, status } = req.body;
  if (!name) return res.status(400).json({ error: '请填写姓名' });
  const result = db.prepare('INSERT INTO users (name,phone,type,avatar,status) VALUES (?,?,?,?,?)').run(
    name, phone||'', type||'宠物主人',
    localAvatar(Math.floor(Math.random()*AVATAR_COUNT)), status||'正常'
  );
  res.json({ success: true, id: result.lastInsertRowid });
});

app.put('/api/admin/users/:id', requirePerm('users:manage'), (req, res) => {
  const existing = db.prepare('SELECT * FROM users WHERE id=?').get(req.params.id);
  if (!existing) return res.status(404).json({ error: '用户不存在' });
  const name = req.body.name ?? existing.name;
  const phone = req.body.phone ?? existing.phone;
  const type = req.body.type ?? existing.type;
  const status = req.body.status ?? existing.status;
  db.prepare('UPDATE users SET name=?, phone=?, type=?, status=? WHERE id=?').run(
    name, phone, type, status, req.params.id
  );
  res.json({ success: true });
});

app.delete('/api/admin/users/:id', requirePerm('users:manage'), (req, res) => {
  db.prepare('DELETE FROM users WHERE id=?').run(req.params.id);
  res.json({ success: true });
});

/* ── 服务项目管理 ── */
// 将DB行映射为前端友好格式
function svcAdminOut(s) {
  const parsed = svcOut(s);
  // base_price: 从 price_range 提取首个数字，或直接存储的数字
  const priceMatch = String(s.price_range||'').match(/\d+/);
  parsed.base_price = s.base_price || (priceMatch ? +priceMatch[0] : 0);
  parsed.pet_types  = s.pet_types  ? parseJSON(s.pet_types) : parseJSON(s.features, []);
  parsed.image      = s.img || '';
  parsed.status     = s.status || '上线';
  return parsed;
}

app.get('/api/admin/services', requirePerm('services:manage'), (req, res) => {
  res.json({ data: db.prepare('SELECT * FROM services ORDER BY sort_order').all().map(svcAdminOut) });
});

app.get('/api/admin/services/:id', requirePerm('services:manage'), (req, res) => {
  const row = db.prepare('SELECT * FROM services WHERE id=?').get(req.params.id);
  if (!row) return res.status(404).json({ error: '服务不存在' });
  res.json({ data: svcAdminOut(row) });
});

app.post('/api/admin/services', requirePerm('services:manage'), (req, res) => {
  const { name, icon, image, img, description, base_price, price_range, pet_types, tag, features, status } = req.body;
  if (!name) return res.status(400).json({ error: '请填写服务名称' });
  const maxOrder = db.prepare('SELECT MAX(sort_order) as m FROM services').get().m || 0;
  const result = db.prepare(`INSERT INTO services
    (name,icon,img,description,price_range,tag,features,sort_order)
    VALUES (?,?,?,?,?,?,?,?)`).run(
    name, icon||'🐾', image||img||'', description||'',
    price_range || (base_price ? base_price+'元/天' : ''),
    tag || (status||''),
    JSON.stringify(pet_types || features || []),
    maxOrder+1
  );
  res.json({ success: true, id: result.lastInsertRowid });
});

app.put('/api/admin/services/:id', requirePerm('services:manage'), (req, res) => {
  const { name, icon, image, img, description, base_price, price_range, pet_types, tag, features, status, sort_order } = req.body;
  db.prepare(`UPDATE services SET name=?,icon=?,img=?,description=?,price_range=?,tag=?,features=?,sort_order=? WHERE id=?`).run(
    name, icon||'🐾', image||img||'', description||'',
    price_range || (base_price ? base_price+'元/天' : ''),
    tag || (status||''),
    JSON.stringify(pet_types || features || []),
    sort_order||0, req.params.id
  );
  res.json({ success: true });
});

app.delete('/api/admin/services/:id', requirePerm('services:manage'), (req, res) => {
  db.prepare('DELETE FROM services WHERE id=?').run(req.params.id);
  res.json({ success: true });
});

/* ── 评价管理 ── */
function reviewOut(r) {
  return {
    ...r,
    reviewer_name:   r.user_name   || '匿名用户',
    reviewer_avatar: r.avatar      || '',
    content:         r.review_text || '',
    service_type:    r.service     || '',
    sitter_name:     r.sitter_name || (() => {
      const s = db.prepare('SELECT name FROM sitters WHERE id=?').get(r.sitter_id);
      return s ? s.name : '-';
    })(),
  };
}

app.get('/api/admin/reviews', requirePerm('reviews:moderate'), (req, res) => {
  const { rating, q, page=1, limit=20 } = req.query;
  let sql = 'SELECT * FROM reviews WHERE 1=1';
  const params = [];
  if (rating) { sql += ' AND rating=?'; params.push(+rating); }
  if (q)      { sql += ' AND (user_name LIKE ? OR review_text LIKE ?)'; params.push('%'+q+'%','%'+q+'%'); }
  const total = db.prepare(sql.replace('SELECT *','SELECT COUNT(*) as n')).all(...params)[0]?.n || 0;
  const pages = Math.ceil(total / +limit) || 1;
  sql += ' ORDER BY id DESC LIMIT ? OFFSET ?';
  params.push(+limit, (+page-1)*(+limit));
  const list = db.prepare(sql).all(...params).map(reviewOut);
  res.json({ data: { list, total, pages, page: +page } });
});

/* 编辑评价文字（不允许修改星级，保护评分真实性） */
app.put('/api/admin/reviews/:id', requirePerm('reviews:moderate'), (req, res) => {
  const review = db.prepare('SELECT * FROM reviews WHERE id=?').get(req.params.id);
  if (!review) return res.status(404).json({ error: '评价不存在' });
  const { review_text } = req.body;
  if (!review_text || !review_text.trim()) return res.status(400).json({ error: '评价内容不能为空' });
  db.prepare('UPDATE reviews SET review_text=? WHERE id=?').run(review_text.trim(), req.params.id);
  res.json({ success: true, message: '评价内容已更新' });
});

/* 删除评价并自动重新计算服务者综合评分 */
app.delete('/api/admin/reviews/:id', requirePerm('reviews:moderate'), (req, res) => {
  const review = db.prepare('SELECT sitter_id FROM reviews WHERE id=?').get(req.params.id);
  db.prepare('DELETE FROM reviews WHERE id=?').run(req.params.id);

  // 重算该服务者的综合评分和评价数
  if (review && review.sitter_id) {
    const agg = db.prepare(
      'SELECT COUNT(*) as cnt, ROUND(AVG(rating),1) as avg FROM reviews WHERE sitter_id=?'
    ).get(review.sitter_id);
    db.prepare('UPDATE sitters SET rating=?, review_count=? WHERE id=?').run(
      agg.avg || 0, agg.cnt || 0, review.sitter_id
    );
  }
  res.json({ success: true, message: '评价已删除，综合评分已重新计算' });
});

/* =========================================================
   财务专属 API（admin + finance 角色均可访问，只读）
   ========================================================= */
app.get('/api/admin/finance/overview', requirePerm('finance:read'), (req, res) => {
  // ── 汇总卡片 ──
  const totalRevenue  = db.prepare("SELECT COALESCE(SUM(price),0) as v FROM bookings WHERE status!='已取消'").get().v;
  const totalBookings = db.prepare("SELECT COUNT(*) as v FROM bookings WHERE status!='已取消'").get().v;
  const thisMonth     = new Date().toISOString().slice(0,7); // YYYY-MM
  const monthRevenue  = db.prepare("SELECT COALESCE(SUM(price),0) as v FROM bookings WHERE status!='已取消' AND strftime('%Y-%m',created_at)=?").get(thisMonth).v;
  const monthBookings = db.prepare("SELECT COUNT(*) as v FROM bookings WHERE status!='已取消' AND strftime('%Y-%m',created_at)=?").get(thisMonth).v;
  const pendingPay    = db.prepare("SELECT COUNT(*) as v FROM bookings WHERE status='待确认'").get().v;
  const avgOrderValue = totalBookings > 0 ? Math.round(totalRevenue / totalBookings) : 0;

  // ── 近 6 个月趋势 ──
  const monthly = db.prepare(`
    SELECT strftime('%Y-%m', created_at) as month,
           COUNT(*) as bookings,
           COALESCE(SUM(price),0) as revenue
    FROM bookings WHERE status!='已取消'
    GROUP BY month ORDER BY month DESC LIMIT 6
  `).all().reverse();

  // ── 服务类型收益分析 ──
  const byService = db.prepare(`
    SELECT service_type, COUNT(*) as bookings, COALESCE(SUM(price),0) as revenue
    FROM bookings WHERE status!='已取消' AND service_type!=''
    GROUP BY service_type ORDER BY revenue DESC
  `).all();

  // ── 城市收益分析 ──
  const byCity = db.prepare(`
    SELECT s.city, COUNT(b.id) as bookings, COALESCE(SUM(b.price),0) as revenue
    FROM bookings b JOIN sitters s ON b.sitter_id=s.id
    WHERE b.status!='已取消' AND s.city!=''
    GROUP BY s.city ORDER BY revenue DESC LIMIT 8
  `).all();

  // ── 近期订单（财务只看脱敏数据，无用户手机号） ──
  const recentOrders = db.prepare(`
    SELECT id, order_no, owner_name, sitter_name, service_type, price, status,
           order_status, start_date, end_date, created_at,
           strftime('%Y-%m-%d', created_at) as date
    FROM bookings ORDER BY id DESC LIMIT 10
  `).all();

  res.json({ data: {
    summary: { totalRevenue, totalBookings, monthRevenue, monthBookings, pendingPay, avgOrderValue },
    monthly, byService, byCity, recentOrders
  }});
});

/* 财务：管理员列表（admin 查看所有，finance 查 role 字段以验证权限） */
app.get('/api/admin/admins/meta', requirePerm('accounts:manage'), (req, res) => {
  res.json({ data: { scopes: ADMIN_SCOPE_OPTIONS, notify_channels: ADMIN_NOTIFY_CHANNELS } });
});

app.get('/api/admin/admins', requirePerm('accounts:manage'), (req, res) => {
  const list = db.prepare("SELECT id, username, display_name, department, role, scopes, notify_channels, status, created_at FROM admins ORDER BY id").all();
  res.json({ data: list.map(adminOut) });
});

app.post('/api/admin/admins', requirePerm('accounts:manage'), (req, res) => {
  const { username, password, role } = req.body;
  if (!username || !password) return res.status(400).json({ error: '请填写账号和密码' });
  if (password.length < 8) return res.status(400).json({ error: '密码至少8位' });
  if (!['super','operator','finance'].includes(role)) return res.status(400).json({ error: '角色无效，可选：super/operator/finance' });
  // finance 管理员只能创建 operator 账号，不能给自己或别人超权
  if (req.admin.role === 'finance' && role !== 'operator') {
    return res.status(403).json({ error: '财务管理员只能创建运营账号' });
  }
  const exist = db.prepare('SELECT id FROM admins WHERE username=?').get(username);
  if (exist) return res.status(400).json({ error: '账号已存在' });
  const hash = bcrypt.hashSync(password, 10);
  const scopes = role === 'super'
    ? ['*']
    : sanitizeAdminList(req.body.scopes, Object.keys(ADMIN_SCOPE_OPTIONS), adminScopesForRole(role));
  const notifyChannels = sanitizeAdminList(req.body.notify_channels, Object.keys(ADMIN_NOTIFY_CHANNELS), ['dingtalk']);
  const displayName = sanitizeText(req.body.display_name || '', 30);
  const department = sanitizeText(req.body.department || '', 30);
  const r = db.prepare(`
    INSERT INTO admins (username,password,role,display_name,department,scopes,notify_channels,status)
    VALUES (?,?,?,?,?,?,?,'active')
  `).run(username, hash, role, displayName, department, JSON.stringify(scopes), JSON.stringify(notifyChannels));
  res.json({ success: true, id: r.lastInsertRowid });
});

app.put('/api/admin/admins/:id', requirePerm('accounts:manage'), (req, res) => {
  const target = db.prepare('SELECT * FROM admins WHERE id=?').get(req.params.id);
  if (!target) return res.status(404).json({ error: '账号不存在' });
  if (req.admin.role === 'finance' && target.role !== 'operator') {
    return res.status(403).json({ error: '财务管理员只能管理运营账号' });
  }
  const role = target.role || 'operator';
  const scopes = role === 'super'
    ? ['*']
    : sanitizeAdminList(req.body.scopes, Object.keys(ADMIN_SCOPE_OPTIONS), adminScopesForRole(role));
  const notifyChannels = sanitizeAdminList(req.body.notify_channels, Object.keys(ADMIN_NOTIFY_CHANNELS), []);
  const displayName = sanitizeText(req.body.display_name || '', 30);
  const department = sanitizeText(req.body.department || '', 30);
  const status = ['active','disabled'].includes(req.body.status) ? req.body.status : (target.status || 'active');
  if (target.id === req.admin.id && status !== 'active') return res.status(400).json({ error: '不能停用当前登录账号' });
  db.prepare(`
    UPDATE admins SET display_name=?, department=?, scopes=?, notify_channels=?, status=?
    WHERE id=?
  `).run(displayName, department, JSON.stringify(scopes), JSON.stringify(notifyChannels), status, target.id);
  res.json({ success: true, data: adminOut(db.prepare('SELECT * FROM admins WHERE id=?').get(target.id)) });
});

app.delete('/api/admin/admins/:id', requirePerm('accounts:manage'), (req, res) => {
  const target = db.prepare('SELECT * FROM admins WHERE id=?').get(req.params.id);
  if (!target) return res.status(404).json({ error: '账号不存在' });
  // 不能删除自己
  if (target.id === req.admin.id) return res.status(400).json({ error: '不能删除当前登录账号' });
  // finance 只能删除 operator 账号
  if (req.admin.role === 'finance' && target.role !== 'operator') {
    return res.status(403).json({ error: '财务管理员只能删除运营账号' });
  }
  // 保留最后一个 super/finance
  if (['super','finance'].includes(target.role)) {
    const count = db.prepare("SELECT COUNT(*) as n FROM admins WHERE role IN ('super','finance')").get().n;
    if (count <= 1) return res.status(400).json({ error: '至少保留一个管理账号（super 或 finance）' });
  }
  db.prepare('DELETE FROM admins WHERE id=?').run(req.params.id);
  res.json({ success: true, message: `账号 ${target.username} 已删除` });
});

/* =========================================================
   帮助中心 公开 API
   ========================================================= */

app.get('/api/help/categories', (req, res) => {
  const cats = db.prepare('SELECT * FROM help_categories ORDER BY sort_order').all();
  // 每个分类附带文章数
  const result = cats.map(c => ({
    ...c,
    article_count: db.prepare('SELECT COUNT(*) as n FROM help_articles WHERE category_id=? AND published=1').get(c.id)?.n || 0,
  }));
  res.json({ data: result });
});

app.get('/api/help/articles', (req, res) => {
  const { category_id, q, role, featured, limit = 50 } = req.query;
  let sql = 'SELECT id,category_id,title,excerpt,image,featured,role,views,sort_order,created_at,updated_at FROM help_articles WHERE published=1';
  const params = [];
  if (category_id) { sql += ' AND category_id=?'; params.push(+category_id); }
  if (role)        { sql += " AND (role=? OR role='' OR role IS NULL)"; params.push(role); }
  if (featured === '1') { sql += ' AND CAST(featured AS INTEGER)=1'; }
  if (q)           { sql += ' AND (title LIKE ? OR excerpt LIKE ? OR content LIKE ?)'; params.push('%'+q+'%','%'+q+'%','%'+q+'%'); }
  sql += " ORDER BY CAST(featured AS INTEGER) DESC, sort_order, datetime(updated_at) DESC, id DESC LIMIT ?";
  params.push(+limit);
  res.json({ data: db.prepare(sql).all(...params) });
});

app.get('/api/help/articles/:id', (req, res) => {
  const art = db.prepare('SELECT * FROM help_articles WHERE id=? AND published=1').get(req.params.id);
  if (!art) return res.status(404).json({ error: '文章不存在' });
  db.prepare('UPDATE help_articles SET views=views+1 WHERE id=?').run(req.params.id);
  const cat = db.prepare('SELECT * FROM help_categories WHERE id=?').get(art.category_id);
  res.json({ data: { ...art, category: cat } });
});

/* ── 帮助中心 管理员 API ── */
app.get('/api/admin/help/categories', requirePerm('help:manage'), (req, res) => {
  const cats = db.prepare('SELECT * FROM help_categories ORDER BY sort_order').all().map(c => ({
    ...c,
    article_count: db.prepare('SELECT COUNT(*) as n FROM help_articles WHERE category_id=?').get(c.id)?.n || 0,
  }));
  res.json({ data: cats });
});

app.post('/api/admin/help/categories', requirePerm('help:manage'), (req, res) => {
  const { name, icon } = req.body;
  if (!name) return res.status(400).json({ error: '请填写分类名称' });
  const max = db.prepare('SELECT MAX(sort_order) as m FROM help_categories').get().m || 0;
  const r = db.prepare('INSERT INTO help_categories (name,icon,sort_order) VALUES (?,?,?)').run(name, icon||'❓', max+1);
  res.json({ success: true, id: r.lastInsertRowid });
});

app.put('/api/admin/help/categories/:id', requirePerm('help:manage'), (req, res) => {
  const { name, icon, sort_order } = req.body;
  db.prepare('UPDATE help_categories SET name=?,icon=?,sort_order=? WHERE id=?').run(name, icon||'❓', sort_order||0, req.params.id);
  res.json({ success: true });
});

app.delete('/api/admin/help/categories/:id', requirePerm('help:manage'), (req, res) => {
  db.prepare('DELETE FROM help_categories WHERE id=?').run(req.params.id);
  db.prepare('DELETE FROM help_articles WHERE category_id=?').run(req.params.id);
  res.json({ success: true });
});

app.get('/api/admin/help/articles', requirePerm('help:manage'), (req, res) => {
  const { category_id, published, q, page=1, limit=20 } = req.query;
  let sql = 'SELECT a.*,c.name as category_name FROM help_articles a LEFT JOIN help_categories c ON a.category_id=c.id WHERE 1=1';
  const params = [];
  if (category_id) { sql += ' AND a.category_id=?'; params.push(+category_id); }
  if (published !== undefined && published !== '') { sql += ' AND a.published=?'; params.push(+published); }
  if (q)           { sql += ' AND a.title LIKE ?';   params.push('%'+q+'%'); }
  const total = db.prepare(sql.replace('SELECT a.*,c.name as category_name','SELECT COUNT(*) as n')).all(...params)[0]?.n || 0;
  const pages = Math.ceil(total / +limit) || 1;
  sql += ' ORDER BY a.category_id, a.sort_order, a.id DESC LIMIT ? OFFSET ?';
  params.push(+limit, (+page-1)*(+limit));
  res.json({ data: { list: db.prepare(sql).all(...params), total, pages, page: +page } });
});

app.get('/api/admin/help/articles/:id', requirePerm('help:manage'), (req, res) => {
  const art = db.prepare('SELECT * FROM help_articles WHERE id=?').get(req.params.id);
  if (!art) return res.status(404).json({ error: '文章不存在' });
  res.json({ data: art });
});

app.post('/api/admin/help/articles', requirePerm('help:manage'), (req, res) => {
  const { category_id, title, content, excerpt, image, featured, role, published, sort_order } = req.body;
  if (!title) return res.status(400).json({ error: '请填写文章标题' });
  const r = db.prepare(
    'INSERT INTO help_articles (category_id,title,content,excerpt,image,featured,role,published,sort_order) VALUES (?,?,?,?,?,?,?,?,?)'
  ).run(
    category_id||0, title, content||'', excerpt||'', image||'',
    featured?1:0, role||'', published===false?0:1, sort_order||0
  );
  res.json({ success: true, id: r.lastInsertRowid });
});

app.put('/api/admin/help/articles/:id', requirePerm('help:manage'), (req, res) => {
  const { category_id, title, content, excerpt, image, featured, role, published, sort_order } = req.body;
  db.prepare(
    "UPDATE help_articles SET category_id=?,title=?,content=?,excerpt=?,image=?,featured=?,role=?,published=?,sort_order=?,updated_at=datetime('now','localtime') WHERE id=?"
  ).run(
    category_id||0, title, content||'', excerpt||'', image||'',
    featured?1:0, role||'', published===false?0:1, sort_order||0, req.params.id
  );
  res.json({ success: true });
});

app.delete('/api/admin/help/articles/:id', requirePerm('help:manage'), (req, res) => {
  db.prepare('DELETE FROM help_articles WHERE id=?').run(req.params.id);
  res.json({ success: true });
});

/* =========================================================
   后台静态文件服务（隐藏路径）
   访问 /[ADMIN_PATH]/ 才能进入后台
   ========================================================= */
app.use(`/${ADMIN_PATH}`, express.static(path.join(__dirname, 'admin')));

/* 后台 HTML 页面路由（方便客户端路由） */
const adminPages = ['login','index','sitters','kyc','bookings','users','services','reviews','password','help','finance','accounts','messages'];
adminPages.forEach(p => {
  app.get(`/${ADMIN_PATH}/${p}`, (req, res) => {
    res.sendFile(path.join(__dirname, 'admin', `${p}.html`));
  });
  app.get(`/${ADMIN_PATH}/${p}.html`, (req, res) => {
    res.sendFile(path.join(__dirname, 'admin', `${p}.html`));
  });
});

/* ========= 协议签署系统 ========= */

/* GET /api/agreements —— 返回当前协议清单（key/version/title），前端据此渲染查看器 */
app.get('/api/agreements', (req, res) => {
  const list = Object.values(AGREEMENTS).map(a => ({
    key: a.key, version: a.version, title: a.title, url: '/legal/' + a.path
  }));
  res.json({ agreements: list });
});

/* GET /api/agreements/me —— 已登录用户查看自己签过的协议 */
app.get('/api/agreements/me', (req, res) => {
  const m = /^Bearer\s+(.+)$/i.exec(req.headers.authorization || '');
  if (!m) return res.status(401).json({ error: '未登录' });
  let uid;
  try { uid = jwt.verify(m[1], JWT_SECRET).uid; }
  catch (e) { return res.status(401).json({ error: 'token 无效或已过期' }); }

  const rows = db.prepare(`
    SELECT agreement_key, version, content_sha256, signed_at, signed_ip
    FROM user_agreements WHERE user_id=? ORDER BY signed_at DESC
  `).all(uid);

  // 富化一下：补上 title + 是否为当前版本
  const enriched = rows.map(r => {
    const current = AGREEMENTS[r.agreement_key];
    return {
      ...r,
      title: current ? current.title : r.agreement_key,
      url: current ? '/legal/' + current.path : '',
      is_current_version: current ? current.version === r.version : false,
    };
  });
  res.json({ agreements: enriched });
});

/* 辅助：给指定 user_id 批量插入协议签署记录（注册时由 /api/users/register 调用）
   keys: 协议 key 数组（如 ['sitter_commitment','sitter_truthfulness','sitter_welfare']）*/
function signAgreementsForUser(userId, keys, req) {
  const ip = (req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').toString().split(',')[0].trim();
  const ua = String(req.headers['user-agent'] || '').slice(0, 300);
  const stmt = db.prepare(`
    INSERT INTO user_agreements (user_id, agreement_key, version, content_sha256, signed_ip, signed_ua)
    VALUES (?, ?, ?, ?, ?, ?)
  `);
  for (const k of keys) {
    const a = AGREEMENTS[k];
    if (!a) continue;
    stmt.run(userId, k, a.version, a.sha256, ip, ua);
  }
}

/* ==========================================================
   担保交易系统 · Phase A+B · 沙盒支付主流程
   --------------------------------------------------------
   订单状态（order_status）：
     WAIT_PAY → PAID_WAIT_SERVICE → IN_SERVICE →
     WAIT_OWNER_CONFIRM → WAIT_REVIEW → COMPLETED
     任何阶段可转 → CANCELLED
   资金状态（fund_status）：
     UNPAID → PAID_FROZEN → SETTLEMENT_PENDING → SETTLED
     退款路径：UNPAID/PAID_FROZEN → REFUNDED
   金额一律"分"存储（INTEGER），避免浮点误差。
   结算冷静期：T+1（24 小时）
   ========================================================== */
const ORDER_STATUS = {
  WAIT_PAY:           'WAIT_PAY',
  PAID_WAIT_SERVICE:  'PAID_WAIT_SERVICE',
  IN_SERVICE:         'IN_SERVICE',
  WAIT_OWNER_CONFIRM: 'WAIT_OWNER_CONFIRM',
  WAIT_REVIEW:        'WAIT_REVIEW',
  COMPLETED:          'COMPLETED',
  CANCELLED:          'CANCELLED',
  DISPUTE:            'DISPUTE',
};
const FUND_STATUS = {
  UNPAID:             'UNPAID',
  PAID_FROZEN:        'PAID_FROZEN',
  SETTLEMENT_PENDING: 'SETTLEMENT_PENDING',
  SETTLED:            'SETTLED',
  REFUNDED:           'REFUNDED',
  DISPUTE_FROZEN:     'DISPUTE_FROZEN',
};
const ORDER_TRANSITIONS = {
  WAIT_PAY:           [ORDER_STATUS.PAID_WAIT_SERVICE, ORDER_STATUS.CANCELLED],
  PAID_WAIT_SERVICE:  [ORDER_STATUS.IN_SERVICE, ORDER_STATUS.CANCELLED, ORDER_STATUS.DISPUTE],
  IN_SERVICE:         [ORDER_STATUS.WAIT_OWNER_CONFIRM, ORDER_STATUS.CANCELLED, ORDER_STATUS.DISPUTE],
  WAIT_OWNER_CONFIRM: [ORDER_STATUS.WAIT_REVIEW, ORDER_STATUS.CANCELLED, ORDER_STATUS.DISPUTE],
  WAIT_REVIEW:        [ORDER_STATUS.COMPLETED, ORDER_STATUS.DISPUTE],
  COMPLETED:          [],
  CANCELLED:          [],
  DISPUTE:            [ORDER_STATUS.CANCELLED, ORDER_STATUS.WAIT_REVIEW, ORDER_STATUS.COMPLETED],
};
const PAY_TTL_MS         = 15 * 60 * 1000;      // 15 分钟未付款 → 取消
const AUTO_CONFIRM_MS    = 24 * 60 * 60 * 1000; // 服务者完成后 24 小时自动确认
const SETTLEMENT_COOL_MS = 24 * 60 * 60 * 1000; // T+1 冷静期
const DEFAULT_FEE_RATE   = 0.12;                // 平台默认抽成 12%

/* ----- 工具 ----- */
function nowISO() {
  const d = new Date();
  const pad = n => String(n).padStart(2, '0');
  return `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
}
function deltaISO(ms) {
  const d = new Date(Date.now() + ms);
  const pad = n => String(n).padStart(2, '0');
  return `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
}
function genOrderNo() {
  const d = new Date();
  const pad = n => String(n).padStart(2, '0');
  const ts = `${d.getFullYear()}${pad(d.getMonth()+1)}${pad(d.getDate())}${pad(d.getHours())}${pad(d.getMinutes())}${pad(d.getSeconds())}`;
  return `PC${ts}${Math.floor(Math.random()*9000)+1000}`;
}
function genPaymentNo() { return 'PAY' + Date.now() + (Math.floor(Math.random()*9000)+1000); }
function yuanToCents(y) { const n = Number(y); return Number.isFinite(n) ? Math.round(n * 100) : NaN; }
function centsToYuan(c) { return (Number(c || 0) / 100).toFixed(2); }
function safeJSON(s, fb) { try { const v = JSON.parse(s); return v || fb; } catch(e) { return fb; } }

/* ----- 鉴权：从 Bearer token 取当前用户 ----- */
function getUserFromToken(req) {
  const m = /^Bearer\s+(.+)$/i.exec(req.headers.authorization || '');
  if (!m) return null;
  try {
    const payload = jwt.verify(m[1], JWT_SECRET);
    const u = db.prepare('SELECT * FROM users WHERE id=?').get(payload.uid);
    if (!u || u.status !== '正常') return null;
    return u;
  } catch (e) { return null; }
}
function requireUser(req, res) {
  const u = getUserFromToken(req);
  if (!u) { res.status(401).json({ error: '未登录或 token 已过期' }); return null; }
  return u;
}

/* ----- 审计事件 ----- */
function appendOrderEvent(orderId, type, actor, actorRole, content, oldStatus, newStatus) {
  try {
    db.prepare(`
      INSERT INTO booking_events (booking_id, type, actor, actor_role, content, old_status, new_status)
      VALUES (?, ?, ?, ?, ?, ?, ?)
    `).run(orderId, type, actor || 'system', actorRole || 'system', content || '', oldStatus || '', newStatus || '');
  } catch(e) { console.error('appendOrderEvent fail:', e.message); }
}

/* ----- 订单状态迁移（带合法性校验） ----- */
function transitionOrder(orderId, nextOrderStatus, nextFundStatus, extraSQL, extraArgs, actor, actorRole, note) {
  const cur = db.prepare('SELECT order_status, fund_status FROM bookings WHERE id=?').get(orderId);
  if (!cur) return { ok:false, msg:'订单不存在' };
  const allowed = ORDER_TRANSITIONS[cur.order_status] || [];
  if (nextOrderStatus !== cur.order_status && !allowed.includes(nextOrderStatus)) {
    return { ok:false, msg:`订单状态不能从 ${cur.order_status} 变为 ${nextOrderStatus}` };
  }
  const sql = `UPDATE bookings SET order_status=?, fund_status=?, updated_at=?${extraSQL ? ', ' + extraSQL : ''} WHERE id=?`;
  db.prepare(sql).run(nextOrderStatus, nextFundStatus, nowISO(), ...(extraArgs || []), orderId);
  appendOrderEvent(orderId, 'system', actor, actorRole, note || '', cur.order_status, nextOrderStatus);
  return { ok:true };
}

/* ----- 钱包 ----- */
function ensureWallet(sitterUserId) {
  const exists = db.prepare('SELECT sitter_user_id FROM sitter_wallets WHERE sitter_user_id=?').get(sitterUserId);
  if (!exists) db.prepare('INSERT INTO sitter_wallets (sitter_user_id) VALUES (?)').run(sitterUserId);
}
function walletCreditPending(sitterUserId, orderId, amountCents, note) {
  ensureWallet(sitterUserId);
  db.prepare(`UPDATE sitter_wallets SET pending_cents = pending_cents + ?, updated_at=? WHERE sitter_user_id=?`)
    .run(amountCents, nowISO(), sitterUserId);
  const w = db.prepare('SELECT balance_cents, pending_cents FROM sitter_wallets WHERE sitter_user_id=?').get(sitterUserId);
  db.prepare(`
    INSERT INTO wallet_transactions (sitter_user_id, order_id, type, amount_cents, balance_after_cents, pending_after_cents, note)
    VALUES (?, ?, 'PENDING_IN', ?, ?, ?, ?)
  `).run(sitterUserId, orderId, amountCents, w.balance_cents, w.pending_cents, note || '');
}
function walletUnfreeze(sitterUserId, orderId, amountCents, note) {
  ensureWallet(sitterUserId);
  const w0 = db.prepare('SELECT pending_cents FROM sitter_wallets WHERE sitter_user_id=?').get(sitterUserId);
  const take = Math.min(amountCents, w0.pending_cents);
  db.prepare(`
    UPDATE sitter_wallets
    SET pending_cents = pending_cents - ?,
        balance_cents = balance_cents + ?,
        total_earned_cents = total_earned_cents + ?,
        updated_at=?
    WHERE sitter_user_id=?
  `).run(take, take, take, nowISO(), sitterUserId);
  const w = db.prepare('SELECT balance_cents, pending_cents FROM sitter_wallets WHERE sitter_user_id=?').get(sitterUserId);
  db.prepare(`
    INSERT INTO wallet_transactions (sitter_user_id, order_id, type, amount_cents, balance_after_cents, pending_after_cents, note)
    VALUES (?, ?, 'UNFREEZE', ?, ?, ?, ?)
  `).run(sitterUserId, orderId, take, w.balance_cents, w.pending_cents, note || '');
}
/* 从钱包 pending 扣减（争议冻结 / 退款） */
function walletDebitPending(sitterUserId, orderId, amountCents, txType, note) {
  ensureWallet(sitterUserId);
  const w0 = db.prepare('SELECT pending_cents FROM sitter_wallets WHERE sitter_user_id=?').get(sitterUserId);
  const take = Math.min(amountCents, w0.pending_cents);
  if (take <= 0) return;
  db.prepare(`UPDATE sitter_wallets SET pending_cents = pending_cents - ?, updated_at=? WHERE sitter_user_id=?`)
    .run(take, nowISO(), sitterUserId);
  const w = db.prepare('SELECT balance_cents, pending_cents FROM sitter_wallets WHERE sitter_user_id=?').get(sitterUserId);
  db.prepare(`
    INSERT INTO wallet_transactions (sitter_user_id, order_id, type, amount_cents, balance_after_cents, pending_after_cents, note)
    VALUES (?, ?, ?, ?, ?, ?, ?)
  `).run(sitterUserId, orderId, txType || 'DISPUTE_FREEZE', -take, w.balance_cents, w.pending_cents, note || '');
}

/* 从 sitters.id 反查 provider 的 users.id（审核通过后 name 一致） */
function resolveSitterUserId(sitterId) {
  const s = db.prepare('SELECT name FROM sitters WHERE id=?').get(sitterId);
  if (!s) return 0;
  const u = db.prepare("SELECT id FROM users WHERE type='宠物服务者' AND name=? LIMIT 1").get(s.name);
  return u ? u.id : 0;
}

/* ========== 订单 API ========== */

/* POST /api/orders —— 创建订单（登录宠物主人） */
app.post('/api/orders', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  if (u.type !== '宠物主人') return res.status(403).json({ error: '仅宠物主人可下单' });

  let { sitter_id, service_type, start_date, end_date, price_yuan,
        pet_name, pet_id, service_address, note } = req.body || {};

  sitter_id = parseInt(sitter_id, 10) || 0;
  service_type = sanitizeText(service_type, 20);
  start_date   = sanitizeText(start_date, 20);
  if (!sitter_id)    return res.status(400).json({ error: '请选择服务者' });
  if (!service_type) return res.status(400).json({ error: '请选择服务类型' });
  if (!start_date)   return res.status(400).json({ error: '请选择服务开始时间' });

  const totalCents = yuanToCents(price_yuan);
  if (!Number.isFinite(totalCents) || totalCents < 100 || totalCents > 10_000_000) {
    return res.status(400).json({ error: '订单金额需在 ¥1 – ¥100,000 之间' });
  }

  const sitter = db.prepare('SELECT id, name, avatar, status FROM sitters WHERE id=?').get(sitter_id);
  if (!sitter) return res.status(404).json({ error: '服务者不存在' });
  if (sitter.status === '已封禁') return res.status(403).json({ error: '该服务者暂不可接单' });

  const feeRate        = DEFAULT_FEE_RATE;
  const platformFee    = Math.round(totalCents * feeRate);
  const providerIncome = totalCents - platformFee;
  const orderNo        = genOrderNo();
  const payDeadline    = deltaISO(PAY_TTL_MS);

  const r = db.prepare(`
    INSERT INTO bookings
      (sitter_id, sitter_name, sitter_avatar, owner_name, owner_phone,
       pet_name, service_type, note, price, status,
       order_no, user_id, pet_id, service_address,
       total_amount_cents, platform_fee_cents, provider_income_cents, platform_fee_rate,
       order_status, fund_status, pay_deadline, start_date, end_date, updated_at)
    VALUES (?,?,?,?,?, ?,?,?,?,?, ?,?,?,?, ?,?,?,?, ?,?,?,?,?,?)
  `).run(
    sitter.id, sitter.name, sitter.avatar || '', u.name, u.phone,
    sanitizeText(pet_name, 20), service_type, sanitizeText(note, 200),
    Math.round(totalCents / 100), '待付款',
    orderNo, u.id, parseInt(pet_id,10) || 0, sanitizeText(service_address, 100),
    totalCents, platformFee, providerIncome, feeRate,
    ORDER_STATUS.WAIT_PAY, FUND_STATUS.UNPAID, payDeadline,
    start_date, sanitizeText(end_date, 20), nowISO()
  );

  const orderId = r.lastInsertRowid;
  appendOrderEvent(orderId, 'system', u.name, 'owner', '订单已创建', '', ORDER_STATUS.WAIT_PAY);

  res.json({
    success: true,
    order_id: orderId, order_no: orderNo,
    order_status: ORDER_STATUS.WAIT_PAY, fund_status: FUND_STATUS.UNPAID,
    total_amount_yuan:    centsToYuan(totalCents),
    platform_fee_yuan:    centsToYuan(platformFee),
    provider_income_yuan: centsToYuan(providerIncome),
    pay_deadline: payDeadline,
    message: '订单已创建，请在 15 分钟内完成支付'
  });
});

function formatOrderForList(b) {
  return {
    id: b.id, order_no: b.order_no,
    sitter_id: b.sitter_id, sitter_name: b.sitter_name, sitter_avatar: b.sitter_avatar,
    pet_name: b.pet_name, service_type: b.service_type,
    start_date: b.start_date, end_date: b.end_date,
    total_amount_yuan: centsToYuan(b.total_amount_cents || 0),
    order_status: b.order_status, fund_status: b.fund_status,
    pay_deadline: b.pay_deadline, auto_confirm_deadline: b.auto_confirm_deadline,
    wallet_available_at: b.wallet_available_at,
    created_at: b.created_at,
  };
}

/* GET /api/orders/summary —— 我的订单汇总（用于"我的订单"页顶部统计 + 服务者自检） */
app.get('/api/orders/summary', (req, res) => {
  const u = requireUser(req, res); if (!u) return;

  // 本月起始 ISO（YYYY-MM-01 00:00:00）
  const now = new Date();
  const monthStart = new Date(now.getFullYear(), now.getMonth(), 1).toISOString();

  if (u.type === '宠物主人') {
    const totalRow      = db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE user_id=?`).get(u.id);
    const waitPayRow    = db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE user_id=? AND order_status='WAIT_PAY'`).get(u.id);
    const inProgressRow = db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE user_id=? AND order_status IN ('PAID_WAIT_SERVICE','IN_SERVICE','WAIT_OWNER_CONFIRM')`).get(u.id);
    const completedRow  = db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE user_id=? AND order_status='COMPLETED'`).get(u.id);
    const waitReviewRow = db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE user_id=? AND order_status='WAIT_REVIEW'`).get(u.id);
    const spentRow      = db.prepare(`SELECT COALESCE(SUM(total_amount_cents),0) AS s FROM bookings WHERE user_id=? AND order_status NOT IN ('CANCELLED','WAIT_PAY')`).get(u.id);
    return res.json({
      role: 'owner',
      stats: {
        total_orders:       totalRow.c,
        wait_pay_count:     waitPayRow.c,
        in_progress_count:  inProgressRow.c,
        wait_review_count:  waitReviewRow.c,
        completed_count:    completedRow.c,
        total_spent_yuan:   centsToYuan(spentRow.s),
      },
    });
  }

  if (u.type === '宠物服务者') {
    const sitterRow = db.prepare('SELECT * FROM sitters WHERE name=?').get(u.name);
    const sitterId = sitterRow ? sitterRow.id : 0;

    const totalRow         = sitterId ? db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE sitter_id=?`).get(sitterId) : { c: 0 };
    const completedRow     = sitterId ? db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE sitter_id=? AND order_status='COMPLETED'`).get(sitterId) : { c: 0 };
    const waitServiceRow   = sitterId ? db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE sitter_id=? AND order_status='PAID_WAIT_SERVICE'`).get(sitterId) : { c: 0 };
    const inServiceRow     = sitterId ? db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE sitter_id=? AND order_status='IN_SERVICE'`).get(sitterId) : { c: 0 };
    const waitConfirmRow   = sitterId ? db.prepare(`SELECT COUNT(*) AS c FROM bookings WHERE sitter_id=? AND order_status='WAIT_OWNER_CONFIRM'`).get(sitterId) : { c: 0 };
    const monthIncomeRow   = sitterId ? db.prepare(`SELECT COALESCE(SUM(provider_income_cents),0) AS s FROM bookings WHERE sitter_id=? AND order_status='COMPLETED' AND owner_confirmed_at >= ?`).get(sitterId, monthStart) : { s: 0 };
    const pendingSettleRow = sitterId ? db.prepare(`SELECT COALESCE(SUM(provider_income_cents),0) AS s FROM bookings WHERE sitter_id=? AND fund_status='SETTLEMENT_PENDING'`).get(sitterId) : { s: 0 };

    // 服务者自检（用于空状态诊断）
    let services_count = 0;
    if (sitterRow) {
      try { services_count = (JSON.parse(sitterRow.services || '[]') || []).length; } catch (_) {}
    }
    let photos_count = 0;
    if (sitterRow) {
      try { photos_count = (JSON.parse(sitterRow.photos || '[]') || []).length; } catch (_) {}
    }

    return res.json({
      role: 'sitter',
      stats: {
        total_orders:            totalRow.c,
        completed_count:         completedRow.c,
        wait_service_count:      waitServiceRow.c,
        in_service_count:        inServiceRow.c,
        wait_confirm_count:      waitConfirmRow.c,
        month_income_yuan:       centsToYuan(monthIncomeRow.s),
        pending_settlement_yuan: centsToYuan(pendingSettleRow.s),
        avg_rating:              sitterRow ? (sitterRow.rating || 0) : 0,
        review_count:            sitterRow ? (sitterRow.review_count || 0) : 0,
      },
      sitter_status: {
        kyc_status:        u.kyc_status || 'basic',
        has_sitter_profile: !!sitterRow,
        listing_status:    sitterRow ? (sitterRow.status || '下线') : '未上架',
        services_count,
        photos_count,
        has_bio:           !!(sitterRow && sitterRow.bio && sitterRow.bio.length >= 10),
        has_avatar:        !!(sitterRow && sitterRow.avatar),
      },
    });
  }

  res.status(403).json({ error: '无权访问' });
});

/* GET /api/orders —— 当前用户的订单列表（owner 看自己下的；sitter 看被指派的） */
app.get('/api/orders', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  const status = sanitizeText(req.query.status || '', 30);
  let rows;
  if (u.type === '宠物主人') {
    rows = db.prepare(`
      SELECT * FROM bookings WHERE user_id=? ${status ? 'AND order_status=?' : ''}
      ORDER BY id DESC LIMIT 100
    `).all(...(status ? [u.id, status] : [u.id]));
  } else if (u.type === '宠物服务者') {
    rows = db.prepare(`
      SELECT b.* FROM bookings b
      JOIN sitters s ON s.id = b.sitter_id
      WHERE s.name = ? ${status ? 'AND b.order_status=?' : ''}
      ORDER BY b.id DESC LIMIT 100
    `).all(...(status ? [u.name, status] : [u.name]));
  } else {
    return res.status(403).json({ error: '无权访问' });
  }
  res.json({ orders: rows.map(formatOrderForList) });
});

/* GET /api/orders/:id —— 订单详情 + 事件 + 支付 + 结算 */
app.get('/api/orders/:id', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  const isOwner  = u.type === '宠物主人' && b.user_id === u.id;
  const sName    = db.prepare('SELECT name FROM sitters WHERE id=?').get(b.sitter_id)?.name;
  const isSitter = u.type === '宠物服务者' && sName === u.name;
  if (!isOwner && !isSitter) return res.status(403).json({ error: '无权访问此订单' });

  const events = db.prepare(
    'SELECT type, actor, actor_role, content, old_status, new_status, created_at FROM booking_events WHERE booking_id=? ORDER BY id ASC'
  ).all(id);
  const payments = db.prepare(
    'SELECT payment_no, pay_channel, amount_cents, status, paid_at, refund_amount_cents, refund_status, created_at FROM payments WHERE order_id=? ORDER BY id DESC'
  ).all(id);
  const settlement = db.prepare('SELECT * FROM settlements WHERE order_id=?').get(id);
  const disputes = db.prepare('SELECT * FROM disputes WHERE order_id=? ORDER BY id DESC').all(id);

  res.json({
    order: {
      ...b,
      total_amount_yuan:    centsToYuan(b.total_amount_cents || 0),
      platform_fee_yuan:    centsToYuan(b.platform_fee_cents || 0),
      provider_income_yuan: centsToYuan(b.provider_income_cents || 0),
      complete_images: safeJSON(b.complete_images, []),
      role: isOwner ? 'owner' : 'sitter',
    },
    events,
    payments: payments.map(p => ({
      ...p,
      amount_yuan: centsToYuan(p.amount_cents),
      refund_amount_yuan: centsToYuan(p.refund_amount_cents || 0),
    })),
    settlement: settlement ? {
      ...settlement,
      settlement_amount_yuan: centsToYuan(settlement.settlement_amount_cents),
      platform_fee_yuan:      centsToYuan(settlement.platform_fee_cents),
    } : null,
    disputes: disputes.map(d => ({
      ...d,
      evidence_images: safeJSON(d.evidence_images, []),
      resolved_amount_yuan: centsToYuan(d.resolved_amount_cents || 0),
    })),
  });
});

/* POST /api/orders/:id/mock-pay —— 沙盒支付回调（幂等） */
app.post('/api/orders/:id/mock-pay', (req, res) => {
  if (!ALLOW_MOCK_PAYMENTS) {
    return res.status(404).json({ error: '沙盒支付未启用' });
  }
  const u = requireUser(req, res); if (!u) return;
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  if (b.user_id !== u.id) return res.status(403).json({ error: '只能支付自己的订单' });

  // 幂等：已支付 → 直接返回
  if (b.fund_status === FUND_STATUS.PAID_FROZEN) {
    return res.json({ success:true, message:'订单已支付（幂等）', order_status: b.order_status, fund_status: b.fund_status });
  }
  if (b.order_status !== ORDER_STATUS.WAIT_PAY) {
    return res.status(400).json({ error: `订单当前状态 ${b.order_status}，不能支付` });
  }
  if (b.pay_deadline && b.pay_deadline < nowISO()) {
    return res.status(400).json({ error: '订单已超时，请重新下单' });
  }

  const idemKey = sanitizeText(req.body?.idempotency_key || ('mock-' + id + '-' + u.id), 80);

  db.exec('BEGIN');
  try {
    const existing = db.prepare("SELECT * FROM payments WHERE idempotency_key=? AND idempotency_key!=''").get(idemKey);
    if (existing && existing.order_id === id) {
      db.exec('ROLLBACK');
      return res.json({ success:true, message:'重复请求已忽略（幂等命中）', payment_no: existing.payment_no });
    }
    const paymentNo = genPaymentNo();
    const txnId     = 'MOCK' + Date.now() + Math.floor(Math.random()*10000);
    db.prepare(`
      INSERT INTO payments (payment_no, order_id, pay_channel, amount_cents, status, transaction_id, idempotency_key, paid_at)
      VALUES (?, ?, 'mock', ?, 'PAID', ?, ?, ?)
    `).run(paymentNo, id, b.total_amount_cents, txnId, idemKey, nowISO());

    const r = transitionOrder(id, ORDER_STATUS.PAID_WAIT_SERVICE, FUND_STATUS.PAID_FROZEN,
      '', [], u.name, 'owner', `沙盒支付成功（${paymentNo}）`);
    if (!r.ok) throw new Error(r.msg);

    db.exec('COMMIT');
    res.json({
      success: true, message: '支付成功，资金已冻结', payment_no: paymentNo,
      order_status: ORDER_STATUS.PAID_WAIT_SERVICE, fund_status: FUND_STATUS.PAID_FROZEN,
    });
  } catch (e) {
    try { db.exec('ROLLBACK'); } catch(_) {}
    res.status(500).json({ error: '支付失败：' + e.message });
  }
});

/* POST /api/orders/:id/start-service —— 服务者开始服务 */
app.post('/api/orders/:id/start-service', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  if (u.type !== '宠物服务者') return res.status(403).json({ error: '仅服务者可操作' });
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  const s = db.prepare('SELECT name FROM sitters WHERE id=?').get(b.sitter_id);
  if (!s || s.name !== u.name) return res.status(403).json({ error: '不是本订单的服务者' });
  if (b.order_status !== ORDER_STATUS.PAID_WAIT_SERVICE) {
    return res.status(400).json({ error: `订单当前状态 ${b.order_status}，不能开始服务` });
  }
  const r = transitionOrder(id, ORDER_STATUS.IN_SERVICE, b.fund_status,
    'service_started_at=?', [nowISO()], u.name, 'sitter', '服务者已开始服务');
  if (!r.ok) return res.status(400).json({ error: r.msg });
  res.json({ success: true, message: '服务已开始', order_status: ORDER_STATUS.IN_SERVICE });
});

/* POST /api/orders/:id/complete-service —— 服务者完成服务（必须有备注或图片） */
app.post('/api/orders/:id/complete-service', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  if (u.type !== '宠物服务者') return res.status(403).json({ error: '仅服务者可操作' });
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  const s = db.prepare('SELECT name FROM sitters WHERE id=?').get(b.sitter_id);
  if (!s || s.name !== u.name) return res.status(403).json({ error: '不是本订单的服务者' });
  if (b.order_status !== ORDER_STATUS.IN_SERVICE) {
    return res.status(400).json({ error: `订单当前状态 ${b.order_status}，不能完成服务` });
  }

  const note = sanitizeText(req.body?.complete_note || '', 300);
  const imgs = Array.isArray(req.body?.complete_images)
    ? req.body.complete_images.map(i => validImage(i, 1_500_000)).filter(Boolean).slice(0, 6)
    : [];
  if (!note && imgs.length === 0) {
    return res.status(400).json({ error: '请填写完成备注或上传至少 1 张服务记录图片' });
  }

  const autoConfirmAt = deltaISO(AUTO_CONFIRM_MS);
  const r = transitionOrder(id, ORDER_STATUS.WAIT_OWNER_CONFIRM, b.fund_status,
    'service_completed_at=?, complete_note=?, complete_images=?, auto_confirm_deadline=?',
    [nowISO(), note, JSON.stringify(imgs), autoConfirmAt],
    u.name, 'sitter', '服务者已提交完成，等待主人确认');
  if (!r.ok) return res.status(400).json({ error: r.msg });

  res.json({
    success: true, message: '已提交完成，等待主人确认（24 小时后自动确认）',
    order_status: ORDER_STATUS.WAIT_OWNER_CONFIRM, auto_confirm_deadline: autoConfirmAt,
  });
});

/* 主人确认 / 超时自动确认 的公共逻辑（事务内）
   → WAIT_OWNER_CONFIRM → WAIT_REVIEW
   → PAID_FROZEN → SETTLEMENT_PENDING
   → 创建 settlement
   → 钱包 pending += provider_income（T+1 后解冻） */
function ownerConfirmInternal(b, actor, actorRole, note) {
  const sitterUserId = resolveSitterUserId(b.sitter_id);
  if (!sitterUserId) return { ok:false, msg:'无法定位服务者用户账号（sitters 表 name 与 users.name 不一致）' };

  const availableAt = deltaISO(SETTLEMENT_COOL_MS);
  db.exec('BEGIN');
  try {
    const r = transitionOrder(b.id, ORDER_STATUS.WAIT_REVIEW, FUND_STATUS.SETTLEMENT_PENDING,
      'owner_confirmed_at=?, wallet_available_at=?',
      [nowISO(), availableAt],
      actor, actorRole, note);
    if (!r.ok) throw new Error(r.msg);

    db.prepare(`
      INSERT INTO settlements (order_id, provider_id, settlement_amount_cents, platform_fee_cents, status, available_at)
      VALUES (?, ?, ?, ?, 'PENDING', ?)
    `).run(b.id, sitterUserId, b.provider_income_cents, b.platform_fee_cents, availableAt);

    walletCreditPending(sitterUserId, b.id, b.provider_income_cents,
      `订单 ${b.order_no || b.id} 结算待解冻 ¥${centsToYuan(b.provider_income_cents)}`);

    db.exec('COMMIT');
    return { ok:true };
  } catch(e) {
    try { db.exec('ROLLBACK'); } catch(_) {}
    return { ok:false, msg: e.message };
  }
}

/* POST /api/orders/:id/confirm —— 主人确认完成 */
app.post('/api/orders/:id/confirm', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  if (u.type !== '宠物主人') return res.status(403).json({ error: '仅宠物主人可确认' });
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  if (b.user_id !== u.id) return res.status(403).json({ error: '只能确认自己的订单' });
  if (b.order_status !== ORDER_STATUS.WAIT_OWNER_CONFIRM) {
    return res.status(400).json({ error: `订单当前状态 ${b.order_status}，不能确认` });
  }
  const r = ownerConfirmInternal(b, u.name, 'owner', '主人手动确认服务完成');
  if (!r.ok) return res.status(400).json({ error: r.msg });
  res.json({
    success: true, message: '已确认完成，结算进入 24 小时冷静期（T+1 后到账）',
    order_status: ORDER_STATUS.WAIT_REVIEW, fund_status: FUND_STATUS.SETTLEMENT_PENDING,
  });
});

/* POST /api/orders/:id/review —— 主人评价（可 skip：稍后评价） */
app.post('/api/orders/:id/review', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  if (u.type !== '宠物主人') return res.status(403).json({ error: '仅宠物主人可评价' });
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  if (b.user_id !== u.id) return res.status(403).json({ error: '只能评价自己的订单' });
  if (b.order_status !== ORDER_STATUS.WAIT_REVIEW && b.order_status !== ORDER_STATUS.COMPLETED) {
    return res.status(400).json({ error: `订单当前状态 ${b.order_status}，不能评价` });
  }

  const skip    = !!req.body?.skip;
  const rating  = Math.max(1, Math.min(5, parseInt(req.body?.rating, 10) || 5));
  const content = sanitizeText(req.body?.content || '', 500);
  const tags    = Array.isArray(req.body?.tags) ? sanitizeArray(req.body.tags, 8, 20) : [];
  const images  = Array.isArray(req.body?.images)
    ? req.body.images.map(i => validImage(i, 1_500_000)).filter(Boolean).slice(0, 6) : [];

  db.exec('BEGIN');
  try {
    if (!skip) {
      db.prepare(`
        INSERT INTO reviews (sitter_id, user_name, avatar, review_text, rating, pet_type, service, booking_id, user_id, tags, images)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
      `).run(b.sitter_id, u.name, u.avatar || '', content, rating, b.pet_name || '', b.service_type || '',
             b.id, u.id, JSON.stringify(tags), JSON.stringify(images));
    }
    if (b.order_status === ORDER_STATUS.WAIT_REVIEW) {
      const r = transitionOrder(b.id, ORDER_STATUS.COMPLETED, b.fund_status, '', [], u.name, 'owner',
        skip ? '主人选择稍后评价' : '主人已提交评价');
      if (!r.ok) throw new Error(r.msg);
    }
    db.exec('COMMIT');
    res.json({ success:true, message: skip ? '已跳过评价，可在 7 天内补充' : '评价成功，感谢反馈！', order_status: ORDER_STATUS.COMPLETED });
  } catch(e) {
    try { db.exec('ROLLBACK'); } catch(_) {}
    res.status(500).json({ error: e.message });
  }
});

/* POST /api/orders/:id/cancel —— 仅服务开始前可取消（用户 / 服务者） */
app.post('/api/orders/:id/cancel', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });
  const isOwner  = u.type === '宠物主人' && b.user_id === u.id;
  const sName    = db.prepare('SELECT name FROM sitters WHERE id=?').get(b.sitter_id)?.name;
  const isSitter = u.type === '宠物服务者' && sName === u.name;
  if (!isOwner && !isSitter) return res.status(403).json({ error: '无权取消此订单' });

  if ([ORDER_STATUS.IN_SERVICE, ORDER_STATUS.WAIT_OWNER_CONFIRM, ORDER_STATUS.WAIT_REVIEW, ORDER_STATUS.COMPLETED].includes(b.order_status)) {
    return res.status(400).json({ error: '服务已开始，请改走售后 / 争议流程' });
  }
  if (b.order_status === ORDER_STATUS.CANCELLED) {
    return res.json({ success:true, message:'订单已取消（幂等）' });
  }

  const reason = sanitizeText(req.body?.reason || (isOwner ? '主人取消' : '服务者取消'), 100);
  const refund = (b.fund_status === FUND_STATUS.PAID_FROZEN);

  db.exec('BEGIN');
  try {
    const r = transitionOrder(b.id, ORDER_STATUS.CANCELLED, refund ? FUND_STATUS.REFUNDED : FUND_STATUS.UNPAID,
      'cancel_reason=?, cancelled_at=?', [reason, nowISO()],
      u.name, isOwner ? 'owner' : 'sitter',
      refund ? `已退款：${reason}` : `取消：${reason}`);
    if (!r.ok) throw new Error(r.msg);

    if (refund) {
      db.prepare(`
        UPDATE payments
        SET refund_amount_cents = amount_cents, refund_status = 'REFUNDED', refunded_at = ?
        WHERE order_id = ? AND status = 'PAID'
      `).run(nowISO(), b.id);
    }
    db.exec('COMMIT');
    res.json({ success:true, message: refund ? '订单已取消，沙盒支付已全额退款' : '订单已取消' });
  } catch(e) {
    try { db.exec('ROLLBACK'); } catch(_) {}
    res.status(500).json({ error: e.message });
  }
});

/* POST /api/orders/:id/dispute —— 发起争议 / 售后（主人或服务者均可）
   可发起状态：PAID_WAIT_SERVICE, IN_SERVICE, WAIT_OWNER_CONFIRM, WAIT_REVIEW
   效果：订单 → DISPUTE，资金 → DISPUTE_FROZEN
   若处于 SETTLEMENT_PENDING（WAIT_REVIEW）：从钱包 pending 扣回 provider_income，避免 T+1 自动解冻 */
app.post('/api/orders/:id/dispute', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  const id = parseInt(req.params.id, 10);
  const b = db.prepare('SELECT * FROM bookings WHERE id=?').get(id);
  if (!b) return res.status(404).json({ error: '订单不存在' });

  const isOwner  = u.type === '宠物主人' && b.user_id === u.id;
  const sName    = db.prepare('SELECT name FROM sitters WHERE id=?').get(b.sitter_id)?.name;
  const isSitter = u.type === '宠物服务者' && sName === u.name;
  if (!isOwner && !isSitter) return res.status(403).json({ error: '无权对此订单发起争议' });

  const eligible = [
    ORDER_STATUS.PAID_WAIT_SERVICE,
    ORDER_STATUS.IN_SERVICE,
    ORDER_STATUS.WAIT_OWNER_CONFIRM,
    ORDER_STATUS.WAIT_REVIEW,
  ];
  if (!eligible.includes(b.order_status)) {
    return res.status(400).json({ error: `当前状态 ${b.order_status} 不能发起售后` });
  }

  // 一单一争议：若已有 OPEN 争议，返回
  const existing = db.prepare("SELECT id FROM disputes WHERE order_id=? AND status='OPEN'").get(id);
  if (existing) return res.status(400).json({ error: '该订单已有待处理的争议，请勿重复提交' });

  const reason = sanitizeText(req.body?.reason || '', 50);
  const description = sanitizeText(req.body?.description || '', 500);
  if (!reason && !description) return res.status(400).json({ error: '请填写争议原因或详情' });
  const images = Array.isArray(req.body?.images)
    ? req.body.images.map(i => validImage(i, 1_500_000)).filter(Boolean).slice(0, 6)
    : [];

  const sitterUserId = resolveSitterUserId(b.sitter_id);
  const wasSettlementPending = (b.fund_status === FUND_STATUS.SETTLEMENT_PENDING);

  db.exec('BEGIN');
  try {
    // 订单迁移至 DISPUTE + 资金冻结
    const r = transitionOrder(id, ORDER_STATUS.DISPUTE, FUND_STATUS.DISPUTE_FROZEN,
      '', [], u.name, isOwner ? 'owner' : 'sitter',
      `${isOwner ? '主人' : '服务者'}发起争议：${reason || '（未选原因）'}`);
    if (!r.ok) throw new Error(r.msg);

    // 若资金已在冷静期（WAIT_REVIEW），从服务者钱包 pending 扣回
    if (wasSettlementPending && sitterUserId) {
      walletDebitPending(sitterUserId, id, b.provider_income_cents || 0, 'DISPUTE_FREEZE',
        `订单 ${b.order_no || id} 因争议暂时冻结 ¥${centsToYuan(b.provider_income_cents || 0)}`);
      db.prepare("UPDATE settlements SET status='FROZEN', updated_at=? WHERE order_id=?")
        .run(nowISO(), id);
    }

    // 写入 disputes 记录
    db.prepare(`
      INSERT INTO disputes (order_id, user_id, provider_id, reason, description, evidence_images, status)
      VALUES (?, ?, ?, ?, ?, ?, 'OPEN')
    `).run(id, b.user_id, sitterUserId || 0, reason, description, JSON.stringify(images));

    db.exec('COMMIT');
    res.json({
      success: true,
      message: '争议已提交，平台将在 1-3 个工作日内介入处理',
      order_status: ORDER_STATUS.DISPUTE,
      fund_status: FUND_STATUS.DISPUTE_FROZEN,
    });
  } catch(e) {
    try { db.exec('ROLLBACK'); } catch(_) {}
    res.status(500).json({ error: e.message });
  }
});

/* GET /api/wallet/me —— 服务者钱包（余额 + 冷静期 + 最近 50 条流水） */
app.get('/api/wallet/me', (req, res) => {
  const u = requireUser(req, res); if (!u) return;
  if (u.type !== '宠物服务者') return res.status(403).json({ error: '仅服务者有钱包' });
  ensureWallet(u.id);
  const w = db.prepare('SELECT * FROM sitter_wallets WHERE sitter_user_id=?').get(u.id);
  const txs = db.prepare(`
    SELECT id, order_id, type, amount_cents, balance_after_cents, pending_after_cents, note, created_at
    FROM wallet_transactions WHERE sitter_user_id=? ORDER BY id DESC LIMIT 50
  `).all(u.id);
  res.json({
    balance_yuan:         centsToYuan(w.balance_cents),
    pending_yuan:         centsToYuan(w.pending_cents),
    total_earned_yuan:    centsToYuan(w.total_earned_cents),
    total_withdrawn_yuan: centsToYuan(w.total_withdrawn_cents),
    transactions: txs.map(t => ({ ...t, amount_yuan: centsToYuan(t.amount_cents) })),
  });
});

/* ========== 定时调度器（每 60 秒） ==========
   1) WAIT_PAY 超 pay_deadline → CANCELLED
   2) WAIT_OWNER_CONFIRM 超 auto_confirm_deadline → 自动 ownerConfirmInternal
   3) SETTLEMENT_PENDING 超 wallet_available_at → SETTLED + 钱包解冻
*/
function runOrderScheduler() {
  const now = nowISO();
  try {
    // 1) 支付超时
    const expiredPays = db.prepare(`
      SELECT id FROM bookings
      WHERE order_status=? AND pay_deadline != '' AND pay_deadline < ?
    `).all(ORDER_STATUS.WAIT_PAY, now);
    for (const row of expiredPays) {
      transitionOrder(row.id, ORDER_STATUS.CANCELLED, FUND_STATUS.UNPAID,
        'cancel_reason=?, cancelled_at=?', ['支付超时自动取消', now],
        'system', 'system', '15 分钟未支付，系统自动取消');
    }
    if (expiredPays.length) console.log(`⏰ 自动取消 ${expiredPays.length} 个超时未付款订单`);

    // 2) 待主人确认超时
    const expiredConfirms = db.prepare(`
      SELECT * FROM bookings
      WHERE order_status=? AND auto_confirm_deadline != '' AND auto_confirm_deadline < ?
    `).all(ORDER_STATUS.WAIT_OWNER_CONFIRM, now);
    for (const b of expiredConfirms) {
      ownerConfirmInternal(b, 'system', 'system', '主人 24 小时未确认，系统自动确认');
    }
    if (expiredConfirms.length) console.log(`⏰ 自动确认 ${expiredConfirms.length} 个订单`);

    // 3) 冷静期结束 → 结算
    const expiredCool = db.prepare(`
      SELECT b.id, b.provider_income_cents, b.order_no, s.provider_id
      FROM bookings b
      LEFT JOIN settlements s ON s.order_id = b.id
      WHERE b.fund_status=? AND b.wallet_available_at != '' AND b.wallet_available_at < ?
    `).all(FUND_STATUS.SETTLEMENT_PENDING, now);
    for (const row of expiredCool) {
      if (!row.provider_id) continue;
      db.exec('BEGIN');
      try {
        walletUnfreeze(row.provider_id, row.id, row.provider_income_cents,
          `订单 ${row.order_no || row.id} T+1 冷静期结束，解冻`);
        db.prepare("UPDATE settlements SET status='SETTLED', settled_at=?, updated_at=? WHERE order_id=?")
          .run(nowISO(), nowISO(), row.id);
        db.prepare('UPDATE bookings SET fund_status=?, settled_at=?, updated_at=? WHERE id=?')
          .run(FUND_STATUS.SETTLED, nowISO(), nowISO(), row.id);
        appendOrderEvent(row.id, 'system', 'system', 'system', 'T+1 冷静期结束，结算完成',
          FUND_STATUS.SETTLEMENT_PENDING, FUND_STATUS.SETTLED);
        db.exec('COMMIT');
      } catch(e) {
        try { db.exec('ROLLBACK'); } catch(_) {}
        db.prepare("UPDATE settlements SET status='FAILED', fail_reason=?, retry_count=retry_count+1, updated_at=? WHERE order_id=?")
          .run(String(e.message).slice(0, 200), nowISO(), row.id);
        console.error('结算失败 order=' + row.id, e.message);
      }
    }
    if (expiredCool.length) console.log(`💰 结算完成 ${expiredCool.length} 个订单`);
  } catch(e) {
    console.error('runOrderScheduler 异常：', e.message);
  }
}
setTimeout(runOrderScheduler, 5_000);
setInterval(runOrderScheduler, 60_000);
console.log('⏰ 担保交易调度器已启动（每 60 秒扫描一次）');

/* 后台根路径重定向到登录 */
app.get(`/${ADMIN_PATH}`, (req, res) => {
  res.redirect(`/${ADMIN_PATH}/login`);
});

/* ── 前台 SPA 回退 ── */
app.get('*', (req, res) => {
  if (req.path.startsWith('/api') || req.path.startsWith('/'+ADMIN_PATH) || path.extname(req.path)) {
    return res.status(404).send('Not found');
  }
  res.sendFile(path.join(__dirname, 'public', 'index.html'));
});

/* ── 启动 ── */
app.listen(PORT, () => {
  console.log('\n🐾 爪小爱服务平台已启动！');
  console.log(`\n   前台地址：http://localhost:${PORT}`);
  console.log(`   管理后台：http://localhost:${PORT}/${ADMIN_PATH}/login`);
  console.log(`\n   注意：管理后台地址请保密，不要对外公开\n`);
});

module.exports = app;
