script_name('AutoToch')
script_author('Claude')
script_version('1.6')
script_description('Авто-заточка аксессуаров Arizona RP до целевого уровня (/toch)')

-- ВАЖНО: сохраняйте файл в кодировке UTF-8.
-- Требуются: MoonLoader, mimgui, SAMP.Lua (lib.samp.events), encoding.

require 'lib.moonloader'
local imgui    = require 'mimgui'
local encoding = require 'encoding'
local sampev   = require 'lib.samp.events'
local ffi      = require 'ffi'

encoding.default = 'CP1251'
local u8 = encoding.UTF8

-- Исходник в UTF-8 и mimgui тоже принимает UTF-8, поэтому для интерфейса
-- перекодировка не нужна (u8() нужен только для чата и серверных сообщений).
local function ui(s) return s end

------------------------------------------------------------------------
-- НАСТРОЙКИ
------------------------------------------------------------------------
local TARGET_LEVEL   = 12      -- до какого уровня точим (можно менять: /toch_level 10)
local START_DELAY    = 800     -- пауза перед первым кликом после старта, мс
local CLICK_DELAY    = 500     -- пауза: положил аксессуар -> кладу камень, мс
local BUTTON_DELAY   = 500     -- пауза: положил камень -> жму "Заточить предмет", мс
local CYCLE_DELAY    = 1200    -- пауза после результата до следующей попытки, мс
local DELAY_JITTER   = 150     -- случайная добавка к каждой паузе (0..N мс)
local RESULT_TIMEOUT = 10000   -- сколько ждать ответ после попытки, мс. Если за это время ничего не произошло -
                               -- считаем, что слоты пустые / не хватило ресурса, и переставляем предмет и камни
local CLICK_RETRY_MS  = 3000   -- если за это время нет ответа, ПОВТОРНО жмём "Заточить" (клик мог проигнорироваться
                               -- из-за анимации), и только потом переставляем предмет и камни
local CLICK_RETRIES   = 2      -- сколько раз повторять клик до переустановки
local MAX_TIMEOUTS   = 3       -- сколько раз подряд "ничего не произошло" допускаем до остановки
local SCAN_WINDOW    = 2500    -- сколько слушать инвентарь после /stats, мс
local FLASH_DURATION = 1.6     -- длительность зелёной вспышки, сек
local STATS_COMMAND  = '/stats'

local CFG_DIR   = getWorkingDirectory() .. '\\config'
local CFG_PATH  = CFG_DIR .. '\\auto_toch.json'
local DUMP_PATH = CFG_DIR .. '\\auto_toch_dump.txt'

-- Ключевые слова (регистр не важен)
local ACCESSORY_KEYWORDS = {
    'лавка', 'аксессуар', 'очки', 'маска', 'часы', 'рюкзак', 'шляпа', 'кепка',
    'бандана', 'кольцо', 'ожерелье', 'цепь', 'серьга', 'перчатки', 'сумка',
    'наушники', 'значок', 'брелок', 'крылья', 'ремень', 'галстук', 'платок',
    'шапка', 'браслет', 'кулон', 'медальон',
}
-- Предметы, которые точно не аксессуары (даже если в названии есть "маска" или "+1")
local NOT_ACCESSORY_KEYWORDS = {
    'тайник', 'талон', 'сертификат', 'контейнер', 'осколок', 'осколки',
    'хрономонета', 'печать', 'номер на', 'iphone', 'az coins', 'обрез',
}
local STONE_KEYWORDS  = { 'точильный камень' }
local AMULET_KEYWORDS = { 'точильный амулет' }
-- Супер-заточка: отдельный предмет, кладётся в ячейку "Супер-заточка" верстака вместе с камнем/амулетом
local SUPER_KEYWORDS  = { 'супер-заточ', 'супер заточ', 'суперзаточ' }
local SUPER_MIN_LEVEL = 12   -- супер-заточку можно применять только к аксессуару с уровнем +12 и выше (попытки на +13 и дальше)
local SUPER_PER_ATTEMPT = 1  -- сколько штук супер-заточки уходит за одну попытку (для учёта остатка)
local SUPER_MAX_LEVEL = 14   -- максимальная заточка в игре
local SUPER_FAIL_DROP = 1    -- на сколько падает уровень, если супер-заточка не сработала (+12 -> +11)
-- Сообщения сервера, после которых продолжать нет смысла (проверяются только пока ждём результат заточки)
-- предмет уже на максимальном уровне: пропускаем его и идём дальше по очереди
local ITEM_MAX_KEYWORDS  = { 'максимальный уровень' }
local HARD_STOP_KEYWORDS = { 'недостаточно денег', 'недостаточно средств',
                             'не хватает денег', 'не хватает средств', 'нет денег' }
-- Сообщения "не хватает / нет": скрипт пробует заново поставить предмет и камни (авто-пополнение)
local RESTOCK_KEYWORDS   = { 'недостаточно', 'у вас нет', 'не хватает' }

------------------------------------------------------------------------
-- СОСТОЯНИЕ
------------------------------------------------------------------------
local S = {
    items     = {},     -- [slot] = {slot, id, name, amount}
    queue     = {},     -- очередь заточки: список слотов аксессуаров (порядок = порядок клика)
    qIndex    = 0,      -- номер текущего предмета в очереди
    qTotal    = 0,      -- сколько предметов было в очереди на старте
    curSlot   = nil,    -- слот предмета, который точим сейчас
    targetReached = false,
    itemMax   = false,
    skip      = false,
    runSuper  = false,  -- в текущем запуске включена супер-заточка
    updCef    = false,  -- окно обновления рисовать через CEF (/toch_cef)
    runTarget = nil,    -- цель текущего запуска
    manualSuper = nil,  -- ручной слот супер-заточки
    resource  = nil,    -- 'stone' | 'amulet'
    running   = false,
    scanning  = false,
    level     = 0,
    attempts  = 0,
    okCount   = 0,
    failCount = 0,
    result    = nil,    -- {ok=bool, from=n, to=n}
    flashUntil = 0,
    flashText  = '',
    learn     = nil,    -- шаг обучения 1..3
    sending   = false,
    debug     = false,
}

local cfg = { tmplItem = nil, tmplRes = nil, button = nil }

local new, str, sizeof = imgui.new, ffi.string, ffi.sizeof
local winMain  = new.bool(false)
local winRes   = new.bool(false)
local searchBuf = new.char[64]()
local showAll  = new.bool(true)
local manualBuf = new.int(-1)   -- ручной слот ресурса (-1 = не использовать)
local superChk  = new.bool(false) -- галочка "Точить до +N с супер-заточкой"
local superBuf  = new.int(14)     -- цель +N в режиме супер-заточки
local manualSuperBuf = new.int(-1) -- ручной слот супер-заточки (-1 = искать по названию)

-- Цель заточки: во время запуска - зафиксированная при старте, иначе по текущим настройкам
local function currentTarget()
    if S.running and S.runTarget then return S.runTarget end
    return superChk[0] and superBuf[0] or TARGET_LEVEL
end

------------------------------------------------------------------------
-- УТИЛИТЫ
------------------------------------------------------------------------
local function chat(msg)
    sampAddChatMessage(u8:decode('{FFD700}[AUTO TOCH]{FFFFFF} ' .. msg), -1)
end

local function chatRaw(msg)
    sampAddChatMessage(u8:decode(msg), -1)
end

-- Приведение к нижнему регистру в CP1251 (для поиска и сравнений)
local function norm(s)
    s = u8:decode(tostring(s or ''))
    s = s:gsub('[\192-\223]', function(c) return string.char(c:byte() + 32) end)
    s = s:gsub('\168', '\184')
    return s:lower()
end

local function hasAny(name, list)
    if not name or name == '' then return false end
    local n = norm(name)
    for _, kw in ipairs(list) do
        if n:find(norm(kw), 1, true) then return true end
    end
    return false
end

local function cpToUtf8(cp)
    if cp < 0x80 then return string.char(cp)
    elseif cp < 0x800 then
        return string.char(0xC0 + math.floor(cp / 0x40), 0x80 + cp % 0x40)
    else
        return string.char(0xE0 + math.floor(cp / 0x1000),
            0x80 + math.floor(cp / 0x40) % 0x40, 0x80 + cp % 0x40)
    end
end

local function dump(line)
    if not S.debug then return end
    local f = io.open(DUMP_PATH, 'a')
    if f then
        f:write(os.date('[%H:%M:%S] '), tostring(line), '\n')
        f:close()
    end
end

local function saveCfg()
    createDirectory(CFG_DIR)
    local f = io.open(CFG_PATH, 'w')
    if f then
        f:write(encodeJson(cfg))
        f:close()
    end
end

local function loadCfg()
    local f = io.open(CFG_PATH, 'r')
    if not f then return end
    local data = f:read('*a')
    f:close()
    local ok, t = pcall(decodeJson, data)
    if ok and type(t) == 'table' then
        cfg.tmplItem = t.tmplItem
        cfg.tmplRes  = t.tmplRes
        cfg.button   = t.button
        cfg.buttonSeq = t.buttonSeq
        if t.superOn ~= nil then superChk[0] = t.superOn and true or false end
        if tonumber(t.superTarget) then superBuf[0] = tonumber(t.superTarget) end
        if t.updCef ~= nil then S.updCef = t.updCef and true or false end
    end
end

-- Обучение больше не нужно: протокол верстака вшит в скрипт.
local function isConfigured()
    return true
end

------------------------------------------------------------------------
-- ИНВЕНТАРЬ
------------------------------------------------------------------------
local function parseLevel(name)
    name = tostring(name or '')
    return tonumber(name:match('%(%s*%+(%d+)%s*%)')) or tonumber(name:match('%+(%d+)'))
end

local function parseInventory(raw)
    if not raw:find('"slot"', 1, true) then return 0 end
    raw = raw:gsub('\\"', '"')
    raw = raw:gsub('\\u(%x%x%x%x)', function(h) return cpToUtf8(tonumber(h, 16)) end)
    local count = 0
    for obj in raw:gmatch('{[^{}]*}') do
        local slot = tonumber(obj:match('"slot"%s*:%s*(%d+)'))
        if slot then
            local name = obj:match('"name"%s*:%s*"(.-)"')
                or obj:match('"title"%s*:%s*"(.-)"')
                or obj:match('"text"%s*:%s*"(.-)"')
                or obj:match('"label"%s*:%s*"(.-)"')
            local it = S.items[slot] or { slot = slot }
            it.id     = tonumber(obj:match('"item"%s*:%s*(%d+)')) or it.id
            it.amount = tonumber(obj:match('"amount"%s*:%s*(%d+)')) or it.amount
            if name and name ~= '' then it.name = name end
            S.items[slot] = it
            count = count + 1
        end
    end
    return count
end

local function sortedItems()
    local t = {}
    for _, it in pairs(S.items) do t[#t + 1] = it end
    table.sort(t, function(a, b) return a.slot < b.slot end)
    return t
end

local function isResource(it)
    return hasAny(it.name, STONE_KEYWORDS) or hasAny(it.name, AMULET_KEYWORDS) or hasAny(it.name, SUPER_KEYWORDS)
end

local function isAccessory(it)
    if not it.name or isResource(it) then return false end
    if hasAny(it.name, NOT_ACCESSORY_KEYWORDS) then return false end
    -- аксессуар с уровнем заточки: "Название (+7)" / "Название(+8)"
    if it.name:find('%(%s*%+%d+%s*%)') then return true end
    return hasAny(it.name, ACCESSORY_KEYWORDS)
end

local function filteredAccessories(query)
    local q = norm(query or '')
    local acc, other = {}, {}
    for _, it in ipairs(sortedItems()) do
        local label = (it.name or ('Предмет ID ' .. tostring(it.id or '?')))
        local matches = q == '' or norm(label):find(q, 1, true) or tostring(it.slot) == q
        if matches then
            if isAccessory(it) then
                acc[#acc + 1] = it
            elseif showAll[0] and not isResource(it) then
                other[#other + 1] = it
            end
        end
    end
    -- сначала аксессуары, потом остальные предметы
    for _, it in ipairs(other) do acc[#acc + 1] = it end
    return acc
end

local function findResource(kind, need)
    need = need or 1
    -- ручной слот ресурса (если камень не нашёлся по названию)
    if S.manualSlot then
        local m = S.items[S.manualSlot] or { slot = S.manualSlot, name = 'ресурс (слот ' .. S.manualSlot .. ')' }
        if m.amount == nil or m.amount >= need then return m end
        -- в ручном слоте не хватает: ищем другую стопку по названию (ниже)
    end
    local kws = (kind == 'amulet') and AMULET_KEYWORDS or STONE_KEYWORDS
    local best
    for _, it in ipairs(sortedItems()) do
        if hasAny(it.name, kws) and (it.amount == nil or it.amount >= need) then
            best = it
            break
        end
    end
    return best
end

local function countResource(kind)
    local kws = (kind == 'amulet') and AMULET_KEYWORDS or STONE_KEYWORDS
    local total = 0
    for _, it in ipairs(sortedItems()) do
        if hasAny(it.name, kws) then total = total + (it.amount or 1) end
    end
    return total
end

-- В режиме супер-заточки ресурс выбирается по уровню: ниже +SUPER_MIN_LEVEL - камни, выше - амулеты (+ супер-заточка)
local function phaseKind()
    if S.runSuper then
        return (S.level >= SUPER_MIN_LEVEL) and 'amulet' or 'stone'
    end
    return S.resource
end

local function findSuper()
    if S.manualSuper then
        local m = S.items[S.manualSuper] or { slot = S.manualSuper, name = 'супер-заточка (слот ' .. S.manualSuper .. ')' }
        if m.amount == nil or m.amount >= SUPER_PER_ATTEMPT then return m end
    end
    for _, it in ipairs(sortedItems()) do
        if hasAny(it.name, SUPER_KEYWORDS) and (it.amount == nil or it.amount >= SUPER_PER_ATTEMPT) then
            return it
        end
    end
end

local function countSuper()
    local total = 0
    for _, it in ipairs(sortedItems()) do
        if hasAny(it.name, SUPER_KEYWORDS) then total = total + (it.amount or 1) end
    end
    return total
end

local function queuePos(slot)
    for i, sl in ipairs(S.queue) do
        if sl == slot then return i end
    end
end

local function queueToggle(slot)
    local pos = queuePos(slot)
    if pos then table.remove(S.queue, pos) else S.queue[#S.queue + 1] = slot end
end

------------------------------------------------------------------------
-- ОТПРАВКА / ПРИЁМ CEF-СОБЫТИЙ (интерфейсы Arizona)
------------------------------------------------------------------------
local function sendCef(text)
    S.sending = true
    local bs = raknetNewBitStream()
    raknetBitStreamWriteInt8(bs, 220)
    raknetBitStreamWriteInt8(bs, 18)
    raknetBitStreamWriteInt16(bs, #text)
    raknetBitStreamWriteString(bs, text)
    raknetBitStreamWriteInt32(bs, 0)
    raknetSendBitStream(bs)
    raknetDeleteBitStream(bs)
    S.sending = false
    dump('SEND >> ' .. text)
end

local function sendTemplate(tmpl, slot)
    local ok, text = pcall(string.format, tmpl, slot)
    if not ok then
        chat('{FF5555}Ошибка шаблона клика. Выполните /toch_learn заново.')
        return false
    end
    sendCef(text)
    return true
end

local function makeTemplate(text)
    local known = {}
    for slot in pairs(S.items) do known[slot] = true end
    local lastS, lastE
    for s, num, e in text:gmatch('()(%d+)()') do
        if known[tonumber(num)] then lastS, lastE = s, e end
    end
    local function esc(x) return (x:gsub('%%', '%%%%')) end
    if lastS then
        return esc(text:sub(1, lastS - 1)) .. '%d' .. esc(text:sub(lastE))
    end
    chat('{FF5555}В событии не найден номер слота из списка /stats: клик будет ВСЕГДА по одному и тому же слоту. '
        .. 'Сначала откройте /toch (скан), потом /toch_learn.')
    return esc(text)
end

local IGNORE_OUT = { 'onActiveViewChanged', 'interfaceLoaded', 'pingHud', 'keepAlive' }

local function handleOutgoingCef(text)
    dump('OUT  << ' .. text)
    if not S.learn or S.sending then return end
    for _, bad in ipairs(IGNORE_OUT) do
        if text:find(bad, 1, true) then return end
    end
    if S.learn == 1 then
        cfg.tmplItem = makeTemplate(text)
        S.learn = 2
        chat('Записан клик по аксессуару: {AAAAAA}' .. cfg.tmplItem:sub(1, 90))
        chat('Теперь нажмите ЛКМ на точильный камень/амулет.')
    elseif S.learn == 2 then
        cfg.tmplRes = makeTemplate(text)
        S.learn = 3
        chat('Записан клик по ресурсу: {AAAAAA}' .. cfg.tmplRes:sub(1, 90))
        chat('Теперь нажмите кнопку {FFD700}"Заточить предмет"{FFFFFF}.')
    elseif S.learn == 3 then
        -- Кнопка может отправлять несколько событий подряд: собираем всё,
        -- что придёт в течение 1.5 секунды, и потом повторяем по порядку.
        S.learn = 4
        S.btnSeq = { text }
        chat('Записано нажатие кнопки: {AAAAAA}' .. text:sub(1, 90))
        lua_thread.create(function()
            wait(1500)
            cfg.buttonSeq = S.btnSeq
            cfg.button = S.btnSeq[1]
            S.learn = nil
            saveCfg()
            chat(string.format('{55FF55}Обучение завершено (событий у кнопки: %d). Запускайте /toch.', #S.btnSeq))
        end)
    elseif S.learn == 4 then
        S.btnSeq[#S.btnSeq + 1] = text
        chat('Доп. событие кнопки: {AAAAAA}' .. text:sub(1, 90))
    end
end

-- Максимальная длина CEF-строки, которую мы вообще пытаемся прочитать.
-- Защита от мусорной длины: без неё ReadString пытается выделить гигантскую
-- строку, память заканчивается и игра падает.
local MAX_CEF_LEN = 60000

local function lenIsSafe(bs, len)
    if type(len) ~= 'number' or len <= 0 or len > MAX_CEF_LEN then return false end
    local unread = raknetBitStreamGetNumberOfUnreadBits(bs)
    return unread >= len * 8
end

function onReceivePacket(id, bs)
    if id ~= 220 then return end
    pcall(function()
        raknetBitStreamIgnoreBits(bs, 8)
        local ptype = raknetBitStreamReadInt8(bs)
        if ptype == 17 then
            raknetBitStreamIgnoreBits(bs, 32)
            local len = raknetBitStreamReadInt16(bs)
            local encoded = raknetBitStreamReadInt8(bs)
            if lenIsSafe(bs, len) then
                local text
                if encoded ~= 0 then
                    if lenIsSafe(bs, len + encoded) then
                        text = raknetBitStreamDecodeString(bs, len + encoded)
                    end
                else
                    text = raknetBitStreamReadString(bs, len)
                end
                if text and #text > 0 then
                    dump('IN   >> ' .. text:sub(1, 1500))
                    if text:find('"slot"', 1, true) then parseInventory(text) end

                    -- какой интерфейс сейчас открыт: "Inventory", верстак и т.д. (null = закрыт)
                    if text:find('event.setActiveView', 1, true) then
                        local v = text:match('event%.setActiveView[^%[]*%[%s*"?([%w_%.%-]+)"?%s*%]')
                        if v == nil or v == 'null' then S.activeView = nil else S.activeView = v end
                        dump('ACTIVE VIEW = ' .. tostring(S.activeView))
                    end
                    -- подсказка при заточке: "Для заточки нужен: Точильный камень ... (4 шт.)"
                    if text:find('Для заточки нужен', 1, true) then
                        S.need = tonumber(text:match('%((%d+)%s*шт'))
                    end
                end
            end
        end
    end)
    raknetBitStreamResetReadPointer(bs)
end

function onSendPacket(id, bs)
    if id ~= 220 then return end
    pcall(function()
        raknetBitStreamIgnoreBits(bs, 8)
        local ptype = raknetBitStreamReadInt8(bs)
        if ptype == 18 then
            local len = raknetBitStreamReadInt16(bs)
            if lenIsSafe(bs, len) then
                local text = raknetBitStreamReadString(bs, len)
                if text and #text > 0 then handleOutgoingCef(text) end
            end
        end
    end)
    raknetBitStreamResetReadPointer(bs)
end

------------------------------------------------------------------------
-- УПРАВЛЕНИЕ ИНТЕРФЕЙСОМ ИГРЫ
------------------------------------------------------------------------
local function tapKey(vk, holdMs)
    setVirtualKeyDown(vk, true)
    wait(holdMs or 80)
    setVirtualKeyDown(vk, false)
end

-- Пауза с небольшой случайной добавкой; разбита на короткие шаги,
-- чтобы остановка (/toch_stop, F12) срабатывала сразу.
local function pause(ms)
    local total = ms + math.random(0, DELAY_JITTER)
    local t0 = os.clock() * 1000
    while S.running and (os.clock() * 1000 - t0) < total do wait(25) end
end

-- Закрытие интерфейса БЕЗ лишних ESC (иначе открывается меню паузы):
--  1) если открыт SA-MP диалог - закрываем его кнопкой;
--  2) ESC шлём только если ESC разрешён (allowEsc) и на экране реально открыт
--     интерфейс с курсором (верстак и т.п.).
local function closeGameUi(allowEsc)
    local okD, dialogOpen = pcall(sampIsDialogActive)
    if okD and dialogOpen then
        pcall(sampCloseCurrentDialogWithButton, 0)
        wait(150)
        return
    end
    if not allowEsc then return end
    local okC, cursorOpen = pcall(sampIsCursorActive)
    if (okC and cursorOpen) or not okC then
        tapKey(0x1B) -- ESC ровно один раз
        wait(150)
    end
end

-- Ответ на диалог с небольшой задержкой (ответ прямо внутри onShowDialog
-- иногда теряется, из-за этого скан срабатывал не с первого раза)
local function respondDialogLater(id, button, listitem)
    lua_thread.create(function()
        wait(150)
        sampSendDialogResponse(id, button, listitem, '')
    end)
end

-- Возвращает true, если инвентарь получен
local function scanInventory()
    if S.scanning or S.running then return false end
    S.scanning = true
    local backup = S.items
    S.items = {}
    S.gotItems = false
    S.dialogSeen = false
    S.scanDone = false
    S.pages = 0
    S.lastExtras = nil
    chat('Сканирую инвентарь через ' .. STATS_COMMAND .. '...')
    sampSendChat(STATS_COMMAND)

    -- Диалоги /stats -> "Предметы" перехватываются в onShowDialog.
    -- Если диалог не пришёл (интерфейс на CEF), нажимаем Enter вручную.
    local t0 = os.clock() * 1000
    while not S.dialogSeen and (os.clock() * 1000 - t0) < 1500 do wait(50) end
    local usedKey = false
    if not S.dialogSeen then
        tapKey(0x0D) -- Enter = "Предметы"
        usedKey = true
    end

    -- ждём все страницы списка (onShowDialog листает их сам и ставит scanDone)
    t0 = os.clock() * 1000
    local lastPages, tPage = 0, t0
    while not S.scanDone and (os.clock() * 1000 - t0) < 20000 do
        wait(50)
        if (S.pages or 0) ~= lastPages then
            lastPages, tPage = S.pages or 0, os.clock() * 1000
        end
        -- страницы перестали приходить: заканчиваем ожидание
        if (os.clock() * 1000 - tPage) > (SCAN_WINDOW + 2000) then break end
    end
    wait(300)
    -- закрываем только оставшийся диалог; ESC - лишь если пришлось жать Enter вручную
    closeGameUi(usedKey and not S.gotItems)
    S.scanning = false

    local n = 0
    for _, it in pairs(S.items) do
        if isAccessory(it) then n = n + 1 end
    end
    if next(S.items) == nil then
        S.items = backup or {}   -- не теряем прежний список
        chat('{FF5555}Инвентарь не получен. Включите /toch_dump и проверьте файл ' .. DUMP_PATH)
        return false
    else
        S.lastScan = os.clock()
        chat(string.format('Страниц: %d, предметов: %d, аксессуаров: %d, точильных камней: %d',
            S.pages or 0, #sortedItems(), n, countResource('stone')))
        -- служебные строки последней страницы (помогают понять, как устроена пагинация)
        local ex = S.lastExtras or {}
        if #ex > 0 then
            local parts = {}
            for i = 1, math.min(#ex, 4) do parts[#parts + 1] = '"' .. ex[i].text:gsub('^%s+', ''):gsub('%s+$', '') .. '"' end
            chat('Служебные строки диалога: ' .. table.concat(parts, ', '))
        end
        return true
    end
end

------------------------------------------------------------------------
-- ЦИКЛ ЗАТОЧКИ
------------------------------------------------------------------------
-- Протокол верстака Arizona (взят из реального лога клиента):
--   updateEnchantSlots|{"index":<слот предмета>,"left":<слот супер-заточки>,"right":<слот камня/амулета>,"color":-1}
--   startEnchant            - кнопка "Заточить предмет"
-- Номера слотов совпадают со списком /stats -> "Предметы".
-- В какую ячейку класть ресурс: 'right' ("Заточка") или 'left' ("Супер-заточка").
local RESOURCE_FIELD = { stone = 'right', amulet = 'right' }
local BENCH_WAIT_MS  = 120000   -- сколько ждать, пока игрок откроет верстак

local function sendEnchantSlots(index, left, right)
    sendCef(string.format('updateEnchantSlots|{"index":%d,"left":%d,"right":%d,"color":-1}', index, left, right))
end

local function benchIsOpen()
    local v = S.activeView
    return v ~= nil and v ~= 'Inventory'
end

-- Ждём, пока откроется верстак (или игрок введёт /toch_go)
local function waitForBench()
    if benchIsOpen() or S.forceGo then return true end
    chat('{FFD700}Откройте верстак{FFFFFF} (Мастерская -> Верстак мастерской, вкладка "Заточка"). Старт начнётся сам; если нет - введите {FFD700}/toch_go')
    local t0 = os.clock() * 1000
    while S.running and not (benchIsOpen() or S.forceGo) and (os.clock() * 1000 - t0) < BENCH_WAIT_MS do
        wait(100)
    end
    return S.running and (benchIsOpen() or S.forceGo) and true or false
end

local function triggerFlash(level)
    S.flashText = 'УСПЕХ +' .. tostring(level)
    S.flashUntil = os.clock() + FLASH_DURATION
end

local function stopRun(reason)
    if S.running then
        S.running = false
        if reason then chat(reason) end
    end
end

-- Точит ОДИН предмет до цели (обычная или с супер-заточкой с +SUPER_MIN_LEVEL).
-- Возвращает: 'done' (цель достигнута) | 'skip' (предмет пропущен) | 'stop' (остановить всю очередь)
local function sharpenItem(slot, isFirst)
    local it = S.items[slot]
    if not it then
        chat('{FFAA00}Слот ' .. slot .. ': предмет не найден в инвентаре, пропускаю.')
        return 'skip'
    end
    S.targetReached, S.itemMax, S.skip = false, false, false
    S.level = parseLevel(it.name) or 0
    if S.level >= currentTarget() then
        chat(string.format('{FFAA00}%s уже +%d (цель +%d), пропускаю.', it.name or ('слот ' .. slot), S.level, currentTarget()))
        return 'skip'
    end

    local lastNeed = 1
    local lastKind           -- какой ресурс (камень/амулет) стоял в прошлый раз
    local placed   = false   -- лежат ли сейчас предмет и камень в ячейках верстака
    local res                -- текущая стопка ресурса в ячейке
    local sup                -- текущая стопка супер-заточки (если используется)
    local stuck    = 0       -- сколько раз подряд "ничего не произошло"
    local restockFails = 0

    chat(string.format('Предмет %d/%d: %s, цель +%d', S.qIndex, S.qTotal, it.name or ('слот ' .. slot), currentTarget()))

    -- Ставит предмет и ресурс в ячейки верстака. Возвращает стопку ресурса или nil (тогда уже вызван stopRun).
    local function place()
        sendEnchantSlots(-1, -1, -1)          -- чистим ячейки только при (пере)установке
        pause(150)
        if not S.running then return nil end

        local kind = phaseKind()
        if kind ~= lastKind then lastNeed, lastKind = 1, kind end   -- камни и амулеты расходуются по-разному
        local cand = findResource(kind, lastNeed)
        if not cand then
            stopRun(kind == 'amulet' and '{FF5555}Точильные амулеты закончились. Остановка.'
                or '{FF5555}Точильные камни закончились. Остановка.')
            return nil
        end

        -- супер-заточка нужна только на уровнях +SUPER_MIN_LEVEL и выше
        sup = nil
        if S.runSuper and S.level >= SUPER_MIN_LEVEL then
            sup = findSuper()
            if not sup then
                stopRun('{FF5555}Супер-заточка закончилась или не найдена. Остановка.')
                return nil
            end
        end

        -- 1) кладём аксессуар в ячейку "Предмет"
        S.need = nil
        sendEnchantSlots(slot, -1, -1)

        -- клиент сообщает, сколько камней нужно для этого уровня: "(4 шт.)"
        local t1 = os.clock() * 1000
        while S.running and not S.need and (os.clock() * 1000 - t1) < 1200 do wait(50) end
        local need = S.need or lastNeed
        lastNeed = need
        if cand.amount and cand.amount < need then
            cand = findResource(kind, need)
            if not cand then
                stopRun(string.format('{FF5555}Для заточки нужно %d шт., в инвентаре столько нет. Остановка.', need))
                return nil
            end
        end
        pause(CLICK_DELAY)
        if not S.running then return nil end

        -- 2) кладём камень / амулет
        local left, right = -1, -1
        if RESOURCE_FIELD[kind] == 'left' then left = cand.slot else right = cand.slot end
        if sup then left = sup.slot end     -- ячейка "Супер-заточка"
        sendEnchantSlots(slot, left, right)
        pause(BUTTON_DELAY)
        if not S.running then return nil end

        placed = true
        return cand
    end

    pause(isFirst and START_DELAY or CYCLE_DELAY)

    while S.running do
        -- на всякий случай: если потеряна связь с сервером (кик, вылет) - останавливаемся, а не крутимся вхолостую
        local okConn, gs = pcall(sampGetGamestate)
        if okConn and gs ~= 3 then
            stopRun('{FF5555}Нет соединения с сервером. Остановка.')
            return 'stop'
        end

        -- Ставим предмет и камни ТОЛЬКО если они не лежат на верстаке:
        -- в начале, после повышения уровня, когда стопка кончилась или когда "ничего не нажимается".
        if not placed then
            res = place()
            if not res or not S.running then return 'stop' end
        end

        -- кнопка "Заточить предмет" (в обычном режиме - единственное действие за попытку)
        S.result, S.restock = nil, false
        S.awaiting = true
        S.attempts = S.attempts + 1
        sendCef('startEnchant')
        S.lastSend = os.clock()

        local t0 = os.clock() * 1000
        local tSent, retries = t0, 0
        S.lastMsg = nil
        while S.running and not S.result and not S.restock and not S.itemMax and not S.skip
              and (os.clock() * 1000 - t0) < RESULT_TIMEOUT do
            wait(50)
            local now = os.clock() * 1000
            -- сервер молчит: скорее всего клик не прошёл (анимация и т.п.) - жмём кнопку ещё раз, ячейки не трогаем
            if retries < CLICK_RETRIES and not S.result and not S.restock and (now - tSent) >= CLICK_RETRY_MS then
                retries = retries + 1
                tSent = now
                sendCef('startEnchant')
                S.lastSend = os.clock()
            end
        end
        S.awaiting = false
        if not S.running then return 'stop' end

        if S.skip then
            chat('{FFAA00}Предмет пропущен вручную.')
            return 'skip'
        end
        if S.itemMax then
            chat('{FFAA00}Предмет на максимальном уровне, пропускаю.')
            return 'skip'
        end

        if S.result then
            -- попытка прошла: ресурс потрачен
            stuck, restockFails = 0, 0
            if res.amount then res.amount = math.max(0, res.amount - lastNeed) end
            if sup and sup.amount then
                sup.amount = math.max(0, sup.amount - SUPER_PER_ATTEMPT)
                if sup.amount < SUPER_PER_ATTEMPT then
                    chat('{FFAA00}Стопка супер-заточки закончилась, ставлю следующую...')
                    placed = false
                end
            end
            if S.targetReached then return 'done' end
            if sup and not S.result.ok then
                -- супер-заточка не сработала: уровень упал, снова нужны камни
                S.level = S.result.newLevel or math.max(0, S.level - SUPER_FAIL_DROP)
                chat(string.format('{FFAA00}Супер-заточка не сработала: уровень упал до +%d, снова точим до +%d.',
                    S.level, SUPER_MIN_LEVEL))
                placed = false
            elseif S.result.ok then
                -- уровень вырос: требуемое число камней могло измениться, а ресурс - смениться (камни -> амулеты)
                placed = false
            elseif res.amount and res.amount < lastNeed then
                -- в ячейке не осталось нужного количества: возьмём следующую стопку
                chat('{FFAA00}Камни в ячейке закончились, ставлю новые...')
                placed = false
            end
        elseif S.restock then
            -- сервер сказал "не хватает / нет": пробуем поставить заново (возможно, другую стопку)
            restockFails = restockFails + 1
            if sup and S.restockText and hasAny(S.restockText, { 'супер' }) then
                if sup.amount then sup.amount = 0 end   -- не хватает именно супер-заточки
            elseif res.amount then
                res.amount = 0
            end
            if restockFails >= MAX_TIMEOUTS then
                stopRun('{FF5555}Сервер: ' .. tostring(S.restockText) .. ' Остановка.')
                return 'stop'
            end
            chat('{FFAA00}Не хватает ресурса, переставляю предмет и камни...')
            placed = false
        else
            -- ничего не произошло: слоты пустые или ресурса не хватает
            stuck = stuck + 1
            chat(string.format('{FFAA00}Нет ответа от сервера (%d/%d), переставляю предмет и камни.', stuck, MAX_TIMEOUTS))
            if S.lastMsg then chat('{AAAAAA}Последнее сообщение сервера: ' .. tostring(S.lastMsg)) end
            if stuck >= MAX_TIMEOUTS then
                stopRun('{FF5555}Ничего не происходит. Проверьте, что верстак открыт, и хватает денег/камней.')
                return 'stop'
            end
            -- второй раз подряд: считаем текущую стопку пустой и пробуем другую
            if stuck >= 2 and res.amount then res.amount = 0 end
            placed = false
        end

        pause(CYCLE_DELAY)
    end
    return 'stop'
end

-- Очередь: берёт предметы по порядку, ресурс (камень/амулет) один и тот же для всех
local function sharpenLoop()
    if S.running then return end
    if #S.queue == 0 then chat('{FF5555}Очередь пуста: выберите аксессуары в меню /toch.') return end
    if not S.resource then chat('{FF5555}Не выбран ресурс заточки.') return end
    S.running  = true
    S.forceGo  = false
    S.awaiting = false
    S.restock  = false
    S.attempts, S.okCount, S.failCount = 0, 0, 0
    S.runSuper  = superChk[0]
    S.runTarget = S.runSuper and math.min(superBuf[0], SUPER_MAX_LEVEL) or TARGET_LEVEL
    S.manualSuper = (manualSuperBuf[0] >= 0) and manualSuperBuf[0] or nil
    if S.runSuper then
        S.manualSlot = nil   -- в режиме супер-заточки камни и амулеты ищем по названию
        local miss = {}
        if countResource('stone') == 0 then miss[#miss + 1] = 'точильные камни' end
        if countResource('amulet') == 0 then miss[#miss + 1] = 'точильные амулеты' end
        if countSuper() == 0 and not S.manualSuper then miss[#miss + 1] = 'супер-заточка (или укажите её слот)' end
        if #miss > 0 then
            chat('{FF5555}В инвентаре не найдено: ' .. table.concat(miss, ', ') .. '.')
            S.running, S.runSuper, S.runTarget = false, false, nil
            return
        end
    end

    local queue = {}
    for i, sl in ipairs(S.queue) do queue[i] = sl end
    S.qTotal = #queue
    if S.runSuper then
        chat(string.format('Старт очереди: %d предм., цель +%d. Камни до +%d, затем амулеты + супер-заточка.',
            #queue, S.runTarget, SUPER_MIN_LEVEL))
    else
        chat(string.format('Старт очереди: %d предм., цель +%d, ресурс: %s', #queue, S.runTarget,
            S.resource == 'stone' and 'точильный камень' or 'точильный амулет'))
    end

    if not waitForBench() then
        stopRun('{FF5555}Верстак не открыт. Остановка.')
        S.running, S.runSuper, S.runTarget = false, false, nil
        return
    end

    local doneN, skipN = 0, 0
    for i, slot in ipairs(queue) do
        if not S.running then break end
        S.qIndex, S.curSlot = i, slot
        local st = sharpenItem(slot, i == 1)
        if st == 'stop' then break end
        -- предмет обработан: убираем его из очереди (при остановке в середине остаток сохранится)
        local pos = queuePos(slot)
        if pos then table.remove(S.queue, pos) end
        if st == 'done' then
            doneN = doneN + 1
            chat(string.format('{55FF55}Готово: предмет %d/%d достиг +%d.', i, #queue, S.runTarget))
        else
            skipN = skipN + 1
        end
    end

    local finishedAll = S.running   -- running всё ещё true => очередь прошла до конца
    S.awaiting = false
    S.running  = false
    S.curSlot  = nil
    S.runSuper, S.runTarget = false, nil
    if finishedAll then
        chatRaw(string.format('{00FF55}[AUTO TOCH] Очередь завершена: заточено %d, пропущено %d (цель +%d)',
            doneN, skipN, S.runTarget))
        lua_thread.create(function()
            wait(300)
            closeGameUi(true) -- один ESC, и только если интерфейс (верстак) открыт
        end)
    else
        chat(string.format('Остановлено. Заточено: %d, пропущено: %d, в очереди осталось: %d.', doneN, skipN, #S.queue))
    end
end

local function startSharpen(kind)
    S.resource = kind
    cfg.superOn, cfg.superTarget = superChk[0], superBuf[0]
    saveCfg()
    lua_thread.create(sharpenLoop)
end

------------------------------------------------------------------------
-- ЧАТ: РЕЗУЛЬТАТЫ ЗАТОЧКИ
------------------------------------------------------------------------
-- Похоже ли сообщение на реплику игрока (VIP-чат, /b, обычный чат и т.п.): "[VIP] Ник[12]: текст", "Ник_Фамилия: текст".
-- Такие строки скрипт полностью игнорирует, чтобы случайная фраза в чате не сбила заточку.
local function looksLikePlayerChat(t)
    if t:find('%[%d+%]%s*:') then return true end                                   -- Ник[12]: ...
    if t:find('^%s*[%[%(][^%]%)]*[%]%)]%s*[%w_%.]+[%[%(]?%d*[%]%)]?%s*:') then return true end  -- [VIP] Ник: ...
    if t:find('^%s*[%w_%.]+%s*:') then return true end                               -- Nick_Name: ...
    if t:find('^%s*[%[%(][^%]%)]*[Vv][Ii][Pp][^%]%)]*[%]%)]') then return true end   -- [VIP] ...
    return false
end

-- Фраза должна стоять в самом начале сообщения (допускается короткий префикс), а не где-то в тексте игрока
local function startsNear(t, phrase, maxOffset)
    local pos = t:find(phrase, 1, true)
    return pos ~= nil and pos <= (maxOffset or 20)
end

local RESTOCK_CONTEXT = { 'заточ', 'точил', 'камн', 'амулет', 'ресурс', 'супер' }

function sampev.onServerMessage(color, text)
    if not S.running then return end
    local clean = u8(text):gsub('{%x%x%x%x%x%x}', '')

    -- Реплики игроков (VIP-чат и т.д.) не обрабатываем вообще
    if looksLikePlayerChat(clean) then return end

    -- Результат попытки принимаем только пока ждём ответ (или сразу после отправки клика: ответ мог запоздать)
    local waiting = S.awaiting or (S.lastSend ~= nil and (os.clock() - S.lastSend) < 15)
    if not waiting then return end

    -- успех
    if startsNear(clean, 'Успех! Вам удалось улучшить предмет') then
        local name, from, to = clean:match('Успех! Вам удалось улучшить предмет (.-) %S+ %+(%d+) на %+(%d+)')
        from, to = tonumber(from), tonumber(to)
        if to and from and to == from + 1 and from >= 0 and to <= 30 then
            dump(string.format('ACCEPT success color=%s: %s', tostring(color), clean))
            S.level = to
            S.okCount = S.okCount + 1
            S.result = { ok = true, from = from, to = to }
            triggerFlash(to)
            chat(string.format('{55FF55}Успех! %s +%d -> +%d (попыток: %d)', name or '', from, to, S.attempts))
            if to >= currentTarget() then
                S.targetReached = true   -- цикл сам перейдёт к следующему предмету очереди
            end
        end
        return
    end

    -- неудача
    if startsNear(clean, 'Увы, вам не удалось улучшить предмет') then
        local fname, ffrom, fto = clean:match('Увы, вам не удалось улучшить предмет (.-) %S+ %+(%d+) на %+(%d+)')
        ffrom, fto = tonumber(ffrom), tonumber(fto)
        if ffrom and ffrom >= 0 and ffrom <= 30 then
            dump(string.format('ACCEPT fail color=%s: %s', tostring(color), clean))
            S.level = ffrom
            S.failCount = S.failCount + 1
            S.result = { ok = false, from = ffrom, newLevel = (fto and fto < ffrom) and fto or nil }
            chat(string.format('{FF8888}Неудача на +%d (попыток: %d)', ffrom, S.attempts))
        end
        return
    end
    -- Запасной разбор: у супер-заточки текст неудачи может отличаться ("Увы ... понижен до +11" и т.п.)
    -- Строго: сообщение начинается с "Увы" и содержит уровень "+N"
    if S.awaiting and startsNear(clean, 'Увы', 12) and clean:find('%+%d+') then
        local nums = {}
        for v in clean:gmatch('%+(%d+)') do nums[#nums + 1] = tonumber(v) end
        local from = nums[1] or S.level
        local newLv
        if #nums >= 2 and nums[#nums] < nums[1] then newLv = nums[#nums] end
        dump(string.format('ACCEPT fail(generic) color=%s: %s', tostring(color), clean))
        S.level = from
        S.failCount = S.failCount + 1
        S.result = { ok = false, from = from, newLevel = newLv }
        chat('{FF8888}Неудача: ' .. clean)
        return
    end

    -- Дальше - только пока ждём результат
    if not S.awaiting then return end
    S.lastMsg = clean   -- для диагностики: что сервер писал, пока мы ждали ответ
    local n = norm(clean)
    for _, kw in ipairs(ITEM_MAX_KEYWORDS) do
        if n:find(norm(kw), 1, true) then
            S.itemMax = true
            return
        end
    end
    for _, kw in ipairs(HARD_STOP_KEYWORDS) do
        if n:find(norm(kw), 1, true) then
            stopRun('{FF5555}Сервер: ' .. clean)
            return
        end
    end
    -- не хватает ресурса: цикл сам переставит предмет и камни.
    -- Только если сообщение про заточку/ресурсы (иначе любая служебная строка сервера давала бы ложную тревогу).
    for _, kw in ipairs(RESTOCK_KEYWORDS) do
        if n:find(norm(kw), 1, true) then
            for _, ctx in ipairs(RESTOCK_CONTEXT) do
                if n:find(norm(ctx), 1, true) then
                    S.restockText = clean
                    S.restock = true
                    return
                end
            end
        end
    end
end

-- Разбор диалога со списком предметов:
-- "[19]  СЕРТИФИКАТ ALPHA<TAB>[1 шт]"
-- Возвращает: число разобранных предметов, число НОВЫХ слотов, список служебных
-- строк {idx = номер пункта списка (с 0), text = текст} (например "Следующая страница").
local function parseDialogItems(text, style)
    local clean = u8(text):gsub('{%x%x%x%x%x%x}', ''):gsub('\r', '')
    local count, newSlots = 0, 0
    local extras = {}
    local listIdx = -1
    local first = true
    for line in (clean .. '\n'):gmatch('(.-)\n') do
        local isEmpty = line:match('^%s*$') ~= nil
        local skipHeader = false
        if not isEmpty and first then
            first = false
            if style == 5 then skipHeader = true end -- TABLIST_HEADERS: первая строка - заголовок
        end
        if not isEmpty and not skipHeader then listIdx = listIdx + 1 end

        local slot, rest = line:match('^%s*%[(%d+)%]%s*(.*)$')
        slot = tonumber(slot)
        if not isEmpty and not skipHeader and not (slot and rest and rest ~= '') then
            extras[#extras + 1] = { idx = listIdx, text = (line:gsub('\t', ' ')) }
        end
        if skipHeader then slot = nil end
        if slot and rest and rest ~= '' then
            local name, qty = rest:match('^(.-)%s*\t+%s*(.*)$')
            if not name then
                -- нет табуляции: количество в конце строки в скобках
                name = rest:gsub('%s*%[%d+[^%]]*%]%s*$', '')
                qty = rest:match('%[(%d+)[^%]]*%]%s*$')
            end
            name = (name or rest):gsub('^%s+', ''):gsub('%s+$', '')
            local amount = tonumber(tostring(qty or ''):match('(%d+)')) or 1
            if name ~= '' then
                if not S.items[slot] then newSlots = newSlots + 1 end
                local it = S.items[slot] or { slot = slot }
                it.name = name
                it.amount = amount
                S.items[slot] = it
                count = count + 1
            end
        end
    end
    return count, newSlots, extras
end

local NEXT_PAGE_KEYWORDS = { 'следующ', 'далее', 'дальше', 'вперед', 'вперёд', '>>', 'ещё', 'еще', 'показать' }
local PREV_PAGE_KEYWORDS = { 'предыдущ', 'назад', '<<' }

local function findNextPageItem(extras)
    for _, ex in ipairs(extras) do
        if hasAny(ex.text, NEXT_PAGE_KEYWORDS) and not hasAny(ex.text, PREV_PAGE_KEYWORDS) then
            return ex
        end
    end
end

function sampev.onShowDialog(id, style, title, b1, b2, text)
    if S.debug then
        dump('DIALOG ' .. id .. ' | ' .. tostring(title) .. ' | ' .. tostring(text))
    end

    -- список предметов парсим всегда (в том числе если игрок открыл его сам)
    local n, newSlots, extras = parseDialogItems(text or '', style)
    if n > 0 then
        S.gotItems = true
        S.dialogSeen = true
        S.pages = (S.pages or 0) + 1
        dump(string.format('ПАРСИНГ ДИАЛОГА: предметов %d, новых слотов %d, style %s', n, newSlots, tostring(style)))
        for _, ex in ipairs(extras) do dump('  служебная строка #' .. ex.idx .. ': ' .. ex.text) end

        if S.scanning then
            S.lastExtras = extras
            -- Диалог разбит на страницы? Нажимаем "Следующая страница", пока появляются новые слоты.
            local nxt = findNextPageItem(extras)
            if nxt and newSlots > 0 and S.pages < 40 then
                respondDialogLater(id, 1, nxt.idx)
            else
                S.scanDone = true
                respondDialogLater(id, 0, -1) -- "Выход"
            end
            return false                              -- не показываем окно
        end
        return
    end

    -- окно "Основная статистика": нажимаем левую кнопку "Предметы"
    if S.scanning then
        local t = norm(title or '') .. ' ' .. norm(text or '')
        if t:find('статистика', 1, true) or t:find('авторизация', 1, true) then
            S.dialogSeen = true
            respondDialogLater(id, 1, 0)
            return false
        end
    end
end

------------------------------------------------------------------------
-- IMGUI
------------------------------------------------------------------------
imgui.OnInitialize(function()
    local imio = imgui.GetIO()   -- не называть "io": это перекроет стандартный модуль io
    imio.IniFilename = nil
    local fonts = imio.Fonts
    local ranges = fonts:GetGlyphRangesCyrillic()
    -- шрифт подгружаем только если файл существует (иначе возможен вылет)
    for _, name in ipairs({ 'trebucbd.ttf', 'arial.ttf', 'tahoma.ttf' }) do
        local path = getFolderPath(0x14) .. '\\' .. name
        local f = io.open(path, 'rb')
        if f then
            f:close()
            fonts:AddFontFromFileTTF(path, 16, nil, ranges)
            break
        end
    end
    imgui.GetStyle().WindowRounding = 8
    imgui.GetStyle().FrameRounding = 5
end)

-- Меню 1: выбор аксессуара
imgui.OnFrame(function() return winMain[0] and not S.scanning end, function(self)
    local sx, sy = getScreenResolution()
    imgui.SetNextWindowPos(imgui.ImVec2(sx / 2, sy / 2), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
    imgui.SetNextWindowSize(imgui.ImVec2(480, 540), imgui.Cond.FirstUseEver)
    if imgui.Begin(ui'Выбор аксессуара', winMain) then
        imgui.InputTextWithHint('##search', ui'Поиск по названию или слоту...', searchBuf, sizeof(searchBuf))
        imgui.Checkbox(ui'Показывать все предметы', showAll)
        imgui.SameLine()
        if imgui.Button(ui'Пересканировать') then
            lua_thread.create(scanInventory)
        end

        imgui.Separator()
        local list = filteredAccessories(str(searchBuf))
        imgui.Text(ui('Показано: ' .. #list .. '   (* - аксессуары, серые - прочие предметы)'))

        imgui.BeginChild('##list', imgui.ImVec2(0, -150), true)
        if #list == 0 then
            imgui.TextWrapped(ui'Список пуст. Нажмите "Пересканировать" или включите "Показывать все предметы".')
        end
        for _, it in ipairs(list) do
            local label = it.name or ('Предмет ID ' .. tostring(it.id or '?'))
            local acc = isAccessory(it)
            local qpos = queuePos(it.slot)
            local line = string.format('%s%s[%d] %s', qpos and ('#' .. qpos .. '  ') or '', acc and '* ' or '   ', it.slot, label)
            if not acc then imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.6, 0.6, 0.6, 1)) end
            if imgui.Selectable(line .. '##' .. it.slot, qpos ~= nil) then
                if S.running then
                    chat('Во время заточки очередь менять нельзя. /toch_stop - остановить.')
                else
                    queueToggle(it.slot)   -- клик добавляет в очередь, повторный клик убирает
                end
            end
            if not acc then imgui.PopStyleColor() end
        end
        imgui.EndChild()

        imgui.Separator()
        imgui.Text(ui(string.format('Цель: +%d   Текущий: +%d   Попыток: %d (успех %d / неудач %d)',
            currentTarget(), S.level, S.attempts, S.okCount, S.failCount)))
        if S.running then
            imgui.Text(ui(string.format('Очередь: предмет %d из %d, осталось в очереди: %d', S.qIndex, S.qTotal, #S.queue)))
        end
        if S.running then
            imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.7, 0.15, 0.15, 1))
            if imgui.Button(ui'СТОП', imgui.ImVec2(-1, 28)) then stopRun('Остановлено пользователем.') end
            imgui.PopStyleColor()
        else
            if #S.queue == 0 then
                imgui.TextDisabled(ui'Кликайте по аксессуарам: они встанут в очередь (#1, #2...) в порядке клика. Повторный клик - убрать.')
            else
                if imgui.Button(ui(string.format('Далее: выбрать ресурс (в очереди: %d)', #S.queue)), imgui.ImVec2(-1, 28)) then
                    winRes[0] = true
                end
                if imgui.Button(ui'Очистить очередь', imgui.ImVec2(-1, 0)) then S.queue = {} end
                imgui.TextDisabled(ui'Затем откройте верстак (Мастерская -> Верстак мастерской).')
            end
        end
    end
    imgui.End()
end)

-- Меню 2: "Чем точить?"
imgui.OnFrame(function() return winMain[0] and winRes[0] and #S.queue > 0 and not S.scanning end, function(self)
    local sx, sy = getScreenResolution()
    imgui.SetNextWindowPos(imgui.ImVec2(sx / 2, sy / 2), imgui.Cond.Appearing, imgui.ImVec2(0.5, 0.5))
    imgui.SetNextWindowSize(imgui.ImVec2(380, 400), imgui.Cond.Appearing)
    if imgui.Begin(ui'Чем точить?', winRes, imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse) then
        local names = {}
        for i = 1, math.min(#S.queue, 4) do
            local q = S.items[S.queue[i]]
            names[#names + 1] = string.format('#%d %s', i, (q and q.name) or ('слот ' .. S.queue[i]))
        end
        if #S.queue > 4 then names[#names + 1] = '... и ещё ' .. (#S.queue - 4) end
        imgui.TextWrapped(ui(string.format('В очереди: %d\n%s', #S.queue, table.concat(names, '\n'))))
        imgui.Separator()

        imgui.Checkbox(ui'Точить до +N с супер-заточкой', superChk)
        if superChk[0] then
            imgui.InputInt(ui'Цель +N', superBuf)
            if superBuf[0] < SUPER_MIN_LEVEL + 1 then superBuf[0] = SUPER_MIN_LEVEL + 1 end
            if superBuf[0] > SUPER_MAX_LEVEL then superBuf[0] = SUPER_MAX_LEVEL end
            imgui.InputInt(ui'Слот супер-заточки', manualSuperBuf)
            if manualSuperBuf[0] < -1 then manualSuperBuf[0] = -1 end
            imgui.TextWrapped(ui(string.format('Камни: %d, амулеты: %d, супер-заточка: %d. До +%d точим камнями, с +%d - амулетами + супер-заточкой. Если она не сработает, уровень упадёт и снова пойдут камни. Максимум +%d.',
                countResource('stone'), countResource('amulet'), countSuper(), SUPER_MIN_LEVEL, SUPER_MIN_LEVEL, SUPER_MAX_LEVEL)))
        else
            imgui.TextDisabled(ui(string.format('Цель: +%d (меняется командой /toch_level)', TARGET_LEVEL)))
        end
        imgui.Separator()

        if superChk[0] then
            if imgui.Button(ui(string.format('Начать: камни -> амулеты + супер-заточка (в очереди: %d)', #S.queue)), imgui.ImVec2(-1, 40)) then
                winRes[0], winMain[0] = false, false
                S.manualSlot = nil
                startSharpen('stone')
            end
        else
        local manual = manualBuf[0] >= 0
        local stones, amulets = countResource('stone'), countResource('amulet')
        if imgui.Button(ui(string.format('Точильный камень (%d)', stones)), imgui.ImVec2(-1, 34)) then
            if stones > 0 or manual then
                winRes[0], winMain[0] = false, false
                S.manualSlot = manual and manualBuf[0] or nil
                startSharpen('stone')
            else
                chat('{FF5555}Точильных камней нет в списке. Укажите слот вручную ниже.')
            end
        end
        if imgui.Button(ui(string.format('Точильный амулет (%d)', amulets)), imgui.ImVec2(-1, 34)) then
            if amulets > 0 or manual then
                winRes[0], winMain[0] = false, false
                S.manualSlot = manual and manualBuf[0] or nil
                startSharpen('amulet')
            else
                chat('{FF5555}Точильных амулетов нет в списке. Укажите слот вручную ниже.')
            end
        end

        imgui.Separator()
        imgui.TextWrapped(ui'Если камень/амулет не нашёлся по названию, введите номер его слота (-1 = искать по названию):')
        imgui.InputInt(ui'Слот ресурса', manualBuf)
        if manualBuf[0] < -1 then manualBuf[0] = -1 end
        end
        if imgui.Button(ui'Отмена', imgui.ImVec2(-1, 0)) then winRes[0] = false end
    end
    imgui.End()
end)

-- Зелёная вспышка "УСПЕХ +N" поверх экрана
imgui.OnFrame(function() return os.clock() < S.flashUntil end, function(self)
    self.HideCursor = true
    local sx, sy = getScreenResolution()
    local left = S.flashUntil - os.clock()
    local k = math.max(0, math.min(1, left / FLASH_DURATION))

    imgui.SetNextWindowPos(imgui.ImVec2(0, 0))
    imgui.SetNextWindowSize(imgui.ImVec2(sx, sy))
    local flags = imgui.WindowFlags.NoDecoration + imgui.WindowFlags.NoMove
        + imgui.WindowFlags.NoBackground + imgui.WindowFlags.NoSavedSettings
        + imgui.WindowFlags.NoInputs + imgui.WindowFlags.NoScrollbar
    imgui.Begin('##toch_flash', nil, flags)

    local dl = imgui.GetForegroundDrawList()
    local col = imgui.ColorConvertFloat4ToU32(imgui.ImVec4(0.1, 1.0, 0.25, 0.55 * k))
    dl:AddRectFilled(imgui.ImVec2(0, 0), imgui.ImVec2(sx, sy), col)

    imgui.SetWindowFontScale(6)
    local text = ui(S.flashText)
    local size = imgui.CalcTextSize(text)
    local px, py = (sx - size.x) / 2, (sy - size.y) / 2
    imgui.SetCursorPos(imgui.ImVec2(px + 4, py + 4))
    imgui.TextColored(imgui.ImVec4(0, 0.25, 0, k), text)
    imgui.SetCursorPos(imgui.ImVec2(px, py))
    imgui.TextColored(imgui.ImVec4(1, 1, 1, k), text)
    imgui.SetWindowFontScale(1)

    imgui.End()
end)

------------------------------------------------------------------------
-- КОМАНДЫ
------------------------------------------------------------------------
------------------------------------------------------------------------
-- АВТООБНОВЛЕНИЕ
------------------------------------------------------------------------
-- Ссылка на JSON с описанием последней версии. Файл выглядит так:
--   { "version": "1.3", "url": "https://raw.githubusercontent.com/АККАУНТ/РЕПО/main/auto_toch.lua", "changelog": "что нового" }
-- Пока ссылка пустая, автообновление выключено.
local UPDATE_JSON_URL       = 'https://raw.githubusercontent.com/rmakarov228/auto_tochka/main/auto_toch.json'
local UPDATE_CHECK_ON_START = true   -- проверять обновление при запуске игры

local function verParts(v)
    local t = {}
    for n in tostring(v):gmatch('%d+') do t[#t + 1] = tonumber(n) end
    return t
end

local function isNewer(remote, current)
    local a, b = verParts(remote), verParts(current)
    for i = 1, math.max(#a, #b) do
        local x, y = a[i] or 0, b[i] or 0
        if x ~= y then return x > y end
    end
    return false
end

local function readFile(path)
    local f = io.open(path, 'rb')
    if not f then return nil end
    local data = f:read('*a')
    f:close()
    return data
end

local function writeFile(path, data)
    local f = io.open(path, 'wb')
    if not f then return false end
    f:write(data)
    f:close()
    return true
end

-- Скачивает файл (вызывать только из потока: внутри wait)
local function downloadFile(url, path)
    local dl = require('moonloader').download_status
    local done = false
    os.remove(path)
    downloadUrlToFile(url, path, function(id, status)
        if status == dl.STATUSEX_ENDDOWNLOAD then done = true end
    end)
    local t0 = os.clock()
    while not done and os.clock() - t0 < 20 do wait(100) end
    return done
end

local updating      = false
local winUpd        = new.bool(false)   -- окно "Доступно обновление"
local pendingUpdate = nil               -- { version, url, changelog }
local declinedVersion = nil             -- версия, от которой отказались в этой сессии (до перезапуска не спрашиваем)

-- Скачивает и устанавливает версию из info (вызывать из потока)
local function installUpdate(info)
    if updating then return end
    updating = true
    local ok, err = pcall(function()
        chat(string.format('Скачиваю версию %s...', info.version))
        local newPath = thisScript().path .. '.new'
        if not downloadFile(info.url, newPath) then error('не удалось скачать скрипт') end
        local code = readFile(newPath)
        -- проверки, чтобы не затереть рабочий скрипт битым файлом
        if not code or #code < 2000 then os.remove(newPath) error('скачанный файл пустой или неполный') end
        local fn, cerr = loadfile(newPath)
        os.remove(newPath)
        if not fn then error('в новой версии ошибка: ' .. tostring(cerr)) end

        local old = readFile(thisScript().path)
        if old then writeFile(thisScript().path .. '.bak', old) end   -- резервная копия прошлой версии
        if not writeFile(thisScript().path, code) then error('не удалось записать файл скрипта') end

        chat('{55FF55}Обновлено до ' .. info.version .. '. Перезагружаю скрипт...')
        wait(500)
        thisScript():reload()
    end)
    updating = false
    if not ok then chat('{FF5555}Обновление: ' .. tostring(err)) end
end

-- Проверяет версию на сервере. Если вышла новая - показывает окно "Скачать / Позже" (ничего не качает само).
local function checkUpdate(manual)
    if updating then return end
    if UPDATE_JSON_URL == '' then
        if manual then chat('Автообновление не настроено: впишите ссылку в UPDATE_JSON_URL (блок АВТООБНОВЛЕНИЕ в скрипте).') end
        return
    end
    updating = true
    local ok, err = pcall(function()
        local jsonPath = CFG_DIR .. '\\auto_toch_update.json'
        if not downloadFile(UPDATE_JSON_URL, jsonPath) then error('не удалось скачать информацию об обновлении') end
        local raw = readFile(jsonPath)
        os.remove(jsonPath)
        local pok, info = pcall(decodeJson, raw or '')
        if not pok or type(info) ~= 'table' or not info.version or not info.url then
            error('файл версии повреждён')
        end
        if not tostring(info.url):find('^https://') then error('ссылка на скрипт должна начинаться с https://') end

        local current = thisScript().version
        if not isNewer(info.version, current) then
            if manual then chat('У вас последняя версия (' .. current .. ').') end
            return
        end
        if S.running then
            chat(string.format('{FFAA00}Доступно обновление %s, но идёт заточка. Проверить позже: /toch_update', info.version))
            return
        end
        -- от этой версии уже отказались: автоматически больше не беспокоим (вручную /toch_update покажет снова)
        if not manual and declinedVersion == tostring(info.version) then return end

        pendingUpdate = { version = tostring(info.version), url = info.url, changelog = info.changelog }
        chat(string.format('{FFD700}Доступно обновление %s (у вас %s).', pendingUpdate.version, current))
        if S.updCef then showUpdateCef(pendingUpdate) else winUpd[0] = true end
    end)
    updating = false
    if not ok and manual then chat('{FF5555}Обновление: ' .. tostring(err)) end
end

-- ======== Окно обновления через CEF (опционально, /toch_cef) ========
-- Lua -> страница: в игровой браузер посылается эмулированный входящий пакет 220/17 с кодом JS,
-- который рисует панель. Обратной связи JS -> Lua нет: панель только показывает текст,
-- а кнопки "Y - скачать" и "N - позже" обрабатывает Lua клавишами.
local UPD_PANEL_ID = 'autotoch-upd'
local cefPanelActive = false

local function evalCef(code)
    local bs = raknetNewBitStream()
    raknetBitStreamWriteInt8(bs, 17)
    raknetBitStreamWriteInt32(bs, 0)
    raknetBitStreamWriteInt16(bs, #code)
    raknetBitStreamWriteInt8(bs, 0)
    raknetBitStreamWriteString(bs, code)
    raknetEmulPacketReceiveBitStream(220, bs)
    raknetDeleteBitStream(bs)
end

local function jsQuote(str)   -- безопасная строка для JS (текст кладём через textContent, не innerHTML)
    str = tostring(str or ''):gsub('\\', '\\\\'):gsub("'", "\\'"):gsub('\r', ''):gsub('\n', '\\n')
    return "'" .. str .. "'"
end

local function hideUpdateCef()
    evalCef("var e=document.getElementById('" .. UPD_PANEL_ID .. "');if(e){e.remove();}")
end

local function showUpdateCef(info, demo)
    if cefPanelActive then return end
    cefPanelActive = true
    local js = table.concat({
        "(function(){",
        "var o=document.getElementById('", UPD_PANEL_ID, "');if(o){o.remove();}",
        "var d=document.createElement('div');d.id='", UPD_PANEL_ID, "';",
        "d.style.cssText='position:fixed;right:24px;top:30%;width:340px;padding:16px 18px;",
        "background:rgba(18,20,28,.94);color:#fff;font:15px/1.4 Arial,sans-serif;",
        "border:1px solid #ffd54a;border-radius:10px;z-index:2147483647;pointer-events:none;",
        "box-shadow:0 6px 24px rgba(0,0,0,.5)';",
        "function row(t,css){var r=document.createElement('div');r.style.cssText=css||'';r.textContent=t;d.appendChild(r);}",
        "row(", jsQuote('AutoToch: доступно обновление'), ",'font-weight:700;color:#ffd54a;margin-bottom:6px');",
        "row(", jsQuote(string.format('Версия %s (у вас %s)', info.version, thisScript().version)), ",'margin-bottom:6px');",
        "row(", jsQuote(info.changelog or ''), ",'color:#cfd3dc;margin-bottom:10px');",
        "row(", jsQuote('Y - скачать и установить     N - позже'), ",'font-weight:700;color:#7CFC9A');",
        "document.body.appendChild(d);})();",
    })
    evalCef(js)
    chat('{FFD700}Окно обновления (CEF): нажмите Y - скачать, N - позже.')
    lua_thread.create(function()
        local t0 = os.clock()
        local choice
        while os.clock() - t0 < 60 and not choice do
            wait(0)
            if not (sampIsChatInputActive() or sampIsDialogActive()) then
                if wasKeyPressed(0x59) then choice = 'yes'       -- Y
                elseif wasKeyPressed(0x4E) then choice = 'no' end -- N
            end
        end
        hideUpdateCef()
        cefPanelActive = false
        if choice == 'yes' then
            if demo then chat('Демо-окно: Y нажата (в реальном обновлении здесь началась бы загрузка).')
            else installUpdate(info) end
        else
            if not demo then declinedVersion = info.version end
            chat(choice == 'no' and 'Обновление отложено.' or 'Окно обновления закрыто по времени.')
        end
    end)
end

imgui.OnFrame(function() return winUpd[0] and pendingUpdate ~= nil end, function(self)
    local sx, sy = getScreenResolution()
    imgui.SetNextWindowPos(imgui.ImVec2(sx / 2, sy / 2), imgui.Cond.Appearing, imgui.ImVec2(0.5, 0.5))
    imgui.SetNextWindowSize(imgui.ImVec2(400, 230), imgui.Cond.Appearing)
    if imgui.Begin(ui'AutoToch: доступно обновление', winUpd, imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse) then
        imgui.Text(ui(string.format('Новая версия: %s   (у вас: %s)', pendingUpdate.version, thisScript().version)))
        imgui.Separator()
        if pendingUpdate.changelog and tostring(pendingUpdate.changelog) ~= '' then
            imgui.TextWrapped(ui('Что нового: ' .. tostring(pendingUpdate.changelog)))
        else
            imgui.TextDisabled(ui'Описание изменений не указано.')
        end
        imgui.Separator()
        if imgui.Button(ui'Скачать и установить', imgui.ImVec2(185, 32)) then
            winUpd[0] = false
            local info = pendingUpdate
            lua_thread.create(function() installUpdate(info) end)
        end
        imgui.SameLine()
        if imgui.Button(ui'Позже', imgui.ImVec2(185, 32)) then
            winUpd[0] = false
        end
        imgui.TextDisabled(ui'Скрипт перезагрузится сам. Позже: /toch_update')
    end
    imgui.End()
    -- закрыли окно ("Позже" или крестик): до перезапуска игры про эту версию не спрашиваем
    if not winUpd[0] and pendingUpdate and not updating then declinedVersion = pendingUpdate.version end
end)


-- Подкоманды теперь отдельные команды через "_": /toch_stop, /toch_go и т.д.
local SUBCOMMANDS = { 'stop', 'skip', 'clear', 'super', 'update', 'cef', 'level', 'delay', 'learn', 'go', 'show', 'dump', 'scan', 'reset', 'help' }

local function runSub(cmd, rest)
    rest = rest or ''
    if cmd == 'stop' then
        if S.running then stopRun('Остановлено пользователем.') else chat('Заточка не запущена.') end
    elseif cmd == 'skip' then
        if S.running then S.skip = true else chat('Заточка не запущена.') end
    elseif cmd == 'clear' then
        if S.running then chat('Во время заточки очередь менять нельзя.') else S.queue = {} chat('Очередь очищена.') end
    elseif cmd == 'cef' then
        -- /toch_cef - вкл/выкл CEF-окно обновления, /toch_cef test - показать демо-панель
        if rest:lower():find('test', 1, true) then
            showUpdateCef({ version = '9.9', changelog = 'Это тест CEF-панели. Y/N закроют её.' }, true)
        else
            S.updCef = not S.updCef
            cfg.updCef = S.updCef
            saveCfg()
            chat('Окно обновления через CEF: ' .. (S.updCef and 'ВКЛ' or 'ВЫКЛ (используется mimgui)')
                .. '. Проверка: /toch_cef test')
        end
    elseif cmd == 'update' then
        lua_thread.create(function() checkUpdate(true) end)
    elseif cmd == 'super' then
        -- /toch_super - вкл/выкл, /toch_super 14 - включить и задать цель
        local n = tonumber(rest)
        if n then
            superChk[0] = true
            superBuf[0] = math.max(SUPER_MIN_LEVEL + 1, math.min(SUPER_MAX_LEVEL, math.floor(n)))
        else
            superChk[0] = not superChk[0]
        end
        cfg.superOn, cfg.superTarget = superChk[0], superBuf[0]
        saveCfg()
        chat(superChk[0] and string.format('Супер-заточка ВКЛ: цель +%d (с +%d и выше).', superBuf[0], SUPER_MIN_LEVEL)
            or ('Супер-заточка ВЫКЛ: цель +' .. TARGET_LEVEL))
    elseif cmd == 'level' then
        local n = tonumber(rest)
        if n and n > 0 and n <= 50 then
            TARGET_LEVEL = n
            chat('Целевой уровень: +' .. n)
        else
            chat('Использование: /toch_level <число>. Сейчас: +' .. currentTarget())
        end
    elseif cmd == 'delay' then
        -- /toch_delay 1500 : одна общая пауза между действиями (мс)
        local n = tonumber(rest)
        if n and n >= 100 and n <= 10000 then
            CLICK_DELAY, BUTTON_DELAY, START_DELAY = n, n, math.floor(n * 1.5)
            CYCLE_DELAY = n * 2
            chat(string.format('Паузы: между кликами %d мс, перед кнопкой %d мс, между попытками %d мс', n, n, n * 2))
        else
            chat(string.format('Использование: /toch_delay <100-10000 мс>. Сейчас: клики %d, кнопка %d, цикл %d',
                CLICK_DELAY, BUTTON_DELAY, CYCLE_DELAY))
        end
    elseif cmd == 'learn' then
        chat('Обучение больше не нужно: события верстака уже вшиты в скрипт.')
    elseif cmd == 'go' then
        -- принудительный старт, если скрипт не заметил открытие верстака
        S.forceGo = true
        chat('Принудительный старт.')
    elseif cmd == 'show' then
        chat(string.format('Интерфейс: %s, верстак открыт: %s, нужно ресурса за попытку: %s, ресурс-поле: %s',
            tostring(S.activeView), tostring(benchIsOpen()), tostring(S.need), tostring(RESOURCE_FIELD.stone)))
    elseif cmd == 'dump' then
        S.debug = not S.debug
        chat('Лог CEF-событий: ' .. (S.debug and 'ВКЛ' or 'ВЫКЛ') .. ' (' .. DUMP_PATH .. ')')
    elseif cmd == 'scan' then
        lua_thread.create(scanInventory)
    elseif cmd == 'reset' then
        cfg.tmplItem, cfg.tmplRes, cfg.button, cfg.buttonSeq = nil, nil, nil, nil
        saveCfg()
        chat('Сохранённые события кликов сброшены.')
    elseif cmd == 'help' then
        chat('/toch - меню | /toch_stop | /toch_skip (пропустить предмет) | /toch_clear (очистить очередь) | /toch_super [N] | /toch_update | /toch_cef [test] | /toch_scan | /toch_go | /toch_show | /toch_level N | /toch_delay MS | /toch_dump')
    end
end

local function cmdToch(arg)
    arg = (arg or ''):gsub('^%s+', ''):gsub('%s+$', '')

    -- старый формат "/toch stop" -> подсказываем новый "/toch_stop" и всё равно выполняем
    local oldCmd, oldRest = arg:match('^(%S+)%s*(.*)$')
    oldCmd = oldCmd and oldCmd:lower() or ''
    for _, sub in ipairs(SUBCOMMANDS) do
        if oldCmd == sub then
            chat('Команды теперь через "_": {FFD700}/toch_' .. sub)
            runSub(sub, oldRest)
            return
        end
    end

    if S.running then
        chat('Заточка уже идёт. /toch_stop - остановить.')
        winMain[0] = true
        return
    end
    S.resource = nil
    winRes[0] = false
    searchBuf[0] = 0
    lua_thread.create(function()
        -- Свежий список (меньше 60 сек) не пересканируем: так верстак не закрывается лишний раз.
        local fresh = next(S.items) ~= nil and S.lastScan and (os.clock() - S.lastScan) < 60
        if not fresh then
            local ok = false
            for attempt = 1, 3 do
                ok = scanInventory()
                if ok then break end
                if attempt < 3 then
                    chat(string.format('{FFAA00}Повторное сканирование (%d/3)...', attempt + 1))
                    wait(800)
                end
            end
        end
        if next(S.items) ~= nil then
            winMain[0] = true
        else
            chat('{FF5555}Не удалось получить инвентарь. Попробуйте /toch_scan или /toch_dump.')
        end
    end)
end

------------------------------------------------------------------------
-- MAIN
------------------------------------------------------------------------
function main()
    while not isSampAvailable() do wait(100) end
    createDirectory(CFG_DIR)
    loadCfg()
    if UPDATE_CHECK_ON_START then
        lua_thread.create(function() wait(5000) checkUpdate(false) end)
    end
    sampRegisterChatCommand('toch', cmdToch)
    for _, sub in ipairs(SUBCOMMANDS) do
        sampRegisterChatCommand('toch_' .. sub, function(a) runSub(sub, a) end)
    end
    chat('Загружен. Команда {FFD700}/toch{FFFFFF}, помощь: /toch_help. Аварийная остановка: {FFD700}F12')
    while true do
        wait(0)
        if S.running and isKeyJustPressed(0x7B) then -- F12
            stopRun('Аварийная остановка (F12).')
        end
    end
end

function onScriptTerminate(scr, quit)
    if scr == thisScript() then
        S.running = false
        setVirtualKeyDown(0x1B, false)
        setVirtualKeyDown(0x0D, false)
    end
end
