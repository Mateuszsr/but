"""
Warspear Online - AutoFarm v36
==============================
pip install pymem pywin32

Fixes v14:
  [FIX1] SELECTING: Enter só é pressionado se loot_stack==4 (cadáver empilhado no tile)
         Antes: Enter sempre após clique → selecionava cadáver aleatório
  [FIX2] _find_nearest_target: cooldown por coord ignora apenas se dist > 2.0u
         Antes: bloqueava toda a posição → ranged/pack next ao mob morto era ignorado
  [FIX3] _collect_entry: loop dinâmico (até 5 tentativas) em vez de range(entry.count)
         Antes: count não confiável com mobs morrendo em tempos diferentes
  [FIX4] recent_dead: bloqueio por posição recente em _find_nearest_target
         Antes: vtable/dead_ptrs não cobriam janela de transição "meio morto"
  [FIX5] ATTACKING: checa loot_ptr antes de entrar em DEATH_WAIT
         Antes: sempre esperava 1.7s + polling mesmo sem loot

Fix v36:
  [FIX6] Detecção de novo spawn no mesmo endereço/coordenada (respawn reuse)
         Problema: mob nasce com mesmo ptr ou mesma coord que um morto recente ->
                   dead_ptrs ou near_recent_dead bloqueavam o novo mob indefinidamente.
         Solucao: _is_respawned() verifica dois criterios independentes antes de bloquear:
           - Criterio HP: 0 < cur_hp <= max_hp E vtable != DEAD
             (endereco reutilizado por mob vivo)
           - Criterio Movimento: posicao atual difere da posicao de morte registrada
             em >= T_RESPAWN_MOVE_MIN unidades (mob se moveu apos spawnar)
         Se qualquer criterio for verdadeiro, o bloqueio e ignorado/removido.
"""

import tkinter as tk
from tkinter import ttk
import threading
import time
import sys
import math
import ctypes
import subprocess
from enum import Enum, auto

# ──────────────────────────────────────────────
# Elevação de privilégios (necessário para ler
# memória de outros processos no Windows)
# ──────────────────────────────────────────────
def _is_admin():
    try:
        return ctypes.windll.shell32.IsUserAnAdmin()
    except:
        return False

if not _is_admin():
    # Reinicia o próprio script com privilégios de administrador
    ctypes.windll.shell32.ShellExecuteW(
        None, "runas", sys.executable, " ".join(f'"{a}"' for a in sys.argv), None, 1
    )
    sys.exit(0)

try:
    import pymem, pymem.process
except ImportError:
    subprocess.call([sys.executable, "-m", "pip", "install", "pymem"]); import pymem

try:
    import win32gui, win32con, win32api, win32process
except ImportError:
    subprocess.call([sys.executable, "-m", "pip", "install", "pywin32"])
    import win32gui, win32con, win32api, win32process

# ──────────────────────────────────────────────
# Memória
# ──────────────────────────────────────────────
PROCESS_NAME           = "Warspear.exe"
STATIC_SYSTEM_INSTANCE = 0x00D4D8AC
OFF_GAMEMANAGER = 0x14
OFF_TREE_HEADER = 0x3C
OFF_PLAYER_OBJ  = 0x40
OFF_CAMERA      = 0x124C
OFF_NODE_LEFT   = 0x04
OFF_NODE_RIGHT  = 0x08
OFF_NODE_ID     = 0x10
OFF_NODE_OBJECT = 0x14
OFF_WORLD_X  = 0x10
OFF_WORLD_Y  = 0x14
OFF_NAME     = 0x64
OFF_CUR_HP   = 268
OFF_MAX_HP   = 272
OFF_CUR_MANA = 276
OFF_MAX_MANA = 280
OFF_CAM_ZOOM   = 0x30
OFF_CAM_X      = 0x64
OFF_CAM_Y      = 0x68
OFF_CAM_PREV_X = 0x6C
OFF_CAM_PREV_Y = 0x70
OFF_VP_LEFT    = 0x76
OFF_VP_TOP     = 0x78
OFF_VP_RIGHT   = 0x7A
OFF_VP_BOTTOM  = 0x7C
OFF_LOOT_PTR        = 0x0FC
OFF_SELECTED_ENTITY = 0x290  # ptr da entidade selecionada pelo player (0 = nenhuma)
VTABLE_ALIVE   = 13133932  # 0xC8686C
VTABLE_DEAD    = 12937312  # 0xC57E60

# ──────────────────────────────────────────────
# UI State (GM + offset)
# ──────────────────────────────────────────────
# Lidos a partir do endereço do GameManager
OFF_UI_LOOT_SIMPLE  = 0x0C0  # 3 = fechado, 4 = janela de loot simples aberta
OFF_UI_LOOT_STACK   = 0x014  # 3 = fechado, 4 = janela de seleção de cadáver empilhado

UI_STATE_NORMAL     = 3
UI_STATE_OPEN       = 4

# Timeouts do loot baseados em UI state (não mais sleeps cegos)
T_UI_OPEN_TIMEOUT   = 5.0   # máximo aguardando janela abrir após clique
T_UI_CLOSE_TIMEOUT  = 5.0   # máximo aguardando janela fechar após Enter
T_UI_POLL           = 0.05  # intervalo de polling do UI state

# ──────────────────────────────────────────────
# Timings (todos centralizados aqui)
# ──────────────────────────────────────────────
T_SELECT_WAIT      = 0.35   # após click no mob, antes do enter para selecionar
T_SELECT_ENTER     = 0.30   # após enter de seleção, antes de começar skills
T_DEATH_WAIT       = 1.70   # aguarda animação de morte
T_LOOT_POLL_DELAY  = 0.20   # intervalo entre tentativas de polling do loot_ptr
T_LOOT_POLL_TRIES  = 8      # quantas vezes tenta ler o loot_ptr antes de desistir
T_LOOT_CLICK_WAIT  = 0.40   # após click no cadáver, antes do enter
T_LOOT_ENTER_WAIT  = 0.70   # entre enters no loot (abre janela → coleta)
T_LOOT_NEXT_WAIT   = 0.35   # entre iterações de cadáveres empilhados
T_DEATH_TIMEOUT    = 12.0   # timeout máximo para mob morrer
T_NEXT_WAIT        = 0.50   # pausa entre mobs
T_STUCK_TIMEOUT    = 8.0    # se mesmo mob for alvo por X segundos sem skills → pular
T_COOLDOWN_COORD   = 15.0   # cooldown em coordenada após morte

# Distância máxima (unidades de mundo) para selecionar alvo.
# Na escala deste jogo mobs visíveis na tela estão a ~100-300u.
# 500u cobre toda a tela confortavelmente sem ir para fora do mapa.
MAX_TARGET_DIST    = 500.0

# Raio máximo em unidades de mundo para considerar "chegou no loot"
# Segundos sem queda de HP para concluir que a seleção falhou
T_SELECT_CONFIRM    = 3.0   # tempo máximo para confirmar seleção via +0x290
T_SELECT_HP_POLL    = 0.15  # intervalo de checagem durante confirmação

# Patrol
T_PATROL_MOVE_WAIT  = 1.5   # aguarda após clicar no chão antes de checar se moveu
T_PATROL_STUCK_MAX  = 3     # tentativas sem movimento antes de desistir do patrol
T_PATROL_ARRIVE_R   = 2.0   # raio em unidades de mundo para considerar "chegou"
T_PATROL_WAIT_SPAWN = 3.0   # aguarda mobs respawnarem ao chegar no waypoint
T_RESPAWN_MOVE_MIN  = 0.5   # deslocamento mínimo (unidades) para considerar que é um novo spawn

# Ciclo de skills: (codigo_tecla, pausa_apos_em_segundos)
SKILL_CYCLE = [
    (0x31, 1.0),
    (0x34, 1.0),
    (0x32, 1.0),
]

# ──────────────────────────────────────────────
# Estados
# ──────────────────────────────────────────────
class State(Enum):
    IDLE         = auto()
    SELECTING    = auto()
    ATTACKING    = auto()
    DEATH_WAIT   = auto()
    LOOTING      = auto()
    LOOT_PENDING = auto()
    PATROLLING   = auto()
    NEXT         = auto()


STATE_LABELS = {
    State.IDLE:         ("Aguardando alvos...",         "#546574"),
    State.SELECTING:    ("Selecionando alvo...",         "#00d4ff"),
    State.ATTACKING:    ("Atacando...",                  "#ff9f43"),
    State.DEATH_WAIT:   ("Aguardando morte...",          "#ffd700"),
    State.LOOTING:      ("Lootando...",                  "#00ff88"),
    State.LOOT_PENDING: ("Loot pendente (área ocupada)", "#ffd700"),
    State.PATROLLING:   ("Patrulhando...",               "#a29bfe"),
    State.NEXT:         ("Próximo alvo...",              "#546574"),
}


# ──────────────────────────────────────────────
# Memória helpers
# ──────────────────────────────────────────────
class MemReader:
    def __init__(self, pm):
        self.pm = pm
    def ptr(self, addr):
        try: v = self.pm.read_int(addr); return v if v else None
        except: return None
    def uint(self, addr):
        try: return self.pm.read_uint(addr)
        except: return 0
    def int_(self, addr):
        try: return self.pm.read_int(addr)
        except: return 0
    def float_(self, addr):
        try: return self.pm.read_float(addr)
        except: return 0.0
    def short_(self, addr):
        try: return int.from_bytes(self.pm.read_bytes(addr, 2), "little", signed=True)
        except: return 0
    def wstr(self, addr, max_len=64):
        try:
            raw  = self.pm.read_bytes(addr, max_len * 2)
            text = raw.decode("utf-16-le", errors="ignore")
            null = text.find('\x00')
            return text[:null].strip() if null != -1 else text.strip()
        except: return "???"


# ──────────────────────────────────────────────
# Câmera / mundo → tela
# ──────────────────────────────────────────────
def read_camera(mem, gm):
    cam_ptr = mem.ptr(gm + OFF_CAMERA)
    if not cam_ptr: return None
    return {
        "x":      mem.float_(cam_ptr + OFF_CAM_X),
        "y":      mem.float_(cam_ptr + OFF_CAM_Y),
        "zoom":   mem.float_(cam_ptr + OFF_CAM_ZOOM),
        "vp_l":   mem.short_(cam_ptr + OFF_VP_LEFT),
        "vp_t":   mem.short_(cam_ptr + OFF_VP_TOP),
        "vp_r":   mem.short_(cam_ptr + OFF_VP_RIGHT),
        "vp_b":   mem.short_(cam_ptr + OFF_VP_BOTTOM),
        "prev_x": mem.float_(cam_ptr + OFF_CAM_PREV_X),
        "prev_y": mem.float_(cam_ptr + OFF_CAM_PREV_Y),
    }

def world_to_screen(cam, wx, wy, dw, dh):
    if not cam: return None, None
    z  = cam["zoom"]
    sx = 0.5 * (dw / 2 - (cam["vp_l"] + cam["vp_r"]) * z) + (wx * z * 2 - cam["x"] * z)
    sy = 0.5 * (dh / 2 - (cam["vp_t"] + cam["vp_b"]) * z) + (wy * z * 2 - cam["y"] * z) - 15
    return sx, sy

def read_entity(mem, obj, eid=0, cam=None, dw=800, dh=600):
    if not obj: return None
    wx = mem.int_(obj + OFF_WORLD_X) / 65536.0
    wy = mem.int_(obj + OFF_WORLD_Y) / 65536.0
    sx, sy = world_to_screen(cam, wx, wy, dw, dh)
    return {
        "ptr": obj, "id": eid,
        "name": mem.wstr(obj + OFF_NAME) or "???",
        "x": wx, "y": wy,
        "screen_x": sx, "screen_y": sy,
        "on_screen": sx is not None and 0 <= sx <= dw and 0 <= sy <= dh,
        "cur_hp": mem.int_(obj + OFF_CUR_HP),
        "max_hp": mem.int_(obj + OFF_MAX_HP),
        "cur_mp": mem.int_(obj + OFF_CUR_MANA),
        "max_mp": mem.int_(obj + OFF_MAX_MANA),
    }

def traverse(mem, node, results, cam, dw, dh, depth=0):
    if not node or depth > 512: return
    traverse(mem, mem.ptr(node + OFF_NODE_LEFT),  results, cam, dw, dh, depth+1)
    obj = mem.ptr(node + OFF_NODE_OBJECT)
    if obj:
        e = read_entity(mem, obj, mem.uint(node + OFF_NODE_ID), cam, dw, dh)
        if e: results.append(e)
    traverse(mem, mem.ptr(node + OFF_NODE_RIGHT), results, cam, dw, dh, depth+1)

def collect(mem, gm, cam, dw, dh):
    header = mem.ptr(gm + OFF_TREE_HEADER)
    if not header: return None, None, []
    root = mem.ptr(header)
    if not root: return header, None, []
    entities = []
    traverse(mem, root, entities, cam, dw, dh)
    return header, root, entities


# ──────────────────────────────────────────────
# Enumeração de instâncias Warspear abertas
# ──────────────────────────────────────────────
def enum_warspear_windows():
    """Retorna lista de (hwnd, titulo, pid) de todas as janelas Warspear abertas."""
    results = []
    def cb(hwnd, _):
        title = win32gui.GetWindowText(hwnd)
        if "warspear" in title.lower() and win32gui.IsWindowVisible(hwnd):
            try:
                _, pid = win32process.GetWindowThreadProcessId(hwnd)
                results.append((hwnd, title, pid))
            except:
                pass
    win32gui.EnumWindows(cb, None)
    return results


# ──────────────────────────────────────────────
# Input helpers
# ──────────────────────────────────────────────
# hwnd da instância selecionada — definido pelo App após conexão
_selected_hwnd: int | None = None

def get_game_hwnd():
    """Retorna o hwnd da instância selecionada; cai para busca automática se não definido."""
    if _selected_hwnd:
        return _selected_hwnd
    hwnd = win32gui.FindWindow(None, "Warspear Online")
    if not hwnd:
        found = []
        def cb(h, x):
            if "warspear" in win32gui.GetWindowText(h).lower(): x.append(h)
        win32gui.EnumWindows(cb, found)
        hwnd = found[0] if found else None
    return hwnd

def get_game_window_rect():
    hwnd = get_game_hwnd()
    if not hwnd: return None
    rect = win32gui.GetClientRect(hwnd)
    pt   = win32gui.ClientToScreen(hwnd, (0, 0))
    return pt[0], pt[1], pt[0] + rect[2], pt[1] + rect[3]

def click_game(sx, sy):
    hwnd = get_game_hwnd()
    if not hwnd: return False
    x, y   = int(round(sx)), int(round(sy))
    lParam = (y << 16) | (x & 0xFFFF)
    win32api.PostMessage(hwnd, win32con.WM_LBUTTONDOWN, win32con.MK_LBUTTON, lParam)
    time.sleep(0.05)
    win32api.PostMessage(hwnd, win32con.WM_LBUTTONUP, 0, lParam)
    return True

def press_enter():
    hwnd = get_game_hwnd()
    if not hwnd: return
    win32api.PostMessage(hwnd, win32con.WM_KEYDOWN, win32con.VK_RETURN, 0)
    time.sleep(0.05)
    win32api.PostMessage(hwnd, win32con.WM_KEYUP, win32con.VK_RETURN, 0)

def press_key(vk):
    hwnd = get_game_hwnd()
    if not hwnd: return
    win32api.PostMessage(hwnd, win32con.WM_KEYDOWN, vk, 0)
    time.sleep(0.05)
    win32api.PostMessage(hwnd, win32con.WM_KEYUP, vk, 0)

def interruptible_sleep(seconds, check_fn, step=0.05):
    """Dorme 'seconds' segundos, verificando check_fn() a cada 'step'.
    Retorna True se dormiu completo, False se check_fn() retornou False antes."""
    elapsed = 0.0
    while elapsed < seconds:
        if not check_fn(): return False
        time.sleep(step)
        elapsed += step
    return True


# ──────────────────────────────────────────────
# UI Colors / Fonts
# ──────────────────────────────────────────────
BG     = "#1a1a2e"
BG2    = "#16213e"
BG3    = "#0f3460"
ACCENT = "#e94560"
GREEN  = "#00ff88"
YELLOW = "#ffd700"
CYAN   = "#00d4ff"
ORANGE = "#ff9f43"
TEXT   = "#c8d6e5"
DIM    = "#546574"
FONT_M = ("Consolas", 9)
FONT_B = ("Consolas", 9, "bold")


# ──────────────────────────────────────────────
# LootEntry — cadáver pendente de loot
# ──────────────────────────────────────────────
class LootEntry:
    """Representa um ou mais cadáveres empilhados na mesma coordenada."""
    def __init__(self, wx, wy):
        self.wx    = wx
        self.wy    = wy
        self.count = 1        # quantos cadáveres empilhados nessa coord

    def merge(self):
        """Incrementa stack quando outro mob morre na mesma coordenada."""
        self.count += 1

    def screen_pos(self, cam, dw, dh):
        """Recalcula posição de tela usando câmera atual (evita erro de câmera movida)."""
        return world_to_screen(cam, self.wx, self.wy, dw, dh)

    def __repr__(self):
        return f"LootEntry(wx={self.wx:.1f}, wy={self.wy:.1f}, count={self.count})"


# ──────────────────────────────────────────────
# FarmContext — estado compartilhado da máquina
# ──────────────────────────────────────────────
class FarmContext:
    """Toda a informação viva de uma sessão de farm.
    A máquina de estados lê e escreve aqui."""
    def __init__(self):
        self.reset()

    def reset(self):
        self.state          = State.IDLE
        self.target         = None
        self.target_wx      = 0.0
        self.target_wy      = 0.0
        self.loot_queue     : list[LootEntry] = []
        self.dead_ptrs      : set  = set()
        self.cooldown_coords: list = []
        self.recent_dead    : list = []       # [(wx, wy, timestamp)] — janela curta pós-morte
        self.waypoint_wx    : float | None = None
        self.waypoint_wy    : float | None = None
        self.kills          = 0
        self.loots          = 0
        self.session_start  = time.time()

    # helpers de fila de loot
    def enqueue_loot(self, wx, wy):
        radius = 1.0
        for entry in self.loot_queue:
            if math.sqrt((entry.wx - wx)**2 + (entry.wy - wy)**2) <= radius:
                entry.merge()
                return entry
        entry = LootEntry(wx, wy)
        self.loot_queue.append(entry)
        return entry

    def purge_expired(self, entities):
        """Remove ptrs mortos que já saíram da árvore e coords de cooldown expiradas."""
        active_ptrs         = {e["ptr"] for e in entities}
        self.dead_ptrs      = {p for p in self.dead_ptrs if p in active_ptrs}
        now                 = time.time()
        self.cooldown_coords = [
            (cx, cy, ts) for (cx, cy, ts) in self.cooldown_coords
            if now - ts < T_COOLDOWN_COORD
        ]

    def add_cooldown(self, wx, wy):
        self.cooldown_coords.append((wx, wy, time.time()))

    def mark_recent_dead(self, wx, wy):
        """Registra posição de morte recente — janela de 3s para bloquear seleção.
        Guarda também a posição exata da morte para detectar novo spawn por movimento."""
        self.recent_dead.append((wx, wy, time.time()))

    def near_recent_dead(self, wx, wy, radius=1.5, window=3.0):
        """True se (wx,wy) estiver perto de uma morte ocorrida nos últimos 'window' segundos."""
        now = time.time()
        self.recent_dead = [(rx, ry, ts) for rx, ry, ts in self.recent_dead
                            if now - ts < window]
        for rx, ry, ts in self.recent_dead:
            if math.sqrt((wx - rx)**2 + (wy - ry)**2) <= radius:
                return True
        return False

    def in_cooldown(self, wx, wy):
        # NOTA: este método só deve ser chamado após confirmar que o mob está VIVO.
        # O cooldown protege contra reataque imediato numa coord onde acabou de morrer
        # um mob — mas NÃO deve bloquear outro mob vivo que esteja na mesma posição.
        # A verificação de "vivo" já é feita em _find_nearest_target antes de chamar isto.
        now = time.time()
        for cx, cy, ts in self.cooldown_coords:
            if now - ts < T_COOLDOWN_COORD:
                if math.sqrt((wx - cx)**2 + (wy - cy)**2) < 1.5:
                    return True
        return False

    def elapsed(self):
        return time.time() - self.session_start

    def stats_str(self):
        mins = int(self.elapsed() // 60)
        secs = int(self.elapsed() % 60)
        kph  = int(self.kills / max(self.elapsed(), 1) * 3600)
        return f"kills={self.kills}  loots={self.loots}  {mins:02d}:{secs:02d}  ({kph}/h)"


# ──────────────────────────────────────────────
# Máquina de estados
# ──────────────────────────────────────────────
class FarmFSM:
    """
    Máquina de estados do farm. Cada método _state_XXX() executa
    a lógica de um estado e retorna o próximo State.

    A thread chama step() em loop, que despacha para o método correto.
    """
    def __init__(self, app: "App"):
        self.app = app
        self.ctx = FarmContext()
        self._skill_idx = 0
        self._attack_start = 0.0   # timestamp do início do ataque atual

    # ── Propriedades de conveniência ──────────
    @property
    def mem(self): return self.app.mem
    @property
    def entities(self): return self.app._entities
    @property
    def player(self): return self.app._player
    @property
    def farming(self): return self.app._farming

    def _alive(self): return self.farming  # usado como check_fn em interruptible_sleep

    # ── Dispatch ──────────────────────────────
    def step(self):
        """Executa um passo da FSM. Retorna o novo estado."""
        s = self.ctx.state
        if   s == State.IDLE:         return self._state_idle()
        elif s == State.SELECTING:    return self._state_selecting()
        elif s == State.ATTACKING:    return self._state_attacking()
        elif s == State.DEATH_WAIT:   return self._state_death_wait()
        elif s == State.LOOTING:      return self._state_looting()
        elif s == State.LOOT_PENDING: return self._state_loot_pending()
        elif s == State.PATROLLING:   return self._state_patrolling()
        elif s == State.NEXT:         return self._state_next()
        return State.IDLE

    def transition(self, new_state: State):
        old = self.ctx.state
        self.ctx.state = new_state
        label, color = STATE_LABELS[new_state]
        self.app._set_farm_status(label, color)
        if old != new_state:
            self.app._log(f"[FSM] {old.name} → {new_state.name}")

    # ══════════════════════════════════════════
    # IDLE — procura próximo alvo
    # ══════════════════════════════════════════
    def _state_idle(self):
        if not self.player or not self.mem:
            time.sleep(0.2)
            return State.IDLE

        self.ctx.purge_expired(self.entities)

        # Tenta coletar loot pendente antes de buscar novo alvo
        if self.ctx.loot_queue:
            self.ctx.loot_queue = self._drain_loot_queue()
            if not self.farming: return State.IDLE

        target = self._find_nearest_target()
        if not target:
            # Sem mobs — patrol se houver waypoint salvo
            if self.ctx.waypoint_wx is not None:
                return State.PATROLLING
            time.sleep(0.3)
            return State.IDLE

        self.ctx.target    = target
        self.ctx.target_wx = target["x"]
        self.ctx.target_wy = target["y"]
        self._attack_start = time.time()
        return State.SELECTING

    # ══════════════════════════════════════════
    # SELECTING — clica no mob e confirma via +0x290
    # ══════════════════════════════════════════
    def _state_selecting(self):
        t      = self.ctx.target
        wx, wy = self.ctx.target_wx, self.ctx.target_wy

        # Checa morte antes de qualquer coisa
        if self._is_dead(t["ptr"]):
            self.app._log(f"Alvo já morto antes do clique")
            self.ctx.dead_ptrs.add(t["ptr"])
            self.ctx.add_cooldown(wx, wy)
            self.ctx.mark_recent_dead(wx, wy)
            loot_val = self.mem.int_(t["ptr"] + OFF_LOOT_PTR)
            if loot_val:
                self.ctx.enqueue_loot(wx, wy)
                self.app._log(f"Loot enfileirado em ({wx:.1f},{wy:.1f})")
                return State.LOOTING
            return State.NEXT

        sx, sy = self._fresh_screen_tolerant(wx, wy)
        if sx is None:
            # Mob fora de tela — vai para o waypoint se houver, senão descarta alvo
            self.app._log(f"Alvo '{t['name']}' fora de tela — indo para o waypoint")
            self.ctx.target = None
            if self.ctx.waypoint_wx is not None:
                return State.PATROLLING
            return State.IDLE

        self.app._log(f"Selecionando '{t['name']}' em ({sx:.0f},{sy:.0f})")
        click_game(sx, sy)

        if not interruptible_sleep(T_SELECT_WAIT, self._alive): return State.IDLE

        # Se morreu durante o sleep
        if self._is_dead(t["ptr"]):
            self.app._log("Alvo morreu durante o clique")
            self.ctx.dead_ptrs.add(t["ptr"])
            self.ctx.add_cooldown(wx, wy)
            self.ctx.mark_recent_dead(wx, wy)
            loot_val = self.mem.int_(t["ptr"] + OFF_LOOT_PTR)
            if loot_val:
                self.ctx.enqueue_loot(wx, wy)
                self.app._log(f"Loot enfileirado em ({wx:.1f},{wy:.1f})")
                return State.LOOTING
            return State.NEXT

        # FIX1: Enter só se houver cadáver empilhado no tile
        if self._ui_loot_stack() == UI_STATE_OPEN:
            press_enter()
            time.sleep(0.15)

        if not interruptible_sleep(T_SELECT_ENTER, self._alive): return State.IDLE

        # Polling confirmação via +0x290
        deadline = time.time() + T_SELECT_CONFIRM
        while time.time() < deadline:
            if not self.farming: return State.IDLE

            if self._is_dead(t["ptr"]):
                self.app._log("Alvo morreu durante confirmação")
                self.ctx.kills += 1
                self.ctx.dead_ptrs.add(t["ptr"])
                self.ctx.add_cooldown(wx, wy)
                self.ctx.mark_recent_dead(wx, wy)
                loot_val = self.mem.int_(t["ptr"] + OFF_LOOT_PTR)
                if loot_val:
                    self.ctx.enqueue_loot(wx, wy)
                    self.app._log(f"Loot enfileirado em ({wx:.1f},{wy:.1f})")
                    return State.LOOTING
                return State.NEXT

            if self._is_mob_selected(t["ptr"]):
                self.app._log(f"Seleção confirmada!")
                self._skill_idx    = 0
                self._attack_start = time.time()
                return State.ATTACKING

            time.sleep(T_SELECT_HP_POLL)

        # Não confirmou em T_SELECT_CONFIRM segundos
        # Trata como morto: verifica loot e segue em frente
        self.app._log(f"Seleção não confirmada — tratando como morto")
        self.ctx.dead_ptrs.add(t["ptr"])
        self.ctx.add_cooldown(wx, wy)
        self.ctx.mark_recent_dead(wx, wy)
        loot_val = self.mem.int_(t["ptr"] + OFF_LOOT_PTR)
        if loot_val:
            self.ctx.enqueue_loot(wx, wy)
            self.app._log(f"Loot enfileirado em ({wx:.1f},{wy:.1f})")
            return State.LOOTING
        return State.NEXT

    # ══════════════════════════════════════════
    # ATTACKING — ciclo de skills até mob morrer
    # ══════════════════════════════════════════
    def _state_attacking(self):
        t       = self.ctx.target
        mob_ptr = t["ptr"]

        # ── Atualiza posição do mob em tempo real ──
        # O mob pode se mover até o player durante o combate.
        # Sempre lemos a posição atual da memória para que target_wx/wy
        # reflita onde o cadáver vai estar, não onde o mob estava ao ser selecionado.
        cur_wx = self.mem.int_(mob_ptr + OFF_WORLD_X) / 65536.0
        cur_wy = self.mem.int_(mob_ptr + OFF_WORLD_Y) / 65536.0
        if cur_wx != 0.0 and cur_wy != 0.0:
            self.ctx.target_wx = cur_wx
            self.ctx.target_wy = cur_wy

        # ── Verifica morte antes de qualquer skill ──
        if self._is_dead(mob_ptr):
            self.app._log(f"'{t['name']}' morreu! pos final: ({self.ctx.target_wx:.1f},{self.ctx.target_wy:.1f})")
            self.ctx.kills += 1
            self.ctx.dead_ptrs.add(mob_ptr)
            self.ctx.add_cooldown(self.ctx.target_wx, self.ctx.target_wy)
            self.ctx.mark_recent_dead(self.ctx.target_wx, self.ctx.target_wy)
            # FIX5: checa loot_ptr imediatamente — se zero, pula DEATH_WAIT direto para NEXT
            if self.mem.int_(mob_ptr + OFF_LOOT_PTR) == 0:
                self.app._log("Sem loot (loot_ptr=0), pulando DEATH_WAIT")
                return State.NEXT
            return State.DEATH_WAIT

        # ── Verifica se seleção foi perdida (+0x290) ──
        if not self._is_mob_selected(mob_ptr):
            # Re-checa morte antes de decidir (HP pode ter lag de 1-2 frames)
            if self._is_dead(mob_ptr):
                self.app._log(f"Seleção perdida — mob confirmado morto")
                self.ctx.kills += 1
                self.ctx.dead_ptrs.add(mob_ptr)
                self.ctx.add_cooldown(self.ctx.target_wx, self.ctx.target_wy)
                self.ctx.mark_recent_dead(self.ctx.target_wx, self.ctx.target_wy)
                if self.mem.int_(mob_ptr + OFF_LOOT_PTR) == 0:
                    self.app._log("Sem loot (loot_ptr=0), pulando DEATH_WAIT")
                    return State.NEXT
                return State.DEATH_WAIT
            cur_hp  = self.mem.int_(mob_ptr + OFF_CUR_HP)
            max_hp  = self.mem.int_(mob_ptr + OFF_MAX_HP)
            pct     = (cur_hp / max_hp * 100) if max_hp > 0 else 999
            if pct < 20 or cur_hp > max_hp:
                # HP baixo ou já inválido — vai morrer pela aura, não clica de novo
                self.app._log(f"Seleção perdida, HP={pct:.0f}% — aguardando morte pela aura")
                return State.DEATH_WAIT
            self.app._log(f"Seleção perdida, HP={pct:.0f}% — resselecionando")
            return State.SELECTING

        # ── Timeout geral do ataque ──
        if time.time() - self._attack_start > T_DEATH_TIMEOUT:
            self.app._log(f"Timeout! '{t['name']}' não morreu em {T_DEATH_TIMEOUT}s, pulando")
            self.ctx.dead_ptrs.add(mob_ptr)
            return State.NEXT

        # ── Dispara próxima skill ──
        vk, delay = SKILL_CYCLE[self._skill_idx % len(SKILL_CYCLE)]
        self._skill_idx += 1
        press_key(vk)

        # ── Aguarda o delay da skill, atualizando posição + checando morte ──
        elapsed = 0.0
        step    = 0.05
        while elapsed < delay:
            if not self.farming: return State.IDLE
            time.sleep(step)
            elapsed += step

            # Atualiza posição continuamente durante o delay
            wx = self.mem.int_(mob_ptr + OFF_WORLD_X) / 65536.0
            wy = self.mem.int_(mob_ptr + OFF_WORLD_Y) / 65536.0
            if wx != 0.0 and wy != 0.0:
                self.ctx.target_wx = wx
                self.ctx.target_wy = wy

            if self._is_dead(mob_ptr):
                self.app._log(f"'{t['name']}' morreu! pos final: ({self.ctx.target_wx:.1f},{self.ctx.target_wy:.1f})")
                self.ctx.kills += 1
                self.ctx.dead_ptrs.add(mob_ptr)
                self.ctx.add_cooldown(self.ctx.target_wx, self.ctx.target_wy)
                self.ctx.mark_recent_dead(self.ctx.target_wx, self.ctx.target_wy)
                # FIX5: checa loot_ptr imediatamente
                if self.mem.int_(mob_ptr + OFF_LOOT_PTR) == 0:
                    self.app._log("Sem loot (loot_ptr=0), pulando DEATH_WAIT")
                    return State.NEXT
                return State.DEATH_WAIT

            if not self._is_mob_selected(mob_ptr):
                # Re-checa morte antes de reselecionar (lag de leitura)
                if self._is_dead(mob_ptr):
                    self.app._log(f"Seleção perdida durante skill — mob confirmado morto")
                    self.ctx.kills += 1
                    self.ctx.dead_ptrs.add(mob_ptr)
                    self.ctx.add_cooldown(self.ctx.target_wx, self.ctx.target_wy)
                    self.ctx.mark_recent_dead(self.ctx.target_wx, self.ctx.target_wy)
                    if self.mem.int_(mob_ptr + OFF_LOOT_PTR) == 0:
                        self.app._log("Sem loot, pulando DEATH_WAIT")
                        return State.NEXT
                    return State.DEATH_WAIT
                cur_hp  = self.mem.int_(mob_ptr + OFF_CUR_HP)
                max_hp  = self.mem.int_(mob_ptr + OFF_MAX_HP)
                pct     = (cur_hp / max_hp * 100) if max_hp > 0 else 999
                if pct < 20 or cur_hp > max_hp:
                    self.app._log(f"Seleção perdida durante skill, HP={pct:.0f}% — aguardando morte")
                    return State.DEATH_WAIT
                self.app._log(f"Seleção perdida durante skill, HP={pct:.0f}% — resselecionando")
                return State.SELECTING

        return State.ATTACKING

    # ══════════════════════════════════════════
    # DEATH_WAIT — aguarda animação + polling do loot
    # ══════════════════════════════════════════
    def _state_death_wait(self):
        # Aguarda animação de morte
        if not interruptible_sleep(T_DEATH_WAIT, self._alive): return State.IDLE

        mob_ptr = self.ctx.target["ptr"]
        wx, wy  = self.ctx.target_wx, self.ctx.target_wy

        # ── Polling do loot_ptr (evita falso-negativo de leitura prematura) ──
        loot_found = False
        for attempt in range(T_LOOT_POLL_TRIES):
            if not self.farming: return State.IDLE
            loot_val = self.mem.int_(mob_ptr + OFF_LOOT_PTR)
            if loot_val != 0:
                loot_found = True
                self.app._log(f"Loot detectado (tentativa {attempt+1}/{T_LOOT_POLL_TRIES})")
                break
            if attempt < T_LOOT_POLL_TRIES - 1:
                time.sleep(T_LOOT_POLL_DELAY)

        if not loot_found:
            self.app._log("Sem loot, próximo alvo")
            return State.NEXT

        # ── Tem loot — verifica se há vivo na coordenada (cadáver sobreposto) ──
        if self._has_alive_at(wx, wy):
            entry = self.ctx.enqueue_loot(wx, wy)
            self.app._log(f"Loot na fila (vivo na coord). Fila: {len(self.ctx.loot_queue)} | {entry}")
            return State.LOOT_PENDING  # fica em LOOT_PENDING até área limpar

        # Loot livre para coletar agora
        entry = self.ctx.enqueue_loot(wx, wy)
        # Seta target do loot como o próximo a processar e vai para LOOTING
        return State.LOOTING

    # ══════════════════════════════════════════
    # LOOTING — coleta todos os cadáveres da fila que estão livres
    # ══════════════════════════════════════════
    def _state_looting(self):
        self.ctx.loot_queue = self._drain_loot_queue()
        return State.NEXT

    # ══════════════════════════════════════════
    # LOOT_PENDING — aguarda área limpa (ainda há vivos na coord)
    # ══════════════════════════════════════════
    def _state_loot_pending(self):
        # Tenta drenar o que já está livre
        self.ctx.loot_queue = self._drain_loot_queue()
        if not self.ctx.loot_queue:
            return State.NEXT

        # Ainda há loot bloqueado — verifica se tem alvo disponível para atacar enquanto espera
        next_target = self._find_nearest_target()
        if next_target:
            # Tem mob vivo para matar — ataca e volta para coletar depois via IDLE
            self.app._log(f"Loot pendente mas há alvo disponível, atacando primeiro")
            self.ctx.target    = next_target
            self.ctx.target_wx = next_target["x"]
            self.ctx.target_wy = next_target["y"]
            self._attack_start = time.time()
            return State.SELECTING

        # Sem alvo disponível — aguarda um pouco e tenta drenar de novo
        time.sleep(0.5)
        return State.LOOT_PENDING

    # ══════════════════════════════════════════
    # NEXT — pausa antes do próximo alvo
    # ══════════════════════════════════════════
    def _state_next(self):
        interruptible_sleep(T_NEXT_WAIT, self._alive)
        self.app._log(self.ctx.stats_str())
        return State.IDLE

    # ══════════════════════════════════════════
    # PATROLLING — anda até o waypoint quando sem mobs
    # ══════════════════════════════════════════
    def _state_patrolling(self):
        if not self.farming: return State.IDLE
        player = self.player
        if not player: return State.IDLE

        wx = self.ctx.waypoint_wx
        wy = self.ctx.waypoint_wy

        px, py = player["x"], player["y"]
        dist   = math.sqrt((px - wx)**2 + (py - wy)**2)

        # Chegou perto o suficiente — aguarda respawn e volta ao IDLE
        if dist <= T_PATROL_ARRIVE_R:
            self.app._log(f"[Patrol] Chegou ao waypoint ({wx:.1f},{wy:.1f}), aguardando respawn...")
            interruptible_sleep(T_PATROL_WAIT_SPAWN, self._alive)
            return State.IDLE

        # Verifica se já apareceu algum mob — se sim, para o patrol imediatamente
        if self._find_nearest_target():
            self.app._log("[Patrol] Mob detectado, retomando farm")
            return State.IDLE

        # Clica em direção ao waypoint com até T_PATROL_STUCK_MAX tentativas
        stuck_count = 0
        while stuck_count < T_PATROL_STUCK_MAX:
            if not self.farming: return State.IDLE

            # Mob apareceu? Para
            if self._find_nearest_target():
                self.app._log("[Patrol] Mob detectado durante movimento, retomando farm")
                return State.IDLE

            # Calcula posição de tela do waypoint
            sx, sy = self._fresh_screen(wx, wy)
            if sx is None:
                # Waypoint fora da tela — clica na borda na direção correta
                sx, sy = self._clamp_direction_to_screen(px, py, wx, wy)
                if sx is None:
                    self.app._log("[Patrol] Não foi possível calcular direção, abortando patrol")
                    return State.IDLE

            self.app._log(f"[Patrol] Movendo para ({wx:.1f},{wy:.1f}), dist={dist:.1f} — clicando ({sx:.0f},{sy:.0f})")
            click_game(sx, sy)

            # Salva posição antes de aguardar
            prev_x, prev_y = px, py
            interruptible_sleep(T_PATROL_MOVE_WAIT, self._alive)
            if not self.farming: return State.IDLE

            # Atualiza posição
            player = self.player
            if not player: return State.IDLE
            px, py = player["x"], player["y"]
            moved  = math.sqrt((px - prev_x)**2 + (py - prev_y)**2)

            if moved < 0.3:
                stuck_count += 1
                self.app._log(f"[Patrol] Jogador não moveu (tentativa {stuck_count}/{T_PATROL_STUCK_MAX})")
            else:
                stuck_count = 0  # moveu — reseta contador de stuck

            dist = math.sqrt((px - wx)**2 + (py - wy)**2)
            if dist <= T_PATROL_ARRIVE_R:
                self.app._log(f"[Patrol] Chegou ao waypoint!")
                interruptible_sleep(T_PATROL_WAIT_SPAWN, self._alive)
                return State.IDLE

        self.app._log("[Patrol] Preso — desistindo e voltando ao IDLE")
        return State.IDLE

    def _clamp_direction_to_screen(self, px, py, tx, ty):
        """Quando o destino está fora da tela, calcula um ponto na borda da tela
        na direção correta para clicar e fazer o personagem se mover."""
        rect = get_game_window_rect()
        if not rect: return None, None
        gx, gy, gr, gb = rect
        dw, dh = gr - gx, gb - gy

        cam = self._current_cam(dw, dh)
        if not cam: return None, None

        # Posição de tela do player (centro de referência)
        cx, cy = world_to_screen(cam, px, py, dw, dh)
        if cx is None: return None, None

        # Direção mundo → normaliza → projeta na tela
        dx, dy = tx - px, ty - py
        length = math.sqrt(dx*dx + dy*dy)
        if length == 0: return None, None
        dx, dy = dx / length, dy / length

        # Projeta 200px na direção correta a partir do centro do player na tela
        PROJ = 200
        sx = cx + dx * PROJ
        sy = cy + dy * PROJ

        # Clamp nos limites da janela com margem de 20px
        sx = max(20, min(dw - 20, sx))
        sy = max(20, min(dh - 20, sy))
        return sx, sy

    # ══════════════════════════════════════════
    # Helpers internos
    # ══════════════════════════════════════════
    def _is_dead(self, mob_ptr) -> bool:
        """Morte detectada por HP inválido (cur_hp > max_hp) OU vtable DEAD.
        Quando o mob morre, o HP vira lixo (número absurdo > max_hp).
        O vtable muda depois — serve como confirmação secundária."""
        cur = self.mem.int_(mob_ptr + OFF_CUR_HP)
        max_ = self.mem.int_(mob_ptr + OFF_MAX_HP)
        if max_ > 0 and cur > max_:
            return True
        vtable = self.mem.int_(mob_ptr)
        return vtable == VTABLE_DEAD

    def _has_alive_at(self, wx, wy, radius=1.0) -> bool:
        """True se houver mob vivo dentro do raio da coordenada.
        Lê árvore direto da memória para evitar delay da snapshot."""
        player_ptr = self.player["ptr"] if self.player else None
        for e in self._fresh_entities():
            if e["ptr"] == player_ptr: continue
            if self._is_dead(e["ptr"]): continue
            if math.sqrt((e["x"] - wx)**2 + (e["y"] - wy)**2) <= radius:
                return True
        return False

    def _fresh_screen(self, wx, wy):
        """Recalcula posição de tela usando câmera e rect atuais.
        Evita usar coordenadas stale salvas no momento da seleção."""
        rect = get_game_window_rect()
        if not rect: return None, None
        gx, gy, gr, gb = rect
        dw, dh = gr - gx, gb - gy
        cam = self._current_cam(dw, dh)
        if not cam: return None, None
        sx, sy = world_to_screen(cam, wx, wy, dw, dh)
        if sx is None: return None, None
        if not (0 <= sx <= dw and 0 <= sy <= dh):
            return None, None
        return sx, sy

    def _fresh_screen_tolerant(self, wx, wy, margin=40):
        """Igual a _fresh_screen mas com margem extra nos limites.
        Usado para checar se um mob está 'visível o suficiente' para clicar,
        absorvendo pequenos erros de calibração da fórmula world_to_screen."""
        rect = get_game_window_rect()
        if not rect: return None, None
        gx, gy, gr, gb = rect
        dw, dh = gr - gx, gb - gy
        cam = self._current_cam(dw, dh)
        if not cam: return None, None
        sx, sy = world_to_screen(cam, wx, wy, dw, dh)
        if sx is None: return None, None
        if not (-margin <= sx <= dw + margin and -margin <= sy <= dh + margin):
            return None, None
        # Clamp para garantir que o clique vai dentro da janela
        sx = max(0, min(dw, sx))
        sy = max(0, min(dh, sy))
        return sx, sy

    def _current_cam(self, dw=800, dh=600):
        try:
            sys_inst = self.mem.ptr(STATIC_SYSTEM_INSTANCE)
            if not sys_inst: return None
            gm = self.mem.ptr(sys_inst + OFF_GAMEMANAGER)
            if not gm: return None
            return read_camera(self.mem, gm)
        except:
            return None

    def _fresh_entities(self):
        """Lê a árvore de entidades direto da memória agora.
        Não usa self.entities (snapshot). Usado em _find_nearest_target
        para garantir que a lista está atualizada no momento da decisão."""
        try:
            sys_inst = self.mem.ptr(STATIC_SYSTEM_INSTANCE)
            if not sys_inst: return []
            gm = self.mem.ptr(sys_inst + OFF_GAMEMANAGER)
            if not gm: return []
            rect = get_game_window_rect()
            if not rect: return []
            gx, gy, gr, gb = rect
            dw, dh = gr - gx, gb - gy
            cam = read_camera(self.mem, gm)
            _, _, entities = collect(self.mem, gm, cam, dw, dh)
            return entities
        except:
            return []

    def _find_nearest_target(self):
        player  = self.player
        targets = self.app._get_selected_names()
        if not player or not targets: return None
        px, py  = player["x"], player["y"]

        entities = self._fresh_entities()
        if not entities: return None

        best      = None
        best_dist = float("inf")

        for e in entities:
            if e["ptr"] == player["ptr"]: continue
            if e["name"].lower() not in targets: continue
            if e["ptr"] in self.ctx.dead_ptrs:
                # [FIX6] Verifica se o endereço foi reaproveitado por um novo spawn
                if self._is_respawned(e):
                    self.app._log(f"  [RESPAWN] '{e['name']}' em dead_ptrs mas parece novo spawn — removendo bloqueio")
                    self.ctx.dead_ptrs.discard(e["ptr"])
                else:
                    self.app._log(f"  [SKIP] '{e['name']}' — em dead_ptrs")
                    continue
            if self._is_dead(e["ptr"]):
                self.app._log(f"  [SKIP] '{e['name']}' — _is_dead=True")
                continue
            if self.ctx.in_cooldown(e["x"], e["y"]):
                dist_cd = math.sqrt((e["x"] - px)**2 + (e["y"] - py)**2)
                if dist_cd > 2.0:
                    self.app._log(f"  [SKIP] '{e['name']}' — cooldown coord dist={dist_cd:.1f}")
                    continue
            if self.ctx.near_recent_dead(e["x"], e["y"]):
                # [FIX6] Antes de bloquear, verifica se o mob se moveu ou tem HP válido
                if self._is_respawned(e):
                    self.app._log(f"  [RESPAWN] '{e['name']}' perto de morte recente mas parece novo spawn — liberando")
                else:
                    self.app._log(f"  [SKIP] '{e['name']}' — near_recent_dead")
                    continue

            dist = math.sqrt((e["x"] - px)**2 + (e["y"] - py)**2)
            if dist > MAX_TARGET_DIST:
                self.app._log(f"  [SKIP] '{e['name']}' — dist={dist:.1f} > MAX={MAX_TARGET_DIST}")
                continue
            if dist < best_dist:
                best_dist = dist
                best      = e

        if best:
            self.app._log(f"[Target] '{best['name']}' dist={best_dist:.1f} em ({best['x']:.1f},{best['y']:.1f})")

        return best

    def _drain_loot_queue(self) -> list:
        """Processa a fila de loot. Coleta os que estão livres, devolve os pendentes."""
        remaining = []
        for entry in self.ctx.loot_queue:
            if not self.farming: break
            if self._has_alive_at(entry.wx, entry.wy):
                remaining.append(entry)
                self.app._log(f"Loot ainda pendente (vivo na coord): {entry}")
            else:
                self._collect_entry(entry)
        return remaining

    def _collect_entry(self, entry: LootEntry):
        self.app._log(f"Coletando loot em ({entry.wx:.1f},{entry.wy:.1f}) count={entry.count}")
        collected = 0
        MAX_ATTEMPTS = 5

        for attempt in range(MAX_ATTEMPTS):
            if not self.farming: return

            # 1. Posição de tela do cadáver
            sx, sy = self._fresh_screen(entry.wx, entry.wy)
            if sx is None:
                self.app._log(f"  [{attempt+1}] Cadáver fora de tela, encerrando")
                break

            # 2. Clica no cadáver
            self.app._log(f"  [{attempt+1}] Clicando em ({sx:.0f},{sy:.0f})")
            click_game(sx, sy)

            # 3. Aguarda a janela abrir (stack ou simples) — até 4s, poll 50ms
            t0 = time.time()
            resultado = None
            while time.time() - t0 < 4.0:
                if not self.farming: return
                stack  = self._ui_loot_stack()
                simple = self._ui_loot_simple()
                self.app._log(f"  [{attempt+1}] UI stack={stack} simple={simple}")
                if stack == UI_STATE_OPEN:
                    resultado = "stack"
                    break
                if simple == UI_STATE_OPEN:
                    resultado = "simples"
                    break
                time.sleep(0.05)

            if resultado is None:
                self.app._log(f"  [{attempt+1}] Janela não abriu em 4s — cadáver já coletado ou sumiu, encerrando")
                break

            # 4. Stack aberto: aguarda 0.8s e pressiona Enter para selecionar cadáver
            if resultado == "stack":
                self.app._log(f"  [{attempt+1}] Stack aberto → aguardando 0.8s → Enter")
                time.sleep(0.8)
                if not self.farming: return
                press_enter()
                # Aguarda virar loot simples
                t0b = time.time()
                while time.time() - t0b < 3.0:
                    if not self.farming: return
                    if self._ui_loot_simple() == UI_STATE_OPEN:
                        resultado = "simples"
                        break
                    time.sleep(0.05)
                if resultado != "simples":
                    self.app._log(f"  [{attempt+1}] Stack não virou simples — encerrando")
                    break

            # 5. Loot simples aberto: aguarda 0.8s e pressiona Enter para coletar
            if resultado == "simples":
                self.app._log(f"  [{attempt+1}] Loot simples aberto → aguardando 0.8s → Enter")
                time.sleep(0.8)
                if not self.farming: return
                press_enter()
                # Aguarda janela fechar (confirma coleta)
                t0c = time.time()
                fechou = False
                while time.time() - t0c < 4.0:
                    if not self.farming: return
                    if self._ui_loot_simple() == UI_STATE_NORMAL:
                        self.app._log(f"  [{attempt+1}] Janela fechou → coletado")
                        collected += 1
                        fechou = True
                        break
                    time.sleep(0.05)
                if not fechou:
                    self.app._log(f"  [{attempt+1}] Janela não fechou em 4s, encerrando")
                    break
                # Coletou com sucesso — sai sempre. Se entry.count > 1 (stack),
                # os demais cadáveres serão coletados na próxima entrada na fila.
                break

        self.ctx.loots += collected
        self.app._log(f"  Total coletado: {collected}/{entry.count}")

    def _selected_entity(self) -> int:
        """Lê player+0x290: ptr da entidade selecionada. 0 = nenhuma / fora de combate."""
        player = self.player
        if not player: return 0
        return self.mem.int_(player["ptr"] + OFF_SELECTED_ENTITY)

    def _is_mob_selected(self, mob_ptr: int) -> bool:
        """True se o mob_ptr for exatamente a entidade selecionada pelo player."""
        return self._selected_entity() == mob_ptr

    def _is_respawned(self, e: dict) -> bool:
        """Detecta se um mob que está em dead_ptrs ou near_recent_dead é na verdade
        um novo spawn reutilizando o mesmo endereço ou coordenada.

        Dois critérios independentes — qualquer um confirmado = ressurreição:
          1. HP válido: 0 < cur_hp <= max_hp  E  vtable != DEAD
             (o endereço tem dados de um mob vivo, não do morto anterior)
          2. Movimento: posição atual difere da posição de morte registrada
             em mais de T_RESPAWN_MOVE_MIN unidades
             (o mob nasceu e já andou — endereço foi reaproveitado)
        """
        ptr    = e["ptr"]
        cur_hp = self.mem.int_(ptr + OFF_CUR_HP)
        max_hp = self.mem.int_(ptr + OFF_MAX_HP)
        vtable = self.mem.int_(ptr)

        # Critério 1 — HP saudável + vtable vivo
        hp_valid  = max_hp > 0 and 0 < cur_hp <= max_hp
        vtbl_alive = vtable != VTABLE_DEAD
        if hp_valid and vtbl_alive:
            return True

        # Critério 2 — Verificar movimento em relação às posições de morte recentes
        ex, ey = e["x"], e["y"]
        now    = time.time()
        for rx, ry, ts in self.ctx.recent_dead:
            if now - ts >= 3.0:
                continue  # entrada expirada, ignora
            dist_from_death = math.sqrt((ex - rx)**2 + (ey - ry)**2)
            if dist_from_death >= T_RESPAWN_MOVE_MIN:
                return True  # mob está longe do ponto de morte → novo spawn se movendo

        return False

    def _gm_addr(self):
        """Retorna o endereço do GameManager em tempo real."""
        try:
            sys_inst = self.mem.ptr(STATIC_SYSTEM_INSTANCE)
            if not sys_inst: return None
            return self.mem.ptr(sys_inst + OFF_GAMEMANAGER)
        except:
            return None

    def _ui_loot_simple(self) -> int:
        """Lê GM+0x0C0: 3=fechado, 4=loot simples aberto."""
        gm = self._gm_addr()
        if not gm: return UI_STATE_NORMAL
        return self.mem.int_(gm + OFF_UI_LOOT_SIMPLE)

    def _ui_loot_stack(self) -> int:
        """Lê GM+0x014: 3=fechado, 4=seleção de cadáver empilhado aberta."""
        gm = self._gm_addr()
        if not gm: return UI_STATE_NORMAL
        return self.mem.int_(gm + OFF_UI_LOOT_STACK)

    def _wait_ui(self, check_fn, timeout, label) -> bool:
        """Aguarda check_fn() retornar True dentro do timeout.
        Retorna True se condição atingida, False se timeout ou farm parado."""
        deadline = time.time() + timeout
        while time.time() < deadline:
            if not self.farming: return False
            if check_fn(): return True
            time.sleep(T_UI_POLL)
        self.app._log(f"Timeout UI: {label}")
        return False



# ──────────────────────────────────────────────
# App (UI + loop)
# ──────────────────────────────────────────────
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Warspear - AutoFarm v14")
        self.configure(bg=BG)
        self.geometry("1100x720")
        self.resizable(True, True)

        self.pm           = None
        self.mem          = None
        self.running      = False
        self._farming     = False
        self._farm_thread = None
        self._entities    = []
        self._player      = None
        self._windows_list: list = []   # [(hwnd, title, pid), ...]

        self._target_vars    = {}
        self._target_widgets = {}
        self._prev_entity_map: dict = {}

        self._fsm = FarmFSM(self)

        self._build_ui()
        self.bind_all("<F5>", lambda e: self._click_nearest_any())

    # ── UI ────────────────────────────────────
    def _build_ui(self):
        top = tk.Frame(self, bg=BG, pady=6)
        top.pack(fill="x", padx=10)
        tk.Label(top, text="WARSPEAR AUTOFARM v14", font=("Consolas", 12, "bold"),
                 bg=BG, fg=ACCENT).pack(side="left")
        self.lbl_status = tk.Label(top, text="DESCONECTADO", font=FONT_B, bg=BG, fg=ACCENT)
        self.lbl_status.pack(side="right")

        tk.Frame(self, bg=BG3, height=1).pack(fill="x")

        # ── Painel de seleção de instância ──
        inst_f = tk.Frame(self, bg=BG2, pady=6)
        inst_f.pack(fill="x", padx=10, pady=(6, 0))

        tk.Label(inst_f, text="Instância do jogo:", font=FONT_M,
                 bg=BG2, fg=TEXT, width=18, anchor="w").pack(side="left")
        self._instance_var   = tk.StringVar(value="— selecione —")
        self._instance_combo = ttk.Combobox(inst_f, textvariable=self._instance_var,
                                             state="readonly", font=FONT_M, width=52)
        self._instance_combo.pack(side="left", padx=(0, 6))
        tk.Button(inst_f, text="🔄 Atualizar", font=FONT_M, bg=BG3, fg=CYAN,
                  relief="flat", padx=8,
                  command=self._refresh_instances).pack(side="left", padx=(0, 6))
        self.btn_connect = tk.Button(inst_f, text="🔌 Conectar", font=FONT_B,
                                     bg=CYAN, fg=BG, relief="flat", padx=12,
                                     command=self._connect_instance)
        self.btn_connect.pack(side="left")

        tk.Frame(self, bg=BG3, height=1).pack(fill="x", pady=(6, 0))

        ctrl = tk.Frame(self, bg=BG2, pady=8)
        ctrl.pack(fill="x", padx=10, pady=(6, 0))

        self.btn_start = tk.Button(ctrl, text="▶ START", font=FONT_B,
                                   bg=GREEN, fg=BG, relief="flat", padx=14,
                                   command=self._start_farm)
        self.btn_start.pack(side="left", padx=(0, 6))

        self.btn_stop = tk.Button(ctrl, text="■ STOP", font=FONT_B,
                                  bg=ACCENT, fg="white", relief="flat", padx=14,
                                  state="disabled", command=self._stop_farm)
        self.btn_stop.pack(side="left")

        self.btn_waypoint = tk.Button(ctrl, text="📍 Salvar posição", font=FONT_M,
                                      bg=BG3, fg=CYAN, relief="flat", padx=10,
                                      command=self._save_waypoint)
        self.btn_waypoint.pack(side="left", padx=(10, 0))

        self.lbl_waypoint = tk.Label(ctrl, text="Waypoint: —", font=FONT_M, bg=BG2, fg=DIM)
        self.lbl_waypoint.pack(side="left", padx=6)

        self.lbl_farm_status = tk.Label(ctrl, text="Parado", font=FONT_M, bg=BG2, fg=DIM)
        self.lbl_farm_status.pack(side="left", padx=16)

        # Label de estatísticas (direita do ctrl)
        self.lbl_stats = tk.Label(ctrl, text="", font=FONT_M, bg=BG2, fg=CYAN)
        self.lbl_stats.pack(side="right", padx=8)

        tk.Frame(self, bg=BG3, height=1).pack(fill="x", pady=(6, 0))

        main = tk.Frame(self, bg=BG)
        main.pack(fill="both", expand=True, padx=10, pady=6)

        # ── Painel de alvos ──
        targets_outer = tk.LabelFrame(main, text=" Alvos ", font=FONT_B,
                                      bg=BG2, fg=CYAN, bd=1, relief="solid", width=180)
        targets_outer.pack(side="left", fill="y", padx=(0, 8))
        targets_outer.pack_propagate(False)

        self._cb_canvas = tk.Canvas(targets_outer, bg=BG2, highlightthickness=0)
        cb_scroll = ttk.Scrollbar(targets_outer, orient="vertical",
                                  command=self._cb_canvas.yview)
        self._cb_canvas.configure(yscrollcommand=cb_scroll.set)
        cb_scroll.pack(side="right", fill="y")
        self._cb_canvas.pack(side="left", fill="both", expand=True)

        self._cb_frame = tk.Frame(self._cb_canvas, bg=BG2)
        self._cb_canvas_window = self._cb_canvas.create_window(
            (0, 0), window=self._cb_frame, anchor="nw")
        self._cb_frame.bind("<Configure>", lambda e: self._cb_canvas.configure(
            scrollregion=self._cb_canvas.bbox("all")))
        self._cb_canvas.bind("<Configure>", lambda e: self._cb_canvas.itemconfig(
            self._cb_canvas_window, width=e.width))

        btn_frame = tk.Frame(targets_outer, bg=BG2)
        btn_frame.pack(fill="x", padx=4, pady=(0, 4))
        tk.Button(btn_frame, text="Marcar todos", font=FONT_M, bg=BG3, fg=TEXT,
                  relief="flat", command=self._check_all).pack(fill="x", pady=(0, 2))
        tk.Button(btn_frame, text="Desmarcar todos", font=FONT_M, bg=BG3, fg=DIM,
                  relief="flat", command=self._uncheck_all).pack(fill="x")

        # ── Tabela ──
        tbl  = tk.Frame(main, bg=BG)
        tbl.pack(side="left", fill="both", expand=True)

        cols    = ("ptr", "name", "hp", "pos", "screen")
        headers = ("Ptr", "Nome", "HP", "Mundo", "Tela")
        widths  = (110, 150, 120, 130, 110)

        style = ttk.Style(self)
        style.theme_use("clam")
        style.configure("W.Treeview", background=BG2, foreground=TEXT,
                        fieldbackground=BG2, rowheight=20, font=FONT_M, borderwidth=0)
        style.configure("W.Treeview.Heading", background=BG3, foreground=YELLOW,
                        font=FONT_B, relief="flat")
        style.map("W.Treeview",
                  background=[("selected", BG3)], foreground=[("selected", ACCENT)])

        self.tree_view = ttk.Treeview(tbl, columns=cols, show="headings", style="W.Treeview")
        for col, hdr, w in zip(cols, headers, widths):
            self.tree_view.heading(col, text=hdr)
            self.tree_view.column(col, width=w, anchor="w")
        self.tree_view.tag_configure("target",  foreground=YELLOW)
        self.tree_view.tag_configure("dead",    foreground=DIM)
        self.tree_view.tag_configure("loot_q",  foreground=CYAN)
        vsb = ttk.Scrollbar(tbl, orient="vertical", command=self.tree_view.yview)
        self.tree_view.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        self.tree_view.pack(fill="both", expand=True)

        # ── Log ──
        log_f = tk.LabelFrame(main, text=" Log ", font=FONT_B,
                               bg=BG2, fg=YELLOW, bd=1, relief="solid", width=260)
        log_f.pack(side="right", fill="y", padx=(8, 0))
        log_f.pack_propagate(False)
        self.log_text = tk.Text(log_f, bg=BG2, fg=TEXT, font=FONT_M,
                                state="disabled", wrap="word",
                                borderwidth=0, highlightthickness=0)
        self.log_text.pack(fill="both", expand=True, padx=4, pady=4)

        # ── Estado da FSM (indicador visual) ──
        fsm_f = tk.Frame(self, bg=BG2, pady=3)
        fsm_f.pack(fill="x", padx=10)
        tk.Label(fsm_f, text="Estado:", font=FONT_M, bg=BG2, fg=DIM).pack(side="left")
        self.lbl_fsm_state = tk.Label(fsm_f, text="IDLE", font=FONT_B, bg=BG2, fg=DIM)
        self.lbl_fsm_state.pack(side="left", padx=6)
        tk.Label(fsm_f, text="Fila loot:", font=FONT_M, bg=BG2, fg=DIM).pack(side="left", padx=(20, 0))
        self.lbl_loot_queue = tk.Label(fsm_f, text="0", font=FONT_B, bg=BG2, fg=CYAN)
        self.lbl_loot_queue.pack(side="left", padx=4)

        foot = tk.Frame(self, bg=BG, pady=4)
        foot.pack(fill="x", padx=10)
        self.lbl_count = tk.Label(foot, text="Entidades: 0", font=FONT_M, bg=BG, fg=DIM)
        self.lbl_count.pack(side="left")
        self.lbl_time = tk.Label(foot, text="", font=FONT_M, bg=BG, fg=DIM)
        self.lbl_time.pack(side="right")

        # Popula combo de instâncias ao abrir
        self.after(100, self._refresh_instances)

    # ── Checkboxes ────────────────────────────
    def _update_checkboxes(self, names_on_map):
        changed = False
        for name in names_on_map:
            if name not in self._target_vars:
                var = tk.BooleanVar(value=False)
                self._target_vars[name] = var
                cb = tk.Checkbutton(
                    self._cb_frame, text=name, variable=var,
                    bg=BG2, fg=TEXT, selectcolor=BG3,
                    activebackground=BG2, activeforeground=CYAN,
                    font=FONT_M, anchor="w", relief="flat",
                    command=lambda n=name: self._on_checkbox(n)
                )
                cb.pack(fill="x", padx=6, pady=1)
                self._target_widgets[name] = cb
                changed = True

        gone = [n for n in list(self._target_vars) if n not in names_on_map]
        for name in gone:
            if not self._target_vars[name].get():
                self._target_widgets[name].destroy()
                del self._target_vars[name]
                del self._target_widgets[name]
                changed = True

        if changed:
            self._cb_canvas.configure(scrollregion=self._cb_canvas.bbox("all"))

    def _on_checkbox(self, name):
        checked = self._target_vars[name].get()
        w = self._target_widgets.get(name)
        if w: w.config(fg=YELLOW if checked else TEXT)

    def _check_all(self):
        for name in self._target_vars:
            self._target_vars[name].set(True)
            self._on_checkbox(name)

    def _uncheck_all(self):
        for name in self._target_vars:
            self._target_vars[name].set(False)
            self._on_checkbox(name)

    def _get_selected_names(self):
        return {n.lower() for n, v in self._target_vars.items() if v.get()}

    # ── Log ───────────────────────────────────
    def _log(self, msg):
        ts = time.strftime("%H:%M:%S")
        def _do():
            self.log_text.config(state="normal")
            self.log_text.insert("end", f"[{ts}] {msg}\n")
            self.log_text.see("end")
            self.log_text.config(state="disabled")
        self.after(0, _do)

    def _set_farm_status(self, msg, color=GREEN):
        self.after(0, lambda: self.lbl_farm_status.config(text=msg, fg=color))

    # ── Farm ──────────────────────────────────
    def _start_farm(self):
        if not self._get_selected_names():
            self._log("Marque pelo menos um alvo!")
            return
        if self._farming: return
        self._farming = True
        self._fsm.ctx.reset()
        self.btn_start.config(state="disabled")
        self.btn_stop.config(state="normal")
        names = ", ".join(n for n, v in self._target_vars.items() if v.get())
        self._set_farm_status(f"Farmando: {names}", GREEN)
        self._log(f"Iniciando farm: {names}")
        self._farm_thread = threading.Thread(target=self._farm_loop, daemon=True)
        self._farm_thread.start()

    def _stop_farm(self):
        self._farming = False
        self.btn_start.config(state="normal")
        self.btn_stop.config(state="disabled")
        self._set_farm_status("Parado", DIM)
        self._log(f"Farm parado. {self._fsm.ctx.stats_str()}")

    def _save_waypoint(self):
        """Salva a posição atual do player como waypoint de patrol."""
        player = self._player
        if not player:
            self._log("Waypoint: player não encontrado")
            return
        wx, wy = player["x"], player["y"]
        self._fsm.ctx.waypoint_wx = wx
        self._fsm.ctx.waypoint_wy = wy
        self.lbl_waypoint.config(text=f"Waypoint: ({wx:.1f}, {wy:.1f})", fg=CYAN)
        self._log(f"📍 Waypoint salvo em ({wx:.1f}, {wy:.1f})")

    def _farm_loop(self):
        """Loop principal — apenas chama fsm.step() e atualiza o estado."""
        fsm = self._fsm
        while self._farming:
            try:
                new_state = fsm.step()
                fsm.transition(new_state)
                # Atualiza indicadores na UI
                self.after(0, self._update_fsm_ui)
            except Exception as e:
                self._log(f"[ERRO FSM] {e}")
                time.sleep(0.5)
        self._set_farm_status("Parado", DIM)

    def _update_fsm_ui(self):
        ctx = self._fsm.ctx
        label, color = STATE_LABELS.get(ctx.state, ("?", DIM))
        self.lbl_fsm_state.config(text=ctx.state.name, fg=color)
        self.lbl_loot_queue.config(text=str(len(ctx.loot_queue)))
        if self._farming:
            self.lbl_stats.config(text=ctx.stats_str())

    # ── Seleção de instância ──────────────────
    def _refresh_instances(self):
        wins = enum_warspear_windows()
        self._windows_list = wins
        if not wins:
            self._instance_combo["values"] = ["Nenhuma janela Warspear encontrada"]
            self._instance_combo.current(0)
        else:
            labels = [f"[PID {pid}]  {title}" for hwnd, title, pid in wins]
            self._instance_combo["values"] = labels
            self._instance_combo.current(0)
        self._log(f"Instâncias encontradas: {len(wins)}")

    def _connect_instance(self):
        idx = self._instance_combo.current()
        if idx < 0 or idx >= len(self._windows_list):
            self._log("Selecione uma instância válida!")
            return
        hwnd, title, pid = self._windows_list[idx]

        global _selected_hwnd
        _selected_hwnd = hwnd
        self._log(f"Conectando à instância [PID {pid}] hwnd=0x{hwnd:X}...")

        def do_connect():
            try:
                pm = pymem.Pymem()
                pm.open_process_from_id(pid)
                self.pm, self.mem = pm, MemReader(pm)
                self.running = True
                self.after(0, lambda: self.lbl_status.config(
                    text=f"CONECTADO [PID {pid}]", fg=GREEN))
                self.after(0, lambda: self.btn_connect.config(
                    text=f"✓ PID {pid}", bg=GREEN, fg=BG, state="normal"))
                self._log(f"✓ Conectado ao processo PID {pid}")
                self._loop()
            except Exception as e:
                self.after(0, lambda: self.lbl_status.config(text="ERRO DE CONEXÃO", fg=ACCENT))
                self._log(f"Erro ao conectar: {e}")

        threading.Thread(target=do_connect, daemon=True).start()

    def _loop(self):
        def run():
            while self.running:
                try: self._update()
                except: pass
                time.sleep(0.1)
        threading.Thread(target=run, daemon=True).start()

    def _update(self):
        mem = self.mem
        sys_inst = mem.ptr(STATIC_SYSTEM_INSTANCE)
        if not sys_inst: return
        gm = mem.ptr(sys_inst + OFF_GAMEMANAGER)
        if not gm: return
        game_rect = get_game_window_rect()
        if not game_rect: return
        gx, gy, gr, gb = game_rect
        dw, dh = gr - gx, gb - gy
        cam    = read_camera(mem, gm)
        pl_obj = mem.ptr(gm + OFF_PLAYER_OBJ)
        player = read_entity(mem, pl_obj, cam=cam, dw=dw, dh=dh) if pl_obj else None
        _, _, entities = collect(mem, gm, cam, dw, dh)

        # ── Monitoramento de mortes por AoE ──────────────────────────────────
        # Compara lista atual com anterior. Mobs que sumiram e tinham loot_ptr
        # são enfileirados automaticamente — mesmo sem serem o alvo principal.
        if self._farming:
            current_map = {e["ptr"]: e for e in entities}
            player_ptr  = player["ptr"] if player else None
            selected    = self._get_selected_names()

            for ptr, prev_e in self._prev_entity_map.items():
                if ptr == player_ptr: continue
                if prev_e["name"].lower() not in selected: continue
                # Sumiu da lista agora?
                if ptr not in current_map:
                    loot_val = mem.int_(ptr + OFF_LOOT_PTR)
                    self._log(f"[AoE DEBUG] '{prev_e['name']}' sumiu — loot_ptr=0x{loot_val:X} em ({prev_e['x']:.1f},{prev_e['y']:.1f})")
                    if loot_val:
                        wx = prev_e["x"]
                        wy = prev_e["y"]
                        entry = self._fsm.ctx.enqueue_loot(wx, wy)
                        self._log(f"[AoE] '{prev_e['name']}' morreu em ({wx:.1f},{wy:.1f}) → loot enfileirado ({entry.count} no local)")
                        # Se era o alvo atual, marca como morto e interrompe SELECTING/ATTACKING
                        if self._fsm.ctx.target and ptr == self._fsm.ctx.target["ptr"]:
                            self._fsm.ctx.dead_ptrs.add(ptr)
                            self._fsm.ctx.add_cooldown(wx, wy)
                            self._fsm.ctx.mark_recent_dead(wx, wy)

            self._prev_entity_map = current_map
        else:
            # Quando não está farmando mantém o mapa atualizado mas não enfileira
            self._prev_entity_map = {e["ptr"]: e for e in entities}

        self._entities = entities
        self._player   = player
        self.after(0, self._render)

    def _render(self):
        selected   = self._get_selected_names()
        player_ptr = self._player["ptr"] if self._player else None
        loot_wxs   = {(e.wx, e.wy) for e in self._fsm.ctx.loot_queue}

        names_on_map = set()
        for e in self._entities:
            if e["ptr"] == player_ptr: continue
            if self._fsm._is_dead(e["ptr"]): continue
            if e["name"] and e["name"] != "???":
                names_on_map.add(e["name"])
        self._update_checkboxes(names_on_map)

        self.tree_view.delete(*self.tree_view.get_children())
        current_target_ptr = self._fsm.ctx.target["ptr"] if self._fsm.ctx.target else None

        for e in self._entities:
            sx_str    = f"{e['screen_x']:.0f}, {e['screen_y']:.0f}" if e['screen_x'] else "—"
            is_target = e["ptr"] == current_target_ptr
            is_dead   = e["ptr"] in self._fsm.ctx.dead_ptrs
            in_queue  = any(
                math.sqrt((e["x"] - wx)**2 + (e["y"] - wy)**2) < 1.0
                for wx, wy in loot_wxs
            )

            if is_target:    tag = ("target",)
            elif in_queue:   tag = ("loot_q",)
            elif is_dead:    tag = ("dead",)
            else:            tag = ()

            self.tree_view.insert("", "end", tags=tag, values=(
                f"0x{e['ptr']:X}", e["name"],
                f"{e['cur_hp']} / {e['max_hp']}",
                f"{e['x']:.1f}, {e['y']:.1f}",
                sx_str,
            ))

        self.lbl_count.config(text=f"Entidades: {len(self._entities)}")
        self.lbl_time.config(text=time.strftime("Atualizado: %H:%M:%S"))

    # ── F5 debug ──────────────────────────────
    def _click_nearest_any(self):
        player   = self._player
        entities = self._entities
        if not player or not entities: return
        px, py   = player["x"], player["y"]
        best, best_dist = None, float("inf")
        for e in entities:
            if e["ptr"] == player["ptr"]: continue
            if self._fsm._is_dead(e["ptr"]): continue
            dist = math.sqrt((e["x"] - px)**2 + (e["y"] - py)**2)
            if dist < best_dist:
                best_dist = dist
                best = e
        if best and best["screen_x"] is not None:
            click_game(best["screen_x"], best["screen_y"])
            self._log(f"F5 -> '{best['name']}' ({best['screen_x']:.0f},{best['screen_y']:.0f})")


if __name__ == "__main__":
    App().mainloop()
