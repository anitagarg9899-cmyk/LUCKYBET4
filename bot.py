import discord
from discord.ext import commands
import aiohttp
import random
import json
import os
import asyncio
import hashlib
import hmac
import secrets
import re
import math
import io
from images import (
    coinflip_card,
    coinflip_anim_card,
    blackjack_card,
    slots_card
)
from dotenv import load_dotenv

load_dotenv()
from datetime import datetime, timezone, timedelta
from images import (
    balance_card, coinflip_card, dice_card, slots_card,
    roulette_card, blackjack_card, addbal_card,  limbo_card,
    rps_card, slide_card, tight_card, war_card, valentines_card, twist_card
)

intents = discord.Intents.default()
intents.message_content = True
intents.members = True
intents.invites = True

bot = commands.Bot(command_prefix='.', intents=intents, help_command=None)

# ── Embed System ──────────────────────────────────────────────────────────────
# Each embed category has its own visual identity — not a single cookie-cutter
# template.  Game embeds are compact and punchy, admin embeds are tight and
# informational, leaderboards are tabular, lobbies are spacious.

class C:
    PRIMARY   = 0x2563EB
    SECONDARY = 0x0891B2
    ACCENT    = 0xD97706
    SUCCESS   = 0x059669
    WARNING   = 0xEA580C
    ERROR     = 0xDC2626
    NEUTRAL   = 0x475569
    GOLD      = 0xCA8A04
    LOBBY     = 0x7C3AED
    DANGER    = 0xB91C1C

_LEGACY = {
    0x00FF88: C.SUCCESS, 0xFF4444: C.ERROR,  0xFFD700: C.ACCENT,
    0x1E90FF: C.PRIMARY, 0x9B59B6: C.LOBBY,  0xFF5000: C.WARNING,
    0x888888: C.NEUTRAL,  0x00BFFF: C.SECONDARY, 0x4FC3F7: C.SECONDARY,
    0xFF8800: C.WARNING,  0xFF6FA5: 0xEC4899, 0x00FF99: C.SUCCESS,
    0xFF0000: C.ERROR,    0x00E676: C.SUCCESS, 0xF1C40F: C.GOLD,
    0x2ECC71: C.SUCCESS,  0x3498DB: C.PRIMARY, 0xE74C3C: C.ERROR,
    0xCD7F32: 0xB45309,   0xC0C0C0: 0x94A3B8, 0x64C8FF: 0x0EA5E9,
    0xB464FF: C.LOBBY,
}

def _c(color):
    if color is None: return C.PRIMARY
    return _LEGACY.get(color, color) if isinstance(color, int) else color

BRAND = "LuckyBet"

def embed(title="", description="", color=None, *, footer=None,
          thumbnail=None, image=None, author=None, url=None):
    e = discord.Embed(
        title=title or None,
        description=description or None,
        color=_c(color),
        timestamp=datetime.now(timezone.utc),
        url=url,
    )
    if author:
        e.set_author(name=author)
    if footer is not None:
        e.set_footer(text=footer)
    if thumbnail:
        e.set_thumbnail(url=thumbnail)
    if image:
        e.set_image(url=image)
    return e

def field_grid(e, fields, inline=True):
    for name, value, *rest in fields:
        e.add_field(name=name, value=value, inline=rest[0] if rest else inline)
    return e

DB_FILE      = os.getenv('DATA_FILE', 'user_data.json')
active_mines = {}
active_bj    = {}
invite_cache = {}   # guild_id -> {code: {'uses': int, 'inviter_id': int|None, 'max_uses': int}}

# Thread lifecycle tracking
# thread_activity: thread_id -> datetime of last message in it
# user_threads:    user_id -> set of thread_ids this user owns/created
THREAD_IDLE_TIMEOUT = 24 * 3600  # seconds before an idle thread is archived
thread_activity = {}
user_threads    = {}

POINTS_TO_USD = 0.0037

# ── Deposits (NOWPayments) ──────────────────────────────────────────────────
NOWPAYMENTS_API_KEY      = os.getenv('NOWPAYMENTS_API_KEY', '')
NOWPAYMENTS_EMAIL        = os.getenv('NOWPAYMENTS_EMAIL', '')
NOWPAYMENTS_PASSWORD     = os.getenv('NOWPAYMENTS_PASSWORD', '')
# TOTP secret from NOWPayments 2FA setup (the base32 key shown when you enabled 2FA).
NOWPAYMENTS_2FA_SECRET   = os.getenv('NOWPAYMENTS_2FA_SECRET', '')
NOWPAYMENTS_API     = 'https://api.nowpayments.io/v1'
DEPOSIT_PAY_CURRENCY = 'ltc'
DEPOSIT_MIN_USD      = 1.0
# NOWPayments statuses that mean money fully arrived
DEPOSIT_PAID_STATES  = {'finished', 'confirmed', 'sending'}
DEPOSIT_DEAD_STATES  = {'failed', 'refunded', 'expired'}
PAYOUT_DONE_STATES   = {'finished'}
PAYOUT_DEAD_STATES   = {'failed', 'rejected', 'expired'}
WITHDRAW_CHANNEL_ID = 1517385238488023061
MIN_WITHDRAW = 500
WITHDRAW_PAY_CURRENCY = 'ltc'
# Keep at least this many points of bankroll buffer after a withdrawal
HOUSE_MIN_BUFFER_PTS = 0

def usd_to_points(usd):
    return int(round(usd / POINTS_TO_USD))

RANKS = [
    (0,         "🥉 Bronze",   0xCD7F32),
    (5_000,     "🥈 Silver",   0xC0C0C0),
    (25_000,    "🥇 Gold",     0xFFD700),
    (100_000,   "💎 Platinum", 0x64C8FF),
    (500_000,   "👑 Diamond",  0xB464FF),
    (2_000_000, "⚡ VIP",      0xFF5000),
]
RANK_KEYS = ["bronze", "silver", "gold", "platinum", "diamond", "vip"]

def get_rank_info(total_wagered):
    rank = RANKS[0]; rank_idx = 0
    for i, entry in enumerate(RANKS):
        if total_wagered >= entry[0]:
            rank = entry; rank_idx = i
    next_rank = RANKS[rank_idx + 1] if rank_idx + 1 < len(RANKS) else None
    return rank, next_rank

def rank_key(rank_name):
    return rank_name.split()[-1].lower()

def fmt(points):
    usd = points * POINTS_TO_USD
    return f"R${points:,} (≈ ${usd:.2f})"

# ── Data ──────────────────────────────────────────────────────────────────────

def load_data():
    if os.path.exists(DB_FILE):
        with open(DB_FILE, 'r') as f:
            return json.load(f)
    return {}

def save_data(data):
    with open(DB_FILE, 'w') as f:
        json.dump(data, f, indent=4)

def get_user(user_id):
    data = load_data(); uid = str(user_id)
    if uid not in data:
        data[uid] = {
            'balance': 0,
            'stats': {'wins': 0, 'losses': 0, 'total_wagered': 0, 'total_lost': 0},
            'last_daily': None, 'last_monthly': None,
            'wager_at_last_monthly': 0, 'rakeback_available': 0.0, 'clan': None,
            'bonus_received': 0, 'tips_sent': 0, 'tips_received': 0, 'total_withdrawn': 0,
            'wager_requirement': 0, 'wager_since_promo': 0, 'total_deposited': 0.0,
        }
        save_data(data)
    u = data[uid]; changed = False
    for key, default in [
        ('last_daily', None), ('last_monthly', None), ('wager_at_last_monthly', 0),
        ('rakeback_available', 0.0), ('clan', None), ('bonus_received', 0),
        ('tips_sent', 0), ('tips_received', 0), ('total_withdrawn', 0),
        ('daily_invites', 0), ('daily_invites_date', None), ('total_invites', 0),
        ('wager_requirement', 0), ('wager_since_promo', 0), ('total_deposited', 0.0),
    ]:
        if key not in u: u[key] = default; changed = True
    if 'total_lost' not in u.get('stats', {}):
        u.setdefault('stats', {})['total_lost'] = 0; changed = True
    if changed: save_data(data)
    return data, uid

def get_user_balance(user_id):
    data, uid = get_user(user_id); return data[uid]['balance']

def resolve_bet(amount_str, balance):
    """Convert 'all', 'half', or a number string to an integer bet amount."""
    s = str(amount_str).lower().strip()
    if s == 'all':
        return balance
    if s == 'half':
        return max(1, balance // 2)
    try:
        return int(s)
    except ValueError:
        return None

def set_user_balance(user_id, amount):
    data, uid = get_user(user_id)
    data[uid]['balance'] = max(0, amount); save_data(data)

def add_to_stats(user_id, result, wager):
    data, uid = get_user(user_id); s = data[uid]['stats']
    s['total_wagered'] += wager
    if result:
        s['wins'] += 1
    else:
        s['losses'] += 1
        s['total_lost'] = s.get('total_lost', 0) + wager
        data[uid]['rakeback_available'] = data[uid].get('rakeback_available', 0.0) + wager * 0.002
    save_data(data)

def get_config():
    return load_data().get('__config__', {})

def save_config(cfg):
    data = load_data(); data['__config__'] = cfg; save_data(data)

def get_codes():
    return load_data().get('__codes__', {})

def save_codes(codes):
    data = load_data(); data['__codes__'] = codes; save_data(data)

def get_clans():
    return load_data().get('__clans__', {})

def save_clans(clans):
    data = load_data(); data['__clans__'] = clans; save_data(data)

def get_deposits():
    return load_data().get('__deposits__', {})

def save_deposits(deposits):
    data = load_data(); data['__deposits__'] = deposits; save_data(data)

def get_withdrawals():
    return load_data().get('__withdrawals__', {})

def save_withdrawals(w):
    data = load_data(); data['__withdrawals__'] = w; save_data(data)

# Re-entrant guard for the JWT cache used by NOWPayments payouts
_NP_JWT = {'token': None, 'expires_at': 0.0}

def compute_house_bankroll_pts():
    """House profit in points = deposited − withdrawn − player balances − rakeback owed."""
    data = load_data()
    player_balances = 0
    deposited_usd = 0.0
    withdrawn_pts = 0
    rakeback_owed = 0.0
    for uid, user in data.items():
        if uid.startswith("__") or not isinstance(user, dict):
            continue
        player_balances += int(user.get("balance", 0) or 0)
        deposited_usd  += float(user.get("total_deposited", 0) or 0)
        withdrawn_pts  += int(user.get("total_withdrawn", 0) or 0)
        rakeback_owed  += float(user.get("rakeback_available", 0) or 0)
    deposited_pts = usd_to_points(deposited_usd)
    return deposited_pts - withdrawn_pts - player_balances - int(round(rakeback_owed))


def send_image(buf, filename='result.png'):
    if isinstance(buf, (bytes, bytearray)):
        buf = io.BytesIO(buf)
    buf.seek(0)
    return discord.File(buf, filename=filename)

# ── Rank Role Helper ──────────────────────────────────────────────────────────

async def assign_rank_role(guild, user_id):
    if not guild: return
    cfg = get_config(); rank_roles = cfg.get('rank_roles', {})
    if not rank_roles: return
    data, uid = get_user(user_id)
    total_wagered = data[uid]['stats']['total_wagered']
    current_rank, _ = get_rank_info(total_wagered)
    rkey = rank_key(current_rank[1])
    role_id = rank_roles.get(rkey)
    member = guild.get_member(user_id)
    if not member: return
    all_rank_ids = set(int(rid) for rid in rank_roles.values())
    to_remove = [r for r in member.roles if r.id in all_rank_ids]
    if to_remove:
        try: await member.remove_roles(*to_remove)
        except: pass
    if role_id:
        role = guild.get_role(int(role_id))
        if role:
            try: await member.add_roles(role)
            except: pass

# ── Provably Fair ─────────────────────────────────────────────────────────────

def generate_seeds():
    server_seed = secrets.token_hex(32)
    client_seed = secrets.token_hex(8)
    public_hash = hashlib.sha256(server_seed.encode()).hexdigest()
    return server_seed, client_seed, public_hash

def pf_mine_positions(server_seed, client_seed, mines_count, total=20):
    h = hmac.new(server_seed.encode(), client_seed.encode(), hashlib.sha256)
    rng_bytes = bytes.fromhex(h.hexdigest()); positions = list(range(total))
    for i in range(total - 1, 0, -1):
        j = rng_bytes[i % len(rng_bytes)] % (i + 1)
        positions[i], positions[j] = positions[j], positions[i]
    return set(positions[:mines_count])

def pf_derive(server_seed, client_seed, nonce=0):
    """Return a float [0, 1) derived from seeds + nonce via HMAC-SHA256."""
    msg = f"{client_seed}:{nonce}".encode()
    h = hmac.new(server_seed.encode(), msg, hashlib.sha256)
    return int(h.hexdigest()[:8], 16) / 0xFFFFFFFF

def pf_coinflip(server_seed, client_seed):
    return "heads" if pf_derive(server_seed, client_seed) < 0.5 else "tails"

def pf_dice_roll(server_seed, client_seed):
    return int(pf_derive(server_seed, client_seed) * 6) + 1

def pf_roulette_spin(server_seed, client_seed):
    return int(pf_derive(server_seed, client_seed) * 37)

def pf_slots_spin(server_seed, client_seed):
    symbols = ["🍎", "🍊", "🍋", "🍌", "⭐", "💎"]
    return [symbols[int(pf_derive(server_seed, client_seed, i) * 6)] for i in range(3)]

LIMBO_HOUSE_EDGE = 0.01

def pf_limbo(server_seed, client_seed):
    """Return a crash-style result multiplier (>= 1.00) for Limbo."""
    r = max(pf_derive(server_seed, client_seed), 1e-9)
    result = (1.0 - LIMBO_HOUSE_EDGE) / r
    return max(1.00, round(result, 2))

RPS_CHOICES = ['rock', 'paper', 'scissors']

def pf_rps(server_seed, client_seed):
    """Bot's provably-fair Rock-Paper-Scissors move."""
    return RPS_CHOICES[int(pf_derive(server_seed, client_seed) * 3) % 3]

SLIDE_HOUSE_EDGE = 0.04
SLIDE_MAX = 10.0

def pf_slide(server_seed, client_seed):
    """Slider lands on a multiplier; payout uses the player's target (1% style)."""
    r = max(pf_derive(server_seed, client_seed), 1e-9)
    result = (1.0 - SLIDE_HOUSE_EDGE) / r
    return round(min(result, SLIDE_MAX), 2)

TIGHT_MAX = 5.0
TIGHT_EXP = 4.208   # tuned so E[result] ≈ 0.96 (96% RTP)

def pf_tight(server_seed, client_seed):
    """Random multiplier in [0, 5.0] skewed low for ~96% RTP."""
    r = pf_derive(server_seed, client_seed)
    return round(TIGHT_MAX * (r ** TIGHT_EXP), 2)

def pf_war_cards(server_seed, client_seed):
    """Return (player_rank, dealer_rank), ranks 2-14 (11=J,12=Q,13=K,14=A)."""
    p = int(pf_derive(server_seed, client_seed, 0) * 13) + 2
    d = int(pf_derive(server_seed, client_seed, 1) * 13) + 2
    return p, d

VALENTINE_SYMBOLS = ['💘', '💖', '💝', '🌹', '🍫', '💍']

def pf_valentines(server_seed, client_seed):
    return [VALENTINE_SYMBOLS[int(pf_derive(server_seed, client_seed, i) * 6) % 6] for i in range(3)]

TWIST_TRACK = {
    3: 5.0, 4: 3.0, 5: 2.0, 6: 1.5, 7: 1.0, 8: 0.5, 9: 0.3, 10: 0.2,
    11: 0.2, 12: 0.5, 13: 1.0, 14: 1.5, 15: 2.0, 16: 3.0, 17: 5.0, 18: 9.5,
}

def pf_twist(server_seed, client_seed):
    """Three dice rolls; token moves sum(rolls) tiles. Returns (rolls, multiplier)."""
    rolls = [int(pf_derive(server_seed, client_seed, i) * 6) + 1 for i in range(3)]
    return rolls, TWIST_TRACK[sum(rolls)]

TREASURE_MAX = 2.5
TREASURE_EXP = 1.604   # tuned so E[multiplier] ≈ 0.96 (96% RTP)

def pf_treasure(server_seed, client_seed, num_chests):
    """Return a multiplier (0..2.5, skewed low) for each chest."""
    return [round(TREASURE_MAX * (pf_derive(server_seed, client_seed, i) ** TREASURE_EXP), 2)
            for i in range(num_chests)]

# Tower: difficulty -> (tiles per row, safe tiles per row)
TOWER_DIFFS = {'easy': (4, 3), 'medium': (3, 2), 'hard': (2, 1)}
TOWER_ROWS = 6
TOWER_EDGE = 0.03

def tower_step_mult(diff):
    tiles, safe = TOWER_DIFFS[diff]
    return (tiles / safe) * (1 - TOWER_EDGE)

def tower_multiplier(diff, rows_cleared):
    return round(tower_step_mult(diff) ** rows_cleared, 2)

def pf_tower_bombs(server_seed, client_seed, diff):
    """Return list (len TOWER_ROWS) of the bomb tile index for each row."""
    tiles, _ = TOWER_DIFFS[diff]
    return [int(pf_derive(server_seed, client_seed, r) * tiles) % tiles for r in range(TOWER_ROWS)]

def pf_blackjack_deck(server_seed, client_seed):
    deck = [2,3,4,5,6,7,8,9,10,10,10,10,11] * 4
    full_bytes = b''
    for i in range(12):
        msg = f"{client_seed}:{i}".encode()
        full_bytes += bytes.fromhex(hmac.new(server_seed.encode(), msg, hashlib.sha256).hexdigest())
    for i in range(len(deck) - 1, 0, -1):
        j = full_bytes[i % len(full_bytes)] % (i + 1)
        deck[i], deck[j] = deck[j], deck[i]
    return deck

def pf_add_field(embed, server_seed, client_seed, public_hash, game):
    """Append a Provably Fair verification field to an embed."""
    embed.add_field(
        name="🔐 Provably Fair",
        value=(
            f"**Server Seed:** `{server_seed}`\n"
            f"**Client Seed:** `{client_seed}`\n"
            f"**Hash (SHA-256):** `{public_hash[:24]}…`\n"
            f"Verify: `.verify {game} {server_seed} {client_seed}`"
        ),
        inline=False
    )


GAME_EMOJIS = {
    'coinflip': '🪙', 'dice': '🎲', 'slots': '🎰', 'roulette': '🎡',
    'blackjack': '🃏', 'mines': '⛏️', 'crash': '🚀', 'jackpot': '🎰',
    'limbo': '📈', 'rps': '✂️', 'slide': '🎢', 'tight': '🗜️', 'tower': '🗼',
    'treasurehunt': '💰', 'twist': '🌀', 'valentines': '💘', 'war': '⚔️',
}

async def send_to_history(guild, game, user_name, user_id, bet, won, profit, new_bal):
    """Post a compact bet result to the configured history channel."""
    if not guild:
        return
    cfg = get_config()
    ch_id = cfg.get('history_channel')
    if not ch_id:
        return
    channel = guild.get_channel(int(ch_id))
    if not channel:
        return
    emoji = GAME_EMOJIS.get(game, '🎮')
    color = C.SUCCESS if won else (C.ACCENT if won is None else C.ERROR)
    if won is True:
        result_str = f"✅ **WIN**  `+R${profit:,}`"
    elif won is False:
        result_str = f"❌ **LOSS**  `-R${abs(profit):,}`"
    else:
        result_str = "🤝 **TIE**  `no change`"
    e = embed("", f"**Bet:** `R${bet:,}`  •  {result_str}\n**Balance:** `R${new_bal:,}`",
              color, author=f"{emoji}  {game.title()}  •  {user_name}")
    try:
        await channel.send(embed=e)
    except Exception:
        pass

# ── Crash Game ────────────────────────────────────────────────────────────────

CRASH_LOBBY_SECS = 20
CRASH_TICK       = 1.0   # seconds between multiplier updates

crash_state = {
    'phase':    'idle',   # idle | lobby | running | crashed
    'bets':     {},       # uid -> {'amount': int, 'start_bal': int, 'username': str}
    'cashed':   {},       # uid -> {'mult': float, 'profit': int}
    'crash_at': 1.0,
    'mult':     1.0,
    'message':  None,
    'channel_id': None,
    'task':     None,
    'view':     None,
    'guild_id': None,
}

def gen_crash_point():
    r = random.random()
    if r < 0.01: return 1.0  # 1% instant crash
    return min(round(0.99 / (1 - r), 2), 200.0)

def crash_mult_at(elapsed):
    return round(1.0 + elapsed * 0.12 + (elapsed ** 1.6) * 0.015, 2)

def crash_embed_build(phase, bets, cashed, mult=1.00, crash_at=None, color=None):
    if phase == 'lobby':
        title = "🚀 Crash — Lobby Open"
        desc  = ("Place your bets — the round starts once the first bet is in.\n"
                 "Use `.crash <amount>` to join.\n\u200b")
        color = C.LOBBY
    elif phase == 'running':
        title = f"🚀 Crash — {mult:.2f}×"
        desc  = f"```\n     {mult:.2f}×\n```"
        color = C.SUCCESS if mult < 3 else (C.ACCENT if mult < 7 else C.WARNING)
    elif phase == 'crashed':
        title = f"💥 Crashed at {crash_at:.2f}×"
        desc  = f"```\n   💥 {crash_at:.2f}×\n```"
        color = C.ERROR
    else:
        title = "🚀 Crash"; desc = ""; color = C.PRIMARY

    if bets:
        lines = []
        for uid, b in bets.items():
            if uid in cashed:
                c = cashed[uid]; sign = "+" if c['profit'] >= 0 else ""
                lines.append(f"💰 **{b['username']}** cashed @ {c['mult']:.2f}×  `{sign}R${c['profit']:,}`")
            elif phase == 'crashed':
                lines.append(f"💥 **{b['username']}**  `-R${b['amount']:,}`")
            else:
                lines.append(f"🎲 **{b['username']}**  `R${b['amount']:,}`")
        desc += "\n" + "\n".join(lines)

    footer = f"Lobby closes ~{CRASH_LOBBY_SECS}s after first bet" if phase == 'lobby' else None
    return embed(title, desc, color, footer=footer)


class CrashView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="💰 Cash Out", style=discord.ButtonStyle.success, custom_id="crash_co")
    async def cashout(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        if crash_state['phase'] != 'running':
            await interaction.response.send_message("No active crash game right now!", ephemeral=True); return
        if uid not in crash_state['bets']:
            await interaction.response.send_message("You didn't bet this round! Use `.crash <amount>` next time.", ephemeral=True); return
        if uid in crash_state['cashed']:
            await interaction.response.send_message("You already cashed out!", ephemeral=True); return
        mult    = crash_state['mult']
        bet     = crash_state['bets'][uid]['amount']
        sb      = crash_state['bets'][uid]['start_bal']
        profit  = round(bet * mult) - bet
        new_bal = sb + profit
        set_user_balance(uid, new_bal)
        add_to_stats(uid, True, bet)
        if crash_state['guild_id']:
            guild = bot.get_guild(crash_state['guild_id'])
            if guild:
                asyncio.create_task(assign_rank_role(guild, uid))
        crash_state['cashed'][uid] = {'mult': mult, 'profit': profit}
        await interaction.response.send_message(
            f"✅ Cashed out at **{mult:.2f}×** — profit: **+R${profit:,}**  |  New balance: {fmt(new_bal)}",
            ephemeral=True
        )
        uname = crash_state['bets'][uid].get('username', str(uid))
        guild  = bot.get_guild(crash_state['guild_id']) if crash_state['guild_id'] else None
        asyncio.create_task(send_to_history(guild, 'crash', uname, uid, bet, True, profit, new_bal))


async def run_crash_game(channel, guild_id):
    crash_state['guild_id'] = guild_id
    view = CrashView()
    crash_state['view'] = view

    # Lobby phase
    embed = crash_embed_build('lobby', crash_state['bets'], crash_state['cashed'])
    crash_state['message'] = await channel.send(embed=embed, view=view)

    await asyncio.sleep(CRASH_LOBBY_SECS)

    if not crash_state['bets']:
        crash_state['phase'] = 'idle'
        await crash_state['message'].edit(
            embed=embed("🚀 Crash — Cancelled", "No bets were placed this round.", C.NEUTRAL),
            view=None)
        return

    # Running phase
    crash_state['phase']    = 'running'
    crash_state['crash_at'] = gen_crash_point()
    crash_state['mult']     = 1.00
    start_time = asyncio.get_event_loop().time()

    while True:
        elapsed = asyncio.get_event_loop().time() - start_time
        crash_state['mult'] = crash_mult_at(elapsed)

        if crash_state['mult'] >= crash_state['crash_at']:
            crash_state['mult'] = crash_state['crash_at']
            break

        embed = crash_embed_build('running', crash_state['bets'], crash_state['cashed'], crash_state['mult'])
        try:
            await crash_state['message'].edit(embed=embed, view=view)
        except Exception:
            pass
        await asyncio.sleep(CRASH_TICK)

    # Crashed
    crash_state['phase'] = 'crashed'
    for uid, b in crash_state['bets'].items():
        if uid not in crash_state['cashed']:
            new_bal = b['start_bal'] - b['amount']
            set_user_balance(uid, max(0, new_bal))
            add_to_stats(uid, False, b['amount'])

    embed = crash_embed_build('crashed', crash_state['bets'], crash_state['cashed'],
                              crash_at=crash_state['crash_at'])
    for item in view.children: item.disabled = True
    try:
        await crash_state['message'].edit(embed=embed, view=view)
    except Exception:
        pass

    await asyncio.sleep(8)

    # Reset
    crash_state.update({'phase': 'idle', 'bets': {}, 'cashed': {}, 'crash_at': 1.0,
                        'mult': 1.0, 'message': None, 'channel_id': None, 'task': None,
                        'view': None, 'guild_id': None})


@bot.command(name='crash')
async def crash_cmd(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return

    uid = ctx.author.id

    if crash_state['phase'] == 'idle':
        # Start lobby
        crash_state['phase']      = 'lobby'
        crash_state['channel_id'] = ctx.channel.id
        crash_state['bets'][uid]  = {'amount': amount, 'start_bal': bal, 'username': ctx.author.name}
        crash_state['task']       = asyncio.create_task(run_crash_game(ctx.channel, ctx.guild.id if ctx.guild else None))
        await ctx.message.delete()

    elif crash_state['phase'] == 'lobby':
        if crash_state['channel_id'] != ctx.channel.id:
            await ctx.send("❌ A crash game is running in another channel!", delete_after=5); return
        if uid in crash_state['bets']:
            await ctx.send("❌ You already bet this round!", delete_after=5); return
        crash_state['bets'][uid] = {'amount': amount, 'start_bal': bal, 'username': ctx.author.name}
        await ctx.message.delete()
        embed = crash_embed_build('lobby', crash_state['bets'], crash_state['cashed'])
        try: await crash_state['message'].edit(embed=embed, view=crash_state['view'])
        except: pass

    elif crash_state['phase'] == 'running':
        await ctx.send("⏳ A game is already in progress! You can bet on the **next** round.", delete_after=6)
    else:
        await ctx.send("⏳ Please wait — wrapping up the last round.", delete_after=5)

CRASH_ROOM_LOBBY_SECS = 30   # seconds before a crash room starts

crash_room_state = {
    'active':     False,
    'host_id':    None,
    'bet_amount': 0,
    'bets':       {},   # uid -> {'amount': int, 'start_bal': int, 'username': str}
    'cashed':     {},   # uid -> {'mult': float, 'profit': int}
    'crash_at':   1.0,
    'mult':       1.0,
    'message':    None,
    'channel_id': None,
    'view':       None,
    'guild_id':   None,
    'phase':      'idle',  # idle | lobby | running | crashed
    'start_requested': False,
}


class CrashRoomView(discord.ui.View):
    def __init__(self, bet_amount, host_id):
        super().__init__(timeout=None)
        self.bet_amount = bet_amount
        self.host_id    = host_id

    @discord.ui.button(label="▶ Start Now", style=discord.ButtonStyle.danger, custom_id="crashroom_start")
    async def start_now(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        if uid != self.host_id:
            await interaction.response.send_message("❌ Only the room host can start early!", ephemeral=True); return
        if crash_room_state['phase'] != 'lobby':
            await interaction.response.send_message("❌ The room is not in the lobby phase!", ephemeral=True); return
        if not crash_room_state['bets']:
            await interaction.response.send_message("❌ No players have joined yet!", ephemeral=True); return
        crash_room_state['start_requested'] = True
        await interaction.response.send_message("🚀 Host started the room — launching now!", ephemeral=True)

    @discord.ui.button(label="Join Now", style=discord.ButtonStyle.primary, custom_id="crashroom_join")
    async def join(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        if crash_room_state['phase'] != 'lobby':
            await interaction.response.send_message("❌ The join window is closed for this room!", ephemeral=True); return
        if uid in crash_room_state['bets']:
            await interaction.response.send_message("✅ You're already in this crash room!", ephemeral=True); return
        bal = get_user_balance(uid)
        if self.bet_amount > bal:
            await interaction.response.send_message(
                f"❌ You need **R${self.bet_amount:,}** to join. Your balance: {fmt(bal)}", ephemeral=True); return
        crash_room_state['bets'][uid] = {
            'amount': self.bet_amount, 'start_bal': bal,
            'username': interaction.user.name
        }
        count = len(crash_room_state['bets'])
        await interaction.response.send_message(
            f"🚀 You joined the crash room! Bet: **R${self.bet_amount:,}** — **{count}** player{'s' if count!=1 else ''} in.",
            ephemeral=True)
        embed = _crash_room_embed('lobby')
        try: await crash_room_state['message'].edit(embed=embed, view=self)
        except: pass

    @discord.ui.button(label="💰 Cash Out", style=discord.ButtonStyle.success, custom_id="crashroom_co")
    async def cashout(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        if crash_room_state['phase'] != 'running':
            await interaction.response.send_message("No active crash room right now!", ephemeral=True); return
        if uid not in crash_room_state['bets']:
            await interaction.response.send_message("You didn't join this room!", ephemeral=True); return
        if uid in crash_room_state['cashed']:
            await interaction.response.send_message("You already cashed out!", ephemeral=True); return
        mult    = crash_room_state['mult']
        bet     = crash_room_state['bets'][uid]['amount']
        sb      = crash_room_state['bets'][uid]['start_bal']
        profit  = round(bet * mult) - bet
        new_bal = sb + profit
        set_user_balance(uid, new_bal)
        add_to_stats(uid, True, bet)
        if crash_room_state['guild_id']:
            guild = bot.get_guild(crash_room_state['guild_id'])
            if guild:
                asyncio.create_task(assign_rank_role(guild, uid))
        crash_room_state['cashed'][uid] = {'mult': mult, 'profit': profit}
        await interaction.response.send_message(
            f"✅ Cashed out at **{mult:.2f}×** — profit: **+R${profit:,}**  |  New balance: {fmt(new_bal)}",
            ephemeral=True)
        uname = crash_room_state['bets'][uid].get('username', str(uid))
        guild  = bot.get_guild(crash_room_state['guild_id']) if crash_room_state['guild_id'] else None
        asyncio.create_task(send_to_history(guild, 'crash', uname, uid, bet, True, profit, new_bal))


def _crash_room_embed(phase):
    bets   = crash_room_state['bets']
    cashed = crash_room_state['cashed']
    mult   = crash_room_state['mult']
    bet    = crash_room_state['bet_amount']
    host   = crash_room_state.get('host_label', 'Host')

    if phase == 'lobby':
        title = "🚀 Crash Room — Lobby Open"
        desc  = (f"```\n  Host     {host}\n  Entry    R${bet:,}\n```\n"
                 "Click **Join Now** to enter  •  Host can hit **Start Now**\n\u200b")
        color = C.LOBBY
    elif phase == 'running':
        title = f"🚀 Crash Room — {mult:.2f}×"
        desc  = f"```\n     {mult:.2f}×\n```"
        color = C.SUCCESS if mult < 3 else (C.ACCENT if mult < 7 else C.WARNING)
    elif phase == 'crashed':
        title = f"💥 Crash Room — Crashed @ {crash_room_state['crash_at']:.2f}×"
        desc  = f"```\n   💥 {crash_room_state['crash_at']:.2f}×\n```"
        color = C.ERROR
    else:
        title = "🚀 Crash Room"; desc = ""; color = C.PRIMARY

    if bets:
        lines = []
        for uid, b in bets.items():
            if uid in cashed:
                c = cashed[uid]; sign = "+" if c['profit'] >= 0 else ""
                lines.append(f"💰 **{b['username']}** cashed @ {c['mult']:.2f}×  `{sign}R${c['profit']:,}`")
            elif phase == 'crashed':
                lines.append(f"💥 **{b['username']}**  `-R${b['amount']:,}`")
            else:
                lines.append(f"🎲 **{b['username']}**  `R${b['amount']:,}`")
        desc += "\n".join(lines)

    footer = f"Entry R${bet:,}  •  {CRASH_ROOM_LOBBY_SECS}s to start" if phase == 'lobby' else None
    return embed(title, desc, color, footer=footer)


async def _run_crash_room(channel, guild_id, host_label):
    crash_room_state['guild_id'] = guild_id
    view   = CrashRoomView(crash_room_state['bet_amount'], crash_room_state['host_id'])
    crash_room_state['view']  = view
    crash_room_state['phase'] = 'lobby'

    embed = _crash_room_embed('lobby')
    crash_room_state['message'] = await channel.send(embed=embed, view=view)

    # Wait for first join (up to 2 min), or host Start Now if players present
    first_join_deadline = asyncio.get_event_loop().time() + 120
    while not crash_room_state['bets'] and asyncio.get_event_loop().time() < first_join_deadline:
        if crash_room_state['start_requested']:
            break
        await asyncio.sleep(1)

    if not crash_room_state['bets']:
        crash_room_state.update({'phase': 'idle', 'active': False, 'message': None, 'view': None})
        try:
            await crash_room_state['message'].edit(
                embed=embed("Crash Room — Cancelled",
                            "No one joined the room in time.", C.NEUTRAL),
                view=None)
        except: pass
        _reset_crash_room()
        return

    # Wait remaining lobby time, unless host hits Start Now
    if not crash_room_state['start_requested']:
        lobby_end = asyncio.get_event_loop().time() + CRASH_ROOM_LOBBY_SECS
        while asyncio.get_event_loop().time() < lobby_end:
            if crash_room_state['start_requested']:
                break
            await asyncio.sleep(1)

    for item in view.children:
        if getattr(item, 'custom_id', None) in ('crashroom_join', 'crashroom_start'):
            item.disabled = True

    embed = _crash_room_embed('lobby')
    try: await crash_room_state['message'].edit(embed=embed, view=view)
    except: pass

    crash_room_state['phase']    = 'running'
    crash_room_state['crash_at'] = gen_crash_point()
    crash_room_state['mult']     = 1.00
    start_time = asyncio.get_event_loop().time()

    while True:
        elapsed = asyncio.get_event_loop().time() - start_time
        crash_room_state['mult'] = crash_mult_at(elapsed)
        if crash_room_state['mult'] >= crash_room_state['crash_at']:
            crash_room_state['mult'] = crash_room_state['crash_at']
            break
        embed = _crash_room_embed('running')
        try: await crash_room_state['message'].edit(embed=embed, view=view)
        except: pass
        await asyncio.sleep(CRASH_TICK)

    crash_room_state['phase'] = 'crashed'
    for uid, b in crash_room_state['bets'].items():
        if uid not in crash_room_state['cashed']:
            new_bal = b['start_bal'] - b['amount']
            set_user_balance(uid, max(0, new_bal))
            add_to_stats(uid, False, b['amount'])

    embed = _crash_room_embed('crashed')
    for item in view.children: item.disabled = True
    try: await crash_room_state['message'].edit(embed=embed, view=view)
    except: pass

    await asyncio.sleep(8)
    _reset_crash_room()


def _reset_crash_room():
    crash_room_state.update({
        'active': False, 'host_id': None, 'bet_amount': 0,
        'bets': {}, 'cashed': {}, 'crash_at': 1.0, 'mult': 1.0,
        'message': None, 'channel_id': None, 'view': None,
        'guild_id': None, 'phase': 'idle', 'start_requested': False
    })


@bot.command(name='crashroom')
async def crashroom_cmd(ctx, amount: str):
    if crash_room_state['phase'] != 'idle' and crash_room_state['active']:
        await ctx.send("❌ A crash room is already active! Wait for it to finish."); return
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None:
        await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0:
        await ctx.send("❌ Entry bet must be positive!"); return
    if amount > bal:
        await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return

    crash_room_state.update({
        'active': True, 'host_id': ctx.author.id, 'bet_amount': amount,
        'channel_id': ctx.channel.id, 'bets': {},
        'cashed': {}, 'phase': 'idle', 'host_label': ctx.author.name,
        'start_requested': False
    })
    asyncio.create_task(_run_crash_room(ctx.channel,
                                        ctx.guild.id if ctx.guild else None,
                                        ctx.author.name))
    try: await ctx.message.delete()
    except: pass


# ── Blackjack ─────────────────────────────────────────────────────────────────

def cv(cards):
    t = sum(cards); a = cards.count(11)
    while t > 21 and a: t -= 10; a -= 1
    return t

def cs(cards):
    return "  ".join("A" if c == 11 else str(c) for c in cards)

def bj_embed(player_cards, dealer_cards, bet, show_dealer=False,
             title="Blackjack", color=C.PRIMARY, extra=""):
    """Text-only fallback embed (kept for any old callers)."""
    pv = cv(player_cards); dv = cv(dealer_cards)
    desc = (
        f"**Your hand:** {cs(player_cards)}  —  **{pv}**\n"
        f"**Dealer:** {cs(dealer_cards) + '  — **' + str(dv) + '**' if show_dealer else str(dealer_cards[0]) + '  🂠'}\n\n"
        f"**Bet:** R${bet:,}"
    )
    if extra: desc += f"\n\n{extra}"
    return embed(title, desc, color)


def bj_card_payload(username, pc, dc, bet, hide_hole, status, color, title, extra="", footer=None):
    """Build (embed, file) using the image card."""
    pv = cv(pc); dv = cv(dc)
    buf = blackjack_card(pc, dc, pv, dv, bet, status=status, hide_dealer=hide_hole)
    file = send_image(buf, "bj.png")
    desc = f"**Bet:** R${bet:,}"
    if extra: desc += f"\n\n{extra}"
    e = embed(title, desc, color, image="attachment://bj.png", footer=footer)
    return e, file


class BlackjackView(discord.ui.View):
    def __init__(self, user_id, user_name, bet, start_balance, player_cards, dealer_cards, deck):
        super().__init__(timeout=120)
        self.user_id       = user_id; self.user_name = user_name; self.bet = bet
        self.start_balance = start_balance
        self.player_cards  = player_cards; self.dealer_cards = dealer_cards
        self.deck          = deck; self.game_over = False; self.first_action = True
        hit = discord.ui.Button(label="👊 Hit",         style=discord.ButtonStyle.primary,  custom_id="bj_hit")
        std = discord.ui.Button(label="🛑 Stand",       style=discord.ButtonStyle.danger,    custom_id="bj_stand")
        dbl = discord.ui.Button(label="⬆️ Double Down", style=discord.ButtonStyle.secondary, custom_id="bj_double")
        hit.callback = self.hit_callback; std.callback = self.stand_callback; dbl.callback = self.double_callback
        self.add_item(hit); self.add_item(std); self.add_item(dbl)

    def _disable_all(self):
        for item in self.children: item.disabled = True

    def _disable_double(self):
        for item in self.children:
            if getattr(item, 'custom_id', None) == 'bj_double': item.disabled = True

    async def _edit(self, interaction, hide_hole, status, color, title, extra="", view=None):
        embed, file = bj_card_payload(self.user_name, self.player_cards, self.dealer_cards,
                                      self.bet, hide_hole, status, color, title, extra)
        kwargs = {'embed': embed, 'attachments': [file]}
        if view is not None: kwargs['view'] = view
        if interaction.response.is_done():
            await interaction.message.edit(**kwargs)
        else:
            await interaction.response.edit_message(**kwargs)

    async def hit_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("Not your game!", ephemeral=True); return
        if self.game_over: return
        self.first_action = False; self._disable_double()
        self.player_cards.append(self.deck.pop())
        if cv(self.player_cards) > 21:
            await self._finish(interaction, bust=True)
        else:
            await self._edit(interaction, hide_hole=True, status='playing',
                             color=C.PRIMARY, title="Blackjack — Hit!", view=self)

    async def stand_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("Not your game!", ephemeral=True); return
        if self.game_over: return
        await self._finish(interaction)

    async def double_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("Not your game!", ephemeral=True); return
        if self.game_over: return
        if not self.first_action:
            await interaction.response.send_message("Double Down only available before hitting!", ephemeral=True); return
        if self.bet > get_user_balance(self.user_id):
            await interaction.response.send_message("Not enough balance to double down!", ephemeral=True); return
        self.bet *= 2; self.player_cards.append(self.deck.pop()); self.first_action = False
        await self._finish(interaction)

    async def _finish(self, interaction, bust=False):
        self.game_over = True; self._disable_all(); self.stop(); active_bj.pop(self.user_id, None)

        # 1) Reveal hole card first
        await self._edit(interaction, hide_hole=False, status='playing',
                         color=C.ACCENT, title="Blackjack — Dealer reveals…", view=self)

        # 2) Dealer draws one card at a time (animated) unless player busted
        if not bust:
            while cv(self.dealer_cards) < 17:
                await asyncio.sleep(0.9)
                self.dealer_cards.append(self.deck.pop())
                await self._edit(interaction, hide_hole=False, status='playing',
                                 color=C.ACCENT, title="Blackjack — Dealer draws…", view=self)

        pv = cv(self.player_cards); dv = cv(self.dealer_cards)
        if bust or pv > 21:   won = False; result = "Bust! You went over 21."; status = 'bust'
        elif dv > 21:         won = True;  result = "Dealer busts! You win!"; status = 'win'
        elif pv > dv:         won = True;  result = "Higher hand — You win!"; status = 'win'
        elif pv < dv:         won = False; result = "Dealer wins.";            status = 'lose'
        else:                 won = None;  result = "Push — it's a tie.";       status = 'push'

        if won is True:
            new_bal = self.start_balance + self.bet; add_to_stats(self.user_id, True, self.bet)
            set_user_balance(self.user_id, new_bal); color = C.SUCCESS
            extra = f"🎉 **{result}**\n+R${self.bet:,}  |  New Balance: {fmt(new_bal)}"
            if interaction.guild: asyncio.create_task(assign_rank_role(interaction.guild, self.user_id))
        elif won is False:
            new_bal = max(0, self.start_balance - self.bet); add_to_stats(self.user_id, False, self.bet)
            set_user_balance(self.user_id, new_bal); color = C.ERROR
            extra = f"😢 **{result}**\n-R${self.bet:,}  |  New Balance: {fmt(new_bal)}"
        else:
            new_bal = self.start_balance; color = C.ACCENT
            extra = f"🤝 **{result}**\nNo change  |  Balance: {fmt(new_bal)}"

        await asyncio.sleep(0.5)
        title = "Blackjack — " + ("WIN!" if won is True else ("LOSS" if won is False else "TIE"))
        await self._edit(interaction, hide_hole=False, status=status,
                         color=color, title=title, extra=extra, view=self)
        profit = self.bet if won is True else (-self.bet if won is False else 0)
        asyncio.create_task(send_to_history(interaction.guild, 'blackjack', self.user_name, self.user_id, self.bet, won, profit, new_bal))

    async def on_timeout(self): active_bj.pop(self.user_id, None)

# ── Mines ─────────────────────────────────────────────────────────────────────

MINES_ROWS = 4; MINES_COLS = 5; MINES_TOTAL = MINES_ROWS * MINES_COLS

def mines_multiplier(mines_count, picks):
    if picks == 0: return 1.0
    mult = 1.0; safe = MINES_TOTAL - mines_count
    for i in range(picks): mult *= (MINES_TOTAL - i) / (safe - i)
    return round(mult * 0.97, 2)

def make_mines_embed(bet, mines_count, picks, client_seed, public_hash,
                     server_seed=None, status=None, color=C.SECONDARY):
    mult = mines_multiplier(mines_count, picks)
    profit = round(bet * mult) - bet if picks > 0 else 0
    safe = MINES_TOTAL - mines_count
    desc = (f"**Bet:** {bet:.2f}\n**Multiplier:** {mult:.1f}×\n**Profits:** {profit:.2f} pts\n"
            f"{mines_count} 💣 | {safe} 💎\n\n🔐 **Provably Fair:**\n"
            f"**Public Hash:** `{public_hash}`\n**Client Seed:** `{client_seed}`\n")
    desc += f"**Server Seed:** `{server_seed}`\n" if server_seed else "**Server Seed:** `Hidden`\n"
    if status: desc += f"\n{status}"
    return embed("⛏️ Mines", desc, color)


class MinesView(discord.ui.View):
    def __init__(self, user_id, user_name, bet, mines_count, mine_positions, server_seed, client_seed, public_hash):
        super().__init__(timeout=120)
        self.user_id = user_id; self.user_name = user_name; self.bet = bet; self.mines_count = mines_count
        self.mine_positions = mine_positions; self.server_seed = server_seed
        self.client_seed = client_seed; self.public_hash = public_hash
        self.revealed = set(); self.game_over = False
        for row in range(MINES_ROWS):
            for col in range(MINES_COLS):
                idx = row * MINES_COLS + col
                btn = discord.ui.Button(label="?", style=discord.ButtonStyle.secondary, row=row, custom_id=f"mine_{idx}")
                btn.callback = self.make_callback(idx); self.add_item(btn)
        co = discord.ui.Button(label="💰 Cash Out", style=discord.ButtonStyle.success, row=4, custom_id="cashout")
        co.callback = self.cashout_callback; self.add_item(co)

    def make_callback(self, idx):
        async def callback(interaction: discord.Interaction):
            if interaction.user.id != self.user_id:
                await interaction.response.send_message("Not your game!", ephemeral=True); return
            if self.game_over or idx in self.revealed:
                await interaction.response.send_message("Invalid move!", ephemeral=True); return
            if idx in self.mine_positions:
                self.game_over = True; self._reveal_all()
                bal = get_user_balance(self.user_id); new_bal = bal - self.bet
                set_user_balance(self.user_id, new_bal); add_to_stats(self.user_id, False, self.bet)
                active_mines.pop(self.user_id, None); self.stop()
                status = f"💥 Hit a mine! Lost **{self.bet:,}** pts  |  New Balance: **R${new_bal:,}**"
                embed = make_mines_embed(self.bet, self.mines_count, len(self.revealed), self.client_seed,
                                         self.public_hash, server_seed=self.server_seed, status=status, color=C.ERROR)
                await interaction.response.edit_message(embed=embed, view=self)
                asyncio.create_task(send_to_history(interaction.guild, 'mines', self.user_name, self.user_id, self.bet, False, self.bet, new_bal))
            else:
                self.revealed.add(idx); picks = len(self.revealed)
                mult = mines_multiplier(self.mines_count, picks); potential = round(self.bet * mult)
                self._set_gem(idx)
                for item in self.children:
                    if getattr(item, 'custom_id', None) == "cashout":
                        item.label = f"💰 Cash Out  R${potential:,}"; break
                await interaction.response.edit_message(
                    embed=make_mines_embed(self.bet, self.mines_count, picks, self.client_seed, self.public_hash),
                    view=self)
        return callback

    async def cashout_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("Not your game!", ephemeral=True); return
        if self.game_over: return
        picks = len(self.revealed)
        if picks == 0:
            await interaction.response.send_message("Pick at least one cell first!", ephemeral=True); return
        self.game_over = True
        mult = mines_multiplier(self.mines_count, picks); winnings = round(self.bet * mult)
        profit = winnings - self.bet; bal = get_user_balance(self.user_id); new_bal = bal + profit
        set_user_balance(self.user_id, new_bal); add_to_stats(self.user_id, True, self.bet)
        active_mines.pop(self.user_id, None); self._reveal_all(); self.stop()
        status = f"✅ Cashed out **{winnings:,}** pts  |  New Balance: **R${new_bal:,}**"
        embed = make_mines_embed(self.bet, self.mines_count, picks, self.client_seed, self.public_hash,
                                  server_seed=self.server_seed, status=status, color=C.SUCCESS)
        await interaction.response.edit_message(embed=embed, view=self)
        if interaction.guild: asyncio.create_task(assign_rank_role(interaction.guild, self.user_id))
        asyncio.create_task(send_to_history(interaction.guild, 'mines', self.user_name, self.user_id, self.bet, True, profit, new_bal))

    def _set_gem(self, idx):
        for item in self.children:
            if getattr(item, 'custom_id', None) == f"mine_{idx}":
                item.label = "💎"; item.style = discord.ButtonStyle.success; item.disabled = True

    def _reveal_all(self):
        for item in self.children:
            cid = getattr(item, 'custom_id', None)
            if not cid: continue
            if cid.startswith("mine_"):
                idx = int(cid.split("_")[1])
                if idx in self.mine_positions: item.label = "💣"; item.style = discord.ButtonStyle.danger
                elif idx in self.revealed:     item.label = "💎"; item.style = discord.ButtonStyle.success
                else:                          item.label = "·";  item.style = discord.ButtonStyle.secondary
                item.disabled = True
            elif cid == "cashout": item.disabled = True

    async def on_timeout(self):
        if not self.game_over and self.user_id in active_mines:
            picks = len(self.revealed)
            if picks > 0:
                mult = mines_multiplier(self.mines_count, picks)
                set_user_balance(self.user_id, get_user_balance(self.user_id) + round(self.bet * mult) - self.bet)
                add_to_stats(self.user_id, True, self.bet)
            else:
                set_user_balance(self.user_id, get_user_balance(self.user_id) - self.bet)
                add_to_stats(self.user_id, False, self.bet)
            active_mines.pop(self.user_id, None)

# ── Events ────────────────────────────────────────────────────────────────────

def _snap_invite(inv):
    return {
        'uses': inv.uses or 0,
        'inviter_id': inv.inviter.id if inv.inviter else None,
        'max_uses': inv.max_uses or 0,
    }

@bot.event
async def on_ready():
    for guild in bot.guilds:
        try:
            invites = await guild.fetch_invites()
            invite_cache[guild.id] = {inv.code: _snap_invite(inv) for inv in invites}
        except Exception:
            pass
    # Seed DAY1 promo code if it doesn't exist yet
    codes = get_codes()
    if 'DAY1' not in codes:
        codes['DAY1'] = {
            'reward':    10,
            'max_uses':  10,
            'expires_at': (datetime.now(timezone.utc) + timedelta(days=2)).isoformat(),
            'used_by':   [],
        }
        save_codes(codes)
    if NOWPAYMENTS_API_KEY and not getattr(bot, '_deposit_watcher_started', False):
        bot._deposit_watcher_started = True
        bot.loop.create_task(deposit_watcher())
    if NOWPAYMENTS_API_KEY and NOWPAYMENTS_EMAIL and NOWPAYMENTS_PASSWORD \
            and not getattr(bot, '_payout_watcher_started', False):
        bot._payout_watcher_started = True
        bot.loop.create_task(payout_watcher())
    if not getattr(bot, '_hourly_rain_started', False):
        bot._hourly_rain_started = True
        bot.loop.create_task(_hourly_rain_loop())
    if not getattr(bot, '_thread_idle_started', False):
        bot._thread_idle_started = True
        bot.loop.create_task(_thread_idle_loop())
    print(f'{bot.user} has connected to Discord!')
    print('------')

@bot.event
async def on_invite_create(invite):
    guild_id = invite.guild.id
    invite_cache.setdefault(guild_id, {})[invite.code] = _snap_invite(invite)

@bot.event
async def on_invite_delete(invite):
    # Keep the cached entry around so on_member_join can still credit
    # single-use / max-uses invites that Discord deletes the moment
    # they're consumed. We only drop it once the join is processed.
    pass

@bot.event
async def on_message(message):
    if isinstance(message.channel, discord.Thread) and not message.channel.archived:
        thread_activity[message.channel.id] = datetime.now(timezone.utc)
    await bot.process_commands(message)


async def _thread_idle_loop():
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            now = datetime.now(timezone.utc)
            stale = []
            for tid, last in list(thread_activity.items()):
                if (now - last).total_seconds() >= THREAD_IDLE_TIMEOUT:
                    stale.append(tid)
            for tid in stale:
                for guild in bot.guilds:
                    thread = guild.get_thread(tid)
                    if thread is not None and not thread.archived:
                        try:
                            await thread.edit(archived=True, reason="Idle for 24h — auto-closed")
                            try:
                                await thread.send("🔒 This thread was auto-closed after 24 hours of inactivity. Create a new one with `.thread create`.")
                            except: pass
                        except discord.Forbidden:
                            pass
                        except Exception:
                            pass
                    thread_activity.pop(tid, None)
            for uids in user_threads.values():
                for tid in stale:
                    uids.discard(tid)
        except Exception as e:
            print(f"[thread_idle_loop] error: {e}")
        await asyncio.sleep(600)


@bot.event
async def on_member_join(member):
    if member.bot:
        return
    guild = member.guild
    try:
        new_invites = await guild.fetch_invites()
    except Exception:
        new_invites = []
    old = invite_cache.get(guild.id, {})
    new_map = {inv.code: _snap_invite(inv) for inv in new_invites}

    inviter_id = None
    consumed_code = None

    # Case 1: an existing invite's use count went up.
    for code, snap in new_map.items():
        prev = old.get(code)
        prev_uses = prev['uses'] if prev else 0
        if snap['uses'] > prev_uses:
            inviter_id = snap['inviter_id'] or (prev['inviter_id'] if prev else None)
            consumed_code = code
            break

    # Case 2: an invite vanished (single-use / hit max_uses) — credit cached inviter.
    if inviter_id is None:
        for code, prev in old.items():
            if code not in new_map:
                inviter_id = prev.get('inviter_id')
                consumed_code = code
                break

    # Refresh cache: keep cached entries that Discord deleted *except*
    # the one we just consumed, so we don't double-credit later joins.
    merged = dict(old)
    merged.update(new_map)
    if consumed_code and consumed_code not in new_map:
        merged.pop(consumed_code, None)
    invite_cache[guild.id] = merged

    if not inviter_id or inviter_id == member.id:
        return
    today = datetime.now(timezone.utc).date().isoformat()
    data, uid = get_user(inviter_id)
    if data[uid].get('daily_invites_date') != today:
        data[uid]['daily_invites'] = 0
        data[uid]['daily_invites_date'] = today
    data[uid]['daily_invites'] = data[uid].get('daily_invites', 0) + 1
    data[uid]['total_invites']  = data[uid].get('total_invites', 0) + 1
    save_data(data)

# ── Admin ─────────────────────────────────────────────────────────────────────

@bot.command(name='addbal')
@commands.has_permissions(administrator=True)
async def addbal(ctx, member: discord.Member, amount: int):
    if amount == 0: await ctx.send("❌ Amount cannot be zero!"); return
    old_bal = get_user_balance(member.id); new_bal = old_bal + amount
    if new_bal < 0: await ctx.send(f"❌ Cannot reduce {member.name}'s balance below R$0!"); return
    set_user_balance(member.id, new_bal)
    img_buf = addbal_card(member.name, amount, new_bal)
    e = embed("🔧 Admin — Balance Updated", color=C.SUCCESS if amount > 0 else C.ERROR, image="attachment://addbal.png")
    await ctx.send(embed=e, file=send_image(img_buf, 'addbal.png'))

@addbal.error
async def addbal_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):   await ctx.send("❌ Member not found — mention them with @")
    else:                                              await ctx.send("❌ Usage: `.addbal @user <amount>`")


@bot.command(name='removebal')
@commands.has_permissions(administrator=True)
async def removebal(ctx, member: discord.Member, amount: int):
    if amount <= 0: await ctx.send("❌ Amount must be positive!"); return
    old_bal = get_user_balance(member.id)
    if amount > old_bal:
        await ctx.send(f"❌ **{member.name}** only has **R${old_bal:,}** — can't remove more than their balance!"); return
    new_bal = old_bal - amount
    set_user_balance(member.id, new_bal)
    img_buf = addbal_card(member.name, -amount, new_bal)
    e = embed(
        "Admin — Balance Removed",
        f"Removed **R${amount:,}** from {member.mention}\n**New Balance:** {fmt(new_bal)}",
        color=C.ERROR, image="attachment://addbal.png",
    )
    await ctx.send(embed=e, file=send_image(img_buf, 'addbal.png'))

@removebal.error
async def removebal_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):   await ctx.send("❌ Member not found — mention them with @")
    else:                                              await ctx.send("❌ Usage: `.removebal @user <amount>`")


@bot.command(name='updwithdraw')
@commands.has_permissions(administrator=True)
async def updwithdraw(ctx, member: discord.Member, amount: int):
    if amount < 0: await ctx.send("❌ Amount cannot be negative!"); return
    data, uid = get_user(member.id)
    data[uid]['total_withdrawn'] = data[uid].get('total_withdrawn', 0) + amount; save_data(data)
    e = embed("🏦 Withdraw Updated", (
        f"**User:** {member.name}\n**Added:** {amount:,} pts\n"
        f"**Total Withdrawn:** {data[uid]['total_withdrawn']:,} pts"), color=C.SUCCESS)
    await ctx.send(embed=e)


@bot.command(name='updatedeposit')
@commands.has_permissions(administrator=True)
async def updatedeposit(ctx, member: discord.Member, amount: float):
    if amount < 0:
        await ctx.send("❌ Amount cannot be negative!")
        return
    data, uid = get_user(member.id)
    data[uid]['total_deposited'] = data[uid].get('total_deposited', 0.0) + amount
    save_data(data)
    e = embed("💰 Deposit Updated", (
        f"**User:** {member.name}\n**Added:** ${amount:.2f}\n"
        f"**Total Deposited:** ${data[uid]['total_deposited']:.2f}"), color=C.SUCCESS)
    await ctx.send(embed=e)


@updatedeposit.error
async def updatedeposit_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):
        await ctx.send("❌ Member not found — mention them with @")
    else:
        await ctx.send("❌ Usage: `.updatedeposit @user <usd_amount>`")


class PromoMultiplierView(discord.ui.View):
    def __init__(self, author_id, member, amount):
        super().__init__(timeout=60)
        self.author_id = author_id
        self.member = member
        self.amount = amount

    @discord.ui.button(label='1×', style=discord.ButtonStyle.secondary, custom_id='promo_1x')
    async def mult_1x(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.apply_promo(interaction, 1)

    @discord.ui.button(label='2×', style=discord.ButtonStyle.primary, custom_id='promo_2x')
    async def mult_2x(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.apply_promo(interaction, 2)

    @discord.ui.button(label='3×', style=discord.ButtonStyle.primary, custom_id='promo_3x')
    async def mult_3x(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.apply_promo(interaction, 3)

    @discord.ui.button(label='5×', style=discord.ButtonStyle.success, custom_id='promo_5x')
    async def mult_5x(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.apply_promo(interaction, 5)

    @discord.ui.button(label='10×', style=discord.ButtonStyle.success, custom_id='promo_10x')
    async def mult_10x(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.apply_promo(interaction, 10)

    @discord.ui.button(label='20×', style=discord.ButtonStyle.danger, custom_id='promo_20x')
    async def mult_20x(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.apply_promo(interaction, 20)

    async def apply_promo(self, interaction, multiplier):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("❌ Only the admin who started this can select a multiplier!", ephemeral=True)
            return

        wager_req = self.amount * multiplier
        old_bal = get_user_balance(self.member.id)
        new_bal = old_bal + self.amount
        set_user_balance(self.member.id, new_bal)

        data, uid = get_user(self.member.id)
        data[uid]['wager_requirement'] = data[uid].get('wager_requirement', 0) + wager_req
        data[uid]['wager_since_promo'] = data[uid]['stats'].get('total_wagered', 0)
        save_data(data)

        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(view=self)

        e = embed("🎁 Promo Applied!", color=C.SUCCESS,
                  footer="User must wager this amount before withdrawing.")
        e.add_field(name="User", value=self.member.mention, inline=False)
        e.add_field(name="Points Added", value=f"R${self.amount:,}", inline=True)
        e.add_field(name="Multiplier", value=f"{multiplier}×", inline=True)
        e.add_field(name="Wager Requirement", value=f"R${wager_req:,}", inline=True)
        e.add_field(name="New Balance", value=fmt(new_bal), inline=False)

        await interaction.followup.send(embed=e)

    async def on_timeout(self):
        for item in self.children:
            item.disabled = True
        try:
            await self.message.edit(view=self)
        except:
            pass


@bot.command(name='promo')
@commands.has_permissions(administrator=True)
async def promo(ctx, member: discord.Member, amount: int):
    if amount <= 0:
        await ctx.send("❌ Amount must be positive!")
        return

    e = embed("🎁 Promo — Select Multiplier", (
        f"**User:** {member.mention}\n"
        f"**Amount:** R${amount:,}\n\n"
        f"Select a wager multiplier requirement.\n"
        f"The user must wager `amount × multiplier` before withdrawing."
    ), C.LOBBY)

    view = PromoMultiplierView(ctx.author.id, member, amount)
    view.message = await ctx.send(embed=e, view=view)


@promo.error
async def promo_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):
        await ctx.send("❌ Member not found — mention them with @")
    else:
        await ctx.send("❌ Usage: `.promo @user <amount>`")


@bot.command(name='wager')
async def wager_status(ctx):
    data, uid = get_user(ctx.author.id)
    wager_req = data[uid].get('wager_requirement', 0)
    if wager_req <= 0:
        await ctx.send("✅ You have no active wager requirements. You can withdraw freely!")
        return

    wager_since = data[uid].get('wager_since_promo', 0)
    total_wagered = data[uid]['stats'].get('total_wagered', 0)
    wagered_amount = total_wagered - wager_since
    remaining = wager_req - wagered_amount
    progress = min(100, (wagered_amount / wager_req) * 100) if wager_req > 0 else 100

    bar_filled = int(progress // 5)
    bar = "█" * bar_filled + "░" * (20 - bar_filled)

    e = embed("🔒 Wager Requirement Status", None,
              C.ACCENT if remaining > 0 else C.SUCCESS)
    e.add_field(name="Requirement", value=f"R${wager_req:,}", inline=True)
    e.add_field(name="Wagered", value=f"R${wagered_amount:,}", inline=True)
    e.add_field(name="Remaining", value=f"R${remaining:,}", inline=True)
    e.add_field(name="Progress", value=f"`{bar}` {progress:.1f}%", inline=False)

    if remaining <= 0:
        e.description = "🎉 **Complete!** You can now withdraw."
        e.color = C.SUCCESS
    else:
        e.description = "Play games to meet the requirement before withdrawing."

    await ctx.send(embed=e)


@bot.command(name='clearwager')
@commands.has_permissions(administrator=True)
async def clearwager(ctx, member: discord.Member):
    data, uid = get_user(member.id)
    old_req = data[uid].get('wager_requirement', 0)
    data[uid]['wager_requirement'] = 0
    data[uid]['wager_since_promo'] = 0
    save_data(data)
    e = embed("🔓 Wager Requirement Cleared",
              f"Cleared wager requirement for {member.mention}\n**Previous:** R${old_req:,}",
              C.SUCCESS)
    await ctx.send(embed=e)


@clearwager.error
async def clearwager_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):
        await ctx.send("❌ Member not found — mention them with @")
    else:
        await ctx.send("❌ Usage: `.clearwager @user`")


@bot.command(name='wagerstatus')
@commands.has_permissions(administrator=True)
async def wagerstatus_admin(ctx, member: discord.Member):
    data, uid = get_user(member.id)
    wager_req = data[uid].get('wager_requirement', 0)

    if wager_req <= 0:
        await ctx.send(f"✅ **{member.name}** has no active wager requirements.")
        return

    wager_since = data[uid].get('wager_since_promo', 0)
    total_wagered = data[uid]['stats'].get('total_wagered', 0)
    wagered_amount = total_wagered - wager_since
    remaining = wager_req - wagered_amount
    progress = min(100, (wagered_amount / wager_req) * 100) if wager_req > 0 else 100

    bar_filled = int(progress // 5)
    bar = "█" * bar_filled + "░" * (20 - bar_filled)

    e = embed(f"🔒 Wager Status — {member.name}", None, C.ACCENT)
    e.add_field(name="Requirement", value=f"R${wager_req:,}", inline=True)
    e.add_field(name="Wagered", value=f"R${wagered_amount:,}", inline=True)
    e.add_field(name="Remaining", value=f"R${remaining:,}", inline=True)
    e.add_field(name="Progress", value=f"`{bar}` {progress:.1f}%", inline=False)

    await ctx.send(embed=e)


@wagerstatus_admin.error
async def wagerstatus_admin_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):
        await ctx.send("❌ Member not found — mention them with @")
    else:
        await ctx.send("❌ Usage: `.wagerstatus @user`")


@updwithdraw.error
async def updwithdraw_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.MemberNotFound):   await ctx.send("❌ Member not found — mention them with @")
    else:                                              await ctx.send("❌ Usage: `.updwithdraw @user <amount>`")


@bot.command(name='resetstats')
@commands.has_permissions(administrator=True)
async def resetstats(ctx):
    data = load_data(); count = 0
    for uid, ud in data.items():
        if uid.startswith('__'): continue
        ud['stats'] = {'wins': 0, 'losses': 0, 'total_wagered': 0, 'total_lost': 0}
        ud['rakeback_available'] = 0.0; ud['wager_at_last_monthly'] = 0; count += 1
    save_data(data)
    e = embed("🔄 Stats Reset", f"Reset stats for **{count}** players.", color=C.WARNING)
    await ctx.send(embed=e)

@resetstats.error
async def resetstats_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")


@bot.command(name='setrank')
@commands.has_permissions(administrator=True)
async def setrank(ctx, rank_name: str, role: discord.Role = None):
    rn = rank_name.lower().strip()
    if rn not in RANK_KEYS:
        await ctx.send(f"❌ Valid ranks: `{', '.join(RANK_KEYS)}`"); return
    cfg = get_config()
    if 'rank_roles' not in cfg: cfg['rank_roles'] = {}
    if role is None:
        cfg['rank_roles'].pop(rn, None); save_config(cfg)
        e = embed("🏅 Rank Role Removed",
                  f"Cleared role for **{rank_name.title()}**.", color=C.WARNING)
    else:
        cfg['rank_roles'][rn] = str(role.id); save_config(cfg)
        e = embed("🏅 Rank Role Set",
                  f"**{rank_name.title()}** rank → {role.mention}", color=C.SUCCESS)
    await ctx.send(embed=e)

@setrank.error
async def setrank_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.RoleNotFound):     await ctx.send("❌ Role not found — mention it with @")
    else:                                              await ctx.send(f"❌ Usage: `.setrank <rank> @role`\nRanks: `{', '.join(RANK_KEYS)}`")


@bot.command(name='rankroles')
@commands.has_permissions(administrator=True)
async def rankroles_cmd(ctx):
    cfg = get_config(); rr = cfg.get('rank_roles', {})
    lines = []
    for rk, (_, rname, rcolor) in zip(RANK_KEYS, RANKS):
        role_id = rr.get(rk)
        role_str = f"<@&{role_id}>" if role_id else "*(not set)*"
        lines.append(f"{rname}: {role_str}")
    e = embed("🏅 Rank Role Configuration", "\n".join(lines), color=C.LOBBY,
              footer="Use .setrank <rank> @role to configure  |  .setrank <rank> to clear")
    await ctx.send(embed=e)


@bot.command(name='sethistory')
@commands.has_permissions(administrator=True)
async def sethistory(ctx, channel: discord.TextChannel = None):
    if channel is None:
        await ctx.send("❌ Usage: `.sethistory #channel`"); return
    cfg = get_config()
    cfg['history_channel'] = str(channel.id)
    save_config(cfg)
    e = embed(
        "Bet History Channel Set",
        f"Every bet result will now be logged to {channel.mention}.",
        color=C.SUCCESS,
    )
    await ctx.send(embed=e)

@sethistory.error
async def sethistory_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.ChannelNotFound):  await ctx.send("❌ Channel not found — mention it with #")
    else: await ctx.send("❌ Usage: `.sethistory #channel`")


@bot.command(name='setdepositlog', aliases=['setdepositlogs'])
@commands.has_permissions(administrator=True)
async def setdepositlog(ctx, channel: discord.TextChannel = None):
    if channel is None:
        await ctx.send("❌ Usage: `.setdepositlog #channel`"); return
    cfg = get_config()
    cfg['deposit_log_channel'] = str(channel.id)
    save_config(cfg)
    e = embed(
        "Deposit Log Channel Set",
        f"Every confirmed deposit will now be logged to {channel.mention}.",
        color=C.SUCCESS,
    )
    await ctx.send(embed=e)

@setdepositlog.error
async def setdepositlog_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    elif isinstance(error, commands.ChannelNotFound):  await ctx.send("❌ Channel not found — mention it with #")
    else: await ctx.send("❌ Usage: `.setdepositlog #channel`")


@bot.command(name='cleardepositlog')
@commands.has_permissions(administrator=True)
async def cleardepositlog(ctx):
    cfg = get_config()
    if 'deposit_log_channel' not in cfg:
        await ctx.send("❌ No deposit log channel is currently set."); return
    del cfg['deposit_log_channel']
    save_config(cfg)
    e = embed("💸 Deposit Logging Disabled", "Deposit logging has been turned off.", color=C.WARNING)
    await ctx.send(embed=e)

@cleardepositlog.error
async def cleardepositlog_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")


@bot.command(name='clearhistory')
@commands.has_permissions(administrator=True)
async def clearhistory(ctx):
    cfg = get_config()
    if 'history_channel' not in cfg:
        await ctx.send("❌ No history channel is currently set."); return
    del cfg['history_channel']
    save_config(cfg)
    e = embed("📋 Bet History Disabled", "Bet history logging has been turned off.", color=C.WARNING)
    await ctx.send(embed=e)

@clearhistory.error
async def clearhistory_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")


# ── Core Commands ─────────────────────────────────────────────────────────────

@bot.command(name='coinflip', aliases=['cf'])
async def coinflip(ctx, amount: str, choice: str):
    bal = get_user_balance(ctx.author.id)
    choice = choice.lower()

    if choice not in ['heads', 'tails', 'h', 't']:
        await ctx.send("❌ Choose **heads** or **tails** (or h/t)")
        return

    amount = resolve_bet(amount, bal)

    if amount is None:
        await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`.")
        return

    if amount <= 0:
        await ctx.send("❌ Bet must be positive!")
        return

    if amount > bal:
        await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}")
        return

    choice = "heads" if choice == "h" else ("tails" if choice == "t" else choice)

    server_seed, client_seed, public_hash = generate_seeds()
    result = pf_coinflip(server_seed, client_seed)
    won = choice == result

    frames = [
        "🌀 Flipping...",
        "🪙 Spinning...",
        "✨ Almost...",
        "🎯 Result..."
    ]

    anim_buf = coinflip_anim_card(result, choice, amount, amount if won else 0)

    e = embed("🪙 Coin Flip", frames[0], C.ACCENT)

    e.set_image(url="attachment://coinflip_anim.png")

    msg = await ctx.send(
        embed=e,
        file=send_image(anim_buf, "coinflip_anim.png")
    )

    for frame in frames[1:]:
        await asyncio.sleep(0.45)
        e.description = frame
        await msg.edit(embed=e)

    await asyncio.sleep(0.35)

    new_bal = bal + amount if won else bal - amount

    add_to_stats(ctx.author.id, won, amount)
    set_user_balance(ctx.author.id, new_bal)

    if ctx.guild:
        asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))

    e = embed("🪙 🎉 Coin Flip — YOU WON!" if won else "❌ Coin Flip — Lost",
              color=C.SUCCESS if won else C.ERROR)

    e.add_field(
        name="You chose",
        value=choice.upper(),
        inline=True
    )

    e.add_field(
        name="Result",
        value=result.upper(),
        inline=True
    )

    e.add_field(
        name="Change",
        value=f"{'+' if won else '-'}R${amount:,}",
        inline=True
    )

    e.add_field(
        name="New Balance",
        value=fmt(new_bal),
        inline=False
    )

    pf_add_field(e, server_seed, client_seed, public_hash, "coinflip")

    img_buf = coinflip_card(result, choice, amount, amount if won else 0)

    e.set_image(url="attachment://coinflip.png")

    await msg.edit(
        embed=e,
        attachments=[send_image(img_buf, "coinflip.png")]
    )

    asyncio.create_task(
        send_to_history(
            ctx.guild,
            'coinflip',
            ctx.author.name,
            ctx.author.id,
            amount,
            won,
            amount,
            new_bal
        )
    )

@bot.command(name='balance', aliases=['bal', 'b'])
async def balance(ctx, member: discord.Member = None):
    target = member or ctx.author
    bal = get_user_balance(target.id)
    img_buf = balance_card(target.name, bal)
    e = embed(f"💰 {target.name}'s Balance", color=C.SECONDARY)
    e.add_field(name="Points", value=f"`{bal:,}`", inline=True)
    e.add_field(name="Cash Value", value=f"`R${bal:,}`", inline=True)
    e.add_field(name="USD", value=f"`${bal * POINTS_TO_USD:.2f}`", inline=True)
    e.set_image(url="attachment://balance.png")
    await ctx.send(embed=e, file=send_image(img_buf, 'balance.png'))




@bot.command(name='dice')
async def dice(ctx, amount: str, guess: int):
    bal = get_user_balance(ctx.author.id)
    if guess < 1 or guess > 6: await ctx.send("❌ Guess a number 1–6!"); return
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    faces = ["⚀","⚁","⚂","⚃","⚄","⚅"]
    e = embed("🎲 Dice Roll", "🎲 Rolling...", C.ACCENT)
    msg = await ctx.send(embed=e)
    for _ in range(4):
        await asyncio.sleep(0.4); e.description = f"🎲 {faces[random.randint(0,5)]}  Rolling..."; await msg.edit(embed=e)
    await asyncio.sleep(0.3)
    roll = pf_dice_roll(server_seed, client_seed); won = guess == roll
    new_bal = (bal + amount * 5) if won else (bal - amount)
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Dice — WIN! (×5)" if won else "❌ Dice — Lost",
              color=C.SUCCESS if won else C.ERROR)
    e.add_field(name="Your guess", value=f"{guess} {faces[guess-1]}", inline=True)
    e.add_field(name="Rolled",     value=f"{roll} {faces[roll-1]}",   inline=True)
    e.add_field(name="Change",     value=f"{'+'if won else '-'}R${amount*(5 if won else 1):,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "dice")
    img_buf = dice_card([roll], amount, amount * 5 if won else 0, pick=guess)
    e.set_image(url="attachment://dice.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'dice.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'dice', ctx.author.name, ctx.author.id, amount, won, amount*5 if won else amount, new_bal))


@bot.command(name='limbo')
async def limbo(ctx, amount: str, target: str = None):
    bal = get_user_balance(ctx.author.id)
    if target is None:
        await ctx.send("❌ Usage: `.limbo <amount> <target>` — e.g. `.limbo 100 2.5`"); return
    try:
        target_mult = round(float(target.lower().replace('x', '').strip()), 2)
    except ValueError:
        await ctx.send("❌ Invalid target! Provide a multiplier like `2.0` or `10x`."); return
    if target_mult < 1.01 or target_mult > 1000:
        await ctx.send("❌ Target multiplier must be between 1.01× and 1000×!"); return
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    result_mult = pf_limbo(server_seed, client_seed)
    e = embed("📈 Limbo", "📈 Climbing...", C.ACCENT)
    msg = await ctx.send(embed=e)
    for step in (1.00, max(1.00, result_mult * 0.4), max(1.00, result_mult * 0.75)):
        await asyncio.sleep(0.4); e.description = f"📈 `{step:.2f}×`  Climbing..."; await msg.edit(embed=e)
    await asyncio.sleep(0.3)
    won = result_mult >= target_mult
    profit = round(amount * target_mult) - amount if won else amount
    new_bal = bal + profit if won else bal - amount
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Limbo — WIN! (×{target_mult:g})" if won else "❌ Limbo — Lost",
              color=C.SUCCESS if won else C.ERROR)
    e.add_field(name="Your target", value=f"{target_mult:.2f}×", inline=True)
    e.add_field(name="Result",      value=f"{result_mult:.2f}×", inline=True)
    e.add_field(name="Change",      value=f"{'+' if won else '-'}R${(profit if won else amount):,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "limbo")
    img_buf = limbo_card(target_mult, result_mult, amount, profit if won else 0, username=ctx.author.name)
    e.set_image(url="attachment://limbo.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'limbo.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'limbo', ctx.author.name, ctx.author.id, amount, won, profit if won else amount, new_bal))


@bot.command(name='rps')
async def rps(ctx, amount: str, choice: str = None):
    bal = get_user_balance(ctx.author.id)
    if choice is None:
        await ctx.send("❌ Usage: `.rps <amount> <rock/paper/scissors>` (or r/p/s)"); return
    cmap = {'r': 'rock', 'p': 'paper', 's': 'scissors', 'rock': 'rock', 'paper': 'paper', 'scissors': 'scissors'}
    player = cmap.get(choice.lower())
    if player is None:
        await ctx.send("❌ Choose **rock**, **paper**, or **scissors** (r/p/s)!"); return
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    bot_move = pf_rps(server_seed, client_seed)
    EMO = {'rock': '🪨', 'paper': '📄', 'scissors': '✂️'}
    e = embed("✂️ Rock · Paper · Scissors", "Rock... Paper... Scissors...", C.ACCENT)
    msg = await ctx.send(embed=e)
    for f in ("🪨", "📄", "✂️"):
        await asyncio.sleep(0.4); e.description = f"Shoot!  {f}"; await msg.edit(embed=e)
    await asyncio.sleep(0.3)
    beats = {'rock': 'scissors', 'paper': 'rock', 'scissors': 'paper'}
    if player == bot_move: outcome = 'tie'
    elif beats[player] == bot_move: outcome = 'win'
    else: outcome = 'lose'
    won = True if outcome == 'win' else (False if outcome == 'lose' else None)
    new_bal = bal + amount if outcome == 'win' else (bal - amount if outcome == 'lose' else bal)
    if outcome != 'tie':
        add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
        if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    title = "🎉 RPS — YOU WON! (×2)" if outcome == 'win' else ("❌ RPS — Lost" if outcome == 'lose' else "🤝 RPS — TIE (push)")
    color = C.SUCCESS if outcome == 'win' else (C.ERROR if outcome == 'lose' else C.ACCENT)
    e = embed(title, color=color)
    e.add_field(name="You", value=f"{EMO[player]} {player.title()}", inline=True)
    e.add_field(name="Bot", value=f"{EMO[bot_move]} {bot_move.title()}", inline=True)
    e.add_field(name="Change", value="±R$0" if outcome == 'tie' else f"{'+' if won else '-'}R${amount:,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "rps")
    img_buf = rps_card(player, bot_move, amount, amount if outcome == 'win' else (-amount if outcome == 'lose' else 0), outcome=outcome)
    e.set_image(url="attachment://rps.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'rps.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'rps', ctx.author.name, ctx.author.id, amount, won, amount if outcome != 'tie' else 0, new_bal))


@bot.command(name='slide')
async def slide(ctx, amount: str, target: str = None):
    bal = get_user_balance(ctx.author.id)
    if target is None:
        await ctx.send("❌ Usage: `.slide <amount> <target>` — pick 1.10×–10.0×, e.g. `.slide 100 2.0`"); return
    try:
        target_mult = round(float(target.lower().replace('x', '').strip()), 2)
    except ValueError:
        await ctx.send("❌ Invalid target! Provide a multiplier like `2.0` or `5x`."); return
    if target_mult < 1.10 or target_mult > SLIDE_MAX:
        await ctx.send(f"❌ Target must be between 1.10× and {SLIDE_MAX:g}×!"); return
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    result_mult = pf_slide(server_seed, client_seed)
    e = embed("🎢 Slide", "🎢 Sliding...", C.ACCENT)
    msg = await ctx.send(embed=e)
    for step in (result_mult * 0.5, result_mult * 0.85, result_mult):
        await asyncio.sleep(0.4); e.description = f"🎢 `{step:.2f}×`  Sliding..."; await msg.edit(embed=e)
    await asyncio.sleep(0.3)
    won = result_mult >= target_mult
    profit = round(amount * target_mult) - amount if won else amount
    new_bal = bal + profit if won else bal - amount
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Slide — WIN! (×{target_mult:g})" if won else "❌ Slide — Lost",
              color=C.SUCCESS if won else C.ERROR)
    e.add_field(name="Your target", value=f"{target_mult:.2f}×", inline=True)
    e.add_field(name="Landed on",   value=f"{result_mult:.2f}×", inline=True)
    e.add_field(name="Change",      value=f"{'+' if won else '-'}R${(profit if won else amount):,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "slide")
    img_buf = slide_card(target_mult, result_mult, amount, profit if won else 0, username=ctx.author.name)
    e.set_image(url="attachment://slide.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'slide.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'slide', ctx.author.name, ctx.author.id, amount, won, profit if won else amount, new_bal))


@bot.command(name='tight')
async def tight(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    result_mult = pf_tight(server_seed, client_seed)
    e = embed("🗜️ Tight", "🗜️ Tightening...", C.ACCENT)
    msg = await ctx.send(embed=e)
    for step in (result_mult * 0.4, result_mult * 0.8, result_mult):
        await asyncio.sleep(0.4); e.description = f"🗜️ `{step:.2f}×`  Tightening..."; await msg.edit(embed=e)
    await asyncio.sleep(0.3)
    payout = round(amount * result_mult)
    won = payout >= amount
    profit = payout - amount
    new_bal = bal - amount + payout
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Tight — {result_mult:.2f}× PROFIT!" if won else f"❌ Tight — {result_mult:.2f}× (loss)",
              color=C.SUCCESS if won else C.ERROR)
    e.add_field(name="Multiplier", value=f"{result_mult:.2f}×", inline=True)
    e.add_field(name="Payout",     value=fmt(payout), inline=True)
    e.add_field(name="Change",     value=f"{'+' if profit >= 0 else '-'}R${abs(profit):,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "tight")
    img_buf = tight_card(max(1, int(round(result_mult))), 10, amount, payout if won else 0)
    e.set_image(url="attachment://tight.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'tight.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'tight', ctx.author.name, ctx.author.id, amount, won, profit if won else (amount - payout), new_bal))


@bot.command(name='war')
async def war(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    p, dealer = pf_war_cards(server_seed, client_seed)
    RANK_NAMES = {11: 'J', 12: 'Q', 13: 'K', 14: 'A'}
    def cname(r): return RANK_NAMES.get(r, str(r))
    e = embed("⚔️ War", "⚔️ Drawing cards...", C.ACCENT)
    msg = await ctx.send(embed=e)
    await asyncio.sleep(0.6); e.description = f"You draw **{cname(p)}**..."; await msg.edit(embed=e)
    await asyncio.sleep(0.6)
    if p > dealer: outcome = 'win'
    elif p < dealer: outcome = 'lose'
    else: outcome = 'tie'
    won = True if outcome == 'win' else (False if outcome == 'lose' else None)
    new_bal = bal + amount if outcome == 'win' else (bal - amount if outcome == 'lose' else bal)
    if outcome != 'tie':
        add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
        if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    title = "🎉 War — YOU WON! (×2)" if outcome == 'win' else ("❌ War — Dealer Wins" if outcome == 'lose' else "🤝 War — TIE (push)")
    color = C.SUCCESS if outcome == 'win' else (C.ERROR if outcome == 'lose' else C.ACCENT)
    e = embed(title, color=color)
    e.add_field(name="Your card",   value=f"**{cname(p)}**", inline=True)
    e.add_field(name="Dealer card", value=f"**{cname(dealer)}**", inline=True)
    e.add_field(name="Change", value="±R$0" if outcome == 'tie' else f"{'+' if won else '-'}R${amount:,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "war")
    img_buf = war_card(p, dealer, amount, amount if outcome == 'win' else (-amount if outcome == 'lose' else 0))
    e.set_image(url="attachment://war.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'war.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'war', ctx.author.name, ctx.author.id, amount, won, amount if outcome != 'tie' else 0, new_bal))


@bot.command(name='valentines')
async def valentines(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    final = pf_valentines(server_seed, client_seed)
    SPIN = "💞"; RING = "💍"
    def disp(r1, r2, r3): return f"┌─────────────┐\n│  {r1}  {r2}  {r3}  │\n└─────────────┘"
    e = embed("💘 Valentine's Slots", color=0xEC4899)
    e.description = f"```\n{disp(SPIN, SPIN, SPIN)}\n```\nSpinning with love..."
    msg = await ctx.send(embed=e)
    for step in range(1, 4):
        await asyncio.sleep(0.6); rv = [final[i] for i in range(step)]; pv = [SPIN] * (3 - step)
        e.description = f"```\n{disp(*(rv + pv))}\n```"; await msg.edit(embed=e)
    await asyncio.sleep(0.4)
    r1, r2, r3 = final
    if r1 == r2 == r3:
        winnings = amount * (100 if r1 == RING else 10); won = True
        label = "💍 JACKPOT ×100" if r1 == RING else "💞 Triple ×10"
    elif r1 == r2 or r2 == r3:
        winnings = amount * 2; won = True; label = "Pair ×2"
    else:
        winnings = 0; won = False; label = "No match"
    new_bal = bal + winnings if won else bal - amount
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Valentine's — {label}" if won else "❌ Valentine's — No Match",
              color=C.SUCCESS if won else C.ERROR)
    e.description = f"```\n{disp(r1, r2, r3)}\n```"
    e.add_field(name="Won" if won else "Lost", value=fmt(winnings if won else amount), inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=True)
    pf_add_field(e, server_seed, client_seed, public_hash, "valentines")
    img_buf = valentines_card(ctx.author.name, "", 100 if won else 0, winnings if won else 0)
    e.set_image(url="attachment://valentines.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'valentines.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'valentines', ctx.author.name, ctx.author.id, amount, won, winnings if won else amount, new_bal))


@bot.command(name='twist')
async def twist(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    rolls, result_mult = pf_twist(server_seed, client_seed)
    faces = ["⚀", "⚁", "⚂", "⚃", "⚄", "⚅"]
    e = embed("🌀 Twist", "🌀 Rolling the dice...", C.ACCENT)
    msg = await ctx.send(embed=e)
    shown = []
    for r in rolls:
        await asyncio.sleep(0.5); shown.append(faces[r - 1])
        e.description = f"🌀 {' '.join(shown)}  moving..."; await msg.edit(embed=e)
    await asyncio.sleep(0.3)
    payout = round(amount * result_mult)
    won = payout >= amount
    profit = payout - amount
    new_bal = bal - amount + payout
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Twist — {result_mult:.2f}× PROFIT!" if won else f"❌ Twist — {result_mult:.2f}× (loss)",
              color=C.SUCCESS if won else C.ERROR)
    e.add_field(name="Rolls", value=f"{' '.join(f'{r}{faces[r-1]}' for r in rolls)}  = {sum(rolls)}", inline=False)
    e.add_field(name="Tile multiplier", value=f"{result_mult:.2f}×", inline=True)
    e.add_field(name="Payout", value=fmt(payout), inline=True)
    e.add_field(name="Change", value=f"{'+' if profit >= 0 else '-'}R${abs(profit):,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "twist")
    img_buf = twist_card([str(r) for r in rolls], amount, payout if won else 0, username=ctx.author.name)
    e.set_image(url="attachment://twist.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'twist.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'twist', ctx.author.name, ctx.author.id, amount, won, profit if won else (amount - payout), new_bal))


class TreasureView(discord.ui.View):
    def __init__(self, user_id, user_name, bet, mults, server_seed, client_seed, public_hash):
        super().__init__(timeout=60)
        self.user_id = user_id; self.user_name = user_name; self.bet = bet
        self.mults = mults; self.server_seed = server_seed
        self.client_seed = client_seed; self.public_hash = public_hash
        self.done = False
        for i in range(len(mults)):
            btn = discord.ui.Button(label=f"🧰 Chest {i+1}", style=discord.ButtonStyle.secondary, custom_id=f"chest_{i}")
            btn.callback = self.make_callback(i); self.add_item(btn)

    def make_callback(self, idx):
        async def callback(interaction: discord.Interaction):
            if interaction.user.id != self.user_id:
                await interaction.response.send_message("Not your game!", ephemeral=True); return
            if self.done:
                await interaction.response.send_message("Already opened a chest!", ephemeral=True); return
            self.done = True
            mult = self.mults[idx]; payout = round(self.bet * mult); profit = payout - self.bet
            won = payout >= self.bet
            bal = get_user_balance(self.user_id); new_bal = bal - self.bet + payout
            set_user_balance(self.user_id, new_bal); add_to_stats(self.user_id, won, self.bet)
            for item in self.children:
                cid = getattr(item, 'custom_id', None)
                if cid and cid.startswith("chest_"):
                    ci = int(cid.split("_")[1]); item.disabled = True
                    item.label = f"{'➡️' if ci == idx else '🧰'} {self.mults[ci]:.2f}×"
                    if ci == idx:
                        item.style = discord.ButtonStyle.success if won else discord.ButtonStyle.danger
            self.stop()
            if interaction.guild: asyncio.create_task(assign_rank_role(interaction.guild, self.user_id))
            e = embed(f"🎉 Treasure Hunt — {mult:.2f}× PROFIT!" if won else f"❌ Treasure Hunt — {mult:.2f}× (loss)",
                      color=C.SUCCESS if won else C.ERROR)
            e.add_field(name="Chest opened", value=f"#{idx+1} → {mult:.2f}×", inline=True)
            e.add_field(name="Payout", value=fmt(payout), inline=True)
            e.add_field(name="Change", value=f"{'+' if profit >= 0 else '-'}R${abs(profit):,}", inline=True)
            e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
            pf_add_field(e, self.server_seed, self.client_seed, self.public_hash, "treasurehunt")
            await interaction.response.edit_message(embed=e, view=self)
            asyncio.create_task(send_to_history(interaction.guild, 'treasurehunt', self.user_name, self.user_id, self.bet, won, profit if won else (self.bet - payout), new_bal))
        return callback


@bot.command(name='treasurehunt', aliases=['th'])
async def treasurehunt(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    mults = pf_treasure(server_seed, client_seed, 3)
    view = TreasureView(ctx.author.id, ctx.author.name, amount, mults, server_seed, client_seed, public_hash)
    e = embed("💰 Treasure Hunt", C.ACCENT,
              description=(
                  f"Bet: **{fmt(amount)}**\n\nPick a chest! Each holds a hidden multiplier of up to **2.5×**.\n"
                  "Your payout = bet × the chest you open."),
              footer="One pick — choose wisely!")
    await ctx.send(embed=e, view=view)


def make_tower_embed(bet, diff, rows_cleared, client_seed, public_hash, server_seed=None, status=None, color=C.PRIMARY):
    tiles, safe = TOWER_DIFFS[diff]
    cur = tower_multiplier(diff, rows_cleared)
    nxt = tower_multiplier(diff, rows_cleared + 1)
    lines = []
    for r in range(TOWER_ROWS - 1, -1, -1):
        if r < rows_cleared: marker = "🟩 " * tiles
        elif r == rows_cleared and status is None: marker = "⬜ " * tiles + " ⬅️"
        else: marker = "⬛ " * tiles
        lines.append(f"`R{r+1}` {marker}")
    footer = None
    if not server_seed:
        footer = f"Client Seed: {client_seed}  |  Hash: {public_hash[:16]}…"
    e = embed("🗼 Tower Climb", "\n".join(lines), color, footer=footer)
    e.add_field(name="Bet", value=fmt(bet), inline=True)
    e.add_field(name="Difficulty", value=f"{diff.title()} ({safe}/{tiles} safe)", inline=True)
    e.add_field(name="Rows cleared", value=str(rows_cleared), inline=True)
    e.add_field(name="Current", value=f"{cur:.2f}× = {fmt(round(bet*cur))}", inline=True)
    if rows_cleared < TOWER_ROWS:
        e.add_field(name="Next row", value=f"{nxt:.2f}×", inline=True)
    if status:
        e.add_field(name="Result", value=status, inline=False)
    if server_seed:
        pf_add_field(e, server_seed, client_seed, public_hash, "tower")
    return e


class TowerView(discord.ui.View):
    def __init__(self, user_id, user_name, bet, diff, bombs, server_seed, client_seed, public_hash):
        super().__init__(timeout=120)
        self.user_id = user_id; self.user_name = user_name; self.bet = bet
        self.diff = diff; self.bombs = bombs; self.server_seed = server_seed
        self.client_seed = client_seed; self.public_hash = public_hash
        self.row = 0; self.game_over = False
        self._build_row()

    def _build_row(self):
        self.clear_items()
        tiles, _ = TOWER_DIFFS[self.diff]
        for col in range(tiles):
            btn = discord.ui.Button(label=f"{col+1}", style=discord.ButtonStyle.secondary, row=0, custom_id=f"tw_{col}")
            btn.callback = self.make_callback(col); self.add_item(btn)
        cur = tower_multiplier(self.diff, self.row)
        co_label = f"💰 Cash Out  R${round(self.bet*cur):,}" if self.row > 0 else "💰 Cash Out"
        co = discord.ui.Button(label=co_label, style=discord.ButtonStyle.success, row=1, custom_id="tw_cash")
        co.callback = self.cashout_callback; self.add_item(co)

    def _settle_win(self, rows_cleared):
        mult = tower_multiplier(self.diff, rows_cleared); winnings = round(self.bet * mult)
        profit = winnings - self.bet; bal = get_user_balance(self.user_id); new_bal = bal + profit
        set_user_balance(self.user_id, new_bal); add_to_stats(self.user_id, True, self.bet)
        return mult, winnings, profit, new_bal

    def make_callback(self, col):
        async def callback(interaction: discord.Interaction):
            if interaction.user.id != self.user_id:
                await interaction.response.send_message("Not your game!", ephemeral=True); return
            if self.game_over: return
            if col == self.bombs[self.row]:
                self.game_over = True
                bal = get_user_balance(self.user_id); new_bal = bal - self.bet
                set_user_balance(self.user_id, new_bal); add_to_stats(self.user_id, False, self.bet)
                for item in self.children: item.disabled = True
                self.stop()
                status = f"💥 Hit a bomb on row {self.row+1}! Lost **{self.bet:,}** pts  |  New Balance: **R${new_bal:,}**"
                embed = make_tower_embed(self.bet, self.diff, self.row, self.client_seed, self.public_hash,
                                         server_seed=self.server_seed, status=status, color=C.ERROR)
                await interaction.response.edit_message(embed=embed, view=self)
                asyncio.create_task(send_to_history(interaction.guild, 'tower', self.user_name, self.user_id, self.bet, False, self.bet, new_bal))
            else:
                self.row += 1
                if self.row >= TOWER_ROWS:
                    self.game_over = True
                    mult, winnings, profit, new_bal = self._settle_win(self.row)
                    for item in self.children: item.disabled = True
                    self.stop()
                    if interaction.guild: asyncio.create_task(assign_rank_role(interaction.guild, self.user_id))
                    status = f"🏆 Reached the top! Won **{winnings:,}** pts ({mult:.2f}×)  |  New Balance: **R${new_bal:,}**"
                    embed = make_tower_embed(self.bet, self.diff, self.row, self.client_seed, self.public_hash,
                                             server_seed=self.server_seed, status=status, color=C.SUCCESS)
                    await interaction.response.edit_message(embed=embed, view=self)
                    asyncio.create_task(send_to_history(interaction.guild, 'tower', self.user_name, self.user_id, self.bet, True, profit, new_bal))
                else:
                    self._build_row()
                    await interaction.response.edit_message(
                        embed=make_tower_embed(self.bet, self.diff, self.row, self.client_seed, self.public_hash), view=self)
        return callback

    async def cashout_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("Not your game!", ephemeral=True); return
        if self.game_over: return
        if self.row == 0:
            await interaction.response.send_message("Clear at least one row first!", ephemeral=True); return
        self.game_over = True
        mult, winnings, profit, new_bal = self._settle_win(self.row)
        for item in self.children: item.disabled = True
        self.stop()
        if interaction.guild: asyncio.create_task(assign_rank_role(interaction.guild, self.user_id))
        status = f"✅ Cashed out **{winnings:,}** pts ({mult:.2f}×)  |  New Balance: **R${new_bal:,}**"
        embed = make_tower_embed(self.bet, self.diff, self.row, self.client_seed, self.public_hash,
                                 server_seed=self.server_seed, status=status, color=C.SUCCESS)
        await interaction.response.edit_message(embed=embed, view=self)
        asyncio.create_task(send_to_history(interaction.guild, 'tower', self.user_name, self.user_id, self.bet, True, profit, new_bal))


class TowerStartView(discord.ui.View):
    def __init__(self, user_id, user_name, bet):
        super().__init__(timeout=60)
        self.user_id = user_id; self.user_name = user_name; self.bet = bet
        for diff in ('easy', 'medium', 'hard'):
            tiles, safe = TOWER_DIFFS[diff]
            btn = discord.ui.Button(label=f"{diff.title()} ({safe}/{tiles})", style=discord.ButtonStyle.primary, custom_id=f"diff_{diff}")
            btn.callback = self.make_callback(diff); self.add_item(btn)

    def make_callback(self, diff):
        async def callback(interaction: discord.Interaction):
            if interaction.user.id != self.user_id:
                await interaction.response.send_message("Not your game!", ephemeral=True); return
            bal = get_user_balance(self.user_id)
            if self.bet > bal:
                await interaction.response.send_message(f"❌ Insufficient balance! You have {fmt(bal)}", ephemeral=True); return
            server_seed, client_seed, public_hash = generate_seeds()
            bombs = pf_tower_bombs(server_seed, client_seed, diff)
            view = TowerView(self.user_id, self.user_name, self.bet, diff, bombs, server_seed, client_seed, public_hash)
            self.stop()
            await interaction.response.edit_message(
                embed=make_tower_embed(self.bet, diff, 0, client_seed, public_hash), view=view)
        return callback


@bot.command(name='tower')
async def tower(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    view = TowerStartView(ctx.author.id, ctx.author.name, amount)
    e = embed("🗼 Tower Climb", (
        f"Bet: **{fmt(amount)}**\n\nChoose a difficulty to start climbing. Pick a safe tile each row to "
        "grow your multiplier — but one tile per row is a bomb. Cash out any time!\n\n"
        "🟢 **Easy** — 3/4 safe\n🟡 **Medium** — 2/3 safe\n🔴 **Hard** — 1/2 safe"), C.PRIMARY)
    await ctx.send(embed=e, view=view)


TTT_WIN_LINES = [(0, 1, 2), (3, 4, 5), (6, 7, 8), (0, 3, 6), (1, 4, 7), (2, 5, 8), (0, 4, 8), (2, 4, 6)]


def make_ttt_embed(p1, p2, turn_mark, status=None):
    if status:
        desc = status
    else:
        cur = p1 if turn_mark == 'X' else p2
        desc = f"It's {cur.mention}'s turn ({turn_mark})"
    e = embed("#️⃣ Tic Tac Toe", desc, C.LOBBY)
    e.add_field(name="❌ Player X", value=p1.mention, inline=True)
    e.add_field(name="⭕ Player O", value=p2.mention, inline=True)
    return e


class TicTacToeView(discord.ui.View):
    def __init__(self, p1, p2):
        super().__init__(timeout=180)
        self.players = {'X': p1, 'O': p2}
        self.turn = 'X'; self.board = [None] * 9; self.over = False
        for i in range(9):
            btn = discord.ui.Button(label="\u200b", style=discord.ButtonStyle.secondary, row=i // 3, custom_id=f"ttt_{i}")
            btn.callback = self.make_callback(i); self.add_item(btn)

    def _winner(self):
        for a, b, c in TTT_WIN_LINES:
            if self.board[a] and self.board[a] == self.board[b] == self.board[c]:
                return self.board[a]
        return None

    def make_callback(self, idx):
        async def callback(interaction: discord.Interaction):
            cur = self.players[self.turn]
            if interaction.user.id != cur.id:
                await interaction.response.send_message("Not your turn!", ephemeral=True); return
            if self.over or self.board[idx] is not None:
                await interaction.response.send_message("Invalid move!", ephemeral=True); return
            self.board[idx] = self.turn
            for item in self.children:
                if getattr(item, 'custom_id', None) == f"ttt_{idx}":
                    item.label = "❌" if self.turn == 'X' else "⭕"
                    item.style = discord.ButtonStyle.danger if self.turn == 'X' else discord.ButtonStyle.primary
                    item.disabled = True
            win_mark = self._winner()
            p1, p2 = self.players['X'], self.players['O']
            if win_mark:
                self.over = True
                for item in self.children: item.disabled = True
                self.stop()
                winner = self.players[win_mark]
                embed = make_ttt_embed(p1, p2, self.turn, status=f"🎉 {winner.mention} wins! ({win_mark})")
            elif all(b is not None for b in self.board):
                self.over = True; self.stop()
                embed = make_ttt_embed(p1, p2, self.turn, status="🤝 It's a draw!")
            else:
                self.turn = 'O' if self.turn == 'X' else 'X'
                embed = make_ttt_embed(p1, p2, self.turn)
            await interaction.response.edit_message(embed=embed, view=self)
        return callback


@bot.command(name='ttt')
async def ttt(ctx, opponent: discord.Member = None):
    if opponent is None or opponent.bot or opponent.id == ctx.author.id:
        await ctx.send("❌ Usage: `.ttt @user` — mention another player to challenge."); return
    view = TicTacToeView(ctx.author, opponent)
    embed = make_ttt_embed(ctx.author, opponent, 'X')
    await ctx.send(content=f"{ctx.author.mention} (❌) vs {opponent.mention} (⭕)", embed=embed, view=view)


@bot.command(name='slots')
async def slots(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    SPIN = "🌀"; GEM = "💎"
    final = pf_slots_spin(server_seed, client_seed)
    def disp(r1,r2,r3): return f"┌─────────────┐\n│  {r1}  {r2}  {r3}  │\n└─────────────┘"
    e = embed("🎰 Slot Machine", C.ACCENT)
    e.description = f"```\n{disp(SPIN,SPIN,SPIN)}\n```\nSpinning..."
    msg = await ctx.send(embed=e)
    for step in range(1, 4):
        await asyncio.sleep(0.6); rv = [final[i] for i in range(step)]; pv = [SPIN]*(3-step)
        e.description = f"```\n{disp(*(rv+pv))}\n```"; await msg.edit(embed=e)
    await asyncio.sleep(0.4)
    r1,r2,r3 = final
    if r1==r2==r3: winnings=amount*(100 if r1==GEM else 10); won=True; label="💎 JACKPOT ×100" if r1==GEM else "✨ Triple ×10"
    elif r1==r2 or r2==r3: winnings=amount*2; won=True; label="Double ×2"
    else: winnings=0; won=False; label="No match"
    new_bal = bal + winnings if won else bal - amount
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    e = embed(f"🎉 Slots — {label}" if won else "❌ Slots — No Match",
              color=C.SUCCESS if won else C.ERROR)
    e.description = f"```\n{disp(r1,r2,r3)}\n```"
    e.add_field(name="Won" if won else "Lost", value=fmt(winnings if won else amount), inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=True)
    pf_add_field(e, server_seed, client_seed, public_hash, "slots")
    img_buf = slots_card(final, amount, winnings if won else 0, username=ctx.author.name)
    e.set_image(url="attachment://slots.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'slots.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'slots', ctx.author.name, ctx.author.id, amount, won, winnings if won else amount, new_bal))


@bot.command(name='roulette')
async def roulette(ctx, amount: str, choice: str):
    bal = get_user_balance(ctx.author.id); choice = choice.lower()
    if choice not in ['red','black','even','odd']: await ctx.send("❌ Choose: `red` `black` `even` `odd`"); return
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    server_seed, client_seed, public_hash = generate_seeds()
    frames = ["🔴 🔵 🟢 🔴 ⚪","⚪ 🔴 🔵 🟢 🔴","🔴 ⚪ 🔴 🔵 🟢","🟢 🔴 ⚪ 🔴 🔵"]
    e = embed("🎡 Roulette", f"Spinning...\n{frames[0]}", C.ACCENT)
    msg = await ctx.send(embed=e)
    for frame in frames[1:]:
        await asyncio.sleep(0.45); e.description = f"Spinning...\n{frame}"; await msg.edit(embed=e)
    await asyncio.sleep(0.4)
    spin = pf_roulette_spin(server_seed, client_seed)
    if spin == 0: rc = "green"; parity = "—"; won = False
    else: rc = "red" if spin%2==1 else "black"; parity = "even" if spin%2==0 else "odd"; won = choice==rc or choice==parity
    new_bal = bal + amount if won else bal - amount
    add_to_stats(ctx.author.id, won, amount); set_user_balance(ctx.author.id, new_bal)
    if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
    ci = "🔴" if rc=="red" else ("⚫" if rc=="black" else "🟢")
    e = embed("🎡 🎉 Roulette — WIN! (×2)" if won else "❌ Roulette — Lost",
              color=C.SUCCESS if won else C.ERROR)
    e.add_field(name="Landed", value=f"{ci} {spin} ({rc}/{parity})", inline=True)
    e.add_field(name="You bet", value=choice.upper(), inline=True)
    e.add_field(name="Change",  value=f"{'+'if won else '-'}R${amount:,}", inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "roulette")
    img_buf = roulette_card(spin, rc, amount, amount if won else 0, pick=choice)
    e.set_image(url="attachment://roulette.png")
    await msg.edit(embed=e, attachments=[send_image(img_buf, 'roulette.png')])
    asyncio.create_task(send_to_history(ctx.guild, 'roulette', ctx.author.name, ctx.author.id, amount, won, amount, new_bal))


@bot.command(name='blackjack', aliases=['bj'])
async def blackjack_cmd(ctx, amount: str):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    if ctx.author.id in active_bj: await ctx.send("❌ You already have an active blackjack game!"); return
    server_seed, client_seed, public_hash = generate_seeds()
    deck = pf_blackjack_deck(server_seed, client_seed)
    pc = [deck.pop(), deck.pop()]; dc = [deck.pop(), deck.pop()]; pv = cv(pc)

    # Natural blackjack — instant win, animated reveal
    if pv == 21:
        winnings = round(amount * 2.5); new_bal = bal + winnings - amount
        add_to_stats(ctx.author.id, True, amount); set_user_balance(ctx.author.id, new_bal)
        if ctx.guild: asyncio.create_task(assign_rank_role(ctx.guild, ctx.author.id))
        # Step 1: show with hole hidden
        embed1, file1 = bj_card_payload(ctx.author.name, pc, dc, amount,
                                        hide_hole=True, status='playing',
                                        color=C.PRIMARY, title="Blackjack — Dealing…")
        msg = await ctx.send(embed=embed1, file=file1)
        await asyncio.sleep(0.9)
        # Step 2: reveal + BLACKJACK banner
        embed2, file2 = bj_card_payload(ctx.author.name, pc, dc, amount,
                                        hide_hole=False, status='blackjack',
                                        color=C.SUCCESS,
                                        title="Blackjack — BLACKJACK! (×2.5)",
                                        extra=f"+R${winnings:,}  |  New Balance: {fmt(new_bal)}")
        pf_add_field(embed2, server_seed, client_seed, public_hash, "blackjack")
        await msg.edit(embed=embed2, attachments=[file2])
        asyncio.create_task(send_to_history(ctx.guild, 'blackjack', ctx.author.name, ctx.author.id, amount, True, winnings, new_bal))
        return

    active_bj[ctx.author.id] = True
    view = BlackjackView(ctx.author.id, ctx.author.name, amount, bal, pc, dc, deck)
    embed, file = bj_card_payload(ctx.author.name, pc, dc, amount,
                                  hide_hole=True, status='playing',
                                  color=C.PRIMARY, title="Blackjack",
                                  footer=f"👊 Hit  |  🛑 Stand  |  ⬆️ Double Down  |  🔐 Seed: {client_seed[:8]}… Hash: {public_hash[:12]}…")
    await ctx.send(embed=embed, file=file, view=view)


@bot.command(name='mines')
async def mines_cmd(ctx, amount: str, mine_count: int = 3):
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Bet must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return
    if mine_count < 1 or mine_count > 15: await ctx.send("❌ Mine count must be 1–15!"); return
    if ctx.author.id in active_mines: await ctx.send("❌ You already have an active mines game!"); return
    server_seed, client_seed, public_hash = generate_seeds()
    mine_positions = pf_mine_positions(server_seed, client_seed, mine_count)
    active_mines[ctx.author.id] = True
    view = MinesView(ctx.author.id, ctx.author.name, amount, mine_count, mine_positions, server_seed, client_seed, public_hash)
    embed = make_mines_embed(amount, mine_count, 0, client_seed, public_hash)
    await ctx.send(embed=embed, view=view)

@bot.command(name='verify')
async def verify(ctx, game: str = None, server_seed: str = None, client_seed: str = None, extra: str = None):
    if not game or not server_seed or not client_seed:
        e = embed("🔐 Provably Fair — Verify", color=C.SECONDARY, description=(
            "Verify any game result using its seeds.\n\n"
            "**Usage:**\n"
            "`.verify coinflip <server_seed> <client_seed>`\n"
            "`.verify dice <server_seed> <client_seed>`\n"
            "`.verify slots <server_seed> <client_seed>`\n"
            "`.verify roulette <server_seed> <client_seed>`\n"
            "`.verify limbo <server_seed> <client_seed>`\n"
            "`.verify slide <server_seed> <client_seed>`\n"
            "`.verify tight <server_seed> <client_seed>`\n"
            "`.verify twist <server_seed> <client_seed>`\n"
            "`.verify rps <server_seed> <client_seed>`\n"
            "`.verify war <server_seed> <client_seed>`\n"
            "`.verify valentines <server_seed> <client_seed>`\n"
            "`.verify mines <server_seed> <client_seed> <mine_count>`\n\n"
            "The **Server Seed** and **Client Seed** are shown at the bottom of every game result."
        ))
        await ctx.send(embed=e); return

    game = game.lower()
    computed_hash = hashlib.sha256(server_seed.encode()).hexdigest()

    e = embed(f"🔐 Verify — {game.title()}", color=C.SECONDARY)
    e.add_field(name="Server Seed",   value=f"`{server_seed}`",    inline=False)
    e.add_field(name="Client Seed",   value=f"`{client_seed}`",    inline=False)
    e.add_field(name="Hash (SHA-256)", value=f"`{computed_hash}`", inline=False)

    if game == "coinflip":
        result = pf_coinflip(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"**{result.upper()}**", inline=False)
    elif game == "dice":
        result = pf_dice_roll(server_seed, client_seed)
        faces = ["⚀","⚁","⚂","⚃","⚄","⚅"]
        embed.add_field(name="✅ Result", value=f"**{result}** {faces[result-1]}", inline=False)
    elif game == "slots":
        result = pf_slots_spin(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"**{result[0]}  {result[1]}  {result[2]}**", inline=False)
    elif game == "roulette":
        spin = pf_roulette_spin(server_seed, client_seed)
        if spin == 0: rc = "green"; parity = "—"
        else: rc = "red" if spin%2==1 else "black"; parity = "even" if spin%2==0 else "odd"
        ci = "🔴" if rc=="red" else ("⚫" if rc=="black" else "🟢")
        embed.add_field(name="✅ Result", value=f"{ci} **{spin}** ({rc} / {parity})", inline=False)
    elif game == "limbo":
        result = pf_limbo(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"**{result:.2f}×** (win if ≥ your target)", inline=False)
    elif game == "slide":
        result = pf_slide(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"**{result:.2f}×** (win if ≥ your target)", inline=False)
    elif game == "tight":
        result = pf_tight(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"**{result:.2f}×** payout multiplier", inline=False)
    elif game == "twist":
        rolls, mult = pf_twist(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"Rolls **{rolls}** = {sum(rolls)} → **{mult:.2f}×**", inline=False)
    elif game == "rps":
        result = pf_rps(server_seed, client_seed)
        embed.add_field(name="✅ Result (bot move)", value=f"**{result.upper()}**", inline=False)
    elif game == "war":
        p, dlr = pf_war_cards(server_seed, client_seed)
        names = {11: 'J', 12: 'Q', 13: 'K', 14: 'A'}
        embed.add_field(name="✅ Result", value=f"You **{names.get(p, p)}** vs Dealer **{names.get(dlr, dlr)}**", inline=False)
    elif game == "valentines":
        result = pf_valentines(server_seed, client_seed)
        embed.add_field(name="✅ Result", value=f"**{result[0]}  {result[1]}  {result[2]}**", inline=False)
    elif game in ("mines", "mine"):
        mine_count = int(extra) if extra and extra.isdigit() else 3
        positions = pf_mine_positions(server_seed, client_seed, mine_count)
        embed.add_field(name="✅ Mine Positions (0-indexed)", value=f"`{sorted(positions)}`", inline=False)
    elif game in ("jackpot", "jp"):
        fail_val = pf_derive(server_seed, client_seed, nonce=0)
        draw_val = pf_derive(server_seed, client_seed, nonce=1)
        failed   = fail_val < JACKPOT_FAIL_ODDS
        embed.add_field(name="Fail roll (nonce 0)",  value=f"`{fail_val:.6f}` — threshold `{JACKPOT_FAIL_ODDS}` → {'**FAILED**' if failed else 'Passed ✅'}", inline=False)
        embed.add_field(name="Draw roll (nonce 1)",  value=f"`{draw_val:.6f}` — used for weighted winner selection", inline=False)
        embed.add_field(name="✅ Outcome", value="**POT FAILED** (no winner)" if failed else f"Winner determined by draw roll `{draw_val:.6f}` against entry weights", inline=False)
    else:
        embed.add_field(name="❌ Unknown game", value=f"Supported: `coinflip`, `dice`, `slots`, `roulette`, `limbo`, `slide`, `tight`, `twist`, `rps`, `war`, `valentines`, `mines`, `jackpot`", inline=False)

    e.set_footer(text="Hash = SHA-256(server_seed) — you can verify this yourself at any SHA-256 tool.")
    await ctx.send(embed=e)


# ── Rewards ───────────────────────────────────────────────────────────────────

@bot.command(name='code', aliases=['redeem'])
async def code_cmd(ctx, code_input: str = None):
    if not code_input:
        await ctx.send("❌ Usage: `.code <CODE>`"); return

    code_input = code_input.upper().strip()
    codes = get_codes()
    now   = datetime.now(timezone.utc)

    if code_input not in codes:
        await ctx.send("❌ Invalid code! Double-check it and try again."); return

    c = codes[code_input]

    # Expiry check
    expires = datetime.fromisoformat(c['expires_at'])
    if expires.tzinfo is None: expires = expires.replace(tzinfo=timezone.utc)
    if now > expires:
        await ctx.send(f"❌ Code **{code_input}** has expired."); return

    # Already used
    if ctx.author.id in c['used_by']:
        await ctx.send(f"❌ You've already redeemed **{code_input}**."); return

    # Uses left
    uses_used = len(c['used_by'])
    if uses_used >= c['max_uses']:
        await ctx.send(f"❌ Code **{code_input}** has run out of uses."); return

    # Requirement check
    req_deposited = c.get('require_deposited', 0)
    req_wagered = c.get('require_wagered', 0)
    data, uid = get_user(ctx.author.id)
    user_deposited = data[uid].get('total_deposited', 0.0)
    user_wagered = data[uid]['stats'].get('total_wagered', 0)

    if req_deposited > 0 or req_wagered > 0:
        meets_deposited = req_deposited > 0 and user_deposited >= req_deposited
        meets_wagered = req_wagered > 0 and user_wagered >= req_wagered
        if not (meets_deposited or meets_wagered):
            req_parts = []
            if req_deposited > 0: req_parts.append(f"${req_deposited} deposited (you: ${user_deposited:.2f})")
            if req_wagered > 0: req_parts.append(f"R${req_wagered:,} wagered (you: R${user_wagered:,})")
            await ctx.send(
                f"❌ **Requirement not met!**\n"
                f"This code requires: {' OR '.join(req_parts)}"
            ); return

    # Redeem
    c['used_by'].append(ctx.author.id)
    save_codes(codes)

    reward  = c['reward']
    new_bal = get_user_balance(ctx.author.id) + reward
    set_user_balance(ctx.author.id, new_bal)

    uses_left = c['max_uses'] - len(c['used_by'])
    time_left = expires - now
    hours     = int(time_left.total_seconds() // 3600)
    minutes   = int((time_left.total_seconds() % 3600) // 60)

    e = embed("🎁 Code Redeemed!", color=C.SUCCESS,
              footer=f"Redeemed by {ctx.author.name}")
    e.add_field(name="Code",      value=f"`{code_input}`",          inline=True)
    e.add_field(name="Reward",    value=f"+R${reward:,}",           inline=True)
    e.add_field(name="New Balance", value=fmt(new_bal),             inline=True)
    e.add_field(name="Uses Left", value=f"{uses_left}/{c['max_uses']}", inline=True)
    e.add_field(name="Expires",   value=f"in {hours}h {minutes}m", inline=True)
    await ctx.send(embed=e)


@bot.command(name='addcode')
@commands.has_permissions(administrator=True)
async def addcode(ctx, code: str = None, reward: int = None, uses: int = None, days: int = None, requirement: str = None):
    if not all([code, reward, uses, days]):
        await ctx.send(
            "❌ Usage: `.addcode <CODE> <reward> <uses> <days> [requirement]`\n"
            "Requirements: `deposited:<amt>` or `wagered:<amt>`\n"
            "Example: `.addcode BONUS100 100 10 7 deposited:1`"
        ); return

    code = code.upper().strip()
    codes = get_codes()

    req_deposited = 0
    req_wagered = 0
    if requirement:
        req = requirement.lower().strip()
        if req.startswith('deposited:'):
            try: req_deposited = float(req.split(':')[1])
            except: req_deposited = 0
        elif req.startswith('wagered:'):
            try: req_wagered = int(req.split(':')[1])
            except: req_wagered = 0

    expires = (datetime.now(timezone.utc) + timedelta(days=days)).isoformat()
    codes[code] = {
        'reward': reward,
        'max_uses': uses,
        'expires_at': expires,
        'used_by': [],
        'require_deposited': req_deposited,
        'require_wagered': req_wagered
    }
    save_codes(codes)

    e = embed("✅ Code Created", color=C.SUCCESS)
    e.add_field(name="Code", value=f"`{code}`", inline=True)
    e.add_field(name="Reward", value=f"R${reward:,}", inline=True)
    e.add_field(name="Uses", value=str(uses), inline=True)
    e.add_field(name="Expires", value=f"in {days} day(s)", inline=True)

    req_parts = []
    if req_deposited > 0: req_parts.append(f"${req_deposited} deposited")
    if req_wagered > 0: req_parts.append(f"R${req_wagered:,} wagered")
    if req_parts:
        e.add_field(name="Requirement", value=" or ".join(req_parts), inline=False)

    await ctx.send(embed=e)


@addcode.error
async def addcode_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")
    else: await ctx.send(
        "❌ Usage: `.addcode <CODE> <reward> <uses> <days> [requirement]`\n"
        "Requirements: `deposited:<amt>` or `wagered:<amt>`"
    )


@bot.command(name='delcode')
@commands.has_permissions(administrator=True)
async def delcode(ctx, code: str = None):
    if not code:
        await ctx.send("❌ Usage: `.delcode <CODE>`"); return
    code = code.upper().strip()
    codes = get_codes()
    if code not in codes:
        await ctx.send(f"❌ Code `{code}` not found."); return
    del codes[code]
    save_codes(codes)
    await ctx.send(f"🗑️ Code `{code}` deleted.")

@delcode.error
async def delcode_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")


@bot.command(name='codes')
@commands.has_permissions(administrator=True)
async def codes_cmd(ctx):
    codes = get_codes()
    now   = datetime.now(timezone.utc)
    if not codes:
        await ctx.send("📋 No codes exist yet. Use `.addcode` to create one."); return
    e = embed("📋 Active Promo Codes", color=C.LOBBY)
    shown = 0
    for name, c in codes.items():
        if not isinstance(c, dict):
            continue
        try:
            reward    = int(c.get('reward', 0) or 0)
            max_uses  = int(c.get('max_uses', 0) or 0)
            used_by   = c.get('used_by', []) or []
            exp_raw   = c.get('expires_at')
            if not exp_raw:
                continue
            expires = datetime.fromisoformat(exp_raw)
            if expires.tzinfo is None: expires = expires.replace(tzinfo=timezone.utc)
            expired   = now > expires
            uses_left = max_uses - len(used_by)
            status    = "❌ Expired" if expired else ("⚠️ Used up" if uses_left <= 0 else f"✅ {uses_left}/{max_uses} uses left")
            td        = expires - now if not expired else timedelta(0)
            h         = int(td.total_seconds() // 3600)
            m         = int((td.total_seconds() % 3600) // 60)
            exp_str   = "Expired" if expired else f"Expires in {h}h {m}m"
            e.add_field(
                name=f"`{name}`",
                value=f"R${reward:,} reward  ·  {status}\n{exp_str}",
                inline=False
            )
            shown += 1
        except Exception:
            continue
    if shown == 0:
        await ctx.send("📋 No valid codes found. Use `.addcode` to create one."); return
    await ctx.send(embed=e)

@codes_cmd.error
async def codes_cmd_error(ctx, error):
    if isinstance(error, commands.MissingPermissions): await ctx.send("🚫 Administrator permission required!")


@bot.command(name='daily')
async def daily(ctx):
    data, uid = get_user(ctx.author.id); now = datetime.now(timezone.utc)
    today = now.date().isoformat()
    
    # Check cooldown first
    last = data[uid].get('last_daily')
    if last:
        last_dt = datetime.fromisoformat(last)
        if last_dt.tzinfo is None: last_dt = last_dt.replace(tzinfo=timezone.utc)
        diff = now - last_dt
        if diff.total_seconds() < 86400:
            rem = timedelta(seconds=86400) - diff
            h = int(rem.total_seconds()//3600); m = int((rem.total_seconds()%3600)//60)
            e = embed("🎁 Daily Reward", f"⏳ Come back in **{h}h {m}m**!", C.ERROR)
            await ctx.send(embed=e); return
        
    DAILY = 5
    data[uid]['last_daily']     = now.isoformat()
    data[uid]['balance']        = data[uid].get('balance', 0) + DAILY
    data[uid]['bonus_received'] = data[uid].get('bonus_received', 0) + DAILY
    save_data(data)
    e = embed("🎁 Daily Reward Claimed!",
              f"Received **R${DAILY}**!\n"
              f"**New Balance:** {fmt(data[uid]['balance'])}",
              C.SUCCESS, footer="Come back in 24 hours!")
    await ctx.send(embed=e)


@bot.command(name='invites')
async def invites_cmd(ctx, member: discord.Member = None):
    target = member or ctx.author
    data, uid = get_user(target.id)
    today = datetime.now(timezone.utc).date().isoformat()
    if data[uid].get('daily_invites_date') != today:
        daily_invs = 0
    else:
        daily_invs = data[uid].get('daily_invites', 0)
    total_invs = data[uid].get('total_invites', 0)
    e = embed(f"📨 {target.name}'s Invites", None, C.SECONDARY,
              footer="Invite 2 people per day to unlock your .daily reward.")
    e.add_field(name="Today's Invites", value=f"**{daily_invs} / 2**", inline=True)
    e.add_field(name="Total Invites",   value=f"**{total_invs}**",     inline=True)
    status = "✅ Can claim daily!" if daily_invs >= 2 else f"❌ Need {2 - daily_invs} more invite(s) today"
    e.add_field(name="Daily Status", value=status, inline=False)
    await ctx.send(embed=e)


class MonthlyClaimView(discord.ui.View):
    def __init__(self, author_id):
        super().__init__(timeout=120)
        self.author_id = author_id

    @discord.ui.button(label='Claim Monthly', style=discord.ButtonStyle.success, custom_id='claim_monthly', emoji='🎁')
    async def claim(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message("This isn't your monthly bonus!", ephemeral=True); return
        data, uid = get_user(self.author_id); now = datetime.now(timezone.utc)
        current_month = now.strftime('%Y-%m')
        if data[uid].get('last_monthly') == current_month:
            next_m = (now.replace(day=1) + timedelta(days=32)).replace(day=1)
            days = (next_m - now).days
            e = embed("📅 Monthly Reward", f"⏳ Already claimed this month!\nCome back in **{days} days**.", C.ERROR)
            await interaction.response.edit_message(embed=e, view=None); return
        wager_since = data[uid]['stats'].get('total_wagered', 0) - data[uid].get('wager_at_last_monthly', 0)
        reward = round(wager_since * 0.0025)
        if reward < 1:
            e = embed("📅 Monthly Reward",
                      f"You need to wager more since your last claim to earn a bonus.\n"
                      f"📊 **Wagered since last claim:** {wager_since:,.2f} points",
                      C.WARNING)
            await interaction.response.edit_message(embed=e, view=None); return
        data[uid]['last_monthly']          = current_month
        data[uid]['wager_at_last_monthly'] = data[uid]['stats']['total_wagered']
        data[uid]['balance']               = data[uid].get('balance', 0) + reward
        data[uid]['bonus_received']        = data[uid].get('bonus_received', 0) + reward
        save_data(data)
        e = embed("📅 Monthly Reward Claimed!",
                  f"🎁 **Claimed:** {reward:,} points\n"
                  f"📊 **Wagered since last claim:** {wager_since:,.2f} points\n"
                  f"💰 **New Balance:** {fmt(data[uid]['balance'])}",
                  C.SUCCESS)
        await interaction.response.edit_message(embed=e, view=None)


@bot.command(name='monthly')
async def monthly(ctx):
    data, uid = get_user(ctx.author.id); now = datetime.now(timezone.utc)
    current_month = now.strftime('%Y-%m')
    wager_since = data[uid]['stats'].get('total_wagered', 0) - data[uid].get('wager_at_last_monthly', 0)
    estimated = round(wager_since * 0.0025)

    if data[uid].get('last_monthly') == current_month:
        next_m = (now.replace(day=1) + timedelta(days=32)).replace(day=1)
        days = (next_m - now).days
        e = embed("📅 Monthly Reward",
                  f"⏳ Already claimed this month!\nCome back in **{days} days**.",
                  C.ERROR)
        await ctx.send(embed=e); return

    is_first = now.day == 1
    desc = (
        f"Your monthly bonus is **0.25% rakeback** on wagers since your last claim!\n"
        f"📊 **Wagered since last claim:** {wager_since:,.2f} points\n"
        f"🎁 **Estimated Monthly Bonus:** **{estimated:,} points**\n"
        f"*This bonus can be claimed once every 30 days.*"
    )
    if not is_first:
        next_first = (now.replace(day=1) + timedelta(days=32)).replace(day=1)
        days = (next_first - now).days
        desc += f"\n\n⏳ **Claimable on the 1st of next month** — {days} days left."
        e = embed("📅 Monthly Reward", desc, C.WARNING)
        await ctx.send(embed=e); return

    e = embed("📅 Monthly Reward", desc, C.SUCCESS)
    await ctx.send(embed=e, view=MonthlyClaimView(ctx.author.id))


@bot.command(name='rakeback')
async def rakeback(ctx):
    data, uid = get_user(ctx.author.id); available = data[uid].get('rakeback_available', 0.0); amount = int(available)
    if amount < 1:
        e = embed("💸 Rakeback", (
            f"**Available:** {available:.4f} pts *(need ≥1 to claim)*\n"
            f"**Rate:** 0.2% of all losses\n**Total Lost:** R${data[uid]['stats'].get('total_lost',0):,}"),
            C.WARNING)
        await ctx.send(embed=e); return
    data[uid]['rakeback_available'] = available - amount
    data[uid]['balance']            = data[uid].get('balance', 0) + amount
    data[uid]['bonus_received']     = data[uid].get('bonus_received', 0) + amount
    save_data(data)
    e = embed("💸 Rakeback Claimed!", (
        f"**Claimed:** {amount:,} pts\n**Remaining:** {(available-amount):.4f}\n"
        f"**New Balance:** {fmt(data[uid]['balance'])}"), C.SUCCESS,
        footer="Rakeback = 0.2% of all losses, accumulated automatically.")
    await ctx.send(embed=e)

# ── Social ────────────────────────────────────────────────────────────────────

@bot.command(name='send')
async def send_points(ctx, member: discord.Member, amount: int):
    if member.id == ctx.author.id: await ctx.send("❌ You can't send points to yourself!"); return
    if amount <= 0: await ctx.send("❌ Amount must be positive!"); return
    sender_bal = get_user_balance(ctx.author.id)
    if amount > sender_bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(sender_bal)}"); return
    set_user_balance(ctx.author.id, sender_bal - amount)
    recv_bal = get_user_balance(member.id); set_user_balance(member.id, recv_bal + amount)
    sd, suid = get_user(ctx.author.id); sd[suid]['tips_sent'] = sd[suid].get('tips_sent',0) + amount; save_data(sd)
    rd, ruid = get_user(member.id);     rd[ruid]['tips_received'] = rd[ruid].get('tips_received',0) + amount; save_data(rd)
    e = embed("🤝 Transfer Complete", (
        f"**{ctx.author.name}** → **{member.name}**\n**Amount:** R${amount:,}\n\n"
        f"**{ctx.author.name}'s balance:** {fmt(sender_bal-amount)}\n"
        f"**{member.name}'s balance:** {fmt(recv_bal+amount)}"), C.SUCCESS)
    await ctx.send(embed=e)

@send_points.error
async def send_error(ctx, error):
    if isinstance(error, commands.MemberNotFound): await ctx.send("❌ Member not found — mention them with @")
    else: await ctx.send("❌ Usage: `.send @user <amount>`")


RAIN_DURATION = 120  # seconds
RAIN_MIN_DEPOSIT_USD = 0.5  # lifetime deposit required to join rain
RAIN_WAGER_MULTIPLIER = 5   # claimed rain points need 5x wager before withdrawal

class RainView(discord.ui.View):
    def __init__(self, host_id, amount, require=False):
        super().__init__(timeout=RAIN_DURATION)
        self.host_id  = host_id  # may be None (hourly/house rain)
        self.amount   = amount
        self.joiners  = set()
        self.require  = require  # True only for hourly/house rains

    @discord.ui.button(label="🌧️ Join Rain", style=discord.ButtonStyle.primary, custom_id="rain_join")
    async def join(self, interaction: discord.Interaction, button: discord.ui.Button):
        uid = interaction.user.id
        if self.host_id is not None and uid == self.host_id:
            await interaction.response.send_message("❌ You started the rain — you can't join it!", ephemeral=True); return
        if uid in self.joiners:
            await interaction.response.send_message("✅ You're already in the rain!", ephemeral=True); return

        if self.require:
            data, ukey = get_user(uid)
            deposited = float(data[ukey].get('total_deposited', 0.0) or 0.0)
            if deposited < RAIN_MIN_DEPOSIT_USD:
                need_pts = usd_to_points(RAIN_MIN_DEPOSIT_USD)
                await interaction.response.send_message(
                    f"❌ **Requirement not met!**\n\n"
                    f"**Requirements to join:**\n"
                    f"💸 Have a lifetime deposit of at least **${RAIN_MIN_DEPOSIT_USD}$** (~{need_pts} points)!\n\n"
                    f"Your lifetime deposit: **${deposited:.2f}**\n\n"
                    f"*(Note: Points claimed from rain have a {RAIN_WAGER_MULTIPLIER}x wager requirement before withdrawal).*",
                    ephemeral=True); return

        self.joiners.add(uid)
        count = len(self.joiners)
        share = self.amount // count if count else self.amount
        extra = f"\n*(Note: claimed points carry a {RAIN_WAGER_MULTIPLIER}x wager requirement.)*" if self.require else ""
        await interaction.response.send_message(
            f"🌧️ You joined the rain! **{count}** player{'s' if count != 1 else ''} in so far — "
            f"current share: **R${share:,}** each.{extra}",
            ephemeral=True)

    async def on_timeout(self):
        pass


def _rain_req_text():
    return (
        f"\n**Requirements to join:**\n"
        f"💸 Have a lifetime deposit of at least **${RAIN_MIN_DEPOSIT_USD}$** "
        f"(~{usd_to_points(RAIN_MIN_DEPOSIT_USD)} points)!\n\n"
        f"*(Note: Points claimed from rain have a {RAIN_WAGER_MULTIPLIER}x wager requirement before withdrawal).*"
    )


async def _run_rain(channel, amount, host_id, host_label):
    """Run a rain round in `channel`. host_id=None for house/hourly rains."""
    require = host_id is None  # hourly/house rains enforce requirements
    view = RainView(host_id, amount, require=require)
    req_text = _rain_req_text() if require else ""
    e = embed(
        "It's Raining Points!",
        (
            f"**{host_label}** is raining **R${amount:,}**!\n\n"
            f"Click **Join Rain** to get your share.\n"
            f"The pot splits equally among everyone who joins.\n\n"
            f"⏳ Rain ends in **{RAIN_DURATION // 60} minutes**."
            f"{req_text}"
        ),
        C.SECONDARY,
        footer=f"Pot: R${amount:,}  |  Splits equally among all joiners",
    )
    msg = await channel.send(embed=e, view=view)

    await asyncio.sleep(RAIN_DURATION - 60)
    if not view.is_finished():
        count = len(view.joiners)
        share = amount // count if count else amount
        e.description = (
            f"**{host_label}** is raining **R${amount:,}**!\n\n"
            f"Click **Join Rain** to get your share.\n\n"
            f"⏳ **1 minute left!**  "
            f"{'**' + str(count) + ' joined** — share: R$' + f'{share:,}' if count else 'No one joined yet!'}"
            f"{req_text}"
        )
        try: await msg.edit(embed=e, view=view)
        except: pass

    for item in view.children: item.disabled = True

    joiners = list(view.joiners)
    if not joiners:
        if host_id is not None:
            set_user_balance(host_id, get_user_balance(host_id) + amount)
            refund_txt = f"**R${amount:,}** refunded to the host."
        else:
            refund_txt = "No payout was issued."
        e = embed(
            "Rain Ended — No Takers",
            f"Nobody joined the rain. {refund_txt}",
            C.WARNING,
        )
        try: await msg.edit(embed=e, view=view)
        except: pass
        return

    share = amount // len(joiners)
    remainder = amount - share * len(joiners)

    names = []
    for i, uid in enumerate(joiners):
        payout = share + (remainder if i == 0 else 0)
        prev = get_user_balance(uid)
        set_user_balance(uid, prev + payout)
        rd, ruid = get_user(uid)
        rd[ruid]['tips_received'] = rd[ruid].get('tips_received', 0) + payout
        if require:
            rd[ruid]['wager_requirement'] = rd[ruid].get('wager_requirement', 0) + payout * RAIN_WAGER_MULTIPLIER
        save_data(rd)
        try: user = await bot.fetch_user(uid); names.append(f"**{user.name}** +R${payout:,}")
        except: names.append(f"+R${payout:,}")

    if host_id is not None:
        sd, suid = get_user(host_id)
        sd[suid]['tips_sent'] = sd[suid].get('tips_sent', 0) + amount
        save_data(sd)

    wager_note = (f"\n\n*(Claimed points carry a **{RAIN_WAGER_MULTIPLIER}x wager requirement** before withdrawal.)*" if require else "")
    e = embed(
        "Rain Complete!",
        (
            f"**{host_label}** rained **R${amount:,}** on **{len(joiners)}** player{'s' if len(joiners)!=1 else ''}!\n\n"
            + "\n".join(names)
            + wager_note
        ),
        C.SUCCESS,
        footer=f"Each player received R${share:,}",
    )
    try: await msg.edit(embed=e, view=view)
    except: pass


@bot.command(name='rain')
async def rain(ctx, amount: str = None):
    if amount is None:
        await ctx.send("❌ Usage: `.rain <amount>`"); return
    bal = get_user_balance(ctx.author.id)
    amount = resolve_bet(amount, bal)
    if amount is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount <= 0: await ctx.send("❌ Amount must be positive!"); return
    if amount > bal: await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return

    set_user_balance(ctx.author.id, bal - amount)
    await _run_rain(ctx.channel, amount, ctx.author.id, ctx.author.name)


# ============ Hourly auto-rain ============

async def _hourly_rain_loop():
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            cfg = get_config()
            hourly = cfg.get('hourly_rains', {}) or {}
            for ch_id, amt in list(hourly.items()):
                try:
                    channel = bot.get_channel(int(ch_id)) or await bot.fetch_channel(int(ch_id))
                    if channel:
                        bot.loop.create_task(_run_rain(channel, int(amt), None, "🏠 House"))
                except Exception as e:
                    print(f"[hourly_rain] {ch_id}: {e}")
        except Exception as e:
            print(f"[hourly_rain] loop error: {e}")
        await asyncio.sleep(3600)


@bot.command(name='sethourlyrain')
@commands.has_permissions(administrator=True)
async def sethourlyrain(ctx, channel: discord.TextChannel = None, amount: str = None):
    if channel is None or amount is None:
        await ctx.send("❌ Usage: `.sethourlyrain #channel <amount>`  (use `0` to disable)"); return
    try: amt = int(amount.replace(',', '').replace('_', ''))
    except: await ctx.send("❌ Amount must be a whole number."); return
    if amt < 0: await ctx.send("❌ Amount can't be negative."); return

    cfg = get_config()
    hourly = cfg.get('hourly_rains', {}) or {}
    if amt == 0:
        hourly.pop(str(channel.id), None)
        cfg['hourly_rains'] = hourly; save_config(cfg)
        await ctx.send(embed=embed(
            "Hourly Rain Disabled",
            f"No more auto-rains in {channel.mention}.",
            color=C.WARNING)); return

    hourly[str(channel.id)] = amt
    cfg['hourly_rains'] = hourly; save_config(cfg)
    if not getattr(bot, '_hourly_rain_started', False):
        bot._hourly_rain_started = True
        bot.loop.create_task(_hourly_rain_loop())
    e = embed(
        "Hourly Rain Set",
        (
            f"Every hour, **R${amt:,}** will rain in {channel.mention}.\n\n"
            f"{_rain_req_text()}"
        ),
        color=C.SECONDARY)
    await ctx.send(embed=e)


@sethourlyrain.error
async def sethourlyrain_error(ctx, error):
    await ctx.send("❌ Usage: `.sethourlyrain #channel <amount>`  (use `0` to disable)")




@bot.command(name='giveaway', aliases=['gw'])
@commands.has_permissions(administrator=True)
async def giveaway(ctx, amount: str = None, minutes: str = None, *args):
    if not amount or not minutes:
        await ctx.send(
            "❌ Usage: `.giveaway <amount> <minutes> [wager:<min>] [invites:<min>]`\n"
            "Example: `.giveaway 5000 10 wager:10000 invites:2`"); return

    bal = get_user_balance(ctx.author.id)
    amount_val = resolve_bet(amount, bal)
    if amount_val is None: await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amount_val <= 0:    await ctx.send("❌ Amount must be positive!"); return
    if amount_val > bal:   await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return

    try:
        mins = int(minutes)
        if mins < 1 or mins > 60: raise ValueError
    except ValueError:
        await ctx.send("❌ Minutes must be a whole number between 1 and 60."); return

    req_wager   = 0
    req_invites = 0
    for arg in args:
        lo = arg.lower()
        if lo.startswith('wager:'):
            try: req_wager   = int(arg.split(':')[1].replace(',', ''))
            except: pass
        elif lo.startswith('invites:'):
            try: req_invites = int(arg.split(':')[1])
            except: pass

    set_user_balance(ctx.author.id, bal - amount_val)

    duration = mins * 60
    view = GiveawayView(ctx.author.id, amount_val, duration, req_wager, req_invites)

    reqs = []
    if req_wager   > 0: reqs.append(f"💰 Total wagered ≥ **R${req_wager:,}**")
    if req_invites > 0: reqs.append(f"📨 Total invites ≥ **{req_invites}**")
    reqs_str = "\n".join(reqs) if reqs else "✅ Open to everyone!"

    e = embed(
        "Giveaway",
        (
            f"**Prize:** 🏆 R${amount_val:,} points\n"
            f"**Host:** {ctx.author.mention}\n\n"
            f"**Requirements:**\n{reqs_str}\n\n"
            f"⏳ Ends in **{mins} minute{'s' if mins != 1 else ''}** — press the button below to enter!"
        ),
        C.GOLD,
        footer=f"0 entries  ·  {mins}m remaining",
    )
    msg = await ctx.send(embed=e, view=view)

    # Schedule countdown nudges
    nudges = []
    if mins >= 10: nudges.append((mins - 5,  "5 minutes"))
    if mins >= 3:  nudges.append((mins - 1,  "1 minute"))
    nudges.sort()

    elapsed = 0
    for at_min, label in nudges:
        wait = at_min * 60 - elapsed
        if wait > 0:
            await asyncio.sleep(wait)
            elapsed += wait
        if not view.is_finished():
            count = len(view.entrants)
            e.set_footer(text=f"{count} entr{'ies' if count != 1 else 'y'}  ·  ⚠️ {label} left!")
            try: await msg.edit(embed=e, view=view)
            except: pass

    remaining = duration - elapsed
    if remaining > 0:
        await asyncio.sleep(remaining)

    for item in view.children:
        item.disabled = True

    entrants = list(view.entrants)

    if not entrants:
        set_user_balance(ctx.author.id, get_user_balance(ctx.author.id) + amount_val)
        e = embed(
            "Giveaway Ended — No Entries",
            f"Nobody entered. **R${amount_val:,}** refunded to {ctx.author.mention}.",
            C.WARNING,
        )
        try: await msg.edit(embed=e, view=view)
        except: pass
        return

    import random
    winner_id  = random.choice(entrants)
    prev_bal   = get_user_balance(winner_id)
    set_user_balance(winner_id, prev_bal + amount_val)

    try:    winner = await bot.fetch_user(winner_id)
    except: winner = None
    winner_str = winner.mention if winner else f"<@{winner_id}>"

    e = embed(
        "Giveaway Over!",
        (
            f"🏆 **Winner:** {winner_str}\n"
            f"💰 **Prize:** R${amount_val:,} points\n"
            f"👥 **Total Entries:** {len(entrants)}\n\n"
            f"**New balance:** {fmt(prev_bal + amount_val)}"
        ),
        C.GOLD,
        footer=f"Hosted by {ctx.author.name}  ·  {len(entrants)} entr{'ies' if len(entrants) != 1 else 'y'}",
    )
    try: await msg.edit(embed=e, view=view)
    except: pass
    await ctx.send(f"🎊 Congratulations {winner_str}! You won **R${amount_val:,}** points!")

@giveaway.error
async def giveaway_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("🚫 Administrator permission required to start a giveaway!")
    else:
        await ctx.send("❌ Usage: `.giveaway <amount> <minutes> [wager:<min>] [invites:<min>]`")


@bot.command(name='rank')
async def rank(ctx):
    data, uid = get_user(ctx.author.id); tw = data[uid]['stats']['total_wagered']
    rank_info, next_r = get_rank_info(tw); _, rname, rcolor = rank_info
    desc = f"**Current Rank:** {rname}\n**Total Wagered:** R${tw:,}\n\n"
    if next_r:
        nt, nn, _ = next_r; rt = rank_info[0]; span = nt - rt; prog = tw - rt
        pct = min(prog/span, 1.0) if span > 0 else 1.0
        bf = int(pct * 20); bar = "█"*bf + "░"*(20-bf)
        desc += (f"**Next Rank:** {nn}\n**Progress:** `[{bar}]` {int(pct*100)}%\n"
                 f"**Still need:** R${nt-tw:,} wagered\n\n")
    else:
        desc += "🎉 **MAX RANK ACHIEVED!**\n\n"
    desc += "**All Ranks:**\n"
    for thresh, name, _ in RANKS:
        marker = "→ " if name == rname else "   "; desc += f"{marker}{name}: R${thresh:,}+\n"
    e = embed("Your Rank", desc, rcolor)
    await ctx.send(embed=e)


@bot.command(name='clan')
async def clan(ctx, action: str = "help", *, arg: str = ""):
    action = action.lower().strip()
    if action == "create":
        name = arg.strip()
        if not name or len(name) > 20: await ctx.send("❌ Usage: `.clan create <name>` (max 20 chars)"); return
        data, uid = get_user(ctx.author.id)
        if data[uid].get('clan'): await ctx.send(f"❌ You're already in **{data[uid]['clan']}**!"); return
        clans = get_clans()
        if any(k.lower() == name.lower() for k in clans): await ctx.send(f"❌ **{name}** already exists!"); return
        clans[name] = {'owner_id': str(ctx.author.id), 'members': [str(ctx.author.id)], 'created_at': datetime.now(timezone.utc).isoformat()[:10]}
        save_clans(clans); data[uid]['clan'] = name; save_data(data)
        await ctx.send(embed=embed("🛡️ Clan Created!", f"You created **{name}**!\nShare `.clan join {name}` with friends.", C.SUCCESS))
    elif action == "join":
        name = arg.strip()
        if not name: await ctx.send("❌ Usage: `.clan join <name>`"); return
        clans = get_clans(); real = next((k for k in clans if k.lower()==name.lower()), None)
        if not real: await ctx.send(f"❌ Clan **{name}** not found!"); return
        data, uid = get_user(ctx.author.id)
        if data[uid].get('clan'): await ctx.send(f"❌ You're already in **{data[uid]['clan']}**!"); return
        clans[real]['members'].append(str(ctx.author.id)); save_clans(clans)
        data[uid]['clan'] = real; save_data(data)
        await ctx.send(embed=embed("🛡️ Joined Clan!", f"You joined **{real}**!", C.SUCCESS))
    elif action == "leave":
        data, uid = get_user(ctx.author.id); cn = data[uid].get('clan')
        if not cn: await ctx.send("❌ You're not in a clan!"); return
        clans = get_clans()
        if cn in clans:
            c = clans[cn]
            if c['owner_id']==str(ctx.author.id) and len(c['members'])>1:
                await ctx.send("❌ You're the owner! Kick all members first or use `.clan disband`."); return
            c['members'] = [m for m in c['members'] if m!=str(ctx.author.id)]
            if not c['members']: del clans[cn]
            save_clans(clans)
        data[uid]['clan'] = None; save_data(data)
        await ctx.send(embed=embed("🛡️ Left Clan", f"You left **{cn}**.", C.WARNING))
    elif action == "disband":
        data, uid = get_user(ctx.author.id); cn = data[uid].get('clan')
        if not cn: await ctx.send("❌ You're not in a clan!"); return
        clans = get_clans()
        if cn not in clans or clans[cn]['owner_id'] != str(ctx.author.id):
            await ctx.send("❌ You're not the owner!"); return
        members = clans[cn]['members']; del clans[cn]; save_clans(clans)
        all_data = load_data()
        for mid in members:
            if mid in all_data: all_data[mid]['clan'] = None
        save_data(all_data)
        await ctx.send(embed=embed("🛡️ Clan Disbanded", f"**{cn}** has been disbanded.", C.ERROR))
    elif action == "kick":
        match = re.search(r'<@!?(\d+)>', arg)
        if not match: await ctx.send("❌ Usage: `.clan kick @member`"); return
        target_id = match.group(1); data, uid = get_user(ctx.author.id); cn = data[uid].get('clan')
        if not cn: await ctx.send("❌ You're not in a clan!"); return
        clans = get_clans()
        if cn not in clans or clans[cn]['owner_id'] != str(ctx.author.id):
            await ctx.send("❌ Only the clan owner can kick!"); return
        if target_id == str(ctx.author.id): await ctx.send("❌ You can't kick yourself!"); return
        if target_id not in clans[cn]['members']: await ctx.send("❌ Not in your clan!"); return
        clans[cn]['members'].remove(target_id); save_clans(clans)
        td, tuid = get_user(int(target_id)); td[tuid]['clan'] = None; save_data(td)
        try: user = await bot.fetch_user(int(target_id)); uname = user.name
        except: uname = target_id
        await ctx.send(embed=embed("🛡️ Member Kicked", f"**{uname}** removed from **{cn}**.", C.WARNING))
    elif action == "info":
        name = arg.strip() if arg else None
        if not name:
            data, uid = get_user(ctx.author.id); name = data[uid].get('clan')
            if not name: await ctx.send("❌ You're not in a clan! Use `.clan info <name>`."); return
        clans = get_clans(); real = next((k for k in clans if k.lower()==name.lower()), None)
        if not real: await ctx.send(f"❌ Clan **{name}** not found!"); return
        c = clans[real]
        try: owner = await bot.fetch_user(int(c['owner_id'])); on = owner.name
        except: on = "Unknown"
        all_data = load_data()
        tw = sum(all_data.get(m,{}).get('stats',{}).get('total_wagered',0) for m in c['members'])
        e = embed(real, None, C.LOBBY)
        e.add_field(name="Owner",   value=on,                  inline=True)
        e.add_field(name="Members", value=str(len(c['members'])),inline=True)
        e.add_field(name="Founded", value=c.get('created_at','?')[:10], inline=True)
        e.add_field(name="Total Wagered", value=f"R${tw:,}", inline=True)
        await ctx.send(embed=e)
    elif action == "top":
        clans = get_clans()
        if not clans: await ctx.send("❌ No clans yet!"); return
        all_data = load_data()
        stats = sorted([(n, sum(all_data.get(m,{}).get('stats',{}).get('total_wagered',0) for m in c['members']), len(c['members'])) for n,c in clans.items()], key=lambda x: x[1], reverse=True)
        medals = ["🥇","🥈","🥉","4️⃣","5️⃣"]
        lines = [f"{medals[i]} **{n}**  —  R${t:,}  ({m} members)" for i,(n,t,m) in enumerate(stats[:5])]
        await ctx.send(embed=embed("🛡️ Clan Leaderboard", "\n".join(lines), C.GOLD))
    else:
        e = embed("🛡️ Clan Commands", None, C.LOBBY)
        for n, v in [(".clan create <name>","Create a new clan"),(".clan join <name>","Join a clan"),(".clan leave","Leave your clan"),(".clan disband","Disband your clan (owner)"),(".clan kick @member","Kick a member (owner)"),(".clan info [name]","View clan details"),(".clan top","Top 5 clans")]:
            e.add_field(name=n, value=v, inline=False)
        await ctx.send(embed=e)


@bot.command(name='price')
async def price(ctx, amount: int = None):
    if amount is not None:
        if amount <= 0: await ctx.send("❌ Amount must be positive!"); return
        usd = amount * POINTS_TO_USD
        description = (
            f"Points: **{amount:,.2f}**\n"
            f"ROBUX: **{amount:,}**\n"
            f"USD: **${usd:.2f}**\n\n"
            f"Rate: **{amount:,} POINT = {amount:,} Robux Or ${usd:.2f}**"
        )
        e = embed("💱 Price Conversion", description, C.SECONDARY)
        await ctx.send(embed=e)
    else:
        rows = [("1","R$1.00","$0.0037"),("100","R$100.00","$0.37"),("1,000","R$1,000","$3.70"),
                ("10,000","R$10,000","$37.00"),("100,000","R$100,000","$370.00"),("1,000,000","R$1,000,000","$3,700.00")]
        lines = ["```", f"{'Points':<12}  {'R$':>12}  {'USD':>10}", "-"*38]
        for pts, brl, usd in rows: lines.append(f"{pts:<12}  {brl:>12}  {usd:>10}")
        lines.append("```")
        e = embed(
            "LuckyBet Points Price",
            "\n".join(lines),
            C.SECONDARY,
            footer="Tip: .price <amount> to convert a specific value  |  Rate: 1pt = R$1 = $0.0037",
        )
        await ctx.send(embed=e)


@bot.group(name='thread', invoke_without_command=True)
async def thread_cmd(ctx):
    e = embed("💬 Thread Commands", color=C.SECONDARY, description=(
        "`.thread create` — Create a private thread\n"
        "`.thread close` — Close (archive) the current thread\n"
        "`.thread add @user` — Add a user to the current thread\n"
        "`.thread remove @user` — Remove a user from the current thread\n"
        "`.thread rename <new name>` — Rename the current thread"
    ))
    await ctx.send(embed=e)

@thread_cmd.command(name='create')
async def thread_create(ctx):
    existing = user_threads.get(ctx.author.id, set())
    live_existing = set()
    for tid in existing:
        guild = ctx.guild
        if guild is not None:
            t = guild.get_thread(tid)
            if t is not None and not t.archived:
                live_existing.add(tid)
    user_threads[ctx.author.id] = live_existing
    if live_existing:
        tid = next(iter(live_existing))
        guild = ctx.guild
        t = guild.get_thread(tid) if guild else None
        mention = t.mention if t else f"thread ID {tid}"
        await ctx.send(f"❌ You already have an active thread: {mention}\nUse `.thread close` there before making a new one.")
        return
    try:
        thread = await ctx.channel.create_thread(
            name=f"{ctx.author.name}'s Thread",
            type=discord.ChannelType.private_thread,
            auto_archive_duration=1440
        )
        await thread.add_user(ctx.author)
        await thread.send(f"Welcome {ctx.author.mention}! 👋 This is your private thread.")
        thread_activity[thread.id] = datetime.now(timezone.utc)
        user_threads.setdefault(ctx.author.id, set()).add(thread.id)
        e = embed("💬 Thread Created", f"Your thread: {thread.mention}", color=C.SUCCESS,
                  footer="Threads auto-close after 24h of inactivity")
        await ctx.send(embed=e)
    except discord.Forbidden:
        await ctx.send("❌ I don't have permission to create private threads!")
    except Exception as e:
        await ctx.send(f"❌ Could not create thread: {e}")

@thread_cmd.command(name='close')
async def thread_close(ctx):
    if not isinstance(ctx.channel, discord.Thread):
        await ctx.send("❌ This command can only be used inside a thread!")
        return
    try:
        await ctx.send("🗑️ Deleting thread...")
        thread_activity.pop(ctx.channel.id, None)
        for uids in user_threads.values():
            uids.discard(ctx.channel.id)
        await ctx.channel.delete()
    except discord.Forbidden:
        await ctx.send("❌ I don't have permission to delete this thread!")
    except Exception as e:
        await ctx.send(f"❌ Could not delete thread: {e}")

@thread_cmd.command(name='add')
async def thread_add(ctx, member: discord.Member = None):
    if not isinstance(ctx.channel, discord.Thread):
        await ctx.send("❌ This command can only be used inside a thread!")
        return
    if member is None:
        await ctx.send("❌ Please mention a user. Usage: `.thread add @user`")
        return
    try:
        await ctx.channel.add_user(member)
        e = embed("💬 User Added", f"{member.mention} has been added to the thread.", color=C.SUCCESS)
        await ctx.send(embed=e)
    except discord.Forbidden:
        await ctx.send("❌ I don't have permission to add users to this thread!")
    except Exception as e:
        await ctx.send(f"❌ Could not add user: {e}")

@thread_cmd.command(name='remove')
async def thread_remove(ctx, member: discord.Member = None):
    if not isinstance(ctx.channel, discord.Thread):
        await ctx.send("❌ This command can only be used inside a thread!")
        return
    if member is None:
        await ctx.send("❌ Please mention a user. Usage: `.thread remove @user`")
        return
    try:
        await ctx.channel.remove_user(member)
        e = embed("💬 User Removed", f"{member.mention} has been removed from the thread.", color=C.ERROR)
        await ctx.send(embed=e)
    except discord.Forbidden:
        await ctx.send("❌ I don't have permission to remove users from this thread!")
    except Exception as e:
        await ctx.send(f"❌ Could not remove user: {e}")


@thread_cmd.command(name='rename')
async def thread_rename(ctx, *, new_name: str = None):
    if not isinstance(ctx.channel, discord.Thread):
        await ctx.send("❌ This command can only be used inside a thread!"); return
    if not new_name:
        await ctx.send("❌ Usage: `.thread rename <new name>`"); return
    if len(new_name) > 100:
        await ctx.send("❌ Thread name must be 100 characters or less!"); return
    try:
        await ctx.channel.edit(name=new_name)
        e = embed("💬 Thread Renamed",
                  f"Thread renamed to **{new_name}**", color=C.SECONDARY)
        await ctx.send(embed=e)
    except discord.Forbidden:
        await ctx.send("❌ I don't have permission to rename this thread!")
    except Exception as e:
        await ctx.send(f"❌ Could not rename thread: {e}")

# ── Jackpot ───────────────────────────────────────────────────────────────────

JACKPOT_DURATION    = 60    # seconds the round stays open
JACKPOT_MIN_BET     = 10    # minimum contribution per entry
JACKPOT_FAIL_ODDS   = 0.12  # 12 % chance nobody wins (provably fair)
JACKPOT_HOUSE_EDGE  = 0.08  # 8 % taken from the pot on a win
JACKPOT_MIN_PLAYERS = 2     # minimum distinct players needed to draw

jackpot_state = {
    'active':      False,
    'entries':     {},        # uid(int) -> {'name': str, 'amount': int}
    'total':       0,
    'channel_id':  None,
    'msg_id':      None,
    'task':        None,
    'server_seed': None,
    'client_seed': None,
    'public_hash': None,
    'ends_at':     None,
}


def _jackpot_embed_live():
    state  = jackpot_state
    now    = datetime.now(timezone.utc)
    secs   = max(0, int((state['ends_at'] - now).total_seconds())) if state['ends_at'] else 0
    total  = state['total']
    e = embed("🎰 Jackpot — Round Open!",
        (
            f"⏳ Drawing in **{secs}s**\n"
            f"💰 Total Pot: **R${total:,}**\n"
            f"👥 Players: **{len(state['entries'])}**\n\n"
            f"🔐 Pre-draw Hash: `{state['public_hash'][:20]}…`"
        ), C.GOLD,
        footer=f"Min: R${JACKPOT_MIN_BET:,}  |  Fail chance: {int(JACKPOT_FAIL_ODDS*100)}%  |  House edge: {int(JACKPOT_HOUSE_EDGE*100)}%")
    if state['entries']:
        lines = []
        for uid, ent in sorted(state['entries'].items(), key=lambda x: x[1]['amount'], reverse=True):
            pct = ent['amount'] / total * 100 if total else 0
            lines.append(f"**{ent['name']}** — R${ent['amount']:,} ({pct:.1f}% chance)")
        e.add_field(name="🎟️ Entries", value="\n".join(lines[:15]), inline=False)
    return e


async def _run_jackpot_draw():
    await asyncio.sleep(JACKPOT_DURATION)

    state       = jackpot_state
    channel     = bot.get_channel(state['channel_id'])
    entries     = dict(state['entries'])
    total       = state['total']
    server_seed = state['server_seed']
    client_seed = state['client_seed']
    public_hash = state['public_hash']

    # Fetch the live message before resetting state
    live_msg = None
    if channel and state['msg_id']:
        try: live_msg = await channel.fetch_message(state['msg_id'])
        except: pass

    # Reset state so a new round can start immediately
    jackpot_state.update(active=False, entries={}, total=0, channel_id=None,
                         msg_id=None, task=None, ends_at=None,
                         server_seed=None, client_seed=None, public_hash=None)

    if not channel:
        return

    # ── Not enough players: refund everyone ──────────────────────────────────
    if len(entries) < JACKPOT_MIN_PLAYERS:
        for uid, e in entries.items():
            set_user_balance(uid, get_user_balance(uid) + e['amount'])
        e = embed("❌ Jackpot — Cancelled",
            (
                f"Only **{len(entries)}** player(s) joined "
                f"({JACKPOT_MIN_PLAYERS} required).\n"
                f"💸 All bets have been **refunded**."
            ), C.ERROR)
        pf_add_field(e, server_seed, client_seed, public_hash, "jackpot")
        if live_msg: await live_msg.edit(embed=e)
        else: await channel.send(embed=e)
        return

    # ── Fail check (nonce 0) ─────────────────────────────────────────────────
    fail_val = pf_derive(server_seed, client_seed, nonce=0)
    if fail_val < JACKPOT_FAIL_ODDS:
        e = embed("💥 Jackpot — FAILED!",
            (
                f"The jackpot has **failed** and nobody wins!\n"
                f"💀 **R${total:,}** has been swallowed by the house.\n\n"
                f"*(Fail roll: `{fail_val:.4f}` < `{JACKPOT_FAIL_ODDS}` threshold)*"
            ), C.ERROR)
        pf_add_field(e, server_seed, client_seed, public_hash, "jackpot")
        if live_msg: await live_msg.edit(embed=e)
        else: await channel.send(embed=e)
        return

    # ── Weighted draw (nonce 1) ───────────────────────────────────────────────
    draw_val   = pf_derive(server_seed, client_seed, nonce=1)
    cursor     = 0.0
    winner_uid = None
    uid_list   = list(entries.keys())
    for uid in uid_list:
        cursor += entries[uid]['amount'] / total
        if draw_val <= cursor:
            winner_uid = uid
            break
    if winner_uid is None:
        winner_uid = uid_list[-1]

    winnings    = int(total * (1 - JACKPOT_HOUSE_EDGE))
    new_bal     = get_user_balance(winner_uid) + winnings
    set_user_balance(winner_uid, new_bal)
    add_to_stats(winner_uid, True, 0)
    winner_name         = entries[winner_uid]['name']
    winner_contribution = entries[winner_uid]['amount']
    winner_pct          = winner_contribution / total * 100

    try: winner_user = await bot.fetch_user(winner_uid)
    except: winner_user = None

    e = embed("🎉 Jackpot — WINNER!",
        (
            f"🏆 **{winner_name}** wins **R${winnings:,}**!\n"
            f"🎟️ Had a **{winner_pct:.1f}%** chance "
            f"(contributed R${winner_contribution:,} of R${total:,})\n"
            f"🏦 New balance: **{fmt(new_bal)}**\n\n"
            f"*(Draw roll: `{draw_val:.4f}`)*"
        ), C.SUCCESS)
    if winner_user:
        e.set_thumbnail(url=winner_user.display_avatar.url)

    lines = []
    for uid, ent in sorted(entries.items(), key=lambda x: x[1]['amount'], reverse=True):
        pct    = ent['amount'] / total * 100
        marker = "👑" if uid == winner_uid else "❌"
        lines.append(f"{marker} **{ent['name']}** — R${ent['amount']:,} ({pct:.1f}%)")
    e.add_field(name="🎟️ All Entries", value="\n".join(lines[:15]), inline=False)
    pf_add_field(e, server_seed, client_seed, public_hash, "jackpot")

    if live_msg: await live_msg.edit(embed=e)
    else: await channel.send(embed=e)

    guild = bot.get_guild(channel.guild.id) if channel else None
    asyncio.create_task(send_to_history(guild, 'jackpot', winner_name, winner_uid, winner_contribution, True, winnings, new_bal))

    if channel:
        await channel.send(f"🎉 Congratulations <@{winner_uid}>! You won **R${winnings:,}**!")


@bot.command(name='jackpot', aliases=['jp'])
async def jackpot_cmd(ctx, amount: str = None):
    state = jackpot_state

    # ── No argument: show status ──────────────────────────────────────────────
    if amount is None:
        if not state['active']:
            e = embed("Jackpot",
                (
                    "No jackpot is currently running.\n\n"
                    f"Start one with `.jackpot <amount>`!\n\n"
                    f"• Min entry: **R${JACKPOT_MIN_BET:,}**\n"
                    f"• Round lasts **{JACKPOT_DURATION}s** after the first entry\n"
                    f"• Contribution = your win chance (more = better)\n"
                    f"• **{int(JACKPOT_FAIL_ODDS*100)}%** chance the pot **fails** and nobody wins\n"
                    f"• **{int(JACKPOT_HOUSE_EDGE*100)}%** house edge deducted from the prize"
                ), C.LOBBY)
            await ctx.send(embed=e)
        else:
            await ctx.send(embed=_jackpot_embed_live())
        return

    # ── Joining / starting a round ────────────────────────────────────────────
    bal = get_user_balance(ctx.author.id)
    amt = resolve_bet(amount, bal)
    if amt is None:
        await ctx.send("❌ Invalid amount! Use a number, `all`, or `half`."); return
    if amt < JACKPOT_MIN_BET:
        await ctx.send(f"❌ Minimum jackpot entry is **R${JACKPOT_MIN_BET:,}**!"); return
    if amt > bal:
        await ctx.send(f"❌ Insufficient balance! You have {fmt(bal)}"); return

    uid = ctx.author.id

    if state['active'] and uid in state['entries']:
        await ctx.send(f"❌ You already entered this round (R${state['entries'][uid]['amount']:,} in)!"); return

    # Deduct immediately
    set_user_balance(uid, bal - amt)

    if not state['active']:
        server_seed, client_seed, public_hash = generate_seeds()
        jackpot_state.update(
            active=True, entries={}, total=0,
            server_seed=server_seed, client_seed=client_seed, public_hash=public_hash,
            channel_id=ctx.channel.id, msg_id=None,
            ends_at=datetime.now(timezone.utc) + timedelta(seconds=JACKPOT_DURATION),
        )

    state['entries'][uid] = {'name': ctx.author.name, 'amount': amt}
    state['total']       += amt

    embed = _jackpot_embed_live()

    if state['msg_id'] is None:
        msg = await ctx.send(embed=embed)
        state['msg_id'] = msg.id
        state['task']   = asyncio.create_task(_run_jackpot_draw())
    else:
        try:
            ch  = bot.get_channel(state['channel_id'])
            lm  = await ch.fetch_message(state['msg_id'])
            await lm.edit(embed=embed)
            await ctx.message.add_reaction("✅")
        except:
            msg = await ctx.send(embed=embed)
            state['msg_id'] = msg.id


# ── General ───────────────────────────────────────────────────────────────────

@bot.command(name='leaderboard', aliases=['lb'])
async def leaderboard(ctx):
    data = load_data(); users = {k:v for k,v in data.items() if not k.startswith('__') and 'balance' in v}
    if not users: await ctx.send("❌ No players yet!"); return
    top = sorted(users.items(), key=lambda x: x[1]['balance'], reverse=True)[:10]
    medals = ["🥇","🥈","🥉"] + ["🏅"]*7
    lines = []
    for idx, (uid, ud) in enumerate(top):
        try: user = await bot.fetch_user(int(uid)); name = user.name
        except: name = "Unknown"
        lines.append(f"{medals[idx]} **{name}**  —  {fmt(ud['balance'])}")
    e = embed("🏆 LuckyBet Leaderboard", "\n".join(lines), C.GOLD)
    await ctx.send(embed=e)


@bot.command(name='stats')
async def stats(ctx, member: discord.Member = None):
    target = member or ctx.author; data, uid = get_user(target.id); ud = data[uid]; s = ud['stats']
    total = s['wins'] + s['losses']; rank_info, _ = get_rank_info(s['total_wagered'])
    now = datetime.now(timezone.utc); last_daily = ud.get('last_daily')
    if last_daily:
        ld = datetime.fromisoformat(last_daily)
        if ld.tzinfo is None: ld = ld.replace(tzinfo=timezone.utc)
        diff = now - ld
        if diff.total_seconds() < 86400:
            rem = timedelta(seconds=86400) - diff
            h = int(rem.total_seconds()//3600); m = int((rem.total_seconds()%3600)//60)
            daily_str = f"⏳ Ready in {h}h {m}m"
        else: daily_str = "✅ Ready to claim!"
    else: daily_str = "✅ Ready to claim!"
    bal = ud['balance']
    e = embed(
        f"📊 {target.name}'s Profile",
        f"💰 **Balance:** {bal:,.0f} pts  •  R${bal:,.0f}  •  ${bal*POINTS_TO_USD:.2f}\n"
        f"🏆 **Rank:** {rank_info[1]}  •  🎁 **Daily:** {daily_str}",
        C.PRIMARY,
        thumbnail=target.display_avatar.url,
    )
    e.add_field(name="Games Played", value=f"`{total:,}`", inline=True)
    e.add_field(name="Won",          value=f"`{s['wins']:,}`", inline=True)
    e.add_field(name="Lost",         value=f"`{s['losses']:,}`", inline=True)
    e.add_field(name="Total Wagered",  value=f"`{s['total_wagered']:,.0f}`", inline=True)
    e.add_field(name="Bonus Received", value=f"`{ud.get('bonus_received',0):,.0f}`", inline=True)
    e.add_field(name="Tips Sent",      value=f"`{ud.get('tips_sent',0):,.0f}`", inline=True)
    e.add_field(name="Tips Received",  value=f"`{ud.get('tips_received',0):,.0f}`", inline=True)
    e.add_field(name="Withdrawn",      value=f"`{ud.get('total_withdrawn',0):,.0f}`", inline=True)
    e.add_field(name="\u200b",          value="\u200b", inline=True)
    await ctx.send(embed=e)

@stats.error
async def stats_error(ctx, error):
    if isinstance(error, commands.MemberNotFound): await ctx.send("❌ Member not found — mention them with @")
    else: await ctx.send("❌ Usage: `.stats` or `.stats @user`")

@bot.command(name="housebal", aliases=["bankroll", "house"])
async def housebal(ctx):
    data = load_data()

    player_balances = 0
    total_deposited_usd = 0.0
    total_withdrawn_pts = 0
    total_wagered = 0
    total_lost = 0
    total_won_count = 0
    total_loss_count = 0
    rakeback_outstanding = 0.0
    active_players = 0

    for uid, user in data.items():
        if uid.startswith("__") or not isinstance(user, dict):
            continue
        bal = int(user.get("balance", 0) or 0)
        player_balances += bal
        total_deposited_usd += float(user.get("total_deposited", 0) or 0)
        total_withdrawn_pts += int(user.get("total_withdrawn", 0) or 0)
        rakeback_outstanding += float(user.get("rakeback_available", 0) or 0)
        s = user.get("stats", {}) or {}
        total_wagered += int(s.get("total_wagered", 0) or 0)
        total_lost    += int(s.get("total_lost", 0) or 0)
        total_won_count  += int(s.get("wins", 0) or 0)
        total_loss_count += int(s.get("losses", 0) or 0)
        if bal > 0 or s.get("total_wagered", 0):
            active_players += 1

    # Bankroll math (points)
    deposited_pts = usd_to_points(total_deposited_usd)
    # House profit = what came in (deposits) − what's owed to players
    # (current balances + outstanding rakeback) − what already cashed out.
    owed_to_players = player_balances + int(round(rakeback_outstanding))
    house_profit_pts = deposited_pts - total_withdrawn_pts - owed_to_players
    house_profit_usd = house_profit_pts * POINTS_TO_USD

    total_bets = total_won_count + total_loss_count
    house_edge = (total_lost / total_wagered * 100.0) if total_wagered else 0.0

    color = C.SUCCESS if house_profit_pts >= 0 else C.ERROR
    e = embed(
        "LuckyBet — House Bankroll",
        (
            f"**House Profit:** `{house_profit_pts:+,}` pts  "
            f"(≈ **${house_profit_usd:+,.2f}**)\n"
            f"_Deposits − Withdrawals − Player Balances − Rakeback owed_"
        ),
        color,
        footer=f"1 pt ≈ ${POINTS_TO_USD:.4f} USD",
    )

    e.add_field(
        name="💰 Money In",
        value=(
            f"Deposits: **${total_deposited_usd:,.2f}**\n"
            f"= **{deposited_pts:,}** pts"
        ),
        inline=True,
    )
    e.add_field(
        name="💸 Money Out",
        value=(
            f"Withdrawn: **{total_withdrawn_pts:,}** pts\n"
            f"≈ **${total_withdrawn_pts*POINTS_TO_USD:,.2f}**"
        ),
        inline=True,
    )
    e.add_field(
        name="👥 Player Liability",
        value=(
            f"Balances: **{player_balances:,}** pts\n"
            f"Rakeback owed: **{rakeback_outstanding:,.0f}** pts\n"
            f"Active players: **{active_players:,}**"
        ),
        inline=False,
    )
    e.add_field(
        name="🎲 Wager Stats",
        value=(
            f"Total wagered: **{total_wagered:,}** pts\n"
            f"Player net loss: **{total_lost:,}** pts\n"
            f"Bets placed: **{total_bets:,}**\n"
            f"House edge (realised): **{house_edge:.2f}%**"
        ),
        inline=False,
    )
    await ctx.send(embed=e)


@bot.command(name="resethouse", aliases=["housereset"])
@commands.has_permissions(administrator=True)
async def resethouse(ctx, scope: str = "all"):
    """Reset house bankroll stats. Scope: all | wager | withdrawn | rakeback | deposits | bets"""
    scope = scope.lower()
    valid = {"all", "wager", "withdrawn", "rakeback", "deposits", "bets"}
    if scope not in valid:
        return await ctx.send(f"❌ Scope must be one of: {', '.join(sorted(valid))}")

    data = load_data()
    touched = 0
    for uid, ud in data.items():
        if not isinstance(ud, dict):
            continue
        s = ud.setdefault('stats', {'wins': 0, 'losses': 0, 'total_wagered': 0, 'total_lost': 0})
        if scope in ("all", "wager"):
            s['total_wagered'] = 0
            s['total_lost'] = 0
            ud['wager_at_last_monthly'] = 0
            ud['wager_since_promo'] = 0
        if scope in ("all", "bets", "wager"):
            s['wins'] = 0
            s['losses'] = 0
        if scope in ("all", "withdrawn"):
            ud['total_withdrawn'] = 0
        if scope in ("all", "rakeback"):
            ud['rakeback_available'] = 0.0
        if scope in ("all", "deposits"):
            ud['deposited'] = 0
        touched += 1
    save_data(data)

    e = embed(
        "House Stats Reset",
        f"Scope: **{scope}** • Users updated: **{touched}**",
        color=C.SUCCESS,
    )
    await ctx.send(embed=e)


@resethouse.error
async def resethouse_error(ctx, error):
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("❌ Admin only.")





GAMES_CATALOG = [
    ("🪙", ".coinflip / .cf <amt> <h/t>", "Coin flip, 1:1 payout"),
    ("🎲", ".dice <amt> <1-6>", "Guess the die roll, ×5"),
    ("📈", ".limbo <amt> <target>", "Beat your target multiplier"),
    ("🎢", ".slide <amt> <target>", "Slider; win if it lands ≥ your pick"),
    ("🗜️", ".tight <amt>", "Random multiplier up to 5.00× (96% RTP)"),
    ("🌀", ".twist <amt>", "Move through multiplier tiles via dice rolls"),
    ("💰", ".treasurehunt / .th <amt>", "Pick a chest, multiplier up to 2.5×"),
    ("🗼", ".tower <amt>", "Climb the tower; choose difficulty after betting"),
    ("⛏️", ".mines <amt> [mines]", "Provably fair mines"),
    ("🎰", ".slots <amt>", "Slots up to ×100"),
    ("💘", ".valentines <amt>", "Special Valentine's Day slots"),
    ("🎡", ".roulette <amt> <r/b/e/o>", "Roulette, ×2"),
    ("🃏", ".blackjack / .bj <amt>", "Hit, Stand, Double"),
    ("⚔️", ".war <amt>", "Card war; highest card wins ×2"),
    ("✂️", ".rps <amt> <r/p/s>", "Rock-Paper-Scissors vs the bot"),
    ("#️⃣", ".ttt @user", "Tic Tac Toe against another user"),
    ("🚀", ".crash <amt>", "Multiplayer crash game"),
    ("🚀", ".crashroom <amt>", "Create a crash room (fixed entry bet)"),
    ("🎰", ".jackpot / .jp <amt>", "Weighted jackpot pool"),
]


@bot.command(name='games')
async def games_command(ctx):
    e = embed(
        "🎮 LuckyBet — All Games",
        f"**{len(GAMES_CATALOG)}** games available — all provably fair.\nUse `.help` for the full command list.",
        color=C.LOBBY)
    lines = [f"{emoji} `{usage}`\n— {desc}" for emoji, usage, desc in GAMES_CATALOG]
    half = (len(lines) + 1) // 2
    e.add_field(name="\u200b", value="\n".join(lines[:half]), inline=True)
    e.add_field(name="\u200b", value="\n".join(lines[half:]), inline=True)
    await ctx.send(embed=e)


async def nowpayments_request(method, path, payload=None):
    headers = {'x-api-key': NOWPAYMENTS_API_KEY, 'Content-Type': 'application/json'}
    url = f"{NOWPAYMENTS_API}{path}"
    async with aiohttp.ClientSession() as session:
        async with session.request(method, url, headers=headers, json=payload, timeout=aiohttp.ClientTimeout(total=30)) as resp:
            data = await resp.json(content_type=None)
            return resp.status, data


async def credit_deposit(payment_id, dep):
    """Credit a confirmed deposit's points to the user exactly once."""
    deposits = get_deposits()
    rec = deposits.get(payment_id)
    if not rec or rec.get('status') == 'credited':
        return
    uid = int(rec['user_id'])
    set_user_balance(uid, get_user_balance(uid) + rec['points'])
    rec['status'] = 'credited'
    rec['credited_at'] = datetime.now(timezone.utc).isoformat()
    deposits[payment_id] = rec
    save_deposits(deposits)
    user = None
    try:
        user = await bot.fetch_user(uid)
        e = embed(None, (
            f"🎉 **Deposit Confirmed!**\n"
            f"Your payment of **${rec['usd']:.2f}** was successfully received. "
            f"**{rec['points']:,} points** have been permanently added to your casino balance!"),
            C.SUCCESS)
        await user.send(embed=e)
    except Exception:
        pass
    await log_deposit(rec, payment_id, user)


async def log_deposit(rec, payment_id, user=None):
    """Post a confirmed deposit to the configured deposit-log channel."""
    cfg = get_config()
    ch_id = cfg.get('deposit_log_channel')
    if not ch_id:
        return
    channel = bot.get_channel(int(ch_id))
    if not channel:
        return
    uid = int(rec['user_id'])
    who = user.mention if user else f"<@{uid}>"
    e = embed("💸 Deposit Logged", None, C.SUCCESS,
              footer=f"Payment ID: {payment_id}")
    e.description = (
        f"**User:** {who} (`{uid}`)\n"
        f"**Amount:** ${rec['usd']:.2f}  ·  {rec.get('pay_amount', '?')} LTC\n"
        f"**Credited:** {rec['points']:,} points")
    try:
        await channel.send(embed=e)
    except Exception:
        pass


@bot.command(name='deposit', aliases=['deposits'])
async def deposit(ctx, amount: str = None):
    if not NOWPAYMENTS_API_KEY:
        await ctx.send("❌ Deposits aren't configured yet. Ask an admin to set up the payment provider."); return
    if amount is None:
        await ctx.send(f"❌ Usage: `.deposit <usd_amount>` (minimum ${DEPOSIT_MIN_USD:g}). Example: `.deposit 10`"); return
    try:
        usd = round(float(amount.lower().replace('$', '').strip()), 2)
    except ValueError:
        await ctx.send("❌ Invalid amount! Enter a USD value, e.g. `.deposit 10`."); return
    if usd < DEPOSIT_MIN_USD:
        await ctx.send(f"❌ Minimum deposit is ${DEPOSIT_MIN_USD:g}."); return

    notice = await ctx.send("📨 Generating your deposit address... check your DMs!")
    order_id = f"{ctx.author.id}-{int(datetime.now(timezone.utc).timestamp())}"
    try:
        status, data = await nowpayments_request('POST', '/payment', {
            'price_amount': usd,
            'price_currency': 'usd',
            'pay_currency': DEPOSIT_PAY_CURRENCY,
            'order_id': order_id,
            'order_description': f"LuckyBet deposit for {ctx.author.name}",
        })
    except Exception:
        await notice.edit(content="❌ Couldn't reach the payment provider. Try again shortly."); return

    if status != 201 or 'pay_address' not in data:
        msg = data.get('message', 'Unknown error') if isinstance(data, dict) else 'Unknown error'
        await notice.edit(content=f"❌ Couldn't create deposit: {msg}"); return

    payment_id = str(data['payment_id'])
    pay_address = data['pay_address']
    pay_amount  = data['pay_amount']
    points      = usd_to_points(usd)

    deposits = get_deposits()
    deposits[payment_id] = {
        'user_id':   str(ctx.author.id),
        'usd':       usd,
        'points':    points,
        'address':   pay_address,
        'pay_amount': pay_amount,
        'status':    'pending',
        'created':   datetime.now(timezone.utc).isoformat(),
    }
    save_deposits(deposits)

    qr = f"https://api.qrserver.com/v1/create-qr-code/?size=240x240&data={pay_address}"
    e = embed("💸 LTC Deposit", (
        f"Send **exactly** the amount below to the address. You'll get **{points:,} points** "
        f"(${usd:.2f}) once it confirms on-chain.\n\u200b"),
        C.ACCENT,
        footer="Send only LTC. Points are credited automatically after network confirmation.")
    e.add_field(name="Amount to send", value=f"```{pay_amount} LTC```", inline=False)
    e.add_field(name="LTC Address",   value=f"```{pay_address}```", inline=False)
    e.set_thumbnail(url=qr)
    try:
        await ctx.author.send(embed=e)
        await notice.edit(content=f"{ctx.author.mention} 📬 Sent your unique LTC deposit address in DMs!")
    except discord.Forbidden:
        await notice.edit(content=f"{ctx.author.mention} ❌ I couldn't DM you — enable DMs from server members and try again.")


async def deposit_watcher():
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            deposits = get_deposits()
            for payment_id, rec in list(deposits.items()):
                if rec.get('status') != 'pending':
                    continue
                try:
                    status, data = await nowpayments_request('GET', f'/payment/{payment_id}')
                except Exception:
                    continue
                if status != 200 or not isinstance(data, dict):
                    continue
                pay_status = data.get('payment_status')
                if pay_status in DEPOSIT_PAID_STATES:
                    await credit_deposit(payment_id, rec)
                elif pay_status == 'partially_paid':
                    rec['status'] = 'partial'; deposits[payment_id] = rec; save_deposits(deposits)
                elif pay_status in DEPOSIT_DEAD_STATES:
                    rec['status'] = pay_status; deposits[payment_id] = rec; save_deposits(deposits)
        except Exception:
            pass
        await asyncio.sleep(45)

async def nowpayments_jwt():
    """Return a cached JWT for NOWPayments payouts (refreshes ~4 min before expiry)."""
    import time
    if _NP_JWT['token'] and _NP_JWT['expires_at'] - time.time() > 60:
        return _NP_JWT['token']
    if not (NOWPAYMENTS_EMAIL and NOWPAYMENTS_PASSWORD):
        raise RuntimeError("NOWPAYMENTS_EMAIL / NOWPAYMENTS_PASSWORD not configured")
    async with aiohttp.ClientSession() as session:
        async with session.post(
            f"{NOWPAYMENTS_API}/auth",
            json={'email': NOWPAYMENTS_EMAIL, 'password': NOWPAYMENTS_PASSWORD},
            timeout=aiohttp.ClientTimeout(total=30),
        ) as resp:
            data = await resp.json(content_type=None)
            if resp.status != 200 or 'token' not in data:
                raise RuntimeError(f"NOWPayments auth failed: {data}")
            _NP_JWT['token'] = data['token']
            _NP_JWT['expires_at'] = time.time() + 5 * 60  # NP JWT lives ~5 min
            return _NP_JWT['token']


def _totp_now(secret):
    """Generate a 6-digit TOTP code from a base32 secret (RFC 6238, 30s step)."""
    import base64, struct, hmac as _hmac, hashlib as _h, time
    key = base64.b32decode(secret.replace(' ', '').upper() + '=' * ((8 - len(secret) % 8) % 8))
    counter = struct.pack('>Q', int(time.time()) // 30)
    digest = _hmac.new(key, counter, _h.sha1).digest()
    offset = digest[-1] & 0x0F
    code = (struct.unpack('>I', digest[offset:offset+4])[0] & 0x7FFFFFFF) % 1_000_000
    return f"{code:06d}"


async def create_payout(user_id, address, ltc_amount, usd_value):
    """Create + verify a NOWPayments LTC payout. Returns (ok, payload_or_error)."""
    if not NOWPAYMENTS_API_KEY:
        return False, "NOWPAYMENTS_API_KEY not configured"
    jwt = await nowpayments_jwt()
    headers = {
        'x-api-key': NOWPAYMENTS_API_KEY,
        'Authorization': f'Bearer {jwt}',
        'Content-Type': 'application/json',
    }
    payload = {'withdrawals': [{
        'address': address,
        'currency': WITHDRAW_PAY_CURRENCY,
        'amount': float(f"{ltc_amount:.8f}"),
        'ipn_callback_url': '',
    }]}
    async with aiohttp.ClientSession() as session:
        async with session.post(f"{NOWPAYMENTS_API}/payout",
                                headers=headers, json=payload,
                                timeout=aiohttp.ClientTimeout(total=30)) as resp:
            data = await resp.json(content_type=None)
            if resp.status not in (200, 201) or not isinstance(data, dict) or 'id' not in data:
                return False, (data.get('message') if isinstance(data, dict) else str(data)) or "create failed"
        batch_id = data['id']
        # Verify with TOTP if 2FA is enabled on the NOWPayments account
        if NOWPAYMENTS_2FA_SECRET:
            code = _totp_now(NOWPAYMENTS_2FA_SECRET)
            async with session.post(f"{NOWPAYMENTS_API}/payout/{batch_id}/verify",
                                    headers=headers, json={'verification_code': code},
                                    timeout=aiohttp.ClientTimeout(total=30)) as vresp:
                vdata = await vresp.json(content_type=None)
                if vresp.status not in (200, 201):
                    return False, (vdata.get('message') if isinstance(vdata, dict) else str(vdata)) or "verify failed"
        return True, {'batch_id': batch_id, 'withdrawals': data.get('withdrawals', [])}


async def get_ltc_estimate(usd_value):
    """Ask NOWPayments how much LTC equals usd_value. Returns float LTC."""
    async with aiohttp.ClientSession() as session:
        async with session.get(
            f"{NOWPAYMENTS_API}/estimate",
            params={'amount': usd_value, 'currency_from': 'usd', 'currency_to': WITHDRAW_PAY_CURRENCY},
            headers={'x-api-key': NOWPAYMENTS_API_KEY},
            timeout=aiohttp.ClientTimeout(total=20),
        ) as resp:
            data = await resp.json(content_type=None)
            if resp.status != 200 or 'estimated_amount' not in data:
                raise RuntimeError(f"estimate failed: {data}")
            return float(data['estimated_amount'])


def is_valid_ltc_address(addr):
    if not addr or len(addr) < 26 or len(addr) > 80:
        return False
    # Legacy (L/M/3), SegWit P2SH (M), bech32 (ltc1...)
    return bool(re.match(r'^(ltc1[02-9ac-hj-np-z]{6,})$|^[LM3][a-km-zA-HJ-NP-Z1-9]{25,34}$', addr))


@bot.command(name="withdraw")
async def withdraw(ctx, amount: int = None, ltc_address: str = None):
    if amount is None or ltc_address is None:
        await ctx.send("❌ Usage: `.withdraw <points> <ltc_address>`"); return
    if amount < MIN_WITHDRAW:
        await ctx.send(f"❌ Minimum withdrawal is **{MIN_WITHDRAW:,} points**."); return
    if not is_valid_ltc_address(ltc_address):
        await ctx.send("❌ That doesn't look like a valid LTC address."); return

    bal = get_user_balance(ctx.author.id)
    if bal < amount:
        await ctx.send(f"❌ You only have **{bal:,} points**."); return

    data, uid = get_user(ctx.author.id)
    wager_req = data[uid].get('wager_requirement', 0)
    if wager_req > 0:
        wager_since = data[uid].get('wager_since_promo', 0)
        total_wagered = data[uid]['stats'].get('total_wagered', 0)
        wagered_amount = total_wagered - wager_since
        remaining = wager_req - wagered_amount
        if remaining > 0:
            await ctx.send(
                f"🔒 **Wager Requirement Active!**\n"
                f"You have a promo wager requirement of **R${wager_req:,}**.\n"
                f"You've wagered **R${wagered_amount:,}** so far.\n"
                f"**Remaining:** R${remaining:,} before you can withdraw."
            )
            return

    if not (NOWPAYMENTS_API_KEY and NOWPAYMENTS_EMAIL and NOWPAYMENTS_PASSWORD):
        await ctx.send("❌ Auto-payouts aren't configured yet. Ask an admin to set NOWPAYMENTS_EMAIL / NOWPAYMENTS_PASSWORD."); return

    # House bankroll safety: don't pay out if it'd drive the bankroll below the buffer.
    house_after = compute_house_bankroll_pts() - amount
    if house_after < HOUSE_MIN_BUFFER_PTS:
        await ctx.send(
            "⚠️ Withdrawal temporarily unavailable — the house bankroll is too low to cover this payout right now. "
            "Try a smaller amount or contact an admin."
        ); return

    usd_value = round(amount * POINTS_TO_USD, 2)

    notice = await ctx.send(f"⏳ Processing your withdrawal of **{amount:,} pts** (≈ ${usd_value:.2f})…")

    # ── ESCROW: deduct now, refund on failure ──
    set_user_balance(ctx.author.id, bal - amount)

    try:
        ltc_amount = await get_ltc_estimate(usd_value)
    except Exception as e:
        set_user_balance(ctx.author.id, get_user_balance(ctx.author.id) + amount)
        await notice.edit(content=f"❌ Couldn't price LTC right now ({e}). Your balance was not charged."); return

    try:
        ok, result = await create_payout(ctx.author.id, ltc_address, ltc_amount, usd_value)
    except Exception as e:
        ok, result = False, str(e)

    if not ok:
        # Refund
        set_user_balance(ctx.author.id, get_user_balance(ctx.author.id) + amount)
        await notice.edit(content=f"❌ Payout failed: `{result}`. Your **{amount:,} pts** were refunded.")
        return

    batch_id = str(result['batch_id'])
    withdrawals = result.get('withdrawals') or []
    np_payout_id = str(withdrawals[0]['id']) if withdrawals and 'id' in withdrawals[0] else batch_id

    # Persist record + bump total_withdrawn
    w = get_withdrawals()
    w[np_payout_id] = {
        'batch_id': batch_id,
        'user_id': str(ctx.author.id),
        'points': amount,
        'usd': usd_value,
        'ltc': ltc_amount,
        'address': ltc_address,
        'status': 'sending',
        'created': datetime.now(timezone.utc).isoformat(),
    }
    save_withdrawals(w)
    data, uid = get_user(ctx.author.id)
    data[uid]['total_withdrawn'] = data[uid].get('total_withdrawn', 0) + amount
    save_data(data)

    e = embed("✅ Withdrawal Sent", (
        f"**{amount:,} pts** (≈ **${usd_value:.2f}**) → `{ltc_amount:.8f} LTC`\n"
        f"To: `{ltc_address}`\n"
        f"Status: **sending** — usually confirms within a few minutes."),
        C.SUCCESS,
        footer=f"Payout ID: {np_payout_id}")
    await notice.edit(content=None, embed=e)

    # Optional admin log channel
    ch = bot.get_channel(WITHDRAW_CHANNEL_ID)
    if ch:
        log = embed("💸 Auto-Withdrawal Processed", None, C.SUCCESS)
        log.description = (
            f"**User:** {ctx.author.mention} (`{ctx.author.id}`)\n"
            f"**Amount:** {amount:,} pts  ·  ${usd_value:.2f}  ·  {ltc_amount:.8f} LTC\n"
            f"**Address:** `{ltc_address}`\n"
            f"**Payout ID:** `{np_payout_id}`")
        try: await ch.send(embed=log)
        except: pass


async def payout_watcher():
    """Poll NOWPayments for payout status, refund failures, mark completions."""
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            withdrawals = get_withdrawals()
            pending = [pid for pid, r in withdrawals.items()
                       if r.get('status') in ('sending', 'waiting', 'creating', 'processing')]
            if pending:
                jwt = await nowpayments_jwt()
                headers = {'x-api-key': NOWPAYMENTS_API_KEY,
                           'Authorization': f'Bearer {jwt}'}
                async with aiohttp.ClientSession() as session:
                    for pid in pending:
                        rec = withdrawals.get(pid)
                        if not rec: continue
                        try:
                            async with session.get(f"{NOWPAYMENTS_API}/payout/{pid}",
                                                   headers=headers,
                                                   timeout=aiohttp.ClientTimeout(total=20)) as resp:
                                data = await resp.json(content_type=None)
                        except Exception:
                            continue
                        status = (data.get('status') or '').lower() if isinstance(data, dict) else ''
                        if status in PAYOUT_DONE_STATES:
                            rec['status'] = 'finished'
                            rec['hash'] = data.get('hash')
                            rec['finished_at'] = datetime.now(timezone.utc).isoformat()
                            withdrawals[pid] = rec; save_withdrawals(withdrawals)
                        elif status in PAYOUT_DEAD_STATES:
                            # Refund the player & decrement total_withdrawn
                            rec['status'] = status
                            withdrawals[pid] = rec; save_withdrawals(withdrawals)
                            uid_int = int(rec['user_id'])
                            set_user_balance(uid_int, get_user_balance(uid_int) + int(rec['points']))
                            d, u = get_user(uid_int)
                            d[u]['total_withdrawn'] = max(0, d[u].get('total_withdrawn', 0) - int(rec['points']))
                            save_data(d)
                            try:
                                user = await bot.fetch_user(uid_int)
                                await user.send(
                                    f"⚠️ Your withdrawal of **{rec['points']:,} pts** failed on-chain "
                                    f"(`{status}`). The points have been refunded to your balance."
                                )
                            except Exception:
                                pass
        except Exception:
            pass
        await asyncio.sleep(60)



    
HELP_CATEGORIES = {
    "games": {
        "label": "🎮 Games",
        "description": "All casino games",
        "emoji": "🎮",
        "color": 0xE91E63,
        "lines": [
            "🪙 `.coinflip` / `.cf <amt> <h/t>` — Coin flip 1:1",
            "🎲 `.dice <amt> <1-6>` — Dice guess ×5",
            "📈 `.limbo <amt> <target>` — Beat your target multiplier",
            "🎰 `.slots <amt>` — Slots up to ×100",
            "🎡 `.roulette <amt> <r/b/e/o>` — Roulette ×2",
            "🃏 `.blackjack` / `.bj <amt>` — Hit, Stand, Double",
            "⛏️ `.mines <amt> [mines]` — Provably fair mines",
            "🚀 `.crash <amt>` — Multiplayer crash game",
            "🚀 `.crashroom <amt>` — Create a crash room (fixed entry)",
            "💎 `.jackpot` / `.jp <amt>` — Weighted jackpot pool",
            "✂️ `.rps <amt> <r/p/s>` — Rock-Paper-Scissors",
            "🎢 `.slide <amt> <target>` — Slider game",
            "#️⃣ `.ttt @user` — Tic Tac Toe vs another user",
            "🗜️ `.tight <amt>` — Random multiplier ×5 (96% RTP)",
            "🗼 `.tower <amt>` — Climb the tower",
            "💰 `.treasurehunt` / `.th <amt>` — Pick a chest, up to 2.5×",
            "🌀 `.twist <amt>` — Multiplier tiles via dice",
            "💘 `.valentines <amt>` — Valentine's Day slots",
            "⚔️ `.war <amt>` — Card war ×2",
        ],
    },
    "rewards": {
        "label": "🎁 Rewards",
        "description": "Daily, monthly, rakeback & codes",
        "emoji": "🎁",
        "color": 0xF1C40F,
        "lines": [
            "`.daily` — 5 pts free (24h cooldown)",
            "`.monthly` — 1pt per R$1,000 wagered",
            "`.rakeback` — Claim 0.2% of your losses",
            "`.code <CODE>` — Redeem a promo code",
        ],
    },
    "social": {
        "label": "🤝 Social",
        "description": "Tips, rain, clans & giveaways",
        "emoji": "🤝",
        "color": 0x2ECC71,
        "lines": [
            "`.send @user <amt>` — Send points",
            "`.rain <amt>` — Rain points on joiners (2 min)",
            "`.giveaway <amt> <mins> [wager:X] [invites:X]` — Admin giveaway",
            "`.clan <create/join/leave/info/top>` — Clan system",
            "`.thread` — Create a private thread",
            "`.invites [@user]` — Invite count",
        ],
    },
    "info": {
        "label": "📊 Info & Account",
        "description": "Balance, stats, deposits, leaderboards",
        "emoji": "📊",
        "color": 0x3498DB,
        "lines": [
            "`.games` — List every game",
            "`.deposit <usd>` — Get a unique LTC address (DM)",
            "`.withdraw <amt> <ltc_address>` — Auto LTC payout",
            "`.balance` / `.bal` — Your balance",
            "`.wager` — Wager requirement status",
            "`.stats [@user]` — Full profile & stats",
            "`.rank` — Rank progress",
            "`.leaderboard` / `.lb` — Top 10 players",
            "`.price` — Points price table",
        ],
    },
    "admin": {
        "label": "🛡️ Admin",
        "description": "Administrator commands",
        "emoji": "🛡️",
        "color": 0xE74C3C,
        "lines": [
            "`.addbal @user <amt>` — Add balance",
            "`.removebal @user <amt>` — Remove balance",
            "`.promo @user <amt>` — Points + wager requirement",
            "`.clearwager @user` — Clear wager requirement",
            "`.wagerstatus @user` — Check wager progress",
            "`.updwithdraw @user <amt>` — Bump withdraw total",
            "`.updatedeposit @user <usd>` — Bump deposit total",
            "`.resetstats` — Reset all player stats",
            "`.housebal` / `.bankroll` — House bankroll report",
            "`.resethouse [scope]` — Reset house stats",
            "`.setrank <rank> @role` — Link rank to role",
            "`.rankroles` — View rank→role config",
            "`.sethistory #channel` — Log every bet result",
            "`.clearhistory` — Disable bet history",
            "`.setdepositlog #channel` — Log deposits",
            "`.cleardepositlog` — Disable deposit log",
            "`.addcode <CODE> <pts> <uses> <days> [req]` — Create code",
            "`.delcode <CODE>` — Delete a code",
            "`.codes` — List active codes",
        ],
    },
}


def _help_home_embed():
    e = embed(
        "🎰 LuckyBet — Help",
        "Select a category from the dropdown to browse commands.\n\u200b",
        color=C.LOBBY,
    )
    for c in HELP_CATEGORIES.values():
        e.add_field(name=f"{c['emoji']} {c['label'].split(' ', 1)[1]}",
                     value=c['description'], inline=False)
    return e


def _help_category_embed(key):
    cat = HELP_CATEGORIES[key]
    e = embed(
        f"{cat['emoji']} {cat['label'].split(' ', 1)[1]} — Commands",
        "\n".join(cat["lines"]),
        color=cat["color"],
    )
    return e


class HelpView(discord.ui.View):
    def __init__(self, author_id):
        super().__init__(timeout=120)
        self.author_id = author_id
        self.add_item(HelpSelect())

    async def interaction_check(self, interaction):
        if interaction.user.id != self.author_id:
            await interaction.response.send_message(
                "❌ Only the user who ran `.help` can use this menu.", ephemeral=True
            )
            return False
        return True

    @discord.ui.button(label="Home", style=discord.ButtonStyle.secondary, emoji="🏠", row=1)
    async def home(self, interaction, button):
        await interaction.response.edit_message(embed=_help_home_embed(), view=self)


class HelpSelect(discord.ui.Select):
    def __init__(self):
        options = [
            discord.SelectOption(
                label=cat["label"].split(" ", 1)[1],
                description=cat["description"][:100],
                emoji=cat["emoji"],
                value=key,
            )
            for key, cat in HELP_CATEGORIES.items()
        ]
        super().__init__(placeholder="📂 Select a category…", options=options, min_values=1, max_values=1)

    async def callback(self, interaction):
        await interaction.response.edit_message(
            embed=_help_category_embed(self.values[0]), view=self.view
        )


@bot.command(name='help')
async def help_command(ctx, *, category: str = None):
    # Allow direct shortcut: .help games
    if category:
        key = category.lower().strip()
        if key in HELP_CATEGORIES:
            return await ctx.send(embed=_help_category_embed(key), view=HelpView(ctx.author.id))
    await ctx.send(embed=_help_home_embed(), view=HelpView(ctx.author.id))



def _format_usage(command):
    """Return a `.cmd <args>` usage string built from the command's signature."""
    prefix = '.'
    name = command.qualified_name
    sig = command.signature  # discord.py auto-builds "<arg> [opt]" style
    aliases = ""
    if command.aliases:
        aliases = f"  ·  aliases: {', '.join('.' + a for a in command.aliases)}"
    line = f"`{prefix}{name}{(' ' + sig) if sig else ''}`{aliases}"
    if command.help:
        line += f"\n{command.help.strip().splitlines()[0]}"
    return line


def _suggest_command(name):
    """Find the closest known command/alias to a mistyped name."""
    import difflib
    pool = []
    for c in bot.commands:
        pool.append(c.name); pool.extend(c.aliases)
    matches = difflib.get_close_matches(name.lower(), pool, n=1, cutoff=0.6)
    return matches[0] if matches else None


@bot.event
async def on_command_error(ctx, error):
    # Unwrap CommandInvokeError to get the real cause
    err = getattr(error, 'original', error)

    # Wrong/unknown command → suggest closest + show its usage
    if isinstance(error, commands.CommandNotFound):
        typed = ctx.message.content.lstrip('.').split()[0] if ctx.message.content else ''
        suggestion = _suggest_command(typed)
        if suggestion:
            cmd = bot.get_command(suggestion)
            if cmd:
                await ctx.send(
                    f"❓ Unknown command `.{typed}`. Did you mean:\n"
                    f"➡️ {_format_usage(cmd)}"
                ); return
        await ctx.send(f"❓ Unknown command `.{typed}`. Try `.help` for a list of commands.")
        return

    # Missing / bad arguments → show that command's correct usage
    if isinstance(error, (commands.MissingRequiredArgument,
                          commands.BadArgument,
                          commands.TooManyArguments,
                          commands.MemberNotFound,
                          commands.UserNotFound,
                          commands.ChannelNotFound,
                          commands.RoleNotFound,
                          commands.BadUnionArgument)) and ctx.command:
        await ctx.send(f"💡 **Usage:** {_format_usage(ctx.command)}")
        return

    # Permission / cooldown messages stay friendly
    if isinstance(error, commands.MissingPermissions):
        await ctx.send("🔒 You don't have permission to use that command."); return
    if isinstance(error, commands.BotMissingPermissions):
        await ctx.send("🔒 I don't have the permissions needed for that command."); return
    if isinstance(error, commands.CommandOnCooldown):
        await ctx.send(f"⏳ Slow down — try again in {error.retry_after:.1f}s."); return
    if isinstance(error, commands.NoPrivateMessage):
        await ctx.send("📭 That command can only be used in a server."); return
    if isinstance(error, commands.CheckFailure):
        await ctx.send("🚫 You can't use that command here."); return

    # Anything else → log to console, give the user a clean message
    print(f"ERROR IN COMMAND {ctx.command}: {repr(err)}")
    if ctx.command:
        await ctx.send(f"⚠️ Something went wrong running `.{ctx.command.qualified_name}`. "
                       f"Usage: {_format_usage(ctx.command)}")
    else:
        await ctx.send("⚠️ Something went wrong. Try `.help` for the command list.")

if __name__ == "__main__":
    TOKEN = os.getenv('DISCORD_TOKEN')
    if not TOKEN: print("❌ DISCORD_TOKEN not set!")
    else: bot.run(TOKEN)
