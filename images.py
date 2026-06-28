"""
Discord casino-style image generation for the bot.

All cards are rendered with a deep felt background, gold/neon accents,
drop shadows, and hand-drawn game assets (cards, slot symbols, dice,
roulette wheel, coins). Public function signatures match what bot.py
expects, so this file is a drop-in replacement.

Required: Pillow (PIL).  Optional: a color emoji font (e.g. Noto Color Emoji)
installed system-wide if you want emoji in titles to render in color.
"""

from __future__ import annotations

import io
import math
import os
import random
from typing import Iterable, List, Optional, Sequence, Tuple

from PIL import Image, ImageDraw, ImageFilter, ImageFont

# ---------------------------------------------------------------------------
# Palette  (Discord-dark casino: deep navy felt + neon gold/red/green accents)
# ---------------------------------------------------------------------------

BG_TOP        = (19,  22,  34)     # near-black navy
BG_BOTTOM     = (11,  13,  20)
FELT_TOP      = (14,  78,  55)     # casino green felt
FELT_BOTTOM   = ( 6,  40,  28)
PANEL_TOP     = (33,  37,  54)
PANEL_BOTTOM  = (22,  25,  38)
GOLD          = (235, 192,  78)
GOLD_DARK     = (158, 118,  28)
RED           = (224,  62,  82)
RED_DARK      = (132,  22,  36)
GREEN         = ( 72, 199, 116)
GREEN_DARK    = ( 24, 110,  58)
WHITE         = (245, 247, 255)
MUTED         = (160, 168, 192)
BLACK         = ( 10,  10,  14)
NEON_BLUE     = ( 88, 165, 255)

CARD_W, CARD_H = 900, 520

# ---------------------------------------------------------------------------
# Font loading
# ---------------------------------------------------------------------------

_FONT_CANDIDATES = [
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/Library/Fonts/Arial Bold.ttf",
    "C:/Windows/Fonts/arialbd.ttf",
    "C:/Windows/Fonts/arial.ttf",
]
_EMOJI_CANDIDATES = [
    "/usr/share/fonts/truetype/noto/NotoColorEmoji.ttf",
    "/System/Library/Fonts/Apple Color Emoji.ttc",
    "C:/Windows/Fonts/seguiemj.ttf",
]


def _find(paths: Iterable[str]) -> Optional[str]:
    for p in paths:
        if os.path.exists(p):
            return p
    return None


_FONT_PATH = _find(_FONT_CANDIDATES)
_EMOJI_PATH = _find(_EMOJI_CANDIDATES)


def font(size: int, bold: bool = True) -> ImageFont.FreeTypeFont:
    if _FONT_PATH:
        try:
            return ImageFont.truetype(_FONT_PATH, size)
        except Exception:
            pass
    return ImageFont.load_default()


# ---------------------------------------------------------------------------
# Primitives
# ---------------------------------------------------------------------------

def vgradient(size: Tuple[int, int],
              top: Tuple[int, int, int],
              bottom: Tuple[int, int, int]) -> Image.Image:
    w, h = size
    img = Image.new("RGB", (1, h))
    px = img.load()
    for y in range(h):
        t = y / max(1, h - 1)
        px[0, y] = (
            int(top[0] + (bottom[0] - top[0]) * t),
            int(top[1] + (bottom[1] - top[1]) * t),
            int(top[2] + (bottom[2] - top[2]) * t),
        )
    return img.resize((w, h))


def rounded_rect(draw: ImageDraw.ImageDraw, xy, radius: int, fill=None, outline=None, width: int = 1):
    draw.rounded_rectangle(xy, radius=radius, fill=fill, outline=outline, width=width)


def drop_shadow(base: Image.Image, mask: Image.Image,
                offset: Tuple[int, int] = (0, 6), blur: int = 12,
                color: Tuple[int, int, int] = (0, 0, 0), alpha: int = 140) -> None:
    shadow = Image.new("RGBA", base.size, (0, 0, 0, 0))
    sd = ImageDraw.Draw(shadow)
    sd.bitmap((0, 0), mask, fill=(*color, alpha))
    shadow = shadow.filter(ImageFilter.GaussianBlur(blur))
    base.alpha_composite(shadow, dest=offset)


def neon_text(img: Image.Image, xy: Tuple[int, int], text: str,
              fnt: ImageFont.ImageFont,
              fill=(255, 255, 255), glow=GOLD, glow_alpha: int = 180, blur: int = 6):
    layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(layer)
    d.text(xy, text, font=fnt, fill=(*glow, glow_alpha))
    layer = layer.filter(ImageFilter.GaussianBlur(blur))
    img.alpha_composite(layer)
    ImageDraw.Draw(img).text(xy, text, font=fnt, fill=fill)


def felt_panel(size: Tuple[int, int], radius: int = 28) -> Image.Image:
    w, h = size
    panel = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    base = vgradient((w, h), FELT_TOP, FELT_BOTTOM).convert("RGBA")
    mask = Image.new("L", (w, h), 0)
    ImageDraw.Draw(mask).rounded_rectangle((0, 0, w, h), radius=radius, fill=255)
    panel.paste(base, (0, 0), mask)

    # subtle felt noise
    noise = Image.effect_noise((w, h), 8).convert("L")
    noise = noise.filter(ImageFilter.GaussianBlur(0.6))
    tint = Image.new("RGBA", (w, h), (255, 255, 255, 0))
    ImageDraw.Draw(tint).bitmap((0, 0), noise, fill=(255, 255, 255, 14))
    panel.alpha_composite(tint)

    # gold rim
    d = ImageDraw.Draw(panel)
    d.rounded_rectangle((1, 1, w - 2, h - 2), radius=radius - 1,
                        outline=GOLD_DARK, width=2)
    d.rounded_rectangle((4, 4, w - 5, h - 5), radius=radius - 4,
                        outline=(GOLD[0], GOLD[1], GOLD[2], 90), width=1)
    return panel


def base_canvas(title: str, subtitle: str = "") -> Tuple[Image.Image, ImageDraw.ImageDraw]:
    img = vgradient((CARD_W, CARD_H), BG_TOP, BG_BOTTOM).convert("RGBA")
    d = ImageDraw.Draw(img)

    # header bar
    rounded_rect(d, (24, 20, CARD_W - 24, 92), 18,
                 fill=(PANEL_TOP[0], PANEL_TOP[1], PANEL_TOP[2], 230),
                 outline=GOLD_DARK, width=2)
    neon_text(img, (44, 32), title, font(34, True), fill=GOLD, glow=GOLD, glow_alpha=140, blur=8)
    if subtitle:
        d.text((44, 70), subtitle, font=font(16, False), fill=MUTED)

    # corner chip decorations
    _draw_chip(img, (CARD_W - 70, 56), 22, RED, WHITE)
    return img, d


def _banner(img: Image.Image, text: str, color: Tuple[int, int, int],
            y: int = CARD_H - 90):
    d = ImageDraw.Draw(img)
    w = CARD_W - 80
    box = (40, y, 40 + w, y + 60)
    rounded_rect(d, box, 16,
                 fill=(color[0] // 4, color[1] // 4, color[2] // 4, 220),
                 outline=color, width=2)
    tw = d.textlength(text, font=font(26, True))
    neon_text(img, (int((CARD_W - tw) / 2), y + 14), text,
              font(26, True), fill=WHITE, glow=color, glow_alpha=200, blur=10)


# ---------------------------------------------------------------------------
# Casino assets
# ---------------------------------------------------------------------------

def _draw_chip(img: Image.Image, center: Tuple[int, int], r: int,
               color: Tuple[int, int, int], stripe: Tuple[int, int, int]):
    d = ImageDraw.Draw(img)
    cx, cy = center
    # shadow
    sh = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(sh).ellipse((cx - r, cy - r + 4, cx + r, cy + r + 4),
                               fill=(0, 0, 0, 120))
    img.alpha_composite(sh.filter(ImageFilter.GaussianBlur(6)))
    # body
    d.ellipse((cx - r, cy - r, cx + r, cy + r), fill=color, outline=BLACK, width=2)
    # stripes
    for ang in range(0, 360, 45):
        a = math.radians(ang)
        x1 = cx + math.cos(a) * (r - 2)
        y1 = cy + math.sin(a) * (r - 2)
        x2 = cx + math.cos(a) * (r - 10)
        y2 = cy + math.sin(a) * (r - 10)
        d.line((x1, y1, x2, y2), fill=stripe, width=4)
    # inner disc
    ir = int(r * 0.55)
    d.ellipse((cx - ir, cy - ir, cx + ir, cy + ir),
              fill=(color[0] // 2, color[1] // 2, color[2] // 2), outline=stripe, width=2)


SUITS = {
    "S": ("\u2660", BLACK),   # ♠
    "C": ("\u2663", BLACK),   # ♣
    "H": ("\u2665", RED_DARK),  # ♥
    "D": ("\u2666", RED_DARK),  # ♦
}


def _parse_card(code: str) -> Tuple[str, str]:
    """Accepts 'AS', '10H', 'KD', numeric blackjack values, etc."""
    if isinstance(code, int):
        rank = "A" if code == 11 else str(code)
        return (rank, "S")
    code = str(code).strip().upper()
    if not code:
        return ("?", "S")
    # suit unicode -> letter
    for letter, (sym, _) in SUITS.items():
        if code.endswith(sym):
            return (code[:-1] or "?", letter)
    suit = code[-1]
    if suit not in SUITS:
        suit = "S"
    rank = code[:-1] or "?"
    if rank == "T":
        rank = "10"
    return (rank, suit)


def _draw_playing_card(img: Image.Image, top_left: Tuple[int, int],
                       code: str, w: int = 110, h: int = 156, hidden: bool = False):
    x, y = top_left
    card = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    cd = ImageDraw.Draw(card)

    # shadow
    sh_mask = Image.new("L", (w, h), 0)
    ImageDraw.Draw(sh_mask).rounded_rectangle((0, 0, w, h), radius=12, fill=255)
    drop_shadow(img, sh_mask.transform(img.size, Image.AFFINE,
                                       (1, 0, -x, 0, 1, -y)),
                offset=(0, 8), blur=10, alpha=160)

    if hidden:
        cd.rounded_rectangle((0, 0, w, h), radius=12,
                             fill=(40, 50, 90), outline=GOLD, width=2)
        # diamond lattice back
        for i in range(-h, w + h, 14):
            cd.line((i, 0, i + h, h), fill=(70, 90, 150), width=1)
            cd.line((i, h, i + h, 0), fill=(70, 90, 150), width=1)
        cd.rounded_rectangle((6, 6, w - 6, h - 6), radius=10,
                             outline=GOLD_DARK, width=2)
        img.alpha_composite(card, dest=(x, y))
        return

    cd.rounded_rectangle((0, 0, w, h), radius=12, fill=WHITE,
                         outline=(180, 180, 195), width=2)

    rank, suit = _parse_card(code)
    sym, color = SUITS[suit]

    rank_font = font(26, True)
    suit_font = font(22, True)
    big_font  = font(60, True)

    # top-left index
    cd.text((8, 4), rank, font=rank_font, fill=color)
    cd.text((10, 32), sym, font=suit_font, fill=color)
    # bottom-right index (rotated by drawing on a tile and pasting)
    corner = Image.new("RGBA", (40, 60), (0, 0, 0, 0))
    ImageDraw.Draw(corner).text((2, 0), rank, font=rank_font, fill=color)
    ImageDraw.Draw(corner).text((4, 28), sym, font=suit_font, fill=color)
    corner = corner.rotate(180)
    card.alpha_composite(corner, dest=(w - 42, h - 62))

    # center pip
    tw = cd.textlength(sym, font=big_font)
    cd.text(((w - tw) / 2, h / 2 - 40), sym, font=big_font, fill=color)

    img.alpha_composite(card, dest=(x, y))


# ---------- Slots ----------

SLOT_SYMBOLS = ["apple", "orange", "lemon", "banana", "cherry", "bell", "star", "seven", "diamond"]
SLOT_EMOJI_MAP = {
    "🍎": "apple",
    "🍒": "cherry",
    "🍊": "orange",
    "🍋": "lemon",
    "🍌": "banana",
    "⭐": "star",
    "🌟": "star",
    "7️⃣": "seven",
    "💎": "diamond",
}


def _slot_kind(kind: str) -> str:
    text = str(kind).strip().lower()
    return SLOT_EMOJI_MAP.get(str(kind).strip(), text if text in SLOT_SYMBOLS else "seven")


def _draw_slot_symbol(img: Image.Image, center: Tuple[int, int], size: int, kind: str):
    d = ImageDraw.Draw(img)
    kind = _slot_kind(kind)
    cx, cy = center
    r = size // 2
    if kind == "apple":
        d.ellipse((cx - r, cy - int(r * 0.85), cx + r, cy + r), fill=RED, outline=BLACK, width=2)
        d.ellipse((cx - r // 3, cy - r, cx + r // 3, cy - r // 2), fill=(60, 150, 65), outline=BLACK, width=1)
        d.line((cx, cy - r, cx + r // 4, cy - r - 16), fill=(100, 70, 35), width=4)
    elif kind == "orange":
        d.ellipse((cx - r, cy - r, cx + r, cy + r), fill=(245, 135, 35), outline=(150, 70, 20), width=2)
        d.arc((cx - r // 2, cy - r // 3, cx + r // 2, cy + r // 2), 20, 210, fill=(255, 190, 80), width=4)
        d.ellipse((cx - 8, cy - r + 8, cx + 8, cy - r + 24), fill=(70, 160, 70), outline=BLACK, width=1)
    elif kind == "cherry":
        d.ellipse((cx - r, cy - 4, cx - 4, cy + r), fill=RED, outline=BLACK, width=2)
        d.ellipse((cx + 4, cy - 4, cx + r, cy + r), fill=RED, outline=BLACK, width=2)
        d.line((cx - r // 2, cy - 4, cx, cy - r), fill=(40, 110, 40), width=3)
        d.line((cx + r // 2, cy - 4, cx, cy - r), fill=(40, 110, 40), width=3)
    elif kind == "lemon":
        d.ellipse((cx - r, cy - int(r * 0.7), cx + r, cy + int(r * 0.7)),
                  fill=(245, 210, 70), outline=(150, 120, 20), width=2)
    elif kind == "banana":
        d.arc((cx - r, cy - r, cx + r, cy + r), 30, 170, fill=(245, 210, 70), width=max(10, r // 3))
        d.arc((cx - r + 10, cy - r + 16, cx + r - 10, cy + r - 8), 30, 170, fill=(150, 110, 30), width=3)
        d.ellipse((cx - r + 6, cy - 6, cx - r + 20, cy + 8), fill=(100, 70, 35))
    elif kind == "bell":
        d.pieslice((cx - r, cy - r, cx + r, cy + r), 180, 360,
                   fill=GOLD, outline=GOLD_DARK, width=2)
        d.rectangle((cx - r, cy - 2, cx + r, cy + 6),
                    fill=GOLD, outline=GOLD_DARK, width=2)
        d.ellipse((cx - 5, cy + 6, cx + 5, cy + 14), fill=GOLD_DARK)
    elif kind == "star":
        pts = []
        for i in range(10):
            ang = -math.pi / 2 + i * math.pi / 5
            rad = r if i % 2 == 0 else r // 2
            pts.append((cx + math.cos(ang) * rad, cy + math.sin(ang) * rad))
        d.polygon(pts, fill=GOLD, outline=GOLD_DARK)
    elif kind == "seven":
        d.text((cx - r + 4, cy - r), "7", font=font(size + 4, True), fill=RED)
    elif kind == "diamond":
        pts = [(cx, cy - r), (cx + r, cy), (cx, cy + r), (cx - r, cy)]
        d.polygon(pts, fill=NEON_BLUE, outline=WHITE)
        d.line((cx - r, cy, cx + r, cy), fill=WHITE, width=1)
        d.line((cx, cy - r, cx, cy + r), fill=WHITE, width=1)


# ---------- Coin / Dice ----------

def _draw_coin(img: Image.Image, center: Tuple[int, int], r: int, face: str):
    d = ImageDraw.Draw(img)
    cx, cy = center
    sh = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(sh).ellipse((cx - r, cy - r + 8, cx + r, cy + r + 8),
                               fill=(0, 0, 0, 150))
    img.alpha_composite(sh.filter(ImageFilter.GaussianBlur(10)))

    # rim
    d.ellipse((cx - r, cy - r, cx + r, cy + r), fill=GOLD_DARK)
    d.ellipse((cx - r + 6, cy - r + 4, cx + r - 6, cy + r - 8), fill=GOLD)
    # highlight
    hl = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(hl).ellipse((cx - r + 14, cy - r + 10, cx + 4, cy),
                               fill=(255, 255, 255, 90))
    img.alpha_composite(hl.filter(ImageFilter.GaussianBlur(8)))

    label = "H" if face.upper().startswith("H") else "T"
    f = font(int(r * 1.1), True)
    tw = d.textlength(label, font=f)
    d.text((cx - tw / 2, cy - r * 0.75), label, font=f, fill=GOLD_DARK)


def draw_die(img: Image.Image, top_left: Tuple[int, int], size: int, pips: int):
    x, y = top_left
    d = ImageDraw.Draw(img)
    # shadow
    sh = Image.new("L", img.size, 0)
    ImageDraw.Draw(sh).rounded_rectangle((x, y + 6, x + size, y + size + 6),
                                         radius=14, fill=255)
    sh_img = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(sh_img).bitmap((0, 0), sh, fill=(0, 0, 0, 160))
    img.alpha_composite(sh_img.filter(ImageFilter.GaussianBlur(8)))

    d.rounded_rectangle((x, y, x + size, y + size), radius=14,
                        fill=WHITE, outline=(180, 180, 200), width=2)
    # subtle top highlight
    d.rounded_rectangle((x + 4, y + 4, x + size - 4, y + size // 3),
                        radius=10, fill=(255, 255, 255, 0),
                        outline=(220, 230, 245), width=1)

    pr = max(6, size // 14)
    cx = x + size // 2
    cy = y + size // 2
    off = size // 4
    spots = {
        1: [(cx, cy)],
        2: [(x + off, y + off), (x + size - off, y + size - off)],
        3: [(x + off, y + off), (cx, cy), (x + size - off, y + size - off)],
        4: [(x + off, y + off), (x + size - off, y + off),
            (x + off, y + size - off), (x + size - off, y + size - off)],
        5: [(x + off, y + off), (x + size - off, y + off), (cx, cy),
            (x + off, y + size - off), (x + size - off, y + size - off)],
        6: [(x + off, y + off), (x + size - off, y + off),
            (x + off, cy), (x + size - off, cy),
            (x + off, y + size - off), (x + size - off, y + size - off)],
    }.get(pips, [(cx, cy)])
    for (sx, sy) in spots:
        d.ellipse((sx - pr, sy - pr, sx + pr, sy + pr), fill=BLACK)


# ---------------------------------------------------------------------------
# Card composition helpers
# ---------------------------------------------------------------------------

def _save(img: Image.Image) -> bytes:
    buf = io.BytesIO()
    img.convert("RGB").save(buf, format="PNG", optimize=True)
    return buf.getvalue()


# ---------------------------------------------------------------------------
# Public API  (matches bot.py expectations)
# ---------------------------------------------------------------------------

def balance_card(username: str, balance: int, currency: str = "chips") -> bytes:
    img, d = base_canvas("\u2660 CASINO WALLET", f"Player: {username}")

    panel = felt_panel((CARD_W - 80, 320))
    img.alpha_composite(panel, dest=(40, 130))

    # chip stacks decoration
    for i, color in enumerate([RED, NEON_BLUE, GREEN, GOLD]):
        _draw_chip(img, (140 + i * 70, 360), 28, color, WHITE)

    label_font = font(22, False)
    big = font(78, True)
    d.text((CARD_W // 2 + 40, 180), "BALANCE", font=label_font, fill=MUTED)
    amount = f"{balance:,}"
    neon_text(img, (CARD_W // 2 + 40, 210), amount, big,
              fill=GOLD, glow=GOLD, glow_alpha=200, blur=10)
    d.text((CARD_W // 2 + 40, 310), currency.upper(),
           font=font(20, True), fill=GREEN)

    return _save(img)


def blackjack_card(player_hand: Sequence[str], dealer_hand: Sequence[str],
                   player_total: int, dealer_total: int,
                   bet: int, status: str = "playing",
                   hide_dealer: bool = False) -> bytes:
    img, d = base_canvas("\u2663 BLACKJACK", f"Bet: {bet:,} chips")
    panel = felt_panel((CARD_W - 80, 400))
    img.alpha_composite(panel, dest=(40, 110))

    d.text((70, 130), f"DEALER  \u2014  {('?' if hide_dealer else dealer_total)}",
           font=font(20, True), fill=MUTED)
    for i, c in enumerate(dealer_hand):
        hidden = hide_dealer and i == 1
        _draw_playing_card(img, (70 + i * 80, 160), c, hidden=hidden)

    d.text((70, 340), f"YOU  \u2014  {player_total}",
           font=font(20, True), fill=WHITE)
    for i, c in enumerate(player_hand):
        _draw_playing_card(img, (70 + i * 80, 370), c, w=90, h=126)

    if status == "win":
        _banner(img, "YOU WIN!", GREEN)
    elif status == "lose":
        _banner(img, "DEALER WINS", RED)
    elif status == "push":
        _banner(img, "PUSH", GOLD)
    elif status == "blackjack":
        _banner(img, "BLACKJACK!", GOLD)
    elif status == "bust":
        _banner(img, "BUST", RED)
    return _save(img)


def slots_card(reels: Sequence[str], bet: int, payout: int,
               username: str = "", match_label: str = "") -> bytes:
    img, d = base_canvas("\u2728 SLOTS", f"{username}  \u00b7  Bet {bet:,}")
    panel = felt_panel((CARD_W - 80, 320))
    img.alpha_composite(panel, dest=(40, 130))

    slot_w, slot_h = 200, 220
    gap = 30
    total_w = slot_w * 3 + gap * 2
    start_x = (CARD_W - total_w) // 2
    y = 180
    for i in range(3):
        sx = start_x + i * (slot_w + gap)
        rounded_rect(d, (sx, y, sx + slot_w, y + slot_h), 18,
                     fill=(18, 22, 32), outline=GOLD, width=3)
        # inner bevel
        rounded_rect(d, (sx + 6, y + 6, sx + slot_w - 6, y + slot_h - 6), 14,
                     outline=GOLD_DARK, width=1)
        sym = reels[i] if i < len(reels) else "seven"
        _draw_slot_symbol(img, (sx + slot_w // 2, y + slot_h // 2), 110, sym)

    if match_label:
        label_font = font(22, True)
        label_text = f"MATCHES: {match_label.upper()}"
        tw = d.textlength(label_text, font=label_font)
        rounded_rect(d, (int((CARD_W - tw) / 2) - 22, 418, int((CARD_W + tw) / 2) + 22, 462), 14,
                     fill=(18, 22, 32, 230), outline=GOLD_DARK, width=2)
        d.text(((CARD_W - tw) / 2, 428), label_text, font=label_font, fill=GOLD if payout > 0 else MUTED)

    if payout > 0:
        _banner(img, f"WIN  +{payout:,}", GREEN, y=CARD_H - 72)
    else:
        _banner(img, f"LOSS  -{bet:,}", RED, y=CARD_H - 72)
    return _save(img)


def roulette_card(number: int, color: str, bet: int, payout: int,
                  pick: str = "") -> bytes:
    img, d = base_canvas("\u25CF ROULETTE",
                         f"Bet {bet:,}  on  {pick or color.upper()}")
    panel = felt_panel((CARD_W - 80, 380))
    img.alpha_composite(panel, dest=(40, 110))

    # wheel
    cx, cy, r = 230, 310, 150
    # outer gold rim
    d.ellipse((cx - r - 14, cy - r - 14, cx + r + 14, cy + r + 14),
              fill=GOLD_DARK)
    d.ellipse((cx - r - 8, cy - r - 8, cx + r + 8, cy + r + 8),
              fill=GOLD)
    # 37 segments (0 green, alternating red/black)
    seg = 360 / 37
    for i in range(37):
        if i == 0:
            seg_color = GREEN_DARK
        else:
            seg_color = RED_DARK if i % 2 == 1 else BLACK
        d.pieslice((cx - r, cy - r, cx + r, cy + r),
                   start=i * seg - 90, end=(i + 1) * seg - 90,
                   fill=seg_color, outline=GOLD_DARK)
    # hub
    d.ellipse((cx - 30, cy - 30, cx + 30, cy + 30), fill=GOLD,
              outline=GOLD_DARK, width=2)
    # pointer
    d.polygon([(cx, cy - r - 22), (cx - 14, cy - r - 4), (cx + 14, cy - r - 4)],
              fill=WHITE, outline=BLACK)

    # result box
    bx, by = 430, 180
    rounded_rect(d, (bx, by, bx + 420, by + 220), 18,
                 fill=(18, 22, 32, 220), outline=GOLD, width=2)
    d.text((bx + 24, by + 16), "RESULT", font=font(20, True), fill=MUTED)
    rc = GREEN if color == "green" else (RED if color == "red" else (40, 40, 50))
    d.ellipse((bx + 24, by + 56, bx + 144, by + 176), fill=rc,
              outline=GOLD, width=3)
    nt = str(number)
    nf = font(64, True)
    tw = d.textlength(nt, font=nf)
    d.text((bx + 84 - tw / 2, by + 86), nt, font=nf, fill=WHITE)
    d.text((bx + 170, by + 70), color.upper(), font=font(28, True),
           fill=rc if rc != (40, 40, 50) else WHITE)
    payout_color = GREEN if payout > 0 else RED
    sign = "+" if payout > 0 else ""
    d.text((bx + 170, by + 120), f"{sign}{payout:,}",
           font=font(36, True), fill=payout_color)

    return _save(img)


def dice_card(rolls: Sequence[int], bet: int, payout: int,
              pick: Optional[int] = None) -> bytes:
    img, d = base_canvas("\u2684 DICE", f"Bet {bet:,}"
                         + (f"  on  {pick}" if pick else ""))
    panel = felt_panel((CARD_W - 80, 320))
    img.alpha_composite(panel, dest=(40, 130))

    size = 150
    gap = 40
    total = len(rolls) * size + (len(rolls) - 1) * gap
    start = (CARD_W - total) // 2
    for i, v in enumerate(rolls):
        draw_die(img, (start + i * (size + gap), 200), size, int(v))

    if payout > 0:
        _banner(img, f"WIN  +{payout:,}  (rolled {sum(rolls)})", GREEN)
    else:
        _banner(img, f"LOSS  -{bet:,}  (rolled {sum(rolls)})", RED)
    return _save(img)


def coinflip_card(result: str, pick: str, bet: int, payout: int) -> bytes:
    img, d = base_canvas("\u25CE COIN FLIP",
                         f"Bet {bet:,}  on  {pick.upper()}")
    panel = felt_panel((CARD_W - 80, 320))
    img.alpha_composite(panel, dest=(40, 130))

    _draw_coin(img, (CARD_W // 2, 280), 110, result)
    d.text((CARD_W // 2 - 60, 410), f"Landed: {result.upper()}",
           font=font(22, True), fill=WHITE)

    if payout > 0:
        _banner(img, f"WIN  +{payout:,}", GREEN)
    else:
        _banner(img, f"LOSS  -{bet:,}", RED)
    return _save(img)


def coinflip_anim_card(result: str, pick: str, bet: int, payout: int) -> bytes:
    """Animated coin flip GIF used by bot.py.

    Returns GIF bytes with the same arguments as coinflip_card, so importing
    coinflip_anim_card will work even when the bot sends an animated preview.
    """
    frames: List[Image.Image] = []
    total_frames = 18
    final_face = "H" if str(result).upper().startswith("H") else "T"

    for i in range(total_frames):
        t = i / (total_frames - 1)
        img, d = base_canvas("\u25CE COIN FLIP", f"Bet {bet:,}  on  {pick.upper()}")
        panel = felt_panel((CARD_W - 80, 320))
        img.alpha_composite(panel, dest=(40, 130))

        # A fast rotating/squashing coin that settles on the final result.
        angle = t * math.pi * 7
        cx, cy = CARD_W // 2, 280
        r = 110
        squash = max(0.12, abs(math.cos(angle)))
        coin_w = max(16, int(r * 2 * squash))
        show_final = i > total_frames * 0.65
        label = final_face if show_final else ("H" if i % 2 == 0 else "T")

        shadow = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ImageDraw.Draw(shadow).ellipse((cx - coin_w // 2, cy + r - 10,
                                        cx + coin_w // 2, cy + r + 18),
                                       fill=(0, 0, 0, 120))
        img.alpha_composite(shadow.filter(ImageFilter.GaussianBlur(10)))

        d.ellipse((cx - coin_w // 2, cy - r, cx + coin_w // 2, cy + r),
                  fill=GOLD_DARK, outline=BLACK, width=2)
        d.ellipse((cx - max(8, coin_w // 2 - 7), cy - r + 7,
                   cx + max(8, coin_w // 2 - 7), cy + r - 10),
                  fill=GOLD, outline=GOLD_DARK, width=2)

        if coin_w > 55:
            f = font(int(r * 0.95), True)
            tw = d.textlength(label, font=f)
            d.text((cx - tw / 2, cy - r * 0.68), label, font=f, fill=GOLD_DARK)

        d.text((CARD_W // 2 - 72, 410), f"Flipping... {pick.upper()}",
               font=font(22, True), fill=WHITE)
        frames.append(img.convert("P", palette=Image.Palette.ADAPTIVE))

    # Hold the final static result for a short moment at the end.
    final_img = Image.open(io.BytesIO(coinflip_card(result, pick, bet, payout))).convert(
        "P", palette=Image.Palette.ADAPTIVE
    )
    frames.extend([final_img] * 8)

    buf = io.BytesIO()
    frames[0].save(buf, format="GIF", save_all=True, append_images=frames[1:],
                   duration=70, loop=0, optimize=False, disposal=2)
    return buf.getvalue()



# ---------------------------------------------------------------------------
# Additional game cards
# ---------------------------------------------------------------------------

def _result_banner(img: Image.Image, payout: int, bet: int,
                   extra: str = "") -> None:
    if payout > 0:
        _banner(img, f"WIN  +{payout:,}" + (f"  {extra}" if extra else ""), GREEN)
    elif payout < 0:
        _banner(img, f"LOSS  {payout:,}" + (f"  {extra}" if extra else ""), RED)
    else:
        _banner(img, f"LOSS  -{bet:,}" + (f"  {extra}" if extra else ""), RED)


def addbal_card(username: str, amount: int, new_balance: int,
                currency: str = "chips", **_kwargs) -> bytes:
    """Admin / reward balance-change card."""
    sign = "+" if amount >= 0 else ""
    img, d = base_canvas("\u2728 BALANCE UPDATED", f"@{username}")
    panel = felt_panel((CARD_W - 80, 360))
    img.alpha_composite(panel, dest=(40, 130))

    color = GREEN if amount >= 0 else RED
    big = font(96, True)
    txt = f"{sign}{amount:,}"
    tw = d.textlength(txt, font=big)
    neon_text(img, ((CARD_W - tw) // 2, 180), txt, big, color)

    d.text((80, 320), "NEW BALANCE", font=font(22, True), fill=MUTED)
    bal_f = font(54, True)
    bal_txt = f"{new_balance:,} {currency}"
    bw = d.textlength(bal_txt, font=bal_f)
    neon_text(img, ((CARD_W - bw) // 2, 360), bal_txt, bal_f, GOLD)

    _draw_chip(img, (110, 430), 46, GOLD, GOLD_DARK)
    _draw_chip(img, (CARD_W - 110, 430), 46, RED, WHITE)

    return _save(img)


def limbo_card(target: float, result: float, bet: int, payout: int,
               username: str = "", **_kwargs) -> bytes:
    """Limbo / crash multiplier card."""
    img, d = base_canvas("\u2933 LIMBO",
                         f"Bet {bet:,}  target  {float(target):.2f}x")
    panel = felt_panel((CARD_W - 80, 340))
    img.alpha_composite(panel, dest=(40, 130))

    won = float(result) >= float(target)
    color = GREEN if won else RED

    big = font(140, True)
    txt = f"{float(result):.2f}x"
    tw = d.textlength(txt, font=big)
    neon_text(img, ((CARD_W - tw) // 2, 190), txt, big, color)

    d.text((80, 380), f"TARGET  {float(target):.2f}x",
           font=font(24, True), fill=MUTED)
    d.text((CARD_W - 280, 380), f"RESULT  {float(result):.2f}x",
           font=font(24, True), fill=WHITE)

    bar_y = 430
    rounded_rect(d, (80, bar_y, CARD_W - 80, bar_y + 18), 9, fill=(40, 50, 70))
    frac = min(1.0, float(result) / max(0.01, float(target) * 2))
    rounded_rect(d, (80, bar_y, 80 + int((CARD_W - 160) * frac), bar_y + 18),
                 9, fill=color)

    _result_banner(img, payout if won else -bet, bet)
    return _save(img)


def rps_card(player: str, bot: str, bet: int, payout: int,
             outcome: str = "", **_kwargs) -> bytes:
    """Rock Paper Scissors card."""
    img, d = base_canvas("ROCK \u00b7 PAPER \u00b7 SCISSORS",
                         f"Bet {bet:,}")
    panel = felt_panel((CARD_W - 80, 340))
    img.alpha_composite(panel, dest=(40, 130))

    glyphs = {"rock": "\u270A", "paper": "\u270B",
              "scissors": "\u270C", "r": "\u270A", "p": "\u270B", "s": "\u270C"}
    pg = glyphs.get(str(player).lower(), "?")
    bg = glyphs.get(str(bot).lower(), "?")

    bigf = font(150, True)
    d.text((140, 200), pg, font=bigf, fill=WHITE)
    d.text((CARD_W - 270, 200), bg, font=bigf, fill=WHITE)
    d.text((CARD_W // 2 - 26, 250), "VS", font=font(48, True), fill=GOLD)

    d.text((140, 380), f"YOU: {str(player).upper()}",
           font=font(22, True), fill=MUTED)
    d.text((CARD_W - 340, 380), f"BOT: {str(bot).upper()}",
           font=font(22, True), fill=MUTED)

    out = outcome.lower() if outcome else ("win" if payout > 0 else
                                           ("tie" if payout == 0 else "loss"))
    if out.startswith("tie") or out.startswith("draw") or out == "push":
        _banner(img, "PUSH  (tie)", GOLD)
    else:
        _result_banner(img, payout, bet)
    return _save(img)


def slide_card(multiplier: float, result: float, bet: int, payout: int,
               username: str = "", **_kwargs) -> bytes:
    """Slide / plinko style multiplier card."""
    img, d = base_canvas("\u25B8 SLIDE", f"Bet {bet:,}")
    panel = felt_panel((CARD_W - 80, 340))
    img.alpha_composite(panel, dest=(40, 130))

    zones = [(0.2, RED), (0.5, (200, 120, 60)), (1.0, MUTED),
             (2.0, GOLD), (5.0, GREEN), (10.0, NEON_BLUE)]
    track_y = 240
    track_x0, track_x1 = 80, CARD_W - 80
    width = track_x1 - track_x0
    step = width / len(zones)
    for i, (mult, col) in enumerate(zones):
        x0 = track_x0 + i * step
        rounded_rect(d, (x0 + 4, track_y, x0 + step - 4, track_y + 70),
                     10, fill=col)
        f = font(20, True)
        label = f"{mult:.1f}x"
        tw = d.textlength(label, font=f)
        d.text((x0 + step / 2 - tw / 2, track_y + 22), label,
               font=f, fill=BLACK)

    landed = float(result)
    idx = min(range(len(zones)), key=lambda i: abs(zones[i][0] - landed))
    px = track_x0 + idx * step + step / 2
    d.polygon([(px - 16, track_y - 30), (px + 16, track_y - 30),
               (px, track_y - 4)], fill=GOLD)

    d.text((80, 360), f"LANDED  {landed:.2f}x",
           font=font(28, True), fill=WHITE)
    _result_banner(img, payout, bet)
    return _save(img)


def tight_card(steps: int, max_steps: int, bet: int, payout: int,
               cashed_out: bool = False, **_kwargs) -> bytes:
    """Tightrope / risk-each-step card."""
    img, d = base_canvas("\u2696 TIGHTROPE",
                         f"Bet {bet:,}   step {int(steps)}/{int(max_steps)}")
    panel = felt_panel((CARD_W - 80, 340))
    img.alpha_composite(panel, dest=(40, 130))

    rope_y = 320
    d.line((80, rope_y, CARD_W - 80, rope_y), fill=GOLD_DARK, width=6)

    total = max(1, int(max_steps))
    for i in range(total):
        x = 90 + i * ((CARD_W - 180) / max(1, total - 1)) if total > 1 else CARD_W // 2
        done = i < int(steps)
        col = GREEN if done else MUTED
        d.ellipse((x - 12, rope_y - 12, x + 12, rope_y + 12),
                  fill=col, outline=BLACK, width=2)

    if total > 1:
        wx = 90 + max(0, int(steps) - 1) * ((CARD_W - 180) / (total - 1))
        wx = max(90, min(CARD_W - 90, wx))
    else:
        wx = CARD_W // 2
    d.ellipse((wx - 18, rope_y - 60, wx + 18, rope_y - 24),
              fill=WHITE, outline=BLACK, width=2)
    d.line((wx, rope_y - 24, wx, rope_y - 4), fill=WHITE, width=4)

    if cashed_out and payout > 0:
        _banner(img, f"CASHED OUT  +{payout:,}", GREEN)
    elif payout > 0:
        _result_banner(img, payout, bet)
    else:
        _banner(img, f"FELL  -{bet:,}", RED)
    return _save(img)


def war_card(player_card: str, dealer_card: str, bet: int, payout: int,
             **_kwargs) -> bytes:
    """Casino War: high card wins."""
    img, d = base_canvas("\u2694 CASINO WAR", f"Bet {bet:,}")
    panel = felt_panel((CARD_W - 80, 360))
    img.alpha_composite(panel, dest=(40, 130))

    d.text((150, 170), "YOU", font=font(22, True), fill=MUTED)
    d.text((CARD_W - 240, 170), "DEALER", font=font(22, True), fill=MUTED)
    _draw_playing_card(img, (110, 210), str(player_card), w=140, h=200)
    _draw_playing_card(img, (CARD_W - 250, 210), str(dealer_card), w=140, h=200)

    d.text((CARD_W // 2 - 26, 290), "VS", font=font(54, True), fill=GOLD)

    if payout == 0:
        _banner(img, "WAR! (tie)", GOLD)
    else:
        _result_banner(img, payout, bet)
    return _save(img)


def valentines_card(username: str, partner: str = "",
                    score: int = 0, reward: int = 0, **_kwargs) -> bytes:
    """Valentines event card."""
    img, d = base_canvas("\u2665 VALENTINES",
                         f"@{username}" + (f"  \u2665  @{partner}" if partner else ""))
    panel = felt_panel((CARD_W - 80, 360))
    img.alpha_composite(panel, dest=(40, 130))

    cx, cy = CARD_W // 2, 290
    heart = Image.new("RGBA", (260, 240), (0, 0, 0, 0))
    hd = ImageDraw.Draw(heart)
    hd.ellipse((10, 10, 140, 140), fill=RED)
    hd.ellipse((110, 10, 240, 140), fill=RED)
    hd.polygon([(20, 90), (240, 90), (130, 230)], fill=RED)
    heart = heart.filter(ImageFilter.GaussianBlur(0.6))
    img.alpha_composite(heart, dest=(cx - 130, cy - 100))

    if score:
        f = font(72, True)
        txt = f"{int(score)}%"
        tw = d.textlength(txt, font=f)
        d.text((cx - tw / 2, cy - 50), txt, font=f, fill=WHITE)

    if reward > 0:
        _banner(img, f"\u2665 GIFTED  +{reward:,}", GREEN)
    else:
        _banner(img, "Happy Valentines!", GOLD)
    return _save(img)


def twist_card(reels: Sequence[str], bet: int, payout: int,
               username: str = "", **_kwargs) -> bytes:
    """Twist (mini slots-style) card."""
    img, d = base_canvas("\u21BB TWIST", f"Bet {bet:,}")
    panel = felt_panel((CARD_W - 80, 340))
    img.alpha_composite(panel, dest=(40, 130))

    n = max(1, len(reels))
    size = 140
    gap = 30
    total_w = n * size + (n - 1) * gap
    start_x = (CARD_W - total_w) // 2
    for i, kind in enumerate(reels):
        x = start_x + i * (size + gap)
        rounded_rect(d, (x, 190, x + size, 190 + size), 18,
                     fill=(20, 30, 50), outline=GOLD_DARK, width=2)
        _draw_slot_symbol(img, (x + size // 2, 190 + size // 2),
                          size - 30, str(kind))

    _result_banner(img, payout, bet)
    return _save(img)


# ---------------------------------------------------------------------------
# Local preview when run directly
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    out = "preview_out"
    os.makedirs(out, exist_ok=True)
    samples = {
        "balance.png":  balance_card("HighRoller", 125_400),
        "blackjack.png": blackjack_card(
            ["AS", "KD"], ["9H", "7C"], 21, 16, 500, status="blackjack"),
        "slots.png":   slots_card(
            ["seven", "seven", "seven"], 100, 5000, "HighRoller"),
        "roulette.png": roulette_card(17, "black", 250, 8750, pick="17"),
        "dice.png":    dice_card([5, 6], 200, 800, pick=11),
        "coinflip.png": coinflip_card("heads", "heads", 100, 200),
    }
    for name, data in samples.items():
        with open(os.path.join(out, name), "wb") as f:
            f.write(data)
    print(f"Wrote {len(samples)} previews to ./{out}/")
