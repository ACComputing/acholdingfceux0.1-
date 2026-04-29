#!/usr/bin/env python3
# =============================================================
#   AC's FCEUX NES EMU 0.5
#   A.C Holdings / Team Flames © 1999–2026
#   Full hardware: 6502 CPU · PPU · APU audio · Mappers 0-4
#   Single-file · Python 3.14/Tkinter · FCEUX-style GUI
# =============================================================

from __future__ import annotations

import os, sys, time, threading, struct, math
from array import array
from collections import deque
import tkinter as tk
from tkinter import filedialog, messagebox

# ── pygame optional audio output ─────────────────────────────
try:
    import pygame
    HAS_PYGAME = True
except Exception:
    pygame = None
    HAS_PYGAME = False

# ── Cython shim ──────────────────────────────────────────────
try:
    import cython
    COMPILED = cython.compiled
except ImportError:
    class _Cy:
        compiled = False
        def cclass(self, c): return c
        def cfunc(self, f): return f
        def locals(self, **kw): return lambda f: f
        def returns(self, t): return lambda f: f
        int = int; double = float; bint = bool; uint = int
    cython = _Cy()
    COMPILED = False

# ── PIL optional fast blit ────────────────────────────────────
try:
    from PIL import Image, ImageTk
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

# =============================================================
#  PALETTE — FCEUX/Nintendulator-style NTSC 2C02 RGB table
# =============================================================
# The NES does not output RGB directly; this 64-entry table is a
# practical NTSC 2C02 approximation used by many emulators.  PPU mask
# grayscale and color-emphasis bits are applied by nes_rgb().
NES_PAL = [
    # 0x00–0x0F
    ( 84, 84, 84),(  0, 30,116),(  8, 16,144),( 48,  0,136),
    ( 68,  0,100),( 92,  0, 48),( 84,  4,  0),( 60, 24,  0),
    ( 32, 42,  0),(  8, 58,  0),(  0, 64,  0),(  0, 60,  0),
    (  0, 50, 60),(  0,  0,  0),(  0,  0,  0),(  0,  0,  0),
    # 0x10–0x1F
    (152,150,152),(  8, 76,196),( 48, 50,236),( 92, 30,228),
    (136, 20,176),(160, 20,100),(152, 34, 32),(120, 60,  0),
    ( 84, 90,  0),( 40,114,  0),(  8,124,  0),(  0,118, 40),
    (  0,102,120),(  0,  0,  0),(  0,  0,  0),(  0,  0,  0),
    # 0x20–0x2F
    (236,238,236),( 76,154,236),(120,124,236),(176, 98,236),
    (228, 84,236),(236, 88,180),(236,106,100),(212,136, 32),
    (160,170,  0),(116,196,  0),( 76,208, 32),( 56,204,108),
    ( 56,180,204),( 60, 60, 60),(  0,  0,  0),(  0,  0,  0),
    # 0x30–0x3F
    (236,238,236),(168,204,236),(188,188,236),(212,178,236),
    (236,174,236),(236,174,212),(236,180,176),(228,196,144),
    (204,210,120),(180,222,120),(168,226,144),(152,226,180),
    (160,214,228),(160,162,160),(  0,  0,  0),(  0,  0,  0),
]

def _clamp8(v):
    return 0 if v < 0 else 255 if v > 255 else int(v)

def nes_rgb(ci, mask=0):
    """Return NES RGB with PPU grayscale/emphasis mask applied."""
    ci &= (0x30 if (mask & 0x01) else 0x3F)
    r, g, b = NES_PAL[ci]

    # Approximate NTSC color-emphasis behavior.  The emphasized channel
    # is held while the other channels are dimmed; multiple bits combine.
    emph = (mask >> 5) & 0x07
    if emph:
        rf = gf = bf = 1.0
        if emph & 0x01:  # red emphasis
            gf *= 0.80; bf *= 0.80
        if emph & 0x02:  # green emphasis
            rf *= 0.80; bf *= 0.80
        if emph & 0x04:  # blue emphasis
            rf *= 0.80; gf *= 0.80
        r, g, b = _clamp8(r * rf), _clamp8(g * gf), _clamp8(b * bf)
    return r, g, b

# =============================================================
#  HELPERS
# =============================================================
def _rev8(b):
    """Reverse bits in a byte."""
    b = ((b & 0xF0) >> 4) | ((b & 0x0F) << 4)
    b = ((b & 0xCC) >> 2) | ((b & 0x33) << 2)
    b = ((b & 0xAA) >> 1) | ((b & 0x55) << 1)
    return b

# =============================================================
#  MAPPERS
# =============================================================
class Mapper:
    def __init__(self, prg, chr_, pb, cb):
        self.prg_rom  = bytes(prg)
        self.chr_rom  = bytearray(chr_) if chr_ else bytearray(8192)
        self.prg_banks = pb
        self.chr_banks = cb
        self.chr_ram   = (len(chr_) == 0)
        self.mirroring = 0   # 0=horiz, 1=vert, 2=4-screen

    def cpu_read(self, a):  return 0xFF
    def cpu_write(self, a, v): pass
    def ppu_read(self, a):  return self.chr_rom[a & 0x1FFF]
    def ppu_write(self, a, v):
        if self.chr_ram:
            self.chr_rom[a & 0x1FFF] = v & 0xFF

class Mapper0(Mapper):
    def cpu_read(self, a):
        if a >= 0x8000:
            if self.prg_banks == 1:
                return self.prg_rom[(a - 0x8000) & 0x3FFF]
            return self.prg_rom[(a - 0x8000) & 0x7FFF]
        return 0xFF

class Mapper1(Mapper):
    def __init__(self, *a):
        super().__init__(*a)
        self.shift = 0x10; self.ctrl = 0x0C
        self.chr0 = self.chr1 = self.prg_bank = 0

    def cpu_write(self, a, v):
        if a < 0x8000: return
        if v & 0x80: self.shift = 0x10; self.ctrl |= 0x0C; return
        full = ((v & 1) << 4) | (self.shift >> 1)
        if self.shift & 1:
            self.shift = 0x10
            reg = (a >> 13) & 3
            if   reg == 0: self.ctrl     = full
            elif reg == 1: self.chr0     = full
            elif reg == 2: self.chr1     = full
            elif reg == 3: self.prg_bank = full & 0x0F
        else:
            self.shift = ((self.shift >> 1) & 0x0F) | ((v & 1) << 4)

    def cpu_read(self, a):
        if a < 0x8000: return 0xFF
        mode = (self.ctrl >> 2) & 3
        ps = len(self.prg_rom)
        if mode <= 1:
            b = self.prg_bank & 0xFE
            return self.prg_rom[(b * 0x8000 + a - 0x8000) % ps]
        elif mode == 2:
            if a < 0xC000:
                return self.prg_rom[(a - 0x8000) % ps]
            return self.prg_rom[(self.prg_bank * 0x4000 + a - 0xC000) % ps]
        else:
            if a >= 0xC000:
                return self.prg_rom[((self.prg_banks - 1) * 0x4000 + a - 0xC000) % ps]
            return self.prg_rom[(self.prg_bank * 0x4000 + a - 0x8000) % ps]

    def ppu_read(self, a):
        if a >= 0x2000: return 0
        cs = len(self.chr_rom)
        if (self.ctrl >> 4) & 1:
            if a < 0x1000:
                return self.chr_rom[(self.chr0 * 0x1000 + a) % cs]
            return self.chr_rom[(self.chr1 * 0x1000 + a - 0x1000) % cs]
        else:
            b = self.chr0 & 0xFE
            return self.chr_rom[(b * 0x1000 + a) % cs]

    def ppu_write(self, a, v):
        if self.chr_ram and a < 0x2000:
            self.chr_rom[a & 0x1FFF] = v & 0xFF

class Mapper2(Mapper):
    def __init__(self, *a):
        super().__init__(*a); self.prg_bank = 0
    def cpu_write(self, a, v):
        if a >= 0x8000: self.prg_bank = v & 0x0F
    def cpu_read(self, a):
        if a < 0x8000: return 0xFF
        ps = len(self.prg_rom)
        if a < 0xC000:
            return self.prg_rom[(self.prg_bank * 0x4000 + a - 0x8000) % ps]
        return self.prg_rom[((self.prg_banks - 1) * 0x4000 + a - 0xC000) % ps]

class Mapper3(Mapper):
    def __init__(self, *a):
        super().__init__(*a); self.chr_bank = 0
    def cpu_write(self, a, v):
        if a >= 0x8000: self.chr_bank = v & 3
    def cpu_read(self, a):
        if a >= 0x8000:
            if self.prg_banks == 1:
                return self.prg_rom[(a - 0x8000) & 0x3FFF]
            return self.prg_rom[(a - 0x8000) & 0x7FFF]
        return 0xFF
    def ppu_read(self, a):
        return self.chr_rom[(self.chr_bank * 0x2000 + a) % len(self.chr_rom)]

class Mapper4(Mapper):
    def __init__(self, *a):
        super().__init__(*a)
        self.regs = [0]*8
        self.bsel = self.prg_mode = self.chr_mode = self.mirror = 0
        self.irq_latch = self.irq_cnt = 0
        self.irq_en = self.irq_flag = False

    def cpu_write(self, a, v):
        if a < 0x8000: return
        e = a & 1
        if   a < 0xA000:
            if e == 0:
                self.bsel = v & 7; self.prg_mode = (v >> 6) & 1; self.chr_mode = (v >> 7) & 1
            else:
                self.regs[self.bsel] = v
        elif a < 0xC000:
            if e == 0: self.mirror = v & 1
        elif a < 0xE000:
            if e == 0: self.irq_latch = v
            else:      self.irq_cnt   = 0
        else:
            if e == 0: self.irq_en = False; self.irq_flag = False
            else:      self.irq_en = True

    def cpu_read(self, a):
        if a < 0x8000: return 0xFF
        ps = len(self.prg_rom); nb = self.prg_banks * 2
        def pg(bank, off): return self.prg_rom[(bank * 0x2000 + off) % ps]
        if self.prg_mode == 0:
            if   a < 0xA000: return pg(self.regs[6],         a - 0x8000)
            elif a < 0xC000: return pg(self.regs[7],         a - 0xA000)
            elif a < 0xE000: return pg(nb - 2,               a - 0xC000)
            else:            return pg(nb - 1,               a - 0xE000)
        else:
            if   a < 0xA000: return pg(nb - 2,               a - 0x8000)
            elif a < 0xC000: return pg(self.regs[7],         a - 0xA000)
            elif a < 0xE000: return pg(self.regs[6],         a - 0xC000)
            else:            return pg(nb - 1,               a - 0xE000)

    def ppu_read(self, a):
        if a >= 0x2000: return 0
        cs = len(self.chr_rom)
        r = self.regs
        if self.chr_mode == 0:
            if   a < 0x0800: return self.chr_rom[((r[0] & 0xFE) * 0x0400 + a)          % cs]
            elif a < 0x1000: return self.chr_rom[((r[1] & 0xFE) * 0x0400 + a - 0x0400) % cs]
            elif a < 0x1400: return self.chr_rom[(r[2] * 0x0400 + a - 0x1000)           % cs]
            elif a < 0x1800: return self.chr_rom[(r[3] * 0x0400 + a - 0x1400)           % cs]
            elif a < 0x1C00: return self.chr_rom[(r[4] * 0x0400 + a - 0x1800)           % cs]
            else:            return self.chr_rom[(r[5] * 0x0400 + a - 0x1C00)           % cs]
        else:
            if   a < 0x0400: return self.chr_rom[(r[2] * 0x0400 + a)                    % cs]
            elif a < 0x0800: return self.chr_rom[(r[3] * 0x0400 + a - 0x0400)           % cs]
            elif a < 0x0C00: return self.chr_rom[(r[4] * 0x0400 + a - 0x0800)           % cs]
            elif a < 0x1000: return self.chr_rom[(r[5] * 0x0400 + a - 0x0C00)           % cs]
            elif a < 0x1800: return self.chr_rom[((r[0] & 0xFE) * 0x0400 + a - 0x1000) % cs]
            else:            return self.chr_rom[((r[1] & 0xFE) * 0x0400 + a - 0x1800 + 0x0400) % cs]

    def ppu_write(self, a, v):
        if self.chr_ram and a < 0x2000:
            self.chr_rom[a & 0x1FFF] = v & 0xFF

MAPPERS = {0: Mapper0, 1: Mapper1, 2: Mapper2, 3: Mapper3, 4: Mapper4}

# =============================================================
#  PPU  — full NTSC PPU with Loopy scrolling
# =============================================================
class PPU:
    def __init__(self):
        # ── MMIO registers
        self.ctrl   = 0   # $2000
        self.mask   = 0   # $2001
        self.status = 0xA0  # $2002 — start with VBL set + sprite 0 compat
        self.oam_addr = 0

        # ── Loopy scroll
        self.v = 0; self.t = 0; self.x = 0; self.w = 0

        # ── Internal memory
        self.vram    = bytearray(0x1000)   # supports 4-screen mirroring too
        self.pal_ram = bytearray(32)
        self.oam     = bytearray(256)

        # ── Background shifters / latches
        self.nt  = self.at  = self.bg_lo = self.bg_hi = 0
        self.sr_lo = self.sr_hi = 0     # 16-bit pattern shift regs
        self.at_lo = self.at_hi = 0     # 8-bit attr shift regs
        self.at_lat_lo = self.at_lat_hi = 0

        # ── Sprite state
        self.sp_count    = 0
        self.sp_pat      = [0]*8
        self.sp_pos      = [0]*8
        self.sp_attr     = [0]*8
        self.sp_index    = [0]*8

        # ── Timing
        self.scanline = 261   # pre-render
        self.dot      = 0
        self.odd      = False
        self.frame_buffer = bytearray(256 * 240 * 3)
        self.frame_ready  = False

        # ── Read buffer
        self.read_buf = 0

        # ── External refs
        self.mapper = None
        self.mirroring = 0    # 0=horiz, 1=vert
        self.nmi_cb = None

    # ── VRAM address decode ─────────────────────────────────
    def _mirror(self, a):
        a &= 0x3FFF
        if a >= 0x3F00:
            b = a & 0x1F
            if b in (0x10, 0x14, 0x18, 0x1C): b &= 0x0F
            return 0x3F00 | b
        if a >= 0x2000:
            a &= 0x2FFF
            nt  = (a - 0x2000) >> 10
            off = (a - 0x2000) & 0x3FF
            if self.mirroring == 2:   # 4-screen
                return 0x2000 | ((nt & 3) << 10) | off
            if self.mirroring == 1:   # vertical
                return 0x2000 | ((nt & 1) << 10) | off
            else:                     # horizontal
                return 0x2000 | (((nt >> 1) & 1) << 10) | off
        return a

    def _vr(self, a):
        a = self._mirror(a)
        if   a < 0x2000: return self.mapper.ppu_read(a)
        elif a < 0x3F00: return self.vram[a & (len(self.vram)-1)]
        else:            return self.pal_ram[a & 0x1F]

    def _vw(self, a, v):
        a = self._mirror(a)
        if   a < 0x2000: self.mapper.ppu_write(a, v)
        elif a < 0x3F00: self.vram[a & (len(self.vram)-1)] = v
        else:            self.pal_ram[a & 0x1F] = v

    # ── CPU register I/O ────────────────────────────────────
    def read_reg(self, r):
        if r == 2:                          # PPUSTATUS
            v = (self.status & 0xE0) | (self.read_buf & 0x1F)
            self.status &= 0x7F             # clear VBL
            self.w = 0
            return v
        if r == 4: return self.oam[self.oam_addr]
        if r == 7:
            v = self.read_buf
            self.read_buf = self._vr(self.v)
            if (self.v & 0x3FFF) >= 0x3F00:
                v = self.read_buf
            self.v = (self.v + (32 if self.ctrl & 4 else 1)) & 0x7FFF
            return v
        return 0

    def write_reg(self, r, v):
        if r == 0:                          # PPUCTRL
            self.ctrl = v
            self.t = (self.t & 0xF3FF) | ((v & 3) << 10)
        elif r == 1: self.mask = v
        elif r == 3: self.oam_addr = v
        elif r == 4:
            self.oam[self.oam_addr] = v
            self.oam_addr = (self.oam_addr + 1) & 0xFF
        elif r == 5:                        # PPUSCROLL
            if self.w == 0:
                self.t = (self.t & 0xFFE0) | (v >> 3)
                self.x = v & 7; self.w = 1
            else:
                self.t = (self.t & 0x8C1F) | ((v & 0xF8) << 2) | ((v & 7) << 12)
                self.w = 0
        elif r == 6:                        # PPUADDR
            if self.w == 0:
                self.t = (self.t & 0x00FF) | ((v & 0x3F) << 8); self.w = 1
            else:
                self.t = (self.t & 0xFF00) | v; self.v = self.t; self.w = 0
        elif r == 7:
            self._vw(self.v, v)
            self.v = (self.v + (32 if self.ctrl & 4 else 1)) & 0x7FFF

    def oam_dma(self, data):
        for i in range(256):
            self.oam[(self.oam_addr + i) & 0xFF] = data[i]

    # ── Loopy helpers ────────────────────────────────────────
    def _inc_h(self):
        if (self.v & 0x1F) == 31:
            self.v &= ~0x1F; self.v ^= 0x0400
        else:
            self.v += 1

    def _inc_v(self):
        if (self.v & 0x7000) != 0x7000:
            self.v += 0x1000
        else:
            self.v &= ~0x7000
            y = (self.v & 0x03E0) >> 5
            if   y == 29: y = 0; self.v ^= 0x0800
            elif y == 31: y = 0
            else:         y += 1
            self.v = (self.v & ~0x03E0) | (y << 5)

    def _copy_h(self): self.v = (self.v & ~0x041F) | (self.t & 0x041F)
    def _copy_v(self): self.v = (self.v & ~0x7BE0) | (self.t & 0x7BE0)

    # ── Tile fetching ────────────────────────────────────────
    def _fetch_nt(self):
        self.nt = self._vr(0x2000 | (self.v & 0x0FFF))

    def _fetch_at(self):
        a = 0x23C0 | (self.v & 0x0C00) | ((self.v >> 4) & 0x38) | ((self.v >> 2) & 7)
        sh = ((self.v >> 4) & 4) | (self.v & 2)
        self.at = (self._vr(a) >> sh) & 3

    def _fetch_lo(self):
        pt = ((self.ctrl & 0x10) << 8) | (self.nt << 4) | ((self.v >> 12) & 7)
        self.bg_lo = self._vr(pt)

    def _fetch_hi(self):
        pt = ((self.ctrl & 0x10) << 8) | (self.nt << 4) | ((self.v >> 12) & 7) | 8
        self.bg_hi = self._vr(pt)

    def _reload(self):
        self.sr_lo = (self.sr_lo & 0xFF00) | self.bg_lo
        self.sr_hi = (self.sr_hi & 0xFF00) | self.bg_hi
        self.at_lat_lo = self.at & 1
        self.at_lat_hi = (self.at >> 1) & 1

    def _shift(self):
        self.sr_lo  = (self.sr_lo  << 1) & 0xFFFF
        self.sr_hi  = (self.sr_hi  << 1) & 0xFFFF
        self.at_lo  = ((self.at_lo  << 1) | self.at_lat_lo) & 0xFF
        self.at_hi  = ((self.at_hi  << 1) | self.at_lat_hi) & 0xFF

    # ── Sprite evaluation ────────────────────────────────────
    def _eval_sprites(self):
        n = 0
        sline = (self.scanline + 1) & 0xFF
        h = 16 if (self.ctrl & 0x20) else 8
        for i in range(64):
            yo = self.oam[i * 4]
            row = sline - yo
            if not (0 <= row < h): continue
            if n >= 8: self.status |= 0x20; break

            tile  = self.oam[i * 4 + 1]
            attr  = self.oam[i * 4 + 2]
            xpos  = self.oam[i * 4 + 3]
            fv    = (attr >> 7) & 1
            fh    = (attr >> 6) & 1

            if h == 8:
                base = (self.ctrl & 0x08) << 9
                r    = (7 - row) if fv else row
                lo   = self._vr(base | (tile << 4) | r)
                hi   = self._vr(base | (tile << 4) | r | 8)
            else:
                base = (tile & 1) << 12; tile &= 0xFE
                r    = (15 - row) if fv else row
                if r >= 8: tile += 1; r -= 8
                lo = self._vr(base | (tile << 4) | r)
                hi = self._vr(base | (tile << 4) | r | 8)

            if fh: lo = _rev8(lo); hi = _rev8(hi)

            self.sp_pat[n]   = (hi << 8) | lo
            self.sp_pos[n]   = xpos
            self.sp_attr[n]  = attr
            self.sp_index[n] = i
            n += 1
        self.sp_count = n

    # ── Pixel render ─────────────────────────────────────────
    def _pixel(self):
        px = self.dot - 1
        py = self.scanline
        rnd = self.mask & 0x18

        bg_px = bg_pal = 0
        if rnd and (self.mask & 0x08) and (px >= 8 or (self.mask & 0x02)):
            bit   = 0x8000 >> self.x
            p0    = 1 if (self.sr_lo & bit) else 0
            p1    = 1 if (self.sr_hi & bit) else 0
            bg_px = (p1 << 1) | p0
            bg_pal = (1 if (self.at_hi & bit) else 0) << 1 | (1 if (self.at_lo & bit) else 0)

        sp_px = sp_pal = sp_pri = 0
        sp0_pos = False
        if rnd and (self.mask & 0x10) and (px >= 8 or (self.mask & 0x04)):
            for i in range(self.sp_count):
                off = px - self.sp_pos[i]
                if not (0 <= off <= 7): continue
                pat = self.sp_pat[i]
                p   = ((pat >> (7 - off)) & 1) | (((pat >> (15 - off)) & 1) << 1)
                if p:
                    sp_px  = p
                    sp_pal = (self.sp_attr[i] & 3) + 4
                    sp_pri = (self.sp_attr[i] >> 5) & 1
                    if self.sp_index[i] == 0: sp0_pos = True
                    break

        if sp0_pos and bg_px and sp_px and px < 255:
            self.status |= 0x40

        if   bg_px == 0 and sp_px == 0: pal_addr = 0
        elif bg_px == 0:                pal_addr = (sp_pal << 2) | sp_px
        elif sp_px == 0:                pal_addr = (bg_pal << 2) | bg_px
        elif sp_pri == 0:               pal_addr = (sp_pal << 2) | sp_px
        else:                           pal_addr = (bg_pal << 2) | bg_px

        ci = self.pal_ram[pal_addr & 0x1F]
        r, g, b = nes_rgb(ci, self.mask)
        i3 = (py * 256 + px) * 3
        self.frame_buffer[i3]   = r
        self.frame_buffer[i3+1] = g
        self.frame_buffer[i3+2] = b

    # ── Main tick ────────────────────────────────────────────
    def step(self):
        sl = self.scanline; d = self.dot
        rnd = bool(self.mask & 0x18)
        vis = sl < 240 or sl == 261

        if vis and rnd:
            # Tile pipeline (dots 1-256, 321-336)
            if (2 <= d <= 257) or (322 <= d <= 337):
                self._shift()
                ph = (d - 1) & 7
                if   ph == 1: self._fetch_nt()
                elif ph == 3: self._fetch_at()
                elif ph == 5: self._fetch_lo()
                elif ph == 7: self._fetch_hi()
                elif ph == 0: self._reload(); self._inc_h()
            if d == 256: self._inc_v()
            if d == 257: self._copy_h()
            if sl == 261 and 280 <= d <= 304: self._copy_v()
            # Sprite evaluation mid-line
            if d == 64 and sl < 240: self.status &= ~0x20
            if d == 260 and sl < 240: self._eval_sprites()

        # Visible pixel output
        if 1 <= d <= 256 and sl < 240 and rnd:
            self._pixel()

        # VBlank
        if sl == 241 and d == 1:
            self.status |= 0x80
            self.frame_ready = True
            if (self.ctrl & 0x80) and self.nmi_cb:
                self.nmi_cb()

        # Pre-render clear
        if sl == 261 and d == 1:
            self.status &= 0x1F
            self.frame_ready = False

        # Advance
        self.dot += 1
        if self.dot > 340:
            self.dot = 0
            self.scanline += 1
            if self.scanline > 261:
                self.scanline = 0
                self.odd = not self.odd
                # Skip (0,0) on odd frames when rendering
                if self.odd and rnd:
                    self.dot = 1

# =============================================================
#  APU  — Pulse×2 · Triangle · Noise · basic DMC stub
# =============================================================
_LENGTH_TBL = [10,254,20,2,40,4,80,6,160,8,60,10,14,12,26,14,
               12,16,24,18,48,20,96,22,192,24,72,26,16,28,32,30]
_DUTY = [[0,1,0,0,0,0,0,0],[0,1,1,0,0,0,0,0],
         [0,1,1,1,1,0,0,0],[1,0,0,1,1,1,1,1]]
_TRI_SEQ = ([15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0] +
            [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
_NOISE_P  = [4,8,16,32,64,96,128,160,202,254,380,508,762,1016,2034,4068]

class APU:
    """Small but live NES APU approximation.

    It models the parts most games need to make audible output: two pulse
    channels, triangle, noise, length counters, envelopes, linear counter,
    $4015 status, and the frame sequencer. DMC is stubbed because full DMC
    playback requires sample DMA timing on the CPU bus.
    """
    CPU_HZ_NTSC = 1789773.0

    def __init__(self, rate=44100):
        self.rate = rate
        self.cpf = self.CPU_HZ_NTSC / rate  # CPU cycles per output sample
        self.sample_acc = 0.0
        self.clk = 0
        self.samples = []
        self.irq_flag = False
        self.fc_mode = 0
        self.fc_irq = True

        # DC blocker for the naturally positive NES mixer output.
        self._dc_prev = 0.0
        self._hp_prev = 0.0

        # Pulse 1
        self.p1_duty = 0; self.p1_halt = 0; self.p1_ce = 0; self.p1_vol = 0
        self.p1_timer = 0; self.p1_cnt = 0; self.p1_len = 0; self.p1_seq = 0
        self.p1_env_div = 0; self.p1_env_vol = 0; self.p1_env_start = False
        # Pulse 2
        self.p2_duty = 0; self.p2_halt = 0; self.p2_ce = 0; self.p2_vol = 0
        self.p2_timer = 0; self.p2_cnt = 0; self.p2_len = 0; self.p2_seq = 0
        self.p2_env_div = 0; self.p2_env_vol = 0; self.p2_env_start = False
        # Triangle
        self.tri_ctrl = 0
        self.tri_timer = 0; self.tri_cnt = 0; self.tri_len = 0; self.tri_seq = 0
        self.tri_lin = 0; self.tri_lin_cnt = 0; self.tri_reload = False
        # Noise
        self.noi_halt = 0; self.noi_ce = 0; self.noi_vol = 0
        self.noi_mode = 0; self.noi_period = _NOISE_P[0]; self.noi_cnt = 0
        self.noi_len = 0; self.noi_shift = 1
        self.noi_env_div = 0; self.noi_env_vol = 0; self.noi_env_start = False
        # DMC stub/status
        self.dmc_en = False
        self.dmc_len = 0
        # Status / enable bits: pulse1, pulse2, triangle, noise, DMC
        self.en = 0x00

    def reset(self):
        rate = self.rate
        self.__init__(rate)

    def read(self, a):
        """Read APU status at $4015."""
        v = 0
        if self.p1_len: v |= 0x01
        if self.p2_len: v |= 0x02
        if self.tri_len: v |= 0x04
        if self.noi_len: v |= 0x08
        if self.dmc_len: v |= 0x10
        if self.irq_flag: v |= 0x40
        self.irq_flag = False
        return v

    def write(self, a, v):
        a &= 0x1F
        v &= 0xFF
        if a == 0x00:
            self.p1_duty = (v >> 6) & 3
            self.p1_halt = (v >> 5) & 1
            self.p1_ce   = (v >> 4) & 1
            self.p1_vol  = v & 0x0F
            self.p1_env_start = True
        elif a == 0x02:
            self.p1_timer = (self.p1_timer & 0x700) | v
        elif a == 0x03:
            self.p1_timer = (self.p1_timer & 0x0FF) | ((v & 7) << 8)
            if self.en & 0x01:
                self.p1_len = _LENGTH_TBL[(v >> 3) & 0x1F]
            self.p1_seq = 0
            self.p1_env_start = True
        elif a == 0x04:
            self.p2_duty = (v >> 6) & 3
            self.p2_halt = (v >> 5) & 1
            self.p2_ce   = (v >> 4) & 1
            self.p2_vol  = v & 0x0F
            self.p2_env_start = True
        elif a == 0x06:
            self.p2_timer = (self.p2_timer & 0x700) | v
        elif a == 0x07:
            self.p2_timer = (self.p2_timer & 0x0FF) | ((v & 7) << 8)
            if self.en & 0x02:
                self.p2_len = _LENGTH_TBL[(v >> 3) & 0x1F]
            self.p2_seq = 0
            self.p2_env_start = True
        elif a == 0x08:
            self.tri_ctrl = (v >> 7) & 1
            self.tri_lin = v & 0x7F
        elif a == 0x0A:
            self.tri_timer = (self.tri_timer & 0x700) | v
        elif a == 0x0B:
            self.tri_timer = (self.tri_timer & 0x0FF) | ((v & 7) << 8)
            if self.en & 0x04:
                self.tri_len = _LENGTH_TBL[(v >> 3) & 0x1F]
            self.tri_reload = True
        elif a == 0x0C:
            self.noi_halt = (v >> 5) & 1
            self.noi_ce   = (v >> 4) & 1
            self.noi_vol  = v & 0x0F
            self.noi_env_start = True
        elif a == 0x0E:
            self.noi_mode = (v >> 7) & 1
            self.noi_period = _NOISE_P[v & 0x0F]
        elif a == 0x0F:
            if self.en & 0x08:
                self.noi_len = _LENGTH_TBL[(v >> 3) & 0x1F]
            self.noi_env_start = True
        elif a == 0x15:
            self.en = v & 0x1F
            if not (self.en & 0x01): self.p1_len = 0
            if not (self.en & 0x02): self.p2_len = 0
            if not (self.en & 0x04): self.tri_len = 0
            if not (self.en & 0x08): self.noi_len = 0
            self.dmc_en = bool(self.en & 0x10)
            if not self.dmc_en: self.dmc_len = 0
            self.irq_flag = False
        elif a == 0x17:
            self.fc_mode = (v >> 7) & 1
            self.fc_irq = not ((v >> 6) & 1)
            if self.fc_irq is False:
                self.irq_flag = False
            if self.fc_mode:
                self._quarter_frame()
                self._half_frame()

    def _clock_envelope(self, prefix):
        start = getattr(self, f'{prefix}_env_start')
        div   = getattr(self, f'{prefix}_env_div')
        vol   = getattr(self, f'{prefix}_env_vol')
        period = getattr(self, f'{prefix}_vol')
        halt = getattr(self, f'{prefix}_halt')
        if start:
            start = False
            vol = 15
            div = period
        else:
            if div > 0:
                div -= 1
            else:
                div = period
                if vol > 0:
                    vol -= 1
                elif halt:
                    vol = 15
        setattr(self, f'{prefix}_env_start', start)
        setattr(self, f'{prefix}_env_div', div)
        setattr(self, f'{prefix}_env_vol', vol)

    def _quarter_frame(self):
        self._clock_envelope('p1')
        self._clock_envelope('p2')
        self._clock_envelope('noi')

        if self.tri_reload:
            self.tri_lin_cnt = self.tri_lin
        elif self.tri_lin_cnt > 0:
            self.tri_lin_cnt -= 1
        if not self.tri_ctrl:
            self.tri_reload = False

    def _half_frame(self):
        if self.p1_len and not self.p1_halt: self.p1_len -= 1
        if self.p2_len and not self.p2_halt: self.p2_len -= 1
        if self.tri_len and not self.tri_ctrl: self.tri_len -= 1
        if self.noi_len and not self.noi_halt: self.noi_len -= 1

    def _clock_frame_counter(self):
        # NTSC 4-step frame sequencer; enough for stable envelopes/lengths.
        pos = self.clk % 29830
        if pos in (7457, 14913, 22371, 29829):
            self._quarter_frame()
        if pos in (14913, 29829):
            self._half_frame()
        if pos == 29829 and self.fc_irq and not self.fc_mode:
            self.irq_flag = True

    def _clock_timers(self):
        # Pulse channels tick every other CPU cycle on hardware; using a
        # doubled reload keeps pitch close while remaining simple.
        if self.p1_cnt <= 0:
            self.p1_cnt = max(1, (self.p1_timer + 1) * 2)
            self.p1_seq = (self.p1_seq + 1) & 7
        else:
            self.p1_cnt -= 1

        if self.p2_cnt <= 0:
            self.p2_cnt = max(1, (self.p2_timer + 1) * 2)
            self.p2_seq = (self.p2_seq + 1) & 7
        else:
            self.p2_cnt -= 1

        if self.tri_cnt <= 0:
            self.tri_cnt = max(1, self.tri_timer + 1)
            if self.tri_len and self.tri_lin_cnt and self.tri_timer > 1:
                self.tri_seq = (self.tri_seq + 1) & 31
        else:
            self.tri_cnt -= 1

        if self.noi_cnt <= 0:
            self.noi_cnt = max(1, self.noi_period)
            tap = 6 if self.noi_mode else 1
            feedback = (self.noi_shift & 1) ^ ((self.noi_shift >> tap) & 1)
            self.noi_shift = ((self.noi_shift >> 1) | (feedback << 14)) & 0x7FFF
        else:
            self.noi_cnt -= 1

    def _pulse(self, duty, seq, timer, length, ce, vol, env, bit):
        if not (self.en & bit) or length == 0 or timer < 8:
            return 0
        out = vol if ce else env
        return out if _DUTY[duty][seq & 7] else 0

    def _triangle(self):
        if not (self.en & 0x04) or self.tri_len == 0 or self.tri_lin_cnt == 0 or self.tri_timer <= 1:
            return 0
        return _TRI_SEQ[self.tri_seq & 31]

    def _noise(self):
        if not (self.en & 0x08) or self.noi_len == 0 or (self.noi_shift & 1):
            return 0
        return self.noi_vol if self.noi_ce else self.noi_env_vol

    def _mix_sample(self):
        p1 = self._pulse(self.p1_duty, self.p1_seq, self.p1_timer, self.p1_len,
                         self.p1_ce, self.p1_vol, self.p1_env_vol, 0x01)
        p2 = self._pulse(self.p2_duty, self.p2_seq, self.p2_timer, self.p2_len,
                         self.p2_ce, self.p2_vol, self.p2_env_vol, 0x02)
        tr = self._triangle()
        no = self._noise()

        pulse_sum = p1 + p2
        pulse_out = 95.88 / ((8128.0 / pulse_sum) + 100.0) if pulse_sum else 0.0
        tnd = tr / 8227.0 + no / 12241.0
        tnd_out = 159.79 / ((1.0 / tnd) + 100.0) if tnd else 0.0
        raw = pulse_out + tnd_out

        # One-pole high-pass filter to remove DC offset.
        hp = raw - self._dc_prev + 0.995 * self._hp_prev
        self._dc_prev = raw
        self._hp_prev = hp
        return max(-32768, min(32767, int(hp * 55000)))

    def clock(self):
        self.clk += 1
        self._clock_frame_counter()
        self._clock_timers()
        self.sample_acc += 1.0
        if self.sample_acc >= self.cpf:
            self.sample_acc -= self.cpf
            self.samples.append(self._mix_sample())

    def get_samples(self):
        s = self.samples[:]
        self.samples.clear()
        return s

# =============================================================
#  AUDIO OUTPUT — optional pygame mixer backend
# =============================================================
class AudioSink:
    def __init__(self, rate=44100):
        self.rate = rate
        self.volume = 0.75
        self.enabled = False
        self.available = False
        self.reason = 'pygame not installed'
        self._pending = []
        self._sounds = deque(maxlen=8)
        self._channel = None

        if HAS_PYGAME:
            try:
                pygame.mixer.pre_init(frequency=rate, size=-16, channels=1, buffer=1024)
                pygame.mixer.init(frequency=rate, size=-16, channels=1, buffer=1024)
                self._channel = pygame.mixer.Channel(0)
                self.available = True
                self.enabled = True
                self.reason = 'pygame mixer ready'
            except Exception as exc:
                self.reason = f'audio disabled: {exc}'

    @property
    def status(self):
        if self.available:
            return 'on' if self.enabled else 'muted'
        return self.reason

    def set_enabled(self, enabled):
        self.enabled = bool(enabled) and self.available
        if not self.enabled:
            self.stop()

    def set_volume(self, volume):
        self.volume = max(0.0, min(1.0, float(volume)))

    def stop(self):
        self._pending.clear()
        if self._channel:
            try: self._channel.stop()
            except Exception: pass

    def push(self, samples):
        if not self.enabled or not self.available or not samples:
            return
        self._pending.extend(int(x) for x in samples)
        # About 1/30 s at 44.1 kHz. Small chunks keep latency low.
        if len(self._pending) < 1470:
            return
        chunk = self._pending[:2048]
        del self._pending[:2048]
        try:
            a = array('h', chunk)
            if sys.byteorder != 'little':
                a.byteswap()
            snd = pygame.mixer.Sound(buffer=a.tobytes())
            snd.set_volume(self.volume)
            self._sounds.append(snd)
            if not self._channel.get_busy():
                self._channel.play(snd)
            elif self._channel.get_queue() is None:
                self._channel.queue(snd)
            # Else drop one chunk rather than building runaway latency.
        except Exception as exc:
            self.reason = f'audio disabled: {exc}'
            self.set_enabled(False)

# =============================================================
#  CPU  — Full Ricoh 2A03 (6502 core, no decimal)
# =============================================================
class CPU:
    def __init__(self):
        self.a=self.x=self.y=0
        self.pc=0; self.sp=0xFD; self.p=0x24
        self.cycles=0; self.stall=0
        self.nmi_pin=False; self.irq_pin=False
        self.bus=None

    # ── Flags ───────────────────────────────────────────────
    def _nz(self, v):
        self.p = (self.p & 0x7D) | (0x80 if v & 0x80 else 0) | (0x02 if (v & 0xFF)==0 else 0)
        return v & 0xFF
    @property
    def C(self): return  self.p & 0x01
    @property
    def Z(self): return (self.p >> 1) & 1
    @property
    def I(self): return (self.p >> 2) & 1
    @property
    def V(self): return (self.p >> 6) & 1
    @property
    def N(self): return (self.p >> 7) & 1

    def _push(self, v): self.bus.write(0x100|self.sp, v&0xFF); self.sp=(self.sp-1)&0xFF
    def _pop(self):     self.sp=(self.sp+1)&0xFF; return self.bus.read(0x100|self.sp)

    # ── Addressing ──────────────────────────────────────────
    def _imm(self):
        a=self.pc; self.pc=(self.pc+1)&0xFFFF; return a
    def _zp(self):
        a=self.bus.read(self.pc); self.pc=(self.pc+1)&0xFFFF; return a
    def _zpx(self):
        a=(self.bus.read(self.pc)+self.x)&0xFF; self.pc=(self.pc+1)&0xFFFF; return a
    def _zpy(self):
        a=(self.bus.read(self.pc)+self.y)&0xFF; self.pc=(self.pc+1)&0xFFFF; return a
    def _abs(self):
        lo=self.bus.read(self.pc); hi=self.bus.read((self.pc+1)&0xFFFF)
        self.pc=(self.pc+2)&0xFFFF; return (hi<<8)|lo
    def _abx(self, ex=True):
        b=self._abs(); a=(b+self.x)&0xFFFF
        if ex and (b&0xFF00)!=(a&0xFF00): self.cycles+=1
        return a
    def _aby(self, ex=True):
        b=self._abs(); a=(b+self.y)&0xFFFF
        if ex and (b&0xFF00)!=(a&0xFF00): self.cycles+=1
        return a
    def _ind(self):
        p=self._abs()
        lo=self.bus.read(p); hi=self.bus.read((p&0xFF00)|((p+1)&0xFF))
        return (hi<<8)|lo
    def _izx(self):
        b=(self.bus.read(self.pc)+self.x)&0xFF; self.pc=(self.pc+1)&0xFFFF
        lo=self.bus.read(b); hi=self.bus.read((b+1)&0xFF); return (hi<<8)|lo
    def _izy(self, ex=True):
        b=self.bus.read(self.pc); self.pc=(self.pc+1)&0xFFFF
        lo=self.bus.read(b); hi=self.bus.read((b+1)&0xFF)
        base=(hi<<8)|lo; a=(base+self.y)&0xFFFF
        if ex and (base&0xFF00)!=(a&0xFF00): self.cycles+=1
        return a
    def _rel(self):
        off=self.bus.read(self.pc); self.pc=(self.pc+1)&0xFFFF
        if off&0x80: off-=256
        return (self.pc+off)&0xFFFF

    def reset(self):
        lo=self.bus.read(0xFFFC); hi=self.bus.read(0xFFFD)
        self.pc=(hi<<8)|lo; self.sp=0xFD; self.p=0x24; self.cycles=7

    def nmi(self):
        self._push(self.pc>>8); self._push(self.pc&0xFF)
        self._push((self.p&~0x10)|0x20)
        self.p|=0x04
        lo=self.bus.read(0xFFFA); hi=self.bus.read(0xFFFB)
        self.pc=(hi<<8)|lo; self.cycles+=7

    def irq(self):
        if self.I: return
        self._push(self.pc>>8); self._push(self.pc&0xFF)
        self._push((self.p&~0x10)|0x20)
        self.p|=0x04
        lo=self.bus.read(0xFFFE); hi=self.bus.read(0xFFFF)
        self.pc=(hi<<8)|lo; self.cycles+=7

    def step(self):
        if self.stall>0: self.stall-=1; self.cycles+=1; return 1
        if self.nmi_pin: self.nmi_pin=False; self.nmi()
        elif self.irq_pin: self.irq_pin=False; self.irq()
        c0=self.cycles
        op=self.bus.read(self.pc); self.pc=(self.pc+1)&0xFFFF
        self._ex(op)
        return self.cycles-c0

    # ── ALU helpers ─────────────────────────────────────────
    def _adc(self,v):
        r=self.a+v+self.C
        self.p=(self.p&0x3C)|(1 if r>0xFF else 0)|(0x80 if r&0x80 else 0)|\
               (0x02 if r&0xFF==0 else 0)|(0x40 if (~(self.a^v)&(self.a^r)&0x80) else 0)
        self.a=r&0xFF
    def _sbc(self,v): self._adc(v^0xFF)
    def _cmp(self,reg,v):
        r=(reg-v)&0xFF
        self.p=(self.p&0x7C)|(1 if reg>=v else 0)|(0x80 if r&0x80 else 0)|(0x02 if r==0 else 0)
    def _bit(self,v):
        self.p=(self.p&0x3D)|(v&0xC0)|(0x02 if (self.a&v)==0 else 0)
    def _asl(self,v):
        self.p=(self.p&0xFE)|(1 if v&0x80 else 0); return self._nz((v<<1)&0xFF)
    def _lsr(self,v):
        self.p=(self.p&0xFE)|(v&1); return self._nz(v>>1)
    def _rol(self,v):
        r=((v<<1)|self.C)&0xFF; self.p=(self.p&0xFE)|(1 if v&0x80 else 0); return self._nz(r)
    def _ror(self,v):
        r=(v>>1)|(self.C<<7); self.p=(self.p&0xFE)|(v&1); return self._nz(r)
    def _br(self, cond):
        addr=self._rel(); self.cycles+=2
        if cond:
            self.cycles+=1
            if (self.pc&0xFF00)!=(addr&0xFF00): self.cycles+=1
            self.pc=addr

    # ── Opcode dispatch ─────────────────────────────────────
    def _ex(self, op):
        r=self.bus.read; w=self.bus.write
        # ── ADC ──────────────────────────────────────────────
        if   op==0x69: self._adc(r(self._imm()));  self.cycles+=2
        elif op==0x65: self._adc(r(self._zp()));   self.cycles+=3
        elif op==0x75: self._adc(r(self._zpx()));  self.cycles+=4
        elif op==0x6D: self._adc(r(self._abs()));  self.cycles+=4
        elif op==0x7D: self._adc(r(self._abx()));  self.cycles+=4
        elif op==0x79: self._adc(r(self._aby()));  self.cycles+=4
        elif op==0x61: self._adc(r(self._izx()));  self.cycles+=6
        elif op==0x71: self._adc(r(self._izy()));  self.cycles+=5
        # ── AND ──────────────────────────────────────────────
        elif op==0x29: self.a=self._nz(self.a&r(self._imm())); self.cycles+=2
        elif op==0x25: self.a=self._nz(self.a&r(self._zp()));  self.cycles+=3
        elif op==0x35: self.a=self._nz(self.a&r(self._zpx())); self.cycles+=4
        elif op==0x2D: self.a=self._nz(self.a&r(self._abs())); self.cycles+=4
        elif op==0x3D: self.a=self._nz(self.a&r(self._abx())); self.cycles+=4
        elif op==0x39: self.a=self._nz(self.a&r(self._aby())); self.cycles+=4
        elif op==0x21: self.a=self._nz(self.a&r(self._izx())); self.cycles+=6
        elif op==0x31: self.a=self._nz(self.a&r(self._izy())); self.cycles+=5
        # ── ASL ──────────────────────────────────────────────
        elif op==0x0A: self.a=self._asl(self.a); self.cycles+=2
        elif op==0x06: a=self._zp(); w(a,self._asl(r(a)));        self.cycles+=5
        elif op==0x16: a=self._zpx();w(a,self._asl(r(a)));        self.cycles+=6
        elif op==0x0E: a=self._abs();w(a,self._asl(r(a)));        self.cycles+=6
        elif op==0x1E: a=self._abx(False);w(a,self._asl(r(a)));   self.cycles+=7
        # ── Branches ─────────────────────────────────────────
        elif op==0x90: self._br(not self.C)
        elif op==0xB0: self._br(bool(self.C))
        elif op==0xF0: self._br(bool(self.Z))
        elif op==0x30: self._br(bool(self.N))
        elif op==0xD0: self._br(not self.Z)
        elif op==0x10: self._br(not self.N)
        elif op==0x50: self._br(not self.V)
        elif op==0x70: self._br(bool(self.V))
        # ── BIT ──────────────────────────────────────────────
        elif op==0x24: self._bit(r(self._zp()));  self.cycles+=3
        elif op==0x2C: self._bit(r(self._abs())); self.cycles+=4
        # ── BRK ──────────────────────────────────────────────
        elif op==0x00:
            self.pc=(self.pc+1)&0xFFFF
            self._push(self.pc>>8); self._push(self.pc&0xFF)
            self._push(self.p|0x30); self.p|=0x04
            lo=r(0xFFFE); hi=r(0xFFFF); self.pc=(hi<<8)|lo; self.cycles+=7
        # ── Clear flags ──────────────────────────────────────
        elif op==0x18: self.p&=~0x01; self.cycles+=2
        elif op==0xD8: self.p&=~0x08; self.cycles+=2
        elif op==0x58: self.p&=~0x04; self.cycles+=2
        elif op==0xB8: self.p&=~0x40; self.cycles+=2
        # ── CMP ──────────────────────────────────────────────
        elif op==0xC9: self._cmp(self.a,r(self._imm())); self.cycles+=2
        elif op==0xC5: self._cmp(self.a,r(self._zp()));  self.cycles+=3
        elif op==0xD5: self._cmp(self.a,r(self._zpx())); self.cycles+=4
        elif op==0xCD: self._cmp(self.a,r(self._abs())); self.cycles+=4
        elif op==0xDD: self._cmp(self.a,r(self._abx())); self.cycles+=4
        elif op==0xD9: self._cmp(self.a,r(self._aby())); self.cycles+=4
        elif op==0xC1: self._cmp(self.a,r(self._izx())); self.cycles+=6
        elif op==0xD1: self._cmp(self.a,r(self._izy())); self.cycles+=5
        # ── CPX ──────────────────────────────────────────────
        elif op==0xE0: self._cmp(self.x,r(self._imm())); self.cycles+=2
        elif op==0xE4: self._cmp(self.x,r(self._zp()));  self.cycles+=3
        elif op==0xEC: self._cmp(self.x,r(self._abs())); self.cycles+=4
        # ── CPY ──────────────────────────────────────────────
        elif op==0xC0: self._cmp(self.y,r(self._imm())); self.cycles+=2
        elif op==0xC4: self._cmp(self.y,r(self._zp()));  self.cycles+=3
        elif op==0xCC: self._cmp(self.y,r(self._abs())); self.cycles+=4
        # ── DEC ──────────────────────────────────────────────
        elif op==0xC6: a=self._zp(); w(a,self._nz((r(a)-1)&0xFF));          self.cycles+=5
        elif op==0xD6: a=self._zpx();w(a,self._nz((r(a)-1)&0xFF));          self.cycles+=6
        elif op==0xCE: a=self._abs();w(a,self._nz((r(a)-1)&0xFF));          self.cycles+=6
        elif op==0xDE: a=self._abx(False);w(a,self._nz((r(a)-1)&0xFF));     self.cycles+=7
        elif op==0xCA: self.x=self._nz((self.x-1)&0xFF); self.cycles+=2
        elif op==0x88: self.y=self._nz((self.y-1)&0xFF); self.cycles+=2
        # ── EOR ──────────────────────────────────────────────
        elif op==0x49: self.a=self._nz(self.a^r(self._imm())); self.cycles+=2
        elif op==0x45: self.a=self._nz(self.a^r(self._zp()));  self.cycles+=3
        elif op==0x55: self.a=self._nz(self.a^r(self._zpx())); self.cycles+=4
        elif op==0x4D: self.a=self._nz(self.a^r(self._abs())); self.cycles+=4
        elif op==0x5D: self.a=self._nz(self.a^r(self._abx())); self.cycles+=4
        elif op==0x59: self.a=self._nz(self.a^r(self._aby())); self.cycles+=4
        elif op==0x41: self.a=self._nz(self.a^r(self._izx())); self.cycles+=6
        elif op==0x51: self.a=self._nz(self.a^r(self._izy())); self.cycles+=5
        # ── INC ──────────────────────────────────────────────
        elif op==0xE6: a=self._zp(); w(a,self._nz((r(a)+1)&0xFF));          self.cycles+=5
        elif op==0xF6: a=self._zpx();w(a,self._nz((r(a)+1)&0xFF));          self.cycles+=6
        elif op==0xEE: a=self._abs();w(a,self._nz((r(a)+1)&0xFF));          self.cycles+=6
        elif op==0xFE: a=self._abx(False);w(a,self._nz((r(a)+1)&0xFF));     self.cycles+=7
        elif op==0xE8: self.x=self._nz((self.x+1)&0xFF); self.cycles+=2
        elif op==0xC8: self.y=self._nz((self.y+1)&0xFF); self.cycles+=2
        # ── JMP / JSR ────────────────────────────────────────
        elif op==0x4C: self.pc=self._abs(); self.cycles+=3
        elif op==0x6C: self.pc=self._ind(); self.cycles+=5
        elif op==0x20:
            a=self._abs()
            self._push(((self.pc-1)>>8)&0xFF); self._push((self.pc-1)&0xFF)
            self.pc=a; self.cycles+=6
        # ── LDA ──────────────────────────────────────────────
        elif op==0xA9: self.a=self._nz(r(self._imm())); self.cycles+=2
        elif op==0xA5: self.a=self._nz(r(self._zp()));  self.cycles+=3
        elif op==0xB5: self.a=self._nz(r(self._zpx())); self.cycles+=4
        elif op==0xAD: self.a=self._nz(r(self._abs())); self.cycles+=4
        elif op==0xBD: self.a=self._nz(r(self._abx())); self.cycles+=4
        elif op==0xB9: self.a=self._nz(r(self._aby())); self.cycles+=4
        elif op==0xA1: self.a=self._nz(r(self._izx())); self.cycles+=6
        elif op==0xB1: self.a=self._nz(r(self._izy())); self.cycles+=5
        # ── LDX ──────────────────────────────────────────────
        elif op==0xA2: self.x=self._nz(r(self._imm())); self.cycles+=2
        elif op==0xA6: self.x=self._nz(r(self._zp()));  self.cycles+=3
        elif op==0xB6: self.x=self._nz(r(self._zpy())); self.cycles+=4
        elif op==0xAE: self.x=self._nz(r(self._abs())); self.cycles+=4
        elif op==0xBE: self.x=self._nz(r(self._aby())); self.cycles+=4
        # ── LDY ──────────────────────────────────────────────
        elif op==0xA0: self.y=self._nz(r(self._imm())); self.cycles+=2
        elif op==0xA4: self.y=self._nz(r(self._zp()));  self.cycles+=3
        elif op==0xB4: self.y=self._nz(r(self._zpx())); self.cycles+=4
        elif op==0xAC: self.y=self._nz(r(self._abs())); self.cycles+=4
        elif op==0xBC: self.y=self._nz(r(self._abx())); self.cycles+=4
        # ── LSR ──────────────────────────────────────────────
        elif op==0x4A: self.a=self._lsr(self.a); self.cycles+=2
        elif op==0x46: a=self._zp(); w(a,self._lsr(r(a)));        self.cycles+=5
        elif op==0x56: a=self._zpx();w(a,self._lsr(r(a)));        self.cycles+=6
        elif op==0x4E: a=self._abs();w(a,self._lsr(r(a)));        self.cycles+=6
        elif op==0x5E: a=self._abx(False);w(a,self._lsr(r(a)));   self.cycles+=7
        # ── NOP (official + unofficial) ──────────────────────
        elif op==0xEA: self.cycles+=2
        elif op in(0x1A,0x3A,0x5A,0x7A,0xDA,0xFA): self.cycles+=2
        elif op in(0x04,0x44,0x64): self._zp();       self.cycles+=3
        elif op==0x0C:              self._abs();       self.cycles+=4
        elif op in(0x14,0x34,0x54,0x74,0xD4,0xF4): self._zpx(); self.cycles+=4
        elif op in(0x1C,0x3C,0x5C,0x7C,0xDC,0xFC): self._abx(); self.cycles+=4
        # ── ORA ──────────────────────────────────────────────
        elif op==0x09: self.a=self._nz(self.a|r(self._imm())); self.cycles+=2
        elif op==0x05: self.a=self._nz(self.a|r(self._zp()));  self.cycles+=3
        elif op==0x15: self.a=self._nz(self.a|r(self._zpx())); self.cycles+=4
        elif op==0x0D: self.a=self._nz(self.a|r(self._abs())); self.cycles+=4
        elif op==0x1D: self.a=self._nz(self.a|r(self._abx())); self.cycles+=4
        elif op==0x19: self.a=self._nz(self.a|r(self._aby())); self.cycles+=4
        elif op==0x01: self.a=self._nz(self.a|r(self._izx())); self.cycles+=6
        elif op==0x11: self.a=self._nz(self.a|r(self._izy())); self.cycles+=5
        # ── Stack ─────────────────────────────────────────────
        elif op==0x48: self._push(self.a);                     self.cycles+=3
        elif op==0x08: self._push(self.p|0x30);                self.cycles+=3
        elif op==0x68: self.a=self._nz(self._pop());           self.cycles+=4
        elif op==0x28: self.p=(self._pop()&~0x10)|0x20;        self.cycles+=4
        # ── ROL ──────────────────────────────────────────────
        elif op==0x2A: self.a=self._rol(self.a); self.cycles+=2
        elif op==0x26: a=self._zp(); w(a,self._rol(r(a)));        self.cycles+=5
        elif op==0x36: a=self._zpx();w(a,self._rol(r(a)));        self.cycles+=6
        elif op==0x2E: a=self._abs();w(a,self._rol(r(a)));        self.cycles+=6
        elif op==0x3E: a=self._abx(False);w(a,self._rol(r(a)));   self.cycles+=7
        # ── ROR ──────────────────────────────────────────────
        elif op==0x6A: self.a=self._ror(self.a); self.cycles+=2
        elif op==0x66: a=self._zp(); w(a,self._ror(r(a)));        self.cycles+=5
        elif op==0x76: a=self._zpx();w(a,self._ror(r(a)));        self.cycles+=6
        elif op==0x6E: a=self._abs();w(a,self._ror(r(a)));        self.cycles+=6
        elif op==0x7E: a=self._abx(False);w(a,self._ror(r(a)));   self.cycles+=7
        # ── RTI / RTS ────────────────────────────────────────
        elif op==0x40:
            self.p=(self._pop()&~0x10)|0x20
            lo=self._pop(); hi=self._pop(); self.pc=(hi<<8)|lo; self.cycles+=6
        elif op==0x60:
            lo=self._pop(); hi=self._pop(); self.pc=(((hi<<8)|lo)+1)&0xFFFF; self.cycles+=6
        # ── SBC ──────────────────────────────────────────────
        elif op==0xE9: self._sbc(r(self._imm())); self.cycles+=2
        elif op==0xEB: self._sbc(r(self._imm())); self.cycles+=2   # unofficial
        elif op==0xE5: self._sbc(r(self._zp()));  self.cycles+=3
        elif op==0xF5: self._sbc(r(self._zpx())); self.cycles+=4
        elif op==0xED: self._sbc(r(self._abs())); self.cycles+=4
        elif op==0xFD: self._sbc(r(self._abx())); self.cycles+=4
        elif op==0xF9: self._sbc(r(self._aby())); self.cycles+=4
        elif op==0xE1: self._sbc(r(self._izx())); self.cycles+=6
        elif op==0xF1: self._sbc(r(self._izy())); self.cycles+=5
        # ── Set flags ────────────────────────────────────────
        elif op==0x38: self.p|=0x01; self.cycles+=2
        elif op==0xF8: self.p|=0x08; self.cycles+=2
        elif op==0x78: self.p|=0x04; self.cycles+=2
        # ── STA ──────────────────────────────────────────────
        elif op==0x85: w(self._zp(),  self.a); self.cycles+=3
        elif op==0x95: w(self._zpx(), self.a); self.cycles+=4
        elif op==0x8D: w(self._abs(), self.a); self.cycles+=4
        elif op==0x9D: w(self._abx(False),self.a); self.cycles+=5
        elif op==0x99: w(self._aby(False),self.a); self.cycles+=5
        elif op==0x81: w(self._izx(), self.a); self.cycles+=6
        elif op==0x91: w(self._izy(False),self.a); self.cycles+=6
        # ── STX / STY ────────────────────────────────────────
        elif op==0x86: w(self._zp(),  self.x); self.cycles+=3
        elif op==0x96: w(self._zpy(), self.x); self.cycles+=4
        elif op==0x8E: w(self._abs(), self.x); self.cycles+=4
        elif op==0x84: w(self._zp(),  self.y); self.cycles+=3
        elif op==0x94: w(self._zpx(), self.y); self.cycles+=4
        elif op==0x8C: w(self._abs(), self.y); self.cycles+=4
        # ── Transfers ────────────────────────────────────────
        elif op==0xAA: self.x=self._nz(self.a);  self.cycles+=2
        elif op==0xA8: self.y=self._nz(self.a);  self.cycles+=2
        elif op==0xBA: self.x=self._nz(self.sp); self.cycles+=2
        elif op==0x8A: self.a=self._nz(self.x);  self.cycles+=2
        elif op==0x9A: self.sp=self.x;            self.cycles+=2
        elif op==0x98: self.a=self._nz(self.y);  self.cycles+=2
        # ── Unofficial: LAX ──────────────────────────────────
        elif op==0xA7: v=r(self._zp()); self.a=self.x=self._nz(v);  self.cycles+=3
        elif op==0xB7: v=r(self._zpy());self.a=self.x=self._nz(v);  self.cycles+=4
        elif op==0xAF: v=r(self._abs());self.a=self.x=self._nz(v);  self.cycles+=4
        elif op==0xBF: v=r(self._aby());self.a=self.x=self._nz(v);  self.cycles+=4
        elif op==0xA3: v=r(self._izx());self.a=self.x=self._nz(v);  self.cycles+=6
        elif op==0xB3: v=r(self._izy());self.a=self.x=self._nz(v);  self.cycles+=5
        # ── Unofficial: SAX ──────────────────────────────────
        elif op==0x87: w(self._zp(),  self.a&self.x); self.cycles+=3
        elif op==0x97: w(self._zpy(), self.a&self.x); self.cycles+=4
        elif op==0x8F: w(self._abs(), self.a&self.x); self.cycles+=4
        elif op==0x83: w(self._izx(), self.a&self.x); self.cycles+=6
        # ── Unofficial: DCP ──────────────────────────────────
        elif op==0xC7: a=self._zp();v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=5
        elif op==0xD7: a=self._zpx();v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=6
        elif op==0xCF: a=self._abs();v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=6
        elif op==0xDF: a=self._abx(False);v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=7
        elif op==0xDB: a=self._aby(False);v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=7
        elif op==0xC3: a=self._izx();v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=8
        elif op==0xD3: a=self._izy(False);v=(r(a)-1)&0xFF;w(a,v);self._cmp(self.a,v);self.cycles+=8
        # ── Unofficial: ISC ──────────────────────────────────
        elif op==0xE7: a=self._zp();v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=5
        elif op==0xF7: a=self._zpx();v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=6
        elif op==0xEF: a=self._abs();v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=6
        elif op==0xFF: a=self._abx(False);v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=7
        elif op==0xFB: a=self._aby(False);v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=7
        elif op==0xE3: a=self._izx();v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=8
        elif op==0xF3: a=self._izy(False);v=(r(a)+1)&0xFF;w(a,v);self._sbc(v);self.cycles+=8
        # ── Unofficial: SLO ──────────────────────────────────
        elif op==0x07: a=self._zp();v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=5
        elif op==0x17: a=self._zpx();v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=6
        elif op==0x0F: a=self._abs();v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=6
        elif op==0x1F: a=self._abx(False);v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=7
        elif op==0x1B: a=self._aby(False);v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=7
        elif op==0x03: a=self._izx();v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=8
        elif op==0x13: a=self._izy(False);v=self._asl(r(a));w(a,v);self.a=self._nz(self.a|v);self.cycles+=8
        # ── Unofficial: RLA ──────────────────────────────────
        elif op==0x27: a=self._zp();v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=5
        elif op==0x37: a=self._zpx();v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=6
        elif op==0x2F: a=self._abs();v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=6
        elif op==0x3F: a=self._abx(False);v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=7
        elif op==0x3B: a=self._aby(False);v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=7
        elif op==0x23: a=self._izx();v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=8
        elif op==0x33: a=self._izy(False);v=self._rol(r(a));w(a,v);self.a=self._nz(self.a&v);self.cycles+=8
        # ── Unofficial: SRE ──────────────────────────────────
        elif op==0x47: a=self._zp();v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=5
        elif op==0x57: a=self._zpx();v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=6
        elif op==0x4F: a=self._abs();v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=6
        elif op==0x5F: a=self._abx(False);v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=7
        elif op==0x5B: a=self._aby(False);v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=7
        elif op==0x43: a=self._izx();v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=8
        elif op==0x53: a=self._izy(False);v=self._lsr(r(a));w(a,v);self.a=self._nz(self.a^v);self.cycles+=8
        # ── Unofficial: RRA ──────────────────────────────────
        elif op==0x67: a=self._zp();v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=5
        elif op==0x77: a=self._zpx();v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=6
        elif op==0x6F: a=self._abs();v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=6
        elif op==0x7F: a=self._abx(False);v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=7
        elif op==0x7B: a=self._aby(False);v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=7
        elif op==0x63: a=self._izx();v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=8
        elif op==0x73: a=self._izy(False);v=self._ror(r(a));w(a,v);self._adc(v);self.cycles+=8
        # ── Fallthrough ──────────────────────────────────────
        else: self.cycles+=2

# =============================================================
#  BUS  — NES memory map
# =============================================================
class Bus:
    def __init__(self):
        self.ram    = bytearray(0x800)
        self.cpu    = None
        self.ppu    = None
        self.apu    = None
        self.mapper = None
        self.ctrl1  = self.ctrl2 = 0   # current button state
        self.c1s    = self.c2s  = 0   # shift regs
        self.strobe = 0

    def read(self, a):
        a &= 0xFFFF
        if   a < 0x2000: return self.ram[a & 0x7FF]
        elif a < 0x4000: return self.ppu.read_reg(a & 7)
        elif a == 0x4015:
            return self.apu.read(a)
        elif a == 0x4016:
            if self.strobe:
                v = (self.ctrl1 >> 7) & 1
            else:
                v = (self.c1s >> 7) & 1
                self.c1s = (self.c1s << 1) & 0xFF
            return v | 0x40
        elif a == 0x4017:
            if self.strobe:
                v = (self.ctrl2 >> 7) & 1
            else:
                v = (self.c2s >> 7) & 1
                self.c2s = (self.c2s << 1) & 0xFF
            return v | 0x40
        elif a < 0x4020: return 0
        elif a >= 0x6000: return self.mapper.cpu_read(a)
        return 0xFF

    def write(self, a, v):
        a &= 0xFFFF; v &= 0xFF
        if   a < 0x2000: self.ram[a & 0x7FF] = v
        elif a < 0x4000: self.ppu.write_reg(a & 7, v)
        elif a == 0x4014:
            base = v << 8
            data = bytearray(256)
            for i in range(256): data[i] = self.read((base+i)&0xFFFF)
            self.ppu.oam_dma(data)
            self.cpu.stall += 513 + (self.cpu.cycles & 1)
        elif a == 0x4016:
            if v & 1:  self.strobe = 1
            else:
                if self.strobe:
                    self.c1s = self.ctrl1
                    self.c2s = self.ctrl2
                self.strobe = 0
        elif a < 0x4020: self.apu.write(a, v)
        elif a >= 0x6000: self.mapper.cpu_write(a, v)

# =============================================================
#  NES CONSOLE
# =============================================================
class NES:
    def __init__(self):
        self.cpu    = CPU()
        self.ppu    = PPU()
        self.apu    = APU()
        self.bus    = Bus()
        self.mapper = None
        self.rom_data = None
        self.rom_info = ''
        self.frame_rate = 60.0
        self.region = 'NTSC'
        self.is_running = False
        self._wire()

    def _wire(self):
        self.bus.cpu = self.cpu
        self.bus.ppu = self.ppu
        self.bus.apu = self.apu
        self.bus.mapper = self.mapper
        self.cpu.bus = self.bus
        self.ppu.mapper = self.mapper
        self.ppu.nmi_cb = lambda: setattr(self.cpu, 'nmi_pin', True)

    def _cold_reset_devices(self):
        self.cpu = CPU()
        self.ppu = PPU()
        self.apu = APU()
        self.bus = Bus()
        self._wire()

    def load_rom(self, data):
        if len(data) < 16 or data[:4] != b'NES\x1a':
            return False, 'Not a valid iNES/NES 2.0 ROM'

        pb = data[4]
        cb = data[5]
        f6 = data[6]
        f7 = data[7]
        nes2 = (f7 & 0x0C) == 0x08
        mn = (f6 >> 4) | (f7 & 0xF0)
        if nes2:
            mn |= (data[8] & 0x0F) << 8

        if mn not in MAPPERS:
            return False, f'Mapper {mn} is not implemented yet. Supported: 0, 1, 2, 3, 4.'

        mi = 2 if (f6 & 0x08) else (1 if (f6 & 0x01) else 0)
        self.region = 'PAL' if (len(data) > 9 and (data[9] & 1)) else 'NTSC'
        self.frame_rate = 50.0 if self.region == 'PAL' else 60.0

        off = 16 + (512 if (f6 & 0x04) else 0)
        prg_size = pb * 16384
        chr_size = cb * 8192
        if len(data) < off + prg_size + chr_size:
            return False, 'ROM file is truncated or has an invalid iNES header.'

        prg = data[off:off + prg_size]
        chr_ = data[off + prg_size:off + prg_size + chr_size]
        cls = MAPPERS[mn]
        self.mapper = cls(prg, chr_, pb, cb)
        self.mapper.mirroring = mi
        self.rom_data = bytes(data)

        self._cold_reset_devices()
        self.bus.mapper = self.mapper
        self.ppu.mapper = self.mapper
        self.ppu.mirroring = mi
        self.cpu.reset()
        self.is_running = True
        mir = '4-screen' if mi == 2 else ('V' if mi else 'H') + '-mirror'
        self.rom_info = f"Mapper {mn} | PRG:{pb}×16KB | CHR:{cb}×8KB | {self.region} | {mir}"
        return True, self.rom_info

    def power_cycle(self):
        if not self.rom_data:
            return False, 'No ROM loaded'
        return self.load_rom(self.rom_data)

    def reset(self):
        if not self.mapper:
            return
        self.cpu.reset()
        self.apu.reset()
        self.bus.ctrl1 = self.bus.ctrl2 = 0
        self.bus.c1s = self.bus.c2s = 0
        self.is_running = True

    def run_frame(self):
        """Run one console frame and leave mixed audio in self.apu.samples."""
        target = 33247 if self.region == 'PAL' else 29781
        elapsed = 0
        while elapsed < target:
            c = self.cpu.step()
            elapsed += c
            for _ in range(c):
                self.apu.clock()
            for _ in range(c * 3):
                self.ppu.step()
                if self.ppu.frame_ready:
                    self.ppu.frame_ready = False

# =============================================================
#  GUI  — FCEUX-style Tkinter interface
# =============================================================
class NESUI:
    # FCEUX-style keyboard defaults:
    #   A=X, B=Z, Select=A/Shift, Start=S/Enter, arrows=D-pad.
    _KEYS = {
        'x':0x80, 'X':0x80, 'k':0x80, 'K':0x80,
        'z':0x40, 'Z':0x40, 'j':0x40, 'J':0x40,
        'a':0x20, 'A':0x20, 'Shift_L':0x20, 'Shift_R':0x20,
        's':0x10, 'S':0x10, 'Return':0x10,
        'Up':0x08, 'Down':0x04, 'Left':0x02, 'Right':0x01,
    }

    def __init__(self, root):
        self.root   = root
        self.nes    = NES()
        self.audio  = AudioSink(rate=self.nes.apu.rate)
        self.live   = False
        self.dead   = False
        self.scale  = 2
        self.W = 256*self.scale
        self.H = 240*self.scale
        self._img_ref = None
        self.last_rom_path = None

        self.audio_enabled_var = tk.BooleanVar(value=self.audio.enabled)
        self.volume_var = tk.IntVar(value=int(self.audio.volume * 100))

        root.title("AC's FCEUX NES EMU 0.5 — Python 3.14/Tkinter")
        root.geometry(f"{self.W}x{self.H+22}")
        root.configure(bg='#0e0e0e')
        root.resizable(True, True)

        self._menu()
        self._canvas()
        self._status()

        root.bind('<KeyPress>',   self._kd)
        root.bind('<KeyRelease>', self._ku)
        root.protocol('WM_DELETE_WINDOW', self._quit)

        threading.Thread(target=self._loop, daemon=True).start()
        self._splash()

    # ── GUI construction ────────────────────────────────────
    def _menu(self):
        _bg='#252525'; _fg='#dddddd'; _ab='#3a3a3a'
        def M(): return tk.Menu(mb, tearoff=0, bg=_bg, fg=_fg, activebackground=_ab, activeforeground='white')
        mb = tk.Menu(self.root, bg=_bg, fg=_fg, activebackground=_ab, activeforeground='white', relief='flat')

        fm = M()
        fm.add_command(label='Open ROM…   Ctrl+O', command=self._open)
        fm.add_command(label='Close ROM', command=self._close_rom)
        fm.add_separator()
        fm.add_command(label='Exit', command=self._quit)
        mb.add_cascade(label='File', menu=fm)

        em = M()
        em.add_command(label='Power / Reload ROM   F5', command=self._power)
        em.add_command(label='Reset                F6', command=self._reset)
        em.add_separator()
        em.add_command(label='Pause                P',  command=self._pause)
        em.add_command(label='Frame Advance        F8', command=self._frame_advance)
        mb.add_cascade(label='Emulation', menu=em)

        vm = M()
        for s in (1, 2, 3, 4):
            vm.add_command(label=f'{s}× ({256*s}×{240*s})', command=lambda n=s: self._rescale(n))
        mb.add_cascade(label='Video', menu=vm)

        am = M()
        am.add_checkbutton(label='Enable Sound   F9', variable=self.audio_enabled_var, command=self._toggle_audio)
        for pct in (25, 50, 75, 100):
            am.add_command(label=f'Volume {pct}%', command=lambda v=pct: self._set_volume(v))
        mb.add_cascade(label='Audio', menu=am)

        cm = M()
        cm.add_command(label='Input / Controls…', command=self._show_controls)
        mb.add_cascade(label='Config', menu=cm)

        hm = M()
        hm.add_command(label='Controls', command=self._show_controls)
        hm.add_command(label='About', command=self._about)
        mb.add_cascade(label='Help', menu=hm)

        self.root.config(menu=mb)
        self.root.bind('<Control-o>', lambda e: self._open())
        self.root.bind('<F5>', lambda e: self._power())
        self.root.bind('<F6>', lambda e: self._reset())
        self.root.bind('<F8>', lambda e: self._frame_advance())
        self.root.bind('<F9>', lambda e: self._toggle_audio_hotkey())
        self.root.bind('p',   lambda e: self._pause())
        self.root.bind('P',   lambda e: self._pause())

    def _canvas(self):
        self.cv = tk.Canvas(self.root, width=self.W, height=self.H, bg='#000', highlightthickness=0)
        self.cv.pack(fill=tk.BOTH, expand=True)
        self._si = self.cv.create_image(0, 0, anchor='nw')

    def _status(self):
        self.sv = tk.StringVar(value='No ROM loaded — File → Open ROM')
        tk.Label(self.root, textvariable=self.sv, bg='#111', fg='#aaa',
                 font=('Courier', 9), anchor='w', padx=5).pack(fill=tk.X, side=tk.BOTTOM)

    def _splash(self):
        self.cv.delete('sp')
        w, h = self.W, self.H
        self.cv.create_rectangle(0, 0, w, h, fill='#080808', tags='sp')
        self.cv.create_text(w//2, h//2-38, text="AC's FCEUX NES EMU 0.5",
                            fill='#4aa3ff', font=('Courier', 18, 'bold'), tags='sp')
        self.cv.create_text(w//2, h//2-8,  text='Python 3.14 + Tkinter NES loader',
                            fill='#bbbbbb', font=('Courier', 12), tags='sp')
        self.cv.create_text(w//2, h//2+24, text='File → Open ROM  or run with: python3.14 acnesemu.py game.nes',
                            fill='#777777', font=('Courier', 10), tags='sp')
        self.cv.create_text(w//2, h-18,    text='FCEUX keys: Z=B  X=A  A/Shift=Select  S/Enter=Start  Arrows=D-Pad',
                            fill='#555555', font=('Courier', 9), tags='sp')

    # ── Actions ─────────────────────────────────────────────
    def _open(self):
        p = filedialog.askopenfilename(
            title='Open NES ROM',
            filetypes=[('NES ROMs', '*.nes'), ('All Files', '*.*')])
        if p:
            self.open_file(p)

    def open_file(self, p):
        try:
            with open(p, 'rb') as f:
                data = f.read()
        except OSError as exc:
            messagebox.showerror('ROM Error', f'Could not open ROM:\n{exc}')
            return
        ok, msg = self.nes.load_rom(data)
        if ok:
            self.last_rom_path = p
            self.live = True
            self.audio.stop()
            self.cv.delete('sp')
            self.sv.set(f'▶  {os.path.basename(p)}   {msg}   Audio:{self.audio.status}')
        else:
            self.live = False
            messagebox.showerror('ROM Error', msg)
            self.sv.set(f'ROM load failed: {msg}')

    def _close_rom(self):
        self.live = False
        self.audio.stop()
        self.nes = NES()
        self.cv.itemconfig(self._si, image='')
        self._splash()
        self.sv.set('No ROM loaded — File → Open ROM')

    def _power(self):
        if not self.nes.rom_data:
            return
        ok, msg = self.nes.power_cycle()
        if ok:
            self.live = True
            self.audio.stop()
            name = os.path.basename(self.last_rom_path or 'ROM')
            self.sv.set(f'▶  {name}   {msg}   Audio:{self.audio.status}')
        else:
            messagebox.showerror('Power Error', msg)

    def _reset(self):
        if not self.nes.mapper:
            return
        self.nes.reset()
        self.live = True
        self.audio.stop()
        self.sv.set(self._status_text('▶'))

    def _pause(self):
        if not self.nes.mapper:
            return
        self.live = not self.live
        if not self.live:
            self.audio.stop()
        self.sv.set(self._status_text('▶' if self.live else '⏸'))

    def _frame_advance(self):
        if not self.nes.mapper:
            return
        self.live = False
        self.audio.stop()
        try:
            self.nes.run_frame()
            fb = bytes(self.nes.ppu.frame_buffer)
            self._blit(fb)
            self.sv.set(self._status_text('⏭'))
        except Exception as ex:
            self.live = False
            messagebox.showerror('Frame Advance Error', str(ex))

    def _rescale(self, s):
        self.scale = int(s)
        self.W = 256 * self.scale
        self.H = 240 * self.scale
        self.cv.config(width=self.W, height=self.H)
        self.root.geometry(f"{self.W}x{self.H+22}")
        if not self.nes.mapper:
            self._splash()

    def _toggle_audio_hotkey(self):
        self.audio_enabled_var.set(not self.audio_enabled_var.get())
        self._toggle_audio()

    def _toggle_audio(self):
        self.audio.set_enabled(self.audio_enabled_var.get())
        self.audio_enabled_var.set(self.audio.enabled)
        if not self.audio.enabled:
            self.audio.stop()
        self.sv.set(self._status_text('▶' if self.live else '⏸'))

    def _set_volume(self, pct):
        self.volume_var.set(int(pct))
        self.audio.set_volume(pct / 100.0)
        self.sv.set(self._status_text('▶' if self.live else '⏸'))

    def _quit(self):
        self.dead = True
        self.live = False
        self.audio.stop()
        try:
            self.root.destroy()
        except Exception:
            pass

    def _status_text(self, prefix):
        name = os.path.basename(self.last_rom_path or 'ROM')
        info = self.nes.rom_info or 'No ROM info'
        return f'{prefix}  {name}   {info}   Audio:{self.audio.status}   Vol:{int(self.audio.volume*100)}%'

    def _show_controls(self):
        messagebox.showinfo('FCEUX-style Controls',
            'Player 1 keyboard defaults:\n\n'
            'B Button:   Z   (alt: J)\n'
            'A Button:   X   (alt: K)\n'
            'Select:     A or Shift\n'
            'Start:      S or Enter\n'
            'D-Pad:      Arrow Keys\n\n'
            'Emulator hotkeys:\n'
            'Ctrl+O Open ROM   F5 Power   F6 Reset   P Pause\n'
            'F8 Frame Advance  F9 Sound On/Off')

    def _about(self):
        messagebox.showinfo('About',
            "AC's FCEUX NES EMU 0.5\n"
            'Python 3.14/Tkinter single-file build\n\n'
            'CPU: 6502 official + common unofficial opcodes\n'
            'PPU: Loopy scrolling, sprites, 2C02 RGB palette, grayscale/emphasis\n'
            'APU: Pulse ×2, Triangle, Noise, live pygame mixer output\n'
            'Mappers: 0 (NROM), 1 (MMC1), 2 (UxROM), 3 (CNROM), 4 (MMC3)\n\n'
            f'Pillow video: {"yes" if HAS_PIL else "no — install Pillow for faster blit"}\n'
            f'pygame audio: {self.audio.status}')

    # ── Controller ──────────────────────────────────────────
    def _button_for_event(self, e):
        return self._KEYS.get(e.keysym) or self._KEYS.get(e.keysym.lower())

    def _kd(self, e):
        b = self._button_for_event(e)
        if b:
            self.nes.bus.ctrl1 |= b

    def _ku(self, e):
        b = self._button_for_event(e)
        if b:
            self.nes.bus.ctrl1 &= (~b) & 0xFF

    # ── Render ──────────────────────────────────────────────
    def _blit(self, fb):
        if self.dead:
            return
        if HAS_PIL:
            img = Image.frombytes('RGB', (256, 240), fb)
            if self.scale != 1:
                nearest = getattr(getattr(Image, 'Resampling', Image), 'NEAREST')
                img = img.resize((self.W, self.H), nearest)
            self._img_ref = ImageTk.PhotoImage(img)
        else:
            img = tk.PhotoImage(width=256, height=240)
            rows = []
            for y in range(240):
                base = y * 256 * 3
                row = '{' + ' '.join(
                    f'#{fb[base+x*3]:02x}{fb[base+x*3+1]:02x}{fb[base+x*3+2]:02x}'
                    for x in range(256)
                ) + '}'
                rows.append(row)
            img.put(' '.join(rows))
            if self.scale != 1:
                img = img.zoom(self.scale, self.scale)
            self._img_ref = img
        self.cv.itemconfig(self._si, image=self._img_ref)

    # ── Emulation thread ────────────────────────────────────
    def _loop(self):
        while not self.dead:
            t0 = time.perf_counter()
            if self.live and self.nes.is_running:
                try:
                    self.nes.run_frame()
                    samples = self.nes.apu.get_samples()
                    self.audio.push(samples)
                    fb = bytes(self.nes.ppu.frame_buffer)
                    if not self.dead:
                        self.root.after(0, self._blit, fb)
                except tk.TclError:
                    self.dead = True
                    break
                except Exception as ex:
                    print(f'[EMU] {ex}')
                    import traceback; traceback.print_exc()
                    self.live = False
                    self.audio.stop()
            else:
                time.sleep(0.016)
            fps = self.nes.frame_rate or 60.0
            rem = (1.0 / fps) - (time.perf_counter() - t0)
            if rem > 0:
                time.sleep(rem)

# =============================================================
#  RUNTIME CYTHON STUB
# =============================================================
def _try_cython():
    try:
        import Cython
        print(f'[AC NES] Cython {Cython.__version__} available — optional shim ready')
    except ImportError:
        print('[AC NES] Pure Python mode')
    print(f'[AC NES] Pillow video: {"yes" if HAS_PIL else "no"} | pygame audio: {"yes" if HAS_PYGAME else "no"}')

# =============================================================
#  ENTRY POINT
# =============================================================
def main(argv=None):
    _try_cython()
    argv = sys.argv[1:] if argv is None else list(argv)
    root = tk.Tk()
    try:
        root.tk.call('tk', 'scaling', 1.0)
    except Exception:
        pass
    app = NESUI(root)
    if argv:
        rom_path = argv[0]
        root.after(100, lambda: app.open_file(rom_path))
    root.mainloop()

if __name__ == '__main__':
    main()
