# class L (2026-09-07 triage, seed 17890114737492785208): compiler-crash
# "an unbound binder: h". A packed constructor argument stays lent and
# term_uses skipped every use under it, so the cut result its field
# reads counted zero uses and was sunk. Fixed on nicolas3: only a lent
# VARIABLE is a non-use. Expected: 32.

import Base

type D0 is Data:
  D0b{g0: U32, g1: D0}
  D0c{g0: U32, -g1: U32}

def mu32(m: Maybe<&2, U32>, alt: U32) -> U32:
  match m:
    case None{}:
      alt
    case Some{v}:
      v

def tl22(n: D0, +a0: U32) -> U32:
  match n:
    case D0b{m25, m27}:
      tl22(m27, (a0 + m25 : U32))
    case D0c{m30, m31}:
      (a0 + m30 : U32)

def xt(+k: U32) -> U32:
  tl22(D0c{mu32(U32.read(U32.show(k)), 4), 7}, 1)

def main() -> IO(Unit):
  IO.print(U32.show(xt(31)))
