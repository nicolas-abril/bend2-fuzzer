# class M (2026-09-07 triage, seed 12417925054720057398): compiler-crash
# "an owned use of a borrow". tf fused with the literal D1a{} as its lent
# argument; its empty box slot is the word "0", which entered the
# borrow set by name. Fixed on nicolas3: non-name words are aliased to
# locals before the marking. Expected: 1.

import Base

type D1 is Data:
  D1a{}
  D1c{g0: String, -g1: U32, g2: Bool}

def tf(x: D1) -> D1:
  match x:
    case D1a{}:
      D1a{}
    case D1c{x0, x1, x2}:
      D1c{(x0 ++ "d"), x1, Bool.not(x2)}

def rd(x: D1) -> U32:
  match x:
    case D1a{}:
      1
    case D1c{x0, x1, x2}:
      2

def fn(p: Unit) -> Maybe<&2, String> -> D1:
  y => tf(D1a{})

def ap(f: (Maybe<&2, String> -> D1)) -> U32:
  rd(f(None{}))

def main() -> IO(Unit):
  IO.print(U32.show(ap(fn(Unit{}))))
