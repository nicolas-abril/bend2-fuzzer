# class N (2026-09-07 triage, seed 13753512098884578431): compiler-crash
# "an owned use of a borrow". D0's flat layout overlays a String box and
# an Either tag at one word; the borrow mark of the box arm followed the
# word into the tag arm, which rebuilt D0c{x0} with it. Fixed on
# nicolas3 (709e359): an arm reading a borrowed box word as a plain word
# gets its own local. Expected: 0.

import Base

type D0 is Data:
  D0a{}
  D0b{-g0: U32, g1: String}
  D0c{g0: +Either<Char, Char>}

def tf(x: D0) -> D0:
  match x:
    case D0a{}:
      D0a{}
    case D0b{x0, x1}:
      D0b{x0, (x1 ++ "!")}
    case D0c{x0}:
      D0c{x0}

def rd(x: D0) -> U32:
  match x:
    case D0a{}:
      0
    case D0b{x0, x1}:
      1
    case D0c{x0}:
      2

def main() -> IO(Unit):
  +sh = {tf(D0a{}) : D0}
  IO.print(U32.show((rd(sh) + rd(sh) : U32)))
