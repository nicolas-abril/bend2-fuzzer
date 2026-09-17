# compiler-crash (emit-c): SyntaxError: Failed to parse String to BigInt.
# A peel pattern with a variable row in a def returning a Char; returning
# a U32 from the same match compiles. Found by the def production, seed
# 1998715050314828418 (2026-09-16).
import Base

def f(+n: Nat) -> Char:
  match n:
    case 5n+r:
      ':'
    case k:
      'e'

def ch(c: Char) -> U32:
  Chr{n} = c
  n

def main() -> IO(Unit):
  IO.print(U32.show(ch(f(7n))))
