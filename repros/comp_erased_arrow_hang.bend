# comp (pre-existing): the erased-arrow application class, C-hang
# flavor — the erased-domain lambda drops, v2 compiles to the raw
# word 1, and rd5's kept application of it livelocks the C binary;
# js_book throws TypeError: 1 is not a function. Found by fuzz.ts
# seed 8559387686525276681 (first binned as the packed-Char
# livelock), delta-reduced 2026-09-01.

import Base
def rd5(f: (@-zq: List<&2, Nat> -> U32)) -> U32:
  f(Con{3n, Nil{}}) + 1
def bu8(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def mp9(r: Map<&2, String> & Maybe<&2, String>) -> U32:
  1 + 1
def rs17() -> U32:
  v2 = {y4 => 1 : @-zq: List<&2, Nat> -> U32}
  v3 = rd5(v2)
  +v7 = bu8(U32.is_eq(1, 1))
  +v10 = mp9(Map.pop(&2, String, Map.new(&2, String), "a"))
  +r16 = (((v3 .^. v7) + v10) * v10)
  ((r16 .^. 1) .^. 1)
def main() -> IO(Unit):
  do IO<Unit>:
    w0 : Unit <- IO.print(U32.show(rs17()))
    IO.pure(Unit, Unit{})