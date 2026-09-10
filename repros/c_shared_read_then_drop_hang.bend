# c_shared_read_then_drop_hang.bend — leg-timeout: the C binary never prints; interp and JS print 4294965533
# finder seed 7059584535593488608, run of 2026-09-04; see TRIAGE-2026-09-04.md class I
# needs all three: v6 from the mk8 CALL (a literal D1a is fine), the rd9 read, and fn16 dropping its unused p1: D1
# ported to the 2026-09-05 operator grammar on 2026-09-06
import Base
type D1 is Data:
  D1a{g0: String, g1: U32, g2: Char}
  D1b{g0: U32, g1: D1}
def bu4(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def mk8(+n: Nat, +s: U32) -> D1:
  match n:
    case 0n:
      D1a{"g", 6, 'a'}
    case 1n+p:
      D1b{s, mk8(p, (s * 3 + 7 : U32))}
def ch12(c: Char) -> U32:
  Chr{n} = c
  n
def sl11(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl11(t, (acc * 31 + ch12(h) : U32))
def rd10(x: String) -> U32:
  sl11(x, 58)
def rd13(x: Char) -> U32:
  (ch12(x) + 57 : U32)
def rd9(x: D1) -> U32:
  match x:
    case D1a{x0, x1, x2}:
      (((rd10(x0) + x1) - rd13(x2)) + 6 : U32)
    case D1b{x0, x1}:
      ((x0 + rd9(x1)) + 9 : U32)
def fn16(+p0: U32, p1: D1, -p2: Char) -> Bool:
  True{}
def rd17(x: Bool) -> U32:
  (bu4(x) + 1 : U32)
def rs19() -> U32:
  +v6 = {mk8(U32.to_nat(((0 + 0) % 10 : U32)), 0) : D1}
  v7 = rd9(v6)
  v14 = {fn16((7 + 0 : U32), v6, '+') : Bool}
  +v15 = rd17(v14)
  +r18 = ((((0 .^. 0) - v7) + v15) - (v15 * 3) : U32)
  ((r18 + 13) - 13 : U32)
def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs19()))
    IO.pure(Unit, Unit{})
