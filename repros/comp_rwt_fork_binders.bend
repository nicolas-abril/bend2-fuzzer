# FIXED 2026-09-01 (carb Rwt drop + fuse_ban in the pure walk);
# regression-covered by .devs/check/tests/reg_rwt_carb_binders.bend
# and reg_fuse_bang_cut.bend in bend2-core.
# comp: same class, fork binders (p3 p4 = ...) lost across a
# statement rewrite; C says 'an under-applied def value', JS throws
# ReferenceError: p3. Found by fuzz.ts seed 11 (2026-09-01), reduced.

import Base
type D1 is Data:
  D1a{}
  D1b{-g0: U32, g1: Unit, g2: D1}
def bt2(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      (((i * 2654435761) .&. 8191) + U32.not(882))
    case 1n+q:
      a b = bt2(q, (i * 2)) bt2(q, (i * 2 + 1))
      (a + b)
type Nt5 is Data:
  Nt5z{}
  Nt5s{p: Nt5}
def ad5(a: Nt5, b: Nt5) -> Nt5:
  match a:
    case Nt5z{}:
      Nt5s{Nt5s{b}}
    case Nt5s{p}:
      Nt5s{Nt5s{ad5(p, b)}}
def th5(a: Nt5, -b: Nt5) -> {ad5(a, Nt5s{b}) == Nt5s{ad5(a, b)} : Nt5}:
  match a:
    case Nt5z{}:
      {==}
    case Nt5s{p}:
      %th5(p, b) : {Nt5s{Nt5s{ad5(p, Nt5s{b})}} == Nt5s{Nt5s{_}} : Nt5};
      {==}
def rd12(x: Unit) -> U32:
  match x:
    case Unit{}:
      16
def rd13(x: D1) -> U32:
  match x:
    case D1a{}:
      (0 + 0)
    case D1b{x0, x1, x2}:
      ((rd12(x1) + rd13(x2)) .^. 633)
def ma8(x: D1) -> U32:
  match x:
    case D1a{}:
      (6 + 0)
    case D1b{m9, m10, m11}:
      ((rd12(m10) + rd13(m11)) + 3459419207)
def bu16(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def tf20(x: D1) -> D1:
  match x:
    case D1a{}:
      D1a{}
    case D1b{x0, x1, x2}:
      D1b{x0, x1, tf20(x2)}
def fn23(p0: Nat) -> Cmp:
  Nat.cmp(Nat.sub(2n, 18n), 304n)
def cu25(c: Cmp) -> U32:
  match c:
    case LT{}:
      24
    case EQ{}:
      93
    case GT{}:
      148
def rd24(x: Cmp) -> U32:
  cu25(x) * 5
def xt18() -> U32:
  +v19 = bu16(U32.is_ge(rd13(tf20(D1a{})), 3))
  v21 = {fn23(Nat.add(5n, 6n)) : Cmp}
  +v22 = rd24(v21)
  ((v19 + v22) + v22)
def rs17() -> U32:
  p3 p4 = bt2(2n, (4149420649 + 8)) bt2!(2n, (413 * 15))
  na6 = {Nt5s{Nt5s{Nt5s{Nt5z{}}}} : Nt5}
  nb6 = {Nt5z{} : Nt5}
  %th5(na6, nb6) : U32;
  v6 = {2147483648 : U32}
  +v7 = ma8(D1b{65536, Unit{}, D1a{}})
  v14 = (v7 / v7)
  +r15 = (((((p3 + p4) * v6) + v7) - v14) + (v7 >> 22n))
  (r15 .^. (bu16((r15 <= 1276196843)) .^. bu16((r15 <= 1276196843))))
def main() -> IO(Unit):
  do IO<Unit>:
    w0 : Unit <- IO.print(U32.show(rs17()))
    IO.pure(Unit, Unit{})