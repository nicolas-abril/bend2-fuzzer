# FIXED 2026-09-01 (carb Rwt drop + fuse_ban in the pure walk);
# regression-covered by .devs/check/tests/reg_rwt_carb_binders.bend
# and reg_fuse_bang_cut.bend in bend2-core.
# comp: a statement-position rewrite drops bindings that cross it.
# The book checks; compile_book dies ('an unbound binder: v8' /
# 'an under-applied def value'), and js_book emits code that throws
# ReferenceError at run — carb_book is the shared culprit.
# Found by fuzz.ts seed 22 (2026-09-01), delta-reduced.

import Base
def tl4(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 + 6)
    case 1n+p:
      tl4(p, (a0 * a0))
def bu5(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def rd7(x: U32) -> U32:
  x + 5
def rd6(x: U32 & U32) -> U32:
  (ta, tb) = x
  rd7(ta) + rd7(tb)
def tl9(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 + 504)
    case 1n+p:
      tl9(p, (a0 .|. 9))
def mb16(b: Bool, +x: U32) -> U32:
  match b:
    case False{}:
      bu5(U32.is_eq(x, 29))
    case True{}:
      bu5(U32.is_eq(x, 54))
def bt17(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      (((i * 2654435761) .&. 8191) + (65536 + 15))
    case 1n+q:
      a b = bt17(q, (i * 2)) bt17(q, (i * 2 + 1))
      (a + b)
def xt14() -> U32:
  v15 = mb16(True{}, 57)
  p18 p19 p20 = bt17(8n, 254) bt17(8n, U32.from_nat(6n)) bt17(8n, U32.inc(9))
  ((((v15 + p18) + p19) + p20) - (268 - 367))
def rs13() -> U32:
  v2 = {(tl4(U32.to_nat(bu5((3 >= 4)) % 10), (14 % 2147483648)), tl4(U32.to_nat((390 - 769) % 10), (312 + 2147483648))) : U32 & U32}
  v3 = rd6(v2)
  +v8 = bu5((rd6(((0 - 2132014851), 164)) <= tl9(U32.to_nat((2694475967 >> 35n) % 13), (4294967295 + 12))))
  qa10 = Equal.cong(U32, U32, w10 => U32.inc(w10), U32.add(2147483648, 15), U32.add(15, 2147483648), U32.add_comm(2147483648, 15))
  %qa10 : U32;
  v10 = (1 * v8)
  v11 = (((338 % 8) .&. 2147483648) + U32.from_nat(Nat.sub(43n, 1n)))
  +r12 = ((((v3 * v8) + v10) * v11) - 10)
  ((r12 + 849) - 849)
def main() -> IO(Unit):
  do IO<Unit>:
    w0 : Unit <- IO.print(U32.show(rs13()))
    IO.pure(Unit, Unit{})