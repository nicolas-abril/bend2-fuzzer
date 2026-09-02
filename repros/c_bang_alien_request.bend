# FIXED 2026-09-01 (carb Rwt drop + fuse_ban in the pure walk);
# regression-covered by .devs/check/tests/reg_rwt_carb_binders.bend
# and reg_fuse_bang_cut.bend in bend2-core.
# comp/C runtime: a !-marked call in this shape aborts the C binary
# with 'bend: error 6: an alien request' (SIGABRT) on every lane
# (--parallel off and --threads alike); dropping the ! runs fine
# (answer 4294966895), and js_book runs the banged spelling fine.
# Found by fuzz.ts seed 3176700307626261127 (2026-09-01), reduced.

import Base
def ch4(c: Char) -> U32:
  Chr{n} = c
  n
def cq7(z: Bool, +n: U32) -> U32:
  match z:
    case False{}:
      n + 74
    case True{}:
      (12 - 12)
def cv6(c: Char) -> U32:
  Chr{n} = c
  +n2 = n
  cq7(U32.is_eq(n2, 89), n2)
def rd13(x: Nat) -> U32:
  U32.from_nat(x) + 38
def xt10() -> U32:
  v11 = {Nat.add(4n, Nat.sub(11n, 2n)) : Nat}
  +v12 = rd13(v11)
  f14 = {21.5 *. 3.25 : F32}
  v15 = F32.to_u32((f14 *. 21.25))
  ((v12 .^. v15) + v12)
def rs9() -> U32:
  v2 = ch4('f')
  v5 = cv6!('Y')
  +r8 = ((v2 - v5) - (503 % 632))
  (r8 + (((r8 + r8) * r8) - ((r8 * r8) + (r8 * r8))))
def main() -> IO(Unit):
  do IO<Unit>:
    w0 : Unit <- IO.print(U32.show(rs9()))
    IO.pure(Unit, Unit{})