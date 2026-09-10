# c_double_free_shared_hang.bend — leg-timeout: the C binary never prints (5.8 GB, killed); interp and JS print 934346114
# finder seed 3451617928445533985, run of 2026-09-04; see TRIAGE-2026-09-04.md class E, finder 3
# on 15b53ff this is a class B cc-fail first (the erased -g0: String field); with the class B patch it hangs
# with the g104 chain replaced by the bare D0b{...} constructor, or without the third read of sh114, C prints 934346114
import Base
type D0 is Data:
  D0a{}
  D0b{-g0: String, g1: U32, g2: U32}
def rd7(x: D0) -> U32:
  match x:
    case D0a{}:
      (127 + 0)
    case D0b{x0, x1, x2}:
      ((x1 .^. x2) * 879)
def ch11(c: Char) -> U32:
  Chr{n} = c
  n
def sl37(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl37(t, (acc * 31 + ch11(h)))
def rd36(x: String) -> U32:
  sl37(x, 20)
def bu40(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
assert fn68:
  forall +p0: Char
  F32
def fn68(p0):
  5.25
def rd69(x: F32) -> U32:
  62
def rd75(x: U32) -> U32:
  x + 20
def rd95(x: Bool) -> U32:
  bu40(x) + 47
def rd94(m: Map<&2, Bool>) -> U32:
  match m:
    case MTip{}:
      5
    case MLeaf{key, val}:
      sl37(key, 3) + rd95(val)
    case MNode{pos, lo, hi}:
      U32.from_nat(pos) + rd94(lo) + rd94(hi)
def g104(qa, -A: Kind(qa), m: Maybe<qa, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v
def us114(+s: D0, +k: U32) -> U32:
  ((rd7(s) - rd7(s)) + k)
def tf117(x: Maybe<D0>) -> Maybe<D0>:
  match x:
    case None{}:
      None{}
    case Some{x0}:
      Some{x0}
def tl125(n: String, +a0: U32) -> U32:
  match n:
    case SNil{}:
      (a0 + 2147483648)
    case SCon{h, t}:
      +hc = ch11(h)
      tl125(t, (11 * 5))
def rd126(x: U32 & String) -> U32:
  (ta, tb) = x
  rd75(ta) + rd36(tb)
def rs131() -> U32:
  v66 = {fn68(Chr{(0 % 55000)}) : F32}
  +v67 = rd69(v66)
  +sh114 = {g104(&1, D0, tf117(Some{D0b{"./\\Z", v67, 2147483648}}), D0b{"-\\", 0, 0}) : D0}
  v115 = us114(sh114, (0 + 2147483648))
  v116 = rd7(sh114) + v115
  v123 = {(tl125("y1aC", bu40(U32.is_eq(0, 0))), ("Axc!" ++ "-Y")) : U32 & String}
  v124 = rd126(v123)
  +r130 = ((((((((((((((((((((((((((((((((((((((((((((((((0 + 0) + 0) + 0) + 0) + 0) - 0) + 0) + 0) * 0) - 0) + 0) .^. 0) + 0) + 0) + 0) + 0) - 0) + 0) .^. 0) + 0) - 0) + 0) + 0) + 0) + 0) - 0) + 0) + v67) + 0) + 0) * 0) - 0) .^. 0) .^. 0) + 0) .^. 0) .^. 0) - 0) .^. 0) + 0) + 0) + 0) .^. v116) + 0) - 0) + v124) + 0) + (609 << 29n))
  (r130 .^. (bu40((r130 <= 2)) .^. bu40((r130 <= 2))))
def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs131()))
    IO.pure(Unit, Unit{})
