# c_double_free_shared_unit_node.bend — leg-diverge: C 'error 10: memory fault' after printing the first line
# finder seed 4992019281265426712, run of 2026-09-04; see TRIAGE-2026-09-04.md
# expected (interp, JS): 12100 then 4294966046; C: 12100 then bend: error 10
# fn24's computed F32 argument only keeps the call from folding away; a literal 7.5 folds and hides the bug
import Base
type D0<qa, qb, -T0: Kind(qa)> is Kind(qa):
  D0a{g0: T0}
def ch3(c: Char) -> U32:
  Chr{n} = c
  n
def bu4(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def sl12(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl12(t, (acc * 31 + ch3(h)))
def sq13(z: Bool, rest: U32) -> U32:
  match z:
    case False{}:
      rest
    case True{}:
      (882 >> 3n)
def sp11(+s: String) -> U32:
  match s:
    case SNil{}:
      31
    case SCon{h, t}:
      sq13(String.eq(SCon{h, t}, "A"), sl12(s, 7))
@unsafe
def fn24(p0: F32, p1: Cmp, +p2: F32) -> D0<&2, &2, Unit>:
  D0a{Unit{}}
def rd26(x: Unit) -> U32:
  match x:
    case Unit{}:
      24
def rd25(x: D0<&2, &2, Unit>) -> U32:
  match x:
    case D0a{x0}:
      (rd26(x0) - 649)
def rs17() -> U32:
  +v10 = sp11("A")
  +r16 = (((((0 + 0) + 0) + v10) + 0) * v10)
  (r16 .^. (bu4((r16 <= 767)) .^. bu4((r16 <= 767))))
def xt19() -> U32:
  +v22 = {fn24((7.5 *. 2.0), GT{}, 28.25) : +D0<Unit>}
  v23 = rd25(v22) + rd25(v22)
  ((0 + v23) - (0 % 0))
def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs17()))
    w0b : Unit <- IO.print(U32.show(xt19()))
    IO.pure(Unit, Unit{})
