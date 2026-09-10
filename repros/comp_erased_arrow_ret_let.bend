# comp_erased_arrow_ret_let.bend — compiler-crash "an under-applied def value: tf7"
# finder seed 2148730115300519031, run of 2026-09-04; see TRIAGE-2026-09-04.md
# expected (interp, JS): 7; C emit: Error: an under-applied def value: tf7
# with plain arrows (Unit -> U32, y5 => 7, f(Unit{})) the same program compiles
import Base
def fn4(p0: Bool, p1: List<Nat>) -> Unit -> @-zq: U32 -> U32:
  y5 => y6 => 7
def tf7(x: List<Nat>) -> List<Nat>:
  match x:
    case Nil{}:
      Nil{}
    case Con{x0, x1}:
      Con{(x0 +n 2n), tf7(x1)}
def rd9(f: Unit -> @-zq: U32 -> U32) -> U32:
  f(Unit{})(3)
def main() -> IO(Unit):
  v2 = {fn4(True{}, tf7(Nil{})) : Unit -> @-zq: U32 -> U32}
  IO.print(U32.show(rd9(v2)))
