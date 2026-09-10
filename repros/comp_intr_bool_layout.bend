# comp_intr_bool_layout.bend — leg-diverge (C fail-stop, error 3)
# finder seed 14495070507384803866, run of 2026-09-04; see TRIAGE-2026-09-04.md
# expected (interp, JS): 0; C: bend: error 3: runtime fail-stop
import Base
def ch12(c: Char) -> U32:
  Chr{n} = c
  n
def bu14(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def rs16() -> U32:
  v10 = {True{} && U32.is_eq(ch12('B'), 8) : Bool}
  bu14(v10)
def main() -> IO(Unit):
  IO.print(U32.show(rs16()))
