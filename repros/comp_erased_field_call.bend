# comp_erased_field_call.bend — compiler-crash "an under-applied def value"
# finder seed 11935020554813482187, run of 2026-09-04; see TRIAGE-2026-09-04.md
# expected (interp, JS): 0; C emit: Error: an under-applied def value: U32.show


import Base

type D1 is Data:
  D1a{g0: +Maybe<Nat>, -g1: String, g2: U32}
  D1b{}

def rd7(x: Nat) -> U32:
  U32.from_nat(x) + 21

def rd6(x: Maybe<&2, Nat>) -> U32:
  match x:
    case None{}:
      (1891431819 + 0)
    case Some{x0}:
      (rd7(x0) - 0)

def rd5(x: D1) -> U32:
  match x:
    case D1a{x0, x1, x2}:
      ((rd6(x0) - x2) - 8)
    case D1b{}:
      (2 + 0)

def us2(+s: D1, +k: U32) -> U32:
  ((rd5(s) * rd5(s)) .^. k)

def cu8(c: Cmp) -> U32:
  match c:
    case LT{}:
      16
    case EQ{}:
      122
    case GT{}:
      159

def rs15() -> U32:
  +sh2 = {D1a{Some{30n}, U32.show(1), 0} : D1}
  v3 = us2(sh2, cu8(U32.cmp(65536, 6)))
  v4 = rd5(sh2) + v3
  +r14 = (((v4 + 0) * 0) .^. 0)
  ((r14 .&. 3571953678) .|. (r14 .&. U32.not(3571953678)))

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs15()))
    IO.pure(Unit, Unit{})
