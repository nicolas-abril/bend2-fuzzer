# comp_erased_arrow_ctr_arg.bend — compiler-crash "a constructor outside a datatype"
# finder seed 3754759287409725014, run of 2026-09-04; see TRIAGE-2026-09-04.md
# expected (interp, JS): 0; C emit: Error: a constructor outside a datatype


import Base

def cu12(c: Cmp) -> U32:
  match c:
    case LT{}:
      3
    case EQ{}:
      78
    case GT{}:
      158

def rd11(x: Cmp) -> U32:
  cu12(x) * 4

def rd10(f: (@-zq: Nat -> Cmp)) -> U32:
  rd11(f(U32.to_nat((1603886560 % 97))))

def rd9(f: (@-zq: Result<Nat, U32> -> @-zq: Nat -> Cmp)) -> U32:
  rd10(f(Fail{455n}))

def rs19() -> U32:
  +v14 = rd9(y16 => y17 => GT{})
  +r18 = (((0 + 0) * v14) * (119 + v14))
  ((r18 .^. 2147483648) .^. 2147483648)

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs19()))
    IO.pure(Unit, Unit{})
