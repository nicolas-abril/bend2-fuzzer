

import Base

law F0:
  for x: Bool
  Type

def F0(x):
  match x:
    case False{}:
      U32
    case True{}:
      &w1: Nat -> Map<&1, Cmp>

def mf6(n: Bool) -> F0(n):
  match n:
    case False{}:
      (1517482774 .^. 0 : U32)
    case True{}:
      (1n, Map.set(&1, Cmp, Map.new(&1, Cmp), ",X?9\\?", LT{}))

def fn5(-p0: String, p1: Maybe<String>, +p2: Char) -> F0(True{}):
  mf6(True{})

def rd10(x: Nat) -> U32:
  (U32.from_nat(x) + 59 : U32)

def ch13(c: Char) -> U32:
  Chr{n} = c
  n

def sl12(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl12(t, (acc * 31 + ch13(h) : U32))

def cu15(c: Cmp) -> U32:
  match c:
    case LT{}:
      31
    case EQ{}:
      72
    case GT{}:
      155

def rd14(x: Cmp) -> U32:
  (cu15(x) * 6 : U32)

def rd11(m: Map<&1, Cmp>) -> U32:
  match m:
    case MTip{}:
      95
    case MLeaf{key, val}:
      (sl12(key, 3) + rd14(val) : U32)
    case MNode{pos, lo, hi}:
      (U32.from_nat(pos) + rd11(lo) + rd11(hi) : U32)

def rd9(x: &w1: Nat -> Map<&1, Cmp>) -> U32:
  (+w1, e) = x
  (rd11(e) + rd10(w1) : U32)

def rf8(n: Bool, v: F0(n)) -> U32:
  match n:
    case False{}:
      v
    case True{}:
      rd9(v)

def rd7(x: F0(True{})) -> U32:
  rf8(True{}, x)

def rs20() -> U32:
  v3 = {fn5("\\8.", None{}, '\u{1b}') : F0(True{})}
  v4 = rd7(v3)
  +r19 = ((((v4 .^. 0 : U32) + 0 : U32) .^. 0 : U32) - U32.not(13) : U32)
  ((r19 + 0 : U32) - 0 : U32)

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs20()))
    IO.pure(Unit, Unit{})
