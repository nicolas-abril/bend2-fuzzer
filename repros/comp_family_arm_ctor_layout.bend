

import Base

type D0<qa, qb, -T0: Kind(qa), -T1: Kind(qb)> is Kind(qa <&> qb):
  D0a{}

type D1 is Data:
  D1a{g0: U32, g1: +D0<U32, Bool>}

type E3 is Data:
  E3a{}
  E3b{}
  E3c{}

law F2:
  for x: E3
  Data

def F2(x):
  match x:
    case E3a{}:
      Either<&2, &2, D1, Sigma<&2, &2, U32, _ => U32>>
    case E3b{}:
      String
    case E3c{}:
      D1

def mf9(n: E3) -> F2(n):
  match n:
    case E3a{}:
      Inr{(2252165573, 4294967295)}
    case E3b{}:
      U32.show(3660662224)
    case E3c{}:
      D1a{2, D0a{}}

def fn8(p0: String & String, -p1: U32 & U32, p2: @-zq: Char -> Bool) -> F2(E3c{}):
  mf9(E3c{})

def rd15(x: D0<&2, &2, U32, Bool>) -> U32:
  match x:
    case D0a{}:
      (4294967295 + 0 : U32)

def rd14(x: D1) -> U32:
  match x:
    case D1a{x0, x1}:
      ((x0 - rd15(x1) : U32) + 228 : U32)

def rd16(x: Sigma<&2, &2, U32, _ => U32>) -> U32:
  (ta, tb) = x
  (ta + tb : U32)

def rd13(x: Either<&2, &2, D1, Sigma<&2, &2, U32, _ => U32>>) -> U32:
  match x:
    case Inl{x0}:
      (rd14(x0) + 192 : U32)
    case Inr{x0}:
      (rd16(x0) + 3578802916 : U32)

def ch19(c: Char) -> U32:
  Chr{n} = c
  n

def sl18(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl18(t, (acc * 31 + ch19(h) : U32))

def rd17(x: String) -> U32:
  sl18(x, 69)

def rf12(n: E3, v: F2(n)) -> U32:
  match n:
    case E3a{}:
      rd13(v)
    case E3b{}:
      rd17(v)
    case E3c{}:
      rd14(v)

def rd11(x: F2(E3c{})) -> U32:
  rf12(E3c{}, x)

def rs36() -> U32:
  +v6 = {fn8(("!#:/XA", ":X+/gA"), (477, 9), y10 => False{}) : F2(E3c{})}
  v7 = (rd11(v6) + rd11(v6) : U32)
  +r35 = ((((0 + v7 : U32) + 0 : U32) .^. 0 : U32) + 65536 : U32)
  ((r35 + 503942837 : U32) - 503942837 : U32)

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs36()))
    IO.pure(Unit, Unit{})
