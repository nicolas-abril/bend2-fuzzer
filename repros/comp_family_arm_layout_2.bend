

import Base

type E1 is Data:
  E1a{}
  E1b{}
  E1c{}

law F0:
  for x: E1
  Data

def F0(x):
  match x:
    case E1a{}:
      U32
    case E1b{}:
      {True{} == True{} : Bool}
    case E1c{}:
      Either<&2, &2, String, U32>

def ch9(c: Char) -> U32:
  Chr{n} = c
  n

def sl8(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl8(t, (acc * 31 + ch9(h) : U32))

def tf19(x: Either<&2, &2, String, U32>) -> Either<&2, &2, String, U32>:
  match x:
    case Inl{x0}:
      Inl{(x0 ++ ".g")}
    case Inr{x0}:
      Inr{(x0 .^. 8 : U32)}

def mf18(n: E1) -> F0(n):
  match n:
    case E1a{}:
      (5 / 95 : U32)
    case E1b{}:
      {==}
    case E1c{}:
      tf19(Inr{4294967295})

def fn17(p0: Cmp) -> F0(E1c{}):
  mf18(E1c{})

def rd22(x: {True{} == True{} : Bool}) -> U32:
  37

def rd24(x: String) -> U32:
  sl8(x, 50)

def rd23(x: Either<&2, &2, String, U32>) -> U32:
  match x:
    case Inl{x0}:
      (rd24(x0) + 82337129 : U32)
    case Inr{x0}:
      (x0 * 4 : U32)

def rf21(n: E1, v: F0(n)) -> U32:
  match n:
    case E1a{}:
      v
    case E1b{}:
      rd22(v)
    case E1c{}:
      rd23(v)

def rd20(x: F0(E1c{})) -> U32:
  rf21(E1c{}, x)

def rs34() -> U32:
  v15 = {fn17(U32.cmp(8, 11)) : F0(E1c{})}
  +v16 = rd20(v15)
  +r33 = (((((((0 - 0 : U32) .^. v16 : U32) + 0 : U32) + 0 : U32) - 0 : U32) - 0 : U32) + (9 * 2147483648 : U32) : U32)
  ((r33 + 3126736155 : U32) - 3126736155 : U32)

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs34()))
    IO.pure(Unit, Unit{})
