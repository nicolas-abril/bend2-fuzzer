import Base

def bt1(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      (((i * 2654435761 : U32) .&. 8191 : U32) + i : U32)
    case 1n+q:
      a b = bt1(q, (i * 2 : U32)) bt1(q, (i * 2 + 1 : U32))
      (a .^. b : U32)

def tl(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      tl(p, (4294967295 % a0 : U32))

def rs() -> U32:
  +p5 +p8 = bt1(3n, 17) bt1!(3n, 1678894587)
  (p5 .^. p8 : U32)

def xt(n: U32, a: U32) -> U32:
  tl!(U32.to_nat(n), a)

def main() -> IO(Unit):
  do IO<Unit>:
    z : Unit <- IO.print(U32.show(rs()))
    a1 : Unit <- IO.print(U32.show(xt(0, 3)))
    a2 : Unit <- IO.print(U32.show(xt(1, 3)))
    a3 : Unit <- IO.print(U32.show(xt(2, 3)))
    a4 : Unit <- IO.print(U32.show(xt(3, 3)))
    a5 : Unit <- IO.print(U32.show(xt(10, 3)))
    a6 : Unit <- IO.print(U32.show(xt(100, 3)))
    a7 : Unit <- IO.print(U32.show(xt(1000, 3)))
    a8 : Unit <- IO.print(U32.show(xt(2065, 3)))
    a9 : Unit <- IO.print(U32.show(xt(2066, 3)))
    b1 : Unit <- IO.print(U32.show(xt(1, 5)))
    b2 : Unit <- IO.print(U32.show(xt(2, 5)))
    b3 : Unit <- IO.print(U32.show(xt(3, 5)))
    b4 : Unit <- IO.print(U32.show(xt(2065, 5)))
    IO.pure(Unit, Unit{})
