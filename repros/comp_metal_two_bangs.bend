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

def xt() -> U32:
  v = tl!(U32.to_nat(2065), U32.from_nat(3n))
  (v * 130 : U32)
def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- IO.print(U32.show(rs()))
    b : Unit <- IO.print(U32.show(xt()))
    IO.pure(Unit, Unit{})
