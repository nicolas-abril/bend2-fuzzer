import Base

def bt1(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      (((i * 2654435761 : U32) .&. 8191 : U32) + i : U32)
    case 1n+q:
      a b = bt1(q, (i * 2 : U32)) bt1(q, (i * 2 + 1 : U32))
      (a .^. b : U32)

def rs() -> U32:
  +p5 +p8 = bt1(3n, 17) bt1!(3n, 1678894587)
  (p5 .^. p8 : U32)

def ta(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      ta(p, (4294967291 % a0 : U32))

def tb(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      tb(p, (4294967195 % a0 : U32))

def tc(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      tc(p, (4294966295 % a0 : U32))

def td(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      td(p, (3000000000 % a0 : U32))

def te(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      te(p, (2147483649 % a0 : U32))

def tf(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 - 10 : U32)
    case 1n+p:
      tf(p, (4294967295 / a0 : U32))

def main() -> IO(Unit):
  do IO<Unit>:
    z : Unit <- IO.print(U32.show(rs()))
    s1 : Unit <- IO.print(U32.show(ta!(1n, 3)))
    s2 : Unit <- IO.print(U32.show(ta!(1n, 6)))
    s3 : Unit <- IO.print(U32.show(ta!(1n, 9)))
    s4 : Unit <- IO.print(U32.show(ta!(1n, 11)))
    s5 : Unit <- IO.print(U32.show(ta!(1n, 13)))
    s6 : Unit <- IO.print(U32.show(tb!(1n, 3)))
    s7 : Unit <- IO.print(U32.show(tb!(1n, 6)))
    s8 : Unit <- IO.print(U32.show(tb!(1n, 9)))
    s9 : Unit <- IO.print(U32.show(tb!(1n, 11)))
    s10 : Unit <- IO.print(U32.show(tb!(1n, 13)))
    s11 : Unit <- IO.print(U32.show(tc!(1n, 3)))
    s12 : Unit <- IO.print(U32.show(tc!(1n, 6)))
    s13 : Unit <- IO.print(U32.show(tc!(1n, 9)))
    s14 : Unit <- IO.print(U32.show(tc!(1n, 11)))
    s15 : Unit <- IO.print(U32.show(tc!(1n, 13)))
    s16 : Unit <- IO.print(U32.show(td!(1n, 3)))
    s17 : Unit <- IO.print(U32.show(td!(1n, 6)))
    s18 : Unit <- IO.print(U32.show(td!(1n, 9)))
    s19 : Unit <- IO.print(U32.show(td!(1n, 11)))
    s20 : Unit <- IO.print(U32.show(td!(1n, 13)))
    s21 : Unit <- IO.print(U32.show(te!(1n, 3)))
    s22 : Unit <- IO.print(U32.show(te!(1n, 6)))
    s23 : Unit <- IO.print(U32.show(te!(1n, 9)))
    s24 : Unit <- IO.print(U32.show(te!(1n, 11)))
    s25 : Unit <- IO.print(U32.show(te!(1n, 13)))
    s26 : Unit <- IO.print(U32.show(tf!(1n, 3)))
    s27 : Unit <- IO.print(U32.show(tf!(1n, 6)))
    s28 : Unit <- IO.print(U32.show(tf!(1n, 9)))
    s29 : Unit <- IO.print(U32.show(tf!(1n, 11)))
    s30 : Unit <- IO.print(U32.show(tf!(1n, 13)))
    IO.pure(Unit, Unit{})
