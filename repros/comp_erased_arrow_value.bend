# comp (pre-existing, unmasked 2026-09-01): the silent flavor of
# comp_erased_arrow_apply.bend -- interp answers 1475, C prints
# 1271401225, JS throws TypeError: v3$0 is not a function ('*').
# Found by fuzz.ts seed 14184753374512456789, delta-reduced.

import Base
type Fn1 is Data:
  Fn1z{}
  Fn1s{p: Fn1}
assert Fv1:
  forall n: Fn1
  Data
type Fv1.Nil is Data:
  Fv1n{}
type Fv1.Con<-p: Fn1> is Data:
  Fv1c{head: U32, tail: Fv1(p)}
def Fv1(n):
  match n:
    case Fn1z{}:
      Fv1.Nil
    case Fn1s{p}:
      Fv1.Con<p>
def fw1(k: Nat) -> Fn1:
  match k:
    case 0n:
      Fn1z{}
    case 1n+p:
      Fn1s{fw1(p)}
def fb1(n: Fn1, +s: U32) -> Fv1(n):
  match n:
    case Fn1z{}:
      Fv1n{}
    case Fn1s{p}:
      Fv1c{s, fb1(p, (s + 3))}
def fe1(n: Fn1, v: Fv1(n), +acc: U32) -> U32:
  match n:
    case Fn1z{}:
      acc
    case Fn1s{p}:
      match v:
        case Fv1c{h, t}:
          fe1(p, t, (acc + h))
def fc1(-m: Fn1, -n: Fn1, e: {m == n : Fn1}, w: Fv1(m)) -> Fv1(n):
  %e : Fv1(_); w
def fu1(k: Nat, +s: U32) -> U32:
  +n = fw1(k)
  fe1(n, fc1(n, n, {==}, fb1(n, s)), 7)
assert fn5:
  forall p0: Bool
  forall -p1: Char
  @-zq: Either<Nat, U32> -> Char
def fn5(p0, p1):
  y6 => '*'
def tf8(x: Either<Nat, U32>) -> Either<Nat, U32>:
  match x:
    case Inl{x0}:
      Inl{(x0 +n 4n)}
    case Inr{x0}:
      Inr{(x0 .^. 9)}
def ch10(c: Char) -> U32:
  Chr{n} = c
  n
def rd9(x: Char) -> U32:
  ch10(x) + 17
def rd7(f: (@-zq: Either<Nat, U32> -> Char)) -> U32:
  rd9(f(tf8(Inr{9})))
def tl14(+n: Nat, +a0: U32, +a1: U32) -> U32:
  match n:
    case 4n+p:
      tl14(p, (a1 - a0), (4294967295 % a1))
    case q:
      ((a0 * a1) - 0)
def bu15(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def cu17(c: Cmp) -> U32:
  match c:
    case LT{}:
      12
    case EQ{}:
      123
    case GT{}:
      145
def bt16(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      (((i * 2654435761) .&. 8191) .^. cu17(U32.cmp(i, i)))
    case 1n+q:
      a b = bt16(q, (i * 2)) bt16(q, (i * 2 + 1))
      (a .^. b)
def tl22(+n: Nat, +a0: U32) -> U32:
  match n:
    case 4n+p:
      tl22(p, (4294967295 .^. a0))
    case q:
      (a0 + 461118115)
def mu23(m: Maybe<&2, U32>, alt: U32) -> U32:
  match m:
    case None{}:
      alt
    case Some{v}:
      v
def tl24(+n: Nat, +a0: U32) -> U32:
  match n:
    case 0n:
      (a0 + 839)
    case 1n+p:
      tl24(p, 4294967295)
def tl25(+n: Nat, +a0: U32, +a1: U32) -> U32:
  match n:
    case 0n:
      ((a0 * a1) .^. 830)
    case 1n+p:
      tl25(p, a1, a0)
def xt13() -> U32:
  p18 p19 = tl14(U32.to_nat(bu15((2646011233 > 4294967295)) % 3762), (4294967295 * 3457837796), U32.inc(4294967295)) bt16(6n, U32.inc(2147483648))
  +f20 = {F32.ceil(((31.25 /. 11.0) %. 3.25)) : F32}
  +v21 = bu15((f20 <. (6.25 *. (F32.neg(1.0625) /. 2.25))))
  p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 = bt16!(9n, (v21 * 5)) v21 bt16(9n, U32.inc(2130479789)) tl24(U32.to_nat(F32.to_u32(6.5) % 2046), U32.from_nat(26n)) bt16(9n, U32.inc(v21)) tl25(U32.to_nat(v21 % 2177), (v21 * 4294967295), 436) bt16(9n, bu15((f20 >. 2.5))) tl22(U32.to_nat(v21 % 200), mu23(U32.read(U32.show(v21)), 668)) v21 bt16(9n, bu15(U32.is_gt(v21, v21)))
  (((((((((((((p18 + p19) + v21) + p26) + p27) + p28) .^. p29) + p30) + p31) + p32) * p33) + p34) .^. p35) - v21)
def rs12() -> U32:
  v2 = fu1(U32.to_nat((2138227993 + 757) % 12), U32.from_nat(7n))
  v3 = {fn5(Bool.and(False{}, False{}), '#') : @-zq: Either<Nat, U32> -> Char}
  +v4 = rd7(v3)
  +r11 = ((v2 * v4) + v4)
  ((((r11 << 12n) .|. (r11 >> 20n)) >> 12n) .|. (((r11 << 12n) .|. (r11 >> 20n)) << 20n))
def main() -> IO(Unit):
  do IO<Unit>:
    w0 : Unit <- IO.print(U32.show(rs12()))
    IO.pure(Unit, Unit{})