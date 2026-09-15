

import Base

law F0:
  for x: Bool
  Type

def F0(x):
  match x:
    case False{}:
      Char
    case True{}:
      Cmp & Map<&2, U32>

type Nt1 is Data:
  Nt1z{}
  Nt1s{p: Nt1}

def ad1(a: Nt1, b: Nt1) -> Nt1:
  match a:
    case Nt1z{}:
      b
    case Nt1s{p}:
      Nt1s{ad1(p, b)}

def th1(a: Nt1, -b: Nt1) -> {ad1(a, Nt1s{b}) == Nt1s{ad1(a, b)} : Nt1}:
  match a:
    case Nt1z{}:
      {==}
    case Nt1s{p}:
      %th1(p, b) : {Nt1s{ad1(p, Nt1s{b})} == Nt1s{_} : Nt1};
      {==}

def ch3(c: Char) -> U32:
  Chr{n} = c
  n

def mf8(n: Bool) -> F0(n):
  match n:
    case False{}:
      '+'
    case True{}:
      (LT{}, Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "# ", 4294967295), "!8A_!B\n-", 0))

def fn6(p0: F32) -> Bool -> F0(False{}):
  y7 => mf8(False{})

def rd12(x: Char) -> U32:
  (ch3(x) + 60 : U32)

def cu15(c: Cmp) -> U32:
  match c:
    case LT{}:
      28
    case EQ{}:
      90
    case GT{}:
      168

def rd14(x: Cmp) -> U32:
  (cu15(x) * 3 : U32)

def sl17(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl17(t, (acc * 31 + ch3(h) : U32))

def rd16(m: Map<&2, U32>) -> U32:
  match m:
    case MTip{}:
      75
    case MLeaf{key, val}:
      (sl17(key, 3) + val : U32)
    case MNode{pos, lo, hi}:
      (U32.from_nat(pos) + rd16(lo) + rd16(hi) : U32)

def rd13(x: Cmp & Map<&2, U32>) -> U32:
  (ta, tb) = x
  (rd14(ta) + rd16(tb) : U32)

def rf11(n: Bool, v: F0(n)) -> U32:
  match n:
    case False{}:
      rd12(v)
    case True{}:
      rd13(v)

def rd10(x: F0(False{})) -> U32:
  rf11(False{}, x)

def rd9(f: (Bool -> F0(False{}))) -> U32:
  rd10(f(Bool.xor(False{}, True{})))

def rd20(x: List<&2, Map<&2, U32>>) -> U32:
  match x:
    case Nil{}:
      (2897481128 + 0 : U32)
    case Con{x0, x1}:
      ((rd16(x0) .^. rd20(x1) : U32) - 3034644358 : U32)

def mf27(m: Maybe<&2, F32>, alt: F32) -> F32:
  match m:
    case None{}:
      alt
    case Some{v}:
      v

def tl30(+n: Nat, +a0: U32, +a1: U32) -> U32:
  match n:
    case 3n+p:
      tl30(p, 161661657, U32.not(812))
    case q:
      ((a0 + a1 : U32) - 2147483648 : U32)

def mu31(m: Maybe<&2, U32>, alt: U32) -> U32:
  match m:
    case None{}:
      alt
    case Some{v}:
      v

def bt32(+d: Nat, +i: U32) -> U32:
  match d:
    case 0n:
      (((i * 2654435761 : U32) .&. 8191 : U32) + i : U32)
    case 1n+q:
      a b = bt32(q, (i * 2 : U32)) bt32(q, (i * 2 + 1 : U32))
      (a + b : U32)

def bu35(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def ge36(r: Result<&1, &1, U32 & String, String>) -> U32:
  match r:
    case Done{s}:
      sl17(s, 1000)
    case Fail{e}:
      (c, m) = e
      (c + 51 : U32)

def rs22() -> U32:
  na2 = {Nt1s{Nt1s{Nt1s{Nt1z{}}}} : Nt1}
  nb2 = {Nt1s{Nt1z{}} : Nt1}
  %th1(na2, nb2) : U32;
  v2 = ch3('B')
  v4 = {fn6(30.0) : Bool -> F0(False{})}
  v5 = rd9(v4)
  +v18 = {[Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "!", 751), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "fCc,9a#f", 0)] : +List<Map<&2, U32>>}
  +v19 = (rd20(v18) + rd20(v18) : U32)
  +r21 = (((v2 + v5 : U32) * v19 : U32) + (v19 / 7 : U32) : U32)
  ((((r21 << 17n : U32) .|. (r21 >> 15n : U32) : U32) >> 17n : U32) .|. (((r21 << 17n : U32) .|. (r21 >> 15n : U32) : U32) << 15n : U32) : U32)

def xt24() -> U32:
  f25 = {(mf27(F32.read(F32.show(6.625)), 4.125) - U32.to_f32(2687998493) : F32) : F32}
  +v26 = F32.to_u32((f25 * 2.8125 : F32))
  +f28 = {7.75 : F32}
  v29 = F32.to_u32((f28 * 25.625 : F32))
  p33 p34 = tl30(U32.to_nat((v26 % 1853 : U32)), U32.from_nat(8n), mu31(U32.read(U32.show(v26)), 2610049180)) bt32(5n, F32.bits(F32.neg(49.0)))
  ((((v26 * v29 : U32) .^. p33 : U32) + p34 : U32) + bu35((v26 > v26 : U32)) : U32)

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs22()))
    t36a : Unit <- IO.print("fz_d481a8_372")
    t36d : Result<&1, &1, U32 & String, String> <- IO.get_env("FZ_UNSET_605")
    t36e : Unit <- IO.print(U32.show(ge36(t36d)))
    t36f : Unit <- IO.print_err("fzerr_d481a8_127")
    w0b : Unit <- IO.print(U32.show(xt24()))
    IO.pure(Unit, Unit{})
