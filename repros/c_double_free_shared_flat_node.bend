# c_double_free_shared_flat_node.bend — leg-diverge: C prints 150011 where interp and JS print 150053
# finder seed 16502150624605953429, run of 2026-09-04; see TRIAGE-2026-09-04.md class E
# us7 computes rd10(s) .^. rd10(s), which must be 0; C's second read sees the freed node
# with the g6 chain replaced by the bare D0a{...} constructor the C value is right
import Base
type D0 is Data:
  D0a{g0: +Either<U32, Bool>, g1: +Sigma<U32, _ => Nat>, g2: U32}
  D0b{g0: U32}
def ac1(r: Array<U32> & U32, +n: U32) -> U32:
  (a4, w) = r
  w + n
def ah1b(r: Array<U32> & U32, c: Array<U32>) -> U32:
  (a3, n) = r
  +n2 = n
  ac1(Array.get(U32, c, n2), n2)
def ah1(r: Array<U32> & Array<U32>) -> U32:
  (b2, c2) = r
  ah1b(Array.size(U32, b2), c2)
def ak1(r: Array<U32> & U32, +i: U32) -> U32:
  (a1, old) = r
  old + ah1(Array.clone(a1))
def aru1(+i: U32, +s: U32) -> U32:
  a0 = Array.new(U32, 4n, s)
  a1 = a0[i] <- (s * 3 + 1)
  ak1(Array.swap(U32, a1, (i + 1), (s .^. 255)), i)
def bu3(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def mu4(m: Maybe<&2, U32>, alt: U32) -> U32:
  match m:
    case None{}:
      alt
    case Some{v}:
      v
def g6(qa, -A: Kind(qa), m: Maybe<qa, A>, d: A) -> A:
  match m:
    case None{}:
      d
    case Some{v}:
      v
def rd12(x: Bool) -> U32:
  bu3(x) + 18
def rd11(x: Either<&2, &2, U32, Bool>) -> U32:
  match x:
    case Inl{x0}:
      (x0 + 4294967295)
    case Inr{x0}:
      (rd12(x0) * 588)
def rd14(x: U32) -> U32:
  x + 84
def rd15(x: Nat) -> U32:
  U32.from_nat(x) + 46
def rd13(x: Sigma<&2, &2, U32, _ => Nat>) -> U32:
  (ta, tb) = x
  rd14(ta) + rd15(tb)
def rd10(x: D0) -> U32:
  match x:
    case D0a{x0, x1, x2}:
      (((rd11(x0) + rd13(x1)) - x2) * 14)
    case D0b{x0}:
      (x0 * 86)
def us7(+s: D0, +k: U32) -> U32:
  ((rd10(s) .^. rd10(s)) * k)
def rs20() -> U32:
  +v2 = aru1(bu3((844 <= 1370425323)), mu4(U32.read(U32.show(4294967295)), 1788155335))
  +sh7 = {g6(&2, D0, g6(&1, Maybe<&2, D0>, None{}, Some{D0a{Inr{False{}}, (2147483648, 17n), v2}}), D0b{6}) : D0}
  v8 = us7(sh7, v2)
  v9 = rd10(sh7) + v8
  +r19 = ((((v2 + 0) + v9) + 0) + (v2 / v2))
  ((((r19 << 2n) .|. (r19 >> 30n)) >> 2n) .|. (((r19 << 2n) .|. (r19 >> 30n)) << 30n))
def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs20()))
    IO.pure(Unit, Unit{})
