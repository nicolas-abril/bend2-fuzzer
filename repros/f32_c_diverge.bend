import ../../bend3/bend-base/List
import ../../bend3/bend-base/Char
type D0<A>:
  D0a{-f0: List(Char)}
  D0b{f0: List(U32)}
def rd6(x: List(U32)) -> U32:
      1
def rd9(x: D0((F32 & F32))) -> U32:
  match x as e10:
    case D0.D0a{x0}:
      1
    case D0.D0b{x0}:
      (rd6(x0) + 14)
def fn13(p0: U32) -> (List(F32) & D0(F32)):
  ([1.0, 1.0], D0.D0b{List.Nil{}})
def rd15(x: List(F32)) -> U32:
  match x:
    case List.Cons{l1_0, List.Cons{l2_0, t}}:
      (((F32.to_u32((l1_0 * 1.0)) .^. F32.to_u32((l2_0 * 1.0))) + rd15(t)) - 367)
    case List.Cons{l1_0, List.Nil{}}:
      (F32.to_u32((l1_0 * 1.0)) + 1)
    case List.Nil{}:
      1
def rd16(x: D0(F32)) -> U32:
  match x:
    case D0.D0a{x0}:
      1
    case D0.D0b{x0}:
      (rd6(x0) + 1)
def rd14(x: (List(F32) & D0(F32))) -> U32:
  match x:
    case (x0, x1):
      ((rd15(x0) + rd16(x1)) .^. 11)
def main() -> U32:
  v11 : (List(F32) & D0(F32)) = fn13(608)
  v12 = rd14(v11)
  r17 = ((((1 + 1) .^. 1) * v12) .^. 1)
  ((((r17 << 31) .|. (r17 >> 1)) >> 31) .|. (((r17 << 31) .|. (r17 >> 1)) << 1))