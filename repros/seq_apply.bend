import ../../bend3/bend-base/Pair
import ../../bend3/bend-base/Unit
def tl15(n: U32, a0: U32, a1: U32, a2: U32) -> U32:
  match n:
    case 0:
      (((a0 + a1) + a2) + 13)
    case 1+n:
      tl15(n, n, 11, (643 + a2))
def op55(p: (U32 & U32), u: Unit) -> (F32 -> ((U32 -> F32) -> (U32 -> U32))):
  (a51, b52) = p
      y53 => y54 => tl15(1, 634, 1)
def main() -> U32:
  v50 = ((op55((1, 317), ()))(((1.0 / 1.0) * (1.0 - 1.0)))(y56 => 1.0)(7) + 1)
  r193 = (1 - v50)
  ((r193 .&. 5) .|. (r193 .&. 1))