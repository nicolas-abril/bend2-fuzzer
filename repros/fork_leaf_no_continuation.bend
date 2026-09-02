type D1:
  D1a{}
  D1b{f0: F32, f1: U32}
type Kf42:
  Kf42a{f: U32 -> U32, k: U32}
def rd8(x: D1) -> U32:
  match x:
    case D1.D1a{}:
      1
    case D1.D1b{x0, x1}:
      ((F32.to_u32((x0 * 1.0)) * x1) .^. 8)
def ku42(c: Kf42) -> ((F32 -> U32) -> U32):
  match c:
    case Kf42.Kf42a{f, k}:
      y43 => 1
def main() -> U32:
  ar5 : [:D1] = ![1: (D1.D1b{1.0, 167} : D1), _: D1.D1a{}; 8]
  _ = ar5@ar6[11] <- (D1.D1b{1.0, 1} : D1)
  v7 = ar6[0] <- (D1.D1a{} : D1)
  v41 = (ku42(Kf42.Kf42a{y44 => 11, 1}))(y45 => 1)
  r59 = ((1 + rd8(v7)) + v41)
  (r59 .^. ((r59 < 1) .^. (r59 < 1)))