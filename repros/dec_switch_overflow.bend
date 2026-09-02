def f(n: U32) -> U32:
  match n:
    case 3000+k:
      k
    case n:
      n

def main() -> U32:
  f(5)
