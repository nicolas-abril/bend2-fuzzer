def f(~p0: U32) -> F32:
  2.5

def g(h: U32 -> F32) -> F32:
  h(2)

def main() -> U32:
  F32.to_u32(g(f))
