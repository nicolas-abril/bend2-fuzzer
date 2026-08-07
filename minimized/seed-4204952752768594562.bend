# comp crash: "non-runtime value after erasure: Low" (interp is fine).
# Minimal trigger -- a def that
#   (1) takes a FUNCTION-typed parameter (p0, discarded),
#   (2) takes an argument that is a RECURSIVE call (tf10(5), discarded), and
#   (3) returns a lambda that is later APPLIED (f(4)).
# Remove any one and it compiles: drop p0 -> ok; make p2 a literal or a
# NON-recursive call -> ok; bind f without applying -> ok. Found by the
# fuzzer (seed 4204952752768594562); eval yields 7, the compiled binary
# never builds.
def tf10(x: U32) -> U32:
  match x:
    case 0:
      0
    case 1+p:
      tf10(p)

def fn7(p0: (U32 -> U32), p2: U32) -> (U32 -> U32):
  y8 => 7

def main() -> U32:
  f = fn7(y9 => 7, tf10(5))
  f(4)
