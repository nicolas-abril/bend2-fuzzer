# compiler-crash (emit-c): Error: a fork's paths hold different values. A
# parallel let whose one call passes a family value at a closed index
# (`mf(True{}) : Fm(True{})`) to a def with a dependent parameter, when the
# family's OTHER arm is filled by a native call (`String.eq`); with a
# literal there, or the call alone, it compiles. Found by the def
# production, seed 2219511069923295291 (2026-09-16).
import Base

law Fm:
  for x: Bool
  Data

def Fm(x):
  match x:
    case False{}:
      Bool
    case True{}:
      U32

def mf(n: Bool) -> Fm(n):
  match n:
    case False{}:
      String.eq("a", "b")
    case True{}:
      7

def g(+q: Bool, a: Fm(q), x: U32) -> U32:
  x

def one(b: Bool) -> U32:
  1

def r() -> U32:
  a b = one(True{}) g(True{}, mf(True{}), 3)
  (a + b : U32)

def main() -> IO(Unit):
  IO.print(U32.show(r()))
