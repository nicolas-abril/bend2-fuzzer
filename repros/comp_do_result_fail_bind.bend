# compiler-crash (emit-c): TypeError: undefined is not an object (evaluating
# 'arm.k'). A do-block over Result whose bind is a Fail; binding a Done
# there compiles. Found by the def production, seed 17604131991226033990
# (2026-09-16).
import Base

def g() -> Result<&1, &2, String, Unit>:
  do Result<&1, &2, String, Unit>:
    bc : Bool <- Fail{"x"}
    return Unit{}

def h(r: Result<&1, &2, String, Unit>) -> U32:
  match r:
    case Fail{e}:
      1
    case Done{u}:
      2

def main() -> IO(Unit):
  IO.print(U32.show(h(g())))
