# repro: C wrong value — a def used as a closure value receives an
# enum-like packed argument (Cmp, Bool: one tag word, no fields) as a
# boxed term_pak(cid, 0), but the flat callee reads r0 as the bare tag
# index, so every such arm dispatches as the first ctor. U32 and boxed
# args coincide in both representations and pass; a lambda passes.
# Regression from the comp.ts rewrite (e5daf2d): 971e683 prints 893.
# Found by seed 87 (--smoke). Expected 893 (GT: 146*6 + 17); C prints 257.
import Base
def cu(c: Cmp) -> U32:
  match c:
    case LT{}:
      40
    case EQ{}:
      119
    case GT{}:
      146
def rd11(x: Cmp) -> U32:
  cu(x) * 6
def rd19(f: (Cmp -> U32)) -> U32:
  f(GT{}) + 17
def main() -> IO(Unit):
  IO.print(U32.show(rd19(rd11)))
