# repro: emit crash "null is not an object (evaluating
# 'call_kind(cb, v(EMPTY)).k')" in carbonize's bound(): a def whose only
# params are erased and whose body is a call, let-bound and then used,
# reaches a cut binding as a non-call. Regression from the comp.ts
# rewrite (e5daf2d): 971e683 prints abc in C and JS.
# Found by seeds 278084597217979855 and 9715490654356164225.
import Base
def mk(-p1: U32) -> String:
  "ab" ++ ""
def rs() -> String:
  v0 = mk(3)
  v0 ++ "c"
def main() -> IO(Unit):
  IO.print(rs())
