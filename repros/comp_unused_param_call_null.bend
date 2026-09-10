# comp_unused_param_call_null.bend — compiler-crash: TypeError: null is not an object (evaluating 't.$')
# finder seed 2066363026174955405, run of 2026-09-04; see TRIAGE-2026-09-04.md class H
# expected (interp, JS): 0 then 0; C emit dies in bind_uses <- emit_open <- emit_expr
# either unused parameter alone triggers it; fn2 returning None{} directly instead of tf3(None{}) compiles
import Base
def tf3(x: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match x:
    case None{}:
      None{}
    case Some{x0}:
      Some{(x0 .^. 8)}
def fn2(p0: Result<&2, &1, U32, Bool>, p1: Either<&1, &2, String, U32>) -> Maybe<&2, U32>:
  tf3(None{})
def rd5(x: Maybe<&2, U32>) -> U32:
  match x:
    case None{}:
      (260 + 0)
    case Some{x0}:
      (x0 - 4)
def bu15(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1
def rs16() -> U32:
  +r14 = ((0 - 0) * 0)
  (r14 .^. (bu15((r14 <= 1621500544)) .^. bu15((r14 <= 1621500544))))
def xt18() -> U32:
  +v19 = rd5(fn2(Fail{4294967295}, Inl{"e.c"}))
  (v19 - v19)
def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs16()))
    w0b : Unit <- IO.print(U32.show(xt18()))
    IO.pure(Unit, Unit{})
