# emit-c, OPEN. `Error: an unbound binder: y` — the program typechecks
# (`--checkup` is silent), the interpreter and the JS backend both print 4,
# and only the C emitter refuses it.
#
# Trigger, all four parts needed:
#   1. a constructor whose own node layout is exactly one machine word
#      (lay_node(..).ks is ["w32"] or []) — here D0a{g0: U32};
#   2. whose datatype is boxed, i.e. some other constructor forces a tag —
#      here the recursive D0b. Drop D0b's self field and it compiles;
#   3. the field spelled as a VARIABLE, not a literal. `D0a{7}` compiles;
#   4. the literal passed to a def that MATCHES on it.
#
# Introduced by bend2-core 8627c94 (2026-09-04, "hvm5_interp: ... and two
# compiler rules that let it borrow and run on stack frames"), by the
# packed-constructor borrow rule in facts_scan's `site`:
#     const s = v.$ === "Var" && env.get(probe_of(v));
#     if (!s) {
#       if (!packed(v)) { flip(lent[j] ? [ck.k, j] : null); }
#       return guard(a);
#     }
# Before the commit the flip was unconditional. Keeping the callee's
# parameter borrowed for a packed constructor literal leaves the field's
# variable with no binding at the emit site.
#
# Still open at 7c2d194 ("Keep cuts and forks in lexical blocks with shared
# value frames"), which is NOT the cause: it fails identically at 7c2d194,
# e48ce06, 60e4fc8, 38a909f, d645938, 128a3c9, d0c111a, c606898, 8c87d99
# and e913e65, and compiles at 8627c94's parent cb81bff.
#
# Found by seed 5349377474635894393 of the 2026-09-09 nine-hour run, as
# `compiler-crash: EMIT crash (emit-c): Error: an unbound binder: h` — the
# `h` there was base's own U32.read (base.bend:1332), whose arm rebuilds
# SCon{h, t}. The binder name follows whatever variable fills the field.
import Base

type D0 is Data:
  D0a{g0: U32}
  D0b{g0: U32, g2: D0}

def tl12(n: D0, a0: U32) -> U32:
  match n:
    case D0a{m13}:
      a0
    case D0b{m15, m17}:
      a0

def xt11(y: U32) -> U32:
  tl12(D0a{y}, 4)

def main() -> IO(Unit):
  IO.print(U32.show(xt11(2)))

#|4
