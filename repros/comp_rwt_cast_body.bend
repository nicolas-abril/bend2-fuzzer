# FIXED 2026-09-01 (carb Rwt drop + fuse_ban in the pure walk);
# regression-covered by .devs/check/tests/reg_rwt_carb_binders.bend
# and reg_fuse_bang_cut.bend in bend2-core.
# comp: a def whose BODY is a hole-motive rewrite (%e : F(_); w —
# base's own Word.cast shape) compiles wrong in both emitters:
# C 'an unbound binder: w', JS ReferenceError: w. Word.cast itself
# is never live-compiled from base, so the shape had no coverage.
# Hand-minimized from fuzz.ts seed 24 (2026-09-01).

import Base

type Fn0 is Data:
  Fn0z{}
  Fn0s{p: Fn0}

assert Fv0:
  forall n: Fn0
  Data

type Fv0.Nil is Data:
  Fv0n{}

type Fv0.Con<-p: Fn0> is Data:
  Fv0c{head: U32, tail: Fv0(p)}

def Fv0(n):
  match n:
    case Fn0z{}:
      Fv0.Nil
    case Fn0s{p}:
      Fv0.Con<p>

def fc0(-m: Fn0, -n: Fn0, e: {m == n : Fn0}, w: Fv0(m)) -> Fv0(n):
  %e : Fv0(_); w

def eat0(n: Fn0, v: Fv0(n), +acc: U32) -> U32:
  match n:
    case Fn0z{}:
      acc
    case Fn0s{p}:
      match v:
        case Fv0c{h, t}:
          eat0(p, t, (acc + h))

def bld0(n: Fn0, +s: U32) -> Fv0(n):
  match n:
    case Fn0z{}:
      Fv0n{}
    case Fn0s{p}:
      Fv0c{s, bld0(p, (s + 3))}

def result() -> U32:
  +n = {Fn0s{Fn0s{Fn0z{}}} : Fn0}
  eat0(n, fc0(n, n, {==}, bld0(n, 5)), 7)

def main() -> IO(Unit):
  IO.print(U32.show(result()))
