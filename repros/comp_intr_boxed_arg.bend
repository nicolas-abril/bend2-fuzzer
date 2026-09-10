# class J (2026-09-07 triage, seed 4970119188418120339): leg-diverge.
# Bool.not's return is boxed (a tail from up2, whose type is computed),
# and the Bool.or intrinsic took the pak Term as its word: C printed 0
# for a True. Fixed on nicolas3 (16e4bf3): intrinsic arguments go through emit_args.
# bend repro --to x.c: C lanes print 0 1 as the interpreter does.

import Base

def uf2(n: Nat) -> Type:
  match n:
    case 0n:
      Bool
    case 1n+p:
      Nat

def up2(n: Nat) -> uf2(n):
  match n:
    case 0n:
      Bool.not(True{})
    case 1n+p:
      22n

def bu4(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def uh2(k: Nat, v: uf2(k)) -> U32:
  match k:
    case 0n:
      bu4(v)
    case 1n+q:
      U32.from_nat(v)

def ud2(+n: Nat) -> U32:
  uh2(n, up2(n))

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(ud2(0n)))
    w0b : Unit <- IO.print(U32.show(bu4(Bool.or(Bool.not(Bool.or(False{}, False{})), False{}))))
    IO.pure(Unit, Unit{})
