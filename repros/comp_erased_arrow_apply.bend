# comp (pre-existing, unmasked 2026-09-01): an erased-domain function
# value (@-zq: A -> B) drops its lambda when compiled, but a dynamic
# application of it can keep the erased argument when the function's
# Ann is lost (inliner readback): loud flavor below dies identically
# everywhere ('a Ctr-headed spine in an expression'); with more
# context (see comp_erased_arrow_value.bend) C prints a WRONG VALUE
# and JS throws TypeError (a Char string applied as a function).

import Base

def mk(p0: Bool) -> @-zq: U32 -> Char:
  y6 => '*'

def ch(c: Char) -> U32:
  Chr{n} = c
  n

def rd(f: (@-zq: U32 -> Char)) -> U32:
  ch(f(7))

def result() -> U32:
  v3 = {mk(False{}) : @-zq: U32 -> Char}
  rd(v3)

def main() -> IO(Unit):
  IO.print(U32.show(result()))
