# FIXED 2026-09-01 (ctr_wrap: a packed Char field builds as its bare
# code and the arm re-wraps it, so aux holds one cid); regression-
# covered by bend2-core's reg_ctr_packed_char.bend.
# C runtime livelock, ROOT-CAUSED (2026-09-01): the packed-ctor rule
# admits a field whose runtime value carries tag bits. D0b{g0: Char}
# packs as term_pak(CID_D0B, term_pak(CID_CHR, 122)) and term_make
# ORs the words: the inner Char's aux (CID_CHR=3) bleeds into the
# outer aux (CID_D0B=14, 14|3 = 15 = CID_D0A) — so this D0b value
# reads back as a D0a whose 'field' is heap address 122. rd7's D0a
# arm then loads corpus-HEADER word 122 as a closure, heap_frees it
# into the class-0 free list (allocator poisoned: heap_alloc spins
# forever at 100% CPU on every lane) and CLO_APPLYs garbage. A U32
# field packs safely (raw word, no tag bits), which is why swapping
# Char for U32 un-hangs it; js_book prints 1 and the interpreter
# agrees. Fix site: the PACKED classification must reject fields
# whose values are themselves tagged/packed terms (Char), taking
# only raw machine words. Found by fuzz.ts seeds 1270680123050758996
# / 8559387686525276681, minimized 95 -> 12 lines (~1600 oracle runs).

import Base

type D0 is Type:
  D0a{g1: Unit -> U32}
  D0b{g0: Char}

def rd7(x: D0) -> U32:
  match x:
    case D0a{x1}:
      x1(Unit{})
    case y:
      1
  
def main() -> IO(Unit):
  IO.print(U32.show(rd7(D0b{'z'})))