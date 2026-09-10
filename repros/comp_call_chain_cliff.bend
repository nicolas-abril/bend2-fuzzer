# class K (2026-09-07 triage, skipped seed 1851479038319650125): a list
# literal of 303 Map.set calls in one def. Every element is a cut whose
# continuation carries all earlier results: 104k lines of C, 316
# continuations, emit 80 s on main and nicolas3 alike (25 entries
# 0.75 s, 50 1.9 s, 100 3.8 s, 200 22.6 s), cc -O1 16 s, run 0.25 s.
# The interpreter times out on it too, so the fuzzer files it as a
# skip. OPEN, compile time.

import Base

type D0<-T0: Kind(&1)> is Type:
  D0a{g0: T0}

type D1 is Data:
  D1a{g0: +Sigma<U32, _ => Bool>}
  D1b{g0: D1, g1: U32, g2: D1}
  D1c{g0: U32, g1: +Either<String, U32>}

def rd7(x: U32) -> U32:
  (x + 44 : U32)

def bu9(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def rd8(x: Bool) -> U32:
  (bu9(x) + 81 : U32)

def rd6(x: Sigma<&2, &2, U32, _ => Bool>) -> U32:
  (ta, tb) = x
  (rd7(ta) + rd8(tb) : U32)

def ch13(c: Char) -> U32:
  Chr{n} = c
  n

def sl12(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      sl12(t, (acc * 31 + ch13(h) : U32))

def rd11(x: String) -> U32:
  sl12(x, 37)

def rd10(x: Either<&2, &2, String, U32>) -> U32:
  match x:
    case Inl{x0}:
      (rd11(x0) .^. 0 : U32)
    case Inr{x0}:
      (x0 + 184 : U32)

def rd5(x: D1) -> U32:
  match x:
    case D1a{x0}:
      (rd6(x0) .^. 0 : U32)
    case D1b{x0, x1, x2}:
      (((rd5(x0) + x1 : U32) + rd5(x2) : U32) + 1462247561 : U32)
    case D1c{x0, x1}:
      ((x0 + rd10(x1) : U32) + 65536 : U32)

def us2(+s: D1, +k: U32) -> U32:
  ((rd5(s) + rd5(s) : U32) * k : U32)

def rd17(f: (Map<&1, Cmp> -> Bool)) -> U32:
  rd8(f(Map.new(&1, Cmp)))

def rd28(x: U32) -> U32:
  (x + 73 : U32)

def rd27(m: Map<&2, U32>) -> U32:
  match m:
    case MTip{}:
      91
    case MLeaf{key, val}:
      (sl12(key, 3) + rd28(val) : U32)
    case MNode{pos, lo, hi}:
      (U32.from_nat(pos) + rd27(lo) + rd27(hi) : U32)

def tl23(n: List<Map<&2, U32>>, +a0: U32, +a1: U32) -> U32:
  match n:
    case Nil{}:
      ((a0 + a1 : U32) * 7 : U32)
    case Con{m24, m25}:
      +h26 = rd27(m24)
      tl23(m25, (134 * a0 : U32), U32.from_nat(87n))

def rs19() -> U32:
  +sh2 = {D1a{(3271542987, True{})} : D1}
  v3 = us2(sh2, (6 .|. 828 : U32))
  v4 = (rd5(sh2) + v3 : U32)
  v14 = {y16 => False{} : Map<&1, Cmp> -> Bool}
  +v15 = rd17(v14)
  +r18 = ((v4 + v15 : U32) + 12 : U32)
  ((r18 .&. 367 : U32) .|. (r18 .&. U32.not(367) : U32) : U32)

def xt21() -> U32:
  v22 = tl23([Map.set(&2, U32, Map.new(&2, U32), "18+1+", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 8), "zy\"Y", 4294967295), Map.set(&2, U32, Map.new(&2, U32), "0Y", 966), Map.set(&2, U32, Map.new(&2, U32), "X+", 2), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Z:\nB", 8), "+?#Bf Zy", 15), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "C+\n", 690), "/", 165), Map.set(&2, U32, Map.new(&2, U32), "*d81b#", 3), Map.set(&2, U32, Map.new(&2, U32), "Zg", 871), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "\\b?*", 828), "", 10), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 964), " b", 11), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "xX#cB", 0), "-.ffa9A", 3), Map.set(&2, U32, Map.new(&2, U32), "-:/?", 1336017964), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 7), "B?*", 4), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "_C ", 8), "0\\bXefyY", 353), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ".*_ BY", 13), "B0", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "CZBxa,", 2), "-", 4294967295), Map.set(&2, U32, Map.new(&2, U32), "g.:C", 465), Map.set(&2, U32, Map.new(&2, U32), "01f9#g", 728), Map.set(&2, U32, Map.new(&2, U32), "-1,e", 5), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "CaB", 15), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Z\\Z!c_", 2147483648), "X0!", 13), Map.set(&2, U32, Map.new(&2, U32), "c", 10), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "", 2147483648), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "Y8/B", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "yB*Yez", 3419009433), "-Z!A", 12), Map.set(&2, U32, Map.new(&2, U32), "\\", 7), Map.set(&2, U32, Map.new(&2, U32), "x:eA#1", 5), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "b", 2), "-ga.:\\:", 9), Map.set(&2, U32, Map.new(&2, U32), "ye\" AYA", 344), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "dxf:Zf", 0), "Z1 \"Y", 9), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "?", 1904444316), "+b#yC", 7), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "X1x9/Cc0", 3473065938), "?Y# f", 65536), Map.set(&2, U32, Map.new(&2, U32), "c+zg\tz!", 885), Map.set(&2, U32, Map.new(&2, U32), "", 38), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Y,,.,C1y", 177), "Z\tfZ\"\".", 4294967295), Map.set(&2, U32, Map.new(&2, U32), "?\n9", 2108206341), Map.set(&2, U32, Map.new(&2, U32), "b.!e", 4294967295), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "#X?Z_c", 4234877206), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "9", 3), "b_\"1c\n-e", 2147483648), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ":9\\*c", 2147483648), "", 867), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "0zb", 6), "y-e", 2147483648), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "_8y1", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "#x\"", 169), "ea,Cb1", 536), Map.set(&2, U32, Map.new(&2, U32), ",", 65536), Map.set(&2, U32, Map.new(&2, U32), "1*yY", 700), Map.set(&2, U32, Map.new(&2, U32), ",#", 4076181195), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "/XY!!!8\"", 3), " .", 7), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "e!-!#", 120), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "+!/9", 2147483648), "gB!de", 871247937), Map.set(&2, U32, Map.new(&2, U32), "\"", 3123798386), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), ":a/x", 203), Map.set(&2, U32, Map.new(&2, U32), "b0,", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "__", 3), Map.set(&2, U32, Map.new(&2, U32), "fxd", 523), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "", 4085781715), Map.set(&2, U32, Map.new(&2, U32), "f.", 4), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Bzz_g.\nZ", 4294967295), "g*dXz?0", 412), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "d9C\\?/#", 13), "/", 912), Map.set(&2, U32, Map.new(&2, U32), "y yX1x", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "8Y,d\\", 8), "b80zx9", 913), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "Y\nc901,g", 3376093102), Map.set(&2, U32, Map.new(&2, U32), "*aA!ze", 332), Map.set(&2, U32, Map.new(&2, U32), "*.d#", 3347496245), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "X9", 1931262831), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 269), ",\":C8z", 1784356629), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "?,\\", 429), Map.set(&2, U32, Map.new(&2, U32), "Aez?-\n?", 952), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "._Y?d8d", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "81X,", 258), "\"", 184826573), Map.set(&2, U32, Map.new(&2, U32), ".zz!/#", 4), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "f-Z/+Xc", 4294967295), " B,.B", 4146757688), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "/x1", 3970018139), "e_?", 857), Map.set(&2, U32, Map.new(&2, U32), "d_", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "e+#9", 15), "", 4294967295), Map.set(&2, U32, Map.new(&2, U32), "./a", 0), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "d", 2147483648), "", 121), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 4294967295), "BZaeC_", 5), Map.set(&2, U32, Map.new(&2, U32), "z#a/e ", 971), Map.set(&2, U32, Map.new(&2, U32), "CzYa0\t", 13), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "_!a#y", 15), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "9by#xey-", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "", 86), Map.set(&2, U32, Map.new(&2, U32), "?:d", 8), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 488388849), "", 8), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "ezy", 2147483648), "b9g1B._X", 11), Map.set(&2, U32, Map.new(&2, U32), "\n8", 3732649957), Map.set(&2, U32, Map.new(&2, U32), "", 4060658365), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "__f-", 65536), "XBc/byf", 352), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "f18Yd!", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "d", 2), Map.set(&2, U32, Map.new(&2, U32), "fd8 0Bz\n", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "f?#xBc", 1), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "B\t01", 15), "gCX a#/-", 6), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 994), "-_adx1d#", 4013320945), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "y# CAgb", 15), "+", 0), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "_Cz8", 2147483648), "*A:YA9?", 65536), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "XY/Y1-b", 1), "_A9cY", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "y_1!# ", 5), Map.set(&2, U32, Map.new(&2, U32), "z!#!#01", 802), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "C8X:+1.", 0), "gfg*!", 2364794831), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "-f", 0), ".-9dCBe", 581), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "?:XCX", 910), "_xz\\", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ":,", 13), "Yz:1ca ", 4053659987), Map.set(&2, U32, Map.new(&2, U32), "", 2121638802), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "e", 4252813051), "b8e!Yy!9", 2572476850), Map.set(&2, U32, Map.new(&2, U32), "-zagz_C/", 11), Map.set(&2, U32, Map.new(&2, U32), "9_Af/g", 655), Map.set(&2, U32, Map.new(&2, U32), "C?", 2147483648), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "X\":A,B-:", 4), "xcd?Cx", 190), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "*:", 12), "B9e0-:g!", 239), Map.set(&2, U32, Map.new(&2, U32), "", 4294967295), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "gX:bz", 263), ".B/-+", 9), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Ac#", 4), "", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "e\\1", 0), "AB: 9xf", 897), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "+8g#X#0f", 4294967295), "", 12), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "1Zf:9yXz", 4294967295), "8-!Z8,y!", 877), Map.set(&2, U32, Map.new(&2, U32), "C:X,", 559), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "f!YfezfX", 4294967295), "e\nc+f,9z", 14), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "!A#z:,+ ", 5), "_X\"*!", 0), Map.set(&2, U32, Map.new(&2, U32), "/b./", 11), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "C?9#", 14), "Ab?-e19", 8), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 2147483648), "X\\:.B0c", 715), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "", 2147483648), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "_c*Z", 12), Map.set(&2, U32, Map.new(&2, U32), "_zabA", 3), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 13), "f \na x ", 2614406338), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "y.Ca", 15), Map.set(&2, U32, Map.new(&2, U32), "", 65536), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "x_9Z?x", 2184368032), "-.Z", 468), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "gb", 710), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "9_", 4294967295), "9#", 519), Map.set(&2, U32, Map.new(&2, U32), "d0!zX:", 192), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "g_a,", 469), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "_1,*z!0", 181), "df/e\"1z", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ",*", 0), ", 1/\\?bg", 7), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "9a8BZ*", 0), "z+z#+", 561), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "g1:C_.C", 14), "!z/xY:", 9), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "1-9X", 12), Map.set(&2, U32, Map.new(&2, U32), "eZg1B", 2), Map.set(&2, U32, Map.new(&2, U32), "e.", 911), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "aeC*", 4294967295), "Z", 14), Map.set(&2, U32, Map.new(&2, U32), "x-8!x?!", 4294967295), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), ":", 5), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "ZZfge!Y", 522), "09:zy\t", 5), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "z", 4), "z Z:Y", 4294967295), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "y\n,Xe\\", 2478246197), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "Z0", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "b0+0", 0), Map.set(&2, U32, Map.new(&2, U32), "X/Bb,*\t_", 4294967295), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ".", 5), "fcc", 14), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "-!9bedZY", 65536), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "+b:Y,", 678), "", 10), Map.set(&2, U32, Map.new(&2, U32), "81", 296), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "yz-c/!", 1740145119), "#f:bgzd,", 462), Map.set(&2, U32, Map.new(&2, U32), "*zB1xC*", 615), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "XyBz", 2147483648), Map.set(&2, U32, Map.new(&2, U32), ",a,Z", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ":A#?efeZ", 14), "/x/e?aB", 2147483648), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "zBeX", 1), "z-,?Ayc", 6), Map.set(&2, U32, Map.new(&2, U32), "bX:z!", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "\ng", 2), "/\nXa?", 949), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Ygg?+", 359), "Z\t,,*8", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 7), "*d", 996004377), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ",,:eA?", 679118128), "?-f*b", 774), Map.set(&2, U32, Map.new(&2, U32), ".f,", 0), Map.set(&2, U32, Map.new(&2, U32), "?Y", 393), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "b.BBB-C", 421), "/yXc/", 943), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 6), "e!c", 29824427), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "fegZe!", 1937746610), "a/db", 75), Map.set(&2, U32, Map.new(&2, U32), "#:,0g:,", 195), Map.set(&2, U32, Map.new(&2, U32), "1", 15), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ".,ZZA_", 13), "y.X.", 101), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "y\n-x#", 6), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "", 12), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "1_Ab0.", 1834728440), "!\n.dx9a", 704), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "cY.dZg", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "fa?:1\\", 4294967295), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "zc_A,\ny", 818046815), "Y9\nb", 12), Map.set(&2, U32, Map.new(&2, U32), ",-C-\"118", 900698391), Map.set(&2, U32, Map.new(&2, U32), "g", 1433531772), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Z19:*", 861644173), "#", 4294967295), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "9fgCz", 9), "+bA", 2147483648), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "-?yx", 0), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "Xx*cc", 458), "-", 8), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 65536), "Yd", 238), Map.set(&2, U32, Map.new(&2, U32), "*: zxb", 13), Map.set(&2, U32, Map.new(&2, U32), "A!Bz1ec", 2147483648), Map.set(&2, U32, Map.new(&2, U32), "dy!9*\t", 2628704302), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "1Ab+", 6), "", 1293430049), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), " \nz\"A\"", 134), "ez", 991), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "_9z\n11f", 4294967295), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "\nf!_fYA", 2), Map.set(&2, U32, Map.new(&2, U32), "/", 486), Map.set(&2, U32, Map.new(&2, U32), "Cfff+", 4294967295), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 4294967295), "", 3403763668), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "-,", 315), "8Y", 704), Map.new(&2, U32), Map.set(&2, U32, Map.new(&2, U32), "z", 871), Map.set(&2, U32, Map.new(&2, U32), "Y*a1/ ,", 13), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "gxg+!\n,d", 2147483648), ": CYZY", 11), Map.set(&2, U32, Map.new(&2, U32), "X", 4), Map.set(&2, U32, Map.new(&2, U32), "_:.x", 701), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), "", 4294967295), ",", 1), Map.new(&2, U32), Map.new(&2, U32), Map.set(&2, U32, Map.set(&2, U32, Map.new(&2, U32), ",?e/?bBC", 0), "dz\"X,?B.", 312), Map.new(&2, U32)], (921 .&. 13 : U32), (8 .|. 1 : U32))
  (v22 - F32.to_u32(14.25) : U32)

def main() -> IO(Unit):
  do IO<Unit>:
    w0a : Unit <- IO.print(U32.show(rs19()))
    w0b : Unit <- IO.print(U32.show(xt21()))
    IO.pure(Unit, Unit{})
