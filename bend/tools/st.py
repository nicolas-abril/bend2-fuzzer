# st.py : prints the fuzzer's record types and their accessors. A Bend
# record has no field syntax: a getter destructures it, a setter rebuilds
# it, so they are generated. St, the generator's state, also gets monadic
# ones (g.f reads a field as a step, s.f replaces it).
RECORDS = [
  ("Adt", "Adt", "a datatype. ctors None: opaque (built and read only through literals and calls); paren: a type-level def, applied as Name(args); rec: a constructor holds the type at its own parameters", [
    ("id", "U32"), ("name", "String"), ("qps", "List<&2, String>"), ("tps", "List<&2, TVI>"), ("ips", "List<&2, IVar>"),
    ("kind", "QT"), ("ctors", "Maybe<&2, List<&2, Ctor>>"), ("paren", "Bool"), ("base", "Bool"), ("rec", "Bool")], True),
  ("Arm", "Arm", "a family's arm; sub: the sub-index a successor arm binds, src the name it binds under first", [
    ("pat", "String"), ("sub", "Maybe<&2, String>"), ("lit", "Maybe<&2, String>"), ("ty", "T"), ("src", "String")], False),
  ("Fam", "Fam", "a type-level def by match on one index", [
    ("id", "U32"), ("name", "String"), ("idx", "T"), ("kind", "QT"), ("arms", "List<&2, Arm>"), ("done", "Bool")], True),
  ("Param", "Pm", "a value parameter of the registry; its type may name an earlier parameter n of an index type (dep: later types depend on it); mask caps an argument (0: none)", [
    ("q", "U32"), ("t", "T"), ("n", "String"), ("dep", "Bool"), ("mask", "U32")], True),
  ("Def", "Def", "a callable def: hdr lists the quantity and type parameters in the telescope's order; tm counts the leading template parameters; stuck: reaches a native claim (off the pure side)", [
    ("name", "String"), ("qps", "List<&2, String>"), ("tps", "List<&2, TVI>"), ("hdr", "List<&2, String>"), ("ps", "List<&2, Param>"),
    ("ret", "T"), ("tm", "U32"), ("stuck", "Bool"), ("base", "Bool")], True),
  ("Wip", "Wip", "a def whose leaves are being drawn: a self-call passes a current sub-field at the decreasing column", [
    ("name", "String"), ("col", "U32"), ("ps", "List<&2, U32>"), ("subs", "List<&2, V>"), ("calls", "U32")], True),
  ("V", "V", "a binder in scope (the state's dead set holds the consumed ids). many: a + binder; dec: a sub-field the self-call may descend on; of: the parameter a variable row re-binds (0: none)", [
    ("id", "U32"), ("name", "String"), ("ty", "T"), ("many", "Bool"), ("dec", "Bool"), ("of", "U32")], True),
  ("Reg", "Reg", "Base read once: its datatypes' ids by name, its defs, the defs by the head of their return type, the datatypes a type may instantiate", [
    ("ids", "Map<&2, U32>"), ("defs", "List<&2, Def>"), ("byhead", "Map<&2, List<&2, Def>>"), ("pool", "List<&2, U32>"),
    ("words", "List<&2, String>"), ("frags", "List<&2, String>"), ("wordset", "Map<&2, Unit>"), ("basenames", "List<&2, String>")], True),
  ("St", "St", "the generator's state", [
    ("rng", "U32"), ("uid", "U32"), ("vid", "U32"), ("steps", "U32"),
    ("base", "Bool"), ("free", "Bool"), ("pure", "Bool"), ("trans", "Bool"), ("tmpl", "Bool"), ("surface", "U32"),
    ("names", "Map<&2, Unit>"), ("decls", "List<&2, String>"), ("entries", "List<&2, String>"),
    ("adts", "Map<&2, Adt>"), ("own", "List<&2, U32>"), ("fams", "Map<&2, Fam>"), ("famids", "List<&2, U32>"),
    ("defs", "List<&2, Def>"), ("memo", "Map<&2, String>"), ("wip", "Map<&2, Unit>"), ("wips", "List<&2, Wip>"),
    ("mints", "U32"), ("maxmints", "U32"), ("feats", "Map<&2, U32>"), ("framed", "Map<&2, String>"),
    ("dead", "Map<&2, Unit>"), ("cost", "Map<&2, U32>"), ("reg", "Reg"), ("idn", "U32"), ("leaves", "U32")], True),
]
out = []
for ty, ctor, doc, fields, setters in RECORDS:
    names = [f for f, _ in fields]
    pat = ctor + "{" + ", ".join(names) + "}"
    out += ["# " + ty + " : " + doc, "type " + ty + " is Data:", "  " + ctor + "{" + ", ".join(f + ": " + t for f, t in fields) + "}", ""]
    for f, t in fields:
        out += [f"def {ty}.{f}?(r: {ty}) -> {t}:", f"  {pat} = r", f"  {f}", ""]
        if setters:
            others = ", ".join("v" if g == f else g for g in names)
            out += [f"def {ty}.set_{f}?(v: {t}, r: {ty}) -> {ty}:", f"  {pat} = r", f"  {ctor}{{{others}}}", ""]
        if ty == "St":
            pat_plus = "St{" + ", ".join(("+" + g) if g == f else g for g in names) + "}"
            out += [f"def g.{f}?(st: St) -> St & Maybe<&1, {t}>:", f"  {pat_plus} = st", f"  ({pat}, Some{{{f}}})", ""]
            out += [f"def s.{f}?(v: {t}, st: St) -> St & Maybe<&1, Unit>:", f"  (St.set_{f}(v, st), Some{{Unit{{}}}})", ""]
print("\n".join(out))
