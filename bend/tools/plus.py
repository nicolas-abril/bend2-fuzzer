# plus.py : marks every parameter of a Data type reusable (+) in fuzz.bend.
# A match on a + parameter hands out + fields, so a def reads its values as
# often as it likes; closures (->), steps (G) and affine lists stay affine.
import os, re
p = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "fuzz.bend")
s = open(p).read()

def split_top(src):
    out, depth, cur = [], 0, ""
    for i, ch in enumerate(src):
        if ch in "<({":
            depth += 1
        elif ch in ">)}" and not (ch == ">" and i > 0 and src[i - 1] in "-="):
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    return out + [cur]

def fix(m):
    head, params, rest = m.group(1), m.group(2), m.group(3)
    # a step's state (a def answering X & Maybe<..>) stays plain: it is
    # threaded, and a + parameter would not be a plain function value
    st = re.match(r"^\) -> (.*) & Maybe<", rest)
    ps = []
    for prm in split_top(params):
        q = prm.strip()
        name_ty = re.match(r"^([+~-]?)(\w+): (.*)$", q, re.S)
        if name_ty and name_ty.group(1) == "":
            ty = name_ty.group(3)
            if st and ty == st.group(1):
                ps.append(q)
                continue
            affine = ty == "St" or "->" in ty or re.match(r"^(G|IO)\(", ty) or "List<&1" in ty or ty in ("Type", "Data")
            if not affine:
                q = "+" + q
        ps.append(q)
    return head + ", ".join(ps) + rest

s = re.sub(r"^(def [\w.]+\??\()(.*)(\) -> .*:)$", fix, s, flags=re.M)

# a do block's bind or let of a Data type: + too
def fix_bind(m):
    ind, name, ty, op = m.group(1), m.group(2), m.group(3), m.group(4)
    affine = ty == "St" or "->" in ty or re.match(r"^(G|IO|P)\(", ty) or "List<&1" in ty or ty in ("Type", "Data") or ty.startswith("Chan(") or ty in ("File",)
    return ind + ("" if affine else "+") + name + " : " + ty + " " + op

s = re.sub(r"^(\s+)(\w+) : (.+?) (<-|=) ", fix_bind, s, flags=re.M)
open(p, "w").write(s)
