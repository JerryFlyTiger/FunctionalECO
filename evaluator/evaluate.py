#!/usr/bin/env python3
"""Independent evaluator for Functional ECO patches (2021 CAD Contest Problem A).

Usage: evaluate.py <g1.v> <r2.v> <patch.v> [--abc /path/to/abc]

Completely independent of the C++ eco implementation:
  1. parses patch.v and computes the official contest cost
  2. applies the patch to g1.v (all-fanout change, _in semantics)
  3. checks the patched netlist is acyclic
  4. writes patched-G1 and R2 as BLIF and runs ABC 'cec' for equivalence

Exit code 0 and "PASS cost=<n>" on success; nonzero otherwise.
"""
import os
import re
import subprocess
import sys
import tempfile

GATE_TYPES = {"and", "or", "nand", "nor", "not", "buf", "xor", "xnor"}
CONSTS = {"1'b0", "1'b1"}


# ---------------- tokenizer / parser ----------------
def tokenize(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    text = re.sub(r"//[^\n]*", " ", text)
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == "\\":  # escaped identifier up to whitespace
            j = i + 1
            while j < n and not text[j].isspace():
                j += 1
            toks.append(text[i + 1 : j])  # store unescaped
            i = j
        elif c.isdigit():
            m = re.match(r"\d+'[bBdDhH][0-9a-fA-FxXzZ_]+|\d+", text[i:])
            toks.append(m.group(0))
            i += len(m.group(0))
        elif c.isalpha() or c == "_" or c == "$":
            m = re.match(r"[A-Za-z_$][A-Za-z0-9_$]*", text[i:])
            toks.append(m.group(0))
            i += len(m.group(0))
        else:
            toks.append(c)
            i += 1
    return toks


class Module:
    def __init__(self):
        self.name = ""
        self.inputs = []   # bit-level net names
        self.outputs = []
        self.gates = []    # (type, out, [ins])  -- assign becomes ("buf", lhs, [rhs])
        self.wires = set()


def parse_verilog(path):
    toks = tokenize(open(path).read())
    p = [0]

    def nxt():
        t = toks[p[0]]
        p[0] += 1
        return t

    def peek():
        return toks[p[0]] if p[0] < len(toks) else None

    def expect(s):
        t = nxt()
        if t != s:
            raise ValueError(f"{path}: expected {s!r} got {t!r}")

    def ref():
        name = nxt()
        if name in CONSTS:
            return name
        if peek() == "[":
            nxt()
            idx = nxt()
            expect("]")
            name = f"{name}[{idx}]"
        return name

    m = Module()
    expect("module")
    m.name = nxt()
    if peek() == "(":
        nxt()
        while peek() != ")":
            nxt()
        expect(")")
    expect(";")
    while True:
        t = nxt()
        if t == "endmodule":
            break
        if t in ("input", "output", "wire"):
            msb = lsb = None
            if peek() == "[":
                nxt()
                msb = int(nxt())
                expect(":")
                lsb = int(nxt())
                expect("]")
            names = []
            while True:
                names.append(nxt())
                d = nxt()
                if d == ";":
                    break
                assert d == ",", f"bad decl near {d}"
            for base in names:
                if msb is None:
                    bits = [base]
                else:
                    lo, hi = min(msb, lsb), max(msb, lsb)
                    bits = [f"{base}[{b}]" for b in range(lo, hi + 1)]
                m.wires.update(bits)
                if t == "input":
                    m.inputs += bits
                elif t == "output":
                    m.outputs += bits
        elif t == "assign":
            lhs = ref()
            expect("=")
            rhs = ref()
            expect(";")
            m.gates.append(("buf", lhs, [rhs]))
        elif t in GATE_TYPES:
            if peek() != "(":
                nxt()  # instance name
            expect("(")
            args = [ref()]
            while True:
                d = nxt()
                if d == ")":
                    break
                assert d == ",", f"bad arg near {d}"
                args.append(ref())
            expect(";")
            m.gates.append((t, args[0], args[1:]))
        else:
            raise ValueError(f"{path}: unexpected token {t!r}")
    return m


# ---------------- official cost ----------------
def patch_cost(pm):
    wires, consts, prim = set(), set(), 0
    wires.update(pm.inputs)
    wires.update(pm.outputs)
    for typ, out, ins in pm.gates:
        wires.add(out)
        prim += len(ins) - 2
        for i in ins:
            (consts if i in CONSTS else wires).add(i)
    return len(wires) + prim + len(consts)


# ---------------- apply patch ----------------
def apply_patch(g1, pm):
    """Returns (drivers, pis, po_net) for the patched circuit.
    drivers: net -> (type, [in nets]); nets referencing targets are rewritten to t##post.
    """
    targets = set(pm.outputs)
    drivers = {}
    for typ, out, ins in g1.gates:
        if out in drivers:
            raise ValueError(f"multiple drivers on {out}")
        drivers[out] = (typ, list(ins))
    pis = list(dict.fromkeys(g1.inputs))

    def post(n):  # post-patch value of net n
        return n + "$post" if n in targets else n

    # original G1 gates now read patched values
    new_drivers = {}
    for out, (typ, ins) in drivers.items():
        new_drivers[out] = (typ, [post(i) if i not in CONSTS else i for i in ins])
    # patch gates: outputs drive t##post; plain input s -> post(s); s_in -> original s
    for typ, out, ins in pm.gates:
        def pin(i):
            if i in CONSTS:
                return i
            if i.endswith("_in") and i[:-3] in targets:
                base = i[:-3]
                if base not in drivers and base not in pis:
                    raise ValueError(f"_in refers to undriven net {base}")
                return base  # original net (old driver or PI still drives it)
            if i in targets:
                return i + "$post"
            if i in pm.outputs or i in pm.inputs:
                pass
            return i if (i in drivers or i in pis or i in CONSTS) else "$patch$" + i
        o = out + "$post" if out in targets else "$patch$" + out
        if o in new_drivers:
            raise ValueError(f"patch drives {out} twice / collides")
        new_drivers[o] = (typ, [pin(i) for i in ins])
    # PO mapping
    po_net = {po: post(po) for po in g1.outputs}
    return new_drivers, pis, po_net


def check_acyclic_and_driven(drivers, pis, needed):
    """Kahn topological check on the cone of `needed`; raises on cycle/undriven net."""
    piset = set(pis)
    # reachable subgraph
    reach, stack = set(), [n for n in needed if n not in CONSTS and n not in piset]
    while stack:
        n = stack.pop()
        if n in reach:
            continue
        if n not in drivers:
            raise ValueError(f"undriven net {n}")
        reach.add(n)
        for i in drivers[n][1]:
            if i not in CONSTS and i not in piset and i not in reach:
                stack.append(i)
    # Kahn
    fanouts, indeg = {}, {}
    for n in reach:
        cnt = 0
        for i in drivers[n][1]:
            if i in reach:
                fanouts.setdefault(i, []).append(n)
                cnt += 1
        indeg[n] = cnt
    queue = [n for n in reach if indeg[n] == 0]
    done = 0
    while queue:
        n = queue.pop()
        done += 1
        for f in fanouts.get(n, ()):  # noqa: B023
            indeg[f] -= 1
            if indeg[f] == 0:
                queue.append(f)
    if done != len(reach):
        raise ValueError("combinational cycle in patched netlist")


# ---------------- BLIF emission ----------------
def names_block(typ, out, ins):
    n = len(ins)
    lines = [f".names {' '.join(ins)} {out}"]
    if typ == "and":
        lines.append("1" * n + " 1")
    elif typ == "nand":
        for k in range(n):
            lines.append("-" * k + "0" + "-" * (n - k - 1) + " 1")
    elif typ == "or":
        for k in range(n):
            lines.append("-" * k + "1" + "-" * (n - k - 1) + " 1")
    elif typ == "nor":
        lines.append("0" * n + " 1")
    elif typ in ("xor", "xnor"):
        for m in range(1 << n):
            ones = bin(m).count("1")
            val = ones % 2 if typ == "xor" else 1 - ones % 2
            if val:
                lines.append("".join(str((m >> (n - 1 - k)) & 1) for k in range(n)) + " 1")
    elif typ == "buf":
        lines.append("1 1")
    elif typ == "not":
        lines.append("0 1")
    else:
        raise ValueError(f"bad gate {typ}")
    return lines


def write_blif(path, drivers, pis, po_net, all_pis):
    """all_pis: canonical input list shared by both sides (sorted union)."""
    lines = [".model top", ".inputs " + " ".join(all_pis),
             ".outputs " + " ".join(po + "$out" for po in sorted(po_net))]
    used_consts = set()
    for out, (typ, ins) in drivers.items():
        subst = []
        for i in ins:
            if i in CONSTS:
                used_consts.add(i)
                subst.append("$c0" if i == "1'b0" else "$c1")
            else:
                subst.append(i)
        lines += names_block(typ, out, subst)
    for po, net in sorted(po_net.items()):
        if net in CONSTS:
            used_consts.add(net)
            net = "$c0" if net == "1'b0" else "$c1"
        lines += names_block("buf", po + "$out", [net])
    if used_consts:
        lines.append(".names $c0")  # empty cover = const0
    if "1'b1" in used_consts:
        lines += names_block("not", "$c1", ["$c0"])
    lines.append(".end")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


def netlist_drivers(m):
    drivers = {}
    for typ, out, ins in m.gates:
        if out in drivers:
            raise ValueError(f"multiple drivers on {out}")
        drivers[out] = (typ, list(ins))
    return drivers


# ---------------- main ----------------
def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    abc = None
    for a in sys.argv[1:]:
        if a.startswith("--abc="):
            abc = a[6:]
    if len(args) != 3:
        print(__doc__)
        return 2
    g1p, r2p, patchp = args
    if abc is None:
        abc = os.environ.get(
            "ABC", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "tools", "abc", "abc"))
    g1 = parse_verilog(g1p)
    r2 = parse_verilog(r2p)
    pm = parse_verilog(patchp)
    if pm.name != "top_eco":
        print(f"FAIL: patch module name is {pm.name!r}, expected top_eco")
        return 1

    cost = patch_cost(pm)

    # apply + structural checks
    try:
        drivers, pis, po_net = apply_patch(g1, pm)
        needed = set(po_net.values())
        check_acyclic_and_driven(drivers, pis, needed)
    except ValueError as e:
        print(f"FAIL: apply patch: {e}")
        return 1

    # equivalence check via ABC cec
    r2_drivers = netlist_drivers(r2)
    r2_po_net = {po: po for po in r2.outputs}
    if sorted(po_net) != sorted(r2_po_net):
        print("FAIL: PO name sets differ between patched G1 and R2")
        return 1
    all_pis = sorted(set(pis) | set(r2.inputs))
    with tempfile.TemporaryDirectory(prefix="ecoeval") as td:
        b1 = os.path.join(td, "patched.blif")
        b2 = os.path.join(td, "r2.blif")
        write_blif(b1, drivers, pis, po_net, all_pis)
        write_blif(b2, r2_drivers, r2.inputs, r2_po_net, all_pis)
        try:
            out = subprocess.run([abc, "-c", f"cec {b1} {b2}"], capture_output=True,
                                 text=True, timeout=600).stdout
        except FileNotFoundError:
            print(f"FAIL: abc binary not found at {abc}")
            return 1
    if "Networks are equivalent" not in out:
        print("FAIL: not equivalent")
        for ln in out.splitlines():
            if "quivalen" in ln or "differ" in ln or "Error" in ln:
                print("  abc:", ln.strip())
        return 1
    print(f"PASS cost={cost}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
