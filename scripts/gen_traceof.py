#!/usr/bin/env python3
"""Generate the event-annotated copy of Surface/Node.lean's mutual block.

Every production that can contain a node property or an alias gets a twin
`T<Name>` with one more index `(ev : List Event)`; its constructors bind one
event list per annotated premise and conclude with their concatenation in
text order.  Productions without events are reused by reference through
`Lift`.  Hand-written leaves (`TCNsProperties`, `TCNsAliasNode`) and the
combinators (`TSeq`, `TOpt`, …) live in TraceOf/Leaves.lean.

Usage: python3 scripts/gen_traceof.py > L4YAML/Proofs/Serialization/TraceOf/Node.lean
"""
import re, sys, pathlib

SRC = pathlib.Path(__file__).resolve().parent.parent / "L4YAML/Surface/Node.lean"
LEAVES = {"SCNsProperties", "SCNsAliasNode"}
COMB = {"GOpt": 1, "GStar": 1, "GPlus": 1, "GSeq": 2, "GSeq3": 3, "GAlt": 2}

def strip_comments(s: str) -> str:
    s = re.sub(r"/-[-!]?.*?-/", "", s, flags=re.S)
    s = re.sub(r"--[^\n]*", "", s)
    s = re.sub(r"@\[[^\]]*\]", "", s)
    return s

def tokenize(s: str):
    toks, i = [], 0
    while i < len(s):
        c = s[i]
        if c.isspace(): i += 1; continue
        if c == "⟨":
            depth, j = 0, i
            while j < len(s):
                if s[j] == "⟨": depth += 1
                elif s[j] == "⟩":
                    depth -= 1
                    if depth == 0: break
                j += 1
            toks.append(s[i:j+1]); i = j + 1; continue
        if c in "()": toks.append(c); i += 1; continue
        j = i
        while j < len(s) and not s[j].isspace() and s[j] not in "()⟨⟩": j += 1
        toks.append(s[i:j]); i = j
    return toks

def parse(toks):
    """tokens -> nested lists (parenthesised groups)"""
    out, stack = [], [[]]
    for t in toks:
        if t == "(": stack.append([])
        elif t == ")":
            g = stack.pop(); stack[-1].append(g)
        else: stack[-1].append(t)
    assert len(stack) == 1, toks
    return stack[0]

def show(e):
    if isinstance(e, list):
        return "(" + " ".join(show(x) for x in e) + ")"
    return e

def head(e):
    return e[0] if isinstance(e, list) else e

class Gen:
    def __init__(self, text):
        self.text = strip_comments(text)
        m = re.search(r"^mutual\n(.*?)^end\b", self.text, flags=re.S | re.M)
        self.block = m.group(1)
        self.inds = self.parse_block()
        self.names = [n for n, _, _ in self.inds]
        self.bearing = self.closure()

    def parse_block(self):
        inds = []
        parts = re.split(r"^\s*inductive\s+", self.block, flags=re.M)[1:]
        for p in parts:
            hm = re.match(r"(\w+)\s*:\s*(.*?)\s+where\s*\n(.*)", p, flags=re.S)
            name, sig, body = hm.group(1), hm.group(2).strip(), hm.group(3)
            ctors = []
            for cm in re.finditer(r"^\s*\|\s*(\w+)\s*((?:\([^()]*\)\s*)*):\s*\n(.*?)(?=^\s*\|\s*\w+|\Z)", body, flags=re.S | re.M):
                cname, binders, rest = cm.group(1), cm.group(2).strip(), cm.group(3)
                lines = [l.strip() for l in rest.strip().split("→\n")]
                lines = [l.strip().rstrip("→").strip() for l in lines if l.strip()]
                premises, concl = lines[:-1], lines[-1]
                ctors.append((cname, binders, premises, concl))
            inds.append((name, sig, ctors))
        return inds

    def rel_names(self, e, acc):
        if isinstance(e, list):
            for x in e: self.rel_names(x, acc)
        elif isinstance(e, str) and re.match(r"^[SG]\w+$", e): acc.add(e)
        return acc

    def closure(self):
        B = set(LEAVES)
        changed = True
        while changed:
            changed = False
            for name, _, ctors in self.inds:
                if name in B: continue
                for _, _, prem, _ in ctors:
                    names = set()
                    for p in prem: self.rel_names(parse(tokenize(p)), names)
                    if names & B:
                        B.add(name); changed = True; break
        return B

    def tname(self, n): return "T" + n[1:]

    def rel_bearing(self, e):
        h = head(e)
        if h in self.bearing: return True
        if h in COMB:
            args = e[1:] if isinstance(e, list) else []
            return any(self.rel_bearing(a) for a in args[:COMB[h]])
        return False

    def trel(self, e):
        """annotated partial relation (without the two positions / ev)"""
        h = head(e)
        args = e[1:] if isinstance(e, list) else []
        if h in self.bearing:
            return "(" + " ".join([self.tname(h)] + [show(a) for a in args]) + ")" if args else self.tname(h)
        if h in COMB:
            n = COMB[h]
            subs = [self.trel(a) if self.rel_bearing(a) else "(Lift " + show(a) + ")" for a in args[:n]]
            return "(T" + h[1:] + " " + " ".join(subs) + ")"
        return "(Lift " + show(e) + ")"

    def premise(self, p, evs):
        e = parse(tokenize(p))
        h = head(e)
        if h == "GNot" or not isinstance(e, list): return p
        if h in COMB:
            n = COMB[h]
            if not any(self.rel_bearing(a) for a in e[1:1+n]): return p
            rel = self.trel(e[:1+n] if False else [h] + e[1:1+n])
            pos = e[1+n:]
            ev = f"ev{len(evs)+1}"; evs.append(ev)
            return f"{rel} {' '.join(show(x) for x in pos)} {ev}"
        if h in self.bearing:
            ev = f"ev{len(evs)+1}"; evs.append(ev)
            return f"{self.tname(h)} {' '.join(show(x) for x in e[1:])} {ev}"
        return p

    def emit(self):
        out = []
        for name, sig, ctors in self.inds:
            if name not in self.bearing: continue
            tsig = sig.replace("SurfPos → SurfPos → Prop", "SurfPos → SurfPos → List Event → Prop")
            out.append(f"  /-- Event-annotated `{name}`. -/")
            out.append(f"  inductive {self.tname(name)} : {tsig} where")
            for cname, binders, prem, concl in ctors:
                evs = []
                tprem = [self.premise(p, evs) for p in prem]
                ce = parse(tokenize(concl))
                tconcl = " ".join([self.tname(head(ce))] + [show(x) for x in ce[1:]])
                evexpr = " ++ ".join(evs) if evs else "[]"
                b = binders + (f" ({' '.join(evs)} : List Event)" if evs else "")
                out.append(f"    | {cname} {b} :")
                for tp in tprem: out.append(f"        {tp} →")
                out.append(f"        {tconcl} ({evexpr})")
            out.append("")
        return "\n".join(out)

if __name__ == "__main__":
    g = Gen(SRC.read_text())
    if "--report" in sys.argv:
        print("mutual inductives:", g.names)
        print("bearing:", sorted(g.bearing))
        print("non-bearing:", sorted(set(g.names) - g.bearing))
        for name, _, ctors in g.inds:
            print(f"  {name}: {len(ctors)} ctors")
        sys.exit(0)
    print("""/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- GENERATED by scripts/gen_traceof.py from L4YAML/Surface/Node.lean — do not edit.
module

public import L4YAML.Proofs.Serialization.TraceOf.Leaves

namespace L4YAML.Proofs.Serialization.TraceOf

@[expose] public section

open L4YAML L4YAML.Surface
open L4YAML.Proofs.Serialization.SerializationWellFormed

mutual
""")
    print(g.emit())
    print("end\n\nend\n\nend L4YAML.Proofs.Serialization.TraceOf")
