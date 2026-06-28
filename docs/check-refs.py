#!/usr/bin/env python3
r"""Drift guard: every \lean{...} reference in docs/formalization.tex must resolve to either a
declaration occurring in the Lean sources or a module file. Run from anywhere; exits non-zero
on a dangling reference."""
import re, sys, glob, os
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
srcdir = os.path.join(root, "MultiViewIdentifiability")
src = "\n".join(open(f, encoding="utf-8").read() for f in glob.glob(os.path.join(srcdir, "*.lean")))
modules = {os.path.splitext(os.path.basename(f))[0] for f in glob.glob(os.path.join(srcdir, "*.lean"))}
tex = open(os.path.join(root, "docs", "formalization.tex"), encoding="utf-8").read()
unesc = lambda s: s.replace(r"\_", "_").replace(r"\&", "&")
from collections import defaultdict
byp = defaultdict(set)
for m in re.findall(r"\\lean\{([^}]*)\}", tex):
    for piece in unesc(m).split("/"):
        piece = piece.strip().rstrip(".,;:()")
        if not piece or piece.endswith(".lean"):
            continue
        if piece in modules:                      # module-name reference (e.g. AtomCertificate)
            continue
        for cand in [piece] + piece.split("."):
            cand = cand.strip("*+ ")
            if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", cand or ""):
                byp[piece].add(cand)
missing = [p for p, cands in byp.items() if not any(c in src or c in modules for c in cands)]
if missing:
    print("DANGLING Lean references in formalization.tex:")
    for p in sorted(missing): print("  -", p)
    sys.exit(1)
print(f"OK: all {len(byp)} cited Lean references resolve to the sources.")
