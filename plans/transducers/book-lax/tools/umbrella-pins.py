#!/usr/bin/env python3
"""Regenerate the umbrella's lakefiles (lax/transducers-book/{concepts,proofs}/lakefile.toml)
so that they require every part submission's concept package (concepts) and
concept + proof packages (proofs), pinned to each part's current archive record
(`lax sync` first). Rerun after any part is resubmitted."""
import json, os
DB = os.path.expanduser("~/.lax/lax-database")
PARTS = [  # (id, folder, comment)
    ("251941", "pcp-undecidability", "Undecidability of the Post correspondence problem"),
    ("765601", "mealy-machines", "Part A: Mealy machines"),
    ("132576", "rational-functions", "Part B: rational functions"),
    ("916827", "regular-functions", "Part C §1–3: regular functions"),
    ("314295", "mso-transductions", "Part C §4: MSO transductions"),
    ("709149", "regular-combinators", "Part C §5: regular combinators"),
    ("194892", "polyregular-functions", "Part D: polyregular functions"),
]
HEAD = """name = "{pkg}"
defaultTargets = ["{pkg}"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "db584cd6d46c92f209a44c0f1c829460d327499d"
"""
def req(name, rev, sub):
    return f'\n[[require]]\nname = "{name}"\ngit = "https://github.com/bojanczyk/transducer-book"\nrev = "{rev}"\nsubDir = "lax/{sub}"\n'
for kind, pkg in [("concepts", "Lax157538"), ("proofs", "Lax157538Proofs")]:
    out = HEAD.format(pkg=pkg)
    if kind == "proofs":
        out += '\n[[require]]\nname = "Lax157538"\npath = "../concepts"\n'
    for n, folder, comment in PARTS:
        rec = json.load(open(f"{DB}/lax-{n}/record.json"))
        rev = rec["source"]["commit"]
        out += f"\n# {comment} (lax-{n})" + req(f"Lax{n}", rev, f"{folder}/concepts")
        if kind == "proofs":
            out += req(f"Lax{n}Proofs", rev, f"{folder}/proofs")
    out += f'\n[[lean_lib]]\nname = "{pkg}"\n'
    p = f"transducers-book/{kind}/lakefile.toml"
    open(p, "w").write(out)
    print(p, out.count("[[require]]"), "requires")
