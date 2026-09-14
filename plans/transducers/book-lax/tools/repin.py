#!/usr/bin/env python3
"""Repin one or more submissions' cross-submission requires to the archive's
current records — the step the chain workflow needs after a dependency is
resubmitted (its record moves, every dependent's `rev` goes stale).

    lax sync
    python3 tools/repin.py <submission-folder>...     # from lax/

For every `[[require]]` with a `git` url in the folder's concepts/ and
proofs/ lakefiles whose name is LaxN / LaxNProofs, `git`, `rev` and `subDir`
are set from ~/.lax/lax-database/lax-N/record.json. A dependency without a
source record (never submitted) is an error: submit it first. Prints one line
per changed pin. The umbrella has its own generator, tools/umbrella-pins.py.
Adapted from ~/git/lax-submissions/.claude/repin.sh.
"""
import json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # lax/
DB = os.path.expanduser("~/.lax/lax-database")
changed, failed = 0, 0
for folder in sys.argv[1:]:
    for kind in ("concepts", "proofs"):
        path = os.path.join(ROOT, folder, kind, "lakefile.toml")
        if not os.path.isfile(path):
            continue
        lines = open(path).read().split("\n")
        out, i = [], 0
        while i < len(lines):
            line = lines[i]
            out.append(line)
            i += 1
            if line.strip() != "[[require]]":
                continue
            # collect the block
            block = []
            while i < len(lines) and not lines[i].startswith("["):
                block.append(lines[i])
                i += 1
            text = "\n".join(block)
            m_name = re.search(r'^name\s*=\s*"(Lax(\d+)(Proofs)?)"$', text, re.M)
            if m_name and re.search(r"^git\s*=", text, re.M):
                name, number = m_name.group(1), m_name.group(2)
                record = os.path.join(DB, f"lax-{number}", "record.json")
                source = json.load(open(record)).get("source") if os.path.isfile(record) else None
                if source is None:
                    print(f"error: {folder}/{kind}: {name} (lax-{number}) has no archive source — submit it first")
                    failed += 1
                else:
                    want = {"git": source["repository"], "rev": source["commit"],
                            "subDir": f"{source['folder']}/{'proofs' if name.endswith('Proofs') else 'concepts'}"}
                    for key, value in want.items():
                        pattern = re.compile(rf'^({key}\s*=\s*)"([^"]*)"$', re.M)
                        m = pattern.search(text)
                        if m and m.group(2) != value:
                            shown = value[:12] if key == "rev" else value
                            print(f"{folder}/{kind}: {name}.{key} {m.group(2)[:12]} -> {shown}")
                            text = pattern.sub(lambda mm: f'{mm.group(1)}"{value}"', text)
                            changed += 1
            out.extend(text.split("\n"))
        open(path, "w").write("\n".join(out))
print(f"repin: {changed} pin(s) changed")
sys.exit(1 if failed else 0)
