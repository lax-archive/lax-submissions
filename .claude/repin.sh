#!/usr/bin/env bash
# Repin one submission's cross-submission requires to the archive's current
# records — the step the cascade needs after a dependency is resubmitted.
#
#   .claude/repin.sh <submission-folder>...
#
# For every `[[require]]` with a `git` url in the folder's concepts/ and
# proofs/ lakefiles whose name is LaxN / LaxNProofs, the `rev` (and `git`,
# `subDir`) are set from ~/.lax/lax-database/lax-N/record.json, refreshed by
# `lax sync`. A dependency without a source record (never submitted) is an
# error: it has to be submitted first. Prints one line per changed pin.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
python3 - "$root" "$@" <<'PY'
import json, os, re, sys
root, folders = sys.argv[1], sys.argv[2:]
db = os.path.expanduser("~/.lax/lax-database")
changed, failed = 0, 0
for folder in folders:
    for kind in ("concepts", "proofs"):
        path = os.path.join(root, folder, kind, "lakefile.toml")
        if not os.path.isfile(path):
            continue
        lines = open(path).read().split("\n")
        out, block, i = [], None, 0
        # split into [[require]] blocks and rewrite each git-pinned Lax one
        blocks = []
        for line in lines:
            if line.strip() == "[[require]]":
                block = []
                blocks.append(block)
            elif line.startswith("[") and line.strip() != "[[require]]":
                block = None
            if block is not None:
                block.append(line)
        for block in blocks:
            text = "\n".join(block)
            m_name = re.search(r'^name\s*=\s*"(Lax(\d+)(Proofs)?)"$', text, re.M)
            if not m_name or not re.search(r'^git\s*=', text, re.M):
                continue
            name, number = m_name.group(1), m_name.group(2)
            record = os.path.join(db, f"lax-{number}", "record.json")
            source = json.load(open(record)).get("source") if os.path.isfile(record) else None
            if source is None:
                print(f"error: {folder}/{kind}: {name} (lax-{number}) has no archive source — submit it first")
                failed += 1
                continue
            want = {"git": source["repository"], "rev": source["commit"],
                    "subDir": f"{source['folder']}/{'proofs' if name.endswith('Proofs') else 'concepts'}"}
            for key, value in want.items():
                pattern = re.compile(rf'^({key}\s*=\s*)"([^"]*)"$', re.M)
                m = pattern.search(text)
                if m and m.group(2) != value:
                    print(f"{folder}/{kind}: {name}.{key} {m.group(2)[:12]} -> {value[:12] if key == 'rev' else value}")
                    text = pattern.sub(lambda mm: f'{mm.group(1)}"{value}"', text)
                    changed += 1
            new = text.split("\n")
            block[:] = new
        # write back: blocks were rewritten in place (they alias `lines` slices only
        # by content, so rebuild the file from the original lines + rewritten blocks)
        result, bi, inblock = [], 0, None
        for line in lines:
            if line.strip() == "[[require]]":
                result.extend(blocks[bi]); bi += 1; inblock = True
                continue
            if inblock and not (line.startswith("[") and line.strip() != "[[require]]"):
                continue  # consumed by the block
            inblock = False
            result.append(line)
        open(path, "w").write("\n".join(result))
print(f"repin: {changed} pin(s) changed")
sys.exit(1 if failed else 0)
PY
