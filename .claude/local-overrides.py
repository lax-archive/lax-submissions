#!/usr/bin/env python3
"""Seed every submission package for a direct `lake build` against the sibling
folders and the machine-wide warm mathlib store — the fast local loop while
the cross-submission pins are not yet on the archive.

    python3 .claude/local-overrides.py [root]   # root defaults to the repository

For each `<submission>/{concepts,proofs}` it writes the two gitignored
files `lax build` would write, adapted to the working tree:

  - lake-manifest.json            the locked entries lake expects: the proof
    package's own concept package (path), every cross-submission require of
    the closure as the *git* entry the lakefile declares (so lake never
    reports the manifest out of date), then the warm store's own locked
    mathlib closure verbatim;
  - .lake/package-overrides.json  path entries redirecting each of those
    names: mathlib and friends to `~/.lax/warm/<env>/.lake/packages/<name>`
    (in place, read-only), each `LaxN`/`LaxNProofs` to the sibling folder.

Lake reads the overrides on every `lake build` and substitutes them after
manifest validation, so the pins stay honest in git while the build reads the
folder next door. Rerun after `lax build`, which rewrites both files from the
pins alone. The port-time sibling of `.claude/sibling-overrides.sh` (which reads the warm-store redirects `lax build` wrote)
and lax's `host/warmstore.ts` (seedManifest/seedOverrides).

Requires the environment's warm store, provisioned once by
`lax doctor --env <leanVersion>`; the store is looked up from each
submission's manifest.yaml (leanVersion, mathlibVersion).
"""
import json, os, re, sys

ROOT = (os.path.abspath(sys.argv[1]) if len(sys.argv) > 1
        else os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # the repo root
WARM_BASE = os.path.expanduser("~/.lax/warm")
MANIFEST_VERSION = "1.2.0"
PACKAGES_DIR = ".lake/packages"


def parse_lakefile(path):
    """Package name plus one dict per [[require]] block (whitelisted TOML: a
    line scanner is enough)."""
    name, requires, cur = None, [], None
    for line in open(path):
        line = line.strip()
        if line == "[[require]]":
            cur = {}
            requires.append(cur)
            continue
        if line.startswith("["):
            cur = None
            continue
        m = re.match(r'^(\w+)\s*=\s*"([^"]*)"$', line)
        if not m:
            continue
        key, value = m.group(1), m.group(2)
        if cur is not None:
            cur[key] = value
        elif key == "name" and name is None:
            name = value
    return name, requires


def manifest_env(submission):
    env = {}
    for line in open(os.path.join(ROOT, submission, "manifest.yaml")):
        m = re.match(r'^(leanVersion|mathlibVersion):\s*"([^"]*)"', line)
        if m:
            env[m.group(1)] = m.group(2)
    return env


packages = {}  # name -> {dir, kind, submission, requires}
for submission in sorted(os.listdir(ROOT)):
    for kind in ("concepts", "proofs"):
        lakefile = os.path.join(ROOT, submission, kind, "lakefile.toml")
        if not os.path.isfile(lakefile):
            continue
        name, requires = parse_lakefile(lakefile)
        packages[name] = {"dir": os.path.join(ROOT, submission, kind), "kind": kind,
                          "submission": submission, "requires": requires}


def closure(name):
    seen, stack = [], [name]
    while stack:
        for require in packages[stack.pop()]["requires"]:
            dep = require["name"]
            if dep in packages and dep not in seen and dep != name:
                seen.append(dep)
                stack.append(dep)
    return seen


def declared_git(dep):
    """The (git, rev, subDir) some lakefile of the tree declares for `dep`,
    borrowing the sibling package's pin when only that one is declared."""
    sibling = dep[:-len("Proofs")] if dep.endswith("Proofs") else dep + "Proofs"
    for candidate in (dep, sibling):
        for package in packages.values():
            for require in package["requires"]:
                if require["name"] == candidate and "git" in require:
                    sub = f"{packages[dep]['submission']}/{packages[dep]['kind']}"
                    return require["git"], require["rev"], sub
    return None


problems, touched = [], 0
for name in sorted(packages):
    package = packages[name]
    env = manifest_env(package["submission"])
    warm = os.path.join(WARM_BASE, f"{env['leanVersion']}-{env['mathlibVersion'][:12]}")
    if not os.path.isfile(os.path.join(warm, ".lax-warm-ok")):
        problems.append(f"{name}: no warm store at {warm} — run `lax doctor --env {env['leanVersion']}`")
        continue
    warm_manifest = json.load(open(os.path.join(warm, "lake-manifest.json")))

    own_concepts = name[:-len("Proofs")] if package["kind"] == "proofs" else None
    declared = {r["name"]: r for r in package["requires"]}
    manifest_entries, override_entries = [], []
    for dep in closure(name):
        if dep == own_concepts:
            manifest_entries.append({
                "type": "path", "scope": "", "name": dep,
                "manifestFile": "lake-manifest.json", "inherited": False,
                "dir": "../concepts", "configFile": "lakefile.toml"})
            continue
        pinned = declared.get(dep)
        if pinned and "git" in pinned:
            git, rev, sub = pinned["git"], pinned["rev"], pinned["subDir"]
        else:
            found = declared_git(dep)
            if found is None:
                problems.append(f"{name}: no git pin found anywhere for {dep} — left out")
                continue
            git, rev, sub = found
        manifest_entries.append({
            "url": git, "type": "git", "subDir": sub, "scope": "", "rev": rev,
            "name": dep, "manifestFile": "lake-manifest.json", "inputRev": rev,
            "inherited": dep not in declared, "configFile": "lakefile.toml"})
        override_entries.append({
            "type": "path", "name": dep, "inherited": False, "scope": "",
            "dir": os.path.relpath(packages[dep]["dir"], package["dir"])})

    manifest_entries.extend(warm_manifest["packages"])
    for pkg in warm_manifest["packages"]:
        entry = {"type": "path", "name": pkg["name"],
                 "dir": os.path.join(warm, PACKAGES_DIR, pkg["name"]),
                 "inherited": pkg["inherited"]}
        if "scope" in pkg:
            entry["scope"] = pkg["scope"]
        override_entries.append(entry)

    os.makedirs(os.path.join(package["dir"], ".lake"), exist_ok=True)
    with open(os.path.join(package["dir"], "lake-manifest.json"), "w") as f:
        f.write(json.dumps({"version": MANIFEST_VERSION, "packagesDir": PACKAGES_DIR,
                            "packages": manifest_entries}, indent=1) + "\n")
    with open(os.path.join(package["dir"], ".lake", "package-overrides.json"), "w") as f:
        f.write(json.dumps({"version": MANIFEST_VERSION, "packages": override_entries},
                           indent=1) + "\n")
    touched += 1
    siblings = [e["name"] for e in override_entries if e["name"].startswith("Lax")]
    print(f"{name}: {', '.join(siblings) or 'mathlib only'}")

print(f"local-overrides: seeded {touched} package(s)")
for problem in problems:
    print(f"warning: {problem}")
sys.exit(1 if problems else 0)
