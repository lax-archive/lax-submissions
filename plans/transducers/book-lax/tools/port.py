#!/usr/bin/env python3
"""Port source modules of transducer-lean into a Lax proof package, verbatim.

    port.py --pkg Lax765601Proofs --dest lax/mealy-machines/proofs \
            [--dep Lax251941Proofs ...] Common/Basic PartA/MealyBasic ...

For each listed module `X/Y` (relative to RequestProject/, no extension) the
file is copied to `<dest>/<pkg>/Source/X/Y.lean` with these rewrites:

  import RequestProject.X.Y     -> import <pkg>.Source.X.Y   if X/Y is ported here
                                -> import <dep>.Source.X.Y   if some --dep package
                                   ports it (recorded in <dep-dest>/../ported.txt)
  import RequestProject.PartC   -> import <IMP1> ... (--replace-import PartC=IMP1,IMP2: a
                                   roll-up import becomes the root modules of the
                                   packages carrying that part; every --dep is then opened)
  namespace Transducers          -> namespace <pkg>.Transducers   (root namespaces only)
  end Transducers                -> end <pkg>.Transducers
  open Transducers               -> open <pkg>.Transducers
  (likewise for the other root namespaces PCP, PCPIndex, Acceptance)

Inside `namespace <pkg>.Transducers`, a fully qualified `Transducers.foo` still
resolves (Lean tries every prefix of the current namespace), and so does a
reference to a dependency's `Transducers.foo` once `open <dep>` is in force;
the script inserts `open <dep> <dep>.Transducers` after the imports of every
ported file, for each --dep package its import closure reaches, following the
dependencies' own imports (a bare `foo` of the dependency needs the second
`open`; opening a namespace that no import declares is an error, hence per
file and exact).

A dependency's ported.txt lists its own modules *and* those of its own
dependencies, so give the --dep packages in chain order (earliest part first):
a module belongs to the first --dep whose ported.txt lists it.

The list of ported modules is written to <dest>/../ported.txt (the submission root;
extra files inside a package are rejected by the archive) so that later
packages can resolve their imports against it.
"""
import argparse, os, re, sys

SRC = os.path.expanduser("~/git/transducer-book/transducer-lean/RequestProject")
ROOT_NS = ["Transducers", "PCP", "PCPIndex", "Acceptance"]

ap = argparse.ArgumentParser()
ap.add_argument("--pkg", required=True)
ap.add_argument("--dest", required=True)
ap.add_argument("--dep", action="append", default=[], help="PKG=DEST of a dependency proof package")
ap.add_argument("--provided", action="append", default=[], help="module X/Y written by hand at <dest>/<pkg>/Source/X/Y.lean")
ap.add_argument("--replace-import", action="append", default=[],
                help="MOD=IMP1,IMP2: rewrite `import RequestProject.MOD` (a roll-up such as PartC) into `import IMP1` … (root modules of the packages carrying it)")
ap.add_argument("modules", nargs="+")
a = ap.parse_args()

deps = {}  # module -> package
for d in a.dep:
    pkg, dest = d.split("=")
    for line in open(os.path.join(dest, "..", "ported.txt")):
        deps.setdefault(line.strip(), pkg)  # first --dep wins (chain order)

mine = set(a.modules) | set(a.provided)
replace = {k: v.split(",") for k, v in (r.split("=") for r in a.replace_import)}

def imports_of(mod):
    """The RequestProject modules imported by `mod` (a hand-written --provided
    module is read at its destination, its imports of ported modules count)."""
    if mod in a.provided:
        out = os.path.join(a.dest, a.pkg, "Source", mod + ".lean")
        if not os.path.exists(out):
            return list(deps)  # unknown: assume it reaches the dependencies
        pat = r"^import (?:%s)\.Source\.([\w.]+)$" % "|".join([a.pkg] + sorted(set(deps.values())))
        return [m.replace(".", "/") for m in re.findall(pat, open(out).read(), flags=re.M)]
    return [m.replace(".", "/") for m in
            re.findall(r"^import RequestProject\.([\w.]+)$", open(os.path.join(SRC, mod + ".lean")).read(), flags=re.M)
            if m not in replace]

depdest = {d.split("=")[0]: d.split("=")[1] for d in a.dep}
_reach = {}
def deps_reached(mod):
    """The --dep packages whose modules the import closure of `mod` reaches,
    following the dependency's own (already rewritten) imports."""
    if mod in deps:
        if mod in _reach:
            return _reach[mod]
        _reach[mod] = {deps[mod]}
        f = os.path.join(depdest[deps[mod]], deps[mod], "Source", mod + ".lean")
        if os.path.exists(f):
            for pkg, m in re.findall(r"^import (Lax\w+Proofs)\.Source\.([\w.]+)$", open(f).read(), flags=re.M):
                _reach[mod] |= deps_reached(m.replace(".", "/"))
        return _reach[mod]
    if mod in a.modules and any(m in replace for m in re.findall(r"^import RequestProject\.([\w.]+)$", open(os.path.join(SRC, mod + ".lean")).read(), flags=re.M)):
        return set(deps.values())
    if mod in _reach:
        return _reach[mod]
    _reach[mod] = set()  # cycles cannot occur, but be safe
    _reach[mod] = set().union(*(deps_reached(m) for m in imports_of(mod)))
    return _reach[mod]

def rewrite_import(m):
    mod = m.group(1)
    if mod.replace("/", ".") in replace:
        return "\n".join(f"import {i}" for i in replace[mod.replace("/", ".")])
    if mod in mine:
        return f"import {a.pkg}.Source.{mod.replace('/', '.')}"
    if mod in deps:
        return f"import {deps[mod]}.Source.{mod.replace('/', '.')}"
    sys.exit(f"unported import RequestProject.{mod.replace('/', '.')}")

for mod in a.modules:
    if mod in a.provided:
        continue
    src = os.path.join(SRC, mod + ".lean")
    s = open(src).read()
    s = re.sub(r"^import RequestProject\.([\w.]+)$",
               lambda m: rewrite_import(type("M", (), {"group": lambda self, i: m.group(1).replace('.', '/')})()),
               s, flags=re.M)
    # rewrite only root-level namespaces (a nested `namespace PCP` inside
    # `namespace Transducers` must stay as it is)
    out_lines, stack = [], []
    for line in s.split("\n"):
        m = re.match(r"^namespace (\S+)\s*$", line)
        if m:
            ns = m.group(1)
            if not stack and not ns.startswith(a.pkg):
                # every root-level namespace must carry the package prefix
                stack.append((ns, True)); out_lines.append(f"namespace {a.pkg}.{ns}"); continue
            stack.append((ns, False)); out_lines.append(line); continue
        m = re.match(r"^end (\S+)\s*$", line)
        if m and stack and stack[-1][0] == m.group(1):
            ns, rewritten = stack.pop()
            out_lines.append(f"end {a.pkg}.{ns}" if rewritten else line); continue
        m = re.match(r"^open (scoped )?(\S+)(.*)$", line)
        if m and m.group(2) in ROOT_NS and not any(n == m.group(2) for n, _ in stack):
            out_lines.append(f"open {m.group(1) or ''}{a.pkg}.{m.group(2)}{m.group(3)}"); continue
        out_lines.append(line)
    s = "\n".join(out_lines)
    deporder = [d.split("=")[0] for d in a.dep]
    depnames = [p for p in deporder if p in deps_reached(mod)]
    if depnames:
        # insert `open <dep> <dep>.Transducers` after the last import line: the
        # first makes a qualified `Transducers.foo` of the dependency resolve,
        # the second a bare `foo` (the dependency's root namespace is
        # `<dep>.Transducers`, and a bare name is not looked up through the
        # prefixes of an opened namespace).  Only in files whose imports reach
        # the dependency: `open` of an unknown namespace is an error.
        lines = s.split("\n")
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines[last + 1:last + 1] = [f"open {p} {p}.Transducers" for p in depnames]
        s = "\n".join(lines)
    out = os.path.join(a.dest, a.pkg, "Source", mod + ".lean")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write(s)
    print("ported", mod, "->", out)

with open(os.path.join(a.dest, "..", "ported.txt"), "w") as f:
    for mod in sorted(mine | set(deps)):
        f.write(mod + "\n")
