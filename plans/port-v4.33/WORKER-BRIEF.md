# Porting a submission from v4.30.0 to v4.33.0 — worker brief

You are porting one Lax submission folder of this repository from the closed
archive environment v4.30.0 (mathlib `c5ea0035`) to the epoch v4.33.0
(Lean `leanprover/lean4:v4.33.0`, mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`). The pins are already moved
(`manifest.yaml`, both `lean-toolchain` files, both lakefiles' mathlib
`rev`); every package is already seeded for a direct `lake build` against
the warm mathlib store and the sibling folders. Your job is the Lean: the
smallest change that makes both packages build, in the order concepts
then proofs.

## Rules

1. **Concepts are the endorsement surface.** Do not change any statement
   in `concepts/` (an `axiom`, a `def`, a `structure`, a `theorem`
   statement, a docstring). If a concept file fails to compile, first try
   a fix that leaves every declared statement byte-identical (e.g. a
   `Std.Symm` bundling in an instance, an added `import`). If the only fix
   changes what is declared, STOP on that file, leave it failing, and
   report it as a "concept change needed" with the exact error and the
   proposed diff. Do not touch the proof package's use of it in that case
   either; report.
2. **Proofs: the smallest change that compiles.** No rewrites, no
   restructuring, no new lemmas beyond what a single failing site needs,
   no `sorry`, no deleted theorems, no weakened statements in
   `proofs/` either (a theorem statement in the proof package is consumed
   by dependents). Keep every existing v4.30 workaround unless it is now
   the thing that fails.
3. **Own only your folder.** Never edit another submission folder, never
   edit `.claude/`, never run `lake update`, never touch `lakefile.toml`,
   `lean-toolchain`, `manifest.yaml`, `lake-manifest.json` or
   `.lake/package-overrides.json`.
4. **Build only your packages.** Everything you depend on is already built.
   Run `lake build` inside `concepts/` first, then inside `proofs/`.
   `lake build` prints per-module errors; fix them file by file, rebuilding
   the one module (`lake build <Module.Name>`) as you go, then a full
   `lake build` of the package at the end. Never run a bare `lake build`
   anywhere else.
5. **Commit checkpoints** on the current branch, staging only files in
   your folder: `git add <folder> && git commit -m "<folder>: <what>"`.
   Never `git push`, never switch branches, never rebase.
6. Do not stop to ask; the person is not watching. Work until both
   packages build or you hit a genuine concept-change question, then
   write the report.

## Environment

```sh
export PATH=$HOME/.elan/bin:$PATH LAKE_ARTIFACT_CACHE=false
cd /home/user/lax-submissions/<folder>/concepts && lake build
cd /home/user/lax-submissions/<folder>/proofs   && lake build
```

The machine has 4 cores and 15 GB; other workers may be building at the
same time. Do not raise thread counts. A full-mathlib import takes a few
GB; if `lake build` dies with a signal/OOM, retry the single module.

If the seeded manifest/overrides go missing (they are gitignored and
regenerated), run `python3 /home/user/lax-submissions/.claude/local-overrides.py /home/user/lax-submissions`
— it rewrites every package's `lake-manifest.json` and
`.lake/package-overrides.json` and changes nothing else.

## Drift classes met so far on this mathlib pin (from the transducers port, 2026-09-14, and the sparsity/word-ram ports)

- (i) tactic targets are checked at `implicit` transparency: `simp`/`rw`
  refuse a term that applies a `→.`, passes an anonymous constructor at a
  `def`-wrapped type, or has a pattern variable at `List X.Elt` against a
  local at `(Ty.list X).Elt`. Fix: term-level `.mp`/`.mpr`, give the lemma
  its explicit arguments, a `show`/`change` exposing the definition, or an
  ascription. `Sum.elim` at a `def`-wrapped scrutinee no longer
  iota-reduces under `simp` — append `rfl` or a `show`. Constructor
  injectivity (`Prod.mk.injEq`, `Sum.inl.injEq`) does not fire when a
  component sits at a `def` — use `congrArg Prod.snd (Sum.inl.inj h)`.
- (ii) a module-name component in Windows' reserved set (`Aux`, `Con`,
  `Nul`, `Prn`, `Com1`…) is a hard error. Rename the module and its
  importers (tell the report).
- (iii) `simp` no longer bridges `id` and `fun x => x` without
  `Function.id_def`.
- (iv) `simpa … using h` is stricter than `exact`: a bridge term that is
  defeq but not syntactically equal fails "after simplification". Split
  into `simp only […]` + `exact h`, or give `simpa` the `def`s it used to
  unfold silently.
- (v) `convert h using 1` on `IsRegular`-like goals leaves an unsolved
  `Iff`; `exact h` or an `_of_eq` lemma works.
- (vi) an `instance` with an explicit argument instance synthesis can never
  supply is a hard error → `lemma`/`def`.
- (vii) `simp only []` no longer makes progress (error). Delete it or name
  the lemmas.
- (viii) `Set` is `Set.ofPred`-based and `Language`-like defs over it are
  type-incorrect at `implicit` transparency for `rw`/`kabstract`; use
  `set L : … := …` before the `rw`, `rw [show <def application> = _ from
  if_pos h]` for an `ite` body, or the term itself.
- (ix) `deriving Fintype` on an enum (all constructors nullary) is a hard
  error at this pin: keep `deriving DecidableEq`, add `instance : Fintype T
  := derive_fintype% _` (may need `import Mathlib.Data.Fintype.Sum`). In a
  concept file this is a concept change — report it (it was accepted once,
  for `Sym8`, as declared content is unchanged).
- (x) `Relation.TransGen.mono` is relation-valued (`TransGen.mono h _ _ hR`).
- (xi) `List.Pairwise.forall` takes `[Std.Symm R]`, not `Symmetric R`.
  Likewise `SimpleGraph.symm` is now a bundled `Std.Symm`: `G.symm h` →
  `G.symm.symm _ _ h`, and a structure field `symm := fun _ _ h => …`
  becomes `symm := ⟨fun _ _ h => …⟩`.
- (xii) an `X = X` that `simp` leaves is two `Classical.propDecidable`
  arguments inside `decide` (`<;> rfl`); "has type X but is expected X"
  with identical printing is two matcher auxiliaries (restate the local
  `have` through the named `def`).
- (xiii) `simp only [Foo.Holds]` unfolds an `ite` condition but leaves its
  `Decidable` instance keyed to the folded name, so a later
  `if_pos`/`if_neg` fails — keep the name folded in the `simp only` and give
  the condition proof its folded type in a `have`.
- (xiv) `decide_eq_decide` no longer fires as a `simp only` rewrite at some
  sites → `refine decide_eq_decide.mpr ?_`.
- word-ram: `simp only [arrOf, List.length_map, List.length_range] at h`
  no longer makes progress (drop it); a `simpa using hfits` over a
  `compile` definition needs `simpa [compile] using hfits`.
- sparsity: `convert (hasDerivAt_pow 2 x).div_const 3 using 1; push_cast;
  ring` → `exact (… ).congr_deriv (by norm_num)`; `simp [E, i]` on a
  `Subtype.val`/`Equiv.apply_symm_apply` goal → `change …; exact congrArg
  Subtype.val (e.apply_symm_apply _)`; `simpa [hs0] using (show … by rw …)`
  → `change …; rw […]`; `simp [SimpleGraph.Walk.length_cons]` → `norm_num
  [SimpleGraph.Walk.length]`.
- `unusedSimpArgs`/`unused variable` linter warnings are not errors; leave
  pre-existing ones alone.

## Report (your final message)

- Both packages green? (`lake build` exit 0 in `concepts/` and in
  `proofs/`, quote the last line.)
- Every file you changed, with line numbers and the drift class per site
  (new classes get a new number and a one-line description).
- Any concept-change question, with the exact error and proposed diff.
- Anything you could not fix, with the error verbatim.
