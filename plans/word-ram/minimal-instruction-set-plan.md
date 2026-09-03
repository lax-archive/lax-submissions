# Word RAM: the canonical instruction set

Rev 2 ACTIVE, 2026-09-02. Jan's decisions of the same day: accumulator out,
Cook–Reckhow register-transfer form in, `halt` kept, bitwise operations
reduced to a generating set plus `not`. Rev 1's audit of the accumulator
machine (which instructions it could lose) is superseded by this file; the
knock-on inventory and the resubmission cascade carry over unchanged.

## 1. Design principle

The instruction set is a **generating set for the standard word-RAM
operations under constant-cost simulation**: every operation the
algorithms literature charges one time unit for (Fredman–Willard 1993,
Hagerup 1998) is either an instruction or derived from instructions in a
fixed number of steps that does not depend on `w`. Two conveniences are kept
knowingly although derivable: `halt` (running past the program halts too, but
that is the totality mechanism) and `jump` (derivable only via a reserved
zero cell). Nothing else is derivable from the rest.

The community agrees on the model at the level of unit-cost operations, not
of an instruction format, so the format is chosen for statability and for
the compiler: memory cells are the only storage, an instruction is
`cell ← f(cells)`, literals enter through one instruction and indirection
through two. This is the RAM of Cook and Reckhow (*Time bounded random access
machines*, JCSS 7, 1973) with bounded words, rather than Aho–Hopcroft–Ullman's
accumulator machine, which mirrors 1960s hardware and is what no algorithm is
written in.

## 2. The machine (`Lax13.Ram`, concept)

Names that downstream concepts use stay byte-identical: `Program`, `State`,
`step`, `run`, `initState`, `RunsTo`, and `RamComputes.ComputesInTime`.
`State` loses `acc`; `Op` disappears.

```
structure State where
  pc  : ℕ
  mem : ℕ → ℕ
  inp : List ℕ
  out : List ℕ
```

Fifteen instructions, destination first. `m[·]` is `s.mem` with the address
reduced modulo `2^w`; every value written is reduced modulo `2^w` (the
uniform truncation rule of the current notes, unchanged).

| instruction | effect | remark |
|---|---|---|
| `set a n` | `m[a] ← n` | the only place a literal appears |
| `load a b` | `m[a] ← m[m[b]]` | indirect read |
| `store a b` | `m[m[a]] ← m[b]` | indirect write |
| `add a b c` | `m[a] ← m[b] + m[c]` | wraps |
| `sub a b c` | `m[a] ← m[b] − m[c]` | monus (truncated at zero), as now |
| `mul a b c` | `m[a] ← m[b] · m[c]` | wraps |
| `div a b c` | `m[a] ← m[b] / m[c]` | `x / 0 = 0`, as now |
| `and a b c` | `m[a] ← m[b] &&& m[c]` | |
| `shiftl a b c` | `m[a] ← m[b] · 2^{m[c]}` | wraps; a shift by `≥ w` gives `0` |
| `not a b` | `m[a] ← 2^w − 1 − m[b]` | two's-complement negation; the one value that depends on `w` other than through truncation |
| `jump l` | `pc ← l` | |
| `jzero a l` | `pc ← l` if `m[a] = 0` | |
| `halt` | halts | |
| `read a` | `m[a] ←` next input, or halt if the tape is exhausted | |
| `write a` | append `m[a]` to the output | |

Derived operations, to be listed in the concept notes with these counts
(`t`, `u` are cells the program spares; `z` a cell holding `0`):

| operation | instructions | count |
|---|---|---|
| copy `a ← b` | `set t b; load a t` | 2 |
| `a ← b ∨ c` | `and t b c; sub t c t; add a b t` | 3 |
| `a ← b ⊕ c` | `and t b c; sub u c t; add u b u; sub a u t` | 4 |
| `a ← b ≫ c` | `set t 1; shiftl t t c; div a b t` | 3 |
| `a ← b mod c` | `div t b c; mul t t c; sub a b t` | 3 |
| if `b ≤ c` goto `l` | `sub t b c; jzero t l` | 2 |
| if `b < c` goto `l` | `sub t c b; jzero t l'; jump l; l':` or via `1 − (c − b)` | 2–3 |
| if `b = c` goto `l` | `sub t b c; sub u c b; add t t u; jzero t l` | 4 |
| unconditional jump without `jump` | `jzero z l` | 1, given `z` |

Why `not` is in although "specific bit operations" are out: without it the
all-ones word costs `O(w)` once per program, and our statements quantify over
all `w` with `c·(n+1) ≤ 2^w`, so that prologue is not absorbed into `c·(n+1)`;
a model without `not` is strictly weaker than the standard word RAM for large
`w`. `and`+`not`+`shiftl` generate every bitwise operation and both shifts in
`O(1)` with no prologue. `xor` alone could not have been the survivor
(recovering `∧` from `⊕` needs `a + b`, which wraps); `and` is the one every
AC⁰-RAM paper keeps.

Why monus stays: comparison is `sub; jzero`, two instructions; with wrapping
subtraction it would need `div` and two jumps, and the IMP+ layer's natural
monus would cost four or five instructions to compile. The current notes'
argument is kept.

Notes to rewrite in `Ram.lean`'s docstring: the header sentence listing the
instructions; the skeleton citation (Cook–Reckhow for the format, Hagerup and
Fredman–Willard for the word model; van Emde Boas, *Machine models and
simulations*, Handbook of TCS A, 1990, for the equivalence of RAM variants);
the "omitted because derivable" paragraph replaced by the table above; the
truncation paragraph (`set`, `not` and the arithmetic instructions produce
values; `load`, `store`, `jzero`, `write` and every `b`/`c` operand use
addresses); the halting paragraph (`halt`, program counter past the end,
exhausted input). `abstract.md` follows.

## 3. The compiler on the new machine

Compile and Simulation are rewritten, not trimmed; Transfer, Reasoning,
Bounds, Spec, Frame, Tactic and the whole `Refine/` tower are untouched
(the IMP+ surface `Solves`/`computesInTime_of_solves`/`compileProgram`/
`Layout`/`Com.Ok` is frozen). Design fixed here so the worker does not drift:

- **Temporaries.** An expression at depth `d` evaluates *into cell `d`*, uses
  cell `d + 1` for its second operand or a literal, and the three lowered
  operators need one more cell `d + 2` (both operands stay live while the
  intermediate `b ∧ c` or `2^c` is formed). To keep every downstream layout
  literal and every `Com.Ok`/`Expr.Ok` proof verbatim, `Ok` keeps demanding
  `d < L.temps` and the layout **reserves `L.temps + 2` cells** for
  temporaries: `varAddr x = L.temps + 2 + idx`, `arrBase` and `span` shift by
  two. `Reaches.frame` becomes "writes only cells `d … L.temps + 1`".
- **Expressions.** `lit n` → `set d n`; `var x` → `set d (varAddr x); load d d`;
  `get a i` → `compileExpr i d; set (d+1) q; mul d d (d+1); set (d+1) (arrBase a);
  add d d (d+1); load d d` (the old `q − 1` repeated additions are gone, so
  `idxLen` is a numeral and `Layout.const` **no longer depends on the number
  of arrays**); `bin op e f` → `compileExpr f d; compileExpr e (d+1); op d (d+1) d`
  for the six machine operators (second operand first, into `d`, as the
  frozen `Expr.Ok` clause `Ok f d ∧ Ok e (d+1)` dictates); `or`, `xor`,
  `shiftr` end in the 3–4 instruction blocks of §2 with `t = d + 2` and, for
  `xor`, the spare `u` being cell `d` itself, dead after its last read.
- **Conditions.** `condExpr` (monus trick) is unchanged; a compiled condition
  leaves its value in cell `0`, followed by `jzero 0 l`.
- **Commands.** `assign x e` → `compileExpr e 0; set 1 (varAddr x); store 1 0`
  (cells `0` and `1` lie inside the `temps + 2` reserve at every layout, so
  `Com.Ok` is byte-identical to before — no extra conjunct was needed);
  `store a i e` → index into `0`, `e` into `1`, `store 0 1`; `write e` →
  `compileExpr e 0; write 0`; `read x` → `read (varAddr x)`; `ite`/`while`
  as now with `jzero 0`; `compileProgram L c = compile L c 0 ++ [.halt]`.
- **Constant.** `Layout.const` becomes a numeral; record the value here when
  the proof settles it. **Settled 2026-09-02: `Layout.const = 10`,**
  independent of the layout (`Layout.idxLen = 4`). Ten is what the equality
  condition forces: `condExpr (eq e f)` compiles both differences, and a
  variable read is two instructions against one unit of IMP+ cost, so
  `bsize ≤ 10 · b.size`; every other construct needs at most five.

## 4. Knock-on inventory

Unchanged from the audit; summarised.

- **word-ram/concepts** (`Ram.lean`, `abstract.md`): the new machine and
  notes. `RamComputes.lean` unchanged. Concept change ⇒ resubmission.
- **word-ram/proofs**: `Machine.lean` (equations for the new instructions;
  `Fits`, `run_*` unchanged), `Compile.lean`, `Simulation.lean` rewritten;
  `Imp.lean` docstring ("six operators are machine instructions, three are
  lowered"); `Smoke.lean`, `Lib/*`, `Refine/Codegen/Harness.lean`,
  `Refine/Codegen/Examples/EndToEnd.lean` numerals and `#guard` gates
  recompute; `Refine/Sepref/SpaceBudgetProbe.lean` and `HeapAlloc.lean` span
  arithmetic shifts. No `Ram.Instr`/`Op` site exists anywhere else (checked
  2026-09-02).
- **ram-linear-time (Lax11)**: proofs only — `const_eq` in `CCMain`, `VCMain`,
  `TreeFoldMain`, `CourcelleMain` (all `10`), headline witnesses
  (`2604 → 840`, `33300 → 9000`, …), span docstrings, step-count gates
  recomputed with identical outputs; repin `Lax13` at resubmission.
  **LANDED 2026-09-02 @ 6d973f7.** One checked claim changed: the Courcelle
  driver's "no multiplication anywhere" gate is false on the new compiler
  (`idxCode` multiplies the index by the array count) and became
  `noDataDependentWide` — no division, no shift, and every `mul` is the
  compiler's stride multiplication by the compile-time constant
  `arrays.length`. `abstract.md` and `notes.md` say the same.
- **vertex-cover-ladder (Lax15)**: proofs only — two `const_eq` (`10`),
  witnesses `90300 → 21000`, `318500 → 65000`, `33300 → 9000`, 52 step-count
  gates recomputed with identical answers, `abstract.md`/`notes.md`
  constants; repin `Lax13`, `Lax11` at resubmission. **LANDED 2026-09-02 @
  cb63a18** (replayed against the landed Lax11 before landing). All code
  leaves of the cascade are now on `main`; only §5 remains.
- **nowhere-dense-model-checking (Lax3)**: `ProgCodegenLayout.lean`
  (`mcLayout_span_le`, span constant `11 → 13`), `ProgCodegen.lean`
  (`mc_computesInTime_of_solveSpec` threads the same `hspan` sum),
  `SolveMatTop.lean` docstring; constants are symbolic. Repin all four
  requires at resubmission. **LANDED 2026-09-02 @ ca76b56.**
- **Unaffected**: Lax12, Lax14, Lax5, both twin-width submissions.
- Headline statements everywhere quantify `∃ (p : Program) (c : ℕ)`, so no
  downstream concept changes.

## 5. Resubmission cascade — DONE 2026-09-03: published as lax-67

**What happened.** Jan registered lax-13 on 2026-09-02 14:43 UTC from
`92ae2d6` (the Cook–Reckhow machine, before the text fixes below).
Registered records are immutable: `.claude/resubmit-cascade.sh` stopped at
its first step with "lax-13 is registered and cannot be changed", no repin
commit and no submission was made. Three concept-text fixes from the
2026-09-02 review are on `main` @ `7603776` (pushed) and therefore not in
the archive: the `Instr` docstring no longer claims the first cell named is
always the one written (`store`, `jzero`, `write` broke that); the
"a program measures `w` itself" sentence is replaced by the real reason no
instruction reports `w` (only the mask `2 ^ w - 1` is ever needed, and an
`O(w)` prologue is not absorbed by any bound stated over all `w`); the
Cook–Reckhow attribution now says which choices are not theirs (words,
monus, `jzero` against their signed integers, exact subtraction and
branch-on-positive). Content of the folder otherwise equals the record.

**Jan's decision (2026-09-02, verbal; reaffirmed 2026-09-03): publish as a
superseding revision, and repin the dependents onto it.** Archive mechanism
(`lax print instructions`, "Additional Info"): a new submission created by
`lax init` whose `manifest.yaml` carries `supersedes: lax-13`; the link
becomes permanent when the successor registers; the predecessor must be
registered (it is), an owner of it must own the successor (`jan3er`), and a
record can have only one successor.

Executed 2026-09-03 @ `483f38b`:

1. `lax init _successor --title "The Word RAM"` reserved **lax-67**; the
   scaffold was discarded and only the id kept.
2. The successor **took over the `word-ram/` folder** — lax-13's source
   stays retrievable at `92ae2d6`, and the tree carries one live word RAM
   rather than two near-identical copies. `manifest.yaml` now reads
   `id: lax-67` / `supersedes: lax-13`; authors, bibEntries and abstract are
   unchanged.
3. The spec makes the concept namespace the submission id, so `Lax13` →
   `Lax67` and `Lax13Proofs` → `Lax67Proofs` renamed throughout: 2 module
   directories and 2 root modules moved, package/`lean_lib`/`defaultTargets`
   names in both lakefiles, every `namespace`/`end`, and the 28
   name-quotation literals in `Lax67Proofs/Tactic.lean` — those are `Name`
   literals resolved at elaboration, so a missed one would have silently
   stopped `run_vcg` from matching rather than failing the build.
4. Jan chose the second of §5's two options: the dependents move too. The
   rename is a pure token swap in `ram-linear-time` (Lax11, 96 occ),
   `refinement-tower` (Lax62, 146 occ) and
   `nowhere-dense-model-checking` (Lax3, 118 occ) — imports, `open` lines,
   qualified names, prose and `[[require]]` names; no identifier embedded
   `13` in any other way. `lax-15` was already gone (below), so it needed
   nothing. `README.md` prose followed; `NIGHTLOG.md` and the rest of
   `plans/` keep `Lax13` as historical record.
5. `word-ram/concepts` and `word-ram/proofs` build green and
   `lax build word-ram` passes the namespace audit (2 concepts, 2m25s). Its
   one warning — whether an owner of lax-13 owns lax-67 could not be checked
   locally — is for the archive to decide at registration.
6. `.claude/resubmit-cascade.sh`'s default order keeps `word-ram` in first
   place, now as Lax67; the folder is a draft again, so the idempotency
   check works on it. The cascade then repins Lax11, Lax62 and Lax3 to the
   lax-67 record and resubmits them, with `sparsity-lectures` and
   `monadic-dependence-neighborhood-complexity` folded in for their own
   abstract edits.

Registration of lax-67 is **not** done and needs fresh explicit consent
([[submission-freeze-consent]] in memory); registration is what makes the
supersedes link permanent.

**Done 2026-09-03: lax-15, vertex-cover-ladder, deleted** on Jan's
instruction ("we no longer need it", 2026-09-02). `lax delete
vertex-cover-ladder` retired the id permanently; `vertex-cover-ladder/` is
removed from the tree (last present at `b80cc51`) and from the cascade
script's default order; `plans/vertex-cover-ladder/` is closed history. The
2^k bounded search tree proof it stated stays in `Lax11Proofs` (VC*.lean)
without a statement on any surface.

## 6. Execution

1. **W1 — word-ram** — **LANDED 2026-09-02 @ 05eb63a** (3286 jobs green,
   `lax build` audit clean, `Transfer.lean` zero diff, `Ok` byte-identical,
   supervisor polish of the concept header). Was: (worktree `ram1`, one worker): `Ram.lean`,
   `abstract.md`, `Machine.lean`, `Compile.lean`, `Simulation.lean`, and the
   mechanical updates listed in §4 inside `word-ram/proofs`. Gates: both
   packages `lake build` green; `lax build --only proofs word-ram` namespace
   audit; `compileProgram_runsTo`, `Solves`, `computesInTime_of_solves`
   statements unchanged; `Com.Ok`/`Expr.Ok` unchanged except the `assign`
   conjunct; `#guard`-check the three bit identities before proving them.
2. **W2a/b/c** — Lax11, Lax15, Lax3, in parallel after W1 lands: repin,
   numerals, docstrings; `lake build` each; `.claude/sibling-overrides.sh`
   clean.
3. Resubmission per §5, Jan-triggered.
4. Fold the settled machine into `word-ram-plan.md`'s "The model (settled)"
   section in place; close this file.
