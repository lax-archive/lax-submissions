# Word RAM: minimal instruction set

Rev 1 PROPOSAL, 2026-09-02. Requested by Jan: remove from `Lax13.Ram.Instr`
every instruction that the remaining ones simulate at constant overhead, and
account for the knock-on effects on everything built on the machine. No code
has been changed; the decision flags at the end are Jan's.

## 1. The audit

`Lax13.Ram.Instr` has 18 constructors, `Op` has 3. Every candidate below was
checked against the concept's exact semantics (`Instr.effect` in
`word-ram/concepts/Lax13/Ram.lean`): a simulation counts only if the machine
state after the block equals the state after the single instruction, on all
word lengths, with only compiler-reserved scratch cells disturbed.

### 1a. Remove — zero overhead

| instruction | simulation | why it is free |
|---|---|---|
| `halt` | none needed | `step` already returns `none` when the program counter runs past the program (and on a `read` from an exhausted tape). `compileProgram L c = compile L c 0 ++ [.halt]` becomes `compile L c 0`. A mid-program halt, which the compiler never emits, is `jump p.length`. |
| `jgtz l` | `jzero (pc+2); jump l` | The accumulator is zero or positive, so the two-instruction block branches exactly as `jgtz`, without touching the accumulator. The compiler never emits `jgtz`; only its `Machine.effect_jgtz` equation exists. Dropping `jump` instead (`jump l = jzero l; jgtz l`) would touch every `ite`/`while` block and the constant, so `jgtz` is the one to go. |

### 1b. Remove — constant overhead, two scratch cells

Let `S0`, `S1` be two cells reserved by the compiler (placement in §3). In
all three blocks every intermediate value is a word whenever the inputs are,
so the concept's `% 2 ^ w` never fires and the simulation is an equality,
not a congruence. `o` is the original operand, re-read where needed; it can
never name `S0`/`S1` because those are not in any layout.

| instruction | block (acc = `a`, operand value `b`) | identity | length |
|---|---|---|---|
| `or o` | `store S0; and o; store S1; load o; sub (mem S1); add (mem S0)` | `a ∨ b = a + (b − (a ∧ b))`; `a ∧ b ⊆ b` makes the monus exact and `a`, `b ∧ ¬a` have disjoint bits so the sum is `a ∨ b < 2^w`, no wrap | 6 |
| `xor o` | `store S0; and o; store S1; load o; sub (mem S1); add (mem S0); sub (mem S1)` | `a ⊕ b = (a ∨ b) − (a ∧ b)`, exact since `a ∧ b ⊆ a ∨ b` | 7 |
| `shiftr o` | `store S0; load (lit 1); shiftl o; store S1; load (mem S0); div (mem S1)` | `a / 2^n`; for `n < w` the divisor is exactly `2^n`; for `n ≥ w` the shift wraps to `0`, `a / 0 = 0`, and `a / 2^n = 0` too since `a < 2^w ≤ 2^n` — the concept's `x / 0 = 0` convention makes the two agree | 6 |

Which bitwise operation to keep: any one of `and`/`or` regenerates the other
two with `add`/`sub` at the lengths above (`and` from `or`:
`a ∧ b = (a∨b) − ((a∨b) − a) − ((a∨b) − b)`). `xor` alone does not:
recovering `a ∧ b` from `a ⊕ b` needs `a + b`, which wraps. Keep `and`, the
one every AC⁰-RAM paper keeps.

Which shift to keep: `shiftl` is the only instruction that produces `2^n`
for a *variable* `n` in one step, and variable shifts are what the bitmask
code uses (`IicfBitmask`: `1 shiftl i`). `shiftr` by a variable amount is
then `div` by that power. The reverse (`shiftl` from `shiftr`) needs the
all-ones word, an `O(w)` prologue, not constant.

### 1c. Derivable but recommended to keep

These are exact constant-cost simulations too; the plan lists them so the
cut is made knowingly. Recommendation: keep all three, because the model is
meant to be recognisably Aho–Hopcroft–Ullman's accumulator machine, and each
of these is a defining feature of that skeleton rather than an operation.

| instruction | simulation | remark |
|---|---|---|
| `load o` | `and (lit 0); add o` (2 instructions, no scratch) | Exact: `0 ∧ a = 0`, `0 + b mod 2^w = b mod 2^w`. A machine that cannot load is a curiosity. **Jan-flag D1.** |
| `Op.mem a` | materialise `a` into a scratch cell and use `Op.ind` (7 instructions, 3 scratch) | Direct addressing is the readable half of AHU addressing; removing it makes every scalar access an indirection. |
| `store a` | bootstrap from zeroed memory with `storeInd` (an `O(program)` prologue that writes each static address into a cell) | The prologue is per program, not per instruction, but it exists; and `store` is what makes memory addressable by fixed cell numbers at all. |

### 1d. Not derivable at constant cost — stay

`read`, `write` (the tapes); `add`; `sub` (wrapping negation needs
`2^w − 1`, an `O(w)` prologue, and monus additionally needs a comparison —
the concept notes already argue monus is the comparison primitive); `mul`,
`div`, `and`, `shiftl` (bit-parallel operations are not `O(1)` in each
other); `storeInd`, `Op.ind` (the only indirect write and read); `jump`,
`jzero` (one unconditional and one conditional jump are the minimum for
`ite`/`while`).

### 1e. Result

18 → 13 instructions: `read, write, load, store, storeInd, add, sub, mul,
div, and, shiftl, jump, jzero`; `Op` unchanged. With D1 taken as well, 12.

## 2. What the change is *not*

IMP+ keeps its nine `Bop`s. The removed operations become compiler-lowered
operators rather than machine instructions: `Compile.binInstr : Bop → Op →
Instr` becomes `binCode : Bop → Op → Program` (a singleton for six
operators, the blocks of §1b for three). Reasons:

- the refinement tower prices IR operations per currency (`"ir.or"`,
  `"ir.xor"`, `"ir.shiftr"` appear in ~10 Sepref/IICF files) and `Embed`
  maps every IR `binop` to one IMP+ `assign` at cost 4 regardless of the
  operator, so the IMP+ cost model is untouched and every landed cost claim
  above IMP+ (ND-MC budgets, tower constants) survives verbatim;
- the ND-MC and tower proofs never touch `Ram.Instr` (checked: no
  `Instr.`/`Op.` constructor site outside `Ram.lean`, `Machine.lean`,
  `Compile.lean`, `Simulation.lean`);
- the machine-step constant `Layout.const` is where the lowering is paid,
  and constants are not defects (Jan, 2026-08-02).

The IMP+ docstring's "one operator for each of the machine's instructions"
is reworded to "six operators are machine instructions, three are lowered by
the compiler to fixed blocks".

## 3. Scratch cells and the layout

The lowering of `or`/`xor` needs three live values (`a`, `b`, `a ∧ b`) and
the accumulator holds one, so two cells beyond the operand's temporary are
unavoidable. Two placements:

- **(a) reserved cells between temporaries and scalars** — `S0 = L.temps`,
  `S1 = L.temps + 1`; `varAddr x = L.temps + 2 + idx`, `arrBase` and `span`
  shift by 2; `Expr.Ok`/`Com.Ok` untouched. Temporaries keep their addresses
  `d`, so `Reaches.frame` widens only to `i < d ∨ L.temps + 2 ≤ i`.
  **Every downstream layout literal and every downstream `Ok` proof survives
  verbatim**; downstream `span` proofs gain a `+ 2` inside an `omega` that has
  hundreds of cells of slack (CC: `17 + 4|x| → 19 + 4|x|` against
  `2604·(|x|+1) ≤ 2^w`).
- (b) require `d + 2 < L.temps` at every `bin` node — changes `Expr.Ok`,
  forces a `temps` bump in every downstream layout (they declare 2–4) and a
  re-check of every `Com.Ok` proof. Rejected.

**Recommendation: (a).**

## 4. The new constant

`esize` of a `bin` node grows from `+ 2` to `+ (1 + binLen op) ≤ + 8`, so
`esize ≤ (idxLen + 8) · size` replaces `(idxLen + 2) · size` and
`Layout.const = 3·idxLen + 13` becomes about `3·idxLen + 31` (the proof of
`compile_correct` settles the exact value; nothing is tight). Downstream
`const_eq` numerals move accordingly, roughly `+ 18`:

| file | now | after (≈) |
|---|---|---|
| `Lax11Proofs/CCMain.lean` | 31 | 49 |
| `Lax11Proofs/VCMain.lean`, `TreeFoldMain.lean` | 37 | 55 |
| `Lax11Proofs/CourcelleMain.lean` | 46 | 64 |
| `Lax15Proofs/Main.lean` (`vcfLayout`) | 43 | 61 |
| `Lax15Proofs/Main3.lean` (`vcf3Layout`) | 49 | 67 |
| `Lax13Proofs/Simulation.lean` sanity `∃ t ≤ 44` | 44 | recomputed |

The headline statements are unaffected: every downstream concept quantifies
`∃ (p : Program) (c : ℕ)`, so only the proof-side witnesses (`2604`,
`90300 = 43·2100`, `318500`, `33300 = 37·900`, …) and their docstrings move.
ND-MC's `mcLayout.const` is symbolic throughout (`Headline.lean`,
`ProgCodegen.lean`) and needs no numeral change.

## 5. Knock-on inventory

### word-ram (Lax13) — the leaf that does the work

Concept package (`word-ram/concepts`, endorsement surface — changes force a
resubmission):

- `Lax13/Ram.lean`: delete five constructors and their `effect` cases;
  rewrite the header ("jumps unconditionally or on the accumulator being
  zero"; no "or halts"); extend the "omitted because derivable" paragraph
  from remainder + negation to remainder, negation (now `(2^w − 1) − a`,
  monus from the all-ones word), `or`, `xor`, `shiftr`, `jgtz`, `halt`, with
  the derivations of §1; fix "tests `a > b` by subtracting and jumping on a
  positive accumulator" (that is `jgtz`) to "subtracting and jumping on zero
  to the other branch"; singularise "the shifts" in the truncation paragraph;
  the halting paragraph now names two halting modes (program counter past the
  end, exhausted input).
- `Lax13/RamComputes.lean`: unchanged.
- `abstract.md`: "multiplication, division, shifts and the bitwise
  operations" → the reduced list; "why remainder and bitwise negation are
  omitted as derivable" → the extended list.
- `manifest.yaml`: unchanged unless the abstract lives there too (check).

Proof package (`word-ram/proofs`):

- `Machine.lean`: delete `effect_or`, `effect_xor`, `effect_shiftr`,
  `effect_jgtz`, `effect_halt`.
- `Compile.lean`: `binInstr` → `binCode` + `binLen`; scratch addresses
  `Layout.scratch0/1`; `varAddr`, `arrBase`, `span` shifted by 2 and the
  five address lemmas (`varAddr_lt_two_pow`, `arrAddr_lt_two_pow`,
  `temps_le_varAddr`, `varAddr_lt`, `le_arrAddr`) re-derived; `esize`
  bin case; `Layout.const`; `compileProgram` loses `[.halt]`. The docstring's
  "all nine operators compile to the same three-block shape" becomes "six
  do; three end in a fixed block".
- `Simulation.lean`: `Reaches.frame` widened; `Represents.reaches` uses the
  new `temps + 2 ≤ varAddr`; `compileExpr_correct` bin case splits into the
  six direct operators (existing `effect_binInstr` argument) and three block
  lemmas `reaches_orCode`, `reaches_xorCode`, `reaches_shiftrCode`, each a
  6–7 step straight-line `Reaches` proof; `esize_le_size`, `bsize_le`,
  `idxLen_le_const` re-proved at the new constant; `compileProgram_runsTo`'s
  `hhalt` becomes "`p[size]? = none`", which is simpler.
- The three bit identities of §1b are **not in mathlib** as such (loogle and
  leansearch, 2026-09-02): prove them once in `Lax13Proofs.Machine` or a
  small `Bits.lean` by `Nat.eq_of_testBit_eq` / `Nat.testBit` case analysis,
  after a `#guard`/Plausible pass (refute-before-prove). This is the only
  non-mechanical proof content of the whole change.
- `Smoke.lean`, `Lib/{Queue,Trail,Csr,Ind,Stack,Fill}.lean`,
  `Refine/Codegen/Harness.lean`, `Refine/Codegen/Examples/EndToEnd.lean`:
  `simp [Layout.const, Layout.idxLen, layout]` numerals and `#guard` step
  gates recompute; the gates compare machine steps against
  `const · K` and `const` grows faster than the lowered blocks, so they keep
  passing.
- `Refine/Sepref/SpaceBudgetProbe.lean` (15 sites) and `HeapAlloc.lean`
  (3): span arithmetic shifts by 2.
- Untouched: `Imp.lean` (docstring only), `Bounds.lean`, `Reasoning.lean`,
  `Transfer.lean`, `Frame.lean`, `Spec.lean`, `Tactic.lean`, the whole
  `Refine/` tower except the two span files above.

### ram-linear-time (Lax11)

Proofs only: four `const_eq` numerals, the four headline witnesses and
docstrings (`CCMain`, `VCMain`, `TreeFoldMain`, `CourcelleMain`,
`TreeFoldRun`), span docstrings. Concepts: repin `Lax13` to its new record
rev (`lakefile.toml`), nothing else. No `Ram.Instr` site anywhere.

### vertex-cover-ladder (Lax15)

Proofs only: two `const_eq` numerals, three headline witnesses (`Main`,
`Main3`, `MainFpt`) and their "the product is" docstrings. Repin `Lax13` and
`Lax11`.

### nowhere-dense-model-checking (Lax3)

Proofs: `ProgCodegenLayout.lean` (`mcLayout_span_le` and its "`11 + |eS|
+ …`" docstring shift by 2), `SolveMatTop.lean` docstring mention of
`temps`. Constants are symbolic; nothing else. Repin `Lax13`, `Lax11`,
`Lax13Proofs`, `Lax12Proofs` as the sibling script reports. Sequence this
after the current ND-MC pause so no open ND-MC worktree builds against a
moving `Lax13Proofs`.

### Unaffected

`sparsity-lectures` (Lax12), `finite-ramsey` (Lax14),
`monadic-dependence-neighborhood-complexity` (Lax5), both twin-width
submissions: no dependency on `word-ram`.

## 6. Resubmission cascade

The concept change moves Lax13's archive record, and cross-submission
requires are rev-pinned, so the drafts must be resubmitted in DAG order:
**Lax13 → Lax11 → {Lax15, Lax3}**. All four are drafts
(`~/.lax/lax-database/lax-N/record.json`, `state: draft`), so no freeze or
registration question arises; this is the same cascade as the 2026-07-27
word-RAM resubmission. `lax submit` of each draft is Jan's action or needs
his go-ahead per submission (standing consent rule); the repo work lands on
`main` independently of it.

## 7. Execution

Sequential leaves, one worktree each, DAG-bounded parallelism after the
root lands:

1. **Leaf W1 — word-ram core** (one worker, ~half a day). Files:
   `Ram.lean`, `abstract.md`, `Machine.lean`, `Compile.lean`,
   `Simulation.lean`, plus the mechanical numeral/gate updates in `Smoke`,
   `Lib/*`, `Harness`, `EndToEnd`, `SpaceBudgetProbe`, `HeapAlloc`, and the
   `Imp.lean` docstring. Gates: `lake build` of both packages green;
   `lax build --only proofs word-ram` for the namespace audit; the three bit
   identities `#guard`ed before proved; `Layout.const` written as a closed
   formula in `idxLen` and the new value recorded here. Review points:
   `compileProgram_runsTo` statement unchanged; `Solves`/`Transfer` surface
   unchanged; `Expr.Ok`/`Com.Ok` unchanged; `Reaches.frame` is the only
   invariant that widened.
2. **Leaf W2a — ram-linear-time**, **W2b — vertex-cover-ladder**, **W2c —
   nowhere-dense-model-checking** (parallel, disjoint submissions, each
   mechanical: repin, numerals, span docstrings). Gate: `lake build` of each
   proofs package; `.claude/sibling-overrides.sh` reports no mismatch.
   W2b depends on W2a's repin only through the `Lax11` record rev, so it
   can run against the sibling folder immediately and repin at submit time.
3. **Resubmission** in the order of §6, Jan-triggered.
4. Update `word-ram/word-ram-plan.md`'s "The model (settled)" section in
   place with the 13-instruction set (supersede-in-place rule) and close this
   file.

## 8. Decisions for Jan

- **D1** — also remove `load` (`and (lit 0); add o`)? Recommendation: keep.
- **D2** — bitwise survivor `and` (recommended) or `or`? `xor` cannot be the
  survivor.
- **D3** — scratch placement (a) reserved cells between temporaries and
  scalars (recommended) vs (b) `d + 2 < temps`.
- **D4** — IMP+ keeps nine `Bop`s with compiler lowering (recommended) vs
  shrinking IMP+ too, which would touch the IR currencies, `Embed`, the
  bitmask implementation and every currency table in `Refine/`.
- **D5** — `halt` out (recommended); running past the program is then the
  compiler's halting mode and a mid-program halt is `jump p.length`.
