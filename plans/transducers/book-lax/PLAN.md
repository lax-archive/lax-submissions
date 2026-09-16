# *Transducers* as Lax submissions — the plan

Rev 2, 2026-09-07. Status: **DECIDED** — Jan answered §1 on 2026-09-07; the
submissions are being scaffolded. Rev 1 was the proposal.

Source: the book *Transducers* (M. Bojańczyk), `../main.tex` with its four
parts, and its Lean formalisation `../transducer-lean/` (Lean 4.28, `import
Mathlib`, 464 files, 138k lines, 100 numbered environments of which 77 results
and 20 definitions are formalised, 81 exercises, everything proved, no
`sorry`, no axiom). `../transducer-lean/` is a mirror of Aristotle's server
(rsynced with `--delete`) and is never edited; the submissions copy out of it.

The goal: the book's mathematics as citable Lax submissions — clean concept
packages a reader of the book recognises, proof packages that absorb the
existing development, and the book's own text as the paper layer on top,
chapter by chapter, with cards on every definition and theorem.

---

## 1. Decisions (Jan, 2026-09-07)

| # | question | decision |
|---|---|---|
| D1 | granularity | **seven** part submissions (Part C cut by topic), as in §2 |
| D2 | paper layer | **only an umbrella** submission S7 `transducers-book` carries the paper: the whole book, requiring all seven part submissions so that its markers can name every concept and proof. The part submissions carry no `paper/`. This makes WEBSITE-REQUEST §3 (reverse links from a concept to the papers marking it) the important request; §1 (cross-submission `\cref`) is moot |
| D3 | biconditionals | split **only the headline characterisations** the book proves as two halves (2dfa ↔ regular, sst ↔ regular, mso transduction ↔ regular, rational ↔ relabelling, Büchi, FO ↔ aperiodic dfa, FO relabelling ↔ aperiodic bimachine, aperiodic ↔ flip-flops, rational primes, bimachines TFAE, for ↔ polyregular, pebble ↔ for); everything else is one axiom as stated |
| D4 | open statements | **exactly what is formalised becomes a concept**, proven or not; nothing is added for results the Lean does not state (so Theorem C.5.4 appears as its proved easy half only, Conjecture C.1.5 and the decidability sentence of A.2.8 do not appear) |
| D5 | exercises | **deferred** to a follow-up campaign (one exercises submission per part) |
| D6 | authors | **Mikołaj Bojańczyk** and **Aristotle (Harmonic)** on every manifest |
| D7 | location | this repository, `lax/<name>/`, one folder per submission |
| D8 | license | the umbrella ships the book's sources and pictures under **Apache 2.0** |
| D9 | environment | the **epoch** (Lean 4.30.0, mathlib `c5ea003`); the port is cheap (§6) |
| D10 | lax-52 | not a dependency; mentioned in the logic submission's abstract |

## 2. The submissions

Seven submissions. Arrows are requires; `P` marks a proof-package require
(discouraged by the spec but unavoidable: the constructions of Part A are the
toolkit of Parts B–D).

```
S0  pcp-undecidability      Undecidability of the Post correspondence problem
S1  mealy-machines          Part A + Introduction        (requires nothing)
S2  rational-functions      Part B                        ← S1, S0 (proofs also S1P)
S3  regular-functions       Part C §1–3: primes, two-way transducers, ssts   ← S2 (S2P)
S4  mso-transductions       Part C §4: logic              ← S3 (S3P)
S5  regular-combinators     Part C §5: combinators        ← S3 (S3P)
S6  polyregular-functions   Part D                        ← S4 (S4P)
S7  transducers-book        the paper: the whole book     ← S0–S6 (and S0P–S6P), no Lean of its own
```

| id | book text (paper) | Lean source (proofs) | lines | concepts (est.) |
|---|---|---|---|---|
| S0 | none (Sipser §4.2, §5.2 cited) | `Acceptance/`, `Sim/`, `PCP/` | 6.6k | 6 |
| S1 | `intro.tex`, `partAMealy/*` | `Common/{Basic,Aux}`, `PartA/*` | 2.8k | 20 |
| S2 | `partBRational/*` | `PartB/*`, `Common/{PrimrecArith,PrimrecList*,RegularAux}` | 18k | 35 |
| S3 | `partCRegular/{intro,regular-primes,2dfa,sst}` | `PartC/*` minus logic and combinators, `Common/HankelRank` | 40k | 28 |
| S4 | `partCRegular/logic` | `PartC/MSO*`, `Mark*`, `FO*`, `Walk*`, `KTypes`, … | 13k | 25 |
| S5 | `partCRegular/combinators` | `PartC/Comb*` | 3k | 5 |
| S6 | `partDPolyregular/*` | `PartD/*` | 22k | 18 |
| S7 | `main.tex` and everything it inputs | none | 0 | 0 |

Why this cut and not another:

- **Per part** is the book's own citable unit, and the reader's. Part C alone
  is 55k lines and five sections on genuinely different models, so it is cut
  along its sections into three; each of the three has a self-contained
  paper (two-way transducers + ssts, logic, combinators).
- **S0 is not book content.** The book takes PCP's undecidability as given;
  Aristotle proved it from Sipser (partial recursive programs as the machine
  model, a Turing-machine simulation, the computation-history reduction).
  It is a general result others will cite, so it stands alone and S2's
  proof of Theorem B.1.6 takes `S0.PostCorrespondenceUndecidable` as an
  assumption in the proof network.
- **Shared helper libraries** (`PrimrecArith`, `PrimrecList`: arithmetic on
  ℤ and ℚ in mathlib's `Primrec` API; `HankelRank`: Schützenberger's rank
  criterion) go into the proof package of the first submission that needs
  them; later proof packages require it. Nothing of them is endorsement
  surface.
- **Not ported:** `Labels.lean` (bookkeeping the markers replace),
  `Main.lean` (global options), the `tools/`, and the exercises (D5).

---

## 3. The concept packages, submission by submission

Conventions carried over unchanged from the source, because a reader of the
book recognises them: strings are `List A`, languages `Language A`, regular
is mathlib's `Language.IsRegular`, finiteness is `[Finite A]`, "there is a
machine" is `∃ (Q : Type) (_ : Finite Q) (M : …), …`, "composition of
primes" is `CompClosure P`, decidability is a `Computable` Boolean function
on finite descriptions (codes) correct under a promise. Everything that is a
`Prop` stays a `Prop`; no `Bool` encodings and no `Classical` in concept
files.

What changes from the source: one module per idea, docstrings rewritten as
paper-level prose with `# Formalization notes`, every derivable field
dropped, the corrected statements of the book (aperiodicity as an
`Option`-valued last letter, Claim C.2.11 on nonempty inputs, sentences
rather than formulas in C.4.13) kept with the reason spelled out on the
card, the tuple codes (`RelCode`, `WCode`, `TwoWayCode`) turned into named
structures where that costs nothing.

Names below are working names (`Definition` / `Theorem` = the frontmatter
`type`). "iff→2+glue" marks the biconditionals that D3 splits.

### S0 `pcp-undecidability`

| concept | type | content |
|---|---|---|
| `AcceptanceProblem` | definition | machines = `Nat.Partrec.Code`, `Accepts`, `IsDecider`, `TuringDecidable`, `ATM`, `ComputablyDecidable` |
| `AcceptanceUndecidable` | theorem | `¬ TuringDecidable ATM` (Sipser 4.11) |
| `TuringMachines` | definition | Sipser's single-tape machine as string rewriting, configurations, `Accepts` |
| `PostCorrespondence` | definition | instances over ℕ, `Solvable` in index form; also `HasMatch` in domino form |
| `PostCorrespondenceReduction` | theorem | PCP decidable → A_TM decidable (Sipser 5.15, the many-one reduction) |
| `PostCorrespondenceUndecidable` | theorem | `¬ ComputablePred Solvable` — the form Part B consumes |

### S1 `mealy-machines`

| concept | type | book |
|---|---|---|
| `Continuity` | definition | Def. 0.1 (`Continuous`, and the relational and partial variants Part B uses) |
| `CompositionClosure` | definition | `CompClosure`, `FamUnion` — the "finite composition of primes" idiom |
| `MealyMachine` | definition | Def. A.1.1: `Mealy`, `run`, `eval`, `IsMealy` |
| `StateTransformations` | definition | `strTrans`, `Mealy.trans`, condition (*) `TransAperiodic` |
| `PrimeMealyMachines` | definition | Def. A.2.1: `Reversible`, `FlipFlop`, `PrimeMealyFam`, `FlipFlopFam` |
| `MapLifting` | definition | Def. A.2.3: `splitSep`, `mapLift` |
| `Aperiodicity` | definition | Def. A.2.7 (corrected: last letter in `Option B`), `npow` |
| `Derivatives` | definition | the derivative `f⁽ʷ⁾` of Lemma A.2.10 |
| `MealyEquivalenceBound` | theorem | Thm. A.1.2 as the finite check `|Q₁|·|Q₂|` |
| `MealyComposition` | theorem | Thm. A.1.3 |
| `MealyContinuity` | theorem | Thm. A.1.4 |
| `KrohnRhodes` | theorem | Thm. A.2.2 |
| `MapLiftingDecomposition` | theorem | Lemma A.2.4 |
| `StateTransformationDecomposition` | theorem | Lemma A.2.5 (the transducer is claim-local) |
| `ReversibleComposition` | theorem | Lemma A.2.6 |
| `AperiodicMealy` | theorem, iff→2+glue | Thm. A.2.8 (`FlipFlopsOfAperiodic`, `AperiodicOfFlipFlops`); the decidability sentence is not formalised and does not appear (D4) |
| `AperiodicPumping` | theorem | Claim A.2.9 |
| `MealyDerivatives` | theorem | Lemma A.2.10 (Myhill–Nerode for Mealy machines) |
| `AperiodicityMinimalMachine` | theorem | Lemma A.2.11, in the "some machine computing f satisfies (*)" form |

### S2 `rational-functions`

| concept | type | book |
|---|---|---|
| `LabelledAutomata` | definition | `LabAut`, paths, accepting paths — the common basis of B.1.1 and B.3.2 |
| `RationalRelations` | definition | Def. B.1.1–B.1.2: `NFAO`, `rel`, `Unambiguous`, `IsRationalRel`, `IsUnambiguousRel`, `Productive` |
| `RationalFunctions` | definition | Def. B.2.1, `homOf` |
| `Bimachines` | definition | Def. B.2.2, `IsBimachine`, `IsAperiodicBimachine` |
| `PrimeRationalFunctions` | definition | the family of Thm. B.2.6 |
| `TransducerCodes` | definition | `RelCode`, `codeRel`, `CodeWord`, `CodeFunctional`, `DecidableUnderPromise` (the decidability idiom, with the note on why totality over ℕ* is vacuous) |
| `WeightedAutomata` | definition | Def. B.3.2, `IsWeighted` |
| `WeightedCodes` | definition | `WCode`, `wcodeEval`, `WCodeValid` |
| `SequentialTransducers` | definition | `Sequential`, `IsSequential` |
| `SubsequentialTransducers` | definition | `Subsequential`, `IsSubsequential` |
| `LeftDistance` | definition | Def. B.4.7, `BoundedVarRel` |
| `RationalComposition` | theorem | Thm. B.1.4 |
| `RationalContinuity` | theorem | Thm. B.1.5 |
| `RationalEquivalenceUndecidable` | theorem | Thm. B.1.6 (proof assumes S0) |
| `HomomorphismComplement` | theorem | Claim B.1.7 |
| `Bimachines…` | theorem, TFAE→3+glue | Thm. B.2.3: `UnambiguousOfRational`, `BimachineOfRational`, `RationalOfBimachine`, glue `RationalUnambiguousBimachine` |
| `EpsilonElimination` | theorem ×2 | Lemma B.2.4, its two sentences |
| `Uniformisation` | theorem | Lemma B.2.5 |
| `RationalPrimes` | theorem, iff→2+glue | Thm. B.2.6 |
| `RationalMealyCharacterisation` | theorem | Thm. B.2.7 |
| `WeightedEquivalenceDecidable` | theorem | Thm. B.3.3 |
| `RationalEquivalenceDecidable` | theorem | Thm. B.3.4 |
| `WeightedPrecomposition` | theorem | Lemma B.3.5 |
| `RationalViaWeighted` | theorem | Thm. B.3.6 (the converse of B.3.5; glue for the iff) |
| `WeightedZeronessDecidable` | theorem | Thm. B.3.7 |
| `MealyMachineIndependent` | theorem | Thm. B.4.1 |
| `MealyDecidable` | theorem | Thm. B.4.2 (relativised to the code's alphabet) |
| `LengthPreservingDecidable` | theorem | Lemma B.4.3 |
| `LengthPreservingTyping` | theorem | Claim B.4.4 |
| `LengthPreservingNormalForm` | theorem | Lemma B.4.5 |
| `SequentialCharacterisation` | theorem | Thm. B.4.6 (with item (c)) |
| `SubsequentialCharacterisation` | theorem | Thm. B.4.8 |
| `RationalMachineIndependent` | theorem | Thm. B.4.13 |

Claims B.4.9–B.4.12 are internal steps of B.4.8, formalised in reorganised
form; they stay helpers (no card; see WEBSITE-REQUEST §4).

### S3 `regular-functions`

| concept | type | book |
|---|---|---|
| `RegularFunctions` | definition | Def. C.0.1: `mapReverse`, `mapDuplicate`, `IsRegularFun` |
| `TwoWayTransducers` | definition | Def. C.2.1: `TwoWay`, configurations, `Reaches`, `Computes`, `IsTwoWay` |
| `ConfigurationGraphs` | definition | the alphabet `C`, `enc`, `pathTrans` of Lemmas C.2.3–C.2.4 |
| `TwoWayCodes` | definition | `TwoWayCode`, `twoWayCodeRel`, `TwoWayCodeTotal` |
| `StreamingStringTransducers` | definition | Def. C.3.1: `Copyless`, `SST`, `eval`, `IsSST` |
| `SnakeGraphs` | definition | snake letters, `snakeOut`, width (Lemma C.2.12) |
| `RegularContinuity`, `RegularComposition` | theorem ×2 | Thm. C.1.1 |
| `ReversalDuplicationContinuous` | theorem | Lemma C.1.2 |
| `MapLiftingContinuity` | theorem | Lemma C.1.3 |
| `RegularEquivalenceDecidable` | theorem | Thm. C.1.4 |
| `TwoWayContinuity` | theorem | Thm. C.2.2 |
| `ConfigurationGraphRational` | theorem | Lemma C.2.3 |
| `ConfigurationGraphOutput` | theorem | Lemma C.2.4 |
| `TwoWayComposition` | theorem | Thm. C.2.5 |
| `TwoWayMealyPrecomposition` | theorem | Lemma C.2.6 |
| `TwoWayRationalPrecomposition` | theorem | Cor. C.2.7 |
| `TwoWayOfRegular` | theorem | Cor. C.2.8 |
| `RegularOfTwoWay` | theorem | Thm. C.2.9, the hard half; `TwoWayIffRegular` glue |
| `RegularMapLifting`, `RegularConcatenation`, `RegularConditional` | theorem ×3 | Lemma C.2.10 |
| `RegularSum` | theorem | Claim C.2.11 (corrected on ε) |
| `SnakeLemma` | theorem | Lemma C.2.12 |
| `SSTOfRegular`, `RegularOfSST` | theorem ×2 + glue | Thm. C.3.2 |

### S4 `mso-transductions`

| concept | type | book |
|---|---|---|
| `MSOLogic` | definition | syntax, `Sat`, `IsFO`, `qrank`, free variables, `MSODefinable`, `FODefinable`, `annotate` |
| `MSORelabellings` | definition | Def. C.4.3, `IsMSORelabelling`, `IsFORelabelling` |
| `MSOTransductions` | definition | Def. C.4.7 in the "copies + extra" presentation, `Proper`, `IsMSOTransduction`, `IsFOTransduction` |
| `KTypes` | definition | Def. C.4.12 |
| `BuchiTheorem` | theorem, iff→2+glue | Thm. C.4.1 |
| `MSOFreeVariables` | theorem | Lemma C.4.2 |
| `RationalOfRelabelling`, `RelabellingOfRational` | theorem ×2 + glue | Thm. C.4.4 |
| `MSOAnnotationRegular` | theorem | Claim C.4.6 |
| `RegularOfMSOTransduction`, `MSOTransductionOfRegular` | theorem ×2 + glue | Thm. C.4.8 |
| `LogicPrecomputation` | theorem | Lemma C.4.10 |
| `AperiodicOfFO`, `FOOfAperiodic` | theorem ×2 + glue | Thm. C.4.11 |
| `KTypesFOEquivalence` | theorem | Lemma C.4.13 (sentences) |
| `KTypesRefinement`, `KTypesCongruence`, `KTypesAperiodicity` | theorem ×3 | Lemma C.4.15 |
| `FORelabellingAperiodicBimachine` | theorem, iff→2+glue | Thm. C.4.16 |

Claim C.4.5, Lemma C.4.9, Claim C.4.14: internal steps, helpers.

### S5 `regular-combinators`

| concept | type | book |
|---|---|---|
| `Types` | definition | Def. C.5.1, string representation (Def. C.5.2) |
| `RegularUnderRepresentation` | definition | Def. C.5.2 |
| `RegularTerms` | definition | Def. C.5.3 |
| `RegularOfTerm` | theorem | Thm. C.5.4, easy half — the only half formalised (D4) |

### S6 `polyregular-functions`

| concept | type | book |
|---|---|---|
| `MarkedSquaring` | definition | Example 33 |
| `PolyregularFunctions` | definition | Def. D.0.1 |
| `ForTransducers` | definition | syntax, semantics, `IsForTransducer`, prenex form (Def. D.1.2) |
| `PebbleTransducers` | definition | `Pebble`, configurations, `Computes`, `IsPebbleTransducer` |
| `PebbleConfigurationEncoding` | definition | `pairEnc`, restricted reachability, `BalancedRun` |
| `ChildConfigurationGraphs` | definition | the alphabets and `CGOutIs` |
| `PolyregularContinuity` | theorem | Thm. D.0.2 |
| `ForOfPolyregular`, `PolyregularOfFor` | theorem ×2 + glue | Thm. D.1.1 |
| `PrenexNormalForm` | theorem | Lemma D.1.3 |
| `ForComposition` | theorem | Lemma D.1.4 |
| `PebbleContinuity` | theorem | Thm. D.2.1 |
| `PebbleReachability` | theorem | Lemma D.2.2 (as a regular language of encodings) |
| `BalancedRunReachability` | theorem | Claim D.2.3 |
| `ForOfPebble`, `PebbleOfFor` | theorem ×2 + glue | Thm. D.2.4 |
| `ChildrenOfConfiguration` | theorem | Lemma D.2.5 |
| `ChildGraphOfConfiguration`, `ChildrenOfChildGraph` | theorem ×2 | Claims D.2.6–D.2.7 |

---

## 4. The proof packages

Mechanical port, module by module, of the source files listed in §2, with
these changes:

- `import Mathlib` stays (the archive's warm store makes it free); the
  per-file `set_option`s of `Main.lean` become per-file where needed.
- Every declaration moves under `LaxNProofs.…`; the source's `Transducers.*`
  definitions that became concepts are *deleted* from the proof package and
  the proofs re-target the concept's declaration (same definitional content,
  so the proofs go through unchanged apart from names). Where a concept
  restates a definition differently (named-field codes, D3 splits), a bridge
  lemma proves the two pointwise equal.
- The old `Statements.lean` files become the proof modules: each numbered
  result becomes a `theorem` with `conclusion:` frontmatter pointing at its
  concept, its docstring rewritten (summary, `# Proof strategy`,
  `# Attribution` = the book's section and Aristotle).
- Cross-part uses of constructions (`Mealy.run_cons`, the bimachine
  builder, `RegAut`, …) are proof-package requires down the chain S1P ← S2P
  ← S3P ← S4P ← S6P. S5P requires S3P.

Order of work: S0 and S1 first (independent), then S2, S3, S4 ∥ S5, S6, then S7.
Each submission is built with `lax build --replay` and submitted as a draft
before the next one pins it; registration bottom-up at the end.

---

## 5. The paper layer: the umbrella S7

S7 `transducers-book` is an empty submission (no concepts, no proofs; the
spec allows it) whose concept package requires the concept packages of
S0–S6 and whose proof package requires their proof packages, so that every
`Lax<N>.Concept` and `Lax<N>Proofs.Name` of the book is markable. Its
`paper/` folder is the book:

```
paper/
  main.tex, intro.tex, preface.tex, knowledges.tex
  partAMealy/ partBRational/ partCRegular/ partDPolyregular/   verbatim + % lax markers
  macros.sty, transducer-macros.sty, bib.bib, transducer-book-pics.pdf
```

- Markers: `% lax begin Lax<N>.Concept` around each definition/theorem
  environment (and the prose that carries a definition), `% lax begin
  Lax<N>Proofs.Name` around each proof, `% lax begin lax-<N>` around each
  part's introduction. Inline markers where a notion is defined in running
  text.
- `\cref` works as in the printed book: one document, one `.aux`.
- The book's `\flag{…}` margin notes (four, Lean divergences) stay;
  `\issue`/`\review` are switched off. The web view drops margin notes.
- `\printbibliography` from `bib.bib` (biber runs on the archive).
- Exercises stay in the text as printed, unmarked (D5).
- S7 is submitted last, after the seven part submissions are drafts, and
  registered last.

Dropped deliberately: the web edition's reference PDFs, foldable solutions
and search index.

## 6. Port probe (2026-09-07)

`scratchpad/portprobe`: the source tree unchanged, `lean-toolchain`
4.30.0, mathlib at the epoch pin through the warm store. First layer of
breakage after ~500 modules: `Primrec.list_drop`/`list_take` now exist in
mathlib (delete ours), two `rw` motive/pattern failures, three
`noncomputable` markers in an exercise file. Cheap. Second layer visible
once the first is fixed; tracked in `PORT.md` when the port starts.

The book compiles with `latexmk -pdf` (2.2 MB, `main.aux` produced); biber
did not run in the scratch copy (`main.bbl-SAVE-ERROR` in the repo root
suggests the author sees the same), to be sorted out when the paper folders
are assembled.

Disk: 11 GB free on this machine; a full build of the proof packages is a
few GB. Build one submission at a time and prune probe builds.
