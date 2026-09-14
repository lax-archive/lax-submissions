# Campaign ledger

Opened 2026-09-07. One row per submission; the *next leaf* column is what the
next session or subagent picks up. Keep this file short and current.

| id | folder | concepts | proofs | state (2026-09-07, 23:00) | next leaf |
|---|---|---|---|---|---|
| lax-251941 | `pcp-undecidability` | 9 | 6, all discharged | **draft on the archive with content** (9680c6e), replay green | none |
| lax-765601 | `mealy-machines` | 22 | 13, all discharged | **draft on the archive with content** (cf8ade7), replay green | none |
| lax-132576 | `rational-functions` | 42 | 29, all discharged; Source = 63 modules | **draft on the archive with content** (972ebef), replay green | none |
| lax-916827 | `regular-functions` | 29 | 23, all discharged; Source = 136 modules; replay green (9m36s) | committed; content resubmit running | after the record moves: repin S4/S5/S6 (concepts) and S4/S5 (proofs) to it, submit S4/S5/S6 |
| lax-314295 | `mso-transductions` | 26 | 22, all discharged; Source = 44 modules; replay green | **draft on the archive with content** (8b8f8c6) | none (S6 and S7 pin it) |
| lax-709149 | `regular-combinators` | 4 | 1, discharged; Source = 15 modules; replay green | **draft on the archive with content** (86f2df5) | none (S7 pins it) |
| lax-194892 | `polyregular-functions` | 21 | 15, all discharged; Source = 72 modules | **draft on the archive with content** (4bdfaae; the first submission hit the replay time cap, the identical retry passed) | none (S7 pins it) |
| lax-157538 | `transducers-book` | none (umbrella) | none | **draft on the archive** (7a3dd76): paper 179 pages, 210 marks resolved, pins all seven records; `backend=bibtex` (the archive's sandboxed `biber` cannot exec) and tikz externalization off around `tikzcd` (made the reflow's lualatex pass succeed) in the umbrella's `macros.sty`. Remaining warning: `paper · web-oracle`, the reflow stream diverges from the PDF text at similarity 0.9800 (< 0.98), first at the preface's "This book" read as "is book" — not the Th ligature (disabling ligatures under lualatex changed nothing, reverted) | registration bottom-up (Jan); the web-oracle warning needs laxreflow's own transcript (archive maintainers) |

## v4.33.0 port (2026-09-14)

The epoch moved to v4.33.0 (mathlib `db584cd6`) on 2026-09-13 and v4.30.0
closed. The eight submissions are drafts, so the port is in place: same ids,
same issues, same package names; every pin moved (manifest `leanVersion`
and `mathlibVersion`, both `lean-toolchain` files, both lakefiles' mathlib
`rev`, `tools/umbrella-pins.py`), the Lean fixed in the proof packages only,
no statement changed, no concept file touched. Prepared without submit
rights: resubmission is bottom-up with a repin at every step
(`tools/repin.py`, then `tools/umbrella-pins.py` for the umbrella), as in
"Cross-submission requires" of CLAUDE.md. Local loop: `lax doctor --env
v4.33.0` once, then `python3 tools/local-overrides.py` and a direct `lake
build` per package (concepts, then proofs).

Drift classes met (Lean 4.33 / mathlib db584cd6): (i) tactic targets are
checked for type-correctness at `implicit` transparency, so `simp`/`rw` bail
on a term applying a `→.` (PFun) or passing an anonymous constructor at a
`def`-wrapped type — term-level `.mp`/`.mpr`, explicit lemma arguments, or an
ascription; (ii) a module-name component in Windows' reserved set (`Aux`,
`Con`, `Nul`, …) is a hard error, no option disables it; (iii) `simp` no
longer bridges `id` and `fun x => x` without `Function.id_def`.

- S0 (`pcp-undecidability`, replay not run locally): `Source/Sim/Compile.lean:303`
  `simp only [Part.bind_eq_bind, Part.mem_bind_iff] at hz; obtain …` →
  `obtain ⟨w, hw, hzf⟩ := Part.mem_bind_iff.mp hz`; `:387` the goal-side
  twin → `refine Part.mem_bind_iff.mpr ⟨vargs k u3, ?_, hz⟩`;
  `Source/Sim/Rfind.lean:354` `show …; rw [Nat.rfind_dom]; exact` → `exact
  Nat.rfind_dom.mpr ⟨…⟩` (the `rw` pattern no longer matches the goal's
  `ℕ → Part Bool` lambda against `ℕ →. Bool`); `:389` `exact Part.bind_some
  _ _` after a `simp` that no longer closes `Part.some x >>= ↑f = Part.some
  (f x)`. The `Sym` alias and the `PCPRed` stub compile as they are.
- S1 (`mealy-machines`): `Source/Common/Aux.lean` renamed
  `Source/Common/Auxiliary.lean` (drift ii; importers `Lax765601Proofs.lean:3`,
  `Source/PartA/Statements.lean:14`; `ported.txt` still lists the source
  module `Common/Aux`, and `port.py` derives the ported name from it, so a
  future `--dep Lax765601Proofs` would emit the old import — a rename map
  in `port.py` is owed if Part A is ever re-ported);
  `Source/PartA/StateTrans.lean:584` `simpa [h, Function.id_def]`;
  `Source/PartA/Statements.lean:406,416-417` `derivMealy_trans` /
  `Function.iterate_succ_apply'` given their arguments with the
  `(⟨deriv f u, u, rfl⟩ : Derivs f)` ascription (drift i: `Derivs f` is a
  `def`), `:414` `show deriv f u = _` before the `simp`.
- S2 (`rational-functions`, 9 files, 13 sites; concepts untouched; none of
  the v4.30 workarounds became unnecessary — the `list_take'`/`list_drop'`
  renames, `decode_rat`, the `PairWeighted` binders and the six `CodeRat`
  `erw` sites all still needed): new drift classes (iv) `simpa … using h`
  is stricter than `exact` — a bridge term that is defeq but not
  syntactically equal (`(toSrc M).init` vs `M.init`) now fails "after
  simplification", split into `simp only […]` + `exact h`; (v) `convert h
  using 1` on `Language.IsRegular` leaves an unsolved `Iff`, `exact h`
  works; (vi) an `instance` with an explicit argument instance synthesis can
  never supply is a hard error; (vii) `simp only []` no longer makes
  progress. Sites: `Results.lean:352,371,543` (iv);
  `Source/PartB/SeqChar.lean:305,310`, `SubseqState.lean:42,48` (v);
  `SubseqAlpha.lean:35` `simpa using h` → `simp only [List.append_nil];
  exact h`; `WeightedNF.lean:862` `instance instFiniteUseful (h :
  M.init.Finite)` → `lemma` (vi; both call sites already pass `h`);
  `HomComplement.lean:272` `simp only [] at ht` → `simp only [aut, delta,
  Set.mem_union] at ht` (vii); `LenDec.lean:257` `simpa [memB_iff, codeAut]`;
  `WCodeEnum.lean:136,141` `simpa [wtr]`; `CodeRat.lean:251-260,374-377`
  `List.length_map` instantiated by hand as `have`s over the `def`-wrapped
  `InA c`/`OutA c` (drift i), `:286` `(by simpa using h2)` → `h2`, `:340`
  `simp only [Subtype.coe_eta]` → `rfl`.
- S3 (`regular-functions`, 23 files; concepts untouched; every v4.30
  workaround still needed): new drift classes (viii) `Set` is
  `Set.ofPred`-based and `Language` a `def` over it, so a set-builder at a
  `Language` position is type-incorrect at `implicit` transparency —
  `rw`/`kabstract` refuse the target, `simp only [if_pos h]` does not fire,
  `convert h using 1` on two `IsRegular`s leaves an `Iff` and the following
  `ext` fails; fixes: the term itself / `.mpr`, `isRegular_of_eq h (fun u =>
  ?_)` for `convert … using 1; ext u`, `set L : Language α := …` *before*
  the `rw`, `rw [show <def application> = _ from if_pos h]` (chain
  `if_neg`s with `.trans`) for an `ite` body at `Language`; (ix) `deriving
  Fintype` on an enum (all constructors nullary) is a hard error at this
  mathlib pin (its `mkFintypeEnum` emits a `rw` that is type-incorrect at
  `implicit` transparency; reproduced against bare mathlib) — `deriving
  DecidableEq` kept, `instance : Fintype T := derive_fintype% _` (the
  proxy-type path) added; (x) `Relation.TransGen.mono` is relation-valued
  (`TransGen.mono h _ _ hR`); (xi) `List.Pairwise.forall` takes
  `[Std.Symm R]`, not `Symmetric R`; (xii) an `X = X` that `simp` leaves is
  two `Classical.propDecidable` arguments inside `decide` (`<;> rfl`), and
  "has type X but is expected X" with identical printing is two matcher
  auxiliaries (restate the local `have` through the named `def`). Sites:
  (viii) `Source/PartC/RegAut.lean:49-57,75-81`, `ContAux.lean:21,61,
  133-138,247-249`, `TwoDFA.lean:557`, `MSOAnnot.lean:109`,
  `SnakeChkWin.lean:110-127`, `Results.lean:241`; (ix) `SumShape.lean:70-75`
  (`Shp`), `SumReg.lean:74-78` (`PreSt`), `RegClosure.lean:100-104` (`Cm`),
  `TwoWayErase.lean:128-132` (`EMode`), `TwoWayPrecomp.lean:497-501`
  (`PMode`); (iv) `simpa` given the `def`s it used to unfold —
  `TwoWay.Computes` at `TwoWayHom.lean:76`, `TwoWayComp.lean:929`,
  `TwoWayPrecomp.lean:277`, `RegCodeSan.lean:198,205`; `ValidFrom` at
  `ConfGraphAnnot.lean:107,110`; `excC` at `SnakePieceIdent.lean:600,631`,
  `SnakeChkSlot.lean:156,165`; `encR` at `SumPrime.lean:275`; `appAut` at
  `TwoWayHom.lean:297`; `bstep` at `ContAux.lean:165`; `Nat.add_assoc` at
  `SnakeWinRun.lean:510,539`; `SumShape.lean:406-410` (xii, `decL`),
  `RegPair.lean:406-408` (`simp only … at h; exact h`),
  `TwoWayCont.lean:227` (xii, `<;> rfl`); (x) `SnakeAlphCyc.lean:158,269,
  295`; (xi) `SSTBasic.lean:62-64`.
- S4 (`mso-transductions`, 9 files; concepts untouched; the `export`
  aliases, the ~110 explicit dot-notation sites and the v4.30 drift fixes
  all still needed): `Source/PartC/FlatIndex.lean:11` `Common.Aux` →
  `Common.Auxiliary` (ii); (i) at `def`-wrapped component types
  (`(trans R).E`, `(trans A₀).P`, `(toI T).Elt`, `(toSrcRel R).Idx`) —
  `ITrans.lean:255,256` `rw [ordRel_toI]; exact` → `exact (ordRel_toI …).2 …`,
  `FORelabTrans.lean:142-144,154-155,166-168` `ordRel_inr_iff` applied
  term-level (the fully-applied `rw [ordRel_inl_iff …]` twins still
  rewrite: giving a lemma its arguments is the cheapest fix),
  `FOTransDup.lean:475-511` `rw [selected_iff] at h` → `replace h :=
  (selected_iff w c p).1 h`, `:535,544,548` `refine <lemma>.2 ?_`,
  `MSONorm.lean:169,172` the `simpa` side goal passed as `h1`, `:199-200`
  `subst this; rfl`, `Results.lean:227-228` `simp only [sat_toSrc]; exact h`;
  (iv) `WalkAut.lean:627-629` `rw [List.append_nil] at h; exact h`,
  `FOTransRev.lean:271,276` and `ITransBuild.lean:156-157` constructor
  injectivity as `congrArg Prod.snd (Sum.inl.inj h)` (new sub-case of (i):
  `Prod.mk.injEq`/`Sum.inl.injEq` do not fire when a component sits at a
  `def` for `Unit`/`Bool`; `simp [Prod.ext_iff]` inside a goal, the
  residue `() = PUnit.unit` closes by `exact fun _ => rfl`, not
  `Subsingleton.elim`), `ITransBuild.lean:187` `Function.id_def` (iii).

## Source edits (against the epoch mathlib)

- S0: `Source/PCP/TuringMachine.lean` — `Sym` aliased to the concept's type
  (abbrev + `@[match_pattern]` constructors); `Source/PartB/PCPRed.lean` is
  a hand-written stub with the index-form PCP definitions.
- S1: none. (Warnings: `push_neg` deprecated in `Common/Aux`, `PartA/StateTrans`,
  `PartA/StateTransAperiodic`.)
- S2 (`rational-functions`, Part B, 62 modules + stub `Source/PCP/Index.lean`,
  which takes `Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable`
  as `Transducers.PCP.solvable_not_computablePred`; the two `Solvable`s are
  defeq, `exact` works):
  `Common/PrimrecList.lean:43,60,63,87,98` and `PartB/WCodePrimrec.lean:65` —
  `list_drop`/`list_take` renamed `list_drop'`/`list_take'` (mathlib now has
  them, flipped argument order);
  `Common/PrimrecArith.lean:251-255` (`decode_rat`) — `rw [decode_ofEquiv,
  decode_ratSig]` → `simp only`, and the `obtain ⟨h1, h2⟩ := h` (goal depends
  on `h`) → `revert h; rintro ⟨h1, h2⟩`;
  `PartB/SubseqAlpha.lean:53` — `rwa [heq] at h` → `exact heq ▸ h` (the
  set-builder in `h` no longer matches syntactically);
  `PartB/CodeRat.lean:146,172-173,268,278,335,362` — `rw`/`simp` with
  `List.map_append`/`List.map_cons` on `List (InA c)`/`List (OutA c)` → `erw`
  (`List.map` now elaborates at the unfolded subtype while the list is at the
  `def` `InA c`, so reducible matching fails; `simp` normalises to `unattach`
  and gets stuck the same way);
  `PartB/PairWeighted.lean:143,146` — auto-bound `K` made an explicit
  `{K : ℕ}` binder in `init_pairW`/`final_pairW`.
  `tools/port.py` fixed: it inserted `open <dep>` into Mathlib-only files
  (unknown namespace) and `open <dep>` alone does not make a bare `Mealy`,
  `PrefixPreserving`, … of the dependency resolve — it now inserts
  `open <dep> <dep>.Transducers` only in files whose import closure reaches the
  dependency. (Warnings: `push_neg` deprecated, 32 sites.)
- S3 (`regular-functions`, Part C §1–3, 136 modules = `Common/HankelRank` +
  135 `PartC/*`; `lake build` green 2026-09-07 15:10, subagent):
  `port.py` mis-resolution (Part B's `ported.txt` lists Part A's modules
  too, so `--dep Lax132576Proofs` claimed them) — eight Part A imports
  rewritten to `Lax765601Proofs.Source.*` (`PartC/KTypes.lean:13`,
  `RegAut.lean:21`, `SSTDef.lean:11`, `MapLiftAux.lean:12`,
  `SSTMealyFF.lean:13`, `SSTMealyRev.lean:13`, `SSTNorm.lean:25`,
  `TwoWayPrecomp.lean:27`) and the inserted `open` line now names every
  dependency package the file's import closure reaches (`tools/port.py`
  fixed: first `--dep` in chain order wins, opens for the whole chain up to
  the furthest package reached);
  cross-package dot notation (`h.congr`, `a.comp b` on Part B's types with
  lemmas declared here) made explicit — `PartC/RatTools.lean:35,193`,
  `ConfGraphReg.lean:170` (`IsRationalRel.congr`), `Statements.lean:73-81`
  (`Continuous.comp`);
  `Set.mem_setOf_eq` no longer rewrites `Language` membership
  (`Language.instMembershipList` ≠ `Set.instMembership`) — `rw [..,
  Set.mem_setOf_eq, ..]` → `change <unfolded membership>` + remaining
  rewrites at `ConfGraphAnnot.lean:182` (the "known ahead" `MultiDFA:59`
  site), `SnakeBase.lean:330,335,522,529`, `MarkStr.lean:217,219`,
  `RunMark.lean:183,329`, `SnakeForall.lean:89`, `SnakeChkMain.lean:164`;
  `rw [if_pos (show u ∈ {v | …} from h)]` → `refine (if_pos h).trans ?_`
  at `SnakeRegTools.lean:48-51`, `SnakeReg.lean:143-145`;
  `TwoWayRat.lean:66` `simpa [filterMap_homOf_padHom] using hb` → `simp
  only [..] at hb; exact hb` (`id` unfolded too early);
  `SnakeChkMain.lean:36` auto-bound `K` → `variable {K : ℕ}`.
  (Warnings: `push_neg` 66 sites, `List.Sublist.cons₂` deprecated in
  `SSTNorm.lean:145`.) No statement changed.
- S3 Bridge (2026-09-07 16:20, subagent): `toSrcTW`/`ofSrcTW` with one
  general `computes_iff_of_step` (a source machine whose step is `M.step`
  under a letter renaming `e`) reused for the configuration-graph alphabet,
  whose concept `VOut` is a distinct inductive (`cletEquiv`, `enc_toSrc`;
  Lemmas C.2.3/C.2.4 through `isRationalFun_map`/`isRegular_map`);
  `TwoWayCode` is the same list type on both sides (`rfl` transports,
  same `Primcodable`); SST `eval` is `rfl`; `IsSnakePath` is a separate
  Prop-structure (`isSnakePath_iff` → `snakeOut_eq` via the source's
  `snakeOutIs_unique`). Bridge imports `Source.PartC.SnakeAlphReg` besides
  `Statements`.
- S5 (`regular-combinators`, Part C §5, 15 modules; `lake build` green
  2026-09-07 15:55, subagent): `CombDepth.lean:141` stale `omega` after a
  `simp at this` that now closes the goal; `CombCombinators.lean:136`
  cross-package dot notation `h.congr` → `IsRationalRel.congr h`;
  `CombAtomConcat.lean:199,202,215,217` and
  `CombAtomSplit.lean:321,324,326,348,351,353,354` — `rw`/`simp` → `erw`
  (`[]`/`x :: l` sit at `List (List A.Elt)` while the lemmas are stated at
  `List (Ty.list A).Elt`; `Ty.Elt` is a non-reducible `def`, so keyed
  matching fails at the epoch). No statement changed.
- S4 (`mso-transductions`, Part C §4, 44 modules; `lake build` green
  2026-09-07 16:40, subagent). (i) The `MSO`/`MSOTransduction`/`Mealy`
  namespaces are split across packages and `open Lax916827Proofs.Transducers.MSO`
  makes `not`/`and`/`or` ambiguous with `Bool`'s, so the needed names are
  `export`ed as aliases into this package's namespace: `MSOSubst.lean:36`
  (the `MSODef` names), `FORel.lean:24` (the `MSOSyntax` names),
  `MSONorm.lean:82` (`MSOTransduction.selected/labRel/ordRel`),
  `FOFlipFlop.lean:15` (`Mealy.trans_cons/trans_append`); the source's
  duplicate `MSO.sat_congr` (declared in both `MSOSubst` and S3's `MSOSyntax`)
  is written `MSO.sat_congr` at `FORel.lean:423`, `FOHintikka.lean:161,175`;
  `FOSeg.lean:15` port-inserted `open Lax132576Proofs …` removed (its closure
  reaches Part A only — `port.py` fixed again, see below). (ii) Cross-package
  dot notation made explicit at ~110 sites (`MSOSubst`, `ITrans`, `MSONorm`,
  `FOFlipFlop`, `FOMealy`, `FOPlug`, `FORename`, `FORev`, `FOBimachRelab`,
  `MSOReg`; `FODefinable.exists_sentence h`, `FODefinable.reverse`).
  (iii) Epoch drift: `MSOSubst.lean:210` `show (∃ S ⊆ _, _)` needs the binder
  type; `MarkDelay.lean:138` `Language` membership `change`;
  `MSONorm.lean:140` `Prod.mk.injEq` at a `def`-level type →
  `Prod.mk.inj`; `FOTransComp.lean:114,124,133` a `rfl` after `rw`,
  `:366,373` `Sum.inr.inj h`; `FOTransDup.lean:490,535` `congrArg Sum.inl` /
  `subst`. No statement changed. Alternative noted by the subagent: an
  `export` placed inside the *other* package's namespace would restore dot
  notation, rejected because it declares into another submission's namespace.
- S5 Bridge (2026-09-07 17:00, subagent): `Ty`, `Ty.Elt`, `Sym8`, `joinSep`,
  `Ty.repr`, `RegTerm`, `eval` are separate copies — `tyEquiv`, `eltEquiv`
  by recursion on the type, `symEquiv`, `repr_toSrc`, `toSrcTerm` with
  `eval_toSrcTerm` (the `pref` case transports the group along
  `(eltEquiv G).symm.group`), `isRegularFun_conj`, then `isRegularUnderRepr_iff`
  / `isRationalUnderRepr_iff` through S3's and S2's bridges. `Ty.Elt`
  keyed matching handled with `show`.
- S6 (`polyregular-functions`, Part D, 72 modules; `lake build` green
  2026-09-07 17:20, subagent): `PartC/RegWin.lean:21` port-inserted `open
  Lax132576Proofs …` removed (closure reaches A and C §1–3 only), `:25`
  `open Lax916827Proofs.Transducers.RegAut` (split namespace);
  `PartD/TwoWayTotal.lean:28` `open Lax916827Proofs.Transducers.TwoWay`
  (split namespace; its roll-up `import RequestProject.PartC` became the
  root modules of S3 and S4, nothing further needed);
  `PartD/ForSem.lean:331,340` `_root_.Transducers.ForTest.…` →
  `_root_.Lax194892Proofs.Transducers.ForTest.…` (prefix rule);
  `PartD/CGSem.lean:228,241,419,533` `Set.mem_setOf_eq` on `Language`
  membership → `erw`; `PartD/Statements.lean:58-63` `Continuous.comp/congr`
  (Part C's, on Part A's `Continuous`; the bare name resolves to mathlib's
  root `Continuous.comp`) fully qualified. No statement changed.
- S6 Bridge (2026-09-07 17:45, subagent): `ForTest`/`ForProg`,
  `PebbleAction`/`Pebble`/`PebbleCfg`, `CGLetter` are the distinct types —
  `toSrc`/`ofSrc` with round trips, `exec_toSrcProg` by induction on the
  program, `reaches_toSrcPeb`/`computes_toSrcPeb`, `cgLetterEquiv` with the
  transport of `CGPath`/`cgOut`/`CGOutIs` along the letter bijection,
  `isForTransducer_map` (letter-to-letter maps are for-transducers via
  `isRationalFun_map` → regular → polyregular → Thm D.1.1); everything else
  `rfl`/`Iff.rfl`.
- S4 Bridge (2026-09-07 18:30, subagent): the concept's MSO syntax is its
  own inductive — `toSrc`/`ofSrc` bijection with `sat_toSrc`/`sat_ofSrc` by
  induction and `isFO_`/`qrank_`/`freeFO_`/`freeSO_` transports; relabellings
  and transductions `toSrcRel`/`toSrcT` with field transports; `tpEquiv :
  TpType A k ≃ …` by induction on `k` for the k-types. All ten theorem names
  the paper's markers expect are used.
- Known ahead (from the port probe of the whole tree, 2026-09-07):
  `Common/PrimrecList.lean` rename `list_drop`/`list_take` to primed names;
  `Common/PrimrecArith.lean:251` `rw` → `simp only` then a `generalize`
  breaks; `PartB/SubseqAlpha.lean:52` set-builder `rwa`; `PartC/MultiDFA.lean:59`
  `Set.mem_setOf_eq` rewrite; `PartB/CodeRat.lean` (`unattach` normal forms,
  ~7 sites); `PartB/PairWeighted.lean:143,146` auto-bound `K`.

- S2 (archive namespace rule): the source's root-level `namespace Primrec`
  in `Common/PrimrecList.lean`, `Common/PrimrecArith.lean` became
  `Lax132576Proofs.Primrec` (every declaration must carry the package prefix),
  with `open Primrec` placed *before* the namespace so that mathlib's `Primrec`
  is still open; `PartB/WCodePrimrec.lean` got a top-level `open Primrec` for
  the same reason (an `open Primrec` inside the package namespace now finds
  only the package's copy). `tools/port.py` now prefixes every root-level
  namespace, not only `Transducers`/`PCP`/`PCPIndex`/`Acceptance`.
  Second round (replay, 2026-09-07 14:00): the two root-level instances
  `Int.primcodable` (`PrimrecArith.lean:87`) and `_root_.Rat.primcodable`
  (`:292`) became `Lax132576Proofs.Int.primcodable` /
  `Lax132576Proofs.Rat.primcodable` (instances resolve by type, nothing
  names them).

## Part D replay limit (2026-09-07, 19:00–20:30)

The archive rejected the first content submission of `polyregular-functions`
(commit 9d091e1) with "proofs kernel replay exceeded its time limit" (the cap
is 20 min of `leanchecker <root>` with `LEAN_NUM_THREADS=2` on a 16 GB,
4-CPU swapless runner; `leanchecker` replays every module with the root as
prefix, one task per module, and holds one ~5.6 GB mathlib environment per
concurrent task). Local measurements, same invocation, 2 threads, unloaded:

| package | modules | root replay | peak RSS | archive |
|---|---|---|---|---|
| `Lax916827Proofs` (C §1–3) | 138 | 8m17s | 14.7 GB | passed |
| `Lax194892Proofs` (D) | 74 | 4m31s | 11.9 GB | rejected on time |

Per module Part D costs ~15 s each (environment import, not kernel work);
`Results`/`Bridge` 17 s/16 s unloaded; the elaboration profiler at 500 ms
finds nothing in `Results`. Our own oleans are ≤ 80 MB per package against
mathlib's 5.7 GB. Nothing local explains the rejection; resubmitted unchanged
(`--force`). If it fails again identically: systematic — reduce the number of
modules (merging Source files is the only lever on import overhead) or ask the
archive maintainers; Jan's call.

## Decisions log

- 2026-09-07 Jan: seven part submissions + umbrella paper; split only the
  headline iffs; exercises deferred; concepts only for what is formalised;
  authors Bojańczyk + Aristotle; Apache 2.0 for the book text; epoch
  environment; commit/push/submit from this repo authorised.
