import Lax3Proofs.SolveAugRoundIn
import Lax3Proofs.SolveAugSymMerge

set_option autoImplicit false

/-!
# F6c12-5d — the augmentation, composed across the three repaired seams

`SolveCoverAllJoin` §4b–§4d proved that the three landed discharges of
`AugBaseIn`, `AugRoundIn` and `AugSymIn` **cannot** be composed: three
parameters `covAugAdjSelIn_of_base_rounds_sym` shares between them are
over-determined.  Each defect has now been repaired at its source, and
this file is the composition the repairs make possible.

## What the three repairs were

1. **`augBasePeelInS_bucketPeelBuild`** (`SolveAugBaseFrame` §2b, stated
   *beside* the landed §2).  The landed peel *pins* `Sbd` to its own
   three length clauses; `augBaseIn_of_adj_peel_orient` takes one `Sbd`
   for all three base passes and the orientation asks that same `Sbd`
   to bound `io`/`it`/`cn` against the carrier cell, which the triple
   never mentions.  The variant frees `Sbd`, at no new program and no
   new proof about `bucketPeelCom`: the landed statement's `Smp` is
   already a parameter carried across the pass, so `Smp ∧ Sbd` carries
   an arbitrary `Sbd` too.

2. **`augBaseOrientIn_orCom`'s `hSrd`/`hSmp`/`hSsw`** (`SolveAugOrient`
   §10, in place).  They now receive
   `(∀ b, (σ'.arrs b).length = (σ.arrs b).length)` beside the write
   frame — a clause the proof already had from `specArrsLength` and used
   two lines later, and which its sibling `augBasePeelIn_bucketPeelBuild`
   already passed to *its* transports.  Without it nothing constraining
   `io j` or `it j` by a length is reachable, and `ardSrd`'s region list
   is headed by exactly that pair.  Handing a caller more information
   weakens no conclusion, and the theorem has no other consumer in the
   package.

3. **`symComW_spec`** (`SolveAugSymMerge` §9, stated *beside* the landed
   `symCom_spec`, which is re-derived from it unchanged).  `GraphCsr`
   pins both array lengths by equality, so an exact-length *output*
   demand is a demand on whoever allocated the arrays — and
   `2·arcCount (selChain sel A.G R)` grows with every round while an
   array's length cannot.  `coverAllSym_srd_forces_constant` turned that
   into a proof that every round emits nothing.  The merge now leaves a
   `GraphCsr` of the **truncation** of `(so, st)`, asking only
   `2·arcCount D ≤ (σ.arrs st).length`, exactly as `augStInNW` already
   does for the orientation region.

## Why windowing, and not "size the merge at `ardCap`" alone

The packet offered a choice.  It is not one: sizing at `ardCap` *and*
windowing are the same repair seen from the two ends, and neither half
works alone.

* An exact-length output of any figure is impossible, because
  `graphCsr_ns_eq_slotCount` forces the slot count of a `GraphCsr` of
  `D.toGraph` to be `2·arcCount D` — there is no freedom to declare it
  `ardCap N` instead.  So the *output* must be windowed.
* A windowed output whose caller obligation is still
  `2·arcCount D ≤ (σ.arrs stO).length` is satisfiable state by state,
  but not by the *round*: `Srd` is one predicate for all `R` rounds,
  established by the base pass and re-proved by every round, and no
  round can prove a bound on the final orientation's arc count.  So the
  *allocation the round maintains* must be in the carrier's currency,
  which is `ardCap`.

§4 re-runs `coverAllSym_srd_forces_constant`'s own test against the
repaired pass and it no longer fires: `augSeamSrd` bounds `stO` by
`ardCap (σ.vars nN)` and `nN` is round-invariant, so nothing links
`σ.vars (nA j)` at one round to `σ'.vars (nA j)` at the next, and
`augSeamSrd_not_forces_constant` exhibits two states of one level whose
arc-count cells differ while both satisfy the descriptor.

## The cost

Nothing new is measured.  The symmetrization is `symK` plus the landed
build's `81·N + 58·ns + 24` at `ns = 2·arcCount`, i.e. `augSymBudget` at
`(171, 196, 84)` — the very triple `covAllJoin_sym_coeffs` already
records — and the base's three are `(545, 554, 113)`.  Every figure is
`A.N` or `arcCount` at the chain's own orientations, and
`covAllJoin_Kord_le` bounds the total by `545·selChainCharge + O(R)`.
The one *space* figure that is not is `ardCap N = 2N³ + N² + N + 1`,
which is the round's own landed allocation (`SolveAugRoundIn` §5) and is
space, not time.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation baseOr fratGraph)
open Lax3Proofs.CoverRoutine (MinDegSel selPerm selChain selRank greedyStep)

/-! ## §1 The symmetrization's sizing, windowed -/

/-- **What the merge-and-build pass asks of the round invariant.**  Every
clause is `≥`, and every figure is the arena's own carrier cell or the
orientation region's arc-count cell, so the predicate names neither the
arena nor the orientation.  This is `symSrd` (`SolveAugSymMerge` §11)
with its one exact-length clause — `symCsrSizes`, the trap — replaced by
the two windowed bounds. -/
def augSeamSymSizes (soO stO qoY qtY dgY aoO ajO dgO mtO : ℕ → String)
    (j : ℕ) (σ : Env) : Prop :=
  ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (soO j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (stO j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (qoY j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (qtY j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (dgY j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (aoO j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (ajO j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (dgO j)).length ∧
    ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs (mtO j)).length

/-! ## §2 `AugSymIn`, discharged

The pass is `symCom … ; bldAdjCom …`.  The second half is the landed
build and applies through `bldAdj_spec` — the *windowed* reading, the
one `augBasePeelIn_bucketPeelBuild`'s own rebuild uses — because
`srcCsr_of_graphCsr` turns the merge's truncated `GraphCsr` into the
`SrcCsr` of the real state at `≥` allocations. -/

open Classical in
/-- **`AugSymIn`, discharged** at the windowed orientation region, the
program `symCom … ; bldAdjCom …` and the budget `171·A.N +
196·arcCount (selChain sel A.G R) + 84`.

`AugSymCsrIn` does not appear: its postcondition is a bare `GraphCsr`,
which is the exact-length demand `SolveCoverAllJoin` §4d shows no round
invariant can carry, so the two halves are composed here directly at the
windowed reading instead of through that contract. -/
theorem augSeamSymIn_symBuild (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (io it nA : ℕ → String)
    (nNy nSy soO stO qoY qtY dgY raY odY : ℕ → String)
    (aoO ajO dgO mtO : ℕ → String)
    (Srd Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnm : ∀ j, SyNames (io j) (it j) (qoY j) (qtY j) (dgY j) (soO j) (stO j))
    (hbn : ∀ j, BldNames (soO j) (stO j) (raY j) (aoO j) (ajO j) (dgO j)
      (mtO j) (odY j))
    (hbc : ∀ j, BldCells (nNy j) (nSy j))
    (hcy : ∀ j, nNy j ∉ syScalars ∧ nSy j ∉ syScalars ∧ nSy j ≠ nNy j ∧
      nNy j ≠ (arenaNames j).nN ∧ nNy j ≠ (arenaNames j).nS ∧
      nSy j ≠ (arenaNames j).nN ∧ nSy j ≠ (arenaNames j).nS)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ qoY j ∧ b ≠ qtY j ∧ b ≠ dgY j ∧ b ≠ soO j ∧ b ≠ stO j ∧
        b ≠ aoO j ∧ b ≠ ajO j ∧ b ≠ dgO j ∧ b ≠ mtO j)
    (hSrd : ∀ (j : ℕ) (σ : Env), Srd j σ →
      augSeamSymSizes soO stO qoY qtY dgY aoO ajO dgO mtO j σ)
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j →
        b ≠ stO j → b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ syScalars → y ∉ tpScalars → y ∉ bldScalars →
        y ≠ nNy j → y ≠ nSy j → σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j →
        b ≠ stO j → b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ syScalars → y ∉ tpScalars → y ∉ bldScalars →
        y ≠ nNy j → y ≠ nSy j → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugSymIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co aoO ajO dgO mtO
      (fun j A => augStInNW io it nA j A) Srd Smp Ssw
      (fun j => .seq
        (symCom (arenaNames j).nN (io j) (it j) (qoY j) (qtY j) (dgY j)
          (soO j) (stO j) (nNy j) (nSy j))
        (bldAdjCom (nNy j) (nSy j) (soO j) (stO j) (aoO j) (ajO j) (dgO j)
          (mtO j)))
      171 196 84 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, ⟨hTrE, -, hnAv⟩, hSrdσ, hcaL, hcoL, hSm, hSw⟩ := hσ
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩ := hcy j
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hSrd j σ hSrdσ
  -- the two figures, and that they are words
  have henc : EncodesGraph x n G := hx.1
  have hnN : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB (three_le_length henc) hq
  have hlenx := henc.length_eq
  have hNB : A.N < mcB q x := by omega
  have hsq : n * n < mcB q x := sq_lt_mcB henc hq
  have hNsq : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
  have hBsq : A.N * A.N < mcB q x := by omega
  have h2a : 2 * arcCount (selChain (sel A.N) A.G R) ≤ A.N * A.N :=
    two_mul_arcCount_le_sq_orient _
  have hnsB : 2 * arcCount (selChain (sel A.N) A.G R) < mcB q x := by omega
  obtain ⟨off, tgt, hTr⟩ := hTrE
  -- the nine allocations, read out of the carrier's own currency
  rw [hnN] at c1 c2 c3 c4 c5 c6 c7 c8 c9
  obtain ⟨p1, p2, -, p4, -, -, -⟩ := ardCap_bounds (selChain (sel A.N) A.G R)
  have p0 : A.N ≤ ardCap A.N := le_trans (Nat.le_succ A.N) p1
  have p3 : 2 * arcCount (selChain (sel A.N) A.G R) ≤ ardCap A.N :=
    le_trans h2a p2
  have hsoL : A.N + 1 ≤ (σ.arrs (soO j)).length := le_trans p1 c1
  have hstL : 2 * arcCount (selChain (sel A.N) A.G R)
      ≤ (σ.arrs (stO j)).length := le_trans p3 c2
  have hqoL : A.N + 1 ≤ (σ.arrs (qoY j)).length := le_trans p1 c3
  have hqtL : arcCount (selChain (sel A.N) A.G R)
      ≤ (σ.arrs (qtY j)).length := le_trans p4 c4
  have hdgL : A.N ≤ (σ.arrs (dgY j)).length := le_trans p0 c5
  have haoL : A.N + 1 ≤ (σ.arrs (aoO j)).length := le_trans p1 c6
  have hajL : 2 * arcCount (selChain (sel A.N) A.G R)
      ≤ (σ.arrs (ajO j)).length := le_trans p3 c7
  have hdgOL : A.N ≤ (σ.arrs (dgO j)).length := le_trans p0 c8
  have hmtL : 2 * arcCount (selChain (sel A.N) A.G R)
      ≤ (σ.arrs (mtO j)).length := le_trans p3 c9
  -- 1. the merge, at the windowed output
  obtain ⟨σ₁, hrun1, ⟨⟨hcsrW, hnNy1, hnSy1⟩, hfv1, hfa1, -, -⟩, hlen1⟩ :=
    (specArrsLength (symComW_spec (B := mcB q x) (nN := (arenaNames j).nN)
      (io := io j) (it := it j) (qo := qoY j) (qt := qtY j) (dg := dgY j)
      (so := soO j) (st := stO j) (nNy := nNy j) (nSy := nSy j)
      (D := selChain (sel A.N) A.G R) (off := off) (tgt := tgt)
      (hnm j) (arenaNames_nN_notMem_syScalars j) (arenaNames_nN_notMem_tpScalars j)
      hy1 hy2 hy3 hBsq).frame).run
      ⟨hnN, hTr, hqoL, hqtL, hdgL, hsoL, hstL⟩
  have hfa1' : ∀ b : String, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j →
      b ≠ stO j → σ₁.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 h5 => hfa1 b (not_mem_warrs_symCom h1 h2 h3 h4 h5)
  have hfv1' : ∀ y : String, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j →
      y ≠ nSy j → σ₁.vars y = σ.vars y :=
    fun y h1 h2 h3 h4 => hfv1 y (not_mem_wvars_symCom h1 h2 h3 h4)
  -- the truncated `GraphCsr` is the real state's `SrcCsr`
  have hso1 : A.N + 1 ≤ (σ₁.arrs (soO j)).length := by
    rw [hlen1 (soO j)]; exact hsoL
  have hst1 : 2 * arcCount (selChain (sel A.N) A.G R) ≤ (σ₁.arrs (stO j)).length := by
    rw [hlen1 (stO j)]; exact hstL
  obtain ⟨off2, tgt2, hsrc⟩ :=
    srcCsr_of_graphCsr hcsrW hso1 hst1
      (fun i hi => by
        rw [arrs_winA_some (inWs_o (soO j) (stO j) A.N
            (2 * arcCount (selChain (sel A.N) A.G R))),
          List.getElem?_take_of_lt (by omega)])
      (fun p hp => by
        rw [arrs_winA_some (inWs_t (Ne.symm (hnm j).so_st) A.N
            (2 * arcCount (selChain (sel A.N) A.G R))),
          List.getElem?_take_of_lt hp])
  -- 2. the landed build, framed
  obtain ⟨σ₂, hrun2, ⟨⟨-, hdel2⟩, hfv2, hfa2, -, -⟩, hlen2⟩ :=
    (specArrsLength (bldAdj_spec (G := (selChain (sel A.N) A.G R).toGraph)
      (off := off2) (tgt := tgt2) (B := mcB q x) (hbn j) (hbc j) hNB hnsB).frame).run
      ⟨hsrc, hnNy1, hnSy1, by rw [hlen1 (aoO j)]; exact haoL,
        by rw [hlen1 (ajO j)]; exact hajL, by rw [hlen1 (dgO j)]; exact hdgOL,
        by rw [hlen1 (mtO j)]; exact hmtL⟩
  have hfa2' : ∀ b : String, b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
      σ₂.arrs b = σ₁.arrs b :=
    fun b h1 h2 h3 h4 => hfa2 b (not_mem_warrs_bldAdjCom h1 h2 h3 h4)
  have hfv2' : ∀ y : String, y ∉ bldScalars → σ₂.vars y = σ₁.vars y := by
    intro y hy
    simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hy
    exact hfv2 y (not_mem_wvars_bldAdjCom h0 h1 h2 h3 h4 h5)
  -- the whole pass's frame
  have hfaT : ∀ b : String, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j →
      b ≠ stO j → b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
      σ₂.arrs b = σ.arrs b := by
    intro b h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hfa2' b h6 h7 h8 h9, hfa1' b h1 h2 h3 h4 h5]
  have hlenT : ∀ b : String, (σ₂.arrs b).length = (σ.arrs b).length :=
    fun b => by rw [hlen2 b, hlen1 b]
  have hfvT : ∀ y : String, y ∉ syScalars → y ∉ tpScalars → y ∉ bldScalars →
      y ≠ nNy j → y ≠ nSy j → σ₂.vars y = σ.vars y := by
    intro y h1 h2 h3 h4 h5
    rw [hfv2' y h3, hfv1' y h1 h2 h4 h5]
  have hclj := bldCells_arenaNames j
  have hvN : σ₂.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
    hfvT _ (arenaNames_nN_notMem_syScalars j) (arenaNames_nN_notMem_tpScalars j)
      hclj.nN_notMem (Ne.symm hy4) (Ne.symm hy6)
  have hvS : σ₂.vars (arenaNames j).nS = σ.vars (arenaNames j).nS :=
    hfvT _ (arenaNames_nS_notMem_syScalars j) (arenaNames_nS_notMem_tpScalars j)
      hclj.nS_notMem (Ne.symm hy5) (Ne.symm hy7)
  obtain ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9⟩ :=
    harn j (arenaNames j).off (Or.inl rfl)
  obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9⟩ :=
    harn j (arenaNames j).tgt (Or.inr (Or.inl rfl))
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩ :=
    harn j (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9⟩ :=
    harn j (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨hh1, hh2, hh3, hh4, hh5, hh6, hh7, hh8, hh9⟩ :=
    harn j (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨σ₂, (hrun1.seq hrun2).mono ?_, ?_, hdel2, ?_, ?_, ?_, ?_⟩
  · simp only [augSymBudget, symK]; omega
  · exact arenaStW_of_eq hArena hvN hvS
      (hfaT _ ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9)
      (hfaT _ ht1 ht2 ht3 ht4 ht5 ht6 ht7 ht8 ht9)
      (hfaT _ hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9)
      (hfaT _ hu1 hu2 hu3 hu4 hu5 hu6 hu7 hu8 hu9)
      (hfaT _ hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9)
  · rw [hlenT (ca j)]; exact hcaL
  · rw [hlenT (co j)]; exact hcoL
  · exact hSmp j σ σ₂ hSm hfaT hlenT hfvT
  · exact hSsw j σ σ₂ hSw hfaT hlenT hfvT

/-! ## §3 The augmentation's own names

The round's twenty-seven are `SolveAugRoundIn` §7's fixed four-character
strings on the base letter `'r'`; the four output regions are the ones
the cover stage reads next (`SolveCoverAllJoin` §1's `"oc.*"`).  What is
added here is the base pass's eight working regions and the
symmetrization's five plus two cells, all level-tagged four-character
bases on the fresh letter `'y'`, so that every disequality among them is
`lv_ne_of_base_ne` and every disequality against the round's is
`lv_ne_len4`. -/

/-- Two distinct four-character bases stay distinct at every level. -/
theorem augSeamNe4 {s t : String} (hs : s.length = 4) (ht : t.length = 4)
    (hst : s ≠ t) (j : ℕ) : lv s j ≠ lv t j :=
  lv_ne_of_base_ne (by rw [hs, ht]) hst j j

/-- Two level-tagged four-character bases with different first letters
stay distinct — the comparison that survives when neither base is
concrete. -/
theorem augSeamNeH {s t : String} {ch : Char} (hs : s.length = 4)
    (ht : t.length = 4) (hsh : s.toList.head? = some ch)
    (hth : t.toList.head? ≠ some ch) (j k : ℕ) : lv s j ≠ lv t k :=
  lv_ne_of_base_ne (by rw [hs, ht]) (by rintro rfl; exact hth hsh) j k

/-- Closes a disequality between two of the augmentation's names: both
level-tagged four-character bases, one level-tagged and one of the
round's fixed names, or two fixed names.  The `refine` unifies the
conclusion with the goal *first*, so the three side conditions are
closed propositions by the time `decide` sees them. -/
macro "seam_ne" : tactic =>
  `(tactic| first
      | exact augSeamNe4 (by decide) (by decide) (by decide) _
      | exact Ne.symm (lv_ne_len4 (by decide) (by decide) (by decide) _)
      | exact lv_ne_len4 (by decide) (by decide) (by decide) _
      | decide)

/-- The base pass's deletable region: offsets. -/
abbrev augSeamAo : ℕ → String := lv "ya.o"
/-- … slots. -/
abbrev augSeamAj : ℕ → String := lv "ya.j"
/-- … live degrees. -/
abbrev augSeamDg : ℕ → String := lv "ya.d"
/-- … mate pointers. -/
abbrev augSeamMt : ℕ → String := lv "ya.m"
/-- The base peel's rank array. -/
abbrev augSeamRa : ℕ → String := lv "yr.a"
/-- The base peel's bucket tops. -/
abbrev augSeamTp : ℕ → String := lv "yt.p"
/-- The base peel's bucket cells. -/
abbrev augSeamSk : ℕ → String := lv "yk.c"
/-- The base orientation's counters. -/
abbrev augSeamCn : ℕ → String := lv "yc.n"
/-- The rank name the region rebuild never reads. -/
abbrev augSeamRaY : ℕ → String := lv "yr.y"
/-- The order name the region rebuild never writes. -/
abbrev augSeamOdY : ℕ → String := lv "yo.d"
/-- The transpose's offsets. -/
abbrev augSeamQo : ℕ → String := lv "yq.o"
/-- The transpose's targets. -/
abbrev augSeamQt : ℕ → String := lv "yq.t"
/-- The transpose's degree counters. -/
abbrev augSeamDgY : ℕ → String := lv "yg.d"
/-- The merged CSR's offsets. -/
abbrev augSeamSo : ℕ → String := lv "ys.o"
/-- The merged CSR's targets. -/
abbrev augSeamSt : ℕ → String := lv "ys.t"
/-- The merged CSR's carrier cell. -/
abbrev augSeamNny : ℕ → String := lv "yn.n"
/-- The merged CSR's slot cell. -/
abbrev augSeamNsy : ℕ → String := lv "yn.s"

/-! ## §4 The augmentation's write set and scratch pool

Every pass of the augmentation writes inside `augSeamWrites` and assigns
inside `augSeamCells`.  Stating the two descriptors' transports once
against *these two lists* — rather than five times against each pass's
own exceptions — is what makes the composition's hypothesis bundle two
clauses instead of ten: each pass's frame is **stronger** (it has fewer
exceptions), so it implies the list-shaped one. -/

/-- The nine regions the symmetrization needs, as four-character bases:
the transpose's three, the merged CSR's two, and the four the build
writes (which are the cover stage's own output regions). -/
def augSeamRegBases : List String :=
  ["yq.o", "yq.t", "yg.d", "ys.o", "ys.t", "oc.p", "oc.j", "oc.d", "oc.m"]

theorem augSeamRegBases_len : ∀ t ∈ augSeamRegBases, t.length = 4 := by decide

/-- … at one level. -/
def augSeamRegs (j : ℕ) : List String := augSeamRegBases.map (fun t => lv t j)

/-- The twenty-three arrays the round writes, as literals. -/
def augSeamArdNames : List String :=
  ["rf.m", "ri.o", "ri.t", "rf.o", "rf.t", "rf.d", "rp.o", "rp.j", "rp.d",
    "rp.m", "rp.s", "rp.p", "rp.k", "rt.o", "rt.t", "rt.m", "ro.o", "ro.t",
    "rq.o", "rq.t", "rz.a", "rz.s", "rz.d"]

theorem augSeamArdNames_len : ∀ b ∈ augSeamArdNames, b.length = 4 := by decide

theorem augSeamRegBases_ne_ard :
    ∀ t ∈ augSeamRegBases, ∀ b ∈ augSeamArdNames, t ≠ b := by decide

/-- The base pass's eight working regions, as bases. -/
def augSeamBaseBases : List String :=
  ["ya.o", "ya.j", "ya.d", "ya.m", "yr.a", "yt.p", "yk.c", "yc.n"]

theorem augSeamBaseBases_len : ∀ t ∈ augSeamBaseBases, t.length = 4 := by decide

/-- … at one level. -/
def augSeamBaseNames (j : ℕ) : List String :=
  augSeamBaseBases.map (fun t => lv t j)

/-- The forty arrays the whole augmentation writes: the round's
twenty-three, the base's eight, the symmetrization's five, and the four
output regions. -/
def augSeamWrites (j : ℕ) : List String :=
  augSeamArdNames ++ augSeamBaseNames j ++ augSeamRegs j

theorem augSeamWrites_ard {j : ℕ} {b : String} (hb : b ∈ augSeamArdNames) :
    b ∈ augSeamWrites j :=
  List.mem_append_left _ (List.mem_append_left _ hb)

theorem augSeamWrites_base {j : ℕ} {t : String} (ht : t ∈ augSeamBaseBases) :
    lv t j ∈ augSeamWrites j :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ht))

theorem augSeamWrites_reg {j : ℕ} {t : String} (ht : t ∈ augSeamRegBases) :
    lv t j ∈ augSeamWrites j :=
  List.mem_append_right _ (List.mem_map_of_mem ht)

/-- **A name outside the three base lists is outside the write set.**
Every clause is `decide` at a concrete base, which is how the sweep's
and the arena's names are cleared in one line each. -/
theorem augSeamNotWrite {s : String} (hlen : s.length = 4)
    (h1 : ∀ b ∈ augSeamArdNames, s ≠ b)
    (h2 : ∀ t ∈ augSeamBaseBases, s ≠ t)
    (h3 : ∀ t ∈ augSeamRegBases, s ≠ t) (j : ℕ) : lv s j ∉ augSeamWrites j := by
  simp only [augSeamWrites, List.mem_append, not_or]
  refine ⟨⟨fun hm => ?_, fun hm => ?_⟩, fun hm => ?_⟩
  · exact lv_ne_len4 hlen (augSeamArdNames_len _ hm) (h1 _ hm) j rfl
  · obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    exact augSeamNe4 hlen (augSeamBaseBases_len t ht) (h2 t ht) j he.symm
  · obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
    exact augSeamNe4 hlen (augSeamRegBases_len t ht) (h3 t ht) j he.symm

/-- **The symmetrization's nine regions are none of the round's
twenty-three**, which is what carries their allocation across a round. -/
theorem augSeamRegs_notArd {j : ℕ} {b : String} (hb : b ∈ augSeamRegs j) :
    b ∉ augSeamArdNames := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  intro hm
  exact lv_ne_len4 (augSeamRegBases_len t ht) (augSeamArdNames_len _ hm)
    (augSeamRegBases_ne_ard t ht _ hm) j rfl

/-- The scalars the whole augmentation assigns: the round's seven pools
and four cells, the merge's and transpose's, the base peel's eighteen,
the orientation's eight, and the merge's two figure cells. -/
def augSeamCells (j : ℕ) : List String :=
  ardScalars ++ syScalars ++ tpScalars ++ basePeelScalars ++ orScalars ++
    ["rc.f", "rc.t", "rc.o", "rc.a", augSeamNny j, augSeamNsy j]

/-- **The arena's two figure cells are outside the augmentation's
scratch pool.**  Every pool but the merge's own starts with a letter
other than `'s'`; the merge's is named, and so are the round's four
`"rc.*"` cells and the merge's two level-tagged `'y'` ones. -/
theorem augSeamNotCell {s : String} (hlen : s.length = 4)
    (hs : s.toList.head? = some 's') (j : ℕ) (hsy : lv s j ∉ syScalars) :
    lv s j ∉ augSeamCells j := by
  simp only [augSeamCells, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  refine ⟨⟨⟨⟨⟨ard_lv_notMem hs ard_ardScalars_head j, hsy⟩,
    ard_lv_notMem hs (by decide) j⟩, ard_lv_notMem hs (by decide) j⟩,
    ard_lv_notMem hs (by decide) j⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | exact ard_lv_ne_head hs (by decide) j
      | exact augSeamNeH hlen (by decide) hs (by decide) j j

theorem augSeam_nN_notMem_cells (j : ℕ) : (arenaNames j).nN ∉ augSeamCells j :=
  augSeamNotCell (s := "sv.n") (by decide) rfl j
    (arenaNames_nN_notMem_syScalars j)

theorem augSeam_nS_notMem_cells (j : ℕ) : (arenaNames j).nS ∉ augSeamCells j :=
  augSeamNotCell (s := "sv.m") (by decide) rfl j
    (arenaNames_nS_notMem_syScalars j)

/-! ## §5 The three descriptors, and the one clause that is not a length

`Srd` is the round invariant, `Sbd` the base's, `Sag` the
augmentation's.  All three are the *same* predicate with successively
more allocations, and every clause of every one of them is a length
except the two mark windows' contents.  That is what makes them
transportable: IMP+ changes no length, so a pass that leaves the two
mark windows alone leaves all three standing. -/

/-- **Everything the augmentation allocates at `ardCap`**: the round's
own twenty-two and the symmetrization's nine.  The list is what
`ardSrd`'s `regs` parameter is instantiated at, so the descriptor the
rounds maintain and the descriptor the merge consumes are literally the
same predicate. -/
def augSeamRegsAll (j : ℕ) : List String :=
  augSeamRegs j ++
    ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo ardAj ardDgP ardMt ardSg
      ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo ardQt ardAd ardSd
      ardDgE j

theorem augSeamArdRegions_head (j : ℕ) :
    ∀ b ∈ ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo ardAj ardDgP ardMt
      ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo ardQt ardAd ardSd
      ardDgE j, b.toList.head? = some 'r' := by
  have h : ∀ b ∈ ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo ardAj ardDgP
      ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo ardQt ardAd
      ardSd ardDgE 0, b.toList.head? = some 'r' := by decide
  exact h

/-- The first letter survives the level tag. -/
theorem augSeamLvHead {s : String} {ch : Char} (hs : s.toList.head? = some ch)
    (j : ℕ) : (lv s j).toList.head? = some ch := by
  rw [lv_toList]
  cases hh : s.toList with
  | nil => rw [hh] at hs; simp at hs
  | cons a l =>
      rw [hh] at hs
      simp only [List.cons_append, List.head?_cons]
      simpa using hs

/-- A member of the allocation list is either one of the round's fixed
`'r'` names or one of the nine level-tagged bases. -/
theorem augSeamRegsAll_cases {j : ℕ} {b : String} (hb : b ∈ augSeamRegsAll j) :
    b.toList.head? = some 'r' ∨ ∃ t ∈ augSeamRegBases, b = lv t j := by
  rcases List.mem_append.mp hb with h | h
  · right
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    exact ⟨t, ht, rfl⟩
  · exact Or.inl (augSeamArdRegions_head j b h)

/-- **No allocation of the list is one of the base pass's own eight
regions** — they are level-tagged `'y'` bases outside the nine. -/
theorem augSeamRegsAll_ne {j : ℕ} {b u : String} (hb : b ∈ augSeamRegsAll j)
    (hu4 : u.length = 4) (huh : u.toList.head? = some 'y')
    (hune : ∀ t ∈ augSeamRegBases, u ≠ t) : b ≠ lv u j := by
  rcases augSeamRegsAll_cases hb with hr | ⟨t, ht, rfl⟩
  · intro h
    rw [h, augSeamLvHead huh j] at hr
    exact absurd hr (by decide)
  · exact augSeamNe4 (augSeamRegBases_len t ht) hu4 (fun h => hune t ht h.symm) j

/-- **The round invariant**, at the augmentation's whole allocation
list.  `ardSrd`'s `regs` is a parameter (`SolveAugRoundIn` §5), so
widening it costs no new statement about the round: the twenty-two the
round itself needs are still there. -/
def augSeamSrd : ℕ → Env → Prop :=
  ardSrd ardMkF ardMkT augSeamRegsAll

/-- **The base pass's descriptor**: the round invariant, plus the two
allocations the orientation pass reads against the arena's *slot* cell
(which `ardCap` cannot see), plus the bucket peel's three against the
root carrier. -/
def augSeamSbd (n : ℕ) (j : ℕ) (σ : Env) : Prop :=
  augSeamSrd j σ ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (ardIt j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (augSeamCn j)).length ∧
    n ≤ (σ.arrs (augSeamRa j)).length ∧ n ≤ (σ.arrs (augSeamTp j)).length ∧
    n * n + n ≤ (σ.arrs (augSeamSk j)).length

/-- **The augmentation's descriptor** — `CovAugAdjSelIn`'s own `Sag`:
the base's, plus the four allocations the region build writes into. -/
def augSeamSag (n : ℕ) (j : ℕ) (σ : Env) : Prop :=
  augSeamSbd n j σ ∧
    σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (augSeamAo j)).length ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (augSeamAj j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (augSeamDg j)).length ∧
    σ.vars (arenaNames j).nS ≤ (σ.arrs (augSeamMt j)).length

/-- The arrays `augSeamSbd` speaks about. -/
def augSeamSbdArrs (j : ℕ) : List String :=
  augSeamRegsAll j ++
    ["rf.m", "rt.m", augSeamCn j, augSeamRa j, augSeamTp j, augSeamSk j]

/-- **The round invariant rides on lengths alone**, plus the two mark
windows' contents. -/
theorem augSeamSrd_of_len {j : ℕ} {σ σ' : Env} (h : augSeamSrd j σ)
    (hlen : ∀ b ∈ augSeamRegsAll j, (σ'.arrs b).length = (σ.arrs b).length)
    (hmkF : σ'.arrs "rf.m" = σ.arrs "rf.m")
    (hmkT : σ'.arrs "rt.m" = σ.arrs "rt.m")
    (hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN) :
    augSeamSrd j σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun b hb => ?_, ?_, ?_, ?_⟩
  · rw [hvN, hlen b hb]; exact h1 b hb
  · rw [hvN, hmkF]; exact h2
  · rw [hmkF]; exact h3
  · rw [hvN, hmkT]; exact h4

/-- … and so does the base's. -/
theorem augSeamSbd_of_len {n j : ℕ} {σ σ' : Env} (h : augSeamSbd n j σ)
    (hlen : ∀ b ∈ augSeamSbdArrs j, (σ'.arrs b).length = (σ.arrs b).length)
    (hmkF : σ'.arrs "rf.m" = σ.arrs "rf.m")
    (hmkT : σ'.arrs "rt.m" = σ.arrs "rt.m")
    (hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN)
    (hvS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS) :
    augSeamSbd n j σ' := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hmem : ∀ b ∈ augSeamRegsAll j, b ∈ augSeamSbdArrs j :=
    fun b hb => List.mem_append_left _ hb
  have hit : ("ri.t" : String) ∈ augSeamRegsAll j := by
    refine List.mem_append_right _ ?_
    simp [ardRegions]
  refine ⟨augSeamSrd_of_len h0 (fun b hb => hlen b (hmem b hb)) hmkF hmkT hvN,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvS, hlen _ (hmem _ hit)]; exact h1
  · rw [hvN, hlen _ (by simp [augSeamSbdArrs])]; exact h2
  · rw [hlen _ (by simp [augSeamSbdArrs])]; exact h3
  · rw [hlen _ (by simp [augSeamSbdArrs])]; exact h4
  · rw [hlen _ (by simp [augSeamSbdArrs])]; exact h5

/-- The base pass's own deletable region is none of the arrays the three
descriptors speak about, so the region build carries all three. -/
theorem augSeamSbdArrs_ne_region {j : ℕ} {b : String}
    (hb : b ∈ augSeamSbdArrs j) :
    b ≠ augSeamAo j ∧ b ≠ augSeamAj j ∧ b ≠ augSeamDg j ∧ b ≠ augSeamMt j := by
  rcases List.mem_append.mp hb with h | h
  · exact ⟨augSeamRegsAll_ne h (by decide) (by decide) (by decide),
      augSeamRegsAll_ne h (by decide) (by decide) (by decide),
      augSeamRegsAll_ne h (by decide) (by decide) (by decide),
      augSeamRegsAll_ne h (by decide) (by decide) (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> seam_ne

/-! ## §6 `AugBaseIn`, discharged

The three base passes at the concrete family, composed by
`augBaseIn_of_adj_peel_orient`.  The two descriptors `Smp` and `Ssw`
stay parameters, and their transports are asked for **once**, against
the augmentation's whole write set and scratch pool (§4): every
individual pass's frame is stronger, so each derives its own. -/

open Classical in
/-- **`AugBaseIn`, discharged** at the concrete name family, the
descriptors `augSeamSag`/`augSeamSrd`, and the coefficients
`(545, 554, 113)` — `covAllJoin_base_coeffs`'s own sum of
`(81, 116, 24)`, `(394, 352, 64)` and `(70, 86, 25)`. -/
theorem augSeamBaseIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hSmpW : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Smp j σ')
    (hSswW : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugBaseIn C hC φ (fun m => bucketSel m) G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInNW ardIo ardIt ardNA j A)
      (augSeamSag n) augSeamSrd Smp Ssw
      (fun j => .seq
        (.seq
          (bldAdjCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
            (arenaNames j).tgt (augSeamAo j) (augSeamAj j) (augSeamDg j)
            (augSeamMt j))
          (.seq
            (bucketPeelCom (augSeamAo j) (augSeamAj j) (augSeamDg j)
              (augSeamMt j) (augSeamRa j) (augSeamTp j) (augSeamSk j)
              (arenaNames j).nN)
            (bldAdjCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
              (arenaNames j).tgt (augSeamAo j) (augSeamAj j) (augSeamDg j)
              (augSeamMt j))))
        (orCom (arenaNames j).nN (ardNA j) (augSeamAo j) (augSeamAj j)
          (augSeamRa j) (ardIo j) (ardIt j) (augSeamCn j)))
      545 554 113 := by
  -- the write set, used to weaken each pass's own frame
  have hW : ∀ (j : ℕ) (b x : String), b ∉ augSeamWrites j →
      x ∈ augSeamWrites j → b ≠ x := fun _ b x hb hx h => hb (by rw [h]; exact hx)
  have hmAo : ∀ j, augSeamAo j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "ya.o") (by decide)
  have hmAj : ∀ j, augSeamAj j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "ya.j") (by decide)
  have hmDg : ∀ j, augSeamDg j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "ya.d") (by decide)
  have hmMt : ∀ j, augSeamMt j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "ya.m") (by decide)
  have hmRa : ∀ j, augSeamRa j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "yr.a") (by decide)
  have hmTp : ∀ j, augSeamTp j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "yt.p") (by decide)
  have hmSk : ∀ j, augSeamSk j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "yk.c") (by decide)
  have hmCn : ∀ j, augSeamCn j ∈ augSeamWrites j :=
    fun j => augSeamWrites_base (t := "yc.n") (by decide)
  have hmIo : ∀ j, ardIo j ∈ augSeamWrites j :=
    fun j => augSeamWrites_ard (b := "ri.o") (by decide)
  have hmIt : ∀ j, ardIt j ∈ augSeamWrites j :=
    fun j => augSeamWrites_ard (b := "ri.t") (by decide)
  -- the scratch pool, likewise
  have hCbld : ∀ (j : ℕ) (y : String), y ∉ augSeamCells j → y ∉ bldScalars :=
    fun j y hy hm => hy (by
      simp only [augSeamCells, List.mem_append, basePeelScalars]
      exact Or.inl (Or.inl (Or.inr (Or.inr hm))))
  have hCbp : ∀ (j : ℕ) (y : String), y ∉ augSeamCells j → y ∉ basePeelScalars :=
    fun j y hy hm => hy (by
      simp only [augSeamCells, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hm)))
  have hCor : ∀ (j : ℕ) (y : String), y ∉ augSeamCells j →
      y ∉ ardNA j :: orScalars := by
    intro j y hy hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact hy (by simp [augSeamCells])
    · exact hy (by simp only [augSeamCells, List.mem_append]; exact Or.inl (Or.inr hm))
  -- the arena's two cells, and the two mark windows, against each pass
  have hclj : ∀ j, BldCells (arenaNames j).nN (arenaNames j).nS :=
    fun j => bldCells_arenaNames j
  have hnNbp : ∀ j, (arenaNames j).nN ∉ basePeelScalars :=
    fun j => ard_lv_notMem (s := "sv.n") rfl (by decide) j
  have hnSbp : ∀ j, (arenaNames j).nS ∉ basePeelScalars :=
    fun j => ard_lv_notMem (s := "sv.m") rfl (by decide) j
  have hbld : ∀ j, BldNames (arenaNames j).off (arenaNames j).tgt (augSeamRaY j)
      (augSeamAo j) (augSeamAj j) (augSeamDg j) (augSeamMt j) (augSeamOdY j) := by
    intro j; constructor <;> seam_ne
  have hmkFor : ∀ j, ("rf.m" : String) ≠ "ri.o" ∧ ("rf.m" : String) ≠ "ri.t" ∧
      ("rf.m" : String) ≠ augSeamCn j ∧ ("rt.m" : String) ≠ "ri.o" ∧
      ("rt.m" : String) ≠ "ri.t" ∧ ("rt.m" : String) ≠ augSeamCn j := by
    intro j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> seam_ne
  have hNcap : ∀ N : ℕ, N + 1 ≤ ardCap N := by intro N; simp only [ardCap]; omega
  have hioMem : ∀ j, ardIo j ∈ augSeamRegsAll j := by
    intro j; refine List.mem_append_right _ ?_; simp [ardRegions]
  refine augBaseIn_of_adj_peel_orient C hC φ (fun m => bucketSel m) G c w q ℓp
    htabF hbf Adm ca co augSeamAo augSeamAj augSeamDg augSeamMt augSeamRa
    (fun j A => augStInNW ardIo ardIt ardNA j A)
    (augSeamSag n) (augSeamSbd n) augSeamSrd Smp Ssw _ _ _
    81 116 24 394 352 64 70 86 25 ?_ ?_ ?_
  -- ### the region build
  · refine augBaseAdjIn_bldAdjCom C hC φ (fun m => bucketSel m) G c w q ℓp htabF
      hbf Adm ca co augSeamAo augSeamAj augSeamDg augSeamMt augSeamRaY
      augSeamOdY (augSeamSag n) (augSeamSbd n) Smp Ssw hq hbld ?_
      (fun j σ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩) ?_ ?_ ?_
    · intro j b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> seam_ne
    · intro j σ σ' h harr hvar
      obtain ⟨k1, k2, k3, k4⟩ : ("rf.m" : String) ≠ augSeamAo j ∧
          ("rf.m" : String) ≠ augSeamAj j ∧ ("rf.m" : String) ≠ augSeamDg j ∧
          ("rf.m" : String) ≠ augSeamMt j := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> seam_ne
      obtain ⟨m1, m2, m3, m4⟩ : ("rt.m" : String) ≠ augSeamAo j ∧
          ("rt.m" : String) ≠ augSeamAj j ∧ ("rt.m" : String) ≠ augSeamDg j ∧
          ("rt.m" : String) ≠ augSeamMt j := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> seam_ne
      refine augSeamSbd_of_len h.1 (fun b hb => ?_) (harr _ k1 k2 k3 k4)
        (harr _ m1 m2 m3 m4) (hvar _ (hclj j).nN_notMem) (hvar _ (hclj j).nS_notMem)
      obtain ⟨e1, e2, e3, e4⟩ := augSeamSbdArrs_ne_region hb
      rw [harr b e1 e2 e3 e4]
    · exact fun j σ σ' h harr hvar => hSmpW j σ σ' h
        (fun b hb => harr b (hW j b _ hb (hmAo j)) (hW j b _ hb (hmAj j))
          (hW j b _ hb (hmDg j)) (hW j b _ hb (hmMt j)))
        (fun y hy => hvar y (hCbld j y hy))
    · exact fun j σ σ' h harr hvar => hSswW j σ σ' h
        (fun b hb => harr b (hW j b _ hb (hmAo j)) (hW j b _ hb (hmAj j))
          (hW j b _ hb (hmDg j)) (hW j b _ hb (hmMt j)))
        (fun y hy => hvar y (hCbld j y hy))
  -- ### the peel, at a parametric base descriptor
  · refine augBasePeelInS_bucketPeelBuild C hC φ G c w q ℓp htabF hbf Adm ca co
      augSeamAo augSeamAj augSeamDg augSeamMt augSeamRa augSeamTp augSeamSk
      augSeamRaY augSeamOdY (augSeamSbd n) Smp Ssw hq ?_ ?_ hbld ?_
      (fun j σ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) ?_ ?_ ?_
    · intro j; constructor <;> seam_ne
    · intro j; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> seam_ne
    · rintro j b (rfl | rfl | rfl | rfl | rfl) <;>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> seam_ne
    · intro j σ σ' h harr hlen hvar
      refine augSeamSbd_of_len h (fun b _ => hlen b) ?_ ?_
        (hvar _ (hnNbp j)) (hvar _ (hnSbp j)) <;>
        refine harr _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> seam_ne
    · exact fun j σ σ' h harr hlen hvar => hSmpW j σ σ' h
        (fun b hb => harr b (hW j b _ hb (hmAo j)) (hW j b _ hb (hmAj j))
          (hW j b _ hb (hmDg j)) (hW j b _ hb (hmMt j)) (hW j b _ hb (hmRa j))
          (hW j b _ hb (hmTp j)) (hW j b _ hb (hmSk j)))
        (fun y hy => hvar y (hCbp j y hy))
    · exact fun j σ σ' h harr hlen hvar => hSswW j σ σ' h
        (fun b hb => harr b (hW j b _ hb (hmAo j)) (hW j b _ hb (hmAj j))
          (hW j b _ hb (hmDg j)) (hW j b _ hb (hmMt j)) (hW j b _ hb (hmRa j))
          (hW j b _ hb (hmTp j)) (hW j b _ hb (hmSk j)))
        (fun y hy => hvar y (hCbp j y hy))
  -- ### the orientation
  · refine augBaseOrientIn_orCom C hC φ (fun m => bucketSel m) G c w q ℓp htabF
      hbf Adm ca co augSeamAo augSeamAj augSeamDg augSeamMt augSeamRa ardIo
      ardIt augSeamCn ardNA (augSeamSbd n) augSeamSrd Smp Ssw hq ?_
      (fun _ => (by decide : ("rc.a" : String) ∉ orScalars)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun j => (by
        constructor <;> seam_ne :
        OrNames (augSeamAo j) (augSeamAj j) (augSeamRa j) "ri.o" "ri.t"
          (augSeamCn j))
    · exact fun j => (lv_ne_len4 (s := "sv.n") (t := "rc.a") (by decide)
        (by decide) (by decide) j).symm
    · exact fun j => (lv_ne_len4 (s := "sv.m") (t := "rc.a") (by decide)
        (by decide) (by decide) j).symm
    · refine fun j b hb => ?_
      have h : ∀ x : String, x ∈ [("ri.o" : String), "ri.t", augSeamCn j] →
          x ≠ (arenaNames j).off ∧ x ≠ (arenaNames j).tgt ∧
          x ≠ (arenaNames j).col ∧ x ≠ (arenaNames j).up ∧
          x ≠ (arenaNames j).hist := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> seam_ne
      exact h b hb
    · refine fun j σ h => ⟨?_, h.2.1, h.2.2.1⟩
      exact le_trans (hNcap _) (h.1.1 (ardIo j) (hioMem j))
    · intro j σ σ' h harr hlen hvar
      refine augSeamSrd_of_len h.1 (fun b _ => hlen b) ?_ ?_ ?_
      · exact harr _ (hmkFor j).1 (hmkFor j).2.1 (hmkFor j).2.2.1
      · exact harr _ (hmkFor j).2.2.2.1 (hmkFor j).2.2.2.2.1 (hmkFor j).2.2.2.2.2
      · refine hvar _ ?_
        simp only [List.mem_cons, not_or]
        exact ⟨lv_ne_len4 (s := "sv.n") (t := "rc.a") (by decide) (by decide)
          (by decide) j, arenaNames_nN_notMem_orScalars j⟩
    · exact fun j σ σ' h harr hlen hvar => hSmpW j σ σ' h
        (fun b hb => harr b (hW j b _ hb (hmIo j)) (hW j b _ hb (hmIt j))
          (hW j b _ hb (hmCn j)))
        (fun y hy => hvar y (hCor j y hy))
    · exact fun j σ σ' h harr hlen hvar => hSswW j σ σ' h
        (fun b hb => harr b (hW j b _ hb (hmIo j)) (hW j b _ hb (hmIt j))
          (hW j b _ hb (hmCn j)))
        (fun y hy => hvar y (hCor j y hy))

/-! ## §7 `AugRoundIn`, at the widened allocation list

`augRoundIn_ardRoundCom` concludes at `ardSrd`'s `regs` instantiated at
the round's own twenty-two.  The symmetrization needs nine more, and the
round must be seen to *preserve* them.  Nothing new is proved about the
round: its `Smp` is a parameter carried by a frame-shaped transport, so
`Smp ∧ (the nine allocations)` carries them, and the rule of consequence
puts the conjunction back where `ardSrd` wants it. -/

/-- The round's own allocation list, at the standard names. -/
abbrev ardRegionsStd : ℕ → List String :=
  ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo ardAj ardDgP ardMt ardSg
    ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo ardQt ardAd ardSd ardDgE

/-- The nine allocations the round does not itself need. -/
def augSeamQ (j : ℕ) (σ : Env) : Prop :=
  ∀ b ∈ augSeamRegs j, ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs b).length

theorem augSeamRegsAll_reg {j : ℕ} {t : String} (ht : t ∈ augSeamRegBases) :
    lv t j ∈ augSeamRegsAll j :=
  List.mem_append_left _ (List.mem_map_of_mem ht)

theorem augSeamWrites_of_ardAlloc {j : ℕ} {b : String}
    (hb : b ∈ augRdAllocs (ardFo j) (ardFt j) (ardDgF j) (ardAo j) (ardAj j)
      (ardDgP j) (ardMt j) (ardSg j) (ardTp j) (ardSk j) (ardRo j) (ardRt j)
      (ardMkT j) (ardOo j) (ardOt j) (ardQo j) (ardQt j) (ardAd j) (ardSd j)
      (ardDgE j)) : b ∈ augSeamArdNames :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb))

/-- **The augmentation's descriptor splits along its two halves.** -/
theorem augSeamSrd_split {j : ℕ} {σ : Env} :
    augSeamSrd j σ ↔ ardSrd ardMkF ardMkT ardRegionsStd j σ ∧ augSeamQ j σ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨fun b hb => h1 b (List.mem_append_right _ hb), h2, h3, h4⟩,
      fun b hb => h1 b (List.mem_append_left _ hb)⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, hq⟩
    refine ⟨fun b hb => ?_, h2, h3, h4⟩
    rcases List.mem_append.mp hb with h | h
    · exact hq b h
    · exact h1 b h

/-- The round's write frame, from the augmentation's. -/
theorem augSeamArdFrame (j : ℕ) {b : String} (hb : b ∉ augSeamWrites j) :
    b ≠ ardMkF j ∧
      b ∉ augRdAllocs (ardFo j) (ardFt j) (ardDgF j) (ardAo j) (ardAj j)
        (ardDgP j) (ardMt j) (ardSg j) (ardTp j) (ardSk j) (ardRo j) (ardRt j)
        (ardMkT j) (ardOo j) (ardOt j) (ardQo j) (ardQt j) (ardAd j) (ardSd j)
        (ardDgE j) ∧ b ≠ ardIo j ∧ b ≠ ardIt j := by
  refine ⟨?_, fun hm => hb (augSeamWrites_ard (augSeamWrites_of_ardAlloc hm)),
    ?_, ?_⟩
  · rintro rfl
    exact hb (augSeamWrites_ard (show ("rf.m" : String) ∈ augSeamArdNames by decide))
  · rintro rfl
    exact hb (augSeamWrites_ard (show ("ri.o" : String) ∈ augSeamArdNames by decide))
  · rintro rfl
    exact hb (augSeamWrites_ard (show ("ri.t" : String) ∈ augSeamArdNames by decide))

/-- The round's scalar frame, from the augmentation's. -/
theorem augSeamArdCells (j : ℕ) {y : String} (hy : y ∉ augSeamCells j) :
    y ∉ ardScalars ∧ y ≠ ardNF j ∧ y ≠ ardNT j ∧ y ≠ ardNO j ∧ y ≠ ardNA j := by
  refine ⟨fun hm => hy (by
      simp only [augSeamCells, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm))))), ?_, ?_, ?_, ?_⟩
  · rintro rfl; exact hy (by simp [augSeamCells])
  · rintro rfl; exact hy (by simp [augSeamCells])
  · rintro rfl; exact hy (by simp [augSeamCells])
  · rintro rfl; exact hy (by simp [augSeamCells])

/-- The arena's carrier cell survives a round. -/
theorem augSeamArdNn (j : ℕ) {σ σ' : Env}
    (hvar : ∀ y : String, y ∉ ardScalars → y ≠ ardNF j → y ≠ ardNT j →
      y ≠ ardNO j → y ≠ ardNA j → σ'.vars y = σ.vars y) :
    σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
  hvar _ (ard_nN_notMem_ardScalars j)
    (lv_ne_len4 (s := "sv.n") (t := "rc.f") (by decide) (by decide) (by decide) j)
    (lv_ne_len4 (s := "sv.n") (t := "rc.t") (by decide) (by decide) (by decide) j)
    (lv_ne_len4 (s := "sv.n") (t := "rc.o") (by decide) (by decide) (by decide) j)
    (lv_ne_len4 (s := "sv.n") (t := "rc.a") (by decide) (by decide) (by decide) j)

open Classical in
/-- **`AugRoundIn`, at the augmentation's whole allocation list.**  Same
program, same coefficients `1025, 455, 588, 305, 287`; only `Srd` is
widened, and the widening is carried by the round's own `Smp` slot. -/
theorem augSeamRoundIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (R : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (Smp Ssw : ℕ → Env → Prop)
    (hword : ArdWord C hC φ (fun m => bucketSel m) R G c w q Adm)
    (hSmpW : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Smp j σ')
    (hSswW : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugRoundIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInNW ardIo ardIt ardNA j A) augSeamSrd Smp Ssw
      (fun j => ardRoundCom (arenaNames j).nN (ardNF j) (ardNT j) (ardNO j)
        (ardNA j) (ardIo j) (ardIt j) (ardFo j) (ardFt j) (ardDgF j)
        (ardMkF j) (ardAo j) (ardAj j) (ardDgP j) (ardMt j) (ardSg j)
        (ardTp j) (ardSk j) (ardRo j) (ardRt j) (ardMkT j) (ardOo j)
        (ardOt j) (ardQo j) (ardQt j) (ardAd j) (ardSd j) (ardDgE j))
      1025 455 588 305 287 := by
  intro x hx j hj A hAdm hbot i hi
  refine (augRoundIn_ardRoundCom C hC φ R G c w q ℓp htabF hbf Adm ca co
    ardNF ardNT ardNO ardNA ardIo ardIt ardFo ardFt ardDgF ardMkF ardAo ardAj
    ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo ardQt
    ardAd ardSd ardDgE (fun jj σ => Smp jj σ ∧ augSeamQ jj σ) Ssw hword
    ardNames_std ardCells_std ?_ ?_ x hx j hj A hAdm hbot i hi).conseq ?_ ?_ le_rfl
  · rintro jj σ σ' ⟨h1, h2⟩ harr hvar
    have hA : ∀ b : String, b ∉ augSeamWrites jj → σ'.arrs b = σ.arrs b := by
      intro b hb
      obtain ⟨e1, e2, e3, e4⟩ := augSeamArdFrame jj hb
      exact harr b e1 e2 e3 e4
    have hV : ∀ y : String, y ∉ augSeamCells jj → σ'.vars y = σ.vars y := by
      intro y hy
      obtain ⟨e1, e2, e3, e4, e5⟩ := augSeamArdCells jj hy
      exact hvar y e1 e2 e3 e4 e5
    refine ⟨hSmpW jj σ σ' h1 hA hV, fun b hb => ?_⟩
    have hbn := augSeamRegs_notArd hb
    have harrb : σ'.arrs b = σ.arrs b := by
      refine harr b ?_ (fun hm => hbn (augSeamWrites_of_ardAlloc hm)) ?_ ?_
      · rintro rfl; exact hbn (show ("rf.m" : String) ∈ augSeamArdNames by decide)
      · rintro rfl; exact hbn (show ("ri.o" : String) ∈ augSeamArdNames by decide)
      · rintro rfl; exact hbn (show ("ri.t" : String) ∈ augSeamArdNames by decide)
    rw [augSeamArdNn jj hvar, harrb]
    exact h2 b hb
  · intro jj σ σ' h harr hvar
    refine hSswW jj σ σ' h (fun b hb => ?_) (fun y hy => ?_)
    · obtain ⟨e1, e2, e3, e4⟩ := augSeamArdFrame jj hb
      exact harr b e1 e2 e3 e4
    · obtain ⟨e1, e2, e3, e4, e5⟩ := augSeamArdCells jj hy
      exact hvar y e1 e2 e3 e4 e5
  · rintro σ ⟨hA, hst, hsrd, hca, hco, hsm, hsw⟩
    obtain ⟨hs1, hs2⟩ := augSeamSrd_split.mp hsrd
    exact ⟨hA, hst, hs1, hca, hco, ⟨hsm, hs2⟩, hsw⟩
  · rintro σ σ' - ⟨hA, hst, hs1, hca, hco, ⟨hsm, hs2⟩, hsw⟩
    exact ⟨hA, hst, augSeamSrd_split.mpr ⟨hs1, hs2⟩, hca, hco, hsm, hsw⟩

/-! ## §8 The augmentation pass, composed

`covAugAdjSelIn_of_base_rounds_sym` at the three discharges above.  The
three shared parameters that `SolveCoverAllJoin` §4b–§4d showed to be
over-determined are now one predicate each: `Sbd := augSeamSbd`,
`Srd := augSeamSrd`, and the orientation region `augStInNW` throughout. -/

/-- The base pass's program: build the region, peel it into the ranks
and rebuild it, orient along the ranks. -/
def augSeamBaseCom (j : ℕ) : Com :=
  .seq
    (.seq
      (bldAdjCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
        (arenaNames j).tgt (augSeamAo j) (augSeamAj j) (augSeamDg j)
        (augSeamMt j))
      (.seq
        (bucketPeelCom (augSeamAo j) (augSeamAj j) (augSeamDg j) (augSeamMt j)
          (augSeamRa j) (augSeamTp j) (augSeamSk j) (arenaNames j).nN)
        (bldAdjCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
          (arenaNames j).tgt (augSeamAo j) (augSeamAj j) (augSeamDg j)
          (augSeamMt j))))
    (orCom (arenaNames j).nN (ardNA j) (augSeamAo j) (augSeamAj j) (augSeamRa j)
      (ardIo j) (ardIt j) (augSeamCn j))

/-- One round, at the standard names. -/
def augSeamRoundComStd (j : ℕ) : Com :=
  ardRoundCom (arenaNames j).nN (ardNF j) (ardNT j) (ardNO j) (ardNA j)
    (ardIo j) (ardIt j) (ardFo j) (ardFt j) (ardDgF j) (ardMkF j) (ardAo j)
    (ardAj j) (ardDgP j) (ardMt j) (ardSg j) (ardTp j) (ardSk j) (ardRo j)
    (ardRt j) (ardMkT j) (ardOo j) (ardOt j) (ardQo j) (ardQt j) (ardAd j)
    (ardSd j) (ardDgE j)

/-- The symmetrization's program: transpose and merge, then the landed
region build. -/
def augSeamSymCom (j : ℕ) : Com :=
  .seq
    (symCom (arenaNames j).nN (ardIo j) (ardIt j) (augSeamQo j) (augSeamQt j)
      (augSeamDgY j) (augSeamSo j) (augSeamSt j) (augSeamNny j) (augSeamNsy j))
    (bldAdjCom (augSeamNny j) (augSeamNsy j) (augSeamSo j) (augSeamSt j)
      (lv "oc.p" j) (lv "oc.j" j) (lv "oc.d" j) (lv "oc.m" j))

/-- The merge's scalar frame, from the augmentation's. -/
theorem augSeamSymCells (j : ℕ) {y : String} (hy : y ∉ augSeamCells j) :
    y ∉ syScalars ∧ y ∉ tpScalars ∧ y ∉ bldScalars ∧ y ≠ augSeamNny j ∧
      y ≠ augSeamNsy j := by
  refine ⟨fun hm => hy (by
      simp only [augSeamCells, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))),
    fun hm => hy (by
      simp only [augSeamCells, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hm)))),
    fun hm => hy (by
      simp only [augSeamCells, List.mem_append, basePeelScalars]
      exact Or.inl (Or.inl (Or.inr (Or.inr hm)))), ?_, ?_⟩
  · rintro rfl; exact hy (by simp [augSeamCells])
  · rintro rfl; exact hy (by simp [augSeamCells])

open Classical in
/-- **`AugSymIn`, at the concrete family.** -/
theorem augSeamSymIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0) (R : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hSmpW : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Smp j σ')
    (hSswW : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugSymIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm ca co
      (lv "oc.p") (lv "oc.j") (lv "oc.d") (lv "oc.m")
      (fun j A => augStInNW ardIo ardIt ardNA j A) augSeamSrd Smp Ssw
      augSeamSymCom 171 196 84 := by
  refine augSeamSymIn_symBuild C hC φ (fun m => bucketSel m) R G c w q ℓp htabF
    hbf Adm ca co ardIo ardIt ardNA augSeamNny augSeamNsy augSeamSo augSeamSt
    augSeamQo augSeamQt augSeamDgY augSeamRaY augSeamOdY (lv "oc.p") (lv "oc.j")
    (lv "oc.d") (lv "oc.m") augSeamSrd Smp Ssw hq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun j => (by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · constructor <;> seam_ne
      all_goals seam_ne :
      SyNames "ri.o" "ri.t" (augSeamQo j) (augSeamQt j) (augSeamDgY j)
        (augSeamSo j) (augSeamSt j))
  · intro j; constructor <;> seam_ne
  · intro j; constructor <;> seam_ne
  · refine fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ard_lv_notMem (s := "yn.n") rfl (by decide) j
    · exact ard_lv_notMem (s := "yn.s") rfl (by decide) j
    all_goals seam_ne
  · rintro j b (rfl | rfl | rfl | rfl | rfl) <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> seam_ne
  · exact fun j σ h => ⟨h.1 _ (augSeamRegsAll_reg (t := "ys.o") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "ys.t") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "yq.o") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "yq.t") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "yg.d") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "oc.p") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "oc.j") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "oc.d") (by decide)),
      h.1 _ (augSeamRegsAll_reg (t := "oc.m") (by decide))⟩
  · intro j σ σ' h harr hlen hvar
    refine hSmpW j σ σ' h (fun b hb => ?_) (fun y hy => ?_)
    · refine harr b ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        · rintro rfl
          exact hb (augSeamWrites_reg (by decide))
    · obtain ⟨e1, e2, e3, e4, e5⟩ := augSeamSymCells j hy
      exact hvar y e1 e2 e3 e4 e5
  · intro j σ σ' h harr hlen hvar
    refine hSswW j σ σ' h (fun b hb => ?_) (fun y hy => ?_)
    · refine harr b ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        · rintro rfl
          exact hb (augSeamWrites_reg (by decide))
    · obtain ⟨e1, e2, e3, e4, e5⟩ := augSeamSymCells j hy
      exact hvar y e1 e2 e3 e4 e5

open Classical in
/-- **`CovAugAdjSelIn`, discharged.**  The augmentation pass at the
concrete family: `augSeamBaseCom ; (augSeamRoundComStd)^R ; augSeamSymCom`,
the descriptor `augSeamSag`, and the budget
`augChainCost 545 554 113 1025 455 588 305 287 171 196 84` — the very
coefficients `covAllJoin_base_coeffs`, `SolveAugRoundIn`'s round and
`covAllJoin_sym_coeffs` already record, so `covAllJoin_Kord_le` bounds
the total by `545·selChainCharge + O(R)` with nothing new measured.

The surviving hypotheses are `1 ≤ q`, `ArdWord` (the round's five figures
are words — `SolveF7CloseQ`'s `f7q` supplies it from `q ≥ 3K + 2`), and
the two descriptors' transports across the augmentation's own write set
and scratch pool. -/
theorem augSeamCovAugAdjSelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hword : ArdWord C hC φ (fun m => bucketSel m) R G c w q Adm)
    (hSmpW : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Smp j σ')
    (hSswW : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b) →
      (∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y) → Ssw j σ') :
    CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm ca co
      (lv "oc.p") (lv "oc.j") (lv "oc.d") (lv "oc.m")
      (augSeamSag n) Smp Ssw
      (fun j => .seq (.seq (augSeamBaseCom j) (comIter (augSeamRoundComStd j) R))
        (augSeamSymCom j))
      (fun _j A => augChainCost 545 554 113 1025 455 588 305 287 171 196 84
        (bucketSel A.N) A.G R) :=
  covAugAdjSelIn_of_base_rounds_sym C hC φ (fun m => bucketSel m) R G c w q ℓp
    htabF hbf Adm ca co (lv "oc.p") (lv "oc.j") (lv "oc.d") (lv "oc.m")
    (fun j A => augStInNW ardIo ardIt ardNA j A) (augSeamSag n) augSeamSrd Smp Ssw
    augSeamBaseCom augSeamRoundComStd augSeamSymCom
    545 554 113 1025 455 588 305 287 171 196 84
    (augSeamBaseIn C hC φ G c w q ℓp htabF hbf Adm ca co Smp Ssw hq hSmpW hSswW)
    (augSeamRoundIn C hC φ R G c w q ℓp htabF hbf Adm ca co Smp Ssw hword
      hSmpW hSswW)
    (augSeamSymIn C hC φ R G c w q ℓp htabF hbf Adm ca co Smp Ssw hq hSmpW hSswW)

/-! ## §8b The no-go of `SolveCoverAllJoin` §4d, re-run against the repair

`coverAllSym_srd_forces_constant` ran on one mechanism: `symCsrSizes`
pins `(σ.arrs (stO j)).length = 2·σ.vars (nA j)` by **equality**, so two
states of one run — which have equal array lengths, `store` being
`List.set` — have equal `nA` cells, and `nA` is the arc count.  The test
of a repair is whether that mechanism still runs.

It does not, and the reason is exhibited rather than asserted: the
repaired obligation is `ardCap (σ.vars nN) ≤ (σ.arrs (stO j)).length`,
whose only figure is the carrier cell, and two states with the *same*
array lengths and the *same* carrier cell can carry **any** two
arc-count cells while both satisfy the descriptor.  So nothing in
`augSeamSrd` relates `σ.vars (ardNA j)` at one round to
`σ'.vars (ardNA j)` at the next, and no analogue of §4d can be
formulated. -/

/-- **The repaired descriptor puts no relation on the arc-count cell.**
At every level and every pair of arc counts there are two states, with
equal array lengths and equal carrier cells, that both satisfy
`augSeamSrd` and whose `nA` cells are the two given numbers.  Under
`symCsrSizes` this is impossible for `a₁ ≠ a₂`; that is the whole of the
difference. -/
theorem augSeamSrd_no_arc_link (j a₁ a₂ : ℕ) :
    ∃ σ₁ σ₂ : Env, augSeamSrd j σ₁ ∧ augSeamSrd j σ₂ ∧
      σ₁.vars (ardNA j) = a₁ ∧ σ₂.vars (ardNA j) = a₂ ∧
      (∀ b : String, (σ₁.arrs b).length = (σ₂.arrs b).length) ∧
      σ₁.vars (arenaNames j).nN = σ₂.vars (arenaNames j).nN := by
  classical
  have hnamk : (arenaNames j).nN ≠ "rc.a" :=
    lv_ne_len4 (s := "sv.n") (t := "rc.a") (by decide) (by decide) (by decide) j
  have hreg : ∀ b ∈ augSeamRegsAll j, b ≠ "rf.m" := by
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
      exact lv_ne_len4 (augSeamRegBases_len t ht) (by decide)
        (augSeamRegBases_ne_ard t ht "rf.m" (by decide)) j
    · exact (show ∀ b ∈ ardRegionsStd 0, b ≠ "rf.m" by decide) b h
  have key : ∀ a : ℕ, ∃ σ : Env, augSeamSrd j σ ∧ σ.vars (ardNA j) = a ∧
      σ.vars (arenaNames j).nN = 0 ∧
      (∀ b : String, (σ.arrs b).length = if b = "rf.m" then 0 else 1) := by
    intro a
    obtain ⟨σ, hσ⟩ : ∃ σ : Env, σ = (⟨fun y => if y = "rc.a" then a else 0,
        fun b => if b = "rf.m" then [] else [0], [], []⟩ : Env) := ⟨_, rfl⟩
    have hvn : σ.vars (arenaNames j).nN = 0 := by rw [hσ]; exact if_neg hnamk
    have hva : σ.vars (ardNA j) = a := by rw [hσ]; simp
    have hmk : σ.arrs "rf.m" = [] := by rw [hσ]; simp
    have hone : ∀ b : String, b ≠ "rf.m" → σ.arrs b = [0] := by
      intro b hb; rw [hσ]; exact if_neg hb
    refine ⟨σ, ⟨fun b hb => ?_, ?_, ?_, ?_⟩, hva, hvn, fun b => ?_⟩
    · rw [hvn, hone b (hreg b hb)]; simp [ardCap]
    · rw [hvn, hmk]; simp
    · intro i; rw [hmk]; simp
    · intro i hi; rw [hvn] at hi; omega
    · by_cases hb : b = "rf.m"
      · rw [hb, hmk, if_pos rfl]; simp
      · rw [hone b hb, if_neg hb]; simp
  obtain ⟨σ₁, s1, v1, n1, l1⟩ := key a₁
  obtain ⟨σ₂, s2, v2, n2, l2⟩ := key a₂
  exact ⟨σ₁, σ₂, s1, s2, v1, v2, fun b => by rw [l1 b, l2 b], by rw [n1, n2]⟩

/-- **The hypothesis `coverAllSym_srd_forces_constant` runs on is not
merely unproved at the repaired descriptor — it is refuted.**  That
theorem needs `hsz : ∀ j σ, Srd j σ → symCsrSizes nA soO stO j σ`; at
`Srd := augSeamSrd` and the round's own arc-count cell no such `hsz`
exists, for **any** choice of the output pair.  So §4d's argument cannot
be re-run against the composition of §8, and the augmentation is free to
emit. -/
theorem augSeamSrd_not_symCsrSizes (j : ℕ) (soO stO : ℕ → String) :
    ¬ (∀ σ : Env, augSeamSrd j σ → symCsrSizes ardNA soO stO j σ) := by
  intro h
  obtain ⟨σ₁, σ₂, s1, s2, v1, v2, hl, -⟩ := augSeamSrd_no_arc_link j 0 1
  have h1 := (h σ₁ s1).2
  have h2 := (h σ₂ s2).2
  rw [v1] at h1
  rw [v2] at h2
  have hlen := hl (stO j)
  omega

/-! ## §9 Axiom audit -/

#print axioms augSeamSymIn_symBuild

#print axioms augSeamBaseIn

#print axioms augSeamRoundIn

#print axioms augSeamSymIn

#print axioms augSeamCovAugAdjSelIn

#print axioms augSeamSrd_no_arc_link

#print axioms augSeamSrd_not_symCsrSizes

#print axioms augSeamNotWrite

#print axioms augSeam_nN_notMem_cells

end Lax3Proofs.Prog
