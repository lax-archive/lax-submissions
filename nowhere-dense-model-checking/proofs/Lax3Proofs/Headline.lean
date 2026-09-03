import Lax3Proofs.Unroll
import Lax3Proofs.Reduction
import Lax11.GraphEncoding
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Order.Interval.Set.Nat

/-!
# The headline, composed — and the exact remainder to the endorsed axiom

The campaign's final leaf. The endorsed axiom
(`Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`,
`concepts/Lax3/ModelChecking.lean:115-125`) asks for a word-RAM
`Program` deciding a plain first-order sentence `φ : FO 0` on every
member of a nowhere dense class in time `c·(|x|+1)^(1+ε)` on CSR
encodings `x`. This file delivers everything the landed layer supports
of it, and maps precisely what it does not:

* **Part 1 — the abstract headline.** `headline_abstract`: for every
  nowhere dense `C`, under the campaign's one assumption
  (`CoverSpec.CoverOrderingTime C`) alone, there are an ordering
  routine and two constants — all fixed before any input is read —
  such that the driver at the campaign setup (`toDistFO φ` at rank
  `rank φ`, the greedy scatter choice) **decides
  `Lax3.FirstOrder.Sat G Fin.elim0 φ` on every graph** and its
  abstract cost on every member of `C` is at most
  `c·(‖G‖+1)^(1+ε)`, `‖G‖ = graphWeight G` = vertices + edges.
  `headline_abstract_unrolled` restates it for the iterative
  (machine-shaped) form `unrolledMC`/`unrolledCost`.

* **Part 2 — the encoding seam.** The axiom's time bound is against
  `x.length`; the driver's is against `graphWeight G`. These close in
  exactly the direction the axiom needs:
  `graphWeight_add_three_le_length` proves
  `graphWeight G + 3 ≤ x.length` from `EncodesGraph x n G` (via
  `ncard_edgeSet_le_edgeCount`: the declared edge count of a CSR word
  is at least the number of edges — the word's target array lists each
  edge from both endpoints, so `2|E| ≤ Σ` block lengths `= 2m`).
  `headline_encoded` then restates Part 1's bound against
  `(x.length + 1)^(1+ε)`, the axiom's own measure. The **reverse**
  inequality does not hold and is not needed: `EncodesGraph` permits
  repeated neighbor entries, so `x.length` is not bounded by any
  function of `graphWeight G` — the seam is one-directional by design
  of the encoding, and the direction that holds is the one the time
  bound consumes.

* **Part 3 — the remainder**, mapped at the end of this file as the
  campaign's continuation record: what still separates Part 1+2 from
  the endorsed axiom, item by item, with the landed feeds and size
  estimates.

Binder order (the campaign's most-repeated gate): the routine `ord`
and the constants `cc` (per-child charge) and `c` (headline constant)
are produced by the existential **before** `n`, `G`, `col`, `x` are
bound, in every statement below; they depend only on `(C, hC, hT, φ,
ε)`, exactly as the axiom's `(p, c, T)` depend only on `(C, φ, ε)`.
-/

namespace Lax3Proofs.Headline

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO rank)
open Lax3Proofs.Driver Lax3Proofs.Reduction Lax3Proofs.CoverEdgeSum
open Lax11.GraphEncoding

/-! ## Part 1 — the abstract headline -/

/-- **The campaign setup of a plain first-order sentence**: the driver's
`Setup` at `L = 0` (no colors — the axiom's graphs are uncolored, and
`toDistFO`'s image mentions no color, so the trivial palette suffices),
formula `toDistFO φ`, rank witness `drank_toDistFO` at `q = rank φ`,
and the algorithm's canonical scatter choice `greedyChoice`. -/
noncomputable def headlineSetup (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) : Setup 0 :=
  mkSetup C hC (toDistFO φ) (drank_toDistFO φ le_rfl) greedyChoice

/-- The root arena weighs exactly the input graph: `‖A₀‖ = ‖G‖`. -/
@[simp] theorem weight_rootArena {L n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) :
    weight (rootArena G col) = graphWeight G := rfl

/-- The driver's cost at an edgeless root is the leaf charge — both the
fuel-`0` and the fuel-`k+1` branch of `dcostAux` return it. (Needed
only for the degenerate `‖G‖ = 0` input, i.e. `n = 0`, which
`dcost_root_le`'s hypothesis `1 ≤ ‖A₀‖` excludes.) -/
theorem dcost_of_bot {L n : ℕ} (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (c : ℝ) (A : Arena (S.pal 0) n) (h : A.G = ⊥) :
    dcost S ord c 0 A = c * (weight A : ℝ) := by
  rw [dcost, Nat.sub_zero]
  cases hd : S.depth with
  | zero => rfl
  | succ k => rw [dcostAux, if_pos h]

/-- **The driver at the campaign setup decides `φ` itself** — the iff
lands on the axiom's semantic object `Lax3.FirstOrder.Sat G Fin.elim0
φ`, through `sat_toDistFO`, on **every** graph (correctness needs
neither class membership nor the routine's quality) and for every
coloring of the empty palette. -/
theorem headlineSetup_mc_correct (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n 0) :
    MC (headlineSetup C hC φ) ord G col ↔
      Lax3.FirstOrder.Sat G Fin.elim0 φ :=
  (mkSetup_mc_correct C hC (toDistFO φ) (drank_toDistFO φ le_rfl)
      greedyChoice ord G col).trans
    (sat_toDistFO G col Fin.elim0 φ)

/-- **The abstract headline** (Grohe–Kreutzer–Siebertz, at the
abstract layer, conditional on the cover's running time): for every
nowhere dense class `C` under `CoverOrderingTime C`, every plain
first-order sentence `φ : FO 0` and every `ε > 0`, there are an
ordering routine `ord` and constants `cc, c ≥ 0` — **all fixed before
any input is read** — such that the driver at the campaign setup with
routine `ord`

* **decides `φ`**: `MC ↔ Lax3.FirstOrder.Sat G Fin.elim0 φ` on every
  graph, and
* **runs in almost linear abstract time on the class**: on every
  member `G` of `C`, `dcost` at per-child constant `cc` is at most
  `c · (‖G‖ + 1)^(1+ε)`.

The two clauses are about the *same* procedure — the same `S`, `ord`
and `cc` appear in the decision (`MC`, whose evaluation `dcost`
prices) and in the bound. `c` is `KD^(ℓ+1)` at the constants
`hT` supplies: `Classical.choose`-dependent, but a function of
`(C, hC, hT, φ, ε)` only. -/
theorem headline_abstract (C : GraphClass) (hC : NowhereDense C)
    (hT : CoverSpec.CoverOrderingTime C) (φ : FO 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ord : CoverSpec.OrderingRoutine) (cc c : ℝ), 0 ≤ cc ∧ 0 ≤ c ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n 0),
        MC (headlineSetup C hC φ) ord G col ↔
          Lax3.FirstOrder.Sat G Fin.elim0 φ) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ∀ col : Coloring n 0,
        dcost (headlineSetup C hC φ) ord cc 0 (rootArena G col) ≤
          c * ((graphWeight G : ℝ) + 1) ^ (1 + ε)) := by
  obtain ⟨ord, cD, f, hcD, hf, hmain⟩ :=
    mkSetup_dcost_root_le C hC hT (toDistFO (L := 0) φ)
      (drank_toDistFO φ le_rfl) greedyChoice hε
  -- the headline constant: `K^(ℓ+1)` at `c = cD`
  have hK1 : (1 : ℝ) ≤ KD (headlineSetup C hC φ) cD cD f := by
    have h1 : (0 : ℝ) ≤ (chargeBound (headlineSetup C hC φ) : ℝ) :=
      Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ cD * (chargeBound (headlineSetup C hC φ) : ℝ) * (cD + 1) :=
      mul_nonneg (mul_nonneg hcD h1) (by linarith)
    unfold KD
    linarith
  have hKpow : (1 : ℝ) ≤
      KD (headlineSetup C hC φ) cD cD f ^ ((headlineSetup C hC φ).depth + 1) :=
    one_le_pow₀ hK1
  refine ⟨ord, cD,
    KD (headlineSetup C hC φ) cD cD f ^ ((headlineSetup C hC φ).depth + 1),
    hcD, by linarith, fun n G col => headlineSetup_mc_correct C hC φ ord G col, ?_⟩
  intro n G hG col
  by_cases hW : 1 ≤ weight (rootArena (L := 0) G col)
  · -- the driver's bound, then `‖G‖ ≤ ‖G‖ + 1` under the exponent
    have h : dcost (headlineSetup C hC φ) ord cD 0 (rootArena G col) ≤
        KD (headlineSetup C hC φ) cD cD f ^ ((headlineSetup C hC φ).depth + 1) *
          (weight (rootArena (L := 0) G col) : ℝ) ^ (1 + ε) :=
      hmain G hG col cD le_rfl hW
    simp only [weight_rootArena] at h ⊢
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
  · -- the degenerate input: `‖G‖ = 0`, so `n = 0`, `G = ⊥`, cost `0`
    have hW0 : weight (rootArena (L := 0) G col) = 0 := by omega
    have hgw : graphWeight G = 0 := by rw [← weight_rootArena G col]; exact hW0
    have hn : n = 0 := by
      have := hgw; unfold graphWeight at this; omega
    subst hn
    have hbot : (rootArena (L := 0) G col).G = ⊥ := by
      show G = ⊥
      ext u v
      exact u.elim0
    have h0 : dcost (headlineSetup C hC φ) ord cD 0 (rootArena G col) =
        cD * (weight (rootArena (L := 0) G col) : ℝ) :=
      dcost_of_bot (headlineSetup C hC φ) ord cD _ hbot
    rw [h0, hW0, hgw]
    simp only [Nat.cast_zero, mul_zero, zero_add, Real.one_rpow, mul_one]
    linarith

/-- The abstract headline for the **iterative** (machine-shaped) form:
the same routine and constants, with the decision by `unrolledMC` and
the charge by `unrolledCost` — the `ℓ+1` static depth-indexed frames a
word RAM realizes. Verbatim transport across
`unrolledMC_eq_MC`/`unrolledCost_eq_dcost`. -/
theorem headline_abstract_unrolled (C : GraphClass) (hC : NowhereDense C)
    (hT : CoverSpec.CoverOrderingTime C) (φ : FO 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ord : CoverSpec.OrderingRoutine) (cc c : ℝ), 0 ≤ cc ∧ 0 ≤ c ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n 0),
        Unroll.unrolledMC (headlineSetup C hC φ) ord G col ↔
          Lax3.FirstOrder.Sat G Fin.elim0 φ) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ∀ col : Coloring n 0,
        Unroll.unrolledCost (headlineSetup C hC φ) ord cc 0 (rootArena G col) ≤
          c * ((graphWeight G : ℝ) + 1) ^ (1 + ε)) := by
  obtain ⟨ord, cc, c, hcc, hc, hMC, hcost⟩ := headline_abstract C hC hT φ hε
  refine ⟨ord, cc, c, hcc, hc, fun n G col => ?_, fun n G hG col => ?_⟩
  · rw [Unroll.unrolledMC_eq_MC]; exact hMC n G col
  · rw [Unroll.unrolledCost_eq_dcost]; exact hcost n G hG col

/-! ## Part 2 — the encoding seam

`Lax11.GraphEncoding.EncodesGraph x n G` pins `x.length = 3 + n + 2m`
where `m = edgeCount x` is the *declared* edge count — at least
`|E(G)|`, with equality exactly when no block repeats a neighbor
(repetitions are deliberately permitted; `GraphEncoding.lean`'s notes).
So the length relation closes in one direction only:
`graphWeight G + 3 ≤ x.length`, which is the direction the axiom's
time bound `c·(|x|+1)^(1+ε)` consumes. The reverse — `x.length`
bounded by `graphWeight G` — is **not derivable and is false**: an
encoding may repeat each neighbor arbitrarily often, making
`edgeCount x` (hence `x.length`) unbounded in terms of `G`. -/

/-- The blocks tile the target array: the block lengths sum to the
target array's length `2·edgeCount x` (telescoping `offset_mono`
between `offset_zero` and `offset_last`). -/
theorem sum_block_lengths {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : EncodesGraph x n G) :
    ∑ i ∈ Finset.range n, (offset x (i + 1) - offset x i) =
      2 * edgeCount x := by
  suffices hk : ∀ k, k ≤ n →
      ∑ i ∈ Finset.range k, (offset x (i + 1) - offset x i) = offset x k by
    rw [hk n le_rfl, h.offset_last]
  intro k
  induction k with
  | zero => intro _; simp [h.offset_zero]
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : offset x k ≤ offset x (k + 1) := h.offset_mono k (by omega)
    omega

/-- **A vertex's degree is at most its block length**: distinct
neighbors of `u` occupy distinct positions of `u`'s block (`adj_iff`
puts each one somewhere in the block; the stored value pins the
neighbor, so the positions are distinct). -/
theorem ncard_neighborSet_le_block {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) (u : Fin n) :
    (G.neighborSet u).ncard ≤ offset x (↑u + 1) - offset x ↑u := by
  classical
  have hch : ∀ v : Fin n, ∃ j, G.Adj u v →
      offset x ↑u ≤ j ∧ j < offset x (↑u + 1) ∧ target x j = ↑v := by
    intro v
    by_cases hv : G.Adj u v
    · obtain ⟨j, hj⟩ := (h.adj_iff u v).mp hv
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun hv' => absurd hv' hv⟩
  choose f hf using hch
  have hmap : ∀ v ∈ G.neighborSet u,
      f v ∈ Set.Ico (offset x ↑u) (offset x (↑u + 1)) := fun v hv =>
    ⟨(hf v hv).1, (hf v hv).2.1⟩
  have hinj : Set.InjOn f (G.neighborSet u) := by
    intro v₁ hv₁ v₂ hv₂ heq
    have h₁ := (hf v₁ hv₁).2.2
    have h₂ := (hf v₂ hv₂).2.2
    exact Fin.val_injective (by rw [← h₁, ← h₂, heq])
  calc (G.neighborSet u).ncard
      ≤ (Set.Ico (offset x ↑u) (offset x (↑u + 1))).ncard :=
        Set.ncard_le_ncard_of_injOn f hmap hinj (Set.finite_Ico _ _)
    _ = offset x (↑u + 1) - offset x ↑u := Set.ncard_Ico_nat _ _

/-- **The declared edge count dominates the true one**: each edge is
listed from both endpoints in disjoint blocks, so `2|E| = Σ degrees ≤
Σ` block lengths `= 2·edgeCount x`. Equality holds exactly for
repetition-free encodings; only this direction is needed. -/
theorem ncard_edgeSet_le_edgeCount {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) :
    G.edgeSet.ncard ≤ edgeCount x := by
  classical
  have hdeg : ∀ u : Fin n, G.degree u = (G.neighborSet u).ncard := by
    intro u
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hcard : G.edgeSet.ncard = G.edgeFinset.card :=
    Set.ncard_eq_toFinset_card' _
  have key : 2 * G.edgeSet.ncard ≤ 2 * edgeCount x := by
    calc 2 * G.edgeSet.ncard
        = ∑ u : Fin n, G.degree u := by
          rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      _ ≤ ∑ u : Fin n, (offset x (↑u + 1) - offset x ↑u) :=
          Finset.sum_le_sum fun u _ => by
            rw [hdeg u]; exact ncard_neighborSet_le_block h u
      _ = ∑ i ∈ Finset.range n, (offset x (i + 1) - offset x i) :=
          Fin.sum_univ_eq_sum_range (fun i => offset x (i + 1) - offset x i) n
      _ = 2 * edgeCount x := sum_block_lengths h
  omega

/-- **The seam, in the direction the axiom's time bound needs**: a CSR
word is at least as long as the graph weighs (with `3` to spare — the
two header entries and the extra offset). -/
theorem graphWeight_add_three_le_length {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) :
    graphWeight G + 3 ≤ x.length := by
  have h1 := ncard_edgeSet_le_edgeCount h
  have h2 := h.length_eq
  unfold graphWeight
  omega

/-- The seam, weakened to the form the monotone bound consumes. -/
theorem graphWeight_le_length {x : List ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (h : EncodesGraph x n G) :
    graphWeight G ≤ x.length :=
  le_trans (Nat.le_add_right _ 3) (graphWeight_add_three_le_length h)

/-- **The headline against the axiom's own measure**: the abstract
cost of the driver on a member of `C`, on any CSR encoding `x` of the
input, is at most `c · (|x| + 1)^(1+ε)` — the exact shape of the
endorsed axiom's time bound, with `ord`, `cc`, `c` fixed before
`n`, `G`, `col`, `x`. -/
theorem headline_encoded (C : GraphClass) (hC : NowhereDense C)
    (hT : CoverSpec.CoverOrderingTime C) (φ : FO 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ord : CoverSpec.OrderingRoutine) (cc c : ℝ), 0 ≤ cc ∧ 0 ≤ c ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (col : Coloring n 0),
        MC (headlineSetup C hC φ) ord G col ↔
          Lax3.FirstOrder.Sat G Fin.elim0 φ) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (col : Coloring n 0) (x : List ℕ), EncodesGraph x n G →
          dcost (headlineSetup C hC φ) ord cc 0 (rootArena G col) ≤
            c * ((x.length : ℝ) + 1) ^ (1 + ε)) := by
  obtain ⟨ord, cc, c, hcc, hc, hMC, hcost⟩ := headline_abstract C hC hT φ hε
  refine ⟨ord, cc, c, hcc, hc, hMC, ?_⟩
  intro n G hG col x hx
  refine (hcost n G hG col).trans (mul_le_mul_of_nonneg_left ?_ hc)
  have hlen : (graphWeight G : ℝ) ≤ (x.length : ℝ) :=
    Nat.cast_le.mpr (graphWeight_le_length hx)
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)

/-! ## Part 3 — the remainder to the endorsed axiom, mapped

What separates `headline_encoded` from
`exists_almostLinearTime_program_modelChecking`
(`concepts/Lax3/ModelChecking.lean:115-125`), item by item. Nothing
below is proved here; this is the campaign's continuation record,
verified against the landed sources on 2026-08-18.

**(a) The assembled program.** The axiom's `∃ p : Program` demands one
word-RAM program. The landed layer has (i) the driver as `ℓ+1` static
depth-indexed code blocks with no self-reference
(`Unroll.unrollAux`/`frameEval`/`botFrame`, with the static frame
layout priced in `Unroll.lean`'s header: `≤ (ℓ+1)(2+c_S)·n²` words,
absorbed by the axiom's squared side condition), and (ii) every
per-node routine implemented with spec and charge and an identity to
the abstract layer: `ImplRestrict` (`restrict`/`isolate` →
`preG`/`childCol0`), `ImplProfiles` (`recordProfiles` →
`Driver.childCol`), `ImplCover` (peeling sweep → `Driver.cluster`,
`CoverCentres.ctr`), `ImplBfs` (tower BFS at `B₀` + `bfsSupports`),
`ImplScatter` (`greedyScatter`, deciding `t ≤ greedyChoice.size`),
`ImplBot` (`botEval` = `tablesAux`'s leaf). **Missing**: the one
composed NREST/`Refine` program — the per-frame sequencing
restrict → profiles → isolate → cover → recurse-readback → scatter,
the loop/`whileT` structure over blocks and vertices, its `Spec`, and
the accounting theorem that its total charge is bounded by `dcost`'s
per-node charges (`nodeCharge`-shaped, plus `ord`'s `steps` — the
alignment `dcost` was designed for). This is the largest remaining
block: comparable in size to the whole `Impl*` family it composes
(estimate: several worker-days, thousands of lines).

**(b) Codegen to a `Lax67.Ram.Program`.** The landed exit is
`computesInTime_of_spec`
(`word-ram/proofs/Lax62Proofs/Refine/Codegen/Cash.lean:408-419`): from
`Com.Ok`, an input bound `∀ x ∈ D, ∀ v ∈ x, v < B x`, a
`Reasoning.Spec` for the IMP+ command, and `Layout.FitsWords (B x) w`,
it yields exactly the axiom's `ComputesInTime w (compileProgram L c) D
f (fun x => L.const * K x)`. The path is exercised once end-to-end by
`RefineBfsProbe`. **Missing**: (a)'s program taken down the Sepref
tower to an `Imp.Com`, plus the **CSR front end** — no module of
`Lax3Proofs` before this file mentions `EncodesGraph` at all: a parser
reading the word `x` (header, offsets, targets) into the root frame's
arena state, with its own linear charge and a spec against
`EncodesGraph x n G`, does not exist. Estimate: the front end is small
(one `RefineBfsProbe`-sized leaf); the Sepref descent of (a) is
proportional to (a).

**(c) The cover's running time** — `CoverSpec.CoverOrderingTime C`,
this campaign's standing assumption (E0), carried here as the
hypothesis `hT`. `CoverSpec.lean`'s header pins the discharge chain
link by link to the sources (GKS `thm:computingorientation` →
Nešetřil–Ossona de Mendez 2005 part II §4 → part I Lemma 6.1, with
the two genuinely missing steps identified: the nowhere-dense
instantiation of NOdM Corollary 4.2 and the `O(md²·n)` accounting at
`md = n^δ`); that is the NOdM formalization campaign, cited here and
not repeated. Two sub-items travel with it: `IsCoverOrdering.data`
(the greedy chain assembly with minimal `ElimPost` eliminations — the
mathematics is landed in `Augmentation`, only the assembly is
missing), and — after (a)/(b) exist — re-reading `steps` off the
machine routine, per `CoverSpec.lean`'s "How a later leaf connects
`steps` to a machine".

**(d) Word-size and space plumbing.** The axiom admits inputs with
`c·(x.length + v + 1)² ≤ 2^w`. That side condition must be spent
twice: as `computesInTime_of_spec`'s `hinp` (entries below the value
bound `B x`) and as its `hfit` (`Layout.FitsWords (B x) w` — the
static layout of (a) fits in `2^w` cells, which is exactly what the
*squared* form was endorsed for; `Unroll.lean`'s layout paragraph does
the arithmetic, `ModelChecking.lean`'s deviation note records the
design decision). The probe for the space side of the tower is
`word-ram/proofs/Lax62Proofs/Refine/Sepref/SpaceBudgetProbe.lean`.
Estimate: bookkeeping against (a)'s layout, small once (a) exists.

**(e) The `T : List ℕ → ℕ` bound.** The axiom's `T` is ℕ-valued with
a real-valued bound `(T x : ℝ) ≤ c·(|x|+1)^(1+ε)`. From (b), `T x =
L.const · K x`; closing the axiom's inequality needs the spec-level
charge `K x` bounded by (a)'s accounting against `dcost` (that is
(a)'s accounting theorem), then this file's `headline_encoded` chain
`dcost ≤ c·(|x|+1)^(1+ε)` finishes the arithmetic — with the ε-budget
split once between the driver's `δ = ε/(ℓ+2)` (already inside
`mkSetup_dcost_root_le`) and the constant `L.const` (absorbed into
`c`). No new mathematics; part of (a)/(b)'s statements.

**Not remaining** — closed by this file and its imports: the `FO 0` ↔
`DistFO` seam (`toDistFO`, `sat_toDistFO`, `drank_toDistFO` — all
landed in `Reduction.lean`), the colored/uncolored seam (`L = 0`,
every `Coloring n 0` is admissible and the statement quantifies over
it), the encoding-length seam in the needed direction (Part 2), and
the binder-order discipline (constants before inputs, throughout). -/

end Lax3Proofs.Headline
