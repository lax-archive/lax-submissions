import Lax457868Proofs.RefinedRoundLoop
import Lax457868Proofs.RefinedProgramSource

/-! Reconstruct the order from an initial full-neighborhood quotient. -/

namespace Lax457868Proofs.RefinedReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrders
open Lax457868Proofs.ReusedOriginal.Construction.Reconstruction
open Lax457868Proofs.ReusedOriginal.Construction.RecordedHistory
open Lax457868Proofs.ReusedOriginal.Construction.Correctness
open Lax457868Proofs.ReusedOriginal.Construction.ListCrossing
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.ReusedOriginal.Construction.ReconstructionSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys

/-- A certified order for one representative of every original neighborhood
is an order for the whole graph with the same crossing bound. -/
lemma certifiedRun_encodes_cover {n k q rounds bound : ℕ}
    {G : SimpleGraph (Fin n)} {C : Set (Fin n)}
    {l : List (Fin n)}
    (h : CertifiedRun G k q rounds Set.univ C l)
    (hcover : ∀ v : Fin n, ∃ b ∈ C, G.neighborSet v = G.neighborSet b)
    (hkq : 2 * k ≤ q) (hbound : (rounds + 1) * q ≤ bound) :
    EncodesGraphWelzlOrder G 1 bound (l.map Fin.val) := by
  have henum := h.enumerates G
  have hl : l.Nodup := henum.1
  have hall : ∀ v : Fin n, v ∈ l := fun v => by
    simpa using (henum.2 v).mpr (Set.mem_univ v)
  have hlen : l.length = n := by
    rw [henum.length_eq_ncard]
    simp
  let π := Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding.permutationOfList
    l hl hall hlen
  refine ⟨π, ?_, ?_⟩
  · exact Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding.map_val_eq_ofFn
      l hl hall hlen
  · unfold IsWelzlOrder
    apply Lax457868Proofs.ReusedOriginal.Construction.Crossing.crossingNumber_le_of_forall
    intro X hX
    rw [Lax457868Proofs.ReusedOriginal.Construction.GraphNeighborhood.neighborhoodSetSystem_one] at hX
    obtain ⟨v, rfl⟩ := hX
    obtain ⟨b, hb, hne⟩ := hcover v
    rw [hne]
    rw [Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding.crossingCount_permutationOfList]
    exact (h.crossingCount_le G hkq b hb).trans hbound

end Lax457868Proofs.RefinedReconstruction







namespace Lax457868Proofs.RefinedReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult

private lemma array_eq_arrOf_view {σ : Env} {a : String} {n : ℕ}
    (hlen : (σ.arrs a).length = n) :
    σ.arrs a = arrOf n (view σ a) := by
  apply List.ext_getElem
  · simpa [length_arrOf] using hlen
  · intro i hi hj
    simp [view, getElem_arrOf, List.getD_eq_getElem?_getD, hi]

private lemma numeric_ncard_eq {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) :
    (finSetAsSet (n := n) S).ncard = S.card := by
  have himage : Fin.val '' (finSetAsSet (n := n) S) = (S : Set ℕ) := by
    ext i
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hi
      exact ⟨⟨i, Finset.mem_range.mp (hS hi)⟩, hi, rfl⟩
  have h := Set.ncard_image_of_injective (finSetAsSet (n := n) S) Fin.val_injective
  rw [himage, Set.ncard_coe_finset] at h
  exact h.symm

private lemma view_mem {σ : Env} {a : String} {i : ℕ}
    (hi : i < (σ.arrs a).length) : view σ a i ∈ σ.arrs a := by
  simpa [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using
    (List.getElem_mem hi)

end Lax457868Proofs.RefinedReconstruction

namespace Lax457868Proofs.RefinedReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WelzlOrdersInGraphs
open Lax457868Proofs.ReusedOriginal.Construction.Reconstruction
open Lax457868Proofs.ReusedOriginal.Construction.RecordedHistory
open Lax457868Proofs.ReusedOriginal.Construction.ReconstructionSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys

/-- Literal reconstruction from a recorded history whose initial neighborhood
side covers every full graph neighborhood. -/
lemma history_reconstructAndWrite_cover {B n k q R bound : ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {A C : ℕ → Set (Fin n)}
    {boundary starts ends removed repAt active next : ℕ → ℕ}
    (h : History G k R A C boundary removed repAt)
    (hA : A 0 = Set.univ)
    (hC : ∀ v : Fin n, ∃ b ∈ C 0,
      ∀ a : Fin n, G.Adj v a ↔ G.Adj b a)
    (hterminal : A R = {v : Fin n | active v.val = 1})
    (hsmall : (A R).ncard ≤ q) (hkq : 2 * k ≤ q)
    (hcross : (R + 1) * q ≤ bound)
    (hn : σ.vars "n" = n) (hround : σ.vars "round" = R)
    (hRn : R ≤ n) (hnB : n < B) (hout : σ.out = [])
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hstarts : σ.arrs "roundStart" = arrOf n starts)
    (hends : σ.arrs "roundEnd" = arrOf n ends)
    (hremoved : σ.arrs "removed" = arrOf n removed)
    (hreps : σ.arrs "removedRep" = arrOf n repAt)
    (hstartVals : ∀ r < R, starts r = boundary r)
    (hendVals : ∀ r < R, ends r = boundary (r + 1))
    (hmono : ∀ r < R, boundary r ≤ boundary (r + 1))
    (hcap : ∀ r ≤ R, boundary r ≤ n)
    (hremN : ∀ i < n, removed i < n)
    (hrepN : ∀ i < n, repAt i < n)
    (hactiveB : ∀ i < n, active i < B)
    (hnextB : ∀ i < n, next i < B)
    (hnonempty : 0 < n → scanList active 0 n ≠ []) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      EncodesGraphWelzlOrder G 1 bound τ.out ∧ τ.inp = σ.inp := by
  have henum : Enumerates (A R) (activeFinList active) := by
    rw [hterminal]
    exact activeFinList_enumerates active
  obtain ⟨orders, hlast, ⟨hlog⟩, hcert⟩ := h.reconstruct henum hsmall
  have hcert' : CertifiedRun G k q R Set.univ (C 0) (orders 0) := by
    simpa [hA] using hcert
  have hlen : ((orders 0).map Fin.val).length = n := by
    rw [List.length_map, (hcert'.enumerates G).length_eq_ncard]
    simp
  have hbase : (orders R).map Fin.val = scanList active 0 n := by
    rw [hlast, activeFinList_map_val]
  obtain ⟨τ, hrun, houtput, hinput⟩ := reconstructAndWrite_run hn hround hRn hnB
    hactive hnext hstarts hends hremoved hreps hstartVals hendVals hmono hcap
    hremN hrepN hactiveB hnextB hbase hnonempty hlog hlen
    (by intro v hv; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv; exact v.isLt)
  refine ⟨τ, hrun, ?_, hinput⟩
  rw [houtput, hout, List.nil_append]
  have hcover : ∀ v : Fin n, ∃ b ∈ C 0,
      G.neighborSet v = G.neighborSet b := by
    intro v
    obtain ⟨b, hb, heq⟩ := hC v
    refine ⟨b, hb, ?_⟩
    ext a
    exact heq a
  exact certifiedRun_encodes_cover hcert' hcover hkq hcross

end Lax457868Proofs.RefinedReconstruction

namespace Lax457868Proofs.RefinedReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundSource
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionRefinementStep

/-- The terminal factual round state supplies every array and log premise of
the literal reconstruction source. -/
lemma reconstruct_from_stored {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {A C : Finset ℕ} {σ : Env}
    (D : RoundData c n x A C σ) (hA : A ⊆ Finset.range n)
    (S : Stored G (refinedCutoffK c) σ)
    (hbounded : ValuesBounded B σ)
    (hsmall : A.card ≤ 2 * refinedCutoffK c)
    (hroundLog : σ.vars "round" + 1 ≤ Nat.clog 2 n)
    (hpositive : 0 < A.card)
    (hnB : n < B) (hout : σ.out = []) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1
        (2 * refinedCutoffK c * Nat.clog 2 n) τ.out ∧
      τ.inp = σ.inp := by
  classical
  let k := refinedCutoffK c
  let active := view σ "activeA"
  let next := view σ "nextVertex"
  let starts := view σ "roundStart"
  let ends := view σ "roundEnd"
  let removed := view σ "removed"
  let repAt := view σ "removedRep"
  have hlength (a : String) (hoff : a ≠ "off") (htgt : a ≠ "tgt")
      (hcount : a ≠ "count") : (σ.arrs a).length = n := by
    simpa [welzlExt, hoff, htgt, hcount] using D.lengths a
  have hactive : σ.arrs "activeA" = arrOf n active :=
    array_eq_arrOf_view (hlength "activeA" (by decide) (by decide) (by decide))
  have hnext : σ.arrs "nextVertex" = arrOf n next :=
    array_eq_arrOf_view (hlength "nextVertex" (by decide) (by decide) (by decide))
  have hstarts : σ.arrs "roundStart" = arrOf n starts :=
    array_eq_arrOf_view (hlength "roundStart" (by decide) (by decide) (by decide))
  have hends : σ.arrs "roundEnd" = arrOf n ends :=
    array_eq_arrOf_view (hlength "roundEnd" (by decide) (by decide) (by decide))
  have hremoved : σ.arrs "removed" = arrOf n removed :=
    array_eq_arrOf_view (hlength "removed" (by decide) (by decide) (by decide))
  have hreps : σ.arrs "removedRep" = arrOf n repAt :=
    array_eq_arrOf_view (hlength "removedRep" (by decide) (by decide) (by decide))
  have hterminal : S.A (σ.vars "round") = finSetAsSet A := by
    rw [S.currentA]
    ext v
    change view σ "activeA" v.val = 1 ↔ v.val ∈ A
    rw [view_of_array D.activeA v.isLt]
    simp [setFlag]
  have hsmall' : (S.A (σ.vars "round")).ncard ≤ 2 * k := by
    rw [hterminal, numeric_ncard_eq hA]
    exact hsmall
  have hcross : (σ.vars "round" + 1) * (2 * k) ≤
      2 * k * Nat.clog 2 n := by
    calc
      _ ≤ (Nat.clog 2 n) * (2 * k) := Nat.mul_le_mul_right _ hroundLog
      _ = _ := by ring
  have hroundN : σ.vars "round" ≤ n := by
    have hle : Nat.clog 2 n ≤ n :=
      (Nat.clog_le_iff_le_pow (by decide)).2 n.lt_two_pow_self.le
    omega
  have hactiveB : ∀ i < n, active i < B := by
    intro i hi
    exact hbounded.arrays "activeA" _
      (view_mem (by simpa [hlength "activeA" (by decide) (by decide) (by decide)] using hi))
  have hnextB : ∀ i < n, next i < B := by
    intro i hi
    exact hbounded.arrays "nextVertex" _
      (view_mem (by simpa [hlength "nextVertex" (by decide) (by decide) (by decide)] using hi))
  have hnonempty : 0 < n → scanList active 0 n ≠ [] := by
    intro _ he
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpositive
    have hvn := Finset.mem_range.mp (hA hv)
    have hav : active v = 1 := by
      change view σ "activeA" v = 1
      rw [view_of_array D.activeA hvn]
      simp [setFlag, hv]
    have hmem : v ∈ scanList active 0 n :=
      mem_scanList.mpr ⟨by omega, by omega, hav⟩
    rw [he] at hmem
    exact List.not_mem_nil hmem
  exact history_reconstructAndWrite_cover S.history S.initialA S.initialC
    (by simpa only [hterminal] using S.currentA)
    hsmall' (by simp [k]) hcross D.vertices rfl hroundN hnB hout
    hactive hnext hstarts hends hremoved hreps
    S.starts S.ends
    (by intro r hr; exact S.monotone r (r + 1) (by omega) (by omega))
    S.capacity S.removedBound S.representativeBound hactiveB hnextB hnonempty

end Lax457868Proofs.RefinedReconstruction

namespace Lax457868Proofs.RefinedReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedProgramSource
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- A positive terminal active count takes the actual reconstruction arm of
the fixed finish command and yields the required graph order. -/
lemma finishRefined_positive_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ : Env}
    (hready : LoopReady B c G x rest σ)
    (hpositive : 0 < σ.vars "acount")
    (hsmall : σ.vars "acount" ≤ 2 * refinedCutoffK c)
    (hnB : n < B) :
    ∃ τ, Run B finishRefined σ τ
      (1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1)) ∧
      Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1
        (2 * refinedCutoffK c * Nat.clog 2 n) τ.out := by
  obtain ⟨A, C, bits, sizes, D, hA, hCsub, hC, hsep, ⟨S⟩,
    hbounded, hcap, hroundCap, hacount, hlen, hsum, hpot,
    hroundLog, hout, hinput, htape⟩ := hready
  have hguard : (Cond.eq (.var "acount") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var (hbounded.vars "acount"))
      (evalB_lit (by omega : 0 < B))]
    simp [show σ.vars "acount" ≠ 0 by omega]
  obtain ⟨τ, hr, hcorrect, _⟩ := reconstruct_from_stored D hA S hbounded
    (by omega : A.card ≤ 2 * refinedCutoffK c) hroundLog
    (by omega : 0 < A.card) hnB hout
  exact ⟨τ, by simpa [finishRefined] using Run.ite_false hguard hr, hcorrect⟩

end Lax457868Proofs.RefinedReconstruction

namespace Lax457868Proofs.RefinedReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedProgramSource
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundInput
open Lax457868Proofs.RefinedRecordedCommit
open Lax457868Proofs.InitialNeighborhoodQuotient
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlStraight

set_option maxRecDepth 6000

/-- The large-input branch executes the quotient, literal outer loop, and
one of the two fixed finish arms. Every non-failing run reconstructs a valid
order; retry failure remains explicit as `acount = 0`. -/
lemma algorithmBody_large_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {bits : List Bool} {σ : Env}
    (R : Lax457868Proofs.RefinedSetup.Ready c n x
      (bits.map Bool.toNat ++ rest) σ)
    (hbounded : ValuesBounded B σ)
    (hx : Lax11.GraphEncoding.EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 2 ≤ c) (hn2 : 2 ≤ n)
    (hB : 4 * (x.length + 1) ≤ B)
    (hlargeN : 2 * refinedCutoffK c < n)
    (htape : n * Lax457868Proofs.RefinedTapeReserve.roundBitReserve c n ≤ bits.length) :
    ∃ τ K, Run B algorithmBody σ τ K ∧
      (Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1
          (2 * refinedCutoffK c * Nat.clog 2 n) τ.out ∨
        τ.vars "acount" = 0) := by
  have hnB : n < B := by
    have hlen := hx.length_eq
    omega
  have hguard : (Cond.lt (.var "cutoffResult") (.var "acount")).evalB B σ =
      some true := by
    have hcut : σ.vars "cutoffResult" = 2 * refinedCutoffK c := by
      rw [R.cutoff, Nat.min_eq_right hlargeN.le]
    rw [evalB_condLt
      (evalB_var (by rw [hcut]; omega : σ.vars "cutoffResult" < B))
      (evalB_var (by rw [R.activeCount]; exact hnB))]
    simp [hcut, R.activeCount, hlargeN]
  obtain ⟨ρ, C, hquot, D, hCsub, hC, htrace, _, _, _, _⟩ :=
    initialQuotientSource_run R hx hn2 hlargeN hB
  have hready : LoopReady B c G x rest ρ :=
    initial_loopReady R hbounded hquot D hn2 hCsub hC htrace htape
  obtain ⟨υ, Kloop, hloop, hnυ, hresult⟩ :=
    round_while_run hx hG hc hB hlargeN hready
  have hprefix : Run B (seqs [initialQuotientSource,
      .while roundGuard Lax457868Proofs.RefinedRoundDriver.preparedRefinedRoundSource])
      σ υ (951 * (x.length + 1) + Kloop) := by
    simpa [seqs] using hquot.seq hloop
  by_cases hzero : υ.vars "acount" = 0
  · have hguard0 : (Cond.eq (.var "acount") (.lit 0)).evalB B υ = some true := by
      rw [evalB_condEq
        (evalB_var (by rw [hzero]; omega : υ.vars "acount" < B))
        (evalB_lit (by omega : 0 < B))]
      simp [hzero]
    obtain ⟨τ, hwrite, _⟩ := writeNaturalOrder_run hnυ hnB
    have hfinish : Run B finishRefined υ τ
        (1 + (Cond.eq (.var "acount") (.lit 0)).size + (10 * n + 6)) := by
      simpa [finishRefined] using Run.ite_true hguard0 hwrite
    have hseq : Run B (seqs [initialQuotientSource,
        .while roundGuard Lax457868Proofs.RefinedRoundDriver.preparedRefinedRoundSource,
        finishRefined]) σ τ
        (951 * (x.length + 1) + Kloop +
          (1 + (Cond.eq (.var "acount") (.lit 0)).size + (10 * n + 6))) := by
      simpa [seqs, Nat.add_assoc] using hquot.seq (hloop.seq hfinish)
    refine ⟨τ, 1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size +
      (951 * (x.length + 1) + Kloop +
        (1 + (Cond.eq (.var "acount") (.lit 0)).size + (10 * n + 6))), ?_, ?_⟩
    · simpa [algorithmBody, roundGuard] using Run.ite_true hguard hseq
    · right
      rw [hwrite.frame_var "acount" (by decide)]
      exact hzero
  · rcases hresult with hfail | ⟨hterminal, hsmall⟩
    · exact False.elim (hzero hfail)
    · have hpositive : 0 < υ.vars "acount" := by omega
      obtain ⟨τ, hfinish, hcorrect⟩ :=
        finishRefined_positive_run hterminal hpositive hsmall hnB
      have hseq : Run B (seqs [initialQuotientSource,
          .while roundGuard Lax457868Proofs.RefinedRoundDriver.preparedRefinedRoundSource,
          finishRefined]) σ τ
          (951 * (x.length + 1) + Kloop +
            (1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1))) := by
        simpa [seqs, Nat.add_assoc] using hquot.seq (hloop.seq hfinish)
      refine ⟨τ, 1 + (Cond.lt (.var "cutoffResult") (.var "acount")).size +
        (951 * (x.length + 1) + Kloop +
          (1 + (Cond.eq (.var "acount") (.lit 0)).size + 100 * (n + 1))), ?_, ?_⟩
      · simpa [algorithmBody, roundGuard] using Run.ite_true hguard hseq
      · exact Or.inl hcorrect

end Lax457868Proofs.RefinedReconstruction
