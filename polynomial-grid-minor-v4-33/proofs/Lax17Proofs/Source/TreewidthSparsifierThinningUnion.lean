import Lax17Proofs.Source.TreewidthSparsifierTheorem51Thinning

namespace Lax17Proofs

universe u v w

/-!
# The finite Karger union bound for blue thinning

This module isolates the deterministic counting form of the probabilistic
argument in Step 3 of Chekuri--Chuzhoy Theorem 5.1.  Cuts are grouped by the
integer quotient of their size by the edge-connectivity.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51
namespace ThinningUnion

open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph
open Karger


variable {W : Type u} [Fintype W] [DecidableEq W]
variable {Ω : Type v} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- All oriented nontrivial vertex cuts. -/
noncomputable def nontrivialCuts : Finset (Finset W) := by
  classical
  exact Finset.univ.filter fun S =>
    S.Nonempty ∧ S ≠ Finset.univ

@[simp] theorem mem_nontrivialCuts (S : Finset W) :
    S ∈ (nontrivialCuts : Finset (Finset W)) ↔
      S.Nonempty ∧ S ≠ Finset.univ := by
  classical
  simp [nontrivialCuts]

/-- The outcomes that lose more than the prescribed `1/r` fraction of one
fixed cut. -/
noncomputable def badForCut
    (Q : FiniteEdgeIndexedGraph W)
    (Q' : Ω → FiniteEdgeIndexedGraph W)
    (r : ℕ) (S : Finset W) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω =>
    ((Q' ω).boundary S).card < (Q.boundary S).card / r

@[simp] theorem mem_badForCut
    (Q : FiniteEdgeIndexedGraph W)
    (Q' : Ω → FiniteEdgeIndexedGraph W)
    (r : ℕ) (S : Finset W) (ω : Ω) :
    ω ∈ badForCut Q Q' r S ↔
      ((Q' ω).boundary S).card < (Q.boundary S).card / r := by
  classical
  simp [badForCut]

/-- Nontrivial cuts whose size divided by `C` is exactly `a`. -/
noncomputable def scaleCuts
    (Q : FiniteEdgeIndexedGraph W) (C a : ℕ) :
    Finset (Finset W) := by
  classical
  exact nontrivialCuts.filter fun S =>
    (Q.boundary S).card / C = a

@[simp] theorem mem_scaleCuts
    (Q : FiniteEdgeIndexedGraph W) (C a : ℕ) (S : Finset W) :
    S ∈ scaleCuts Q C a ↔
      S.Nonempty ∧ S ≠ Finset.univ ∧
        (Q.boundary S).card / C = a := by
  classical
  simp [scaleCuts, and_assoc]

/-- The union of bad outcomes over one cut-size scale. -/
noncomputable def badAtScale
    (Q : FiniteEdgeIndexedGraph W)
    (Q' : Ω → FiniteEdgeIndexedGraph W)
    (C r a : ℕ) : Finset Ω := by
  classical
  exact (scaleCuts Q C a).biUnion (badForCut Q Q' r)

/-- The union of bad outcomes over all nontrivial cuts. -/
noncomputable def allBad
    (Q : FiniteEdgeIndexedGraph W)
    (Q' : Ω → FiniteEdgeIndexedGraph W)
    (r : ℕ) : Finset Ω := by
  classical
  exact nontrivialCuts.biUnion (badForCut Q Q' r)

/-- A scale class is contained in the cumulative family counted by Karger. -/
theorem scaleCuts_subset_smallCuts
    (Q : FiniteEdgeIndexedGraph W) {C a : ℕ}
    (hC : 0 < C) :
    scaleCuts Q C a ⊆ smallCuts Q C (a + 1) := by
  intro S hS
  have hm := (mem_scaleCuts Q C a S).mp hS
  apply (mem_smallCuts Q C (a + 1) S).mpr
  refine ⟨hm.1, hm.2.1, ?_⟩
  have hmod := Nat.mod_lt (Q.boundary S).card hC
  have hdiv := Nat.mod_add_div (Q.boundary S).card C
  rw [hm.2.2] at hdiv
  exact Nat.le_of_lt <| calc
    (Q.boundary S).card =
        (Q.boundary S).card % C + C * a := hdiv.symm
    _ < C + C * a := Nat.add_lt_add_right hmod _
    _ = (a + 1) * C := by
      rw [Nat.mul_comm (a + 1) C, Nat.mul_add]
      simp
      ac_rfl

theorem card_scaleCuts_le_smallCuts
    (Q : FiniteEdgeIndexedGraph W) {C a : ℕ}
    (hC : 0 < C) :
    (scaleCuts Q C a).card ≤
      (smallCuts Q C (a + 1)).card :=
  Finset.card_le_card (scaleCuts_subset_smallCuts Q hC)

/-- Elementary natural-number division bookkeeping used at every scale. -/
theorem mul_div_le_div_of_mul_le
    {c d p N : ℕ} (hp : 0 < p) (hd : 0 < d)
    (hcd : c * d ≤ p) :
    c * (N / p) ≤ N / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  calc
    c * (N / p) * d = (N / p) * (c * d) := by ac_rfl
    _ ≤ (N / p) * p := Nat.mul_le_mul_left _ hcd
    _ ≤ N := Nat.div_mul_le_self _ _

/-- The fixed-cut lower-tail estimates combine with a cut-count/failure-factor
capacity bound to control one complete scale. -/
theorem card_badAtScale_le
    (Q : FiniteEdgeIndexedGraph W)
    (Q' : Ω → FiniteEdgeIndexedGraph W)
    {C r a : ℕ}
    (hC : 0 < C) (hr : 0 < r)
    (htail :
      ∀ S ∈ nontrivialCuts,
        (badForCut Q Q' r S).card *
            4 ^ ((Q.boundary S).card / r + 1) ≤
          Fintype.card Ω)
    (hcapacity :
      (scaleCuts Q C a).card * 2 ^ (a + 2) ≤
        4 ^ ((a * C) / r + 1)) :
    (badAtScale Q Q' C r a).card ≤
      Fintype.card Ω / 2 ^ (a + 2) := by
  classical
  let P : ℕ := 4 ^ ((a * C) / r + 1)
  have hP : 0 < P := by
    exact pow_pos (by norm_num) _
  have hd : 0 < 2 ^ (a + 2) := pow_pos (by norm_num) _
  have hpiece :
      ∀ S ∈ scaleCuts Q C a,
        (badForCut Q Q' r S).card ≤ Fintype.card Ω / P := by
    intro S hS
    have hmem := (mem_scaleCuts Q C a S).mp hS
    have hmul := htail S
      ((mem_nontrivialCuts S).mpr ⟨hmem.1, hmem.2.1⟩)
    have hmulScale :
        a * C ≤ (Q.boundary S).card := by
      have := Nat.mul_div_le (Q.boundary S).card C
      simpa [hmem.2.2, Nat.mul_comm] using this
    have hpow :
        P ≤ 4 ^ ((Q.boundary S).card / r + 1) := by
      apply Nat.pow_le_pow_right (by norm_num)
      exact Nat.add_le_add_right
        (Nat.div_le_div_right hmulScale) 1
    apply (Nat.le_div_iff_mul_le hP).2
    exact (Nat.mul_le_mul_left _ hpow).trans hmul
  calc
    (badAtScale Q Q' C r a).card ≤
        ∑ S ∈ scaleCuts Q C a,
          (badForCut Q Q' r S).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ scaleCuts Q C a, Fintype.card Ω / P :=
      Finset.sum_le_sum hpiece
    _ = (scaleCuts Q C a).card * (Fintype.card Ω / P) := by
      simp [Nat.mul_comm]
    _ = (scaleCuts Q C a).card * (Fintype.card Ω / P) := rfl
    _ ≤ Fintype.card Ω / 2 ^ (a + 2) :=
      mul_div_le_div_of_mul_le hP hd hcapacity

/-- Every nontrivial cut belongs to a positive scale bounded by the total
number of named edges. -/
theorem scale_mem_Ico
    (Q : FiniteEdgeIndexedGraph W) {C : ℕ}
    (hC : 0 < C) (hconn : Q.IsEdgeConnected C)
    (S : Finset W) (hS : S ∈ nontrivialCuts) :
    (Q.boundary S).card / C ∈
      Finset.Ico 1 (Fintype.card Q.Edge + 1) := by
  have hm := (mem_nontrivialCuts S).mp hS
  have hmin := hconn S hm.1 hm.2
  have hpos : 0 < (Q.boundary S).card / C :=
    Nat.div_pos hmin hC
  have hboundary :
      (Q.boundary S).card ≤ Fintype.card Q.Edge := by
    simpa using Finset.card_le_univ (Q.boundary S)
  have hscale :
      (Q.boundary S).card / C ≤ Fintype.card Q.Edge := by
    exact (Nat.div_le_self _ _).trans hboundary
  exact Finset.mem_Ico.mpr ⟨hpos, by omega⟩

/-- If every scale has the geometric bound above, one outcome preserves all
nontrivial quotient cuts simultaneously. -/
theorem exists_outcome_preserving_all_cuts
    (Q : FiniteEdgeIndexedGraph W)
    (Q' : Ω → FiniteEdgeIndexedGraph W)
    {C r : ℕ}
    (hC : 0 < C) (hr : 0 < r)
    (hconn : Q.IsEdgeConnected C)
    (htail :
      ∀ S ∈ nontrivialCuts,
        (badForCut Q Q' r S).card *
            4 ^ ((Q.boundary S).card / r + 1) ≤
          Fintype.card Ω)
    (hcapacity :
      ∀ a, 0 < a →
        (scaleCuts Q C a).card * 2 ^ (a + 2) ≤
          4 ^ ((a * C) / r + 1)) :
    ∃ ω : Ω, ∀ S : Finset W,
      S.Nonempty → S ≠ Finset.univ →
        (Q.boundary S).card / r ≤
          ((Q' ω).boundary S).card := by
  classical
  let scales := Finset.Ico 1 (Fintype.card Q.Edge + 1)
  let U : Finset Ω :=
    scales.biUnion fun a => badAtScale Q Q' C r a
  have hallSubset : allBad Q Q' r ⊆ U := by
    intro ω hω
    rcases Finset.mem_biUnion.mp hω with ⟨S, hS, hωS⟩
    let a := (Q.boundary S).card / C
    have haRange := scale_mem_Ico Q hC hconn S hS
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haRange, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, hωS⟩
    exact (mem_scaleCuts Q C a S).mpr
      ⟨(mem_nontrivialCuts S).mp hS |>.1,
        (mem_nontrivialCuts S).mp hS |>.2, rfl⟩
  have hUcard :
      U.card ≤
        ∑ a ∈ scales, Fintype.card Ω / 2 ^ (a + 2) := by
    calc
      U.card ≤ ∑ a ∈ scales,
          (badAtScale Q Q' C r a).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ a ∈ scales, Fintype.card Ω / 2 ^ (a + 2) := by
        apply Finset.sum_le_sum
        intro a ha
        have haPos : 0 < a := (Finset.mem_Ico.mp ha).1
        exact card_badAtScale_le Q Q' hC hr htail
          (hcapacity a haPos)
  have hgeom :
      (∑ a ∈ scales, Fintype.card Ω / 2 ^ (a + 2)) ≤
        Fintype.card Ω / 4 := by
    have heq :
        ∀ a,
          Fintype.card Ω / 2 ^ (a + 2) =
            (Fintype.card Ω / 4) / 2 ^ a := by
      intro a
      rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [pow_add]
      norm_num
      ac_rfl
    simp_rw [heq]
    simpa [scales] using
      (Nat.geom_sum_Ico_le (b := 2) (by norm_num)
        (Fintype.card Ω / 4) (Fintype.card Q.Edge + 1))
  have hAllCard :
      (allBad Q Q' r).card < Fintype.card Ω := by
    have hle :
        (allBad Q Q' r).card ≤ Fintype.card Ω / 4 :=
      (Finset.card_le_card hallSubset).trans (hUcard.trans hgeom)
    have hΩpos : 0 < Fintype.card Ω := Fintype.card_pos
    have hdiv : Fintype.card Ω / 4 < Fintype.card Ω := by
      exact Nat.div_lt_self hΩpos (by norm_num)
    exact hle.trans_lt hdiv
  have hexists :
      ∃ ω : Ω, ω ∉ allBad Q Q' r := by
    by_contra h
    push Not at h
    have huniv : (Finset.univ : Finset Ω) ⊆ allBad Q Q' r :=
      fun ω _ => h ω
    have hcard : Fintype.card Ω ≤ (allBad Q Q' r).card := by
      simpa using Finset.card_le_card huniv
    exact (Nat.not_lt_of_ge hcard) hAllCard
  rcases hexists with ⟨ω, hω⟩
  refine ⟨ω, ?_⟩
  intro S hS hproper
  by_contra hbad
  have hlt :
      ((Q' ω).boundary S).card <
        (Q.boundary S).card / r := by omega
  apply hω
  apply Finset.mem_biUnion.mpr
  refine ⟨S, (mem_nontrivialCuts S).mpr ⟨hS, hproper⟩, ?_⟩
  exact (mem_badForCut Q Q' r S ω).mpr hlt

/-- Generic finite Karger union bound.  Unlike
`exists_outcome_preserving_all_cuts`, the bad event need not be the boundary
of another graph.  This is used for carrier-clean physical chunks, whose
canonical representative may depend on the cut. -/
theorem exists_outcome_avoiding_all_cut_badSets
    (Q : FiniteEdgeIndexedGraph W)
    {C r : ℕ}
    (hC : 0 < C) (hr : 0 < r)
    (hconn : Q.IsEdgeConnected C)
    (bad : Finset W → Finset Ω)
    (htail :
      ∀ S ∈ nontrivialCuts,
        (bad S).card *
            4 ^ ((Q.boundary S).card / r + 1) ≤
          Fintype.card Ω)
    (hcapacity :
      ∀ a, 0 < a →
        (scaleCuts Q C a).card * 2 ^ (a + 2) ≤
          4 ^ ((a * C) / r + 1)) :
    ∃ ω : Ω, ∀ S : Finset W,
      S.Nonempty → S ≠ Finset.univ → ω ∉ bad S := by
  classical
  let badAt (a : ℕ) : Finset Ω :=
    (scaleCuts Q C a).biUnion bad
  have hbadAt :
      ∀ a, 0 < a →
        (badAt a).card ≤
          Fintype.card Ω / 2 ^ (a + 2) := by
    intro a ha
    let F : ℕ := 4 ^ ((a * C) / r + 1)
    have hF : 0 < F := pow_pos (by norm_num) _
    have hd : 0 < 2 ^ (a + 2) := pow_pos (by norm_num) _
    have hpiece :
        ∀ S ∈ scaleCuts Q C a,
          (bad S).card ≤ Fintype.card Ω / F := by
      intro S hS
      have hmem := (mem_scaleCuts Q C a S).mp hS
      have hmul :=
        htail S
          ((mem_nontrivialCuts S).mpr
            ⟨hmem.1, hmem.2.1⟩)
      have hmulScale :
          a * C ≤ (Q.boundary S).card := by
        have hdiv := Nat.mul_div_le (Q.boundary S).card C
        simpa [hmem.2.2, Nat.mul_comm] using hdiv
      have hpow :
          F ≤ 4 ^ ((Q.boundary S).card / r + 1) := by
        apply Nat.pow_le_pow_right (by norm_num)
        exact Nat.add_le_add_right
          (Nat.div_le_div_right hmulScale) 1
      apply (Nat.le_div_iff_mul_le hF).2
      exact (Nat.mul_le_mul_left _ hpow).trans hmul
    calc
      (badAt a).card ≤
          ∑ S ∈ scaleCuts Q C a, (bad S).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ scaleCuts Q C a,
          Fintype.card Ω / F :=
        Finset.sum_le_sum hpiece
      _ = (scaleCuts Q C a).card *
          (Fintype.card Ω / F) := by
        simp [Nat.mul_comm]
      _ ≤ Fintype.card Ω / 2 ^ (a + 2) := by
        exact mul_div_le_div_of_mul_le hF hd
          (hcapacity a ha)
  let scales := Finset.Ico 1 (Fintype.card Q.Edge + 1)
  let allBad : Finset Ω :=
    nontrivialCuts.biUnion bad
  let U : Finset Ω :=
    scales.biUnion badAt
  have hallSubset : allBad ⊆ U := by
    intro ω hω
    rcases Finset.mem_biUnion.mp hω with ⟨S, hS, hωS⟩
    let a := (Q.boundary S).card / C
    have haRange := scale_mem_Ico Q hC hconn S hS
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haRange, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, hωS⟩
    exact (mem_scaleCuts Q C a S).mpr
      ⟨(mem_nontrivialCuts S).mp hS |>.1,
        (mem_nontrivialCuts S).mp hS |>.2, rfl⟩
  have hUcard :
      U.card ≤
        ∑ a ∈ scales, Fintype.card Ω / 2 ^ (a + 2) := by
    calc
      U.card ≤ ∑ a ∈ scales, (badAt a).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ a ∈ scales,
          Fintype.card Ω / 2 ^ (a + 2) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hbadAt a (Finset.mem_Ico.mp ha).1
  have hgeom :
      (∑ a ∈ scales, Fintype.card Ω / 2 ^ (a + 2)) ≤
        Fintype.card Ω / 4 := by
    have heq :
        ∀ a,
          Fintype.card Ω / 2 ^ (a + 2) =
            (Fintype.card Ω / 4) / 2 ^ a := by
      intro a
      rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [pow_add]
      norm_num
      ac_rfl
    simp_rw [heq]
    simpa [scales] using
      (Nat.geom_sum_Ico_le (b := 2) (by norm_num)
        (Fintype.card Ω / 4) (Fintype.card Q.Edge + 1))
  have hAllCard : allBad.card < Fintype.card Ω := by
    have hle : allBad.card ≤ Fintype.card Ω / 4 :=
      (Finset.card_le_card hallSubset).trans (hUcard.trans hgeom)
    exact hle.trans_lt
      (Nat.div_lt_self Fintype.card_pos (by norm_num))
  have hexists : ∃ ω : Ω, ω ∉ allBad := by
    by_contra h
    push Not at h
    have huniv : (Finset.univ : Finset Ω) ⊆ allBad :=
      fun ω _ => h ω
    have hcard : Fintype.card Ω ≤ allBad.card := by
      simpa using Finset.card_le_card huniv
    exact (Nat.not_lt_of_ge hcard) hAllCard
  rcases hexists with ⟨ω, hω⟩
  refine ⟨ω, ?_⟩
  intro S hS hproper hbad
  apply hω
  exact Finset.mem_biUnion.mpr
    ⟨S, (mem_nontrivialCuts S).mpr ⟨hS, hproper⟩, hbad⟩

end ThinningUnion
end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
