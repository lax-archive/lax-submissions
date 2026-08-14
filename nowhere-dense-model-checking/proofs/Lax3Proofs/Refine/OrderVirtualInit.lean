import Lax3Proofs.Refine.OrderVirtualProvider
import Lax3Proofs.Refine.SigmaLoop

/-!
# Initial degrees from regenerated rows

The first pass of virtual elimination calls the provider once per vertex and
stores the returned row cardinality as its degree.  No graph-sized edge array
is retained: the only row storage is `vrow`, of length `n`.
-/

namespace Lax3Proofs.Refine.OrderVirtualInit

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation (nbrsIn)
open Lax3Proofs.Refine.OrderVirtualProvider

/-- The degree of an in-range numeric vertex, extended by zero outside the
carrier. -/
noncomputable def virtualDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : ℕ) : ℕ :=
  if h : v < n then (nbrsIn G Finset.univ ⟨v, h⟩).card else 0

theorem virtualDegree_eq {n : ℕ} {G : SimpleGraph (Fin n)} {v : ℕ} (hv : v < n) :
    virtualDegree G v = (nbrsIn G Finset.univ (⟨v, hv⟩ : Fin n)).card := by
  simp [virtualDegree, hv]

/-- Prefix invariant for the initial degree pass. -/
def VirtualDegInv (n W : ℕ) (G : SimpleGraph (Fin n)) (P : Env → Prop)
    (σ : Env) : Prop :=
  P σ ∧ σ.vars "i" ≤ n ∧
    ∃ E D R ID BH BV BN,
      EngineArrays n W E D R ID BH BV BN σ ∧
      (∀ u < n, E u = 0) ∧
      (∀ u < σ.vars "i", D u = virtualDegree G u)

/-- One degree row: select `i`, regenerate its row, store the exact row
cardinality, and advance. -/
def virtualDegRow (provide : Com) : Com :=
  .seq (.assign "w" (.var "i"))
    (.seq provide
      (.seq (.store "deg" (.var "i") (.var "vtail"))
        (.assign "i" (.add (.var "i") (.lit 1)))))

/-- One regenerated row extends the initialized prefix by one. -/
theorem virtualDegRow_spec {B n W : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n W G P provide κ) (hclosed : EngineClosed P)
    (hB : n + W + 1 < B) {v : ℕ} (hv : v < n) :
    Spec B
      (fun σ => VirtualDegInv n W G P σ ∧ σ.vars "i" = v)
      (virtualDegRow provide)
      (fun _ σ' => VirtualDegInv n W G P σ' ∧ σ'.vars "i" = v + 1)
      (κ v + 9) := by
  intro σ hpre
  obtain ⟨⟨hP, hile, E, D, R, ID, BH, BV, BN, heng, hzero, hdone⟩, hiv⟩ := hpre
  have hvB : v < B := by omega
  have hiB : σ.vars "i" < B := by omega
  have hengW : EngineArrays n W E D R ID BH BV BN
      (σ.setVar "w" (σ.vars "i")) :=
    ⟨by simp [heng.n_eq], by simp [heng.elm_eq], by simp [heng.deg_eq],
      by simp [heng.rank_eq], by simp [heng.idg_eq], by simp [heng.head_eq],
      by simp [heng.val_eq], by simp [heng.next_eq]⟩
  run_vcg [hp ⟨v, hv⟩ E D R ID BH BV BN]
  · obtain ⟨hP', heng', hstable, tail, A, hrow, htail, hA⟩ := ‹_ ∧ _ ∧ _ ∧ ∃ _ _, _›
    have hi' := hstable.i_eq_after_w
    rw [hiv] at hi'
    have htailB : tail < B := lt_of_le_of_lt hrow.tail_le (by omega)
    have hiLen : v < (arrOf n D).length := by rw [length_arrOf]; exact hv
    have htailDeg : tail = virtualDegree G v := by
      rw [virtualDegree_eq hv]
      exact hrow.card_eq
    refine ⟨?_, by simp [hi']⟩
    refine ⟨?_, by simp [hi']; omega, E,
      upd D v tail, R, ID, BH, BV, BN, ?_, hzero, ?_⟩
    · apply hclosed.setVar (a := "i") (by simp [engineVarNames])
      apply hclosed.setArr (a := "deg") (by simp [engineArrNames])
      exact hP'
    · refine ⟨by simp [heng'.n_eq], by simp [heng'.elm_eq], ?_,
        by simp [heng'.rank_eq], by simp [heng'.idg_eq],
        by simp [heng'.head_eq], by simp [heng'.val_eq], by simp [heng'.next_eq]⟩
      simp [heng'.deg_eq, hi', htail, set_arrOf_eq_upd]
    · intro u hu
      simp [hi'] at hu
      rcases Nat.lt_or_eq_of_le (by omega : u ≤ v) with huv | rfl
      · rw [upd_of_ne _ (by omega)]
        exact hdone u (by omega)
      · rw [upd_self, htailDeg]
  · refine ⟨hclosed.setVar (a := "w") (by simp [engineVarNames]) hP, ?_, by simp [hiv]⟩
    exact hengW
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  all_goals
    try obtain ⟨hP', heng', hstable, tail, A, hrow, htail, hA⟩ := ‹_ ∧ _ ∧ _ ∧ ∃ _ _, _›
  all_goals try have hi' := hstable.i_eq_after_w
  all_goals try rw [hiv] at hi'
  all_goals try have htailB : tail < B := lt_of_le_of_lt hrow.tail_le (by omega)
  all_goals try have hdegLen' := heng'.deg_length
  all_goals omega

/-- Initialize every degree by regenerating every row once. -/
def virtualInitDeg (provide : Com) : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var "n")) (virtualDegRow provide))

/-- The full pass pays the sum of the actual provider charges. -/
theorem virtualInitDeg_spec {B n W : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n W G P provide κ) (hclosed : EngineClosed P)
    (hB : n + W + 1 < B) :
    Spec B
      (fun σ => P σ ∧
        ∃ E D R ID BH BV BN,
          EngineArrays n W E D R ID BH BV BN σ ∧ (∀ u < n, E u = 0))
      (virtualInitDeg provide)
      (fun _ σ' => VirtualDegInv n W G P σ' ∧ σ'.vars "i" = n)
      ((∑ k ∈ Finset.range n, (κ k + 13)) + 6) := by
  have hnB : n < B := by omega
  have hloop := Lax3Proofs.Refine.SigmaLoop.forRangeZeroSum
    "i" "n" (VirtualDegInv n W G P) n (fun k => κ k + 9) hnB
    (fun _ hI => hI.2.1)
    (fun _ hI => by
      obtain ⟨-, -, E, D, R, ID, BH, BV, BN, heng, -, -⟩ := hI
      exact heng.n_eq)
    (fun k hk => virtualDegRow_spec hp hclosed hB hk)
  intro σ hpre
  obtain ⟨hP, E, D, R, ID, BH, BV, BN, heng, hzero⟩ := hpre
  have heng0 : EngineArrays n W E D R ID BH BV BN (σ.setVar "i" 0) :=
    ⟨by simp [heng.n_eq], by simp [heng.elm_eq], by simp [heng.deg_eq],
      by simp [heng.rank_eq], by simp [heng.idg_eq], by simp [heng.head_eq],
      by simp [heng.val_eq], by simp [heng.next_eq]⟩
  have hI0 : VirtualDegInv n W G P (σ.setVar "i" 0) :=
    ⟨hclosed.setVar (a := "i") (by simp [engineVarNames]) hP, by simp,
      E, D, R, ID, BH, BV, BN, heng0, hzero, by simp⟩
  obtain ⟨σ', hrun, hI', hi'⟩ := hloop.run hI0
  exact ⟨σ', by simpa [virtualInitDeg] using hrun, hI', hi'⟩

/-- At the end of the degree pass the abstract Matula--Beck invariant is
initialized for the all-alive graph. -/
theorem elim_init_of_virtual_deg {n W : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {σ : Env}
    (hI : VirtualDegInv n W G P σ) (hi : σ.vars "i" = n) :
    ∃ E D R ID BH BV BN,
      EngineArrays n W E D R ID BH BV BN σ ∧
      Lax3Proofs.RamElim.Elim G (fun _ => 1) E D R ID 0 0 0 := by
  obtain ⟨-, -, E, D, R, ID, BH, BV, BN, heng, hzero, hdone⟩ := hI
  refine ⟨E, D, R, ID, BH, BV, BN, heng,
    Lax3Proofs.RamElim.Elim.init hzero ?_⟩
  intro v
  have hd := hdone (v : ℕ) (by rw [hi]; exact v.isLt)
  rw [virtualDegree_eq v.isLt] at hd
  rw [Lax3Proofs.RamElim.masked_of_all_alive G (by simp)]
  exact hd

/-! ## Axiom audit -/

#print axioms virtualDegRow_spec
#print axioms virtualInitDeg_spec
#print axioms elim_init_of_virtual_deg

end Lax3Proofs.Refine.OrderVirtualInit
