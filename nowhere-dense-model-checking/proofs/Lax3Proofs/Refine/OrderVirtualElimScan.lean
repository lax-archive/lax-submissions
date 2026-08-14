import Lax3Proofs.Refine.OrderVirtualRowRep

/-!
# Scanning an implicit row during greedy elimination

This is the first executable part of the virtual eliminator.  A row provider
has left one exact, duplicate-free row in `vrow[0..vtail)`.  The scan lowers
the degree of every still-uneliminated neighbour and uses the landed lazy
bucket push.  Its capacity invariant is local: enough room for the unscanned
suffix of this one row, never for all edges of the graph.
-/

namespace Lax3Proofs.Refine.OrderVirtualElimScan

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamElim (Buck)
open Lax3Proofs.Refine.OrderVirtualRowRep

variable {n : ℕ}

/-- One slot of a regenerated row. -/
def decVirtualSlot : Com :=
  .seq (.assign "u" (.get "vrow" (.var "j")))
    (.seq
      (.ite (.lt (.get "elm" (.var "u")) (.lit 1))
        (.seq
          (.store "deg" (.var "u")
            (.sub (.get "deg" (.var "u")) (.lit 1)))
          (.seq (.assign "d" (.get "deg" (.var "u")))
            (Lax3Proofs.RamElim.push "u")))
        .skip)
      (.assign "j" (.add (.var "j") (.lit 1))))

/-- The arrays fixed throughout a virtual decrement scan. -/
structure ScanArrays (n W tail : ℕ)
    (A E D R ID BH BV BN : ℕ → ℕ) (σ : Env) : Prop where
  n_eq : σ.vars "n" = n
  tail_eq : σ.vars "vtail" = tail
  row_eq : σ.arrs "vrow" = arrOf n A
  elm_eq : σ.arrs "elm" = arrOf n E
  deg_eq : σ.arrs "deg" = arrOf n D
  rank_eq : σ.arrs "rnk" = arrOf n R
  idg_eq : σ.arrs "idg" = arrOf n ID
  head_eq : σ.arrs "bh" = arrOf (n + 1) BH
  val_eq : σ.arrs "bv" = arrOf (n + W + 1) BV
  next_eq : σ.arrs "bn" = arrOf (n + W + 1) BN

/-- Scan invariant.  `D₀` is the degree array before the row: a vertex
already met in the prefix has fallen once, and every other cell is unchanged.
The last three clauses are exactly the linear-arena safety facts. -/
def ScanInv (n W tail sp₀ ls₀ : ℕ) (A E R ID D₀ : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ D BH BV BN,
    ScanArrays n W tail A E D R ID BH BV BN σ ∧
    Buck n n E D BH BV BN (σ.vars "sp") (σ.vars "ls") ∧
    (∀ u < n, E u ≤ 1) ∧
    (∀ u < n, D u < n) ∧
    (∀ u < n, Hit E A (σ.vars "j") u → D u = D₀ u - 1) ∧
    (∀ u < n, ¬ Hit E A (σ.vars "j") u → D u = D₀ u) ∧
    σ.vars "j" ≤ tail ∧
    σ.vars "sp" + (tail - σ.vars "j") < n + W + 1 ∧
    σ.vars "ls" + 1 ≤ σ.vars "sp" ∧
    σ.vars "sp" ≤ sp₀ + σ.vars "j" ∧
    σ.vars "ls" ≤ ls₀ + σ.vars "j"

/-- One duplicate-free row slot preserves the scan invariant. -/
theorem decVirtualSlot_run {B n W tail sp₀ ls₀ : ℕ} {G : SimpleGraph (Fin n)}
    {w : Fin n} {A E R ID D₀ : ℕ → ℕ} (hrow : RowRep G w tail A)
    (hB : n + W + 1 < B) {σ : Env}
    (hI : ScanInv n W tail sp₀ ls₀ A E R ID D₀ σ)
    (hjlt : σ.vars "j" < tail) :
    ∃ σ' K, Run B decVirtualSlot σ σ' K ∧ K ≤ 43 ∧
      ScanInv n W tail sp₀ ls₀ A E R ID D₀ σ' ∧
      σ'.vars "j" = σ.vars "j" + 1 := by
  obtain ⟨D, BH, BV, BN, harr, hbuck, hbit, hDlt, hhit, hmiss,
    hjle, hroom, hls, hspUsed, hlsUsed⟩ := hI
  obtain ⟨hn, htail, hrowA, helm, hdeg, hrnk, hidg, hbh, hbv, hbn⟩ := harr
  have hjn : σ.vars "j" < n := lt_of_lt_of_le hjlt hrow.tail_le
  have huN : A (σ.vars "j") < n := hrow.value_lt _ hjlt
  have hread : (σ.arrs "vrow").getD (σ.vars "j") 0 = A (σ.vars "j") := by
    rw [hrowA, getD_arrOf A hjn]
  have hread' : (σ.arrs "vrow")[σ.vars "j"]?.getD 0 = A (σ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]
    exact hread
  have hjlen : σ.vars "j" < (σ.arrs "vrow").length := by
    rw [hrowA, length_arrOf]
    exact hjn
  have huB : (σ.arrs "vrow").getD (σ.vars "j") 0 < B := by
    rw [hread]
    omega
  have helmLen : (σ.arrs "vrow").getD (σ.vars "j") 0 < (σ.arrs "elm").length := by
    rw [hread, helm, length_arrOf]
    exact huN
  have helmVal : (σ.arrs "elm").getD
      ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 = E (A (σ.vars "j")) := by
    rw [hread, helm, getD_arrOf E huN]
  have helmB : (σ.arrs "elm").getD
      ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 < B := by
    rw [helmVal]
    have := hbit _ huN
    omega
  have hdegLen : (σ.arrs "vrow").getD (σ.vars "j") 0 < (σ.arrs "deg").length := by
    rw [hread, hdeg, length_arrOf]
    exact huN
  have hdegVal : (σ.arrs "deg").getD
      ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 = D (A (σ.vars "j")) := by
    rw [hread, hdeg, getD_arrOf D huN]
  have hdegB : (σ.arrs "deg").getD
      ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 < B := by
    rw [hdegVal]
    exact lt_trans (hDlt _ huN) (by omega)
  have hbrElm : ((σ.setVar "u" ((σ.arrs "vrow").getD (σ.vars "j") 0)).arrs "elm").getD
      ((σ.setVar "u" ((σ.arrs "vrow").getD (σ.vars "j") 0)).vars "u") 0 =
      E (A (σ.vars "j")) := by
    rw [arrs_setVar, vars_setVar]
    simpa using helmVal
  have hbrElmB : ((σ.setVar "u" ((σ.arrs "vrow").getD (σ.vars "j") 0)).arrs "elm").getD
      ((σ.setVar "u" ((σ.arrs "vrow").getD (σ.vars "j") 0)).vars "u") 0 < B := by
    rw [hbrElm]
    have := hbit _ huN
    omega
  have hfresh : ¬ ∃ p < σ.vars "j", A p = A (σ.vars "j") :=
    hrow.no_repeat_before hjlt
  have hnotHit : ¬ Hit E A (σ.vars "j") (A (σ.vars "j")) := by
    intro hh
    exact hfresh hh.2
  have hspLen : σ.vars "sp" < n + W + 1 := by
    have : 0 < tail - σ.vars "j" := Nat.sub_pos_of_lt hjlt
    omega
  have hspB : σ.vars "sp" < B := by omega
  have hbvLen : σ.vars "sp" < (σ.arrs "bv").length := by
    rw [hbv, length_arrOf]
    exact hspLen
  have hbnLen : σ.vars "sp" < (σ.arrs "bn").length := by
    rw [hbn, length_arrOf]
    exact hspLen
  have hbhLen : (σ.arrs "bh").length = n + 1 := by
    rw [hbh, length_arrOf]
  have hbvLen' : (σ.arrs "bv").length = n + W + 1 := by
    rw [hbv, length_arrOf]
  have hbnLen' : (σ.arrs "bn").length = n + W + 1 := by
    rw [hbn, length_arrOf]
  have hlsB : σ.vars "ls" + 1 < B := by omega
  have hjB : σ.vars "j" + 1 < B := by omega
  have hDu : D (A (σ.vars "j")) < n := hDlt _ huN
  have hd1n : D (A (σ.vars "j")) - 1 < n + 1 := by omega
  have hsetD : ((σ.arrs "deg").set ((σ.arrs "vrow").getD (σ.vars "j") 0)
      ((σ.arrs "deg").getD ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 - 1)).getD
      ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 = D (A (σ.vars "j")) - 1 := by
    rw [hdegVal, hread, hdeg, set_arrOf_eq_upd, getD_arrOf _ huN, upd_self]
  have hhead : BH (D (A (σ.vars "j")) - 1) < σ.vars "sp" :=
    hbuck.head_lt _ (by omega)
  have hbhGet : (σ.arrs "bh").getD
      (((σ.arrs "deg").set ((σ.arrs "vrow").getD (σ.vars "j") 0)
        ((σ.arrs "deg").getD ((σ.arrs "vrow").getD (σ.vars "j") 0) 0 - 1)).getD
        ((σ.arrs "vrow").getD (σ.vars "j") 0) 0) 0 =
      BH (D (A (σ.vars "j")) - 1) := by
    rw [hsetD, hbh, getD_arrOf BH hd1n]
  have hDnew : ∀ u < n,
      upd D (A (σ.vars "j")) (D (A (σ.vars "j")) - 1) u < n := by
    intro u hu
    by_cases heu : u = A (σ.vars "j")
    · rw [heu, upd_self]
      omega
    · rw [upd_of_ne _ heu]
      exact hDlt u hu
  run_vcg
  · -- The row entry is still alive: decrement it and push one fresh node.
    have hEu : E (A (σ.vars "j")) = 0 := by omega
    have hpush := hbuck.push
      (D' := upd D (A (σ.vars "j")) (D (A (σ.vars "j")) - 1))
      (x := A (σ.vars "j"))
      (d := D (A (σ.vars "j")) - 1) (m' := n) huN (by omega)
      (upd_self ..)
      (fun v hv => upd_of_ne _ hv)
      (fun v hv => le_of_lt (hDnew v hv)) (fun v hv _ => hv)
    refine ⟨⟨upd D (A (σ.vars "j")) (D (A (σ.vars "j")) - 1),
      upd BH (D (A (σ.vars "j")) - 1) (σ.vars "sp"),
      upd BV (σ.vars "sp") (A (σ.vars "j")),
      upd BN (σ.vars "sp") (BH (D (A (σ.vars "j")) - 1)),
      ⟨by simp [hn], by simp [htail], by simp [hrowA], by simp [helm],
        by simp [hdeg, hread', set_arrOf_eq_upd, huN], by simp [hrnk],
        by simp [hidg],
        by simp [hbh, hdeg, hread', set_arrOf_eq_upd, huN, hd1n],
        by simp [hbv, hread', set_arrOf_eq_upd],
        by simp [hbn, hbh, hdeg, hread', set_arrOf_eq_upd, huN, hd1n]⟩,
      by simpa using hpush, hbit, by simpa using hDnew, ?_, ?_,
      by simp; omega, by simp; omega, by simp; omega, by simp; omega,
      by simp; omega⟩, by simp⟩
    · intro x hx hh
      simp only [vars_setVar] at hh
      rcases hit_succ.mp (by simpa using hh) with hold | ⟨hEx, hAx⟩
      · have hne : x ≠ A (σ.vars "j") := by
          intro heq
          subst x
          exact hnotHit hold
        rw [upd_of_ne _ hne]
        exact hhit x hx hold
      · have hxeq : x = A (σ.vars "j") := hAx.symm
        subst x
        rw [upd_self, hmiss _ huN hnotHit]
    · intro x hx hnh
      simp only [vars_setVar] at hnh
      have hnh' : ¬ Hit E A (σ.vars "j" + 1) x := by simpa using hnh
      have hne : x ≠ A (σ.vars "j") := by
        intro heq
        subst x
        exact hnh' (hit_succ.mpr (Or.inr ⟨hEu, rfl⟩))
      rw [upd_of_ne _ hne]
      exact hmiss x hx (fun hh => hnh' (hit_mono hh))
  · -- An eliminated row entry is skipped.
    have hEu : E (A (σ.vars "j")) ≠ 0 := by omega
    refine ⟨⟨D, BH, BV, BN,
      ⟨by simp [hn], by simp [htail], by simp [hrowA], by simp [helm],
        by simp [hdeg], by simp [hrnk], by simp [hidg], by simp [hbh],
        by simp [hbv], by simp [hbn]⟩,
      by simpa using hbuck, hbit, hDlt, ?_, ?_,
      by simp; omega, by simp; omega, by simp; omega, by simp; omega,
      by simp; omega⟩, by simp⟩
    · intro x hx hh
      simp only [vars_setVar] at hh
      rcases hit_succ.mp (by simpa using hh) with hold | ⟨hEx, hAx⟩
      · exact hhit x hx hold
      · subst x
        exact absurd hEx hEu
    · intro x hx hnh
      simp only [vars_setVar] at hnh
      exact hmiss x hx (fun hh => hnh (by simpa using hit_mono hh))
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq]
  all_goals omega

/-- Scan the regenerated row from slot zero to its live tail. -/
def decVirtualScan : Com :=
  Csr.scan "j" "vtail" decVirtualSlot

/-- A complete regenerated row lowers precisely the degrees of its live
neighbours.  The cost and the arena consumption are linear in this row,
independently of all rows generated before it. -/
theorem decVirtualScan_spec {B n W tail sp₀ ls₀ : ℕ} {G : SimpleGraph (Fin n)}
    {w : Fin n} {A E R ID D₀ : ℕ → ℕ} (hrow : RowRep G w tail A)
    (hB : n + W + 1 < B) :
    Spec B
      (fun σ => ScanInv n W tail sp₀ ls₀ A E R ID D₀ σ ∧ σ.vars "j" = 0)
      decVirtualScan
      (fun _ σ' => ScanInv n W tail sp₀ ls₀ A E R ID D₀ σ' ∧ σ'.vars "j" = tail)
      (47 * tail + 4) := by
  refine Csr.rowScan_spec B (47 * tail + 4) tail 43
    "j" "vtail" decVirtualSlot (ScanInv n W tail sp₀ ls₀ A E R ID D₀)
    (lt_of_le_of_lt hrow.tail_le (by omega)) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D, BH, BV, BN, harr, -, -, -, -, -, hjle, -, -, -, -⟩ := hσ
    exact ⟨harr.tail_eq, hjle⟩
  · obtain ⟨σ', K', hrun, hK, hI', hj'⟩ :=
      decVirtualSlot_run hrow hB hσ hlt
    exact ⟨σ', K', hrun, hI', hj', hK⟩

/-- The terminal hit/miss facts of a virtual scan are exactly the two
degree-update hypotheses consumed by `RamElim.Elim.extract`, with the
all-alive mask used by an ordering run. -/
theorem extract_of_virtual_scan {G : SimpleGraph (Fin n)} {w : Fin n}
    {tail : ℕ} {A E D D' : ℕ → ℕ} (hrow : RowRep G w tail A)
    (hh : ∀ u < n, Hit (upd E (w : ℕ) 1) A tail u → D' u = D u - 1)
    (hnh : ∀ u < n, ¬ Hit (upd E (w : ℕ) 1) A tail u → D' u = D u) :
    (∀ u < n, E u = 0 →
        Lax3Proofs.RamBfs.MAdj G (fun _ => 1) u (w : ℕ) → D' u = D u - 1) ∧
      (∀ u < n, E u = 0 →
        ¬ Lax3Proofs.RamBfs.MAdj G (fun _ => 1) u (w : ℕ) → D' u = D u) := by
  have hall : ∀ v < n, (fun _ : ℕ => 1) v ≠ 0 := by simp
  refine ⟨?_, ?_⟩
  · intro u hu hEu hadj
    have hadjG : G.Adj ⟨u, hu⟩ w := by
      rcases hadj with ⟨hu', hw', hadj'⟩
      have hg := (Lax3Proofs.RamBfs.masked_adj.1 hadj').1
      simpa using hg
    have huw : u ≠ (w : ℕ) := by
      intro heq
      exact (G.ne_of_adj hadjG) (Fin.ext heq)
    apply hh u hu
    apply (hit_last_iff hrow hu).2
    exact ⟨by rw [upd_of_ne _ huw]; exact hEu, hadjG⟩
  · intro u hu hEu hnadj
    apply hnh u hu
    intro hhit
    have hhg := (hit_last_iff hrow hu).1 hhit
    apply hnadj
    refine ⟨hu, w.isLt, ?_⟩
    exact Lax3Proofs.RamBfs.masked_adj.2 ⟨hhg.2, hall u hu, hall _ w.isLt⟩

/-! ## Axiom audit -/

#print axioms decVirtualSlot_run
#print axioms decVirtualScan_spec
#print axioms extract_of_virtual_scan

end Lax3Proofs.Refine.OrderVirtualElimScan
