import Lax808846Proofs.Lib.Csr
import Lax185574Proofs.Words.ForLoop

/-!
One step of the breadth-first search of lem:compute-stp: marking the
targets of one row of an adjacency structure in compressed-row form.

`relaxRow o t` reads the bounds of row `bw` from the offsets array `o`
and stores `1` into the array `dn` at every target of the row, read from
the target array `t`. Afterwards entry `v` of `dn` is `1` if it was `1`
before or `v` is a target of the row.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr

/-- `v` is a target of row `w`. -/
def InRow (off tgt : ℕ → ℕ) (w v : ℕ) : Prop := ∃ p, off w ≤ p ∧ p < off (w + 1) ∧ tgt p = v

/-- Store `1` at the target under the pointer and advance the pointer. -/
def slotBody (t : String) : Com :=
  .seq (.assign "bv" (.get t (.var "bj"))) (.seq (.store "dn" (.var "bv") (.lit 1))
    (.assign "bj" (.add (.var "bj") (.lit 1))))

/-- Mark the targets of row `bw`. -/
def relaxRow (o t : String) : Com := .seq (loadRow o "bw" "bj" "be") (scan "bj" "be" (slotBody t))

theorem relaxRow_wvars (o t : String) : (relaxRow o t).wvars = ["bj", "be", "bv", "bj"] := by
  simp [relaxRow, slotBody, loadRow, scan, Com.wvars]

theorem relaxRow_warrs (o t : String) : (relaxRow o t).warrs = ["dn"] := by
  simp [relaxRow, slotBody, loadRow, scan, Com.warrs]

theorem relaxRow_noWrite (o t : String) : (relaxRow o t).NoWrite := by
  simp [relaxRow, slotBody, loadRow, scan, Com.NoWrite]

/-- **Marking a row.** -/
theorem relaxRow_run {B n ns : ℕ} {o t : String} {off tgt g : ℕ → ℕ} {σ : Env} {w : ℕ}
    (hc : Csr o t n ns n off tgt σ) (hnB : n + 1 < B) (hnsB : ns + 1 < B)
    (hw : σ.vars "bw" = w) (hwn : w < n) (hdn : σ.arrs "dn" = arrOf n g)
    (hg : ∀ v < n, g v ≤ 1) (ho : o ≠ "dn") (ht : t ≠ "dn") :
    ∃ σ' g', Run B (relaxRow o t) σ σ' (14 * (off (w + 1) - off w) + 13) ∧
      σ'.arrs "dn" = arrOf n g' ∧
      (∀ v < n, (g' v = 1 ↔ g v = 1 ∨ InRow off tgt w v) ∧ g' v ≤ 1) := by
  have hpre : RowPre o t "bw" n ns n B off tgt σ :=
    ⟨⟨hc, by omega, by omega⟩, by omega, by omega⟩
  obtain ⟨σ1, hr1, hc1, hj1, he1, hσ1⟩ :=
    (loadRow_spec B n ns n o t "bw" "bj" "be" off tgt (by decide) (by decide)).run hpre
  rw [hw] at hj1 he1
  have hle : off w ≤ off (w + 1) := hc.off_le_succ hwn
  have hlt : off (w + 1) ≤ ns := hc.row_le hwn
  let I : Env → Prop := fun τ => Csr o t n ns n off tgt τ ∧ τ.vars "be" = off (w + 1) ∧
    off w ≤ τ.vars "bj" ∧ τ.vars "bj" ≤ off (w + 1) ∧
    ∃ g', τ.arrs "dn" = arrOf n g' ∧
      ∀ v < n, (g' v = 1 ↔ g v = 1 ∨ ∃ p, off w ≤ p ∧ p < τ.vars "bj" ∧ tgt p = v) ∧ g' v ≤ 1
  have hI1 : I σ1 := by
    refine ⟨hc1, he1, by omega, by omega, g, ?_, fun v hv => ⟨?_, hg v hv⟩⟩
    · rw [hσ1]; simpa using hdn
    · rw [hj1]; constructor
      · exact Or.inl
      · rintro (h | ⟨p, h1, h2, -⟩)
        · exact h
        · omega
  have hscan := rowScan_spec B (14 * (off (w + 1) - off w) + 4) (off (w + 1)) 10 "bj" "be"
    (slotBody t) (P := fun τ => τ = σ1) I (by omega) (fun τ hI => ⟨hI.2.1, hI.2.2.2.1⟩)
    (by
      rintro τ ⟨hcτ, heτ, hj0, hj2, g', hdg, hg'⟩ hjlt
      set j := τ.vars "bj" with hj
      have hjns : j < ns := by omega
      have htj : tgt j < n := hcτ.target hjns
      set τ1 := τ.setVar "bv" (tgt j) with hτ1
      set τ2 := τ1.setArr "dn" (tgt j) 1 with hτ2
      set τ3 := τ2.setVar "bj" (j + 1) with hτ3
      have r1 : Run B (.assign "bv" (.get t (.var "bj"))) τ τ1 3 := by
        refine (Run.assign ?_).mono (by simp)
        simp only [evalB_get_iff, evalB_var_iff]
        refine ⟨j, ⟨rfl, by omega⟩, ?_, by omega⟩
        rw [hcτ.tgtArr, getElem?_arrOf _ hjns]
      have r2 : Run B (.store "dn" (.var "bv") (.lit 1)) τ1 τ2 3 := by
        refine (Run.store (idx := tgt j) (v := 1) (by simp [hτ1]; omega) (by simp; omega) ?_).mono
          (by simp)
        simp [hτ1, hdg]; omega
      have r3 : Run B (.assign "bj" (.add (.var "bj") (.lit 1))) τ2 τ3 4 := by
        refine (Run.assign ?_).mono (by simp)
        simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        have : τ2.vars "bj" = j := by simp [hτ2, hτ1, hj]
        refine ⟨j, 1, ⟨this.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
      refine ⟨τ3, 10, (Run.seq r1 (Run.seq r2 r3)).mono (by simp), ⟨?_, ?_, ?_, ?_, ?_⟩,
        by simp [hτ3], by omega⟩
      · exact (((hcτ.setVar "bv" (tgt j)).setArr_of_ne ho.symm ht.symm (tgt j) 1).setVar "bj" (j + 1))
      · simp [hτ3, hτ2, hτ1, heτ]
      · simp [hτ3]; omega
      · simp [hτ3]; omega
      · refine ⟨fun v => if v = tgt j then 1 else g' v, ?_, fun v hv => ⟨?_, ?_⟩⟩
        · simp [hτ3, hτ2, hτ1, hdg, set_arrOf]
        · simp only [hτ3, vars_setVar, if_true]
          by_cases hv' : v = tgt j
          · simp only [hv', if_true, true_iff]
            exact Or.inr ⟨j, hj0, by omega, rfl⟩
          · simp only [hv', if_false, (hg' v hv).1]
            constructor
            · rintro (h | ⟨p, h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨p, h1, by omega, h3⟩
            · rintro (h | ⟨p, h1, h2, h3⟩)
              · exact Or.inl h
              · refine Or.inr ⟨p, h1, ?_, h3⟩
                rcases Nat.lt_or_ge p j with h | h
                · exact h
                · exfalso; apply hv'; rw [← h3]; congr 1; omega
        · by_cases hv' : v = tgt j <;> simp [hv', (hg' v hv).2])
    (fun τ h => h ▸ hI1) (fun τ h => by rw [h, hj1])
  obtain ⟨σ2, hr2, ⟨-, -, -, -, g', hdg, hg'⟩, hj2⟩ := hscan.run rfl
  refine ⟨σ2, g', (Run.seq hr1 hr2).mono (by omega), hdg, fun v hv => ⟨?_, (hg' v hv).2⟩⟩
  rw [(hg' v hv).1, hj2]
  rfl

end Lax185574Proofs.StpRam
