import Lax185574Proofs.StpRam.GreedyCmd

/-!
Writing the triples of the scatter type.

For the radius `gr` and the word `u` of index `gu`, the command
`emitTriple` writes the frame of `gr :: u ++ [gc]`, where `gc` holds the
value computed by `greedyCmd`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574Proofs.Words

/-- Write the entries of the word at `ep` of length `el`. -/
def writeEntries : Com := forUp "ek" (.var "el") (.write (.get "a" (.add (.var "ep") (.var "ek"))))

/-- Write the frame of `gr :: u ++ [gc]` for the word `u` of index `gu`. -/
def emitTriple : Com :=
  .seq (.assign "ep" (.get "st" (.var "gu"))) (.seq (.assign "el" (.get "ln" (.var "gu")))
    (.seq (.write (.add (.var "el") (.lit 2))) (.seq (.write (.var "gr"))
      (.seq writeEntries (.write (.var "gc"))))))

/-- **Writing a triple.** -/
theorem emitTriple_run {B : ℕ} {A : List (List ℕ)} {σ : Env} (hw : WordsAt A σ) (hb : WordsBound B A)
    {ui r m : ℕ} (hu : σ.vars "gu" = ui) (huA : ui < A.length) (hr : σ.vars "gr" = r) (hrB : r < B)
    (hm : σ.vars "gc" = m) (hmB : m < B) (htB : total A + 3 < B) :
    ∃ σ', Run B emitTriple σ σ' (13 * A[ui].length + 30) ∧
      σ'.out = σ.out ++ ((A[ui].length + 2) :: r :: A[ui] ++ [m]) := by
  have hlen := hb.len
  have hoff := off_add_le huA
  set u := A[ui] with hu'
  have hlu : u.length ≤ total A := by rw [hu', ← wd_eq huA]; exact length_wd_le A ui
  set τ1 := σ.setVar "ep" (off A ui) with hτ1
  set τ2 := τ1.setVar "el" u.length with hτ2
  have r1 : Run B (.assign "ep" (.get "st" (.var "gu"))) σ τ1 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    exact ⟨ui, ⟨hu.symm, by omega⟩, hw.st ui huA, by omega⟩
  have r2 : Run B (.assign "el" (.get "ln" (.var "gu"))) τ1 τ2 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    refine ⟨ui, ⟨by simp [hτ1, hu], by simp [hτ1, hu]; omega⟩, ?_, by omega⟩
    simp only [hτ1, arrs_setVar]; exact hw.ln ui huA
  set τ3 : Env := { τ2 with out := σ.out ++ [u.length + 2] } with hτ3
  have r3 : Run B (.write (.add (.var "el") (.lit 2))) τ2 τ3 4 := by
    refine (Run.write ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨u.length, 2, ⟨by simp [hτ2], by simp [hτ2]; omega⟩, ⟨rfl, by have := hb.three; omega⟩,
      by simp [Bop.apply], by omega⟩
  set τ4 : Env := { τ3 with out := τ3.out ++ [r] } with hτ4
  have r4 : Run B (.write (.var "gr")) τ3 τ4 2 := by
    refine (Run.write (v := r) ?_).mono (by simp)
    have hgr3 : τ3.vars "gr" = r := by simp [hτ3, hτ2, hτ1, hr]
    simp only [evalB_var_iff]; exact ⟨hgr3.symm, by rw [hgr3]; exact hrB⟩
  obtain ⟨τ5, r5, ⟨hout5, hm5, -⟩, -⟩ := forUp_run (B := B) (i := "ek") (e := .var "el")
    (body := .write (.get "a" (.add (.var "ep") (.var "ek")))) (N := u.length) (K := 5)
    (fun k τ => τ.out = σ.out ++ [u.length + 2, r] ++ u.take k ∧ τ.vars "gc" = m ∧
      τ.vars "el" = u.length ∧ τ.vars "ep" = off A ui ∧ τ.arrs "a" = σ.arrs "a") (σ := τ4) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.2.1.symm, by rw [hI.2.2.1]; omega⟩)
    ⟨by simp [hτ4, hτ3], by simp [hτ4, hτ3, hτ2, hτ1, hm], by simp [hτ4, hτ3, hτ2],
      by simp [hτ4, hτ3, hτ2, hτ1], by simp [hτ4, hτ3, hτ2, hτ1]⟩
    (by
      rintro k hk τ ⟨ho, hgc, hel, hep, ha⟩ hek
      have hent : (σ.arrs "a")[off A ui + k]? = some u[k] := hw.a ui huA k hk
      have huk : u[k] < B := hb.ent u (List.getElem_mem huA) _ (List.getElem_mem hk)
      refine ⟨{ τ with out := τ.out ++ [u[k]] }, (Run.write ?_).mono (by simp), by simp [hek],
        ?_, by simp [hgc], by simp [hel], by simp [hep], by simp [ha]⟩
      · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff]
        refine ⟨off A ui + k, ⟨off A ui, k, ⟨hep.symm, by omega⟩, ⟨hek.symm, by omega⟩,
          by simp [Bop.apply], by omega⟩, by rw [ha]; exact hent, huk⟩
      · simp only [out_setVar, ho, List.take_add_one, List.getElem?_eq_getElem hk]; simp)
  have hτ5 : τ5.out = σ.out ++ [u.length + 2, r] ++ u := by rw [hout5, List.take_length]
  refine ⟨{ τ5 with out := τ5.out ++ [m] }, ?_, ?_⟩
  · unfold emitTriple writeEntries
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.write (v := m) ?_)))))).mono ?_
    · simp only [evalB_var_iff]; exact ⟨hm5.symm, by omega⟩
    · simp only [Expr.size]; omega
  · simp [hτ5]

end Lax185574Proofs.StpRam
