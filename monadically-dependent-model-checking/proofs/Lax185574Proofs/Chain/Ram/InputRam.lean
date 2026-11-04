import Lax185574Proofs.Chain.Ram.WOrder
import Lax185574Proofs.Words.FinsetRead

/-!
Reading the input `(r, ε, G)`.

The word of the input is `r`, then the integer `num ε` (the tag `0` and
its value, since `ε > 0`), then `den ε`, then the graph as the number `n`
of vertices followed by the words of the neighborhoods. The command
`readIn` reads `r` into `tr`, `num ε` into `qa`, `den ε` into `qden`,
`n` into `n`, and the adjacency matrix into `adj`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574.WordEncoding

/-- Read the input. -/
def readIn : Com :=
  .seq (.read "tr") (.seq (.read "qsg") (.seq (.read "qa") (.seq (.read "qden")
    (.seq (.read "n") (readRows "adj" "n")))))

open Classical in
/-- The neighborhoods of a graph, as the graph's word lists them. -/
noncomputable def nbhds {n : ℕ} (G : SimpleGraph (Fin n)) : List (Finset (Fin n)) :=
  List.ofFn fun v : Fin n => univ.filter (G.Adj v)

theorem toWord_input {n r : ℕ} {ε : ℚ} (hε : 0 < ε) (G : SimpleGraph (Fin n)) :
    toWord (r, ε, G) = r :: 0 :: ε.num.natAbs :: ε.den :: n :: ((nbhds G).map toWord).flatten := by
  have hnum : ε.num = Int.ofNat ε.num.natAbs := by
    have := Rat.num_pos.2 hε
    simp only [Int.ofNat_eq_natCast, Int.natCast_natAbs]; exact (abs_of_pos this).symm
  have h2 : toWord G = (nbhds G).length :: ((nbhds G).map toWord).flatten := rfl
  have h3 : (nbhds G).length = n := by simp [nbhds]
  have h4 : toWord ε = toWord ε.num ++ [ε.den] := rfl
  have h5 : toWord ε.num = [0, ε.num.natAbs] := by rw [hnum]; rfl
  have h6 : toWord (r, ε, G) = [r] ++ (toWord ε ++ toWord G) := rfl
  rw [h6, h4, h5, h2, h3]; simp

theorem readIn_run {B n r : ℕ} {ε : ℚ} (hε : 0 < ε) (G : SimpleGraph (Fin n))
    (hB : n * n + n + 1 < B) {σ : Env}
    (hinp : σ.inp = toWord (r, ε, G)) (harr : σ.arrs "adj" = List.replicate (n * n) 0) :
    ∃ σ', Run B readIn σ σ' (n * (17 * n + 15) + 20) ∧ σ'.inp = [] ∧
      σ'.vars "tr" = r ∧ σ'.vars "qa" = ε.num.natAbs ∧ σ'.vars "qden" = ε.den ∧
      σ'.vars "n" = n ∧ Mat σ' "adj" n (fun u v => ind (gA G u v)) ∧
      (∀ x, x ∉ ["tr", "qsg", "qa", "qden", "n", "r", "d", "k", "x1", "x"] →
        σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "adj" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out := by
  rw [toWord_input hε] at hinp
  set σ1 := { σ.setVar "tr" r with inp := 0 :: ε.num.natAbs :: ε.den :: n ::
    ((nbhds G).map toWord).flatten } with hσ1
  have r1 : Run B (.read "tr") σ σ1 1 := Run.read hinp
  set σ2 := { σ1.setVar "qsg" 0 with inp := ε.num.natAbs :: ε.den :: n ::
    ((nbhds G).map toWord).flatten } with hσ2
  have r2 : Run B (.read "qsg") σ1 σ2 1 := Run.read rfl
  set σ3 := { σ2.setVar "qa" ε.num.natAbs with inp := ε.den :: n ::
    ((nbhds G).map toWord).flatten } with hσ3
  have r3 : Run B (.read "qa") σ2 σ3 1 := Run.read rfl
  set σ4 := { σ3.setVar "qden" ε.den with inp := n :: ((nbhds G).map toWord).flatten } with hσ4
  have r4 : Run B (.read "qden") σ3 σ4 1 := Run.read rfl
  set σ5 := { σ4.setVar "n" n with inp := ((nbhds G).map toWord).flatten } with hσ5
  have r5 : Run B (.read "n") σ4 σ5 1 := Run.read rfl
  have hL : (nbhds G).length = n := by simp [nbhds]
  obtain ⟨σ6, r6, hinp6, hl6, he6⟩ :=
    readRows_run (B := B) (n := n) (L := nbhds G) (rest := []) (σ := σ5) (arr := "adj")
      (cnt := "n") (by decide) (by decide) (by simp [hσ5]) (by simp [hσ5, hL])
      (by simp [hσ5]) (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, harr, hL]) (by rw [hL]; omega)
      (by rw [hL]; omega)
  have hrun : Run B readIn σ σ6 (n * (17 * n + 15) + 20) :=
    (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono (by rw [hL]; omega)
  have hv : ∀ x, x ∉ ["r", "d", "k", "x1", "x"] → σ6.vars x = σ5.vars x := fun x hx =>
    r6.frame_var x (by
      intro h; apply hx
      have : (readRows "adj" "n").wvars ⊆ ["r", "d", "k", "x1", "x"] := by decide
      exact this h)
  refine ⟨σ6, hrun, by simpa using hinp6, by rw [hv _ (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1],
    by rw [hv _ (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1],
    by rw [hv _ (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1],
    by rw [hv _ (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1],
    ⟨by rw [hl6, hL], fun u hu v hv' => ?_⟩, fun x hx => ?_, fun a ha => ?_, ?_⟩
  · rw [he6 u (by rw [hL]; exact hu) v hv']
    congr 1
    unfold ind
    have : v ∈ sortedVals (nbhds G)[u] ↔ gA G u v := by
      rw [mem_sortedVals]
      simp only [nbhds, List.getElem_ofFn, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨h, hadj⟩ => ⟨hu, h, hadj⟩, fun ⟨_, h, hadj⟩ => ⟨h, hadj⟩⟩
    by_cases h : gA G u v <;> simp [h, this]
  · simp at hx
    rw [hv x (by simp; tauto)]
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1]
  · rw [r6.frame_arr a (by
      have : (readRows "adj" "n").warrs = ["adj"] := by decide
      rw [this]; simpa using ha)]
    simp [hσ5, hσ4, hσ3, hσ2, hσ1]
  · rw [r6.out_eq (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1]

end Lax185574Proofs.Chain.Ram
