import Lax185574Proofs.ResolveRam.Glue.CR1A

/-!
The new head and the plan of round `1`.

`hdR1 ph k` sets the scalars of the new head (phase `ph`, position
`0, 0, 0`, `NLV = n`), the index `6` of the first item word and the
kind `k` of the query, and `plR1` stores the plan `psR1` (`hdR1_run`).
The plan takes from the library `libR1 z` the color table, two empty
words, the lengths of the levels, the words of the scatter type and the
item words of level `0` (`planW_r1`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam

/-- The scalars of the new head of round `1`. -/
def hdR1 (ph k : ℕ) : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", .lit ph), ("Nd", .lit 0), ("Ni", .lit 0), ("Nm", .lit 0),
    ("NFA", .lit 0), ("NCO", .lit 0), ("NLV", .var "gn"), ("ox", .lit 6), ("qk", .lit k), ("po", .lit 0)]

/-- The names of `hdR1`. -/
def hdR1N : List String := ["Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NFA", "NCO", "NLV", "ox", "qk", "po"]

theorem hdR1_names (ph k : ℕ) : (hdR1 ph k).map Prod.fst = hdR1N := rfl

/-- The plan of round `1`, as expressions. -/
def plR1 : List (Expr × Expr) :=
  [(.lit 5, .lit 1), (.lit 1, .lit 2), (.lit 4, .lit 1), (.add (.lit 6) (.var "gn"), .var "NSG"),
    (.lit 6, .var "gn")]

/-- The plan of round `1`. -/
def psR1 (n nS : ℕ) : List (ℕ × ℕ) := [(5, 1), (1, 2), (4, 1), (6 + n, nS), (6, n)]

set_option maxHeartbeats 1600000 in
/-- **The new head and the plan of round `1`.** -/
theorem hdR1_run {W ph k nn nS : ℕ} {τ : Env} (har : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hW : 64 ≤ W)
    (hph : ph ≤ 3) (hk : k ≤ 3) (hgn : τ.vars "gn" = nn) (hnS : τ.vars "NSG" = nS) (hn : nn + 6 < W + 1) :
    ∃ τ', Run (W + 1) (.seq (asgs (hdR1 ph k)) (stPlan plR1)) τ τ' 200 ∧
      τ'.vars "Nt" = 1 ∧ τ'.vars "Nw" = 0 ∧ τ'.vars "Nph" = ph ∧ τ'.vars "Nd" = 0 ∧ τ'.vars "Ni" = 0 ∧
      τ'.vars "Nm" = 0 ∧ τ'.vars "NSG" = nS ∧ τ'.vars "NFA" = 0 ∧ τ'.vars "NCO" = 0 ∧
      τ'.vars "NLV" = nn ∧ τ'.vars "ox" = 6 ∧ τ'.vars "qk" = k ∧ τ'.vars "po" = 0 ∧
      PreAt "PR" (prW (psR1 nn nS)) τ' ∧ τ'.vars "np" = 5 ∧
      (∀ y, y ≠ "np" → y ∉ hdR1N → τ'.vars y = τ.vars y) ∧ (∀ b, b ≠ "PR" → τ'.arrs b = τ.arrs b) ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  let f : String → ℕ := fun y =>
    if y = "Nt" then 1 else if y = "Nph" then ph else if y = "NLV" then nn else if y = "ox" then 6
    else if y = "qk" then k else 0
  have hnS' : nS < W + 1 := by rw [← hnS]; exact hlt.vars _
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ) (l := hdR1 ph k) (f := f)
    (by
      intro p hp
      simp only [hdR1, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show f "Nt" = 1 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Nw" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Nph" = ph by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Nd" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Ni" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Nm" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "NFA" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "NCO" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "NLV" = nn by simp [f]]; exact ev_var hgn (by omega)
      · rw [show f "ox" = 6 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "qk" = k by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "po" = 0 by simp [f]]; exact evalB_lit (by omega))
    (by simp [hdR1, exRv])
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  have hgn1 : τ1.vars "gn" = nn := by rw [g1 "gn" (by simp [hdR1]), hgn]
  have hnS1 : τ1.vars "NSG" = nS := by rw [g1 "NSG" (by simp [hdR1]), hnS]
  obtain ⟨τ2, r2, PR2, np2, v2, a2, l2, o2, i2⟩ := stPlan_run (W := W) (l := plR1) (ps := psR1 nn nS)
    (τ := τ1) rfl (by rw [a1]; exact har "PR") (by simp [plR1]; omega)
    (by
      intro j hj
      simp only [plR1, List.length_cons, List.length_nil] at hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
        simp only [psR1, plR1, List.getElem_cons_succ, List.getElem_cons_zero]
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨ev_add (evalB_lit (by omega)) (ev_var hgn1 (by omega)) (by omega), ev_var hnS1 hnS'⟩
      · exact ⟨evalB_lit (by omega), ev_var hgn1 (by omega)⟩)
    (by decide)
  have hS : ∀ y ∈ hdR1N, τ2.vars y = f y := fun y hy => by
    rw [v2 y (by intro h; subst h; simp [hdR1N] at hy)]; exact s1 y (by rw [hdR1_names]; exact hy)
  have hrun : Run (W + 1) (.seq (asgs (hdR1 ph k)) (stPlan plR1)) τ τ2 200 := by
    refine (Run.seq r1 r2).mono ?_
    simp [asgK, hdR1, plR1, Expr.size]
  refine ⟨τ2, hrun, by rw [hS "Nt" (by simp [hdR1N])]; simp [f], by rw [hS "Nw" (by simp [hdR1N])]; simp [f],
    by rw [hS "Nph" (by simp [hdR1N])]; simp [f], by rw [hS "Nd" (by simp [hdR1N])]; simp [f],
    by rw [hS "Ni" (by simp [hdR1N])]; simp [f], by rw [hS "Nm" (by simp [hdR1N])]; simp [f],
    by rw [v2 "NSG" (by decide), hnS1], by rw [hS "NFA" (by simp [hdR1N])]; simp [f],
    by rw [hS "NCO" (by simp [hdR1N])]; simp [f], by rw [hS "NLV" (by simp [hdR1N])]; simp [f],
    by rw [hS "ox" (by simp [hdR1N])]; simp [f], by rw [hS "qk" (by simp [hdR1N])]; simp [f],
    by rw [hS "po" (by simp [hdR1N])]; simp [f], PR2, by rw [np2]; rfl,
    fun y h1 h2 => by rw [v2 y h1, g1 y (by rw [hdR1_names]; exact h2)],
    fun b hb => by rw [a2 b hb, a1], fun b => ?_, Run.envLt hrun hlt, by rw [o2, o1], by rw [i2, i1]⟩
  by_cases hb : b = "PR"
  · subst hb; exact l2
  · rw [a2 b hb, a1]; exact har b

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem length_lvW_zero : (lvW G P Q s k₀ q₀ 0).length = n := by rw [lvW_zero]; simp

/-- **The plan of round `1`.** -/
theorem planW_r1 (z : ℕ) (X : List (List ℕ)) :
    planW (libR1 G P Q s k₀ q₀ z ++ X) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) =
      [ctW G P Q, [], [], n :: List.replicate z 0] ++ (Lax185574.ScatterTypes.stp G k₀ q₀).words ++
        lvW G P Q s k₀ q₀ 0 := by
  have hl := length_lvW_zero G P Q s k₀ q₀
  simp only [planW, psR1, libR1, midR1, ws_stp, List.flatMap_cons, List.flatMap_nil, rng]
  simp [List.drop_append, List.take_append, hl]
  rw [show 6 + n = n + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  simp only [List.drop_succ_cons]
  rw [List.drop_left' hl]
  simp

end Lax185574Proofs.ResolveRam.Glue
