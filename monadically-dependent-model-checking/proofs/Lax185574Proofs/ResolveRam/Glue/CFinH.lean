import Lax185574Proofs.ResolveRam.Glue.CaseKit
import Lax185574Proofs.ResolveRam.Glue.CaseDn

/-!
The new head and the plan of a round that finishes an item on the way
down.

`hdFn eph ed ei k` sets the scalars of the new head (the phase, depth
and item of the new position are the values of `eph`, `ed`, `ei`, the
number of item words grows by `ne`), the kind `k` of the next call and
`po`. `plFn` stores the plan `psFn` of the new state: the color table,
two empty words, the new lengths (word `iL`), the scatter type, the old
item words and the `ne` new item words from word `e0` on (`hdFn_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- The scalars of the new head after an item. -/
def hdFn (eph ed ei : Expr) (k : ℕ) : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", eph), ("Nd", ed), ("Ni", ei), ("Nm", .lit 0), ("NSG", .var "nSG"),
    ("NFA", .lit 0), ("NCO", .lit 0), ("NLV", .add (.var "nLV") (.var "ne")), ("qk", .lit k), ("po", .lit 0)]

/-- The plan after an item, as expressions. -/
def plFn : List (Expr × Expr) :=
  [(.lit 0, .lit 1), (.var "m0", .lit 1), (.var "m0", .lit 1), (.var "iL", .lit 1), (.lit 4, .var "nSG"),
    (.add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO"), .var "nLV"), (.var "e0", .var "ne")]

/-- The plan after an item. -/
def psFn (M0 iLL e0 nE nS nF nC nL : ℕ) : List (ℕ × ℕ) :=
  [(0, 1), (M0, 1), (M0, 1), (iLL, 1), (4, nS), (4 + nS + nF + nC, nL), (e0, nE)]

theorem psFin_eq (w : SW) (M0 iLL e0 nE : ℕ) :
    psFin w M0 iLL e0 nE = psFn M0 iLL e0 nE w.SG.length w.FA.length w.CO.length w.LV.length := rfl

/-- The names of the new head. -/
def hdNames : List String := ["Nt", "Nw", "Nph", "Nd", "Ni", "Nm", "NSG", "NFA", "NCO", "NLV", "qk", "po"]

theorem hdFn_names (eph ed ei : Expr) (k : ℕ) : (hdFn eph ed ei k).map Prod.fst = hdNames := rfl

set_option maxHeartbeats 1600000 in
/-- **The new head and the plan after an item.** -/
theorem hdFn_run {W M0 iLL e0 nE nS nF nC nL a1 a2 a3 k : ℕ} {eph ed ei : Expr} {τ : Env}
    (har : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hW : 64 ≤ W)
    (hm0 : τ.vars "m0" = M0) (hiL : τ.vars "iL" = iLL) (he0 : τ.vars "e0" = e0) (hne : τ.vars "ne" = nE)
    (hnS : τ.vars "nSG" = nS) (hnF : τ.vars "nFA" = nF) (hnC : τ.vars "nCO" = nC) (hnL : τ.vars "nLV" = nL)
    (h1 : eph.evalB (W + 1) τ = some a1) (h2 : ed.evalB (W + 1) τ = some a2) (h3 : ei.evalB (W + 1) τ = some a3)
    (hrd : ∀ y ∈ hdNames, y ∉ exRv eph ∧ y ∉ exRv ed ∧ y ∉ exRv ei)
    (hk : k ≤ 3) (hsum : nL + nE < W + 1) (h4 : 4 + nS + nF + nC < W + 1) :
    ∃ τ', Run (W + 1) (.seq (asgs (hdFn eph ed ei k)) (stPlan plFn)) τ τ' (asgK (hdFn eph ed ei k) + 186) ∧
      τ'.vars "Nt" = 1 ∧ τ'.vars "Nw" = 0 ∧ τ'.vars "Nph" = a1 ∧ τ'.vars "Nd" = a2 ∧ τ'.vars "Ni" = a3 ∧
      τ'.vars "Nm" = 0 ∧ τ'.vars "NSG" = nS ∧ τ'.vars "NFA" = 0 ∧ τ'.vars "NCO" = 0 ∧
      τ'.vars "NLV" = nL + nE ∧ τ'.vars "qk" = k ∧ τ'.vars "po" = 0 ∧
      PreAt "PR" (prW (psFn M0 iLL e0 nE nS nF nC nL)) τ' ∧ τ'.vars "np" = 7 ∧
      (∀ y, y ≠ "np" → y ∉ hdNames → τ'.vars y = τ.vars y) ∧ (∀ b, b ≠ "PR" → τ'.arrs b = τ.arrs b) ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  let f : String → ℕ := fun y =>
    if y = "Nt" then 1 else if y = "Nph" then a1 else if y = "Nd" then a2 else if y = "Ni" then a3
    else if y = "NSG" then nS else if y = "NLV" then nL + nE else if y = "qk" then k else 0
  have ev : ∀ y v, τ.vars y = v → (Expr.var y).evalB (W + 1) τ = some v := fun y v h =>
    ev_var h (by rw [← h]; exact hlt.vars _)
  obtain ⟨τ1, r1, s1, g1, a1', o1, i1⟩ := asgs_run (B := W + 1) (τ := τ) (l := hdFn eph ed ei k) (f := f)
    (by
      intro p hp
      simp only [hdFn, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [show f "Nt" = 1 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Nw" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "Nph" = a1 by simp [f]]; exact h1
      · rw [show f "Nd" = a2 by simp [f]]; exact h2
      · rw [show f "Ni" = a3 by simp [f]]; exact h3
      · rw [show f "Nm" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "NSG" = nS by simp [f]]; exact ev _ _ hnS
      · rw [show f "NFA" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "NCO" = 0 by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "NLV" = nL + nE by simp [f]]; exact ev_add (ev _ _ hnL) (ev _ _ hne) hsum
      · rw [show f "qk" = k by simp [f]]; exact evalB_lit (by omega)
      · rw [show f "po" = 0 by simp [f]]; exact evalB_lit (by omega))
    (by
      intro p hp q hq
      have hq' : q.1 ∈ hdNames := by rw [← hdFn_names eph ed ei k]; exact List.mem_map_of_mem hq
      simp only [hdFn, List.mem_cons, List.mem_nil_iff, or_false] at hp
      obtain ⟨b1, b2, b3⟩ := hrd q.1 hq'
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [exRv]
      · simp [exRv]
      · exact b1
      · exact b2
      · exact b3
      · simp [exRv]
      · simp only [exRv, List.mem_singleton]; intro h; rw [h] at hq'; revert hq'; decide
      · simp [exRv]
      · simp [exRv]
      · simp only [exRv, List.mem_append, List.mem_singleton]
        rintro (h | h) <;> (rw [h] at hq'; revert hq'; decide)
      · simp [exRv]
      · simp [exRv])
  have v1 : ∀ y, y ∉ hdNames → τ1.vars y = τ.vars y := fun y hy => g1 y (by rwa [hdFn_names])
  have ev1 : ∀ y v, y ∉ hdNames → τ.vars y = v → (Expr.var y).evalB (W + 1) τ1 = some v :=
    fun y v hy h => ev_var (by rw [v1 y hy, h]) (by rw [← h]; exact hlt.vars _)
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  obtain ⟨τ2, r2, PR2, np2, f2, a2', l2, o2, i2⟩ := stPlan_run (W := W) (l := plFn)
    (ps := psFn M0 iLL e0 nE nS nF nC nL) (τ := τ1) rfl (by rw [a1']; exact har "PR")
    (by simp [plFn]; omega)
    (by
      intro j hj
      simp only [plFn, List.length_cons, List.length_nil] at hj
      have em := ev1 "m0" M0 (by decide) hm0
      have eS := ev1 "nSG" nS (by decide) hnS
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨evalB_lit (by omega), evalB_lit (by omega)⟩
      · exact ⟨em, evalB_lit (by omega)⟩
      · exact ⟨em, evalB_lit (by omega)⟩
      · exact ⟨ev1 "iL" iLL (by decide) hiL, evalB_lit (by omega)⟩
      · exact ⟨evalB_lit (by omega), eS⟩
      · exact ⟨ev_add (ev_add (ev_add (evalB_lit (by omega)) eS (by omega)) (ev1 "nFA" nF (by decide) hnF)
          (by omega)) (ev1 "nCO" nC (by decide) hnC) (by omega), ev1 "nLV" nL (by decide) hnL⟩
      · exact ⟨ev1 "e0" e0 (by decide) he0, ev1 "ne" nE (by decide) hne⟩)
    (by decide)
  have hrun := Run.seq r1 r2
  have hs : ∀ y, y ∈ hdNames → τ2.vars y = f y := fun y hy => by
    rw [f2 y (by intro h; subst h; revert hy; decide)]; exact s1 y (by rwa [hdFn_names])
  have hc : plFn.length * ((plFn.map fun p => p.1.size + p.2.size).sum + 6) + 4 = 186 := by decide
  refine ⟨τ2, hrun.mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    PR2, by rw [np2]; rfl, fun y h0 h1 => by rw [f2 y h0, v1 y h1], fun b hb => by rw [a2' b hb, a1'],
    fun b => by
      by_cases hb : b = "PR"
      · subst hb; exact l2
      · rw [a2' b hb, a1']; exact har b,
    Run.envLt hrun hlt, by rw [o2, o1], by rw [i2, i1]⟩
  all_goals first
    | (rw [hs _ (by decide)]; simp [f])

end Lax185574Proofs.ResolveRam.Glue
