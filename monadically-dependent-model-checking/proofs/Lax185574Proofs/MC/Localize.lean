import Lax185574.DistanceLogic
import Lax185574.ConstructionSequences
import Lax185574Proofs.Legacy
import Mathlib.Tactic

/-!
The localization `φ^loc(x)` of a sentence, used at the end of the proof
of thm:mc (model-checking.tex, proof of thm:mc). Every quantifier
`∃ y` at nesting depth `j` becomes `∃ y (dist(x, y) ≤ ρ⁺(j + 2, q − j − 1) ∧ …)`,
which has distance rank `(1, q)`. In a partial graph whose pairs are all
resolved every vertex is within distance one of every other, so the
localization does not change the truth value.
-/

namespace Lax185574Proofs.MC

open Lax185574.PartialGraphs Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The localization of a formula with `ℓ` free variables at the depth
bound `q`: the free variables move up by one, the new variable `0` is
`x`, and every quantifier is guarded by `x` at radius
`ρ⁺(ℓ + 2, q − ℓ − 1)`. -/
def loc (q : ℕ) : {ℓ : ℕ} → Lax3.FirstOrder.FO ℓ → DistFO (ℓ + 1)
  | _, .adj i j => .edge i.succ j.succ
  | _, .eq i j => .eq i.succ j.succ
  | _, .not φ => .not (loc q φ)
  | _, .and φ ψ => .and (loc q φ) (loc q ψ)
  | ℓ, .ex φ => .exLocal 0 (rhoPlus (ℓ + 2) (q - ℓ - 1)) (loc q φ)

/-- The localization has distance rank `(ℓ + 1, q − ℓ)` when the
quantifier rank leaves room. -/
theorem loc_drank (q : ℕ) : ∀ {ℓ : ℕ} (φ : Lax3.FirstOrder.FO ℓ), Lax3.FirstOrder.rank φ + ℓ ≤ q →
    DRank (ℓ + 1) (q - ℓ) (loc q φ)
  | _, .adj i j, _ => DRank.edge _ _
  | _, .eq i j, _ => DRank.eq _ _
  | _, .not φ, h => DRank.not (loc_drank q φ (by simpa [Lax3.FirstOrder.rank] using h))
  | _, .and φ ψ, h => by
      simp only [Lax3.FirstOrder.rank] at h
      exact DRank.and (loc_drank q φ (by omega)) (loc_drank q ψ (by omega))
  | ℓ, .ex φ, h => by
      simp only [Lax3.FirstOrder.rank] at h
      have hq : q - ℓ = (q - (ℓ + 1)) + 1 := by omega
      have := loc_drank q φ (by omega)
      rw [hq]
      show DRank (ℓ + 1) (q - (ℓ + 1) + 1) (.exLocal 0 (rhoPlus (ℓ + 2) (q - ℓ - 1)) (loc q φ))
      rw [show q - ℓ - 1 = q - (ℓ + 1) by omega]
      exact DRank.exLocal 0 this

theorem one_le_rhoPlus (k q : ℕ) : 1 ≤ rhoPlus k q := Nat.one_le_pow _ _ (by decide)

/-- In a partial graph whose resolved pairs are all pairs, and whose
edges are those of `G`, the localization holds of `x` exactly when the
formula holds in `G`. -/
theorem sat_loc {n : ℕ} (G : SimpleGraph (Fin n)) (H : PartialGraph (Fin n))
    (hE : H.edge = G) (hR : ∀ u v : Fin n, u ≠ v → H.resolved.Adj u v) (q : ℕ) (a : Fin n) :
    ∀ {ℓ : ℕ} (φ : Lax3.FirstOrder.FO ℓ) (m : Fin ℓ → Fin n),
      Sat H (Fin.cons a m) (loc q φ) ↔ Lax3.FirstOrder.Sat G m φ
  | _, .adj i j, m => by simp [loc, Sat, Lax3.FirstOrder.Sat, hE]
  | _, .eq i j, m => by simp [loc, Sat, Lax3.FirstOrder.Sat]
  | _, .not φ, m => by
      simp only [loc, Sat, Lax3.FirstOrder.Sat]; rw [sat_loc G H hE hR q a φ m]
  | _, .and φ ψ, m => by
      simp only [loc, Sat, Lax3.FirstOrder.Sat]
      rw [sat_loc G H hE hR q a φ m, sat_loc G H hE hR q a ψ m]
  | ℓ, .ex φ, m => by
      simp only [loc, Sat, Lax3.FirstOrder.Sat]
      refine exists_congr fun v => ?_
      rw [Fin.cons_snoc_eq_snoc_cons a m v |>.symm, sat_loc G H hE hR q a φ (Fin.snoc m v)]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        simp only [Fin.cons_zero]
        by_cases hv : a = v
        · subst hv; exact ⟨SimpleGraph.Walk.nil, by simp⟩
        · exact ⟨SimpleGraph.Walk.cons (hR a v hv) SimpleGraph.Walk.nil,
            by simp; exact one_le_rhoPlus _ _⟩

/-- **Localization of a sentence.** In the last partial graph of a
construction sequence of `G`, the localization of a sentence `φ` of
quantifier rank at most `q` has distance rank `(1, q)` and holds of any
vertex exactly when `G ⊨ φ`. -/
theorem sat_loc_sentence {n : ℕ} (G : SimpleGraph (Fin n)) (H : PartialGraph (Fin n))
    (hE : H.edge = G) (hN : H.nonEdge = Gᶜ) (q : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (hq : Lax3.FirstOrder.rank φ ≤ q) (a : Fin n) :
    DRank 1 q (loc q φ) ∧ (Sat H ![a] (loc q φ) ↔ Lax3.FirstOrder.Sat G Fin.elim0 φ) := by
  refine ⟨by simpa using loc_drank q φ (by omega), ?_⟩
  have hR : ∀ u v : Fin n, u ≠ v → H.resolved.Adj u v := by
    intro u v huv
    simp only [PartialGraph.resolved, SimpleGraph.sup_adj, hE, hN, SimpleGraph.compl_adj]
    tauto
  have := sat_loc G H hE hR q a φ Fin.elim0
  rwa [show (Fin.cons a Fin.elim0 : Fin 1 → Fin n) = ![a] by ext i; fin_cases i; rfl] at this

end Lax185574Proofs.MC
