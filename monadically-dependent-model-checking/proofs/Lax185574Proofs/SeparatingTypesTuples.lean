import Lax185574.SeparatingTypes
import Lax185574.SeparatingTypesTuples
import Lax185574Proofs.DistanceFormulaRank
import Lax185574Proofs.TypeCodes

/-!
Proof of the bound on the types of tuples `ā ū` over `U`, where `ā` is far
from `U` and `ū` is a fixed tuple from `U`.
-/

namespace Lax185574Proofs.SeparatingTypesTuples

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574Proofs.DistanceFormulaRank
open Lax185574Proofs.TypeCodes

universe u v z

variable {L : Language.{u, v}} {V : Type z} [L.Structure V]

/-- Replace the last `m` free variables by the parameters `ū`. -/
def plugParams {k m : ℕ} (U : Set V) (w : Fin m → U) : Fin (k + m) ⊕ U → Fin k ⊕ U :=
  Sum.elim (Fin.append (fun i => Sum.inl i) (fun j => Sum.inr (w j))) Sum.inr

theorem elim_comp_plugParams {k m : ℕ} (U : Set V) (w : Fin m → U) (a : Fin k → V) :
    (Sum.elim a Subtype.val ∘ plugParams U w : Fin (k + m) ⊕ U → V) =
      Sum.elim (Fin.append a (Subtype.val ∘ w)) Subtype.val := by
  funext x
  rcases x with i | x
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [plugParams]
    · simp [plugParams]
  · rfl

/-- The type of `ā ū` over `U` is determined by the type of `ā` over `U`. -/
theorem rankTypeOver_append_eq {q k m : ℕ} (U : Set V) (w : Fin m → U) (a b : Fin k → V)
    (h : rankTypeOver (L := L) q U a = rankTypeOver q U b) :
    rankTypeOver (L := L) q U (Fin.append a (Subtype.val ∘ w)) =
      rankTypeOver q U (Fin.append b (Subtype.val ∘ w)) := by
  have key : ∀ (c : Fin k → V) (φ : L.Formula (Fin (k + m) ⊕ U)),
      φ ∈ rankTypeOver q U (Fin.append c (Subtype.val ∘ w)) ↔
        φ.relabel (plugParams U w) ∈ rankTypeOver q U c := by
    intro c φ
    simp only [rankTypeOver, Set.mem_ofPred_eq, Formula.realize_relabel,
      elim_comp_plugParams]
    unfold Formula.relabel
    rw [qr_relabel]
  ext φ
  rw [key, key, h]

/--
---
conclusion: Lax185574.SeparatingTypesTuples.ncard_rankTypeOver_append_le
---
The bound follows from `SeparatingTypes`, since for a fixed tuple `ū` from
`U` the type of `ā ū` over `U` is determined by the type of `ā` over `U`.
A formula about `ā ū` becomes a formula about `ā` of the same quantifier
rank when the variables for `ū` are replaced by the parameters `ū`.
-/
theorem ncard_rankTypeOver_append_le (q : ℕ) :
    ∃ r : ℕ, ∀ k c : ℕ, ∃ T : ℕ,
      ∀ (V : Type z) [Finite V] (G : SimpleGraph V) (colors : Fin c → Set V)
        (U : Set V) (m : ℕ) (u : Fin m → V), (∀ i, u i ∈ U) →
        ((fun a : Fin k → V =>
            @rankTypeOver (Lax710763.Transductions.withColors Language.graph c) V
              (Lax185574.Colorings.expansion G colors) q U
              (k + m) (Fin.append a u)) ''
          {a | ∀ i, a i ∉ Lax185574.GraphBalls.graphBall G r U}).ncard ≤ T := by
  obtain ⟨r, hr⟩ := Lax185574.SeparatingTypes.typeCountOver_far_le.{z} q
  refine ⟨r, fun k c => ?_⟩
  obtain ⟨T, hT⟩ := hr k c
  refine ⟨T, fun V _ G colors U m u hu => ?_⟩
  let _ := Lax185574.Colorings.expansion G colors
  refine le_trans ?_ (hT V G colors U)
  let w : Fin m → U := fun j => ⟨u j, hu j⟩
  have hw : u = Subtype.val ∘ w := rfl
  rw [hw]
  apply ncard_image_le_of_factor (Set.toFinite _)
  intro a _ b _ hab
  exact rankTypeOver_append_eq U w a b hab

end Lax185574Proofs.SeparatingTypesTuples
