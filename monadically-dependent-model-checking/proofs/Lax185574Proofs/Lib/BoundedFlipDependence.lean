import Lax185574Proofs.Lib.Internal.BoundedFlipDependence
import Lax185574Proofs.Lib.MonadicDependenceClosure
import Lax185574Proofs.Lib.DefinableFlips

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
A fixed interpretation of bounded partition flips. The first block of
colors names parts; the second encodes each row of the toggle matrix as
a vertex set. No extra hypothesis on the source graph class is used.
-/

namespace Lax185574Proofs.Lib.BoundedFlipDependence

open FirstOrder Lax710763.Transductions
open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax185574Proofs.Lib.PartitionMetricConversion Lax185574Proofs.Lib.Internal.BoundedFlipDependence

noncomputable section

private def colorAtom {c k : ℕ} (i : Fin c) (a : Fin k) :
    (withColors Language.graph c).Formula (Fin k) :=
  .rel (.inr (.color i)) (fun _ => .var (.inl a))

private def adjAtom (c : ℕ) : (withColors Language.graph c).Formula (Fin 2) :=
  .rel (.inl .adj) ![.var (.inl 0), .var (.inl 1)]

private def rowFormula (P : ℕ) :
    (withColors Language.graph (P + P)).Formula (Fin 2) :=
  ((Finset.univ : Finset (Fin P)).toList.map (fun i =>
    colorAtom (i.castAdd P) 0 ⊓ colorAtom (i.natAdd P) 1)).foldr (· ⊔ ·) ⊥

private def edgeFormula (P : ℕ) :
    (withColors Language.graph (P + P)).Formula (Fin 2) :=
  (Language.BoundedFormula.equal (.var (.inl 0)) (.var (.inl 1))).not ⊓
    ((adjAtom (P + P)).iff (rowFormula P)).not

private def flipTransduction (P : ℕ) : Transduction Language.graph Language.graph where
  colors := P + P
  domain := ⊤
  rel | .adj => edgeFormula P

private def witnessColors {n p P : ℕ} (hp : p ≤ P) (part : Fin n → Fin p)
    (toggle : Fin p → Fin p → Bool) : Fin (P + P) → Set (Fin n) :=
  Fin.append (fun i => {x | (part x).castLE hp = i})
    (fun i => {y | ∃ a : Fin p, a.castLE hp = i ∧ toggle a (part y) = true})

private theorem realize_colorAtom {n c k : ℕ} (G : SimpleGraph (Fin n))
    (colors : Fin c → Set (Fin n)) (i : Fin c) (a : Fin k) (v : Fin k → Fin n) :
    RealizeIn G.structure colors (colorAtom i a) v ↔ v a ∈ colors i := Iff.rfl

private theorem realize_rowFormula {n p P : ℕ} (G : SimpleGraph (Fin n))
    (hp : p ≤ P) (part : Fin n → Fin p) (toggle : Fin p → Fin p → Bool)
    (v : Fin 2 → Fin n) :
    RealizeIn G.structure (witnessColors hp part toggle) (rowFormula P) v ↔
      toggle (part (v 0)) (part (v 1)) = true := by
  let := G.structure
  let := colorStructure (witnessColors hp part toggle)
  have hrow (i : Fin P) :
      (colorAtom (i.castAdd P) 0 ⊓ colorAtom (i.natAdd P) 1).Realize v ↔
        (part (v 0)).castLE hp = i ∧
          ∃ a : Fin p, a.castLE hp = i ∧ toggle a (part (v 1)) = true := by
    rw [Language.Formula.realize_inf]
    change (RealizeIn G.structure _ (colorAtom _ _) v ∧
      RealizeIn G.structure _ (colorAtom _ _) v) ↔ _
    rw [realize_colorAtom, realize_colorAtom]
    simp only [witnessColors, Fin.append_left, Fin.append_right, Set.mem_ofPred_eq]
  change (rowFormula P).Realize v ↔ _
  unfold Language.Formula.Realize
  rw [rowFormula, Language.BoundedFormula.realize_foldr_sup]
  constructor
  · rintro ⟨φ, hφ, hreal⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hφ
    obtain ⟨hi, a, ha, ht⟩ := (hrow i).mp hreal
    have heq : a = part (v 0) :=
      Fin.ext (congrArg (fun z : Fin P => z.val) (ha.trans hi.symm))
    simpa only [heq] using ht
  · intro ht
    refine ⟨_, List.mem_map.mpr ⟨(part (v 0)).castLE hp, by simp, rfl⟩, ?_⟩
    exact (hrow _).mpr ⟨rfl, part (v 0), rfl, ht⟩

private theorem realize_edgeFormula {n p P : ℕ} (G : SimpleGraph (Fin n))
    (hp : p ≤ P) (part : Fin n → Fin p) (toggle : Fin p → Fin p → Bool)
    (hsymm : ∀ i j, toggle i j = toggle j i) (v : Fin 2 → Fin n) :
    RealizeIn G.structure (witnessColors hp part toggle) (edgeFormula P) v ↔
      (flip G part toggle hsymm).Adj (v 0) (v 1) := by
  let := G.structure
  let := colorStructure (witnessColors hp part toggle)
  change (edgeFormula P).Realize v ↔ _
  rw [edgeFormula, Language.Formula.realize_inf, Language.Formula.realize_not,
    Language.Formula.realize_not, Language.Formula.realize_iff]
  change (v 0 ≠ v 1 ∧ ¬ (G.Adj (v 0) (v 1) ↔
    RealizeIn G.structure (witnessColors hp part toggle) (rowFormula P) v)) ↔ _
  rw [realize_rowFormula]
  change (_ ∧ ¬ (_ ↔ _)) ↔ _ ∧ Xor _ _
  simp only [Xor]
  tauto

/--
One transduction with two blocks of P colors produces every desired flip.
-/
theorem transduces_boundedFlipImage (C : GraphClass) (P : ℕ) :
    Lax710763.GraphTransductions.Transduces C (BoundedFlipImage C P) := by
  refine ⟨flipTransduction P, ?_⟩
  intro n N hN
  obtain ⟨H, hH, rfl⟩ := hN
  obtain ⟨G, hG, p, hp, part, toggle, hsymm, rfl⟩ := hH
  refine ⟨n, G.structure, ⟨G, hG, rfl⟩,
    witnessColors hp part toggle, Function.Embedding.refl _, ?_, ?_⟩
  · intro x
    let := G.structure
    let := colorStructure (witnessColors hp part toggle)
    change (∃ y : Fin n, y = x) ↔
      RealizeIn G.structure (witnessColors hp part toggle)
        (⊤ : (withColors Language.graph (P + P)).Formula (Fin 1)) ![x]
    unfold RealizeIn
    rw [Language.Formula.realize_top]
    exact iff_true_intro ⟨x, rfl⟩
  · intro r R v
    cases R
    exact (realize_edgeFormula G hp part toggle hsymm v).symm

/--
Apply monadic-dependence preservation to the fixed bounded-flip transduction.
-/
theorem monadicallyDependent_boundedFlipImage (C : GraphClass)
    (hC : MonadicallyDependent C) (P : ℕ) :
    MonadicallyDependent (BoundedFlipImage C P) :=
  MonadicDependenceClosure.monadicallyDependent_of_transduces hC
    (transduces_boundedFlipImage C P)

theorem definableFlipImage_subset_boundedFlipImage (C : GraphClass) (s : ℕ)
    (n : ℕ) (H : SimpleGraph (Fin n)) (hH : DefinableFlipImage C s n H) :
    BoundedFlipImage C (4 ^ s) n H := by
  obtain ⟨G, hG, S, hS, hflip⟩ := hH
  obtain ⟨p, part, toggle, hsymm, hp, hH⟩ :=
    DefinableFlips.exists_bounded_partition G H S hflip
  exact ⟨G, hG, p, hp.trans (Nat.pow_le_pow_right (by decide) hS),
    part, toggle, hsymm, hH⟩

/--
Restrict the bounded-flip target class to s-definable flips.
-/
theorem transduces_definableFlipImage (C : GraphClass) (s : ℕ) :
    Lax710763.GraphTransductions.Transduces C (DefinableFlipImage C s) := by
  refine TransductionCalculus.Transduces.mono_target
    (transduces_boundedFlipImage C (4 ^ s)) ?_
  rintro n N ⟨H, hH, rfl⟩
  exact ⟨H, definableFlipImage_subset_boundedFlipImage C s n H hH, rfl⟩

/--
Definable-flip images preserve genuine registered monadic dependence.
-/
theorem monadicallyDependent_definableFlipImage (C : GraphClass)
    (hC : MonadicallyDependent C) (s : ℕ) :
    MonadicallyDependent (DefinableFlipImage C s) :=
  MonadicDependenceClosure.monadicallyDependent_of_transduces hC
    (transduces_definableFlipImage C s)

end

end Lax185574Proofs.Lib.BoundedFlipDependence
