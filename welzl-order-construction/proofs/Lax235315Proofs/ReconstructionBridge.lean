import Lax235315.ReconstructionCorrectness
import Lax235315Proofs.Construction.Reconstruction
import Lax235315Proofs.Construction.Correctness
import Lax235315Proofs.Construction.ListCrossing

namespace Lax235315Proofs.ReconstructionBridge

open Lax235315.TwinReconstruction
open Lax235315Proofs.Construction.Reconstruction

private lemma insertAfter_eq {n : ℕ} (a x : Fin n) (l : List (Fin n)) :
    Lax235315.TwinReconstruction.insertAfter a x l =
      Lax235315Proofs.Construction.ListCrossing.insertAfter a x l := by
  induction l with
  | nil => rfl
  | cons v rest ih =>
      simp [Lax235315.TwinReconstruction.insertAfter,
        Lax235315Proofs.Construction.ListCrossing.insertAfter, ih]

private lemma twinExpansion_toConstruction {n : ℕ} {G : SimpleGraph (Fin n)}
    {B : Set (Fin n)} {small big : List (Fin n)}
    (h : Lax235315.TwinReconstruction.TwinExpansion G B small big) :
    Lax235315Proofs.Construction.Reconstruction.TwinExpansion G B small big := by
  induction h with
  | refl => exact .refl _
  | insert previous present fresh twins ih =>
      rw [insertAfter_eq]
      exact .insert ih present fresh twins

private def reduction_toConstruction {n k : ℕ} {G : SimpleGraph (Fin n)}
    {A B A' B' : Set (Fin n)} {small big : List (Fin n)}
    (h : Lax235315.TwinReconstruction.Reduction G k A B A' B' small big) :
    Lax235315Proofs.Construction.Reconstruction.Reduction G k A B A' B' small big :=
  { small_enumerates := h.small_enumerates
    big_enumerates := h.big_enumerates
    expands := twinExpansion_toConstruction h.expands
    representative := h.representative
    representative_mem := h.representative_mem
    near := h.near }

private lemma run_toCertifiedRun {n k q rounds : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Set (Fin n)} {l : List (Fin n)}
    (h : Lax235315.TwinReconstruction.Run G k q rounds A B l) :
    Lax235315Proofs.Construction.Reconstruction.CertifiedRun G k q rounds A B l := by
  induction h with
  | base enumerates small => exact .base enumerates small
  | step reduction tail ih =>
      exact .step (reduction_toConstruction reduction) ih

/--
---
conclusion: Lax235315.ReconstructionCorrectness.encodesGraphWelzlOrder
---
The public reconstruction certificate has exactly the same content as the
proof-side certificate, so the established crossing induction proves its
encoded graph Welzl order.

# Proof strategy
Convert each public twin expansion, checked reduction, and run to the
corresponding proof-side certificate by induction on the constructors. The
lists, sets, and checks agree directly; then apply the existing certified-run
correctness theorem.

# Attribution
This bridge carries the reconstruction correctness proof of Theorem 3.2 in
Dreier and Kuske, *Near-Linear Time Computation of Welzl Orders on Graphs with
Linear Neighborhood Complexity*, into the submitted certificate types.
-/
lemma encodesGraphWelzlOrder {n k q rounds bound : ℕ}
    (G : SimpleGraph (Fin n)) (l : List (Fin n))
    (h : Lax235315.TwinReconstruction.Run G k q rounds Set.univ Set.univ l)
    (hkq : 2 * k ≤ q) (hbound : (rounds + 1) * q ≤ bound) :
    Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1 bound (l.map Fin.val) := by
  exact Lax235315Proofs.Construction.Correctness.certifiedRun_encodesGraphWelzlOrder
    G l (run_toCertifiedRun h) hkq hbound

end Lax235315Proofs.ReconstructionBridge
