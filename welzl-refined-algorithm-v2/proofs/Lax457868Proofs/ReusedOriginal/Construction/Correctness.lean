/-
Reused source module: `Lax235315Proofs.Construction.Correctness`.
Source: https://github.com/lax-archive/lax-submissions/tree/33f2eca4379b6ff944489c7c59ac1990c286c21b/welzl-order-construction/proofs
License: Apache-2.0.
The mathematical code is unchanged except for namespace transport.
-/
import Lax457868Proofs.ReusedOriginal.Construction.Crossing
import Lax457868Proofs.ReusedOriginal.Construction.GraphNeighborhood
import Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding
import Lax457868Proofs.ReusedOriginal.Construction.Reconstruction
import Lax195003.WelzlOrdersComputation
import Mathlib.Tactic.Ring

/-!
Conversion of a successful reconstruction certificate into the exact output
predicate of the submitted theorem.
-/

namespace Lax457868Proofs.ReusedOriginal.Construction.Correctness

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersInGraphs
open Lax457868Proofs.ReusedOriginal.Construction.Reconstruction

noncomputable section

/-- Vertices in their native `Fin` order. -/
def naturalVertexOrder (n : ℕ) : List (Fin n) :=
  List.ofFn id

lemma naturalVertexOrder_enumerates (n : ℕ) :
    Enumerates (Set.univ : Set (Fin n)) (naturalVertexOrder n) := by
  constructor
  · exact List.nodup_ofFn.mpr Function.injective_id
  · intro v
    simp [naturalVertexOrder]

lemma naturalVertexOrder_map_val (n : ℕ) :
    (naturalVertexOrder n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp [naturalVertexOrder]
  · intro i h₁ h₂
    simp [naturalVertexOrder]

/-- A certified run on both full vertex sides yields exactly the graph Welzl
order encoding used by the submission. -/
lemma certifiedRun_encodesGraphWelzlOrder {n k q rounds bound : ℕ}
    (G : SimpleGraph (Fin n)) (l : List (Fin n))
    (h : CertifiedRun G k q rounds Set.univ Set.univ l)
    (hkq : 2 * k ≤ q) (hbound : (rounds + 1) * q ≤ bound) :
    EncodesGraphWelzlOrder G 1 bound (l.map Fin.val) := by
  have henum := h.enumerates G
  have hl : l.Nodup := henum.1
  have hall : ∀ v : Fin n, v ∈ l := fun v => by
    simpa using (henum.2 v).mpr (Set.mem_univ v)
  have hlen : l.length = n := by
    rw [henum.length_eq_ncard]
    simp
  let π := Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding.permutationOfList l hl hall hlen
  refine ⟨π, ?_, ?_⟩
  · exact Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding.map_val_eq_ofFn l hl hall hlen
  · unfold IsWelzlOrder
    apply Lax457868Proofs.ReusedOriginal.Construction.Crossing.crossingNumber_le_of_forall
    intro X hX
    rw [Lax457868Proofs.ReusedOriginal.Construction.GraphNeighborhood.neighborhoodSetSystem_one] at hX
    obtain ⟨v, rfl⟩ := hX
    rw [Lax457868Proofs.ReusedOriginal.Construction.OrderEncoding.crossingCount_permutationOfList]
    exact (h.crossingCount_le G hkq v (Set.mem_univ v)).trans hbound

/-- The paper's choice `q = 12 c² log n`, together with at most `log n - 1`
reduction rounds, gives the advertised `12 c² log² n` crossing bound. -/
lemma certifiedRun_encodesGraphWelzlOrder_paperBound {n c rounds : ℕ}
    (G : SimpleGraph (Fin n)) (l : List (Fin n))
    (h : CertifiedRun G
      (6 * c ^ 2 * Nat.clog 2 n)
      (12 * c ^ 2 * Nat.clog 2 n)
      rounds Set.univ Set.univ l)
    (hrounds : rounds + 1 ≤ Nat.clog 2 n) :
    EncodesGraphWelzlOrder G 1
      (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) (l.map Fin.val) := by
  apply certifiedRun_encodesGraphWelzlOrder G l h
  · ring_nf
    exact le_rfl
  · calc
      (rounds + 1) * (12 * c ^ 2 * Nat.clog 2 n) ≤
          Nat.clog 2 n * (12 * c ^ 2 * Nat.clog 2 n) :=
        Nat.mul_le_mul_right _ hrounds
      _ = 12 * c ^ 2 * (Nat.clog 2 n) ^ 2 := by ring

/-- On a small instance the native order is already within any bound at
least `n`; this is the deterministic base branch of the implementation. -/
lemma naturalOrder_encodesGraphWelzlOrder {n bound : ℕ}
    (G : SimpleGraph (Fin n)) (hbound : n ≤ bound) :
    EncodesGraphWelzlOrder G 1 bound (List.range n) := by
  have hrun : CertifiedRun G 0 n 0 Set.univ Set.univ
      (naturalVertexOrder n) :=
    CertifiedRun.base (naturalVertexOrder_enumerates n) (by simp)
  have hout : EncodesGraphWelzlOrder G 1 bound
      ((naturalVertexOrder n).map Fin.val) :=
    certifiedRun_encodesGraphWelzlOrder (bound := bound) G
      (naturalVertexOrder n) hrun (by simp) (by simpa using hbound)
  rwa [naturalVertexOrder_map_val] at hout

end

end Lax457868Proofs.ReusedOriginal.Construction.Correctness
