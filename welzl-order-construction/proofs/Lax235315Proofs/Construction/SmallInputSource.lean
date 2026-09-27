import Lax235315Proofs.Construction.Correctness
import Lax235315Proofs.Construction.GraphNeighborhood
import Lax235315Proofs.Construction.ReconstructionSource

/-! The degenerate cases whose advertised crossing budget is zero. -/

namespace Lax235315Proofs.Construction.SmallInputSource

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax235315Proofs.Construction.Correctness
open Lax235315Proofs.Construction.Crossing
open Lax235315Proofs.Construction.ReconstructionSource
open Lax235315Proofs.Construction.ReadKeys (scanList)
open Lax235315Proofs.Construction.WelzlProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

lemma crossingCount_eq_zero_of_le_one {n : ℕ} (π : Equiv.Perm (Fin n))
    (hn : n ≤ 1) (X : Set (Fin n)) : crossingCount π X = 0 := by
  unfold crossingCount
  have hempty : {u : Fin n | ∃ v : Fin n,
      (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)} = ∅ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨v, h, _⟩
      have hu := (π u).isLt
      have hv := (π v).isLt
      omega
    · intro h
      exact False.elim h
  rw [hempty]
  simp

/-- On zero or one vertex, the native order has crossing number zero, including
the one-vertex case where the algorithm's branch bound is exactly zero. -/
lemma naturalOrder_small_encodes {n : ℕ} (G : SimpleGraph (Fin n))
    (hn : n ≤ 1) : EncodesGraphWelzlOrder G 1 0 (List.range n) := by
  refine ⟨Equiv.refl (Fin n), ?_, ?_⟩
  · calc
      List.range n = (naturalVertexOrder n).map Fin.val :=
        (naturalVertexOrder_map_val n).symm
      _ = List.ofFn (fun i : Fin n => i.val) := by
        simp [naturalVertexOrder, List.map_ofFn]
      _ = List.ofFn (fun i : Fin n => (Equiv.refl (Fin n)).symm i |>.val) := by
        rfl
  · change crossingNumber (neighborhoodSetSystem G 1) (Equiv.refl (Fin n)) ≤ 0
    apply crossingNumber_le_of_forall
    intro X hX
    rw [crossingCount_eq_zero_of_le_one _ hn X]

/-- From an all-active state with no recorded reductions, the literal source
reconstruction writes the native order within its linear source bound. -/
lemma reconstructAndWrite_allActive {B n : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hround : σ.vars "round" = 0) (hnB : n < B)
    (hactive : σ.arrs "activeA" = arrOf n (fun _ => 1))
    (hnext : σ.arrs "nextVertex" = arrOf n (fun _ => 0))
    (hstarts : σ.arrs "roundStart" = arrOf n (fun _ => 0))
    (hends : σ.arrs "roundEnd" = arrOf n (fun _ => 0))
    (hremoved : σ.arrs "removed" = arrOf n (fun _ => 0))
    (hreps : σ.arrs "removedRep" = arrOf n (fun _ => 0)) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      τ.out = σ.out ++ List.range' 0 n ∧ τ.inp = σ.inp := by
  have hscan' : ∀ start count,
      scanList (fun _ => 1) start count = List.range' start count := by
    intro start count
    induction count generalizing start with
    | zero => simp [scanList]
    | succ count ih => simp [scanList, ih, List.range'_succ]
  have hscan : scanList (fun _ => 1) 0 n = List.range' 0 n := hscan' 0 n
  let boundary : ℕ → ℕ := fun _ => 0
  let zeros : ℕ → ℕ := fun _ => 0
  let orders : ℕ → List ℕ := fun _ => List.range' 0 n
  have hlog : LoggedRestorations 0 boundary zeros zeros orders := by
    refine ⟨(fun _ _ => 0), ?_, ?_, ?_, ?_, ?_⟩ <;> intro r hr <;> omega
  have hrun := reconstructAndWrite_run (B := B) (n := n) (R := 0)
    hn hround (by omega) hnB hactive hnext hstarts hends hremoved hreps
    (by intro r hr; rfl) (by intro r hr; rfl)
    (by intro r hr; rfl) (by intro r hr; simp [boundary])
    (by intro i hi; omega) (by intro i hi; omega)
    (by intro i hi; omega)
    (by intro i hi; omega)
    (by exact hscan.symm)
    (by intro hpos hnil
        rw [hscan] at hnil
        have hl0 : (List.range' 0 n).length = 0 := by
          simpa using congrArg List.length hnil
        have hlen' : (List.range' 0 n).length = n := by simp
        rw [hlen'] at hl0
        omega)
    hlog
    (by simp [orders])
    (by intro v hv; simp only [orders, List.mem_range'] at hv; rcases hv with ⟨i, hi, hv⟩; omega)
  simpa [orders] using hrun

end Lax235315Proofs.Construction.SmallInputSource
