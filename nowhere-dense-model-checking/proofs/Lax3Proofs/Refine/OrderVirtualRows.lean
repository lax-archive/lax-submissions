import Lax3Proofs.Refine.OrderVirtualMath

/-!
# Local rows of an implicit augmentation

An implicit ordering engine must be able to regenerate one row while keeping
only carrier-sized stamps.  The identities below express the row of the next
underlying graph as local walks through the current orientation:

* the old in- and out-neighbours;
* two consecutive outgoing arcs;
* two consecutive incoming arcs; and
* two arcs with a common head.

No intermediate edge array occurs in these statements.  Duplicate witnesses
are deliberately left to a single carrier-sized stamp row, just as in the
materialized `RamAugment` implementation.
-/

namespace Lax3Proofs.Refine.OrderVirtualRows

open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment

variable {n : ℕ}

/-- Vertices that demand an arc *into* `v`.  `RamAugment.demandOut`
already records demands from `v`; both directions are needed to enumerate
the undirected row of the next augmentation. -/
noncomputable def demandIn (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  pick (fun u => Demand D u v)

theorem mem_demandIn {D : Orientation n} {u v : Fin n} :
    u ∈ demandIn D v ↔ Demand D u v := mem_pick

/-- Reverse demands are enumerated by incoming two-paths and common-head
two-paths. -/
theorem demandIn_eq (D : Orientation n) (v : Fin n) :
    demandIn D v =
      (D.inN v).biUnion (fun w => D.inN w) ∪
        (outSet D v).biUnion (fun w => D.inN w) := by
  classical
  ext u
  rw [mem_demandIn, Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro (⟨w, huw, hwv⟩ | ⟨w, huw, hvw⟩)
    · exact Or.inl ⟨w, hwv, huw⟩
    · exact Or.inr ⟨w, mem_outSet.2 hvw, huw⟩
  · rintro (⟨w, hwv, huw⟩ | ⟨w, hvw, huw⟩)
    · exact Or.inl ⟨w, huw, hwv⟩
    · exact Or.inr ⟨w, huw, mem_outSet.1 hvw⟩

/-- The entire undirected row of one augmentation can be regenerated from
three local sets of the previous orientation.  Injectivity is the only fact
about the new rank needed to cover a pair demanded in both directions. -/
theorem adjSet_augOr_eq (D : Orientation n) {rank : Fin n → ℕ}
    (hinj : Function.Injective rank) (v : Fin n) :
    adjSet (augOr D rank) v =
      (adjSet D v ∪ demandOut D v ∪ demandIn D v).erase v := by
  classical
  let D' := augOr D rank
  have hstep : AugStep D D' := augStep_augOr D hinj
  ext u
  rw [mem_adjSet, Finset.mem_erase, Finset.mem_union, Finset.mem_union,
    mem_adjSet, mem_demandOut, mem_demandIn]
  constructor
  · intro hadj
    have hne : u ≠ v := by
      rcases hadj with huv | hvu
      · exact D'.ne_of_mem_inN huv
      · exact (D'.ne_of_mem_inN hvu).symm
    refine ⟨hne, ?_⟩
    rcases hadj with huv | hvu
    · rcases hstep.tight u v huv with hold | hd
      · exact Or.inl (Or.inl (Or.inl hold))
      · exact Or.inr hd
    · rcases hstep.tight v u hvu with hold | hd
      · exact Or.inl (Or.inl (Or.inr hold))
      · exact Or.inl (Or.inr hd)
  · rintro ⟨hne, ((hold | hout) | hin)⟩
    · rcases hold with hold | hold
      · exact Or.inl (hstep.mono u v hold)
      · exact Or.inr (hstep.mono v u hold)
    · rcases hout with htrans | hfrat
      · exact adjacent_comm (hstep.trans_cov v u hne.symm htrans)
      · exact adjacent_comm (hstep.frat_cov v u hne.symm hfrat)
    · rcases hin with htrans | hfrat
      · exact hstep.trans_cov u v hne htrans
      · exact hstep.frat_cov u v hne hfrat

/-- The arc rule in the three stamped sets used by a local incoming-row
generator. -/
theorem newArc_in_iff {D : Orientation n} {rank : Fin n → ℕ} {u v : Fin n} :
    NewArc D rank u v ↔
      u ∉ adjSet D v ∧ u ∈ demandIn D v ∧
        (u ∈ demandOut D v → rank u < rank v) := by
  rw [NewArc, mem_adjSet, mem_demandIn, mem_demandOut]

/-- The same rule from the outgoing endpoint. -/
theorem newArc_out_iff {D : Orientation n} {rank : Fin n → ℕ} {u v : Fin n} :
    NewArc D rank v u ↔
      u ∉ adjSet D v ∧ u ∈ demandOut D v ∧
        (u ∈ demandIn D v → rank v < rank u) := by
  rw [NewArc, mem_adjSet, mem_demandIn, mem_demandOut]
  constructor
  · rintro ⟨hadj, hd, hdir⟩
    exact ⟨fun h => hadj (adjacent_comm h), hd, hdir⟩
  · rintro ⟨hadj, hd, hdir⟩
    exact ⟨fun h => hadj (adjacent_comm h), hd, hdir⟩

/-- New incoming neighbours, before union with the old incoming row. -/
noncomputable def inCand (D : Orientation n) (rank : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) := pick (fun u => NewArc D rank u v)

theorem mem_inCand {D : Orientation n} {rank : Fin n → ℕ} {u v : Fin n} :
    u ∈ inCand D rank v ↔ NewArc D rank u v := mem_pick

/-- The semantic candidate set is the locally testable filter of the reverse
demand row.  This is the exact predicate used by the recursive executable
provider: adjacency and the opposite demand are stamps, while the last test
is one read from the saved rank array. -/
theorem inCand_eq_filter (D : Orientation n) (rank : Fin n → ℕ) (v : Fin n) :
    inCand D rank v =
      (demandIn D v).filter fun u =>
        u ∉ adjSet D v ∧ (u ∈ demandOut D v → rank u < rank v) := by
  classical
  ext u
  rw [mem_inCand, newArc_in_iff, Finset.mem_filter]
  tauto

/-- New outgoing neighbours, before union with the old out-row. -/
noncomputable def outCand (D : Orientation n) (rank : Fin n → ℕ) (v : Fin n) :
    Finset (Fin n) := pick (fun u => NewArc D rank v u)

theorem mem_outCand {D : Orientation n} {rank : Fin n → ℕ} {u v : Fin n} :
    u ∈ outCand D rank v ↔ NewArc D rank v u := mem_pick

/-- The outgoing candidates are the analogous filter of the forward demand
row. -/
theorem outCand_eq_filter (D : Orientation n) (rank : Fin n → ℕ) (v : Fin n) :
    outCand D rank v =
      (demandOut D v).filter fun u =>
        u ∉ adjSet D v ∧ (u ∈ demandIn D v → rank v < rank u) := by
  classical
  ext u
  rw [mem_outCand, newArc_out_iff, Finset.mem_filter]
  tauto

/-- An incoming row of the next orientation is the old incoming row plus
exactly the locally filtered reverse-demand candidates. -/
theorem inSet_augOr_eq (D : Orientation n) (rank : Fin n → ℕ) (v : Fin n) :
    (augOr D rank).inN v = D.inN v ∪ inCand D rank v := by
  ext u
  rw [Finset.mem_union, mem_augOr, mem_inCand]

/-- An outgoing row of the next orientation is the old outgoing row plus
exactly the locally filtered outgoing candidates. -/
theorem outSet_augOr_eq (D : Orientation n) (rank : Fin n → ℕ) (v : Fin n) :
    outSet (augOr D rank) v = outSet D v ∪ outCand D rank v := by
  ext u
  rw [Finset.mem_union, mem_outSet, mem_outSet, mem_outCand, mem_augOr]

/-- The row identity specialized to the rank-only chain. -/
theorem rankChain_adjSet_succ {G : SimpleGraph (Fin n)}
    {rank : ℕ → Fin n → ℕ} {i ki : ℕ}
    (hcert : Lax3Proofs.RamElim.ElimCert
      (fratGraph (OrderVirtualMath.rankChain G rank i)) (rank (i + 1)) ki)
    (v : Fin n) :
    adjSet (OrderVirtualMath.rankChain G rank (i + 1)) v =
      (adjSet (OrderVirtualMath.rankChain G rank i) v ∪
        demandOut (OrderVirtualMath.rankChain G rank i) v ∪
        demandIn (OrderVirtualMath.rankChain G rank i) v).erase v := by
  rw [OrderVirtualMath.rankChain_succ]
  exact adjSet_augOr_eq _ hcert.inj v

/-! ## Aggregate work of the local walks -/

/-- Raw common-head witnesses visited while regenerating all fraternity
rows.  Repeated witnesses are counted here; the row stamp removes them from
the emitted row. -/
noncomputable def fratWalkWork (D : Orientation n) : ℕ :=
  ∑ v : Fin n, ∑ w ∈ outSet D v, (D.inN w).card

/-- Raw outgoing two-paths visited while regenerating all rows. -/
noncomputable def transOutWalkWork (D : Orientation n) : ℕ :=
  ∑ v : Fin n, ∑ w ∈ outSet D v, (outSet D w).card

/-- Raw incoming two-paths visited while regenerating all rows. -/
noncomputable def transInWalkWork (D : Orientation n) : ℕ :=
  ∑ v : Fin n, ∑ w ∈ D.inN v, (D.inN w).card

/-- Summing a weight over every out-list is the same as charging each head
once for every incoming arc. -/
theorem sum_outSet_weight (D : Orientation n) (f : Fin n → ℕ) :
    (∑ v : Fin n, ∑ w ∈ outSet D v, f w) =
      ∑ w : Fin n, (D.inN w).card * f w := by
  classical
  simp only [outSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp [Finset.sum_ite_irrel, Finset.sum_const, smul_eq_mul]

/-- Common-head enumeration is globally `n * d²` under an in-degree bound,
even though one vertex may have unbounded out-degree. -/
theorem fratWalkWork_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    fratWalkWork D ≤ n * (d * d) := by
  classical
  calc
    fratWalkWork D
        ≤ ∑ v : Fin n, ∑ _w ∈ outSet D v, d :=
          Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hd w
    _ = (∑ v : Fin n, (outSet D v).card) * d := by
          simp only [Finset.sum_const, smul_eq_mul, Finset.sum_mul]
    _ = (∑ w : Fin n, (D.inN w).card) * d := by rw [sum_card_outSet]
    _ ≤ (∑ _w : Fin n, d) * d :=
          Nat.mul_le_mul_right d (Finset.sum_le_sum fun w _ => hd w)
    _ = n * (d * d) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          simp [mul_assoc]

/-- Incoming two-path enumeration has the same global bound. -/
theorem transInWalkWork_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    transInWalkWork D ≤ n * (d * d) := by
  classical
  calc
    transInWalkWork D
        ≤ ∑ v : Fin n, ∑ _w ∈ D.inN v, d :=
          Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hd w
    _ = ∑ v : Fin n, (D.inN v).card * d := by
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ _v : Fin n, d * d :=
          Finset.sum_le_sum fun v _ => Nat.mul_le_mul_right d (hd v)
    _ = n * (d * d) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Outgoing two-path enumeration is also globally `n * d²`: exchange the
middle vertex first, then charge its out-list at most `d` times. -/
theorem transOutWalkWork_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    transOutWalkWork D ≤ n * (d * d) := by
  classical
  rw [transOutWalkWork, sum_outSet_weight]
  calc
    (∑ w : Fin n, (D.inN w).card * (outSet D w).card)
        ≤ ∑ w : Fin n, d * (outSet D w).card :=
          Finset.sum_le_sum fun w _ => Nat.mul_le_mul_right _ (hd w)
    _ = d * ∑ w : Fin n, (outSet D w).card := by
          rw [Finset.mul_sum]
    _ = d * ∑ w : Fin n, (D.inN w).card := by rw [sum_card_outSet]
    _ ≤ d * ∑ _w : Fin n, d :=
          Nat.mul_le_mul_left d (Finset.sum_le_sum fun w _ => hd w)
    _ = n * (d * d) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          simp [mul_assoc, mul_left_comm, mul_comm]

end Lax3Proofs.Refine.OrderVirtualRows
