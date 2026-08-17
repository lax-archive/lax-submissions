import Lax3Proofs.Refine.OrderVirtualBucket

/-!
# A reusable single-row interface for implicit graphs

The virtual ordering engine never materializes a CSR for an augmented graph.
Instead a provider regenerates one deduplicated row in a carrier-sized buffer.
`RowRep` is the exact contract between such a provider and elimination.
-/

namespace Lax3Proofs.Refine.OrderVirtualRowRep

open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)

variable {n : ℕ}

/-- The live prefix of a numeric row buffer, as an ordinary list. -/
def rowList (tail : ℕ) (A : ℕ → ℕ) : List ℕ :=
  List.ofFn fun i : Fin tail => A (i : ℕ)

@[simp] theorem length_rowList (tail : ℕ) (A : ℕ → ℕ) :
    (rowList tail A).length = tail := by
  simp [rowList]

theorem mem_rowList_iff {tail : ℕ} {A : ℕ → ℕ} {u : ℕ} :
    u ∈ rowList tail A ↔ ∃ j < tail, A j = u := by
  constructor
  · simp only [rowList, List.mem_ofFn]
    rintro ⟨j, hj⟩
    exact ⟨j, j.isLt, hj⟩
  · rintro ⟨j, hj, heq⟩
    simp only [rowList, List.mem_ofFn]
    exact ⟨⟨j, hj⟩, heq⟩

/-- A prefix enumerates the undirected row of `w` exactly once.  The
cardinality clause is kept explicit: providers normally obtain it directly
from their stamp invariant, and elimination uses it to initialize degrees. -/
structure RowRep (G : SimpleGraph (Fin n)) (w : Fin n)
    (tail : ℕ) (A : ℕ → ℕ) : Prop where
  tail_le : tail ≤ n
  value_lt : ∀ j < tail, A j < n
  nodup : (rowList tail A).Nodup
  adj_iff : ∀ u : Fin n, G.Adj u w ↔ (u : ℕ) ∈ rowList tail A
  card_eq : tail = (nbrsIn G Finset.univ w).card

namespace RowRep

variable {G : SimpleGraph (Fin n)} {w : Fin n} {tail : ℕ} {A : ℕ → ℕ}

theorem exists_slot_iff (h : RowRep G w tail A) {u : ℕ} (hu : u < n) :
    G.Adj ⟨u, hu⟩ w ↔ ∃ j < tail, A j = u := by
  rw [h.adj_iff, mem_rowList_iff]

theorem slot_adj (h : RowRep G w tail A) {j : ℕ} (hj : j < tail) :
    G.Adj ⟨A j, h.value_lt j hj⟩ w := by
  rw [h.adj_iff, mem_rowList_iff]
  exact ⟨j, hj, rfl⟩

theorem slot_ne (h : RowRep G w tail A) {j k : ℕ}
    (hj : j < tail) (hk : k < tail) (hjk : j ≠ k) :
    A j ≠ A k := by
  intro heq
  have hjlen : j < (rowList tail A).length := by simpa using hj
  have hklen : k < (rowList tail A).length := by simpa using hk
  have he : (rowList tail A)[j] = (rowList tail A)[k] := by
    simpa [rowList] using heq
  have hi := (List.Nodup.getElem_inj_iff h.nodup).1 he
  exact hjk (by omega)

theorem no_repeat_before (h : RowRep G w tail A) {j : ℕ} (hj : j < tail) :
    ¬ ∃ p < j, A p = A j := by
  rintro ⟨p, hp, heq⟩
  exact h.slot_ne (lt_trans hp hj) hj (by omega) heq

theorem card_lt (h : RowRep G w tail A) : tail < n + 1 := by
  have := h.tail_le
  omega

/-- Cells beyond the live prefix are irrelevant to a row representation. -/
theorem congr_prefix (h : RowRep G w tail A) {A' : ℕ → ℕ}
    (heq : ∀ j < tail, A' j = A j) : RowRep G w tail A' := by
  have hlist : rowList tail A' = rowList tail A := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simpa [rowList] using heq j (by simpa using hj)
  exact ⟨h.tail_le, fun j hj => by rw [heq j hj]; exact h.value_lt j hj,
    by rw [hlist]; exact h.nodup,
    fun u => by rw [hlist]; exact h.adj_iff u, h.card_eq⟩

end RowRep

/-! ## Prefix hits used by the decrement scan -/

/-- A live vertex has already occurred in the scanned prefix. -/
def Hit (E A : ℕ → ℕ) (j u : ℕ) : Prop :=
  E u = 0 ∧ ∃ p < j, A p = u

theorem hit_zero {E A : ℕ → ℕ} {u : ℕ} : ¬ Hit E A 0 u := by
  simp [Hit]

theorem hit_mono {E A : ℕ → ℕ} {j u : ℕ} (h : Hit E A j u) :
    Hit E A (j + 1) u := by
  obtain ⟨hE, p, hp, hv⟩ := h
  exact ⟨hE, p, by omega, hv⟩

theorem hit_succ {E A : ℕ → ℕ} {j u : ℕ} :
    Hit E A (j + 1) u ↔ Hit E A j u ∨ (E u = 0 ∧ A j = u) := by
  constructor
  · rintro ⟨hE, p, hp, hv⟩
    rcases Nat.lt_or_eq_of_le (by omega : p ≤ j) with hpj | rfl
    · exact Or.inl ⟨hE, p, hpj, hv⟩
    · exact Or.inr ⟨hE, hv⟩
  · rintro (h | ⟨hE, hv⟩)
    · exact hit_mono h
    · exact ⟨hE, j, by omega, hv⟩

theorem hit_last_iff {G : SimpleGraph (Fin n)} {w : Fin n}
    {tail : ℕ} {A E : ℕ → ℕ} (h : RowRep G w tail A)
    {u : ℕ} (hu : u < n) :
    Hit E A tail u ↔ E u = 0 ∧ G.Adj ⟨u, hu⟩ w := by
  rw [Hit, h.exists_slot_iff hu]

/-! ## Axiom audit -/

#print axioms RowRep.slot_ne
#print axioms RowRep.congr_prefix
#print axioms hit_last_iff

end Lax3Proofs.Refine.OrderVirtualRowRep
