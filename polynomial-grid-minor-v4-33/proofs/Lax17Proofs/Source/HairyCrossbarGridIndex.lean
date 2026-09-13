import Mathlib.Tactic
import Lax17Proofs.Source.GridContract

namespace Lax17Proofs

universe u v w

/-!
# Index conventions for hairy crossbar-grid assembly

This definition-only module records the paper's one-based parity convention
for clusters.  A zero-based `Fin` index is odd in the paper's one-based
numbering exactly when its natural value is even.
-/

namespace SimpleGraph
namespace HairyCrossbarGrid

/-- A zero-based `Fin` index is odd in the paper's one-based convention exactly
when its natural value is even. -/
def OneBasedOdd {ell : ℕ} (i : Fin ell) : Prop :=
  i.1 % 2 = 0

namespace OneBasedOdd

/-- The one-based parity convention is preserved when an index is cast into a
longer cluster sequence. -/
theorem castLE {ell ell' : ℕ} (hle : ell ≤ ell') {i : Fin ell}
    (h : OneBasedOdd i) : OneBasedOdd (Fin.castLE hle i) := by
  simpa [OneBasedOdd, Fin.val_castLE] using h

end OneBasedOdd

/-- The `i`th odd one-based cluster among the first `2 * m` zero-based
positions.  Since one-based odd clusters are exactly the zero-based even
indices, this is the index with value `2 * i`. -/
def oddClusterIndex {ell m : ℕ} (hlen : 2 * m ≤ ell) (i : Fin m) :
    Fin ell :=
  ⟨2 * i.1, by
    have hi : i.1 < m := i.2
    omega⟩

@[simp] theorem oddClusterIndex_val {ell m : ℕ} (hlen : 2 * m ≤ ell)
    (i : Fin m) :
    (oddClusterIndex hlen i).1 = 2 * i.1 := rfl

/-- The selected cluster indices are odd in the paper's one-based convention. -/
theorem oddClusterIndex_oneBasedOdd {ell m : ℕ} (hlen : 2 * m ≤ ell)
    (i : Fin m) :
    OneBasedOdd (oddClusterIndex hlen i) := by
  simp [OneBasedOdd, oddClusterIndex]

/-- The selected odd cluster indices are strictly order-preserving. -/
theorem oddClusterIndex_lt_of_lt {ell m : ℕ} {hlen : 2 * m ≤ ell}
    {i j : Fin m} (hij : i.1 < j.1) :
    (oddClusterIndex hlen i).1 < (oddClusterIndex hlen j).1 := by
  simp [oddClusterIndex]
  omega

/-- The selected odd cluster indices are injective. -/
theorem oddClusterIndex_injective {ell m : ℕ} (hlen : 2 * m ≤ ell) :
    Function.Injective (oddClusterIndex hlen : Fin m → Fin ell) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp [oddClusterIndex] at hval
  omega

/-- Distinct selected odd cluster indices come from distinct grid rows. -/
theorem oddClusterIndex_ne_of_ne {ell m : ℕ} (hlen : 2 * m ≤ ell)
    {i j : Fin m} (hij : i ≠ j) :
    oddClusterIndex hlen i ≠ oddClusterIndex hlen j := by
  intro h
  exact hij ((oddClusterIndex_injective hlen) h)

/-- The even one-based cluster immediately after a selected odd one-based
cluster.  In zero-based indexing this has value `2*i + 1`. -/
def middleClusterIndex {ell m : ℕ} (hlen : 2 * m ≤ ell) (i : Fin m) :
    Fin ell :=
  ⟨2 * i.1 + 1, by
    have hi : i.1 < m := i.2
    omega⟩

@[simp] theorem middleClusterIndex_val {ell m : ℕ} (hlen : 2 * m ≤ ell)
    (i : Fin m) :
    (middleClusterIndex hlen i).1 = 2 * i.1 + 1 := rfl

/-- The intervening middle cluster indices are injective. -/
theorem middleClusterIndex_injective {ell m : ℕ} (hlen : 2 * m ≤ ell) :
    Function.Injective (middleClusterIndex hlen : Fin m → Fin ell) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp [middleClusterIndex] at hval
  omega

/-- Distinct grid-row indices give distinct intervening middle clusters. -/
theorem middleClusterIndex_ne_of_ne {ell m : ℕ} (hlen : 2 * m ≤ ell)
    {i j : Fin m} (hij : i ≠ j) :
    middleClusterIndex hlen i ≠ middleClusterIndex hlen j := by
  intro h
  exact hij ((middleClusterIndex_injective hlen) h)

/-- A selected odd cluster is never one of the intervening middle clusters. -/
theorem oddClusterIndex_ne_middleClusterIndex {ell m : ℕ}
    (hlen : 2 * m ≤ ell) (i j : Fin m) :
    oddClusterIndex hlen i ≠ middleClusterIndex hlen j := by
  intro h
  have hval := congrArg Fin.val h
  simp [oddClusterIndex, middleClusterIndex] at hval
  omega

/-- A middle cluster is never one of the selected odd clusters. -/
theorem middleClusterIndex_ne_oddClusterIndex {ell m : ℕ}
    (hlen : 2 * m ≤ ell) (i j : Fin m) :
    middleClusterIndex hlen i ≠ oddClusterIndex hlen j := by
  intro h
  exact oddClusterIndex_ne_middleClusterIndex hlen j i h.symm

/-- The gap from a selected odd cluster to the following middle cluster exists. -/
theorem oddClusterIndex_gap {ell m : ℕ} (hlen : 2 * m ≤ ell)
    (i : Fin m) :
    (oddClusterIndex hlen i).1 + 1 < ell := by
  simp [oddClusterIndex]
  omega

@[simp] theorem middleClusterIndex_eq_odd_succ {ell m : ℕ}
    (hlen : 2 * m ≤ ell) (i : Fin m) :
    middleClusterIndex hlen i =
      ⟨(oddClusterIndex hlen i).1 + 1, oddClusterIndex_gap hlen i⟩ := by
  apply Fin.ext
  simp [middleClusterIndex, oddClusterIndex]

/-- If there is a next selected odd cluster, the gap from the middle cluster to
that next odd cluster exists. -/
theorem middleClusterIndex_gap {ell m : ℕ} (hlen : 2 * m ≤ ell)
    {i : Fin m} (hnext : i.1 + 1 < m) :
    (middleClusterIndex hlen i).1 + 1 < ell := by
  simp [middleClusterIndex]
  omega

@[simp] theorem oddClusterIndex_next_eq_middle_succ {ell m : ℕ}
    (hlen : 2 * m ≤ ell) {i : Fin m} (hnext : i.1 + 1 < m) :
    oddClusterIndex hlen ⟨i.1 + 1, hnext⟩ =
      ⟨(middleClusterIndex hlen i).1 + 1,
        middleClusterIndex_gap hlen hnext⟩ := by
  apply Fin.ext
  simp [oddClusterIndex, middleClusterIndex]
  omega

/-- Grid-coordinate indexing of a `g^2`-element path family. -/
noncomputable def gridVertexEquivFin (g : ℕ) :
    GridVertex g ≃ Fin (g ^ 2) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_two]))

@[simp] theorem gridVertexEquivFin_val (g : ℕ) (x : GridVertex g) :
    (gridVertexEquivFin g x).1 = x.1.1 * g + x.2.1 := by
  change ((finCongr (by rw [pow_two]) (finProdFinEquiv x)).1) =
    x.1.1 * g + x.2.1
  simp [finProdFinEquiv]
  rw [Nat.mul_comm, Nat.add_comm]

end HairyCrossbarGrid
end SimpleGraph

end Lax17Proofs
