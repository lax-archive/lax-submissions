/-
A general-purpose criterion, with nothing about transducers in it: a function on
strings which admits a *Hankel decomposition* of size `D` — that is, which can be
written as

  `f (u ++ v) = ∑ i, g i u * h i v`

for finitely many pairs of functions indexed by a type of cardinality `D` — is
identically zero as soon as it vanishes on the strings of length at most `D`.

This is the form of Schützenberger's zeroness criterion that
`RequestProject/PartC/RegHankel.lean` needs.  The project already has the
criterion for a *linear representation*
(`Transducers.linRep_zero_of_short`, `RequestProject/PartB/WeightedZero.lean`);
the point of the version below is that it asks only for a factorisation of `f`
through a finite index set, and not for an automaton, so that it can be applied
to a two-way transducer through the decomposition of a run at a cut of the input
without ever building the automaton.

The proof is the usual one for the rank of a Hankel matrix.  The *rows* of `f`
are the functions `row f u : v ↦ f (u ++ v)`; a Hankel decomposition of size `D`
puts all of them inside the span of the `D` functions `h i`, so the increasing
sequence of subspaces `Vk f k` spanned by the rows of the strings of length at
most `k` has dimension at most `D` and must stop growing at some `k ≤ D`.  A
subspace of rows which is stable under the shifts `φ ↦ (v ↦ φ (a :: v))` and
contains the row of the empty string contains every row, so `Vk f k` contains
all of them; and if `f` vanishes on the strings of length at most `k` then every
generator of `Vk f k`, hence every element of it, vanishes at the empty string.
-/
import Mathlib

namespace Lax916827Proofs.Transducers

namespace HankelRank

variable {A : Type}

/-- The row of `f` indexed by the string `u`: the function `v ↦ f (u ++ v)`. -/
def row (f : List A → ℚ) (u : List A) : List A → ℚ := fun v => f (u ++ v)

/-- The shift of a function on strings by a letter. -/
def shift (a : A) : (List A → ℚ) →ₗ[ℚ] (List A → ℚ) where
  toFun φ := fun v => φ (a :: v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shift_row (f : List A → ℚ) (u : List A) (a : A) :
    shift a (row f u) = row f (u ++ [a]) := by
  funext v
  simp [shift, row]

/-- The span of the rows of the strings of length at most `k`. -/
def Vk (f : List A → ℚ) (k : ℕ) : Submodule ℚ (List A → ℚ) :=
  Submodule.span ℚ {φ | ∃ u : List A, u.length ≤ k ∧ φ = row f u}

lemma row_mem_Vk {f : List A → ℚ} {u : List A} {k : ℕ} (h : u.length ≤ k) :
    row f u ∈ Vk f k :=
  Submodule.subset_span ⟨u, h, rfl⟩

lemma Vk_mono (f : List A → ℚ) {k l : ℕ} (h : k ≤ l) : Vk f k ≤ Vk f l := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨u, hu, rfl⟩
  exact row_mem_Vk (hu.trans h)

lemma shift_Vk_le (f : List A → ℚ) (a : A) (k : ℕ) :
    (Vk f k).map (shift a) ≤ Vk f (k + 1) := by
  rw [Vk, Submodule.map_span, Submodule.span_le]
  rintro φ ⟨ψ, ⟨u, hu, rfl⟩, rfl⟩
  rw [shift_row]
  exact row_mem_Vk (by simpa using Nat.succ_le_succ hu)

/-- If the span of the rows stops growing at `k`, it contains every row. -/
lemma row_mem_of_stab {f : List A → ℚ} {k : ℕ} (hstab : Vk f (k + 1) = Vk f k) (u : List A) :
    row f u ∈ Vk f k := by
  induction u using List.reverseRecOn with
  | nil => exact row_mem_Vk (by simp)
  | append_singleton u a ih =>
      have : shift a (row f u) ∈ Vk f (k + 1) :=
        shift_Vk_le f a k ⟨row f u, ih, rfl⟩
      rw [hstab, shift_row] at this
      exact this

variable {ι : Type} [Fintype ι]

/-- **The Hankel criterion.**  A function on strings which factors through a
finite index set as `f (u ++ v) = ∑ i, g i u * h i v` and which vanishes on all
strings of length at most the cardinality of the index set vanishes
everywhere. -/
theorem zero_of_short {f : List A → ℚ} {g h : ι → List A → ℚ}
    (hdec : ∀ u v : List A, f (u ++ v) = ∑ i, g i u * h i v)
    (hshort : ∀ w : List A, w.length ≤ Fintype.card ι → f w = 0) :
    ∀ w : List A, f w = 0 := by
  classical
  set D := Fintype.card ι with hD
  -- every row lies in the span of the `h i`
  set W : Submodule ℚ (List A → ℚ) := Submodule.span ℚ (Set.range h) with hW
  have hWfin : FiniteDimensional ℚ W := by
    rw [hW]
    exact FiniteDimensional.span_of_finite ℚ (Set.finite_range h)
  have hrowW : ∀ u : List A, row f u ∈ W := by
    intro u
    have : row f u = ∑ i, g i u • h i := by
      funext v
      simp only [row, hdec u v, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVW : ∀ k, Vk f k ≤ W := by
    intro k
    exact Submodule.span_le.2 (by rintro φ ⟨u, -, rfl⟩; exact hrowW u)
  have hWcard : Module.finrank ℚ W ≤ D := by
    rw [hW, hD]
    calc Module.finrank ℚ (Submodule.span ℚ (Set.range h))
        ≤ (Set.range h).toFinset.card := finrank_span_le_card _
      _ ≤ Fintype.card ι := by
          rw [Set.toFinset_range]
          simpa using Finset.card_image_le (s := (Finset.univ : Finset ι)) (f := h)
  -- so the dimensions of the `Vk f k` are bounded by `D`
  have hfinV : ∀ k, FiniteDimensional ℚ (Vk f k) := fun k =>
    Submodule.finiteDimensional_of_le (hVW k)
  have hVcard : ∀ k, Module.finrank ℚ (Vk f k) ≤ D := by
    intro k
    haveI := hWfin
    exact le_trans (Submodule.finrank_mono (hVW k)) hWcard
  -- the sequence must stop growing at some `k ≤ D`
  have hstab : ∃ k ≤ D, Vk f (k + 1) = Vk f k := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ k ≤ D, Module.finrank ℚ (Vk f k) < Module.finrank ℚ (Vk f (k + 1)) := by
      intro k hk
      haveI := hfinV (k + 1)
      exact Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (Vk_mono f (Nat.le_succ k)) (fun hh => hcon k hk hh.symm))
    have hgrow : ∀ k ≤ D + 1, k ≤ Module.finrank ℚ (Vk f k) := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
          intro hk
          have h1 : k ≤ Module.finrank ℚ (Vk f k) := ih (by omega)
          have h2 := hlt k (by omega)
          omega
    have := hgrow (D + 1) le_rfl
    have := hVcard (D + 1)
    omega
  obtain ⟨k, hkD, hk⟩ := hstab
  -- and then every row lies in `Vk f k`, whose elements all vanish at the empty string
  have hev : Vk f k ≤ LinearMap.ker (LinearMap.proj (R := ℚ) (φ := fun _ : List A => ℚ) ([] : List A)) := by
    refine Submodule.span_le.2 ?_
    rintro φ ⟨u, hu, rfl⟩
    have : f u = 0 := hshort u (hu.trans hkD)
    simpa [LinearMap.mem_ker, row] using this
  intro w
  have hmem := hev (row_mem_of_stab hk w)
  simpa [LinearMap.mem_ker, row] using hmem

end HankelRank

end Lax916827Proofs.Transducers
