import Lax185574Proofs.Lib.PartitionMetricConversionDefs
import Lax185574Proofs.Lib.PartitionMetricTransfer
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
Proof of the partition-metric conversion of Bonnet et al., Lemma 8.
Each original part is refined by one Boolean label for every other part.
The local one-part and bipartite conversions ensure that every remaining
edge has a walk of length at most six in every original-partition flip.
Concatenating these walks proves the bound at every radius.
-/

namespace Lax185574Proofs.Lib.PartitionMetricConversion

open Lax185574Proofs.Lib.PartitionMetricConversion PartitionMetricWalks PartitionMetricTransfer

universe u

/--
A single bounded refinement flip approximates every original partition
flip simultaneously, with radius factor six independent of the part count.
-/
theorem exists_refinement_flip {V : Type u} [Fintype V] (G : SimpleGraph V)
    (p : ℕ) (part : V → Fin p) :
    ∃ (q : ℕ) (refined : V → Fin q)
      (toggle : Fin q → Fin q → Bool) (hsymm : ∀ i j, toggle i j = toggle j i),
      q ≤ p * 2 ^ p ∧
      (∀ u v, refined u = refined v → part u = part v) ∧
      ∀ (r : ℕ) (v u : V), Within (flip G refined toggle hsymm) r v u →
        u ∈ partitionBall G part (6 * r) v := by
  classical
  have hbip (i j : Fin p) := BipartiteMetricConversion.exists_split
    (fun x : Fiber part i => fun y : Fiber part j => G.Adj x.val y.val)
  choose left right blocks hblocks using hbip
  have hdiag (i : Fin p) := GraphMetricConversion.exists_toggle
    (G.comap (Subtype.val : Fiber part i → V))
  choose diagonal hdiagonal using hdiag
  let Label := Fin p × (Fin p → Bool)
  let code (v : V) : Label := (part v, fun j =>
    if part v < j then left (part v) j ⟨v, rfl⟩
    else if j < part v then right j (part v) ⟨v, rfl⟩ else false)
  let matrix (a b : Label) : Bool :=
    if a.1 = b.1 then diagonal a.1
    else if a.1 < b.1 then blocks a.1 b.1 (a.2 b.1) (b.2 a.1)
    else blocks b.1 a.1 (b.2 a.1) (a.2 b.1)
  have hmatrix : ∀ a b, matrix a b = matrix b a := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [matrix, hij, hij.ne, hij.ne.symm, not_lt.mpr hij.le]
    · simp [matrix, hij]
    · simp [matrix, hij, hij.ne, hij.ne.symm, not_lt.mpr hij.le]
  have hleft {i j : Fin p} (hij : i < j) (x : Fiber part i) :
      (code x.val).2 j = left i j x := by
    rcases x with ⟨x, hx⟩
    subst i
    simp [code, hij]
  have hright {i j : Fin p} (hij : i < j) (y : Fiber part j) :
      (code y.val).2 i = right i j y := by
    rcases y with ⟨y, hy⟩
    subst j
    simp [code, hij, not_lt.mpr hij.le]
  have hcode_part {i : Fin p} (x : Fiber part i) : (code x.val).1 = i := x.property
  have hmatrix_cross {i j : Fin p} (hij : i < j) (x : Fiber part i) (y : Fiber part j) :
      matrix (code x.val) (code y.val) = blocks i j (left i j x) (right i j y) := by
    simp only [matrix, hcode_part x, hcode_part y, hij.ne, ↓reduceIte, hij,
      hleft hij x, hright hij y]
  have hmatrix_diagonal {i : Fin p} (x y : Fiber part i) :
      matrix (code x.val) (code y.val) = diagonal i := by
    simp [matrix, hcode_part x, hcode_part y]
  let e : Label ≃ Fin (p * 2 ^ p) := Fintype.equivFinOfCardEq (by
    simp [Label])
  let refined : V → Fin (p * 2 ^ p) := fun v => e (code v)
  let toggle (a b : Fin (p * 2 ^ p)) : Bool := matrix (e.symm a) (e.symm b)
  have htoggle : ∀ a b, toggle a b = toggle b a :=
    fun a b => hmatrix (e.symm a) (e.symm b)
  let H := flip G refined toggle htoggle
  have hadj (x y : V) : H.Adj x y ↔
      x ≠ y ∧ Xor (G.Adj x y) (matrix (code x) (code y) = true) := by
    simp [H, Lax185574Proofs.Lib.PartitionMetricConversion.flip, refined, toggle]
  refine ⟨p * 2 ^ p, refined, toggle, htoggle, le_rfl, ?_, ?_⟩
  · intro u v huv
    exact congrArg Prod.fst (e.injective huv)
  · intro r v u hpath T hT
    have hcross {i j : Fin p} (hij : i < j) (x : Fiber part i) (y : Fiber part j)
        (hxy : H.Adj x.val y.val) : Within (flip G part T hT) 6 x.val y.val := by
      have hx := (hadj x.val y.val).mp hxy
      rw [hmatrix_cross hij x y] at hx
      obtain ⟨h₀, h₁⟩ := hblocks i j x y hx.2
      exact bipartite_transfer G part T hT hij.ne h₀ h₁
    apply within_edge_transfer 6 (fun x y hxy => ?_) hpath
    rcases lt_trichotomy (part x) (part y) with hij | hij | hij
    · exact hcross hij ⟨x, rfl⟩ ⟨y, rfl⟩ hxy
    · let a : Fiber part (part x) := ⟨x, rfl⟩
      let b : Fiber part (part x) := ⟨y, hij.symm⟩
      have hx := (hadj x y).mp hxy
      rw [hmatrix_diagonal a b] at hx
      have hab : a ≠ b := fun hab => hx.1 (congrArg Subtype.val hab)
      obtain ⟨h₀, h₁⟩ := hdiagonal (part x) a b hab hx.2
      exact diagonal_transfer G part T hT h₀ h₁
    · exact within_symm (hcross hij ⟨y, rfl⟩ ⟨x, rfl⟩ hxy.symm)

end Lax185574Proofs.Lib.PartitionMetricConversion
