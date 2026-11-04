import Lax185574Proofs.TypeTreeSizes

/-!
The size of a type tree, bounded by any number `K` that bounds the colors
meeting the ball of radius `ρ⁺(k, q)` around the vertex and the number of
nodes of tuples from this ball, per rank and arity. The proof uses
lem:locality only. Adapted from `TypeTreeSizes.lean`, where `K` is the
number of types of tuples from the ball.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574Proofs.TypeTreeSizes
open Lax3.DistFO (rhoMinus rhoPlus)

section Size

variable {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) (v : Fin n) (K : ℕ)

/-- The counting hypotheses: at most `K` colors meet the ball, and at most
`K` nodes per rank `(k+i, q−i)` and arity `ℓ ∈ [k+i]` belong to tuples
from the ball. -/
structure BallCounts : Prop where
  colors : (G.color '' G.ball (rhoPlus k q) v).ncard ≤ K
  nodes : ∀ (i m ℓ : ℕ), i ≤ q → m = q - i → 1 ≤ ℓ → ℓ ≤ k + i →
    {μ : Node m ℓ | ∃ u : Fin ℓ → Fin n, (∀ t, u t ∈ G.ball (rhoPlus k q) v) ∧
      μ = node G (k + i) m u}.ncard ≤ K

variable {G k q v K}

theorem atoms_length_le_of (hK : BallCounts G k q v K) (j m : ℕ) (hj : j + m = q)
    (w : Fin (j + 1) → Fin n) (hw0 : w 0 = v) (hw : Guarded G k q j w) :
    wordLength (finsetOf (atp G (k + j) m w)) ≤ atomBound k q K := by
  have hloc := Lax185574.TreeLocality.ball_of_guarded G k q j (by omega) w hw
  rw [hw0, show q - j = m by omega] at hloc
  refine le_trans (wordLength_finset_le _ 5
    (fun φ hφ => wordLength_atom_le φ (mem_of_mem_finsetOf hφ).1)) ?_
  rw [card_finsetOf]
  have hR : rhoPlus (k + j) m ≤ rhoPlus k q := by
    have := rhoPlus_shift_le k q j (by omega)
    rwa [show q - j = m by omega] at this
  have hA := ncard_atp_le G (k + j) m (j + 1) w (rhoPlus k q) hR
    (G.color '' G.ball (rhoPlus k q) v) (Set.toFinite _)
    (fun φ hφ Y hY => by
      obtain ⟨u, hu, hc⟩ := hloc.2 φ hφ Y hY
      exact ⟨u, hu, hc⟩)
  have hle : 6 * (rhoPlus k q + 1) * ((G.color '' G.ball (rhoPlus k q) v).ncard + 1) *
      ((j + 1) * (j + 1)) ≤ 6 * (rhoPlus k q + 1) * (K + 1) * ((q + 1) * (q + 1)) := by
    have := hK.colors
    gcongr <;> omega
  have := Nat.mul_le_mul_right 6 (hA.trans hle)
  unfold atomBound
  omega

/-- A node of depth `j` of `tree_{k,q}(v)`, reached by a guarded tuple, has
word length at most `sizeBound` of its height. -/
theorem node_length_le_of (hk : 1 ≤ k) (hK : BallCounts G k q v K) : ∀ m j, j + m = q →
    ∀ w : Fin (j + 1) → Fin n, w 0 = v → Guarded G k q j w →
    wordLength (node G (k + j) m w) ≤ sizeBound (atomBound k q K) (q + 1) K m := by
  intro m
  induction m with
  | zero =>
    intro j hj w hw0 hw
    exact atoms_length_le_of hK j 0 hj w hw0 hw
  | succ m ih =>
    intro j hj w hw0 hw
    classical
    set X := G.ball (rhoPlus k q) v
    let E : Set (Fin (j + 1) × Node m (j + 1 + 1)) := {e | ∃ (i : Fin (j + 1)) (b : Fin n),
      WithinDist G.resolved (rhoPlus (k + j + 1) m) (w i) b ∧
        e = (i, node G (k + j + 1) m (Fin.snoc w b))}
    show wordLength ((finsetOf (atp G (k + j) (m + 1) w), finsetOf E) :
      Finset (DistFO (j + 1)) × Finset (Fin (j + 1) × Node m (j + 1 + 1))) ≤ _
    rw [wordLength_prod]
    have hatoms : wordLength (finsetOf (atp G (k + j) (m + 1) w)) ≤ atomBound k q K :=
      atoms_length_le_of hK j (m + 1) hj w hw0 hw
    have hguard : ∀ (i : Fin (j + 1)) (b : Fin n),
        WithinDist G.resolved (rhoPlus (k + j + 1) m) (w i) b →
        Guarded G k q (j + 1) (Fin.snoc w b) := by
      intro i b hb
      refine guarded_snoc hw i b ?_
      rwa [show q - (j + 1) = m by omega]
    have hext : ∀ e ∈ finsetOf E, wordLength e ≤ sizeBound (atomBound k q K) (q + 1) K m + 1 := by
      intro e he
      obtain ⟨i, b, hb, rfl⟩ := mem_of_mem_finsetOf he
      rw [wordLength_prod]
      have := ih (j + 1) (by omega) (Fin.snoc w b) (by rw [snoc_zero, hw0]) (hguard i b hb)
      have hi : wordLength i = 1 := rfl
      have : wordLength (node G (k + j + 1) m (Fin.snoc w b)) ≤
          sizeBound (atomBound k q K) (q + 1) K m := this
      omega
    let Ch : Set (Node m (j + 1 + 1)) :=
      {μ | ∃ u : Fin (j + 1 + 1) → Fin n, (∀ t, u t ∈ X) ∧ μ = node G (k + (j + 1)) m u}
    have hCh : Ch.ncard ≤ K :=
      hK.nodes (j + 1) m (j + 1 + 1) (by omega) (by omega) (by omega) (by omega)
    have hChfin : Ch.Finite :=
      Set.Finite.subset (Set.finite_range fun u : Fin (j + 1 + 1) → Fin n => node G (k + (j + 1)) m u)
        (by rintro μ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)
    have hEsub : E ⊆ (Set.univ : Set (Fin (j + 1))) ×ˢ Ch := by
      rintro e ⟨i, b, hb, rfl⟩
      refine ⟨Set.mem_univ _, Fin.snoc w b, fun t => ?_, rfl⟩
      have hloc := (Lax185574.TreeLocality.ball_of_guarded G k q (j + 1) (by omega) (Fin.snoc w b)
        (hguard i b hb)).1 t
      rwa [snoc_zero, hw0] at hloc
    have hEcard : (finsetOf E).card ≤ (j + 1) * K := by
      rw [card_finsetOf]
      calc E.ncard ≤ ((Set.univ : Set (Fin (j + 1))) ×ˢ Ch).ncard :=
            Set.ncard_le_ncard hEsub (Set.finite_univ.prod hChfin)
        _ = (j + 1) * Ch.ncard := by rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
            Fintype.card_fin]
        _ ≤ (j + 1) * K := Nat.mul_le_mul_left _ hCh
    have hE := wordLength_finset_le (finsetOf E) _ hext
    have h1 : (finsetOf E).card * (sizeBound (atomBound k q K) (q + 1) K m + 1 + 1) ≤
        ((q + 1) * K) * (sizeBound (atomBound k q K) (q + 1) K m + 2) :=
      Nat.mul_le_mul (hEcard.trans (Nat.mul_le_mul_right _ (by omega))) le_rfl
    simp only [sizeBound]
    omega

end Size

/-- **Size from counts.** The word length of `tree_{k,q}(v)` is at most
`c (K+1)^a` for every `K` with `BallCounts`, where `c` and `a` depend on
`k` and `q` only. -/
theorem tree_length_le_of (k q : ℕ) (hk : 1 ≤ k) :
    ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (v : Fin n) (K : ℕ),
      BallCounts G k q v K → wordLength (tree G k q ![v]) ≤ c * (K + 1) ^ a := by
  let A0 := 1 + 36 * (rhoPlus k q + 1) * ((q + 1) * (q + 1))
  refine ⟨3 + sizeCoeff A0 (q + 1) q, q + 1, fun n G v K hK => ?_⟩
  have hnode := node_length_le_of hk hK q 0 (by omega) ![v] rfl
    (fun i hi => absurd hi (by omega))
  have hA : atomBound k q K ≤ A0 * (K + 1) := by
    unfold atomBound
    have e : A0 * (K + 1) = (K + 1) + 6 * (rhoPlus k q + 1) * (K + 1) * ((q + 1) * (q + 1)) * 6 := by
      simp only [A0]
      ring
    omega
  have hB := sizeBound_le _ A0 (q + 1) K hA q
  have hlen : wordLength (tree G k q ![v]) = 3 + wordLength (node G k q ![v]) := by
    show (toWord (k, q, 1) ++ toWord (node G k q ![v])).length = _
    rw [List.length_append]
    rfl
  have hP : 1 ≤ (K + 1) ^ (q + 1) := Nat.one_le_pow _ _ (Nat.succ_pos K)
  rw [hlen]
  have : wordLength (node G k q ![v]) ≤ sizeCoeff A0 (q + 1) q * (K + 1) ^ (q + 1) :=
    hnode.trans hB
  nlinarith

end Lax185574Proofs.ResolveRam
