import Lax185574.TreeEquivalence
import Lax185574.Evaluation
import Lax185574Proofs.TypeTreeTransport
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.EquivFin
import Lax185574Proofs.Interface.Shim.Evaluation

/-!
Proof that type trees are distance types, following the proof of
cor:tp-tree. The rightwards implication is read off the evaluation
program of lem:eval: a deterministic program that decides `G ⊨ φ(ā)` from
the pair `(tree_{k,q}(ā), φ)` gives the same answer for two tuples with
the same tree. The converse is the induction on `q` of the source.
-/

namespace Lax185574Proofs.TreeEquivalence

open Lax808846.Ram Lax808846.RamComputes
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding Lax185574.Computing
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574Proofs.TypeTreeTransport
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### Outputs of a program are unique -/

/-- Two objects computed by the same program from the same input have the
same word: at a large word length, the program halts by the first
statement, and its output is the word of the second object by the
soundness clause of the second statement. -/
theorem computes_toWord_eq {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b b' : β} {T T' : ℕ → ℕ} (h : Computes p e c a b T)
    (h' : Computes p e c a b' T') : toWord b = toWord b' := by
  set x := toWord a
  set N := c * (x.length + x.sum + 1) ^ e + T (wordLength a)
  have hN : N < 2 ^ N := Nat.lt_two_pow_self
  have hadm : WordAdmissible e c N x := by
    intro v hv
    have hv' : v ≤ x.sum := List.le_sum_of_mem hv
    have : c * (x.length + v + 1) ^ e ≤ c * (x.length + x.sum + 1) ^ e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  obtain ⟨t, -, hrun⟩ := (h N hadm).2 (by omega) x (Set.mem_singleton x)
  exact (h' N hadm).1 _ t hrun

/-- **Rightwards implication on `Fin n`.** Tuples with the same type tree
satisfy the same formulas of the rank of the tree, by `lem:eval`. -/
theorem sat_iff_of_tree_eq_fin {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ}
    (hℓ : ℓ ≤ k) (a b : Fin ℓ → Fin n) (htree : tree G k q a = tree G k q b)
    (φ : DistFO ℓ) (hφ : DRank k q φ) : Sat G a φ ↔ Sat G b φ := by
  classical
  obtain ⟨p, e, hp⟩ := Lax185574Proofs.Shim.Evaluation.exists_program_eval
  obtain ⟨c, d, hc⟩ := hp k q
  have h1 := hc n G ℓ a φ hℓ hφ
  have h2 := hc n G ℓ b φ hℓ hφ
  rw [← htree] at h2
  have := computes_toWord_eq h1 h2
  by_cases ha : Sat G a φ <;> by_cases hb : Sat G b φ <;> simp_all [word_simps]

/-- **Rightwards implication.** -/
theorem sat_iff_of_tree_eq {V : Type*} [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ}
    (hℓ : ℓ ≤ k) (a b : Fin ℓ → V) (htree : tree G k q a = tree G k q b)
    (φ : DistFO ℓ) (hφ : DRank k q φ) : Sat G a φ ↔ Sat G b φ := by
  have : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  rw [← sat_transport G e, ← sat_transport G e]
  refine sat_iff_of_tree_eq_fin (transport G e) k q hℓ _ _ ?_ φ hφ
  rw [tree_transport, tree_transport, htree]

/-! ### Conjunctions -/

/-- The conjunction of the formulas of a list and the formula `t`. -/
def conj {m : ℕ} (t : DistFO m) : List (DistFO m) → DistFO m
  | [] => t
  | ψ :: l => .and ψ (conj t l)

theorem sat_conj {V : Type*} (G : PartialGraph V) {m : ℕ} (x : Fin m → V) (t : DistFO m) :
    ∀ l : List (DistFO m), Sat G x (conj t l) ↔ Sat G x t ∧ ∀ ψ ∈ l, Sat G x ψ
  | [] => by simp [conj]
  | ψ :: l => by
    simp only [conj, Sat, sat_conj G x t l, List.mem_cons, forall_eq_or_imp]
    tauto

theorem drank_conj {k q m : ℕ} (t : DistFO m) (ht : DRank k q t) :
    ∀ l : List (DistFO m), (∀ ψ ∈ l, DRank k q ψ) → DRank k q (conj t l)
  | [], _ => ht
  | ψ :: l, h => .and (h ψ (by simp)) (drank_conj t ht l fun ψ' hψ' => h ψ' (by simp [hψ']))

/-! ### The converse -/

/-- **Converse, by induction on `q`.** Tuples satisfying the same formulas
of distance rank `(k, q)` have the same type tree. For an extension of the
first tuple by a vertex `c` near its entry `i`, a conjunction `χ` of
formulas of rank `(k+1, q−1)` separates `ā c` from all tuples with a
different tree, by the induction hypothesis. The formula
`∃ y (dist(xᵢ, y) ≤ ρ⁺(k+1, q−1) ∧ χ)` has rank `(k, q)` and holds of the
first tuple, hence of the second, and its witness gives the extension. -/
theorem node_eq_of_sat_iff {V : Type*} [Finite V] (G : PartialGraph V) :
    ∀ (q k : ℕ) {ℓ : ℕ} (a b : Fin ℓ → V),
      (∀ φ : DistFO ℓ, DRank k q φ → (Sat G a φ ↔ Sat G b φ)) → node G k q a = node G k q b
  | 0, k, ℓ, a, b, h => by
    show finsetOf _ = finsetOf _
    congr 1
    ext φ
    simp only [atp, Set.mem_ofPred_eq]
    exact and_congr_right fun _ => and_congr_right fun hr => h φ hr
  | q + 1, k, ℓ, a, b, h => by
    classical
    have hatp : atp G k (q + 1) a = atp G k (q + 1) b := by
      ext φ
      simp only [atp, Set.mem_ofPred_eq]
      exact and_congr_right fun _ => and_congr_right fun hr => h φ hr
    -- one inclusion of the extension sets, for any two such tuples
    have hsub : ∀ (a b : Fin ℓ → V),
        (∀ φ : DistFO ℓ, DRank k (q + 1) φ → (Sat G a φ ↔ Sat G b φ)) →
        {x | ∃ (i : Fin ℓ) (c : V), WithinDist G.resolved (rhoPlus (k + 1) q) (a i) c ∧
            x = (i, node G (k + 1) q (Fin.snoc a c))} ⊆
          {x | ∃ (i : Fin ℓ) (c : V), WithinDist G.resolved (rhoPlus (k + 1) q) (b i) c ∧
            x = (i, node G (k + 1) q (Fin.snoc b c))} := by
      intro a b h x hx
      obtain ⟨i, c, hc, rfl⟩ := hx
      set xa : Fin (ℓ + 1) → V := Fin.snoc a c
      have hsep : ∀ y : Fin (ℓ + 1) → V, node G (k + 1) q y ≠ node G (k + 1) q xa →
          ∃ ψ : DistFO (ℓ + 1), DRank (k + 1) q ψ ∧ Sat G xa ψ ∧ ¬ Sat G y ψ := by
        intro y hy
        by_contra hno
        push Not at hno
        refine hy (node_eq_of_sat_iff G q (k + 1) y xa fun φ hφ => ⟨fun hy' => ?_, hno φ hφ⟩)
        by_contra hx'
        exact (hno (.not φ) (.not hφ) hx') hy'
      let ψ : (Fin (ℓ + 1) → V) → DistFO (ℓ + 1) := fun y =>
        if hy : node G (k + 1) q y ≠ node G (k + 1) q xa then Classical.choose (hsep y hy)
        else .eq 0 0
      have hψ : ∀ y, DRank (k + 1) q (ψ y) ∧ Sat G xa (ψ y) ∧
          (node G (k + 1) q y ≠ node G (k + 1) q xa → ¬ Sat G y (ψ y)) := by
        intro y
        by_cases hy : node G (k + 1) q y ≠ node G (k + 1) q xa
        · have := Classical.choose_spec (hsep y hy)
          simp only [ψ, dif_pos hy]
          exact ⟨this.1, this.2.1, fun _ => this.2.2⟩
        · simp only [ψ, dif_neg hy]
          exact ⟨.eq 0 0, rfl, fun h' => absurd h' hy⟩
      have : Fintype V := Fintype.ofFinite V
      let χ : DistFO (ℓ + 1) := conj (.eq 0 0) ((Finset.univ : Finset (Fin (ℓ + 1) → V)).toList.map ψ)
      have hχr : DRank (k + 1) q χ := by
        refine drank_conj _ (.eq 0 0) _ ?_
        simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
        rintro _ ⟨y, rfl⟩
        exact (hψ y).1
      have hχa : Sat G xa χ := by
        refine (sat_conj G xa _ _).2 ⟨rfl, ?_⟩
        simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
        rintro _ ⟨y, rfl⟩
        exact (hψ y).2.1
      have hχy : ∀ y, Sat G y χ → node G (k + 1) q y = node G (k + 1) q xa := by
        intro y hy
        by_contra hne
        refine (hψ y).2.2 hne (((sat_conj G y _ _).1 hy).2 (ψ y) ?_)
        simp
      have hΦ : Sat G b (.exLocal i (rhoPlus (k + 1) q) χ) :=
        (h _ (.exLocal i hχr)).1 ⟨c, hc, hχa⟩
      obtain ⟨c', hc', hχb⟩ := hΦ
      exact ⟨i, c', hc', by rw [hχy _ hχb]⟩
    show (finsetOf _, finsetOf _) = (finsetOf _, finsetOf _)
    rw [hatp, Set.Subset.antisymm (hsub a b h) (hsub b a fun φ hφ => (h φ hφ).symm)]

/--
---
conclusion: Lax185574.TreeEquivalence.tree_eq_iff
---
The rightwards implication follows from the evaluation lemma: the
evaluation program receives equal inputs for the two tuples, so it gives
equal answers. The vertex type is renamed to `Fin n` for this. The
converse is `node_eq_of_sat_iff`, by induction on `q`.
-/
theorem tree_eq_iff {V : Type*} [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ}
    (hℓ : ℓ ≤ k) (a b : Fin ℓ → V) :
    tree G k q a = tree G k q b ↔
      ∀ φ : DistFO ℓ, DRank k q φ → (Sat G a φ ↔ Sat G b φ) := by
  refine ⟨fun h φ hφ => sat_iff_of_tree_eq G k q hℓ a b h φ hφ, fun h => ?_⟩
  simp only [tree, node_eq_of_sat_iff G q k a b h]

end Lax185574Proofs.TreeEquivalence
