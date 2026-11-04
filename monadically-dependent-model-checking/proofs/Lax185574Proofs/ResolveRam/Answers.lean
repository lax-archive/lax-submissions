import Lax185574Proofs.ResolveRam.Expand
import Lax185574Proofs.ResolveRam.FarMapOf
import Lax185574Proofs.ResolveRam.OutputSize
import Lax185574.RankShift
import Lax185574.FarComposition
import Lax185574Proofs.Interface.Shim.FarComposition
import Lax185574Proofs.Interface.Shim.RankShift

/-!
The answers of the callees as functions of the queries.

The rank shift of lem:shift and the composition of lem:compose are
functions of the type trees, since one program computes them
(`shift_congr`, `compose_congr`, as `ftree_congr` for the far tree).
So the answers of the callees on the trees of tuples of `G` are given by
functions `shOf`, `faOf`, `coOf` of the queries, and these satisfy
`AnsOK`. With them the script computes the family of the trees after the
resolve (`script_family_of`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n))

/-- **The rank shift is a function of the type tree**, by lem:shift. -/
theorem shift_congr {k q ℓ ℓ' : ℕ} {u : Fin ℓ → Fin n} {u' : Fin ℓ' → Fin n} (h1 : 1 ≤ ℓ)
    (hk : ℓ ≤ k) (h1' : 1 ≤ ℓ') (hk' : ℓ' ≤ k) (h : tree G k (q + 1) u = tree G k (q + 1) u') :
    tree G (k + 1) q u = tree G (k + 1) q u' := by
  have := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
  obtain ⟨p, e, hp⟩ := Lax185574Proofs.Shim.RankShift.exists_program_shift
  obtain ⟨c, a, hc⟩ := hp k q
  have hx := hc n G ℓ u h1 hk
  have hx' := hc n G ℓ' u' h1' hk'
  rw [h] at hx
  exact toWord_injective (computes_word_eq hx hx')

/-- **The composition with a far vertex is a function of the two type
trees**, by lem:compose. -/
theorem compose_congr {k q ℓ ℓ' : ℕ} {u : Fin ℓ → Fin n} {u' : Fin ℓ' → Fin n} {b b' : Fin n}
    (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) (h1' : 1 ≤ ℓ') (hk' : ℓ' ≤ k)
    (hb : ∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b)
    (hb' : ∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u' i) b')
    (h : tree G (k + 1) q u = tree G (k + 1) q u') (h' : tree G (k + 1) q ![b] = tree G (k + 1) q ![b']) :
    tree G (k + 1) q (Fin.snoc u b) = tree G (k + 1) q (Fin.snoc u' b') := by
  have := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
  obtain ⟨p, e, hp⟩ := Lax185574Proofs.Shim.FarComposition.exists_program_compose
  obtain ⟨c, a, hc⟩ := hp (k + 1) q
  have hx := hc n G ℓ 1 u ![b] h1 le_rfl (by omega)
    (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i)
  have hx' := hc n G ℓ' 1 u' ![b'] h1' le_rfl (by omega)
    (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb' i)
  rw [h, h'] at hx
  have := toWord_injective (computes_word_eq hx hx')
  rw [Fin.append_right_eq_snoc, Fin.append_right_eq_snoc] at this
  exact this

open Classical in
/-- The answer of the rank shift. -/
noncomputable def shOf (τ : TypeTree) : TypeTree :=
  if h : ∃ x : (Σ ℓ, Fin ℓ → Fin n) × ℕ × ℕ, 1 ≤ x.1.1 ∧ x.1.1 ≤ x.2.1 ∧
      τ = tree G x.2.1 (x.2.2 + 1) x.1.2
  then tree G (h.choose.2.1 + 1) h.choose.2.2 h.choose.1.2 else τ

open Classical in
/-- The answer of the composition. -/
noncomputable def coOf (σ ν : TypeTree) : TypeTree :=
  if h : ∃ x : (Σ ℓ, Fin ℓ → Fin n) × Fin n × ℕ × ℕ, 1 ≤ x.1.1 ∧ x.1.1 ≤ x.2.2.1 ∧
      (∀ i, ¬ WithinDist G.resolved (rhoMinus (x.2.2.1 + 1) x.2.2.2) (x.1.2 i) x.2.1) ∧
      σ = tree G (x.2.2.1 + 1) x.2.2.2 x.1.2 ∧ ν = tree G (x.2.2.1 + 1) x.2.2.2 ![x.2.1]
  then tree G (h.choose.2.2.1 + 1) h.choose.2.2.2 (Fin.snoc h.choose.1.2 h.choose.2.1) else σ

/-- The answer of the far tree, as the list of its members in the order
of their words. -/
noncomputable def faOf : TypeTree → List TypeTree
  | ⟨k, q + 1, ℓ, t⟩ => elems (farMapOf G k q ℓ t ∅)
  | ⟨_, 0, _, _⟩ => []

theorem shOf_tree {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    shOf G (tree G k (q + 1) u) = tree G (k + 1) q u := by
  have hex : ∃ x : (Σ ℓ, Fin ℓ → Fin n) × ℕ × ℕ, 1 ≤ x.1.1 ∧ x.1.1 ≤ x.2.1 ∧
      tree G k (q + 1) u = tree G x.2.1 (x.2.2 + 1) x.1.2 := ⟨(⟨ℓ, u⟩, k, q), h1, hk, rfl⟩
  rw [shOf, dif_pos hex]
  obtain ⟨h1', hk', hx⟩ := hex.choose_spec
  generalize hex.choose = x at h1' hk' hx ⊢
  obtain ⟨⟨ℓ', u'⟩, k', q'⟩ := x
  simp only at h1' hk' hx ⊢
  have ek : k = k' := congrArg TypeTree.k hx
  have eq' : q + 1 = q' + 1 := congrArg TypeTree.q hx
  obtain rfl := ek
  obtain rfl : q = q' := by omega
  exact (shift_congr G h1 hk h1' hk' hx).symm

theorem coOf_tree {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k)
    (hb : ∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) :
    coOf G (tree G (k + 1) q u) (tree G (k + 1) q ![b]) = tree G (k + 1) q (Fin.snoc u b) := by
  have hex : ∃ x : (Σ ℓ, Fin ℓ → Fin n) × Fin n × ℕ × ℕ, 1 ≤ x.1.1 ∧ x.1.1 ≤ x.2.2.1 ∧
      (∀ i, ¬ WithinDist G.resolved (rhoMinus (x.2.2.1 + 1) x.2.2.2) (x.1.2 i) x.2.1) ∧
      tree G (k + 1) q u = tree G (x.2.2.1 + 1) x.2.2.2 x.1.2 ∧
      tree G (k + 1) q ![b] = tree G (x.2.2.1 + 1) x.2.2.2 ![x.2.1] :=
    ⟨(⟨ℓ, u⟩, b, k, q), h1, hk, hb, rfl, rfl⟩
  rw [coOf, dif_pos hex]
  obtain ⟨h1', hk', hb', hx, hy⟩ := hex.choose_spec
  generalize hex.choose = x at h1' hk' hb' hx hy ⊢
  obtain ⟨⟨ℓ', u'⟩, b', k', q'⟩ := x
  simp only at h1' hk' hb' hx hy ⊢
  have ek : k + 1 = k' + 1 := congrArg TypeTree.k hx
  have eq' : q = q' := congrArg TypeTree.q hx
  obtain rfl : k = k' := by omega
  obtain rfl := eq'
  exact (compose_congr G h1 hk h1' hk' hb hb' hx hy).symm

/-- **The answers are right.** -/
theorem ansOK_of (k₀ q₀ : ℕ) : AnsOK G (shOf G) (faOf G) (coOf G) k₀ q₀ where
  sh k q ℓ u h1 hk := shOf_tree G u h1 hk
  fa k q ℓ u h1 hk _ _ ν := by
    have := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
    show ν ∈ elems (farMapOf G k q ℓ (node G k (q + 1) u) ∅) ↔ _
    rw [mem_elems]
    exact iff_of_eq (congrArg (ν ∈ ·) (farSpec_farMapOf G k q ℓ u h1 hk))
  co k q ℓ u b h1 hk hb := coOf_tree G u b h1 hk hb

/-- **The script with the answers of the callees computes the family
after the resolve.** -/
theorem script_family_of (D : ResolveData) {k₀ q₀ : ℕ} (hk : 1 ≤ k₀) (hD : D.Spec G k₀ q₀) :
    outsAt D (exG D (shOf G) (faOf G) (coOf G)) (famItems G k₀ q₀) q₀ 0 =
      (List.finRange n).map fun b => family (resolveBy G D.sign D.P D.Q) k₀ q₀ b :=
  script_family D (farMapOf G) hk hD (farSpec_farMapOf G)
    (expandOK_exG D (farMapOf G) hD (farSpec_farMapOf G) (ansOK_of G k₀ q₀))

end Lax185574Proofs.ResolveRam
