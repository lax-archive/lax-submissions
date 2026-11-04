import Lax185574Proofs.TreeAlgo.ToFarTree
import Lax185574.ScatterTypeRestriction

/-!
Restricting a scatter type to a smaller domain (obs:stp-restrict). The
entries of `stp_{k,q}` are pairs `((r, ν), m)` where `ν` is a type tree of
rank `(k+i, q−i)` with `i ≥ 1`. Keeping the entries with `ν.k ≥ k + 2`
gives `stp_{k+1,q−1}`, by obs:stp-restrict. Iterating, the entries of
`stp_{k₀,q₀}` with `ν.k ≥ k + 1` form `stp_{k,q}` whenever `k₀ ≤ k` and
`k + q = k₀ + q₀`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574Proofs.TreeAlgo

/-- The entries of a scatter type whose tree has first rank at least `m`. -/
def stpCut (m : ℕ) (σ : Finset ((ℕ × TypeTree) × ℕ)) : Finset ((ℕ × TypeTree) × ℕ) :=
  σ.filter fun p => m ≤ p.1.2.k

theorem mem_stpCut {m : ℕ} {σ : Finset ((ℕ × TypeTree) × ℕ)} {p : (ℕ × TypeTree) × ℕ} :
    p ∈ stpCut m σ ↔ p ∈ σ ∧ m ≤ p.1.2.k := Finset.mem_filter

theorem stpCut_stpCut {m m' : ℕ} (h : m' ≤ m) (σ : Finset ((ℕ × TypeTree) × ℕ)) :
    stpCut m (stpCut m' σ) = stpCut m σ := by
  ext p
  simp only [mem_stpCut]
  constructor
  · rintro ⟨⟨hp, -⟩, hm⟩; exact ⟨hp, hm⟩
  · rintro ⟨hp, hm⟩; exact ⟨⟨hp, by omega⟩, hm⟩

variable {n : ℕ} (G : PartialGraph (Fin n))

theorem domain_k {k q : ℕ} {x : ℕ × TypeTree} (hx : x ∈ domain G k q) :
    ∃ i, 1 ≤ i ∧ i ≤ q ∧ x.2.k = k + i := by
  obtain ⟨i, b, hi1, hiq, -, -, hx2⟩ := hx
  exact ⟨i, hi1, hiq, by rw [hx2]; rfl⟩

/-- Every entry of `stp_{k,q}` has a tree of first rank at least `k + 1`. -/
theorem stpCut_self (k q : ℕ) : stpCut (k + 1) (stp G k q) = stp G k q := by
  refine Finset.filter_true_of_mem fun p hp => ?_
  obtain ⟨i, hi1, -, hk⟩ := domain_k G ((mem_stp (G := G) k q p).1 hp).1
  omega

/-- One step of obs:stp-restrict: the entries of `stp_{k,q+1}` of first
rank at least `k + 2` form `stp_{k+1,q}`. -/
theorem stpCut_step (k q : ℕ) : stpCut (k + 2) (stp G k (q + 1)) = stp G (k + 1) q := by
  obtain ⟨hdom, hval⟩ := Lax185574.ScatterTypeRestriction.stp_restrict G k q
  ext p
  rw [mem_stpCut, mem_stp (G := G), mem_stp (G := G)]
  constructor
  · rintro ⟨⟨hd, hv⟩, hk⟩
    have hd' : p.1 ∈ domain G (k + 1) q := by
      obtain ⟨i, b, hi1, hiq, hr1, hr, hx2⟩ := hd
      have hki : p.1.2.k = k + i := by rw [hx2]; rfl
      refine ⟨i - 1, b, by omega, by omega, hr1, ?_, ?_⟩
      · rwa [show k + 1 + (i - 1) = k + i by omega, show q - (i - 1) = q + 1 - i by omega]
      · rwa [show k + 1 + (i - 1) = k + i by omega, show q - (i - 1) = q + 1 - i by omega]
    exact ⟨hd', by rw [hval p.1 hd', hv]⟩
  · rintro ⟨hd, hv⟩
    obtain ⟨i, hi1, -, hk⟩ := domain_k G hd
    exact ⟨⟨hdom hd, by rw [← hval p.1 hd, hv]⟩, by omega⟩

/-- **obs:stp-restrict, iterated.** The entries of `stp_{k₀,q₀}` of first
rank at least `k + 1` form `stp_{k,q}`. -/
theorem stpCut_stp {n : ℕ} (G : PartialGraph (Fin n)) {k₀ q₀ : ℕ} :
    ∀ (d k q : ℕ), k = k₀ + d → k + q = k₀ + q₀ → stpCut (k + 1) (stp G k₀ q₀) = stp G k q
  | 0, k, q, hk, hs => by
    obtain rfl : k = k₀ := hk
    obtain rfl : q = q₀ := by omega
    exact stpCut_self G k q
  | d + 1, k, q, hk, hs => by
    have ih := stpCut_stp G (k₀ := k₀) (q₀ := q₀) d (k₀ + d) (q + 1) rfl (by omega)
    rw [← stpCut_stpCut (show k₀ + d + 1 ≤ k + 1 by omega), ih]
    subst hk
    exact stpCut_step G (k₀ + d) q

theorem stpCut_stp' {k₀ q₀ k q : ℕ} (hk : k₀ ≤ k) (hs : k + q = k₀ + q₀) :
    stpCut (k + 1) (stp G k₀ q₀) = stp G k q :=
  stpCut_stp G (k - k₀) k q (by omega) hs

end Lax185574Proofs.ResolveRam
