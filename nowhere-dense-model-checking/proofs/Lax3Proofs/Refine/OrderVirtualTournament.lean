import Lax3Proofs.Refine.OrderVirtualRows

/-!
# A linear-resident minimum-degree tournament

The materialized elimination engine uses one lazily allocated bucket node for
every degree decrement.  That is fast, but its address range is proportional
to the (possibly superlinear) edge count.  For the implicit ordering phase we
instead keep a tournament tree with `n` leaves and fewer than `n` internal
nodes.  A degree change touches one root path; hence the extra logarithmic
time buys a carrier-linear address range.

This file is the representation-independent root theorem.  It deliberately
uses two natural-number components for a key—degree and vertex—so no
`n * n` pairing is ever formed in the machine representation.
-/

namespace Lax3Proofs.Refine.OrderVirtualTournament

/-- Lexicographic order on the two-word `(degree, vertex)` key. -/
def KeyLE (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

theorem keyLE_refl (a : ℕ × ℕ) : KeyLE a a := by
  exact Or.inr ⟨rfl, le_rfl⟩

theorem keyLE_trans {a b c : ℕ × ℕ} (hab : KeyLE a b) (hbc : KeyLE b c) :
    KeyLE a c := by
  rcases hab with hab | ⟨hab, hab₂⟩ <;>
    rcases hbc with hbc | ⟨hbc, hbc₂⟩
  all_goals unfold KeyLE; omega

theorem keyLE_total (a b : ℕ × ℕ) : KeyLE a b ∨ KeyLE b a := by
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.2 b.2 with h₂ | h₂
    · exact Or.inl (Or.inr ⟨h, h₂⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h₂⟩)
  · exact Or.inr (Or.inl h)

theorem fst_le_of_keyLE {a b : ℕ × ℕ} (h : KeyLE a b) : a.1 ≤ b.1 := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- The comparison used at each internal tournament node. -/
instance keyLEDecidable (a b : ℕ × ℕ) : Decidable (KeyLE a b) := by
  unfold KeyLE
  infer_instance

def keyMin (a b : ℕ × ℕ) : ℕ × ℕ := if KeyLE a b then a else b

theorem keyMin_eq_left {a b : ℕ × ℕ} (h : KeyLE a b) : keyMin a b = a := by
  simp [keyMin, h]

theorem keyMin_eq_right {a b : ℕ × ℕ} (h : ¬ KeyLE a b) : keyMin a b = b := by
  simp [keyMin, h]

theorem keyMin_le_left (a b : ℕ × ℕ) : KeyLE (keyMin a b) a := by
  by_cases h : KeyLE a b
  · rw [keyMin_eq_left h]
    exact keyLE_refl _
  · rw [keyMin_eq_right h]
    exact (keyLE_total a b).resolve_left h

theorem keyMin_le_right (a b : ℕ × ℕ) : KeyLE (keyMin a b) b := by
  by_cases h : KeyLE a b
  · rw [keyMin_eq_left h]
    exact h
  · rw [keyMin_eq_right h]
    exact keyLE_refl _

/-- The key represented by the two parallel tree arrays. -/
def treeKey (TD TV : ℕ → ℕ) (p : ℕ) : ℕ × ℕ := (TD p, TV p)

/-- An eliminated vertex receives the sentinel degree `n`; a live vertex
receives its exact current degree. -/
def leafKey (n : ℕ) (E D : ℕ → ℕ) (v : ℕ) : ℕ × ℕ :=
  if E v = 0 then (D v, v) else (n, v)

/-- A tournament stored at indices `1, …, 2*n-1`, with leaves
`n, …, 2*n-1`.  Index zero is deliberately unused. -/
structure Rep (n : ℕ) (E D TD TV : ℕ → ℕ) : Prop where
  leaf : ∀ v < n, treeKey TD TV (n + v) = leafKey n E D v
  node : ∀ p, 0 < p → p < n →
    treeKey TD TV p = keyMin (treeKey TD TV (2 * p)) (treeKey TD TV (2 * p + 1))

namespace Rep

variable {n : ℕ} {E D TD TV : ℕ → ℕ}

/-- Every stored node is the key of one of its descendant leaves. -/
theorem node_eq_leaf (rep : Rep n E D TD TV) {p : ℕ} (hp0 : 0 < p)
    (hp2n : p < 2 * n) :
    ∃ v < n, treeKey TD TV p = leafKey n E D v := by
  generalize hfuel : n - p = fuel
  induction fuel using Nat.strong_induction_on generalizing p with
  | h fuel ih =>
      by_cases hpn : n ≤ p
      · refine ⟨p - n, by omega, ?_⟩
        have hp : n + (p - n) = p := by omega
        calc
          treeKey TD TV p = treeKey TD TV (n + (p - n)) := congrArg _ hp.symm
          _ = leafKey n E D (p - n) := rep.leaf (p - n) (by omega)
      · have hplt : p < n := Nat.lt_of_not_ge hpn
        have hnode := rep.node p hp0 hplt
        by_cases hc : KeyLE (treeKey TD TV (2 * p)) (treeKey TD TV (2 * p + 1))
        · have heq : treeKey TD TV p = treeKey TD TV (2 * p) := by
            rw [hnode, keyMin_eq_left hc]
          have hc0 : 0 < 2 * p := by omega
          have hc2n : 2 * p < 2 * n := by omega
          have hm : n - 2 * p < fuel := by omega
          obtain ⟨v, hv, hleaf⟩ := ih (n - 2 * p) hm hc0 hc2n rfl
          exact ⟨v, hv, heq.trans hleaf⟩
        · have heq : treeKey TD TV p = treeKey TD TV (2 * p + 1) := by
            rw [hnode, keyMin_eq_right hc]
          have hc0 : 0 < 2 * p + 1 := by omega
          have hc2n : 2 * p + 1 < 2 * n := by omega
          have hm : n - (2 * p + 1) < fuel := by omega
          obtain ⟨v, hv, hleaf⟩ := ih (n - (2 * p + 1)) hm
            hc0 hc2n rfl
          exact ⟨v, hv, heq.trans hleaf⟩

/-- The root key is no larger than the key at any stored node. -/
theorem root_le_node (rep : Rep n E D TD TV) (hn : 0 < n) {q : ℕ}
    (hq0 : 0 < q) (hq2n : q < 2 * n) :
    KeyLE (treeKey TD TV 1) (treeKey TD TV q) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq : q = 1
      · subst q
        exact keyLE_refl _
      · have hq1 : 1 < q := by omega
        let p := q / 2
        have hp0 : 0 < p := by
          dsimp [p]
          omega
        have hpq : p < q := by
          dsimp [p]
          omega
        have hpn : p < n := by
          dsimp [p]
          omega
        have hrootp : KeyLE (treeKey TD TV 1) (treeKey TD TV p) :=
          ih p hpq hp0 (by omega)
        have hnode := rep.node p hp0 hpn
        have hqp : q = 2 * p ∨ q = 2 * p + 1 := by
          dsimp [p]
          omega
        have hpqkey : KeyLE (treeKey TD TV p) (treeKey TD TV q) := by
          rcases hqp with hqeven | hqodd
          · rw [hqeven, hnode]
            exact keyMin_le_left _ _
          · rw [hqodd, hnode]
            exact keyMin_le_right _ _
        exact keyLE_trans hrootp hpqkey

/-- The root is an exact minimum-degree live vertex whenever one remains.
This is the sole semantic fact the elimination loop needs from the physical
tournament. -/
theorem root_min (h : Rep n E D TD TV) (hn : 0 < n)
    (hdeg : ∀ v < n, E v = 0 → D v < n)
    (halive : ∃ v < n, E v = 0) :
    let w := TV 1
    w < n ∧ E w = 0 ∧ TD 1 = D w ∧
      ∀ u < n, E u = 0 → TD 1 ≤ D u := by
  obtain ⟨w, hw, hroot⟩ := h.node_eq_leaf (p := 1) (by omega) (by omega)
  obtain ⟨a, ha, hEa⟩ := halive
  have hrootle : KeyLE (treeKey TD TV 1) (treeKey TD TV (n + a)) :=
    h.root_le_node hn (by omega) (by omega)
  rw [h.leaf a ha, leafKey, if_pos hEa] at hrootle
  have hrootfst : TD 1 < n :=
    lt_of_le_of_lt (fst_le_of_keyLE hrootle) (hdeg a ha hEa)
  have hwkey : treeKey TD TV 1 = leafKey n E D w := hroot
  have hEw : E w = 0 := by
    by_contra hne
    have hpos : 0 < E w := Nat.pos_of_ne_zero hne
    rw [leafKey, if_neg hne] at hwkey
    have := congrArg Prod.fst hwkey
    simp [treeKey] at this
    omega
  have hTD : TD 1 = D w := by
    rw [leafKey, if_pos hEw] at hwkey
    exact congrArg Prod.fst hwkey
  have hTV : TV 1 = w := by
    rw [leafKey, if_pos hEw] at hwkey
    exact congrArg Prod.snd hwkey
  dsimp
  rw [hTV]
  refine ⟨hw, hEw, hTD, fun u hu hEu => ?_⟩
  have hle : KeyLE (treeKey TD TV 1) (treeKey TD TV (n + u)) :=
    h.root_le_node hn (by omega) (by omega)
  rw [h.leaf u hu, leafKey, if_pos hEu] at hle
  exact fst_le_of_keyLE hle

end Rep

end Lax3Proofs.Refine.OrderVirtualTournament
