import Lax185574Proofs.StpRam.Glue
import Lax185574Proofs.ShiftRam.Rounds
import Lax185574Proofs.Compose.CsrToGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
Sizes for the composite of lem:compute-stp.

The shifted trees are not longer than the family trees, and their
entries are bounded by those of the family trees and `k + q + 2`
(`level_bound`, `answers_bound`). Entry `i < q · n` of the list
`F ++ A` of the family trees and the answers is the tree of level
`i / n` of vertex `i % n`, and entry `i` of `A` is its shift
(`query_eq`, `answer_eq`). The number of neighbors in the two
adjacency structures is at most twice the size of the partial graph
(`offL_add_le`). The word of the scatter type is not longer than
`1 + R₁ · q · n · (L + 3)` (`length_toWord_stp_le`).
-/

namespace Lax185574Proofs.StpRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs
open Lax185574.ScatterTypes Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ShiftRam Lax185574Proofs.Compose Lax185574Proofs.Simulate

variable {n : ℕ}

/-! ### The shifted trees -/

theorem toWord_tree_eq (G : PartialGraph (Fin n)) (k q : ℕ) (v : Fin n) :
    toWord (tree G k q ![v]) = [k, q, 1] ++ toWord (node G k q ![v]) := rfl

/-- **One shift.** -/
theorem shift_bound (G : PartialGraph (Fin n)) (k q : ℕ) (v : Fin n) (Bz : ℕ)
    (hc : ∀ y ∈ toWord (tree G k (q + 1) ![v]), y < Bz)
    (hl : (toWord (tree G k (q + 1) ![v])).length < Bz) (hk : k + 1 < Bz) (hq : q + 2 < Bz) :
    (toWord (tree G (k + 1) q ![v])).length ≤ (toWord (tree G k (q + 1) ![v])).length ∧
      ∀ y ∈ toWord (tree G (k + 1) q ![v]), y < Bz := by
  obtain ⟨a, ha, -⟩ := exists_guard_zero G k q (ℓ := 1) le_rfl ![v]
  obtain ⟨b, hb⟩ := child_eq G k q ![v] ha
  have hinf := child_infix ha
  rw [hb] at hinf
  have hx := toWord_tree_eq G k (q + 1) v
  have hcl := hinf.length_le
  have hcv : ∀ y ∈ toWord (node G (k + 1) q (Fin.snoc ![v] b)), y < Bz := fun y hy =>
    hc y (by rw [hx]; exact List.mem_append_right _ (hinf.subset hy))
  obtain ⟨h1, h2⟩ := answer_bound G (k + 1) q ![v] b Bz hcv
    (by rw [hx] at hl; simp at hl; omega) (by omega) hk (by omega)
  refine ⟨?_, h2⟩
  rw [hx]; simp; omega

/-- **The shifted trees of a vertex.** -/
theorem level_bound (G : PartialGraph (Fin n)) (k q : ℕ) (v : Fin n) (Bz : ℕ)
    (hc : ∀ y ∈ toWord (tree G k q ![v]), y < Bz) (hl : (toWord (tree G k q ![v])).length < Bz)
    (hkq : k + q + 2 < Bz) :
    ∀ i ≤ q, (toWord (tree G (k + i) (q - i) ![v])).length ≤ (toWord (tree G k q ![v])).length ∧
      ∀ y ∈ toWord (tree G (k + i) (q - i) ![v]), y < Bz := by
  intro i
  induction i with
  | zero => intro _; exact ⟨le_rfl, hc⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨r, hr⟩ : ∃ r, q - i = r + 1 := ⟨q - i - 1, by omega⟩
    rw [hr] at h1 h2
    obtain ⟨h3, h4⟩ := shift_bound G (k + i) r v Bz h2 (by omega) (by omega) (by omega)
    rw [show k + (i + 1) = k + i + 1 by ring, show q - (i + 1) = r by omega]
    exact ⟨le_trans h3 h1, h4⟩

/-- **The answers.** -/
theorem answers_bound (G : PartialGraph (Fin n)) (k q L Bz : ℕ)
    (hL : ∀ v : Fin n, (toWord (family G k q v)).length ≤ L)
    (hc : ∀ v : Fin n, ∀ y ∈ toWord (family G k q v), y < Bz) (hLB : L < Bz) (hkq : k + q + 2 < Bz) :
    ∀ u ∈ answers G k q, u.length ≤ L ∧ ∀ y ∈ u, y < Bz := by
  intro u hu
  obtain ⟨i, -, hiq, v, rfl⟩ := (mem_answers k q).mp hu
  obtain ⟨h1, h2⟩ := level_bound G k q v Bz (hc v) (lt_of_le_of_lt (hL v) hLB) hkq i hiq
  exact ⟨le_trans h1 (hL v), h2⟩

theorem length_answers (G : PartialGraph (Fin n)) (k q : ℕ) : (answers G k q).length = q * n := by
  simp [answers]

theorem total_le (ws : List (List ℕ)) (L : ℕ) (h : ∀ u ∈ ws, u.length ≤ L) :
    total ws ≤ ws.length * L := by
  induction ws with
  | nil => simp [total]
  | cons u ws ih =>
    have h1 := h u (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    have e : total (u :: ws) = u.length + total ws := by simp [total]
    rw [e, List.length_cons]; nlinarith

/-! ### Queries and answers -/

theorem answer_eq (G : PartialGraph (Fin n)) (k q : ℕ) {i : ℕ} (hi : i < q * n) :
    ∃ h : i % n < n, (answers G k q).getD i [] =
      toWord (tree G (k + (i / n + 1)) (q - (i / n + 1)) ![⟨i % n, h⟩]) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hi
    · exact h
  have hiq : i / n < q := by rw [Nat.div_lt_iff_lt_mul hn]; exact hi
  refine ⟨Nat.mod_lt _ hn, ?_⟩
  have := ansW_eq (G := G) k q hiq ⟨i % n, Nat.mod_lt _ hn⟩
  simp only at this
  rw [Nat.div_add_mod' i n] at this
  rw [← this]
  simp [answers, List.getD_eq_getElem?_getD, hi]

theorem query_eq (G : PartialGraph (Fin n)) (k q : ℕ) {i : ℕ} (hi : i < q * n) :
    ∃ h : i % n < n, (famW (family G k q) ++ answers G k q).getD i [] =
      toWord (tree G (k + i / n) (q - i / n) ![⟨i % n, h⟩]) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hi
    · exact h
  by_cases hin : i < n
  · refine ⟨Nat.mod_lt _ hn, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_famW]; exact hin)]
    simp [famW, hin, Nat.div_eq_of_lt hin, Nat.mod_eq_of_lt hin, family]
  · have hi' : i - n < q * n := by omega
    obtain ⟨h, he⟩ := answer_eq G k q hi'
    have e1 : (i - n) % n = i % n := by
      conv_rhs => rw [show i = (i - n) + n by omega, Nat.add_mod_right]
    have e2 : (i - n) / n + 1 = i / n := by
      conv_rhs => rw [show i = (i - n) + n by omega]
      rw [Nat.add_div_right _ hn]
    refine ⟨Nat.mod_lt _ hn, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [length_famW]; omega),
      length_famW, ← List.getD_eq_getElem?_getD, he]
    simp only [e1, e2]

theorem shift_query (G : PartialGraph (Fin n)) (k q : ℕ) {i : ℕ} (hi : i < q * n) :
    ∃ (h : i % n < n) (k' q' : ℕ), k ≤ k' ∧
      (famW (family G k q) ++ answers G k q).getD i [] = toWord (tree G k' (q' + 1) ![⟨i % n, h⟩]) ∧
      (answers G k q).getD i [] = toWord (tree G (k' + 1) q' ![⟨i % n, h⟩]) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hi
    · exact h
  have hiq : i / n < q := by rw [Nat.div_lt_iff_lt_mul hn]; exact hi
  obtain ⟨h, h1⟩ := query_eq G k q hi
  obtain ⟨h', h2⟩ := answer_eq G k q hi
  refine ⟨h, k + i / n, q - i / n - 1, Nat.le_add_right _ _, ?_, ?_⟩
  · rw [h1, show q - i / n - 1 + 1 = q - i / n by omega]
  · rw [h2, show k + i / n + 1 = k + (i / n + 1) by ring, show q - i / n - 1 = q - (i / n + 1) by omega]

/-! ### The word of the scatter type -/

theorem length_toWord_flatMap_le (R c d : ℕ) (g : ℕ → List (List ℕ))
    (hg : ∀ r, (g r).length ≤ c ∧ ∀ w ∈ g r, w.length ≤ d) :
    (toWord ((List.range R).flatMap g)).length ≤ 1 + R * c * (d + 1) := by
  rw [length_toWord_words]
  induction R with
  | zero => simp [total]
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, total_append]
    obtain ⟨h1, h2⟩ := hg R
    have h3 := total_le (g R) d h2
    have : (g R).length * d ≤ c * d := Nat.mul_le_mul_right _ h1
    nlinarith

theorem length_toWord_emitList_le {adj : Fin n → List (Fin n)} {A : List (List ℕ)} {k q L : ℕ}
    (hA : ∀ u ∈ A, u.length ≤ L) :
    (toWord (emitList adj A k q)).length ≤ 1 + radius k q 1 * A.length * (L + 3) := by
  unfold emitList
  have hp := sortedDistinct_perm A
  have hlen : (sortedDistinct A).length ≤ A.length := by
    rw [hp.length_eq]; exact List.Sublist.length_le (List.dedup_sublist A)
  have hmem : ∀ u ∈ sortedDistinct A, u ∈ A := fun u hu => List.mem_dedup.mp (hp.mem_iff.mp hu)
  refine le_trans (length_toWord_flatMap_le _ A.length (L + 2) _ fun r => ⟨?_, ?_⟩) (by ring_nf; omega)
  · simp only [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen
  · intro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    have := hA u (hmem u (List.mem_filter.mp hu).1)
    simp [triple]; omega

theorem length_toWord_stp_le (G : PartialGraph (Fin n)) (k q L : ℕ)
    (hA : ∀ u ∈ answers G k q, u.length ≤ L) :
    (toWord (stp G k q)).length ≤ 1 + radius k q 1 * (q * n) * (L + 3) := by
  rw [toWord_stp (fun u v => mem_adjOf_resolved G u v), ← length_answers G k q]
  exact length_toWord_emitList_le hA

/-! ### The neighbors and the size -/

theorem length_nbrL (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (v : Fin n) :
    (nbrL H v).length = H.degree v := by
  classical
  have h := words_fin (Finset.univ.filter (H.Adj v))
  have hfil : ((List.range n).filter (fun z => ∃ h : z < n, (⟨z, h⟩ : Fin n) ∈
      Finset.univ.filter (H.Adj v))) = nbrL H v := by
    unfold nbrL; congr 1; funext z
    apply decide_eq_decide.mpr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h, ha⟩ => ⟨h, v.isLt, ha⟩, fun ⟨h, _, ha⟩ => ⟨h, ha⟩⟩
  rw [hfil] at h
  have hl := congrArg List.length h
  rw [List.length_map] at hl
  rw [← hl, ← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  unfold Finset.words
  rw [Finset.length_sort, Finset.card_image_of_injective]
  intro a b hab
  exact Fin.ext (by simpa [word_simps] using hab)

theorem sum_range_list (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem offL_eq (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    offL H n = 2 * H.edgeFinset.card := by
  rw [offL, sum_range_list (fun w => (nbrL H w).length) n, Finset.sum_range (fun i => (nbrL H i).length),
    ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun v _ => length_nbrL H v)

/-- **The neighbors and the size.** -/
theorem offL_add_le (G : PartialGraph (Fin n)) :
    offL G.edge n + offL G.nonEdge n ≤ 2 * G.size := by
  classical
  rw [offL_eq, offL_eq]
  have h2 : G.resolved.edgeSet.ncard = G.edge.edgeFinset.card + G.nonEdge.edgeFinset.card := by
    rw [PartialGraph.resolved, SimpleGraph.edgeSet_sup,
      Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr G.disjoint),
      ← SimpleGraph.coe_edgeFinset, ← SimpleGraph.coe_edgeFinset (G := G.nonEdge),
      Set.ncard_coe_finset, Set.ncard_coe_finset]
  simp only [PartialGraph.size]
  omega

end Lax185574Proofs.StpRam
