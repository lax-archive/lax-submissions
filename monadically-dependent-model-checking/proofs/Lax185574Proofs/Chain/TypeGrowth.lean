import Lax185574Proofs.Chain.TypeFormulas
import Lax710763.AlmostLinearNC

/-!
Monadically dependent classes have almost linear growth of `(k+1)`-types
(`thm:mondep-r-types` of the companion paper, by the reduction without
copying of its appendix `sec:types-without-copying`).

For atomic types this is the almost linear neighborhood complexity of
Dreier, Mählmann, McCarty, Pilipczuk and Toruńczyk (`Lax710763`), up to
the additive `|A|`. For `(k+2)`-types, the reduction colors a member `G`
of the class with five colors and passes to the bipartite graph `H` of
`φ*`. The atomic types of `H` over a set `R` of at most three vertices
per `(k+1)`-type refine the `(k+2)`-types of `G`, and `H` lies in a class
transduced from the original one.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset Classical
open Lax199508.GraphClasses Lax199508.NeighborhoodComplexity Lax710763.MonadicDependence

universe u

/-! ### Atomic types and neighborhood traces -/

section Trace

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem card_image_le_of_factor {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (f : α → β) (g : α → γ) (h : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    (s.image f).card ≤ (s.image g).card := by
  have hsub : s.image f ⊆ (s.image g).attach.image
      (fun c => f (Classical.choose (mem_image.1 c.2))) := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hb
    refine mem_image.2 ⟨⟨g x, mem_image_of_mem _ hx⟩, mem_attach _ _, ?_⟩
    have hc := Classical.choose_spec (mem_image.1 (mem_image_of_mem g hx))
    exact h _ hc.1 _ hx hc.2
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- The atomic types over `R` are at most the neighborhood traces on `R`
plus the vertices of `R`. -/
theorem numCls_le_traceCount (H : SimpleGraph V) [DecidableRel H.Adj] (R : Finset V) :
    numCls (tpRel H R 0) univ ≤ traceCount H (R : Set V) + R.card := by
  have hsplit : (univ : Finset V) = R ∪ (univ \ R) := by simp
  rw [hsplit]
  refine (numCls_union_le _ _ _).trans ?_
  rw [Nat.add_comm]
  refine Nat.add_le_add ?_ (numCls_le_card _ _)
  unfold numCls traceCount
  have hfin : ({S : Set V | ∃ v : V, S = H.neighborSet v ∩ (R : Set V)}).Finite := Set.toFinite _
  calc ((univ \ R).image (cls (tpRel H R 0))).card
      ≤ ((univ \ R).image fun v => H.neighborSet v ∩ (R : Set V)).card := by
        refine card_image_le_of_factor _ _ _ fun x hx y hy hxy => ?_
        refine (cls_eq_iff (tpRel_isEquiv R 0)).2 (tpRel_zero.2 (Or.inr ⟨(Finset.mem_sdiff.1 hx).2,
          (Finset.mem_sdiff.1 hy).2, fun z hz => ?_⟩))
        have := congrArg (fun S : Set V => z ∈ S) hxy
        simpa [SimpleGraph.mem_neighborSet, hz] using this
    _ = (((univ \ R).image fun v => H.neighborSet v ∩ (R : Set V) : Finset (Set V)) :
          Set (Set V)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard (fun S hS => by
        obtain ⟨v, -, rfl⟩ := mem_image.1 (mem_coe.1 hS)
        exact ⟨v, rfl⟩) hfin

end Trace

/-! ### The reduction -/

section Construction

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (A : Finset V) (k : ℕ)

/-- Three distinct elements of a set with at least three elements (and
`d` otherwise). -/
noncomputable def pick3 (c : Finset V) (d : V) : V × V × V :=
  if h : 2 < c.card then
    (Classical.choose (two_lt_card_iff.1 h),
      Classical.choose (Classical.choose_spec (two_lt_card_iff.1 h)),
      Classical.choose (Classical.choose_spec (Classical.choose_spec (two_lt_card_iff.1 h))))
  else (d, d, d)

theorem pick3_spec {c : Finset V} (h : 2 < c.card) (d : V) :
    (pick3 c d).1 ∈ c ∧ (pick3 c d).2.1 ∈ c ∧ (pick3 c d).2.2 ∈ c ∧
      (pick3 c d).1 ≠ (pick3 c d).2.1 ∧ (pick3 c d).1 ≠ (pick3 c d).2.2 ∧
        (pick3 c d).2.1 ≠ (pick3 c d).2.2 := by
  simp only [pick3, dif_pos h]
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (two_lt_card_iff.1 h)))

theorem pick3_indep {c : Finset V} (h : 2 < c.card) (d d' : V) : pick3 c d = pick3 c d' := by
  simp only [pick3, dif_pos h]

/-- The coloring of the reduction: `A`, the vertices of types with at most
two vertices, and three chosen vertices of every larger type. -/
noncomputable def redColors : Fin 5 → Set V :=
  ![(A : Set V),
    {v | (cls (tpRel G A k) v).card ≤ 2},
    {v | 2 < (cls (tpRel G A k) v).card ∧ v = (pick3 (cls (tpRel G A k) v) v).1},
    {v | 2 < (cls (tpRel G A k) v).card ∧ v = (pick3 (cls (tpRel G A k) v) v).2.1},
    {v | 2 < (cls (tpRel G A k) v).card ∧ v = (pick3 (cls (tpRel G A k) v) v).2.2}]

/-- The set `R` of the reduction, as a finite set. -/
noncomputable def redR : Finset V := univ.filter fun v => v ∈ rSet (redColors G A k)

variable {G A k}

theorem cls_eq_of_mem {x z : V} (h : z ∈ cls (tpRel G A k) x) :
    cls (tpRel G A k) z = cls (tpRel G A k) x :=
  ((cls_eq_iff (tpRel_isEquiv A k)).2 ((tpRel_isEquiv A k).symm _ _ (mem_cls.1 h)))

/-- The chosen vertices of a large type are colored. -/
theorem pick_mem_colors {x : V} (h : 2 < (cls (tpRel G A k) x).card) :
    (pick3 (cls (tpRel G A k) x) x).1 ∈ redColors G A k 2 ∧
    (pick3 (cls (tpRel G A k) x) x).2.1 ∈ redColors G A k 3 ∧
    (pick3 (cls (tpRel G A k) x) x).2.2 ∈ redColors G A k 4 := by
  obtain ⟨h1, h2, h3, -⟩ := pick3_spec h x
  simp only [redColors, Matrix.cons_val, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [cls_eq_of_mem h1]; exact ⟨h, congrArg (fun p => p.1) (pick3_indep h x _)⟩
  · rw [cls_eq_of_mem h2]; exact ⟨h, congrArg (fun p => p.2.1) (pick3_indep h x _)⟩
  · rw [cls_eq_of_mem h3]; exact ⟨h, congrArg (fun p => p.2.2) (pick3_indep h x _)⟩

/-- The colors are pairwise disjoint. -/
theorem redColors_disjoint {z : V} :
    (z ∈ redColors G A k 1 → z ∉ redColors G A k 2 ∧ z ∉ redColors G A k 3 ∧
      z ∉ redColors G A k 4) ∧
    (z ∈ redColors G A k 2 → z ∉ redColors G A k 3 ∧ z ∉ redColors G A k 4) ∧
    (z ∈ redColors G A k 3 → z ∉ redColors G A k 4) := by
  simp only [redColors, Matrix.cons_val, Set.mem_ofPred_eq]
  refine ⟨fun h => ⟨fun h' => by omega, fun h' => by omega, fun h' => by omega⟩,
    fun h => ⟨fun h' => ?_, fun h' => ?_⟩, fun h h' => ?_⟩
  · obtain ⟨-, -, -, hne, -, -⟩ := pick3_spec h.1 z
    exact hne (h.2.symm.trans h'.2)
  · obtain ⟨-, -, -, -, hne, -⟩ := pick3_spec h.1 z
    exact hne (h.2.symm.trans h'.2)
  · obtain ⟨-, -, -, -, -, hne⟩ := pick3_spec h.1 z
    exact hne (h.2.symm.trans h'.2)

/-- Adjacency of `H` between `x ∉ R` and `z ∈ R`. -/
theorem redGraph_adj {x z : V} (hx : x ∉ rSet (redColors G A k)) (hz : z ∈ rSet (redColors G A k)) :
    (redGraph G (redColors G A k) A k).Adj x z ↔
      PhiRel G (redColors G A k) A k x z := by
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact absurd hz h.1
  · intro h
    exact ⟨fun e => hx (e ▸ hz), Or.inl h⟩

/-- **The reduction refines the `(k+2)`-types.** -/
theorem tpRel_of_redGraph {x y : V}
    (h : tpRel (redGraph G (redColors G A k) A k) (redR G A k) 0 x y) :
    tpRel G A (k + 1) x y := by
  rcases tpRel_zero.1 h with rfl | ⟨hx, hy, hxy⟩
  · exact (tpRel_isEquiv A (k + 1)).refl _
  have hx' : x ∉ rSet (redColors G A k) := fun h' => hx (mem_filter.2 ⟨mem_univ _, h'⟩)
  have hy' : y ∉ rSet (redColors G A k) := fun h' => hy (mem_filter.2 ⟨mem_univ _, h'⟩)
  have hR : ∀ z ∈ rSet (redColors G A k), (redGraph G (redColors G A k) A k).Adj x z ↔
      (redGraph G (redColors G A k) A k).Adj y z :=
    fun z hz => hxy z (mem_filter.2 ⟨mem_univ _, hz⟩)
  have hdis := fun z => redColors_disjoint (G := G) (A := A) (k := k) (z := z)
  have hmemR : ∀ i : Fin 5, i ≠ 0 → ∀ z, z ∈ redColors G A k i → z ∈ rSet (redColors G A k) := by
    intro i hi z hz
    simp only [rSet, Set.mem_union]
    fin_cases i
    · exact absurd rfl hi
    all_goals simp_all
  -- the four kinds of vertices of `R`
  have hadj1 : ∀ w, ∀ z ∈ redColors G A k 1, ¬ w ∈ rSet (redColors G A k) →
      ((redGraph G (redColors G A k) A k).Adj w z ↔ G.Adj w z) := by
    intro w z hz hw
    rw [redGraph_adj hw (hmemR 1 (by decide) z hz)]
    obtain ⟨h2, h3, h4⟩ := (hdis z).1 hz
    have := hmemR 1 (by decide) z hz
    simp only [PhiRel]
    exact ⟨fun h => h.2.2.1 hz, fun h => ⟨hw, this, fun _ => h, fun h' => absurd h' h2,
      fun h' => absurd h' h3, fun h' => absurd h' h4⟩⟩
  have hadj2 : ∀ w, ∀ z ∈ redColors G A k 2, ¬ w ∈ rSet (redColors G A k) →
      ((redGraph G (redColors G A k) A k).Adj w z ↔ IsComplete G w (cls (tpRel G A k) z)) := by
    intro w z hz hw
    rw [redGraph_adj hw (hmemR 2 (by decide) z hz)]
    have h1 : z ∉ redColors G A k 1 := fun h1 => ((hdis z).1 h1).1 hz
    obtain ⟨h3, h4⟩ := (hdis z).2.1 hz
    simp only [PhiRel]
    have := hmemR 2 (by decide) z hz
    exact ⟨fun h => h.2.2.2.1 hz, fun h => ⟨hw, this, fun h' => absurd h' h1, fun _ => h,
      fun h' => absurd h' h3, fun h' => absurd h' h4⟩⟩
  have hadj3 : ∀ w, ∀ z ∈ redColors G A k 3, ¬ w ∈ rSet (redColors G A k) →
      ((redGraph G (redColors G A k) A k).Adj w z ↔
        IsAnticomplete G w (cls (tpRel G A k) z)) := by
    intro w z hz hw
    rw [redGraph_adj hw (hmemR 3 (by decide) z hz)]
    have h1 : z ∉ redColors G A k 1 := fun h1 => ((hdis z).1 h1).2.1 hz
    have h2 : z ∉ redColors G A k 2 := fun h2 => ((hdis z).2.1 h2).1 hz
    have h4 := (hdis z).2.2 hz
    simp only [PhiRel]
    have := hmemR 3 (by decide) z hz
    exact ⟨fun h => h.2.2.2.2.1 hz, fun h => ⟨hw, this, fun h' => absurd h' h1,
      fun h' => absurd h' h2, fun _ => h, fun h' => absurd h' h4⟩⟩
  have hadj4 : ∀ w, ∀ z ∈ redColors G A k 4, ¬ w ∈ rSet (redColors G A k) →
      ((redGraph G (redColors G A k) A k).Adj w z ↔ tpRel G A k w z) := by
    intro w z hz hw
    rw [redGraph_adj hw (hmemR 4 (by decide) z hz)]
    have h1 : z ∉ redColors G A k 1 := fun h1 => ((hdis z).1 h1).2.2 hz
    have h2 : z ∉ redColors G A k 2 := fun h2 => ((hdis z).2.1 h2).2 hz
    have h3 : z ∉ redColors G A k 3 := fun h3 => (hdis z).2.2 h3 hz
    simp only [PhiRel]
    have := hmemR 4 (by decide) z hz
    exact ⟨fun h => h.2.2.2.2.2 hz, fun h => ⟨hw, this, fun h' => absurd h' h1,
      fun h' => absurd h' h2, fun h' => absurd h' h3, fun _ => h⟩⟩
  -- vertices outside `R` lie in large types
  have hbig : ∀ w, w ∉ rSet (redColors G A k) → 2 < (cls (tpRel G A k) w).card := by
    intro w hw
    by_contra hc
    have hc' : (cls (tpRel G A k) w).card ≤ 2 := by omega
    exact hw (hmemR 1 (by decide) w (by simp only [redColors, Matrix.cons_val, Set.mem_ofPred_eq]; exact hc'))
  have hEk := tpRel_isEquiv (G := G) A k
  rw [tpRel_succ]
  refine ⟨?_, fun w => ?_⟩
  · -- the same `(k+1)`-type, through the chosen vertex `r^∈`
    set c := cls (tpRel G A k) x
    have hc := hbig x hx'
    have hpm := (pick_mem_colors hc).2.2
    have hpc := (pick3_spec hc x).2.2.1
    have h1 : tpRel G A k x (pick3 c x).2.2 := mem_cls.1 hpc
    have h2 := (hadj4 x _ hpm hx').2 h1
    have h3 := (hadj4 y _ hpm hy').1 ((hR _ (hmemR 4 (by decide) _ hpm)).1 h2)
    exact hEk.trans _ _ _ h1 (hEk.symm _ _ h3)
  · set Q := cls (tpRel G A k) w
    rcases Nat.lt_or_ge 2 Q.card with hQ | hQ
    · obtain ⟨p2, p3, -⟩ := pick_mem_colors hQ
      have hc2 : cls (tpRel G A k) (pick3 Q w).1 = Q := cls_eq_of_mem (pick3_spec hQ w).1
      have hc3 : cls (tpRel G A k) (pick3 Q w).2.1 = Q := cls_eq_of_mem (pick3_spec hQ w).2.1
      refine ⟨?_, ?_⟩
      · rw [← hc2, ← hadj2 x _ p2 hx', ← hadj2 y _ p2 hy']
        exact hR _ (hmemR 2 (by decide) _ p2)
      · rw [← hc3, ← hadj3 x _ p3 hx', ← hadj3 y _ p3 hy']
        exact hR _ (hmemR 3 (by decide) _ p3)
    · -- a small type lies in `R₀`
      have hsmall : ∀ z ∈ Q, z ∈ redColors G A k 1 := by
        intro z hz
        simp only [redColors, Matrix.cons_val, Set.mem_ofPred_eq]
        rw [cls_eq_of_mem hz]; exact hQ
      have hxQ : ∀ z ∈ Q, z ≠ x := fun z hz e => hx' (e ▸ hmemR 1 (by decide) z (hsmall z hz))
      have hyQ : ∀ z ∈ Q, z ≠ y := fun z hz e => hy' (e ▸ hmemR 1 (by decide) z (hsmall z hz))
      have key : ∀ z ∈ Q, (G.Adj x z ↔ G.Adj y z) := by
        intro z hz
        rw [← hadj1 x z (hsmall z hz) hx', ← hadj1 y z (hsmall z hz) hy']
        exact hR z (hmemR 1 (by decide) z (hsmall z hz))
      refine ⟨⟨fun h z hz _ => (key z hz).1 (h z hz (hxQ z hz)),
          fun h z hz _ => (key z hz).2 (h z hz (hyQ z hz))⟩,
        ⟨fun h z hz _ hyz => h z hz (hxQ z hz) ((key z hz).2 hyz),
          fun h z hz _ hxz => h z hz (hyQ z hz) ((key z hz).1 hxz)⟩⟩

theorem mem_rSet_of_mem {i : Fin 5} (hi : i ≠ 0) {z : V} (hz : z ∈ redColors G A k i) :
    z ∈ rSet (redColors G A k) := by
  simp only [rSet, Set.mem_union]
  fin_cases i
  · exact absurd rfl hi
  all_goals simp_all

theorem redR_nonempty [Nonempty V] : (redR G A k).Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  rcases Nat.lt_or_ge 2 (cls (tpRel G A k) x).card with h | h
  · exact ⟨_, mem_filter.2 ⟨mem_univ _, mem_rSet_of_mem (i := 2) (by decide)
      (pick_mem_colors h).1⟩⟩
  · refine ⟨x, mem_filter.2 ⟨mem_univ _, mem_rSet_of_mem (i := 1) (by decide) ?_⟩⟩
    simp only [redColors, Matrix.cons_val, Set.mem_ofPred_eq]; exact h

/-- `|R| ≤ 3 |𝒯_{k+1}(G, A)|`. -/
theorem card_redR_le : (redR G A k).card ≤ 3 * numCls (tpRel G A k) univ := by
  unfold numCls
  rw [card_eq_sum_card_fiberwise (f := cls (tpRel G A k)) (t := univ.image (cls (tpRel G A k)))
    (fun z _ => mem_image_of_mem _ (mem_univ z))]
  rw [Nat.mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun c hc => ?_
  obtain ⟨x0, -, rfl⟩ := mem_image.1 hc
  set F := (redR G A k).filter fun z => cls (tpRel G A k) z = cls (tpRel G A k) x0
  rcases Nat.lt_or_ge 2 (cls (tpRel G A k) x0).card with h | h
  · set p := pick3 (cls (tpRel G A k) x0) x0
    have hsub : F ⊆ {p.1, p.2.1, p.2.2} := by
      intro z hz
      obtain ⟨hzR, hzc⟩ := mem_filter.1 hz
      have hzR' := (mem_filter.1 hzR).2
      simp only [rSet, Set.mem_union] at hzR'
      simp only [mem_insert, mem_singleton]
      simp only [redColors, Matrix.cons_val, Set.mem_ofPred_eq] at hzR'
      rw [hzc] at hzR'
      rcases hzR' with ((h1 | ⟨-, h2⟩) | ⟨-, h3⟩) | ⟨-, h4⟩
      · omega
      · left; rw [h2, pick3_indep h z x0]
      · right; left; rw [h3, pick3_indep h z x0]
      · right; right; rw [h4, pick3_indep h z x0]
    exact (card_le_card hsub).trans (card_le_three)
  · have hsub : F ⊆ cls (tpRel G A k) x0 := by
      intro z hz
      rw [← (mem_filter.1 hz).2]
      exact mem_cls.2 ((tpRel_isEquiv A k).refl z)
    exact (card_le_card hsub).trans (by omega)

end Construction

/-! ### Growth bounds -/

section Growth

/-- **Almost linear growth of types in monadically dependent classes.**
For every `k` and `η > 0` there is `c` with `|𝒯_{k+1}(G, A)| ≤ c |A|^{1+η}`
for all members `G` of the class and nonempty `A`. -/
theorem exists_typeGrowth (C : GraphClass) (hC : MonadicallyDependent C) :
    ∀ (k : ℕ) (η : ℝ), 0 < η → ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      [DecidableRel G.Adj], C n G → ∀ A : Finset (Fin n), A.Nonempty →
        (numCls (tpRel G A k) univ : ℝ) ≤ c * (A.card : ℝ) ^ (1 + η) := by
  intro k
  induction k with
  | zero =>
    intro η hη
    obtain ⟨c, hc⟩ := Lax710763.AlmostLinearNC.hasAlmostLinearNC_of_monadicallyDependent C hC η hη
    refine ⟨max c 0 + 1, by positivity, fun n G _ hG A hA => ?_⟩
    have h1 := numCls_le_traceCount G A
    have h2 := hc n G hG (A : Set (Fin n)) (by simpa using hA)
    rw [Set.ncard_coe_finset] at h2
    have ha : (1 : ℝ) ≤ A.card := by exact_mod_cast card_pos.2 hA
    have hpow : (A.card : ℝ) ≤ (A.card : ℝ) ^ (1 + η) := by
      conv_lhs => rw [← Real.rpow_one (A.card : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le ha (by linarith)
    have hpos : 0 ≤ (A.card : ℝ) ^ (1 + η) := by positivity
    calc (numCls (tpRel G A 0) univ : ℝ) ≤ traceCount G (A : Set (Fin n)) + A.card := by
          exact_mod_cast h1
      _ ≤ c * (A.card : ℝ) ^ (1 + η) + (A.card : ℝ) ^ (1 + η) := by linarith
      _ ≤ (max c 0 + 1) * (A.card : ℝ) ^ (1 + η) := by
          have : c * (A.card : ℝ) ^ (1 + η) ≤ max c 0 * (A.card : ℝ) ^ (1 + η) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
          linarith
  | succ k ih =>
    intro η hη
    set η' := min (η / 3) 1
    have hη' : 0 < η' := lt_min (by linarith) one_pos
    have hη'1 : η' ≤ 1 := min_le_right _ _
    have hη'3 : η' ≤ η / 3 := min_le_left _ _
    have hsq : (1 + η') * (1 + η') ≤ 1 + η := by nlinarith
    obtain ⟨c1, hc1, hk⟩ := ih η' hη'
    obtain ⟨c2, hc2⟩ := Lax710763.AlmostLinearNC.hasAlmostLinearNC_of_monadicallyDependent
      (redClass C k) (monadicallyDependent_redClass C hC k) η' hη'
    set d1 := max c1 1
    set d2 := max c2 0
    refine ⟨d2 * (3 * d1) ^ (1 + η') + 3 * d1, by positivity, fun n G _ hG A hA => ?_⟩
    have : Nonempty (Fin n) := ⟨hA.choose⟩
    set H := redGraph G (redColors G A k) A k
    set R := redR G A k
    have hHmem : redClass C k n H := ⟨G, hG, redColors G A k, fun x y =>
      (realizeIn_psiF G (redColors G A k) A rfl k ![x, y]).symm⟩
    have hRne : R.Nonempty := redR_nonempty
    -- the reduction
    have h1 : numCls (tpRel G A (k + 1)) univ ≤ numCls (tpRel H R 0) univ :=
      numCls_le_of_le (tpRel_isEquiv A (k + 1)) (tpRel_isEquiv R 0)
        fun x _ y _ h => tpRel_of_redGraph h
    have h2 := numCls_le_traceCount H R
    have h3 := hc2 n H hHmem (R : Set (Fin n)) (by simpa using hRne)
    rw [Set.ncard_coe_finset] at h3
    have h4 := card_redR_le (G := G) (A := A) (k := k)
    have h5 := hk n G hG A hA
    -- real estimates
    have ha : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast card_pos.2 hA
    have hx1 : (1 : ℝ) ≤ (numCls (tpRel G A k) univ : ℝ) := by
      have : 1 ≤ numCls (tpRel G A k) univ := by
        obtain ⟨v, hv⟩ := hA
        exact card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ v)⟩
      exact_mod_cast this
    have hR : (R.card : ℝ) ≤ 3 * (numCls (tpRel G A k) univ : ℝ) := by exact_mod_cast h4
    set a : ℝ := (A.card : ℝ)
    set x : ℝ := (numCls (tpRel G A k) univ : ℝ)
    have hR1 : (1 : ℝ) ≤ R.card := by exact_mod_cast card_pos.2 hRne
    have hxa : x ≤ d1 * a ^ (1 + η') :=
      h5.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hd1 : 1 ≤ d1 := le_max_right _ _
    have hpow1 : a ^ (1 + η') ≤ a ^ (1 + η) :=
      Real.rpow_le_rpow_of_exponent_le ha (by linarith)
    have hpow2 : (a ^ (1 + η')) ^ (1 + η') ≤ a ^ (1 + η) := by
      rw [← Real.rpow_mul (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le ha hsq
    have hRpow : (R.card : ℝ) ^ (1 + η') ≤ (3 * d1) ^ (1 + η') * a ^ (1 + η) := by
      calc (R.card : ℝ) ^ (1 + η') ≤ (3 * d1 * a ^ (1 + η')) ^ (1 + η') :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
        _ = (3 * d1) ^ (1 + η') * (a ^ (1 + η')) ^ (1 + η') :=
            Real.mul_rpow (by positivity) (by positivity)
        _ ≤ (3 * d1) ^ (1 + η') * a ^ (1 + η) :=
            mul_le_mul_of_nonneg_left hpow2 (by positivity)
    have hRlin : (R.card : ℝ) ≤ 3 * d1 * a ^ (1 + η) := by
      calc (R.card : ℝ) ≤ 3 * x := hR
        _ ≤ 3 * (d1 * a ^ (1 + η')) := by linarith
        _ ≤ 3 * (d1 * a ^ (1 + η)) := by
            have : 0 ≤ d1 := by linarith
            nlinarith
        _ = 3 * d1 * a ^ (1 + η) := by ring
    have hc2' : c2 * (R.card : ℝ) ^ (1 + η') ≤ d2 * (R.card : ℝ) ^ (1 + η') :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hd2 : 0 ≤ d2 := le_max_right _ _
    calc (numCls (tpRel G A (k + 1)) univ : ℝ) ≤ numCls (tpRel H R 0) univ := by
          exact_mod_cast h1
      _ ≤ traceCount H (R : Set (Fin n)) + R.card := by exact_mod_cast h2
      _ ≤ d2 * (R.card : ℝ) ^ (1 + η') + R.card := by linarith
      _ ≤ d2 * ((3 * d1) ^ (1 + η') * a ^ (1 + η)) + 3 * d1 * a ^ (1 + η) := by
          have := mul_le_mul_of_nonneg_left hRpow hd2
          linarith
      _ = (d2 * (3 * d1) ^ (1 + η') + 3 * d1) * a ^ (1 + η) := by ring

end Growth

end Lax185574Proofs.Chain
