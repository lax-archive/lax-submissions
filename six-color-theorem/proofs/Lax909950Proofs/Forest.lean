import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Lax909950Proofs.Deletion

/-!
Drawings of forests have exactly one face. Both sides of a leaf edge lie in the
same face; deleting leaf edges one at a time reduces to the edgeless graph.
-/

namespace Lax909950Proofs

open Lax68.StraightLineDrawings Lax909950.EulerFormula Set Topology

variable {V : Type*} {G : SimpleGraph V}

theorem leaf_isClosed_segment (x y : Point) : IsClosed (segment ℝ x y) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

/-- Near the leaf endpoint `b`, the image consists only of the segment of `ab`. -/
theorem leaf_eventually_mem_segment [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hleaf : ∀ c, G.Adj b c → c = a) :
    ∀ᶠ y in 𝓝 (D.point b), y ∈ image D → y ∈ segment ℝ (D.point a) (D.point b) := by
  have h1 : ∀ᶠ y in 𝓝 (D.point b), ∀ c, c ≠ b → y ≠ D.point c := by
    refine Filter.eventually_all.2 fun c => ?_
    by_cases hc : c = b
    · exact .of_forall fun _ h => absurd hc h
    · exact (eventually_ne_nhds (D.injective.ne (Ne.symm hc))).mono fun _ hy _ => hy
  have h2 : ∀ᶠ y in 𝓝 (D.point b), ∀ c d, G.Adj c d → s(c, d) ≠ s(a, b) →
      y ∉ segment ℝ (D.point c) (D.point d) := by
    refine Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun d => ?_
    by_cases hcd : G.Adj c d ∧ s(c, d) ≠ s(a, b)
    · have hq : D.point b ∉ segment ℝ (D.point c) (D.point d) := by
        by_cases hbc : b = c
        · subst hbc
          exact absurd (by rw [hleaf d hcd.1, Sym2.eq_swap]) hcd.2
        by_cases hbd : b = d
        · subst hbd
          exact absurd (by rw [hleaf c hcd.1.symm]) hcd.2
        exact D.noVertexOnEdge hcd.1 hbc hbd
      exact Filter.mem_of_superset ((leaf_isClosed_segment _ _).isOpen_compl.mem_nhds hq)
        fun _ hy _ _ => hy
    · exact .of_forall fun _ h h' => absurd ⟨h, h'⟩ hcd
  refine (h1.and h2).mono fun y ⟨hy1, hy2⟩ hy => ?_
  simp only [Lax909950.EulerFormula.image, mem_union, mem_range, mem_iUnion] at hy
  rcases hy with ⟨c, rfl⟩ | ⟨c, d, hcd, hy⟩
  · by_cases hc : c = b
    · subst hc; exact right_mem_segment _ _ _
    · exact absurd rfl (hy1 c hc)
  · by_cases he : s(c, d) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hy
      · rwa [segment_symm]
    · exact absurd hy (hy2 c d hcd he)

/-- Both sides of an edge `ab` whose endpoint `b` has no other neighbor lie in the
same face. -/
theorem edgeFace_eq_of_leaf [Finite V] (D : StraightLineDrawing G) {a b : V}
    (hab : G.Adj a b) (hleaf : ∀ c, G.Adj b c → c = a) :
    edgeFace D a b true = edgeFace D a b false := by
  set p := D.point a with hp
  set q := D.point b with hq
  set v : Point := q - p with hv
  have hpq : p ≠ q := D.injective.ne hab.ne
  have hN : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    rcases eq_or_ne v.1 0 with h1 | h1
    · have : v.2 ≠ 0 := by
        intro h2; apply hpq
        have : v = 0 := Prod.ext h1 h2
        rw [hv, sub_eq_zero] at this; exact this.symm
      positivity
    · positivity
  set N := v.1 ^ 2 + v.2 ^ 2 with hNdef
  let n : Point := (-v.2, v.1)
  let g : ℝ × ℝ → Point := fun z => q + z.1 • v + z.2 • n
  let h : Point → ℝ × ℝ := fun y =>
    (((y - q).1 * v.1 + (y - q).2 * v.2) / N, ((y - q).1 * (-v.2) + (y - q).2 * v.1) / N)
  have hg : Continuous g := by fun_prop
  have hh : Continuous h := by fun_prop
  have hhg : ∀ z, h (g z) = z := by
    rintro ⟨t, s⟩
    simp only [g, h, n, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    constructor <;> field_simp <;> ring
  have hgh : ∀ y, g (h y) = y := by
    rintro ⟨y1, y2⟩
    simp only [g, h, n, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    constructor <;> field_simp <;> ring
  have hg0 : g 0 = q := by simp [g]
  -- a square around `0` whose image avoids all of the drawing except the segment `pq`
  have hE := leaf_eventually_mem_segment D hleaf
  have hgt : Filter.Tendsto g (𝓝 0) (𝓝 q) := hg0 ▸ hg.continuousAt.tendsto
  obtain ⟨δ, hδ, hδE⟩ := Metric.eventually_nhds_iff.1 (hgt.eventually hE)
  set η := min (δ / 2) (1 / 2) with hη
  have hη0 : 0 < η := by positivity
  have hηδ : η < δ := by
    have := min_le_left (δ / 2) (1 / 2); linarith
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  set Q : Set (ℝ × ℝ) := Ioo (-η) η ×ˢ Ioo (-η) η with hQ
  have hsegim : segment ℝ p q ⊆ image D := fun y hy =>
    Or.inr (mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨hab, hy⟩⟩⟩)
  have key : ∀ z ∈ Q, (g z ∈ image D ↔ z.2 = 0 ∧ z.1 ≤ 0) := by
    rintro ⟨t, s⟩ ⟨⟨ht1, ht2⟩, ⟨hs1, hs2⟩⟩
    constructor
    · intro hz
      have hd : dist (t, s) (0 : ℝ × ℝ) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero, abs_lt]
        constructor <;> constructor <;> linarith
      obtain ⟨α, β, hα, hβ, hαβ, heq⟩ := hδE hd hz
      have e1 := congrArg Prod.fst heq
      have e2 := congrArg Prod.snd heq
      simp only [g, n, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
        hv, Prod.fst_sub, Prod.snd_sub, ← hp, ← hq] at e1 e2
      have hβ' : β = 1 - α := by linarith
      subst hβ'
      have hs0 : s * N = 0 := by
        rw [hNdef, hv]; simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (q.2 - p.2) * e1 - (q.1 - p.1) * e2
      have hs : s = 0 := by
        rcases mul_eq_zero.1 hs0 with h | h
        · exact h
        · exact absurd h hN.ne'
      subst hs
      have ht : (t + α) * N = 0 := by
        rw [hNdef, hv]; simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (-(q.1 - p.1)) * e1 - (q.2 - p.2) * e2
      have : t + α = 0 := by
        rcases mul_eq_zero.1 ht with h | h
        · exact h
        · exact absurd h hN.ne'
      exact ⟨rfl, by linarith⟩
    · rintro ⟨rfl, ht⟩
      apply hsegim
      refine ⟨-t, 1 + t, by linarith, by linarith, by ring, ?_⟩
      simp only [g, n, zero_smul, add_zero, hv]
      ext <;> simp <;> ring
  -- the region `T` is connected
  set T : Set (ℝ × ℝ) := Q ∩ {z | ¬(z.2 = 0 ∧ z.1 ≤ 0)} with hT
  have hTc : IsPreconnected T := by
    have hU : IsPreconnected (Ioo (-η) η ×ˢ Ioo 0 η) :=
      ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
    have hL : IsPreconnected (Ioo (-η) η ×ˢ Ioo (-η) 0) :=
      ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
    have hR : IsPreconnected (Ioo 0 η ×ˢ Ioo (-η) η) :=
      ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
    have h1 := hU.union (η / 2, η / 2)
      (by constructor <;> constructor <;> simp <;> linarith)
      (by constructor <;> constructor <;> simp <;> linarith) hR
    have h2 := h1.union (η / 2, -(η / 2))
      (by right; constructor <;> constructor <;> simp <;> linarith)
      (by constructor <;> constructor <;> simp <;> linarith) hL
    convert h2 using 1
    ext ⟨t, s⟩
    simp only [hT, hQ, mem_inter_iff, mem_prod, mem_Ioo, mem_ofPred_eq, mem_union, not_and,
      not_le]
    constructor
    · rintro ⟨⟨⟨ht1, ht2⟩, hs1, hs2⟩, hn⟩
      rcases lt_trichotomy s 0 with hs | hs | hs
      · right; exact ⟨⟨ht1, ht2⟩, hs1, hs⟩
      · left; right; exact ⟨⟨hn hs, ht2⟩, hs1, hs2⟩
      · left; left; exact ⟨⟨ht1, ht2⟩, hs, hs2⟩
    · rintro ((⟨⟨ht1, ht2⟩, hs1, hs2⟩ | ⟨⟨ht1, ht2⟩, hs1, hs2⟩) | ⟨⟨ht1, ht2⟩, hs1, hs2⟩)
      · exact ⟨⟨⟨ht1, ht2⟩, by linarith, hs2⟩, fun h => by linarith⟩
      · exact ⟨⟨⟨by linarith, ht2⟩, hs1, hs2⟩, fun _ => ht1⟩
      · exact ⟨⟨⟨ht1, ht2⟩, hs1, by linarith⟩, fun h => by linarith⟩
  set S := g '' T with hS
  have hSc : IsPreconnected S := hTc.image g hg.continuousOn
  have hSI : S ⊆ (image D)ᶜ := by
    rintro _ ⟨z, ⟨hzQ, hz⟩, rfl⟩ hzI
    exact hz ((key z hzQ).1 hzI)
  -- a point of the open segment inside the region
  set x := g (-(η / 2), 0) with hx
  have hxseg : x ∈ edgeSeg D a b := by
    refine ⟨η / 2, 1 - η / 2, by linarith, by linarith, by ring, ?_⟩
    simp only [hx, g, n, zero_smul, add_zero, hv]
    ext <;> simp <;> ring
  have hmeet : ∀ s, ∃ y ∈ S, y ∈ edgeFace D a b s := by
    intro s
    have hcl := edgeSeg_subset_closure_edgeFace D hab s hxseg
    have hnhds : h ⁻¹' Q ∈ 𝓝 x := by
      refine (hh.isOpen_preimage _ (isOpen_Ioo.prod isOpen_Ioo)).mem_nhds ?_
      show h (g _) ∈ Q
      rw [hhg]
      constructor <;> constructor <;> simp <;> linarith
    obtain ⟨y, hyQ, hyF⟩ := mem_closure_iff_nhds.1 hcl _ hnhds
    have hyI : y ∉ image D := subset_compl_of_mem_faces D (edgeFace_mem_faces D hab s) hyF
    refine ⟨y, ⟨h y, ⟨hyQ, fun hk => hyI ?_⟩, hgh y⟩, hyF⟩
    have := (key (h y) hyQ).2 hk
    rwa [hgh] at this
  obtain ⟨y1, hy1S, hy1F⟩ := hmeet true
  obtain ⟨y2, hy2S, hy2F⟩ := hmeet false
  have hsub := subset_face_of_isPreconnected D hSc hSI (edgeFace_mem_faces D hab true) hy1S hy1F
  exact eq_of_mem_faces D (edgeFace_mem_faces D hab true) (edgeFace_mem_faces D hab false)
    (hsub hy2S) hy2F

/-- A finite acyclic graph with an edge has a leaf edge. -/
theorem exists_leaf_edge [Finite V] (hG : G.IsAcyclic) {x y : V} (hxy : G.Adj x y) :
    ∃ a b, G.Adj a b ∧ ∀ c, G.Adj b c → c = a := by
  have : Nonempty V := ⟨x⟩
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hnil : ¬p.Nil := by
    intro hn
    have h1 := hmax _ _ (SimpleGraph.Walk.cons hxy SimpleGraph.Walk.nil)
      (SimpleGraph.Walk.IsPath.nil.cons (by simpa using hxy.ne))
    rw [SimpleGraph.Walk.length_eq_zero_iff.2 hn] at h1
    simp at h1
  refine ⟨p.snd, u, (p.adj_snd hnil).symm, fun c hc => ?_⟩
  by_cases hcs : c ∈ p.support
  · exact hG.eq_snd_of_adj_start hp hc hcs
  · have h1 := hmax _ _ (SimpleGraph.Walk.cons hc.symm p) (hp.cons hcs)
    simp at h1

theorem encard_faces_of_isAcyclic_aux [Finite V] (n : ℕ) :
    ∀ (G : SimpleGraph V) (D : StraightLineDrawing G), G.IsAcyclic →
      G.edgeSet.encard = n → (faces D).encard = 1 := by
  induction n with
  | zero =>
    intro G D _ hn
    exact encard_faces_of_edgeless D (SimpleGraph.edgeSet_eq_empty.1 (encard_eq_zero.1 hn))
  | succ n ih =>
    intro G D hG hn
    obtain ⟨e, he⟩ : G.edgeSet.Nonempty := by
      rw [nonempty_iff_ne_empty]; rintro h; simp [h] at hn; norm_cast at hn
    induction e using Sym2.ind with
    | h x y =>
    obtain ⟨a, b, hab, hleaf⟩ := exists_leaf_edge hG (G.mem_edgeSet.1 he)
    rw [encard_faces_deleteEdge_of_eq D hab (edgeFace_eq_of_leaf D hab hleaf)]
    refine ih _ _ (hG.anti (G.deleteEdges_le _)) ?_
    have h1 := encard_sdiff_singleton_add_one (G.mem_edgeSet.2 hab)
    rw [← SimpleGraph.edgeSet_deleteEdges, hn] at h1
    have hfin : (G.deleteEdges {s(a, b)}).edgeSet.encard ≠ ⊤ := by
      intro h; rw [h] at h1; norm_cast at h1
    lift (G.deleteEdges {s(a, b)}).edgeSet.encard to ℕ using hfin with m hm
    norm_cast at h1 ⊢
    omega

/-- A drawing of a forest has exactly one face. -/
theorem encard_faces_of_isAcyclic [Finite V] (D : StraightLineDrawing G)
    (hG : G.IsAcyclic) : (faces D).encard = 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, G.edgeSet.encard = n :=
    ENat.ne_top_iff_exists.1 (Set.toFinite _).encard_lt_top.ne |>.imp fun _ h => h.symm
  exact encard_faces_of_isAcyclic_aux n G D hG hn

end Lax909950Proofs
