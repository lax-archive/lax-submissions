import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Tactic

/-!
The hereditary edge-density bound for the finite one-inclusion graph.
An edge is represented once, by its upper endpoint and the coordinate erased.
-/

namespace Lax457868Proofs.SamplerOneInclusion

variable {α : Type*} [DecidableEq α]

/-- Undirected one-inclusion edges, represented once by their upper endpoint
and the coordinate erased to obtain the lower endpoint. -/
def edges (H : Finset (Finset α)) : Finset (Finset α × α) :=
  (H.biUnion fun h => h.image fun a => (h, a)).filter
    (fun e => e.1.erase e.2 ∈ H)

lemma mem_edges {H : Finset (Finset α)} {h : Finset α} {a : α} :
    (h, a) ∈ edges H ↔ h ∈ H ∧ a ∈ h ∧ h.erase a ∈ H := by
  simp [edges, and_assoc]

/-- Number of edges in the one-inclusion graph of `H`. -/
def edgeCount (H : Finset (Finset α)) : ℕ := (edges H).card

lemma edges_mono {H K : Finset (Finset α)} (hHK : H ⊆ K) :
    edges H ⊆ edges K := by
  intro e he
  rcases e with ⟨h, a⟩
  rw [mem_edges] at he ⊢
  exact ⟨hHK he.1, he.2.1, hHK he.2.2⟩

lemma edges_inter (H K : Finset (Finset α)) :
    edges (H ∩ K) = edges H ∩ edges K := by
  ext e
  rcases e with ⟨h, a⟩
  simp only [mem_edges, Finset.mem_inter]
  tauto

lemma edges_union_superset (H K : Finset (Finset α)) :
    edges H ∪ edges K ⊆ edges (H ∪ K) :=
  Finset.union_subset (edges_mono Finset.subset_union_left)
    (edges_mono Finset.subset_union_right)

/-- Edge count is supermodular as an induced-graph edge count. -/
lemma edgeCount_supermodular (H K : Finset (Finset α)) :
    edgeCount H + edgeCount K ≤ edgeCount (H ∪ K) + edgeCount (H ∩ K) := by
  unfold edgeCount
  rw [← Finset.card_union_add_card_inter, ← edges_inter]
  exact Nat.add_le_add_right (Finset.card_le_card (edges_union_superset H K)) _

/-- Forget coordinate `a` from every pattern. -/
def projection (H : Finset (Finset α)) (a : α) : Finset (Finset α) :=
  H.image (fun h => h.erase a)

/-- Patterns realized both with and without coordinate `a`. -/
def doubleFiber (H : Finset (Finset α)) (a : α) : Finset (Finset α) :=
  H.nonMemberSubfamily a ∩ H.memberSubfamily a

lemma projection_eq_union (H : Finset (Finset α)) (a : α) :
    projection H a = H.nonMemberSubfamily a ∪ H.memberSubfamily a := by
  simpa [projection, Finset.union_comm] using
    (Finset.memberSubfamily_union_nonMemberSubfamily a H).symm

lemma shatters_projection_of_shatters (H : Finset (Finset α))
    (a : α) {S : Finset α} (ha : a ∉ S)
    (hs : (projection H a).Shatters S) : H.Shatters S := by
  intro T hT
  obtain ⟨u, hu, hSu⟩ := hs hT
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu
  refine ⟨h, hh, ?_⟩
  rw [← hSu]
  ext x
  by_cases hxa : x = a
  · subst x
    simp [ha]
  · simp [hxa]

lemma shatters_insert_of_doubleFiber (H : Finset (Finset α))
    (a : α) {S : Finset α} (ha : a ∉ S)
    (hs : (doubleFiber H a).Shatters S) :
    H.Shatters (insert a S) := by
  intro T hT
  by_cases hat : a ∈ T
  · have hsub : T.erase a ⊆ S := by
      intro x hx
      have hxT : x ∈ T := Finset.mem_of_mem_erase hx
      have hxU := hT hxT
      rcases Finset.mem_insert.mp hxU with rfl | hxS
      · exact False.elim ((Finset.ne_of_mem_erase hx) rfl)
      · exact hxS
    obtain ⟨u, hu, hSu⟩ := hs hsub
    have hum : u ∈ H.memberSubfamily a := (Finset.mem_inter.mp hu).2
    have hh : insert a u ∈ H := (Finset.mem_memberSubfamily.mp hum).1
    refine ⟨insert a u, hh, ?_⟩
    rw [← Finset.insert_inter_distrib, hSu]
    rw [Finset.insert_erase hat]
  · have hsub : T ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with hxa | hxS
      · exact False.elim (hat (hxa ▸ hx))
      · exact hxS
    obtain ⟨u, hu, hSu⟩ := hs hsub
    have hum : u ∈ H.nonMemberSubfamily a := (Finset.mem_inter.mp hu).1
    have ⟨hh, hau⟩ := Finset.mem_nonMemberSubfamily.mp hum
    refine ⟨u, hh, ?_⟩
    rw [Finset.insert_inter_of_notMem hau, hSu]

lemma vcDim_projection_le (H : Finset (Finset α)) (a : α) :
    (projection H a).vcDim ≤ H.vcDim := by
  unfold Finset.vcDim
  apply Finset.sup_le
  intro S hS
  have hs : (projection H a).Shatters S := Finset.mem_shatterer.mp hS
  obtain ⟨u, hu, hSu⟩ := hs.exists_superset
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu
  have ha : a ∉ S := by
    intro haS
    have : a ∉ h.erase a := by simp
    exact this (hSu haS)
  exact (shatters_projection_of_shatters H a ha hs).card_le_vcDim

/-- A pattern realized on both sides of a coordinate has one extra shattered
coordinate in the original family. -/
lemma vcDim_doubleFiber_succ_le (H : Finset (Finset α)) (a : α)
    (hne : (doubleFiber H a).Nonempty) :
    (doubleFiber H a).vcDim + 1 ≤ H.vcDim := by
  have hbase : 1 ≤ H.vcDim := by
    have hs : (doubleFiber H a).Shatters ∅ := Finset.shatters_empty.mpr hne
    have hins := shatters_insert_of_doubleFiber H a (by simp) hs
    simpa using hins.card_le_vcDim
  have hle : (doubleFiber H a).vcDim ≤ H.vcDim - 1 := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro S hS
    have hs : (doubleFiber H a).Shatters S := Finset.mem_shatterer.mp hS
    obtain ⟨u, hu, hSu⟩ := hs.exists_superset
    have ha : a ∉ S := by
      have hau : a ∉ u :=
        (Finset.mem_nonMemberSubfamily.mp (Finset.mem_inter.mp hu).1).2
      intro haS
      exact hau (hSu haS)
    have hins := shatters_insert_of_doubleFiber H a ha hs
    have hcard := hins.card_le_vcDim
    rw [Finset.card_insert_of_notMem ha] at hcard
    change S.card ≤ H.vcDim - 1
    omega
  omega

private lemma mem_edges_lower_iff (H : Finset (Finset α)) (a : α)
    (h : Finset α) (x : α) :
    (h, x) ∈ edges (H.nonMemberSubfamily a) ↔
      (h, x) ∈ edges H ∧ a ∉ h := by
  simp only [mem_edges, Finset.mem_nonMemberSubfamily]
  constructor
  · rintro ⟨⟨hh, ha⟩, hx, ⟨hl, -⟩⟩
    exact ⟨⟨hh, hx, hl⟩, ha⟩
  · rintro ⟨⟨hh, hx, hl⟩, ha⟩
    refine ⟨⟨hh, ha⟩, hx, ⟨hl, ?_⟩⟩
    intro hax
    exact ha (Finset.erase_subset x h hax)

private lemma mem_edges_upper_iff (H : Finset (Finset α)) (a : α)
    (h : Finset α) (x : α) :
    (h, x) ∈ edges (H.memberSubfamily a) ↔
      (insert a h, x) ∈ edges H ∧ a ∉ h ∧ x ≠ a := by
  simp only [mem_edges, Finset.mem_memberSubfamily]
  constructor
  · rintro ⟨⟨hh, ha⟩, hx, ⟨hl, -⟩⟩
    have hxa : x ≠ a := by rintro rfl; exact ha hx
    have hax : a ≠ x := Ne.symm hxa
    have herase : (insert a h).erase x = insert a (h.erase x) :=
      Finset.erase_insert_of_ne hax
    exact ⟨⟨hh, Finset.mem_insert_of_mem hx, herase ▸ hl⟩, ha, hxa⟩
  · rintro ⟨⟨hh, hx, hl⟩, ha, hxa⟩
    have hx' : x ∈ h := (Finset.mem_insert.mp hx).resolve_left hxa
    have hax : a ≠ x := Ne.symm hxa
    have herase : (insert a h).erase x = insert a (h.erase x) :=
      Finset.erase_insert_of_ne hax
    refine ⟨⟨hh, ha⟩, hx', ⟨?_, ?_⟩⟩
    · simpa only [herase] using hl
    · intro haer
      exact ha (Finset.erase_subset x h haer)

private lemma mem_edges_bridge_iff (H : Finset (Finset α)) (a : α)
    (h : Finset α) :
    h ∈ doubleFiber H a ↔ (insert a h, a) ∈ edges H ∧ a ∉ h := by
  simp only [doubleFiber, Finset.mem_inter, Finset.mem_nonMemberSubfamily,
    Finset.mem_memberSubfamily, mem_edges]
  constructor
  · rintro ⟨⟨hh, ha⟩, ⟨hupper, -⟩⟩
    simp only [Finset.mem_insert_self, true_and]
    exact ⟨⟨hupper, by simpa [Finset.erase_insert ha] using hh⟩, ha⟩
  · rintro ⟨⟨hupper, -, hlower⟩, ha⟩
    exact ⟨⟨by simpa [Finset.erase_insert ha] using hlower, ha⟩, ⟨hupper, ha⟩⟩

private def upperLift (a : α) (e : Finset α × α) : Finset α × α :=
  (insert a e.1, e.2)

private def bridgeLift (a : α) (h : Finset α) : Finset α × α :=
  (insert a h, a)

private lemma edges_split (H : Finset (Finset α)) (a : α) :
    edges H = edges (H.nonMemberSubfamily a) ∪
      ((edges (H.memberSubfamily a)).image (upperLift a) ∪
        (doubleFiber H a).image (bridgeLift a)) := by
  ext e
  rcases e with ⟨h, x⟩
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · intro he
    by_cases hah : a ∈ h
    · let u := h.erase a
      have hua : a ∉ u := by simp [u]
      have heq : insert a u = h := Finset.insert_erase hah
      by_cases hxa : x = a
      · subst x
        right; right
        refine ⟨u, ?_, ?_⟩
        · apply (mem_edges_bridge_iff H a u).mpr
          exact ⟨by simpa [heq] using he, hua⟩
        · simp [bridgeLift, heq]
      · right; left
        refine ⟨(u, x), ?_, ?_⟩
        · apply (mem_edges_upper_iff H a u x).mpr
          exact ⟨by simpa [heq] using he, hua, hxa⟩
        · simp [upperLift, heq]
    · left
      exact (mem_edges_lower_iff H a h x).mpr ⟨he, hah⟩
  · rintro (he | he | he)
    · exact (mem_edges_lower_iff H a h x).mp he |>.1
    · rcases he with ⟨⟨u, y⟩, hu, heq⟩
      simp only [upperLift, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact (mem_edges_upper_iff H a u y).mp hu |>.1
    · rcases he with ⟨u, hu, heq⟩
      simp only [bridgeLift, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact (mem_edges_bridge_iff H a u).mp hu |>.1

private lemma upperLift_injOn (H : Finset (Finset α)) (a : α) :
    Set.InjOn (upperLift a) (edges (H.memberSubfamily a) : Set (Finset α × α)) := by
  rintro ⟨h, x⟩ hh ⟨k, y⟩ hk heq
  have ha_h : a ∉ h := (Finset.mem_memberSubfamily.mp (mem_edges.mp hh).1).2
  have ha_k : a ∉ k := (Finset.mem_memberSubfamily.mp (mem_edges.mp hk).1).2
  have heq_fst : insert a h = insert a k := congrArg Prod.fst heq
  have heq_snd : x = y := congrArg Prod.snd heq
  have heq_h : h = k := by
    calc
      h = (insert a h).erase a := (Finset.erase_insert ha_h).symm
      _ = (insert a k).erase a := congrArg (fun s : Finset α => s.erase a) heq_fst
      _ = k := Finset.erase_insert ha_k
  cases heq_h
  cases heq_snd
  rfl

private lemma bridgeLift_injOn (H : Finset (Finset α)) (a : α) :
    Set.InjOn (bridgeLift a) (doubleFiber H a : Set (Finset α)) := by
  intro h hh k hk heq
  have ha_h : a ∉ h := (mem_edges_bridge_iff H a h).mp hh |>.2
  have ha_k : a ∉ k := (mem_edges_bridge_iff H a k).mp hk |>.2
  have heq_fst : insert a h = insert a k := congrArg Prod.fst heq
  calc
    h = (insert a h).erase a := (Finset.erase_insert ha_h).symm
    _ = (insert a k).erase a := congrArg (fun s : Finset α => s.erase a) heq_fst
    _ = k := Finset.erase_insert ha_k

private lemma lower_disjoint_upper (H : Finset (Finset α)) (a : α) :
    Disjoint (edges (H.nonMemberSubfamily a))
      ((edges (H.memberSubfamily a)).image (upperLift a)) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨h, x⟩ hlow hup
  have ha : a ∉ h := (mem_edges_lower_iff H a h x).mp hlow |>.2
  obtain ⟨⟨u, y⟩, -, heq⟩ := Finset.mem_image.mp hup
  have hhu : insert a u = h := congrArg Prod.fst heq
  exact ha (hhu ▸ Finset.mem_insert_self a u)

private lemma lower_disjoint_bridge (H : Finset (Finset α)) (a : α) :
    Disjoint (edges (H.nonMemberSubfamily a))
      ((doubleFiber H a).image (bridgeLift a)) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨h, x⟩ hlow hbridge
  have ha : a ∉ h := (mem_edges_lower_iff H a h x).mp hlow |>.2
  obtain ⟨u, -, heq⟩ := Finset.mem_image.mp hbridge
  have hhu : insert a u = h := congrArg Prod.fst heq
  exact ha (hhu ▸ Finset.mem_insert_self a u)

private lemma upper_disjoint_bridge (H : Finset (Finset α)) (a : α) :
    Disjoint ((edges (H.memberSubfamily a)).image (upperLift a))
      ((doubleFiber H a).image (bridgeLift a)) := by
  apply Finset.disjoint_left.mpr
  intro e hup hbridge
  obtain ⟨⟨u, x⟩, hu, heq⟩ := Finset.mem_image.mp hup
  obtain ⟨v, -, heq'⟩ := Finset.mem_image.mp hbridge
  have hxa : x ≠ a := (mem_edges_upper_iff H a u x).mp hu |>.2.2
  have hx : x = a := by
    calc
      x = (upperLift a (u, x)).2 := rfl
      _ = e.2 := congrArg Prod.snd heq
      _ = (bridgeLift a v).2 := (congrArg Prod.snd heq').symm
      _ = a := rfl
  exact hxa hx

/-- Splitting one coordinate yields two induced one-inclusion graphs and one
crossing edge for each pattern present in both fibers. -/
lemma edgeCount_split (H : Finset (Finset α)) (a : α) :
    edgeCount H = edgeCount (H.nonMemberSubfamily a) +
      edgeCount (H.memberSubfamily a) + (doubleFiber H a).card := by
  have hdisj : Disjoint (edges (H.nonMemberSubfamily a))
      ((edges (H.memberSubfamily a)).image (upperLift a) ∪
        (doubleFiber H a).image (bridgeLift a)) := by
    rw [Finset.disjoint_union_right]
    exact ⟨lower_disjoint_upper H a, lower_disjoint_bridge H a⟩
  unfold edgeCount
  rw [edges_split H a, Finset.card_union_of_disjoint hdisj,
    Finset.card_union_of_disjoint (upper_disjoint_bridge H a),
    Finset.card_image_of_injOn (upperLift_injOn H a),
    Finset.card_image_of_injOn (bridgeLift_injOn H a)]
  omega

private lemma edgeCount_le_vcDim_mul_card_on_ground
    (S : Finset α) (H : Finset (Finset α))
    (hground : ∀ h ∈ H, h ⊆ S) :
    edgeCount H ≤ H.vcDim * H.card := by
  induction S using Finset.induction generalizing H with
  | empty =>
    have hzero : edges H = ∅ := by
      apply Finset.ext
      rintro ⟨h, a⟩
      constructor
      · intro he
        obtain ⟨hh, ha, _⟩ := mem_edges.mp he
        have contra : a ∈ (∅ : Finset α) := hground h hh ha
        simp at contra
      · intro he
        simp at he
    simp [edgeCount, hzero]
  | @insert a S ha ih =>
    let H₀ := H.nonMemberSubfamily a
    let H₁ := H.memberSubfamily a
    let C := H₀ ∪ H₁
    let D := H₀ ∩ H₁
    have hCground : ∀ h ∈ C, h ⊆ S := by
      intro u hu x hx
      have hu' : u ∈ projection H a := by
        rwa [projection_eq_union]
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu'
      have hx' : x ∈ h := Finset.mem_of_mem_erase hx
      have hxin := hground h hh hx'
      rcases Finset.mem_insert.mp hxin with rfl | hxs
      · exact False.elim ((Finset.ne_of_mem_erase hx) rfl)
      · exact hxs
    have hDground : ∀ h ∈ D, h ⊆ S := by
      intro h hh
      exact hCground h (Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mp hh).1))
    have ihC : edgeCount C ≤ C.vcDim * C.card := ih C hCground
    have ihD : edgeCount D ≤ D.vcDim * D.card := ih D hDground
    have hvcC : C.vcDim ≤ H.vcDim := by
      have heq : C = projection H a := (projection_eq_union H a).symm
      rw [heq]
      exact vcDim_projection_le H a
    have hDterm : edgeCount D + D.card ≤ H.vcDim * D.card := by
      by_cases hDempty : D = ∅
      · simp [hDempty, edgeCount, edges]
      · have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hDempty
        have hvcD : D.vcDim + 1 ≤ H.vcDim :=
          vcDim_doubleFiber_succ_le H a (by simpa [D, doubleFiber] using hDne)
        have hmul := Nat.mul_le_mul_right D.card hvcD
        nlinarith
    have hsuper : edgeCount H₀ + edgeCount H₁ ≤ edgeCount C + edgeCount D :=
      edgeCount_supermodular H₀ H₁
    have hcards : C.card + D.card = H.card := by
      calc
        C.card + D.card = H₀.card + H₁.card := Finset.card_union_add_card_inter H₀ H₁
        _ = H.card := by
          dsimp [H₀, H₁]
          rw [add_comm]
          exact Finset.card_memberSubfamily_add_card_nonMemberSubfamily a H
    have hsplit : edgeCount H = edgeCount H₀ + edgeCount H₁ + D.card := by
      simpa [H₀, H₁, D, doubleFiber] using edgeCount_split H a
    have hCterm : edgeCount C ≤ H.vcDim * C.card :=
      ihC.trans (Nat.mul_le_mul_right _ hvcC)
    calc
      edgeCount H = edgeCount H₀ + edgeCount H₁ + D.card := hsplit
      _ ≤ edgeCount C + edgeCount D + D.card := Nat.add_le_add_right hsuper _
      _ ≤ H.vcDim * C.card + H.vcDim * D.card := by omega
      _ = H.vcDim * H.card := by rw [← Nat.mul_add, hcards]

/-- Every finite one-inclusion graph has at most `VCdim × vertices` edges. -/
lemma edgeCount_le_vcDim_mul_card (H : Finset (Finset α)) :
    edgeCount H ≤ H.vcDim * H.card := by
  let S := H.biUnion id
  have hground : ∀ h ∈ H, h ⊆ S := by
    intro h hh x hx
    exact Finset.mem_biUnion.mpr ⟨h, hh, hx⟩
  exact edgeCount_le_vcDim_mul_card_on_ground S H hground

/-- The same density bound holds in every vertex-induced subgraph of a
family of VC dimension at most `d`. -/
lemma edgeCount_hereditary_bound (H K : Finset (Finset α)) (d : ℕ)
    (hKH : K ⊆ H) (hvc : H.vcDim ≤ d) :
    edgeCount K ≤ d * K.card := by
  exact (edgeCount_le_vcDim_mul_card K).trans
    ((Nat.mul_le_mul_right K.card) ((Finset.vcDim_mono hKH).trans hvc))

private lemma sum_range_indicator (M n : ℕ) (hn : n ≤ M) :
    (∑ t ∈ Finset.range M, if t < n then 1 else 0) = n := by
  have hfilter : (Finset.range M).filter (fun t => t < n) = Finset.range n := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  simp

/-- A hereditary edge-density bound controls the sum of the smaller
endpoint weights, with no orientation choice. -/
lemma weighted_min_bound_of_hereditary {V EType : Type*} [DecidableEq V]
    (vertices : Finset V) (E : Finset EType) (source target : EType → V)
    (w : V → ℕ) (d : ℕ)
    (hend : ∀ e ∈ E, source e ∈ vertices ∧ target e ∈ vertices)
    (hdensity : ∀ K ⊆ vertices,
      (E.filter fun e => source e ∈ K ∧ target e ∈ K).card ≤ d * K.card) :
    (∑ e ∈ E, min (w (source e)) (w (target e))) ≤
      d * ∑ v ∈ vertices, w v := by
  let M := vertices.sup w
  have hw (v : V) (hv : v ∈ vertices) : w v ≤ M := Finset.le_sup hv
  have hleft : (∑ e ∈ E, min (w (source e)) (w (target e))) =
      ∑ t ∈ Finset.range M,
        (E.filter fun e => t < w (source e) ∧ t < w (target e)).card := by
    calc
      (∑ e ∈ E, min (w (source e)) (w (target e))) =
          ∑ e ∈ E, ∑ t ∈ Finset.range M,
            if t < w (source e) ∧ t < w (target e) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        have hmin : min (w (source e)) (w (target e)) ≤ M :=
          (Nat.min_le_left _ _).trans (hw (source e) (hend e he).1)
        simpa [lt_min_iff] using
          (sum_range_indicator M (min (w (source e)) (w (target e))) hmin).symm
      _ = ∑ t ∈ Finset.range M, ∑ e ∈ E,
          if t < w (source e) ∧ t < w (target e) then 1 else 0 := Finset.sum_comm
      _ = ∑ t ∈ Finset.range M,
          (E.filter fun e => t < w (source e) ∧ t < w (target e)).card := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [← Finset.sum_filter]
        simp
  have hright : (∑ t ∈ Finset.range M,
      (vertices.filter fun v => t < w v).card) = ∑ v ∈ vertices, w v := by
    calc
      (∑ t ∈ Finset.range M, (vertices.filter fun v => t < w v).card) =
          ∑ t ∈ Finset.range M, ∑ v ∈ vertices, if t < w v then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [← Finset.sum_filter]
        simp
      _ = ∑ v ∈ vertices, ∑ t ∈ Finset.range M,
          if t < w v then 1 else 0 := Finset.sum_comm
      _ = ∑ v ∈ vertices, w v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact sum_range_indicator M (w v) (hw v hv)
  rw [hleft, ← hright, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  let K := vertices.filter (fun v => t < w v)
  have hK : K ⊆ vertices := Finset.filter_subset _ _
  have hfilter : (E.filter fun e => t < w (source e) ∧ t < w (target e)) =
      E.filter (fun e => source e ∈ K ∧ target e ∈ K) := by
    ext e
    by_cases he : e ∈ E
    · have ⟨he1, he2⟩ := hend e he
      simp [K, he, he1, he2]
    · simp [he]
  rw [hfilter]
  exact hdensity K hK

/-- The weighted one-inclusion charging inequality follows from hereditary
edge density by summing over weight levels. -/
lemma weighted_oneInclusion_bound (H : Finset (Finset α)) (w : Finset α → ℕ)
    (d : ℕ) (hvc : H.vcDim ≤ d) :
    (∑ e ∈ edges H, min (w e.1) (w (e.1.erase e.2))) ≤
      d * ∑ h ∈ H, w h := by
  apply weighted_min_bound_of_hereditary H (edges H) Prod.fst
    (fun e => e.1.erase e.2) w d
  · intro e he
    rcases e with ⟨h, a⟩
    obtain ⟨hh, _, hl⟩ := mem_edges.mp he
    exact ⟨hh, hl⟩
  · intro K hKH
    have hfilter : (edges H).filter
        (fun e => e.1 ∈ K ∧ e.1.erase e.2 ∈ K) = edges K := by
      ext e
      rcases e with ⟨h, a⟩
      simp only [Finset.mem_filter, mem_edges]
      constructor
      · rintro ⟨⟨-, ha, -⟩, hh, hl⟩
        exact ⟨hh, ha, hl⟩
      · rintro ⟨hh, ha, hl⟩
        exact ⟨⟨hKH hh, ha, hKH hl⟩, hh, hl⟩
    rw [hfilter]
    exact edgeCount_hereditary_bound H K d hKH hvc

lemma twice_weighted_oneInclusion_bound (H : Finset (Finset α))
    (w : Finset α → ℕ) (d : ℕ) (hvc : H.vcDim ≤ d) :
    (∑ e ∈ edges H, 2 * min (w e.1) (w (e.1.erase e.2))) ≤
      2 * d * ∑ h ∈ H, w h := by
  calc
    (∑ e ∈ edges H, 2 * min (w e.1) (w (e.1.erase e.2))) =
        2 * ∑ e ∈ edges H, min (w e.1) (w (e.1.erase e.2)) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (d * ∑ h ∈ H, w h) :=
      Nat.mul_le_mul_left 2 (weighted_oneInclusion_bound H w d hvc)
    _ = 2 * d * ∑ h ∈ H, w h := by ring

end Lax457868Proofs.SamplerOneInclusion
