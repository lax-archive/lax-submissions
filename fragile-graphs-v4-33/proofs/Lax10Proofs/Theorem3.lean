import Lax10Proofs.Coloring
import Lax10Proofs.Connectivity

/-!
# Proof pieces for Theorem 3

This file contains the local proof components for the induction proving
Theorem 3.  The first component proves the 3-connected branch of the paper's
argument: if the graph is already $(m - 1)$-colorable, the unused color gives
C1--C4.
-/

namespace Lax10Proofs

universe u

namespace Theorem3

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
private lemma singleton_independent {x : V} :
    ∀ ⦃a b : V⦄, a ∈ ({x} : Finset V) → b ∈ ({x} : Finset V) → ¬ G.Adj a b := by
  intro a b ha hb
  simp only [Finset.mem_singleton] at ha hb
  rintro hab
  subst a
  subst b
  exact G.irrefl hab

private lemma pair_independent {x y : V} (hn : ¬ G.Adj x y) :
    ∀ ⦃a b : V⦄, a ∈ ({x, y} : Finset V) → b ∈ ({x, y} : Finset V) →
      ¬ G.Adj a b := by
  intro a b ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rintro hab
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact G.irrefl hab
  · exact hn hab
  · exact hn hab.symm
  · exact G.irrefl hab

private lemma image_pair_xy {m : Nat} (hm : 0 < m) (c : KColoring (m - 1) G)
    {x y z : V} (hxz : x ≠ z) (hyz : y ≠ z)
    (hindep : ∀ ⦃a b : V⦄, a ∈ ({x, y} : Finset V) → b ∈ ({x, y} : Finset V) →
      ¬ G.Adj a b) :
    (({x, y, z} : Finset V).image
      (KColoring.recolorIndependent hm c ({x, y} : Finset V) hindep).color).card = 2 := by
  classical
  let d := KColoring.recolorIndependent hm c ({x, y} : Finset V) hindep
  have hne : freshColor hm ≠ embedOldColor hm (c.color z) :=
    (embedOldColor_ne_fresh hm (c.color z)).symm
  change (Finset.image d.color ({x, y, z} : Finset V)).card = 2
  simp [d, KColoring.recolorIndependent, hxz.symm, hyz.symm, hne]

private lemma image_pair_xz {m : Nat} (hm : 0 < m) (c : KColoring (m - 1) G)
    {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z)
    (hindep : ∀ ⦃a b : V⦄, a ∈ ({x, z} : Finset V) → b ∈ ({x, z} : Finset V) →
      ¬ G.Adj a b) :
    (({x, y, z} : Finset V).image
      (KColoring.recolorIndependent hm c ({x, z} : Finset V) hindep).color).card = 2 := by
  classical
  let d := KColoring.recolorIndependent hm c ({x, z} : Finset V) hindep
  have hne : freshColor hm ≠ embedOldColor hm (c.color y) :=
    (embedOldColor_ne_fresh hm (c.color y)).symm
  change (Finset.image d.color ({x, y, z} : Finset V)).card = 2
  simp [d, KColoring.recolorIndependent, hxy.symm, hyz, hne]

private lemma image_pair_yz {m : Nat} (hm : 0 < m) (c : KColoring (m - 1) G)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hindep : ∀ ⦃a b : V⦄, a ∈ ({y, z} : Finset V) → b ∈ ({y, z} : Finset V) →
      ¬ G.Adj a b) :
    (({x, y, z} : Finset V).image
      (KColoring.recolorIndependent hm c ({y, z} : Finset V) hindep).color).card = 2 := by
  classical
  let d := KColoring.recolorIndependent hm c ({y, z} : Finset V) hindep
  change (Finset.image d.color ({x, y, z} : Finset V)).card = 2
  simp [d, KColoring.recolorIndependent, hxy, hxz]

private theorem exists_perm_map_one {m : Nat} (a b : Fin m) :
    ∃ σ : Equiv.Perm (Fin m), σ a = b := by
  exact ⟨Equiv.swap a b, Equiv.swap_apply_left a b⟩

private theorem exists_perm_map_pair {m : Nat} {a₁ a₂ b₁ b₂ : Fin m}
    (hpat : (a₁ = a₂ ↔ b₁ = b₂)) :
    ∃ σ : Equiv.Perm (Fin m), σ a₁ = b₁ ∧ σ a₂ = b₂ := by
  classical
  by_cases ha : a₁ = a₂
  · have hb : b₁ = b₂ := hpat.mp ha
    subst a₂
    subst b₂
    exact ⟨Equiv.swap a₁ b₁, Equiv.swap_apply_left a₁ b₁, Equiv.swap_apply_left a₁ b₁⟩
  · have hb : b₁ ≠ b₂ := by
      intro h
      exact ha (hpat.mpr h)
    let τ : Equiv.Perm (Fin m) := Equiv.swap a₁ b₁
    let t : Fin m := τ a₂
    have ht_ne_b1 : t ≠ b₁ := by
      intro ht
      have h : τ a₂ = τ a₁ := by
        simpa [τ, t, Equiv.swap_apply_left] using ht
      exact ha (τ.injective h.symm)
    have hfix_b1 : (Equiv.swap t b₂) b₁ = b₁ :=
      Equiv.swap_apply_of_ne_of_ne ht_ne_b1.symm hb
    let σ : Equiv.Perm (Fin m) := τ.trans (Equiv.swap t b₂)
    refine ⟨σ, ?_, ?_⟩
    · simp [σ, τ, t, Equiv.swap_apply_left, hfix_b1]
    · simp [σ, τ, t, Equiv.swap_apply_left]

private theorem exists_perm_agree_on_finset {m : Nat} {S : Finset V}
    (hS : S.card ≤ 2) (a b : V → Fin m)
    (hpat : ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → (b x = b y ↔ a x = a y)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ ⦃x : V⦄, x ∈ S → σ (b x) = a x := by
  classical
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · refine ⟨Equiv.refl (Fin m), ?_⟩
    intro x hx
    have : S = ∅ := Finset.card_eq_zero.mp h0
    simp [this] at hx
  · rcases Finset.card_eq_one.mp h1 with ⟨u, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_perm_map_one (b u) (a u)
    refine ⟨σ, ?_⟩
    intro x hx
    simp at hx
    subst x
    exact hσ
  · rcases Finset.card_eq_two.mp h2 with ⟨u, v, _huv, rfl⟩
    have hpat_uv : b u = b v ↔ a u = a v := hpat (by simp) (by simp)
    obtain ⟨σ, hσu, hσv⟩ := exists_perm_map_pair hpat_uv
    refine ⟨σ, ?_⟩
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hσu
    · exact hσv

private noncomputable def imageEquivOfSamePattern {α : Type*} [DecidableEq α]
    {S : Finset V} (a b : V → α)
    (hpat : ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → (b x = b y ↔ a x = a y)) :
    {c // c ∈ S.image b} ≃ {c // c ∈ S.image a} := by
  classical
  let preB (c : {c // c ∈ S.image b}) : V :=
    Classical.choose (Finset.mem_image.mp c.2)
  have preB_mem (c : {c // c ∈ S.image b}) : preB c ∈ S :=
    (Classical.choose_spec (Finset.mem_image.mp c.2)).1
  have preB_eq (c : {c // c ∈ S.image b}) : b (preB c) = c.1 :=
    (Classical.choose_spec (Finset.mem_image.mp c.2)).2
  let f : {c // c ∈ S.image b} → {c // c ∈ S.image a} := fun c =>
    ⟨a (preB c), Finset.mem_image.mpr ⟨preB c, preB_mem c, rfl⟩⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro c d hcd
    apply Subtype.ext
    have haeq : a (preB c) = a (preB d) := by
      simpa [f] using congrArg Subtype.val hcd
    have hbeq : b (preB c) = b (preB d) :=
      (hpat (preB_mem c) (preB_mem d)).mpr haeq
    exact (preB_eq c).symm.trans (hbeq.trans (preB_eq d))
  · intro d
    rcases Finset.mem_image.mp d.2 with ⟨x, hxS, hax⟩
    refine ⟨⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    dsimp [f]
    have hbpre : b (preB ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩) = b x :=
      preB_eq ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩
    have hapre : a (preB ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩) = a x :=
      (hpat (preB_mem ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩) hxS).mp hbpre
    exact hapre.trans hax

omit [DecidableEq V] in
private theorem imageEquivOfSamePattern_apply {α : Type*} [DecidableEq α]
    {S : Finset V} (a b : V → α)
    (hpat : ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → (b x = b y ↔ a x = a y))
    {x : V} (hxS : x ∈ S) :
    imageEquivOfSamePattern a b hpat ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩ =
      ⟨a x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩ := by
  classical
  apply Subtype.ext
  dsimp [imageEquivOfSamePattern]
  let preB (c : {c // c ∈ S.image b}) : V :=
    Classical.choose (Finset.mem_image.mp c.2)
  have preB_mem (c : {c // c ∈ S.image b}) : preB c ∈ S :=
    (Classical.choose_spec (Finset.mem_image.mp c.2)).1
  have preB_eq (c : {c // c ∈ S.image b}) : b (preB c) = c.1 :=
    (Classical.choose_spec (Finset.mem_image.mp c.2)).2
  have hbpre : b (preB ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩) = b x :=
    preB_eq ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩
  exact (hpat (preB_mem ⟨b x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩) hxS).mp hbpre

private noncomputable def extendPatternPerm {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Finset α} (e : {c // c ∈ s} ≃ {c // c ∈ t}) : Equiv.Perm α := by
  classical
  have hcard_sub : Fintype.card {c // c ∈ s} = Fintype.card {c // c ∈ t} :=
    Fintype.card_congr e
  have hcard_compl : Fintype.card {c // ¬ c ∈ s} = Fintype.card {c // ¬ c ∈ t} := by
    rw [Fintype.card_subtype_compl (fun c => c ∈ s),
      Fintype.card_subtype_compl (fun c => c ∈ t), hcard_sub]
  let ec : {c // ¬ c ∈ s} ≃ {c // ¬ c ∈ t} := Fintype.equivOfCardEq hcard_compl
  refine ⟨?toFun, ?invFun, ?left, ?right⟩
  · intro x
    exact if hx : x ∈ s then (e ⟨x, hx⟩).1 else (ec ⟨x, hx⟩).1
  · intro y
    exact if hy : y ∈ t then (e.symm ⟨y, hy⟩).1 else (ec.symm ⟨y, hy⟩).1
  · intro x
    by_cases hx : x ∈ s
    · have ht : (e ⟨x, hx⟩).1 ∈ t := (e ⟨x, hx⟩).2
      simp [hx, ht]
    · have ht : ¬ (ec ⟨x, hx⟩).1 ∈ t := (ec ⟨x, hx⟩).2
      simp [hx, ht]
  · intro y
    by_cases hy : y ∈ t
    · have hs : (e.symm ⟨y, hy⟩).1 ∈ s := (e.symm ⟨y, hy⟩).2
      simp [hy, hs]
    · have hs : ¬ (ec.symm ⟨y, hy⟩).1 ∈ s := (ec.symm ⟨y, hy⟩).2
      simp [hy, hs]

omit [DecidableEq V] in
private theorem exists_perm_agree_general {α : Type*} [Fintype α] [DecidableEq α]
    {S : Finset V} (a b : V → α)
    (hpat : ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → (b x = b y ↔ a x = a y)) :
    ∃ σ : Equiv.Perm α, ∀ ⦃x : V⦄, x ∈ S → σ (b x) = a x := by
  classical
  let e := imageEquivOfSamePattern a b hpat
  let σ := extendPatternPerm e
  refine ⟨σ, ?_⟩
  intro x hxS
  let hbmem : b x ∈ S.image b := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
  have hval : (e ⟨b x, hbmem⟩).1 = a x := congrArg Subtype.val
    (imageEquivOfSamePattern_apply a b hpat hxS)
  have hsigma : σ (b x) = (e ⟨b x, hbmem⟩).1 := by
    dsimp [σ, extendPatternPerm]
    rw [dif_pos hbmem]
  exact hsigma.trans hval

private def tri {α : Type*} (a b c : α) : Fin 3 → α
  | 0 => a
  | 1 => b
  | 2 => c

private theorem exists_perm_map_triple {m : Nat}
    {a₁ a₂ a₃ b₁ b₂ b₃ : Fin m}
    (h12 : (a₁ = a₂ ↔ b₁ = b₂))
    (h13 : (a₁ = a₃ ↔ b₁ = b₃))
    (h23 : (a₂ = a₃ ↔ b₂ = b₃)) :
    ∃ σ : Equiv.Perm (Fin m), σ a₁ = b₁ ∧ σ a₂ = b₂ ∧ σ a₃ = b₃ := by
  classical
  let source : Fin 3 → Fin m := tri a₁ a₂ a₃
  let target : Fin 3 → Fin m := tri b₁ b₂ b₃
  have hpat :
      ∀ ⦃x y : Fin 3⦄, x ∈ (Finset.univ : Finset (Fin 3)) →
        y ∈ (Finset.univ : Finset (Fin 3)) →
        (source x = source y ↔ target x = target y) := by
    intro x y _ _
    fin_cases x <;> fin_cases y <;> simp [source, target, tri, h12, h13, h23, eq_comm]
  obtain ⟨σ, hσ⟩ := exists_perm_agree_general target source hpat
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact hσ (x := (0 : Fin 3)) (by simp)
  · exact hσ (x := (1 : Fin 3)) (by simp)
  · exact hσ (x := (2 : Fin 3)) (by simp)

private theorem exists_fin_not_mem_of_card_lt {m : Nat} (s : Finset (Fin m))
    (hcard : s.card < m) :
    ∃ a : Fin m, a ∉ s := by
  classical
  obtain ⟨a, _ha_univ, ha⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := s) (t := (Finset.univ : Finset (Fin m))) (by
        simpa [Fintype.card_fin] using hcard)
  exact ⟨a, ha⟩

private theorem exists_perm_avoid_on_finset {m : Nat} (s : Finset (Fin m)) (p : Fin m)
    (hcard : s.card < m) :
    ∃ σ : Equiv.Perm (Fin m), ∀ ⦃q : Fin m⦄, q ∈ s → σ q ≠ p := by
  classical
  obtain ⟨w, hw⟩ := exists_fin_not_mem_of_card_lt s hcard
  let σ : Equiv.Perm (Fin m) := Equiv.swap p w
  refine ⟨σ, ?_⟩
  intro q hq hσ
  by_cases hqw : q = w
  · exact hw (hqw ▸ hq)
  · by_cases hqp : q = p
    · have hpw : p ≠ w := by
        intro hpw
        exact hqw (hqp.trans hpw)
      simp [σ, Equiv.swap_apply_left, hqp] at hσ
      exact hpw hσ.symm
    · have hfix : σ q = q := Equiv.swap_apply_of_ne_of_ne hqp hqw
      exact hqp (hfix.symm.trans hσ)

omit [DecidableEq V] in
private theorem exists_relabel_pair_avoid_on_finset {m : Nat}
    (T : Finset V) (f : V → Fin m) {u v y z : V}
    (huT : u ∈ T) (hvT : v ∈ T) (hyT : y ∈ T) (hzT : z ∈ T)
    {p su sv tu tv : Fin m}
    (hfu : f u = su) (hfv : f v = sv)
    (hp_tu : p ≠ tu) (hp_tv : p ≠ tv)
    (hpat : (su = sv ↔ tu = tv))
    (hcard : (T.image f).card < m) :
    ∃ σ : Equiv.Perm (Fin m), σ su = tu ∧ σ sv = tv ∧ σ (f y) ≠ p ∧ σ (f z) ≠ p := by
  classical
  obtain ⟨σ0, hσu, hσv⟩ := exists_perm_map_pair hpat
  let img0 : Finset (Fin m) := T.image (fun t => σ0 (f t))
  have hcard0 : img0.card < m := by
    have himg : img0 = (T.image f).image σ0 := by
      ext a
      simp [img0]
    rw [himg, Finset.card_image_of_injective _ σ0.injective]
    exact hcard
  obtain ⟨w, hw⟩ := exists_fin_not_mem_of_card_lt img0 hcard0
  let τ : Equiv.Perm (Fin m) := Equiv.swap p w
  let σ : Equiv.Perm (Fin m) := σ0.trans τ
  have htu_mem : tu ∈ img0 := by
    refine Finset.mem_image.mpr ⟨u, huT, ?_⟩
    simp [hfu, hσu]
  have htv_mem : tv ∈ img0 := by
    refine Finset.mem_image.mpr ⟨v, hvT, ?_⟩
    simp [hfv, hσv]
  have hw_ne_tu : w ≠ tu := by
    intro h
    exact hw (h ▸ htu_mem)
  have hw_ne_tv : w ≠ tv := by
    intro h
    exact hw (h ▸ htv_mem)
  have tau_tu : τ tu = tu := by
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hp_tu.symm
    · exact hw_ne_tu.symm
  have tau_tv : τ tv = tv := by
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hp_tv.symm
    · exact hw_ne_tv.symm
  have avoid_of_mem : ∀ {q : Fin m}, q ∈ img0 → τ q ≠ p := by
    intro q hq hτ
    by_cases hqw : q = w
    · exact hw (hqw ▸ hq)
    · by_cases hqp : q = p
      · have hpw : p ≠ w := by
          intro hpw
          exact hqw (hqp.trans hpw)
        simp [τ, Equiv.swap_apply_left, hqp] at hτ
        exact hpw hτ.symm
      · have hfix : τ q = q := Equiv.swap_apply_of_ne_of_ne hqp hqw
        exact hqp (hfix.symm.trans hτ)
  have hy_mem : σ0 (f y) ∈ img0 := Finset.mem_image.mpr ⟨y, hyT, rfl⟩
  have hz_mem : σ0 (f z) ∈ img0 := Finset.mem_image.mpr ⟨z, hzT, rfl⟩
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · simp [σ, τ, hσu, tau_tu]
  · simp [σ, τ, hσv, tau_tv]
  · exact avoid_of_mem hy_mem
  · exact avoid_of_mem hz_mem

private theorem no_clique4_of_mfragile_four [Fintype V]
    (hfrag : MFragile 4 G) {s : Finset V} (hcard : s.card = 4)
    (hclique : ∀ ⦃a b : V⦄, a ∈ s → b ∈ s → a ≠ b → G.Adj a b) : False := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce (s : Set V)
  have hverts : H.verts = (s : Set V) := by
    simp [H, SimpleGraph.Subgraph.induce_verts]
  have hcardH : Fintype.card H.verts = 4 := by
    rw [hverts]
    convert hcard using 1
    symm
    simp
  have hcomplete : ∀ a b : H.verts, a ≠ b → H.coe.Adj a b := by
    intro a b hab
    rw [SimpleGraph.Subgraph.coe_adj]
    simp [H, SimpleGraph.Subgraph.induce_adj]
    have ha : a.1 ∈ s := by
      change a.1 ∈ (s : Set V)
      rw [← hverts]
      exact a.2
    have hb : b.1 ∈ s := by
      change b.1 ∈ (s : Set V)
      rw [← hverts]
      exact b.2
    have hne : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    exact hclique ha hb hne
  have hthree : ThreeConnected H.coe := by
    constructor
    · rw [Nat.card_eq_fintype_card]
      exact hcardH.ge
    · intro S _hS hsep
      rcases hsep with ⟨x, y, hnot⟩
      apply hnot
      by_cases hxy : x.1 = y.1
      · have hxy' : x = y := Subtype.ext hxy
        subst y
        exact SimpleGraph.Reachable.rfl
      · exact SimpleGraph.Adj.reachable
          (show (deleteVertices H.coe S).Adj x y from hcomplete x.1 y.1 hxy)
  have hnot3 : ¬ KColorable 3 H.coe := by
    rintro ⟨c⟩
    have hinj : Function.Injective c.color := by
      intro a b hab
      by_contra hne
      exact c.valid (hcomplete a b hne) hab
    have hle := Fintype.card_le_of_injective c.color hinj
    rw [hcardH, Fintype.card_fin] at hle
    omega
  exact hnot3 (hfrag H hthree)

omit [DecidableEq V] in
private theorem card_image_lt_of_pair_eq {β : Type*} [DecidableEq β]
    (T : Finset V) (f : V → β) {a b : V}
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) (hfab : f a = f b) :
    (T.image f).card < T.card := by
  have hle : (T.image f).card ≤ T.card := Finset.card_image_le
  have hne : (T.image f).card ≠ T.card := by
    intro hcard
    have hinj : Set.InjOn f (T : Set V) := Finset.card_image_iff.mp hcard
    exact hab (hinj ha hb hfab)
  omega

private theorem card_pair_le_two (a b : V) :
    ({a, b} : Finset V).card ≤ 2 := by
  calc
    ({a, b} : Finset V).card ≤ ({b} : Finset V).card + 1 :=
      Finset.card_insert_le a ({b} : Finset V)
    _ = 2 := by simp

private theorem card_triple_le_three (a b c : V) :
    ({a, b, c} : Finset V).card ≤ 3 := by
  calc
    ({a, b, c} : Finset V).card ≤ ({b, c} : Finset V).card + 1 :=
      Finset.card_insert_le a ({b, c} : Finset V)
    _ ≤ 2 + 1 := Nat.add_le_add_right (card_pair_le_two b c) 1
    _ = 3 := by omega

private theorem card_quad_le_four (a b c d : V) :
    ({a, b, c, d} : Finset V).card ≤ 4 := by
  calc
    ({a, b, c, d} : Finset V).card ≤ ({b, c, d} : Finset V).card + 1 :=
      Finset.card_insert_le a ({b, c, d} : Finset V)
    _ ≤ 3 + 1 := Nat.add_le_add_right (card_triple_le_three b c d) 1
    _ = 4 := by omega

private theorem image_card_two_of_xy_eq {β : Type*} [DecidableEq β]
    {x y z : V} (f : V → β) (hxy : f x = f y) (hxz : f x ≠ f z) :
    (({x, y, z} : Finset V).image f).card = 2 := by
  have hyz : f y ≠ f z := by
    intro h
    exact hxz (hxy.trans h)
  simp [hxy, hyz]

private theorem image_card_two_of_xz_eq {β : Type*} [DecidableEq β]
    {x y z : V} (f : V → β) (hxz : f x = f z) (hxy : f x ≠ f y) :
    (({x, y, z} : Finset V).image f).card = 2 := by
  have hyz : f y ≠ f z := by
    intro h
    exact hxy (hxz.trans h.symm)
  simp [hxz, hyz]

private theorem image_card_two_of_yz_eq {β : Type*} [DecidableEq β]
    {x y z : V} (f : V → β) (hyz : f y = f z) (hxy : f x ≠ f y) :
    (({x, y, z} : Finset V).image f).card = 2 := by
  have hxz : f x ≠ f z := by
    intro h
    exact hxy (h.trans hyz.symm)
  simp [hyz, hxz]

private theorem color_pair_card_two {α : Type*} [DecidableEq α] {a b : α}
    (hab : a ≠ b) :
    ({a, b} : Finset α).card = 2 := by
  simp [hab]

private theorem color_card_two_of_xz_eq {α : Type*} [DecidableEq α] {a b c : α}
    (hac : a = c) (hab : a ≠ b) :
    ({a, b, c} : Finset α).card = 2 := by
  have hbc : b ≠ c := by
    intro h
    exact hab (hac.trans h.symm)
  simp [hac, hbc]

private theorem color_card_two_of_xy_eq {α : Type*} [DecidableEq α] {a b c : α}
    (hab_eq : a = b) (hac_ne : a ≠ c) :
    ({a, b, c} : Finset α).card = 2 := by
  have hbc : b ≠ c := by
    intro h
    exact hac_ne (hab_eq.trans h)
  simp [hab_eq, hbc]

private theorem color_card_two_of_yz_eq {α : Type*} [DecidableEq α] {a b c : α}
    (hbc_eq : b = c) (hab_ne : a ≠ b) :
    ({a, b, c} : Finset α).card = 2 := by
  have hac : a ≠ c := by
    intro h
    exact hab_ne (h.trans hbc_eq.symm)
  simp [hbc_eq, hac]

private theorem exists_color_for_c4_edge {m : Nat} (hm : 4 ≤ m)
    {cu cv cy cz : Fin m} (_hucv : cu ≠ cv) (hucy : cu ≠ cy) (hucz : cu ≠ cz) :
    ∃ p : Fin m, p ≠ cu ∧ p ≠ cv ∧
      ({p, cy, cz} : Finset (Fin m)).card = 2 := by
  classical
  by_cases hyz : cy = cz
  · let forbidden : Finset (Fin m) := {cu, cv, cy}
    have hforbidden_card : forbidden.card < m := by
      have hle : forbidden.card ≤ 3 := by
        simpa [forbidden] using card_triple_le_three cu cv cy
      omega
    obtain ⟨p, hp⟩ := exists_fin_not_mem_of_card_lt forbidden hforbidden_card
    have hp_cu : p ≠ cu := by
      intro h
      exact hp (by simp [forbidden, h])
    have hp_cv : p ≠ cv := by
      intro h
      exact hp (by simp [forbidden, h])
    have hp_cy : p ≠ cy := by
      intro h
      exact hp (by simp [forbidden, h])
    have hp_cz : p ≠ cz := by
      simpa [hyz] using hp_cy
    refine ⟨p, hp_cu, hp_cv, ?_⟩
    simp [hyz, hp_cz]
  · by_cases hcvcy : cv = cy
    · refine ⟨cz, ?_, ?_, ?_⟩
      · intro h
        exact hucz h.symm
      · intro h
        exact hyz (hcvcy.symm.trans h.symm)
      · simp [hyz]
    · refine ⟨cy, ?_, ?_, ?_⟩
      · intro h
        exact hucy h.symm
      · intro h
        exact hcvcy h.symm
      · simp [hyz]

private theorem exists_color_for_c4_nonedge {m : Nat} (hm : 4 ≤ m)
    {cu cv cy cz : Fin m} (_hucv : cu ≠ cv)
    (hnot_pair : ¬ ((cy = cu ∧ cz = cv) ∨ (cy = cv ∧ cz = cu))) :
    ∃ p : Fin m, p ≠ cu ∧ p ≠ cv ∧
      ({p, cy, cz} : Finset (Fin m)).card = 2 := by
  classical
  by_cases hyz : cy = cz
  · let forbidden : Finset (Fin m) := {cu, cv, cy}
    have hforbidden_card : forbidden.card < m := by
      have hle : forbidden.card ≤ 3 := by
        simpa [forbidden] using card_triple_le_three cu cv cy
      omega
    obtain ⟨p, hp⟩ := exists_fin_not_mem_of_card_lt forbidden hforbidden_card
    have hp_cu : p ≠ cu := by
      intro h
      exact hp (by simp [forbidden, h])
    have hp_cv : p ≠ cv := by
      intro h
      exact hp (by simp [forbidden, h])
    have hp_cz : p ≠ cz := by
      intro h
      exact hp (by simp [forbidden, hyz, h])
    refine ⟨p, hp_cu, hp_cv, ?_⟩
    simp [hyz, hp_cz]
  · by_cases hy_cu : cy = cu
    · have hz_cv : cz ≠ cv := by
        intro h
        exact hnot_pair (Or.inl ⟨hy_cu, h⟩)
      refine ⟨cz, ?_, hz_cv, ?_⟩
      · intro h
        exact hyz (hy_cu.trans h.symm)
      · simp [hyz]
    · by_cases hy_cv : cy = cv
      · have hz_cu : cz ≠ cu := by
          intro h
          exact hnot_pair (Or.inr ⟨hy_cv, h⟩)
        refine ⟨cz, hz_cu, ?_, ?_⟩
        · intro h
          exact hyz (hy_cv.trans h.symm)
        · simp [hyz]
      · refine ⟨cy, hy_cu, hy_cv, ?_⟩
        simp [hyz]

private theorem color_eq_left_or_right_of_card_two {m : Nat}
    {a b c : Fin m} (hab : a ≠ b)
    (hcard : ({c, a, b} : Finset (Fin m)).card = 2) :
    c = a ∨ c = b := by
  by_contra hnot
  push Not at hnot
  have hcard3 : ({c, a, b} : Finset (Fin m)).card = 3 := by
    simp [hnot.1, hnot.2, hab]
  omega

private theorem colorable_of_conditions [Fintype V] {m : Nat} (hmpos : 0 < m)
    (hT : T3Conditions m G) : KColorable m G := by
  classical
  rcases subsingleton_or_nontrivial V with hsub | _hnon
  · exact ⟨KColoring.ofSubsingleton G hmpos⟩
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    obtain ⟨c, _⟩ := hT.c2 hxy
    exact ⟨c⟩

private theorem side_coloring_four_image_card_lt [Fintype V] {m : Nat}
    (hm : 4 ≤ m) (hfrag : MFragile m G)
    {C : SeparatedCover G} (hB : T3Conditions m (G.induce C.B))
    (T : Finset V) (hTcard : T.card ≤ 4)
    (hTB : ∀ ⦃t : V⦄, t ∈ T → t ∈ C.B) :
    ∃ cB : KColoring m (G.induce C.B),
      (T.image (fun t =>
        if ht : t ∈ T then cB.color ⟨t, hTB ht⟩
        else freshColor (lt_of_lt_of_le (by decide : 0 < 4) hm))).card < m := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  by_cases hm5 : 5 ≤ m
  · obtain ⟨cB⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    refine ⟨cB, ?_⟩
    have hle :
        (T.image (fun t =>
          if ht : t ∈ T then cB.color ⟨t, hTB ht⟩ else freshColor hmpos)).card ≤
          T.card := Finset.card_image_le
    omega
  · have hm_eq : m = 4 := by omega
    subst m
    let hmpos4 : 0 < 4 := by decide
    by_cases hTlt : T.card < 4
    · obtain ⟨cB⟩ := colorable_of_conditions (G := G.induce C.B) hmpos4 hB
      refine ⟨cB, ?_⟩
      have hle :
          (T.image (fun t =>
            if ht : t ∈ T then cB.color ⟨t, hTB ht⟩ else freshColor hmpos4)).card ≤
            T.card := Finset.card_image_le
      omega
    · have hTcard_eq : T.card = 4 := by omega
      by_cases hnon :
          ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ ¬ G.Adj a b
      · rcases hnon with ⟨a, ha, b, hb, hab, hnab⟩
        have hnB : ¬ (G.induce C.B).Adj ⟨a, hTB ha⟩ ⟨b, hTB hb⟩ := by
          intro habB
          exact hnab habB
        obtain ⟨cB, hceq⟩ := hB.c1 hnB
        refine ⟨cB, ?_⟩
        let f : V → Fin 4 := fun t =>
          if ht : t ∈ T then cB.color ⟨t, hTB ht⟩ else freshColor hmpos4
        have hfab : f a = f b := by
          simp [f, ha, hb, hceq]
        have himg_lt : (T.image f).card < T.card :=
          card_image_lt_of_pair_eq T f ha hb hab hfab
        simpa [f] using (by omega : (T.image f).card < 4)
      · have hclique : ∀ ⦃a b : V⦄, a ∈ T → b ∈ T → a ≠ b → G.Adj a b := by
          intro a b ha hb hab
          by_contra hnab
          exact hnon ⟨a, ha, b, hb, hab, hnab⟩
        exact False.elim (no_clique4_of_mfragile_four (G := G) hfrag hTcard_eq hclique)

private theorem side_coloring_matching_separator [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hB : T3Conditions m (G.induce C.B))
    (cA : KColoring m (G.induce C.A)) :
    ∃ cB : KColoring m (G.induce C.B),
      ∀ ⦃x : V⦄, (hxA : x ∈ C.A) → (hxB : x ∈ C.B) →
        cA.color ⟨x, hxA⟩ = cB.color ⟨x, hxB⟩ := by
  classical
  let S := C.separator
  have hSsmall : S.card ≤ 2 := C.separator_small
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · obtain ⟨cB0⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    refine ⟨cB0, ?_⟩
    intro x hxA hxB
    have hxS : x ∈ S := C.inter_subset_separator ⟨hxA, hxB⟩
    have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
    simp [S, hSempty] at hxS
  · rcases Finset.card_eq_one.mp h1 with ⟨u, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    obtain ⟨cB0⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    obtain ⟨σ, hσ⟩ :=
      exists_perm_map_one (cB0.color ⟨u, huB⟩) (cA.color ⟨u, huA⟩)
    refine ⟨cB0.relabel σ, ?_⟩
    intro x hxA hxB
    have hxS : x ∈ S := C.inter_subset_separator ⟨hxA, hxB⟩
    have hx_eq : x = u := by
      simpa [hS_eq] using hxS
    subst x
    simpa [KColoring.relabel_color] using hσ.symm
  · rcases Finset.card_eq_two.mp h2 with ⟨u, v, huv, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have hvS : v ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hvA : v ∈ C.A := (C.separator_subset_inter hvS).1
    have hvB : v ∈ C.B := (C.separator_subset_inter hvS).2
    by_cases hAeq : cA.color ⟨u, huA⟩ = cA.color ⟨v, hvA⟩
    · have hnB : ¬ (G.induce C.B).Adj ⟨u, huB⟩ ⟨v, hvB⟩ := by
        intro hAdjB
        exact cA.valid (show (G.induce C.A).Adj ⟨u, huA⟩ ⟨v, hvA⟩ from hAdjB) hAeq
      obtain ⟨cB0, hBuv⟩ := hB.c1 hnB
      let a : V → Fin m :=
        fun x => if hx : x ∈ C.A then cA.color ⟨x, hx⟩ else freshColor hmpos
      let b : V → Fin m :=
        fun x => if hx : x ∈ C.B then cB0.color ⟨x, hx⟩ else freshColor hmpos
      have hpat : ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → (b x = b y ↔ a x = a y) := by
        intro x y hxS hyS
        have hxA : x ∈ C.A := (C.separator_subset_inter hxS).1
        have hxB : x ∈ C.B := (C.separator_subset_inter hxS).2
        have hyA : y ∈ C.A := (C.separator_subset_inter hyS).1
        have hyB : y ∈ C.B := (C.separator_subset_inter hyS).2
        have hxuv : x = u ∨ x = v := by simpa [S, hS_eq] using hxS
        have hyuv : y = u ∨ y = v := by simpa [S, hS_eq] using hyS
        rcases hxuv with rfl | rfl <;> rcases hyuv with rfl | rfl <;>
          simp [a, b, huA, huB, hvA, hvB, hAeq, hBuv]
      obtain ⟨σ, hσ⟩ := exists_perm_agree_on_finset hSsmall a b hpat
      refine ⟨cB0.relabel σ, ?_⟩
      intro x hxA hxB
      have hxS : x ∈ S := C.inter_subset_separator ⟨hxA, hxB⟩
      have hxσ := hσ hxS
      simpa [a, b, hxA, hxB, KColoring.relabel_color] using hxσ.symm
    · obtain ⟨cB0, hBuv⟩ := hB.c2
        (show (⟨u, huB⟩ : C.B) ≠ ⟨v, hvB⟩ from by
          intro h
          exact huv (Subtype.ext_iff.mp h))
      have hAeq_rev : cA.color ⟨v, hvA⟩ ≠ cA.color ⟨u, huA⟩ := fun h => hAeq h.symm
      have hBuv_rev : cB0.color ⟨v, hvB⟩ ≠ cB0.color ⟨u, huB⟩ := fun h => hBuv h.symm
      let a : V → Fin m :=
        fun x => if hx : x ∈ C.A then cA.color ⟨x, hx⟩ else freshColor hmpos
      let b : V → Fin m :=
        fun x => if hx : x ∈ C.B then cB0.color ⟨x, hx⟩ else freshColor hmpos
      have hpat : ∀ ⦃x y : V⦄, x ∈ S → y ∈ S → (b x = b y ↔ a x = a y) := by
        intro x y hxS hyS
        have hxA : x ∈ C.A := (C.separator_subset_inter hxS).1
        have hxB : x ∈ C.B := (C.separator_subset_inter hxS).2
        have hyA : y ∈ C.A := (C.separator_subset_inter hyS).1
        have hyB : y ∈ C.B := (C.separator_subset_inter hyS).2
        have hxuv : x = u ∨ x = v := by simpa [S, hS_eq] using hxS
        have hyuv : y = u ∨ y = v := by simpa [S, hS_eq] using hyS
        rcases hxuv with rfl | rfl <;> rcases hyuv with rfl | rfl <;>
          simp [a, b, huA, huB, hvA, hvB, hAeq, hAeq_rev, hBuv, hBuv_rev]
      obtain ⟨σ, hσ⟩ := exists_perm_agree_on_finset hSsmall a b hpat
      refine ⟨cB0.relabel σ, ?_⟩
      intro x hxA hxB
      have hxS : x ∈ S := C.inter_subset_separator ⟨hxA, hxB⟩
      have hxσ := hσ hxS
      simpa [a, b, hxA, hxB, KColoring.relabel_color] using hxσ.symm

private theorem extend_left_coloring [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hB : T3Conditions m (G.induce C.B))
    (cA : KColoring m (G.induce C.A)) :
    ∃ c : KColoring m G,
      ∀ ⦃x : V⦄, (hxA : x ∈ C.A) → c.color x = cA.color ⟨x, hxA⟩ := by
  classical
  obtain ⟨cB, hagree⟩ := side_coloring_matching_separator hmpos C hB cA
  let c : KColoring m G := KColoring.glueSeparated C.A C.B C.cover C.no_edge cA cB hagree
  refine ⟨c, ?_⟩
  intro x hxA
  simp [c, KColoring.glueSeparated, hxA]

private theorem extend_right_coloring [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A))
    (cB : KColoring m (G.induce C.B)) :
    ∃ c : KColoring m G,
      ∀ ⦃x : V⦄, (hxB : x ∈ C.B) → c.color x = cB.color ⟨x, hxB⟩ := by
  exact extend_left_coloring hmpos C.symm hA cB

private theorem separated_c1_left [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y : V} (hxA : x ∈ C.A) (hyA : y ∈ C.A) (hnxy : ¬ G.Adj x y) :
    ∃ c : KColoring m G, c.color x = c.color y := by
  have hnA : ¬ (G.induce C.A).Adj ⟨x, hxA⟩ ⟨y, hyA⟩ := by
    intro hxy
    exact hnxy hxy
  obtain ⟨cA, hxyA⟩ := hA.c1 hnA
  obtain ⟨c, hcx⟩ := extend_left_coloring hmpos C hB cA
  refine ⟨c, ?_⟩
  rw [hcx hxA, hcx hyA, hxyA]

private theorem separated_c2_left [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y : V} (hxA : x ∈ C.A) (hyA : y ∈ C.A) (hxy : x ≠ y) :
    ∃ c : KColoring m G, c.color x ≠ c.color y := by
  have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
    intro h
    exact hxy (Subtype.ext_iff.mp h)
  obtain ⟨cA, hneqA⟩ := hA.c2 hxyA
  obtain ⟨c, hcx⟩ := extend_left_coloring hmpos C hB cA
  refine ⟨c, ?_⟩
  simpa [hcx hxA, hcx hyA] using hneqA

private theorem separated_c3_left [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hyA : y ∈ C.A) (hzA : z ∈ C.A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
    intro h
    exact hxy (Subtype.ext_iff.mp h)
  have hxzA : (⟨x, hxA⟩ : C.A) ≠ ⟨z, hzA⟩ := by
    intro h
    exact hxz (Subtype.ext_iff.mp h)
  have hyzA : (⟨y, hyA⟩ : C.A) ≠ ⟨z, hzA⟩ := by
    intro h
    exact hyz (Subtype.ext_iff.mp h)
  obtain ⟨cA, hnotA⟩ := hA.c3 hxyA hxzA hyzA
  obtain ⟨c, hcx⟩ := extend_left_coloring hmpos C hB cA
  refine ⟨c, ?_⟩
  simpa [hcx hxA, hcx hyA, hcx hzA] using hnotA

private theorem separated_c4_left [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hyA : y ∈ C.A) (hzA : z ∈ C.A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnot_triangle : ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z)) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
    intro h
    exact hxy (Subtype.ext_iff.mp h)
  have hxzA : (⟨x, hxA⟩ : C.A) ≠ ⟨z, hzA⟩ := by
    intro h
    exact hxz (Subtype.ext_iff.mp h)
  have hyzA : (⟨y, hyA⟩ : C.A) ≠ ⟨z, hzA⟩ := by
    intro h
    exact hyz (Subtype.ext_iff.mp h)
  have hnotA :
      ¬ ((G.induce C.A).Adj ⟨x, hxA⟩ ⟨y, hyA⟩ ∧
        (G.induce C.A).Adj ⟨x, hxA⟩ ⟨z, hzA⟩ ∧
        (G.induce C.A).Adj ⟨y, hyA⟩ ⟨z, hzA⟩) := by
    rintro ⟨hxyE, hxzE, hyzE⟩
    exact hnot_triangle ⟨hxyE, hxzE, hyzE⟩
  obtain ⟨cA, hcardA⟩ := hA.c4 hxyA hxzA hyzA hnotA
  obtain ⟨c, hcx⟩ := extend_left_coloring hmpos C hB cA
  refine ⟨c, ?_⟩
  simpa [hcx hxA, hcx hyA, hcx hzA] using hcardA

omit [DecidableEq V] in
private theorem agree_on_overlap_of_separator {m : Nat} {G : SimpleGraph V}
    (C : SeparatedCover G) (cA : KColoring m (G.induce C.A))
    (cB : KColoring m (G.induce C.B))
    (hsep : ∀ ⦃x : V⦄, (hxS : x ∈ C.separator) →
      cA.color ⟨x, (C.separator_subset_inter hxS).1⟩ =
        cB.color ⟨x, (C.separator_subset_inter hxS).2⟩) :
    ∀ ⦃x : V⦄, (hxA : x ∈ C.A) → (hxB : x ∈ C.B) →
      cA.color ⟨x, hxA⟩ = cB.color ⟨x, hxB⟩ := by
  intro x hxA hxB
  have hxS : x ∈ C.separator := C.inter_subset_separator ⟨hxA, hxB⟩
  simpa using hsep hxS

omit [DecidableEq V] in
private theorem glue_cross_equal {m : Nat} {G : SimpleGraph V} (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B) (hyNotA : y ∉ C.A)
    (hagree : ∀ ⦃z : V⦄, (hzA : z ∈ C.A) → (hzB : z ∈ C.B) →
      cA.color ⟨z, hzA⟩ = cB.color ⟨z, hzB⟩)
    (hxy : cA.color ⟨x, hxA⟩ = cB.color ⟨y, hyB⟩) :
    ∃ c : KColoring m G, c.color x = c.color y := by
  classical
  let c : KColoring m G := KColoring.glueSeparated C.A C.B C.cover C.no_edge cA cB hagree
  refine ⟨c, ?_⟩
  simp [c, KColoring.glueSeparated, hxA, hyNotA, hxy]

omit [DecidableEq V] in
private theorem glue_cross_avoid {m : Nat} {G : SimpleGraph V} (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B) (hzB : z ∈ C.B)
    (hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
      cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩)
    (hy_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨y, hyB⟩)
    (hz_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  let c : KColoring m G := KColoring.glueSeparated C.A C.B C.cover C.no_edge cA cB hagree
  have hcx : c.color x = cA.color ⟨x, hxA⟩ := by
    simp [c, KColoring.glueSeparated, hxA]
  have hcy : c.color y = cB.color ⟨y, hyB⟩ := by
    by_cases hyA : y ∈ C.A
    · have hyagree := hagree hyA hyB
      simp [c, KColoring.glueSeparated, hyA, hyagree]
    · simp [c, KColoring.glueSeparated, hyA]
  have hcz : c.color z = cB.color ⟨z, hzB⟩ := by
    by_cases hzA : z ∈ C.A
    · have hzagree := hagree hzA hzB
      simp [c, KColoring.glueSeparated, hzA, hzagree]
    · simp [c, KColoring.glueSeparated, hzA]
  refine ⟨c, ?_⟩
  simp [hcx, hcy, hcz, hy_ne, hz_ne]

private theorem glue_cross_avoid_of_separator_pair [Fintype V] {m : Nat}
    {G : SimpleGraph V} (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z u v : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B) (hzB : z ∈ C.B)
    (huS : u ∈ C.separator) (hvS : v ∈ C.separator)
    (hS_eq : C.separator = {u, v})
    (hu_eq : cA.color ⟨u, (C.separator_subset_inter huS).1⟩ =
      cB.color ⟨u, (C.separator_subset_inter huS).2⟩)
    (hv_eq : cA.color ⟨v, (C.separator_subset_inter hvS).1⟩ =
      cB.color ⟨v, (C.separator_subset_inter hvS).2⟩)
    (hy_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨y, hyB⟩)
    (hz_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  refine glue_cross_avoid C cA cB hxA hyB hzB ?_ hy_ne hz_ne
  refine agree_on_overlap_of_separator C cA cB ?_
  intro w hwS
  have hwuv : w = u ∨ w = v := by simpa [hS_eq] using hwS
  rcases hwuv with rfl | rfl
  · exact hu_eq
  · exact hv_eq

omit [DecidableEq V] in
private theorem glue_left_left_right_avoid {m : Nat} {G : SimpleGraph V}
    (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hyA : y ∈ C.A)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
      cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩)
    (hxy_ne : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨y, hyA⟩)
    (hz_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  let c : KColoring m G := KColoring.glueSeparated C.A C.B C.cover C.no_edge cA cB hagree
  refine ⟨c, ?_⟩
  simp [c, KColoring.glueSeparated, hxA, hyA, hzNotA, hxy_ne, hz_ne]

private theorem glue_left_left_right_avoid_of_separator_pair [Fintype V] {m : Nat}
    {G : SimpleGraph V} (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z u v : V} (hxA : x ∈ C.A) (hyA : y ∈ C.A)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (huS : u ∈ C.separator) (hvS : v ∈ C.separator)
    (hS_eq : C.separator = {u, v})
    (hu_eq : cA.color ⟨u, (C.separator_subset_inter huS).1⟩ =
      cB.color ⟨u, (C.separator_subset_inter huS).2⟩)
    (hv_eq : cA.color ⟨v, (C.separator_subset_inter hvS).1⟩ =
      cB.color ⟨v, (C.separator_subset_inter hvS).2⟩)
    (hxy_ne : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨y, hyA⟩)
    (hz_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  refine glue_left_left_right_avoid C cA cB hxA hyA hzB hzNotA ?_ hxy_ne hz_ne
  refine agree_on_overlap_of_separator C cA cB ?_
  intro w hwS
  have hwuv : w = u ∨ w = v := by simpa [hS_eq] using hwS
  rcases hwuv with rfl | rfl
  · exact hu_eq
  · exact hv_eq

private theorem glue_cross_image_two_xz {m : Nat} {G : SimpleGraph V}
    (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
      cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩)
    (hxz_eq : cA.color ⟨x, hxA⟩ = cB.color ⟨z, hzB⟩)
    (hxy_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨y, hyB⟩) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  let c : KColoring m G := KColoring.glueSeparated C.A C.B C.cover C.no_edge cA cB hagree
  have hcx : c.color x = cA.color ⟨x, hxA⟩ := by
    simp [c, KColoring.glueSeparated, hxA]
  have hcy : c.color y = cB.color ⟨y, hyB⟩ := by
    by_cases hyA : y ∈ C.A
    · have hyagree := hagree hyA hyB
      simp [c, KColoring.glueSeparated, hyA, hyagree]
    · simp [c, KColoring.glueSeparated, hyA]
  have hcz : c.color z = cB.color ⟨z, hzB⟩ := by
    simp [c, KColoring.glueSeparated, hzNotA]
  refine ⟨c, ?_⟩
  exact image_card_two_of_xz_eq c.color (by simpa [hcx, hcz] using hxz_eq)
    (by
      intro h
      exact hxy_ne (by simpa [hcx, hcy] using h))

private theorem glue_cross_image_two_of_colors {m : Nat} {G : SimpleGraph V}
    (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
      cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩)
    (hcard :
      ({cA.color ⟨x, hxA⟩, cB.color ⟨y, hyB⟩, cB.color ⟨z, hzB⟩} :
        Finset (Fin m)).card = 2) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  let c : KColoring m G := KColoring.glueSeparated C.A C.B C.cover C.no_edge cA cB hagree
  have hcx : c.color x = cA.color ⟨x, hxA⟩ := by
    simp [c, KColoring.glueSeparated, hxA]
  have hcy : c.color y = cB.color ⟨y, hyB⟩ := by
    by_cases hyA : y ∈ C.A
    · have hyagree := hagree hyA hyB
      simp [c, KColoring.glueSeparated, hyA, hyagree]
    · simp [c, KColoring.glueSeparated, hyA]
  have hcz : c.color z = cB.color ⟨z, hzB⟩ := by
    simp [c, KColoring.glueSeparated, hzNotA]
  refine ⟨c, ?_⟩
  simpa [hcx, hcy, hcz] using hcard

private theorem glue_cross_image_two_xz_of_separator_pair [Fintype V] {m : Nat}
    {G : SimpleGraph V} (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y z u v : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (huS : u ∈ C.separator) (hvS : v ∈ C.separator)
    (hS_eq : C.separator = {u, v})
    (hu_eq : cA.color ⟨u, (C.separator_subset_inter huS).1⟩ =
      cB.color ⟨u, (C.separator_subset_inter huS).2⟩)
    (hv_eq : cA.color ⟨v, (C.separator_subset_inter hvS).1⟩ =
      cB.color ⟨v, (C.separator_subset_inter hvS).2⟩)
    (hxz_eq : cA.color ⟨x, hxA⟩ = cB.color ⟨z, hzB⟩)
    (hxy_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨y, hyB⟩) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  refine glue_cross_image_two_xz C cA cB hxA hyB hzB hzNotA ?_ hxz_eq hxy_ne
  refine agree_on_overlap_of_separator C cA cB ?_
  intro w hwS
  have hwuv : w = u ∨ w = v := by simpa [hS_eq] using hwS
  rcases hwuv with rfl | rfl
  · exact hu_eq
  · exact hv_eq

private theorem side_coloring_match_pair_avoid_one [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    {C : SeparatedCover G} (hB : T3Conditions m (G.induce C.B))
    {u v w : V} (huv : u ≠ v) (huB : u ∈ C.B) (hvB : v ∈ C.B) (hwB : w ∈ C.B)
    {p tu tv : Fin m} (hp_tu : p ≠ tu) (hp_tv : p ≠ tv)
    (hnuv_of_eq : tu = tv → ¬ G.Adj u v) :
    ∃ cB : KColoring m (G.induce C.B),
      cB.color ⟨u, huB⟩ = tu ∧ cB.color ⟨v, hvB⟩ = tv ∧
        cB.color ⟨w, hwB⟩ ≠ p := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  let T : Finset V := {u, v, w}
  have huT : u ∈ T := by simp [T]
  have hvT : v ∈ T := by simp [T]
  have hwT : w ∈ T := by simp [T]
  by_cases hteq : tu = tv
  · have hnB : ¬ (G.induce C.B).Adj ⟨u, huB⟩ ⟨v, hvB⟩ := by
      intro huvB
      exact hnuv_of_eq hteq huvB
    obtain ⟨cB0, huv_eq⟩ := hB.c1 hnB
    let f : V → Fin m := fun t =>
      if ht : t ∈ T then
        cB0.color ⟨t, by
          have ht' : t = u ∨ t = v ∨ t = w := by simpa [T] using ht
          rcases ht' with rfl | rfl | rfl
          · exact huB
          · exact hvB
          · exact hwB⟩
      else freshColor hmpos
    have hcard : (T.image f).card < m := by
      have hle : (T.image f).card ≤ T.card := Finset.card_image_le
      have hTle : T.card ≤ 3 := by simpa [T] using card_triple_le_three u v w
      omega
    obtain ⟨σ, hσu, hσv, hσw, _⟩ :=
      exists_relabel_pair_avoid_on_finset T f huT hvT hwT hwT
        (u := u) (v := v) (y := w) (z := w)
        (p := p) (su := cB0.color ⟨u, huB⟩) (sv := cB0.color ⟨v, hvB⟩)
        (tu := tu) (tv := tv)
        (by simp [f, T]) (by simp [f, T])
        hp_tu hp_tv
        (by simp [huv_eq, hteq])
        hcard
    let cB := cB0.relabel σ
    refine ⟨cB, ?_, ?_, ?_⟩
    · simpa [cB, KColoring.relabel_color] using hσu
    · simpa [cB, KColoring.relabel_color] using hσv
    · intro h
      have h' : σ (f w) = p := by
        simpa [cB, KColoring.relabel_color, f, T] using h
      exact hσw h'
  · obtain ⟨cB0, huv_ne⟩ := hB.c2
      (show (⟨u, huB⟩ : C.B) ≠ ⟨v, hvB⟩ from by
        intro h
        exact huv (Subtype.ext_iff.mp h))
    let f : V → Fin m := fun t =>
      if ht : t ∈ T then
        cB0.color ⟨t, by
          have ht' : t = u ∨ t = v ∨ t = w := by simpa [T] using ht
          rcases ht' with rfl | rfl | rfl
          · exact huB
          · exact hvB
          · exact hwB⟩
      else freshColor hmpos
    have hcard : (T.image f).card < m := by
      have hle : (T.image f).card ≤ T.card := Finset.card_image_le
      have hTle : T.card ≤ 3 := by simpa [T] using card_triple_le_three u v w
      omega
    obtain ⟨σ, hσu, hσv, hσw, _⟩ :=
      exists_relabel_pair_avoid_on_finset T f huT hvT hwT hwT
        (u := u) (v := v) (y := w) (z := w)
        (p := p) (su := cB0.color ⟨u, huB⟩) (sv := cB0.color ⟨v, hvB⟩)
        (tu := tu) (tv := tv)
        (by simp [f, T]) (by simp [f, T])
        hp_tu hp_tv
        (by
          constructor
          · intro h
            exact False.elim (huv_ne h)
          · intro h
            exact False.elim (hteq h))
        hcard
    let cB := cB0.relabel σ
    refine ⟨cB, ?_, ?_, ?_⟩
    · simpa [cB, KColoring.relabel_color] using hσu
    · simpa [cB, KColoring.relabel_color] using hσv
    · intro h
      have h' : σ (f w) = p := by
        simpa [cB, KColoring.relabel_color, f, T] using h
      exact hσw h'

private theorem glue_cross_equal_of_triple_pattern [Fintype V] {m : Nat}
    {G : SimpleGraph V} (C : SeparatedCover G)
    (cA : KColoring m (G.induce C.A)) (cB : KColoring m (G.induce C.B))
    {x y u v : V} (hxA : x ∈ C.A) (hyB : y ∈ C.B) (hyNotA : y ∉ C.A)
    (huS : u ∈ C.separator) (hvS : v ∈ C.separator)
    (hS_eq : C.separator = {u, v})
    (hyu : (cB.color ⟨y, hyB⟩ = cB.color ⟨u, (C.separator_subset_inter huS).2⟩ ↔
      cA.color ⟨x, hxA⟩ = cA.color ⟨u, (C.separator_subset_inter huS).1⟩))
    (hyv : (cB.color ⟨y, hyB⟩ = cB.color ⟨v, (C.separator_subset_inter hvS).2⟩ ↔
      cA.color ⟨x, hxA⟩ = cA.color ⟨v, (C.separator_subset_inter hvS).1⟩))
    (huv : (cB.color ⟨u, (C.separator_subset_inter huS).2⟩ =
        cB.color ⟨v, (C.separator_subset_inter hvS).2⟩ ↔
      cA.color ⟨u, (C.separator_subset_inter huS).1⟩ =
        cA.color ⟨v, (C.separator_subset_inter hvS).1⟩)) :
    ∃ c : KColoring m G, c.color x = c.color y := by
  classical
  obtain ⟨σ, hσy, hσu, hσv⟩ :=
    exists_perm_map_triple hyu hyv huv
  let cB' := cB.relabel σ
  have hagree : ∀ ⦃z : V⦄, (hzA : z ∈ C.A) → (hzB : z ∈ C.B) →
      cA.color ⟨z, hzA⟩ = cB'.color ⟨z, hzB⟩ := by
    refine agree_on_overlap_of_separator C cA cB' ?_
    intro z hzS
    have hzuv : z = u ∨ z = v := by simpa [hS_eq] using hzS
    rcases hzuv with rfl | rfl
    · simpa [cB', KColoring.relabel_color] using hσu.symm
    · simpa [cB', KColoring.relabel_color] using hσv.symm
  exact glue_cross_equal C cA cB' hxA hyB hyNotA hagree
    (by simpa [cB', KColoring.relabel_color] using hσy.symm)

private theorem separated_c1_cross_hard [Fintype V] {m : Nat}
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y u v : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hyNotA : y ∉ C.A)
    (huvV : u ≠ v) (huS : u ∈ C.separator) (hvS : v ∈ C.separator)
    (hS_eq : C.separator = {u, v})
    (aA : KColoring m (G.induce C.A)) (aB : KColoring m (G.induce C.B))
    (ha_xu : aA.color ⟨x, hxA⟩ ≠ aA.color ⟨u, (C.separator_subset_inter huS).1⟩)
    (ha_xv : aA.color ⟨x, hxA⟩ ≠ aA.color ⟨v, (C.separator_subset_inter hvS).1⟩)
    (ha_uv : aA.color ⟨u, (C.separator_subset_inter huS).1⟩ ≠
      aA.color ⟨v, (C.separator_subset_inter hvS).1⟩)
    (hb_yu : aB.color ⟨y, hyB⟩ ≠ aB.color ⟨u, (C.separator_subset_inter huS).2⟩)
    (hb_yv : aB.color ⟨y, hyB⟩ ≠ aB.color ⟨v, (C.separator_subset_inter hvS).2⟩)
    (hb_uv : aB.color ⟨u, (C.separator_subset_inter huS).2⟩ =
      aB.color ⟨v, (C.separator_subset_inter hvS).2⟩) :
    ∃ c : KColoring m G, c.color x = c.color y := by
  classical
  let huA : u ∈ C.A := (C.separator_subset_inter huS).1
  let huB : u ∈ C.B := (C.separator_subset_inter huS).2
  let hvA : v ∈ C.A := (C.separator_subset_inter hvS).1
  let hvB : v ∈ C.B := (C.separator_subset_inter hvS).2
  have hxuV : x ≠ u := by
    intro h
    subst u
    exact hxNotB huB
  have hxvV : x ≠ v := by
    intro h
    subst v
    exact hxNotB hvB
  have hyuV : y ≠ u := by
    intro h
    subst u
    exact hyNotA huA
  have hyvV : y ≠ v := by
    intro h
    subst v
    exact hyNotA hvA
  have huxA : (⟨u, huA⟩ : C.A) ≠ ⟨x, hxA⟩ := by
    intro h
    exact hxuV (Subtype.ext_iff.mp h).symm
  have huvA : (⟨u, huA⟩ : C.A) ≠ ⟨v, hvA⟩ := by
    intro h
    exact huvV (Subtype.ext_iff.mp h)
  have hyuB_ne : (⟨y, hyB⟩ : C.B) ≠ ⟨u, huB⟩ := by
    intro h
    exact hyuV (Subtype.ext_iff.mp h)
  have huvB : (⟨u, huB⟩ : C.B) ≠ ⟨v, hvB⟩ := by
    intro h
    exact huvV (Subtype.ext_iff.mp h)

  obtain ⟨bA, hbAraw⟩ := hA.c3
    (x := ⟨u, huA⟩) (y := ⟨x, hxA⟩) (z := ⟨v, hvA⟩)
    huxA huvA (by
    intro h
    exact hxvV (Subtype.ext_iff.mp h))
  have hbA_ux : bA.color ⟨u, huA⟩ ≠ bA.color ⟨x, hxA⟩ := by
    intro h
    exact hbAraw (by simp [h])
  have hbA_uv : bA.color ⟨u, huA⟩ ≠ bA.color ⟨v, hvA⟩ := by
    intro h
    exact hbAraw (by simp [h])
  obtain ⟨bB, hbBraw⟩ := hB.c3
    (x := ⟨u, huB⟩) (y := ⟨y, hyB⟩) (z := ⟨v, hvB⟩)
    (by
    intro h
    exact hyuV (Subtype.ext_iff.mp h).symm) huvB (by
    intro h
    exact hyvV (Subtype.ext_iff.mp h))
  have hbB_uy : bB.color ⟨u, huB⟩ ≠ bB.color ⟨y, hyB⟩ := by
    intro h
    exact hbBraw (by simp [h])
  have hbB_uv : bB.color ⟨u, huB⟩ ≠ bB.color ⟨v, hvB⟩ := by
    intro h
    exact hbBraw (by simp [h])
  by_cases hb_same :
      (bB.color ⟨y, hyB⟩ = bB.color ⟨v, hvB⟩ ↔
        bA.color ⟨x, hxA⟩ = bA.color ⟨v, hvA⟩)
  · exact glue_cross_equal_of_triple_pattern C bA bB hxA hyB hyNotA huS hvS hS_eq
      (by
        constructor
        · intro h
          exact False.elim (hbB_uy h.symm)
        · intro h
          exact False.elim (hbA_ux h.symm))
      hb_same
      (by
        constructor
        · intro h
          exact False.elim (hbB_uv h)
        · intro h
          exact False.elim (hbA_uv h))
  · by_cases hbB_yv : bB.color ⟨y, hyB⟩ = bB.color ⟨v, hvB⟩
    · have hbA_xv : bA.color ⟨x, hxA⟩ ≠ bA.color ⟨v, hvA⟩ := by
        intro h
        exact hb_same ⟨fun _ => h, fun _ => hbB_yv⟩
      -- Continue with the $c$-colourings.
      obtain ⟨cA, hcAraw⟩ := hA.c3
        (x := ⟨v, hvA⟩) (y := ⟨x, hxA⟩) (z := ⟨u, huA⟩)
        (by
        intro h
        exact hxvV (Subtype.ext_iff.mp h).symm) (by
        intro h
        exact huvV (Subtype.ext_iff.mp h).symm) (by
        intro h
        exact hxuV (Subtype.ext_iff.mp h))
      have hcA_vx : cA.color ⟨v, hvA⟩ ≠ cA.color ⟨x, hxA⟩ := by
        intro h
        exact hcAraw (by simp [h])
      have hcA_vu : cA.color ⟨v, hvA⟩ ≠ cA.color ⟨u, huA⟩ := by
        intro h
        exact hcAraw (by simp [h])
      obtain ⟨cB, hcBraw⟩ := hB.c3
        (x := ⟨v, hvB⟩) (y := ⟨y, hyB⟩) (z := ⟨u, huB⟩)
        (by
        intro h
        exact hyvV (Subtype.ext_iff.mp h).symm) (by
        intro h
        exact huvV (Subtype.ext_iff.mp h).symm) (by
        intro h
        exact hyuV (Subtype.ext_iff.mp h))
      have hcB_vy : cB.color ⟨v, hvB⟩ ≠ cB.color ⟨y, hyB⟩ := by
        intro h
        exact hcBraw (by simp [h])
      have hcB_vu : cB.color ⟨v, hvB⟩ ≠ cB.color ⟨u, huB⟩ := by
        intro h
        exact hcBraw (by simp [h])
      by_cases hc_same :
          (cB.color ⟨y, hyB⟩ = cB.color ⟨u, huB⟩ ↔
            cA.color ⟨x, hxA⟩ = cA.color ⟨u, huA⟩)
      · exact glue_cross_equal_of_triple_pattern C cA cB hxA hyB hyNotA huS hvS hS_eq
          hc_same
          (by
            constructor
            · intro h
              exact False.elim (hcB_vy h.symm)
            · intro h
              exact False.elim (hcA_vx h.symm))
          (by
            constructor
            · intro h
              exact False.elim (hcB_vu h.symm)
            · intro h
              exact False.elim (hcA_vu h.symm))
      · by_cases hcB_yu : cB.color ⟨y, hyB⟩ = cB.color ⟨u, huB⟩
        · have hcA_xu : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨u, huA⟩ := by
            intro h
            exact hc_same ⟨fun _ => h, fun _ => hcB_yu⟩
          -- Final $d$-colouring from C4 on the left.
          have huv_nonedge : ¬ G.Adj u v := by
            intro huvE
            exact aB.valid
              (show (G.induce C.B).Adj ⟨u, huB⟩ ⟨v, hvB⟩ from huvE) hb_uv
          have hnot_triangle :
              ¬ ((G.induce C.A).Adj ⟨x, hxA⟩ ⟨u, huA⟩ ∧
                (G.induce C.A).Adj ⟨x, hxA⟩ ⟨v, hvA⟩ ∧
                (G.induce C.A).Adj ⟨u, huA⟩ ⟨v, hvA⟩) := by
            rintro ⟨_, _, huvE⟩
            exact huv_nonedge huvE
          obtain ⟨dA, hdAcard⟩ := hA.c4 (by
            intro h
            exact hxuV (Subtype.ext_iff.mp h)) (by
            intro h
            exact hxvV (Subtype.ext_iff.mp h)) huvA hnot_triangle
          by_cases hd_xu : dA.color ⟨x, hxA⟩ = dA.color ⟨u, huA⟩
          · have hd_xv : dA.color ⟨x, hxA⟩ ≠ dA.color ⟨v, hvA⟩ := by
              intro h
              have huv_eq : dA.color ⟨u, huA⟩ = dA.color ⟨v, hvA⟩ := hd_xu.symm.trans h
              simp [hd_xu, huv_eq] at hdAcard
            have hd_uv : dA.color ⟨u, huA⟩ ≠ dA.color ⟨v, hvA⟩ := by
              intro h
              simp [hd_xu, h] at hdAcard
            exact glue_cross_equal_of_triple_pattern C dA cB hxA hyB hyNotA huS hvS hS_eq
              (by simp [hd_xu, hcB_yu])
              (by
                constructor
                · intro h
                  exact False.elim (hcB_vy h.symm)
                · intro h
                  exact False.elim (hd_xv h))
              (by
                constructor
                · intro h
                  exact False.elim (hcB_vu h.symm)
                · intro h
                  exact False.elim (hd_uv h))
          · by_cases hd_xv : dA.color ⟨x, hxA⟩ = dA.color ⟨v, hvA⟩
            · have hd_uv : dA.color ⟨u, huA⟩ ≠ dA.color ⟨v, hvA⟩ := by
                intro h
                have hxu_eq : dA.color ⟨x, hxA⟩ = dA.color ⟨u, huA⟩ := hd_xv.trans h.symm
                exact hd_xu hxu_eq
              exact glue_cross_equal_of_triple_pattern C dA bB hxA hyB hyNotA huS hvS hS_eq
                (by
                  constructor
                  · intro h
                    exact False.elim (hbB_uy h.symm)
                  · intro h
                    exact False.elim (hd_xu h))
                (by simp [hd_xv, hbB_yv])
                (by
                  constructor
                  · intro h
                    exact False.elim (hbB_uv h)
                  · intro h
                    exact False.elim (hd_uv h))
            · have hd_uv_eq : dA.color ⟨u, huA⟩ = dA.color ⟨v, hvA⟩ := by
                by_contra hd_uv
                simp [hd_xu, hd_xv, hd_uv] at hdAcard
              exact glue_cross_equal_of_triple_pattern C dA aB hxA hyB hyNotA huS hvS hS_eq
                (by
                  constructor
                  · intro h
                    exact False.elim (hb_yu h)
                  · intro h
                    exact False.elim (hd_xu h))
                (by
                  constructor
                  · intro h
                    exact False.elim (hb_yv h)
                  · intro h
                    exact False.elim (hd_xv h))
                (by simp [hd_uv_eq, hb_uv])
        · exact glue_cross_equal_of_triple_pattern C aA cB hxA hyB hyNotA huS hvS hS_eq
            (by
              constructor
              · intro h
                exact False.elim (hcB_yu h)
              · intro h
                exact False.elim (ha_xu h))
            (by
              constructor
              · intro h
                exact False.elim (hcB_vy h.symm)
              · intro h
                exact False.elim (ha_xv h))
            (by
              constructor
              · intro h
                exact False.elim (hcB_vu h.symm)
              · intro h
                exact False.elim (ha_uv h))
    · exact glue_cross_equal_of_triple_pattern C aA bB hxA hyB hyNotA huS hvS hS_eq
        (by
          constructor
          · intro h
            exact False.elim (hbB_uy h.symm)
          · intro h
            exact False.elim (ha_xu h))
        (by
          constructor
          · intro h
            exact False.elim (hbB_yv h)
          · intro h
            exact False.elim (ha_xv h))
        (by
          constructor
          · intro h
            exact False.elim (hbB_uv h)
          · intro h
            exact False.elim (ha_uv h))

private theorem separated_c1_cross [Fintype V] {m : Nat} (hmpos : 0 < m)
    {G : SimpleGraph V} (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hyNotA : y ∉ C.A) :
    ∃ c : KColoring m G, c.color x = c.color y := by
  classical
  let S := C.separator
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by
    have : S.card ≤ 2 := by simpa [S] using C.separator_small
    omega
  rcases hcases with h0 | h1 | h2
  · obtain ⟨cA⟩ := colorable_of_conditions (G := G.induce C.A) hmpos hA
    obtain ⟨cB0⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    obtain ⟨σ, hσ⟩ := exists_perm_map_one (cB0.color ⟨y, hyB⟩) (cA.color ⟨x, hxA⟩)
    let cB := cB0.relabel σ
    have hagree : ∀ ⦃z : V⦄, (hzA : z ∈ C.A) → (hzB : z ∈ C.B) →
        cA.color ⟨z, hzA⟩ = cB.color ⟨z, hzB⟩ := by
      intro z hzA hzB
      have hzS : z ∈ S := C.inter_subset_separator ⟨hzA, hzB⟩
      have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
      simp [S, hSempty] at hzS
    exact glue_cross_equal C cA cB hxA hyB hyNotA hagree
      (by simpa [cB, KColoring.relabel_color] using hσ.symm)
  · rcases Finset.card_eq_one.mp h1 with ⟨u, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hxu : (⟨x, hxA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact hxNotB (by
        have hval : x = u := congrArg Subtype.val h
        rw [hval]
        exact huB)
    have hyu : (⟨y, hyB⟩ : C.B) ≠ ⟨u, huB⟩ := by
      intro h
      exact hyNotA (by
        have hval : y = u := congrArg Subtype.val h
        rw [hval]
        exact huA)
    obtain ⟨cA, hcA⟩ := hA.c2 hxu
    obtain ⟨cB0, hcB⟩ := hB.c2 hyu
    obtain ⟨σ, hσy, hσu⟩ := exists_perm_map_pair
      (by
        constructor
        · intro h
          exact False.elim (hcB h)
        · intro h
          exact False.elim (hcA h))
    let cB := cB0.relabel σ
    have hagree : ∀ ⦃z : V⦄, (hzA : z ∈ C.A) → (hzB : z ∈ C.B) →
        cA.color ⟨z, hzA⟩ = cB.color ⟨z, hzB⟩ := by
      refine agree_on_overlap_of_separator C cA cB ?_
      intro z hzS
      have hz_eq : z = u := by simpa [S, hS_eq] using hzS
      subst z
      simpa [cB, KColoring.relabel_color] using hσu.symm
    exact glue_cross_equal C cA cB hxA hyB hyNotA hagree
      (by simpa [cB, KColoring.relabel_color] using hσy.symm)
  · rcases Finset.card_eq_two.mp h2 with ⟨u, v, huvV, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have hvS : v ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hvA : v ∈ C.A := (C.separator_subset_inter hvS).1
    have hvB : v ∈ C.B := (C.separator_subset_inter hvS).2
    have hxuV : x ≠ u := by
      intro h
      subst u
      exact hxNotB huB
    have hxvV : x ≠ v := by
      intro h
      subst v
      exact hxNotB hvB
    have hyuV : y ≠ u := by
      intro h
      subst u
      exact hyNotA huA
    have hyvV : y ≠ v := by
      intro h
      subst v
      exact hyNotA hvA
    obtain ⟨aA, haAraw⟩ := hA.c3
      (x := ⟨x, hxA⟩) (y := ⟨u, huA⟩) (z := ⟨v, hvA⟩)
      (by intro h; exact hxuV (Subtype.ext_iff.mp h))
      (by intro h; exact hxvV (Subtype.ext_iff.mp h))
      (by intro h; exact huvV (Subtype.ext_iff.mp h))
    have ha_xu : aA.color ⟨x, hxA⟩ ≠ aA.color ⟨u, huA⟩ := by
      intro h
      exact haAraw (by simp [h])
    have ha_xv : aA.color ⟨x, hxA⟩ ≠ aA.color ⟨v, hvA⟩ := by
      intro h
      exact haAraw (by simp [h])
    obtain ⟨aB, haBraw⟩ := hB.c3
      (x := ⟨y, hyB⟩) (y := ⟨u, huB⟩) (z := ⟨v, hvB⟩)
      (by intro h; exact hyuV (Subtype.ext_iff.mp h))
      (by intro h; exact hyvV (Subtype.ext_iff.mp h))
      (by intro h; exact huvV (Subtype.ext_iff.mp h))
    have hb_yu : aB.color ⟨y, hyB⟩ ≠ aB.color ⟨u, huB⟩ := by
      intro h
      exact haBraw (by simp [h])
    have hb_yv : aB.color ⟨y, hyB⟩ ≠ aB.color ⟨v, hvB⟩ := by
      intro h
      exact haBraw (by simp [h])
    by_cases ha_uv_eq : aA.color ⟨u, huA⟩ = aA.color ⟨v, hvA⟩
    · by_cases hb_uv_eq : aB.color ⟨u, huB⟩ = aB.color ⟨v, hvB⟩
      · exact glue_cross_equal_of_triple_pattern C aA aB hxA hyB hyNotA huS hvS hS_eq
          (by
            constructor
            · intro h
              exact False.elim (hb_yu h)
            · intro h
              exact False.elim (ha_xu h))
          (by
            constructor
            · intro h
              exact False.elim (hb_yv h)
            · intro h
              exact False.elim (ha_xv h))
          (by simp [ha_uv_eq, hb_uv_eq])
      · obtain ⟨c, hc⟩ := separated_c1_cross_hard C.symm hB hA
          (x := y) (y := x) (u := u) (v := v)
          hyB hyNotA hxA hxNotB huvV huS hvS hS_eq
          aB aA hb_yu hb_yv hb_uv_eq ha_xu ha_xv ha_uv_eq
        exact ⟨c, hc.symm⟩
    · by_cases hb_uv_eq : aB.color ⟨u, huB⟩ = aB.color ⟨v, hvB⟩
      · exact separated_c1_cross_hard C hA hB hxA hxNotB hyB hyNotA
          huvV huS hvS hS_eq aA aB ha_xu ha_xv ha_uv_eq hb_yu hb_yv hb_uv_eq
      · exact glue_cross_equal_of_triple_pattern C aA aB hxA hyB hyNotA huS hvS hS_eq
          (by
            constructor
            · intro h
              exact False.elim (hb_yu h)
            · intro h
              exact False.elim (ha_xu h))
          (by
            constructor
            · intro h
              exact False.elim (hb_yv h)
            · intro h
              exact False.elim (ha_xv h))
          (by
            constructor
            · intro h
              exact False.elim (hb_uv_eq h)
            · intro h
              exact False.elim (ha_uv_eq h))

private theorem separated_c3_cross_one_left [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m) (hfrag : MFragile m G)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hzB : z ∈ C.B)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  let S := C.separator
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by
    have : S.card ≤ 2 := by simpa [S] using C.separator_small
    omega
  rcases hcases with h0 | h1 | h2
  · obtain ⟨cA⟩ := colorable_of_conditions (G := G.induce C.A) hmpos hA
    have hyzB_ne : (⟨y, hyB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
      intro h
      exact hyz (Subtype.ext_iff.mp h)
    obtain ⟨cB0, _hyz_ne⟩ := hB.c2 hyzB_ne
    let p := cA.color ⟨x, hxA⟩
    let img : Finset (Fin m) :=
      ({y, z} : Finset V).image (fun t =>
        if ht : t ∈ ({y, z} : Finset V) then
          cB0.color ⟨t, by
            have ht' : t = y ∨ t = z := by simpa using ht
            rcases ht' with rfl | rfl
            · exact hyB
            · exact hzB⟩
        else freshColor hmpos)
    have hcard_img : img.card < m := by
      have hle : img.card ≤ ({y, z} : Finset V).card := by
        dsimp [img]
        exact Finset.card_image_le
      have hpair_card : ({y, z} : Finset V).card ≤ 2 := card_pair_le_two y z
      omega
    obtain ⟨σ, hσavoid⟩ := exists_perm_avoid_on_finset img p hcard_img
    let cB := cB0.relabel σ
    have hy_mem : cB0.color ⟨y, hyB⟩ ∈ img := by
      dsimp [img]
      refine Finset.mem_image.mpr ⟨y, by simp, ?_⟩
      simp
    have hz_mem : cB0.color ⟨z, hzB⟩ ∈ img := by
      dsimp [img]
      refine Finset.mem_image.mpr ⟨z, by simp, ?_⟩
      simp
    have hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
        cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩ := by
      intro w hwA hwB
      have hwS : w ∈ S := C.inter_subset_separator ⟨hwA, hwB⟩
      have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
      simp [S, hSempty] at hwS
    exact glue_cross_avoid C cA cB hxA hyB hzB hagree
      (by
        intro h
        exact (hσavoid hy_mem) h.symm)
      (by
        intro h
        exact (hσavoid hz_mem) h.symm)
  · rcases Finset.card_eq_one.mp h1 with ⟨u, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hxu : (⟨x, hxA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact hxNotB (by
        have hval : x = u := congrArg Subtype.val h
        rw [hval]
        exact huB)
    obtain ⟨cA, hx_ne_u⟩ := hA.c2 hxu
    obtain ⟨cB0⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    let T : Finset V := {u, y, z}
    let f : V → Fin m := fun t =>
      if ht : t ∈ T then
        cB0.color ⟨t, by
          have ht' : t = u ∨ t = y ∨ t = z := by simpa [T] using ht
          rcases ht' with rfl | rfl | rfl
          · exact huB
          · exact hyB
          · exact hzB⟩
      else freshColor hmpos
    have hTcard : (T.image f).card < m := by
      have hle : (T.image f).card ≤ T.card := Finset.card_image_le
      have hTle : T.card ≤ 3 := by
        simpa [T] using card_triple_le_three u y z
      omega
    have huT : u ∈ T := by simp [T]
    have hyT : y ∈ T := by simp [T]
    have hzT : z ∈ T := by simp [T]
    obtain ⟨σ, hσu, _hσu', hσy, hσz⟩ :=
      exists_relabel_pair_avoid_on_finset T f huT huT hyT hzT
        (u := u) (v := u) (y := y) (z := z)
        (p := cA.color ⟨x, hxA⟩)
        (su := cB0.color ⟨u, huB⟩) (sv := cB0.color ⟨u, huB⟩)
        (tu := cA.color ⟨u, huA⟩) (tv := cA.color ⟨u, huA⟩)
        (by simp [f, T]) (by simp [f, T])
        (by
          intro h
          exact hx_ne_u h)
        (by
          intro h
          exact hx_ne_u h)
        (by simp) hTcard
    let cB := cB0.relabel σ
    have hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
        cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩ := by
      refine agree_on_overlap_of_separator C cA cB ?_
      intro w hwS
      have hw_eq : w = u := by simpa [S, hS_eq] using hwS
      subst w
      simpa [cB, KColoring.relabel_color] using hσu.symm
    exact glue_cross_avoid C cA cB hxA hyB hzB hagree
      (by
        intro h
        have h' : σ (f y) = cA.color ⟨x, hxA⟩ := by
          simpa [cB, KColoring.relabel_color, f, T] using h.symm
        exact hσy h')
      (by
        intro h
        have h' : σ (f z) = cA.color ⟨x, hxA⟩ := by
          simpa [cB, KColoring.relabel_color, f, T] using h.symm
        exact hσz h')
  · rcases Finset.card_eq_two.mp h2 with ⟨u, v, huvV, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have hvS : v ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hvA : v ∈ C.A := (C.separator_subset_inter hvS).1
    have hvB : v ∈ C.B := (C.separator_subset_inter hvS).2
    have hxuV : x ≠ u := by
      intro h
      subst u
      exact hxNotB huB
    have hxvV : x ≠ v := by
      intro h
      subst v
      exact hxNotB hvB
    let T : Finset V := {u, v, y, z}
    have huT : u ∈ T := by simp [T]
    have hvT : v ∈ T := by simp [T]
    have hyT : y ∈ T := by simp [T]
    have hzT : z ∈ T := by simp [T]
    have hTcard : T.card ≤ 4 := by
      simpa [T] using card_quad_le_four u v y z
    let mkF (cB : KColoring m (G.induce C.B)) : V → Fin m := fun t =>
      if ht : t ∈ T then
        cB.color ⟨t, by
          have ht' : t = u ∨ t = v ∨ t = y ∨ t = z := by simpa [T] using ht
          rcases ht' with rfl | rfl | rfl | rfl
          · exact huB
          · exact hvB
          · exact hyB
          · exact hzB⟩
      else freshColor hmpos
    by_cases huvE : G.Adj u v
    · obtain ⟨cA, hAraw⟩ := hA.c3
        (x := ⟨x, hxA⟩) (y := ⟨u, huA⟩) (z := ⟨v, hvA⟩)
        (by intro h; exact hxuV (Subtype.ext_iff.mp h))
        (by intro h; exact hxvV (Subtype.ext_iff.mp h))
        (by intro h; exact huvV (Subtype.ext_iff.mp h))
      have hx_ne_u : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨u, huA⟩ := by
        intro h
        exact hAraw (by simp [h])
      have hx_ne_v : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨v, hvA⟩ := by
        intro h
        exact hAraw (by simp [h])
      have hu_ne_v_A : cA.color ⟨u, huA⟩ ≠ cA.color ⟨v, hvA⟩ :=
        cA.valid (show (G.induce C.A).Adj ⟨u, huA⟩ ⟨v, hvA⟩ from huvE)
      obtain ⟨cB0, hBcard⟩ :=
        side_coloring_four_image_card_lt (G := G) hm hfrag hB T hTcard (by
          intro t ht
          have ht' : t = u ∨ t = v ∨ t = y ∨ t = z := by simpa [T] using ht
          rcases ht' with rfl | rfl | rfl | rfl
          · exact huB
          · exact hvB
          · exact hyB
          · exact hzB)
      let f := mkF cB0
      have hfu : f u = cB0.color ⟨u, huB⟩ := by simp [f, mkF, T]
      have hfv : f v = cB0.color ⟨v, hvB⟩ := by simp [f, mkF, T]
      have hu_ne_v_B : cB0.color ⟨u, huB⟩ ≠ cB0.color ⟨v, hvB⟩ :=
        cB0.valid (show (G.induce C.B).Adj ⟨u, huB⟩ ⟨v, hvB⟩ from huvE)
      obtain ⟨σ, hσu, hσv, hσy, hσz⟩ :=
        exists_relabel_pair_avoid_on_finset T f huT hvT hyT hzT
          (u := u) (v := v) (y := y) (z := z)
          (p := cA.color ⟨x, hxA⟩)
          (su := cB0.color ⟨u, huB⟩) (sv := cB0.color ⟨v, hvB⟩)
          (tu := cA.color ⟨u, huA⟩) (tv := cA.color ⟨v, hvA⟩)
          hfu hfv hx_ne_u hx_ne_v
          (by
            constructor
            · intro h
              exact False.elim (hu_ne_v_B h)
            · intro h
              exact False.elim (hu_ne_v_A h))
          (by simpa [f, mkF] using hBcard)
      let cB := cB0.relabel σ
      exact glue_cross_avoid_of_separator_pair C cA cB hxA hyB hzB huS hvS hS_eq
        (by simpa [cB, KColoring.relabel_color] using hσu.symm)
        (by simpa [cB, KColoring.relabel_color] using hσv.symm)
        (by
          intro h
          have h' : σ (f y) = cA.color ⟨x, hxA⟩ := by
            simpa [cB, KColoring.relabel_color, f, mkF, T] using h.symm
          exact hσy h')
        (by
          intro h
          have h' : σ (f z) = cA.color ⟨x, hxA⟩ := by
            simpa [cB, KColoring.relabel_color, f, mkF, T] using h.symm
          exact hσz h')
    · by_cases hex :
        ∃ cA : KColoring m (G.induce C.A),
          cA.color ⟨x, hxA⟩ ≠ cA.color ⟨u, huA⟩ ∧
            cA.color ⟨u, huA⟩ = cA.color ⟨v, hvA⟩
      · rcases hex with ⟨cA, hx_ne_u, hu_eq_v_A⟩
        have hnB : ¬ (G.induce C.B).Adj ⟨u, huB⟩ ⟨v, hvB⟩ := by
          intro h
          exact huvE h
        obtain ⟨cB0, hu_eq_v_B⟩ := hB.c1 hnB
        let f := mkF cB0
        have hfu : f u = cB0.color ⟨u, huB⟩ := by simp [f, mkF, T]
        have hfv : f v = cB0.color ⟨v, hvB⟩ := by simp [f, mkF, T]
        have hBcard : (T.image f).card < m := by
          have himg_lt_T : (T.image f).card < T.card := by
            refine card_image_lt_of_pair_eq T f huT hvT huvV ?_
            simp [f, mkF, T, hu_eq_v_B]
          omega
        obtain ⟨σ, hσu, hσv, hσy, hσz⟩ :=
          exists_relabel_pair_avoid_on_finset T f huT hvT hyT hzT
            (u := u) (v := v) (y := y) (z := z)
            (p := cA.color ⟨x, hxA⟩)
            (su := cB0.color ⟨u, huB⟩) (sv := cB0.color ⟨v, hvB⟩)
            (tu := cA.color ⟨u, huA⟩) (tv := cA.color ⟨v, hvA⟩)
            hfu hfv hx_ne_u (by simpa [hu_eq_v_A] using hx_ne_u)
            (by simp [hu_eq_v_B, hu_eq_v_A])
            hBcard
        let cB := cB0.relabel σ
        exact glue_cross_avoid_of_separator_pair C cA cB hxA hyB hzB huS hvS hS_eq
          (by simpa [cB, KColoring.relabel_color] using hσu.symm)
          (by simpa [cB, KColoring.relabel_color] using hσv.symm)
          (by
            intro h
            have h' : σ (f y) = cA.color ⟨x, hxA⟩ := by
              simpa [cB, KColoring.relabel_color, f, mkF, T] using h.symm
            exact hσy h')
          (by
            intro h
            have h' : σ (f z) = cA.color ⟨x, hxA⟩ := by
              simpa [cB, KColoring.relabel_color, f, mkF, T] using h.symm
            exact hσz h')
      · obtain ⟨bA, hbAraw⟩ := hA.c3
          (x := ⟨x, hxA⟩) (y := ⟨u, huA⟩) (z := ⟨v, hvA⟩)
          (by intro h; exact hxuV (Subtype.ext_iff.mp h))
          (by intro h; exact hxvV (Subtype.ext_iff.mp h))
          (by intro h; exact huvV (Subtype.ext_iff.mp h))
        have hb_xu : bA.color ⟨x, hxA⟩ ≠ bA.color ⟨u, huA⟩ := by
          intro h
          exact hbAraw (by simp [h])
        have hb_xv : bA.color ⟨x, hxA⟩ ≠ bA.color ⟨v, hvA⟩ := by
          intro h
          exact hbAraw (by simp [h])
        have hb_uv : bA.color ⟨u, huA⟩ ≠ bA.color ⟨v, hvA⟩ := by
          intro h
          exact hex ⟨bA, hb_xu, h⟩
        have hnot_triangle :
            ¬ ((G.induce C.A).Adj ⟨x, hxA⟩ ⟨u, huA⟩ ∧
              (G.induce C.A).Adj ⟨x, hxA⟩ ⟨v, hvA⟩ ∧
              (G.induce C.A).Adj ⟨u, huA⟩ ⟨v, hvA⟩) := by
          rintro ⟨_, _, huvA⟩
          exact huvE huvA
        obtain ⟨cA, hcAcard⟩ := hA.c4
          (by intro h; exact hxuV (Subtype.ext_iff.mp h))
          (by intro h; exact hxvV (Subtype.ext_iff.mp h))
          (by intro h; exact huvV (Subtype.ext_iff.mp h))
          hnot_triangle
        obtain ⟨dB, hd_uv⟩ := hB.c2
          (show (⟨u, huB⟩ : C.B) ≠ ⟨v, hvB⟩ from by
            intro h
            exact huvV (Subtype.ext_iff.mp h))
        let f := mkF dB
        have hfu : f u = dB.color ⟨u, huB⟩ := by simp [f, mkF, T]
        have hfv : f v = dB.color ⟨v, hvB⟩ := by simp [f, mkF, T]
        by_cases hBcard : (T.image f).card < m
        · obtain ⟨σ, hσu, hσv, hσy, hσz⟩ :=
            exists_relabel_pair_avoid_on_finset T f huT hvT hyT hzT
              (u := u) (v := v) (y := y) (z := z)
              (p := bA.color ⟨x, hxA⟩)
              (su := dB.color ⟨u, huB⟩) (sv := dB.color ⟨v, hvB⟩)
              (tu := bA.color ⟨u, huA⟩) (tv := bA.color ⟨v, hvA⟩)
              hfu hfv hb_xu hb_xv
              (by
                constructor
                · intro h
                  exact False.elim (hd_uv h)
                · intro h
                  exact False.elim (hb_uv h))
              hBcard
          let dB' := dB.relabel σ
          exact glue_cross_avoid_of_separator_pair C bA dB' hxA hyB hzB huS hvS hS_eq
            (by simpa [dB', KColoring.relabel_color] using hσu.symm)
            (by simpa [dB', KColoring.relabel_color] using hσv.symm)
            (by
              intro h
              have h' : σ (f y) = bA.color ⟨x, hxA⟩ := by
                simpa [dB', KColoring.relabel_color, f, mkF, T] using h.symm
              exact hσy h')
            (by
              intro h
              have h' : σ (f z) = bA.color ⟨x, hxA⟩ := by
                simpa [dB', KColoring.relabel_color, f, mkF, T] using h.symm
              exact hσz h')
        · have hm_eq : m = 4 := by
            have hle_img : (T.image f).card ≤ T.card := Finset.card_image_le
            omega
          have hImg4 : (T.image f).card = 4 := by
            have hle_img : (T.image f).card ≤ T.card := Finset.card_image_le
            omega
          have hT4 : T.card = 4 := by
            have hle_img : (T.image f).card ≤ T.card := Finset.card_image_le
            omega
          have hinj : Set.InjOn f (T : Set V) := by
            apply Finset.card_image_iff.mp
            omega
          have fy_ne_fu : f y ≠ f u := by
            intro h
            have hyu : y = u := hinj hyT huT h
            subst y
            have hTle3 : T.card ≤ 3 := by
              simpa [T] using card_triple_le_three v u z
            omega
          have fz_ne_fu : f z ≠ f u := by
            intro h
            have hzu : z = u := hinj hzT huT h
            have hnot_card : T.card < 4 := by
              subst z
              have hTle3 : T.card ≤ 3 := by
                simpa [T] using card_triple_le_three v y u
              omega
            omega
          have fy_ne_fv : f y ≠ f v := by
            intro h
            have hyv : y = v := hinj hyT hvT h
            have hnot_card : T.card < 4 := by
              subst y
              have hTle3 : T.card ≤ 3 := by
                simpa [T] using card_triple_le_three u v z
              omega
            omega
          have fz_ne_fv : f z ≠ f v := by
            intro h
            have hzv : z = v := hinj hzT hvT h
            have hnot_card : T.card < 4 := by
              subst z
              have hTle3 : T.card ≤ 3 := by
                simpa [T] using card_triple_le_three u y v
              omega
            omega
          by_cases hcxu : cA.color ⟨x, hxA⟩ = cA.color ⟨u, huA⟩
          · have hcuv : cA.color ⟨u, huA⟩ ≠ cA.color ⟨v, hvA⟩ := by
              intro h
              have hc' :
                  ({cA.color ⟨u, huA⟩, cA.color ⟨v, hvA⟩} :
                    Finset (Fin m)).card = 2 := by
                simpa [hcxu] using hcAcard
              have hc1 :
                  ({cA.color ⟨u, huA⟩, cA.color ⟨v, hvA⟩} :
                    Finset (Fin m)).card = 1 := by
                simp [h]
              omega
            obtain ⟨σ, hσu, hσv⟩ := exists_perm_map_pair
              (by
                constructor
                · intro h
                  exact False.elim (hd_uv h)
                · intro h
                  exact False.elim (hcuv h))
            let dB' := dB.relabel σ
            have hy_ne : cA.color ⟨x, hxA⟩ ≠ dB'.color ⟨y, hyB⟩ := by
              intro h
              have hyu : f y = f u := σ.injective (by
                simpa [dB', KColoring.relabel_color, f, mkF, T, hfu, hσu, hcxu] using h.symm)
              exact fy_ne_fu hyu
            have hz_ne : cA.color ⟨x, hxA⟩ ≠ dB'.color ⟨z, hzB⟩ := by
              intro h
              have hzu : f z = f u := σ.injective (by
                simpa [dB', KColoring.relabel_color, f, mkF, T, hfu, hσu, hcxu] using h.symm)
              exact fz_ne_fu hzu
            exact glue_cross_avoid_of_separator_pair C cA dB' hxA hyB hzB huS hvS hS_eq
              (by simpa [dB', KColoring.relabel_color] using hσu.symm)
              (by simpa [dB', KColoring.relabel_color] using hσv.symm)
              hy_ne hz_ne
          · by_cases hcxv : cA.color ⟨x, hxA⟩ = cA.color ⟨v, hvA⟩
            · have hcuv : cA.color ⟨u, huA⟩ ≠ cA.color ⟨v, hvA⟩ := by
                intro h
                have hxu : cA.color ⟨x, hxA⟩ = cA.color ⟨u, huA⟩ := hcxv.trans h.symm
                exact hcxu hxu
              obtain ⟨σ, hσu, hσv⟩ := exists_perm_map_pair
                (by
                  constructor
                  · intro h
                    exact False.elim (hd_uv h)
                  · intro h
                    exact False.elim (hcuv h))
              let dB' := dB.relabel σ
              have hy_ne : cA.color ⟨x, hxA⟩ ≠ dB'.color ⟨y, hyB⟩ := by
                intro h
                have hyv : f y = f v := σ.injective (by
                  simpa [dB', KColoring.relabel_color, f, mkF, T, hfv, hσv, hcxv] using h.symm)
                exact fy_ne_fv hyv
              have hz_ne : cA.color ⟨x, hxA⟩ ≠ dB'.color ⟨z, hzB⟩ := by
                intro h
                have hzv : f z = f v := σ.injective (by
                  simpa [dB', KColoring.relabel_color, f, mkF, T, hfv, hσv, hcxv] using h.symm)
                exact fz_ne_fv hzv
              exact glue_cross_avoid_of_separator_pair C cA dB' hxA hyB hzB huS hvS hS_eq
                (by simpa [dB', KColoring.relabel_color] using hσu.symm)
                (by simpa [dB', KColoring.relabel_color] using hσv.symm)
                hy_ne hz_ne
            · have huv_eq : cA.color ⟨u, huA⟩ = cA.color ⟨v, hvA⟩ := by
                by_contra huv_ne
                simp [hcxu, hcxv, huv_ne] at hcAcard
              exact False.elim (hex ⟨cA, hcxu, huv_eq⟩)

private theorem separated_c3_cross_two_left [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyA : y ∈ C.A) (_hyNotB : y ∉ C.B)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hxy : x ≠ y) (_hxz : x ≠ z) (_hyz : y ≠ z) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  let S := C.separator
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by
    have : S.card ≤ 2 := by simpa [S] using C.separator_small
    omega
  rcases hcases with h0 | h1 | h2
  · have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
      intro h
      exact hxy (Subtype.ext_iff.mp h)
    obtain ⟨cA, hxy_ne⟩ := hA.c2 hxyA
    obtain ⟨cB0⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    let img : Finset (Fin m) := {cB0.color ⟨z, hzB⟩}
    have hcard : img.card < m := by
      have hle : img.card ≤ 1 := by simp [img]
      omega
    obtain ⟨σ, hσavoid⟩ := exists_perm_avoid_on_finset img (cA.color ⟨x, hxA⟩) hcard
    let cB := cB0.relabel σ
    have hz_mem : cB0.color ⟨z, hzB⟩ ∈ img := by simp [img]
    have hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
        cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩ := by
      intro w hwA hwB
      have hwS : w ∈ S := C.inter_subset_separator ⟨hwA, hwB⟩
      have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
      simp [S, hSempty] at hwS
    exact glue_left_left_right_avoid C cA cB hxA hyA hzB hzNotA hagree hxy_ne
      (by
        intro h
        exact (hσavoid hz_mem) h.symm)
  · rcases Finset.card_eq_one.mp h1 with ⟨u, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hxuV : x ≠ u := by
      intro h
      subst u
      exact hxNotB huB
    have hyuV : y ≠ u := by
      intro h
      subst u
      exact _hyNotB huB
    have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
      intro h
      exact hxy (Subtype.ext_iff.mp h)
    have hxuA : (⟨x, hxA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact hxuV (Subtype.ext_iff.mp h)
    have hyuA : (⟨y, hyA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact hyuV (Subtype.ext_iff.mp h)
    obtain ⟨cA, hAraw⟩ := hA.c3 hxyA hxuA hyuA
    have hx_ne_y : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨y, hyA⟩ := by
      intro h
      exact hAraw (by simp [h])
    have hx_ne_u : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨u, huA⟩ := by
      intro h
      exact hAraw (by simp [h])
    obtain ⟨cB0⟩ := colorable_of_conditions (G := G.induce C.B) hmpos hB
    let T : Finset V := {u, z}
    let f : V → Fin m := fun t =>
      if ht : t ∈ T then
        cB0.color ⟨t, by
          have ht' : t = u ∨ t = z := by simpa [T] using ht
          rcases ht' with rfl | rfl
          · exact huB
          · exact hzB⟩
      else freshColor hmpos
    have hcard : (T.image f).card < m := by
      have hle : (T.image f).card ≤ T.card := Finset.card_image_le
      have hTle : T.card ≤ 2 := by simpa [T] using card_pair_le_two u z
      omega
    have huT : u ∈ T := by simp [T]
    have hzT : z ∈ T := by simp [T]
    obtain ⟨σ, hσu, _, hσz, _⟩ :=
      exists_relabel_pair_avoid_on_finset T f huT huT hzT hzT
        (u := u) (v := u) (y := z) (z := z)
        (p := cA.color ⟨x, hxA⟩)
        (su := cB0.color ⟨u, huB⟩) (sv := cB0.color ⟨u, huB⟩)
        (tu := cA.color ⟨u, huA⟩) (tv := cA.color ⟨u, huA⟩)
        (by simp [f, T]) (by simp [f, T])
        hx_ne_u hx_ne_u (by simp) hcard
    let cB := cB0.relabel σ
    have hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
        cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩ := by
      refine agree_on_overlap_of_separator C cA cB ?_
      intro w hwS
      have hw_eq : w = u := by simpa [S, hS_eq] using hwS
      subst w
      simpa [cB, KColoring.relabel_color] using hσu.symm
    exact glue_left_left_right_avoid C cA cB hxA hyA hzB hzNotA hagree hx_ne_y
      (by
        intro h
        have h' : σ (f z) = cA.color ⟨x, hxA⟩ := by
          simpa [cB, KColoring.relabel_color, f, T] using h.symm
        exact hσz h')
  · rcases Finset.card_eq_two.mp h2 with ⟨u, v, huvV, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have hvS : v ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hvA : v ∈ C.A := (C.separator_subset_inter hvS).1
    have hvB : v ∈ C.B := (C.separator_subset_inter hvS).2
    have hxuV : x ≠ u := by
      intro h
      subst u
      exact hxNotB huB
    have hyuV : y ≠ u := by
      intro h
      subst u
      exact _hyNotB huB
    have hzvV : z ≠ v := by
      intro h
      subst z
      exact hzNotA hvA
    have hzuV : z ≠ u := by
      intro h
      subst z
      exact hzNotA huA
    have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
      intro h
      exact hxy (Subtype.ext_iff.mp h)
    have hxuA : (⟨x, hxA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact hxuV (Subtype.ext_iff.mp h)
    have hyuA : (⟨y, hyA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact hyuV (Subtype.ext_iff.mp h)
    obtain ⟨aA, haAraw⟩ := hA.c3 hxyA hxuA hyuA
    have ha_xy : aA.color ⟨x, hxA⟩ ≠ aA.color ⟨y, hyA⟩ := by
      intro h
      exact haAraw (by simp [h])
    have ha_xu : aA.color ⟨x, hxA⟩ ≠ aA.color ⟨u, huA⟩ := by
      intro h
      exact haAraw (by simp [h])
    by_cases ha_xv : aA.color ⟨x, hxA⟩ = aA.color ⟨v, hvA⟩
    · have hvuB_ne : (⟨v, hvB⟩ : C.B) ≠ ⟨u, huB⟩ := by
        intro h
        exact huvV (Subtype.ext_iff.mp h).symm
      have hvzB_ne : (⟨v, hvB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hzvV (Subtype.ext_iff.mp h).symm
      have huzB_ne : (⟨u, huB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hzuV (Subtype.ext_iff.mp h).symm
      obtain ⟨bB, hbBraw⟩ := hB.c3
        (x := ⟨v, hvB⟩) (y := ⟨u, huB⟩) (z := ⟨z, hzB⟩)
        hvuB_ne hvzB_ne huzB_ne
      have hb_vu : bB.color ⟨v, hvB⟩ ≠ bB.color ⟨u, huB⟩ := by
        intro h
        exact hbBraw (by simp [h])
      have hb_vz : bB.color ⟨v, hvB⟩ ≠ bB.color ⟨z, hzB⟩ := by
        intro h
        exact hbBraw (by simp [h])
      obtain ⟨σ, hσu, hσv⟩ := exists_perm_map_pair
        (by
          constructor
          · intro h
            exact False.elim (hb_vu h.symm)
          · intro h
            exact False.elim (ha_xu (ha_xv.trans h.symm)))
      let bB' := bB.relabel σ
      have hz_ne : aA.color ⟨x, hxA⟩ ≠ bB'.color ⟨z, hzB⟩ := by
        intro h
        have hzv : bB.color ⟨z, hzB⟩ = bB.color ⟨v, hvB⟩ := σ.injective (by
          simpa [bB', KColoring.relabel_color, ha_xv, hσv] using h.symm)
        exact hb_vz hzv.symm
      exact glue_left_left_right_avoid_of_separator_pair C aA bB' hxA hyA hzB hzNotA
        huS hvS hS_eq
        (by simpa [bB', KColoring.relabel_color] using hσu.symm)
        (by simpa [bB', KColoring.relabel_color] using hσv.symm)
        ha_xy hz_ne
    · obtain ⟨cB, hcu, hcv, hcz⟩ :=
        side_coloring_match_pair_avoid_one (G := G) hm hB huvV huB hvB hzB
          (p := aA.color ⟨x, hxA⟩)
          (tu := aA.color ⟨u, huA⟩) (tv := aA.color ⟨v, hvA⟩)
          ha_xu ha_xv
          (by
            intro huv_eq huvE
            exact aA.valid
              (show (G.induce C.A).Adj ⟨u, huA⟩ ⟨v, hvA⟩ from huvE) huv_eq)
      exact glue_left_left_right_avoid_of_separator_pair C aA cB hxA hyA hzB hzNotA
        huS hvS hS_eq hcu.symm hcv.symm ha_xy hcz.symm

private theorem separated_c3_cross_separator [Fintype V] {m : Nat}
    {G : SimpleGraph V} (_hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hxB : x ∈ C.B)
    (hyA : y ∈ C.A) (hyNotB : y ∉ C.B)
    (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hxy : x ≠ y) (hxz : x ≠ z) (_hyz : y ≠ z) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  let S := C.separator
  have hxS : x ∈ S := C.inter_subset_separator ⟨hxA, hxB⟩
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by
    have : S.card ≤ 2 := by simpa [S] using C.separator_small
    omega
  rcases hcases with h0 | h1 | h2
  · have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
    simp [S, hSempty] at hxS
  · rcases Finset.card_eq_one.mp h1 with ⟨u, hS_eq⟩
    have hx_eq : x = u := by simpa [S, hS_eq] using hxS
    subst u
    have hxyA : (⟨x, hxA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
      intro h
      exact hxy (Subtype.ext_iff.mp h)
    have hxzB : (⟨x, hxB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
      intro h
      exact hxz (Subtype.ext_iff.mp h)
    obtain ⟨cA, hAxy⟩ := hA.c2 hxyA
    obtain ⟨cB0, hBxz⟩ := hB.c2 hxzB
    obtain ⟨σ, hσx⟩ :=
      exists_perm_map_one (cB0.color ⟨x, hxB⟩) (cA.color ⟨x, hxA⟩)
    let cB := cB0.relabel σ
    have hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
        cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩ := by
      refine agree_on_overlap_of_separator C cA cB ?_
      intro w hwS
      have hw_eq : w = x := by simpa [S, hS_eq] using hwS
      subst w
      simpa [cB, KColoring.relabel_color] using hσx.symm
    exact glue_left_left_right_avoid C cA cB hxA hyA hzB hzNotA hagree hAxy
      (by
        intro h
        have hxz_same : cB0.color ⟨x, hxB⟩ = cB0.color ⟨z, hzB⟩ := σ.injective (by
          simpa [cB, KColoring.relabel_color] using hσx.trans h)
        exact hBxz hxz_same)
  · rcases Finset.card_eq_two.mp h2 with ⟨u, v, huvV, hS_eq⟩
    have hxuv : x = u ∨ x = v := by simpa [S, hS_eq] using hxS
    rcases hxuv with hx_eq | hx_eq
    · have huA : u ∈ C.A := by
        simpa [hx_eq] using hxA
      have huB : u ∈ C.B := by
        simpa [hx_eq] using hxB
      have hvS : v ∈ S := by simp [hS_eq]
      have hvA : v ∈ C.A := (C.separator_subset_inter hvS).1
      have hvB : v ∈ C.B := (C.separator_subset_inter hvS).2
      have huyA : (⟨u, huA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
        intro h
        exact hxy (hx_eq.trans (Subtype.ext_iff.mp h))
      have huvA : (⟨u, huA⟩ : C.A) ≠ ⟨v, hvA⟩ := by
        intro h
        exact huvV (Subtype.ext_iff.mp h)
      have hvyA : (⟨v, hvA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
        intro h
        exact hyNotB (by
          have hvy : v = y := Subtype.ext_iff.mp h
          simpa [hvy] using hvB)
      obtain ⟨cA, hAraw⟩ := hA.c3
        (x := ⟨u, huA⟩) (y := ⟨v, hvA⟩) (z := ⟨y, hyA⟩)
        huvA huyA (by
          intro h
          exact hyNotB (by
            have hval : v = y := Subtype.ext_iff.mp h
            simpa [hval] using hvB))
      have hAu_v : cA.color ⟨u, huA⟩ ≠ cA.color ⟨v, hvA⟩ := by
        intro h
        exact hAraw (by simp [h])
      have hAu_y : cA.color ⟨u, huA⟩ ≠ cA.color ⟨y, hyA⟩ := by
        intro h
        exact hAraw (by simp [h])
      have huzB : (⟨u, huB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hxz (hx_eq.trans (Subtype.ext_iff.mp h))
      have huvB : (⟨u, huB⟩ : C.B) ≠ ⟨v, hvB⟩ := by
        intro h
        exact huvV (Subtype.ext_iff.mp h)
      have hvzB : (⟨v, hvB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hzNotA (by
          have hvz : v = z := Subtype.ext_iff.mp h
          simpa [hvz] using hvA)
      obtain ⟨cB0, hBraw⟩ := hB.c3
        (x := ⟨u, huB⟩) (y := ⟨v, hvB⟩) (z := ⟨z, hzB⟩)
        huvB huzB hvzB
      have hBu_v : cB0.color ⟨u, huB⟩ ≠ cB0.color ⟨v, hvB⟩ := by
        intro h
        exact hBraw (by simp [h])
      have hBu_z : cB0.color ⟨u, huB⟩ ≠ cB0.color ⟨z, hzB⟩ := by
        intro h
        exact hBraw (by simp [h])
      obtain ⟨σ, hσu, hσv⟩ := exists_perm_map_pair
        (by
          constructor
          · intro h
            exact False.elim (hBu_v h)
          · intro h
            exact False.elim (hAu_v h))
      let cB := cB0.relabel σ
      have hz_ne : cA.color ⟨u, huA⟩ ≠ cB.color ⟨z, hzB⟩ := by
        intro h
        have hsame : cB0.color ⟨u, huB⟩ = cB0.color ⟨z, hzB⟩ := σ.injective (by
          simpa [cB, KColoring.relabel_color] using hσu.trans h)
        exact hBu_z hsame
      have huS : u ∈ S := by simp [hS_eq]
      have hAx_y : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨y, hyA⟩ := by
        intro h
        exact hAu_y (by simpa [hx_eq] using h)
      have hz_ne_x : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩ := by
        intro h
        exact hz_ne (by simpa [hx_eq] using h)
      exact glue_left_left_right_avoid_of_separator_pair C cA cB hxA hyA hzB hzNotA
        huS hvS hS_eq
        (by simpa [cB, KColoring.relabel_color] using hσu.symm)
        (by simpa [cB, KColoring.relabel_color] using hσv.symm)
        hAx_y hz_ne_x
    · have hvA : v ∈ C.A := by
        simpa [hx_eq] using hxA
      have hvB : v ∈ C.B := by
        simpa [hx_eq] using hxB
      have huS : u ∈ S := by simp [hS_eq]
      have hvS : v ∈ S := by simp [hS_eq]
      have huA : u ∈ C.A := (C.separator_subset_inter huS).1
      have huB : u ∈ C.B := (C.separator_subset_inter huS).2
      have hvyA : (⟨v, hvA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
        intro h
        exact hxy (hx_eq.trans (Subtype.ext_iff.mp h))
      have hvuA : (⟨v, hvA⟩ : C.A) ≠ ⟨u, huA⟩ := by
        intro h
        exact huvV (Subtype.ext_iff.mp h).symm
      have huyA : (⟨u, huA⟩ : C.A) ≠ ⟨y, hyA⟩ := by
        intro h
        exact hyNotB (by
          have huy : u = y := Subtype.ext_iff.mp h
          simpa [huy] using huB)
      obtain ⟨cA, hAraw⟩ := hA.c3
        (x := ⟨v, hvA⟩) (y := ⟨u, huA⟩) (z := ⟨y, hyA⟩)
        hvuA hvyA huyA
      have hAv_u : cA.color ⟨v, hvA⟩ ≠ cA.color ⟨u, huA⟩ := by
        intro h
        exact hAraw (by simp [h])
      have hAv_y : cA.color ⟨v, hvA⟩ ≠ cA.color ⟨y, hyA⟩ := by
        intro h
        exact hAraw (by simp [h])
      have hvzB : (⟨v, hvB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hxz (hx_eq.trans (Subtype.ext_iff.mp h))
      have hvuB : (⟨v, hvB⟩ : C.B) ≠ ⟨u, huB⟩ := by
        intro h
        exact huvV (Subtype.ext_iff.mp h).symm
      have huzB : (⟨u, huB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hzNotA (by
          have huz : u = z := Subtype.ext_iff.mp h
          simpa [huz] using huA)
      obtain ⟨cB0, hBraw⟩ := hB.c3
        (x := ⟨v, hvB⟩) (y := ⟨u, huB⟩) (z := ⟨z, hzB⟩)
        hvuB hvzB huzB
      have hBv_u : cB0.color ⟨v, hvB⟩ ≠ cB0.color ⟨u, huB⟩ := by
        intro h
        exact hBraw (by simp [h])
      have hBv_z : cB0.color ⟨v, hvB⟩ ≠ cB0.color ⟨z, hzB⟩ := by
        intro h
        exact hBraw (by simp [h])
      obtain ⟨σ, hσv, hσu⟩ := exists_perm_map_pair
        (by
          constructor
          · intro h
            exact False.elim (hBv_u h)
          · intro h
            exact False.elim (hAv_u h))
      let cB := cB0.relabel σ
      have hz_ne : cA.color ⟨v, hvA⟩ ≠ cB.color ⟨z, hzB⟩ := by
        intro h
        have hsame : cB0.color ⟨v, hvB⟩ = cB0.color ⟨z, hzB⟩ := σ.injective (by
          simpa [cB, KColoring.relabel_color] using hσv.trans h)
        exact hBv_z hsame
      have hAx_y : cA.color ⟨x, hxA⟩ ≠ cA.color ⟨y, hyA⟩ := by
        intro h
        exact hAv_y (by simpa [hx_eq] using h)
      have hz_ne_x : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩ := by
        intro h
        exact hz_ne (by simpa [hx_eq] using h)
      exact glue_left_left_right_avoid_of_separator_pair C cA cB hxA hyA hzB hzNotA
        huS hvS hS_eq
        (by simpa [cB, KColoring.relabel_color] using hσu.symm)
        (by simpa [cB, KColoring.relabel_color] using hσv.symm)
        hAx_y hz_ne_x

private theorem separated_c3_with_x_left [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m) (hfrag : MFragile m G)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  by_cases hyA : y ∈ C.A
  · by_cases hzA : z ∈ C.A
    · exact separated_c3_left (lt_of_lt_of_le (by decide : 0 < 4) hm)
        C hA hB hxA hyA hzA hxy hxz hyz
    · have hzB : z ∈ C.B := by
        have hzAB : z ∈ C.A ∪ C.B := by simp [C.cover]
        exact hzAB.resolve_left hzA
      by_cases hxB : x ∈ C.B
      · by_cases hyB : y ∈ C.B
        · exact separated_c3_left (lt_of_lt_of_le (by decide : 0 < 4) hm)
            C.symm hB hA hxB hyB hzB hxy hxz hyz
        · exact separated_c3_cross_separator hm C hA hB hxA hxB hyA hyB hzB hzA
            hxy hxz hyz
      · by_cases hyB : y ∈ C.B
        · exact separated_c3_cross_one_left hm hfrag C hA hB hxA hxB hyB hzB
            hxy hxz hyz
        · exact separated_c3_cross_two_left hm C hA hB hxA hxB hyA hyB hzB hzA
            hxy hxz hyz
  · have hyB : y ∈ C.B := by
      have hyAB : y ∈ C.A ∪ C.B := by simp [C.cover]
      exact hyAB.resolve_left hyA
    by_cases hzA : z ∈ C.A
    · by_cases hxB : x ∈ C.B
      · by_cases hzB : z ∈ C.B
        · exact separated_c3_left (lt_of_lt_of_le (by decide : 0 < 4) hm)
            C.symm hB hA hxB hyB hzB hxy hxz hyz
        · obtain ⟨c, hc⟩ :=
            separated_c3_cross_separator hm C hA hB hxA hxB hzA hzB hyB hyA
              hxz hxy hyz.symm
          refine ⟨c, ?_⟩
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm] using hc
      · by_cases hzB : z ∈ C.B
        · exact separated_c3_cross_one_left hm hfrag C hA hB hxA hxB hyB hzB
            hxy hxz hyz
        · obtain ⟨c, hc⟩ :=
            separated_c3_cross_two_left hm C hA hB hxA hxB hzA hzB hyB hyA
              hxz hxy hyz.symm
          refine ⟨c, ?_⟩
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm] using hc
    · have hzB : z ∈ C.B := by
        have hzAB : z ∈ C.A ∪ C.B := by simp [C.cover]
        exact hzAB.resolve_left hzA
      by_cases hxB : x ∈ C.B
      · exact separated_c3_left (lt_of_lt_of_le (by decide : 0 < 4) hm)
          C.symm hB hA hxB hyB hzB hxy hxz hyz
      · exact separated_c3_cross_one_left hm hfrag C hA hB hxA hxB hyB hzB
          hxy hxz hyz

private theorem separated_c3 [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m) (hfrag : MFragile m G)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)) := by
  classical
  by_cases hxA : x ∈ C.A
  · exact separated_c3_with_x_left hm hfrag C hA hB hxA hxy hxz hyz
  · have hxB : x ∈ C.B := by
      have hxAB : x ∈ C.A ∪ C.B := by simp [C.cover]
      exact hxAB.resolve_left hxA
    exact separated_c3_with_x_left hm hfrag C.symm hB hA hxB hxy hxz hyz

omit [DecidableEq V] in
private theorem separated_c2_of_c3 [Fintype V] {m : Nat} {G : SimpleGraph V}
    (hc3 : ∀ ⦃x y z : V⦄, x ≠ y → x ≠ z → y ≠ z →
      ∃ c : KColoring m G,
        c.color x ∉ ({c.color y, c.color z} : Finset (Fin m)))
    {x y : V} (hxy : x ≠ y) (hthird : ∃ z : V, x ≠ z ∧ y ≠ z) :
    ∃ c : KColoring m G, c.color x ≠ c.color y := by
  rcases hthird with ⟨z, hxz, hyz⟩
  obtain ⟨c, hc⟩ := hc3 hxy hxz hyz
  refine ⟨c, ?_⟩
  intro h
  exact hc (by simp [h])

private theorem exists_third_of_card_three [Fintype V] {x y : V}
    (_hxy : x ≠ y) (hcard : 3 ≤ Fintype.card V) :
    ∃ z : V, x ≠ z ∧ y ≠ z := by
  classical
  by_contra hnone
  have hsub : (Finset.univ : Finset V) ⊆ ({x, y} : Finset V) := by
    intro z _hz
    by_contra hznot
    have hxz : x ≠ z := by
      intro hxz
      exact hznot (by simp [hxz])
    have hyz : y ≠ z := by
      intro hyz
      exact hznot (by simp [hyz])
    exact hnone ⟨z, hxz, hyz⟩
  have hle : Fintype.card V ≤ 2 := by
    rw [← Finset.card_univ]
    exact le_trans (Finset.card_le_card hsub) (card_pair_le_two x y)
  omega

private theorem separated_c4_cross_main_small_separator [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G) (hsmall : C.separator.card ≤ 1)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (_hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (_hxy : x ≠ y) (_hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  let S := C.separator
  have hcases : S.card = 0 ∨ S.card = 1 := by
    have : S.card ≤ 1 := by simpa [S] using hsmall
    omega
  rcases hcases with h0 | h1
  · obtain ⟨cA⟩ := colorable_of_conditions (G := G.induce C.A) hmpos hA
    have hyzB : (⟨y, hyB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
      intro h
      exact hyz (Subtype.ext_iff.mp h)
    obtain ⟨cB0, hyz_ne⟩ := hB.c2 hyzB
    obtain ⟨σ, hσz⟩ :=
      exists_perm_map_one (cB0.color ⟨z, hzB⟩) (cA.color ⟨x, hxA⟩)
    let cB := cB0.relabel σ
    have hagree : ∀ ⦃w : V⦄, (hwA : w ∈ C.A) → (hwB : w ∈ C.B) →
        cA.color ⟨w, hwA⟩ = cB.color ⟨w, hwB⟩ := by
      intro w hwA hwB
      have hwS : w ∈ S := C.inter_subset_separator ⟨hwA, hwB⟩
      have hSempty : S = ∅ := Finset.card_eq_zero.mp h0
      simp [S, hSempty] at hwS
    exact glue_cross_image_two_xz C cA cB hxA hyB hzB hzNotA hagree
      (by simpa [cB, KColoring.relabel_color] using hσz.symm)
      (by
        intro h
        have hsame : cB0.color ⟨z, hzB⟩ = cB0.color ⟨y, hyB⟩ := σ.injective (by
          exact hσz.trans h)
        exact hyz_ne hsame.symm)
  · rcases Finset.card_eq_one.mp h1 with ⟨u, hS_eq⟩
    have huS : u ∈ S := by simp [hS_eq]
    have huA : u ∈ C.A := (C.separator_subset_inter huS).1
    have huB : u ∈ C.B := (C.separator_subset_inter huS).2
    have hxuA : (⟨x, hxA⟩ : C.A) ≠ ⟨u, huA⟩ := by
      intro h
      exact _hxNotB (by
        have hxu : x = u := Subtype.ext_iff.mp h
        simpa [hxu] using huB)
    obtain ⟨cA, hxu_ne⟩ := hA.c2 hxuA
    by_cases hyu : y = u
    · subst y
      have huzB : (⟨u, huB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
        intro h
        exact hyz (Subtype.ext_iff.mp h)
      obtain ⟨cB0, huz_ne⟩ := hB.c2 huzB
      obtain ⟨σ, hσu, hσz⟩ := exists_perm_map_pair
        (a₁ := cB0.color ⟨u, huB⟩) (a₂ := cB0.color ⟨z, hzB⟩)
        (b₁ := cA.color ⟨u, huA⟩) (b₂ := cA.color ⟨x, hxA⟩)
        (by
          constructor
          · intro h
            exact False.elim (huz_ne h)
          · intro h
            exact False.elim (hxu_ne h.symm))
      let cB := cB0.relabel σ
      exact glue_cross_image_two_xz C cA cB hxA huB hzB hzNotA
        (agree_on_overlap_of_separator C cA cB (by
          intro w hwS
          have hw_eq : w = u := by simpa [S, hS_eq] using hwS
          subst w
          simpa [cB, KColoring.relabel_color] using hσu.symm))
        (by simpa [cB, KColoring.relabel_color] using hσz.symm)
        (by
          intro h
          exact hxu_ne (h.trans hσu))
    · have hyuB : (⟨y, hyB⟩ : C.B) ≠ ⟨u, huB⟩ := by
        intro h
        exact hyu (Subtype.ext_iff.mp h)
      have hzuB : (⟨z, hzB⟩ : C.B) ≠ ⟨u, huB⟩ := by
        intro h
        exact hzNotA (by
          have hzu : z = u := Subtype.ext_iff.mp h
          simpa [hzu] using huA)
      have hzyB : (⟨z, hzB⟩ : C.B) ≠ ⟨y, hyB⟩ := by
        intro h
        exact hyz (Subtype.ext_iff.mp h).symm
      obtain ⟨cB0, hBraw⟩ := hB.c3
        (x := ⟨z, hzB⟩) (y := ⟨u, huB⟩) (z := ⟨y, hyB⟩)
        hzuB hzyB hyuB.symm
      have hz_ne_u : cB0.color ⟨z, hzB⟩ ≠ cB0.color ⟨u, huB⟩ := by
        intro h
        exact hBraw (by simp [h])
      have hz_ne_y : cB0.color ⟨z, hzB⟩ ≠ cB0.color ⟨y, hyB⟩ := by
        intro h
        exact hBraw (by simp [h])
      obtain ⟨σ, hσz, hσu⟩ := exists_perm_map_pair
        (a₁ := cB0.color ⟨z, hzB⟩) (a₂ := cB0.color ⟨u, huB⟩)
        (b₁ := cA.color ⟨x, hxA⟩) (b₂ := cA.color ⟨u, huA⟩)
        (by
          constructor
          · intro h
            exact False.elim (hz_ne_u h)
          · intro h
            exact False.elim (hxu_ne h))
      let cB := cB0.relabel σ
      exact glue_cross_image_two_xz C cA cB hxA hyB hzB hzNotA
        (agree_on_overlap_of_separator C cA cB (by
          intro w hwS
          have hw_eq : w = u := by simpa [S, hS_eq] using hwS
          subst w
          simpa [cB, KColoring.relabel_color] using hσu.symm))
        (by simpa [cB, KColoring.relabel_color] using hσz.symm)
        (by
          intro h
          have hsame : cB0.color ⟨z, hzB⟩ = cB0.color ⟨y, hyB⟩ := σ.injective (by
            simpa [cB, KColoring.relabel_color] using hσz.trans h)
          exact hz_ne_y hsame)

private theorem separated_c4_cross_main_sep2_edge_oriented [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z s t : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hsS : s ∈ C.separator) (htS : t ∈ C.separator)
    (hS_eq : C.separator = {s, t}) (hst : s ≠ t) (hstE : G.Adj s t)
    (hys : y ≠ s) (_hxy : x ≠ y) (_hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  have hsA : s ∈ C.A := (C.separator_subset_inter hsS).1
  have hsB : s ∈ C.B := (C.separator_subset_inter hsS).2
  have htA : t ∈ C.A := (C.separator_subset_inter htS).1
  have htB : t ∈ C.B := (C.separator_subset_inter htS).2
  have hxs : x ≠ s := by
    intro h
    subst s
    exact hxNotB hsB
  have hxt : x ≠ t := by
    intro h
    subst t
    exact hxNotB htB
  have hzs : z ≠ s := by
    intro h
    subst s
    exact hzNotA hsA
  have hstB : (⟨s, hsB⟩ : C.B) ≠ ⟨t, htB⟩ := by
    intro h
    exact hst (Subtype.ext_iff.mp h)
  have hsyB : (⟨s, hsB⟩ : C.B) ≠ ⟨y, hyB⟩ := by
    intro h
    exact hys (Subtype.ext_iff.mp h).symm
  have hszB : (⟨s, hsB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
    intro h
    exact hzs (Subtype.ext_iff.mp h).symm
  have hyzB : (⟨y, hyB⟩ : C.B) ≠ ⟨z, hzB⟩ := by
    intro h
    exact hyz (Subtype.ext_iff.mp h)
  obtain ⟨cB, hBraw⟩ := hB.c3
    (x := ⟨s, hsB⟩) (y := ⟨y, hyB⟩) (z := ⟨z, hzB⟩)
    hsyB hszB hyzB
  have hBs_y : cB.color ⟨s, hsB⟩ ≠ cB.color ⟨y, hyB⟩ := by
    intro h
    exact hBraw (by simp [h])
  have hBs_z : cB.color ⟨s, hsB⟩ ≠ cB.color ⟨z, hzB⟩ := by
    intro h
    exact hBraw (by simp [h])
  have hBs_t : cB.color ⟨s, hsB⟩ ≠ cB.color ⟨t, htB⟩ :=
    cB.valid (show (G.induce C.B).Adj ⟨s, hsB⟩ ⟨t, htB⟩ from hstE)
  obtain ⟨p, hp_s, hp_t, hp_card⟩ :=
    exists_color_for_c4_edge hm hBs_t hBs_y hBs_z
  have hxsA : (⟨x, hxA⟩ : C.A) ≠ ⟨s, hsA⟩ := by
    intro h
    exact hxs (Subtype.ext_iff.mp h)
  have hxtA : (⟨x, hxA⟩ : C.A) ≠ ⟨t, htA⟩ := by
    intro h
    exact hxt (Subtype.ext_iff.mp h)
  have hstA : (⟨s, hsA⟩ : C.A) ≠ ⟨t, htA⟩ := by
    intro h
    exact hst (Subtype.ext_iff.mp h)
  obtain ⟨cA0, hAraw⟩ := hA.c3 hxsA hxtA hstA
  have hAx_s : cA0.color ⟨x, hxA⟩ ≠ cA0.color ⟨s, hsA⟩ := by
    intro h
    exact hAraw (by simp [h])
  have hAx_t : cA0.color ⟨x, hxA⟩ ≠ cA0.color ⟨t, htA⟩ := by
    intro h
    exact hAraw (by simp [h])
  have hAs_t : cA0.color ⟨s, hsA⟩ ≠ cA0.color ⟨t, htA⟩ :=
    cA0.valid (show (G.induce C.A).Adj ⟨s, hsA⟩ ⟨t, htA⟩ from hstE)
  obtain ⟨σ, hσx, hσs, hσt⟩ := exists_perm_map_triple
    (by
      constructor
      · intro h
        exact False.elim (hAx_s h)
      · intro h
        exact False.elim (hp_s h))
    (by
      constructor
      · intro h
        exact False.elim (hAx_t h)
      · intro h
        exact False.elim (hp_t h))
    (by
      constructor
      · intro h
        exact False.elim (hAs_t h)
      · intro h
        exact False.elim (hBs_t h))
  let cA := cA0.relabel σ
  exact glue_cross_image_two_of_colors C cA cB hxA hyB hzB hzNotA
    (agree_on_overlap_of_separator C cA cB (by
      intro w hwS
      have hwst : w = s ∨ w = t := by simpa [hS_eq] using hwS
      rcases hwst with rfl | rfl
      · simpa [cA, KColoring.relabel_color] using hσs
      · simpa [cA, KColoring.relabel_color] using hσt))
    (by simpa [cA, KColoring.relabel_color, hσx] using hp_card)

private theorem separated_c4_cross_main_sep2_nonedge_oriented [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z s t : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hsS : s ∈ C.separator) (htS : t ∈ C.separator)
    (hS_eq : C.separator = {s, t}) (hst : s ≠ t) (hnstE : ¬ G.Adj s t)
    (hys : y ≠ s) (_hxy : x ≠ y) (_hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  have hsA : s ∈ C.A := (C.separator_subset_inter hsS).1
  have hsB : s ∈ C.B := (C.separator_subset_inter hsS).2
  have htA : t ∈ C.A := (C.separator_subset_inter htS).1
  have htB : t ∈ C.B := (C.separator_subset_inter htS).2
  have hxs : x ≠ s := by
    intro h
    subst s
    exact hxNotB hsB
  have hxt : x ≠ t := by
    intro h
    subst t
    exact hxNotB htB
  have hzs : z ≠ s := by
    intro h
    subst s
    exact hzNotA hsA
  have hzt : z ≠ t := by
    intro h
    subst t
    exact hzNotA htA
  have hnstB : ¬ (G.induce C.B).Adj ⟨s, hsB⟩ ⟨t, htB⟩ := by
    intro h
    exact hnstE h
  by_cases hex :
      ∃ cA : KColoring m (G.induce C.A),
        cA.color ⟨x, hxA⟩ ≠ cA.color ⟨s, hsA⟩ ∧
          cA.color ⟨s, hsA⟩ = cA.color ⟨t, htA⟩
  · rcases hex with ⟨cA, hx_ne_s, hs_eq_t_A⟩
    obtain ⟨cB0, hs_eq_t_B⟩ := hB.c1 hnstB
    let T : Finset V := {s, t, y, z}
    let f : V → Fin m := fun w =>
      if hw : w ∈ T then
        cB0.color ⟨w, by
          have hw' : w = s ∨ w = t ∨ w = y ∨ w = z := by simpa [T] using hw
          rcases hw' with rfl | rfl | rfl | rfl
          · exact hsB
          · exact htB
          · exact hyB
          · exact hzB⟩
      else freshColor hmpos
    have hsT : s ∈ T := by simp [T]
    have htT : t ∈ T := by simp [T]
    have hyT : y ∈ T := by simp [T]
    have hzT : z ∈ T := by simp [T]
    have hfs : f s = cB0.color ⟨s, hsB⟩ := by simp [f, T]
    have hft : f t = cB0.color ⟨t, htB⟩ := by simp [f, T]
    have hTcard : T.card ≤ 4 := by simpa [T] using card_quad_le_four s t y z
    have himg_lt : (T.image f).card < m := by
      have himg_lt_T : (T.image f).card < T.card := by
        refine card_image_lt_of_pair_eq T f hsT htT hst ?_
        simp [f, T, hs_eq_t_B]
      omega
    by_cases hyz_col : cB0.color ⟨y, hyB⟩ = cB0.color ⟨z, hzB⟩
    · obtain ⟨σ, hσs, hσt, hσy, hσz⟩ :=
        exists_relabel_pair_avoid_on_finset T f hsT htT hyT hzT
          (u := s) (v := t) (y := y) (z := z)
          (p := cA.color ⟨x, hxA⟩)
          (su := cB0.color ⟨s, hsB⟩) (sv := cB0.color ⟨t, htB⟩)
          (tu := cA.color ⟨s, hsA⟩) (tv := cA.color ⟨t, htA⟩)
          hfs hft hx_ne_s (by simpa [hs_eq_t_A] using hx_ne_s)
          (by simp [hs_eq_t_B, hs_eq_t_A]) himg_lt
      let cB := cB0.relabel σ
      have hcard :
          ({cA.color ⟨x, hxA⟩, cB.color ⟨y, hyB⟩, cB.color ⟨z, hzB⟩} :
            Finset (Fin m)).card = 2 := by
        have hy_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨y, hyB⟩ := by
          intro h
          have h' : σ (f y) = cA.color ⟨x, hxA⟩ := by
            simpa [cB, KColoring.relabel_color, f, T] using h.symm
          exact hσy h'
        have hyz_eq' : cB.color ⟨y, hyB⟩ = cB.color ⟨z, hzB⟩ := by
          simp [cB, KColoring.relabel_color, hyz_col]
        exact color_card_two_of_yz_eq hyz_eq' hy_ne
      exact glue_cross_image_two_of_colors C cA cB hxA hyB hzB hzNotA
        (agree_on_overlap_of_separator C cA cB (by
          intro w hwS
          have hwst : w = s ∨ w = t := by simpa [hS_eq] using hwS
          rcases hwst with rfl | rfl
          · simpa [cB, KColoring.relabel_color] using hσs.symm
          · simpa [cB, KColoring.relabel_color] using hσt.symm))
        hcard
    · by_cases hy_s_col : cB0.color ⟨y, hyB⟩ = cB0.color ⟨s, hsB⟩
      · obtain ⟨σ, hσs, hσz⟩ := exists_perm_map_pair
          (a₁ := cB0.color ⟨s, hsB⟩) (a₂ := cB0.color ⟨z, hzB⟩)
          (b₁ := cA.color ⟨s, hsA⟩) (b₂ := cA.color ⟨x, hxA⟩)
          (by
            constructor
            · intro h
              exact False.elim (hyz_col (hy_s_col.trans h))
            · intro h
              exact False.elim (hx_ne_s h.symm))
        let cB := cB0.relabel σ
        have hcard :
            ({cA.color ⟨x, hxA⟩, cB.color ⟨y, hyB⟩, cB.color ⟨z, hzB⟩} :
              Finset (Fin m)).card = 2 := by
          have hy_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨y, hyB⟩ := by
            intro h
            have hy_eq_s : cB.color ⟨y, hyB⟩ = cA.color ⟨s, hsA⟩ := by
              simpa [cB, KColoring.relabel_color, hy_s_col] using hσs
            exact hx_ne_s (h.trans hy_eq_s)
          have hz_eq : cA.color ⟨x, hxA⟩ = cB.color ⟨z, hzB⟩ := by
            simpa [cB, KColoring.relabel_color] using hσz.symm
          exact color_card_two_of_xz_eq hz_eq hy_ne
        have hσt : σ (cB0.color ⟨t, htB⟩) = cA.color ⟨t, htA⟩ := by
          simpa [hs_eq_t_B, hs_eq_t_A] using hσs
        exact glue_cross_image_two_of_colors C cA cB hxA hyB hzB hzNotA
          (agree_on_overlap_of_separator C cA cB (by
            intro w hwS
            have hwst : w = s ∨ w = t := by simpa [hS_eq] using hwS
            rcases hwst with rfl | rfl
            · simpa [cB, KColoring.relabel_color] using hσs.symm
            · simpa [cB, KColoring.relabel_color] using hσt.symm))
          hcard
      · obtain ⟨σ, hσs, hσy⟩ := exists_perm_map_pair
          (a₁ := cB0.color ⟨s, hsB⟩) (a₂ := cB0.color ⟨y, hyB⟩)
          (b₁ := cA.color ⟨s, hsA⟩) (b₂ := cA.color ⟨x, hxA⟩)
          (by
            constructor
            · intro h
              exact False.elim (hy_s_col h.symm)
            · intro h
              exact False.elim (hx_ne_s h.symm))
        let cB := cB0.relabel σ
        have hcard :
            ({cA.color ⟨x, hxA⟩, cB.color ⟨y, hyB⟩, cB.color ⟨z, hzB⟩} :
              Finset (Fin m)).card = 2 := by
          have hy_eq : cA.color ⟨x, hxA⟩ = cB.color ⟨y, hyB⟩ := by
            simpa [cB, KColoring.relabel_color] using hσy.symm
          have hz_ne : cA.color ⟨x, hxA⟩ ≠ cB.color ⟨z, hzB⟩ := by
            intro h
            have hsame : cB0.color ⟨y, hyB⟩ = cB0.color ⟨z, hzB⟩ := σ.injective (by
              simpa [cB, KColoring.relabel_color] using hσy.trans h)
            exact hyz_col hsame
          exact color_card_two_of_xy_eq hy_eq hz_ne
        have hσt : σ (cB0.color ⟨t, htB⟩) = cA.color ⟨t, htA⟩ := by
          simpa [hs_eq_t_B, hs_eq_t_A] using hσs
        exact glue_cross_image_two_of_colors C cA cB hxA hyB hzB hzNotA
          (agree_on_overlap_of_separator C cA cB (by
            intro w hwS
            have hwst : w = s ∨ w = t := by simpa [hS_eq] using hwS
            rcases hwst with rfl | rfl
            · simpa [cB, KColoring.relabel_color] using hσs.symm
            · simpa [cB, KColoring.relabel_color] using hσt.symm))
          hcard
  · have hxsA : (⟨x, hxA⟩ : C.A) ≠ ⟨s, hsA⟩ := by
      intro h
      exact hxs (Subtype.ext_iff.mp h)
    have hxtA : (⟨x, hxA⟩ : C.A) ≠ ⟨t, htA⟩ := by
      intro h
      exact hxt (Subtype.ext_iff.mp h)
    have hstA : (⟨s, hsA⟩ : C.A) ≠ ⟨t, htA⟩ := by
      intro h
      exact hst (Subtype.ext_iff.mp h)
    obtain ⟨bA0, hBleftRaw⟩ := hA.c3 hxsA hxtA hstA
    have hb_xs : bA0.color ⟨x, hxA⟩ ≠ bA0.color ⟨s, hsA⟩ := by
      intro h
      exact hBleftRaw (by simp [h])
    have hb_xt : bA0.color ⟨x, hxA⟩ ≠ bA0.color ⟨t, htA⟩ := by
      intro h
      exact hBleftRaw (by simp [h])
    have hb_st : bA0.color ⟨s, hsA⟩ ≠ bA0.color ⟨t, htA⟩ := by
      intro h
      exact hex ⟨bA0, hb_xs, h⟩
    have hnot_triangle :
        ¬ ((G.induce C.A).Adj ⟨x, hxA⟩ ⟨s, hsA⟩ ∧
          (G.induce C.A).Adj ⟨x, hxA⟩ ⟨t, htA⟩ ∧
          (G.induce C.A).Adj ⟨s, hsA⟩ ⟨t, htA⟩) := by
      rintro ⟨_, _, hstAedge⟩
      exact hnstE hstAedge
    obtain ⟨cA0, hcAcard⟩ := hA.c4 hxsA hxtA hstA hnot_triangle
    have hc_st : cA0.color ⟨s, hsA⟩ ≠ cA0.color ⟨t, htA⟩ := by
      intro hst_eq
      by_cases hx_s : cA0.color ⟨x, hxA⟩ = cA0.color ⟨s, hsA⟩
      · have hx_t : cA0.color ⟨x, hxA⟩ = cA0.color ⟨t, htA⟩ := hx_s.trans hst_eq
        have hcard1 :
            ({cA0.color ⟨x, hxA⟩, cA0.color ⟨s, hsA⟩, cA0.color ⟨t, htA⟩} :
              Finset (Fin m)).card = 1 := by
          simp [hx_s, hst_eq]
        have hcard2 :
            ({cA0.color ⟨x, hxA⟩, cA0.color ⟨s, hsA⟩, cA0.color ⟨t, htA⟩} :
              Finset (Fin m)).card = 2 := by
          simpa using hcAcard
        omega
      · exact hex ⟨cA0, hx_s, hst_eq⟩
    have hx_eq_s_or_t :
        cA0.color ⟨x, hxA⟩ = cA0.color ⟨s, hsA⟩ ∨
          cA0.color ⟨x, hxA⟩ = cA0.color ⟨t, htA⟩ := by
      exact color_eq_left_or_right_of_card_two hc_st (by simpa using hcAcard)
    have hstB : (⟨s, hsB⟩ : C.B) ≠ ⟨t, htB⟩ := by
      intro h
      exact hst (Subtype.ext_iff.mp h)
    obtain ⟨dB, hd_st⟩ := hB.c2 hstB
    let cu := dB.color ⟨s, hsB⟩
    let cv := dB.color ⟨t, htB⟩
    let cy := dB.color ⟨y, hyB⟩
    let cz := dB.color ⟨z, hzB⟩
    by_cases hpair : (cy = cu ∧ cz = cv) ∨ (cy = cv ∧ cz = cu)
    · obtain ⟨σ, hσs, hσt⟩ := exists_perm_map_pair
        (a₁ := cA0.color ⟨s, hsA⟩) (a₂ := cA0.color ⟨t, htA⟩)
        (b₁ := cu) (b₂ := cv)
        (by
          constructor
          · intro h
            exact False.elim (hc_st h)
          · intro h
            exact False.elim (hd_st h))
      let cA := cA0.relabel σ
      have hx_boundary :
          cA.color ⟨x, hxA⟩ = cu ∨ cA.color ⟨x, hxA⟩ = cv := by
        rcases hx_eq_s_or_t with hx_s | hx_t
        · left
          simpa [cA, KColoring.relabel_color, hx_s] using hσs
        · right
          simpa [cA, KColoring.relabel_color, hx_t] using hσt
      have hcard :
          ({cA.color ⟨x, hxA⟩, dB.color ⟨y, hyB⟩, dB.color ⟨z, hzB⟩} :
            Finset (Fin m)).card = 2 := by
        rcases hpair with ⟨hy, hz⟩ | ⟨hy, hz⟩ <;> rcases hx_boundary with hxcu | hxcv
        · simpa [cu, cv, cy, cz, hy, hz, hxcu] using
            (color_pair_card_two (α := Fin m) (by simpa [cu, cv] using hd_st))
        · simpa [cu, cv, cy, cz, hy, hz, hxcv] using
            (color_pair_card_two (α := Fin m) (by simpa [cu, cv] using hd_st))
        · simpa [cu, cv, cy, cz, hy, hz, hxcu] using
            (color_pair_card_two (α := Fin m) (by simpa [cu, cv] using hd_st.symm))
        · simpa [cu, cv, cy, cz, hy, hz, hxcv] using
            (color_pair_card_two (α := Fin m) (by simpa [cu, cv] using hd_st.symm))
      exact glue_cross_image_two_of_colors C cA dB hxA hyB hzB hzNotA
        (agree_on_overlap_of_separator C cA dB (by
          intro w hwS
          have hwst : w = s ∨ w = t := by simpa [hS_eq] using hwS
          rcases hwst with rfl | rfl
          · simpa [cA, KColoring.relabel_color, cu] using hσs
          · simpa [cA, KColoring.relabel_color, cv] using hσt))
        hcard
    · obtain ⟨p, hp_s, hp_t, hp_card⟩ :=
        exists_color_for_c4_nonedge hm (by simpa [cu, cv] using hd_st) hpair
      obtain ⟨σ, hσx, hσs, hσt⟩ := exists_perm_map_triple
        (by
          constructor
          · intro h
            exact False.elim (hb_xs h)
          · intro h
            exact False.elim (hp_s h))
        (by
          constructor
          · intro h
            exact False.elim (hb_xt h)
          · intro h
            exact False.elim (hp_t h))
        (by
          constructor
          · intro h
            exact False.elim (hb_st h)
          · intro h
            exact False.elim (hd_st h))
      let bA := bA0.relabel σ
      exact glue_cross_image_two_of_colors C bA dB hxA hyB hzB hzNotA
        (agree_on_overlap_of_separator C bA dB (by
          intro w hwS
          have hwst : w = s ∨ w = t := by simpa [hS_eq] using hwS
          rcases hwst with rfl | rfl
          · simpa [bA, KColoring.relabel_color, cu] using hσs
          · simpa [bA, KColoring.relabel_color, cv] using hσt))
        (by simpa [bA, KColoring.relabel_color, hσx, cu, cv, cy, cz] using hp_card)

private theorem triple_image_card_of_finset_eq {α : Type*} [DecidableEq α]
    {a b c x y z : V} (f : V → α)
    (hset : ({a, b, c} : Finset V) = ({x, y, z} : Finset V))
    (hcard : (({a, b, c} : Finset V).image f).card = 2) :
    (({x, y, z} : Finset V).image f).card = 2 := by
  simpa [← hset] using hcard

private theorem separated_c4_cross_main_sep2 [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z u v : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (huS : u ∈ C.separator) (hvS : v ∈ C.separator)
    (hS_eq : C.separator = {u, v}) (huv : u ≠ v)
    (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  by_cases huvE : G.Adj u v
  · by_cases hyu : y = u
    · subst y
      have hS_swap : C.separator = ({v, u} : Finset V) := by
        rw [hS_eq]
        ext w
        simp [or_comm]
      exact separated_c4_cross_main_sep2_edge_oriented hm C hA hB
        hxA hxNotB hyB hzB hzNotA hvS huS hS_swap huv.symm huvE.symm
        (by simpa using huv) _hxy hxz hyz
    · exact separated_c4_cross_main_sep2_edge_oriented hm C hA hB
        hxA hxNotB hyB hzB hzNotA huS hvS hS_eq huv huvE hyu _hxy hxz hyz
  · by_cases hyu : y = u
    · subst y
      have hS_swap : C.separator = ({v, u} : Finset V) := by
        rw [hS_eq]
        ext w
        simp [or_comm]
      have hnvu : ¬ G.Adj v u := by
        intro h
        exact huvE h.symm
      exact separated_c4_cross_main_sep2_nonedge_oriented hm C hA hB
        hxA hxNotB hyB hzB hzNotA hvS huS hS_swap huv.symm hnvu
        (by simpa using huv) _hxy hxz hyz
    · exact separated_c4_cross_main_sep2_nonedge_oriented hm C hA hB
        hxA hxNotB hyB hzB hzNotA huS hvS hS_eq huv huvE hyu _hxy hxz hyz

private theorem separated_c4_cross_main [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A) (hxNotB : x ∉ C.B)
    (hyB : y ∈ C.B) (hzB : z ∈ C.B) (hzNotA : z ∉ C.A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  by_cases hsmall : C.separator.card ≤ 1
  · exact separated_c4_cross_main_small_separator hm C hsmall hA hB
      hxA hxNotB hyB hzB hzNotA hxy hxz hyz
  · have hle : C.separator.card ≤ 2 := C.separator_small
    have hcard : C.separator.card = 2 := by
      omega
    rcases Finset.card_eq_two.mp hcard with ⟨u, v, huv, hS_eq⟩
    have huS : u ∈ C.separator := by simp [hS_eq]
    have hvS : v ∈ C.separator := by simp [hS_eq]
    exact separated_c4_cross_main_sep2 hm C hA hB
      hxA hxNotB hyB hzB hzNotA huS hvS hS_eq huv hxy hxz hyz

private theorem separated_c4_with_x_left [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxA : x ∈ C.A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnot_triangle : ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z)) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  by_cases hyA : y ∈ C.A
  · by_cases hzA : z ∈ C.A
    · exact separated_c4_left hmpos C hA hB hxA hyA hzA hxy hxz hyz hnot_triangle
    · have hzB : z ∈ C.B := by
        have hzAB : z ∈ C.A ∪ C.B := by simp [C.cover]
        exact hzAB.resolve_left hzA
      by_cases hxB : x ∈ C.B
      · by_cases hyB : y ∈ C.B
        · exact separated_c4_left hmpos C.symm hB hA hxB hyB hzB hxy hxz hyz
            hnot_triangle
        · obtain ⟨c, hc⟩ :=
            separated_c4_cross_main hm C.symm hB hA
              hzB hzA hxA hyA hyB hxz.symm hyz.symm hxy
          refine ⟨c, ?_⟩
          exact triple_image_card_of_finset_eq c.color
            (by ext w; simp [or_comm, or_left_comm]) hc
      · by_cases hyB : y ∈ C.B
        · exact separated_c4_cross_main hm C hA hB
            hxA hxB hyB hzB hzA hxy hxz hyz
        · obtain ⟨c, hc⟩ :=
            separated_c4_cross_main hm C.symm hB hA
              hzB hzA hxA hyA hyB hxz.symm hyz.symm hxy
          refine ⟨c, ?_⟩
          exact triple_image_card_of_finset_eq c.color
            (by ext w; simp [or_comm, or_left_comm]) hc
  · have hyB : y ∈ C.B := by
      have hyAB : y ∈ C.A ∪ C.B := by simp [C.cover]
      exact hyAB.resolve_left hyA
    by_cases hzA : z ∈ C.A
    · by_cases hxB : x ∈ C.B
      · by_cases hzB : z ∈ C.B
        · exact separated_c4_left hmpos C.symm hB hA hxB hyB hzB hxy hxz hyz
            hnot_triangle
        · obtain ⟨c, hc⟩ :=
            separated_c4_cross_main hm C hA hB
              hzA hzB hxB hyB hyA hxz.symm hyz.symm hxy
          refine ⟨c, ?_⟩
          exact triple_image_card_of_finset_eq c.color
            (by ext w; simp [or_comm, or_left_comm]) hc
      · by_cases hzB : z ∈ C.B
        · obtain ⟨c, hc⟩ :=
            separated_c4_cross_main hm C hA hB
              hxA hxB hzB hyB hyA hxz hxy hyz.symm
          refine ⟨c, ?_⟩
          exact triple_image_card_of_finset_eq c.color
            (by ext w; simp [or_comm]) hc
        · obtain ⟨c, hc⟩ :=
            separated_c4_cross_main hm C.symm hB hA
              hyB hyA hxA hzA hzB hxy.symm hyz hxz
          refine ⟨c, ?_⟩
          exact triple_image_card_of_finset_eq c.color
            (by ext w; simp [or_left_comm]) hc
    · have hzB : z ∈ C.B := by
        have hzAB : z ∈ C.A ∪ C.B := by simp [C.cover]
        exact hzAB.resolve_left hzA
      by_cases hxB : x ∈ C.B
      · exact separated_c4_left hmpos C.symm hB hA hxB hyB hzB hxy hxz hyz
          hnot_triangle
      · exact separated_c4_cross_main hm C hA hB
          hxA hxB hyB hzB hzA hxy hxz hyz

private theorem separated_c4 [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnot_triangle : ¬ (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z)) :
    ∃ c : KColoring m G,
      (({x, y, z} : Finset V).image c.color).card = 2 := by
  classical
  by_cases hxA : x ∈ C.A
  · exact separated_c4_with_x_left hm C hA hB hxA hxy hxz hyz hnot_triangle
  · have hxB : x ∈ C.B := by
      have hxAB : x ∈ C.A ∪ C.B := by simp [C.cover]
      exact hxAB.resolve_left hxA
    exact separated_c4_with_x_left hm C.symm hB hA hxB hxy hxz hyz hnot_triangle

/--
If $G$ is $(m - 1)$-colorable and $m ≥ 4$, then $G$ satisfies all 4
Theorem 3 extension conditions.  This is the paper's 3-connected case once
$m$-fragility supplies the $(m - 1)$-coloring.
-/
theorem conditions_of_colorable_pred {m : Nat} (hm : 4 ≤ m)
    (hc : KColorable (m - 1) G) :
    T3Conditions m G := by
  classical
  obtain ⟨c⟩ := hc
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  refine ⟨?c1, ?c2, ?c3, ?c4⟩
  · intro x y hnxy
    by_cases hxy : x = y
    · let d := KColoring.recolorIndependent hmpos c ({x} : Finset V) singleton_independent
      refine ⟨d, ?_⟩
      subst y
      rfl
    · let d := KColoring.recolorIndependent hmpos c ({x, y} : Finset V)
        (pair_independent (G := G) hnxy)
      refine ⟨d, ?_⟩
      simp [d, KColoring.recolorIndependent]
  · intro x y hxy
    let d := KColoring.recolorIndependent hmpos c ({x} : Finset V) singleton_independent
    refine ⟨d, ?_⟩
    have hne : freshColor hmpos ≠ embedOldColor hmpos (c.color y) :=
      (embedOldColor_ne_fresh hmpos (c.color y)).symm
    simp [d, KColoring.recolorIndependent, hxy.symm, hne]
  · intro x y z hxy hxz hyz
    let d := KColoring.recolorIndependent hmpos c ({x} : Finset V) singleton_independent
    refine ⟨d, ?_⟩
    have hney : freshColor hmpos ≠ embedOldColor hmpos (c.color y) :=
      (embedOldColor_ne_fresh hmpos (c.color y)).symm
    have hnez : freshColor hmpos ≠ embedOldColor hmpos (c.color z) :=
      (embedOldColor_ne_fresh hmpos (c.color z)).symm
    simp [d, KColoring.recolorIndependent, hxy.symm, hxz.symm, hney, hnez]
  · intro x y z hxy hxz hyz hnot_triangle
    by_cases hxy_edge : G.Adj x y
    · by_cases hxz_edge : G.Adj x z
      · have hyz_nonedge : ¬ G.Adj y z := by
          intro hyz_edge
          exact hnot_triangle ⟨hxy_edge, hxz_edge, hyz_edge⟩
        let d := KColoring.recolorIndependent hmpos c ({y, z} : Finset V)
          (pair_independent (G := G) hyz_nonedge)
        refine ⟨d, ?_⟩
        exact image_pair_yz hmpos c hxy hxz (pair_independent (G := G) hyz_nonedge)
      · let d := KColoring.recolorIndependent hmpos c ({x, z} : Finset V)
          (pair_independent (G := G) hxz_edge)
        refine ⟨d, ?_⟩
        exact image_pair_xz hmpos c hxy hyz (pair_independent (G := G) hxz_edge)
    · let d := KColoring.recolorIndependent hmpos c ({x, y} : Finset V)
        (pair_independent (G := G) hxy_edge)
      refine ⟨d, ?_⟩
      exact image_pair_xy hmpos c hxz hyz (pair_independent (G := G) hxy_edge)

/--
The 3-connected branch of the induction, assuming the top subgraph has already
been identified as 3-connected.
-/
theorem conditions_of_fragile_three_connected {m : Nat} [Fintype V]
    (hm : 4 ≤ m) (hfrag : MFragile m G)
    (htop : ThreeConnected (⊤ : G.Subgraph).coe) :
    T3Conditions m G := by
  obtain ⟨c⟩ := hfrag (⊤ : G.Subgraph) htop
  exact conditions_of_colorable_pred (G := G) hm ⟨KColoring.ofTopCoe c⟩

/-- The paper's 3-connected induction branch. -/
theorem conditions_of_fragile_connected {m : Nat} [Fintype V]
    (hm : 4 ≤ m) (hfrag : MFragile m G) (hconn : ThreeConnected G) :
    T3Conditions m G :=
  conditions_of_fragile_three_connected (G := G) hm hfrag (threeConnected_topCoe hconn)

/-- Small graphs satisfy C1--C4 directly. -/
theorem conditions_of_card_le_three [Fintype V] {m : Nat}
    (hm : 4 ≤ m) (hcard : Fintype.card V ≤ 3) :
    T3Conditions m G := by
  have hpalette : Fintype.card V ≤ Fintype.card (Fin (m - 1)) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hpalette
  have hc : KColorable (m - 1) G := by
    refine ⟨{ color := e, valid := ?_ }⟩
    intro x y hxy hsame
    exact hxy.ne (e.injective hsame)
  exact conditions_of_colorable_pred (G := G) hm hc

private theorem card_subtype_lt_of_exists_not_mem [Fintype V] (A : Set V) [Fintype A]
    (hmiss : ∃ x : V, x ∉ A) :
    Fintype.card A < Fintype.card V := by
  classical
  rcases hmiss with ⟨w, hwA⟩
  let imageA : Finset V := (Finset.univ : Finset A).image (fun x : A => (x : V))
  have hsubset : imageA ⊆ (Finset.univ : Finset V) := by
    intro x _hx
    simp
  have hw_not_image : w ∉ imageA := by
    intro hw
    rcases Finset.mem_image.mp hw with ⟨a, _ha, hval⟩
    exact hwA (by
      rw [← hval]
      exact a.property)
  have hproper : imageA ⊂ (Finset.univ : Finset V) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
    intro hEq
    exact hw_not_image (by simp [hEq])
  have hlt := Finset.card_lt_card hproper
  have hcard_image : imageA.card = (Finset.univ : Finset A).card := by
    dsimp [imageA]
    exact Finset.card_image_of_injective (Finset.univ : Finset A)
      (fun a b h => Subtype.ext h : Function.Injective (fun x : A => (x : V)))
  rw [hcard_image] at hlt
  exact hlt

private theorem conditions_of_separated_cover [Fintype V] {m : Nat}
    {G : SimpleGraph V} (hm : 4 ≤ m) (hfrag : MFragile m G)
    (C : SeparatedCover G)
    (hA : T3Conditions m (G.induce C.A)) (hB : T3Conditions m (G.induce C.B))
    (hcard3 : 3 ≤ Fintype.card V) :
    T3Conditions m G := by
  classical
  let hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  refine ⟨?c1, ?c2, ?c3, ?c4⟩
  · intro x y hnxy
    by_cases hxA : x ∈ C.A
    · by_cases hyA : y ∈ C.A
      · exact separated_c1_left hmpos C hA hB hxA hyA hnxy
      · have hyB : y ∈ C.B := by
          have hyAB : y ∈ C.A ∪ C.B := by simp [C.cover]
          exact hyAB.resolve_left hyA
        by_cases hxB : x ∈ C.B
        · exact separated_c1_left hmpos C.symm hB hA hxB hyB hnxy
        · exact separated_c1_cross hmpos C hA hB hxA hxB hyB hyA
    · have hxB : x ∈ C.B := by
        have hxAB : x ∈ C.A ∪ C.B := by simp [C.cover]
        exact hxAB.resolve_left hxA
      by_cases hyB : y ∈ C.B
      · exact separated_c1_left hmpos C.symm hB hA hxB hyB hnxy
      · have hyA : y ∈ C.A := by
          have hyAB : y ∈ C.A ∪ C.B := by simp [C.cover]
          exact hyAB.resolve_right hyB
        obtain ⟨c, hc⟩ := separated_c1_cross hmpos C hA hB hyA hyB hxB hxA
        exact ⟨c, hc.symm⟩
  · intro x y hxy
    exact separated_c2_of_c3
      (fun {_x _y _z : V} hxy hxz hyz =>
        separated_c3 hm hfrag C hA hB hxy hxz hyz)
      hxy (exists_third_of_card_three hxy hcard3)
  · intro x y z hxy hxz hyz
    exact separated_c3 hm hfrag C hA hB hxy hxz hyz
  · intro x y z hxy hxz hyz hnot_triangle
    exact separated_c4 hm C hA hB hxy hxz hyz hnot_triangle

theorem theorem3_mfragile_aux (m n : Nat) (hm : 4 ≤ m) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      Fintype.card V = n →
      ∀ G : SimpleGraph V, MFragile m G → T3Conditions m G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _instFintype _instDecidable hcard_eq G hfrag
    classical
    by_cases hsmall : Fintype.card V ≤ 3
    · exact conditions_of_card_le_three (G := G) hm hsmall
    · have hcard4 : 4 ≤ Fintype.card V := by omega
      by_cases hconn : ThreeConnected G
      · exact conditions_of_fragile_connected (G := G) hm hfrag hconn
      · have hcard4_nat : 4 ≤ Nat.card V := by
          simpa [Nat.card_eq_fintype_card] using hcard4
        obtain ⟨C⟩ := not_three_connected_decomp G hcard4_nat hconn
        have hA_ltV : Fintype.card C.A < Fintype.card V :=
          card_subtype_lt_of_exists_not_mem C.A
            ⟨C.right_nonempty.some, C.right_nonempty.some_mem.2⟩
        have hB_ltV : Fintype.card C.B < Fintype.card V :=
          card_subtype_lt_of_exists_not_mem C.B
            ⟨C.left_nonempty.some, C.left_nonempty.some_mem.2⟩
        have hA_ltn : Fintype.card C.A < n := by
          simpa [hcard_eq] using hA_ltV
        have hB_ltn : Fintype.card C.B < n := by
          simpa [hcard_eq] using hB_ltV
        have hAcond : T3Conditions m (G.induce C.A) :=
          ih (Fintype.card C.A) hA_ltn (V := C.A) rfl
            (G.induce C.A) (mfragile_induced hfrag C.A)
        have hBcond : T3Conditions m (G.induce C.B) :=
          ih (Fintype.card C.B) hB_ltn (V := C.B) rfl
            (G.induce C.B) (mfragile_induced hfrag C.B)
        exact conditions_of_separated_cover hm hfrag C hAcond hBcond (by omega)

end Theorem3

/-- Theorem 3, paper numbering: finite simple $m$-fragile graphs satisfy C1--C4. -/
theorem theorem3_mfragile {V : Type u} [Fintype V] [DecidableEq V]
    (m : Nat) (G : SimpleGraph V)
    (hm : 4 ≤ m) (hfrag : MFragile m G) :
    T3Conditions m G :=
  Theorem3.theorem3_mfragile_aux m (Fintype.card V) hm rfl G hfrag

end Lax10Proofs
