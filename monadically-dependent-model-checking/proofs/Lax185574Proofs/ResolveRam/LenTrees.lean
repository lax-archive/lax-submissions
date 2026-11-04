import Lax185574Proofs.ResolveRam.SizeSpec
import Lax185574Proofs.ResolveRam.SizeBound
import Lax185574Proofs.RamPipeFwd

/-!
Sizes of the trees of `G` that occur in the calls of lem:resolve-lift.

The bounds are polynomials in `M + 1`, where `M` is the largest size of
a tree of the family, with coefficients and degrees of the rank. The
output of a program is no longer than its time bound
(`wordLength_le_time`). So the tree of a vertex at the rank `(k₀ + i,
q₀ − i)` is bounded by `i` rank shifts of a tree of the family
(`single_le`). The items of the levels are bounded by induction on the
level (`item_le`): a member of an expansion is a child of the item or the
composition of the shifted item with a tree of a vertex. A scatter type
at a rank below the top has at most `|G|` times a constant entries,
each a radius, a tree of a vertex and a value (`stp_le`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.TypeTreeSizes
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### Polynomial bounds -/

theorem pc_comp {x c a d b M : ℕ} (h : x ≤ c * (M + 1) ^ a) :
    d * (x + 1) ^ b ≤ d * (c + 1) ^ b * (M + 1) ^ (a * b) := by
  have h1 : 1 ≤ (M + 1) ^ a := Nat.one_le_pow _ _ (Nat.succ_pos M)
  have : x + 1 ≤ (c + 1) * (M + 1) ^ a := by nlinarith
  calc d * (x + 1) ^ b ≤ d * ((c + 1) * (M + 1) ^ a) ^ b :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this b)
    _ = d * (c + 1) ^ b * (M + 1) ^ (a * b) := by rw [mul_pow, ← pow_mul]; ring

theorem pc_exp {x c a a' M : ℕ} (h : x ≤ c * (M + 1) ^ a) (ha : a ≤ a') :
    x ≤ c * (M + 1) ^ a' :=
  le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos M) ha))

theorem pc_add {x y c a c' a' M : ℕ} (hx : x ≤ c * (M + 1) ^ a) (hy : y ≤ c' * (M + 1) ^ a') :
    x + y ≤ (c + c') * (M + 1) ^ (a + a') := by
  have h1 := pc_exp hx (show a ≤ a + a' by omega)
  have h2 := pc_exp hy (show a' ≤ a + a' by omega)
  rw [add_mul]; omega

theorem pc_base {x c a M M' : ℕ} (h : x ≤ c * (M + 1) ^ a) (hM : M ≤ M') :
    x ≤ c * (M' + 1) ^ a :=
  le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) a))

/-- The output of a program that computes `b` from `a` is no longer than
its time bound. Copied from `MC/Bounds/TreeMax`. -/
theorem wordLength_le_time' {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b : β} {T : ℕ → ℕ} (h : Computes p e c a b T) :
    wordLength b ≤ T (wordLength a) := by
  set W := c * ((toWord a).length + maxEntry (toWord a) + 1) ^ e + T (wordLength a)
  have hW : W < 2 ^ W := Nat.lt_two_pow_self
  have hadm : WordAdmissible e c W (toWord a) := by
    intro v hv
    have := le_maxEntry hv
    have : c * ((toWord a).length + v + 1) ^ e ≤
        c * ((toWord a).length + maxEntry (toWord a) + 1) ^ e := by gcongr
    omega
  obtain ⟨t, ht, hr⟩ := (h W hadm).2 (by omega) (toWord a) rfl
  exact le_trans (Lax185574Proofs.RamSim.runsTo_out_length hr) ht

/-! ### Words of finite sets and trees -/

theorem wordLength_mem_lt {α : Type*} [WordEncoding α] {S : Finset α} {x : α} (hx : x ∈ S) :
    wordLength x < wordLength S := by
  show wordLength x < wordLength (Finset.words S)
  rw [wordLength_list]
  have hm : toWord x ∈ Finset.words S := by
    simp only [Finset.words, Finset.mem_sort, Finset.mem_image]
    exact ⟨x, hx, rfl⟩
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := wordLength) hm)
  rw [wordLength_list_nat] at this
  show (toWord x).length < _
  omega

theorem wordLength_tt (τ : TypeTree) : wordLength τ = 3 + wordLength τ.root := by
  show (toWord (τ.k, τ.q, τ.ℓ) ++ toWord τ.root).length = _
  rw [List.length_append]; rfl

theorem child_le {k q ℓ : ℕ} {t : Node (q + 1) ℓ} {e : Fin ℓ × Node q (ℓ + 1)}
    (he : e ∈ Node.exts t) :
    wordLength (⟨k + 1, q, ℓ + 1, e.2⟩ : TypeTree) ≤ wordLength (⟨k, q + 1, ℓ, t⟩ : TypeTree) := by
  rw [wordLength_tt, wordLength_tt]
  have h1 := wordLength_mem_lt he
  have h2 : wordLength e = wordLength e.1 + wordLength e.2 := wordLength_prod _ _
  have h3 : wordLength (⟨k, q + 1, ℓ, t⟩ : TypeTree).root = wordLength t.1 + wordLength t.2 :=
    wordLength_prod _ _
  simp only [Node.exts_def] at h1
  show 3 + wordLength e.2 ≤ 3 + wordLength (⟨k, q + 1, ℓ, t⟩ : TypeTree).root
  omega

/-! ### Trees of vertices -/

variable (k₀ q₀ : ℕ)

/-- **Trees of vertices.** -/
theorem single_le (hk : 1 ≤ k₀) : ∀ i ≤ q₀, ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (b : Fin n), wordLength (tree G (k₀ + i) (q₀ - i) ![b]) ≤ c * (maxTreeSize G k₀ q₀ + 1) ^ a
  | 0, _ => ⟨1, 1, fun n G b => by
      have : wordLength (family G k₀ q₀ b) ≤ maxTreeSize G k₀ q₀ :=
        Finset.le_sup (f := fun a : Fin n => wordLength (family G k₀ q₀ a)) (Finset.mem_univ b)
      simp only [family] at this
      simpa using this.trans (Nat.le_succ _)⟩
  | i + 1, hi => by
    obtain ⟨c, a, h⟩ := single_le hk i (by omega)
    refine ⟨cSh (k₀ + i) (q₀ - i - 1) * (c + 1) ^ aSh (k₀ + i) (q₀ - i - 1),
      a * aSh (k₀ + i) (q₀ - i - 1), fun n G b => ?_⟩
    have hc := wordLength_le_time' (hSh' (k₀ + i) (q₀ - i - 1) n G 1 ![b] le_rfl (by omega))
    rw [show q₀ - i - 1 + 1 = q₀ - i by omega] at hc
    rw [show k₀ + (i + 1) = k₀ + i + 1 by omega, show q₀ - (i + 1) = q₀ - i - 1 by omega]
    exact le_trans hc (pc_comp (h n G b))

/-- One bound for the trees of vertices at all ranks below the top. -/
theorem single_le_all (hk : 1 ≤ k₀) : ∃ c a : ℕ, ∀ i ≤ q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (b : Fin n), wordLength (tree G (k₀ + i) (q₀ - i) ![b]) ≤ c * (maxTreeSize G k₀ q₀ + 1) ^ a := by
  have h := fun i (hi : i ≤ q₀) => single_le k₀ q₀ hk i hi
  choose! c a hc using h
  refine ⟨∑ i ∈ Finset.range (q₀ + 1), c i, ∑ i ∈ Finset.range (q₀ + 1), a i,
    fun i hi n G b => ?_⟩
  have hm : i ∈ Finset.range (q₀ + 1) := Finset.mem_range.2 (by omega)
  refine le_trans (hc i hi n G b) (Nat.mul_le_mul ?_ ?_)
  · exact Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) hm
  · exact Nat.pow_le_pow_right (Nat.succ_pos _)
      (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) hm)

/-! ### The items -/

variable {n : ℕ} (G : PartialGraph (Fin n))

theorem mem_exAt_cases {D : ResolveData} {sh : TypeTree → TypeTree}
    {fa : TypeTree → List TypeTree} {co : TypeTree → TypeTree → TypeTree} {k q ℓ : ℕ}
    {t : Node (q + 1) ℓ} {gc : ℕ × TypeTree} (h : gc ∈ exAt D sh fa co k q ℓ t) :
    (∃ e ∈ Node.exts t, gc.2 = (⟨k + 1, q, ℓ + 1, e.2⟩ : TypeTree)) ∨
      ∃ ν ∈ fa ⟨k, q + 1, ℓ, t⟩, gc.2 = co (sh ⟨k, q + 1, ℓ, t⟩) ν := by
  have hg : ∀ {q' ℓ' : ℕ} (R : ℕ) (r : Node q' (ℓ' + 1)) (c : TypeTree) (p : ℕ × TypeTree),
      p ∈ guarded D R r c → p.2 = c := by
    intro q' ℓ' R r c p hp
    simp only [guarded, List.mem_filterMap] at hp
    obtain ⟨i, -, hi⟩ := hp
    split_ifs at hi
    · simp only [Option.some.injEq] at hi; rw [← hi]
  have hel : ∀ e ∈ elems (Node.exts t), e ∈ Node.exts t := by
    intro e he
    have := Lax185574Proofs.EncodingInjectivity.prefixFree_node q (ℓ + 1)
    exact mem_elems.1 he
  simp only [exAt, List.mem_append, List.mem_map, List.mem_flatMap] at h
  rcases h with (⟨e, he, rfl⟩ | ⟨e, he, hgc⟩) | ⟨ν, hν, r, -, hgc⟩
  · exact Or.inl ⟨e, hel e he, rfl⟩
  · exact Or.inl ⟨e, hel e he, hg _ _ _ _ hgc⟩
  · exact Or.inr ⟨ν, hν, hg _ _ _ _ hgc⟩

theorem faP_tree {P Q : ℕ} {s : Bool} {d : ℕ} (hd : d < q₀) {ℓ : ℕ} {u : Fin ℓ → Fin n}
    (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k₀ + d) {ν : TypeTree}
    (hν : ν ∈ faP G (dataOf G P Q s k₀ q₀) (tree G (k₀ + d) (q₀ - d - 1 + 1) u)) :
    ∃ b, (∀ i, ¬ WithinDist G.resolved (rhoMinus (k₀ + d + 1) (q₀ - d - 1)) (u i) b) ∧
      ν = tree G (k₀ + d + 1) (q₀ - d - 1) ![b] := by
  have hfa := (ansOK_of G k₀ q₀).fa (k₀ + d) (q₀ - d - 1) ℓ u h1 hk (by omega) (by omega) ν
  exact (mem_ftree (G := G) (k₀ + d) (q₀ - d - 1) u ν).1 (hfa.1 (List.mem_filter.1 hν).1)

/-- **The items.** -/
theorem item_le (hk : 1 ≤ k₀) : ∀ d ≤ q₀, ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ x ∈ lvR G P Q s k₀ q₀ d,
      wordLength x.2 ≤ c * (maxTreeSize G k₀ q₀ + 1) ^ a
  | 0, _ => ⟨1, 1, fun n G P Q s x hx => by
      simp only [lvR, levels, Function.iterate_zero, id, famItems, List.mem_map] at hx
      obtain ⟨b, -, rfl⟩ := hx
      have : wordLength (family G k₀ q₀ b) ≤ maxTreeSize G k₀ q₀ :=
        Finset.le_sup (f := fun a : Fin n => wordLength (family G k₀ q₀ a)) (Finset.mem_univ b)
      simpa using this.trans (Nat.le_succ _)⟩
  | d + 1, hd => by
    obtain ⟨c, a, ih⟩ := item_le hk d (by omega)
    obtain ⟨c1, a1, hs1⟩ := single_le k₀ q₀ hk (d + 1) hd
    set m := q₀ - d - 1
    set cS := cSh (k₀ + d) m
    set aS := aSh (k₀ + d) m
    set c2 := cS * (c + 1) ^ aS
    set a2 := a * aS
    set cC := cCo (k₀ + d + 1) m
    set aC := aCo (k₀ + d + 1) m
    refine ⟨c + cC * (c2 + c1 + 1) ^ aC, a + (a2 + a1) * aC, fun n G P Q s x hx => ?_⟩
    unfold lvR at hx
    rw [levels_succ] at hx
    obtain ⟨i, hi, gc, hgc, rfl⟩ := mem_nextLevel.1 hx
    have hy : (levels (exR G P Q s k₀ q₀) (famItems G k₀ q₀) d)[i] ∈ lvR G P Q s k₀ q₀ d :=
      List.getElem_mem hi
    have hI := ih n G P Q s _ hy
    obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk (by omega) hy
    rw [show q₀ - d = m + 1 by omega] at hu
    rw [hu] at hgc hI
    have hgc' : gc ∈ exAt (dataOf G P Q s k₀ q₀) (shOf G) (faP G (dataOf G P Q s k₀ q₀)) (coOf G)
        (k₀ + d) m ℓ (node G (k₀ + d) (m + 1) u) := hgc
    show wordLength gc.2 ≤ _
    rcases mem_exAt_cases hgc' with ⟨e, he, h2⟩ | ⟨ν, hν, h2⟩
    · rw [h2]
      refine pc_add (le_trans (child_le he) hI) (Nat.zero_le _) |>.trans' ?_
      omega
    · rw [h2]
      obtain ⟨b, hb, rfl⟩ := faP_tree k₀ q₀ G (by omega) h1 hℓ hν
      have hsh : shOf G ⟨k₀ + d, m + 1, ℓ, node G (k₀ + d) (m + 1) u⟩ =
          tree G (k₀ + d + 1) m u := shOf_tree G u h1 hℓ
      rw [hsh, coOf_tree G u b h1 hℓ hb]
      have tS := wordLength_le_time' (hSh' (k₀ + d) m n G ℓ u h1 hℓ)
      have tS' : wordLength (tree G (k₀ + d + 1) m u) ≤ c2 * (maxTreeSize G k₀ q₀ + 1) ^ a2 :=
        le_trans tS (pc_comp hI)
      have hν1 := hs1 n G b
      rw [show k₀ + (d + 1) = k₀ + d + 1 by omega, show q₀ - (d + 1) = m by omega] at hν1
      have tC := wordLength_le_time' (hCo' (k₀ + d + 1) m n G ℓ 1 u ![b] h1 le_rfl (by omega)
        (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i))
      rw [Fin.append_right_eq_snoc] at tC
      have hsum : wordLength (tree G (k₀ + d + 1) m u, tree G (k₀ + d + 1) m ![b]) ≤
          (c2 + c1) * (maxTreeSize G k₀ q₀ + 1) ^ (a2 + a1) := by
        rw [wordLength_prod]; exact pc_add tS' hν1
      have := le_trans tC (pc_comp hsum)
      refine le_trans this ?_
      have h3 := pc_exp (le_refl (cC * (c2 + c1 + 1) ^ aC * (maxTreeSize G k₀ q₀ + 1) ^ ((a2 + a1) * aC)))
        (show (a2 + a1) * aC ≤ a + (a2 + a1) * aC by omega)
      refine le_trans h3 (Nat.mul_le_mul_right _ ?_)
      omega

/-- One bound for the items of all levels. -/
theorem item_le_all (hk : 1 ≤ k₀) : ∃ c a : ℕ, ∀ d ≤ q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ x ∈ lvR G P Q s k₀ q₀ d,
      wordLength x.2 ≤ c * (maxTreeSize G k₀ q₀ + 1) ^ a := by
  have h := fun d (hd : d ≤ q₀) => item_le k₀ q₀ hk d hd
  choose! c a hc using h
  refine ⟨∑ i ∈ Finset.range (q₀ + 1), c i, ∑ i ∈ Finset.range (q₀ + 1), a i,
    fun d hd n G P Q s x hx => ?_⟩
  have hm : d ∈ Finset.range (q₀ + 1) := Finset.mem_range.2 (by omega)
  refine le_trans (hc d hd n G P Q s x hx) (Nat.mul_le_mul ?_ ?_)
  · exact Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) hm
  · exact Nat.pow_le_pow_right (Nat.succ_pos _)
      (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) hm)

/-! ### Scatter types -/

/-- The bound on the radii of the scatter types below the top rank. -/
noncomputable def radC (k₀ q₀ : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (q₀ + 1), 9 ^ (k₀ + j) * rhoMinus (k₀ + j) (q₀ - j)

/-- **Scatter types below the top rank.** -/
theorem stp_le (hk : 1 ≤ k₀) : ∃ c a : ℕ, ∀ d ≤ q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n)),
    wordLength (stp G (k₀ + d) (q₀ - d)) ≤ c * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ a := by
  obtain ⟨c1, a1, h1⟩ := single_le_all k₀ q₀ hk
  refine ⟨1 + (q₀ + 1) * (radC k₀ q₀ + 1) * (c1 + 3), a1, fun d hd n G => ?_⟩
  classical
  obtain ⟨M, hM⟩ : ∃ M, M = maxTreeSize G k₀ q₀ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = c1 * (M + 1) ^ a1 + 2 := ⟨_, rfl⟩
  rw [← hM]
  set S := {p : (ℕ × TypeTree) × ℕ | p.1 ∈ domain G (k₀ + d) (q₀ - d) ∧
    p.2 = value G (k₀ + d) (q₀ - d) p.1}
  have hS : stp G (k₀ + d) (q₀ - d) = finsetOf S := rfl
  have hel : ∀ p ∈ stp G (k₀ + d) (q₀ - d), wordLength p ≤ B := by
    intro p hp
    rw [hS] at hp
    obtain ⟨⟨i, b, hi1, hi2, -, -, hν⟩, -⟩ := mem_of_mem_finsetOf hp
    have hj := h1 (d + i) (by omega) n G b
    rw [show k₀ + (d + i) = k₀ + d + i by omega, show q₀ - (d + i) = q₀ - d - i by omega,
      ← hν, ← hM] at hj
    rw [wordLength_prod, wordLength_prod]
    show 1 + wordLength p.1.2 + 1 ≤ B
    omega
  let f : ℕ × ℕ × Fin n → (ℕ × TypeTree) × ℕ := fun x =>
    ((x.2.1, tree G (k₀ + d + x.1) (q₀ - d - x.1) ![x.2.2]),
      value G (k₀ + d) (q₀ - d) (x.2.1, tree G (k₀ + d + x.1) (q₀ - d - x.1) ![x.2.2]))
  have hsub : S ⊆ ↑((Finset.range (q₀ + 1) ×ˢ Finset.range (radC k₀ q₀ + 1) ×ˢ
      (Finset.univ : Finset (Fin n))).image f) := by
    rintro ⟨⟨r, ν⟩, v⟩ ⟨⟨i, b, hi1, hi2, hr1, hr2, hν⟩, hv⟩
    dsimp only at hi1 hi2 hr1 hr2 hν hv
    subst hν hv
    have hR : 9 ^ (k₀ + d + i) * rhoMinus (k₀ + d + i) (q₀ - d - i) ≤ radC k₀ q₀ := by
      have := Finset.single_le_sum (f := fun j => 9 ^ (k₀ + j) * rhoMinus (k₀ + j) (q₀ - j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (show d + i < q₀ + 1 by omega))
      rw [show k₀ + (d + i) = k₀ + d + i by omega, show q₀ - (d + i) = q₀ - d - i by omega] at this
      exact this
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_range, Finset.mem_univ, and_true]
    refine ⟨(i, r, b), ⟨by dsimp only; omega, by dsimp only; omega⟩, ?_⟩
    rfl
  have hcard : (stp G (k₀ + d) (q₀ - d)).card ≤ (q₀ + 1) * (radC k₀ q₀ + 1) * n := by
    rw [hS, card_finsetOf]
    refine le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _)) ?_
    rw [Set.ncard_coe_finset]
    refine le_trans Finset.card_image_le ?_
    simp [Finset.card_product, mul_assoc]
  have hw := wordLength_finset_le _ B hel
  have hP : 1 ≤ (M + 1) ^ a1 := Nat.one_le_pow _ _ (Nat.succ_pos M)
  have e1 : (stp G (k₀ + d) (q₀ - d)).card * (B + 1) ≤
      (q₀ + 1) * (radC k₀ q₀ + 1) * n * ((c1 + 3) * (M + 1) ^ a1) :=
    Nat.mul_le_mul hcard (by rw [hB]; nlinarith)
  have e2 : 1 + (q₀ + 1) * (radC k₀ q₀ + 1) * n * ((c1 + 3) * (M + 1) ^ a1) ≤
      (1 + (q₀ + 1) * (radC k₀ q₀ + 1) * (c1 + 3)) * (n + 1) * (M + 1) ^ a1 := by
    have : (1 + (q₀ + 1) * (radC k₀ q₀ + 1) * (c1 + 3)) * (n + 1) * (M + 1) ^ a1 =
        (n + 1) * (M + 1) ^ a1 + (q₀ + 1) * (radC k₀ q₀ + 1) * n * ((c1 + 3) * (M + 1) ^ a1) +
          (q₀ + 1) * (radC k₀ q₀ + 1) * ((c1 + 3) * (M + 1) ^ a1) := by ring
    rw [this]
    have : 1 ≤ (n + 1) * (M + 1) ^ a1 := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  omega

end Lax185574Proofs.ResolveRam
