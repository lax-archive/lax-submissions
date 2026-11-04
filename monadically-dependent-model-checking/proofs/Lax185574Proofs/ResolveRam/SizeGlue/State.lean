import Lax185574Proofs.ResolveRam.SizeGlue.Answers
import Lax185574Proofs.ResolveRam.Glue.Head

/-!
The length of the state of the glue program of lem:resolve-lift.

Write `M` for the largest size of a tree of the family, `T` for
`treeCount` and `Y = M + T + 1`. The word of a list of words `ws` has
length `1 + Σ (|w| + 1)` (`length_toWord_ws`). The state at a position
that carries a call, at the start and at the end holds

* the color table, `3` entries per color that occurs, at most `3 n`
  (`ctW_len`),
* the words of the scatter type, at most a constant times `(n + 1)(M +
  1)^A` (`stp_le`),
* the answers of the rank shift, of the far tree and of the
  compositions of the current item, at most `T` words of size
  polynomial in `M` (`shift_ans_le`, `faOf_mem_le`, `compose_ans_le`,
  `length_faP_leT`),
* the answer of the canonical form on the atom words of an item,
  polynomial in `T` (`upW_le`),
* the lengths of the levels, at most `q₀ + 2` entries,
* the item words of at most `q₀ + 1` levels and of a part of the next,
  at most `n` times a polynomial in `T` items of size polynomial in `M`
  each (`length_lvR_leT`, `item_le_all`),
* the output words of two levels, at most `n` times a polynomial in `T`
  words of size at most `kidB T` (`outR_mem_le`).

So the state has length at most a constant times `(n + 1) Y^A`
(`stOf_len`). There is no term in `‖H‖`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words Lax185574Proofs.TypeTreeSizes
open Lax185574Proofs.MC

/-! ### Words of lists of words -/

/-- The sum of the lengths of the words of a list plus one per word. -/
def tot (ws : List (List ℕ)) : ℕ := (ws.map fun w => w.length + 1).sum

theorem length_toWord_ws (ws : List (List ℕ)) : (toWord ws).length = 1 + tot ws := by
  have h := wordLength_list ws
  have e : ws.map (wordLength (α := List ℕ)) = ws.map fun w => w.length + 1 :=
    List.map_congr_left fun w _ => wordLength_list_nat w
  rw [e] at h
  exact h

theorem tot_append (a b : List (List ℕ)) : tot (a ++ b) = tot a + tot b := by
  simp [tot, List.sum_append]

theorem tot_cons (w : List ℕ) (ws : List (List ℕ)) : tot (w :: ws) = w.length + 1 + tot ws := by
  simp [tot]

theorem tot_nil : tot [] = 0 := rfl

theorem tot_le {ws : List (List ℕ)} {B : ℕ} (h : ∀ w ∈ ws, w.length ≤ B) :
    tot ws ≤ ws.length * (B + 1) := by
  induction ws with
  | nil => simp [tot]
  | cons w ws ih =>
    rw [tot_cons, List.length_cons]
    have h1 := h w (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    nlinarith

/-! ### Single fields -/

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem length_colsL : (colsL G).length ≤ n := by
  unfold colsL
  rw [Finset.length_sort]
  refine le_trans Finset.card_image_le ?_
  simp

/-- **The color table.** -/
theorem ctW_len : (ctW G P Q).length ≤ 3 * n := by
  have h := length_colsL G
  have e : (ctW G P Q).length = 3 * (colsL G).length := by
    unfold ctW
    induction colsL G with
    | nil => simp
    | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, ih]; ring
  omega

theorem llW_length (d : ℕ) : (llW G P Q s k₀ q₀ d).length = d + 1 := by
  simp [llW]

theorem length_itemW (x : Item) : (itemW x).length = 2 + wordLength x.2 := by
  simp [itemW, wordLength]; omega

/-- The expansions of the first items of a level are a part of the next level. -/
theorem nxL_sublist (d i : ℕ) : List.Sublist (nxL G P Q s k₀ q₀ d i) (lvR G P Q s k₀ q₀ (d + 1)) := by
  rw [← nxL_full G P Q s k₀ q₀ d]
  unfold nxL
  have hL : (lvR G P Q s k₀ q₀ d).zipIdx.take (lvR G P Q s k₀ q₀ d).length =
      (lvR G P Q s k₀ q₀ d).zipIdx := List.take_of_length_le (by simp)
  rw [hL]
  conv_rhs => rw [← List.take_append_drop i (lvR G P Q s k₀ q₀ d).zipIdx]
  rw [List.flatMap_append]
  exact List.sublist_append_left _ _

/-- **The output words of the items.** -/
theorem outW_mem_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) :
    ∀ w ∈ outW G P Q s k₀ q₀ d, w.length ≤ kidB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  intro w hw
  simp only [outW, List.mem_map] at hw
  obtain ⟨τ, hτ, rfl⟩ := hw
  exact outR_mem_le G P Q s hk hd τ hτ

/-! ### Arithmetic -/

theorem cnt_mul {N Y A cL aL c a cnt B : ℕ} (hY : 1 ≤ Y) (hcnt : cnt ≤ cL * (N + 1) * Y ^ aL)
    (hB : B ≤ c * Y ^ a) (hA : aL + a ≤ A) : cnt * (B + 1) ≤ cL * (c + 1) * ((N + 1) * Y ^ A) := by
  have h1 : 1 ≤ Y ^ a := Nat.one_le_pow _ _ hY
  have h2 : B + 1 ≤ (c + 1) * Y ^ a := by nlinarith
  calc cnt * (B + 1) ≤ (cL * (N + 1) * Y ^ aL) * ((c + 1) * Y ^ a) := Nat.mul_le_mul hcnt h2
    _ = cL * (c + 1) * ((N + 1) * Y ^ (aL + a)) := by rw [pow_add]; ring
    _ ≤ cL * (c + 1) * ((N + 1) * Y ^ A) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY hA))

theorem pow_Z {N Y A c a : ℕ} (hY : 1 ≤ Y) (ha : a ≤ A) : c * Y ^ a ≤ c * ((N + 1) * Y ^ A) := by
  refine Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_right hY ha) ?_)
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- The number of items of a level. -/
theorem lvR_len (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) :
    (lvR G P Q s k₀ q₀ d).length ≤ ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ * (n + 1) *
      (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ q₀ := by
  have h := length_lvR_leT G P Q s k₀ q₀ hk d hd
  set T := treeCount G (resolveBy G s P Q) k₀ q₀
  set K := (k₀ + q₀ + 2) ^ 2
  have h1 : exMaxT k₀ q₀ T ^ d ≤ ((K + 1) * (maxTreeSize G k₀ q₀ + T + 1)) ^ q₀ := by
    unfold exMaxT
    have : K * T ≤ (K + 1) * (maxTreeSize G k₀ q₀ + T + 1) := by nlinarith
    calc (K * T) ^ d ≤ ((K + 1) * (maxTreeSize G k₀ q₀ + T + 1)) ^ d := Nat.pow_le_pow_left this d
      _ ≤ _ := Nat.pow_le_pow_right (Nat.one_le_iff_ne_zero.2 (by positivity)) hd
  rw [mul_pow] at h1
  calc (lvR G P Q s k₀ q₀ d).length ≤ n * exMaxT k₀ q₀ T ^ d := h
    _ ≤ (n + 1) * ((K + 1) ^ q₀ * (maxTreeSize G k₀ q₀ + T + 1) ^ q₀) :=
        Nat.mul_le_mul (by omega) h1
    _ = _ := by ring

/-! ### The state -/

/-- The bound of the fields of the state at a position. -/
theorem stOf_eq (c : Cur) : (stOf G P Q s k₀ q₀ c).length = 18 +
    ((swAt G P Q s k₀ q₀ c).CT.length + 1) + ((swAt G P Q s k₀ q₀ c).SH.length + 1) +
    ((swAt G P Q s k₀ q₀ c).AT.length + 1) + ((swAt G P Q s k₀ q₀ c).LL.length + 1) +
    tot (swAt G P Q s k₀ q₀ c).SG + tot (swAt G P Q s k₀ q₀ c).FA +
    tot (swAt G P Q s k₀ q₀ c).CO + tot (swAt G P Q s k₀ q₀ c).LV + tot (swAt G P Q s k₀ q₀ c).OU := by
  have e1 : (scW G P Q s k₀ q₀ c).length = 17 := by
    unfold scW curW; cases c <;> simp
  rw [stOf, List.length_append, e1, length_toWord_ws, SW.ws]
  simp only [tot_append, tot_cons, tot_nil]
  ring

/-- **The length of the state.** At the start, at the end and at every
position that carries a call, the state has length at most a constant
times `(n + 1) Y^A`. -/
theorem stOf_len (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool) (c : Cur), (c = .stp ∨ c = .fin ∨ Valid G P Q s k₀ q₀ c) →
      (stOf G P Q s k₀ q₀ c).length ≤
        C * (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A := by
  obtain ⟨c0, a0, hI⟩ := item_le_all k₀ q₀ hk
  obtain ⟨cS, aS, hS⟩ := stp_le k₀ q₀ hk
  obtain ⟨cH, aH, hH⟩ := shift_ans_le (q₀ := q₀) hk
  obtain ⟨c1, a1, hF⟩ := faOf_mem_le (q₀ := q₀) hk
  obtain ⟨cC, aC, hC⟩ := compose_ans_le (q₀ := q₀) hk
  set cL := ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀
  set cA := cCa * (upCst k₀ q₀ + 1) ^ aCa
  set aA := (q₀ + 2) * aCa
  set SC := ∑ m ∈ Finset.range (q₀ + 1), sizeCoeff (1 + 36 * (Lax3.DistFO.rhoPlus k₀ q₀ + 1) *
    ((q₀ + 1) * (q₀ + 1))) (q₀ + 1) m
  set A := 2 * q₀ + 2 + a0 + aS + aH + a1 + aC + aA with hAd
  refine ⟨18 + 4 + (cH + 1) + (cA + 1) + (q₀ + 3) + cS + (1 * (c1 + 1)) + (1 * (cC + 1)) + ((q₀ + 2) * (cL * (c0 + 2 + 1))) + (2 * (cL * (3 + SC + 1))), A, ?_⟩
  intro n G P Q s c hc
  set M := maxTreeSize G k₀ q₀ with hM
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hT
  set Y := M + T + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  set Z := (n + 1) * Y ^ A with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hMY : ∀ c a, a ≤ A → c * (M + 1) ^ a ≤ c * Z := fun c a ha =>
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) a)) (pow_Z hY1 ha)
  -- the counts
  have hcnt : ∀ e ≤ q₀, (lvR G P Q s k₀ q₀ e).length ≤ cL * (n + 1) * Y ^ q₀ :=
    fun e he => lvR_len G P Q s k₀ q₀ hk he
  have hTc : T ≤ 1 * (n + 1) * Y ^ 1 := by
    simp only [one_mul, pow_one]; nlinarith
  -- the levels
  have hitem : ∀ e ≤ q₀, ∀ x ∈ lvR G P Q s k₀ q₀ e, (itemW x).length ≤ (c0 + 2) * Y ^ a0 := by
    intro e he x hx
    rw [length_itemW]
    have h1 := hI e he n G P Q s x hx
    have h2 : (M + 1) ^ a0 ≤ Y ^ a0 := Nat.pow_le_pow_left (by omega) _
    have h3 : 1 ≤ Y ^ a0 := Nat.one_le_pow _ _ hY1
    nlinarith
  have hlvW : ∀ e ≤ q₀, tot (lvW G P Q s k₀ q₀ e) ≤ cL * (c0 + 2 + 1) * Z := by
    intro e he
    refine le_trans (tot_le (B := (c0 + 2) * Y ^ a0) ?_) ?_
    · intro w hw
      simp only [lvW, List.mem_map] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact hitem e he x hx
    · rw [show (lvW G P Q s k₀ q₀ e).length = (lvR G P Q s k₀ q₀ e).length by simp [lvW]]
      exact cnt_mul (A := A) hY1 (hcnt e he) le_rfl (by omega)
  have hlvsW : ∀ d ≤ q₀, tot (lvsW G P Q s k₀ q₀ d) ≤ (d + 1) * (cL * (c0 + 2 + 1) * Z) := by
    intro d hd
    induction d with
    | zero =>
      have : lvsW G P Q s k₀ q₀ 0 = lvW G P Q s k₀ q₀ 0 := by simp [lvsW]
      rw [this]; have := hlvW 0 (Nat.zero_le _); omega
    | succ d ih =>
      rw [lvsW_succ, tot_append]
      have h1 := ih (by omega)
      have h2 := hlvW (d + 1) hd
      rw [add_mul, one_mul]
      omega
  have hnxW : ∀ d < q₀, ∀ i, tot (nxW G P Q s k₀ q₀ d i) ≤ cL * (c0 + 2 + 1) * Z := by
    intro d hd i
    have hsub := nxL_sublist G P Q s k₀ q₀ d i
    refine le_trans (tot_le (B := (c0 + 2) * Y ^ a0) ?_) ?_
    · intro w hw
      simp only [nxW, List.mem_map] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact hitem (d + 1) hd x (hsub.subset hx)
    · rw [show (nxW G P Q s k₀ q₀ d i).length = (nxL G P Q s k₀ q₀ d i).length by simp [nxW]]
      exact cnt_mul (A := A) hY1 (le_trans hsub.length_le (hcnt (d + 1) hd)) le_rfl (by omega)
  -- the outputs
  have hkid : kidB k₀ q₀ T ≤ (3 + SC) * Y ^ (q₀ + 1) := by
    have ek : kidB k₀ q₀ T = 3 + SC * (T + 1) ^ (q₀ + 1) := rfl
    rw [ek]
    have h1 : (T + 1) ^ (q₀ + 1) ≤ Y ^ (q₀ + 1) := Nat.pow_le_pow_left (by omega) _
    have h2 : 1 ≤ Y ^ (q₀ + 1) := Nat.one_le_pow _ _ hY1
    have h3 : SC * (T + 1) ^ (q₀ + 1) ≤ SC * Y ^ (q₀ + 1) := Nat.mul_le_mul_left _ h1
    rw [add_mul]; omega
  have houtW : ∀ d ≤ q₀, ∀ i, tot ((outW G P Q s k₀ q₀ d).take i) ≤ cL * (3 + SC + 1) * Z := by
    intro d hd i
    refine le_trans (tot_le (B := (3 + SC) * Y ^ (q₀ + 1)) ?_) ?_
    · intro w hw
      exact le_trans (outW_mem_le G P Q s k₀ q₀ hk hd w (List.mem_of_mem_take hw)) hkid
    · refine cnt_mul (A := A) (aL := q₀) hY1 (le_trans (List.take_sublist _ _).length_le ?_) le_rfl (by omega)
      rw [length_outW]; exact hcnt d hd
  have houtW' : ∀ d ≤ q₀, tot (outW G P Q s k₀ q₀ d) ≤ cL * (3 + SC + 1) * Z := by
    intro d hd
    have := houtW d hd (outW G P Q s k₀ q₀ d).length
    rwa [List.take_length] at this
  -- the scatter type
  have hSG : tot (stp G k₀ q₀).words ≤ cS * Z := by
    have h1 := hS 0 (Nat.zero_le _) n G
    simp only [Nat.add_zero, Nat.sub_zero, ← hM] at h1
    have e : wordLength (stp G k₀ q₀) = 1 + tot (stp G k₀ q₀).words := length_toWord_ws _
    have h2 : cS * (n + 1) * (M + 1) ^ aS ≤ cS * Z := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left (by omega) _)
        (Nat.pow_le_pow_right hY1 (by omega))))
    omega
  have hCT : (ctW G P Q).length + 1 ≤ 4 * Z := by
    have := ctW_len G P Q
    have : n + 1 ≤ Z := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hY1)
    omega
  have hLL : ∀ L : List ℕ, L.length ≤ q₀ + 2 → L.length + 1 ≤ (q₀ + 3) * Z := by
    intro L hL
    have : (q₀ + 3) ≤ (q₀ + 3) * Z := Nat.le_mul_of_pos_right _ hZ1
    omega
  have hE1 : ∀ K, 1 ≤ K → ([] : List ℕ).length + 1 ≤ K * Z := by
    intro K hK; simp only [List.length_nil]; nlinarith
  -- the cases
  have hfinal : ∀ (w : SW), w.CT.length + 1 ≤ 4 * Z → w.SH.length + 1 ≤ (cH + 1) * Z →
      w.AT.length + 1 ≤ (cA + 1) * Z → w.LL.length + 1 ≤ (q₀ + 3) * Z → tot w.SG ≤ cS * Z →
      tot w.FA ≤ (1 * (c1 + 1)) * Z → tot w.CO ≤ (1 * (cC + 1)) * Z → tot w.LV ≤ ((q₀ + 2) * (cL * (c0 + 2 + 1))) * Z → tot w.OU ≤ (2 * (cL * (3 + SC + 1))) * Z →
      18 + (w.CT.length + 1) + (w.SH.length + 1) + (w.AT.length + 1) + (w.LL.length + 1) +
        tot w.SG + tot w.FA + tot w.CO + tot w.LV + tot w.OU ≤
        (18 + 4 + (cH + 1) + (cA + 1) + (q₀ + 3) + cS + (1 * (c1 + 1)) + (1 * (cC + 1)) + ((q₀ + 2) * (cL * (c0 + 2 + 1))) + (2 * (cL * (3 + SC + 1)))) * (n + 1) * Y ^ A := by
    intro w h1 h2 h3 h4 h5 h6 h7 h8 h9
    have e : (18 + 4 + (cH + 1) + (cA + 1) + (q₀ + 3) + cS + (1 * (c1 + 1)) + (1 * (cC + 1)) + ((q₀ + 2) * (cL * (c0 + 2 + 1))) + (2 * (cL * (3 + SC + 1)))) * (n + 1) * Y ^ A =
        18 * Z + 4 * Z + (cH + 1) * Z + (cA + 1) * Z + (q₀ + 3) * Z + cS * Z + (1 * (c1 + 1)) * Z + (1 * (cC + 1)) * Z + ((q₀ + 2) * (cL * (c0 + 2 + 1))) * Z +
          (2 * (cL * (3 + SC + 1))) * Z := by simp only [Z]; ring
    have : 18 ≤ 18 * Z := Nat.le_mul_of_pos_right _ hZ1
    omega
  rw [stOf_eq]
  have hKLV : ∀ d ≤ q₀, ∀ X : List (List ℕ), tot X ≤ cL * (c0 + 2 + 1) * Z →
      tot (lvsW G P Q s k₀ q₀ d ++ X) ≤ ((q₀ + 2) * (cL * (c0 + 2 + 1))) * Z := by
    intro d hd X hX
    rw [tot_append]
    have h1 := hlvsW d hd
    have e : ((q₀ + 2) * (cL * (c0 + 2 + 1))) * Z = (q₀ + 2) * (cL * (c0 + 2 + 1) * Z) := by ring
    have h2 : (d + 1) * (cL * (c0 + 2 + 1) * Z) ≤ (q₀ + 1) * (cL * (c0 + 2 + 1) * Z) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [e, show q₀ + 2 = (q₀ + 1) + 1 by ring, add_mul, one_mul]
    omega
  have hstp : ∀ w : SW, w = ⟨[], [], [], [], [], [], [], [], []⟩ →
      18 + (w.CT.length + 1) + (w.SH.length + 1) + (w.AT.length + 1) + (w.LL.length + 1) +
        tot w.SG + tot w.FA + tot w.CO + tot w.LV + tot w.OU ≤
        (18 + 4 + (cH + 1) + (cA + 1) + (q₀ + 3) + cS + (1 * (c1 + 1)) + (1 * (cC + 1)) + ((q₀ + 2) * (cL * (c0 + 2 + 1))) + (2 * (cL * (3 + SC + 1)))) * (n + 1) * Y ^ A := by
    rintro w rfl
    exact hfinal _ (hE1 _ (by omega)) (hE1 _ (by omega)) (hE1 _ (by omega))
      (hE1 _ (by omega)) (by simp [tot]) (by simp [tot]) (by simp [tot]) (by simp [tot]) (by simp [tot])
  cases c with
    | stp => exact hstp _ rfl
    | fin => exact hstp _ rfl
    | dn d i m =>
      rcases hc with h | h | hv
      · cases h
      · cases h
      obtain ⟨hd, hi, hm⟩ := hv
      have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
        rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
      set τ := (itm G P Q s k₀ q₀ d i).2 with hτ
      obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk d hd.le _ hx
      have hfaP : (faP G (dataOf G P Q s k₀ q₀) τ).length ≤ T := by
        rw [hτ, hwx, show q₀ - d = (q₀ - d - 1) + 1 by omega]
        exact length_faP_leT G P Q s k₀ q₀ hk (show d + (q₀ - d - 1 + 1) = q₀ by omega) w hw
      have hSH := hH d hd n G P Q s _ hx
      simp only [← hM, ← hτ] at hSH
      refine hfinal _ hCT ?_ (hE1 _ (by omega)) (hLL _ ?_) hSG ?_ ?_ (hKLV d hd.le _ (hnxW d hd i))
        (by simp [swAt, tot])
      · show (if 1 ≤ m then toWord (shOf G τ) else []).length + 1 ≤ (cH + 1) * Z
        split_ifs
        · have : wordLength (shOf G τ) ≤ cH * Z := le_trans (by omega) (hMY cH aH (by omega))
          have : (toWord (shOf G τ)).length + 1 ≤ (cH + 1) * Z := by
            show wordLength (shOf G τ) + 1 ≤ _; rw [add_mul, one_mul]; omega
          exact this
        · exact hE1 _ (by omega)
      · show (llW G P Q s k₀ q₀ d ++ [(nxL G P Q s k₀ q₀ d i).length]).length ≤ q₀ + 2
        simp only [List.length_append, llW_length, List.length_singleton]; omega
      · show tot (if 2 ≤ m then (faP G (dataOf G P Q s k₀ q₀) τ).map toWord else []) ≤ (1 * (c1 + 1)) * Z
        split_ifs
        · refine le_trans (tot_le (B := c1 * Y ^ a1) ?_) ?_
          · intro v hv
            obtain ⟨ν, hν, rfl⟩ := List.mem_map.1 hv
            have := hF d hd n G P Q s _ hx ν (List.mem_filter.1 hν).1
            exact le_trans this (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
          · rw [List.length_map]
            exact cnt_mul (A := A) hY1 (le_trans hfaP hTc) le_rfl (by omega)
        · simp [tot]
      · show tot ((coW G P Q s k₀ q₀ τ).take (m - 2)) ≤ (1 * (cC + 1)) * Z
        refine le_trans (tot_le (B := cC * Y ^ aC) ?_) ?_
        · intro v hv
          have hv' := List.mem_of_mem_take hv
          simp only [coW, List.mem_map] at hv'
          obtain ⟨ν, hν, rfl⟩ := hv'
          have := hC d hd n G P Q s _ hx ν (List.mem_filter.1 hν).1
          simp only [← hτ, ← hM] at this
          have h2 : wordLength (coOf G (shOf G τ) ν) ≤ cC * (M + 1) ^ aC := by omega
          exact le_trans h2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
        · refine cnt_mul (A := A) (aL := 1) hY1 (le_trans (List.take_sublist _ _).length_le ?_) le_rfl
            (by omega)
          rw [length_coW]; exact le_trans hfaP hTc
    | up d i m =>
      rcases hc with h | h | hv
      · cases h
      · cases h
      obtain ⟨hd, hi, hm⟩ := hv
      have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
        rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
      set τ := (itm G P Q s k₀ q₀ d i).2 with hτ
      refine hfinal _ hCT (hE1 _ (by omega)) ?_ (hLL _ ?_) hSG (by simp [swAt, tot])
        (by simp [swAt, tot]) (by have h := hKLV q₀ le_rfl [] (by simp [tot]); rw [List.append_nil] at h; exact h) ?_
      · show (if m = 1 then canonW (atomQ G P Q s k₀ q₀ τ) else []).length + 1 ≤ (cA + 1) * Z
        split_ifs
        · have h1 := realY_le (G := G) (k₀ := k₀) (q₀ := q₀) hk (c := .canon (atomQ G P Q s k₀ q₀ τ))
            trivial
          have h2 := atomQ_le G P Q s k₀ q₀ hk hd hx
          simp only [← hτ, ← hT] at h2
          have h3 := upW_le k₀ q₀ T
          have h4 : wordLength (atomQ G P Q s k₀ q₀ τ) ≤ upCst k₀ q₀ * (T + 1) ^ (q₀ + 2) := by
            omega
          have h5 := pc_comp (d := cCa) (b := aCa) h4
          have h6 : (canonW (atomQ G P Q s k₀ q₀ τ)).length ≤ cA * (T + 1) ^ aA := by
            refine le_trans h1 (le_trans h5 ?_)
            show cCa * (upCst k₀ q₀ + 1) ^ aCa * (T + 1) ^ ((q₀ + 2) * aCa) ≤ _
            exact le_rfl
          have h7 : cA * (T + 1) ^ aA ≤ cA * Z :=
            le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) (pow_Z hY1 (by omega))
          rw [show (cA + 1) * Z = cA * Z + Z by ring]
          omega
        · exact hE1 _ (by omega)
      · show (llW G P Q s k₀ q₀ q₀).length ≤ q₀ + 2
        rw [llW_length]; omega
      · show tot ((if d < q₀ then outW G P Q s k₀ q₀ (d + 1) else []) ++ outP G P Q s k₀ q₀ d i) ≤
          (2 * (cL * (3 + SC + 1))) * Z
        rw [tot_append]
        have h2 := houtW d hd i
        have h1 : tot (if d < q₀ then outW G P Q s k₀ q₀ (d + 1) else []) ≤
            cL * (3 + SC + 1) * Z := by
          split_ifs with h
          · exact houtW' (d + 1) h
          · simp [tot]
        have e : (2 * (cL * (3 + SC + 1))) * Z = cL * (3 + SC + 1) * Z + cL * (3 + SC + 1) * Z := by ring
        unfold outP
        omega

/-- **The length of the state of round `j`.** -/
theorem stOf_cur_len (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ j ≤ (rcalls G P Q s k₀ q₀).length,
      (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).length ≤
        C * (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A := by
  obtain ⟨C, A, h⟩ := stOf_len k₀ q₀ hk
  refine ⟨C, A, fun n G P Q s j hj => h n G P Q s _ ?_⟩
  by_cases hn : n = 0
  · have : (rcalls G P Q s k₀ q₀).length = 0 := by simp [rcalls, hn]
    obtain rfl : j = 0 := by omega
    exact Or.inl rfl
  · rcases (rcalls_drop G P Q s k₀ q₀ (by omega) j hj).2 with hv | hf
    · exact Or.inr (Or.inr hv)
    · exact Or.inr (Or.inl hf)

end Lax185574Proofs.ResolveRam.Glue
