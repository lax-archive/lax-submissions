import Lax185574Proofs.ResolveRam.SizeGlue.State
import Lax185574Proofs.ResolveRam.EntCalls

/-!
The entries of the heads of the glue program of lem:resolve-lift.

Let `x` be the input, `X` its largest entry, `M` the largest size of a
tree of the family, `T = treeCount` and `Y = M + T + 1`. The scalars
of the state are `ySz x`, `|x|`, `n`, `P`, `Q` (entries of `x`), the
sign, the rank, the position and the numbers of words of four fields.
The words of the state are the color table (colors and distances, at
most `X` and `n`), trees of `G` and of `H` and members of the scatter
type (at most their length plus `cK k₀ q₀` plus `X`, by `good_tree`
and `good_stp_mem`), item words (a parent, a guard and a tree), the
answer of the canonical form on atom words and the lengths of the
levels. So every entry of the state at a position that carries a call is
at most the length of the state plus `cK k₀ q₀` plus `ySz x` plus a
constant times `(n + 1) Y^{q₀}` plus `T` (`stOf_ent`). With the bound on
the length of the state (`stOf_len`) this gives the bound on the heads
(`heads_clause`), with no term in `‖H‖`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.DistanceLogic
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words Lax185574Proofs.TypeTreeSizes
open Lax185574Proofs.MC

/-! ### Words of lists of words -/

theorem mem_toWord_ws {ws : List (List ℕ)} {e : ℕ} (he : e ∈ toWord ws) :
    e = ws.length ∨ ∃ w ∈ ws, e = w.length ∨ e ∈ w := by
  change e ∈ ws.length :: (ws.map toWord).flatten at he
  rcases List.mem_cons.1 he with h | h
  · exact Or.inl h
  · obtain ⟨u, hu, heu⟩ := List.mem_flatten.1 h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    rw [toWord_listNat] at heu
    rcases List.mem_cons.1 heu with h2 | h2
    · exact Or.inr ⟨w, hw, Or.inl h2⟩
    · exact Or.inr ⟨w, hw, Or.inr h2⟩

theorem length_lt_tot {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) : w.length < tot ws := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun w : List ℕ => w.length + 1) hw)
  unfold tot; omega

theorem length_le_tot (ws : List (List ℕ)) : ws.length ≤ tot ws := by
  induction ws with
  | nil => simp [tot]
  | cons w ws ih => rw [tot_cons, List.length_cons]; omega

/-! ### The input -/

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem P_le_x : P ≤ maxEntry (xIn G k₀ q₀ P Q s) := by
  refine le_maxEntry ?_
  rw [toWord_xIn]
  simp

theorem Q_le_x : Q ≤ maxEntry (xIn G k₀ q₀ P Q s) := by
  refine le_maxEntry ?_
  rw [toWord_xIn]
  simp

/-! ### The items -/

/-- The parent of an item is an index into the previous level and its
guard is a position of the tuple of the parent. -/
theorem item_idx (hk : 1 ≤ k₀) : ∀ d ≤ q₀, ∀ x ∈ lvR G P Q s k₀ q₀ d,
    x.1.1 ≤ ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ * (n + 1) *
      (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ q₀ ∧ x.1.2 ≤ q₀
  | 0, _, x, hx => by
    simp only [lvR, levels, Function.iterate_zero, id, famItems, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    simp
  | d + 1, hd, x, hx => by
    unfold lvR at hx
    rw [levels_succ] at hx
    obtain ⟨i, hi, gc, hgc, rfl⟩ := mem_nextLevel.1 hx
    obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk d (by omega) _ (List.getElem_mem hi)
    obtain ⟨m, hm⟩ : ∃ m, q₀ - d = m + 1 := ⟨q₀ - d - 1, by omega⟩
    rw [hwx, hm] at hgc
    obtain ⟨e, -, rfl⟩ := (expandOK_exR G P Q s k₀ q₀ (k₀ + d) m (d + 1) w (by omega) (by omega)
      (by omega) (by omega) gc).1 hgc
    refine ⟨le_trans hi.le (lvR_len G P Q s k₀ q₀ hk (by omega)), ?_⟩
    have := e.1.isLt
    simp only
    omega

local notation "KK" => cK k₀ q₀
local notation "XX" => maxEntry (xIn G k₀ q₀ P Q s)
local notation "LB" => ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ * (n + 1) *
  (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ q₀

theorem good_treeG {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (hk : k < entN k₀ q₀) (hq : q < entN k₀ q₀)
    (hℓ : ℓ < entN k₀ q₀) : Good KK XX (toWord (tree G k q u)) :=
  good_tree G k q u (tree_le_cK hk hq hℓ) (color_le_x G P Q s k₀ q₀)

/-- The entries of an item word. -/
theorem itemW_ent (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    ∀ e ∈ itemW x, e ≤ (itemW x).length + KK + XX + LB + q₀ := by
  obtain ⟨h1, h2⟩ := item_idx G P Q s k₀ q₀ hk d hd x hx
  obtain ⟨ℓ, u, hu, hℓ1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd hx
  have g := good_treeG G P Q s k₀ q₀ u (k := k₀ + d) (q := q₀ - d) (by unfold entN; omega)
    (by unfold entN; omega) (by unfold entN; omega)
  rw [← hu] at g
  intro e he
  simp only [itemW, List.mem_cons] at he
  have hl : (itemW x).length = 2 + (toWord x.2).length := by simp [itemW]; omega
  rcases he with rfl | rfl | he
  · omega
  · omega
  · have := g e he; omega

/-! ### The words of the state -/

theorem mem_ws {w : SW} {v : List ℕ} (h : v ∈ w.ws) :
    v = w.CT ∨ v = w.SH ∨ v = w.AT ∨ v = w.LL ∨ v ∈ w.SG ∨ v ∈ w.FA ∨ v ∈ w.CO ∨ v ∈ w.LV ∨
      v ∈ w.OU := by
  simp only [SW.ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  tauto

/-- The entries of the words of the state at a position that carries a
call. -/
theorem sw_ent (hk : 1 ≤ k₀) (c : Cur) (hc : c = .stp ∨ c = .fin ∨ Valid G P Q s k₀ q₀ c) :
    ∀ w ∈ (swAt G P Q s k₀ q₀ c).ws, ∀ e ∈ w, e ≤ w.length + KK + XX + LB + q₀ + 5 := by
  have hcol := color_le_x G P Q s k₀ q₀
  have hnX := n_le_x G P Q s k₀ q₀
  -- the color table
  have hCT : ∀ e ∈ ctW G P Q, e ≤ XX := by
    intro e he
    simp only [ctW, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
    obtain ⟨Y, hY, h⟩ := he
    simp only [colsL, Finset.mem_sort, colsCore, Finset.mem_image, Finset.mem_univ,
      true_and] at hY
    obtain ⟨v, rfl⟩ := hY
    rcases h with rfl | rfl | rfl
    · exact hcol v
    · exact le_trans (cTab_le G _ _) hnX
    · exact le_trans (cTab_le G _ _) hnX
  -- the scatter type
  have hSG : ∀ w ∈ (stp G k₀ q₀).words, ∀ e ∈ w, e ≤ w.length + KK + XX := by
    intro w hw e he
    obtain ⟨p, hp, rfl⟩ := mem_words.1 hw
    exact good_stp_mem G P Q s k₀ q₀ hp e he
  -- the levels
  have hLV : ∀ d ≤ q₀, ∀ w ∈ lvsW G P Q s k₀ q₀ d, ∀ e ∈ w, e ≤ w.length + KK + XX + LB + q₀ := by
    intro d hd w hw
    simp only [lvsW, lvW, List.mem_flatMap, List.mem_range, List.mem_map] at hw
    obtain ⟨d', hd', x, hx, rfl⟩ := hw
    exact itemW_ent G P Q s k₀ q₀ hk (by omega) hx
  have hNX : ∀ d < q₀, ∀ i, ∀ w ∈ nxW G P Q s k₀ q₀ d i, ∀ e ∈ w,
      e ≤ w.length + KK + XX + LB + q₀ := by
    intro d hd i w hw
    simp only [nxW, List.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact itemW_ent G P Q s k₀ q₀ hk (d := d + 1) (by omega)
      ((nxL_sublist G P Q s k₀ q₀ d i).subset hx)
  have hLL : ∀ d ≤ q₀, ∀ e ∈ llW G P Q s k₀ q₀ d, e ≤ LB := by
    intro d hd e he
    simp only [llW, List.mem_map, List.mem_range] at he
    obtain ⟨d', hd', rfl⟩ := he
    exact lvR_len G P Q s k₀ q₀ hk (by omega)
  -- the outputs
  have hOU : ∀ d ≤ q₀, ∀ w ∈ outW G P Q s k₀ q₀ d, ∀ e ∈ w, e ≤ w.length + KK + XX := by
    intro d hd w hw e he
    simp only [outW, List.mem_map] at hw
    obtain ⟨τ, hτ, rfl⟩ := hw
    rw [outR_eq_lift G P Q s hk hd] at hτ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hτ
    obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd hx
    have e1 : liftT (dataOf G P Q s k₀ q₀) (farMapOf G) x.2 =
        tree (resolveBy G s P Q) (k₀ + d) (q₀ - d) u := by
      rw [hu]
      simp only [liftT, tree]
      rw [resolveNodeF_node _ (farMapOf G) (dataOf_spec G P Q s k₀ q₀) (farSpec_farMapOf G)
        (q₀ - d) (k₀ + d) u h1 hℓ (by omega) (by omega)]
      rfl
    rw [e1] at he ⊢
    refine good_tree _ _ _ u (tree_le_cK (by unfold entN; omega) (by unfold entN; omega)
      (by unfold entN; omega)) (fun v => ?_) e he
    rw [resolveBy_color]; exact hcol v
  intro w hw e he
  cases c with
  | stp => simp [swAt, SW.ws] at hw; rcases hw with rfl | rfl | rfl | rfl <;> simp at he
  | fin => simp [swAt, SW.ws] at hw; rcases hw with rfl | rfl | rfl | rfl <;> simp at he
  | dn d i m =>
    rcases hc with h | h | ⟨hd, hi, hm⟩
    · cases h
    · cases h
    have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
      rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
    obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
    rw [show q₀ - d = q₀ - d - 1 + 1 by omega] at hu
    rcases mem_ws hw with rfl | rfl | rfl | rfl | h | h | h | h | h
    · have := hCT e he; omega
    · by_cases h1m : 1 ≤ m
      · have hl : (swAt G P Q s k₀ q₀ (.dn d i m)).SH =
            toWord (tree G (k₀ + d + 1) (q₀ - d - 1) u) := by
          simp only [swAt, h1m, if_true]; rw [hu, shOf_tree G u h1 hℓ]
        rw [hl] at he ⊢
        have := good_treeG G P Q s k₀ q₀ u (k := k₀ + d + 1) (q := q₀ - d - 1)
          (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega) e he
        omega
      · simp [swAt, h1m] at he
    · simp [swAt] at he
    · have he' : e ∈ llW G P Q s k₀ q₀ d ++ [(nxL G P Q s k₀ q₀ d i).length] := he
      rcases List.mem_append.1 he' with he | he
      · have := hLL d hd.le e he; omega
      · rw [List.mem_singleton] at he
        subst he
        have := (nxL_sublist G P Q s k₀ q₀ d i).length_le
        have := lvR_len G P Q s k₀ q₀ hk (d := d + 1) (by omega)
        omega
    · have := hSG w h e he; omega
    · have h' : w ∈ (if 2 ≤ m then (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord
          else []) := h
      split_ifs at h'
      · obtain ⟨ν, hν, rfl⟩ := List.mem_map.1 h'
        rw [hu] at hν
        obtain ⟨b, -, rfl⟩ := faOf_tree G hd h1 hℓ (List.mem_filter.1 hν).1
        have := good_treeG G P Q s k₀ q₀ ![b] (k := k₀ + d + 1) (q := q₀ - d - 1)
          (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega) e he
        omega
      · simp at h'
    · have h' : w ∈ (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).take (m - 2) := h
      have h'' := List.mem_of_mem_take h'
      simp only [coW, List.mem_map] at h''
      obtain ⟨ν, hν, rfl⟩ := h''
      rw [hu] at hν he ⊢
      obtain ⟨b, hb, rfl⟩ := faOf_tree G hd h1 hℓ (List.mem_filter.1 hν).1
      rw [shOf_tree G u h1 hℓ, coOf_tree G u b h1 hℓ hb] at he ⊢
      have := good_treeG G P Q s k₀ q₀ (Fin.snoc u b) (k := k₀ + d + 1) (q := q₀ - d - 1)
        (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega) e he
      omega
    · have h' : w ∈ lvsW G P Q s k₀ q₀ d ++ nxW G P Q s k₀ q₀ d i := h
      rcases List.mem_append.1 h' with h | h
      · have := hLV d hd.le w h e he; omega
      · have := hNX d hd i w h e he; omega
    · have h' : w ∈ ([] : List (List ℕ)) := h
      simp at h'
  | up d i m =>
    rcases hc with h | h | ⟨hd, hi, hm⟩
    · cases h
    · cases h
    have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
      rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
    obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd hx
    rcases mem_ws hw with rfl | rfl | rfl | rfl | h | h | h | h | h
    · have := hCT e he; omega
    · simp [swAt] at he
    · by_cases hm1 : m = 1
      · subst hm1
        have hl : (swAt G P Q s k₀ q₀ (.up d i 1)).AT =
            canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) := by simp [swAt]
        rw [hl] at he ⊢
        rcases canonW_entry he with h2 | ⟨w', hw', hew⟩
        · omega
        · have hk' : (itm G P Q s k₀ q₀ d i).2.k < entN k₀ q₀ := by
            rw [hu]; unfold entN; simp only [tree]; omega
          have hq' : (itm G P Q s k₀ q₀ d i).2.q < entN k₀ q₀ := by
            rw [hu]; unfold entN; simp only [tree]; omega
          have hl' : (itm G P Q s k₀ q₀ d i).2.ℓ < entN k₀ q₀ := by
            rw [hu]; unfold entN; simp only [tree]; omega
          have g := good_atomQ G P Q s k₀ q₀ (d := d) hk' hq' hl' w' hw' e hew
          have hlen : w'.length ≤ 5 := by
            simp only [atomQ, List.mem_map] at hw'
            obtain ⟨φ, hφ, rfl⟩ := hw'
            exact wordLength_atom_le φ (isAtom_candL (List.mem_filter.1 hφ).1)
          omega
      · simp [swAt, hm1] at he
    · have he' : e ∈ llW G P Q s k₀ q₀ q₀ := he
      have := hLL q₀ le_rfl e he'; omega
    · have := hSG w h e he; omega
    · have h' : w ∈ ([] : List (List ℕ)) := h
      simp at h'
    · have h' : w ∈ ([] : List (List ℕ)) := h
      simp at h'
    · have := hLV q₀ le_rfl w h e he; omega
    · have h' : w ∈ (if d < q₀ then outW G P Q s k₀ q₀ (d + 1) else []) ++
          outP G P Q s k₀ q₀ d i := h
      rcases List.mem_append.1 h' with h | h
      · split_ifs at h with hdq
        · have := hOU (d + 1) hdq w h e he; omega
        · simp at h
      · have := hOU d hd w (List.mem_of_mem_take h) e he; omega

/-- **The entries of the state.** At the start, at the end and at every
position that carries a call, every entry of the state is at most the
length of the state plus `cK k₀ q₀`, `ySz x`, a constant times `(n + 1)
Y^{q₀}` and `T + k₀ + q₀ + 5`. -/
theorem stOf_ent (hk : 1 ≤ k₀) (c : Cur) (hc : c = .stp ∨ c = .fin ∨ Valid G P Q s k₀ q₀ c) :
    ∀ e ∈ stOf G P Q s k₀ q₀ c, e ≤ (stOf G P Q s k₀ q₀ c).length + KK +
      ySz (xIn G k₀ q₀ P Q s) + LB + treeCount G (resolveBy G s P Q) k₀ q₀ + k₀ + q₀ + 5 := by
  have hX : XX + 1 ≤ ySz (xIn G k₀ q₀ P Q s) := by unfold ySz; omega
  have hnX := n_le_x G P Q s k₀ q₀
  have hPX := P_le_x G P Q s k₀ q₀
  have hQX := Q_le_x G P Q s k₀ q₀
  have hW := sw_ent G P Q s k₀ q₀ hk c hc
  set ws := (swAt G P Q s k₀ q₀ c).ws
  have hlen : (stOf G P Q s k₀ q₀ c).length = (scW G P Q s k₀ q₀ c).length + 1 + tot ws := by
    rw [stOf, List.length_append, length_toWord_ws]; ring
  have hscW : (scW G P Q s k₀ q₀ c).length = 17 := by
    unfold scW curW; cases c <;> simp
  have hfield : (swAt G P Q s k₀ q₀ c).SG.length + (swAt G P Q s k₀ q₀ c).FA.length +
      (swAt G P Q s k₀ q₀ c).CO.length + (swAt G P Q s k₀ q₀ c).LV.length ≤ tot ws := by
    have e : tot ws = ((swAt G P Q s k₀ q₀ c).CT.length + 1) + ((swAt G P Q s k₀ q₀ c).SH.length + 1) +
        ((swAt G P Q s k₀ q₀ c).AT.length + 1) + ((swAt G P Q s k₀ q₀ c).LL.length + 1) +
        tot (swAt G P Q s k₀ q₀ c).SG + tot (swAt G P Q s k₀ q₀ c).FA +
        tot (swAt G P Q s k₀ q₀ c).CO + tot (swAt G P Q s k₀ q₀ c).LV +
        tot (swAt G P Q s k₀ q₀ c).OU := by
      simp only [ws, SW.ws, tot_append, tot_cons, tot_nil]; ring
    have := length_le_tot (swAt G P Q s k₀ q₀ c).SG
    have := length_le_tot (swAt G P Q s k₀ q₀ c).FA
    have := length_le_tot (swAt G P Q s k₀ q₀ c).CO
    have := length_le_tot (swAt G P Q s k₀ q₀ c).LV
    omega
  have hcur : ∀ e ∈ curW c, e ≤ LB + treeCount G (resolveBy G s P Q) k₀ q₀ + q₀ + 3 := by
    intro e he
    cases c with
    | stp => simp [curW] at he; omega
    | fin => simp [curW] at he; omega
    | dn d i m =>
      rcases hc with h | h | ⟨hd, hi, hm⟩
      · cases h
      · cases h
      have h1 := lvR_len G P Q s k₀ q₀ hk hd.le
      have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
        rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
      obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk d hd.le _ hx
      have h2 := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
      have h3 : (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length ≤
          treeCount G (resolveBy G s P Q) k₀ q₀ := by
        rw [hwx, show q₀ - d = (q₀ - d - 1) + 1 by omega]
        exact length_faP_leT G P Q s k₀ q₀ hk (show d + (q₀ - d - 1 + 1) = q₀ by omega) w hw
      simp only [curW, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> omega
    | up d i m =>
      rcases hc with h | h | ⟨hd, hi, hm⟩
      · cases h
      · cases h
      have h1 := lvR_len G P Q s k₀ q₀ hk hd
      have h2 : nUp q₀ d ≤ 2 := by unfold nUp; split_ifs <;> omega
      simp only [curW, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> omega
  have hxl : (xIn G k₀ q₀ P Q s).length ≤ ySz (xIn G k₀ q₀ P Q s) := by unfold ySz; omega
  intro e he
  have he' : e ∈ scW G P Q s k₀ q₀ c ++ toWord ws := he
  rcases List.mem_append.1 he' with h | h
  · simp only [scW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with ((h | h | h | h | h | h | h | h | h) | h) | (h | h | h | h)
    all_goals first
      | omega
      | (split_ifs at h <;> omega)
      | (have := hcur e h; omega)
  · rcases mem_toWord_ws h with h | ⟨w, hw, h | h⟩
    · have := length_le_tot ws; omega
    · have := length_lt_tot hw; omega
    · have := length_lt_tot hw
      have := hW w hw e h
      omega

/-- **The heads.** Every head of the glue program has size at most a
constant times `ySz x + (n + 1) Y^A`, with no term in `‖H‖`. -/
theorem heads_clause (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ j < (rcalls G P Q s k₀ q₀).length,
      ySz (hdJ G P Q s k₀ q₀ j) ≤ C * (ySz (xIn G k₀ q₀ P Q s) + (n + 1) *
        (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A) := by
  obtain ⟨C1, A1, hL⟩ := stOf_cur_len k₀ q₀ hk
  set cL := ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀
  set A := A1 + q₀ + 1
  refine ⟨2 * C1 + cL + 1 + cK k₀ q₀ + k₀ + q₀ + 20, A, fun n G P Q s j hj => ?_⟩
  have hn : 1 ≤ n := by
    by_contra h0
    have : (rcalls G P Q s k₀ q₀).length = 0 := by simp [rcalls, show n = 0 by omega]
    omega
  obtain ⟨hv, -⟩ := rcalls_get G P Q s k₀ q₀ hn hj
  set c := cur G P Q s k₀ q₀ j with hc
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hTd
  set Y := maxTreeSize G k₀ q₀ + T + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  set Z := (n + 1) * Y ^ A with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_iff_ne_zero.2 (by positivity)
  set S := (stOf G P Q s k₀ q₀ c).length
  have hS : S ≤ C1 * Z := by
    refine le_trans (hL n G P Q s j hj.le) ?_
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega)))
  have hLB : cL * (n + 1) * Y ^ q₀ ≤ cL * Z := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega)))
  have hT : T ≤ Z := by
    have : T ≤ Y ^ A := le_trans (show T ≤ Y by omega) (Nat.le_self_pow (by omega) _)
    exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
  have hE := stOf_ent G P Q s k₀ q₀ hk c (Or.inr (Or.inr hv))
  rw [show ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ * (n + 1) *
      (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ q₀ =
      cL * (n + 1) * Y ^ q₀ from rfl] at hE
  have hxl : (xIn G k₀ q₀ P Q s).length ≤ ySz (xIn G k₀ q₀ P Q s) := by unfold ySz; omega
  have hwin : winOf G P Q s k₀ q₀ c ≤ (xIn G k₀ q₀ P Q s).length := by unfold winOf; split_ifs <;> omega
  have hmax : maxEntry (hdJ G P Q s k₀ q₀ j) ≤ S + cK k₀ q₀ + ySz (xIn G k₀ q₀ P Q s) + cL * (n + 1) * Y ^ q₀ +
      T + k₀ + q₀ + 5 + (xIn G k₀ q₀ P Q s).length + 1 := by
    have hhd : hdJ G P Q s k₀ q₀ j = tagOf G P Q s k₀ q₀ c :: S :: winOf G P Q s k₀ q₀ c ::
        stOf G P Q s k₀ q₀ c := rfl
    refine maxEntry_le_bound fun e he => ?_
    rw [hhd] at he
    simp only [tagOf, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | he
    · omega
    · omega
    · omega
    · exact le_trans (hE e he) (by omega)
  have hlen : (hdJ G P Q s k₀ q₀ j).length = S + 3 := by
    show (hdOf G P Q s k₀ q₀ c).length = S + 3
    simp [hdOf, S]
  have e : (2 * C1 + cL + 1 + cK k₀ q₀ + k₀ + q₀ + 20) * (ySz (xIn G k₀ q₀ P Q s) + Z) =
      (2 * C1 + cL + 1 + cK k₀ q₀ + k₀ + q₀ + 20) * ySz (xIn G k₀ q₀ P Q s) + 2 * (C1 * Z) + cL * Z + Z +
        (cK k₀ q₀ + k₀ + q₀ + 20) * Z := by ring
  have h1 : cK k₀ q₀ + k₀ + q₀ + 20 ≤ (cK k₀ q₀ + k₀ + q₀ + 20) * Z := Nat.le_mul_of_pos_right _ hZ1
  have h2 : 3 * ySz (xIn G k₀ q₀ P Q s) ≤ (2 * C1 + cL + 1 + cK k₀ q₀ + k₀ + q₀ + 20) * ySz (xIn G k₀ q₀ P Q s) :=
    Nat.mul_le_mul_right _ (by omega)
  have hy : ySz (hdJ G P Q s k₀ q₀ j) =
      (hdJ G P Q s k₀ q₀ j).length + maxEntry (hdJ G P Q s k₀ q₀ j) + 1 := rfl
  rw [hy, hlen, e]
  omega

end Lax185574Proofs.ResolveRam.Glue
