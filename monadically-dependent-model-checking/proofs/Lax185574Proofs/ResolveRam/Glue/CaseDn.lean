import Lax185574Proofs.ResolveRam.Glue.OutEq

/-!
The cases of a later round on the way down, on words.

The round at position `c` grows the library `ws ++ news` and writes the
state of the next position as ranges of it. Here: the rank shift
(`case_shift`): the news are the empty word and the answer, the next
position is `dn d i 1`, and its state is the old one with the answer of
the shift in place of `SH`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.Words

variable {n : ℕ} {G : PartialGraph (Fin n)} {P Q : ℕ} {s : Bool} {k₀ q₀ : ℕ}

theorem rng_one {L : List (List ℕ)} {i : ℕ} (h : i < L.length) : rng L i 1 = [L[i]] := by
  simp [rng, List.take_one, List.head?_drop, List.getElem?_eq_getElem h]

theorem rng_drop {L M : List (List ℕ)} {lo : ℕ} (h : lo ≤ L.length) :
    rng (L ++ M) lo (L.length - lo) = L.drop lo := by
  rw [rng_append_left (by omega)]
  simp [rng, List.take_of_length_le]

/-- The plan that replaces word `1` by the word `M0 + 1` of the library. -/
def psRep1 (M0 : ℕ) : List (ℕ × ℕ) := [(0, 1), (M0 + 1, 1), (2, M0 - 2)]

theorem SW.ws_eq (w : SW) : w.ws = w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO ++ w.LV ++ w.OU) := by
  simp [SW.ws]

theorem length_SW_ws (w : SW) : 4 ≤ w.ws.length := by rw [SW.ws_eq]; simp

theorem planW_rep1 (w : SW) (Y : List ℕ) :
    planW (w.ws ++ [[], Y]) (psRep1 w.ws.length) = ({ w with SH := Y } : SW).ws := by
  have h4 := length_SW_ws w
  simp only [planW, psRep1, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hY : (w.ws ++ [[], Y])[w.ws.length + 1]'(by simp) = Y := by
    rw [List.getElem_append_right (by omega)]; simp
  have h0 : (w.ws ++ [[], Y])[0]'(by simp) = w.CT := by
    rw [List.getElem_append_left (by omega)]; simp [SW.ws_eq]
  rw [rng_one (by simp), rng_one (by simp), rng_drop (by omega), hY, h0]
  simp [SW.ws_eq]

/-- **The rank shift.** -/
theorem case_shift {d i : ℕ} :
    planW ((swAt G P Q s k₀ q₀ (.dn d i 0)).ws ++
        [[], toWord (shOf G (itm G P Q s k₀ q₀ d i).2)]) (psRep1 (swAt G P Q s k₀ q₀ (.dn d i 0)).ws.length) =
      (swAt G P Q s k₀ q₀ (.dn d i 1)).ws := by
  rw [planW_rep1, sw_shift]

theorem rng_append_right {L M : List (List ℕ)} {lo N : ℕ} :
    rng (L ++ M) (L.length + lo) N = rng M lo N := by
  simp only [rng, List.drop_append, List.drop_eq_nil_of_le (show L.length ≤ L.length + lo by omega),
    List.nil_append, Nat.add_sub_cancel_left]

theorem rng_full (L : List (List ℕ)) : rng L 0 L.length = L := by simp [rng]

theorem rng_ws_SG (w : SW) (M : List (List ℕ)) : rng (w.ws ++ M) 4 w.SG.length = w.SG := by
  rw [SW.ws_eq]; simp [rng, List.take_append_of_le_length]

theorem rng_ws_LV (w : SW) (M : List (List ℕ)) :
    rng (w.ws ++ M) (4 + w.SG.length + w.FA.length + w.CO.length) w.LV.length = w.LV := by
  rw [SW.ws_eq]
  have : 4 + w.SG.length + w.FA.length + w.CO.length = (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO)).length := by
    simp; omega
  rw [this]
  simp only [List.cons_append, List.append_assoc]
  rw [show w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ (w.FA ++ (w.CO ++ (w.LV ++ (w.OU ++ M))))) =
    (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ (w.FA ++ w.CO))) ++ (w.LV ++ (w.OU ++ M)) by simp]
  have e := rng_append_right (L := w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ (w.FA ++ w.CO)))
    (M := w.LV ++ (w.OU ++ M)) (lo := 0) (N := w.LV.length)
  simp only [Nat.add_zero] at e
  rw [e]; simp [rng]

/-- The plan of the state after an item on the way down: the color table,
two empty words, the new lengths, the scatter type, and the old levels
followed by the expansion. -/
def psFin (w : SW) (M0 iLL e0 nE : ℕ) : List (ℕ × ℕ) :=
  [(0, 1), (M0, 1), (M0, 1), (iLL, 1), (4, w.SG.length),
    (4 + w.SG.length + w.FA.length + w.CO.length, w.LV.length), (e0, nE)]

/-- **The state after an item, on words.** The library is the old state
followed by `X`, whose word `0` is empty, words `e` to `e + |E| - 1` are
the expansion and word `l` the new lengths. -/
theorem planW_fin (w : SW) (X E : List (List ℕ)) (LL' : List ℕ) {e l : ℕ}
    (h0 : X[0]? = some []) (hl : X[l]? = some LL') (hE : rng X e E.length = E) :
    planW (w.ws ++ X) (psFin w w.ws.length (w.ws.length + l) (w.ws.length + e) E.length) =
      (⟨w.CT, w.SG, [], [], LL', [], [], w.LV ++ E, []⟩ : SW).ws := by
  have h4 := length_SW_ws w
  have hX0 : 0 < X.length := by by_contra h; rw [List.getElem?_eq_none (by omega)] at h0; simp at h0
  have hXl : l < X.length := by by_contra h; rw [List.getElem?_eq_none (by omega)] at hl; simp at hl
  have g0 : (w.ws ++ X)[w.ws.length]'(by simp; omega) = [] := by
    rw [List.getElem_append_right (by omega)]; simp only [Nat.sub_self]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h0)
  have gl : (w.ws ++ X)[w.ws.length + l]'(by simp; omega) = LL' := by
    rw [List.getElem_append_right (by omega)]; simp only [Nat.add_sub_cancel_left]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hl)
  have gc : (w.ws ++ X)[0]'(by simp; omega) = w.CT := by
    rw [List.getElem_append_left (by omega)]; simp [SW.ws_eq]
  simp only [planW, psFin, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rng_one (by simp; omega), rng_one (by simp; omega), rng_one (by simp; omega), g0, gc, gl,
    rng_ws_SG, rng_ws_LV, rng_append_right, hE]
  simp [SW.ws_eq]

/-- The plan that replaces word `2` by the word `M0 + 1` of the library. -/
def psRep2 (M0 : ℕ) : List (ℕ × ℕ) := [(0, 2), (M0 + 1, 1), (3, M0 - 3)]

theorem planW_rep2 (w : SW) (Y : List ℕ) :
    planW (w.ws ++ [[], Y]) (psRep2 w.ws.length) = ({ w with AT := Y } : SW).ws := by
  have h4 := length_SW_ws w
  simp only [planW, psRep2, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hY : (w.ws ++ [[], Y])[w.ws.length + 1]'(by simp) = Y := by
    rw [List.getElem_append_right (by omega)]; simp
  rw [rng_one (by simp), rng_drop (by omega), hY]
  have h2 : rng (w.ws ++ [[], Y]) 0 2 = [w.CT, w.SH] := by
    rw [rng_append_left (by omega)]; simp [rng, SW.ws_eq]
  rw [h2]
  simp [SW.ws_eq]

/-- **The atom words of an item with children.** -/
theorem case_atoms {d i : ℕ} :
    planW ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++
        [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2)])
        (psRep2 (swAt G P Q s k₀ q₀ (.up d i 0)).ws.length) =
      (swAt G P Q s k₀ q₀ (.up d i 1)).ws := by
  rw [planW_rep2, sw_atoms]

theorem SW.ws_eq' (w : SW) : w.ws = (w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO ++ w.LV)) ++ w.OU := by
  simp [SW.ws]

/-- The plan of the state after an item on the way up: the old state with
an empty word for `AT`, the outputs from `p` on and the new output word. -/
def psUp (w : SW) (M0 iW p : ℕ) : List (ℕ × ℕ) :=
  [(0, 2), (M0, 1), (3, M0 - 3 - w.OU.length), (M0 - w.OU.length + p, w.OU.length - p), (iW, 1)]

/-- **The state after an item on the way up, on words.** -/
theorem planW_up (w : SW) (X : List (List ℕ)) (wo : List ℕ) {j p : ℕ} (hp : p ≤ w.OU.length)
    (h0 : X[0]? = some []) (hj : X[j]? = some wo) :
    planW (w.ws ++ X) (psUp w w.ws.length (w.ws.length + j) p) =
      ({ w with AT := [], OU := w.OU.drop p ++ [wo] } : SW).ws := by
  have h4 := length_SW_ws w
  have hX0 : 0 < X.length := by by_contra h; rw [List.getElem?_eq_none (by omega)] at h0; simp at h0
  have hXj : j < X.length := by by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; simp at hj
  have hl : w.ws.length = 4 + w.SG.length + w.FA.length + w.CO.length + w.LV.length + w.OU.length := by
    rw [SW.ws_eq]; simp; omega
  have g0 : (w.ws ++ X)[w.ws.length]'(by simp; omega) = [] := by
    rw [List.getElem_append_right (by omega)]; simp only [Nat.sub_self]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans h0)
  have gj : (w.ws ++ X)[w.ws.length + j]'(by simp; omega) = wo := by
    rw [List.getElem_append_right (by omega)]; simp only [Nat.add_sub_cancel_left]
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hj)
  simp only [planW, psUp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rng_one (by simp; omega), rng_one (by simp; omega), g0, gj]
  have r1 : rng (w.ws ++ X) 0 2 = [w.CT, w.SH] := by
    rw [rng_append_left (by omega)]; simp [rng, SW.ws_eq]
  set A := w.CT :: w.SH :: w.AT :: w.LL :: (w.SG ++ w.FA ++ w.CO ++ w.LV) with hA
  have hwA : w.ws ++ X = A ++ (w.OU ++ X) := by rw [SW.ws_eq', List.append_assoc]
  have hAl : w.ws.length = A.length + w.OU.length := by rw [SW.ws_eq', List.length_append]
  have r2 : rng (w.ws ++ X) 3 (w.ws.length - 3 - w.OU.length) = w.LL :: (w.SG ++ w.FA ++ w.CO ++ w.LV) := by
    rw [hwA, rng_append_left (by omega), hAl]
    simp [rng, hA]
    omega
  have r3 : rng (w.ws ++ X) (w.ws.length - w.OU.length + p) (w.OU.length - p) = w.OU.drop p := by
    rw [hwA, hAl, show A.length + w.OU.length - w.OU.length + p = A.length + p by omega, rng_append_right,
      rng_append_left (by omega)]
    simp [rng]
  rw [r1, r2, r3]
  simp [SW.ws_eq]

end Lax185574Proofs.ResolveRam.Glue
