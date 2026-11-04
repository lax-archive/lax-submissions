import Lax185574Proofs.Words.TreeExts
import Lax185574Proofs.Words.ForLoop

/-!
The bound on the entries of a transformed tree word, the frames of the
hooks that transform the atoms and the extensions of a node, and the
size of the candidate lists of a node.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Array lengths -/

/-- A run never changes the length of an array. -/
theorem Run.length_arrs {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨k, -, hb⟩ := h.bigStep
  exact bigStep_length_arrs hb a

/-! ### Bounds on entries -/

theorem toWord_words_lt {B : ℕ} {ws : List (List ℕ)} (h1 : ws.length < B)
    (h2 : ∀ u ∈ ws, u.length < B) (h3 : ∀ u ∈ ws, ∀ v ∈ u, v < B) : ∀ v ∈ toWord ws, v < B := by
  intro v hv
  rw [toWord_words] at hv
  simp only [List.mem_cons, frames, List.mem_flatten, List.mem_map] at hv
  rcases hv with rfl | ⟨_, ⟨u, hu, rfl⟩, hv⟩
  · exact h1
  · simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact h2 u hu
    · exact h3 u hu v hv

theorem toWord_sortedDistinct_lt {B : ℕ} {ws : List (List ℕ)} (h1 : ws.length < B)
    (h2 : ∀ u ∈ ws, u.length < B) (h3 : ∀ u ∈ ws, ∀ v ∈ u, v < B) :
    ∀ v ∈ toWord (sortedDistinct ws), v < B :=
  toWord_words_lt (lt_of_le_of_lt (length_sortedDistinct_le ws) h1)
    (fun u hu => h2 u (mem_sortedDistinct.mp hu)) (fun u hu => h3 u (mem_sortedDistinct.mp hu))

theorem mem_frWord {X : List ℕ} {f v : ℕ} (h : v ∈ frWord X f) : v ∈ X :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem xg_mem {X : List ℕ} {i : ℕ} (h : i < X.length) : xg X i ∈ X := by
  rw [xg_of_lt h]; exact List.getElem_mem h

theorem atomMap_lt {B : ℕ} {S : List ℕ} {sub : ℕ → ℕ → ℕ → ℕ → Option ℕ} {d : ℕ}
    (hsub : ∀ tg k v r, v ∈ S → sub tg k d v = some r → r < B) {w u : List ℕ}
    (hw : ∀ v ∈ w, v ∈ S) (h : atomMap sub d w = some u) : ∀ v ∈ u, v < B := by
  rw [atomMap_eq] at h
  split_ifs at h with hall
  simp only [Option.some.injEq] at h
  subst h
  intro v hv
  simp only [List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk, rfl⟩ := hv
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hall k hk)
  have hwk : w.getD k 0 ∈ S := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact hw _ (List.getElem_mem hk)
  simp only [mapVal, hr, Option.getD_some]
  exact hsub _ _ _ _ hwk hr

/-- The entries of a transformed node are below `B` if the entries of
the input, its length, the depth plus height, and the values of `sub` and
`gsub` are. -/
theorem treeOut_lt {B : ℕ} (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ)
    (X : List ℕ) (hX : ∀ v ∈ X, v < B) (hXB : X.length < B) :
    ∀ (h d ℓ : ℕ) (p : ℕ) (t : Node h ℓ) (r : List ℕ), X.drop p = toWord t ++ r →
      (∀ tg k v r, v ∈ X → sub tg k d v = some r → r < B) →
      (∀ dd, d < dd → dd ≤ d + h → ∀ tg k v r, v ∈ X → sub tg k dd v = some r → r < B) →
      (∀ dd i r, d ≤ dd → dd < d + h → i ∈ X → gsub dd i = some r → r < B) →
      ∀ v ∈ treeOut sub gsub h d X p, v < B := by
  have hlen : ∀ h ℓ p (t : Node h ℓ) r, X.drop p = toWord t ++ r → (toWord t).length ≤ X.length :=
    fun h ℓ p t r hx => by have := le_of_drop_eq hx (toWord_node_ne_nil t); omega
  have hatoms : ∀ (d ℓ p : ℕ) (A : Finset (Lax185574.DistanceLogic.DistFO ℓ)) (r : List ℕ),
      X.drop p = toWord A.words ++ r → (toWord A.words).length ≤ X.length →
      (∀ tg k v r, v ∈ X → sub tg k d v = some r → r < B) →
      ∀ v ∈ toWord (sortedDistinct (atomCands sub d X p)), v < B := by
    intro d ℓ p A r hx hl hsub
    have hlw := length_toWord_words A.words
    rw [atomCands, listWords_eq hx]
    refine toWord_sortedDistinct_lt ?_ ?_ ?_
    · have := List.length_filterMap_le (atomMap sub d) A.words; omega
    · intro u hu
      obtain ⟨w, hw, hwu⟩ := List.mem_filterMap.mp hu
      rw [length_atomMap hwu]
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hw)
      simp only [total, List.length_flatten] at hlw
      omega
    · intro u hu v hv
      obtain ⟨w, hw, hwu⟩ := List.mem_filterMap.mp hu
      refine atomMap_lt hsub (fun v hv' => ?_) hwu v hv
      have := (List.mem_append_left r ((toWord_words A.words ▸ List.mem_cons_of_mem _
        (by simp only [frames, List.mem_flatten, List.mem_map]
            exact ⟨_, ⟨w, hw, rfl⟩, List.mem_cons_of_mem _ hv'⟩)) : v ∈ toWord A.words))
      rw [← hx] at this
      exact List.mem_of_mem_drop this
  intro h
  induction h with
  | zero =>
    intro d ℓ p t r hx hsub _ _
    rw [treeOut_zero]
    rw [toWord_node_zero] at hx
    exact hatoms d ℓ p _ r hx (by rw [← toWord_node_zero]; exact hlen _ _ _ _ _ (by rw [toWord_node_zero]; exact hx)) hsub
  | succ h ih =>
    intro d ℓ p t r hx hsub hsub' hg
    obtain ⟨h1, h2⟩ := nodeSplit hx
    have hl := hlen _ _ _ _ _ hx
    rw [toWord_node_succ, List.length_append] at hl
    rw [treeOut_succ]
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hatoms d ℓ p _ _ h1 (by omega) hsub v hv
    · have h0 := (listAt h2).1
      unfold extCands at hv
      rw [h0] at hv
      have hlw := length_toWord_words (Node.exts t).words
      refine toWord_sortedDistinct_lt ?_ ?_ ?_ v hv
      · have := List.length_filterMap_le (l := List.range (Node.exts t).words.length)
          (fun j => (gsub d (xg X (frPos X (listEnd X p) j + 1))).map fun g =>
            g :: treeOut sub gsub h (d + 1) X (frPos X (listEnd X p) j + 2))
        rw [List.length_range] at this; omega
      · intro u hu
        obtain ⟨j, hj, hju⟩ := List.mem_filterMap.mp hu
        rw [List.mem_range] at hj
        obtain ⟨a, ha, haw⟩ := getElem_words hj
        obtain ⟨-, r', hr'⟩ := extFrame h2 hj haw
        simp only [Option.map_eq_some_iff] at hju
        obtain ⟨g, -, rfl⟩ := hju
        have := length_treeOut_le sub gsub h (d + 1) (ℓ + 1) X _ a.2 r' hr'
        have hlw' := length_toWord_words (Node.exts t).words
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) (List.getElem_mem hj))
        rw [← haw, toWord_ext] at this
        simp only [total, List.length_flatten] at hlw'
        simp only [List.length_cons] at this ⊢
        omega
      · intro u hu w hw
        obtain ⟨j, hj, hju⟩ := List.mem_filterMap.mp hu
        rw [List.mem_range] at hj
        obtain ⟨a, ha, haw⟩ := getElem_words hj
        obtain ⟨hga, r', hr'⟩ := extFrame h2 hj haw
        simp only [Option.map_eq_some_iff] at hju
        obtain ⟨g, hg', rfl⟩ := hju
        rcases List.mem_cons.mp hw with rfl | hw
        · refine hg d _ _ le_rfl (by omega) ?_ hg'
          have := le_of_drop_eq hr' (toWord_node_ne_nil a.2)
          exact xg_mem (by omega)
        · exact ih (d + 1) (ℓ + 1) _ a.2 r' hr' (hsub' (d + 1) (by omega) (by omega))
            (fun dd h1 h2 => hsub' dd (by omega) (by omega))
            (fun dd i r h1 h2 => hg dd i r (by omega) (by omega)) w hw

/-! ### The frames of the hooks -/

theorem atList_var {subCmd : Com} (hF : HookFrame subCmd) {y : String} (h1 : y ∉ hookVars)
    (h2 : y ∉ ["e1", "y", "e2", "m", "ap", "lf", "tg", "dr", "kk", "ev"]) :
    y ∉ (atList subCmd).wvars := by
  intro h3
  simp only [atList, atFrame, atEntries, atEntry, Com.wvars, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.nil_append] at h2 h3
  have := hF.1 y
  simp_all

theorem atList_arr {subCmd : Com} (hF : HookFrame subCmd) {b : String} (h1 : b ∉ ["a", "st", "ln"]) :
    b ∉ (atList subCmd).warrs := by
  intro h2
  simp only [atList, atFrame, atEntries, atEntry, Com.warrs, hF.2.1, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.nil_append, List.append_nil] at h1 h2
  simp_all

theorem exList_var {grdCmd : Com} (hF : HookFrame grdCmd) {y : String} (h1 : y ∉ hookVars)
    (h2 : y ∉ ["e1", "y", "e2", "m", "ap", "cc", "gi", "cs", "cl", "ck"]) :
    y ∉ (exList grdCmd).wvars := by
  intro h3
  simp only [exList, exFrame, exCopies, exCopy, Com.wvars, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.nil_append] at h2 h3
  have := hF.1 y
  simp_all

theorem exList_arr {grdCmd : Com} (hF : HookFrame grdCmd) {b : String} (h1 : b ∉ ["a", "st", "ln"]) :
    b ∉ (exList grdCmd).warrs := by
  intro h2
  simp only [exList, exFrame, exCopies, exCopy, Com.warrs, hF.2.1, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.nil_append, List.append_nil] at h1 h2
  simp_all

/-- The candidate lists of a node fit into the room of its word. -/
theorem toWord_atomCands_le {X : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : X.drop p = toWord ws ++ r) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) :
    (toWord (atomCands sub d X p)).length ≤ (toWord ws).length := by
  rw [atomCands, listWords_eq hx, filterMap_eq_range]
  have := total_filterMap_le ws.length ws rfl (fun j => atomMap sub d (ws.getD j [])) (fun j hj u hu => by
    have e : ws.getD j [] = ws[j] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp only [e] at hu
    rw [length_atomMap hu])
  rw [length_toWord_words, length_toWord_words]; omega

end Lax185574Proofs.Words
