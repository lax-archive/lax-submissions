import Lax185574Proofs.Words.Lex
import Lax185574Proofs.Words.TreeCopy
import Lax185574Proofs.TreeAlgo.Basic

/-!
Type-tree words read by position.

A program that works on a type tree keeps the word of its root in an
array and finds the parts of a node by position. A list of words starts
with its length, followed by the frames of the words, every word preceded
by its own length. A node of height `0` is the list of the codes of its
atoms. A node of height `h + 1` is that list followed by the list of the
words of its extensions, where the word of an extension is its guard
followed by the word of the child.

This module gives the positions as functions of the word (`frPos`,
`listEnd`), the words of a list (`listWords`), and the general shape of a
one-pass transformation of a tree (`treeOut`): every atom code is mapped
entry by entry, and may be dropped, every guard is mapped and the
extension may be dropped, and the results are brought into canonical form
at every node.
-/

namespace Lax185574Proofs.Words

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Positions in a word -/

/-- Entry `i` of a word, `0` beyond its end. -/
def xg (x : List ℕ) (i : ℕ) : ℕ := x.getD i 0

/-- The position after `n` frames from position `p` on. -/
def skipFr (x : List ℕ) : ℕ → ℕ → ℕ
  | p, 0 => p
  | p, n + 1 => skipFr x (p + 1 + xg x p) n

/-- The position of frame `j` of the list of words at `p`. -/
def frPos (x : List ℕ) (p j : ℕ) : ℕ := skipFr x (p + 1) j

/-- The position after the list of words at `p`. -/
def listEnd (x : List ℕ) (p : ℕ) : ℕ := skipFr x (p + 1) (xg x p)

/-- The word of the frame at `f`. -/
def frWord (x : List ℕ) (f : ℕ) : List ℕ := ((x.drop (f + 1)).take (xg x f))

/-- The words of the list at `p`. -/
def listWords (x : List ℕ) (p : ℕ) : List (List ℕ) :=
  (List.range (xg x p)).map fun j => frWord x (frPos x p j)

/-- The position after the node of height `h` at `p`. -/
def nodeEnd (x : List ℕ) (p : ℕ) : ℕ → ℕ
  | 0 => listEnd x p
  | _ + 1 => listEnd x (listEnd x p)

theorem skipFr_succ' (x : List ℕ) (p n : ℕ) :
    skipFr x p (n + 1) = skipFr x p n + 1 + xg x (skipFr x p n) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [skipFr, ih, ← skipFr]

theorem xg_of_drop {x : List ℕ} {p a : ℕ} {r : List ℕ} (h : x.drop p = a :: r) : xg x p = a := by
  have h2 := congrArg (fun l => l[0]?) h
  simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h2
  simp [xg, List.getD_eq_getElem?_getD, h2]

theorem drop_add_of_drop {x : List ℕ} {p : ℕ} {u r : List ℕ} (h : x.drop p = u ++ r) :
    x.drop (p + u.length) = r := by
  rw [← List.drop_drop, h]; simp

/-- Reading frames: with the frames of `ws` at `f`, the position after
`j` of them is `f` plus the length of the frames of the first `j`
words, and the frames of the rest follow. -/
theorem skipFr_frames {x : List ℕ} {f : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : x.drop f = frames ws ++ r) {j : ℕ} (hj : j ≤ ws.length) :
    skipFr x f j = f + (frames (ws.take j)).length ∧
      x.drop (skipFr x f j) = frames (ws.drop j) ++ r := by
  induction j with
  | zero => simp [skipFr, hx, frames]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hjl : j < ws.length := by omega
    rw [frames_drop hjl] at h2
    have hxg : xg x (skipFr x f j) = ws[j].length := xg_of_drop (by rw [h2]; rfl)
    refine ⟨by rw [skipFr_succ', hxg, h1, length_frames_take_succ hjl]; omega, ?_⟩
    rw [skipFr_succ', hxg, Nat.add_assoc]
    have := drop_add_of_drop (u := ws[j].length :: ws[j])
      (r := frames (ws.drop (j + 1)) ++ r) (h2.trans (by simp))
    rw [← this]; congr 1; simp; omega


/-! ### A list of words at a position -/

/-- The facts about a list of words found at a position. -/
theorem listAt {x : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : x.drop p = toWord ws ++ r) :
    xg x p = ws.length ∧
    (∀ j ≤ ws.length, frPos x p j = p + 1 + (frames (ws.take j)).length ∧
      x.drop (frPos x p j) = frames (ws.drop j) ++ r) ∧
    (∀ j (hj : j < ws.length), xg x (frPos x p j) = ws[j].length ∧
      frWord x (frPos x p j) = ws[j] ∧ x.drop (frPos x p j + 1) = ws[j] ++ (frames (ws.drop (j + 1)) ++ r)) ∧
    listEnd x p = p + (toWord ws).length ∧ x.drop (listEnd x p) = r := by
  rw [toWord_words] at hx
  have h0 : xg x p = ws.length := xg_of_drop (by rw [hx]; rfl)
  have hf : x.drop (p + 1) = frames ws ++ r := by
    have := drop_add_of_drop (u := [ws.length]) (r := frames ws ++ r) (by rw [hx]; rfl)
    simpa using this
  have hpos : ∀ j ≤ ws.length, frPos x p j = p + 1 + (frames (ws.take j)).length ∧
      x.drop (frPos x p j) = frames (ws.drop j) ++ r := fun j hj => skipFr_frames hf hj
  refine ⟨h0, hpos, fun j hj => ?_, ?_, ?_⟩
  · obtain ⟨-, h2⟩ := hpos j hj.le
    rw [frames_drop hj] at h2
    have hxg : xg x (frPos x p j) = ws[j].length := xg_of_drop (by rw [h2]; rfl)
    have h3 : x.drop (frPos x p j + 1) = ws[j] ++ (frames (ws.drop (j + 1)) ++ r) := by
      have := drop_add_of_drop (u := [ws[j].length]) (r := ws[j] ++ (frames (ws.drop (j + 1)) ++ r))
        (by rw [h2]; simp)
      simpa using this
    refine ⟨hxg, ?_, h3⟩
    rw [frWord, h3, hxg]; simp
  · rw [listEnd, h0]
    obtain ⟨h1, -⟩ := hpos ws.length le_rfl
    rw [frPos] at h1
    rw [h1, List.take_length, toWord_words]; simp; omega
  · rw [listEnd, h0]
    obtain ⟨-, h2⟩ := hpos ws.length le_rfl
    rw [frPos] at h2
    rw [h2]; simp [frames]

theorem listWords_eq {x : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : x.drop p = toWord ws ++ r) : listWords x p = ws := by
  obtain ⟨h0, -, h2, -⟩ := listAt hx
  apply List.ext_getElem
  · simp [listWords, h0]
  · intro j h1 h2'
    simp only [listWords, List.getElem_map, List.getElem_range]
    exact (h2 j h2').2.1

/-! ### Mapping atom codes entry by entry -/

/-- Map the entries of a code, entry `k` with value `v` to
`sub tag k d v`. Nothing if some entry has no image. -/
def atomMapAux (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (tag d : ℕ) : ℕ → List ℕ → Option (List ℕ)
  | _, [] => some []
  | k, v :: w => (sub tag k d v).bind fun a => (atomMapAux sub tag d (k + 1) w).map (a :: ·)

/-- Map an atom code at depth `d`. The tag is the first entry. -/
def atomMap (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (w : List ℕ) : Option (List ℕ) :=
  atomMapAux sub (w.headD 0) d 0 w

theorem length_atomMapAux {sub : ℕ → ℕ → ℕ → ℕ → Option ℕ} {tag d : ℕ} :
    ∀ {k : ℕ} {w u : List ℕ}, atomMapAux sub tag d k w = some u → u.length = w.length
  | _, [], u, h => by simp [atomMapAux] at h; subst h; rfl
  | k, v :: w, u, h => by
    simp only [atomMapAux, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, -, b, hb, rfl⟩ := h
    simp [length_atomMapAux hb]

theorem length_atomMap {sub : ℕ → ℕ → ℕ → ℕ → Option ℕ} {d : ℕ} {w u : List ℕ}
    (h : atomMap sub d w = some u) : u.length = w.length := length_atomMapAux h

/-! ### One-pass transformations of trees -/

/-- The candidates for the atoms of the transformed node at `p`. -/
def atomCands (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (x : List ℕ) (p : ℕ) :
    List (List ℕ) :=
  (listWords x p).filterMap (atomMap sub d)

/-- The transformation of the node of height `h` at depth `d` at
position `p` of `x`: the atom codes are mapped by `sub`, the guards by
`gsub`, the children transformed, and every set is put into canonical
form. -/
def treeOut (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) :
    ℕ → ℕ → List ℕ → ℕ → List ℕ
  | 0, d, x, p => toWord (sortedDistinct (atomCands sub d x p))
  | h + 1, d, x, p => toWord (sortedDistinct (atomCands sub d x p)) ++
      toWord (sortedDistinct ((List.range (xg x (listEnd x p))).filterMap fun j =>
        (gsub d (xg x (frPos x (listEnd x p) j + 1))).map fun g =>
          g :: treeOut sub gsub h (d + 1) x (frPos x (listEnd x p) j + 2)))

/-- The candidates for the extensions of the transformed node. -/
def extCands (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (h d : ℕ)
    (x : List ℕ) (p : ℕ) : List (List ℕ) :=
  (List.range (xg x (listEnd x p))).filterMap fun j =>
    (gsub d (xg x (frPos x (listEnd x p) j + 1))).map fun g =>
      g :: treeOut sub gsub h (d + 1) x (frPos x (listEnd x p) j + 2)

theorem treeOut_zero (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (d : ℕ)
    (x : List ℕ) (p : ℕ) :
    treeOut sub gsub 0 d x p = toWord (sortedDistinct (atomCands sub d x p)) := rfl

theorem treeOut_succ (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (h d : ℕ)
    (x : List ℕ) (p : ℕ) :
    treeOut sub gsub (h + 1) d x p = toWord (sortedDistinct (atomCands sub d x p)) ++
      toWord (sortedDistinct (extCands sub gsub h d x p)) := rfl

/-! ### Canonical form of the image of a finite set -/

theorem sort_eq_of_toFinset {s t : Finset (List ℕ)} (h : s = t) :
    s.sort (· ≤ ·) = t.sort (· ≤ ·) := by rw [h]

/-- The canonical form of the candidates computed from the words of a
finite set is the word list of the image set. The candidate of entry
`j` is computed from any element whose word is entry `j`. -/
theorem sortedDistinct_cands {α β : Type*} [WordEncoding α] [WordEncoding β] [DecidableEq β]
    (S : Finset α) (F : α → Option β) (c : ℕ → Option (List ℕ))
    (hc : ∀ j (hj : j < S.words.length), ∀ a ∈ S, toWord a = S.words[j] →
      c j = (F a).map toWord) :
    sortedDistinct ((List.range S.words.length).filterMap c) =
      Finset.words (S.biUnion fun a => (F a).toFinset) := by
  unfold sortedDistinct Finset.words
  congr 1
  ext u
  simp only [List.mem_toFinset, List.mem_filterMap, List.mem_range, Finset.mem_image,
    Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨j, hj, hcj⟩
    have hmem : S.words[j] ∈ S.words := List.getElem_mem hj
    simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hmem
    obtain ⟨a, ha, haw⟩ := hmem
    rw [hc j hj a ha haw, Option.map_eq_some_iff] at hcj
    obtain ⟨b, hb, rfl⟩ := hcj
    exact ⟨b, ⟨a, ha, hb⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, hb⟩, rfl⟩
    have hmem : toWord a ∈ S.words := by
      simp only [Finset.words, Finset.mem_sort, Finset.mem_image]; exact ⟨a, ha, rfl⟩
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hmem
    exact ⟨j, hj, by rw [hc j hj a ha hjw.symm, hb]; rfl⟩

/-! ### Sizes -/

theorem sortedDistinct_perm (ws : List (List ℕ)) : (sortedDistinct ws).Perm ws.dedup := by
  rw [← Multiset.coe_eq_coe, sortedDistinct, Finset.sort_eq, List.toFinset_val]

theorem total_sortedDistinct_le (ws : List (List ℕ)) : total (sortedDistinct ws) ≤ total ws := by
  have h1 : total (sortedDistinct ws) = total ws.dedup := by
    simp only [total, List.length_flatten]
    exact ((sortedDistinct_perm ws).map List.length).sum_eq
  rw [h1]
  simp only [total, List.length_flatten]
  exact ((List.dedup_sublist ws).map List.length).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem length_toWord_sortedDistinct_le (ws : List (List ℕ)) :
    (toWord (sortedDistinct ws)).length ≤ (toWord ws).length := by
  rw [length_toWord_words, length_toWord_words]
  have := total_sortedDistinct_le ws
  have := length_sortedDistinct_le ws
  omega

/-! ### Node words -/

theorem toWord_node_zero {ℓ : ℕ} (t : Node 0 ℓ) :
    toWord t = toWord (Node.atoms t).words := rfl

theorem toWord_node_succ {h ℓ : ℕ} (t : Node (h + 1) ℓ) :
    toWord t = toWord (Node.atoms t).words ++ toWord (Node.exts t).words := rfl

theorem toWord_ext {h ℓ : ℕ} (e : Fin ℓ × Node h (ℓ + 1)) :
    toWord e = e.1.val :: toWord e.2 := rfl

theorem toWord_atom {ℓ : ℕ} (φ : Lax185574.DistanceLogic.DistFO ℓ) :
    toWord φ = Lax185574.DistanceLogic.DistFO.code φ := Lax185574Proofs.Legacy.encode_eq_code φ

theorem mem_words {α : Type*} [WordEncoding α] {S : Finset α} {u : List ℕ} :
    u ∈ S.words ↔ ∃ a ∈ S, toWord a = u := by
  simp [Finset.words]

theorem getElem_words {α : Type*} [WordEncoding α] {S : Finset α} {j : ℕ}
    (hj : j < S.words.length) : ∃ a ∈ S, toWord a = S.words[j] :=
  mem_words.mp (List.getElem_mem hj)

theorem filterMap_eq_range {β : Type*} (l : List (List ℕ)) (f : List ℕ → Option β) :
    l.filterMap f = (List.range l.length).filterMap fun j => f (l.getD j []) := by
  have : l = (List.range l.length).map fun j => l.getD j [] := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [List.getElem?_eq_getElem h1]
  conv_lhs => rw [this]
  rw [List.filterMap_map]; rfl

/-- The atom candidates of a node whose atoms are `A`, when `sub` maps
the code of every atom as `F` does. -/
theorem sortedDistinct_atomCands {m m' : ℕ} {x : List ℕ} {p : ℕ}
    {A : Finset (Lax185574.DistanceLogic.DistFO m)} {r : List ℕ}
    (hx : x.drop p = toWord A.words ++ r) {sub : ℕ → ℕ → ℕ → ℕ → Option ℕ} {d : ℕ}
    (F : Lax185574.DistanceLogic.DistFO m → Option (Lax185574.DistanceLogic.DistFO m'))
    (hF : ∀ φ ∈ A, atomMap sub d (toWord φ) = (F φ).map toWord) :
    sortedDistinct (atomCands sub d x p) = Finset.words (A.biUnion fun φ => (F φ).toFinset) := by
  rw [← sortedDistinct_cands A F (fun j => atomMap sub d (A.words.getD j []))]
  · rw [atomCands, listWords_eq hx, filterMap_eq_range]
  · intro j hj a ha haw
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [← haw, hF a ha]

/-- The two lists of a node of positive height. -/
theorem nodeSplit {h ℓ : ℕ} {x : List ℕ} {p : ℕ} {t : Node (h + 1) ℓ} {r : List ℕ}
    (hx : x.drop p = toWord t ++ r) :
    x.drop p = toWord (Node.atoms t).words ++ (toWord (Node.exts t).words ++ r) ∧
      x.drop (listEnd x p) = toWord (Node.exts t).words ++ r := by
  rw [toWord_node_succ, List.append_assoc] at hx
  exact ⟨hx, (listAt hx).2.2.2.2⟩

/-- The frame of an extension: its guard, then the word of the child. -/
theorem extFrame {h m : ℕ} {x : List ℕ} {e : ℕ} {E : Finset (Fin m × Node h (m + 1))}
    {r : List ℕ} (he : x.drop e = toWord E.words ++ r) {j : ℕ} (hj : j < E.words.length)
    {a : Fin m × Node h (m + 1)} (ha : toWord a = E.words[j]) :
    xg x (frPos x e j + 1) = a.1.val ∧
      ∃ r', x.drop (frPos x e j + 2) = toWord a.2 ++ r' := by
  obtain ⟨-, -, h2, -⟩ := listAt he
  have h3 := (h2 j hj).2.2
  rw [← ha, toWord_ext] at h3
  refine ⟨xg_of_drop (by rw [h3]; rfl), frames (List.drop (j + 1) E.words) ++ r, ?_⟩
  have := drop_add_of_drop (u := [a.1.val])
    (r := toWord a.2 ++ (frames (List.drop (j + 1) E.words) ++ r)) (by rw [h3]; simp)
  simpa [Nat.add_assoc] using this

/-- The extension candidates of a node whose extensions are `E`, when
`gsub` maps guards as `Gf` does and the children are transformed as `R`
does. -/
theorem sortedDistinct_extCands {h m m' : ℕ} {x : List ℕ} {p : ℕ}
    {E : Finset (Fin m × Node h (m + 1))} {r : List ℕ}
    (he : x.drop (listEnd x p) = toWord E.words ++ r)
    {sub : ℕ → ℕ → ℕ → ℕ → Option ℕ} {gsub : ℕ → ℕ → Option ℕ} {d : ℕ}
    (Gf : Fin m → Option (Fin m')) (R : Node h (m + 1) → Node h (m' + 1))
    (hG : ∀ i : Fin m, gsub d i.val = (Gf i).map Fin.val)
    (hR : ∀ ε ∈ E, ∀ P r', x.drop P = toWord ε.2 ++ r' →
      treeOut sub gsub h (d + 1) x P = toWord (R ε.2)) :
    sortedDistinct (extCands sub gsub h d x p) =
      Finset.words (E.biUnion fun ε => ((Gf ε.1).map fun j => (j, R ε.2)).toFinset) := by
  have h0 := (listAt he).1
  unfold extCands
  rw [h0]
  refine sortedDistinct_cands E _ _ fun j hj a ha haw => ?_
  obtain ⟨hg, r', hr'⟩ := extFrame he hj haw
  rw [hg, hG, hR a ha _ r' hr', Option.map_map, Option.map_map]
  rfl

/-! ### The size of the output -/

theorem total_append (a b : List (List ℕ)) : total (a ++ b) = total a + total b := by
  simp [total]

theorem total_singleton (u : List ℕ) : total [u] = u.length := by
  simp [total]

theorem total_filterMap_le (n : ℕ) (ws : List (List ℕ)) (hn : n = ws.length)
    (c : ℕ → Option (List ℕ))
    (hc : ∀ j (hj : j < ws.length), ∀ u, c j = some u → u.length ≤ ws[j].length) :
    ((List.range n).filterMap c).length ≤ ws.length ∧
      total ((List.range n).filterMap c) ≤ total ws := by
  subst hn
  induction ws using List.reverseRecOn with
  | nil => simp [total]
  | append_singleton ws w ih =>
    have ih' := ih fun j hj u hu => by
      have := hc j (by simp; omega) u hu
      rwa [List.getElem_append_left hj] at this
    simp only [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil, total_append, total_singleton] at ih' ⊢
    cases hcw : c ws.length with
    | none => simp only [List.length_nil, total, List.flatten_nil] at ih' ⊢; omega
    | some u =>
      have := hc ws.length (by simp) u hcw
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton] at this
      simp only [List.length_singleton, total_singleton] at ih' ⊢; omega

theorem length_toWord_filterMap_le (ws : List (List ℕ)) (c : ℕ → Option (List ℕ))
    (hc : ∀ j (hj : j < ws.length), ∀ u, c j = some u → u.length ≤ ws[j].length) :
    (toWord (sortedDistinct ((List.range ws.length).filterMap c))).length ≤ (toWord ws).length := by
  refine (length_toWord_sortedDistinct_le _).trans ?_
  obtain ⟨h1, h2⟩ := total_filterMap_le ws.length ws rfl c hc
  rw [length_toWord_words, length_toWord_words]; omega

/-- The transformation does not make a node longer. -/
theorem length_treeOut_le (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) :
    ∀ (h d ℓ : ℕ) (x : List ℕ) (p : ℕ) (t : Node h ℓ) (r : List ℕ),
      x.drop p = toWord t ++ r → (treeOut sub gsub h d x p).length ≤ (toWord t).length := by
  have hatoms : ∀ (d ℓ : ℕ) (x : List ℕ) (p : ℕ) (A : Finset (Lax185574.DistanceLogic.DistFO ℓ))
      (r : List ℕ), x.drop p = toWord A.words ++ r →
      (toWord (sortedDistinct (atomCands sub d x p))).length ≤ (toWord A.words).length := by
    intro d ℓ x p A r hx
    rw [atomCands, listWords_eq hx, filterMap_eq_range]
    refine length_toWord_filterMap_le _ _ fun j hj u hu => ?_
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hu
    rw [length_atomMap hu]
  intro h
  induction h with
  | zero =>
    intro d ℓ x p t r hx
    rw [treeOut_zero, toWord_node_zero]
    rw [toWord_node_zero] at hx
    exact hatoms d ℓ x p _ r hx
  | succ h ih =>
    intro d ℓ x p t r hx
    obtain ⟨h1, h2⟩ := nodeSplit hx
    rw [treeOut_succ, toWord_node_succ, List.length_append, List.length_append]
    refine Nat.add_le_add (hatoms d ℓ x p _ _ h1) ?_
    have h0 := (listAt h2).1
    unfold extCands
    rw [h0]
    refine length_toWord_filterMap_le _ _ fun j hj u hu => ?_
    obtain ⟨a, ha, haw⟩ := getElem_words hj
    obtain ⟨-, r', hr'⟩ := extFrame h2 hj haw
    simp only [Option.map_eq_some_iff] at hu
    obtain ⟨g, -, rfl⟩ := hu
    rw [← haw, toWord_ext]
    simpa using ih (d + 1) (ℓ + 1) x _ a.2 r' hr'

/-! ### Well-formed nodes at a position -/

/-- The word of a node of height `h`, of some arity, starts at `p`. -/
def NodeAt (x : List ℕ) (p h : ℕ) : Prop :=
  ∃ (ℓ : ℕ) (t : Node h ℓ) (r : List ℕ), x.drop p = toWord t ++ r

theorem nodeEnd_eq {h ℓ : ℕ} {x : List ℕ} {p : ℕ} {t : Node h ℓ} {r : List ℕ}
    (hx : x.drop p = toWord t ++ r) : nodeEnd x p h = p + (toWord t).length := by
  cases h with
  | zero =>
    rw [toWord_node_zero] at hx ⊢
    exact (listAt hx).2.2.2.1
  | succ h =>
    obtain ⟨h1, h2⟩ := nodeSplit hx
    rw [nodeEnd, (listAt h2).2.2.2.1, (listAt h1).2.2.2.1, toWord_node_succ]
    simp; omega

theorem toWord_node_ne_nil {h ℓ : ℕ} (t : Node h ℓ) : toWord t ≠ [] := by
  cases h with
  | zero => rw [toWord_node_zero, toWord_words]; simp
  | succ h => rw [toWord_node_succ, toWord_words]; simp

theorem le_of_drop_eq {x : List ℕ} {p : ℕ} {u r : List ℕ} (hx : x.drop p = u ++ r)
    (hu : u ≠ []) : p + u.length ≤ x.length := by
  have := congrArg List.length hx
  rw [List.length_drop, List.length_append] at this
  have : 0 < u.length := List.length_pos_iff.mpr hu
  omega

theorem frames_append (a b : List (List ℕ)) : frames (a ++ b) = frames a ++ frames b := by
  simp [frames]

theorem length_frames_take_le (ws : List (List ℕ)) (j : ℕ) :
    (frames (ws.take j)).length ≤ (frames ws).length := by
  conv_rhs => rw [← List.take_append_drop j ws, frames_append, List.length_append]
  omega

/-- The frames of a list lie between its start and its end. -/
theorem frPos_le_listEnd {x : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : x.drop p = toWord ws ++ r) {j : ℕ} (hj : j ≤ xg x p) :
    p + 1 + j ≤ frPos x p j ∧ frPos x p j ≤ listEnd x p ∧ p + 1 + xg x p ≤ listEnd x p := by
  obtain ⟨h0, hpos, -, hle, -⟩ := listAt hx
  rw [h0] at hj ⊢
  obtain ⟨h3, -⟩ := hpos j hj
  have h5 := length_frames_take_le ws j
  have h6 : j ≤ (frames (ws.take j)).length := by
    rw [length_frames]; simp; omega
  have h7 := length_toWord_words ws
  have h8 := length_frames ws
  rw [h3, hle]
  refine ⟨by omega, by omega, by omega⟩

/-- The list of atom codes of a node, and its position. -/
theorem NodeAt.atomList {x : List ℕ} {p h : ℕ} (hn : NodeAt x p h) :
    ∃ (ws : List (List ℕ)) (r : List ℕ), x.drop p = toWord ws ++ r := by
  obtain ⟨ℓ, t, r, hx⟩ := hn
  cases h with
  | zero => exact ⟨_, r, hx⟩
  | succ h => exact ⟨_, _, (nodeSplit hx).1⟩

theorem NodeAt.listEnd_le {x : List ℕ} {p h : ℕ} (hn : NodeAt x p h) :
    listEnd x p ≤ nodeEnd x p h ∧ nodeEnd x p h ≤ x.length := by
  obtain ⟨ℓ, t, r, hx⟩ := hn
  refine ⟨?_, by rw [nodeEnd_eq hx]; exact le_of_drop_eq hx (toWord_node_ne_nil t)⟩
  cases h with
  | zero => exact le_rfl
  | succ h =>
    obtain ⟨-, h2⟩ := nodeSplit hx
    have := (frPos_le_listEnd h2 (j := 0) (Nat.zero_le _)).2.2
    rw [nodeEnd]; omega

/-- The atom codes of a node: the frames lie before the end of the
list, which lies before the end of the node. -/
theorem NodeAt.atoms {x : List ℕ} {p h : ℕ} (hn : NodeAt x p h) :
    (∀ j ≤ xg x p, p + 1 + j ≤ frPos x p j ∧ frPos x p j ≤ listEnd x p) ∧
      p + 1 + xg x p ≤ listEnd x p ∧ listEnd x p ≤ nodeEnd x p h ∧ nodeEnd x p h ≤ x.length := by
  obtain ⟨ws, r, hx⟩ := hn.atomList
  exact ⟨fun j hj => ⟨(frPos_le_listEnd hx hj).1, (frPos_le_listEnd hx hj).2.1⟩,
    (frPos_le_listEnd hx (Nat.zero_le _)).2.2, hn.listEnd_le⟩

/-- The extensions of a node of positive height: every frame holds a
guard and the word of a child of height one less, which fills the rest
of the frame. -/
theorem NodeAt.exts {x : List ℕ} {p h : ℕ} (hn : NodeAt x p (h + 1)) :
    (∀ j < xg x (listEnd x p), NodeAt x (frPos x (listEnd x p) j + 2) h ∧
      nodeEnd x (frPos x (listEnd x p) j + 2) h = frPos x (listEnd x p) (j + 1) ∧
      1 ≤ xg x (frPos x (listEnd x p) j)) ∧
    (∀ j ≤ xg x (listEnd x p), frPos x (listEnd x p) j ≤ nodeEnd x p (h + 1)) ∧
    nodeEnd x p (h + 1) = listEnd x (listEnd x p) := by
  obtain ⟨ℓ, t, r, hx⟩ := hn
  obtain ⟨-, h2⟩ := nodeSplit hx
  obtain ⟨h0, hpos, hfr, hle, -⟩ := listAt h2
  refine ⟨fun j hj => ?_, fun j hj => ?_, rfl⟩
  · rw [h0] at hj
    obtain ⟨a, -, haw⟩ := getElem_words hj
    obtain ⟨-, r', hr'⟩ := extFrame h2 hj haw
    obtain ⟨hl, -, -⟩ := hfr j hj
    refine ⟨⟨ℓ + 1, a.2, r', hr'⟩, ?_, ?_⟩
    · have hl' : xg x (skipFr x (listEnd x p + 1) j) = _ := hl
      rw [nodeEnd_eq hr']
      show _ = skipFr x (listEnd x p + 1) (j + 1)
      rw [skipFr_succ', hl', ← haw, toWord_ext]
      simp [frPos]; omega
    · rw [hl, ← haw, toWord_ext]; simp
  · rw [nodeEnd]
    exact (frPos_le_listEnd h2 hj).2.1

end Lax185574Proofs.Words
