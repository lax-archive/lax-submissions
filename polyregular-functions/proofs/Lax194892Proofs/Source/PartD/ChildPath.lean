/-
**The string representation of a child configuration graph, built from the list of its vertices.**

`RequestProject/PartD/ChildGraph.lean` defines the alphabet `Transducers.CG.CGLetter` of the string
representation of a child configuration graph and the predicate `Transducers.CG.CGPath`, which says
that a string over that alphabet represents a given list of children.  This file goes the other
way: given the list of children -- a finite sequence `ch 0, …, ch m` of vertices whose columns lie
in the input and change by at most one at a time, and which are pairwise distinct -- it builds the
string `Transducers.CG.cgOfPath` that represents it, and proves `Transducers.CG.CGPath` for it.

The file is about the alphabet only; no pebble transducer appears in it.  The three hypotheses are
exactly what a *run* of a pebble transducer provides:

* the columns of the children lie in the input string;
* consecutive children sit in the same column or in adjacent ones, because between two consecutive
  children the machine either moves the top pebble one step, or pushes a pebble and pops it again;
* the children are pairwise distinct, because a repetition would make the run periodic and the last
  child would then have a successor.
-/
import Lax194892Proofs.Source.PartD.ChildGraph
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

open scoped Classical

variable {A Q : Type} {k : ℕ}

/-! ## The direction of an edge between two columns -/

/-- The direction that leads from the column `a` to the column `b`, for adjacent columns. -/
def dirOf (a b : ℕ) : Dir := if b = a then none else if a < b then some true else some false

lemma dest_dirOf {a b : ℕ} (h₁ : b ≤ a + 1) (h₂ : a ≤ b + 1) : dest a (dirOf a b) = some b := by
  rcases lt_trichotomy b a with h | h | h
  · have hb : b = a - 1 := by omega
    have ha : a ≠ 0 := by omega
    rw [dirOf, if_neg (show ¬ b = a by omega), if_neg (show ¬ a < b by omega)]
    simp only [dest, if_neg ha, hb]
  · subst h
    rw [dirOf, if_pos rfl]
    simp [dest]
  · have hb : b = a + 1 := by omega
    rw [dirOf, if_neg (show ¬ b = a by omega), if_pos h]
    simp [dest, hb]

@[simp] lemma dirOf_self (a : ℕ) : dirOf a a = none := by simp [dirOf]

lemma dirOf_succ (a : ℕ) : dirOf a (a + 1) = some true := by simp [dirOf]

lemma dirOf_pred {a b : ℕ} (h : b < a) : dirOf a b = some false := by
  unfold dirOf
  rw [if_neg (by omega), if_neg (by omega)]

lemma dirOf_eq_some_true {a b : ℕ} (h : dirOf a b = some true) : a < b := by
  unfold dirOf at h
  split at h
  · simp at h
  · split at h
    · assumption
    · simp at h

lemma dirOf_eq_some_false {a b : ℕ} (h : dirOf a b = some false) : b < a := by
  unfold dirOf at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · omega

lemma dirOf_eq_none {a b : ℕ} (h : dirOf a b = none) : b = a := by
  unfold dirOf at h
  split at h
  · assumption
  · split at h <;> simp at h

/-! ## The index of a vertex in the list of children -/

/-- The index `t < m` at which the vertex `v` occurs in the list of children, if there is one. -/
noncomputable def idxAt (ch : ℕ → Vtx Q) (m : ℕ) (v : Vtx Q) : Option ℕ :=
  if h : ∃ t, t < m ∧ ch t = v then some (Nat.find h) else none

/-- The index `t < m` such that the vertex `v` is the child following `ch t`, if there is one. -/
noncomputable def idxSuccAt (ch : ℕ → Vtx Q) (m : ℕ) (v : Vtx Q) : Option ℕ :=
  if h : ∃ t, t < m ∧ ch (t + 1) = v then some (Nat.find h) else none

variable {ch : ℕ → Vtx Q} {m : ℕ}

/-- The distinctness hypothesis on the list of children. -/
def Distinct (ch : ℕ → Vtx Q) (m : ℕ) : Prop := ∀ s t, s ≤ m → t ≤ m → ch s = ch t → s = t

lemma idxAt_eq_some (hd : Distinct ch m) {t : ℕ} (ht : t < m) : idxAt ch m (ch t) = some t := by
  classical
  have hex : ∃ s, s < m ∧ ch s = ch t := ⟨t, ht, rfl⟩
  rw [idxAt, dif_pos hex]
  congr 1
  obtain ⟨hlt, heq⟩ := Nat.find_spec hex
  exact hd _ _ (by omega) (by omega) heq

lemma idxAt_eq_none {v : Vtx Q} (h : ∀ t, t < m → ch t ≠ v) : idxAt ch m v = none := by
  classical
  rw [idxAt, dif_neg]
  rintro ⟨t, ht, hct⟩
  exact h t ht hct

lemma idxAt_spec {v : Vtx Q} {t : ℕ} (h : idxAt ch m v = some t) : t < m ∧ ch t = v := by
  classical
  rw [idxAt] at h
  split at h
  · rename_i hex
    obtain rfl : t = Nat.find hex := by simpa using h.symm
    exact Nat.find_spec hex
  · simp at h

lemma idxSuccAt_eq_some (hd : Distinct ch m) {t : ℕ} (ht : t < m) :
    idxSuccAt ch m (ch (t + 1)) = some t := by
  classical
  have hex : ∃ s, s < m ∧ ch (s + 1) = ch (t + 1) := ⟨t, ht, rfl⟩
  rw [idxSuccAt, dif_pos hex]
  congr 1
  obtain ⟨hlt, heq⟩ := Nat.find_spec hex
  have := hd _ _ (by omega) (by omega) heq
  omega

lemma idxSuccAt_eq_none {v : Vtx Q} (h : ∀ t, t < m → ch (t + 1) ≠ v) :
    idxSuccAt ch m v = none := by
  classical
  rw [idxSuccAt, dif_neg]
  rintro ⟨t, ht, hct⟩
  exact h t ht hct

lemma idxSuccAt_spec {v : Vtx Q} {t : ℕ} (h : idxSuccAt ch m v = some t) :
    t < m ∧ ch (t + 1) = v := by
  classical
  rw [idxSuccAt] at h
  split at h
  · rename_i hex
    obtain rfl : t = Nat.find hex := by simpa using h.symm
    exact Nat.find_spec hex
  · simp at h

/-! ## The string representation -/

/-- **The string representation of the child configuration graph** whose children are
`ch 0, …, ch m`, over an input with `n + 1` gaps whose gap `j` carries the input letter `lett j` and
the fixed pebbles `peb j`, the moving pebble having the index `nid`. -/
noncomputable def cgOfPath (lett : ℕ → Option A) (peb : ℕ → Fin k → Bool) (nid : Fin k)
    (n : ℕ) (ch : ℕ → Vtx Q) (m : ℕ) : List (CGLetter A Q k) :=
  (List.range (n + 1)).map fun j =>
    { lett := lett j
      peb := peb j
      nid := nid
      src := fun q' => decide ((q', j) = ch 0)
      nxt := fun q' => (idxAt ch m (q', j)).map fun t => ((ch (t + 1)).1, dirOf j (ch (t + 1)).2)
      prv := fun q' => (idxSuccAt ch m (q', j)).map fun t => ((ch t).1, dirOf (ch t).2 j) }

variable {lett : ℕ → Option A} {peb : ℕ → Fin k → Bool} {nid : Fin k} {n : ℕ}

@[simp] lemma cgOfPath_length : (cgOfPath lett peb nid n ch m).length = n + 1 := by
  simp [cgOfPath]

lemma cgOfPath_getElem? {j : ℕ} (hj : j ≤ n) :
    (cgOfPath lett peb nid n ch m)[j]? = some
      { lett := lett j
        peb := peb j
        nid := nid
        src := fun q' => decide ((q', j) = ch 0)
        nxt := fun q' => (idxAt ch m (q', j)).map fun t => ((ch (t + 1)).1, dirOf j (ch (t + 1)).2)
        prv := fun q' => (idxSuccAt ch m (q', j)).map fun t => ((ch t).1, dirOf (ch t).2 j) } := by
  classical
  have hlt : j < (List.range (n + 1)).length := by simp; omega
  rw [cgOfPath, List.getElem?_map, List.getElem?_eq_getElem hlt]
  simp

lemma cgOfPath_getElem?_of_gt {j : ℕ} (hj : n < j) :
    (cgOfPath lett peb nid n ch m)[j]? = none := by
  refine List.getElem?_eq_none ?_
  simp
  omega

/-! ## The string represents the list of children -/

lemma isSrc_cgOfPath_iff {v : Vtx Q} (h0 : (ch 0).2 ≤ n) :
    IsSrc (cgOfPath lett peb nid n ch m) v ↔ v = ch 0 := by
  classical
  constructor
  · rintro ⟨c, hc, hsrc⟩
    by_cases hv : v.2 ≤ n
    · rw [cgOfPath_getElem? hv] at hc
      obtain rfl := (Option.some.injEq _ _ ▸ hc : _ = c).symm
      simp only [decide_eq_true_eq] at hsrc
      rw [← hsrc]
    · rw [cgOfPath_getElem?_of_gt (by omega)] at hc
      simp at hc
  · rintro rfl
    refine ⟨_, cgOfPath_getElem? h0, ?_⟩
    simp

lemma succOf_cgOfPath (hd : Distinct ch m) (hcol : ∀ t ≤ m, (ch t).2 ≤ n)
    (hadj : ∀ t < m, (ch (t + 1)).2 ≤ (ch t).2 + 1 ∧ (ch t).2 ≤ (ch (t + 1)).2 + 1)
    {t : ℕ} (ht : t < m) :
    succOf (cgOfPath lett peb nid n ch m) (ch t) = some (ch (t + 1)) := by
  classical
  have hc := cgOfPath_getElem? (lett := lett) (peb := peb) (nid := nid) (ch := ch) (m := m)
    (hcol t (by omega))
  rw [succOf, hc]
  simp only [Option.bind_some]
  have hidx : idxAt ch m ((ch t).1, (ch t).2) = some t := by
    have : ((ch t).1, (ch t).2) = ch t := rfl
    rw [this]
    exact idxAt_eq_some hd ht
  rw [hidx]
  simp only [Option.map_some, Option.bind_some]
  obtain ⟨h1, h2⟩ := hadj t ht
  rw [dest_dirOf h1 h2]
  simp

lemma succOf_cgOfPath_last (hd : Distinct ch m) (hcol : ∀ t ≤ m, (ch t).2 ≤ n) :
    succOf (cgOfPath lett peb nid n ch m) (ch m) = none := by
  classical
  have hc := cgOfPath_getElem? (lett := lett) (peb := peb) (nid := nid) (ch := ch) (m := m)
    (hcol m le_rfl)
  rw [succOf, hc]
  simp only [Option.bind_some]
  have hidx : idxAt ch m ((ch m).1, (ch m).2) = none := by
    have he : ((ch m).1, (ch m).2) = ch m := rfl
    rw [he]
    refine idxAt_eq_none ?_
    intro t ht hct
    have := hd t m (by omega) le_rfl hct
    omega
  rw [hidx]
  simp

lemma chk_cgOfPath (hd : Distinct ch m)
    (hadj : ∀ t < m, (ch (t + 1)).2 ≤ (ch t).2 + 1 ∧ (ch t).2 ≤ (ch (t + 1)).2 + 1) :
    Chk (cgOfPath lett peb nid n ch m) := by
  classical
  intro i hi
  simp only [pairOK, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- an edge to the right is recorded at its target
    intro q q' ca cb hca hcb hnxt
    -- `ca` is the letter of the column `i - 1`, `cb` that of the column `i`
    have hi0 : i ≠ 0 := by
      intro h
      rw [leftLet, if_pos h] at hca
      simp at hca
    rw [leftLet, if_neg hi0] at hca
    have hib : i ≤ n := by
      by_contra hcon
      rw [cgOfPath_getElem?_of_gt (by omega)] at hcb
      simp at hcb
    rw [cgOfPath_getElem? (by omega)] at hca
    rw [cgOfPath_getElem? hib] at hcb
    obtain rfl := (Option.some.injEq _ _ ▸ hca : _ = ca).symm
    obtain rfl := (Option.some.injEq _ _ ▸ hcb : _ = cb).symm
    simp only [Option.map_eq_some_iff] at hnxt
    obtain ⟨t, hidx, heq⟩ := hnxt
    obtain ⟨htm, hct⟩ := idxAt_spec hidx
    have h1 : (ch (t + 1)).1 = q' := congrArg Prod.fst heq
    have h2 : dirOf (i - 1) (ch (t + 1)).2 = some true := congrArg Prod.snd heq
    have h3 : (ch (t + 1)).2 = i := by
      have := dirOf_eq_some_true h2
      obtain ⟨ha, hb⟩ := hadj t htm
      have : (ch t).2 = i - 1 := congrArg Prod.snd hct
      omega
    have hsucc : ch (t + 1) = (q', i) := by
      refine Prod.ext ?_ ?_ <;> simpa using ‹_›
    simp only []
    rw [show ((q', i) : Vtx Q) = ch (t + 1) from hsucc.symm, idxSuccAt_eq_some hd htm]
    simp only [Option.map_some]
    have hct2 : (ch t).2 = i - 1 := congrArg Prod.snd hct
    have hct1 : (ch t).1 = q := congrArg Prod.fst hct
    rw [hct1, hct2]
    have : dirOf (i - 1) i = some true := by
      have : i = (i - 1) + 1 := by omega
      rw [this]
      simpa using dirOf_succ (i - 1)
    rw [this]
  · -- an edge to the left is recorded at its target
    intro q q' ca cb hca hcb hnxt
    have hi0 : i ≠ 0 := by
      intro h
      rw [leftLet, if_pos h] at hca
      simp at hca
    rw [leftLet, if_neg hi0] at hca
    have hib : i ≤ n := by
      by_contra hcon
      rw [cgOfPath_getElem?_of_gt (by omega)] at hcb
      simp at hcb
    rw [cgOfPath_getElem? (by omega)] at hca
    rw [cgOfPath_getElem? hib] at hcb
    obtain rfl := (Option.some.injEq _ _ ▸ hca : _ = ca).symm
    obtain rfl := (Option.some.injEq _ _ ▸ hcb : _ = cb).symm
    simp only [Option.map_eq_some_iff] at hnxt
    obtain ⟨t, hidx, heq⟩ := hnxt
    obtain ⟨htm, hct⟩ := idxAt_spec hidx
    have h1 : (ch (t + 1)).1 = q' := congrArg Prod.fst heq
    have h2 : dirOf i (ch (t + 1)).2 = some false := congrArg Prod.snd heq
    have hct2 : (ch t).2 = i := congrArg Prod.snd hct
    have hct1 : (ch t).1 = q := congrArg Prod.fst hct
    have h3 : (ch (t + 1)).2 = i - 1 := by
      have := dirOf_eq_some_false h2
      obtain ⟨ha, hb⟩ := hadj t htm
      omega
    have hsucc : ch (t + 1) = (q', i - 1) := by
      refine Prod.ext ?_ ?_ <;> simpa using ‹_›
    simp only []
    rw [show ((q', i - 1) : Vtx Q) = ch (t + 1) from hsucc.symm, idxSuccAt_eq_some hd htm]
    simp only [Option.map_some]
    rw [hct1, hct2]
    have : dirOf i (i - 1) = some false := dirOf_pred (by omega)
    rw [this]
  · -- an edge inside a column is recorded at its target
    intro q q' cb hcb hnxt
    have hib : i ≤ n := by
      by_contra hcon
      rw [cgOfPath_getElem?_of_gt (by omega)] at hcb
      simp at hcb
    rw [cgOfPath_getElem? hib] at hcb
    obtain rfl := (Option.some.injEq _ _ ▸ hcb : _ = cb).symm
    simp only [Option.map_eq_some_iff] at hnxt
    obtain ⟨t, hidx, heq⟩ := hnxt
    obtain ⟨htm, hct⟩ := idxAt_spec hidx
    have h1 : (ch (t + 1)).1 = q' := congrArg Prod.fst heq
    have h2 : dirOf i (ch (t + 1)).2 = none := congrArg Prod.snd heq
    have h3 : (ch (t + 1)).2 = i := dirOf_eq_none h2
    have hct2 : (ch t).2 = i := congrArg Prod.snd hct
    have hct1 : (ch t).1 = q := congrArg Prod.fst hct
    have hsucc : ch (t + 1) = (q', i) := by
      refine Prod.ext ?_ ?_ <;> simpa using ‹_›
    simp only []
    rw [show ((q', i) : Vtx Q) = ch (t + 1) from hsucc.symm, idxSuccAt_eq_some hd htm]
    simp only [Option.map_some]
    rw [hct1, hct2]
    simp
  · -- the first child has no incoming edge
    intro q cb hcb hsrc
    have hib : i ≤ n := by
      by_contra hcon
      rw [cgOfPath_getElem?_of_gt (by omega)] at hcb
      simp at hcb
    rw [cgOfPath_getElem? hib] at hcb
    obtain rfl := (Option.some.injEq _ _ ▸ hcb : _ = cb).symm
    simp only [decide_eq_true_eq] at hsrc
    simp only []
    rw [hsrc, idxSuccAt_eq_none, Option.map_none]
    intro t ht hct
    have := hd (t + 1) 0 (by omega) (by omega) hct
    omega

/-- **The string built from a list of children represents that list.** -/
theorem cgPath_cgOfPath (hd : Distinct ch m) (hcol : ∀ t ≤ m, (ch t).2 ≤ n)
    (hadj : ∀ t < m, (ch (t + 1)).2 ≤ (ch t).2 + 1 ∧ (ch t).2 ≤ (ch (t + 1)).2 + 1) :
    CGPath (cgOfPath lett peb nid n ch m) m ch where
  chk := chk_cgOfPath hd hadj
  srcEq := fun _ => isSrc_cgOfPath_iff (hcol 0 (Nat.zero_le _))
  inRange := fun t ht => by rw [cgOfPath_getElem? (hcol t ht)]; simp
  step := fun _ ht => succOf_cgOfPath hd hcol hadj ht
  last := succOf_cgOfPath_last hd hcol

/-- The string representation of the child at a vertex, read off `cgOfPath`. -/
lemma confAt_cgOfPath (v : Vtx Q) :
    confAt (cgOfPath lett peb nid n ch m) v =
      (List.range (n + 1)).map fun j =>
        (v.1, lett j, fun i => peb j i || (decide (i = nid) && decide (v.2 = j))) := by
  classical
  refine List.ext_getElem? ?_
  intro j
  by_cases hj : j ≤ n
  · rw [confAt, List.getElem?_mapIdx, cgOfPath_getElem? hj, List.getElem?_map,
      List.getElem?_eq_getElem (by simp; omega)]
    simp
  · have h1 : (confAt (cgOfPath lett peb nid n ch m) v)[j]? = none := by
      refine List.getElem?_eq_none ?_
      rw [confAt_length, cgOfPath_length]
      omega
    have h2 : ((List.range (n + 1)).map fun j =>
        ((v.1, lett j, fun i => peb j i || (decide (i = nid) && decide (v.2 = j))) :
          ConfLetter A Q k))[j]? = none := by
      refine List.getElem?_eq_none ?_
      simp
      omega
    rw [h1, h2]

end CG

end Lax194892Proofs.Transducers
