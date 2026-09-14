/-
**Cutting the annotated string of stage 1 into blocks.**

The annotation of stage 1 of the induction step of the book's snake lemma is
letter to letter: every annotated letter carries a bit `sep` saying that a block
boundary precedes it and a bit `sepA` saying that a block boundary follows it,
and the homomorphism that produces the marked input inserts the separators
accordingly.  This file computes the list of blocks of the resulting string
(`Transducers.BlockIdx.splitSep_homOf_outLet`): they are the factors of the
annotation between consecutive marked positions, with an empty block in front
and, if the last letter carries `sepA`, an empty block at the end.

Nothing here is specific to transducers.

Throughout, `seg` is `Transducers.TwoWay.seg`, the factor of a list between two
cuts; it is written out because the ambient namespace `Transducers` carries a
second, differently phrased, definition of the same name.
-/
import Lax916827Proofs.Source.PartC.SnakeChkSplit
import Lax916827Proofs.Source.PartC.SnakeAssemble
import Lax916827Proofs.Source.PartC.TwoWayBlock
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace BlockIdx

open RegPair TwoWay

variable {Γ C : Type}

/-! ## The separator-inserting homomorphism -/

/-- The image of an annotated letter: the letter, preceded and followed by a
separator as its two bits prescribe. -/
def outLet (sep sepA : Γ → Bool) (lett : Γ → C) (c : Γ) : List (Option C) :=
  (if sep c then [none] else []) ++ some (lett c) :: (if sepA c then [none] else [])

/-- The same without the trailing separator, which only the last letter of the
string may carry. -/
def outLetF (sep : Γ → Bool) (lett : Γ → C) (c : Γ) : List (Option C) :=
  (if sep c then [none] else []) ++ [some (lett c)]

variable {sep sepA : Γ → Bool} {lett : Γ → C}

/-- Away from the last letter the two homomorphisms agree. -/
lemma homOf_outLet_of_no_sepA {v : List Γ} (h : ∀ c ∈ v, sepA c = false) :
    homOf (outLet sep sepA lett) v = homOf (outLetF sep lett) v := by
  induction v with
  | nil => rfl
  | cons c v ih =>
      rw [homOf_cons, homOf_cons, ih (fun x hx => h x (by simp [hx])), outLet, outLetF,
        h c (by simp)]
      simp

/-- The string produced by the annotation: the blocks, followed by a final
separator if the last letter asks for one. -/
lemma homOf_outLet_eq (u : List Γ)
    (hsa : ∀ (j : ℕ) (hj : j < u.length), sepA u[j] = true → j = u.length - 1) :
    homOf (outLet sep sepA lett) u
      = homOf (outLetF sep lett) u ++ (if u.getLast?.elim false sepA then [none] else []) := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton v z ih =>
      have hv : ∀ c ∈ v, sepA c = false := by
        intro c hc
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
        by_contra hcon
        have hjvz : j < (v ++ [z]).length := by simp; omega
        have hcon' : sepA ((v ++ [z])[j]'hjvz) = true := by
          rw [List.getElem_append_left hj]
          simpa using hcon
        have := hsa j hjvz hcon'
        simp at this
        omega
      rw [homOf_append, homOf_append, homOf_outLet_of_no_sepA hv]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.elim]
      rw [show homOf (outLet sep sepA lett) [z] = outLet sep sepA lett z from by simp [homOf],
        show homOf (outLetF sep lett) [z] = outLetF sep lett z from by simp [homOf],
        outLet, outLetF]
      by_cases h : sepA z <;> simp [h, List.append_assoc]

/-! ## Splitting the string -/

lemma splitSep_append_none (v : List (Option C)) :
    splitSep (v ++ [none]) = splitSep v ++ [[]] := by
  induction v with
  | nil => rfl
  | cons x v ih =>
      cases x with
      | none => rw [List.cons_append, show splitSep (none :: (v ++ [none])) = [] :: splitSep
          (v ++ [none]) from rfl, ih, show splitSep (none :: v) = [] :: splitSep v from rfl]
                simp
      | some c =>
          rcases hv : splitSep v with _ | ⟨b, bs⟩
          · exact absurd hv (splitSep_ne_nil v)
          · rw [List.cons_append,
              show splitSep (some c :: (v ++ [none])) = (c :: (splitSep (v ++ [none])).headI)
                :: (splitSep (v ++ [none])).tail from by
                rw [splitSep]
                rcases h2 : splitSep (v ++ [none]) with _ | ⟨b', bs'⟩
                · exact absurd h2 (splitSep_ne_nil _)
                · rfl,
              ih, hv,
              show splitSep (some c :: v) = (c :: b) :: bs from by rw [splitSep, hv]]
            simp

/-- The blocks of the string produced by a list of blocks of the annotation. -/
lemma splitSep_homOf_outLetF_flatten (Bs : List (List Γ))
    (hB : ∀ B ∈ Bs, ∃ c B', B = c :: B' ∧ sep c = true ∧ ∀ x ∈ B', sep x = false) :
    splitSep (homOf (outLetF sep lett) Bs.flatten) = [] :: Bs.map (fun B => B.map lett) := by
  have hflat : ∀ (v : List Γ), (∀ x ∈ v, sep x = false) →
      homOf (outLetF sep lett) v = (v.map lett).map some := by
    intro v
    induction v with
    | nil => intro _; rfl
    | cons x v ih2 =>
        intro hv
        rw [homOf_cons, ih2 (fun y hy => hv y (by simp [hy])), outLetF, hv x (by simp)]
        simp
  induction Bs with
  | nil => rfl
  | cons B Bs ih =>
      obtain ⟨c, B', rfl, hc, hB'⟩ := hB B (by simp)
      have ihv := ih (fun B hB2 => hB B (by simp [hB2]))
      rcases hrest : splitSep (homOf (outLetF sep lett) Bs.flatten) with _ | ⟨b0, bs0⟩
      · exact absurd hrest (splitSep_ne_nil _)
      · rw [hrest] at ihv
        obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 ihv
        have hstep : homOf (outLetF sep lett) ((c :: B') ++ Bs.flatten)
            = none :: ((lett c :: B'.map lett).map some
                ++ homOf (outLetF sep lett) Bs.flatten) := by
          rw [List.cons_append, homOf_cons,
            show outLetF sep lett c = [none, some (lett c)] from by rw [outLetF, hc]; rfl,
            homOf_append _ _ _, hflat B' hB']
          simp
        rw [List.flatten_cons, hstep,
          show splitSep (none :: ((lett c :: B'.map lett).map some
              ++ homOf (outLetF sep lett) Bs.flatten))
            = [] :: splitSep ((lett c :: B'.map lett).map some
              ++ homOf (outLetF sep lett) Bs.flatten) from rfl,
          splitSep_map_some_append _ _ _ _ hrest]
        simp

/-! ## Reading a factor position by position -/

lemma seg_getElem (u : List Γ) (x y i : ℕ) (h : i < (TwoWay.seg u x y).length)
    (h2 : x + i < u.length) : (TwoWay.seg u x y)[i] = u[x + i] := by
  simp [TwoWay.seg]

lemma exists_index_of_mem_seg {u : List Γ} {x y : ℕ} (hy : y ≤ u.length) {c : Γ}
    (hc : c ∈ TwoWay.seg u x y) : ∃ j, x ≤ j ∧ j < y ∧ ∃ hj : j < u.length, c = u[j] := by
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have hlen : (TwoWay.seg u x y).length = y - x := TwoWay.seg_length u hy
  rw [hlen] at hi
  have h2 : x + i < u.length := by omega
  exact ⟨x + i, by omega, by omega, h2, by rw [← hci, seg_getElem u x y i (by rw [hlen]; omega) h2]⟩

lemma seg_cons {u : List Γ} {x y : ℕ} (hxy : x < y) (hx : x < u.length) :
    TwoWay.seg u x y = u[x] :: TwoWay.seg u (x + 1) y := by
  rw [TwoWay.seg, TwoWay.seg, List.drop_eq_getElem_cons hx,
    show y - x = (y - (x + 1)) + 1 from by omega, List.take_succ_cons]

/-- Splitting off the first element of a `List.range`-indexed map. -/
lemma cons_range_map {D : Type} (f : ℕ → D) :
    ∀ N : ℕ, f 0 :: (List.range N).map (fun m => f (m + 1)) = (List.range (N + 1)).map f := by
  intro N
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-! ## The blocks of the annotation -/

/-- The factors of the annotation between consecutive marked positions cover the
annotation. -/
lemma flatten_seg_range (u : List Γ) (Y : ℕ → ℕ) (hmono : ∀ m, Y m ≤ Y (m + 1)) :
    ∀ L : ℕ, ((List.range L).map (fun m => TwoWay.seg u (Y m) (Y (m + 1)))).flatten
      = TwoWay.seg u (Y 0) (Y L) := by
  intro L
  induction L with
  | zero => simp [seg_eq_nil (le_refl (Y 0))]
  | succ L ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, ih]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      exact seg_append (snakeY_chain hmono 0 L (Nat.zero_le _)) (hmono L)

/-- The number of blocks of the string produced by the annotation, minus one. -/
noncomputable def nbl (sep sepA : Γ → Bool) (u : List Γ) : ℕ :=
  nsep sep u + (if u.getLast?.elim false sepA then 1 else 0)

/-- **The blocks of the string produced by the annotation** are the factors of
the annotation between consecutive marked positions, with an empty block in
front and, if the last letter carries `sepA`, an empty block at the end. -/
theorem splitSep_homOf_outLet {u : List Γ} (hne : u ≠ [])
    (h0 : ∀ hu : 0 < u.length, sep u[0] = true)
    (hsa : ∀ (j : ℕ) (hj : j < u.length), sepA u[j] = true → j = u.length - 1) :
    splitSep (homOf (outLet sep sepA lett) u)
      = (List.range (nbl sep sepA u + 1)).map
          (fun m => (TwoWay.seg u (bstart sep u m) (bstart sep u (m + 1))).map lett) := by
  classical
  have hulen : 0 < u.length := by
    cases u with
    | nil => exact absurd rfl hne
    | cons a v => simp
  set n := nsep sep u with hn
  have hb1 : bstart sep u 1 = 0 :=
    Nat.le_zero.1 (bstart_min hulen (by rw [blk_zero_of_sep hulen (h0 hulen)]))
  have hbig : ∀ k, n < k → bstart sep u k = u.length := fun k hk => bstart_of_gt hk
  have hex : ∀ m, m + 1 ≤ n → ∃ j, j < u.length ∧ m + 1 ≤ blk sep u j :=
    fun m hm => ⟨u.length - 1, by omega, by rw [blk_last hulen]; exact hm⟩
  set Bs : List (List Γ) :=
    (List.range n).map (fun m => TwoWay.seg u (bstart sep u (m + 1)) (bstart sep u (m + 1 + 1)))
    with hBs
  -- the factors between consecutive marked positions cover the annotation
  have hflat : Bs.flatten = u := by
    have h := flatten_seg_range u (fun m => bstart sep u (m + 1))
      (fun m => bstart_mono (by omega)) n
    rw [hBs, h, hb1, hbig (n + 1) (by omega), TwoWay.seg, Nat.sub_zero, List.drop_zero,
      List.take_length]
  -- every factor starts at a marked position and contains no other one
  have hB : ∀ B ∈ Bs, ∃ c B', B = c :: B' ∧ sep c = true ∧ ∀ x ∈ B', sep x = false := by
    intro B hBmem
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hBmem
    have hmn : m < n := List.mem_range.1 hm
    have hXY : bstart sep u (m + 1) < bstart sep u (m + 1 + 1) :=
      bstart_lt_succ (by omega) (by omega) hulen
    have hYu : bstart sep u (m + 1 + 1) ≤ u.length := bstart_le_length _
    have hXu : bstart sep u (m + 1) < u.length := by omega
    have hblkX : blk sep u (bstart sep u (m + 1)) = m + 1 :=
      blk_bstart (hex m (by omega)) (by omega)
    have hsepX : sep u[bstart sep u (m + 1)] = true := by
      rw [sep_iff_bstart h0 hXu, hblkX]
    refine ⟨u[bstart sep u (m + 1)],
      TwoWay.seg u (bstart sep u (m + 1) + 1) (bstart sep u (m + 1 + 1)),
      seg_cons hXY hXu, hsepX, ?_⟩
    intro x hx
    obtain ⟨j, hj1, hj2, hju, rfl⟩ := exists_index_of_mem_seg hYu hx
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    have hjb : j = bstart sep u (blk sep u j) := (sep_iff_bstart h0 hju).1 hcon
    have hmono : blk sep u (bstart sep u (m + 1)) ≤ blk sep u j := blk_mono (by omega)
    have hne1 : blk sep u j ≠ m + 1 := by
      intro heq
      rw [heq] at hjb
      omega
    have : bstart sep u (m + 1 + 1) ≤ bstart sep u (blk sep u j) := bstart_mono (by omega)
    omega
  have hsplitF : splitSep (homOf (outLetF sep lett) u) = [] :: Bs.map (fun B => B.map lett) := by
    rw [← hflat]
    exact splitSep_homOf_outLetF_flatten Bs hB
  have hhead : ((TwoWay.seg u (bstart sep u 0) (bstart sep u 1)).map lett) = [] := by
    rw [bstart_zero, hb1, seg_eq_nil (le_refl 0)]
    rfl
  have hpre : [] :: Bs.map (fun B => B.map lett)
      = (List.range (n + 1)).map
          (fun m => (TwoWay.seg u (bstart sep u m) (bstart sep u (m + 1))).map lett) := by
    rw [← cons_range_map
      (fun m => (TwoWay.seg u (bstart sep u m) (bstart sep u (m + 1))).map lett) n,
      hhead, hBs, List.map_map]
    rfl
  rw [homOf_outLet_eq u hsa]
  by_cases hlast : u.getLast?.elim false sepA
  · have hfn : (TwoWay.seg u (bstart sep u (n + 1)) (bstart sep u (n + 1 + 1))).map lett = [] := by
      rw [hbig (n + 1) (by omega), hbig (n + 1 + 1) (by omega), seg_eq_nil (le_refl _)]
      rfl
    rw [if_pos hlast, splitSep_append_none, hsplitF, hpre]
    show _ = (List.range (nbl sep sepA u + 1)).map _
    rw [nbl, ← hn, if_pos hlast, show n + 1 + 1 = (n + 1) + 1 from rfl]
    conv_rhs => rw [List.range_succ]
    rw [List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [hfn]
  · rw [if_neg hlast, List.append_nil, hsplitF, hpre]
    show _ = (List.range (nbl sep sepA u + 1)).map _
    rw [nbl, ← hn, if_neg hlast, Nat.add_zero]

end BlockIdx

end Lax916827Proofs.Transducers
