/-
**Assembling the marking of stage 1 out of the data of the pieces.**

The annotation that the induction step of the book's snake lemma needs
(`TwoWay.IsSnakeMarking`, `RequestProject/PartC/SnakeBlock.lean`) is built from
purely numerical data:

* the cutting points `Y 0 ≤ Y 1 ≤ ⋯ ≤ Y (N+2)` of the input into the `N+2`
  blocks of the record-breaker decomposition (`Y m` is the first position of the
  `m`-th block; the `0`-th block is empty and the last one ends at the end of
  the input);
* for every pair `i` of neighbouring blocks and every piece slot `r`, the window
  `[a i r, b i r)` of that piece -- a factor of the pair -- and the parameters
  `p i r` of the window transducer computing it.

This file turns such data into an annotated string and proves that the string is
a correct marking, provided the windows lie inside the corresponding pair of
blocks and the outputs of the pieces come out right
(`TwoWay.isSnakeMarking_snakeAnn`).  What is left open in stage 1 is then
exactly the *machine-theoretic* half: that the data above can be computed from
the input by a regular function.
-/
import Lax916827Proofs.Source.PartC.SnakeBlock
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open RegPair

variable {A B Q : Type}

/-! ## Annotating the letters of a factor with their positions -/

/-- Annotate every letter of a list with its position, the first one being `j`. -/
def annFrom {C : Type} (f : ℕ → A → C) : ℕ → List A → List C
  | _, [] => []
  | j, c :: v => f j c :: annFrom f (j + 1) v

@[simp] lemma annFrom_nil {C : Type} (f : ℕ → A → C) (j : ℕ) : annFrom f j ([] : List A) = [] :=
  rfl

@[simp] lemma annFrom_cons {C : Type} (f : ℕ → A → C) (j : ℕ) (c : A) (v : List A) :
    annFrom f j (c :: v) = f j c :: annFrom f (j + 1) v := rfl

lemma head?_annFrom {C : Type} (f : ℕ → A → C) (j : ℕ) (v : List A) :
    (annFrom f j v).head? = v.head?.map (f j) := by cases v <;> rfl

lemma annFrom_eq_nil_iff {C : Type} (f : ℕ → A → C) (j : ℕ) (v : List A) :
    annFrom f j v = [] ↔ v = [] := by cases v <;> simp

/-! ## Factors of the input -/

lemma seg_eq_nil {w : List A} {x y : ℕ} (h : y ≤ x) : seg w x y = [] := by
  rw [seg, show y - x = 0 from by omega, List.take_zero]

lemma seg_append {w : List A} {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    seg w x y ++ seg w y z = seg w x z := by
  have hd : w.drop y = (w.drop x).drop (y - x) := by
    rw [List.drop_drop]; congr 1; omega
  rw [seg, seg, seg, hd, show z - x = (y - x) + (z - y) from by omega, List.take_add]

/-- Cutting a factor out of a factor. -/
lemma seg_seg (w : List A) {s e a b : ℕ} (hse : s ≤ e) :
    seg (seg w s e) (a - s) (b - s) = seg w (max a s) (min e b) := by
  rw [seg, seg, seg, List.drop_take, List.take_take, List.drop_drop]
  congr 1
  · omega
  · congr 1; omega

/-! ## The annotation built from the data of the pieces -/

variable {R : ℕ}

/-- The slot data of the `t`-th slot of a letter of the `m`-th block: the even
slots carry the data of the pair of blocks in which the letter's block is the
left one, the odd slots that of the pair in which it is the right one. -/
def slotData (K : ℕ) (a b : ℕ → ℕ → ℕ) (p : ℕ → ℕ → PieceParam A Q) (m j : ℕ)
    (t : Fin (2 * (2 * K + 1))) : Bool × PieceParam A Q :=
  let r := t.val / 2
  let i := if t.val % 2 = 1 then m - 1 else m
  (decide (a i r ≤ j ∧ j < b i r), p i r)

/-- The annotated letters of the `m`-th block. -/
def snakeBlock (w : List A) (K : ℕ) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) (m : ℕ) : List (SnakeLet A Q (2 * (2 * K + 1))) :=
  annFrom (fun j c => (c, slotData K a b p m j)) (Y m) (seg w (Y m) (Y (m + 1)))

/-- **The annotated input** built from the cutting points `Y` and from the
windows and parameters of the pieces. -/
def snakeAnn (w : List A) (K : ℕ) (N : ℕ) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) : List (Option (SnakeLet A Q (2 * (2 * K + 1)))) :=
  blockStr ((List.range (N + 2)).map (snakeBlock w K Y a b p))

/-! ## Reading the annotation back -/

lemma extractWinAux_map_some (r : ℕ) (side : Bool) (L : List (SnakeLet A Q R))
    (rest : List (Option (SnakeLet A Q R))) :
    extractWinAux r side (L.map some ++ rest)
      = (L.filter (fun g => inWin (slot side r) g)).map Prod.fst
        ++ extractWinAux r side rest := by
  induction L with
  | nil => simp
  | cons g L ih =>
      rw [List.map_cons, List.cons_append,
        show extractWinAux r side (some g :: (L.map some ++ rest))
          = (if inWin (slot side r) g then [g.1] else [])
              ++ extractWinAux r side (L.map some ++ rest) from rfl,
        ih, List.filter_cons]
      by_cases h : inWin (slot side r) g = true
      · rw [if_pos h, if_pos h]
        simp
      · rw [if_neg h, if_neg h]
        simp

lemma extractWin_encPair (r : ℕ) (C D : List (SnakeLet A Q R)) :
    extractWin r (encPair C D)
      = (C.filter (fun g => inWin (slot false r) g)).map Prod.fst
        ++ (D.filter (fun g => inWin (slot true r) g)).map Prod.fst := by
  rw [encPair, extractWin, extractWinAux_map_some]
  congr 1
  rw [show extractWinAux r false (none :: D.map some)
      = extractWinAux r true (D.map some) from rfl,
    show (D.map some : List (Option (SnakeLet A Q R))) = D.map some ++ [] from by simp,
    extractWinAux_map_some]
  simp [extractWinAux]

lemma firstLetAux_map_some (s : Bool) (L : List (SnakeLet A Q R))
    (rest : List (Option (SnakeLet A Q R))) :
    firstLetAux s (L.map some ++ rest)
      = match L.head? with
        | some g => some (s, g)
        | none => firstLetAux s rest := by
  cases L with
  | nil => simp
  | cons g L => rfl

lemma paramOf_encPair (r : ℕ) (C D : List (SnakeLet A Q R)) :
    paramOf r (encPair C D)
      = match C.head? with
        | some g => parAt (slot false r) g
        | none => match D.head? with
          | some g => parAt (slot true r) g
          | none => default := by
  rw [paramOf, firstLet, encPair, firstLetAux_map_some]
  cases hC : C.head? with
  | some g => simp
  | none =>
      simp only []
      rw [show firstLetAux false (none :: D.map some)
          = firstLetAux true (D.map some) from rfl,
        show (D.map some : List (Option (SnakeLet A Q R))) = D.map some ++ [] from by simp,
        firstLetAux_map_some]
      cases hD : D.head? with
      | some g => simp
      | none => simp [firstLetAux]

/-! ## The letters selected by a slot -/

/-- **The letters of a block that a slot selects** are exactly the letters of
the window of that slot which lie in the block. -/
lemma filter_annFrom (t : ℕ) (f : ℕ → A → SnakeLet A Q R) (a b : ℕ)
    (hbit : ∀ j c, inWin t (f j c) = decide (a ≤ j ∧ j < b))
    (hfst : ∀ j c, (f j c).1 = c) :
    ∀ (v : List A) (j : ℕ),
      ((annFrom f j v).filter (fun g => inWin t g)).map Prod.fst = seg v (a - j) (b - j) := by
  intro v
  induction v with
  | nil => intro j; simp [seg]
  | cons c v ih =>
      intro j
      rw [annFrom_cons, List.filter_cons, hbit j c]
      by_cases h : a ≤ j ∧ j < b
      · rw [if_pos (by simpa using h)]
        rw [List.map_cons, hfst j c, ih (j + 1)]
        have h1 : a - j = 0 := by omega
        have h2 : a - (j + 1) = 0 := by omega
        rw [h1, h2, seg, seg]
        simp only [List.drop_zero, Nat.sub_zero]
        rw [show b - j = (b - (j + 1)) + 1 from by omega]
        rw [List.take_succ_cons]
      · rw [if_neg (by simpa using h), ih (j + 1)]
        rcases Nat.lt_or_ge j a with hja | hja
        · rw [seg, seg]
          have hd : (c :: v).drop (a - j) = v.drop (a - (j + 1)) := by
            rw [show a - j = (a - (j + 1)) + 1 from by omega]
            simp
          rw [hd]
          congr 1
          omega
        · have hbj : b ≤ j := by omega
          rw [seg_eq_nil (by omega), seg_eq_nil (by omega)]

/-! ## The marking -/

section Marking

variable (M : TwoWay A B Q) (K : ℕ) (w : List A)

/-- The blocks of the annotation. -/
lemma splitSep_snakeAnn (N : ℕ) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) :
    splitSep (snakeAnn w K N Y a b p) = (List.range (N + 2)).map (snakeBlock w K Y a b p) := by
  refine splitSep_blockStr _ ?_
  simp

lemma pairBlocks_snakeAnn (N : ℕ) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) :
    pairBlocks (snakeAnn w K N Y a b p)
      = List.zipWith encPair ((List.range (N + 2)).map (snakeBlock w K Y a b p))
          (((List.range (N + 2)).map (snakeBlock w K Y a b p)).tail) := by
  rw [pairBlocks, splitSep_snakeAnn, pairsList]

lemma length_pairBlocks_snakeAnn (N : ℕ) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) :
    (pairBlocks (snakeAnn w K N Y a b p)).length = N + 1 := by
  rw [pairBlocks_snakeAnn]
  simp

lemma getElem?_pairBlocks_snakeAnn (N : ℕ) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) {i : ℕ} (hi : i < N + 1) :
    (pairBlocks (snakeAnn w K N Y a b p))[i]?
      = some (encPair (snakeBlock w K Y a b p i) (snakeBlock w K Y a b p (i + 1))) := by
  have h1 : ((List.range (N + 2)).map (snakeBlock w K Y a b p))[i]?
      = some (snakeBlock w K Y a b p i) := by
    rw [List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have h2 : (((List.range (N + 2)).map (snakeBlock w K Y a b p)).tail)[i]?
      = some (snakeBlock w K Y a b p (i + 1)) := by
    rw [List.getElem?_tail, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  rw [pairBlocks_snakeAnn]
  simp [List.getElem?_zipWith, h1, h2]

/-- The window that a slot cuts out of a block. -/
lemma extract_snakeBlock (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) (m : ℕ) (side : Bool) (r : ℕ) (hr : r < 2 * K + 1)
    (hY : Y m ≤ Y (m + 1)) :
    ((snakeBlock w K Y a b p m).filter (fun g => inWin (slot side r) g)).map Prod.fst
      = seg w (max (a (if side then m - 1 else m) r) (Y m))
          (min (Y (m + 1)) (b (if side then m - 1 else m) r)) := by
  set i := if side then m - 1 else m with hi
  have hslot : slot side r < 2 * (2 * K + 1) := slot_lt hr side
  have hbit : ∀ (j : ℕ) (c : A),
      inWin (slot side r) ((c, slotData K a b p m j) : SnakeLet A Q (2 * (2 * K + 1)))
        = decide (a i r ≤ j ∧ j < b i r) := by
    intro j c
    rw [inWin, dif_pos hslot]
    show (slotData K a b p m j ⟨slot side r, hslot⟩).1 = _
    rw [slotData]
    cases side <;> simp [slot, hi, Nat.mul_add_div]
  have hfst : ∀ (j : ℕ) (c : A),
      (((c, slotData K a b p m j) : SnakeLet A Q (2 * (2 * K + 1)))).1 = c := fun _ _ => rfl
  rw [snakeBlock, filter_annFrom (slot side r) _ (a i r) (b i r) hbit hfst,
    seg_seg w hY]

/-- The parameters that a slot reads off a block. -/
lemma param_snakeBlock (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q) (m : ℕ) (side : Bool) (r : ℕ) (hr : r < 2 * K + 1)
    {g : SnakeLet A Q (2 * (2 * K + 1))} (hg : (snakeBlock w K Y a b p m).head? = some g) :
    parAt (slot side r) g = p (if side then m - 1 else m) r := by
  have hslot : slot side r < 2 * (2 * K + 1) := slot_lt hr side
  rw [snakeBlock, head?_annFrom] at hg
  rcases hc : (seg w (Y m) (Y (m + 1))).head? with _ | c
  · rw [hc] at hg; simp at hg
  · rw [hc] at hg
    simp only [Option.map_some, Option.some.injEq] at hg
    subst hg
    rw [parAt, dif_pos hslot]
    show (slotData K a b p m (Y m) ⟨slot side r, hslot⟩).2 = _
    rw [slotData]
    cases side <;> simp [slot, Nat.mul_add_div]

/-- The cutting points are monotone. -/
lemma snakeY_chain {Y : ℕ → ℕ} (hYmono : ∀ m, Y m ≤ Y (m + 1)) :
    ∀ m n : ℕ, m ≤ n → Y m ≤ Y n := by
  intro m n hmn
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact le_trans (ih (by omega)) (hYmono n)
      · have : m = n + 1 := by omega
        rw [this]

/-- **The window and the parameters that the `r`-th slot of the `i`-th pair of
neighbouring blocks reads off the annotation** are the ones prescribed by the
data. -/
lemma extractWin_paramOf_snakeAnn {N : ℕ} (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q)
    (hYmono : ∀ m, Y m ≤ Y (m + 1)) (hYlast : Y (N + 2) = w.length)
    (hYne : ∀ i ≤ N, Y i < Y (i + 2))
    {i r : ℕ} (hiN : i ≤ N) (hr : r < 2 * K + 1)
    (hwa : Y i ≤ a i r) (hab : a i r ≤ b i r) (hbY : b i r ≤ Y (i + 2)) :
    extractWin r (encPair (snakeBlock w K Y a b p i) (snakeBlock w K Y a b p (i + 1)))
        = seg w (a i r) (b i r) ∧
      paramOf r (encPair (snakeBlock w K Y a b p i) (snakeBlock w K Y a b p (i + 1)))
        = p i r := by
  classical
  have hchain : ∀ m n : ℕ, m ≤ n → Y m ≤ Y n := snakeY_chain hYmono
  refine ⟨?_, ?_⟩
  · rw [extractWin_encPair,
      extract_snakeBlock K w Y a b p i false r hr (hYmono i),
      extract_snakeBlock K w Y a b p (i + 1) true r hr (hYmono (i + 1))]
    rw [show (if (false : Bool) = true then i - 1 else i) = i from by simp,
      show (if (true : Bool) = true then (i + 1) - 1 else i + 1) = i from by simp]
    have hmax : max (a i r) (Y i) = a i r := by omega
    rw [hmax]
    by_cases hb1 : b i r ≤ Y (i + 1)
    · have h1 : min (Y (i + 1)) (b i r) = b i r := by omega
      have h2 : max (a i r) (Y (i + 1)) = Y (i + 1) := by omega
      rw [h1, h2, seg_eq_nil (by omega : min (Y (i + 1 + 1)) (b i r) ≤ Y (i + 1))]
      simp
    · have h1 : min (Y (i + 1)) (b i r) = Y (i + 1) := by omega
      have h2 : min (Y (i + 1 + 1)) (b i r) = b i r := by
        have := hbY
        have he : i + 1 + 1 = i + 2 := by omega
        rw [he]
        omega
      rw [h1, h2]
      by_cases ha1 : a i r ≤ Y (i + 1)
      · rw [show max (a i r) (Y (i + 1)) = Y (i + 1) from by omega]
        exact seg_append ha1 (by omega)
      · rw [show max (a i r) (Y (i + 1)) = a i r from by omega,
          seg_eq_nil (by omega : Y (i + 1) ≤ a i r)]
        simp
  · rw [paramOf_encPair]
    rcases hC : (snakeBlock w K Y a b p i).head? with _ | g
    · -- the left block is empty, so the right one is not
      have hCnil : snakeBlock w K Y a b p i = [] := by
        rcases hL : snakeBlock w K Y a b p i with _ | ⟨g', L⟩
        · rfl
        · rw [hL] at hC; simp at hC
      have hseg : seg w (Y i) (Y (i + 1)) = [] := by
        rw [snakeBlock, annFrom_eq_nil_iff] at hCnil
        exact hCnil
      have hYeq : Y (i + 1) ≤ Y i ∨ w.length ≤ Y i := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨h1, h2⟩ := hcon
        have hlen : (seg w (Y i) (Y (i + 1))).length = 0 := by rw [hseg]; rfl
        rw [seg_length w (by
          calc Y (i + 1) ≤ Y (N + 2) := hchain (i + 1) (N + 2) (by omega)
            _ = w.length := hYlast)] at hlen
        omega
      have hDne : snakeBlock w K Y a b p (i + 1) ≠ [] := by
        rw [Ne, snakeBlock, annFrom_eq_nil_iff]
        intro hcon
        have hlen : (seg w (Y (i + 1)) (Y (i + 1 + 1))).length = 0 := by rw [hcon]; rfl
        have h2 : Y (i + 1 + 1) ≤ w.length := by
          calc Y (i + 1 + 1) ≤ Y (N + 2) := hchain _ _ (by omega)
            _ = w.length := hYlast
        rw [seg_length w h2] at hlen
        have := hYne i hiN
        have he : i + 1 + 1 = i + 2 := by omega
        rw [he] at hlen h2
        omega
      rcases hD : (snakeBlock w K Y a b p (i + 1)).head? with _ | g
      · exact absurd (List.head?_eq_none_iff.1 hD) hDne
      · simp only []
        rw [param_snakeBlock K w Y a b p (i + 1) true r hr hD]
        simp
    · simp only []
      rw [param_snakeBlock K w Y a b p i false r hr hC]
      simp

/-- **The annotation built from the data of the pieces is a correct marking.**
The hypotheses are that the blocks tile the input (`hYmono`, `hYlast`),
that no pair of neighbouring blocks is empty (`hYne`), that the window of every
piece lies inside the corresponding pair of blocks (`hwin`), and that the piece
outputs are correct (`hpiece`). -/
theorem isSnakeMarking_snakeAnn {N : ℕ} (hN : N = rbN M w) (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q)
    (hYmono : ∀ m, Y m ≤ Y (m + 1)) (hYlast : Y (N + 2) = w.length)
    (hYne : ∀ i ≤ N, Y i < Y (i + 2))
    (hwin : ∀ i ≤ N, ∀ r < 2 * K + 1,
      Y i ≤ a i r ∧ a i r ≤ b i r ∧ b i r ≤ Y (i + 2))
    (hpiece : ∀ i ≤ N, ∀ r < 2 * K + 1,
      pieceOut M (K - 1) (p i r) (seg w (a i r) (b i r)) = pieceOutput M w K i r) :
    IsSnakeMarking M K w (snakeAnn w K N Y a b p) := by
  classical
  refine ⟨by rw [length_pairBlocks_snakeAnn, hN], ?_⟩
  intro i z hz r hr
  have hilen : i < N + 1 := by
    by_contra hcon
    have : (pairBlocks (snakeAnn w K N Y a b p))[i]? = none := by
      apply List.getElem?_eq_none
      rw [length_pairBlocks_snakeAnn]
      omega
    rw [this] at hz
    simp at hz
  have hiN : i ≤ N := by omega
  have hzeq : z = encPair (snakeBlock w K Y a b p i) (snakeBlock w K Y a b p (i + 1)) := by
    rw [getElem?_pairBlocks_snakeAnn K w N Y a b p hilen] at hz
    exact (Option.some_injective _ hz).symm
  subst hzeq
  obtain ⟨hwa, hab, hbY⟩ := hwin i hiN r hr
  obtain ⟨hwindow, hparam⟩ :=
    extractWin_paramOf_snakeAnn K w Y a b p hYmono hYlast hYne hiN hr hwa hab hbY
  rw [hwindow, hparam]
  exact hpiece i hiN r hr

/-- **The neighbouring-block map combinator applied to the block function, on an
annotation built from the data of the pieces, is the concatenation of the
outputs of the pieces.**  Unlike `TwoWay.isSnakeMarking_snakeAnn` this says
nothing about the record-breaker decomposition: it only reads the annotation
back. -/
theorem pairMap_snakeAnn {k N : ℕ} (Y : ℕ → ℕ) (a b : ℕ → ℕ → ℕ)
    (p : ℕ → ℕ → PieceParam A Q)
    (hYmono : ∀ m, Y m ≤ Y (m + 1)) (hYlast : Y (N + 2) = w.length)
    (hYne : ∀ i ≤ N, Y i < Y (i + 2))
    (hwin : ∀ i ≤ N, ∀ r < 2 * K + 1,
      Y i ≤ a i r ∧ a i r ≤ b i r ∧ b i r ≤ Y (i + 2)) :
    pairMap (blockFun M k (2 * K + 1)) (snakeAnn w K N Y a b p)
      = (List.range (N + 1)).flatMap (fun i => (List.range (2 * K + 1)).flatMap
          (fun r => pieceOut M k (p i r) (seg w (a i r) (b i r)))) := by
  classical
  have hmap : (pairBlocks (snakeAnn w K N Y a b p)).map (blockFun M k (2 * K + 1))
      = (List.range (N + 1)).map (fun i => (List.range (2 * K + 1)).flatMap
          (fun r => pieceOut M k (p i r) (seg w (a i r) (b i r)))) := by
    refine List.ext_getElem (by simp [length_pairBlocks_snakeAnn]) ?_
    intro i h1 h2
    have h1' : i < (pairBlocks (snakeAnn w K N Y a b p)).length := by simpa using h1
    have hilen : i < N + 1 := by
      rw [length_pairBlocks_snakeAnn] at h1'; exact h1'
    have hiN : i ≤ N := by omega
    have hz : (pairBlocks (snakeAnn w K N Y a b p))[i]'h1'
        = encPair (snakeBlock w K Y a b p i) (snakeBlock w K Y a b p (i + 1)) := by
      have := getElem?_pairBlocks_snakeAnn K w N Y a b p hilen
      rw [List.getElem?_eq_getElem h1'] at this
      exact Option.some_injective _ this
    rw [List.getElem_map, List.getElem_map, List.getElem_range, hz, blockFun]
    refine List.flatMap_congr ?_
    intro r hr
    have hr' : r < 2 * K + 1 := List.mem_range.1 hr
    obtain ⟨hwa, hab, hbY⟩ := hwin i hiN r hr'
    obtain ⟨hwindow, hparam⟩ :=
      extractWin_paramOf_snakeAnn K w Y a b p hYmono hYlast hYne hiN hr' hwa hab hbY
    rw [hwindow, hparam]
  rw [pairMap, hmap, ← List.flatMap_def]

end Marking

end TwoWay

end Lax916827Proofs.Transducers
