/-
**The chain of pieces of stage 1 of the induction step of the book's snake
lemma, as a self-contained package of data.**

The checking automaton of stage 1 (`RequestProject/PartC/SnakeChkEnc.lean`)
verifies *local* conditions on an annotation of the input.  What those local
conditions add up to is the package collected here
(`Transducers.TwoWay.Chk.ChainData`): the cutting points of the input into
blocks, and, for every pair of neighbouring blocks and every piece slot, a
window inside that pair together with the parameters of a window transducer, so
that the pieces form a *chain*: the first one starts at the left end of the
input in the initial state, consecutive pieces meet at a common cut in a common
state, and the last one halts.

The one theorem of this file, `Transducers.TwoWay.Chk.runOut_of_chainData`, says
that the outputs of the pieces of such a chain concatenate to the output of the
run.  It is the whole mathematical content of the soundness of the checking
automaton; reading the package off an accepted annotation
(`RequestProject/PartC/SnakeChkRead.lean`) and building an annotation from it
(`RequestProject/PartC/SnakeChkBuild.lean`) is then bookkeeping.
-/
import Lax916827Proofs.Source.PartC.SnakeChkWin
import Lax916827Proofs.Source.PartC.SnakeAssemble
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q : Type}

/-! ## The two cuts of a piece -/

/-- The cut at which a piece with parameters `p` and window `[x, y)` starts: the
left end of the window for the kinds `1` and `3`, the right end for the kinds
`2` and `4`. -/
def stCut (p : PieceParam A Q) (x y : ℕ) : ℕ :=
  if kdOf p = 1 ∨ kdOf p = 3 then x else y

/-- The cut at which a piece with parameters `p` and window `[x, y)` ends.  It
is used only for the kinds `1` and `2`, the pieces of the kinds `3` and `4`
halting inside their window. -/
def enCut (p : PieceParam A Q) (x y : ℕ) : ℕ :=
  if kdOf p = 1 then y else x

/-! ## The chain of pieces -/

/-- **A chain of pieces of the run of `M` on `w`.**  The input is cut into
`N + 2` blocks at the positions `Y 0 = Y 1 = 0 ≤ Y 2 ≤ ⋯ ≤ Y (N+2) = |w|`, and
for every pair `i ≤ N` of neighbouring blocks and every slot `r ≤ 2K` there is a
window `[a i r, b i r)` inside the pair together with the parameters `p i r` of
a window transducer computing that piece.

The conditions are exactly the ones that the checking automaton of stage 1
verifies: the windows lie in their pair, the context letters and the states are
the ones prescribed by the input, the kinds follow the pattern of the
record-breaker decomposition, the pieces of a pair meet at a common cut in a
common state, the first piece of a pair starts at the boundary between its two
blocks and the last one ends at the right end of the pair, and every window
satisfies the window condition. -/
structure ChainData (M : TwoWay A B Q) (K : ℕ) (w : List A) where
  /-- The number of pairs of neighbouring blocks, minus one. -/
  N : ℕ
  /-- The first position of the `m`-th block. -/
  Y : ℕ → ℕ
  /-- The left end of the window of the `r`-th piece of the pair `i`. -/
  a : ℕ → ℕ → ℕ
  /-- The right end of the window of the `r`-th piece of the pair `i`. -/
  b : ℕ → ℕ → ℕ
  /-- The parameters of the `r`-th piece of the pair `i`. -/
  p : ℕ → ℕ → PieceParam A Q
  /-- The `0`-th block is empty. -/
  Y_one : Y 1 = 0
  /-- The blocks follow one another. -/
  Y_mono : ∀ m, Y m ≤ Y (m + 1)
  /-- The last block ends at the end of the input. -/
  Y_last : Y (N + 2) = w.length
  /-- No pair of neighbouring blocks is empty. -/
  Y_lt : ∀ i ≤ N, Y i < Y (i + 2)
  /-- All the blocks but the `0`-th one and the last one are nonempty.  (The
  `0`-th block is always empty, and the last one is empty exactly when the last
  record-breaking column is the right end of the input.) -/
  Y_blk : ∀ m, 1 ≤ m → m ≤ N → Y m < Y (m + 1)
  /-- The window of a piece lies inside its pair of blocks. -/
  win : ∀ i ≤ N, ∀ r < 2 * K + 1, Y i ≤ a i r ∧ a i r ≤ b i r ∧ b i r ≤ Y (i + 2)
  /-- The letter to the left of the window. -/
  ctxL : ∀ i ≤ N, ∀ r < 2 * K + 1, lOf (p i r) = (w.take (a i r)).getLast?
  /-- The letter to the right of the window. -/
  ctxR : ∀ i ≤ N, ∀ r < 2 * K + 1, rOf (p i r) = (w.drop (b i r)).head?
  /-- Every piece announces an entry and an exit state. -/
  st : ∀ i ≤ N, ∀ r < 2 * K + 1, ∃ q f, stOf (p i r) = some (q, f)
  /-- The pieces other than the last one of a pair cross their window. -/
  kind : ∀ i ≤ N, ∀ r < 2 * K, kdOf (p i r) = 1 ∨ kdOf (p i r) = 2
  /-- The last piece of a pair which is not the last pair crosses its window. -/
  kind_mid : ∀ i < N, kdOf (p i (2 * K)) = 1 ∨ kdOf (p i (2 * K)) = 2
  /-- The last piece of the last pair halts inside its window. -/
  kind_last : kdOf (p N (2 * K)) = 3 ∨ kdOf (p N (2 * K)) = 4
  /-- A halting piece does not change the state. -/
  st_last : entOf (p N (2 * K)) = extOf (p N (2 * K))
  /-- The first piece of a pair starts at the boundary between its two blocks. -/
  cut_zero : ∀ i ≤ N, stCut (p i 0) (a i 0) (b i 0) = Y (i + 1)
  /-- Consecutive pieces of a pair meet at a common cut. -/
  cut_step : ∀ i ≤ N, ∀ r < 2 * K,
    enCut (p i r) (a i r) (b i r) = stCut (p i (r + 1)) (a i (r + 1)) (b i (r + 1))
  /-- The last piece of a pair which is not the last pair ends at the right end
  of the pair. -/
  cut_last : ∀ i < N, enCut (p i (2 * K)) (a i (2 * K)) (b i (2 * K)) = Y (i + 2)
  /-- The first piece starts in the initial state. -/
  ent_zero : entOf (p 0 0) = some M.init
  /-- Consecutive pieces of a pair meet in a common state. -/
  ext_step : ∀ i ≤ N, ∀ r < 2 * K, extOf (p i r) = entOf (p i (r + 1))
  /-- The last piece of a pair and the first piece of the next one meet in a
  common state. -/
  ext_pair : ∀ i < N, extOf (p i (2 * K)) = entOf (p (i + 1) 0)
  /-- Every window satisfies the window condition. -/
  wcond : ∀ i ≤ N, ∀ r < 2 * K + 1, TwoWay.seg w (a i r) (b i r) ∈ WinCond M (K - 1) (p i r)

namespace ChainData

variable {M : TwoWay A B Q} {K : ℕ} {w : List A} (d : ChainData M K w)

lemma Y_le {m n : ℕ} (h : m ≤ n) : d.Y m ≤ d.Y n := snakeY_chain d.Y_mono m n h

lemma Y_le_length (i : ℕ) (hi : i ≤ d.N + 2) : d.Y i ≤ w.length := by
  rw [← d.Y_last]; exact d.Y_le hi

lemma b_le_length {i r : ℕ} (hi : i ≤ d.N) (hr : r < 2 * K + 1) : d.b i r ≤ w.length :=
  le_trans (d.win i hi r hr).2.2 (d.Y_le_length (i + 2) (by omega))

include d in
lemma Y_zero : d.Y 0 = 0 := by
  have h := d.Y_le (show (0 : ℕ) ≤ 1 from Nat.zero_le 1)
  have h1 := d.Y_one
  omega

include d in
lemma length_pos : 0 < w.length := by
  have h1 : d.Y 0 < d.Y 2 := d.Y_lt 0 (Nat.zero_le _)
  have h2 := d.Y_le_length 2 (by omega)
  omega

end ChainData

/-! ## The output of the run is the concatenation of the outputs of the chain -/

section Chain

variable {M : TwoWay A B Q} {K : ℕ} {w : List A} (d : ChainData M K w)

open Classical in
/-- The entry state of the `r`-th piece of the pair `i`. -/
noncomputable def entSt (M : TwoWay A B Q) (p : PieceParam A Q) : Q :=
  (entOf p).getD M.init

lemma entSt_eq {p : PieceParam A Q} {q f : Q} (h : stOf p = some (q, f)) :
    entSt M p = q := by
  have h' : p.2.2.2 = some (q, f) := h
  rw [entSt, entOf, h']; rfl

lemma extOf_eq {p : PieceParam A Q} {q f : Q} (h : stOf p = some (q, f)) :
    extOf p = some f := by
  have h' : p.2.2.2 = some (q, f) := h
  rw [extOf, h']; rfl

lemma entOf_eq {p : PieceParam A Q} {q f : Q} (h : stOf p = some (q, f)) :
    entOf p = some q := by
  have h' : p.2.2.2 = some (q, f) := h
  rw [entOf, h']; rfl

/-- **The output of the run is the concatenation of the outputs of the pieces of
a chain.** -/
theorem runOut_of_chainData :
    runOut M w = (List.range (d.N + 1)).flatMap (fun i =>
      (List.range (2 * K + 1)).flatMap (fun r =>
        pieceOut M (K - 1) (d.p i r) (TwoWay.seg w (d.a i r) (d.b i r)))) := by
  classical
  set R := 2 * K + 1 with hR
  have hRpos : 0 < R := by omega
  rw [flatMap_range_mul _ R hRpos]
  set g : ℕ → List B := fun j =>
    pieceOut M (K - 1) (d.p (j / R) (j % R))
      (TwoWay.seg w (d.a (j / R) (j % R)) (d.b (j / R) (j % R))) with hg
  set c : ℕ → ℕ := fun j =>
    stCut (d.p (j / R) (j % R)) (d.a (j / R) (j % R)) (d.b (j / R) (j % R)) with hc
  set stf : ℕ → Q := fun j => entSt M (d.p (j / R) (j % R)) with hstf
  have hidx : ∀ i r : ℕ, r < R → (i * R + r) / R = i ∧ (i * R + r) % R = r := by
    intro i r hr
    constructor
    · rw [Nat.mul_comm, Nat.mul_add_div hRpos, Nat.div_eq_of_lt hr, Nat.add_zero]
    · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hsplit : ∀ j : ℕ, j = (j / R) * R + j % R := by
    intro j; rw [Nat.div_add_mod']
  have hexp : (d.N + 1) * R = d.N * R + R := by ring
  refine runOut_of_chain_halt M w ((d.N + 1) * R) (d.N * R + 2 * K) (by omega) g c stf ?_ ?_
    (by intro j h1 h2; exfalso; omega) ?_
  · -- the first cut is the left end of the input
    have h0 : (0 : ℕ) / R = 0 := Nat.zero_div _
    have h1 : (0 : ℕ) % R = 0 := Nat.zero_mod _
    rw [hc]
    simp only [h0, h1]
    rw [d.cut_zero 0 (Nat.zero_le _), d.Y_one]
  · -- the first piece starts in the initial state
    have h0 : (0 : ℕ) / R = 0 := Nat.zero_div _
    have h1 : (0 : ℕ) % R = 0 := Nat.zero_mod _
    rw [hstf]
    simp only [h0, h1]
    rw [entSt, d.ent_zero]
    rfl
  · -- the chain step
    intro j hj t ht
    set i := j / R with hi
    set r := j % R with hr
    have hrR : r < R := Nat.mod_lt _ hRpos
    have hjeq : j = i * R + r := hsplit j
    have hiN : i ≤ d.N := by
      by_contra hcon
      push_neg at hcon
      have hmul : (d.N + 1) * R ≤ i * R := Nat.mul_le_mul_right R hcon
      omega
    obtain ⟨q, f, hst⟩ := d.st i hiN r (by omega)
    obtain ⟨hwa, hab, hbY⟩ := d.win i hiN r (by omega)
    have hyw : d.b i r ≤ w.length := d.b_le_length hiN (by omega)
    have hstq : stf j = q := entSt_eq hst
    have hlastF : j = d.N * R + 2 * K → i = d.N ∧ r = 2 * K := by
      intro h
      have h1 : (d.N * R + 2 * K) / R = d.N := (hidx d.N (2 * K) (by omega)).1
      have h2 : (d.N * R + 2 * K) % R = 2 * K := (hidx d.N (2 * K) (by omega)).2
      exact ⟨by rw [hi, h, h1], by rw [hr, h, h2]⟩
    have hlastB : i = d.N → r = 2 * K → j = d.N * R + 2 * K := by
      intro h1 h2; rw [hjeq, h1, h2]
    by_cases hlastj : j = d.N * R + 2 * K
    · -- the last piece halts
      obtain ⟨hiN', hr'⟩ := hlastF hlastj
      have hkd : kdOf (d.p i r) = 3 ∨ kdOf (d.p i r) = 4 := by
        rw [hiN', hr']; exact d.kind_last
      have hqf : q = f := by
        have h1 := d.st_last
        rw [← hiN', ← hr', entOf_eq hst, extOf_eq hst] at h1
        exact Option.some_injective _ h1
      have hstart : cfgAt M w t = some (Cfg.conf (w.take (if (d.p i r).1 = 3 then d.a i r
          else d.b i r)) q (w.drop (if (d.p i r).1 = 3 then d.a i r else d.b i r))) := by
        rw [← hstq]
        convert ht using 3 <;>
          · rw [hc]
            simp only [← hi, ← hr, stCut, kdOf]
            rcases hkd with h | h <;> rw [kdOf] at h <;> rw [h] <;> simp
      have hst' : (d.p i r).2.2.2 = some (q, q) := by
        have h' : (d.p i r).2.2.2 = some (q, f) := hst
        rw [h', hqf]
      obtain ⟨n, hhalt, hout⟩ := chain_step_halt M w hab hst'
        (d.ctxL i hiN r (by omega)) (d.ctxR i hiN r (by omega)) hkd hstart
        (d.wcond i hiN r (by omega))
      exact ⟨n, hout, by rw [if_pos hlastj]; exact hhalt⟩
    · -- a piece that crosses its window
      have hkd : kdOf (d.p i r) = 1 ∨ kdOf (d.p i r) = 2 := by
        rcases Nat.lt_or_ge r (2 * K) with h | h
        · exact d.kind i hiN r h
        · have hr2 : r = 2 * K := by omega
          have hiN2 : i < d.N := by
            rcases Nat.lt_or_ge i d.N with h' | h'
            · exact h'
            · exact absurd (hlastB (by omega) hr2) hlastj
          rw [hr2]; exact d.kind_mid i hiN2
      have hstart : cfgAt M w t = some (Cfg.conf (w.take (if (d.p i r).1 = 1 then d.a i r
          else d.b i r)) q (w.drop (if (d.p i r).1 = 1 then d.a i r else d.b i r))) := by
        rw [← hstq]
        convert ht using 3 <;>
          · rw [hc]
            simp only [← hi, ← hr, stCut, kdOf]
            rcases hkd with h | h <;> rw [kdOf] at h <;> rw [h] <;> simp
      obtain ⟨n, hnext, hout⟩ := chain_step_adv M w hab hst
        (d.ctxL i hiN r (by omega)) (d.ctxR i hiN r (by omega)) hkd hstart
        (d.wcond i hiN r (by omega))
      refine ⟨n, hout, ?_⟩
      rw [if_neg hlastj]
      -- the end cut of the piece is the start cut of the next one
      have hencut : (if (d.p i r).1 = 1 then d.b i r else d.a i r)
          = enCut (d.p i r) (d.a i r) (d.b i r) := by
        rw [enCut, kdOf]
      rw [hencut] at hnext
      have hnextidx : c (j + 1) = enCut (d.p i r) (d.a i r) (d.b i r) ∧
          stf (j + 1) = f := by
        rcases Nat.lt_or_ge (r + 1) R with hrl | hrg
        · -- the next piece is in the same pair
          have hd : (j + 1) / R = i ∧ (j + 1) % R = r + 1 := by
            rw [show j + 1 = i * R + (r + 1) by omega]
            exact hidx i (r + 1) hrl
          constructor
          · rw [hc]
            simp only [hd.1, hd.2]
            exact (d.cut_step i hiN r (by omega)).symm
          · have hh := d.ext_step i hiN r (by omega)
            rw [extOf_eq hst] at hh
            rw [hstf]
            simp only [hd.1, hd.2]
            rw [entSt, ← hh]
            rfl
        · -- the next piece is the first one of the next pair
          have hr2 : r = 2 * K := by omega
          have hiN2 : i < d.N := by
            rcases Nat.lt_or_ge i d.N with h' | h'
            · exact h'
            · exact absurd (hlastB (by omega) hr2) hlastj
          have hd : (j + 1) / R = i + 1 ∧ (j + 1) % R = 0 := by
            rw [show j + 1 = (i + 1) * R + 0 by rw [Nat.add_mul]; omega]
            exact hidx (i + 1) 0 hRpos
          constructor
          · rw [hc]
            simp only [hd.1, hd.2]
            rw [d.cut_zero (i + 1) (by omega), hr2]
            exact (d.cut_last i hiN2).symm
          · have hh := d.ext_pair i hiN2
            rw [← hr2] at hh
            rw [extOf_eq hst] at hh
            rw [hstf]
            simp only [hd.1, hd.2]
            rw [entSt, ← hh]
            rfl
      rw [hnextidx.1, hnextidx.2]
      exact hnext

end Chain

end Chk

end TwoWay

end Lax916827Proofs.Transducers
