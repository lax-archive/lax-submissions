/-
**The data of the marking of stage 1 exists**: for every halting run of width at
most `K` on a nonempty input there is a correct marking
(`TwoWay.IsSnakeMarking`) of that input.

This is the mathematical half of the book's first stage in the proof of the
snake lemma.  The blocks are cut at the record-breaking columns
(`TwoWay.snakeY`), and inside every pair of neighbouring blocks the `2K+1` piece
slots are filled with the windows and the window transducers supplied by the
identification theorems of `RequestProject/PartC/SnakePieceIdent.lean` and
`RequestProject/PartC/SnakeFinalConf.lean`.  What has to be checked, and is
checked here, is that every one of those windows is contained in the pair of
blocks that carries it; this is the confinement of the pieces of the
record-breaker decomposition (`RequestProject/PartC/SnakeConfine.lean`), which
enters through the identification of the window of an excursion as the interval
between the record-breaking column and the column furthest away from it that the
excursion reaches.

What is *not* proved here -- and is the one remaining gap of Theorem
`thm:2dfa-decomposition-into-primes`, see `RequestProject/PartC/SnakeStage1.lean` -- is that a
marking can be chosen by a *regular function* of the input. -/
import Lax916827Proofs.Source.PartC.SnakeAssemble
import Lax916827Proofs.Source.PartC.SnakeFinalConf
import Lax916827Proofs.Source.PartC.SnakeConfine
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ## Reading a piece off its parameters -/

section Kinds

variable (M : TwoWay A B Q) (k : ℕ) (l rr : Option A) (q f : Q) (v : List A)

@[simp] lemma pieceOut_kind_one :
    pieceOut M k ((1 : Fin 5), l, rr, some (q, f)) v = widthOut (stopRight M l rr q f) k v := by
  simp [pieceOut]

@[simp] lemma pieceOut_kind_two :
    pieceOut M k ((2 : Fin 5), l, rr, some (q, f)) v
      = widthOut (stopRight (mirror M) rr l q f) k v.reverse := by
  simp [pieceOut]

@[simp] lemma pieceOut_kind_three :
    pieceOut M k ((3 : Fin 5), l, rr, some (q, f)) v
      = widthOut (M.withContext l rr q) k v := by
  simp [pieceOut]

@[simp] lemma pieceOut_kind_four :
    pieceOut M k ((4 : Fin 5), l, rr, some (q, f)) v
      = widthOut ((mirror M).withContext rr l q) k v.reverse := by
  simp [pieceOut]

end Kinds

/-! ## The cutting points of the input into blocks -/

variable (M : TwoWay A B Q) (w : List A)

/-- The cutting points of the input into the blocks of the record-breaker
decomposition: the `m`-th block consists of the positions `snakeY m ≤ j <
snakeY (m+1)`.  The `0`-th block is empty, the block `m+1` starts at the `m`-th
record-breaking column for `m ≤ N`, and the last block ends at the end of the
input. -/
noncomputable def snakeY (m : ℕ) : ℕ :=
  if m = 0 then 0 else if m ≤ rbN M w + 1 then rbCol M w (m - 1) else w.length

variable {M w}

@[simp] lemma snakeY_zero : snakeY M w 0 = 0 := by rw [snakeY, if_pos rfl]

lemma snakeY_succ_of_le {m : ℕ} (h : m ≤ rbN M w) : snakeY M w (m + 1) = rbCol M w m := by
  rw [snakeY, if_neg (Nat.succ_ne_zero m), if_pos (by omega)]
  simp

lemma snakeY_of_gt {m : ℕ} (h : rbN M w + 1 < m) : snakeY M w m = w.length := by
  rw [snakeY, if_neg (by omega), if_neg (by omega)]

/-! ## Elementary facts about the record-breaking columns -/

@[simp] lemma rbCol_zero : rbCol M w 0 = 0 := by
  rw [rbCol, Walk.recSeq_zero, traj_zero]

lemma rbCol_mono {i j : ℕ} (h : i ≤ j) : rbCol M w i ≤ rbCol M w j := Walk.recSeq_mono h

lemma rbCol_lt_succ {i : ℕ} (h : i < rbN M w) : rbCol M w i < rbCol M w (i + 1) :=
  Walk.lt_recSeq_succ (Walk.not_recStable_of_lt_recN h)

variable {T K : ℕ}

lemma traj_le_length (hT : cfgAt M w T = some Cfg.halt) {t : ℕ} (ht : t ≤ endT M w) :
    traj M w t ≤ w.length :=
  posAt_le_length M w (posAt_traj hT ht)

lemma rbCol_le_length (hT : cfgAt M w T = some Cfg.halt) (i : ℕ) : rbCol M w i ≤ w.length := by
  have h := traj_le_length hT (rbLast_le_endT (M := M) (w := w) i)
  rwa [pos_rbLast] at h

/-! ## The blocks tile the input -/

lemma snakeY_mono_step (hT : cfgAt M w T = some Cfg.halt) (m : ℕ) :
    snakeY M w m ≤ snakeY M w (m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    by_cases h : n + 1 ≤ rbN M w
    · rw [snakeY_succ_of_le (by omega), snakeY_succ_of_le h]
      exact rbCol_mono (by omega)
    · by_cases h' : n ≤ rbN M w
      · rw [snakeY_succ_of_le h', snakeY_of_gt (by omega)]
        exact rbCol_le_length hT n
      · rw [snakeY_of_gt (by omega), snakeY_of_gt (by omega)]

lemma snakeY_mono (hT : cfgAt M w T = some Cfg.halt) {m n : ℕ} (h : m ≤ n) :
    snakeY M w m ≤ snakeY M w n := by
  induction n with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h1 | h1
      · exact le_trans (ih (by omega)) (snakeY_mono_step hT n)
      · have : m = n + 1 := by omega
        rw [this]

lemma snakeY_last : snakeY M w (rbN M w + 2) = w.length := snakeY_of_gt (by omega)

lemma snakeY_lt_two (hT : cfgAt M w T = some Cfg.halt) (hw : w ≠ []) {i : ℕ}
    (hi : i ≤ rbN M w) : snakeY M w i < snakeY M w (i + 2) := by
  have hwlen : 0 < w.length := List.length_pos_iff.2 hw
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rcases Nat.eq_zero_or_pos (rbN M w) with h0 | h0
    · rw [snakeY_zero, snakeY_of_gt (by omega)]
      exact hwlen
    · rw [snakeY_zero, show (0 : ℕ) + 2 = 1 + 1 from rfl, snakeY_succ_of_le (by omega)]
      have := rbCol_lt_succ (M := M) (w := w) (i := 0) (by omega)
      simpa using this
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [snakeY_succ_of_le (by omega : n ≤ rbN M w)]
    by_cases h : n + 2 ≤ rbN M w
    · rw [show n + 1 + 2 = (n + 2) + 1 from rfl, snakeY_succ_of_le h]
      calc rbCol M w n ≤ rbCol M w (n + 1) := rbCol_mono (by omega)
        _ < rbCol M w (n + 2) := rbCol_lt_succ (by omega)
    · rw [snakeY_of_gt (by omega)]
      calc rbCol M w n < rbCol M w (n + 1) := rbCol_lt_succ (by omega)
        _ ≤ w.length := rbCol_le_length hT (n + 1)

/-! ## The pieces are confined to two neighbouring blocks -/

lemma snakeY_le_rbCol {i : ℕ} (hi : i ≤ rbN M w) : snakeY M w i ≤ rbCol M w i := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [snakeY_succ_of_le (by omega : n ≤ rbN M w)]
    exact rbCol_mono (by omega)

lemma rbCol_le_snakeY_two (hT : cfgAt M w T = some Cfg.halt) {i : ℕ} (hi : i ≤ rbN M w) :
    rbCol M w i ≤ snakeY M w (i + 2) := by
  by_cases h : i + 1 ≤ rbN M w
  · rw [show i + 2 = (i + 1) + 1 from rfl, snakeY_succ_of_le h]
    exact rbCol_mono (by omega)
  · rw [snakeY_of_gt (by omega)]
    exact rbCol_le_length hT i

/-- After the last visit to the previous record-breaking column the run stays to
the right of the left end of the pair of blocks of the `i`-th one. -/
lemma snakeY_le_traj (hT : cfgAt M w T = some Cfg.halt) {i : ℕ} (hi : i ≤ rbN M w)
    {t : ℕ} (h1 : rbFirst M w i ≤ t) (h2 : t ≤ endT M w) :
    snakeY M w i ≤ traj M w t := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have hnN : n < rbN M w := by omega
    have hns : ¬ Walk.RecStable (traj M w) 0 (endT M w) n :=
      Walk.not_recStable_of_lt_recN hnN
    have hlt : Walk.recLast (traj M w) 0 (endT M w) n < t :=
      lt_of_lt_of_le (Walk.recLast_lt_recFirst_succ hns) h1
    have := Walk.recSeq_lt_of_recLast_lt (isWalk_trajE M w hT) (Nat.zero_le _) (le_refl _)
      hns hlt h2
    rw [snakeY_succ_of_le (by omega : n ≤ rbN M w)]
    exact le_of_lt this

/-- The loop part of the `i`-th record-breaking column stays to the left of the
right end of its pair of blocks. -/
lemma traj_le_snakeY_two (hT : cfgAt M w T = some Cfg.halt) {i : ℕ} (hi : i ≤ rbN M w)
    {t : ℕ} (h2 : t ≤ rbLast M w i) : traj M w t ≤ snakeY M w (i + 2) := by
  by_cases h : i < rbN M w
  · have hns : ¬ Walk.RecStable (traj M w) 0 (endT M w) i :=
      Walk.not_recStable_of_lt_recN h
    have := Walk.lt_recSeq_succ_of_le_recLast (isWalk_trajE M w hT) (Nat.zero_le _)
      (le_refl _) hns (Nat.zero_le t) h2
    rw [show i + 2 = (i + 1) + 1 from rfl, snakeY_succ_of_le (by omega)]
    exact le_of_lt this
  · rw [snakeY_of_gt (by omega)]
    exact traj_le_length hT (le_trans h2 (rbLast_le_endT i))

/-! ## The data of the pieces -/

lemma seg_to_length (v : List A) (x : ℕ) : seg v x v.length = v.drop x := by
  rw [seg]
  exact List.take_of_length_le (by simp)

lemma rbFirst_le_excT (i j : ℕ) : rbFirst M w i ≤ excT M w i j := by
  have := Walk.visSeq_mono (p := traj M w) (c := rbCol M w i) (b0 := rbLast M w i)
    (a0 := rbFirst M w i) (rbFirst_le_rbLast i) (Nat.zero_le j)
  simpa [excT] using this

/-- **The data of one piece of the record-breaker decomposition**: a window
contained in the pair of blocks of the piece, and the parameters of a window
transducer computing the piece on that window. -/
lemma exists_pieceData (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K) (hK : 2 ≤ K)
    (i r : ℕ) :
    ∃ (aa bb : ℕ) (pp : PieceParam A Q), i ≤ rbN M w →
      snakeY M w i ≤ aa ∧ aa ≤ bb ∧ bb ≤ snakeY M w (i + 2) ∧
        pieceOut M (K - 1) pp (seg w aa bb) = pieceOutput M w K i r := by
  classical
  by_cases hi : i ≤ rbN M w
  swap
  · exact ⟨0, 0, default, fun h => absurd h hi⟩
  by_cases hr : r = 2 * K
  · subst hr
    by_cases hiN : i < rbN M w
    · -- the progress part of a record-breaking column which is not the last one
      obtain ⟨q₀, fin, h⟩ := exists_widthOut_prog hT hwidth hK hiN
      refine ⟨rbCol M w i, rbCol M w (i + 1),
        ((1 : Fin 5), (w.take (rbCol M w i)).getLast?,
          (w.drop (rbCol M w (i + 1))).head?, some (q₀, fin)), fun _ => ?_⟩
      refine ⟨snakeY_le_rbCol hi, rbCol_mono (by omega), ?_, ?_⟩
      · rw [show i + 2 = (i + 1) + 1 from rfl, snakeY_succ_of_le (by omega)]
      · rw [pieceOut_kind_one, pieceOutput, if_pos rfl, progEnd, if_pos hiN, h]
    · -- the final progress part
      have hiN' : i = rbN M w := by omega
      subst hiN'
      have hx : snakeY M w (rbN M w) ≤ rbCol M w (rbN M w) := snakeY_le_rbCol hi
      have hlow : ∀ t, rbLast M w (rbN M w) ≤ t → t ≤ endT M w →
          snakeY M w (rbN M w) ≤ traj M w t := by
        intro t h1 h2
        exact snakeY_le_traj hT hi (le_trans (rbFirst_le_rbLast (rbN M w)) h1) h2
      obtain ⟨q₀, hor⟩ := exists_widthOut_finalProg_confined hT hwidth hK hx hlow
      rcases hor with h | h
      · refine ⟨rbCol M w (rbN M w), w.length,
          ((3 : Fin 5), (w.take (rbCol M w (rbN M w))).getLast?, none, some (q₀, q₀)),
          fun _ => ?_⟩
        refine ⟨hx, rbCol_le_length hT (rbN M w), ?_, ?_⟩
        · rw [snakeY_of_gt (by omega)]
        · rw [pieceOut_kind_three, seg_to_length, pieceOutput, if_pos rfl, progEnd,
            if_neg (by omega), h]
      · refine ⟨snakeY M w (rbN M w), rbCol M w (rbN M w),
          ((4 : Fin 5), (w.take (snakeY M w (rbN M w))).getLast?,
            (w.drop (rbCol M w (rbN M w))).head?, some (q₀, q₀)), fun _ => ?_⟩
        refine ⟨le_refl _, hx, rbCol_le_snakeY_two hT hi, ?_⟩
        rw [pieceOut_kind_four, pieceOutput, if_pos rfl, progEnd, if_neg (by omega), h]
  · -- one of the two halves of an excursion
    obtain ⟨x, y, hxdef, hydef, hxy, hyw, q₁, f₁, q₂, f₂, hor⟩ :=
      exists_widthOut_excHalves hT hwidth hK i (r / 2)
    -- the window of the excursion is confined to the pair of blocks
    have hsplit : traj M w (excS M w i (r / 2)) = excC M w i (r / 2) :=
      Walk.pos_excSplit (excT_mono_step i (r / 2))
    have hs1 : rbFirst M w i ≤ excS M w i (r / 2) :=
      le_trans (rbFirst_le_excT i (r / 2)) (excS_bounds i (r / 2)).1
    have hs2 : excS M w i (r / 2) ≤ rbLast M w i :=
      le_trans (excS_bounds i (r / 2)).2 (excT_le i (r / 2 + 1))
    have hlow : snakeY M w i ≤ excC M w i (r / 2) := by
      rw [← hsplit]
      exact snakeY_le_traj hT hi hs1 (le_trans hs2 (rbLast_le_endT i))
    have hhigh : excC M w i (r / 2) ≤ snakeY M w (i + 2) := by
      rw [← hsplit]
      exact traj_le_snakeY_two hT hi hs2
    have hlow' : snakeY M w i ≤ rbCol M w i := snakeY_le_rbCol hi
    have hhigh' : rbCol M w i ≤ snakeY M w (i + 2) := rbCol_le_snakeY_two hT hi
    have hbx : snakeY M w i ≤ x := by omega
    have hby : y ≤ snakeY M w (i + 2) := by omega
    by_cases hpar : r % 2 = 0
    · -- the first half
      have hout : pieceOutput M w K i r = outRange M w (excT M w i (r / 2)) (excS M w i (r / 2)) :=
        by rw [pieceOutput, if_neg hr, if_pos hpar]
      rcases hor with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨x, y, ((1 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q₁, f₁)),
          fun _ => ⟨hbx, hxy, hby, by rw [pieceOut_kind_one, hout, h1]⟩⟩
      · exact ⟨x, y, ((2 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q₁, f₁)),
          fun _ => ⟨hbx, hxy, hby, by rw [pieceOut_kind_two, hout, h1]⟩⟩
    · -- the second half
      have hout : pieceOutput M w K i r
          = outRange M w (excS M w i (r / 2)) (excT M w i (r / 2 + 1)) := by
        rw [pieceOutput, if_neg hr, if_neg hpar]
      rcases hor with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact ⟨x, y, ((2 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q₂, f₂)),
          fun _ => ⟨hbx, hxy, hby, by rw [pieceOut_kind_two, hout, h2]⟩⟩
      · exact ⟨x, y, ((1 : Fin 5), (w.take x).getLast?, (w.drop y).head?, some (q₂, f₂)),
          fun _ => ⟨hbx, hxy, hby, by rw [pieceOut_kind_one, hout, h2]⟩⟩

/-- **A correct marking of the input exists**, for every nonempty input whose
run halts and has width at most `K`.  This is the mathematical content of the
book's first stage in the proof of the snake lemma; what stage 1 adds to it is
that the marking can be chosen by a regular function of the input
(`TwoWay.exists_snakeMarking`). -/
theorem exists_isSnakeMarking (hw : w ≠ []) (hK : 2 ≤ K)
    (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K) :
    ∃ (a b : ℕ → ℕ → ℕ) (p : ℕ → ℕ → PieceParam A Q),
      IsSnakeMarking M K w (snakeAnn w K (rbN M w) (snakeY M w) a b p) := by
  classical
  choose a b p hdata using fun i r => exists_pieceData hT hwidth hK i r
  exact ⟨a, b, p, isSnakeMarking_snakeAnn M K w rfl (snakeY M w) a b p
    (snakeY_mono_step hT) snakeY_last (fun i hiN => snakeY_lt_two hT hw hiN)
    (fun i hiN r _ => ⟨(hdata i r hiN).1, (hdata i r hiN).2.1, (hdata i r hiN).2.2.1⟩)
    (fun i hiN r _ => (hdata i r hiN).2.2.2)⟩

end TwoWay

end Lax916827Proofs.Transducers
