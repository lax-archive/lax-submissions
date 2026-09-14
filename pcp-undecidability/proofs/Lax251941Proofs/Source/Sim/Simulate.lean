/-
# Simulating a counter machine by a tape machine

Each instruction of the program is simulated by a *leg* of the tape machine's run, from
the home square back to the home square.  This file proves the four cases (increment,
decrement of a zero register, decrement of a positive register, jump) and assembles them
into the equivalence between the halting of the program and the acceptance of the machine.
-/
import Lax251941Proofs.Source.Sim.Tape
import Lax251941Proofs.Source.Sim.Impl

namespace Lax251941Proofs.PCP
namespace Sim

variable {P : Prog} {N : ℕ}

/-! ## Generalities -/

lemma prog_lt {p : ℕ} {ins : Instr} (hp : P[p]? = some ins) : p < P.length := by
  by_contra h
  rw [List.getElem?_eq_none (by omega)] at hp
  exact absurd hp (by simp)

lemma stHome_ne {p : ℕ} (h : p < P.length) : stHome p ≠ stHome P.length := by
  unfold stHome; omega
lemma stBack_ne {p : ℕ} : stBack p ≠ stHome P.length := by
  unfold stBack stHome; omega
lemma stBounce_ne {p : ℕ} : stBounce p ≠ stHome P.length := by
  unfold stBounce stHome; omega
lemma stSinc_ne {p : ℕ} : stSinc p ≠ stHome P.length := by
  unfold stSinc stHome; omega
lemma stTdec_ne {p : ℕ} : stTdec p ≠ stHome P.length := by
  unfold stTdec stHome; omega
lemma stSdec_ne {p : ℕ} : stSdec p ≠ stHome P.length := by
  unfold stSdec stHome; omega
lemma stCdec_ne {p : ℕ} : stCdec p ≠ stHome P.length := by
  unfold stCdec stHome; omega
lemma stJmp_ne {p : ℕ} : stJmp p ≠ stHome P.length := by
  unfold stJmp stHome; omega

/-- The configuration with the head on the home square, the tape holding `m` cells. -/
noncomputable def homeCfg (N : ℕ) (q : ℕ) (s : Regs) (m : ℕ) : Cfg :=
  ⟨[], q, mark N :: cellsFrom N s 0 m⟩

/-! ## Cells and register updates -/

lemma cellAt_update (N : ℕ) (s : Regs) (r v j : ℕ) :
    cellAt N (Function.update s r v) j
      = fun i : Fin N => if (i : ℕ) = r then decide (j ≤ v) else decide (j ≤ s i) := by
  funext i
  by_cases hi : (i : ℕ) = r <;> simp [cellAt, Function.update_apply, hi]

lemma cellAt_update_eq {N : ℕ} {s : Regs} {r v j : ℕ} (h : (j ≤ v) ↔ (j ≤ s r)) :
    cellAt N (Function.update s r v) j = cellAt N s j := by
  rw [cellAt_update]
  funext i
  by_cases hi : (i : ℕ) = r
  · simp only [hi, cellAt]
    simp [h]
  · simp [hi, cellAt]

lemma cellAt_update_set {N : ℕ} {s : Regs} {r v j : ℕ} (h : j ≤ v) :
    cellAt N (Function.update s r v) j = setBit (cellAt N s j) r := by
  rw [cellAt_update]
  funext i
  by_cases hi : (i : ℕ) = r <;> simp [hi, setBit, cellAt, h]

lemma cellAt_update_clr {N : ℕ} {s : Regs} {r v j : ℕ} (h : ¬ j ≤ v) :
    cellAt N (Function.update s r v) j = clrBit (cellAt N s j) r := by
  rw [cellAt_update]
  funext i
  by_cases hi : (i : ℕ) = r <;> simp [hi, clrBit, cellAt, h]

lemma mem_cellsFrom_iff {N : ℕ} {s : Regs} {a d : ℕ} :
    ∀ b ∈ cellsFrom N s a d, ∃ j, a < j ∧ j ≤ a + d ∧ b = cellCode (cellAt N s j) := by
  induction d generalizing a with
  | zero => simp
  | succ d ih =>
    intro b hb
    rw [cellsFrom_succ, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨a + 1, by omega, by omega, rfl⟩
    · obtain ⟨j, h1, h2, h3⟩ := ih b hb
      exact ⟨j, by omega, by omega, h3⟩

/-! ## Returning to the home square -/

/-- A single step to the left from the square next to the home square. -/
lemma bounce_home {q q' : ℕ} (hq : q ≠ stHome P.length) {R : List ℕ}
    (htr : (q, R.headI, q', R.headI, false) ∈ (tmOf P N).trans) :
    Leg P N ⟨[mark N], q, R⟩ ⟨[], q', mark N :: R.headI :: R.tail⟩ := by
  refine leg_step ?_ hq
  have hE : entry (tmOf P N) (Cfg.mk [mark N] q R).st (Cfg.mk [mark N] q R).right.headI
      = some (q', R.headI, false) := (entry_eq_some_iff (det_tmOf P N)).mpr htr
  rw [dstep_left hE (rfl : (Cfg.mk [mark N] q R).left = mark N :: [])]

/-- From the home square, in the state `stBack p`, to the home square in the state of the
next instruction. -/
lemma back_at_home {p : ℕ} {ins : Instr} (hp : P[p]? = some ins) {X : List ℕ}
    (hX : ∀ a ∈ X, IsCell N a) (hXne : X ≠ []) :
    Leg P N ⟨[], stBack p, mark N :: X⟩
      ⟨[], stHome (min (p + 1) P.length), mark N :: X⟩ := by
  have hplt := prog_lt hp
  refine leg_trans (c' := ⟨[mark N], stBounce p, X⟩) (leg_step ?_ (stBack_ne)) ?_
  · exact dstep_move_right (det_tmOf P N) (trans_back_mark hp)
  · obtain ⟨x, hx⟩ := isCell_headI hX
    have htr : (stBounce p, X.headI, stHome (min (p + 1) P.length), X.headI, false)
        ∈ (tmOf P N).trans := by rw [hx]; exact trans_bounce hp x
    have := bounce_home (P := P) (N := N) (stBounce_ne) htr
    rwa [list_headI_tail hXne] at this

/-- Writing a symbol, stepping left, and returning to the home square. -/
lemma write_left_and_home {p : ℕ} {ins : Instr} (hp : P[p]? = some ins)
    {q : ℕ} (hq : q ≠ stHome P.length) {LL R : List ℕ} {b : ℕ}
    (hLL : ∀ a ∈ LL, IsCell N a) (hR : ∀ a ∈ R, IsCell N a) (hb : IsCell N b)
    (htr : (q, R.headI, stBack p, b, false) ∈ (tmOf P N).trans) :
    Leg P N ⟨LL ++ [mark N], q, R⟩
      ⟨[], stHome (min (p + 1) P.length), mark N :: (LL.reverse ++ b :: R.tail)⟩ := by
  have hplt := prog_lt hp
  have hEnt : entry (tmOf P N) q R.headI = some (stBack p, b, false) :=
    (entry_eq_some_iff (det_tmOf P N)).mpr htr
  cases LL with
  | nil =>
    have hstep : dstep (tmOf P N) ⟨[] ++ [mark N], q, R⟩
        = ⟨[], stBack p, mark N :: b :: R.tail⟩ := by
      have hE : entry (tmOf P N) (Cfg.mk ([] ++ [mark N]) q R).st
          (Cfg.mk ([] ++ [mark N]) q R).right.headI = some (stBack p, b, false) := hEnt
      rw [dstep_left hE (rfl : (Cfg.mk ([] ++ [mark N]) q R).left = mark N :: [])]
      try rfl
    refine leg_trans (leg_step hstep hq) ?_
    have := back_at_home (N := N) hp (X := b :: R.tail) ?_ (by simp)
    · simpa using this
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hb
      · exact isCell_tail hR a ha
  | cons y LL' =>
    have hy : IsCell N y := hLL y (by simp)
    have hLL' : ∀ a ∈ LL', IsCell N a := fun a ha => hLL a (by simp [ha])
    have hstep : dstep (tmOf P N) ⟨(y :: LL') ++ [mark N], q, R⟩
        = ⟨LL' ++ [mark N], stBack p, y :: b :: R.tail⟩ := by
      have hE : entry (tmOf P N) (Cfg.mk ((y :: LL') ++ [mark N]) q R).st
          (Cfg.mk ((y :: LL') ++ [mark N]) q R).right.headI = some (stBack p, b, false) := hEnt
      rw [dstep_left hE (rfl : (Cfg.mk ((y :: LL') ++ [mark N]) q R).left
        = y :: (LL' ++ [mark N]))]
      try rfl
    refine leg_trans (leg_step hstep hq) ?_
    set Z := LL'.reverse ++ y :: b :: R.tail with hZ
    have hZcell : ∀ a ∈ Z, IsCell N a := by
      intro a ha
      rw [hZ, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hLL' a (List.mem_reverse.mp ha)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact hy
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact hb
          · exact isCell_tail hR a ha
    have hwalk : Leg P N ⟨LL' ++ [mark N], stBack p, y :: b :: R.tail⟩ ⟨[mark N], stBack p, Z⟩ := by
      refine leg_walk_left (stBack_ne) (by simp) ?_
      intro a ha
      have : IsCell N a := by
        rcases List.mem_cons.mp ha with rfl | ha
        · simpa using hy
        · exact hLL' a ha
      obtain ⟨x, rfl⟩ := this
      exact trans_back_cell hp x
    refine leg_trans hwalk (leg_trans (c' := ⟨[], stBack p, mark N :: Z.headI :: Z.tail⟩) ?_ ?_)
    · obtain ⟨x, hx⟩ := isCell_headI hZcell
      have htr2 : (stBack p, Z.headI, stBack p, Z.headI, false) ∈ (tmOf P N).trans := by
        rw [hx]; exact trans_back_cell hp x
      exact bounce_home (stBack_ne) htr2
    · have hZne : Z ≠ [] := by
        rw [hZ]; cases LL' <;> simp
      rw [list_headI_tail hZne]
      have := back_at_home (N := N) hp hZcell hZne
      simpa [hZ] using this

/-! ## Nonempty legs -/

/-- A leg of the computation taking at least one step. -/
def Leg1 (P : Prog) (N : ℕ) (c c' : Cfg) : Prop :=
  ∃ T, 0 < T ∧ (dstep (tmOf P N))^[T] c = c' ∧
    ∀ t < T, ((dstep (tmOf P N))^[t] c).st ≠ stHome P.length

lemma leg1_cons {c c1 c' : Cfg} (h : dstep (tmOf P N) c = c1)
    (hst : c.st ≠ stHome P.length) (h2 : Leg P N c1 c') : Leg1 P N c c' := by
  obtain ⟨T, e, n⟩ := h2
  refine ⟨T + 1, by omega, ?_, ?_⟩
  · rw [Function.iterate_succ_apply, h, e]
  · intro t ht
    cases t with
    | zero => simpa using hst
    | succ u =>
      rw [Function.iterate_succ_apply, h]
      exact n u (by omega)

/-! ## The four kinds of leg -/

lemma sim_inc {p r : ℕ} (hp : P[p]? = some (.inc r)) (hr : r < N) (s : Regs) (m : ℕ)
    (hm : ∀ i : Fin N, s i ≤ m) :
    Leg1 P N (homeCfg N (stHome p) s m)
      (homeCfg N (stHome (min (p + 1) P.length)) (Function.update s r (s r + 1))
        (max m (s r + 1))) := by
  have hplt := prog_lt hp
  set k := s r with hk
  have hkm : k ≤ m := hm ⟨r, hr⟩
  set s' := Function.update s r (k + 1) with hs'
  have hsplit : cellsFrom N s 0 m = cellsFrom N s 0 k ++ cellsFrom N s k (m - k) := by
    have h := cellsFrom_add N s 0 k (m - k)
    rw [show k + (m - k) = m by omega, Nat.zero_add] at h
    exact h
  -- the first step
  refine leg1_cons (c1 := ⟨[mark N], stSinc p, cellsFrom N s 0 m⟩) ?_ (stHome_ne hplt) ?_
  · exact dstep_move_right (det_tmOf P N) (trans_inc_start hp)
  -- the walk to the right
  have h2 : Leg P N ⟨[mark N], stSinc p, cellsFrom N s 0 m⟩
      ⟨(cellsFrom N s 0 k).reverse ++ [mark N], stSinc p, cellsFrom N s k (m - k)⟩ := by
    rw [hsplit]
    refine leg_walk_right stSinc_ne ?_
    intro a ha
    obtain ⟨j, hj1, hj2, rfl⟩ := mem_cellsFrom_iff a ha
    refine trans_sinc_move hp ?_
    rw [bitOf_cellAt _ _ hr]
    simp only [decide_eq_true_eq]
    omega
  refine leg_trans h2 ?_
  -- the write and the return
  have hhead : (cellsFrom N s k (m - k)).headI = cellCode (cellAt N s (k + 1)) :=
    headI_cellsFrom (fun i => by have := hm i; omega)
  have hbit : bitOf (cellAt N s (k + 1)) r = false := by
    rw [bitOf_cellAt _ _ hr]
    simp only [decide_eq_false_iff_not]
    omega
  have h3 := write_left_and_home (N := N) hp (q := stSinc p) stSinc_ne
      (LL := (cellsFrom N s 0 k).reverse) (R := cellsFrom N s k (m - k))
      (b := cellCode (setBit (cellAt N s (k + 1)) r))
      (fun a ha => isCell_mem_cellsFrom a (List.mem_reverse.mp ha))
      (fun a ha => isCell_mem_cellsFrom a ha) (isCell_code _)
      (by rw [hhead]; exact trans_sinc_set hp hbit)
  have hcong : ∀ j, k + 1 < j → cellAt N s j = cellAt N s' j := by
    intro j hj
    exact (cellAt_update_eq (by omega)).symm
  have hb : cellCode (setBit (cellAt N s (k + 1)) r) = cellCode (cellAt N s' (k + 1)) := by
    rw [cellAt_update_set (le_refl (k + 1))]
  have hw := cells_write (N := N) (s := s) (s' := s') k (m - k) hcong
  have hpre : cellsFrom N s 0 k = cellsFrom N s' 0 k :=
    cellsFrom_congr 0 k (fun j h1 h2 => (cellAt_update_eq (by omega)).symm)
  have heq : (Cfg.mk [] (stHome (min (p + 1) P.length))
      (mark N :: (((cellsFrom N s 0 k).reverse).reverse ++
        cellCode (setBit (cellAt N s (k + 1)) r) :: (cellsFrom N s k (m - k)).tail)))
      = homeCfg N (stHome (min (p + 1) P.length)) s' (max m (k + 1)) := by
    simp only [homeCfg, List.reverse_reverse, Cfg.mk.injEq, true_and]
    rw [hb, hw, hpre]
    have := cellsFrom_add N s' 0 k (max (m - k) 1)
    rw [Nat.zero_add, show k + max (m - k) 1 = max m (k + 1) by omega] at this
    rw [this]
  rw [← heq]
  exact h3

lemma sim_dec_zero {p r j : ℕ} (hp : P[p]? = some (.dec r j)) (hr : r < N) (s : Regs) (m : ℕ)
    (hm : ∀ i : Fin N, s i ≤ m) (hz : s r = 0) :
    Leg1 P N (homeCfg N (stHome p) s m) (homeCfg N (stHome (min j P.length)) s (max m 1)) := by
  have hplt := prog_lt hp
  refine leg1_cons (c1 := ⟨[mark N], stTdec p, cellsFrom N s 0 m⟩) ?_ (stHome_ne hplt) ?_
  · exact dstep_move_right (det_tmOf P N) (trans_dec_start hp)
  have hhead : (cellsFrom N s 0 m).headI = cellCode (cellAt N s 1) :=
    headI_cellsFrom (fun i => by have := hm i; omega)
  have hbit : bitOf (cellAt N s 1) r = false := by
    rw [bitOf_cellAt _ _ hr]
    simp only [decide_eq_false_iff_not]
    omega
  have h2 := bounce_home (P := P) (N := N) (q := stTdec p) (q' := stHome (min j P.length))
      stTdec_ne (R := cellsFrom N s 0 m) (by rw [hhead]; exact trans_tdec_zero hp hbit)
  have heq : (Cfg.mk [] (stHome (min j P.length))
      (mark N :: (cellsFrom N s 0 m).headI :: (cellsFrom N s 0 m).tail))
      = homeCfg N (stHome (min j P.length)) s (max m 1) := by
    simp only [homeCfg, Cfg.mk.injEq, true_and]
    rw [hhead]
    have := cells_write (N := N) (s := s) (s' := s) 0 m (fun _ _ => rfl)
    rw [Nat.zero_add] at this
    rw [this]
  rw [← heq]
  exact h2

lemma sim_jmp {p j : ℕ} (hp : P[p]? = some (.jmp j)) (s : Regs) (m : ℕ)
    (hm : ∀ i : Fin N, s i ≤ m) :
    Leg1 P N (homeCfg N (stHome p) s m) (homeCfg N (stHome (min j P.length)) s (max m 1)) := by
  have hplt := prog_lt hp
  refine leg1_cons (c1 := ⟨[mark N], stJmp p, cellsFrom N s 0 m⟩) ?_ (stHome_ne hplt) ?_
  · exact dstep_move_right (det_tmOf P N) (trans_jmp_start hp)
  have hhead : (cellsFrom N s 0 m).headI = cellCode (cellAt N s 1) :=
    headI_cellsFrom (fun i => by have := hm i; omega)
  have h2 := bounce_home (P := P) (N := N) (q := stJmp p) (q' := stHome (min j P.length))
      stJmp_ne (R := cellsFrom N s 0 m) (by rw [hhead]; exact trans_jmp_end hp _)
  have heq : (Cfg.mk [] (stHome (min j P.length))
      (mark N :: (cellsFrom N s 0 m).headI :: (cellsFrom N s 0 m).tail))
      = homeCfg N (stHome (min j P.length)) s (max m 1) := by
    simp only [homeCfg, Cfg.mk.injEq, true_and]
    rw [hhead]
    have := cells_write (N := N) (s := s) (s' := s) 0 m (fun _ _ => rfl)
    rw [Nat.zero_add] at this
    rw [this]
  rw [← heq]
  exact h2

lemma sim_dec_pos {p r j : ℕ} (hp : P[p]? = some (.dec r j)) (hr : r < N) (s : Regs) (m : ℕ)
    (hm : ∀ i : Fin N, s i ≤ m) (hz : s r ≠ 0) :
    Leg1 P N (homeCfg N (stHome p) s m)
      (homeCfg N (stHome (min (p + 1) P.length)) (Function.update s r (s r - 1))
        (max m (s r + 1))) := by
  have hplt := prog_lt hp
  set k := s r with hk
  have hk1 : 1 ≤ k := by omega
  have hkm : k ≤ m := hm ⟨r, hr⟩
  set s' := Function.update s r (k - 1) with hs'
  refine leg1_cons (c1 := ⟨[mark N], stTdec p, cellsFrom N s 0 m⟩) ?_ (stHome_ne hplt) ?_
  · exact dstep_move_right (det_tmOf P N) (trans_dec_start hp)
  -- the first cell has the bit set: move on to the search
  have hm1 : cellsFrom N s 0 m = cellCode (cellAt N s 1) :: cellsFrom N s 1 (m - 1) := by
    have h := cellsFrom_succ N s 0 (m - 1)
    rw [show m - 1 + 1 = m by omega] at h
    simpa using h
  have hbit1 : bitOf (cellAt N s 1) r = true := by
    rw [bitOf_cellAt _ _ hr]
    simp only [decide_eq_true_eq]
    omega
  have h2 : Leg P N ⟨[mark N], stTdec p, cellsFrom N s 0 m⟩
      ⟨[cellCode (cellAt N s 1), mark N], stSdec p, cellsFrom N s 1 (m - 1)⟩ := by
    rw [hm1]
    exact leg_step (dstep_move_right (det_tmOf P N) (trans_tdec_pos hp hbit1)) stTdec_ne
  refine leg_trans h2 ?_
  -- the walk to the right
  have hsplit : cellsFrom N s 1 (m - 1) = cellsFrom N s 1 (k - 1) ++ cellsFrom N s k (m - k) := by
    have h := cellsFrom_add N s 1 (k - 1) (m - k)
    rw [show k - 1 + (m - k) = m - 1 by omega, show 1 + (k - 1) = k by omega] at h
    exact h
  have h3 : Leg P N ⟨[cellCode (cellAt N s 1), mark N], stSdec p, cellsFrom N s 1 (m - 1)⟩
      ⟨(cellsFrom N s 1 (k - 1)).reverse ++ [cellCode (cellAt N s 1), mark N], stSdec p,
        cellsFrom N s k (m - k)⟩ := by
    rw [hsplit]
    refine leg_walk_right stSdec_ne ?_
    intro a ha
    obtain ⟨jj, hj1, hj2, rfl⟩ := mem_cellsFrom_iff a ha
    refine trans_sdec_move hp ?_
    rw [bitOf_cellAt _ _ hr]
    simp only [decide_eq_true_eq]
    omega
  refine leg_trans h3 ?_
  -- rewrite the left part of the tape
  have e1 : cellsFrom N s 0 k = cellCode (cellAt N s 1) :: cellsFrom N s 1 (k - 1) := by
    have h := cellsFrom_succ N s 0 (k - 1)
    rw [show k - 1 + 1 = k by omega] at h
    simpa using h
  have e2 : cellsFrom N s 0 k = cellsFrom N s 0 (k - 1) ++ [cellCode (cellAt N s k)] := by
    have h := cellsFrom_snoc N s 0 (k - 1)
    rw [show k - 1 + 1 = k by omega, show 0 + (k - 1) + 1 = k by omega] at h
    exact h
  have hleft : (cellsFrom N s 1 (k - 1)).reverse ++ [cellCode (cellAt N s 1), mark N]
      = cellCode (cellAt N s k) :: ((cellsFrom N s 0 (k - 1)).reverse ++ [mark N]) := by
    have : (cellsFrom N s 1 (k - 1)).reverse ++ [cellCode (cellAt N s 1), mark N]
        = (cellsFrom N s 0 k).reverse ++ [mark N] := by rw [e1]; simp
    rw [this, e2]
    simp
  rw [hleft]
  set R := cellsFrom N s k (m - k) with hR
  have hRcell : ∀ a ∈ R, IsCell N a := fun a ha => isCell_mem_cellsFrom a ha
  have hRhead : R.headI = cellCode (cellAt N s (k + 1)) :=
    headI_cellsFrom (fun i => by have := hm i; omega)
  have hbitk1 : bitOf (cellAt N s (k + 1)) r = false := by
    rw [bitOf_cellAt _ _ hr]
    simp only [decide_eq_false_iff_not]
    omega
  -- step back onto the last set cell
  have hstep4 : dstep (tmOf P N)
      ⟨cellCode (cellAt N s k) :: ((cellsFrom N s 0 (k - 1)).reverse ++ [mark N]), stSdec p, R⟩
      = ⟨(cellsFrom N s 0 (k - 1)).reverse ++ [mark N], stCdec p,
          cellCode (cellAt N s k) :: R.headI :: R.tail⟩ := by
    have hE : entry (tmOf P N)
        (Cfg.mk (cellCode (cellAt N s k) :: ((cellsFrom N s 0 (k - 1)).reverse ++ [mark N]))
          (stSdec p) R).st
        (Cfg.mk (cellCode (cellAt N s k) :: ((cellsFrom N s 0 (k - 1)).reverse ++ [mark N]))
          (stSdec p) R).right.headI = some (stCdec p, R.headI, false) :=
      (entry_eq_some_iff (det_tmOf P N)).mpr (by rw [hRhead]; exact trans_sdec_stop hp hbitk1)
    rw [dstep_left hE rfl]
  refine leg_trans (leg_step hstep4 stSdec_ne) ?_
  -- clear the cell and go home
  have h5 := write_left_and_home (N := N) hp (q := stCdec p) stCdec_ne
      (LL := (cellsFrom N s 0 (k - 1)).reverse)
      (R := cellCode (cellAt N s k) :: R.headI :: R.tail)
      (b := cellCode (clrBit (cellAt N s k) r))
      (fun a ha => isCell_mem_cellsFrom a (List.mem_reverse.mp ha))
      (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact isCell_code _
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact isCell_headI hRcell
          · exact isCell_tail hRcell a ha)
      (isCell_code _) (trans_cdec hp (cellAt N s k))
  -- identify the resulting configuration
  have hcong : ∀ jj, k + 1 < jj → cellAt N s jj = cellAt N s' jj := fun jj hjj =>
    (cellAt_update_eq (by omega)).symm
  have hRhead' : R.headI = cellCode (cellAt N s' (k + 1)) := by
    rw [hRhead, cellAt_update_eq (v := k - 1) (j := k + 1) (by omega)]
  have hw := cells_write (N := N) (s := s) (s' := s') k (m - k) hcong
  have hpre : cellsFrom N s 0 (k - 1) = cellsFrom N s' 0 (k - 1) :=
    cellsFrom_congr 0 (k - 1) (fun jj h1 h2 => (cellAt_update_eq (by omega)).symm)
  have hclr : cellCode (clrBit (cellAt N s k) r) = cellCode (cellAt N s' k) := by
    rw [cellAt_update_clr (v := k - 1) (j := k) (by omega)]
  have heq : (Cfg.mk [] (stHome (min (p + 1) P.length))
      (mark N :: (((cellsFrom N s 0 (k - 1)).reverse).reverse ++
        cellCode (clrBit (cellAt N s k) r) :: (cellCode (cellAt N s k) :: R.headI :: R.tail).tail)))
      = homeCfg N (stHome (min (p + 1) P.length)) s' (max m (k + 1)) := by
    simp only [homeCfg, List.reverse_reverse, List.tail_cons, Cfg.mk.injEq, true_and]
    rw [hclr, hpre, hRhead', hw]
    have esnoc : cellsFrom N s' 0 (k - 1) ++ [cellCode (cellAt N s' k)] = cellsFrom N s' 0 k := by
      have h := cellsFrom_snoc N s' 0 (k - 1)
      rw [show k - 1 + 1 = k by omega, show 0 + (k - 1) + 1 = k by omega] at h
      exact h.symm
    rw [show cellsFrom N s' 0 (k - 1) ++ cellCode (cellAt N s' k) ::
        cellsFrom N s' k (max (m - k) 1)
      = (cellsFrom N s' 0 (k - 1) ++ [cellCode (cellAt N s' k)]) ++
        cellsFrom N s' k (max (m - k) 1) by simp, esnoc]
    have := cellsFrom_add N s' 0 k (max (m - k) 1)
    rw [Nat.zero_add, show k + max (m - k) 1 = max m (k + 1) by omega] at this
    rw [this]
  rw [← heq]
  exact h5

/-! ## Simulating the whole program -/

/-- One instruction of the program is one leg of the machine's run. -/
lemma sim_instr (hN : ∀ i ∈ P, i.reg < N) {p : ℕ} {ins : Instr} (hp : P[p]? = some ins)
    (s : Regs) (m : ℕ) (hm : ∀ i : Fin N, s i ≤ m) :
    ∃ m', (∀ i : Fin N, (instrStep ins (p, s)).2 i ≤ m') ∧
      Leg1 P N (homeCfg N (stHome p) s m)
        (homeCfg N (stHome (min (instrStep ins (p, s)).1 P.length))
          (instrStep ins (p, s)).2 m') := by
  have hmem : ins ∈ P := List.mem_of_getElem? hp
  cases ins with
  | inc r =>
    have hr : r < N := hN _ hmem
    refine ⟨max m (s r + 1), ?_, ?_⟩
    · intro i
      simp only [instrStep, Function.update_apply]
      by_cases hi : (i : ℕ) = r
      · simp [hi]
      · have := hm i
        simp [hi]
        omega
    · exact sim_inc hp hr s m hm
  | dec r j =>
    have hr : r < N := hN _ hmem
    by_cases hz : s r = 0
    · refine ⟨max m 1, ?_, ?_⟩
      · intro i
        have := hm i
        simp only [instrStep, hz, if_pos]
        omega
      · have h := sim_dec_zero hp hr s m hm hz
        simpa [instrStep, hz] using h
    · refine ⟨max m (s r + 1), ?_, ?_⟩
      · intro i
        simp only [instrStep, hz]
        by_cases hi : (i : ℕ) = r
        · have := hm i
          simp [hi]
          omega
        · have := hm i
          simp [hi]
          omega
      · have h := sim_dec_pos hp hr s m hm hz
        simpa [instrStep, hz] using h
  | jmp j =>
    refine ⟨max m 1, ?_, ?_⟩
    · intro i
      have := hm i
      simp only [instrStep]
      omega
    · have h := sim_jmp hp s m hm
      simpa [instrStep] using h

/-- The program halts when started from the configuration `c`. -/
def CHaltsAt (P : Prog) (c : CCfg) : Prop := ∃ t, P.length ≤ ((cstep P)^[t] c).1

lemma chaltsAt_of_step {c : CCfg} (h : CHaltsAt P (cstep P c)) : CHaltsAt P c := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t + 1, by rwa [Function.iterate_succ_apply]⟩

lemma lt_length_of_not_chaltsAt {c : CCfg} (h : ¬ CHaltsAt P c) : c.1 < P.length := by
  by_contra hc
  exact h ⟨0, by simpa using (by omega : P.length ≤ c.1)⟩

/-- If the program halts, the machine reaches its accept state. -/
lemma accepts_of_chaltsAt (hN : ∀ i ∈ P, i.reg < N) :
    ∀ (t p : ℕ) (s : Regs) (m : ℕ), (∀ i : Fin N, s i ≤ m) →
      P.length ≤ ((cstep P)^[t] (p, s)).1 →
      ∃ u, ((dstep (tmOf P N))^[u] (homeCfg N (stHome (min p P.length)) s m)).st
        = stHome P.length := by
  intro t
  induction t with
  | zero =>
    intro p s m _ hhalt
    simp only [Function.iterate_zero, id_eq] at hhalt
    exact ⟨0, by simp [homeCfg, show min p P.length = P.length by omega]⟩
  | succ t ih =>
    intro p s m hm hhalt
    by_cases hp : p < P.length
    · obtain ⟨ins, hins⟩ : ∃ ins, P[p]? = some ins :=
        ⟨P[p]'hp, List.getElem?_eq_getElem hp⟩
      obtain ⟨m', hm', T, hT0, hTe, -⟩ := sim_instr hN hins s m hm
      rw [Function.iterate_succ_apply, cstep_of_getElem? (c := (p, s)) hins] at hhalt
      obtain ⟨u, hu⟩ := ih _ _ m' hm' hhalt
      refine ⟨T + u, ?_⟩
      rw [iter_add', show min p P.length = p by omega, hTe]
      exact hu
    · exact ⟨0, by simp [homeCfg, show min p P.length = P.length by omega]⟩

/-- A criterion for a state never to be visited. -/
lemma never_state {M : TM} {qbad : ℕ} (X : Cfg → Prop)
    (hX : ∀ c, X c → ∃ T, 0 < T ∧ X ((dstep M)^[T] c) ∧
      ∀ t < T, ((dstep M)^[t] c).st ≠ qbad)
    {c : Cfg} (hc : X c) : ∀ t, ((dstep M)^[t] c).st ≠ qbad := by
  intro t
  induction t using Nat.strong_induction_on generalizing c with
  | _ t ih =>
    obtain ⟨T, hT0, hXT, hne⟩ := hX c hc
    by_cases h : t < T
    · exact hne t h
    · obtain ⟨u, rfl⟩ : ∃ u, t = T + u := ⟨t - T, by omega⟩
      rw [iter_add']
      exact ih u (by omega) hXT

/-- If the program does not halt, the machine never reaches its accept state. -/
lemma not_accepts_of_not_chaltsAt (hN : ∀ i ∈ P, i.reg < N) {p : ℕ} {s : Regs} {m : ℕ}
    (hm : ∀ i : Fin N, s i ≤ m) (h : ¬ CHaltsAt P (p, s)) :
    ∀ t, ((dstep (tmOf P N))^[t] (homeCfg N (stHome (min p P.length)) s m)).st
      ≠ stHome P.length := by
  refine never_state
    (fun c => ∃ p s m, (∀ i : Fin N, s i ≤ m) ∧ ¬ CHaltsAt P (p, s) ∧
      c = homeCfg N (stHome (min p P.length)) s m) ?_ ⟨p, s, m, hm, h, rfl⟩
  rintro c ⟨p', s', m', hm', hnh, rfl⟩
  have hp : p' < P.length := lt_length_of_not_chaltsAt hnh
  obtain ⟨ins, hins⟩ : ∃ ins, P[p']? = some ins := ⟨P[p']'hp, List.getElem?_eq_getElem hp⟩
  obtain ⟨m'', hm'', T, hT0, hTe, hTne⟩ := sim_instr hN hins s' m' hm'
  rw [show min p' P.length = p' by omega]
  refine ⟨T, hT0, ?_, hTne⟩
  rw [hTe]
  refine ⟨(instrStep ins (p', s')).1, (instrStep ins (p', s')).2, m'', hm'', ?_, rfl⟩
  intro hc
  exact hnh (chaltsAt_of_step (by rwa [cstep_of_getElem? (c := (p', s')) hins]))

/-- **The machine accepts exactly when the program halts.** -/
theorem accepts_iff_chalts (hN : ∀ i ∈ P, i.reg < N) (s : Regs) (m : ℕ)
    (hm : ∀ i : Fin N, s i ≤ m) :
    (tmOf P N).Accepts (mark N :: cellsFrom N s 0 m) ↔ CHalts P s := by
  rw [accepts_iff_dstep (det_tmOf P N)]
  have hinit : initCfg (tmOf P N) (mark N :: cellsFrom N s 0 m)
      = homeCfg N (stHome (min 0 P.length)) s m := by
    simp [initCfg, homeCfg]
  rw [hinit, tmOf_qacc]
  constructor
  · intro h
    by_contra hnh
    obtain ⟨t, ht⟩ := h
    exact not_accepts_of_not_chaltsAt hN hm hnh t ht
  · intro h
    obtain ⟨t, ht⟩ := h
    exact accepts_of_chaltsAt hN t 0 s m hm ht

/-! ## The unary input -/

/-- The register state holding `n` in register `0` and nothing else. -/
def initRegs (n : ℕ) : Regs := fun i => if i = 0 then n else 0

/-- The cell with only the bit of register `0` set. -/
def unitCell (N : ℕ) : Cell N := fun i => decide ((i : ℕ) = 0)

lemma cellsFrom_initRegs {N : ℕ} (n : ℕ) :
    ∀ (a d : ℕ), a + d ≤ n → cellsFrom N (initRegs n) a d = List.replicate d (cellCode (unitCell N))
  | _, 0, _ => rfl
  | a, d + 1, h => by
    have hcell : cellAt N (initRegs n) (a + 1) = unitCell N := by
      funext i
      by_cases hi : (i : ℕ) = 0
      · simp [cellAt, initRegs, unitCell, hi]
        omega
      · simp [cellAt, initRegs, unitCell, hi]
    rw [cellsFrom_succ, hcell, cellsFrom_initRegs n (a + 1) d (by omega), List.replicate_succ]

/-- **The machine accepts the unary encoding of `n` exactly when the program halts on
`n`.** -/
theorem accepts_unary_iff (hN : ∀ i ∈ P, i.reg < N) (n : ℕ) :
    (tmOf P N).Accepts (mark N :: List.replicate n (cellCode (unitCell N)))
      ↔ CHalts P (initRegs n) := by
  have h := accepts_iff_chalts hN (initRegs n) n (fun i => by
    simp only [initRegs]
    by_cases hi : (i : ℕ) = 0 <;> simp [hi])
  rwa [cellsFrom_initRegs n 0 n (by omega)] at h

end Sim
end Lax251941Proofs.PCP
