import Lax185574Proofs.RamDoveInv

/-!
The pieces of one slot of the dovetailer.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

/-! ### Layout -/

theorem length_flatten_pairs {α : Type} (n : ℕ) (f : ℕ → List α) (hf : ∀ l, (f l).length = 2) :
    ((List.range n).map f).flatten.length = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ih]
      simp [hf]; ring

section layout

variable (Q : Program) (B K : ℕ)

@[simp] theorem dvInit_length : (dvInit B K).length = dvL0 := rfl
@[simp] theorem dvHead_length : (dvHead Q).length = 36 := rfl
@[simp] theorem dvDispatch_length : (dvDispatch Q).length = 2 * Q.length + 1 := by
  rw [dvDispatch, List.length_append, length_flatten_pairs _ _ (fun _ => rfl)]; rfl
@[simp] theorem dvStubs_length : (dvStubs Q).length = 2 * Q.length :=
  length_flatten_pairs _ _ (fun _ => rfl)
theorem dvBlocks_length : (blocks (dvCode Q) (dvH Q) dvL Q).length = dvL * Q.length :=
  blocks_length (dvCode Q) _ _ _ le_rfl

theorem fits_mid' {p a b c : Program} {n : ℕ} (hp : p = a ++ b ++ c) (hn : a.length = n) :
    Fits p n b := hp ▸ hn ▸ fits_mid a b c

theorem dv_fits_init : Fits (dvProg Q B K) 0 (dvInit B K) := by
  have := fits_self (dvInit B K) (dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q ++ dvSaveCode ++ dvSkipCode ++ dvDeadCode ++ dvExitCode Q)
  simpa [dvProg, List.append_assoc] using this

theorem dv_fits_head : Fits (dvProg Q B K) dvL0 (dvHead Q) :=
  fits_mid' (a := dvInit B K) (c := dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q ++ dvSaveCode ++ dvSkipCode ++ dvDeadCode ++ dvExitCode Q)
    (by simp [dvProg, List.append_assoc]) rfl

theorem dv_fits_disp : Fits (dvProg Q B K) dvDisp (dvDispatch Q) :=
  fits_mid' (a := dvInit B K ++ dvHead Q) (c := blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q ++ dvSaveCode ++ dvSkipCode ++ dvDeadCode ++ dvExitCode Q)
    (by simp [dvProg, List.append_assoc]) (by simp [dvDisp])

theorem dv_prog_blocks : dvProg Q B K = (dvInit B K ++ dvHead Q ++ dvDispatch Q) ++
    blocks (dvCode Q) (dvH Q) dvL Q ++ (dvStubs Q ++ dvSaveCode ++ dvSkipCode ++ dvDeadCode ++
      dvExitCode Q) := by
  simp [dvProg, List.append_assoc]

theorem dv_pre_length : (dvInit B K ++ dvHead Q ++ dvDispatch Q).length = dvH Q := by
  simp [dvH, dvDisp]; omega

theorem dv_fits_stubs : Fits (dvProg Q B K) (dvStub Q) (dvStubs Q) :=
  fits_mid' (a := dvInit B K ++ dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q)
    (c := dvSaveCode ++ dvSkipCode ++ dvDeadCode ++ dvExitCode Q)
    (by simp [dvProg, List.append_assoc])
    (by rw [List.length_append, dv_pre_length, dvBlocks_length]; rfl)

theorem dv_fits_save : Fits (dvProg Q B K) (dvSave Q) (dvSaveCode) :=
  fits_mid' (a := dvInit B K ++ dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q) (c := dvSkipCode ++ dvDeadCode ++ dvExitCode Q)
    (by simp [dvProg, List.append_assoc])
    (by rw [List.length_append, List.length_append, dv_pre_length, dvBlocks_length,
      dvStubs_length]; rfl)

theorem dv_fits_skip : Fits (dvProg Q B K) (dvSkip Q) dvSkipCode :=
  fits_mid' (a := dvInit B K ++ dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q ++ dvSaveCode) (c := dvDeadCode ++ dvExitCode Q)
    (by simp [dvProg, List.append_assoc])
    (by rw [List.length_append, List.length_append, List.length_append, dv_pre_length,
      dvBlocks_length, dvStubs_length]; rfl)

theorem dv_fits_dead : Fits (dvProg Q B K) (dvDead Q) dvDeadCode :=
  fits_mid' (a := dvInit B K ++ dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q ++ dvSaveCode ++ dvSkipCode) (c := dvExitCode Q)
    (by simp [dvProg, List.append_assoc])
    (by rw [List.length_append, List.length_append, List.length_append, List.length_append,
      dv_pre_length, dvBlocks_length, dvStubs_length]; rfl)

theorem dv_fits_exit : Fits (dvProg Q B K) (dvExit Q) (dvExitCode Q) :=
  fits_mid' (a := dvInit B K ++ dvHead Q ++ dvDispatch Q ++ blocks (dvCode Q) (dvH Q) dvL Q ++
    dvStubs Q ++ dvSaveCode ++ dvSkipCode ++ dvDeadCode) (c := [])
    (by simp [dvProg, List.append_assoc])
    (by rw [List.length_append, List.length_append, List.length_append, List.length_append,
      List.length_append, dv_pre_length, dvBlocks_length, dvStubs_length]; rfl)

end layout

end Lax185574Proofs.RamSim

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

variable {w K B : ℕ} {Q : Program} {x : List ℕ}

/-! ### Frames -/

theorem Saved.frame {i : ℕ} {S S' s : State} (h : Saved w K B x i S s)
    (hf : ∀ a, (dvCtx B i ≤ a ∧ a < dvCtx B i + dvR B) ∨
      (dvBase w K i ≤ a ∧ a < dvBase w K i + 2 ^ (w - K - i)) → S'.mem a = S.mem a) :
    Saved w K B x i S' s := by
  have hR : dvR B = B + 5 := rfl
  have hoc := h.ocB
  exact
    { pc := by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h.pc
      cur := by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h.cur
      inp := by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h.inp
      oc := by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h.oc
      ocB := h.ocB
      alive := by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h.alive
      buf := fun k hk => by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h.buf k hk
      mem := fun a ha => by rw [hf _ (Or.inr ⟨by omega, by omega⟩)]; exact h.mem a ha
      cword := h.cword
      input := h.input }

theorem TInv.frame {i c : ℕ} {S S' : State} (h : TInv w K B Q x i c S)
    (hf : ∀ a, (dvCtx B i ≤ a ∧ a < dvCtx B i + dvR B) ∨
      (dvBase w K i ≤ a ∧ a < dvBase w K i + 2 ^ (w - K - i)) → S'.mem a = S.mem a) :
    TInv w K B Q x i c S' := by
  have hR : dvR B = B + 5 := rfl
  rcases h with ⟨s, h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨s, h1, h2, h3.frame hf⟩
  · exact Or.inr ⟨by rw [hf _ (Or.inl ⟨by omega, by omega⟩)]; exact h1, h2⟩

theorem dvBase_mono {m n : ℕ} (hK : 2 ≤ K) (hmn : m < n) (hn : n + K < w) :
    dvBase w K m + 2 ^ (w - K - m) ≤ dvBase w K n := by
  induction n, hmn using Nat.le_induction with
  | base => exact (dvBase_bounds hK (by omega)).2.2
  | succ n hmn ih =>
      exact le_trans (ih (by omega)) (le_trans (Nat.le_add_right _ _)
        (dvBase_bounds hK (by omega)).2.2)

/-- The records and memories of two different threads are disjoint, and
both lie above the scheduler's cells. -/
theorem dv_disjoint (G : DGlob w K B Q x) {i i' : ℕ} (hi : i + K < w) (hi' : i' + K < w)
    (hne : i ≠ i') (a : ℕ)
    (ha : (dvCtx B i' ≤ a ∧ a < dvCtx B i' + dvR B) ∨
      (dvBase w K i' ≤ a ∧ a < dvBase w K i' + 2 ^ (w - K - i'))) :
    40 ≤ a ∧ ¬ (dvCtx B i ≤ a ∧ a < dvCtx B i + dvR B) ∧
      ¬ (dvBase w K i ≤ a ∧ a < dvBase w K i + 2 ^ (w - K - i)) := by
  have hK : 2 ≤ K := by have := G.k2; omega
  have room := G.room
  have hR : 1 ≤ dvR B := by simp [dvR]
  have c1 : dvCtx B i + dvR B ≤ 40 + dvR B * w := by
    simp only [dvCtx]; nlinarith
  have c2 : dvCtx B i' + dvR B ≤ 40 + dvR B * w := by
    simp only [dvCtx]; nlinarith
  obtain ⟨b1, b2, b3⟩ := dvBase_bounds hK hi
  obtain ⟨b1', b2', b3'⟩ := dvBase_bounds hK hi'
  -- memories are ordered by index
  have mono : ∀ m n, m < n → n + K < w → dvBase w K m + 2 ^ (w - K - m) ≤ dvBase w K n :=
    fun m n hmn hn => dvBase_mono hK hmn hn
  have cdis : dvCtx B i + dvR B ≤ dvCtx B i' ∨ dvCtx B i' + dvR B ≤ dvCtx B i := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · left; simp only [dvCtx]; nlinarith
    · right; simp only [dvCtx]; nlinarith
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := mono i i' h hi'
    rcases ha with ha | ha <;> refine ⟨by simp only [dvCtx] at *; omega, ?_, ?_⟩ <;> omega
  · have := mono i' i h hi
    rcases ha with ha | ha <;> refine ⟨by simp only [dvCtx] at *; omega, ?_, ?_⟩ <;> omega

end Lax185574Proofs.RamSim
