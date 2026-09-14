/-
# Macros for counter machine programs

Building on the calculus of `RequestProject/Sim/Impl.lean`, this file provides the
macros used by the compiler: copying a register, a one-armed conditional, a loop rule
with a decreasing measure, and the block operations (clearing, moving and copying a
range of registers).
-/
import Lax251941Proofs.Source.Sim.Impl

namespace Lax251941Proofs.PCP
namespace Sim

/-! ## A relational description of a program's action

The block macros are more conveniently described by *what holds* of the final registers
than by an explicit transformation. -/

/-- `Acts P Q`: the program `P` halts on every input, and the initial and final registers
are related by `Q`. -/
def Acts (P : Prog) (Q : Regs → Regs → Prop) : Prop :=
  ∀ s, ∃ s', Runs P s s' ∧ Q s s'

lemma Impl.acts {P : Prog} {F : Regs → Regs} (h : Impl P F) :
    Acts P (fun s s' => s' = F s) := fun s => ⟨F s, h s, rfl⟩

lemma acts_mono {P : Prog} {Q Q' : Regs → Regs → Prop} (h : Acts P Q)
    (hQ : ∀ s s', Q s s' → Q' s s') : Acts P Q' := by
  intro s
  obtain ⟨s', hr, hq⟩ := h s
  exact ⟨s', hr, hQ s s' hq⟩

lemma acts_nil : Acts [] (fun s s' => s' = s) := fun s => ⟨s, runs_nil s, rfl⟩

lemma acts_seq {P Q : Prog} {Q₁ Q₂ : Regs → Regs → Prop} (h₁ : Acts P Q₁) (h₂ : Acts Q Q₂) :
    Acts (pseq P Q) (fun s s'' => ∃ s', Q₁ s s' ∧ Q₂ s' s'') := by
  intro s
  obtain ⟨s₁, hr₁, hq₁⟩ := h₁ s
  obtain ⟨s₂, hr₂, hq₂⟩ := h₂ s₁
  exact ⟨s₂, runs_pseq hr₁ hr₂, s₁, hq₁, hq₂⟩

/-! ## Copying a register -/

/-- Copy one register into another, using a third one as scratch. -/
def pcopy (src dst tmp : ℕ) : Prog :=
  pseq (pseq (pclear dst) (pclear tmp))
    (pseq (loopDec src (pseq [Instr.inc dst] [Instr.inc tmp]))
      (loopDec tmp [Instr.inc src]))

section pcopy

variable {src dst tmp : ℕ}

private lemma impl_clear2 (dst tmp : ℕ) :
    Impl (pseq (pclear dst) (pclear tmp))
      (fun s => fun i => if i = tmp then 0 else if i = dst then 0 else s i) := by
  refine impl_of_eq (impl_seq (impl_clear dst) (impl_clear tmp)) (fun s => ?_)
  funext i
  simp only [Function.update_apply]

private lemma impl_pcopy_loop1 (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) :
    Impl (loopDec src (pseq [Instr.inc dst] [Instr.inc tmp]))
      (fun s => fun i => if i = src then 0 else if i = dst then s dst + s src
        else if i = tmp then s tmp + s src else s i) := by
  have hb : Impl (pseq [Instr.inc dst] [Instr.inc tmp])
      (fun t => Function.update (Function.update t dst (t dst + 1)) tmp
        (Function.update t dst (t dst + 1) tmp + 1)) := impl_seq (impl_inc dst) (impl_inc tmp)
  have hl := impl_loop (r := src) hb
    (fun t => by simp only [Function.update_apply, if_neg h1, if_neg h2])
  have key : ∀ n (t : Regs),
      (fun t => Function.update (Function.update (Function.update t src (t src - 1)) dst
          (Function.update t src (t src - 1) dst + 1)) tmp
          (Function.update (Function.update t src (t src - 1)) dst
            (Function.update t src (t src - 1) dst + 1) tmp + 1))^[n] t
      = fun i => if i = src then t src - n else if i = dst then t dst + n
          else if i = tmp then t tmp + n else t i := by
    intro n
    induction n with
    | zero =>
      intro t
      funext i
      by_cases hs : i = src
      · subst hs; simp
      · by_cases hd : i = dst
        · subst hd; simp [hs]
        · by_cases ht : i = tmp
          · subst ht; simp [hs, hd]
          · simp [hs, hd, ht]
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply, ih]
      funext i
      simp only [Function.update_apply, if_neg h1, if_neg h2, if_neg h3]
      split_ifs <;> omega
  refine impl_of_eq hl (fun s => ?_)
  rw [key (s src) s]
  funext i
  by_cases hs : i = src
  · subst hs; simp
  · simp [hs]

private lemma impl_pcopy_loop2 (h2 : src ≠ tmp) :
    Impl (loopDec tmp [Instr.inc src])
      (fun s => fun i => if i = tmp then 0 else if i = src then s src + s tmp else s i) := by
  have hl := impl_loop (r := tmp) (impl_inc src)
    (fun t => by simp only [Function.update_apply, if_neg (Ne.symm h2)])
  have key : ∀ n (t : Regs),
      (fun t => Function.update (Function.update t tmp (t tmp - 1)) src
        (Function.update t tmp (t tmp - 1) src + 1))^[n] t
      = fun i => if i = tmp then t tmp - n else if i = src then t src + n else t i := by
    intro n
    induction n with
    | zero =>
      intro t
      funext i
      by_cases ht : i = tmp
      · subst ht; simp
      · by_cases hs : i = src
        · subst hs; simp [ht]
        · simp [ht, hs]
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply, ih]
      funext i
      simp only [Function.update_apply, if_neg (Ne.symm h2)]
      split_ifs <;> omega
  refine impl_of_eq hl (fun s => ?_)
  rw [key (s tmp) s]
  funext i
  by_cases ht : i = tmp
  · subst ht; simp
  · simp [ht]

lemma impl_pcopy (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) :
    Impl (pcopy src dst tmp)
      (fun s => fun i => if i = dst then s src else if i = tmp then 0 else s i) := by
  refine impl_of_eq (impl_seq (impl_clear2 dst tmp)
    (impl_seq (impl_pcopy_loop1 h1 h2 h3) (impl_pcopy_loop2 h2))) (fun s => ?_)
  funext i
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg (Ne.symm h2), if_neg (Ne.symm h3)]
  by_cases ht : i = tmp
  · subst ht; simp [Ne.symm h3]
  · by_cases hs : i = src
    · subst hs; simp [ht, h1]
    · by_cases hd : i = dst
      · subst hd; simp [ht, hs]
      · simp [ht, hs, hd]

end pcopy


/-! ## A one-armed conditional -/

/-- Run `B` if the register `r` is nonzero (and then leave `r` zero). -/
def pifnz (r : ℕ) (B : Prog) : Prog := loopDec r (pseq (pclear r) B)

lemma impl_pifnz (r : ℕ) {B : Prog} {G : Regs → Regs} (hB : Impl B G) (hG : ∀ t, G t r = t r) :
    Impl (pifnz r B) (fun s => if s r = 0 then s else G (Function.update s r 0)) := by
  intro s
  refine runs_loopDec ?_
  show LoopRuns r (pseq (pclear r) B) s (if s r = 0 then s else G (Function.update s r 0))
  by_cases h : s r = 0
  · rw [if_pos h]
    exact LoopRuns.zero h
  · rw [if_neg h]
    have hupd : Function.update (Function.update s r (s r - 1)) r 0 = Function.update s r 0 :=
      by simp
    refine LoopRuns.step h ?_ (LoopRuns.zero ?_)
    · have := runs_pseq (runs_pclear r (Function.update s r (s r - 1)))
        (hB (Function.update (Function.update s r (s r - 1)) r 0))
      rwa [hupd] at this
    · rw [hG, Function.update_self]

/-! ## A loop rule with a decreasing measure -/

lemma runs_loopDec_of_measure {r : ℕ} {B : Prog} {I : Regs → Prop} {mu : Regs → ℕ}
    (hstep : ∀ s, I s → s r ≠ 0 →
      ∃ s', Runs B (Function.update s r (s r - 1)) s' ∧ I s' ∧ mu s' < mu s) :
    ∀ s, I s → ∃ s', Runs (loopDec r B) s s' ∧ I s' ∧ s' r = 0 := by
  have key : ∀ n s, mu s ≤ n → I s → ∃ s', LoopRuns r B s s' ∧ I s' ∧ s' r = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hmu hI
      by_cases h : s r = 0
      · exact ⟨s, LoopRuns.zero h, hI, h⟩
      · obtain ⟨s', _, _, hlt⟩ := hstep s hI h
        omega
    | succ n ih =>
      intro s hmu hI
      by_cases h : s r = 0
      · exact ⟨s, LoopRuns.zero h, hI, h⟩
      · obtain ⟨s', hr, hI', hlt⟩ := hstep s hI h
        obtain ⟨s'', hl, hI'', hz⟩ := ih s' (by omega) hI'
        exact ⟨s'', LoopRuns.step h hr hl, hI'', hz⟩
  intro s hI
  obtain ⟨s', hl, hI', hz⟩ := key (mu s) s le_rfl hI
  exact ⟨s', runs_loopDec hl, hI', hz⟩

/-- Run the programs `Q 0, Q 1, …, Q (j-1)` in succession. -/
def pstages (Q : ℕ → Prog) : ℕ → Prog
  | 0 => []
  | (j + 1) => pseq (pstages Q j) (Q j)

/-! ## Block operations -/

/-- Clear the registers `lo, lo+1, …, lo+m-1`. -/
def pclearRange : ℕ → ℕ → Prog
  | _, 0 => []
  | lo, (m + 1) => pseq (pclear lo) (pclearRange (lo + 1) m)

lemma acts_pclearRange (lo m : ℕ) :
    Acts (pclearRange lo m) (fun s s' =>
      (∀ i, lo ≤ i → i < lo + m → s' i = 0) ∧ ∀ i, (i < lo ∨ lo + m ≤ i) → s' i = s i) := by
  induction m generalizing lo with
  | zero =>
    refine acts_mono acts_nil (fun s s' hs => ?_)
    subst hs
    exact ⟨fun i h1 h2 => by omega, fun i _ => rfl⟩
  | succ m ih =>
    refine acts_mono (acts_seq (impl_clear lo).acts (ih (lo + 1))) (fun s s'' h => ?_)
    obtain ⟨s₁, hs₁, hz, hf⟩ := h
    subst hs₁
    constructor
    · intro i h1 h2
      rcases eq_or_ne i lo with rfl | hne
      · rw [hf i (Or.inl (by omega))]
        simp
      · exact hz i (by omega) (by omega)
    · intro i hi
      rw [hf i (by omega), Function.update_of_ne (by omega)]

/-- Move the block of `m` registers starting at `src` to the block starting at `dst`. -/
def pmoveBlock : ℕ → ℕ → ℕ → Prog
  | _, _, 0 => []
  | src, dst, (m + 1) => pseq (pmove src dst) (pmoveBlock (src + 1) (dst + 1) m)

lemma acts_pmoveBlock {src dst : ℕ} : ∀ {m : ℕ}, (src + m ≤ dst ∨ dst + m ≤ src) →
    Acts (pmoveBlock src dst m) (fun s s' =>
      (∀ j, j < m → s' (dst + j) = s (src + j)) ∧
      (∀ j, j < m → s' (src + j) = 0) ∧
      (∀ i, (∀ j, j < m → i ≠ src + j ∧ i ≠ dst + j) → s' i = s i)) := by
  intro m
  induction m generalizing src dst with
  | zero =>
    intro _
    refine acts_mono acts_nil (fun s s' hs => ?_)
    subst hs
    exact ⟨fun j h => by omega, fun j h => by omega, fun i _ => rfl⟩
  | succ m ih =>
    intro hd
    have hne : src ≠ dst := by omega
    have hd' : (src + 1) + m ≤ dst + 1 ∨ (dst + 1) + m ≤ src + 1 := by omega
    refine acts_mono (acts_seq (impl_pmove hne).acts (ih hd')) (fun s s'' h => ?_)
    obtain ⟨s₁, hs₁, h1, h2, h3⟩ := h
    subst hs₁
    have hsrc : (fun i => if i = src then 0 else if i = dst then s src else s i : Regs) src = 0 := by
      simp
    have hdst : (fun i => if i = src then 0 else if i = dst then s src else s i : Regs) dst
        = s src := by simp [Ne.symm hne]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      match j with
      | 0 => rw [Nat.add_zero, h3 dst (fun k hk => by omega), Nat.add_zero]; exact hdst
      | (k + 1) =>
        have := h1 k (by omega)
        rw [show dst + (k + 1) = (dst + 1) + k from by omega, this,
          show (src + 1) + k = src + (k + 1) from by omega]
        simp only [if_neg (show src + (k + 1) ≠ src from by omega),
          if_neg (show src + (k + 1) ≠ dst from by omega)]
    · intro j hj
      match j with
      | 0 => rw [Nat.add_zero, h3 src (fun k hk => by omega)]; exact hsrc
      | (k + 1) =>
        have := h2 k (by omega)
        rw [show src + (k + 1) = (src + 1) + k from by omega, this]
    · intro i hi
      rw [h3 i (fun k hk => by
        have := hi (k + 1) (by omega)
        omega)]
      have h0 := hi 0 (by omega)
      simp only [Nat.add_zero] at h0
      simp [h0.1, h0.2]

/-- Copy the block of `m` registers starting at `src` to the block starting at `dst`,
using `tmp` as scratch. -/
def pcopyBlock : ℕ → ℕ → ℕ → ℕ → Prog
  | _, _, tmp, 0 => pclear tmp
  | src, dst, tmp, (m + 1) => pseq (pcopy src dst tmp) (pcopyBlock (src + 1) (dst + 1) tmp m)

lemma acts_pcopyBlock {src dst tmp : ℕ} : ∀ {m : ℕ}, (src + m ≤ dst ∨ dst + m ≤ src) →
    (∀ j, j < m → tmp ≠ src + j) → (∀ j, j < m → tmp ≠ dst + j) →
    Acts (pcopyBlock src dst tmp m) (fun s s' =>
      (∀ j, j < m → s' (dst + j) = s (src + j)) ∧ s' tmp = 0 ∧
      (∀ i, i ≠ tmp → (∀ j, j < m → i ≠ dst + j) → s' i = s i)) := by
  intro m
  induction m generalizing src dst with
  | zero =>
    intro _ _ _
    refine acts_mono (impl_clear tmp).acts (fun s s' hs => ?_)
    subst hs
    exact ⟨fun j h => by omega, by simp, fun i hi _ => Function.update_of_ne hi 0 s⟩
  | succ m ih =>
    intro hd ht1 ht2
    have hne : src ≠ dst := by omega
    have htsrc : tmp ≠ src := by simpa using ht1 0 (by omega)
    have htdst : tmp ≠ dst := by simpa using ht2 0 (by omega)
    have hd' : (src + 1) + m ≤ dst + 1 ∨ (dst + 1) + m ≤ src + 1 := by omega
    refine acts_mono (acts_seq (impl_pcopy hne (Ne.symm htsrc) (Ne.symm htdst)).acts
      (ih hd' (fun j hj => by have := ht1 (j + 1) (by omega); omega)
        (fun j hj => by have := ht2 (j + 1) (by omega); omega))) (fun s s'' h => ?_)
    obtain ⟨s₁, hs₁, h1, h2, h3⟩ := h
    subst hs₁
    refine ⟨?_, h2, ?_⟩
    · intro j hj
      match j with
      | 0 =>
        rw [Nat.add_zero, h3 dst (Ne.symm htdst) (fun k hk => by omega), Nat.add_zero]
        simp
      | (k + 1) =>
        have := h1 k (by omega)
        rw [show dst + (k + 1) = (dst + 1) + k from by omega, this,
          show (src + 1) + k = src + (k + 1) from by omega]
        have e1 : src + (k + 1) ≠ dst := by omega
        have e2 : src + (k + 1) ≠ tmp := by have := ht1 (k + 1) (by omega); omega
        simp only [if_neg e1, if_neg e2]
    · intro i hi hj
      rw [h3 i hi (fun k hk => by have := hj (k + 1) (by omega); omega)]
      have h0 := hj 0 (by omega)
      simp only [Nat.add_zero] at h0
      simp [h0, hi]

end Sim
end Lax251941Proofs.PCP
