/-
# A calculus for writing counter machine programs

A program that always halts is described by the transformation it effects on the
registers (`Impl P F`); a program that may diverge is described by a domain and a
transformation (`Sat P D F`).  Both are closed under sequencing, which is what makes it
possible to build up large programs from small ones without ever reasoning about the
program counter.
-/
import Lax251941Proofs.Source.Sim.Counter

namespace Lax251941Proofs.PCP
namespace Sim

/-- The register an instruction acts on. -/
def Instr.reg : Instr → ℕ
  | .inc r => r
  | .dec r _ => r
  | .jmp _ => 0

/-- All registers used by the program are below `b`. -/
def RegBound (P : Prog) (b : ℕ) : Prop := ∀ i ∈ P, i.reg < b

lemma regBound_mono {P : Prog} {b b' : ℕ} (h : RegBound P b) (hb : b ≤ b') : RegBound P b' :=
  fun i hi => lt_of_lt_of_le (h i hi) hb

@[simp] lemma regBound_nil (b : ℕ) : RegBound [] b := by simp [RegBound]

@[simp] lemma reg_shiftI (k : ℕ) (i : Instr) : (shiftI k i).reg = i.reg := by
  cases i <;> rfl

lemma regBound_shift {P : Prog} {b : ℕ} (h : RegBound P b) (k : ℕ) :
    RegBound (shift k P) b := by
  intro i hi
  rw [shift, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  rw [reg_shiftI]
  exact h j hj

lemma regBound_append {P Q : Prog} {b : ℕ} (hP : RegBound P b) (hQ : RegBound Q b) :
    RegBound (P ++ Q) b := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact hP i h
  · exact hQ i h

lemma regBound_pseq {P Q : Prog} {b : ℕ} (hP : RegBound P b) (hQ : RegBound Q b) :
    RegBound (pseq P Q) b :=
  regBound_append hP (regBound_shift hQ _)

lemma regBound_loopDec {B : Prog} {r b : ℕ} (hr : r < b) (hB : RegBound B b) :
    RegBound (loopDec r B) b := by
  intro i hi
  rw [loopDec, List.mem_cons] at hi
  rcases hi with rfl | hi
  · exact hr
  · rcases List.mem_append.mp hi with h | h
    · exact regBound_shift hB 1 i h
    · simp only [List.mem_singleton] at h
      subst h
      exact Nat.zero_lt_of_lt hr

/-! ## Total programs -/

/-- `Impl P F`: the program `P` always halts, transforming the registers by `F`. -/
def Impl (P : Prog) (F : Regs → Regs) : Prop := ∀ s, Runs P s (F s)

lemma impl_of_eq {P : Prog} {F G : Regs → Regs} (h : Impl P F) (hFG : ∀ s, F s = G s) :
    Impl P G := fun s => (hFG s) ▸ h s

lemma impl_nil : Impl [] id := fun s => runs_nil s

lemma impl_seq {P Q : Prog} {F G : Regs → Regs} (h1 : Impl P F) (h2 : Impl Q G) :
    Impl (pseq P Q) (fun s => G (F s)) := fun s => runs_pseq (h1 s) (h2 (F s))

lemma impl_inc (r : ℕ) : Impl [Instr.inc r] (fun s => Function.update s r (s r + 1)) :=
  fun s => runs_inc r s

lemma impl_clear (r : ℕ) : Impl (pclear r) (fun s => Function.update s r 0) :=
  fun s => runs_pclear r s

/-- The effect of a loop whose body does not touch the loop register. -/
lemma impl_loop {B : Prog} {G : Regs → Regs} {r : ℕ} (h : Impl B G) (hr : ∀ t, G t r = t r) :
    Impl (loopDec r B)
      (fun s => (fun t => G (Function.update t r (t r - 1)))^[s r] s) := by
  set H : Regs → Regs := fun t => G (Function.update t r (t r - 1)) with hH
  have key : ∀ n (s : Regs), s r = n → LoopRuns r B s (H^[n] s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      simpa using LoopRuns.zero hs
    | succ n ih =>
      intro s hs
      have h1 : (H s) r = n := by
        rw [hH]
        simp only
        rw [hr]
        simp [hs]
      refine LoopRuns.step (by omega) (h _) ?_
      have := ih (H s) h1
      rwa [← Function.iterate_succ_apply] at this
  intro s
  exact runs_loopDec (key (s r) s rfl)

/-! ## Programs that may diverge -/

/-- `Sat P D F`: the program `P` halts exactly on the register states satisfying `D`, and
then transforms the registers by `F`. -/
def Sat (P : Prog) (D : Regs → Prop) (F : Regs → Regs) : Prop :=
  (∀ s, D s → Runs P s (F s)) ∧ (∀ s, ¬ D s → ¬ CHalts P s)

lemma Impl.toSat {P : Prog} {F : Regs → Regs} (h : Impl P F) :
    Sat P (fun _ => True) F := ⟨fun s _ => h s, fun _ hs => absurd trivial hs⟩

lemma sat_seq {P Q : Prog} {D E : Regs → Prop} {F G : Regs → Regs}
    (h1 : Sat P D F) (h2 : Sat Q E G) :
    Sat (pseq P Q) (fun s => D s ∧ E (F s)) (fun s => G (F s)) := by
  constructor
  · rintro s ⟨hD, hE⟩
    exact runs_pseq (h1.1 s hD) (h2.1 _ hE)
  · intro s hs
    by_cases hD : D s
    · exact not_halts_pseq_right (h1.1 s hD) (h2.2 _ (fun hE => hs ⟨hD, hE⟩))
    · exact not_halts_pseq_left (h1.2 s hD)

lemma sat_of_iff {P : Prog} {D E : Regs → Prop} {F G : Regs → Regs} (h : Sat P D F)
    (hDE : ∀ s, D s ↔ E s) (hFG : ∀ s, D s → F s = G s) : Sat P E G := by
  constructor
  · intro s hs
    have hD := (hDE s).mpr hs
    rw [← hFG s hD]
    exact h.1 s hD
  · intro s hs
    exact h.2 s (fun hD => hs ((hDE s).mp hD))

/-! ## Basic macros -/

/-- Move the contents of one register to another. -/
def pmove (src dst : ℕ) : Prog := pseq (pclear dst) (loopDec src (pseq [] [Instr.inc dst]))

lemma regBound_pmove {src dst b : ℕ} (h1 : src < b) (h2 : dst < b) :
    RegBound (pmove src dst) b :=
  regBound_pseq (regBound_loopDec h2 (by simp [RegBound]))
    (regBound_loopDec h1 (regBound_pseq (by simp)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact h2)))

lemma impl_pmove {src dst : ℕ} (h : src ≠ dst) :
    Impl (pmove src dst)
      (fun s => fun i => if i = src then 0 else if i = dst then s src else s i) := by
  have hbody : Impl (pseq [] [Instr.inc dst])
      (fun t => Function.update t dst (t dst + 1)) := impl_seq impl_nil (impl_inc dst)
  have hloop := impl_loop (r := src) hbody (fun t => by simp [Function.update_of_ne h])
  have hall := impl_seq (impl_clear dst) hloop
  refine impl_of_eq hall (fun s => ?_)
  have key : ∀ n (t : Regs),
      (fun t => Function.update (Function.update t src (t src - 1)) dst
        (Function.update t src (t src - 1) dst + 1))^[n] t
      = fun i => if i = src then t src - n else if i = dst then t dst + n else t i := by
    intro n
    induction n with
    | zero =>
      intro t
      funext i
      rcases eq_or_ne i src with rfl | hi
      · simp
      · rcases eq_or_ne i dst with rfl | hd
        · simp [hi]
        · simp [hi, hd]
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply, ih]
      funext i
      simp only [Function.update_apply]
      split_ifs <;> omega
  rw [key (Function.update s dst 0 src) (Function.update s dst 0)]
  have hsrc : Function.update s dst 0 src = s src := Function.update_of_ne h 0 s
  funext i
  simp only [hsrc, Function.update_apply]
  split_ifs <;> omega

end Sim
end Lax251941Proofs.PCP
