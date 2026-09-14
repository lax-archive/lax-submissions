/-
# A tape machine for every partial recursive function

The theorem of this file is the Turing-completeness of the tape machines of
`RequestProject/PCP/TuringMachine.lean`, in the form in which it is used to make the
undecidability of the Post Correspondence Problem unconditional: for every partial
recursive `f : ℕ →. ℕ` there is a *single* tape machine which, on the unary encoding of
`n`, reaches its accept state exactly when `f n` is defined.

The machine is obtained by compiling `f` to a counter machine program
(`RequestProject/Sim/Compile.lean`) and the program to a tape machine
(`RequestProject/Sim/Simulate.lean`).
-/
import Lax251941Proofs.Source.PCP.Undecidable
import Lax251941Proofs.Source.Sim.Rfind

namespace Lax251941Proofs.PCP
namespace Sim

/-- **Turing completeness of the tape machines.**  For every partial recursive function
there is a tape machine and two tape symbols such that the machine accepts the word
`mk :: c^n` exactly when the function is defined at `n`. -/
theorem exists_regBound : ∀ P : Prog, ∃ N, 1 ≤ N ∧ ∀ i ∈ P, i.reg < N
  | [] => ⟨1, le_rfl, by simp⟩
  | (a :: P) => by
    obtain ⟨N, h1, hN⟩ := exists_regBound P
    refine ⟨max N (a.reg + 1), by omega, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · have := hN i hi
      omega

theorem exists_tape_machine (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ (M : TM) (mk c : ℕ), ∀ n : ℕ, M.Accepts (mk :: List.replicate n c) ↔ (f n).Dom := by
  obtain ⟨b, P, hP⟩ := exists_prog (Nat.Partrec'.part_iff₁.mpr hf)
  obtain ⟨N, hN1, hN⟩ := exists_regBound P
  refine ⟨tmOf P N, mark N, cellCode (unitCell N), fun n => ?_⟩
  rw [accepts_unary_iff hN n]
  have hpre : ∀ i, 1 ≤ i → i < b → initRegs n i = 0 := by
    intro i h1 _
    simp only [initRegs]
    rw [if_neg (by omega)]
  have hv : (vargs 1 (initRegs n)).head = n := by
    rw [vargs_one_head]
    simp [initRegs]
  obtain ⟨hrun, hdiv⟩ := hP.2 (initRegs n) hpre
  simp only [hv] at hrun hdiv
  constructor
  · intro hh
    by_contra hd
    exact hdiv hd hh
  · intro hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    exact CHalts.of_runs (hrun y hy)

/-- The input words used by `exists_tape_machine` depend computably on `n`. -/
theorem computable_unaryInput (mk c : ℕ) :
    Computable fun n : ℕ => mk :: List.replicate n c := by
  have h := Primrec.nat_rec' (f := fun n : ℕ => n) (g := fun _ => ([] : List ℕ))
      (h := fun (_ : ℕ) (p : ℕ × List ℕ) => c :: p.2) Primrec.id (Primrec.const [])
      (Primrec.list_cons.comp (Primrec.const c) (Primrec.snd.comp Primrec.snd))
  have h2 : Primrec fun n : ℕ => List.replicate n c := by
    refine h.of_eq fun n => ?_
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ] using congrArg (c :: ·) ih
  exact (Primrec.list_cons.comp (Primrec.const mk) h2).to_comp

end Sim
end Lax251941Proofs.PCP
