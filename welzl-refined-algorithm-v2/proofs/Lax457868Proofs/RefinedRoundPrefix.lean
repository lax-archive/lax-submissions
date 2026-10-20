import Lax457868Proofs.RefinedBodyEstimate

/-! The actual chronological round boundary is a stopping prefix. This
connects conditional component estimates to the physical body execution. -/
namespace Lax457868Proofs.RefinedRoundPrefix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedBodyEstimate
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.StoppedPrefixAveraging
open Lax195003.WordRamRandomness

/-- Execute at most the first `i` guarded rounds. -/
def prefixSource : ℕ → Com
  | 0 => .skip
  | i+1 => .ite roundGuard (preparedRefinedRoundSource.seq (prefixSource i)) .skip

def stateBefore : List RoundEvent → Env → ℕ → Env
  | [], σ, _ => σ
  | _::_, σ, 0 => σ
  | e::es, _, i+1 => stateBefore es e.exit i

lemma prefix_run {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events)
    (ht : roundGuard.evalB B τ = some false) (i : ℕ) :
    ∃ K, Run B (prefixSource i) σ (stateBefore events σ i) K := by
  induction h generalizing i with
  | nil σ =>
    cases i with
    | zero => exact ⟨1, Run.skip⟩
    | succ j => exact ⟨_, Run.ite_false ht Run.skip⟩
  | cons hready hg ha hr hin hcons ho hstop htail ih =>
    cases i with
    | zero => exact ⟨1, Run.skip⟩
    | succ j =>
      obtain ⟨K,hK⟩ := ih ht j
      exact ⟨_,Run.ite_true hg (hr.1.seq hK)⟩

lemma prefix_input {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) (i : ℕ) :
    σ.inp = ((events.take i).flatMap fun e => e.consumed) ++
      (stateBefore events σ i).inp := by
  induction h generalizing i with
  | nil => simp [stateBefore]
  | cons hready hg ha hr hin hcons ho hstop htail ih =>
    cases i with
    | zero => simp [stateBefore]
    | succ j =>
      simpa [stateBefore, List.append_assoc] using hin.trans
        (congrArg (fun xs => _ ++ xs) (ih j))

lemma activeAt_guard {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events)
    (ht : roundGuard.evalB B τ = some false) (i : ℕ) :
    activeAt events i = if roundGuard.evalB B (stateBefore events σ i) = some true
      then (stateBefore events σ i).vars "acount" else 0 := by
  induction h generalizing i with
  | nil => simp [activeAt, stateBefore, ht]
  | cons hready hg ha hr hin hcons ho hstop htail ih =>
    cases i with
    | zero => simpa [activeAt, stateBefore, hg] using ha.symm
    | succ j => exact ih ht j

/-- The initial quotient reads no random bits, followed by exactly the
recorded prefix of guarded rounds. -/
lemma body_prefix_run {B c n N : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} (F : LargeBodyFamily B c n N G x σ)
    (ρ : Tape N) (i : ℕ) :
    ∃ K, Run B
      (Lax457868Proofs.InitialNeighborhoodQuotient.initialQuotientSource.seq
        (prefixSource i))
      {σ with inp := (List.ofFn ρ).map Bool.toNat}
      (stateBefore (F.events ρ) (F.quotient ρ) i) K := by
  obtain ⟨K,hK⟩ := prefix_run (F.trace ρ) (F.terminal_guard ρ) i
  have hq := F.quotient_run ρ
  have hbits : bitTape ρ = (List.ofFn ρ).map Bool.toNat := by
    simp only [bitTape, List.map_ofFn, Function.comp_def]
    congr 1
    funext j
    cases ρ j <;> rfl
  rw [hbits] at hq
  exact ⟨_,hq.seq hK⟩

lemma body_prefix_input {B c n N : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} (F : LargeBodyFamily B c n N G x σ)
    (ρ : Tape N) (i : ℕ) :
    (stateBefore (F.events ρ) (F.quotient ρ) i).inp =
      ((List.ofFn ρ).drop (usedBefore (F.events ρ) i)).map Bool.toNat := by
  have hq : (F.quotient ρ).inp = bitTape ρ :=
    (F.quotient_run ρ).frame_inp (by decide)
  have hi := prefix_input (F.trace ρ) i
  rw [hq] at hi
  have hd := congrArg (List.drop (usedBefore (F.events ρ) i)) hi
  have hbits : bitTape ρ = (List.ofFn ρ).map Bool.toNat := by
    simp only [bitTape, List.map_ofFn, Function.comp_def]
    congr 1
    funext j
    cases ρ j <;> rfl
  rw [hbits] at hd
  simpa [usedBefore, List.drop_append, List.map_drop] using hd.symm

/-- Equal consumed prefixes give the same next-round machine state and
active size, even when one execution has already terminated. -/
lemma body_prefix_causal {B c n N : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env} (F : LargeBodyFamily B c n N G x σ)
    (ρ η : Tape N) (i : ℕ)
    (hp : (List.ofFn ρ).take (usedBefore (F.events ρ) i) =
      (List.ofFn η).take (usedBefore (F.events ρ) i)) :
    usedBefore (F.events η) i = usedBefore (F.events ρ) i ∧
    stateBefore (F.events η) (F.quotient η) i =
      {stateBefore (F.events ρ) (F.quotient ρ) i with
        inp := ((List.ofFn η).drop (usedBefore (F.events ρ) i)).map Bool.toNat} ∧
    activeAt (F.events η) i = activeAt (F.events ρ) i := by
  obtain ⟨K,hK⟩ := body_prefix_run F ρ i
  obtain ⟨J,hJ⟩ := body_prefix_run F η i
  have hi := body_prefix_input F ρ i
  have hj := body_prefix_input F η i
  have hh := bool_run_same_prefix (σ := σ) (List.ofFn ρ) (List.ofFn η) []
    (by simpa using hK) (by simpa using hJ)
    (by simpa using hi) (by simpa using hj)
    (by simpa using F.usedBefore_le ρ i) (by simpa using F.usedBefore_le η i) hp
  refine ⟨hh.1, by simpa using hh.2, ?_⟩
  rw [activeAt_guard (F.trace η) (F.terminal_guard η),
    activeAt_guard (F.trace ρ) (F.terminal_guard ρ), hh.2]
  rfl

end Lax457868Proofs.RefinedRoundPrefix
