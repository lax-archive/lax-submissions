import Lax457868Proofs.RefinedRoundPrefix

/-! Lift a fixed-start mean for the physical prepared round to each stopped
chronological round prefix of the actual body execution. -/
namespace Lax457868Proofs.RefinedPrefixMean

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WordRamRandomness
open Lax457868Proofs.RefinedRoundLoop
open Lax457868Proofs.RefinedRoundDriver
open Lax457868Proofs.RefinedRoundTrace
open Lax457868Proofs.RefinedRoundPrefix
open Lax457868Proofs.RefinedBodyEstimate
open Lax457868Proofs.RefinedTapeReserve
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

set_option maxHeartbeats 2000000

private lemma roundGuard_reinput {B : ℕ} (S : Env) (inp : List ℕ) :
    roundGuard.evalB B {S with inp := inp} = roundGuard.evalB B S := by
  rfl

lemma event_at_data {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events) (i : ℕ)
    {e : RoundEvent} (he : events[i]? = some e) :
    e.entry = stateBefore events σ i ∧
    LoopReady B c G x rest e.entry ∧
    roundGuard.evalB B e.entry = some true ∧
    e.active = e.entry.vars "acount" ∧
    BigStepB B preparedRefinedRoundSource e.entry e.exit e.cost := by
  induction h generalizing i e with
  | nil => simp at he
  | cons hready hg ha hr hin hcons ho hstop htail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst e
          exact ⟨rfl, hready, hg, ha.symm, hr.2⟩
      | succ j =>
          simpa [stateBefore] using ih j (by simpa using he)

lemma event_of_guard {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x rest : List ℕ} {σ τ : Env} {events : List RoundEvent}
    (h : TraceChain B c G x rest σ τ events)
    (ht : roundGuard.evalB B τ = some false) (i : ℕ)
    (hg : roundGuard.evalB B (stateBefore events σ i) = some true) :
    ∃ e, events[i]? = some e := by
  induction h generalizing i with
  | nil => simp [stateBefore, ht] at hg
  | cons hready hguard hactive hrun hinput hconsumed houtcome hstop htail ih =>
      cases i with
      | zero => exact ⟨_, rfl⟩
      | succ j =>
          obtain ⟨e, he⟩ := ih ht j (by simpa [stateBefore] using hg)
          exact ⟨e, by simpa using he⟩

lemma chargeAt_of_event (events : List RoundEvent) (i : ℕ)
    {e : RoundEvent} (he : events[i]? = some e) :
    chargeAt events i = 1 + roundGuard.size + e.cost := by
  induction events generalizing i with
  | nil => simp at he
  | cons head tail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst e
          rfl
      | succ j => exact ih j (by simpa using he)

lemma chargeAt_zero_of_no_event (events : List RoundEvent) (i : ℕ)
    (he : events[i]? = none) : chargeAt events i = 0 := by
  induction events generalizing i with
  | nil => rfl
  | cons head tail ih =>
      cases i with
      | zero => simp at he
      | succ j => exact ih j (by simpa using he)

lemma reserve_of_ready_guard {B c n L : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {S : Env}
    (hready : LoopReady B c G x [] S)
    (hg : roundGuard.evalB B S = some true)
    (hlen : S.inp.length = L) : roundBitReserve c n ≤ L := by
  obtain ⟨A,C,bits,sizes,D,hA,hC,hCne,hsep,hstored,hbounded,
    hremoved,hround,hacount,hsizes,hpotential,hshrink,hroundlog,
    hout,hinp,hreserve⟩ := hready
  have hpositive : 0 < A.card := by
    have hlt : S.vars "cutoffResult" < S.vars "acount" := by
      have hh := hg
      simp [roundGuard, evalB_condLt_iff] at hh
      omega
    omega
  have hbits : bits.length = L := by
    have hh := congrArg List.length hinp
    simp at hh
    omega
  have hle : roundBitReserve c n ≤ A.card * roundBitReserve c n := by
    have hm := Nat.mul_le_mul_right (roundBitReserve c n) hpositive
    simpa using hm
  omega

/-- Replacing the unread tail preserves the actual next-round state, apart
from its input tape. -/
lemma suffix_state {B c n N : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ) (ρ : Tape N) (i : ℕ)
    (suffix : Tape (N - usedBefore (F.events ρ) i)) :
    let used := usedBefore (F.events ρ) i
    let η := (splitEquiv (F.usedBefore_le ρ i)).symm
      ((splitEquiv (F.usedBefore_le ρ i) ρ).1, suffix)
    usedBefore (F.events η) i = used ∧
    stateBefore (F.events η) (F.quotient η) i =
      {stateBefore (F.events ρ) (F.quotient ρ) i with
        inp := (List.ofFn suffix).map Bool.toNat} ∧
    activeAt (F.events η) i = activeAt (F.events ρ) i := by
  dsimp
  let used := usedBefore (F.events ρ) i
  let η := (splitEquiv (F.usedBefore_le ρ i)).symm
    ((splitEquiv (F.usedBefore_le ρ i) ρ).1, suffix)
  have hpair : splitEquiv (F.usedBefore_le ρ i) η =
      ((splitEquiv (F.usedBefore_le ρ i) ρ).1, suffix) :=
    Equiv.apply_symm_apply _ _
  have hp : (List.ofFn ρ).take used = (List.ofFn η).take used := by
    rw [StoppedPrefixAveraging.prefix_of_split (F.usedBefore_le ρ i),
      StoppedPrefixAveraging.prefix_of_split (F.usedBefore_le ρ i), hpair]
  obtain ⟨hu, hs, ha⟩ := body_prefix_causal F ρ η i hp
  have hd : (List.ofFn η).drop used = List.ofFn suffix := by
    rw [StoppedPrefixAveraging.boolTape_split (F.usedBefore_le ρ i) η, hpair]
    have hlen :
        (List.ofFn ((splitEquiv (F.usedBefore_le ρ i) ρ).1)).length = used := by
      simp [used]
    rw [List.drop_append_of_le_length (by omega : used ≤
      (List.ofFn ((splitEquiv (F.usedBefore_le ρ i) ρ).1)).length)]
    simp [hlen]
  rw [hd] at hs
  exact ⟨hu, by simpa only [List.map_ofFn] using hs, ha⟩

/-- A fixed-start estimate for the physical prepared source, including every
status branch.  Its start state is a genuine loop entry, and the sampled
suffix replaces precisely the remaining input bits. -/
def FixedPreparedRoundMean {B c n M D : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} : Prop :=
  ∀ (S : Env) (L : ℕ),
    LoopReady B c G x [] S →
    roundGuard.evalB B S = some true →
    S.inp.length = L →
    roundBitReserve c n ≤ L →
    (final : Tape L → Env) → (cost : Tape L → ℕ) →
    (∀ tail, BigStepB B preparedRefinedRoundSource
      {S with inp := (List.ofFn tail).map Bool.toNat}
      (final tail) (cost tail)) →
    (∑ tail, (cost tail : ℚ)) ≤
      (((M * (x.length + 1) +
          D * S.vars "acount" * (Nat.clog 2 n + 1) : ℕ) : ℚ) * 2 ^ L)

/-- The actual body family satisfies the stopped-prefix round obligation
once its fixed-start physical source law is known. -/
lemma prefixRoundMeanAt_of_fixed {B c n N M D : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (F : LargeBodyFamily B c n N G x σ)
    (hfixed : FixedPreparedRoundMean (B := B) (c := c) (n := n)
      (M := M) (D := D) (G := G) (x := x))
    (i : ℕ) :
    PrefixRoundMeanAt (M := M + 1 + roundGuard.size) (D := D) F i := by
  classical
  let used : Tape N → ℕ := fun ρ => usedBefore (F.events ρ) i
  have hbound : ∀ ρ, used ρ ≤ N := fun ρ => F.usedBefore_le ρ i
  refine ⟨used, hbound, ?_, ?_, ?_⟩
  · intro ρ η hp
    exact (body_prefix_causal F ρ η i hp).1
  · intro ρ η hp
    exact (body_prefix_causal F ρ η i hp).2.2
  · intro ρ
    let S := stateBefore (F.events ρ) (F.quotient ρ) i
    let L := N - used ρ
    let extend : Tape L → Tape N := fun tail =>
      (splitEquiv (hbound ρ)).symm
        ((splitEquiv (hbound ρ) ρ).1, tail)
    have hSlen : S.inp.length = L := by
      have hi := body_prefix_input F ρ i
      simpa [S, L, used, List.length_drop, List.length_ofFn,
        Nat.sub_eq_iff_eq_add (hbound ρ)] using congrArg List.length hi
    by_cases hg : roundGuard.evalB B S = some true
    · obtain ⟨base, hbase⟩ := event_of_guard (F.trace ρ)
        (F.terminal_guard ρ) i hg
      obtain ⟨hentry, hready, _, _, _⟩ :=
        event_at_data (F.trace ρ) i hbase
      have hreadyS : LoopReady B c G x [] S := by simpa [hentry] using hready
      have hreserve := reserve_of_ready_guard hreadyS hg hSlen
      have hinfo (tail : Tape L) :
          ∃ e, (F.events (extend tail))[i]? = some e ∧
            BigStepB B preparedRefinedRoundSource
              {S with inp := (List.ofFn tail).map Bool.toNat}
              e.exit e.cost ∧
            chargeAt (F.events (extend tail)) i =
              1 + roundGuard.size + e.cost := by
        have hs := suffix_state F ρ i tail
        have hstate : stateBefore (F.events (extend tail))
            (F.quotient (extend tail)) i =
            {S with inp := (List.ofFn tail).map Bool.toNat} := by
          simpa [S, L, used, extend] using hs.2.1
        have hg' : roundGuard.evalB B
            (stateBefore (F.events (extend tail))
              (F.quotient (extend tail)) i) = some true := by
          simpa [hstate, roundGuard] using hg
        obtain ⟨e, he⟩ := event_of_guard (F.trace (extend tail))
          (F.terminal_guard (extend tail)) i hg'
        obtain ⟨heEntry, _, _, _, heRun⟩ :=
          event_at_data (F.trace (extend tail)) i he
        refine ⟨e, he, ?_, chargeAt_of_event _ _ he⟩
        simpa [heEntry, hstate] using heRun
      choose event hevent hrun hcharge using hinfo
      have hmean := hfixed S L hreadyS hg hSlen hreserve
        (fun tail => (event tail).exit) (fun tail => (event tail).cost) hrun
      have hactive : activeAt (F.events ρ) i = S.vars "acount" := by
        simpa [S, hg] using activeAt_guard (F.trace ρ)
          (F.terminal_guard ρ) i
      have hsum : (∑ tail : Tape L,
          ((chargeAt (F.events (extend tail)) i : ℕ) : ℚ)) =
          (1 + roundGuard.size : ℚ) * 2 ^ L +
            ∑ tail : Tape L, ((event tail).cost : ℚ) := by
        simp_rw [hcharge]
        simp only [Nat.cast_add, Finset.sum_add_distrib]
        simp [card_tape, Nat.cast_pow]
        ring
      have hcoeff :
          ((1 + roundGuard.size +
            (M * (x.length + 1) +
              D * S.vars "acount" * (Nat.clog 2 n + 1)) : ℕ) : ℚ) ≤
          (((M + 1 + roundGuard.size) * (x.length + 1) +
            D * S.vars "acount" * (Nat.clog 2 n + 1) : ℕ) : ℚ) := by
        exact_mod_cast (show 1 + roundGuard.size +
          (M * (x.length + 1) +
            D * S.vars "acount" * (Nat.clog 2 n + 1)) ≤
          (M + 1 + roundGuard.size) * (x.length + 1) +
            D * S.vars "acount" * (Nat.clog 2 n + 1) by
          nlinarith only [Nat.zero_le x.length])
      change (∑ tail : Tape L,
          ((chargeAt (F.events (extend tail)) i : ℕ) : ℚ)) ≤ _
      rw [hsum, hactive]
      have hp := mul_le_mul_of_nonneg_right hcoeff
        (show (0 : ℚ) ≤ 2 ^ L by positivity)
      have hbase : (1 + roundGuard.size : ℚ) * 2 ^ L +
          (∑ tail : Tape L, ((event tail).cost : ℚ)) ≤
          (((1 + roundGuard.size +
            (M * (x.length + 1) +
              D * S.vars "acount" * (Nat.clog 2 n + 1)) : ℕ) : ℚ) *
                2 ^ L) := by
        calc
          _ ≤ (1 + roundGuard.size : ℚ) * 2 ^ L +
                (((M * (x.length + 1) +
                  D * S.vars "acount" * (Nat.clog 2 n + 1) : ℕ) : ℚ) *
                  2 ^ L) := by
                    simpa only [add_comm] using
                      add_le_add_left hmean
                        ((1 + roundGuard.size : ℚ) * 2 ^ L)
          _ = _ := by push_cast; ring
      exact hbase.trans (by simpa [L, hactive] using hp)
    · have hzero (tail : Tape L) :
          chargeAt (F.events (extend tail)) i = 0 := by
        have hs := suffix_state F ρ i tail
        have hstate : stateBefore (F.events (extend tail))
            (F.quotient (extend tail)) i =
            {S with inp := (List.ofFn tail).map Bool.toNat} := by
          simpa [S, L, used, extend] using hs.2.1
        cases he : (F.events (extend tail))[i]? with
        | none => exact chargeAt_zero_of_no_event _ _ he
        | some e =>
            obtain ⟨heEntry, _, hg', _, _⟩ :=
              event_at_data (F.trace (extend tail)) i he
            have hsame : roundGuard.evalB B
                (stateBefore (F.events (extend tail))
                  (F.quotient (extend tail)) i) =
                roundGuard.evalB B S := by
              rw [hstate]
              exact roundGuard_reinput S _
            have hgt : roundGuard.evalB B S = some true := by
              rw [heEntry, hsame] at hg'
              exact hg'
            exact False.elim (hg hgt)
      change (∑ tail : Tape L,
          ((chargeAt (F.events (extend tail)) i : ℕ) : ℚ)) ≤ _
      simp [hzero]
      positivity

end Lax457868Proofs.RefinedPrefixMean
