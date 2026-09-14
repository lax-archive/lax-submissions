/-
One-pebble transducers are two-way transducers.

This is the base case of the induction on the number of pebbles that proves the hard inclusion of
Theorem `thm:pebble-are-for`: a pebble transducer computes a polyregular function.

A one-pebble transducer has two levels.  With an empty stack it is blind (it sees the empty view,
so its behaviour does not depend on the input at all); with one pebble on the stack it is a
two-way head.  A two-way transducer must move its head at every step, while a pebble transducer
also has steps that leave the head in place (printing a letter, popping the pebble, pushing it
again), so the simulation is by *big steps*: all the steps performed at one gap of the input are
collapsed into a single step of the two-way transducer, whose output is the concatenation of the
letters printed by them.  These steps form the run of a *local* machine, whose configurations are
`LSt Q` (the pebble is at the current gap, or the stack is empty) and whose exits are `Exit Q`:

* `Exit.halt` -- the machine terminated;
* `Exit.move d q` -- the pebble moved, so the head of the two-way transducer moves;
* `Exit.rewind q` -- the pebble was popped and pushed again, which puts it back at the gap `0`,
  so the head of the two-way transducer walks back to the left end of the input;
* `Exit.dead` -- the pebble transducer got stuck.

The simulation is faithful on the inputs on which the pebble transducer halts, which is all that
is needed: the halting completion of `RequestProject/PartD/TwoWayTotal.lean` then turns the
two-way transducer into a total regular function that agrees with it there.
-/
import Lax194892Proofs.Source.PartD.PebbleDef
import Lax194892Proofs.Source.PartD.TwoWayTotal
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebOne

variable {A B Q : Type}

/-! ## Counting the steps of a run of a pebble transducer -/

/-- Reachability with the number of steps recorded. -/
inductive ReachesN (M : Pebble A B Q 1) (w : List A) :
    ℕ → PebbleCfg Q → List B → PebbleCfg Q → Prop
  | refl (c : PebbleCfg Q) : ReachesN M w 0 c [] c
  | step {n : ℕ} {c c' c'' : PebbleCfg Q} {o o' : List B} :
      M.stepCfg w c = some (o, c') → ReachesN M w n c' o' c'' →
        ReachesN M w (n + 1) c (o ++ o') c''

lemma exists_reachesN {M : Pebble A B Q 1} {w : List A} {c c' : PebbleCfg Q} {v : List B}
    (h : M.Reaches w c v c') : ∃ n, ReachesN M w n c v c' := by
  induction h with
  | refl c => exact ⟨0, ReachesN.refl c⟩
  | step hstep _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, ReachesN.step hstep hn⟩

lemma reachesN_halt {M : Pebble A B Q 1} {w : List A} {n : ℕ} {v : List B}
    (h : ReachesN M w n PebbleCfg.halt v PebbleCfg.halt) : v = [] := by
  cases h with
  | refl => rfl
  | step hstep _ => exact absurd hstep (by simp [Pebble.stepCfg])

/-! ## The local machine -/

/-- A local state: the pebble is on the stack, at the current gap (`at1`), or the stack is empty
(`at0`). -/
inductive LSt (Q : Type) : Type
  | at1 : Q → LSt Q
  | at0 : Q → LSt Q

/-- The way a local run ends. -/
inductive Exit (Q : Type) : Type
  /-- The pebble transducer is stuck. -/
  | dead : Exit Q
  /-- The pebble transducer terminated. -/
  | halt : Exit Q
  /-- The pebble moved in the given direction. -/
  | move : Bool → Q → Exit Q
  /-- The pebble was popped and pushed again, so it is back at the gap `0`. -/
  | rewind : Q → Exit Q

/-- The result of one step of the local machine. -/
inductive LRes (Q B : Type) : Type
  | cont : List B → LSt Q → LRes Q B
  | fin : List B → Exit Q → LRes Q B

instance [Finite Q] : Finite (LSt Q) :=
  Finite.of_injective (fun s => match s with | LSt.at1 q => Sum.inl q | LSt.at0 q => Sum.inr q)
    (by
      intro s s' h
      cases s <;> cases s' <;> simp_all)

variable (M : Pebble A B Q 1) (l r : Option A)

/-- One step of the local machine at a gap whose adjacent letters are `l` and `r`. -/
def lstep : LSt Q → LRes Q B
  | LSt.at1 q =>
      match M.step q [((l, r), [true])] with
      | (q', PebbleAction.out b) => LRes.cont [b] (LSt.at1 q')
      | (q', PebbleAction.move d) => LRes.fin [] (Exit.move d q')
      | (q', PebbleAction.pop) => LRes.cont [] (LSt.at0 q')
      | (_, PebbleAction.push) => LRes.fin [] Exit.dead
      | (_, PebbleAction.terminate) => LRes.fin [] Exit.halt
  | LSt.at0 q =>
      match M.step q [] with
      | (q', PebbleAction.out b) => LRes.cont [b] (LSt.at0 q')
      | (_, PebbleAction.move _) => LRes.fin [] Exit.dead
      | (q', PebbleAction.push) =>
          match l with
          | none => LRes.cont [] (LSt.at1 q')
          | some _ => LRes.fin [] (Exit.rewind q')
      | (_, PebbleAction.pop) => LRes.fin [] Exit.dead
      | (_, PebbleAction.terminate) => LRes.fin [] Exit.halt

/-- A complete local run: from the local state `s`, the local machine produces the output `o` and
exits with `e`. -/
inductive LocRun : LSt Q → List B → Exit Q → Prop
  | fin {s : LSt Q} {o : List B} {e : Exit Q} : lstep M l r s = LRes.fin o e → LocRun s o e
  | cont {s s' : LSt Q} {o o' : List B} {e : Exit Q} :
      lstep M l r s = LRes.cont o s' → LocRun s' o' e → LocRun s (o ++ o') e

lemma locRun_unique {s : LSt Q} {o o' : List B} {e e' : Exit Q}
    (h : LocRun M l r s o e) (h' : LocRun M l r s o' e') : o = o' ∧ e = e' := by
  induction h generalizing o' e' with
  | fin hf =>
      cases h' with
      | fin hf' =>
          rw [hf] at hf'
          injection hf' with h1 h2
          exact ⟨h1, h2⟩
      | cont hc _ => rw [hf] at hc; exact absurd hc (by simp)
  | cont hc _ ih =>
      cases h' with
      | fin hf' => rw [hc] at hf'; exact absurd hf' (by simp)
      | cont hc' hrest' =>
          rw [hc] at hc'
          have h1 : _ := hc'
          injection h1 with e1 e2
          subst e1
          subst e2
          obtain ⟨rfl, rfl⟩ := ih hrest'
          exact ⟨rfl, rfl⟩

open scoped Classical in
/-- The output and the exit of the local run started in `s`, chosen arbitrarily when there is
none (that is, when the local machine loops for ever). -/
noncomputable def locOut (s : LSt Q) : List B × Exit Q :=
  if h : ∃ p : List B × Exit Q, LocRun M l r s p.1 p.2 then h.choose else ([], Exit.halt)

open scoped Classical in
lemma locOut_eq {s : LSt Q} {o : List B} {e : Exit Q} (h : LocRun M l r s o e) :
    locOut M l r s = (o, e) := by
  have hex : ∃ p : List B × Exit Q, LocRun M l r s p.1 p.2 := ⟨(o, e), h⟩
  rw [locOut, dif_pos hex]
  obtain ⟨h1, h2⟩ := locRun_unique M l r hex.choose_spec h
  exact Prod.ext h1 h2

/-! ## The two-way transducer -/

/-- The action of the two-way transducer at the end of a local run. -/
def exitAct : List B × Exit Q → List B ⊕ ((LSt Q ⊕ Q) × List B × Bool)
  | (o, Exit.dead) => Sum.inl o
  | (o, Exit.halt) => Sum.inl o
  | (o, Exit.move d q) => Sum.inr (Sum.inl (LSt.at1 q), o, d)
  | (o, Exit.rewind q) => Sum.inr (Sum.inr q, o, false)

open scoped Classical in
/-- The two-way transducer simulating a one-pebble transducer: the state `Sum.inl s` runs the
local machine from `s` at the current gap, and the state `Sum.inr q` walks back to the left end of
the input, where the pebble is pushed again in the state `q`. -/
noncomputable def twoWay : TwoWay A B (LSt Q ⊕ Q) where
  init := Sum.inl (LSt.at0 M.init)
  step := fun l st r =>
    match st with
    | Sum.inl s => exitAct (locOut M l r s)
    | Sum.inr q =>
        match l with
        | none => exitAct (locOut M l r (LSt.at1 q))
        | some _ => Sum.inr (Sum.inr q, [], false)

/-! ## The correspondence -/

variable {M} {w : List A}

/-- The letter to the left of the gap `p`. -/
def lLet (w : List A) (p : ℕ) : Option A := if p = 0 then none else w[p - 1]?

/-- The letter to the right of the gap `p`. -/
def rLet (w : List A) (p : ℕ) : Option A := w[p]?

lemma viewOf_single (w : List A) (p : ℕ) :
    viewOf w [p] = [((lLet w p, rLet w p), [true])] := by
  simp [viewOf, lLet, rLet]

lemma lLet_eq_none_iff {p : ℕ} (hp : p ≤ w.length) : lLet w p = none ↔ p = 0 := by
  constructor
  · intro h
    by_contra hne
    rw [lLet, if_neg hne] at h
    have hlt : p - 1 < w.length := by omega
    rw [List.getElem?_eq_getElem hlt] at h
    exact absurd h (by simp)
  · intro h; simp [lLet, h]

lemma take_getLast? {p : ℕ} (hp : p ≤ w.length) : (w.take p).getLast? = lLet w p := by
  cases p with
  | zero => simp [lLet]
  | succ p =>
      have h1 : (w.take (p + 1)).length = p + 1 := by simp; omega
      rw [List.getLast?_eq_getElem?, h1]
      simp only [Nat.add_sub_cancel, lLet, if_neg (Nat.succ_ne_zero p)]
      rw [List.getElem?_take, if_pos (by omega)]

/-- Dropping the last letter of a prefix. -/
lemma dropLast_take_le {p : ℕ} (hp : p ≤ w.length) :
    (w.take p).dropLast = w.take (p - 1) := by
  rcases lt_or_eq_of_le hp with h1 | h1
  · exact List.dropLast_take h1
  · subst h1
    rw [List.take_length, List.dropLast_eq_take]

lemma drop_head? {p : ℕ} : (w.drop p).head? = rLet w p := by
  rw [List.head?_eq_getElem?, List.getElem?_drop]
  simp [rLet]

/-- The configuration of the pebble transducer described by a local state at the gap `p`. -/
def mcfg (s : LSt Q) (p : ℕ) : PebbleCfg Q :=
  match s with
  | LSt.at1 q => PebbleCfg.conf q [p]
  | LSt.at0 q => PebbleCfg.conf q []

/-- The configuration of the pebble transducer that a local run continues in. -/
def contCfg (p : ℕ) : Exit Q → PebbleCfg Q
  | Exit.dead => PebbleCfg.halt
  | Exit.halt => PebbleCfg.halt
  | Exit.move d q => PebbleCfg.conf q [if d then p + 1 else p - 1]
  | Exit.rewind q => PebbleCfg.conf q [0]

/-- The exit of a local run that really occurs in a run of the pebble transducer. -/
def ContOK (w : List A) (p : ℕ) : Exit Q → Prop
  | Exit.dead => False
  | Exit.halt => True
  | Exit.move d _ => if d then p < w.length else 0 < p
  | Exit.rewind _ => 0 < p

/-- **Extraction of a local run.**  A halting run of the pebble transducer starting at the gap `p`
begins with a complete local run at that gap. -/
lemma local_extract : ∀ (n : ℕ) (s : LSt Q) (p : ℕ) (v : List B), p ≤ w.length →
    ReachesN M w n (mcfg s p) v PebbleCfg.halt →
    ∃ (o : List B) (e : Exit Q) (v' : List B) (n' : ℕ),
      LocRun M (lLet w p) (rLet w p) s o e ∧ ContOK w p e ∧ v = o ++ v' ∧
        ReachesN M w n' (contCfg p e) v' PebbleCfg.halt ∧ n' < n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s p v hp hrun
    cases s with
    | at1 q =>
        rw [show mcfg (LSt.at1 q) p = PebbleCfg.conf q [p] from rfl] at hrun
        cases hrun with
        | @step n₀ c c' c'' o o' hstep hrest =>
            rw [Pebble.stepCfg, viewOf_single] at hstep
            rcases hact : M.step q [((lLet w p, rLet w p), [true])] with ⟨q', act⟩
            rw [hact] at hstep
            cases act with
            | out b =>
                simp only at hstep
                injection hstep with hstep
                injection hstep with h1 h2
                subst h1
                subst h2
                obtain ⟨o₂, e, v', n', hloc, hok, hv, hrun', hlt⟩ :=
                  ih n₀ (by omega) (LSt.at1 q') p o' hp hrest
                exact ⟨[b] ++ o₂, e, v', n', LocRun.cont (by rw [lstep, hact]) hloc, hok,
                  by rw [hv]; simp, hrun', by omega⟩
            | move d =>
                cases d with
                | true =>
                    simp only [List.getLast?_singleton, if_true] at hstep
                    by_cases hlt : p < w.length
                    · rw [if_pos hlt] at hstep
                      injection hstep with hstep
                      injection hstep with h1 h2
                      subst h1
                      subst h2
                      refine ⟨[], Exit.move true q', o', n₀, LocRun.fin (by rw [lstep, hact]),
                        by simpa [ContOK] using hlt, by simp, ?_, by omega⟩
                      simpa [contCfg] using hrest
                    · rw [if_neg hlt] at hstep; exact absurd hstep (by simp)
                | false =>
                    simp only [List.getLast?_singleton] at hstep
                    by_cases hpos : 0 < p
                    · rw [if_pos hpos] at hstep
                      injection hstep with hstep
                      injection hstep with h1 h2
                      subst h1
                      subst h2
                      refine ⟨[], Exit.move false q', o', n₀, LocRun.fin (by rw [lstep, hact]),
                        by simpa [ContOK] using hpos, by simp, ?_, by omega⟩
                      simpa [contCfg] using hrest
                    · rw [if_neg hpos] at hstep; exact absurd hstep (by simp)
            | push =>
                simp only at hstep
                rw [if_neg (by simp)] at hstep
                exact absurd hstep (by simp)
            | pop =>
                simp only at hstep
                rw [if_neg (by simp)] at hstep
                injection hstep with hstep
                injection hstep with h1 h2
                subst h1
                subst h2
                obtain ⟨o₂, e, v', n', hloc, hok, hv, hrun', hlt⟩ :=
                  ih n₀ (by omega) (LSt.at0 q') p o' hp (by simpa [mcfg] using hrest)
                exact ⟨o₂, e, v', n', LocRun.cont (by rw [lstep, hact]) hloc, hok,
                  by rw [hv]; simp, hrun', by omega⟩
            | terminate =>
                simp only at hstep
                injection hstep with hstep
                injection hstep with h1 h2
                subst h1
                subst h2
                exact ⟨[], Exit.halt, o', n₀, LocRun.fin (by rw [lstep, hact]), trivial, by simp,
                  by simpa [contCfg] using hrest, by omega⟩
    | at0 q =>
        rw [show mcfg (LSt.at0 q) p = PebbleCfg.conf q [] from rfl] at hrun
        cases hrun with
        | @step n₀ c c' c'' o o' hstep hrest =>
            rw [Pebble.stepCfg, show viewOf w [] = [] from rfl] at hstep
            rcases hact : M.step q ([] : PebbleView A) with ⟨q', act⟩
            rw [hact] at hstep
            cases act with
            | out b =>
                simp only at hstep
                injection hstep with hstep
                injection hstep with h1 h2
                subst h1
                subst h2
                obtain ⟨o₂, e, v', n', hloc, hok, hv, hrun', hlt⟩ :=
                  ih n₀ (by omega) (LSt.at0 q') p o' hp (by simpa [mcfg] using hrest)
                exact ⟨[b] ++ o₂, e, v', n', LocRun.cont (by rw [lstep, hact]) hloc, hok,
                  by rw [hv]; simp, hrun', by omega⟩
            | move d =>
                simp only [List.getLast?_nil] at hstep
                exact absurd hstep (by simp)
            | push =>
                simp only at hstep
                rw [if_pos (by simp)] at hstep
                injection hstep with hstep
                injection hstep with h1 h2
                subst h1
                subst h2
                by_cases hp0 : p = 0
                · subst hp0
                  have hl : lLet w 0 = (none : Option A) := by simp [lLet]
                  obtain ⟨o₂, e, v', n', hloc, hok, hv, hrun', hlt⟩ :=
                    ih n₀ (by omega) (LSt.at1 q') 0 o' hp (by simpa [mcfg] using hrest)
                  refine ⟨o₂, e, v', n', ?_, hok, by rw [hv]; simp, hrun', by omega⟩
                  have hcont : lstep M (lLet w 0) (rLet w 0) (LSt.at0 q)
                      = LRes.cont [] (LSt.at1 q') := by
                    simp only [lstep, hact, hl]
                  simpa using LocRun.cont hcont hloc
                · have hl : lLet w p ≠ none := fun h => hp0 ((lLet_eq_none_iff hp).mp h)
                  refine ⟨[], Exit.rewind q', o', n₀, ?_, by simp [ContOK]; omega, by simp,
                    by simpa [contCfg] using hrest, by omega⟩
                  refine LocRun.fin ?_
                  cases hlv : lLet w p with
                  | none => exact absurd hlv hl
                  | some a => simp only [lstep, hact]
            | pop =>
                simp only at hstep
                simp at hstep
            | terminate =>
                simp only at hstep
                injection hstep with hstep
                injection hstep with h1 h2
                subst h1
                subst h2
                exact ⟨[], Exit.halt, o', n₀, LocRun.fin (by rw [lstep, hact]), trivial, by simp,
                  by simpa [contCfg] using hrest, by omega⟩

/-! ### Elementary steps of the two-way transducer -/

lemma getElem_of_getElem? {p : ℕ} {a : A} (hp : p < w.length) (h : w[p]? = some a) :
    w[p] = a := by
  rw [List.getElem?_eq_getElem hp] at h
  exact Option.some.inj h

lemma drop_eq_cons_of {p : ℕ} {a : A} (hp : p < w.length) (h : w[p]? = some a) :
    w.drop p = a :: w.drop (p + 1) := by
  rw [List.drop_eq_getElem_cons hp, getElem_of_getElem? hp h]

lemma take_append_of {p : ℕ} {a : A} (h : w[p]? = some a) :
    w.take p ++ [a] = w.take (p + 1) := by
  rw [List.take_add_one, h]
  rfl

open scoped Classical in
/-- Walking back to the left end of the input. -/
lemma reaches_rewind (q : Q) : ∀ (p : ℕ), p ≤ w.length →
    (twoWay M).Reaches (Cfg.conf (w.take p) (Sum.inr q) (w.drop p)) []
      (Cfg.conf [] (Sum.inr q) w) := by
  intro p
  induction p with
  | zero => intro _; simpa using TwoWay.Reaches.refl (Cfg.conf ([] : List A) (Sum.inr q) w)
  | succ p ih =>
      intro hp
      have hne : (w.take (p + 1)).getLast? = lLet w (p + 1) := take_getLast? hp
      have hlast : w[p]? = some (w[p]'(by omega)) := List.getElem?_eq_getElem (by omega)
      have ha : (w.take (p + 1)).getLast? = some (w[p]'(by omega)) := by
        rw [hne, lLet, if_neg (by omega)]
        simp
      have hstep : (twoWay M).step (w.take (p + 1)).getLast? (Sum.inr q) (w.drop (p + 1)).head?
          = Sum.inr (Sum.inr q, [], false) := by
        rw [ha]; rfl
      have hdrop : w[p]'(by omega) :: w.drop (p + 1) = w.drop p :=
        (drop_eq_cons_of (by omega) hlast).symm
      have hdl : (w.take (p + 1)).dropLast = w.take p := by
        rw [dropLast_take_le hp]
        simp
      have hcfg : (twoWay M).stepCfg (Cfg.conf (w.take (p + 1)) (Sum.inr q) (w.drop (p + 1)))
          = some ([], Cfg.conf (w.take p) (Sum.inr q) (w.drop p)) := by
        rw [TwoWay.stepCfg_left_some _ ha hstep, hdl, hdrop]
      simpa using TwoWay.Reaches.step hcfg (ih (by omega))

open scoped Classical in
lemma reaches_of_stepCfg_eq {c₁ c₂ : Cfg A (LSt Q ⊕ Q)} {v : List B}
    (h : (twoWay M).stepCfg c₁ = (twoWay M).stepCfg c₂) (hne : c₂ ≠ Cfg.halt)
    (hr : (twoWay M).Reaches c₂ v Cfg.halt) : (twoWay M).Reaches c₁ v Cfg.halt := by
  cases hr with
  | refl c => exact absurd rfl hne
  | step hs hrest => exact TwoWay.Reaches.step (h.trans hs) hrest

open scoped Classical in
/-- **The two-way transducer simulates the one-pebble transducer.** -/
lemma sim_run : ∀ (n : ℕ) (s : LSt Q) (p : ℕ) (v : List B), p ≤ w.length →
    ReachesN M w n (mcfg s p) v PebbleCfg.halt →
    (twoWay M).Reaches (Cfg.conf (w.take p) (Sum.inl s) (w.drop p)) v Cfg.halt := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s p v hp hrun
    obtain ⟨o, e, v', n', hloc, hok, hv, hrun', hlt⟩ := local_extract n s p v hp hrun
    have hstep : (twoWay M).step (w.take p).getLast? (Sum.inl s) (w.drop p).head?
        = exitAct (o, e) := by
      rw [take_getLast? hp, drop_head?]
      rw [show (twoWay M).step (lLet w p) (Sum.inl s) (rLet w p)
          = exitAct (locOut M (lLet w p) (rLet w p) s) from rfl, locOut_eq M _ _ hloc]
    cases e with
    | dead => exact absurd hok (by simp [ContOK])
    | halt =>
        have hv' : v' = [] := reachesN_halt (by simpa [contCfg] using hrun')
        have hcfg : (twoWay M).stepCfg (Cfg.conf (w.take p) (Sum.inl s) (w.drop p))
            = some (o, Cfg.halt) := TwoWay.stepCfg_halt_eq _ (by rw [hstep]; rfl)
        rw [hv, hv']
        simpa using TwoWay.Reaches.step hcfg (TwoWay.Reaches.refl _)
    | move d q' =>
        cases d with
        | true =>
            have hplt : p < w.length := by simpa [ContOK] using hok
            have hlast : w[p]? = some (w[p]'hplt) := List.getElem?_eq_getElem hplt
            have hdrop : w.drop p = w[p]'hplt :: w.drop (p + 1) := drop_eq_cons_of hplt hlast
            have hstep' : (twoWay M).step (w.take p).getLast? (Sum.inl s)
                ((w[p]'hplt) :: w.drop (p + 1)).head?
                = Sum.inr (Sum.inl (LSt.at1 q'), o, true) := by
              rw [← hdrop, hstep]; rfl
            have htake : w.take p ++ [w[p]'hplt] = w.take (p + 1) := take_append_of hlast
            have hcfg : (twoWay M).stepCfg (Cfg.conf (w.take p) (Sum.inl s) (w.drop p))
                = some (o, Cfg.conf (w.take (p + 1)) (Sum.inl (LSt.at1 q')) (w.drop (p + 1))) := by
              rw [hdrop, TwoWay.stepCfg_right_cons _ hstep', htake]
            rw [hv]
            refine TwoWay.Reaches.step hcfg (ih n' hlt (LSt.at1 q') (p + 1) v' (by omega) ?_)
            simpa [contCfg, mcfg] using hrun'
        | false =>
            have hppos : 0 < p := by simpa [ContOK] using hok
            have hplt : p - 1 < w.length := by omega
            have hlast : w[p - 1]? = some (w[p - 1]'hplt) := List.getElem?_eq_getElem hplt
            have ha : (w.take p).getLast? = some (w[p - 1]'hplt) := by
              rw [take_getLast? hp, lLet, if_neg (by omega), hlast]
            have hstep' : (twoWay M).step (w.take p).getLast? (Sum.inl s) (w.drop p).head?
                = Sum.inr (Sum.inl (LSt.at1 q'), o, false) := by rw [hstep]; rfl
            have hdrop : (w[p - 1]'hplt) :: w.drop p = w.drop (p - 1) := by
              have h2 := drop_eq_cons_of hplt hlast
              rw [show p - 1 + 1 = p by omega] at h2
              exact h2.symm
            have hcfg : (twoWay M).stepCfg (Cfg.conf (w.take p) (Sum.inl s) (w.drop p))
                = some (o, Cfg.conf (w.take (p - 1)) (Sum.inl (LSt.at1 q')) (w.drop (p - 1))) := by
              rw [TwoWay.stepCfg_left_some _ ha hstep', hdrop, dropLast_take_le hp]
            rw [hv]
            refine TwoWay.Reaches.step hcfg (ih n' hlt (LSt.at1 q') (p - 1) v' (by omega) ?_)
            simpa [contCfg, mcfg] using hrun'
    | rewind q' =>
        have hppos : 0 < p := by simpa [ContOK] using hok
        have hplt : p - 1 < w.length := by omega
        have hlast : w[p - 1]? = some (w[p - 1]'hplt) := List.getElem?_eq_getElem hplt
        have ha : (w.take p).getLast? = some (w[p - 1]'hplt) := by
          rw [take_getLast? hp, lLet, if_neg (by omega), hlast]
        have hstep' : (twoWay M).step (w.take p).getLast? (Sum.inl s) (w.drop p).head?
            = Sum.inr (Sum.inr q', o, false) := by rw [hstep]; rfl
        have hdrop : (w[p - 1]'hplt) :: w.drop p = w.drop (p - 1) := by
          have h2 := drop_eq_cons_of hplt hlast
          rw [show p - 1 + 1 = p by omega] at h2
          exact h2.symm
        have hcfg : (twoWay M).stepCfg (Cfg.conf (w.take p) (Sum.inl s) (w.drop p))
            = some (o, Cfg.conf (w.take (p - 1)) (Sum.inr q') (w.drop (p - 1))) := by
          rw [TwoWay.stepCfg_left_some _ ha hstep', hdrop, dropLast_take_le hp]
        have hwalk := reaches_rewind (M := M) (w := w) q' (p - 1) (by omega)
        have hIH := ih n' hlt (LSt.at1 q') 0 v' (by omega) (by simpa [contCfg, mcfg] using hrun')
        have hIH' : (twoWay M).Reaches (Cfg.conf [] (Sum.inl (LSt.at1 q')) w) v' Cfg.halt := by
          simpa using hIH
        have hsame : (twoWay M).stepCfg (Cfg.conf [] (Sum.inr q') w)
            = (twoWay M).stepCfg (Cfg.conf [] (Sum.inl (LSt.at1 q')) w) := by
          have hs : (twoWay M).step ([] : List A).getLast? (Sum.inr q') w.head?
              = (twoWay M).step ([] : List A).getLast? (Sum.inl (LSt.at1 q')) w.head? := rfl
          simp only [TwoWay.stepCfg, hs]
        have hfin : (twoWay M).Reaches (Cfg.conf [] (Sum.inr q') w) v' Cfg.halt :=
          reaches_of_stepCfg_eq hsame (by simp) hIH'
        rw [hv]
        simpa using TwoWay.Reaches.step hcfg (hwalk.trans hfin)

open scoped Classical in
/-- **The two-way transducer computes what the one-pebble transducer computes.** -/
theorem twoWay_computes {v : List B} (h : M.Computes w v) : (twoWay M).Computes w v := by
  obtain ⟨n, hn⟩ := exists_reachesN h
  have hsim := sim_run (M := M) (w := w) n (LSt.at0 M.init) 0 v (by omega)
    (by simpa [mcfg] using hn)
  simpa [TwoWay.Computes, twoWay] using hsim

open scoped Classical in
/-- **A one-pebble transducer computes a regular function**, on the inputs on which it halts. -/
theorem exists_regularFun_of_pebble_one [Finite A] [Finite B] [Finite Q] (M : Pebble A B Q 1) :
    ∃ F : List A → List B, IsRegularFun F ∧ ∀ w v, M.Computes w v → F w = v := by
  classical
  obtain ⟨F, hF, hFs⟩ := TwoWay.exists_regularFun_of_twoWay (twoWay M)
  exact ⟨F, hF, fun w v hv => hFs w v (twoWay_computes hv)⟩

end PebOne

end Lax194892Proofs.Transducers
