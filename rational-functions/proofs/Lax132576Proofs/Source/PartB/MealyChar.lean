/-
The machine independent characterisation of Mealy machines (Theorem `thm:mealy-machine-independent`)
from *Transducers* (M. Bojanczyk).

A function is computed by a Mealy machine if and only if it is continuous,
prefix preserving and length preserving.  The interesting implication builds a
Mealy machine whose states are the Myhill-Nerode classes of the languages
`{w | the last letter of f w is b}`, which are regular by continuity.
-/
import Lax765601Proofs.Source.PartA.MealyBasic
import Lax132576Proofs.Source.Common.RegularAux
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

variable {A B : Type}

/-! ## Elementary consequences of prefix and length preservation -/

/-- If `f` is prefix preserving and length preserving, then extending the input
by one letter extends the output by exactly one letter. -/
lemma exists_step_letter {f : List A → List B} (hpre : PrefixPreserving f)
    (hlen : LengthPreserving f) (w : List A) (a : A) :
    ∃ b : B, f (w ++ [a]) = f w ++ [b] := by
  have hprefix : f w <+: f (w ++ [a]) := hpre w (w ++ [a]) (List.prefix_append w [a])
  obtain ⟨t, ht⟩ := hprefix
  have hlen_eq : t.length = 1 := by
    have : (f w ++ t).length = (f w).length + 1 := by rw [ht, hlen, hlen]; simp
    simp at this
    exact this
  match t with
  | [] => simp at hlen_eq
  | b :: [] => exact ⟨b, by rw [ht]⟩
  | _ :: _ :: _ => simp at hlen_eq

/-! ## The Myhill-Nerode states of `f` -/

/-- The language of input strings on which the last output letter is `b`. -/
def lastPre (f : List A → List B) (b : B) : Language A := {w | (f w).getLast? = some b}

/-- The state of the canonical machine after reading `w`: the family of left
quotients of the languages `lastPre f b`. -/
def nerodeState (f : List A → List B) (w : List A) : B → Language A :=
  fun b => (lastPre f b).leftQuotient w

lemma nerodeState_append (f : List A → List B) (w : List A) (a : A) :
    nerodeState f (w ++ [a]) = fun b => (nerodeState f w b).leftQuotient [a] := by
  funext b
  simp [nerodeState, lastPre, Language.leftQuotient]
  ext y
  rfl

lemma mem_nerodeState {f : List A → List B} {w : List A} {u : List A} {b : B} :
    u ∈ nerodeState f w b ↔ (f (w ++ u)).getLast? = some b := Iff.rfl

/-- Continuity makes each language `lastPre f b` regular. -/
lemma lastPre_isRegular [Finite B] {f : List A → List B} (hf : Continuous f) (b : B) :
    (lastPre f b).IsRegular := by
  have h : lastPre f b = {w | f w ∈ lastLang b} := by ext; rfl
  rw [h]
  exact hf _ (lastLang_isRegular b)

/-- Continuity makes the set of states finite. -/
lemma nerodeState_range_finite [Finite B] {f : List A → List B} (hf : Continuous f) :
    (Set.range (nerodeState f)).Finite := by
  -- Each lastPre f b is regular
  have hreg : ∀ b, (lastPre f b).IsRegular := fun b => lastPre_isRegular hf b
  -- For a regular language, the set of left quotients is finite
  have hfin : ∀ b : B, (Set.range (fun w => (lastPre f b).leftQuotient w)).Finite := by
    intro b
    exact Language.IsRegular.finite_range_leftQuotient (hreg b)
  -- The range of nerodeState f is a subset of a finite product
  apply Set.Finite.subset (Set.Finite.pi (fun b => hfin b))
  intro s hs
  obtain ⟨w, rfl⟩ := hs
  exact fun b _ => ⟨w, rfl⟩

open Classical in
/-- The canonical Mealy machine of a prefix and length preserving function. -/
noncomputable def nerodeMealy [Inhabited B] (f : List A → List B) :
    Mealy A B (Set.range (nerodeState f)) where
  init := ⟨nerodeState f [], ⟨[], rfl⟩⟩
  step := fun s a =>
    (⟨fun b => (s.val b).leftQuotient [a], by
        obtain ⟨w, hw⟩ := s.2
        refine ⟨w ++ [a], ?_⟩
        rw [nerodeState_append, hw]⟩,
      if h : ∃ b, [a] ∈ s.val b then h.choose else default)

lemma nerodeMealy_trans [Inhabited B] (f : List A → List B) (w : List A) :
    ((nerodeMealy f).trans w (nerodeMealy f).init).val = nerodeState f w := by
  have h : ∀ u : List A, ∀ (q : Set.range (nerodeState f)) (hu : q.val = nerodeState f u),
      ((nerodeMealy f).trans w q).val = nerodeState f (u ++ w) := by
    induction w with
    | nil =>
      intro u q hu
      simp [Mealy.trans_nil, hu]
    | cons a w ih =>
      intro u q hu
      rw [Mealy.trans_cons]
      -- Need to show letterTrans a q = nerodeState f (u ++ [a])
      have hmem : nerodeState f (u ++ [a]) ∈ Set.range (nerodeState f) := ⟨u ++ [a], rfl⟩
      have hstep : (nerodeMealy f).letterTrans a q = ⟨nerodeState f (u ++ [a]), hmem⟩ := by
        simp [Mealy.letterTrans, nerodeMealy, nerodeState_append]
        rw [hu]
      rw [hstep]
      have := ih (u ++ [a]) ⟨nerodeState f (u ++ [a]), hmem⟩ rfl
      simp at this ⊢
      exact this
  exact h [] (nerodeMealy f).init (by simp [nerodeMealy])

lemma nerodeMealy_eval [Inhabited B] {f : List A → List B} (hpre : PrefixPreserving f)
    (hlen : LengthPreserving f) : (nerodeMealy f).eval = f := by
  apply funext
  intro w
  -- Key lemma: run from state nerodeState f w' on input w gives the suffix of f (w' ++ w)
  -- after f w' (which has the same length as w)
  have hrun : ∀ u v : List A,
      (nerodeMealy f).run ⟨nerodeState f u, ⟨u, rfl⟩⟩ v = (f (u ++ v)).drop (f u).length := by
    intro u v
    induction v generalizing u with
    | nil =>
      rw [Mealy.run_nil]
      simp [List.drop_length]
    | cons a v ih =>
      rw [Mealy.run_cons]
      -- Get the step letter b such that f (u ++ [a]) = f u ++ [b]
      obtain ⟨b, hb⟩ := exists_step_letter hpre hlen u a
      -- The output letter is b
      have hstate : ((nerodeMealy f).step ⟨nerodeState f u, ⟨u, rfl⟩⟩ a).1 = ⟨nerodeState f (u ++ [a]), ⟨u ++ [a], rfl⟩⟩ := by
        simp [nerodeMealy, nerodeState_append]
      have hout : ((nerodeMealy f).step ⟨nerodeState f u, ⟨u, rfl⟩⟩ a).2 = b := by
        simp [nerodeMealy]
        -- Need to show: if h : ∃ b', [a] ∈ nerodeState f u b' then h.choose else default = b
        have hbmem : [a] ∈ nerodeState f u b := by
          rw [mem_nerodeState]
          simp [hb]
        -- The existential is true
        have hex : ∃ b, [a] ∈ nerodeState f u b := ⟨b, hbmem⟩
        -- h.choose satisfies the property
        split
        · rename_i h
          have hchoose := h.choose_spec
          rw [mem_nerodeState] at hchoose hbmem
          exact Option.some.inj (hchoose.symm.trans hbmem)
        · exact absurd hex ‹¬∃ b, [a] ∈ nerodeState f u b›
      rw [hstate, hout, ih]
      -- Now show: b :: drop (f (u ++ [a])).length (f (u ++ [a] ++ v)) = drop (f u).length (f (u ++ a :: v))
      have heqv : u ++ [a] ++ v = u ++ a :: v := by simp [List.append_assoc]
      rw [heqv]
      -- Use hb : f (u ++ [a]) = f u ++ [b]
      have hlen_ub : (f (u ++ [a])).length = (f u).length + 1 := by
        rw [hb]; simp
      rw [hlen_ub]
      -- Need prefix preservation: f (u ++ [a]) <+: f (u ++ a :: v)
      have hpre2 : f (u ++ [a]) <+: f (u ++ a :: v) :=
        hpre (u ++ [a]) (u ++ a :: v) (by simp)
      obtain ⟨t, ht⟩ := hpre2
      rw [hb] at ht
      rw [← ht]
      simp [List.drop_append]
  have hinit : (nerodeMealy f).init = ⟨nerodeState f [], ⟨[], rfl⟩⟩ := rfl
  rw [Mealy.eval, hinit]
  simp [hrun]
  have : (f []).length = 0 := hlen []
  simp [this]

/-- If the output alphabet is empty, a length preserving function is computed by
a one state Mealy machine (the input alphabet must then be empty as well). -/
lemma isMealy_of_isEmpty_output [IsEmpty B] {f : List A → List B}
    (hlen : LengthPreserving f) : IsMealy f := by
  have h : ∀ a : A, False := fun a => by
    have := hlen [a]
    have heq : f [a] = [] := by
      rcases hf : f [a] with ⟨⟩ | ⟨b, _⟩
      · rfl
      · exact isEmptyElim b
    simp [heq] at this
  let step : Unit → A → Unit × B := fun _ a => ((), False.elim (h a))
  let M : Mealy A B Unit := ⟨(), step⟩
  haveI : IsEmpty A := ⟨h⟩
  exact ⟨Unit, inferInstance, M, funext fun w => by
    rcases w with ⟨⟩ | ⟨a, as⟩
    · -- w = [], show f [] = M.eval []
      simp [Mealy.eval]
      -- f [] = [] since B is empty
      rcases hf : f [] with ⟨⟩ | ⟨b, _⟩
      · rfl
      · exact isEmptyElim b
    · exact isEmptyElim a⟩

/-- **Theorem `thm:mealy-machine-independent`.**  A function is computed by a Mealy machine if and
only if it is continuous, prefix preserving and length preserving. -/
theorem isMealy_iff_aux [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ (Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f) := by
  constructor
  · intro hf
    obtain ⟨Q, hQ, M, rfl⟩ := hf
    refine ⟨?_, fun w v hv => Mealy.eval_prefix M hv, fun w => Mealy.eval_length M w⟩
    intro L hL
    obtain ⟨σ, hσ, D, hD⟩ := hL
    refine ⟨Q × σ, Fintype.ofFinite _, M.dfaComp D, ?_⟩
    rw [M.dfaComp_accepts, ← hD]
  · intro ⟨hcont, hpre, hlen⟩
    by_cases hB : Nonempty B
    · letI : Inhabited B := ⟨hB.some⟩
      exact ⟨Set.range (nerodeState f), nerodeState_range_finite hcont, nerodeMealy f,
        nerodeMealy_eval hpre hlen⟩
    · haveI : IsEmpty B := not_nonempty_iff.mp hB
      exact isMealy_of_isEmpty_output hlen

end Lax132576Proofs.Transducers
