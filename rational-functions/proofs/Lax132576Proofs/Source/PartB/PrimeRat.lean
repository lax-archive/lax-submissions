/-
The prime rational functions of Theorem `thm:rational-primes` and the easy implication of that
theorem: every composition of prime rational functions is rational.

The four kinds of prime rational functions are

* prime Mealy machines,
* their right-to-left variants,
* string homomorphisms,
* the function `w ↦ w#` appending a fresh separator.

Each of them is rational: Mealy machines and homomorphisms are read directly as
nfas with output, the separator needs one ε-transition, and a right-to-left
Mealy machine is a bimachine whose prefix automaton is trivial, hence rational
by `rationalFun_of_isBimachine`.
-/
import Lax132576Proofs.Source.PartB.RatBimach
import Lax132576Proofs.Source.PartB.RatComp
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-- The family of **prime rational functions** (Theorem `thm:rational-primes`): prime Mealy
machines, their right-to-left variants, string homomorphisms, and the function
`w ↦ w#` appending a fresh separator. -/
def PrimeRationalFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  PrimeMealyFam A B f ∨
  PrimeMealyFam A B (fun w => (f w.reverse).reverse) ∨
  (∃ φ : A → List B, f = homOf φ) ∨
  (∃ e : Option A ≃ B, f = fun w => w.map (fun a => e (some a)) ++ [e none])

namespace PrimeRat

open LabAut NFAO

/-! ### Mealy machines are rational -/

namespace MealyRat

variable {A B Q : Type} [Finite A] [Finite Q] (M : Mealy A B Q)

/-- The nfa with output that reads a Mealy machine as a transducer. -/
def aut : NFAO A B Q where
  init := {M.init}
  final := Set.univ
  δ := (fun x : Q × A => (x.1, [x.2], [(M.step x.1 x.2).2], (M.step x.1 x.2).1)) '' Set.univ
  δ_finite := Set.Finite.image _ Set.finite_univ

lemma delta_mem {z : Q × List A × List B × Q} :
    z ∈ (aut M).δ ↔ ∃ q a, z = (q, [a], [(M.step q a).2], (M.step q a).1) := by
  constructor
  · rintro ⟨⟨q, a⟩, -, rfl⟩; exact ⟨q, a, rfl⟩
  · rintro ⟨q, a, rfl⟩; exact ⟨(q, a), Set.mem_univ _, rfl⟩

lemma relFrom_run (q : Q) (w : List A) : (aut M).relFrom q w (M.run q w) (M.trans w q) := by
  induction w generalizing q with
  | nil => exact NFAO.relFrom_nil _ _
  | cons a w ih =>
      have ht : (q, [a], [(M.step q a).2], (M.step q a).1) ∈ (aut M).δ :=
        (delta_mem M).mpr ⟨q, a, rfl⟩
      have := NFAO.relFrom_step ht (ih (M.step q a).1)
      simpa [Mealy.trans_cons, Mealy.letterTrans] using this

lemma relFrom_eq {q p : Q} {w : List A} {v : List B} (h : (aut M).relFrom q w v p) :
    v = M.run q w ∧ p = M.trans w q := by
  refine NFAO.relFrom_induction (M := aut M)
    (motive := fun q w v => v = M.run q w ∧ p = M.trans w q) ⟨rfl, rfl⟩ ?_ h
  rintro q q' u x w v ht - ⟨hv, hp⟩
  obtain ⟨q₀, a, heq⟩ := (delta_mem M).mp ht
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  refine ⟨by simp [hv], ?_⟩
  rw [hp]
  simp [Mealy.trans_cons, Mealy.letterTrans]

theorem aut_rel (w : List A) (v : List B) : (aut M).rel w v ↔ v = M.eval w := by
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨q, hq, p, -, hrel⟩
    have hq' : q = M.init := hq
    subst hq'
    exact (relFrom_eq M hrel).1
  · rintro rfl
    exact ⟨M.init, rfl, M.trans w M.init, Set.mem_univ _, relFrom_run M M.init w⟩

end MealyRat

theorem rationalFun_of_isMealy {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsMealy f) : IsRationalFun f := by
  obtain ⟨Q, hQ, M, rfl⟩ := hf
  exact ⟨Q, hQ, MealyRat.aut M, fun w v => (MealyRat.aut_rel M w v).symm⟩

/-! ### Right-to-left Mealy machines are rational -/

namespace RevMealy

variable {A B Q : Type} (M : Mealy A B Q)

/-- The bimachine computing the right-to-left variant of a Mealy machine: the
prefix automaton is trivial and the suffix automaton is the Mealy machine, which
remembers the letter it has just produced. -/
def bm : Bimachine A B Unit (Q × Option B) where
  prefixInit := ()
  prefixStep := fun _ _ => ()
  suffixInit := (M.init, none)
  suffixStep := fun s a => ((M.step s.1 a).1, some (M.step s.1 a).2)
  out := fun _ s => match s.2 with | none => [] | some b => [b]

/-- The state of the suffix automaton after the reverse of `z`. -/
def sState (z : List A) : Q × Option B :=
  strTrans (bm M).suffixStep z.reverse (bm M).suffixInit

lemma sState_nil : sState M [] = (M.init, none) := rfl

lemma sState_cons (a : A) (z : List A) :
    sState M (a :: z) = (bm M).suffixStep (sState M z) a := by
  simp [sState, strTrans, List.reverse_cons]

lemma sState_fst (z : List A) : (sState M z).1 = M.trans z.reverse M.init := by
  induction z with
  | nil => rfl
  | cons a z ih =>
      rw [sState_cons, List.reverse_cons, Mealy.trans_append]
      simp [bm, ih, Mealy.trans, strTrans, Mealy.transFun]

lemma evalFrom_eq (w : List A) :
    (bm M).evalFrom () w = (M.eval w.reverse).reverse := by
  induction w with
  | nil => simp [Bimachine.evalFrom_nil, bm, Mealy.eval]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons, ih]
      have hs : strTrans (bm M).suffixStep (a :: w).reverse (bm M).suffixInit =
          (bm M).suffixStep (sState M w) a := sState_cons M a w
      rw [hs]
      have hout : (bm M).out () ((bm M).suffixStep (sState M w) a) =
          [(M.step (M.trans w.reverse M.init) a).2] := by
        simp [bm, sState_fst M w]
      rw [hout, List.reverse_cons, Mealy.eval_append]
      simp

theorem bm_eval : (bm M).eval = fun w => (M.eval w.reverse).reverse := by
  funext w
  rw [Bimachine.eval_eq_evalFrom]
  exact evalFrom_eq M w

end RevMealy

theorem rationalFun_of_revMealy {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsMealy (fun w => (f w.reverse).reverse)) : IsRationalFun f := by
  obtain ⟨Q, hQ, M, hM⟩ := hf
  have hfeq : f = fun w => (M.eval w.reverse).reverse := by
    funext w
    have h2 := congrFun hM w.reverse
    simp only [List.reverse_reverse] at h2
    rw [h2]
    simp
  refine rationalFun_of_isBimachine ⟨Unit, Q × Option B, inferInstance, inferInstance,
    RevMealy.bm M, ?_⟩
  rw [RevMealy.bm_eval, ← hfeq]

/-! ### Homomorphisms are rational -/

namespace HomRat

variable {A B : Type} [Finite A] (φ : A → List B)

/-- The one-state nfa with output computing a homomorphism. -/
def aut : NFAO A B Unit where
  init := Set.univ
  final := Set.univ
  δ := (fun a : A => ((), [a], φ a, ())) '' Set.univ
  δ_finite := Set.Finite.image _ Set.finite_univ

lemma delta_mem {z : Unit × List A × List B × Unit} :
    z ∈ (aut φ).δ ↔ ∃ a, z = ((), [a], φ a, ()) := by
  constructor
  · rintro ⟨a, -, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, Set.mem_univ _, rfl⟩

lemma relFrom_hom (w : List A) : (aut φ).relFrom () w (homOf φ w) () := by
  induction w with
  | nil => exact NFAO.relFrom_nil _ _
  | cons a w ih =>
      have ht : ((), [a], φ a, ()) ∈ (aut φ).δ := (delta_mem φ).mpr ⟨a, rfl⟩
      have := NFAO.relFrom_step ht ih
      simpa [homOf] using this

lemma relFrom_eq {w : List A} {v : List B} (h : (aut φ).relFrom () w v ()) :
    v = homOf φ w := by
  refine NFAO.relFrom_induction (M := aut φ) (motive := fun _ w v => v = homOf φ w) rfl ?_ h
  rintro q q' u x w v ht - hv
  obtain ⟨a, heq⟩ := (delta_mem φ).mp ht
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl, rfl, -⟩ := heq
  simp [hv, homOf]

theorem aut_rel (w : List A) (v : List B) : (aut φ).rel w v ↔ v = homOf φ w := by
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨q, -, p, -, hrel⟩
    cases q; cases p
    exact relFrom_eq φ hrel
  · rintro rfl
    exact ⟨(), Set.mem_univ _, (), Set.mem_univ _, relFrom_hom φ w⟩

end HomRat

theorem rationalFun_homOf {A B : Type} [Finite A] (φ : A → List B) :
    IsRationalFun (homOf φ) :=
  ⟨Unit, inferInstance, HomRat.aut φ, fun w v => (HomRat.aut_rel φ w v).symm⟩

/-! ### The separator function is rational -/

namespace SepRat

variable {A B : Type} [Finite A] (e : Option A ≃ B)

/-- The two-state nfa with output computing `w ↦ w#`. -/
def aut : NFAO A B Bool where
  init := {false}
  final := {true}
  δ := (fun a : A => (false, [a], [e (some a)], false)) '' Set.univ ∪
    {(false, [], [e none], true)}
  δ_finite := Set.Finite.union (Set.Finite.image _ Set.finite_univ) (Set.finite_singleton _)

lemma delta_mem {z : Bool × List A × List B × Bool} :
    z ∈ (aut e).δ ↔ (∃ a, z = (false, [a], [e (some a)], false)) ∨
      z = (false, [], [e none], true) := by
  constructor
  · rintro (⟨a, -, rfl⟩ | hz)
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr hz
  · rintro (⟨a, rfl⟩ | rfl)
    · exact Or.inl ⟨a, Set.mem_univ _, rfl⟩
    · exact Or.inr rfl

/-- The function computed by the automaton. -/
def sep (w : List A) : List B := w.map (fun a => e (some a)) ++ [e none]

lemma relFrom_sep (w : List A) : (aut e).relFrom false w (sep e w) true := by
  induction w with
  | nil =>
      have ht : (false, ([] : List A), [e none], true) ∈ (aut e).δ :=
        (delta_mem e).mpr (Or.inr rfl)
      simpa [sep] using NFAO.relFrom_single ht
  | cons a w ih =>
      have ht : (false, [a], [e (some a)], false) ∈ (aut e).δ :=
        (delta_mem e).mpr (Or.inl ⟨a, rfl⟩)
      have := NFAO.relFrom_step ht ih
      simpa [sep] using this

lemma relFrom_eq {q : Bool} {w : List A} {v : List B} (h : (aut e).relFrom q w v true) :
    (q = false → v = sep e w) ∧ (q = true → w = [] ∧ v = []) := by
  refine NFAO.relFrom_induction (M := aut e)
    (motive := fun q w v => (q = false → v = sep e w) ∧ (q = true → w = [] ∧ v = []))
    ⟨by simp, fun _ => ⟨rfl, rfl⟩⟩ ?_ h
  rintro q q' u x w v ht - ih
  rcases (delta_mem e).mp ht with ⟨a, heq⟩ | heq
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    exact ⟨fun _ => by simp [sep, ih.1 rfl], by simp⟩
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
    obtain ⟨hw, hv⟩ := ih.2 rfl
    exact ⟨fun _ => by simp [sep, hw, hv], by simp⟩

theorem aut_rel (w : List A) (v : List B) : (aut e).rel w v ↔ v = sep e w := by
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨q, hq, p, hp, hrel⟩
    have hq' : q = false := hq
    have hp' : p = true := hp
    subst hq'; subst hp'
    exact (relFrom_eq e hrel).1 rfl
  · rintro rfl
    exact ⟨false, rfl, true, rfl, relFrom_sep e w⟩

end SepRat

theorem rationalFun_sep {A B : Type} [Finite A] (e : Option A ≃ B) :
    IsRationalFun (fun w : List A => w.map (fun a => e (some a)) ++ [e none]) :=
  ⟨Bool, inferInstance, SepRat.aut e, fun w v => (SepRat.aut_rel e w v).symm⟩

/-! ### Closure under composition -/

theorem rationalFun_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsRationalFun f) (hg : IsRationalFun g) : IsRationalFun (g ∘ f) := by
  have h := rationalRel_comp_aux hf hg
  obtain ⟨Q, hQ, M, hM⟩ := h
  refine ⟨Q, hQ, M, fun w v => ?_⟩
  rw [← hM]
  constructor
  · rintro rfl; exact ⟨f w, rfl, rfl⟩
  · rintro ⟨u, rfl, rfl⟩; rfl

theorem rationalFun_id {A : Type} [Finite A] : IsRationalFun (id : List A → List A) := by
  have : (id : List A → List A) = homOf (fun a => [a]) := by
    funext w
    induction w with
    | nil => rfl
    | cons a w ih => simp [homOf] at ih ⊢; exact ih
  rw [this]
  exact rationalFun_homOf _

/-! ### Prime rational functions are rational -/

theorem rationalFun_of_prime {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : PrimeRationalFam A B f) : IsRationalFun f := by
  rcases hf with hm | hrm | ⟨φ, rfl⟩ | ⟨e, rfl⟩
  · refine rationalFun_of_isMealy ?_
    rcases hm with ⟨Q, hQ, M, hM, -⟩ | ⟨Q, hQ, M, hM, -⟩ <;> exact ⟨Q, hQ, M, hM⟩
  · refine rationalFun_of_revMealy ?_
    rcases hrm with ⟨Q, hQ, M, hM, -⟩ | ⟨Q, hQ, M, hM, -⟩ <;> exact ⟨Q, hQ, M, hM⟩
  · exact rationalFun_homOf φ
  · exact rationalFun_sep e

theorem rationalFun_of_compClosure :
    ∀ {A B : Type} {f : List A → List B}, CompClosure PrimeRationalFam A B f →
      Finite A → Finite B → IsRationalFun f := by
  intro A B f h
  induction h with
  | base hf => intro hA hB; exact rationalFun_of_prime hf
  | id A => intro hA _; exact rationalFun_id
  | @comp A B C hB f g hf hg ihf ihg =>
      intro hA hC
      exact rationalFun_comp (ihf hA hB) (ihg hB hC)

end PrimeRat

end Lax132576Proofs.Transducers
