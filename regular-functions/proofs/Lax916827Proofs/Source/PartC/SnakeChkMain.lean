/-
**Stage 1 of the induction step of the book's snake lemma: the regular language
of correct annotations.**

The book's first stage marks the record-breaking columns by *guessing* them with
a nondeterministic automaton with output and *checking* the guess.  This file
assembles the checking language out of

* `Transducers.TwoWay.Chk.ChkLang`, the annotations that describe a chain of
  pieces of the run, which is sound (`Transducers.TwoWay.Chk.chk_sound`) and
  complete (`Transducers.TwoWay.Chk.chk_complete`) on the *good* inputs, and
* the *flat* annotations, which carry no block boundary at all and are used on
  the inputs on which the width-`K` output function is empty.

The result is `Transducers.TwoWay.exists_regular_snakeLang`: a regular language
of annotations, over an alphabet of its own, all of whose members are correct
markings and which contains an annotation of every input.
-/
import Lax916827Proofs.Source.PartC.SnakeChkGeom
import Lax916827Proofs.Source.PartC.SnakeChkComp
import Lax132576Proofs.Source.PartB.GuessCheck
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open RegPair Chk

variable {A B Q : Type}

/-! ## Flat annotations -/

namespace Chk

variable {S : Type} {K : ℕ}

/-- A word all of whose letters carry no block boundary. -/
def flatB (u : List (Gam A Q S K)) : Bool :=
  u.foldl (fun s c => s || sb c || sa c) false

lemma foldl_or_eq_false_iff {Γ : Type} (f : Γ → Bool) :
    ∀ (u : List Γ) (s : Bool),
      u.foldl (fun s c => s || f c) s = false ↔ s = false ∧ ∀ c ∈ u, f c = false := by
  intro u
  induction u with
  | nil => intro s; simp
  | cons c u ih =>
      intro s
      rw [List.foldl_cons, ih]
      constructor
      · rintro ⟨h1, h2⟩
        have hs : s = false := by
          cases s <;> simp_all
        have hc : f c = false := by
          cases hfc : f c <;> simp_all
        exact ⟨hs, by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hc
          · exact h2 x hx⟩
      · rintro ⟨rfl, h2⟩
        refine ⟨by simpa using h2 c (by simp), fun x hx => h2 x (by simp [hx])⟩

lemma flatB_eq_false_iff (u : List (Gam A Q S K)) :
    flatB u = false ↔ ∀ c ∈ u, sb c = false ∧ sa c = false := by
  have h := foldl_or_eq_false_iff (fun c : Gam A Q S K => sb c || sa c) u false
  have hfun : (fun (s : Bool) (c : Gam A Q S K) => s || sb c || sa c)
      = (fun (s : Bool) (c : Gam A Q S K) => s || (sb c || sa c)) := by
    funext s c; rw [Bool.or_assoc]
  rw [flatB, hfun, h]
  simp only [true_and, Bool.or_eq_false_iff]

/-- The flat annotations: those with no block boundary. -/
def FlatLang : Language (Gam A Q S K) := {u | flatB u = false}

lemma isRegular_flatLang [Finite A] [Finite Q] [Finite S] {K : ℕ} :
    (FlatLang (A := A) (Q := Q) (S := S) (K := K)).IsRegular := by
  classical
  have h := RegAut.isRegular_foldl (Γ := Gam A Q S K) (S := Bool)
    (fun s c => s || sb c || sa c) false {b | b = false}
  exact h

/-- A flat annotation produces a string without separators. -/
lemma homOf_snakeOutLet_of_flat {K : ℕ} {u : List (Gam A Q S K)}
    (hu : ∀ c ∈ u, sb c = false ∧ sa c = false) :
    homOf (snakeOutLet K) u = (u.map (fun c => (lt c, slotsOf c))).map some := by
  induction u with
  | nil => rfl
  | cons c u ih =>
      have hc := hu c (by simp)
      rw [homOf, List.map_cons, List.flatten_cons, ← homOf,
        ih (fun x hx => hu x (by simp [hx])), snakeOutLet, hc.1, hc.2]
      simp

end Chk

/-! ## The language of correct annotations -/

/-- **Stage 1 of the induction step of the snake lemma**, in the shape in which
the book states it: the marking is *guessed* by a nondeterministic automaton
with output and *checked*, so that what has to be produced is the language of
the checking automaton -- a regular language of correctly annotated inputs which
contains an annotation of every input -- and not a function.

The annotation is letter to letter: an annotated letter is a letter of the
input together with the block boundary bits, the window flags, the parameters of
the window transducer and the state of the automaton checking the window
condition, for each of the `2K+1` piece slots and each of the two sides of a
block boundary (`Transducers.TwoWay.Chk.Gam`).  The separators are inserted
afterwards by the homomorphism `Transducers.TwoWay.Chk.snakeOutLet`. -/
theorem exists_regular_snakeLang [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) {K : ℕ}
    (hK : 2 ≤ K) :
    ∃ (Γ : Type) (_ : Finite Γ) (inH : Γ → List A)
      (outH : Γ → List (Option (SnakeLet A Q (2 * (2 * K + 1))))) (L : Language Γ),
      L.IsRegular ∧ (∀ u ∈ L, SnakeRel M K (homOf inH u) (homOf outH u)) ∧
      (∀ w : List A, ∃ u ∈ L, homOf inH u = w) := by
  classical
  obtain ⟨S, hS, stp, ini, acc, hacc⟩ :=
    exists_uniform_dfa (fun p : PieceParam A Q => WinCond M (K - 1) p)
      (fun p => isRegular_winCond M (K - 1) p)
  haveI := hS
  haveI : Inhabited S := ⟨ini⟩
  -- the good inputs form a regular language
  have hG : Language.IsRegular {w : List A | GoodInput M K w} := by
    refine RegAut.isRegular_of_eq (RegAut.isRegular_and
      (RegAut.isRegular_not RegAut.isRegular_eq_nil)
      (SnakeRun.isRegular_haltWidthLang M K)) ?_
    intro w
    constructor
    · rintro ⟨hne, hhalt, hwidth⟩
      exact ⟨hne, hhalt, hwidth⟩
    · rintro ⟨hne, hhalt, hwidth⟩
      exact ⟨hne, hhalt, hwidth⟩
  set L : Language (Gam A Q S K) :=
    {u | (u.map lt ∈ {w : List A | GoodInput M K w} ∧ u ∈ ChkLang M K stp ini acc) ∨
      (u.map lt ∉ {w : List A | GoodInput M K w} ∧ u ∈ FlatLang)} with hLdef
  have hLreg : L.IsRegular := by
    refine RegAut.isRegular_or (RegAut.isRegular_and (RegAut.isRegular_comap lt hG)
      (isRegular_chkLang M K stp ini acc))
      (RegAut.isRegular_and (RegAut.isRegular_not (RegAut.isRegular_comap lt hG))
        isRegular_flatLang)
  refine ⟨Gam A Q S K, inferInstance, snakeIn K, snakeOutLet K, L, hLreg, ?_, ?_⟩
  · rintro u (⟨hgood, hchk⟩ | ⟨hbad, hflat⟩) hne
    · rw [homOf_snakeIn] at hne ⊢
      rw [chk_sound M stp ini acc hacc hchk hgood,
        widthOut_eq_runOut_of_good hgood]
    · rw [homOf_snakeIn] at hne ⊢
      rw [homOf_snakeOutLet_of_flat ((flatB_eq_false_iff u).1 hflat), pairMap,
        pairBlocks_map_some]
      simp only [List.map_nil, List.flatten_nil]
      exact (widthOut_eq_nil_of_not_good hne hbad).symm
  · intro w
    by_cases hgood : GoodInput M K w
    · obtain ⟨u, hu, hmap⟩ := chk_complete M hK stp ini acc hacc hgood
      exact ⟨u, Or.inl ⟨by rw [hmap]; exact hgood, hu⟩, by rw [homOf_snakeIn, hmap]⟩
    · have hmapid : (w.map (fun c => ((c, (default : Dat A Q S K)) : Gam A Q S K))).map lt = w := by
        rw [List.map_map,
          show (lt ∘ fun c : A => ((c, (default : Dat A Q S K)) : Gam A Q S K)) = id from rfl,
          List.map_id]
      refine ⟨w.map (fun c => (c, (default : Dat A Q S K))), Or.inr ⟨?_, ?_⟩, ?_⟩
      · rw [Set.mem_setOf_eq, hmapid]
        exact hgood
      · change flatB _ = false
        rw [flatB_eq_false_iff]
        intro c hc
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
        exact ⟨rfl, rfl⟩
      · rw [homOf_snakeIn, hmapid]

end TwoWay

end Lax916827Proofs.Transducers
