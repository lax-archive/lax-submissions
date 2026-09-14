/-
Lemma `lem:logic-precomputation` of *Transducers* (M. Bojańczyk): the precomputation of a finite
family of mso formulas with one or two free first-order variables by a
letter-to-letter rational function.

Every formula `χ` of the family gives, by Lemma `lem:mso-free-variables` (in the form
`MarkStr.markedSat2`), a regular language of doubly marked strings; let `D χ` be
a deterministic automaton for it.  The rational function `f` produced here is
the letter-to-letter function that decorates every position `x` of the input `w`
by the tuple of pairs

  `(state of D χ before x, state transformation of D χ after x)`,

which is `MarkBimach.markFun`; it is rational because it is computed by a
bimachine (Theorem `thm:bimachines`).

* A formula `φ(x)` with one free variable holds in the position `x` if and only
  if the letter in the position `x` of `f w` belongs to the set of letters for
  which the run of `D φ` through the position marked twice is accepting.
* A formula `φ(x, y)` with two free variables holds if and only if the infix of
  `f w` between the positions `x` and `y` belongs to a regular language: the
  first letter of the infix carries the state of `D φ` before `x`, the last one
  carries the state transformation of `D φ` after `y`, and the letters in
  between provide the input of the run of `D φ` on the infix.  Since the
  automaton reading the infix only learns which position is the last one when
  the string ends, it keeps the last letter it has read pending; this is the
  delayed automaton of `RequestProject/PartC/MarkDelay.lean`.
-/
import Lax314295Proofs.Source.PartC.MarkDelay
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

open MarkStr MarkBimach MarkDelay

/-- **Lemma `lem:logic-precomputation`.**  For a finite set of mso formulas with one or two free
first-order variables there is a letter-to-letter rational function
`f : A* → C*` such that the formulas with one free variable correspond to sets
of letters of the output, and the formulas with two free variables correspond to
regular languages of infixes of the output. -/
theorem mso_formulas_via_rational_aux {A : Type} [Finite A]
    (Φ₁ Φ₂ : Set (MSO A)) (hΦ₁ : Φ₁.Finite) (hΦ₂ : Φ₂.Finite) :
    ∃ (C : Type) (_ : Finite C) (f : List A → List C),
      IsRationalFun f ∧ LengthPreserving f ∧
      (∀ φ ∈ Φ₁, ∃ F : Set C, ∀ (w : List A) (x : ℕ), x < w.length →
        (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ ∃ c ∈ F, (f w)[x]? = some c)) ∧
      (∀ φ ∈ Φ₂, ∃ L : Language C, L.IsRegular ∧ ∀ (w : List A) (x y : ℕ),
        x ≤ y → y < w.length →
        (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ ↔
          ((f w).drop x).take (y - x + 1) ∈ L)) := by
  classical
  haveI : Finite ↥(Φ₁ ∪ Φ₂) := (hΦ₁.union hΦ₂).to_subtype
  have hreg : ∀ χ : ↥(Φ₁ ∪ Φ₂), (markedSat2 (χ : MSO A)).IsRegular :=
    fun χ => isRegular_markedSat2 _
  choose σ hσ D hD using hreg
  haveI : ∀ χ, Finite (σ χ) := fun χ => @Finite.of_fintype _ (hσ χ)
  haveI : Finite (A × ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ))) := inferInstance
  -- the letter-to-letter function decorating every position by the states of
  -- all the automata of the family
  set f₀ : A → ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ)) →
      A × ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ)) := fun a g => (a, g) with hf₀
  set hout : A → ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ)) →
      List (A × ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ))) := fun a g => [f₀ a g] with hhout
  set f : List A → List (A × ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ))) :=
    markFun D hout [] with hf
  have hgetElem : ∀ (w : List A) (x : ℕ) (hx : x < w.length),
      (f w)[x]? = some (w[x], fun χ => (markPreSt D w x χ, sufTr D w x χ)) :=
    fun w x hx => markFun_getElem? D hout [] f₀ (fun _ _ => rfl) rfl w x hx
  have hLP : LengthPreserving f :=
    markFun_lengthPreserving D hout [] f₀ (fun _ _ => rfl) rfl
  -- the truth value of a formula in a position, read off the decoration
  have hsat1 : ∀ (χ : ↥(Φ₁ ∪ Φ₂)) (w : List A) (x : ℕ) (hx : x < w.length),
      (sufTr D w x χ ((D χ).step (markPreSt D w x χ) (w[x], true, true)) ∈ (D χ).accept ↔
        MSO.Sat w (fun _ => x) (fun _ => ∅) (χ : MSO A)) := by
    intro χ w x hx
    simp only [sufTr, markPreSt]
    rw [← eval_markAt2_diag (D χ) w x hx, hD χ, markAt2_mem_markedSat2 _ w x x hx hx]
    have hfo : (fun j => if j = 0 then x else x) = (fun _ : ℕ => x) := by
      funext j; simp
    rw [hfo]
  refine ⟨A × ((χ : ↥(Φ₁ ∪ Φ₂)) → σ χ × (σ χ → σ χ)), inferInstance, f,
    isRationalFun_markFun D hout [], hLP, ?_, ?_⟩
  · -- the formulas with one free variable
    intro φ hφ
    have hmem : φ ∈ Φ₁ ∪ Φ₂ := Or.inl hφ
    refine ⟨{c | (c.2 ⟨φ, hmem⟩).2 ((D ⟨φ, hmem⟩).step (c.2 ⟨φ, hmem⟩).1 (c.1, true, true))
      ∈ (D ⟨φ, hmem⟩).accept}, ?_⟩
    intro w x hx
    rw [hgetElem w x hx]
    constructor
    · intro hsat
      exact ⟨_, (hsat1 ⟨φ, hmem⟩ w x hx).2 hsat, rfl⟩
    · rintro ⟨c, hc, hceq⟩
      obtain rfl : c = (w[x], fun χ => (markPreSt D w x χ, sufTr D w x χ)) :=
        (Option.some.inj hceq).symm
      exact (hsat1 ⟨φ, hmem⟩ w x hx).1 hc
  · -- the formulas with two free variables
    intro φ hφ
    have hmem : φ ∈ Φ₁ ∪ Φ₂ := Or.inr hφ
    refine ⟨delayLang (fun c => c.1) (D ⟨φ, hmem⟩) (fun c => (c.2 ⟨φ, hmem⟩).1)
      (fun c => (c.2 ⟨φ, hmem⟩).2), isRegular_delayLang _ _ _ _, ?_⟩
    intro w x y hxy hy
    have hx : x < w.length := lt_of_le_of_lt hxy hy
    have hlen : (f w).length = w.length := hLP w
    have hinfix : ∀ k, k < y - x + 1 →
        (((f w).drop x).take (y - x + 1))[k]? = (f w)[x + k]? := by
      intro k hk
      rw [List.getElem?_take, if_pos hk, List.getElem?_drop]
    have hulen : (((f w).drop x).take (y - x + 1)).length = y - x + 1 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    obtain ⟨c, t, hct⟩ :
        ∃ c t, ((f w).drop x).take (y - x + 1) = c :: t := by
      refine List.exists_cons_of_ne_nil ?_
      intro hnil
      rw [hnil] at hulen
      simp at hulen
    have htlen : t.length = y - x := by
      rw [hct, List.length_cons] at hulen
      omega
    have hc : c = (w[x], fun χ => (markPreSt D w x χ, sufTr D w x χ)) := by
      have h0 := hinfix 0 (by omega)
      rw [hct, Nat.add_zero, hgetElem w x hx] at h0
      exact Option.some.inj h0
    have hlast : lastC c t = (w[y], fun χ => (markPreSt D w y χ, sufTr D w y χ)) := by
      have hL := hinfix t.length (by omega)
      rw [hct, show x + t.length = y by omega, hgetElem w y hy] at hL
      rw [lastC_eq_getElem]
      rw [List.getElem?_eq_getElem (by simp : t.length < (c :: t).length)] at hL
      exact Option.some.inj hL
    have hfst : (f w).map Prod.fst = w := by
      apply List.ext_getElem?
      intro j
      rw [List.getElem?_map]
      by_cases hj : j < w.length
      · rw [hgetElem w j hj, List.getElem?_eq_getElem hj]
        rfl
      · rw [List.getElem?_eq_none (by omega : (f w).length ≤ j),
          List.getElem?_eq_none (by omega : w.length ≤ j)]
        rfl
    have hmap : (c :: t).map (fun c => c.1) = (w.drop x).take (y - x + 1) := by
      rw [← hct]
      show List.map Prod.fst (((f w).drop x).take (y - x + 1)) = _
      rw [List.map_take, List.map_drop, hfst]
    have heval := eval_markAt2 (D ⟨φ, hmem⟩) w x y hxy hy
    simp only [strTrans] at heval
    rw [hct, mem_delayLang, hmap, hlast, hc]
    simp only [sufTr, markPreSt, strTrans]
    rw [← heval, hD ⟨φ, hmem⟩, markAt2_mem_markedSat2 _ w x y hx hy]

end Lax314295Proofs.Transducers
