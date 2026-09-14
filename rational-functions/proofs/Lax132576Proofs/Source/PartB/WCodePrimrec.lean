/-
Computability of the evaluation procedure for coded weighted automata over `ℚ`, and with it the
proof of what used to be the effectivity hypothesis
`Transducers.EffectiveWeightedEvalEq` of `RequestProject/PartB/Effective.lean`.

`RequestProject/PartB/WCodeEnum.lean` computes the value of a coded weighted automaton on an
input string as the sum of an explicitly enumerated list of rationals
(`Transducers.WEnum.wcodeEvalList`).  What is proved here is that this function is primitive
recursive, hence computable, so that the equality test of two coded weighted automata on a given
input is a `Computable` procedure.

The arithmetic on `ℤ` and on `ℚ` that this needs -- which Mathlib's `Primrec` API does not have --
is developed in the general-purpose files `RequestProject/Common/PrimrecArith.lean` and
`RequestProject/Common/PrimrecList.lean`.
-/
import Lax132576Proofs.Source.PartB.WCodeEnum
import Lax132576Proofs.Source.Common.PrimrecArith
import Lax132576Proofs.Source.Common.PrimrecList
open Primrec
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace WEnum

open Primrec

/-- The transition of the automaton described by a coded transition is a primitive recursive
function of the coded transition. -/
theorem primrec_wtr : Primrec wtr := by
  have h : Primrec fun s : ℕ × List ℕ × (ℤ × ℕ) × ℕ =>
      ((s.1, s.2.1, mkRat s.2.2.1.1 s.2.2.1.2, s.2.2.2) : WT) := by
    refine Primrec.pair fst (Primrec.pair (fst.comp snd)
      (Primrec.pair ?_ (snd.comp (snd.comp snd))))
    exact rat_mkRat.comp (fst.comp (fst.comp (snd.comp snd)))
      (snd.comp (fst.comp (snd.comp snd)))
  refine h.of_eq fun s => ?_
  simp [wtr, Rat.mkRat_eq_div]

/-- One step of the search is primitive recursive. -/
theorem primrec_extend : Primrec₂ extend := by
  have hfilter : Primrec fun p : WCode × PRun =>
      p.1.1.filter (fun s => decide (s.1 = p.2.2.1) && s.2.1.isPrefixOf p.2.2.2) := by
    refine Primrec.list_filter (f := fun p : WCode × PRun => p.1.1)
      (p := fun (p : WCode × PRun) (s : ℕ × List ℕ × (ℤ × ℕ) × ℕ) =>
        decide (s.1 = p.2.2.1) && s.2.1.isPrefixOf p.2.2.2)
      (fst.comp fst) ?_
    have he : Primrec fun q : (WCode × PRun) × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) =>
        decide (q.2.1 = q.1.2.2.1) :=
      (PrimrecRel.comp (Primrec.eq (α := ℕ)) (fst.comp snd)
        (fst.comp (snd.comp (snd.comp fst)))).decide
    have hp : Primrec fun q : (WCode × PRun) × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) =>
        q.2.2.1.isPrefixOf q.1.2.2.2 :=
      list_isPrefixOf.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp (snd.comp fst)))
    exact (Primrec.and.comp he hp).to₂
  have hmap : Primrec fun p : WCode × PRun =>
      (p.1.1.filter (fun s => decide (s.1 = p.2.2.1) && s.2.1.isPrefixOf p.2.2.2)).map
        (fun s => ((wtr s :: p.2.1, s.2.2.2, p.2.2.2.drop s.2.1.length) : PRun)) := by
    refine Primrec.list_map hfilter ?_
    have hcons : Primrec fun q : (WCode × PRun) × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) =>
        wtr q.2 :: q.1.2.1 :=
      list_cons.comp (primrec_wtr.comp snd) (fst.comp (snd.comp fst))
    have hst : Primrec fun q : (WCode × PRun) × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) =>
        q.2.2.2.2 := snd.comp (snd.comp (snd.comp snd))
    have hdrop : Primrec fun q : (WCode × PRun) × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) =>
        q.1.2.2.2.drop q.2.2.1.length :=
      list_drop'.comp (snd.comp (snd.comp (snd.comp fst)))
        (list_length.comp (fst.comp (snd.comp snd)))
    exact (Primrec.pair hcons (Primrec.pair hst hdrop)).to₂
  exact hmap.to₂

/-! ## The bounded search -/

/-- The one-step closure of a list of partial runs. -/
private def fm (c : WCode) (P : List PRun) : List PRun := P.flatMap (extend c)

private lemma upto_succ' (c : WCode) : ∀ (K : ℕ) (P : List PRun),
    upto c (K + 1) P = upto c K P ++ (fm c)^[K + 1] P := by
  intro K
  induction K with
  | zero => intro P; simp [upto, fm]
  | succ K ih =>
      intro P
      show P ++ upto c (K + 1) (fm c P) = (P ++ upto c K (fm c P)) ++ (fm c)^[K + 2] P
      have hit : (fm c)^[K + 2] P = (fm c)^[K + 1] (fm c P) :=
        Function.iterate_succ_apply _ _ _
      rw [ih (fm c P), List.append_assoc, hit]

/-- The bounded search, run as an iteration of a single step on a pair
`(frontier, accumulated list)`. -/
private lemma iterate_step_eq (c : WCode) (P : List PRun) : ∀ K : ℕ,
    (fun x : List PRun × List PRun => (fm c x.1, x.2 ++ fm c x.1))^[K] (P, P)
      = ((fm c)^[K] P, upto c K P) := by
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [Function.iterate_succ_apply', ih]
      refine Prod.ext ?_ ?_
      · show fm c ((fm c)^[K] P) = (fm c)^[K + 1] P
        rw [Function.iterate_succ_apply']
      · show upto c K P ++ fm c ((fm c)^[K] P) = upto c (K + 1) P
        rw [upto_succ' c K P, ← Function.iterate_succ_apply' (fm c) K P]

/-- The bounded search is primitive recursive. -/
theorem primrec_upto : Primrec fun p : (WCode × List PRun) × ℕ => upto p.1.1 p.2 p.1.2 := by
  have hstep : Primrec₂ fun (a : (WCode × List PRun) × ℕ) (x : List PRun × List PRun) =>
      ((fm a.1.1 x.1, x.2 ++ fm a.1.1 x.1) : List PRun × List PRun) := by
    have hf : Primrec fun q : ((WCode × List PRun) × ℕ) × (List PRun × List PRun) =>
        q.2.1.flatMap (extend q.1.1.1) := by
      refine Primrec.list_flatMap
        (f := fun q : ((WCode × List PRun) × ℕ) × (List PRun × List PRun) => q.2.1)
        (g := fun q x => extend q.1.1.1 x) (fst.comp snd) ?_
      exact (primrec_extend.comp (fst.comp (fst.comp (fst.comp fst))) snd).to₂
    exact (Primrec.pair hf (list_append.comp (snd.comp snd) hf)).to₂
  have hiter := Primrec.nat_iterate (f := fun p : (WCode × List PRun) × ℕ => p.2)
    (g := fun p : (WCode × List PRun) × ℕ => ((p.1.2, p.1.2) : List PRun × List PRun))
    (h := fun (a : (WCode × List PRun) × ℕ) (x : List PRun × List PRun) =>
      ((fm a.1.1 x.1, x.2 ++ fm a.1.1 x.1) : List PRun × List PRun))
    snd (Primrec.pair (snd.comp fst) (snd.comp fst)) hstep
  refine (snd.comp hiter).of_eq fun p => ?_
  rw [iterate_step_eq]

/-! ## Deduplication -/

/-- Deduplication is primitive recursive. -/
theorem primrec_dedupR {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupR : List α → List α) := by
  refine Primrec.list_foldr (f := fun l : List α => l) (g := fun _ => ([] : List α))
    (h := fun (_ : List α) (x : α × List α) => if x.1 ∈ x.2 then x.2 else x.1 :: x.2)
    Primrec.id (const ([] : List α)) ?_
  have hcond : Primrec fun q : List α × (α × List α) =>
      bif decide (q.2.1 ∈ q.2.2) then q.2.2 else q.2.1 :: q.2.2 :=
    Primrec.cond (PrimrecRel.comp list_mem (fst.comp snd) (snd.comp snd)).decide
      (snd.comp snd) (list_cons.comp (fst.comp snd) (snd.comp snd))
  exact hcond.to₂.of_eq fun a x => by by_cases h : x.1 ∈ x.2 <;> simp [h]

/-! ## The enumeration and the evaluation -/

theorem primrec_wcodeStates : Primrec wcodeStates := by
  have h : Primrec fun c : WCode => c.2.1 ++ c.2.2 ++ c.1.flatMap (fun s => [s.1, s.2.2.2]) := by
    refine list_append.comp (list_append.comp (fst.comp snd) (snd.comp snd)) ?_
    refine Primrec.list_flatMap (f := fun c : WCode => c.1)
      (g := fun (_ : WCode) (s : ℕ × List ℕ × (ℤ × ℕ) × ℕ) => [s.1, s.2.2.2]) fst ?_
    exact (list_cons.comp (fst.comp snd)
      (list_cons.comp (snd.comp (snd.comp (snd.comp snd))) (const []))).to₂
  exact h

theorem primrec_wcodeRunBound : Primrec₂ wcodeRunBound :=
  (Primrec.nat_mul.comp (Primrec.succ.comp (list_length.comp snd))
    (list_length.comp (primrec_wcodeStates.comp fst))).to₂

/-- The list of accepting runs is a primitive recursive function of the code and the input. -/
theorem primrec_wruns : Primrec₂ wruns := by
  have hinit : Primrec fun p : WCode × List ℕ =>
      p.1.2.1.map (fun q => (([], q, p.2) : PRun)) := by
    refine Primrec.list_map (f := fun p : WCode × List ℕ => p.1.2.1)
      (g := fun (p : WCode × List ℕ) (q : ℕ) => (([], q, p.2) : PRun))
      (fst.comp (snd.comp fst)) ?_
    exact (Primrec.pair (const []) (Primrec.pair snd (snd.comp fst))).to₂
  have hupto : Primrec fun p : WCode × List ℕ =>
      upto p.1 (wcodeRunBound p.1 p.2) (p.1.2.1.map (fun q => (([], q, p.2) : PRun))) :=
    primrec_upto.comp (Primrec.pair (Primrec.pair fst hinit) (primrec_wcodeRunBound.comp fst snd))
  have hfilter : Primrec fun p : WCode × List ℕ =>
      (upto p.1 (wcodeRunBound p.1 p.2)
        (p.1.2.1.map (fun q => (([], q, p.2) : PRun)))).filter
          (fun x => decide (x.2.2 = []) && decide (x.2.1 ∈ p.1.2.2)) := by
    refine Primrec.list_filter hupto ?_
    have h1 : Primrec fun q : (WCode × List ℕ) × PRun => decide (q.2.2.2 = []) :=
      (PrimrecRel.comp (Primrec.eq (α := List ℕ)) (snd.comp (snd.comp snd))
        (const [])).decide
    have h2 : Primrec fun q : (WCode × List ℕ) × PRun => decide (q.2.2.1 ∈ q.1.1.2.2) :=
      (PrimrecRel.comp list_mem (fst.comp (snd.comp snd))
        (snd.comp (snd.comp (fst.comp fst)))).decide
    exact (Primrec.and.comp h1 h2).to₂
  have hmap : Primrec fun p : WCode × List ℕ =>
      ((upto p.1 (wcodeRunBound p.1 p.2)
        (p.1.2.1.map (fun q => (([], q, p.2) : PRun)))).filter
          (fun x => decide (x.2.2 = []) && decide (x.2.1 ∈ p.1.2.2))).map
            (fun x => x.1.reverse) := by
    refine Primrec.list_map hfilter ?_
    exact (list_reverse.comp (fst.comp snd)).to₂
  exact (primrec_dedupR.comp hmap).to₂

/-- **The evaluation procedure is primitive recursive.** -/
theorem primrec_wcodeEvalList : Primrec₂ wcodeEvalList := by
  have hweight : Primrec fun ts : List WT => LabAut.weightOf ts := by
    have hlabels : Primrec fun ts : List WT => ts.map (fun t => t.2.2.1) :=
      Primrec.list_map Primrec.id (fst.comp (snd.comp (snd.comp snd))).to₂
    have hprod : Primrec fun ts : List WT =>
        (ts.map (fun t => t.2.2.1)).foldr (fun a b : ℚ => a * b) 1 :=
      Primrec.list_foldr (f := fun ts : List WT => ts.map (fun t => t.2.2.1))
        (g := fun _ => (1 : ℚ)) (h := fun (_ : List WT) (x : ℚ × ℚ) => x.1 * x.2)
        hlabels (const 1) ((rat_mul.comp (fst.comp snd) (snd.comp snd)).to₂)
    exact hprod.of_eq fun ts => by
      rw [LabAut.weightOf, LabAut.labelsOf, List.prod_eq_foldr]
  have hmap : Primrec fun p : WCode × List ℕ => (wruns p.1 p.2).map LabAut.weightOf :=
    Primrec.list_map (primrec_wruns.comp fst snd) (hweight.comp snd).to₂
  have hsum : Primrec fun p : WCode × List ℕ =>
      ((wruns p.1 p.2).map LabAut.weightOf).foldr (fun a b : ℚ => a + b) 0 :=
    Primrec.list_foldr (f := fun p : WCode × List ℕ => (wruns p.1 p.2).map LabAut.weightOf)
      (g := fun _ => (0 : ℚ)) (h := fun (_ : WCode × List ℕ) (x : ℚ × ℚ) => x.1 + x.2)
      hmap (const 0) ((rat_add.comp (fst.comp snd) (snd.comp snd)).to₂)
  exact hsum.to₂.of_eq fun c v => by rw [wcodeEvalList, List.sum_eq_foldr]

end WEnum

/-- **Evaluating coded weighted automata over `ℚ`.**

There is a computable procedure which, given two codes `c₁, c₂` of weighted automata over `ℚ` and
a string `v`, decides whether the two automata take the same value on `v` -- correctly at least
when both codes are *valid*, i.e. when every input string has only finitely many accepting runs
(`WCodeValid`).

This used to be an explicit hypothesis of the decidability results of Section *Rational relations
and weighted automata*, because Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℤ` or
on `ℚ`.  That arithmetic is now developed in the general-purpose files
`RequestProject/Common/PrimrecArith.lean` and `RequestProject/Common/PrimrecList.lean`, the
accepting runs of a valid code over a given input are enumerated in
`RequestProject/PartB/WCodeEnum.lean` (they are boundedly many, by the pumping argument of
`RequestProject/PartB/WCodeRunBound.lean`), and the resulting procedure is shown primitive
recursive above. -/
theorem EffectiveWeightedEvalEq :
    ∃ D : WCode × WCode × List ℕ → Bool, Computable D ∧
      ∀ c₁ c₂ (v : List ℕ), WCodeValid c₁ → WCodeValid c₂ →
        (D (c₁, c₂, v) = true ↔ wcodeEval c₁ v = wcodeEval c₂ v) := by
  refine ⟨fun p => decide (WEnum.wcodeEvalList p.1 p.2.2 = WEnum.wcodeEvalList p.2.1 p.2.2), ?_, ?_⟩
  · exact ((Primrec.eq (α := ℚ)).comp
      (WEnum.primrec_wcodeEvalList.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (WEnum.primrec_wcodeEvalList.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).decide.to_comp
  · intro c₁ c₂ v h₁ h₂
    rw [decide_eq_true_eq, WEnum.wcodeEvalList_eq h₁, WEnum.wcodeEvalList_eq h₂]

end Lax132576Proofs.Transducers
