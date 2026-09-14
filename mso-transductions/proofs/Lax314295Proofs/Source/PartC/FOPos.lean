/-
Compositionality of first-order logic at a distinguished position: whether a
first-order formula of quantifier rank at most `k`, evaluated with all its
variables at one position `p` of a string `w`, holds depends only on the
`k`-type of the prefix before `p`, the letter at `p` and the `k`-type of the
suffix after `p`.

This is the instance of Claim `claim:fo-composition-quantifier-rank` (`Transducers.sat_iff_of_kEquiv` in
`RequestProject/PartC/FOComp.lean`) that is used in the proof of
Theorem `thm:fo-rational-functions` of *Transducers* (M. Bojańczyk): "the output produced by the
first-order relabelling on the `i`-th position depends [...] only on the
`k`-type of the prefix `a₁ ⋯ a_{i-1}`, the letter `a_i` and the `k`-type of the
suffix `a_{i+1} ⋯ a_n`".

The valuation is the constant one, as in the semantics of an mso relabelling
(`MSORelabelling.Relabels`), so no assumption on the free variables of the
formula is needed: the marked set is taken to be the set of all its variables.
-/
import Lax314295Proofs.Source.PartC.FOComp
import Lax916827Proofs.Source.PartC.MSOSyntax
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

variable {A : Type}

open MSO

/-- The three pieces of level-`k` information about a position of a string:
the `k`-type of the prefix before it, its letter, and the `k`-type of the suffix
after it. -/
theorem sat_const_iff_of_tp_split (φ : MSO A) (hfo : φ.IsFO) {k : ℕ} (hqr : φ.qrank ≤ k)
    {w v : List A} {p q : ℕ} (hp : p < w.length) (hq : q < v.length)
    (hlab : w[p]? = v[q]?)
    (hpre : tp k (w.take p) = tp k (v.take q))
    (hsuf : tp k (w.drop (p + 1)) = tp k (v.drop (q + 1)))
    (so so' : ℕ → Set ℕ) :
    Sat w (fun _ => p) so φ ↔ Sat v (fun _ => q) so' φ := by
  classical
  -- the whole strings have the same `k`-type
  have hw : w = w.take p ++ w[p] :: w.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop p w]
    rw [List.drop_eq_getElem_cons hp]
  have hv : v = v.take q ++ v[q] :: v.drop (q + 1) := by
    conv_lhs => rw [← List.take_append_drop q v]
    rw [List.drop_eq_getElem_cons hq]
  have hlab' : w[p] = v[q] := by
    have h1 : w[p]? = some w[p] := List.getElem?_eq_getElem hp
    have h2 : v[q]? = some v[q] := List.getElem?_eq_getElem hq
    rw [h1, h2] at hlab
    exact Option.some.inj hlab
  have htotal : tp k w = tp k v := by
    conv_lhs => rw [hw]
    conv_rhs => rw [hv]
    rw [hlab']
    exact tp_congr_cons k _ hpre hsuf
  refine sat_iff_of_kEquiv φ (V := φ.foVars.toFinset) hfo hqr ?_ ?_
  · intro i hi
    simpa using freeFO_subset_foVars φ hi
  · refine ⟨fun i _ => hp, fun i _ => hq, fun i _ => hlab, fun i _ j _ => by simp, ?_⟩
    intro b c _ _ _
    cases b with
    | none =>
        cases c with
        | none =>
            have e1 : segP w (none : Option ℕ) none = w := by
              simp [segP, hiB, loB]
            have e2 : segP v (none : Option ℕ) none = v := by
              simp [segP, hiB, loB]
            simpa [e1, e2] using htotal
        | some j =>
            have e1 : segP w (none : Option ℕ) (some p) = w.take p := by
              simp [segP, hiB, loB]
            have e2 : segP v (none : Option ℕ) (some q) = v.take q := by
              simp [segP, hiB, loB]
            simpa [e1, e2] using hpre
    | some i =>
        cases c with
        | none =>
            have e1 : segP w (some p) (none : Option ℕ) = w.drop (p + 1) := by
              simp [segP, hiB, loB]
            have e2 : segP v (some q) (none : Option ℕ) = v.drop (q + 1) := by
              simp [segP, hiB, loB]
            simpa [e1, e2] using hsuf
        | some j =>
            have e1 : segP w (some p) (some p) = ([] : List A) := by
              simp [segP, hiB, loB]
            have e2 : segP v (some q) (some q) = ([] : List A) := by
              simp [segP, hiB, loB]
            simp [e1, e2]

end Lax314295Proofs.Transducers
