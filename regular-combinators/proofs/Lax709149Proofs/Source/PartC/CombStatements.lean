/-
The easy direction of Theorem `thm:regular-terms` of Section *Combinators* of *Transducers*
(M. Bojańczyk).

Theorem `thm:regular-terms` says that a type-to-type function is regular under string
representation *if and only if* it is defined by some regular term.  This file proves the
implication

    defined by a regular term  ⟹  regular under string representation,

which is `Transducers.regularTerm_isRegular`.  The converse -- expressive completeness of the
terms -- is not proved here, and is *not* assumed anywhere either: no statement of this
development takes it as a hypothesis, so the theorem below is unconditional.  It is for that
reason that the equivalence itself is not stated: a biconditional whose second half rested on an
assumption would be worth less than the half that is proved.

The proof is the induction on the term that the book describes.  Its basis is that every atomic
term is regular under string representation, which is the content of `CombAtomProj.lean`,
`CombAtomDistr.lean`, `CombAtomCons.lean`, `CombAtomConcat.lean`, `CombAtomSplit.lean`,
`CombAtomReverse.lean` and `CombAtomPref.lean`; its induction step is the content of
`CombCombinators.lean` (composition being `Transducers.IsRegularUnderRepr.comp`, in
`CombTypes.lean`).  All that is left here is to put the cases together.
-/
import Lax709149Proofs.Source.PartC.CombAtomProj
import Lax709149Proofs.Source.PartC.CombAtomDistr
import Lax709149Proofs.Source.PartC.CombAtomCons
import Lax709149Proofs.Source.PartC.CombAtomConcat
import Lax709149Proofs.Source.PartC.CombAtomSplit
import Lax709149Proofs.Source.PartC.CombAtomReverse
import Lax709149Proofs.Source.PartC.CombAtomPref
import Lax709149Proofs.Source.PartC.CombCombinators
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers

open Comb

/-- **Every regular term defines a function that is regular under string representation.**  This
is the easy direction of Theorem `thm:regular-terms`, by induction on the term. -/
theorem RegTerm.isRegularUnderRepr :
    ∀ {A B : Ty} (t : RegTerm A B), IsRegularUnderRepr t.eval
  | _, _, .id A => isRegularUnderRepr_id A
  | _, _, .fst A B => isRegularUnderRepr_fst A B
  | _, _, .snd A B => isRegularUnderRepr_snd A B
  | _, _, .inl A B => isRegularUnderRepr_inl A B
  | _, _, .inr A B => isRegularUnderRepr_inr A B
  | _, _, .distr A B C => isRegularUnderRepr_distr A B C
  | _, _, .cons A => isRegularUnderRepr_cons A
  | _, _, .uncons A => isRegularUnderRepr_uncons A
  | _, _, .reverse A => isRegularUnderRepr_reverse A
  | _, _, .concat A => isRegularUnderRepr_concat A
  | _, _, .split A B => isRegularUnderRepr_split A B
  | _, _, .pref G grp hfin => by
      letI := grp
      haveI := hfin
      exact isRegularUnderRepr_pref G
  | _, _, .comp s t => (RegTerm.isRegularUnderRepr s).comp (RegTerm.isRegularUnderRepr t)
  | _, _, .pair s t =>
      IsRegularUnderRepr.pair (RegTerm.isRegularUnderRepr s) (RegTerm.isRegularUnderRepr t)
  | _, _, .copair s t =>
      IsRegularUnderRepr.copair (RegTerm.isRegularUnderRepr s) (RegTerm.isRegularUnderRepr t)
  | _, _, .map t => IsRegularUnderRepr.mapList (RegTerm.isRegularUnderRepr t)

/-- **Theorem `thm:regular-terms`, the easy direction.**  Every type-to-type function that is
defined by a regular term is regular under string representation. -/
theorem regularTerm_isRegular {A B : Ty} {f : A.Elt → B.Elt} (h : IsRegularTermFun f) :
    IsRegularUnderRepr f := by
  obtain ⟨t, ht⟩ := h
  exact ht ▸ t.isRegularUnderRepr

end Lax709149Proofs.Transducers
