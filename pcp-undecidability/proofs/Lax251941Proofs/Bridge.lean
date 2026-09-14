import Lax251941.Acceptance
import Lax251941.TuringMachines
import Lax251941.PostCorrespondence
import Lax251941Proofs.Source.PCP.Index
import Lax251941Proofs.Source.Acceptance.Bridge

/-!
The bridge between the concept package and the ported source development. The
machines of `Acceptance` and the Post correspondence problem are defined
identically on both sides, so their bridges are definitional; a Turing machine
and its string rewriting system are structures on both sides, related by
`toSrc`, and the one-step and reachability relations are transported along it.
The alphabet `Sym` is shared (the source's `Sym` is an abbreviation of the
concept's), so no translation of configurations is needed.
-/

namespace Lax251941Proofs.Bridge

open Lax251941.TuringMachines Lax251941.PostCorrespondence

/-! ## Turing machines and rewriting systems -/

/-- A concept machine as a source machine. -/
def toSrc (M : TM) : PCP.TM := ⟨M.trans, M.q0, M.qacc⟩

/-- A source machine as a concept machine. -/
def ofSrc (M : PCP.TM) : TM := ⟨M.trans, M.q0, M.qacc⟩

@[simp] lemma toSrc_ofSrc (M : PCP.TM) : toSrc (ofSrc M) = M := rfl

@[simp] lemma ofSrc_toSrc (M : TM) : ofSrc (toSrc M) = M := rfl

/-- A concept rewriting system as a source rewriting system. -/
def toSrcSRS {α : Type*} (S : SRS α) : PCP.SRS α := ⟨S.alphabet, S.rules, S.ext⟩

lemma stepRule_iff {α : Type*} (rules : List (List α × List α)) (a b : List α) :
    StepRule rules a b ↔ PCP.StepRule rules a b := by
  constructor
  · rintro ⟨l, u, v, r, h⟩
    exact PCP.StepRule.mk l u v r h
  · rintro ⟨l, u, v, r, h⟩
    exact StepRule.mk l u v r h

lemma step_iff {α : Type*} (S : SRS α) (a b : List α) :
    Step S a b ↔ PCP.Step (toSrcSRS S) a b := by
  constructor
  · rintro (h | h)
    · exact PCP.Step.rule ((stepRule_iff _ _ _).1 h)
    · exact PCP.Step.ext h
  · rintro (h | h)
    · exact Step.rule ((stepRule_iff _ _ _).2 h)
    · exact Step.ext h

lemma reaches_iff {α : Type*} (S : SRS α) (a b : List α) :
    Reaches S a b ↔ PCP.Reaches (toSrcSRS S) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail ((step_iff S _ _).1 hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail ((step_iff S _ _).2 hstep)

lemma machineSRS_eq (M : TM) (w : List ℕ) :
    toSrcSRS (M.machineSRS w) = (toSrc M).machineSRS w := rfl

lemma accepts_iff (M : TM) (w : List ℕ) : M.Accepts w ↔ (toSrc M).Accepts w := by
  unfold TM.Accepts PCP.TM.Accepts
  simp only [reaches_iff, machineSRS_eq]
  exact Iff.rfl

/-- The passage to the source machine is primitive recursive (both encodings are the
table with the two states). -/
lemma primrec_toSrc : Primrec toSrc :=
  ((Primrec.of_equiv_symm_iff (e := PCP.tmEquiv)).2 (Primrec.of_equiv (e := tmEquiv))).of_eq
    fun _ => rfl

lemma primrec_ofSrc : Primrec ofSrc :=
  ((Primrec.of_equiv_symm_iff (e := tmEquiv)).2 (Primrec.of_equiv (e := PCP.tmEquiv))).of_eq
    fun _ => rfl

/-! ## Decidability -/

/-- The source's notion of a computably decidable predicate is mathlib's
`ComputablePred`. -/
lemma computablyDecidable_iff {α : Type} [Primcodable α] (p : α → Prop) :
    PCP.ComputablyDecidable p ↔ ComputablePred p := by
  rw [ComputablePred.computable_iff]
  constructor
  · rintro ⟨f, hf, hspec⟩
    exact ⟨f, hf, funext fun a => propext (hspec a).symm⟩
  · rintro ⟨f, hf, hspec⟩
    exact ⟨f, hf, fun a => by rw [hspec]⟩

/-- Precomposing a computable predicate with a computable map. -/
lemma computablePred_comp {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : ComputablePred p) {g : α → β} (hg : Computable g) : ComputablePred fun a => p (g a) := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.1 hp
  exact ComputablePred.computable_iff.2 ⟨fun a => f (g a), hf.comp hg, rfl⟩

/-- Decidability of the acceptance problem, concept form and source form. -/
lemma computablePred_accepts_iff :
    ComputablePred (fun p : TM × List ℕ => p.1.Accepts p.2) ↔
      PCP.ComputablyDecidable PCP.AcceptanceProblem := by
  rw [computablyDecidable_iff]
  constructor
  · intro h
    have h' := computablePred_comp h
      (Primrec.pair (primrec_ofSrc.comp Primrec.fst) Primrec.snd).to_comp
    refine h'.of_eq fun p => ?_
    show (ofSrc p.1).Accepts p.2 ↔ PCP.AcceptanceProblem p
    rw [accepts_iff, toSrc_ofSrc]
    exact Iff.rfl
  · intro h
    have h' := computablePred_comp h
      (Primrec.pair (primrec_toSrc.comp Primrec.fst) Primrec.snd).to_comp
    refine h'.of_eq fun p => ?_
    exact (accepts_iff p.1 p.2).symm

/-! ## The Post correspondence problem: the domino form over `ℕ` -/

/-- Moving an instance from `Sym` to `ℕ` along the injective encoding preserves and
reflects the existence of a match. -/
lemma hasMatch_mapInst_iff (P : PCP.Inst PCP.Sym) :
    PCP.HasMatch (PCPIndex.mapInst Encodable.encode P) ↔ PCP.HasMatch P := by
  rw [← PCPIndex.solvable_iff_hasMatch, ← PCPIndex.solvable_iff_hasMatch]
  exact PCPIndex.solvable_mapInst_iff Encodable.encode_injective P

lemma hasMatch_iff (P : Inst ℕ) : HasMatch P ↔ PCP.HasMatch P := Iff.rfl

lemma solvable_iff (P : Instance) : Solvable P ↔ Transducers.PCP.Solvable P := Iff.rfl

/-- A decision procedure for the problem over `ℕ` gives one over `Sym`. -/
lemma computablyDecidable_hasMatch_sym (h : ComputablePred fun P : Inst ℕ => HasMatch P) :
    PCP.ComputablyDecidable fun P : PCP.Inst PCP.Sym => PCP.HasMatch P := by
  rw [computablyDecidable_iff]
  have h' := computablePred_comp h (PCPIndex.primrec_mapInst (α := PCP.Sym)).to_comp
  exact h'.of_eq fun P => hasMatch_mapInst_iff P

end Lax251941Proofs.Bridge
