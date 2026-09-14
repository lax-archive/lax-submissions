/-
The value of a coded rational function on the empty input.

The reduction of Theorem `thm:equivalence-rational-functions` to Theorem
`thm:equivalence-weighted-automata` compares two coded functions on all *nonempty* strings; the
empty string has to be treated separately, and this file does so.  A run over the empty input uses
only transitions reading no letter, and if it visits a state twice the loop may be removed
(`CodeMerge.eps_short`), so under the promise that the code describes a function the value on the
empty input is the output of one of the finitely many transition sequences of length smaller than
the number of states of the code. `epsOut` picks the first such sequence, and the promise guarantees
that all of them have the same output. -/
import Lax132576Proofs.Source.PartB.CodeAlpha
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace CodeEps

open LabAut LenDec CodeMerge

/-- The transition sequences that are accepting runs over the empty input and
are short enough to be enumerated. -/
def epsSeqs (c : RelCode) : List (List CodeMerge.Tr) :=
  (seqsUpto c.1 (stateList c).length).filter
    (fun ts => acceptB c ts && decide (inputOf ts = []))

/-- The value of the relation described by a code on the empty input, if there
is one. -/
def epsOut (c : RelCode) : Option (List ℕ) :=
  ((epsSeqs c).head?).map (NFAO.outputOf : List CodeMerge.Tr → List ℕ)

lemma mem_epsSeqs {c : RelCode} {ts : List CodeMerge.Tr} (h : ts ∈ epsSeqs c) :
    (codeAut c).Accepting ts ∧ inputOf ts = [] := by
  simp only [epsSeqs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(acceptB_iff c ts).1 h.2.1, h.2.2⟩

/-- If the enumeration finds a run, its output is a value of the relation on the
empty input. -/
lemma epsOut_sound {c : RelCode} {v : List ℕ} (h : epsOut c = some v) : codeRel c [] v := by
  simp only [epsOut, Option.map_eq_some_iff] at h
  obtain ⟨ts, hts, rfl⟩ := h
  obtain ⟨hacc, hin⟩ := mem_epsSeqs (List.mem_of_mem_head? hts)
  exact ⟨ts, hacc, hin, rfl⟩

/-- If the relation described by the code has a value on the empty input, then
the enumeration finds a run. -/
lemma epsOut_isSome {c : RelCode} {v : List ℕ} (h : codeRel c [] v) :
    (epsOut c).isSome = true := by
  obtain ⟨ts, ⟨q, hq, p, hp, hpath⟩, hin, -⟩ := h
  have hqS : q ∈ stateList c := init_mem_stateList c q hq
  obtain ⟨ts', hpath', hin', hlen⟩ := CodeMerge.eps_short hqS hpath hin
  have hmem : ts' ∈ epsSeqs c := by
    simp only [epsSeqs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(mem_seqsUpto _ _ _).2 ⟨le_of_lt hlen, fun t ht => Path.mem_delta hpath' t ht⟩,
      (acceptB_iff c ts').2 ⟨q, hq, p, hp, hpath'⟩, hin'⟩
  rcases hl : epsSeqs c with _ | ⟨x, xs⟩
  · rw [hl] at hmem; exact absurd hmem (by simp)
  · simp [epsOut, hl]

/-- Under the promise, `epsOut` computes the value of the coded function on the
empty input. -/
lemma epsOut_eq_some {c : RelCode} (hc : CodeFunctional c) {v : List ℕ}
    (h : codeRel c [] v) : epsOut c = some v := by
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.1 (epsOut_isSome h)
  obtain ⟨u, -, hu⟩ := hc [] (fun x hx => absurd hx (by simp))
  rw [hts, Option.some_inj]
  rw [hu _ (epsOut_sound hts), hu _ h]

/-- Under the promises, the two coded relations agree on the empty input exactly
when `epsOut` gives the same answer for both. -/
lemma epsOut_eq_iff {c₁ c₂ : RelCode} (h₁ : CodeFunctional c₁) (h₂ : CodeFunctional c₂) :
    (epsOut c₁ = epsOut c₂) ↔ ∀ v, codeRel c₁ [] v ↔ codeRel c₂ [] v := by
  obtain ⟨v₁, hv₁, hu₁⟩ := h₁ [] (fun x hx => absurd hx (by simp))
  obtain ⟨v₂, hv₂, hu₂⟩ := h₂ [] (fun x hx => absurd hx (by simp))
  rw [epsOut_eq_some h₁ hv₁, epsOut_eq_some h₂ hv₂]
  constructor
  · intro h v
    have : v₁ = v₂ := Option.some_inj.1 h
    subst this
    constructor
    · intro hv; rw [hu₁ _ hv]; exact hv₂
    · intro hv; rw [hu₂ _ hv]; exact hv₁
  · intro h
    rw [Option.some_inj]
    exact hu₂ _ ((h v₁).1 hv₁)

/-! ## Computability -/

lemma primrec_epsSeqs : Primrec epsSeqs := by
  refine CodeMerge.primrec_filter
    (primrec_seqsUpto.comp Primrec.fst
      (Primrec.list_length.comp primrec_stateList)) ?_
  have h1 : Primrec (fun z : RelCode × List CodeMerge.Tr => acceptB z.1 z.2) := primrec_acceptB
  have h2 : Primrec (fun z : RelCode × List CodeMerge.Tr => decide (inputOf z.2 = [])) :=
    primrec_decEq (primrec_inputOf.comp Primrec.snd) (Primrec.const [])
  exact (Primrec.and.comp h1 h2).to₂

lemma primrec_epsOut : Primrec epsOut :=
  Primrec.option_map (Primrec.list_head?.comp primrec_epsSeqs)
    (primrec_outputOf.comp Primrec.snd).to₂

end CodeEps
end Lax132576Proofs.Transducers
