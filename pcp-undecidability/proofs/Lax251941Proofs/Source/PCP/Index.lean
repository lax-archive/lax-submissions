/-
# The Post Correspondence Problem in index form

The main result of this development, `Acceptance.hasMatch_not_computablyDecidable`, says
that the Post Correspondence Problem is undecidable, where an instance is a list of
dominos over the symbol type `PCP.Sym` and a match is a list of dominos taken from the
instance.

This file restates that result in the formulation used elsewhere: an instance is a list of
pairs of strings over `ℕ`, and a solution is a nonempty list of *indices* into the
instance.  Two bridges are needed.

* **Dominos versus indices.**  A list of dominos each of which belongs to `P` and a list of
  positions in `P` carry the same information: choose an index for each domino, or read a
  domino off each index (`PCPIndex.solvable_iff_hasMatch`).
* **The alphabet.**  `PCP.Sym` is countable; mapping an instance along an injective map of
  alphabets preserves and reflects solvability (`PCPIndex.solvable_mapInst_iff`).  The map
  used is `Encodable.encode`, which is primitive recursive, so the resulting reduction is
  computable.
-/
import Lax251941Proofs.Source.Acceptance.Bridge
import Lax251941Proofs.Source.PartB.PCPRed

/-!
`Transducers.PCP.Instance`, `Transducers.PCP.conc` and `Transducers.PCP.Solvable`
are *not* declared here: they are the book's own, in
`RequestProject/PartB/PCPRed.lean`, imported above.  This file exists to prove
`Transducers.PCP.solvable_not_computablePred` about those very definitions, so
restating them would both duplicate the declarations and leave the theorem talking
about a copy rather than about the definition the book's results are stated with.
-/

namespace Lax251941Proofs.PCPIndex

open Lax251941Proofs.PCP

variable {α β : Type*}

/-! ## The index formulation over an arbitrary alphabet -/

/-- `Transducers.PCP.conc` over an arbitrary alphabet. -/
def gconc (ws : List (List α)) (idx : List ℕ) : List α :=
  (idx.map (fun i => ws.getD i [])).flatten

/-- `Transducers.PCP.Solvable` over an arbitrary alphabet. -/
def GSolvable (P : List (List α × List α)) : Prop :=
  ∃ idx : List ℕ, idx ≠ [] ∧ (∀ i ∈ idx, i < P.length) ∧
    gconc (P.map Prod.fst) idx = gconc (P.map Prod.snd) idx

lemma gsolvable_iff_solvable (P : Transducers.PCP.Instance) :
    GSolvable P ↔ Transducers.PCP.Solvable P := Iff.rfl

lemma getD_map_fst (P : List (List α × List α)) {i : ℕ} (h : i < P.length) :
    (P.map Prod.fst).getD i [] = (P.getD i ([], [])).1 := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
  simp

lemma getD_map_snd (P : List (List α × List α)) {i : ℕ} (h : i < P.length) :
    (P.map Prod.snd).getD i [] = (P.getD i ([], [])).2 := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
  simp

lemma gconc_map_fst (P : List (List α × List α)) (idx : List ℕ)
    (h : ∀ i ∈ idx, i < P.length) :
    gconc (P.map Prod.fst) idx = topStr (idx.map fun i => P.getD i ([], [])) := by
  unfold gconc topStr
  rw [List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
  exact getD_map_fst P (h i hi)

lemma gconc_map_snd (P : List (List α × List α)) (idx : List ℕ)
    (h : ∀ i ∈ idx, i < P.length) :
    gconc (P.map Prod.snd) idx = botStr (idx.map fun i => P.getD i ([], [])) := by
  unfold gconc botStr
  rw [List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
  exact getD_map_snd P (h i hi)

/-- Every list of dominos taken from `P` is read off from a list of positions in `P`. -/
lemma exists_idx (P : List (List α × List α)) :
    ∀ s : List (List α × List α), (∀ d ∈ s, d ∈ P) →
      ∃ idx : List ℕ, idx.length = s.length ∧ (∀ i ∈ idx, i < P.length) ∧
        idx.map (fun i => P.getD i ([], [])) = s := by
  intro s
  induction s with
  | nil => exact fun _ => ⟨[], by simp⟩
  | cons d t ih =>
      intro hs
      obtain ⟨idx, h1, h2, h3⟩ := ih fun e he => hs e (List.mem_cons_of_mem _ he)
      obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp (hs d List.mem_cons_self)
      refine ⟨i :: idx, by simp [h1], ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact h2 j hj
      · simp only [List.map_cons, h3]
        rw [List.getD_eq_getElem _ _ hi, hd]

/-- **The two formulations agree**: an instance is solvable in the index sense exactly
when it has a match in the sense of dominos. -/
lemma solvable_iff_hasMatch (P : List (List α × List α)) :
    GSolvable P ↔ HasMatch P := by
  constructor
  · rintro ⟨idx, hne, hlt, heq⟩
    refine ⟨idx.map fun i => P.getD i ([], []), ?_, ?_, ?_⟩
    · simpa using hne
    · rintro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      rw [List.getD_eq_getElem _ _ (hlt i hi)]
      exact List.getElem_mem _
    · rw [← gconc_map_fst P idx hlt, ← gconc_map_snd P idx hlt]
      exact heq
  · rintro ⟨s, hne, hmem, heq⟩
    obtain ⟨idx, hlen, hlt, hmap⟩ := exists_idx P s hmem
    refine ⟨idx, ?_, hlt, ?_⟩
    · intro h
      apply hne
      rw [← List.length_eq_zero_iff, ← hlen, h, List.length_nil]
    · rw [gconc_map_fst P idx hlt, gconc_map_snd P idx hlt, hmap]
      exact heq

/-! ## Changing the alphabet -/

/-- Map an instance along a map of alphabets. -/
def mapInst (f : α → β) (P : List (List α × List α)) : List (List β × List β) :=
  P.map fun d => (d.1.map f, d.2.map f)

@[simp] lemma length_mapInst (f : α → β) (P : List (List α × List α)) :
    (mapInst f P).length = P.length := by simp [mapInst]

lemma gconc_map_map (f : α → β) (ws : List (List α)) (idx : List ℕ) :
    gconc (ws.map fun w => w.map f) idx = (gconc ws idx).map f := by
  unfold gconc
  rw [List.map_flatten, List.map_map]
  refine congrArg List.flatten (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  rcases lt_or_ge i ws.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ h]
    simp

/-- Mapping an instance along an injective map of alphabets preserves and reflects
solvability. -/
lemma solvable_mapInst_iff {f : α → β} (hf : Function.Injective f)
    (P : List (List α × List α)) : GSolvable (mapInst f P) ↔ GSolvable P := by
  have hfst : (mapInst f P).map Prod.fst = (P.map Prod.fst).map fun w => w.map f := by
    simp [mapInst, List.map_map, Function.comp]
  have hsnd : (mapInst f P).map Prod.snd = (P.map Prod.snd).map fun w => w.map f := by
    simp [mapInst, List.map_map, Function.comp]
  constructor
  · rintro ⟨idx, hne, hlt, heq⟩
    rw [hfst, hsnd, gconc_map_map, gconc_map_map] at heq
    exact ⟨idx, hne, by simpa using hlt, List.map_injective_iff.2 hf heq⟩
  · rintro ⟨idx, hne, hlt, heq⟩
    refine ⟨idx, hne, by simpa using hlt, ?_⟩
    rw [hfst, hsnd, gconc_map_map, gconc_map_map, heq]

/-! ## Computability of the change of alphabet -/

lemma primrec_mapInst {α : Type} [Primcodable α] :
    Primrec fun P : List (List α × List α) => mapInst (Encodable.encode) P := by
  have h : Primrec₂ fun (_ : List (List α × List α)) (d : List α × List α) =>
      ((d.1.map Encodable.encode : List ℕ), (d.2.map Encodable.encode : List ℕ)) := by
    refine Primrec.pair ?_ ?_
    · exact Primrec.comp (Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂)
        (Primrec.fst.comp Primrec.snd)
    · exact Primrec.comp (Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂)
        (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_map Primrec.id h).of_eq fun P => rfl

end Lax251941Proofs.PCPIndex

namespace Lax251941Proofs.Transducers
namespace PCP

open Lax251941Proofs.PCPIndex

/-- **The Post Correspondence Problem, in index form, is undecidable.**

This is `Acceptance.hasMatch_not_computablyDecidable` transported along the two bridges of
this file: the passage between lists of dominos and lists of indices, and the primitive
recursive injection `PCP.Sym ↪ ℕ` given by `Encodable.encode`. -/
theorem solvable_not_computablePred : ¬ ComputablePred Solvable := by
  intro h
  rw [ComputablePred.computable_iff] at h
  obtain ⟨g, hg, hgspec⟩ := h
  refine Acceptance.hasMatch_not_computablyDecidable
    ⟨fun P => g (mapInst Encodable.encode P), hg.comp primrec_mapInst.to_comp, fun P => ?_⟩
  have h1 : Solvable (mapInst Encodable.encode P) ↔ g (mapInst Encodable.encode P) = true := by
    rw [hgspec]
  rw [← h1, ← gsolvable_iff_solvable,
    solvable_mapInst_iff (Encodable.encode_injective) P, solvable_iff_hasMatch]

end PCP
end Lax251941Proofs.Transducers
