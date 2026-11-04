import Lax185574Proofs.ResolveRam.Glue.RootW
import Lax185574Proofs.FarRam.Pure

/-!
The restricted scatter type and the far filter on words.

`words_filter`: the words of a filtered finite set are the filtered words,
if the test on a word agrees with the filter. So the query of the far
tree contains the entries of `σ` whose second entry (the first rank of the
tree) is at least `m` (`stpCut_words`). `passW` is the test `passF` on the
headers and atom words of the shifted tree and of a member of the far tree
(`passW_eq`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574.TypeTrees
open Lax185574Proofs.TreeAlgo Lax185574Proofs.ResolveRam Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus rhoPlus)

/-- **The words of a filtered set.** -/
theorem words_filter {α : Type*} [WordEncoding α] (S : Finset α) (P : α → Prop) [DecidablePred P]
    (sel : List ℕ → Bool) (h : ∀ a ∈ S, sel (toWord a) = decide (P a)) :
    (S.filter P).words = S.words.filter sel := by
  have hL : (S.words.filter sel).Pairwise (· ≤ ·) := (Finset.pairwise_sort _ _).filter sel
  have hnd1 : (S.words.filter sel).Nodup := (Finset.sort_nodup _ _).filter sel
  have hnd2 : (S.filter P).words.Nodup := Finset.sort_nodup _ _
  have hperm := List.perm_of_nodup_nodup_toFinset_eq hnd2 hnd1 (by
    ext w
    rw [List.mem_toFinset, List.mem_toFinset, mem_words, List.mem_filter, mem_words]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Finset.mem_filter] at ha
      exact ⟨⟨a, ha.1, rfl⟩, by rw [h a ha.1, decide_eq_true_iff]; exact ha.2⟩
    · rintro ⟨⟨a, ha, rfl⟩, hs⟩
      rw [h a ha, decide_eq_true_iff] at hs
      exact ⟨a, Finset.mem_filter.2 ⟨ha, hs⟩, rfl⟩)
  exact hperm.eq_of_pairwise' (Finset.pairwise_sort _ _) hL

/-- The test of the restricted scatter type on the word of an entry: the
first rank of its tree is at least `m`. -/
def cutSel (m : ℕ) (w : List ℕ) : Bool := decide (m ≤ w.getD 1 0)

/-- **The restricted scatter type on words.** -/
theorem stpCut_words (m : ℕ) (σ : Finset ((ℕ × TypeTree) × ℕ)) :
    (stpCut m σ).words = σ.words.filter (cutSel m) := by
  unfold stpCut
  refine words_filter σ _ (cutSel m) fun p _ => ?_
  rw [FarRam.toWord_entry, FarRam.toWord_typeTree]
  rfl

/-- The test `passF` on the header `kσ, qσ, ℓσ` and the atom words `Aσ` of
the shifted tree and the arity `ℓν` and atom words `Aν` of a member of the
far tree. -/
def passW (Dw : DW) (kσ qσ ℓσ : ℕ) (Aσ : List (List ℕ)) (ℓν : ℕ) (Aν : List (List ℕ)) : Bool :=
  (ℓν == 1) && (List.range ℓσ).any fun i => hop2W Dw Aσ i Aν 0 (rhoPlus kσ qσ)

/-- **The far filter on words.** -/
theorem passW_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) (σ ν : TypeTree) :
    passW Dw σ.k σ.q σ.ℓ (Node.atoms σ.root).words ν.ℓ (Node.atoms ν.root).words = passF D σ ν := by
  unfold passW passF
  split_ifs with hν
  · simp only [hν, beq_self_eq_true, Bool.true_and]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, any_range_iff]
    constructor
    · rintro ⟨i, hi, hh⟩
      refine ⟨⟨i, Finset.mem_range.1 hi⟩, ?_⟩
      have := hop2W_eq h σ.root ⟨i, Finset.mem_range.1 hi⟩ ν.root ⟨0, by omega⟩ (rhoPlus σ.k σ.q)
      rw [hh, eq_comm, decide_eq_true_iff] at this
      exact this
    · rintro ⟨i, hh⟩
      refine ⟨i.val, Finset.mem_range.2 i.isLt, ?_⟩
      have := hop2W_eq h σ.root i ν.root ⟨0, by omega⟩ (rhoPlus σ.k σ.q)
      rw [this, decide_eq_true_iff]
      exact hh
  · simp [hν]

/-- The far filter on the word `νw` of a member, against the word `sw` of
the shifted tree. -/
def passSel (Dw : DW) (sw νw : List ℕ) : Bool :=
  passW Dw (sw.getD 0 0) (sw.getD 1 0) (sw.getD 2 0) (listWords sw 3) (νw.getD 2 0) (listWords νw 3)

theorem passSel_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) (σ ν : TypeTree) :
    passSel Dw (toWord σ) (toWord ν) = passF D σ ν := by
  have a1 : listWords (toWord σ) 3 = (Node.atoms σ.root).words :=
    EvalRam.atoms_listWords (r := []) (by rw [FarRam.toWord_typeTree]; simp)
  have a2 : listWords (toWord ν) 3 = (Node.atoms ν.root).words :=
    EvalRam.atoms_listWords (r := []) (by rw [FarRam.toWord_typeTree]; simp)
  unfold passSel
  rw [a1, a2, ← passW_eq h σ ν, FarRam.toWord_typeTree, FarRam.toWord_typeTree]
  rfl

/-- **The filtered far tree on words.** The members of the far tree that
pass the test are the words of the answer that pass `passSel` against the
word of the shifted tree. -/
theorem faP_words {n : ℕ} {G : Lax185574.PartialGraphs.PartialGraph (Fin n)} {Dw : DW}
    {D : ResolveData} (h : Dw.OK D) (τ : TypeTree) :
    (faP G D τ).map toWord = ((faOf G τ).map toWord).filter (passSel Dw (toWord (shOf G τ))) := by
  unfold faP
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro ν _
  simp only [Function.comp, passSel_eq h]

end Lax185574Proofs.ResolveRam.Glue
