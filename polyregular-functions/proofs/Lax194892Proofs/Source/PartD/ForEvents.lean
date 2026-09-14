/-
Part D: for-transducers -- the positions of the output string of a nest of loops.

The output of a nest of loops whose body produces at most one letter per iteration is read off its
events: the tuples of positions at which the body does produce a letter.  This file establishes the
dictionary between the positions of the output string and the events -- they are as many, the
`q`-th letter of the output is the one produced at the `q`-th event, and the order of the positions
is the lexicographic order of the tuples -- which is what the translation of the outer
for-transducer uses to represent a position of its input by a tuple of positions of the input of
the inner one.
-/
import Lax194892Proofs.Source.PartD.ForAtom

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B : Type}

section

variable (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B)

/-- At an event, the body produces exactly one letter. -/
lemma outAt_length_one (hout1 : p.OutputsAtMostOne) {z : List ℕ}
    (hz : z ∈ events w L p (fun _ => 0) (fun _ => false)) :
    (outAt w L p (fun _ => 0) (fun _ => false) z).length = 1 := by
  have h1 : (outAt w L p (fun _ => 0) (fun _ => false) z).length ≤ 1 :=
    hout1 w _ _
  have h2 : outAt w L p (fun _ => 0) (fun _ => false) z ≠ [] := (mem_events.mp hz).2
  have := List.length_eq_zero_iff.not.mpr h2
  omega

/-- There are as many events as there are positions in the output string. -/
lemma events_length (hout1 : p.OutputsAtMostOne) :
    (events w L p (fun _ => 0) (fun _ => false)).length
      = (ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2.length := by
  rw [nest_out_events]
  exact (length_flatMap_singleton _ _ (fun z hz => outAt_length_one w L p hout1 hz)).symm

/-- The letter at a position of the output string is the one produced at the corresponding
event. -/
lemma events_outAt_getElem (hout1 : p.OutputsAtMostOne) (q : ℕ)
    (hq : q < (events w L p (fun _ => 0) (fun _ => false)).length) :
    outAt w L p (fun _ => 0) (fun _ => false)
        (events w L p (fun _ => 0) (fun _ => false))[q]
      = [(ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2[q]'
          (by rw [← events_length w L p hout1]; exact hq)] := by
  have hmem : (events w L p (fun _ => 0) (fun _ => false))[q]
      ∈ events w L p (fun _ => 0) (fun _ => false) := List.getElem_mem hq
  obtain ⟨c, hc⟩ : ∃ c, outAt w L p (fun _ => 0) (fun _ => false)
      (events w L p (fun _ => 0) (fun _ => false))[q] = [c] := by
    have h1 := outAt_length_one w L p hout1 hmem
    match hout : outAt w L p (fun _ => 0) (fun _ => false)
        (events w L p (fun _ => 0) (fun _ => false))[q] with
    | [] => rw [hout] at h1; simp at h1
    | c :: [] => exact ⟨c, rfl⟩
    | c :: c' :: t => rw [hout] at h1; simp at h1
  have hget := getElem?_flatMap_singleton (outAt w L p (fun _ => 0) (fun _ => false))
    (events w L p (fun _ => 0) (fun _ => false))
    (fun z hz => outAt_length_one w L p hout1 hz) q hq
  rw [← nest_out_events, hc] at hget
  rw [hc]
  have : ((ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2)[q]? = some c :=
    hget
  rw [List.getElem?_eq_getElem (by rw [← events_length w L p hout1]; exact hq)] at this
  simp only [Option.some.injEq] at this
  rw [this]

/-- Every event is a tuple of the nest. -/
lemma events_length_tuple {z : List ℕ} (hz : z ∈ events w L p (fun _ => 0) (fun _ => false)) :
    z.length = L.length :=
  length_of_mem_tuplesOf L w.length (events_subset hz)

end

/-! ## The order of the events -/

/-- In a list sorted by the lexicographic order, the order of the entries is the order of the
indices. -/
lemma lexLt_getElem_iff (ds : List Bool) (l : List (List ℕ)) (hs : l.Pairwise (LexLt ds)) (q q' : ℕ) (hq : q < l.length) (hq' : q' < l.length) :
    LexLt ds l[q] l[q'] ↔ q < q' := by
  constructor
  · intro h
    by_contra hc
    rcases Nat.lt_or_ge q' q with h' | h'
    · exact lexLt_asymm ds _ _ h (List.pairwise_iff_getElem.mp hs q' q hq' hq h')
    · have : q = q' := by omega
      subst this
      exact lexLt_irrefl ds _ h
  · intro h
    exact List.pairwise_iff_getElem.mp hs q q' hq hq' h

/-- In a list sorted by the lexicographic order, equal entries have equal indices. -/
lemma lexLt_getElem_inj (ds : List Bool) (l : List (List ℕ)) (hs : l.Pairwise (LexLt ds))
    (q q' : ℕ) (hq : q < l.length) (hq' : q' < l.length) (h : l[q] = l[q']) : q = q' := by
  by_contra hc
  rcases Nat.lt_or_ge q q' with h' | h'
  · exact lexLt_irrefl ds _ (h ▸ List.pairwise_iff_getElem.mp hs q q' hq hq' h')
  · have h'' : q' < q := by omega
    exact lexLt_irrefl ds _ (h ▸ List.pairwise_iff_getElem.mp hs q' q hq' hq h'')

/-- Comparing two entries of a list sorted by the lexicographic order. -/
lemma lexLt_getElem_le_iff (ds : List Bool) (l : List (List ℕ)) (hs : l.Pairwise (LexLt ds))
    (q q' : ℕ) (hq : q < l.length) (hq' : q' < l.length) :
    q ≤ q' ↔ ¬ LexLt ds l[q'] l[q] := by
  rw [lexLt_getElem_iff ds l hs q' q hq' hq]
  omega

end Lax194892Proofs.Transducers
