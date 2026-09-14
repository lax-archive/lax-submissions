/-
An explicit enumeration of the accepting runs of a coded weighted automaton over `ℚ`, and the
resulting evaluation procedure.

Together with the length bound of `RequestProject/PartB/WCodeRunBound.lean` this turns the value
`Transducers.wcodeEval c v` -- a `finsum` over the set of accepting runs, and therefore
noncomputable as it stands -- into the sum of an explicitly computed list of rationals,
`Transducers.WEnum.wcodeEvalList c v`.  The computability of that list is proved in
`RequestProject/PartB/WCodePrimrec.lean`.

The enumeration is a breadth-first search over *partial runs* `(σ, q, u)`: the transitions read so
far in reverse order, the current state, and the part of the input that is left.  `extend` performs
one step, `upto` collects everything reachable in at most `K` steps, and `wruns` keeps the partial
runs that have consumed the whole input and ended in a final state, deduplicated -- the same run
may be produced twice, since a code may list the same transition twice, or two coded weights with
the same value.
-/
import Lax132576Proofs.Source.PartB.WCodeRunBound
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace WEnum

open LabAut

/-- A partial run: the transitions read so far in reverse order, the current state, and the part
of the input that is left. -/
abbrev PRun := List WT × ℕ × List ℕ

/-- One step of the search: all ways of extending a partial run by one transition of the code. -/
def extend (c : WCode) (x : PRun) : List PRun :=
  (c.1.filter (fun s => decide (s.1 = x.2.1) && s.2.1.isPrefixOf x.2.2)).map
    (fun s => (wtr s :: x.1, s.2.2.2, x.2.2.drop s.2.1.length))

/-- All partial runs reachable from a list of partial runs in at most `K` steps. -/
def upto (c : WCode) : ℕ → List PRun → List PRun
  | 0, P => P
  | K + 1, P => P ++ upto c K (P.flatMap (extend c))

/-- Deduplication, in the form of a fold; it agrees with `List.dedup` (`dedupR_eq_dedup`) and is
manifestly primitive recursive. -/
def dedupR {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldr (fun a m => if a ∈ m then m else a :: m) []

lemma dedupR_eq_dedup {α : Type} [DecidableEq α] (l : List α) : dedupR l = l.dedup := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      show (if a ∈ dedupR l then dedupR l else a :: dedupR l) = (a :: l).dedup
      rw [ih]
      by_cases h : a ∈ l
      · rw [if_pos (List.mem_dedup.2 h), List.dedup_cons_of_mem h]
      · rw [if_neg (fun hc => h (List.mem_dedup.1 hc)), List.dedup_cons_of_notMem h]

/-- The accepting runs of a code over an input string, listed without repetitions. -/
def wruns (c : WCode) (v : List ℕ) : List (List WT) :=
  dedupR (((upto c (wcodeRunBound c v) (c.2.1.map (fun q => ([], q, v)))).filter
    (fun x => decide (x.2.2 = []) && decide (x.2.1 ∈ c.2.2))).map (fun x => x.1.reverse))

/-- The value of a coded weighted automaton, computed as a finite sum of rationals. -/
def wcodeEvalList (c : WCode) (v : List ℕ) : ℚ := ((wruns c v).map weightOf).sum

/-! ## Correctness of the enumeration -/

lemma mem_extend {c : WCode} {x y : PRun} :
    y ∈ extend c x ↔ ∃ s ∈ c.1, s.1 = x.2.1 ∧ s.2.1 <+: x.2.2 ∧
      y = (wtr s :: x.1, s.2.2.2, x.2.2.drop s.2.1.length) := by
  simp only [extend, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
    List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨s, ⟨hs, hq, hpre⟩, rfl⟩
    exact ⟨s, hs, hq, hpre, rfl⟩
  · rintro ⟨s, hs, hq, hpre, rfl⟩
    exact ⟨s, ⟨hs, hq, hpre⟩, rfl⟩

/-- The partial runs reachable in at most `K` steps are exactly those obtained by following a path
of at most `K` transitions. -/
lemma mem_upto {c : WCode} : ∀ (K : ℕ) (P : List PRun) (y : PRun),
    y ∈ upto c K P ↔ ∃ x ∈ P, ∃ ts : List WT, ts.length ≤ K ∧ y.1 = ts.reverse ++ x.1 ∧
      (wcodeAut c).Path x.2.1 ts y.2.1 ∧ inputOf ts ++ y.2.2 = x.2.2 := by
  intro K
  induction K with
  | zero =>
      intro P y
      constructor
      · intro hy
        exact ⟨y, hy, [], le_rfl, by simp, Path.nil _, by simp⟩
      · rintro ⟨x, hx, ts, hlen, h1, h2, h3⟩
        have hts : ts = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
        subst hts
        have hq : x.2.1 = y.2.1 := Path.eq_of_nil h2
        simp only [List.reverse_nil, List.nil_append] at h1
        simp only [inputOf_nil, List.nil_append] at h3
        have : y = x := by
          refine Prod.ext h1 (Prod.ext hq.symm h3)
        rw [this]; exact hx
  | succ K ih =>
      intro P y
      show y ∈ P ++ upto c K (P.flatMap (extend c)) ↔ _
      rw [List.mem_append, ih]
      constructor
      · rintro (hy | ⟨z, hz, ts, hlen, h1, h2, h3⟩)
        · exact ⟨y, hy, [], Nat.zero_le _, by simp, Path.nil _, by simp⟩
        · obtain ⟨x, hx, hzx⟩ := List.mem_flatMap.1 hz
          obtain ⟨s, hs, hq, hpre, rfl⟩ := mem_extend.1 hzx
          refine ⟨x, hx, wtr s :: ts, by simpa using Nat.succ_le_succ hlen, by simpa using h1,
            ?_, ?_⟩
          · have hmem : wtr s ∈ (wcodeAut c).δ := ⟨s, hs, rfl⟩
            have hsrc : (wtr s).1 = x.2.1 := hq
            have : (wcodeAut c).Path (wtr s).1 (wtr s :: ts) y.2.1 :=
              Path.cons hmem (by simpa using h2)
            rw [hsrc] at this
            exact this
          · have hdrop : s.2.1 ++ x.2.2.drop s.2.1.length = x.2.2 := by
              obtain ⟨w, hw⟩ := hpre
              rw [← hw]
              simp
            simp only [inputOf_cons, List.append_assoc]
            rw [show (wtr s).2.1 = s.2.1 from rfl]
            simp only at h3
            rw [h3, hdrop]
      · rintro ⟨x, hx, ts, hlen, h1, h2, h3⟩
        match hts : ts with
        | [] =>
            left
            have hq : x.2.1 = y.2.1 := Path.eq_of_nil (by simpa [hts] using h2)
            have h1' : y.1 = x.1 := by simpa using h1
            have h3' : y.2.2 = x.2.2 := by simpa using h3
            have : y = x := Prod.ext h1' (Prod.ext hq.symm h3')
            rw [this]; exact hx
        | t :: ts' =>
            right
            obtain ⟨hsrc, htδ, hrest⟩ := Path.cons_inv h2
            obtain ⟨s, hs, rfl⟩ := htδ
            refine ⟨(wtr s :: x.1, (wtr s).2.2.2, x.2.2.drop (wtr s).2.1.length), ?_, ts',
              by simpa using Nat.le_of_succ_le_succ hlen, by simpa using h1, hrest, ?_⟩
            · refine List.mem_flatMap.2 ⟨x, hx, mem_extend.2 ⟨s, hs, hsrc, ?_, ?_⟩⟩
              · refine ⟨inputOf ts' ++ y.2.2, ?_⟩
                simpa using h3
              · rfl
            · have : (wtr s).2.1 ++ (inputOf ts' ++ y.2.2) = x.2.2 := by simpa using h3
              rw [← this]
              simp

/-- The enumeration lists exactly the accepting runs. -/
theorem mem_wruns {c : WCode} (hc : WCodeValid c) {v : List ℕ} {ts : List WT} :
    ts ∈ wruns c v ↔ ts ∈ (wcodeAut c).acceptingOn v := by
  classical
  rw [wruns, dedupR_eq_dedup, List.mem_dedup]
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hnil, hfin⟩, rfl⟩
    obtain ⟨z, hz, ts', -, h1, h2, h3⟩ := (mem_upto _ _ _).1 hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hz
    simp only at h1 h2 h3
    rw [List.append_nil] at h1
    refine ⟨⟨q, hq, x.2.1, hfin, ?_⟩, ?_⟩
    · rw [h1]; simpa using h2
    · rw [h1]
      simp only [List.reverse_reverse]
      rw [hnil, List.append_nil] at h3
      exact h3
  · rintro ⟨⟨q, hq, p, hp, hpath⟩, hin⟩
    have hlen : ts.length ≤ wcodeRunBound c v :=
      length_le_of_mem_acceptingOn hc ⟨⟨q, hq, p, hp, hpath⟩, hin⟩
    refine ⟨(ts.reverse, p, []), ⟨?_, rfl, hp⟩, by simp⟩
    refine (mem_upto _ _ _).2 ⟨([], q, v), List.mem_map.2 ⟨q, hq, rfl⟩, ts, hlen, by simp, ?_, ?_⟩
    · exact hpath
    · simpa using hin

lemma wruns_nodup (c : WCode) (v : List ℕ) : (wruns c v).Nodup := by
  classical
  rw [wruns, dedupR_eq_dedup]
  exact List.nodup_dedup _

/-- **The evaluation procedure is correct**: for a valid code the sum of the weights of the
enumerated runs is the value of the coded weighted automaton. -/
theorem wcodeEvalList_eq {c : WCode} (hc : WCodeValid c) (v : List ℕ) :
    wcodeEvalList c v = wcodeEval c v := by
  classical
  have hset : (wcodeAut c).acceptingOn v = ((wruns c v).toFinset : Finset (List WT)) := by
    ext ts
    simp only [List.coe_toFinset, Set.mem_setOf_eq]
    exact (mem_wruns hc).symm
  show ((wruns c v).map weightOf).sum = (wcodeAut c).wEval v
  rw [LabAut.wEval, hset, finsum_mem_coe_finset,
    List.sum_toFinset _ (wruns_nodup c v)]

end WEnum
end Lax132576Proofs.Transducers
