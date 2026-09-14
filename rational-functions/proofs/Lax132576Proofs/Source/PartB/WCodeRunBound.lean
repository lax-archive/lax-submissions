/-
A length bound for the accepting runs of a coded weighted automaton over `ℚ`.

This file proves the combinatorial fact behind `Transducers.EffectiveWeightedEvalEq`
(`RequestProject/PartB/WCodePrimrec.lean`): if a code is
*valid*, i.e. if every input string has only finitely many accepting runs, then every accepting
run over an input `v` has at most `(|v| + 1) * n` transitions, where `n` is the number of states
occurring in the code.

An accepting run with a
nonempty infix that starts and ends in the same state and reads nothing can be *pumped*: repeating
that infix any number of times gives again an accepting run over the same input, and these runs are
pairwise distinct because their lengths differ, so the code would have infinitely many accepting
runs over `v`.  A run without such an infix has, between two consecutive transitions that read a
nonempty string, at most `n - 1` transitions reading nothing -- the states along such a block are
pairwise distinct -- and it has at most `|v|` transitions that read a nonempty string.
-/
import Lax132576Proofs.Source.PartB.WCodes
import Lax132576Proofs.Source.PartB.PathComb
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace WEnum

open LabAut

/-- The transitions of a coded weighted automaton, as a type abbreviation. -/
abbrev WT := ℕ × List ℕ × ℚ × ℕ

/-- The transition of the automaton described by a coded transition. -/
def wtr (s : ℕ × List ℕ × (ℤ × ℕ) × ℕ) : WT :=
  (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)

lemma mem_wcodeAut_delta {c : WCode} {t : WT} :
    t ∈ (wcodeAut c).δ ↔ ∃ s ∈ c.1, t = wtr s := Iff.rfl

/-- The states occurring in a code: the initial states, the final states, and the sources and
targets of the transitions. -/
def wcodeStates (c : WCode) : List ℕ :=
  c.2.1 ++ c.2.2 ++ c.1.flatMap (fun s => [s.1, s.2.2.2])

/-- The bound on the number of transitions of an accepting run of a valid code over an input of
length `|v|`. -/
def wcodeRunBound (c : WCode) (v : List ℕ) : ℕ := (v.length + 1) * (wcodeStates c).length

/-! ## Elementary facts about paths -/

lemma inputOf_append (ts ts' : List WT) : inputOf (ts ++ ts') = inputOf ts ++ inputOf ts' := by
  simp [inputOf]

/-- The target of a transition of a code occurs in the code. -/
lemma target_mem_wcodeStates {c : WCode} {t : WT} (ht : t ∈ (wcodeAut c).δ) :
    t.2.2.2 ∈ wcodeStates c := by
  obtain ⟨s, hs, rfl⟩ := mem_wcodeAut_delta.1 ht
  refine List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨s, hs, ?_⟩))
  simp [wtr]

/-- Every state visited by a path that starts in a state of the code occurs in the code. -/
lemma mem_wcodeStates_of_path {c : WCode} {q p : ℕ} {ts : List WT}
    (hq : q ∈ wcodeStates c) (h : (wcodeAut c).Path q ts p) {r : ℕ} (hr : r ∈ statesOf q ts) :
    r ∈ wcodeStates c := by
  rcases List.mem_cons.1 hr with rfl | hr
  · exact hq
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hr
    exact target_mem_wcodeStates (Path.mem_delta h t ht)

lemma mem_wcodeStates_of_init {c : WCode} {q : ℕ} (hq : q ∈ c.2.1) : q ∈ wcodeStates c :=
  List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hq)))

/-! ## Pumping -/

/-- Repeating a loop that reads nothing gives again a loop that reads nothing. -/
lemma path_flatten_replicate {c : WCode} {r : ℕ} {σ : List WT}
    (h : (wcodeAut c).Path r σ r) : ∀ k : ℕ, (wcodeAut c).Path r (List.replicate k σ).flatten r := by
  intro k
  induction k with
  | zero => simpa using Path.nil r
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons]
      exact h.append ih

lemma inputOf_flatten_replicate {σ : List WT} (h : inputOf σ = []) (k : ℕ) :
    inputOf (List.replicate k σ).flatten = [] := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, inputOf_append, h, ih]; rfl

lemma length_flatten_replicate {σ : List WT} (k : ℕ) :
    ((List.replicate k σ).flatten).length = k * σ.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

/-- **Pumping.**  A nonempty infix of an accepting run that reads nothing and returns to its
starting state can be repeated, so a valid code has no such infix in an accepting run. -/
lemma no_pumpable_loop {c : WCode} (hc : WCodeValid c)
    {q p r : ℕ} (hq : q ∈ c.2.1) (hp : p ∈ c.2.2) {ts₁ ts₂ ts₃ : List WT}
    (h₁ : (wcodeAut c).Path q ts₁ r) (h₂ : (wcodeAut c).Path r ts₂ r)
    (h₃ : (wcodeAut c).Path r ts₃ p)
    (hnil : inputOf ts₂ = []) : ts₂ = [] := by
  by_contra hne
  have hlen : 0 < ts₂.length := List.length_pos_iff.2 hne
  refine absurd (hc (inputOf (ts₁ ++ ts₂ ++ ts₃))) (Set.not_finite.2 ?_)
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ts₁ ++ (List.replicate k ts₂).flatten ++ ts₃) ?_ ?_
  · intro k k' hkk'
    have := congrArg List.length hkk'
    simp only [List.length_append, length_flatten_replicate] at this
    exact Nat.eq_of_mul_eq_mul_right hlen (by omega)
  · intro k
    refine ⟨⟨q, hq, p, hp, (h₁.append (path_flatten_replicate h₂ k)).append h₃⟩, ?_⟩
    simp only [inputOf_append, inputOf_flatten_replicate hnil, hnil]

/-- The first element of `dropWhile` fails the test. -/
private lemma head_dropWhile_false {α : Type} {p : α → Bool} :
    ∀ (l : List α) (t : α) (r : List α), l.dropWhile p = t :: r → p t = false := by
  intro l
  induction l with
  | nil => intro t r h; simp at h
  | cons a l ih =>
      intro t r h
      rw [List.dropWhile_cons] at h
      by_cases hp : p a
      · rw [if_pos hp] at h
        exact ih t r h
      · rw [if_neg hp] at h
        obtain ⟨rfl, -⟩ := List.cons.inj h
        simpa using hp

/-! ## The length bound -/

/-- **The length bound.**  Every accepting run of a valid code over `v` has at most
`wcodeRunBound c v` transitions. -/
theorem length_le_of_mem_acceptingOn {c : WCode} (hc : WCodeValid c) {v : List ℕ} {ts : List WT}
    (hts : ts ∈ (wcodeAut c).acceptingOn v) : ts.length ≤ wcodeRunBound c v := by
  classical
  obtain ⟨⟨q, hq, p, hp, hpath⟩, hin⟩ := hts
  have hq' : q ∈ c.2.1 := hq
  have hp' : p ∈ c.2.2 := hp
  set n := (wcodeStates c).length with hn
  -- the main claim, by induction on the length of the suffix
  have key : ∀ (m : ℕ) (α suf : List WT) (r : ℕ), suf.length ≤ m → ts = α ++ suf →
      (wcodeAut c).Path q α r → (wcodeAut c).Path r suf p →
      suf.length ≤ ((inputOf suf).length + 1) * n := by
    intro m
    induction m with
    | zero =>
        intro α suf r hm _ _ _
        have : suf = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hm)
        subst this
        simp
    | succ m ih =>
        intro α suf r hm hsplit hα hsuf
        -- split off the maximal block of transitions that read nothing
        set e := suf.takeWhile (fun t : WT => decide (t.2.1 = [])) with he
        set d := suf.dropWhile (fun t : WT => decide (t.2.1 = [])) with hd
        have hed : e ++ d = suf := List.takeWhile_append_dropWhile
        have hein : inputOf e = [] := by
          have : ∀ t ∈ e, t.2.1 = [] := by
            intro t ht
            simpa using List.mem_takeWhile_imp (p := fun t : WT => decide (t.2.1 = [])) ht
          simp only [inputOf, List.flatten_eq_nil_iff, List.mem_map]
          rintro l ⟨t, ht, rfl⟩
          exact this t ht
        obtain ⟨r', hpe, hpd⟩ : ∃ r', (wcodeAut c).Path r e r' ∧ (wcodeAut c).Path r' d p := by
          have := hsuf
          rw [← hed] at this
          exact Path.split_append this
        -- the states along the block are pairwise distinct
        have hnd : (statesOf r e).Nodup := by
          by_contra hcon
          obtain ⟨e₁, e₂, e₃, r'', hsp, hne, hp1, hp2, hp3⟩ := Path.loop_of_not_nodup hpe hcon
          have h2nil : inputOf e₂ = [] := by
            have h0 : inputOf (e₁ ++ e₂ ++ e₃) = [] := by rw [← hsp]; exact hein
            rw [inputOf_append, inputOf_append] at h0
            simpa using (List.append_eq_nil_iff.1 ((List.append_eq_nil_iff.1 h0).1)).2
          exact hne (no_pumpable_loop hc hq' hp' (hα.append hp1) hp2 (hp3.append hpd) h2nil)
        -- hence the block is short
        have hrmem : r ∈ wcodeStates c :=
          Path.target_mem (wcodeStates c) (fun _ ht => target_mem_wcodeStates ht) hα
            (mem_wcodeStates_of_init hq')
        have helen : e.length + 1 ≤ n :=
          Path.length_lt_of_nodup (wcodeStates c)
            (fun _ ht => target_mem_wcodeStates ht) hpe hrmem hnd
        -- now recurse on the rest
        match hdcase : d with
        | [] =>
            have hsufe : suf = e := by simpa using hed.symm
            calc suf.length = e.length := by rw [hsufe]
              _ ≤ n := by omega
              _ ≤ ((inputOf suf).length + 1) * n := Nat.le_mul_of_pos_left n (by omega)
        | t :: d' =>
            have htne : t.2.1 ≠ [] := by
              have h0 := head_dropWhile_false (p := fun t : WT => decide (t.2.1 = [])) suf t d'
                (by rw [← hd])
              simpa using h0
            obtain ⟨r'', ht, hpd'⟩ : ∃ r'', ((wcodeAut c).Path r' [t] r'') ∧
                (wcodeAut c).Path r'' d' p := by
              obtain ⟨hq0, htδ, hrest⟩ := Path.cons_inv hpd
              refine ⟨t.2.2.2, ?_, hrest⟩
              have hmem : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : WT) ∈ (wcodeAut c).δ := htδ
              have h' : (wcodeAut c).Path t.1 [t] t.2.2.2 := Path.cons hmem (Path.nil _)
              rw [hq0] at h'
              exact h'
            have hlensuf : suf.length = e.length + 1 + d'.length := by
              rw [← hed]; simp; omega
            have hlen' : d'.length ≤ m := by omega
            have hIH := ih (α ++ e ++ [t]) d' r'' hlen' (by rw [hsplit, ← hed]; simp)
              ((hα.append hpe).append ht) hpd'
            have hinsuf : inputOf suf = t.2.1 ++ inputOf d' := by
              rw [← hed, inputOf_append, hein]
              simp
            have hlent : 1 ≤ t.2.1.length := by
              rcases hcase : t.2.1 with _ | ⟨a, l⟩
              · exact absurd hcase htne
              · simp
            have hin_len : (inputOf suf).length = t.2.1.length + (inputOf d').length := by
              rw [hinsuf]; simp
            calc suf.length = e.length + 1 + d'.length := hlensuf
              _ ≤ n + ((inputOf d').length + 1) * n := by omega
              _ = ((inputOf d').length + 2) * n := by ring
              _ ≤ ((inputOf suf).length + 1) * n := by
                  refine Nat.mul_le_mul_right n ?_
                  omega
  have := key ts.length [] ts q le_rfl (by simp) (Path.nil q) hpath
  rw [hin] at this
  exact this

end WEnum
end Lax132576Proofs.Transducers
