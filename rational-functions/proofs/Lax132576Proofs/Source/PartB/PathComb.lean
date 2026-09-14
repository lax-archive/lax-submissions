/-
Combinatorics of paths in an automaton with labelled transitions: splitting a
path at a visited state, extracting a short loop (pigeonhole), and replacing a
path by a simple one with the same endpoints.

These are the ingredients of the pumping arguments used for the decidability
results of Section *Machine independent characterisations* of *Transducers* (M. Bojańczyk).
-/
import Lax132576Proofs.Source.PartB.LabAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace LabAut

variable {A L Q : Type}

/-- The list of states visited by a path starting in `q`, given as the list of
transitions of the path. -/
def statesOf (q : Q) (ts : List (Q × List A × L × Q)) : List Q :=
  q :: ts.map (fun t => t.2.2.2)

@[simp] lemma statesOf_nil (q : Q) : statesOf q ([] : List (Q × List A × L × Q)) = [q] := rfl

@[simp] lemma statesOf_length (q : Q) (ts : List (Q × List A × L × Q)) :
    (statesOf q ts).length = ts.length + 1 := by simp [statesOf]

/-- An empty path does not move. -/
lemma Path.eq_of_nil {M : LabAut A L Q} {q p : Q} (h : M.Path q [] p) : q = p := by
  cases h; rfl

/-- Inversion for a nonempty path. -/
lemma Path.cons_inv {M : LabAut A L Q} {q p : Q} {t : Q × List A × L × Q}
    {ts : List (Q × List A × L × Q)} (h : M.Path q (t :: ts) p) :
    t.1 = q ∧ t ∈ M.δ ∧ M.Path t.2.2.2 ts p := by
  cases h with
  | cons ht hpath => exact ⟨rfl, ht, hpath⟩

/-- A path over a concatenation splits into two paths. -/
lemma Path.split_append {M : LabAut A L Q} {q p : Q} :
    ∀ {ts₁ ts₂ : List (Q × List A × L × Q)}, M.Path q (ts₁ ++ ts₂) p →
      ∃ r, M.Path q ts₁ r ∧ M.Path r ts₂ p := by
  intro ts₁
  induction ts₁ generalizing q with
  | nil => intro ts₂ h; exact ⟨q, Path.nil q, h⟩
  | cons t ts ih =>
      intro ts₂ h
      obtain ⟨hq, ht, hpath⟩ := Path.cons_inv h
      obtain ⟨r, h₁, h₂⟩ := ih hpath
      subst hq
      refine ⟨r, ?_, h₂⟩
      have : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Q × List A × L × Q) ∈ M.δ := ht
      exact Path.cons this h₁

/-- A path can be split at any state that it visits. -/
lemma Path.split_at_state {M : LabAut A L Q} {q p r : Q} :
    ∀ {ts : List (Q × List A × L × Q)}, M.Path q ts p → r ∈ statesOf q ts →
      ∃ ts₁ ts₂, ts = ts₁ ++ ts₂ ∧ M.Path q ts₁ r ∧ M.Path r ts₂ p := by
  intro ts
  induction ts generalizing q with
  | nil =>
      intro h hr
      simp [statesOf] at hr
      subst hr
      exact ⟨[], [], rfl, Path.nil r, h⟩
  | cons t ts ih =>
      intro h hr
      obtain ⟨hq, ht, hpath⟩ := Path.cons_inv h
      by_cases hrq : r = q
      · subst hrq; exact ⟨[], t :: ts, rfl, Path.nil r, h⟩
      · have hr' : r ∈ statesOf t.2.2.2 ts := by
          simp only [statesOf, List.map_cons, List.mem_cons] at hr ⊢
          rcases hr with h1 | h1 | h1
          · exact absurd h1 hrq
          · exact Or.inl h1
          · exact Or.inr h1
        obtain ⟨ts₁, ts₂, hsplit, h₁, h₂⟩ := ih hpath hr'
        subst hq
        refine ⟨t :: ts₁, ts₂, by rw [hsplit]; rfl, ?_, h₂⟩
        have : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Q × List A × L × Q) ∈ M.δ := ht
        exact Path.cons this h₁

/-- If a path visits some state twice, then it contains a nonempty loop. -/
lemma Path.loop_of_not_nodup {M : LabAut A L Q} {q p : Q} :
    ∀ {ts : List (Q × List A × L × Q)}, M.Path q ts p → ¬ (statesOf q ts).Nodup →
      ∃ (ts₁ ts₂ ts₃ : List (Q × List A × L × Q)) (r : Q),
        ts = ts₁ ++ ts₂ ++ ts₃ ∧ ts₂ ≠ [] ∧
          M.Path q ts₁ r ∧ M.Path r ts₂ r ∧ M.Path r ts₃ p := by
  intro ts
  induction ts generalizing q with
  | nil => intro _ hnd; exact absurd (by simp) hnd
  | cons t ts ih =>
      intro h hnd
      obtain ⟨hq, ht, hpath⟩ := Path.cons_inv h
      by_cases hmem : q ∈ statesOf t.2.2.2 ts
      · obtain ⟨ts₁, ts₂, hsplit, h₁, h₂⟩ := Path.split_at_state hpath hmem
        subst hq
        have htδ : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Q × List A × L × Q) ∈ M.δ := ht
        refine ⟨[], t :: ts₁, ts₂, t.1, by rw [hsplit]; rfl, by simp, Path.nil _,
          Path.cons htδ h₁, h₂⟩
      · have hnd' : ¬ (statesOf t.2.2.2 ts).Nodup := by
          intro hcon
          apply hnd
          have : statesOf q (t :: ts) = q :: statesOf t.2.2.2 ts := rfl
          rw [this]
          exact List.nodup_cons.2 ⟨hmem, hcon⟩
        obtain ⟨ts₁, ts₂, ts₃, r, hsplit, hne, h₁, h₂, h₃⟩ := ih hpath hnd'
        subst hq
        have htδ : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Q × List A × L × Q) ∈ M.δ := ht
        exact ⟨t :: ts₁, ts₂, ts₃, r, by rw [hsplit]; rfl, hne, Path.cons htδ h₁, h₂, h₃⟩

/-- All transitions of a path are transitions of the automaton. -/
lemma Path.mem_delta {M : LabAut A L Q} {q p : Q} :
    ∀ {ts : List (Q × List A × L × Q)}, M.Path q ts p → ∀ t ∈ ts, t ∈ M.δ := by
  intro ts
  induction ts generalizing q with
  | nil => intro _ t ht; simp at ht
  | cons t ts ih =>
      intro h s hs
      obtain ⟨_, ht, hpath⟩ := Path.cons_inv h
      rcases List.mem_cons.1 hs with rfl | hs'
      · exact ht
      · exact ih hpath s hs'

/-- Every state visited by a path lies in a set that contains the source and is
closed under transition targets. -/
lemma Path.mem_of_statesOf {M : LabAut A L Q} {q p : Q} (S : List Q)
    (hS : ∀ t ∈ M.δ, (t.2.2.2 : Q) ∈ S) :
    ∀ {ts : List (Q × List A × L × Q)}, M.Path q ts p → q ∈ S → ∀ r ∈ statesOf q ts, r ∈ S := by
  intro ts
  induction ts generalizing q with
  | nil => intro _ hq r hr; simp only [statesOf_nil, List.mem_singleton] at hr; exact hr ▸ hq
  | cons t ts ih =>
      intro h hq r hr
      obtain ⟨_, ht, hpath⟩ := Path.cons_inv h
      have hmem : r = q ∨ r ∈ statesOf t.2.2.2 ts := by
        simpa [statesOf, or_assoc] using hr
      rcases hmem with rfl | hr'
      · exact hq
      · exact ih hpath (hS _ ht) r hr'

/-- The endpoint of a path lies in any set containing the source and closed
under transition targets. -/
lemma Path.target_mem {M : LabAut A L Q} {q p : Q} (S : List Q)
    (hS : ∀ t ∈ M.δ, (t.2.2.2 : Q) ∈ S) :
    ∀ {ts : List (Q × List A × L × Q)}, M.Path q ts p → q ∈ S → p ∈ S := by
  intro ts
  induction ts generalizing q with
  | nil => intro h hq; exact (Path.eq_of_nil h) ▸ hq
  | cons t ts ih =>
      intro h _
      obtain ⟨_, ht, hpath⟩ := Path.cons_inv h
      exact ih hpath (hS _ ht)

/-- A path that visits no state twice is short. -/
lemma Path.length_lt_of_nodup {M : LabAut A L Q} {q p : Q} {ts : List (Q × List A × L × Q)}
    (S : List Q) (hS : ∀ t ∈ M.δ, (t.2.2.2 : Q) ∈ S) (h : M.Path q ts p) (hq : q ∈ S)
    (hnd : (statesOf q ts).Nodup) : ts.length < S.length := by
  have hsub : statesOf q ts ⊆ S := fun r hr => Path.mem_of_statesOf S hS h hq r hr
  have := (hnd.subperm hsub).length_le
  simp only [statesOf_length] at this
  omega

/-- Every path can be replaced by a short path with the same endpoints. -/
lemma Path.exists_short {M : LabAut A L Q} (S : List Q) (hS : ∀ t ∈ M.δ, (t.2.2.2 : Q) ∈ S)
    {q p : Q} {ts : List (Q × List A × L × Q)} (h : M.Path q ts p) (hq : q ∈ S) :
    ∃ ts', M.Path q ts' p ∧ ts'.length < S.length := by
  generalize hn : ts.length = n
  induction n using Nat.strong_induction_on generalizing ts q with
  | _ n ih =>
    by_cases hnd : (statesOf q ts).Nodup
    · exact ⟨ts, h, Path.length_lt_of_nodup S hS h hq hnd⟩
    · obtain ⟨ts₁, ts₂, ts₃, r, hsplit, hne, h₁, h₂, h₃⟩ := Path.loop_of_not_nodup h hnd
      have hlen : (ts₁ ++ ts₃).length < ts.length := by
        subst hsplit
        have : ts₂.length ≠ 0 := by simpa using hne
        simp only [List.length_append]
        omega
      exact ih (ts₁ ++ ts₃).length (by omega) (h₁.append h₃) hq rfl

/-- Pigeonhole: a path that is at least as long as the state list contains a
nonempty loop of length at most the number of states. -/
lemma Path.small_loop {M : LabAut A L Q} (S : List Q) (hS : ∀ t ∈ M.δ, (t.2.2.2 : Q) ∈ S)
    {q p : Q} {ts : List (Q × List A × L × Q)} (h : M.Path q ts p) (hq : q ∈ S)
    (hlen : S.length ≤ ts.length) :
    ∃ (ts₁ ts₂ ts₃ : List (Q × List A × L × Q)) (r : Q),
      ts = ts₁ ++ ts₂ ++ ts₃ ∧ ts₂ ≠ [] ∧ ts₂.length ≤ S.length ∧
        M.Path q ts₁ r ∧ M.Path r ts₂ r ∧ M.Path r ts₃ p := by
  set n := S.length with hn
  have hcat : ts.take n ++ ts.drop n = ts := List.take_append_drop n ts
  obtain ⟨m, hpre, hrest⟩ := Path.split_append (hcat ▸ h)
  have hprelen : (ts.take n).length = n := by
    rw [List.length_take]; omega
  have hnd : ¬ (statesOf q (ts.take n)).Nodup := by
    intro hcon
    have := Path.length_lt_of_nodup S hS hpre hq hcon
    omega
  obtain ⟨ts₁, ts₂, ts₃, r, hsplit, hne, h₁, h₂, h₃⟩ := Path.loop_of_not_nodup hpre hnd
  refine ⟨ts₁, ts₂, ts₃ ++ ts.drop n, r, ?_, hne, ?_, h₁, h₂, h₃.append hrest⟩
  · have hassoc : ts₁ ++ ts₂ ++ (ts₃ ++ ts.drop n) = (ts₁ ++ ts₂ ++ ts₃) ++ ts.drop n := by simp
    rw [hassoc, ← hsplit, hcat]
  · have hL := congrArg List.length hsplit
    rw [hprelen] at hL
    simp only [List.length_append] at hL
    omega

end LabAut
end Lax132576Proofs.Transducers
