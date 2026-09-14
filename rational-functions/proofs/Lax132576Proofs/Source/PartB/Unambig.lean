/-
Unambiguity by means of the lexicographically least accepting run.

Let `M` be an nfa with output in the ε-free normal form of Lemma
`lemma:eliminate-epsilon-transitions`: in every accepting run over a nonempty input each transition
reads exactly one letter, and the accepting runs over the empty input consist of a single
transition.

Fix a linear order on the transitions of `M` and on its states.  Every run over
a fixed nonempty input then has exactly one transition per letter, so the runs
over a fixed input are compared by the *key*

```
  runKey q₀ (t₁ … tₙ) = rq q₀ · Kⁿ + rk t₁ · Kⁿ⁻¹ + … + rk tₙ ,
```

where `rk` ranks the transitions below `K` and `rq` ranks the states.  Two
distinct runs over the same input have distinct keys, so among the accepting
runs over an input there is exactly one whose key is least.

The automaton `unambAut` keeps track, along a run, of the set of states that are
reachable by a run over the same input with a smaller key; it accepts if the run
ends in a final state and none of the smaller runs does, that is, if the run is
the least accepting run.  The empty input is dealt with by two extra states,
carrying one transition producing a fixed output.

The result is `exists_unambiguous_of_epsFree`: every ε-free nfa with output
whose relation is total contains an unambiguous one with the same domain.
-/
import Lax132576Proofs.Source.PartB.EpsElim
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Unambig

open LabAut NFAO

/-- The type of transitions of an nfa with output. -/
abbrev Tr (A B Q : Type) := Q × List A × List B × Q

variable {A B Q : Type}

/-- A finite set of a type can be ranked injectively by an initial segment of
the naturals. -/
lemma exists_rank {α : Type} {s : Set α} (hs : s.Finite) :
    ∃ (n : ℕ) (f : α → ℕ), (∀ t ∈ s, f t < n) ∧ Set.InjOn f s := by
  classical
  have : Finite s := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine ⟨n, fun t => if h : t ∈ s then (e ⟨t, h⟩ : Fin n).val else 0, ?_, ?_⟩
  · intro t ht
    simp only [dif_pos ht]
    exact (e ⟨t, ht⟩).isLt
  · intro t ht t' ht' h
    simp only [dif_pos ht, dif_pos ht'] at h
    have := e.injective (Fin.ext h)
    exact congrArg Subtype.val this

section

variable (M : NFAO A B Q)

/-- The automaton `M` with only the transitions that read exactly one letter. -/
def letterAut : NFAO A B Q where
  init := M.init
  final := M.final
  δ := {t ∈ M.δ | t.2.1.length = 1}
  δ_finite := M.δ_finite.subset (fun _ ht => ht.1)

@[simp] lemma letterAut_init : (letterAut M).init = M.init := rfl

@[simp] lemma letterAut_final : (letterAut M).final = M.final := rfl

lemma letterAut_delta_mem {t : Tr A B Q} :
    t ∈ (letterAut M).δ ↔ t ∈ M.δ ∧ t.2.1.length = 1 := Iff.rfl

lemma letterAut_delta_subset : (letterAut M).δ ⊆ M.δ := fun _ ht => ht.1

/-- Along a path of the one-letter automaton, the input has one letter per
transition. -/
lemma letterPath_length {q p : Q} {ts : List (Tr A B Q)} (h : (letterAut M).Path q ts p) :
    (inputOf ts).length = ts.length := by
  induction h with
  | nil q => simp
  | @cons q u l q' ts p ht _ ih =>
      simp only [inputOf_cons, List.length_append, List.length_cons, ih]
      have : u.length = 1 := ht.2
      omega

/-- A path of the one-letter automaton over the empty input is empty. -/
lemma letterPath_nil {q p : Q} {ts : List (Tr A B Q)} (h : (letterAut M).Path q ts p)
    (hin : inputOf ts = []) : ts = [] ∧ q = p := by
  have hlen := letterPath_length M h
  rw [hin] at hlen
  have : ts = [] := List.eq_nil_of_length_eq_zero hlen.symm
  subst this
  cases h
  exact ⟨rfl, rfl⟩

/-- A path can be split at its last transition. -/
lemma path_snoc_iff {L : Type} {N : LabAut A L Q} {q p : Q} {ts : List (Q × List A × L × Q)}
    {t : Q × List A × L × Q} :
    N.Path q (ts ++ [t]) p ↔ N.Path q ts t.1 ∧ t ∈ N.δ ∧ t.2.2.2 = p := by
  constructor
  · intro h
    induction ts generalizing q with
    | nil =>
        simp only [List.nil_append] at h
        cases h with
        | cons ht hrest =>
            cases hrest
            exact ⟨Path.nil _, ht, rfl⟩
    | cons t' ts ih =>
        simp only [List.cons_append] at h
        cases h with
        | cons ht hrest =>
            obtain ⟨h1, h2, h3⟩ := ih hrest
            exact ⟨Path.cons ht h1, h2, h3⟩
  · rintro ⟨h1, h2, rfl⟩
    refine h1.append ?_
    exact Path.cons h2 (Path.nil _)

/-- A path of the one-letter automaton over a nonempty input ends with a
transition. -/
lemma letterPath_snoc {q p : Q} {ts : List (Tr A B Q)} (h : (letterAut M).Path q ts p)
    {w : List A} {a : A} (hin : inputOf ts = w ++ [a]) :
    ∃ (ts' : List (Tr A B Q)) (t : Tr A B Q), ts = ts' ++ [t] ∧ inputOf ts' = w ∧
      t.2.1 = [a] := by
  have hlen := letterPath_length M h
  rw [hin] at hlen
  have hne : ts ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    simp at hlen
  obtain ⟨ts', t, rfl⟩ : ∃ ts' t, ts = ts' ++ [t] := by
    rcases List.eq_nil_or_concat ts with rfl | ⟨ts', t, rfl⟩
    · exact absurd rfl hne
    · exact ⟨ts', t, by simp⟩
  have hsplit : inputOf (ts' ++ [t]) = inputOf ts' ++ t.2.1 := by
    simp [inputOf]
  rw [hsplit] at hin
  have hcard : (t.2.1).length = 1 := by
    have := path_snoc_iff.mp h
    exact this.2.1.2
  obtain ⟨b, hb⟩ : ∃ b, t.2.1 = [b] := by
    match hcase : t.2.1 with
    | [] => rw [hcase] at hcard; simp at hcard
    | [b] => exact ⟨b, rfl⟩
    | b :: c :: r => rw [hcase] at hcard; simp at hcard
  rw [hb] at hin
  have := List.append_inj' hin rfl
  exact ⟨ts', t, rfl, this.1, by rw [hb]; rw [← this.2]⟩

end

section

variable (M : NFAO A B Q) (rk : Tr A B Q → ℕ) (K : ℕ) (rq : Q → ℕ)

/-- The key of a run: the number whose base-`K` digits are the ranks of the
transitions, with the rank of the first state in front. -/
def runKey (q₀ : Q) (ts : List (Tr A B Q)) : ℕ :=
  ts.foldl (fun n t => n * K + rk t) (rq q₀)

@[simp] lemma runKey_nil (q₀ : Q) : runKey rk K rq q₀ [] = rq q₀ := rfl

lemma runKey_snoc (q₀ : Q) (ts : List (Tr A B Q)) (t : Tr A B Q) :
    runKey rk K rq q₀ (ts ++ [t]) = runKey rk K rq q₀ ts * K + rk t := by
  simp [runKey, List.foldl_append]

/-- The states that are reachable from a state of `S` by one transition reading
`u`. -/
def stepSet (S : Set Q) (u : List A) : Set Q :=
  {p | ∃ r ∈ S, ∃ y, (r, u, y, p) ∈ (letterAut M).δ}

/-- The set of states tracked after taking the transition `t` from a state whose
set of "smaller" states is `S`. -/
def nxt (S : Set Q) (t : Tr A B Q) : Set Q :=
  stepSet M S t.2.1 ∪
    {p | ∃ y, (t.1, t.2.1, y, p) ∈ (letterAut M).δ ∧ rk (t.1, t.2.1, y, p) < rk t}

/-- The initial states with a smaller rank than `q`. -/
def initSet (q : Q) : Set Q := {p | p ∈ M.init ∧ rq p < rq q}

/-- The states reachable by a run over the same input with a strictly smaller
key. -/
def smallerReach (q₀ : Q) (ts : List (Tr A B Q)) : Set Q :=
  {p | ∃ q₀' ∈ M.init, ∃ ts', (letterAut M).Path q₀' ts' p ∧ inputOf ts' = inputOf ts ∧
    runKey rk K rq q₀' ts' < runKey rk K rq q₀ ts}

end

/-! ### Arithmetic of keys -/

lemma digit_lt_of_lt {x y u v K : ℕ} (hu : u < K) (hxy : x < y) : x * K + u < y * K + v := by
  have h1 : x * K + K ≤ y * K := by
    have : (x + 1) * K ≤ y * K := Nat.mul_le_mul_right K hxy
    simpa [Nat.succ_mul] using this
  exact lt_of_lt_of_le (Nat.add_lt_add_left hu _) (le_trans h1 (Nat.le_add_right _ _))

lemma digit_lt_iff {x y u v K : ℕ} (hu : u < K) (hv : v < K) :
    x * K + u < y * K + v ↔ x < y ∨ (x = y ∧ u < v) := by
  constructor
  · intro h
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact Or.inl hlt
    · subst heq; exact Or.inr ⟨rfl, Nat.lt_of_add_lt_add_left h⟩
    · exact absurd h (asymm (digit_lt_of_lt hv hgt))
  · rintro (hlt | ⟨rfl, hlt⟩)
    · exact digit_lt_of_lt hu hlt
    · exact Nat.add_lt_add_left hlt _

lemma digit_eq_of_eq {x y u v K : ℕ} (hu : u < K) (hv : v < K) (h : x * K + u = y * K + v) :
    x = y ∧ u = v := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (digit_lt_of_lt hu hlt))
  · subst heq; exact ⟨rfl, Nat.add_left_cancel h⟩
  · exact absurd h.symm (ne_of_lt (digit_lt_of_lt hv hgt))

section

variable (M : NFAO A B Q) (rk : Tr A B Q → ℕ) (K : ℕ) (rq : Q → ℕ)

/-- Two runs of the same length with the same key have the same first state and
the same sequence of ranks. -/
lemma runKey_inj (hK : ∀ t ∈ M.δ, rk t < K) :
    ∀ (ts ts' : List (Tr A B Q)) (q₀ q₀' : Q), ts.length = ts'.length →
      (∀ t ∈ ts, t ∈ M.δ) → (∀ t ∈ ts', t ∈ M.δ) →
      runKey rk K rq q₀ ts = runKey rk K rq q₀' ts' →
      rq q₀ = rq q₀' ∧ ts.map rk = ts'.map rk := by
  intro ts
  induction ts using List.reverseRecOn with
  | nil =>
      intro ts' q₀ q₀' hlen _ _ hkey
      have : ts' = [] := by
        simpa [List.length_eq_zero_iff, eq_comm] using hlen
      subst this
      exact ⟨hkey, rfl⟩
  | append_singleton ts t ih =>
      intro ts' q₀ q₀' hlen hmem hmem' hkey
      obtain ⟨ts'', t', rfl⟩ : ∃ ts'' t', ts' = ts'' ++ [t'] := by
        rcases List.eq_nil_or_concat ts' with rfl | ⟨ts'', t', rfl⟩
        · simp at hlen
        · exact ⟨ts'', t', by simp⟩
      rw [runKey_snoc, runKey_snoc] at hkey
      have ht : t ∈ M.δ := hmem t (by simp)
      have ht' : t' ∈ M.δ := hmem' t' (by simp)
      obtain ⟨h1, h2⟩ := digit_eq_of_eq (hK t ht) (hK t' ht') hkey
      have hlen' : ts.length = ts''.length := by simpa using hlen
      obtain ⟨h3, h4⟩ := ih ts'' q₀ q₀' hlen'
        (fun s hs => hmem s (by simp [hs])) (fun s hs => hmem' s (by simp [hs])) h1
      exact ⟨h3, by simp [h4, h2]⟩

/-- Every transition of a path is a transition of the automaton. -/
lemma path_mem_delta {L : Type} {N : LabAut A L Q} {q p : Q} {ts : List (Q × List A × L × Q)}
    (h : N.Path q ts p) : ∀ t ∈ ts, t ∈ N.δ := by
  induction h with
  | nil q => simp
  | @cons q u l q' ts p ht _ ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ht
      · exact ih s hs

/-- The end state of a path is determined by its first state and its
transitions. -/
lemma path_end_unique {L : Type} {N : LabAut A L Q} {q p p' : Q}
    {ts : List (Q × List A × L × Q)} (h : N.Path q ts p) (h' : N.Path q ts p') : p = p' := by
  induction h generalizing p' with
  | nil q => cases h'; rfl
  | @cons q u l q' ts p ht hpath ih =>
      cases h' with
      | cons ht' hpath' => exact ih hpath'

/-- Transitions of `M` are determined by their rank. -/
lemma list_eq_of_map_rk_eq (hrk : Set.InjOn rk M.δ) :
    ∀ (ts ts' : List (Tr A B Q)), (∀ t ∈ ts, t ∈ M.δ) → (∀ t ∈ ts', t ∈ M.δ) →
      ts.map rk = ts'.map rk → ts = ts' := by
  intro ts
  induction ts with
  | nil => intro ts' _ _ h; simpa [eq_comm] using h
  | cons s ss ih =>
      intro ts' hm hm' h
      cases ts' with
      | nil => simp at h
      | cons s' ss' =>
          simp only [List.map_cons, List.cons.injEq] at h
          have hs : s = s' := hrk (hm s (by simp)) (hm' s' (by simp)) h.1
          have := ih ss' (fun t ht => hm t (by simp [ht])) (fun t ht => hm' t (by simp [ht])) h.2
          rw [hs, this]

/-- Two runs of the same length with the same key are equal. -/
lemma run_eq_of_runKey_eq (hK : ∀ t ∈ M.δ, rk t < K) (hrk : Set.InjOn rk M.δ)
    (hrq : Function.Injective rq) {ts ts' : List (Tr A B Q)} {q₀ q₀' : Q}
    (hlen : ts.length = ts'.length) (hm : ∀ t ∈ ts, t ∈ M.δ) (hm' : ∀ t ∈ ts', t ∈ M.δ)
    (hkey : runKey rk K rq q₀ ts = runKey rk K rq q₀' ts') : q₀ = q₀' ∧ ts = ts' := by
  obtain ⟨h1, h2⟩ := runKey_inj M rk K rq hK ts ts' q₀ q₀' hlen hm hm' hkey
  exact ⟨hrq h1, list_eq_of_map_rk_eq M rk hrk ts ts' hm hm' h2⟩

lemma smallerReach_nil (q₀ : Q) : smallerReach M rk K rq q₀ [] = initSet M rq q₀ := by
  ext p
  constructor
  · rintro ⟨q₀', hq₀', ts', hpath, hin, hkey⟩
    obtain ⟨rfl, rfl⟩ := letterPath_nil M hpath (by simpa using hin)
    exact ⟨hq₀', by simpa [runKey] using hkey⟩
  · rintro ⟨hp, hlt⟩
    exact ⟨p, hp, [], Path.nil _, rfl, by simpa [runKey] using hlt⟩

lemma smallerReach_snoc (hK : ∀ t ∈ M.δ, rk t < K) (hrk : Set.InjOn rk M.δ)
    (hrq : Function.Injective rq)
    {q₀ q : Q} {ts : List (Tr A B Q)} (hpath : (letterAut M).Path q₀ ts q)
    (hq₀ : q₀ ∈ M.init) {t : Tr A B Q} (ht : t ∈ (letterAut M).δ) (htq : t.1 = q) :
    smallerReach M rk K rq q₀ (ts ++ [t]) = nxt M rk (smallerReach M rk K rq q₀ ts) t := by
  have hinsnoc : inputOf (ts ++ [t]) = inputOf ts ++ t.2.1 := by simp [inputOf]
  obtain ⟨a, ha⟩ : ∃ a, t.2.1 = [a] := by
    have hcard : (t.2.1).length = 1 := ht.2
    match hcase : t.2.1 with
    | [] => rw [hcase] at hcard; simp at hcard
    | [b] => exact ⟨b, rfl⟩
    | b :: c :: r => rw [hcase] at hcard; simp at hcard
  ext p
  constructor
  · rintro ⟨q₀', hq₀', ts'', hpath'', hin'', hkey⟩
    rw [hinsnoc, ha] at hin''
    obtain ⟨ts', t', rfl, hin', ht'a⟩ := letterPath_snoc M hpath'' hin''
    obtain ⟨hpath', ht'δ, ht'p⟩ := path_snoc_iff.mp hpath''
    rw [runKey_snoc, runKey_snoc] at hkey
    have hb1 : rk t' < K := hK t' ht'δ.1
    have hb2 : rk t < K := hK t ht.1
    rcases (digit_lt_iff hb1 hb2).mp hkey with hlt | ⟨heq, hlt⟩
    · left
      refine ⟨t'.1, ⟨q₀', hq₀', ts', hpath', hin', hlt⟩, t'.2.2.1, ?_⟩
      have : (t'.1, t.2.1, t'.2.2.1, p) = t' := by
        rw [ha, ← ht'a, ← ht'p]
      rw [this]
      exact ht'δ
    · right
      obtain ⟨rfl, rfl⟩ := run_eq_of_runKey_eq M rk K rq hK hrk hrq
        (ts := ts) (ts' := ts') (q₀ := q₀) (q₀' := q₀')
        (by
          have h1 := letterPath_length M hpath
          have h2 := letterPath_length M hpath'
          rw [hin'] at h2
          omega)
        (fun s hs => (path_mem_delta hpath s hs).1)
        (fun s hs => (path_mem_delta hpath' s hs).1) heq.symm
      have hend : t'.1 = q := path_end_unique hpath' hpath
      refine ⟨t'.2.2.1, ?_, ?_⟩
      · have : (t.1, t.2.1, t'.2.2.1, p) = t' := by
          rw [ha, ← ht'a, ← ht'p, htq, ← hend]
        rw [this]; exact ht'δ
      · have : (t.1, t.2.1, t'.2.2.1, p) = t' := by
          rw [ha, ← ht'a, ← ht'p, htq, ← hend]
        rw [this]; exact hlt
  · rintro (⟨r, ⟨q₀', hq₀', ts', hpath', hin', hkey'⟩, y, hy⟩ | ⟨y, hy, hylt⟩)
    · refine ⟨q₀', hq₀', ts' ++ [(r, t.2.1, y, p)], ?_, ?_, ?_⟩
      · exact path_snoc_iff.mpr ⟨hpath', hy, rfl⟩
      · simpa [inputOf] using hin'
      · rw [runKey_snoc, runKey_snoc]
        exact digit_lt_of_lt (hK _ hy.1) hkey'
    · refine ⟨q₀, hq₀, ts ++ [(t.1, t.2.1, y, p)], ?_, ?_, ?_⟩
      · exact path_snoc_iff.mpr ⟨by rw [htq]; exact hpath, hy, rfl⟩
      · simp [inputOf]
      · rw [runKey_snoc, runKey_snoc]
        exact Nat.add_lt_add_left hylt _

end

/-! ### The unambiguous automaton -/

section

variable (M : NFAO A B Q) (rk : Tr A B Q → ℕ) (K : ℕ) (rq : Q → ℕ)

/-- The states of the unambiguous automaton: a state of `M` together with the
set of states reachable by a smaller run, plus two states for the empty
input. -/
abbrev USt (Q : Type) : Type := (Q × Set Q) ⊕ Bool

/-- The set of tracked states after a run. -/
def Sfold (S : Set Q) (ts : List (Tr A B Q)) : Set Q := ts.foldl (fun S t => nxt M rk S t) S

@[simp] lemma Sfold_nil (S : Set Q) : Sfold M rk S [] = S := rfl

lemma Sfold_cons (S : Set Q) (t : Tr A B Q) (ts : List (Tr A B Q)) :
    Sfold M rk S (t :: ts) = Sfold M rk (nxt M rk S t) ts := rfl

lemma Sfold_snoc (S : Set Q) (ts : List (Tr A B Q)) (t : Tr A B Q) :
    Sfold M rk S (ts ++ [t]) = nxt M rk (Sfold M rk S ts) t := by
  simp [Sfold, List.foldl_append]

/-- The run of the unambiguous automaton corresponding to a run of `M`. -/
def liftRun (S : Set Q) : List (Tr A B Q) → List (USt Q × List A × List B × USt Q)
  | [] => []
  | t :: ts => (Sum.inl (t.1, S), t.2.1, t.2.2.1, Sum.inl (t.2.2.2, nxt M rk S t)) ::
      liftRun (nxt M rk S t) ts

lemma liftRun_input (S : Set Q) (ts : List (Tr A B Q)) :
    inputOf (liftRun M rk S ts) = inputOf ts := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih => simp [liftRun, ih]

lemma liftRun_inputs (S : Set Q) (ts : List (Tr A B Q)) :
    ∀ t ∈ liftRun M rk S ts, t.2.1 ∈ ts.map (fun t => t.2.1) := by
  induction ts generalizing S with
  | nil => simp [liftRun]
  | cons t ts ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · simp
      · exact List.mem_cons_of_mem _ (ih _ s hs)

lemma liftRun_output (S : Set Q) (ts : List (Tr A B Q)) :
    outputOf (liftRun M rk S ts) = outputOf ts := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih => simp [liftRun, ih]

/-- The unambiguous automaton. -/
def unambAut [Finite Q] (v₀ : List B) : NFAO A B (USt Q) where
  init := {P | (∃ q ∈ M.init, P = Sum.inl (q, initSet M rq q)) ∨ P = Sum.inr false}
  final := {P | (∃ q S, q ∈ M.final ∧ (∀ p ∈ S, p ∉ M.final) ∧ P = Sum.inl (q, S)) ∨
    P = Sum.inr true}
  δ := (fun x : Tr A B Q × Set Q =>
        (Sum.inl (x.1.1, x.2), x.1.2.1, x.1.2.2.1, Sum.inl (x.1.2.2.2, nxt M rk x.2 x.1))) ''
        ((letterAut M).δ ×ˢ (Set.univ : Set (Set Q))) ∪
      {(Sum.inr false, [], v₀, Sum.inr true)}
  δ_finite := by
    refine Set.Finite.union (Set.Finite.image _ ?_) (Set.finite_singleton _)
    exact Set.Finite.prod (letterAut M).δ_finite Set.finite_univ

variable [Finite Q]

lemma unambAut_delta_mem (v₀ : List B) {z : USt Q × List A × List B × USt Q} :
    z ∈ (unambAut M rk rq v₀).δ ↔
      (∃ t ∈ (letterAut M).δ, ∃ S : Set Q,
        z = (Sum.inl (t.1, S), t.2.1, t.2.2.1, Sum.inl (t.2.2.2, nxt M rk S t))) ∨
      z = (Sum.inr false, [], v₀, Sum.inr true) := by
  constructor
  · rintro (⟨⟨t, S⟩, ⟨ht, -⟩, rfl⟩ | hz)
    · exact Or.inl ⟨t, ht, S, rfl⟩
    · exact Or.inr hz
  · rintro (⟨t, ht, S, rfl⟩ | rfl)
    · exact Or.inl ⟨(t, S), ⟨ht, Set.mem_univ _⟩, rfl⟩
    · exact Or.inr rfl

/-- Every run of `M` reading one letter per transition lifts to a run of the
unambiguous automaton. -/
lemma liftRun_path (v₀ : List B) {q₀ q : Q} {ts : List (Tr A B Q)}
    (h : (letterAut M).Path q₀ ts q) (S : Set Q) :
    (unambAut M rk rq v₀).Path (Sum.inl (q₀, S)) (liftRun M rk S ts)
      (Sum.inl (q, Sfold M rk S ts)) := by
  induction h generalizing S with
  | nil q => exact Path.nil _
  | @cons q u l q' ts p ht hpath ih =>
      rw [liftRun, Sfold_cons]
      exact Path.cons ((unambAut_delta_mem M rk rq v₀).mpr
        (Or.inl ⟨(q, u, l, q'), ht, S, rfl⟩)) (ih _)

/-- Conversely, every run of the unambiguous automaton starting in a state of
the first kind comes from a run of `M`. -/
lemma path_of_liftRun (v₀ : List B) {q₀ : Q} {S : Set Q} {P : USt Q}
    {us : List (USt Q × List A × List B × USt Q)}
    (h : (unambAut M rk rq v₀).Path (Sum.inl (q₀, S)) us P) :
    ∃ (ts : List (Tr A B Q)) (q : Q), (letterAut M).Path q₀ ts q ∧
      P = Sum.inl (q, Sfold M rk S ts) ∧ us = liftRun M rk S ts := by
  generalize hP₀ : (Sum.inl (q₀, S) : USt Q) = P₀ at h
  induction h generalizing q₀ S with
  | nil q => exact ⟨[], q₀, Path.nil _, hP₀.symm, rfl⟩
  | @cons p u l p' us r ht hpath ih =>
      subst hP₀
      rcases (unambAut_delta_mem M rk rq v₀).mp ht with ⟨t, htl, S', heq⟩ | heq
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨he1, he2, he3, he4⟩ := heq
        have h2 : q₀ = t.1 ∧ S = S' := by
          have := Sum.inl.inj he1
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨ts, q, hts, hend, hus⟩ := ih (q₀ := t.2.2.2) (S := nxt M rk S t) he4.symm
        refine ⟨t :: ts, q, ?_, ?_, ?_⟩
        · have hteq : t = (t.1, t.2.1, t.2.2.1, t.2.2.2) := rfl
          rw [hteq]
          exact Path.cons htl hts
        · rw [hend, Sfold_cons]
        · rw [liftRun, hus, he2, he3, he4]
      · simp only [Prod.mk.injEq] at heq
        exact absurd heq.1 (by simp)

omit [Finite Q] in
/-- The tracked set along a run started in an initial state is the set of states
reachable by a smaller run. -/
lemma Sfold_eq_smallerReach (hK : ∀ t ∈ M.δ, rk t < K) (hrk : Set.InjOn rk M.δ)
    (hrq : Function.Injective rq) {q₀ q : Q} (hq₀ : q₀ ∈ M.init) :
    ∀ {ts : List (Tr A B Q)}, (letterAut M).Path q₀ ts q →
      Sfold M rk (initSet M rq q₀) ts = smallerReach M rk K rq q₀ ts := by
  intro ts
  induction ts using List.reverseRecOn generalizing q with
  | nil =>
      intro _
      rw [Sfold_nil, smallerReach_nil]
  | append_singleton ts t ih =>
      intro hpath
      obtain ⟨hpre, htδ, hte⟩ := path_snoc_iff.mp hpath
      rw [Sfold_snoc, ih hpre,
        smallerReach_snoc M rk K rq hK hrk hrq hpre hq₀ htδ rfl]

/-- There is no transition leaving the second extra state. -/
lemma path_from_true (v₀ : List B) {P : USt Q}
    {us : List (USt Q × List A × List B × USt Q)}
    (h : (unambAut M rk rq v₀).Path (Sum.inr true) us P) : us = [] ∧ P = Sum.inr true := by
  cases h with
  | nil q => exact ⟨rfl, rfl⟩
  | @cons p u l p' us r ht hrest =>
      exfalso
      rcases (unambAut_delta_mem M rk rq v₀).mp ht with ⟨t, -, S, heq⟩ | heq <;>
        (simp only [Prod.mk.injEq] at heq; exact absurd heq.1 (by simp))

/-- The only run from the first extra state is the extra transition. -/
lemma path_from_false (v₀ : List B) {P : USt Q}
    {us : List (USt Q × List A × List B × USt Q)}
    (h : (unambAut M rk rq v₀).Path (Sum.inr false) us P) :
    (us = [] ∧ P = Sum.inr false) ∨
      (us = [(Sum.inr false, [], v₀, Sum.inr true)] ∧ P = Sum.inr true) := by
  cases h with
  | nil q => exact Or.inl ⟨rfl, rfl⟩
  | @cons p u l p' us r ht hrest =>
      rcases (unambAut_delta_mem M rk rq v₀).mp ht with ⟨t, -, S, heq⟩ | heq
      · exfalso
        simp only [Prod.mk.injEq] at heq
        exact absurd heq.1 (by simp)
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨-, he2, he3, he4⟩ := heq
        subst he4
        obtain ⟨hus, hP⟩ := path_from_true M rk rq v₀ hrest
        exact Or.inr ⟨by rw [hus, he2, he3], hP⟩

end

/-! ### The main theorem -/

/-- A path of `M` all of whose transitions read one letter is a path of the
one-letter automaton. -/
lemma letterPath_of_path {M : NFAO A B Q} {q p : Q} {ts : List (Tr A B Q)}
    (h : M.Path q ts p) (hlen : ∀ t ∈ ts, t.2.1.length = 1) : (letterAut M).Path q ts p := by
  induction h with
  | nil q => exact Path.nil _
  | @cons q u l q' ts p ht hpath ih =>
      exact Path.cons ⟨ht, hlen _ (by simp)⟩ (ih (fun t htm => hlen t (by simp [htm])))

/-- A path of the one-letter automaton is a path of `M`. -/
lemma path_of_letterPath {M : NFAO A B Q} {q p : Q} {ts : List (Tr A B Q)}
    (h : (letterAut M).Path q ts p) : M.Path q ts p := by
  induction h with
  | nil q => exact Path.nil _
  | @cons q u l q' ts p ht hpath ih => exact Path.cons ht.1 ih

/-- **Unambiguisation.**  An nfa with output in ε-free normal form whose
relation is total contains an unambiguous nfa with output with the same
domain. -/
theorem exists_unambiguous_of_epsFree [Finite Q] (M : NFAO A B Q)
    (hef : ∀ ts, M.Accepting ts →
      (inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧ (inputOf ts = [] → ts.length = 1))
    (htot : ∀ w, ∃ v, M.rel w v) :
    ∃ (P : Type) (_ : Finite P) (N : NFAO A B P),
      N.Unambiguous ∧
      (∀ ts, N.Accepting ts →
        (inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧ (inputOf ts = [] → ts.length = 1)) ∧
      ∀ w v, N.rel w v → M.rel w v := by
  classical
  obtain ⟨K, rk, hKb, hrkinj⟩ := exists_rank M.δ_finite
  obtain ⟨rq, hrq⟩ : ∃ rq : Q → ℕ, Function.Injective rq := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin Q
    exact ⟨fun q => (e q : Fin n).val, fun q q' h => e.injective (Fin.ext h)⟩
  obtain ⟨v₀, hv₀⟩ := htot []
  -- no state is both initial and final
  have hif : ∀ q ∈ M.init, q ∉ M.final := by
    intro q hq hq'
    have := (hef [] ⟨q, hq, q, hq', Path.nil q⟩).2 rfl
    simp at this
  set N := unambAut M rk rq v₀ with hN
  have hgadget : (Sum.inr false, ([] : List A), v₀, Sum.inr true) ∈ N.δ :=
    (unambAut_delta_mem M rk rq v₀).mpr (Or.inr rfl)
  have hgadgetAcc : N.Accepting [(Sum.inr false, ([] : List A), v₀, Sum.inr true)] :=
    ⟨Sum.inr false, Or.inr rfl, Sum.inr true, Or.inr rfl,
      Path.cons hgadget (Path.nil _)⟩
  -- the shape of an accepting run of `N`
  have hshape : ∀ (us : List (USt Q × List A × List B × USt Q)), N.Accepting us →
      (us = [(Sum.inr false, ([] : List A), v₀, Sum.inr true)]) ∨
      (∃ (q₀ q : Q) (ts : List (Tr A B Q)), q₀ ∈ M.init ∧ q ∈ M.final ∧
        (letterAut M).Path q₀ ts q ∧ us = liftRun M rk (initSet M rq q₀) ts ∧
        (∀ p ∈ smallerReach M rk K rq q₀ ts, p ∉ M.final)) := by
    rintro us ⟨P₀, hP₀, P₁, hP₁, hpath⟩
    rcases hP₀ with ⟨q₀, hq₀, rfl⟩ | rfl
    · right
      obtain ⟨ts, q, hts, hend, hus⟩ := path_of_liftRun M rk rq v₀ hpath
      subst hend
      rcases hP₁ with ⟨q', S', hq'f, hS', heq⟩ | heq
      · have h2 := Sum.inl.inj heq
        have hq'' : q = q' := congrArg Prod.fst h2
        have hS'' : Sfold M rk (initSet M rq q₀) ts = S' := congrArg Prod.snd h2
        subst hq''
        refine ⟨q₀, q, ts, hq₀, hq'f, hts, hus, ?_⟩
        rw [← Sfold_eq_smallerReach M rk K rq hKb hrkinj hrq hq₀ hts, hS'']
        exact hS'
      · exact absurd heq (by simp)
    · left
      rcases path_from_false M rk rq v₀ hpath with ⟨hus, hP⟩ | ⟨hus, -⟩
      · exfalso
        rw [hP] at hP₁
        rcases hP₁ with ⟨q', S', -, -, heq⟩ | heq
        · exact absurd heq (by simp)
        · exact absurd heq (by simp)
      · exact hus
  refine ⟨USt Q, inferInstance, N, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w = []
    · subst hw
      refine ⟨[(Sum.inr false, ([] : List A), v₀, Sum.inr true)], ⟨hgadgetAcc, rfl⟩, ?_⟩
      rintro us ⟨hacc, hin⟩
      rcases hshape us hacc with h | ⟨q₀, q, ts, hq₀, hqf, hts, hus, -⟩
      · exact h
      · exfalso
        have hin' : inputOf ts = [] := by
          rw [← liftRun_input M rk (initSet M rq q₀) ts, ← hus, hin]
        obtain ⟨rfl, rfl⟩ := letterPath_nil M hts hin'
        exact hif q₀ hq₀ hqf
    · -- nonempty input: the least accepting run
      have hex : ∃ nkey : ℕ, ∃ (q₀ q : Q) (ts : List (Tr A B Q)), q₀ ∈ M.init ∧ q ∈ M.final ∧
          (letterAut M).Path q₀ ts q ∧ inputOf ts = w ∧ runKey rk K rq q₀ ts = nkey := by
        obtain ⟨v, hv⟩ := htot w
        obtain ⟨ts, ⟨q₀, hq₀, q, hq, hpath⟩, hin, -⟩ := hv
        have hlen := (hef ts ⟨q₀, hq₀, q, hq, hpath⟩).1 (by rw [hin]; exact hw)
        exact ⟨runKey rk K rq q₀ ts, q₀, q, ts, hq₀, hq,
          letterPath_of_path hpath hlen, hin, rfl⟩
      set m := Nat.find hex with hm
      obtain ⟨q₀, q, ts, hq₀, hqf, hts, htsin, htskey⟩ := Nat.find_spec hex
      have hmin : ∀ (q₀' q' : Q) (ts' : List (Tr A B Q)), q₀' ∈ M.init → q' ∈ M.final →
          (letterAut M).Path q₀' ts' q' → inputOf ts' = w → m ≤ runKey rk K rq q₀' ts' := by
        intro q₀' q' ts' h1 h2 h3 h4
        by_contra hlt
        push_neg at hlt
        exact Nat.find_min hex hlt ⟨q₀', q', ts', h1, h2, h3, h4, rfl⟩
      have hnosmaller : ∀ p ∈ smallerReach M rk K rq q₀ ts, p ∉ M.final := by
        rintro p ⟨q₀', hq₀', ts', hpath', hin', hkey'⟩ hpf
        have := hmin q₀' p ts' hq₀' hpf hpath' (by rw [hin', htsin])
        omega
      refine ⟨liftRun M rk (initSet M rq q₀) ts, ⟨⟨Sum.inl (q₀, initSet M rq q₀),
        Or.inl ⟨q₀, hq₀, rfl⟩, Sum.inl (q, Sfold M rk (initSet M rq q₀) ts), ?_,
        liftRun_path M rk rq v₀ hts _⟩, ?_⟩, ?_⟩
      · refine Or.inl ⟨q, Sfold M rk (initSet M rq q₀) ts, hqf, ?_, rfl⟩
        rw [Sfold_eq_smallerReach M rk K rq hKb hrkinj hrq hq₀ hts]
        exact hnosmaller
      · rw [liftRun_input M rk (initSet M rq q₀) ts, htsin]
      · rintro us ⟨hacc, hin⟩
        rcases hshape us hacc with h | ⟨q₀', q', ts', hq₀', hq'f, hts', hus, hns⟩
        · exfalso
          rw [h] at hin
          exact hw (by simpa using hin.symm)
        · have hin' : inputOf ts' = w := by
            rw [← liftRun_input M rk (initSet M rq q₀') ts', ← hus, hin]
          -- the run `ts'` is also minimal
          have hle : runKey rk K rq q₀' ts' ≤ runKey rk K rq q₀ ts := by
            by_contra hgt
            push_neg at hgt
            exact hns q ⟨q₀, hq₀, ts, hts, by rw [htsin, hin'], hgt⟩ hqf
          have hge : m ≤ runKey rk K rq q₀' ts' := hmin q₀' q' ts' hq₀' hq'f hts' hin'
          have hkeyeq : runKey rk K rq q₀ ts = runKey rk K rq q₀' ts' := by omega
          obtain ⟨rfl, rfl⟩ := run_eq_of_runKey_eq M rk K rq hKb hrkinj hrq
            (by
              have h1 := letterPath_length M hts
              have h2 := letterPath_length M hts'
              rw [htsin] at h1
              rw [hin'] at h2
              omega)
            (fun s hs => (path_mem_delta hts s hs).1)
            (fun s hs => (path_mem_delta hts' s hs).1) hkeyeq
          rw [hus]
  · -- the automaton is ε-free
    intro us hacc
    rcases hshape us hacc with h | ⟨q₀, q, ts, hq₀, hqf, hts, hus, -⟩
    · rw [h]
      refine ⟨fun hne => absurd (by simp [inputOf]) hne, fun _ => rfl⟩
    · constructor
      · intro _ t ht
        rw [hus] at ht
        obtain ⟨t', ht', heq⟩ := List.mem_map.mp (liftRun_inputs M rk _ ts t ht)
        rw [← heq]
        exact (path_mem_delta hts t' ht').2
      · intro hnil
        exfalso
        have hin' : inputOf ts = [] := by
          rw [← liftRun_input M rk (initSet M rq q₀) ts, ← hus, hnil]
        obtain ⟨rfl, rfl⟩ := letterPath_nil M hts hin'
        exact hif q₀ hq₀ hqf
  · rintro w v ⟨us, hacc, hin, hout⟩
    rcases hshape us hacc with h | ⟨q₀, q, ts, hq₀, hqf, hts, hus, -⟩
    · rw [h] at hin hout
      have hw : w = [] := by simpa using hin.symm
      have hv : v = v₀ := by simpa [outputOf] using hout.symm
      rw [hw, hv]
      exact hv₀
    · refine ⟨ts, ⟨q₀, hq₀, q, hqf, path_of_letterPath hts⟩, ?_, ?_⟩
      · rw [← hin, hus, liftRun_input]
      · rw [← hout, hus, liftRun_output]

end Unambig

end Lax132576Proofs.Transducers
