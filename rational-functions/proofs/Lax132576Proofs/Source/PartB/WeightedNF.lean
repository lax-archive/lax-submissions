/- Normal forms for weighted automata (Section *Rational relations and weighted automata* of
*Transducers*).

A weighted automaton, as defined in `RequestProject/PartB/LabAut.lean`, is an automaton whose
transitions are labelled by an input *string* and a weight, and whose value on an input string is
the sum of the weights of the accepting runs. In order to compare the runs of a weighted automaton
with the runs of another automaton (which is what the product construction of Lemma
`lem:closure-weighted-automata-precomposition` does) one first brings it into a normal form:

* at most one state is both initial and final (`UniqueEmptyRun`), so that the
  runs can be grouped according to their first state;
* every transition reads at most one letter (`Atomic`), so that a run can be
  split at the boundary between two letters;
* every state lies on some accepting run (`AllUseful`), which together with the
  requirement that every input has finitely many accepting runs makes the set of
  paths with a fixed source, target and input string finite.

The linear representation of an automaton in this normal form is constructed in
`RequestProject/PartB/WeightedLinRep.lean`.
-/
import Lax132576Proofs.Source.PartB.LabAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace WNF

open LabAut

variable {B S : Type}

/-! ## Generalities on paths -/

section Paths

variable {Q : Type} {M : LabAut B S Q}

lemma path_src {q p : Q} {t : Q × List B × S × Q} {ts : List (Q × List B × S × Q)}
    (h : M.Path q (t :: ts) p) : t.1 = q := by
  cases h with
  | cons _ _ => rfl

lemma path_head_mem {q p : Q} {t : Q × List B × S × Q} {ts : List (Q × List B × S × Q)}
    (h : M.Path q (t :: ts) p) : t ∈ M.δ := by
  cases h with
  | cons ht _ => exact ht

lemma path_tail {q p : Q} {t : Q × List B × S × Q} {ts : List (Q × List B × S × Q)}
    (h : M.Path q (t :: ts) p) : M.Path t.2.2.2 ts p := by
  cases h with
  | cons _ hts => exact hts

lemma path_cons_iff {q p : Q} {t : Q × List B × S × Q} {ts : List (Q × List B × S × Q)} :
    M.Path q (t :: ts) p ↔ t.1 = q ∧ t ∈ M.δ ∧ M.Path t.2.2.2 ts p := by
  constructor
  · intro h; exact ⟨path_src h, path_head_mem h, path_tail h⟩
  · rintro ⟨rfl, ht, htail⟩
    exact LabAut.Path.cons (q := t.1) (u := t.2.1) (l := t.2.2.1) (q' := t.2.2.2) ht htail

lemma path_nil_iff {q p : Q} : M.Path q [] p ↔ q = p := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact LabAut.Path.nil q

lemma path_mem {q p : Q} {ts : List (Q × List B × S × Q)} (h : M.Path q ts p) :
    ∀ t ∈ ts, t ∈ M.δ := by
  induction h with
  | nil => simp
  | cons ht _ ih =>
      intro t htmem
      rcases List.mem_cons.mp htmem with rfl | hmem
      · exact ht
      · exact ih t hmem

lemma path_split {q p : Q} {ts us : List (Q × List B × S × Q)} (h : M.Path q (ts ++ us) p) :
    ∃ r, M.Path q ts r ∧ M.Path r us p := by
  induction ts generalizing q with
  | nil => exact ⟨q, LabAut.Path.nil q, by simpa using h⟩
  | cons t ts ih =>
      rw [List.cons_append, path_cons_iff] at h
      obtain ⟨hsrc, hmem, htail⟩ := h
      obtain ⟨r, h1, h2⟩ := ih htail
      exact ⟨r, by rw [path_cons_iff]; exact ⟨hsrc, hmem, h1⟩, h2⟩

lemma path_target_eq {q : Q} : ∀ {σ : List (Q × List B × S × Q)} {p p' : Q},
    M.Path q σ p → M.Path q σ p' → σ ≠ [] → p = p' := by
  intro σ
  induction σ generalizing q with
  | nil => intro p p' _ _ hne; exact absurd rfl hne
  | cons t σ' ih =>
      intro p p' h h' _
      rw [path_cons_iff] at h h'
      rcases σ' with _ | ⟨t', σ''⟩
      · rw [path_nil_iff] at h h'
        exact h.2.2.symm.trans h'.2.2
      · exact ih h.2.2 h'.2.2 (by simp)

/-- There are only finitely many paths of bounded length. -/
lemma bounded_paths_finite (M : LabAut B S Q) : ∀ n : ℕ,
    {σ : List (Q × List B × S × Q) | (∀ t ∈ σ, t ∈ M.δ) ∧ σ.length ≤ n}.Finite := by
  intro n
  induction n with
  | zero =>
      refine (Set.finite_singleton []).subset ?_
      rintro σ ⟨-, hlen⟩
      exact List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
  | succ n ih =>
      refine ((Set.finite_singleton []).union
        ((M.δ_finite.prod ih).image (fun p => p.1 :: p.2))).subset ?_
      rintro σ ⟨hmem, hlen⟩
      cases σ with
      | nil => exact Or.inl rfl
      | cons t σ' =>
          refine Or.inr ⟨(t, σ'), ⟨hmem t (by simp), fun t' ht' => hmem t' (by simp [ht']), ?_⟩, rfl⟩
          simp only [List.length_cons] at hlen
          show σ'.length ≤ n
          omega

/-- The set of accepting runs of `M` that start at `q` and read `v`. -/
def accFrom (M : LabAut B S Q) (q : Q) (v : List B) : Set (List (Q × List B × S × Q)) :=
  {ts | (∃ p ∈ M.final, M.Path q ts p) ∧ inputOf ts = v}

/-- The sum of the weights of the accepting runs that start at `q` and read `v`. -/
noncomputable def accWeight [Semiring S] (M : LabAut B S Q) (q : Q) (v : List B) : S :=
  ∑ᶠ ts ∈ accFrom M q v, weightOf ts

/-- At most one state is both initial and final; equivalently, the empty run is
accepting for at most one initial state. -/
def UniqueEmptyRun (M : LabAut B S Q) : Prop :=
  ∀ q ∈ M.init, ∀ q' ∈ M.init, q ∈ M.final → q' ∈ M.final → q = q'

/-- A state lies on some accepting run. -/
def Useful (M : LabAut B S Q) (q : Q) : Prop :=
  ∃ q₀ ∈ M.init, ∃ p ∈ M.final, ∃ ts₁ ts₂, M.Path q₀ ts₁ q ∧ M.Path q ts₂ p

/-- Every state lies on some accepting run. -/
def AllUseful (M : LabAut B S Q) : Prop := ∀ q : Q, Useful M q

/-- For every source, target and input string there are only finitely many
paths. -/
def PathsFinite (M : LabAut B S Q) : Prop :=
  ∀ (q p : Q) (x : List B), {σ | M.Path q σ p ∧ inputOf σ = x}.Finite

/-- Every transition reads at most one letter. -/
def Atomic (M : LabAut B S Q) : Prop := ∀ t ∈ M.δ, t.2.1.length ≤ 1

lemma acceptingOn_eq_biUnion (M : LabAut B S Q) (v : List B) :
    M.acceptingOn v = ⋃ q ∈ M.init, accFrom M q v := by
  ext ts
  simp only [LabAut.acceptingOn, LabAut.Accepting, accFrom, Set.mem_setOf_eq,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨q, hq, p, hp, hpath⟩, hin⟩
    exact ⟨q, hq, ⟨p, hp, hpath⟩, hin⟩
  · rintro ⟨q, hq, ⟨p, hp, hpath⟩, hin⟩
    exact ⟨⟨q, hq, p, hp, hpath⟩, hin⟩

/-- If at most one state is both initial and final, the accepting runs are
partitioned according to their initial state. -/
lemma wEval_eq_finsum_accWeight [Semiring S] [Finite Q] {M : LabAut B S Q} (hu : UniqueEmptyRun M)
    (hfin : M.FinitelyManyRuns) (v : List B) :
    M.wEval v = ∑ᶠ q ∈ M.init, accWeight M q v := by
  classical
  have hdisj : M.init.PairwiseDisjoint (fun q => accFrom M q v) := by
    intro q hq q' hq' hne
    refine Set.disjoint_left.mpr ?_
    rintro ts ⟨⟨p, hp, hpath⟩, hin⟩ ⟨⟨p', hp', hpath'⟩, -⟩
    cases ts with
    | nil =>
        rw [path_nil_iff] at hpath hpath'
        subst hpath; subst hpath'
        exact hne (hu q hq q' hq' hp hp')
    | cons t ts =>
        exact hne ((path_src hpath).symm.trans (path_src hpath'))
  have hsub : ∀ q ∈ M.init, (accFrom M q v).Finite := by
    intro q hq
    refine (hfin v).subset ?_
    intro ts hts
    rw [acceptingOn_eq_biUnion]
    exact Set.mem_biUnion hq hts
  rw [LabAut.wEval, acceptingOn_eq_biUnion,
    finsum_mem_biUnion hdisj (Set.toFinite _) hsub]
  rfl

end Paths

/-! ## Making the empty run unique

The value of a weighted automaton is a sum over *lists of transitions*, so the
empty run is counted only once even if several initial states are final.  We
therefore replace every initial state by a copy which is not final, and add a
separate initial-and-final state `phi` accounting for the empty run. -/

section InitCopy

variable {Q : Type} [Semiring S] (M : LabAut B S Q)

/-- The states of `initCopy M`: the old states, a copy of every state used as an
initial state, and the state `phi` responsible for the empty run. -/
abbrev ISt (Q : Type) := Q ⊕ Q ⊕ Unit

/-- The copy of a state, used as an initial state of `initCopy M`. -/
def cop (q : Q) : ISt Q := Sum.inr (Sum.inl q)

/-- The state of `initCopy M` responsible for the empty run. -/
def phi : ISt Q := Sum.inr (Sum.inr ())

/-- A transition between old states of `initCopy M`. -/
def liftTr (t : Q × List B × S × Q) : ISt Q × List B × S × ISt Q :=
  (Sum.inl t.1, t.2.1, t.2.2.1, Sum.inl t.2.2.2)

/-- The copy of a transition leaving an initial state. -/
def copTr (t : Q × List B × S × Q) : ISt Q × List B × S × ISt Q :=
  (cop t.1, t.2.1, t.2.2.1, Sum.inl t.2.2.2)

/-- The automaton `M` with the initial states replaced by copies that are not
final, together with a state `phi` accounting for the empty run. -/
def initCopy : LabAut B S (ISt Q) where
  init := cop '' M.init ∪ {x | x = phi ∧ (M.init ∩ M.final).Nonempty}
  final := Sum.inl '' M.final ∪ {x | x = phi ∧ (M.init ∩ M.final).Nonempty}
  δ := liftTr '' M.δ ∪ copTr '' {t ∈ M.δ | t.1 ∈ M.init}
  δ_finite :=
    (M.δ_finite.image _).union ((M.δ_finite.subset (fun _ ht => ht.1)).image _)

/-- The image of a run of `M` in `initCopy M`. -/
def liftRun : List (Q × List B × S × Q) → List (ISt Q × List B × S × ISt Q)
  | [] => []
  | t :: ts => copTr t :: ts.map liftTr

omit [Semiring S] in
lemma liftTr_injective : Function.Injective (liftTr (Q := Q) (B := B) (S := S)) := by
  intro a b hab
  simp only [liftTr, Prod.mk.injEq, Sum.inl.injEq] at hab
  exact Prod.ext hab.1 (Prod.ext hab.2.1 (Prod.ext hab.2.2.1 hab.2.2.2))

omit [Semiring S] in
lemma inputOf_liftRun (ts : List (Q × List B × S × Q)) :
    inputOf (liftRun ts) = inputOf ts := by
  have hmap : ∀ us : List (Q × List B × S × Q),
      inputOf (us.map liftTr) = inputOf us := by
    intro us
    simp [inputOf, List.map_map, Function.comp_def, liftTr]
  cases ts with
  | nil => rfl
  | cons t ts =>
      have := hmap ts
      simp only [inputOf, List.map_map] at this
      simp [liftRun, inputOf, copTr, List.map_map, this]

lemma weightOf_liftRun (ts : List (Q × List B × S × Q)) :
    weightOf (liftRun ts) = weightOf ts := by
  have hmap : ∀ us : List (Q × List B × S × Q),
      weightOf (us.map liftTr) = weightOf us := by
    intro us
    simp [weightOf, labelsOf, List.map_map, Function.comp_def, liftTr]
  cases ts with
  | nil => rfl
  | cons t ts =>
      have := hmap ts
      simp only [weightOf, labelsOf, List.map_map] at this
      simp [liftRun, weightOf, labelsOf, copTr, List.map_map, this]

omit [Semiring S] in
lemma path_liftRun {q p : Q} {ts : List (Q × List B × S × Q)} (h : M.Path q ts p) :
    (initCopy M).Path (Sum.inl q) (ts.map liftTr) (Sum.inl p) := by
  induction h with
  | nil q => exact LabAut.Path.nil _
  | @cons q u l q' ts p ht _ ih =>
      refine LabAut.Path.cons (q := Sum.inl q) (u := u) (l := l) (q' := Sum.inl q') ?_ ih
      exact Or.inl ⟨_, ht, rfl⟩

omit [Semiring S] in
lemma unlift_path {q : Q} {τ : List (ISt Q × List B × S × ISt Q)} {x : ISt Q}
    (h : (initCopy M).Path (Sum.inl q) τ x) :
    ∃ (p : Q) (ts : List (Q × List B × S × Q)),
      x = Sum.inl p ∧ τ = ts.map liftTr ∧ M.Path q ts p := by
  induction τ generalizing q with
  | nil =>
      rw [path_nil_iff] at h
      exact ⟨q, [], h.symm, rfl, LabAut.Path.nil q⟩
  | cons t τ ih =>
      rw [path_cons_iff] at h
      obtain ⟨hsrc, hmem, htail⟩ := h
      rcases hmem with ⟨t₀, ht₀, rfl⟩ | ⟨t₀, ht₀, rfl⟩
      · have hq : t₀.1 = q := by simpa [liftTr] using hsrc
        obtain ⟨p, ts, hx, hτ, hpath⟩ := ih (q := t₀.2.2.2) (by simpa [liftTr] using htail)
        refine ⟨p, t₀ :: ts, hx, by simp [hτ], ?_⟩
        rw [path_cons_iff]
        exact ⟨hq, ht₀, hpath⟩
      · exact absurd hsrc (by simp [copTr, cop])

omit [Semiring S] in
lemma liftRun_accepting {v : List B} {ts : List (Q × List B × S × Q)}
    (h : ts ∈ M.acceptingOn v) : liftRun ts ∈ (initCopy M).acceptingOn v := by
  obtain ⟨⟨q, hq, p, hp, hpath⟩, hin⟩ := h
  refine ⟨?_, by rw [inputOf_liftRun, hin]⟩
  cases ts with
  | nil =>
      rw [path_nil_iff] at hpath
      subst hpath
      have hne : (M.init ∩ M.final).Nonempty := ⟨q, hq, hp⟩
      exact ⟨phi, Or.inr ⟨rfl, hne⟩, phi, Or.inr ⟨rfl, hne⟩, LabAut.Path.nil _⟩
  | cons t ts =>
      have hsrc : t.1 = q := path_src hpath
      refine ⟨cop q, Or.inl ⟨q, hq, rfl⟩, Sum.inl p, Or.inl ⟨p, hp, rfl⟩, ?_⟩
      rw [liftRun, path_cons_iff]
      refine ⟨by simp [copTr, hsrc], Or.inr ⟨t, ⟨path_head_mem hpath, by rw [hsrc]; exact hq⟩, rfl⟩,
        ?_⟩
      exact path_liftRun M (path_tail hpath)

omit [Semiring S] in
lemma liftRun_injective : Function.Injective (liftRun (Q := Q) (B := B) (S := S)) := by
  intro ts us h
  cases ts with
  | nil =>
      cases us with
      | nil => rfl
      | cons u us => simp [liftRun] at h
  | cons t ts =>
      cases us with
      | nil => simp [liftRun] at h
      | cons u us =>
          simp only [liftRun, List.cons.injEq] at h
          obtain ⟨h1, h2⟩ := h
          have ht : t = u := by
            simp only [copTr, cop, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq] at h1
            exact Prod.ext h1.1 (Prod.ext h1.2.1 (Prod.ext h1.2.2.1 h1.2.2.2))
          rw [ht, List.map_injective_iff.mpr liftTr_injective h2]

omit [Semiring S] in
lemma acceptingOn_initCopy (v : List B) :
    (initCopy M).acceptingOn v = liftRun '' M.acceptingOn v := by
  apply Set.Subset.antisymm
  · rintro τ ⟨⟨x, hx, y, hy, hpath⟩, hin⟩
    cases τ with
    | nil =>
        rw [path_nil_iff] at hpath
        subst hpath
        have hxphi : (M.init ∩ M.final).Nonempty := by
          rcases hx with ⟨q, hq, rfl⟩ | ⟨rfl, hne⟩
          · rcases hy with ⟨p, hp, hpe⟩ | ⟨he, -⟩
            · exact absurd hpe.symm (by simp [cop])
            · exact absurd he (by simp [cop, phi])
          · exact hne
        refine ⟨[], ⟨⟨hxphi.choose, hxphi.choose_spec.1, hxphi.choose, hxphi.choose_spec.2,
          LabAut.Path.nil _⟩, ?_⟩, rfl⟩
        simpa using hin
    | cons t τ =>
        rw [path_cons_iff] at hpath
        obtain ⟨hsrc, hmem, htail⟩ := hpath
        rcases hx with ⟨q, hq, rfl⟩ | ⟨rfl, -⟩
        · rcases hmem with ⟨t₀, ht₀, rfl⟩ | ⟨t₀, ht₀, rfl⟩
          · exact absurd hsrc (by simp [liftTr, cop])
          · have hq0 : t₀.1 = q := by simpa [copTr, cop] using hsrc
            obtain ⟨p, ts, hy', hτ, hpath'⟩ :=
              unlift_path M (q := t₀.2.2.2) (by simpa [copTr] using htail)
            subst hy'
            have hpfin : p ∈ M.final := by
              rcases hy with ⟨p', hp', hpe⟩ | ⟨he, -⟩
              · cases hpe; exact hp'
              · exact absurd he (by simp [phi])
            refine ⟨t₀ :: ts, ⟨⟨q, hq, p, hpfin, ?_⟩, ?_⟩, ?_⟩
            · rw [path_cons_iff]; exact ⟨hq0, ht₀.1, hpath'⟩
            · rw [← hin, hτ]
              exact (inputOf_liftRun (t₀ :: ts)).symm
            · rw [liftRun, hτ]
        · rcases hmem with ⟨t₀, ht₀, rfl⟩ | ⟨t₀, ht₀, rfl⟩
          · exact absurd hsrc (by simp [liftTr, phi])
          · exact absurd hsrc (by simp [copTr, cop, phi])
  · rintro τ ⟨ts, hts, rfl⟩
    exact liftRun_accepting M hts

lemma wEval_initCopy (v : List B) : (initCopy M).wEval v = M.wEval v := by
  rw [LabAut.wEval, LabAut.wEval, acceptingOn_initCopy]
  refine (finsum_mem_eq_of_bijOn liftRun ?_ ?_).symm
  · exact ⟨fun ts hts => ⟨ts, hts, rfl⟩, fun a _ b _ h => liftRun_injective h, fun x hx => hx⟩
  · intro ts _
    exact (weightOf_liftRun ts).symm

omit [Semiring S] in
lemma finitelyManyRuns_initCopy (hfin : M.FinitelyManyRuns) :
    (initCopy M).FinitelyManyRuns := by
  intro v
  rw [acceptingOn_initCopy]
  exact (hfin v).image _

omit [Semiring S] in
lemma uniqueEmptyRun_initCopy : UniqueEmptyRun (initCopy M) := by
  have key : ∀ x, x ∈ (initCopy M).init → x ∈ (initCopy M).final → x = phi := by
    rintro x (⟨q, hq, rfl⟩ | ⟨rfl, -⟩) hxf
    · rcases hxf with ⟨p, hp, hpe⟩ | ⟨he, -⟩
      · exact absurd hpe.symm (by simp [cop])
      · exact absurd he (by simp [cop, phi])
    · rfl
  intro x hx y hy hxf hyf
  rw [key x hx hxf, key y hy hyf]

end InitCopy

/-! ## Atomisation

Every transition is split into a chain of transitions, the first of which reads
nothing and carries the whole weight, while the remaining ones read one letter
each and carry the weight `1`.  A state of the atomised automaton is either an
old state, or a pair consisting of a transition and the part of its input string
that has not been read yet. -/

section Atomize

variable {Q : Type} [Semiring S] (M : LabAut B S Q)

/-- The states of the atomised automaton. -/
abbrev ASt (Q B S : Type) := Q ⊕ ((Q × List B × S × Q) × List B)

/-- The state of the atomised automaton in which the transition `t` still has to
read `x`. -/
def cfg (t : Q × List B × S × Q) : List B → ASt Q B S
  | [] => Sum.inl t.2.2.2
  | b :: y => Sum.inr (t, b :: y)

/-- The chain of transitions reading the remaining input `x` of `t`. -/
def steps (t : Q × List B × S × Q) :
    List B → List (ASt Q B S × List B × S × ASt Q B S)
  | [] => []
  | b :: y => (Sum.inr (t, b :: y), [b], (1 : S), cfg t y) :: steps t y

/-- The chain of transitions replacing a single transition `t`. -/
def trav (t : Q × List B × S × Q) : List (ASt Q B S × List B × S × ASt Q B S) :=
  (Sum.inl t.1, [], t.2.2.1, cfg t t.2.1) :: steps t t.2.1

/-- The image of a run of `M` in the atomised automaton. -/
def atomRun (ts : List (Q × List B × S × Q)) : List (ASt Q B S × List B × S × ASt Q B S) :=
  (ts.map trav).flatten

/-- The atomised automaton: every transition reads at most one letter. -/
def atom : LabAut B S (ASt Q B S) where
  init := Sum.inl '' M.init
  final := Sum.inl '' M.final
  δ := {tr | (∃ t ∈ M.δ, tr = (Sum.inl t.1, [], t.2.2.1, cfg t t.2.1)) ∨
        (∃ t ∈ M.δ, ∃ (b : B) (y : List B), b :: y <:+ t.2.1 ∧
          tr = (Sum.inr (t, b :: y), [b], (1 : S), cfg t y))}
  δ_finite := by
    have hsuf : ∀ l : List B, {x : List B | x <:+ l}.Finite := by
      intro l
      refine (l.tails.finite_toSet).subset ?_
      intro x hx
      exact (List.mem_tails x l).mpr hx
    have h1 : {tr : ASt Q B S × List B × S × ASt Q B S |
        ∃ t ∈ M.δ, tr = (Sum.inl t.1, [], t.2.2.1, cfg t t.2.1)}.Finite := by
      refine (M.δ_finite.image (fun t => (Sum.inl t.1, [], t.2.2.1, cfg t t.2.1))).subset ?_
      rintro tr ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    have hF : {p : (Q × List B × S × Q) × List B | p.1 ∈ M.δ ∧ p.2 <:+ p.1.2.1}.Finite := by
      refine (M.δ_finite.biUnion (fun t _ => ((hsuf t.2.1).image (fun x => (t, x))))).subset ?_
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact Set.mem_biUnion ht ⟨x, hx, rfl⟩
    have h2 : {tr : ASt Q B S × List B × S × ASt Q B S |
        ∃ t ∈ M.δ, ∃ (b : B) (y : List B), b :: y <:+ t.2.1 ∧
          tr = (Sum.inr (t, b :: y), [b], (1 : S), cfg t y)}.Finite := by
      refine (hF.image (fun p => (Sum.inr p, p.2.take 1, (1 : S), cfg p.1 (p.2.drop 1)))).subset ?_
      rintro tr ⟨t, ht, b, y, hsu, rfl⟩
      exact ⟨(t, b :: y), ⟨ht, hsu⟩, by simp⟩
    exact h1.union h2
omit [Semiring S] in
lemma inputOf_append (ts us : List (Q × List B × S × Q)) :
    inputOf (ts ++ us) = inputOf ts ++ inputOf us := by
  simp [inputOf]

lemma mem_atom_entry {t : Q × List B × S × Q} (ht : t ∈ M.δ) :
    ((Sum.inl t.1 : ASt Q B S), [], t.2.2.1, cfg t t.2.1) ∈ (atom M).δ := Or.inl ⟨t, ht, rfl⟩

lemma mem_atom_step {t : Q × List B × S × Q} (ht : t ∈ M.δ) {b : B} {y : List B}
    (hsuf : b :: y <:+ t.2.1) :
    ((Sum.inr (t, b :: y) : ASt Q B S), [b], (1 : S), cfg t y) ∈ (atom M).δ :=
  Or.inr ⟨t, ht, b, y, hsuf, rfl⟩

lemma inputOf_steps (t : Q × List B × S × Q) (x : List B) : inputOf (steps t x) = x := by
  induction x with
  | nil => rfl
  | cons b y ih =>
      simp only [steps, inputOf_cons, ih]
      rfl

lemma weightOf_steps (t : Q × List B × S × Q) (x : List B) : weightOf (steps t x) = (1 : S) := by
  induction x with
  | nil => rfl
  | cons b y ih => simp [steps, weightOf, labelsOf] at ih ⊢; simp [ih]

lemma inputOf_trav (t : Q × List B × S × Q) : inputOf (trav t) = t.2.1 := by
  rw [trav, inputOf_cons, inputOf_steps]
  rfl

lemma weightOf_trav (t : Q × List B × S × Q) : weightOf (trav t) = t.2.2.1 := by
  have := weightOf_steps (S := S) t t.2.1
  simp [trav, weightOf, labelsOf] at this ⊢
  simp [this]

lemma steps_path {t : Q × List B × S × Q} (ht : t ∈ M.δ) :
    ∀ {x : List B}, x <:+ t.2.1 → (atom M).Path (cfg t x) (steps t x) (Sum.inl t.2.2.2) := by
  intro x
  induction x with
  | nil => intro _; exact LabAut.Path.nil _
  | cons b y ih =>
      intro hsuf
      have hy : y <:+ t.2.1 := (List.suffix_cons b y).trans hsuf
      exact LabAut.Path.cons (M := atom M) (q := Sum.inr (t, b :: y)) (u := [b]) (l := (1 : S))
        (q' := cfg t y) (mem_atom_step M ht hsuf) (ih hy)

lemma trav_path {t : Q × List B × S × Q} (ht : t ∈ M.δ) :
    (atom M).Path (Sum.inl t.1) (trav t) (Sum.inl t.2.2.2) :=
  LabAut.Path.cons (M := atom M) (q := Sum.inl t.1) (u := []) (l := t.2.2.1)
    (q' := cfg t t.2.1) (mem_atom_entry M ht) (steps_path M ht (List.suffix_refl _))

lemma atomRun_path {q p : Q} {ts : List (Q × List B × S × Q)} (h : M.Path q ts p) :
    (atom M).Path (Sum.inl q) (atomRun ts) (Sum.inl p) := by
  induction h with
  | nil q => exact LabAut.Path.nil _
  | @cons q u l q' ts p ht _ ih =>
      have h1 := trav_path M (t := (q, u, l, q')) ht
      have : atomRun ((q, u, l, q') :: ts) = trav (q, u, l, q') ++ atomRun ts := by
        simp [atomRun]
      rw [this]
      exact h1.append ih

lemma inputOf_atomRun (ts : List (Q × List B × S × Q)) :
    inputOf (atomRun ts) = inputOf ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have : atomRun (t :: ts) = trav t ++ atomRun ts := by simp [atomRun]
      rw [this, inputOf_append, ih, inputOf_trav, inputOf_cons]

lemma weightOf_atomRun (ts : List (Q × List B × S × Q)) :
    weightOf (atomRun ts) = weightOf ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have : atomRun (t :: ts) = trav t ++ atomRun ts := by simp [atomRun]
      rw [this, weightOf_append, ih, weightOf_trav, weightOf_cons]

/-- A path leaving a state inside the transition `t` starts by finishing the
chain of `t`. -/
lemma from_inner {t : Q × List B × S × Q} :
    ∀ {x : List B}, ∀ {τ : List (ASt Q B S × List B × S × ASt Q B S)} {p : Q},
      (atom M).Path (cfg t x) τ (Sum.inl p) →
      ∃ τ', τ = steps t x ++ τ' ∧ (atom M).Path (Sum.inl t.2.2.2) τ' (Sum.inl p) := by
  intro x
  induction x with
  | nil => intro τ p h; exact ⟨τ, by simp [steps], h⟩
  | cons b y ih =>
      intro τ p h
      cases τ with
      | nil =>
          rw [path_nil_iff] at h
          exact absurd h (by simp [cfg])
      | cons e τ₀ =>
          rw [path_cons_iff] at h
          obtain ⟨hsrc, hmem, htail⟩ := h
          have he : e = (Sum.inr (t, b :: y), [b], (1 : S), cfg t y) := by
            rcases hmem with ⟨t', ht', rfl⟩ | ⟨t', ht', b', y', hsuf', rfl⟩
            · exact absurd hsrc (by simp [cfg])
            · have : (Sum.inr (t', b' :: y') : ASt Q B S) = Sum.inr (t, b :: y) := by
                simpa [cfg] using hsrc
              simp only [Sum.inr.injEq, Prod.mk.injEq] at this
              obtain ⟨ht'', hby⟩ := this
              subst ht''
              rw [List.cons.injEq] at hby
              obtain ⟨rfl, rfl⟩ := hby
              rfl
          subst he
          obtain ⟨τ', hτ', hpath⟩ := ih (τ := τ₀) (p := p) (by simpa using htail)
          exact ⟨τ', by simp [steps, hτ'], hpath⟩

/-- Every path between old states of the atomised automaton is the image of a
path of `M`. -/
lemma from_old : ∀ (n : ℕ) (τ : List (ASt Q B S × List B × S × ASt Q B S)) (q p : Q),
    τ.length ≤ n → (atom M).Path (Sum.inl q) τ (Sum.inl p) →
    ∃ ts, M.Path q ts p ∧ τ = atomRun ts := by
  intro n
  induction n with
  | zero =>
      intro τ q p hlen h
      have : τ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this
      rw [path_nil_iff] at h
      cases h
      exact ⟨[], LabAut.Path.nil _, rfl⟩
  | succ n ih =>
      intro τ q p hlen h
      cases τ with
      | nil =>
          rw [path_nil_iff] at h
          cases h
          exact ⟨[], LabAut.Path.nil _, rfl⟩
      | cons e τ₀ =>
          rw [path_cons_iff] at h
          obtain ⟨hsrc, hmem, htail⟩ := h
          rcases hmem with ⟨t, ht, rfl⟩ | ⟨t, ht, b, y, hsuf, rfl⟩
          · have hq : t.1 = q := by simpa using hsrc
            obtain ⟨τ', hτ', hpath⟩ := from_inner M (x := t.2.1) (τ := τ₀) (p := p) (by simpa using htail)
            have hlen' : τ'.length ≤ n := by
              have : τ₀.length = (steps t t.2.1).length + τ'.length := by
                rw [hτ']; simp
              simp only [List.length_cons] at hlen
              omega
            obtain ⟨ts, hts, hτ⟩ := ih τ' t.2.2.2 p hlen' hpath
            refine ⟨t :: ts, ?_, ?_⟩
            · rw [path_cons_iff]; exact ⟨hq, ht, hts⟩
            · have : atomRun (t :: ts) = trav t ++ atomRun ts := by simp [atomRun]
              rw [this, ← hτ, trav, hτ']
              simp
          · exact absurd hsrc (by simp)

lemma trav_ne_nil (t : Q × List B × S × Q) : trav t ≠ [] := by simp [trav]

lemma atomRun_injective : Function.Injective (atomRun (Q := Q) (B := B) (S := S)) := by
  intro ts
  induction ts with
  | nil =>
      intro us h
      cases us with
      | nil => rfl
      | cons u us =>
          exfalso
          have : atomRun (u :: us) = trav u ++ atomRun us := by simp [atomRun]
          rw [this] at h
          simp [atomRun, trav] at h
  | cons t ts ih =>
      intro us h
      cases us with
      | nil =>
          exfalso
          have : atomRun (t :: ts) = trav t ++ atomRun ts := by simp [atomRun]
          rw [this] at h
          simp [atomRun, trav] at h
      | cons u us =>
          have h1 : trav t ++ atomRun ts = trav u ++ atomRun us := by
            simpa [atomRun] using h
          have hhead : (Sum.inl t.1, [], t.2.2.1, cfg t t.2.1) =
              ((Sum.inl u.1, [], u.2.2.1, cfg u u.2.1) : ASt Q B S × List B × S × ASt Q B S) := by
            have := congrArg (fun l => l.head?) h1
            simpa [trav] using this
          have htu : t = u := by
            simp only [Prod.mk.injEq, Sum.inl.injEq] at hhead
            obtain ⟨h11, -, h13, h14⟩ := hhead
            -- the target of the entry transition determines the input string and target state
            cases hx : t.2.1 with
            | nil =>
                cases hy : u.2.1 with
                | nil =>
                    have : t.2.2.2 = u.2.2.2 := by
                      have := h14
                      rw [hx, hy] at this
                      simpa [cfg] using this
                    exact Prod.ext h11 (Prod.ext (by rw [hx, hy]) (Prod.ext h13 this))
                | cons b y =>
                    exfalso
                    have := h14
                    rw [hx, hy] at this
                    simp [cfg] at this
            | cons b y =>
                cases hy : u.2.1 with
                | nil =>
                    exfalso
                    have := h14
                    rw [hx, hy] at this
                    simp [cfg] at this
                | cons b' y' =>
                    have := h14
                    rw [hx, hy] at this
                    simp only [cfg, Sum.inr.injEq, Prod.mk.injEq] at this
                    exact this.1
          subst htu
          have : atomRun ts = atomRun us := by
            exact List.append_cancel_left h1
          rw [ih this]

lemma acceptingOn_atom (v : List B) :
    (atom M).acceptingOn v = atomRun '' M.acceptingOn v := by
  apply Set.Subset.antisymm
  · rintro τ ⟨⟨x, ⟨q, hq, rfl⟩, y, ⟨p, hp, rfl⟩, hpath⟩, hin⟩
    obtain ⟨ts, hts, rfl⟩ := from_old M τ.length τ q p le_rfl hpath
    exact ⟨ts, ⟨⟨q, hq, p, hp, hts⟩, by rw [← hin, inputOf_atomRun]⟩, rfl⟩
  · rintro τ ⟨ts, ⟨⟨q, hq, p, hp, hpath⟩, hin⟩, rfl⟩
    exact ⟨⟨Sum.inl q, ⟨q, hq, rfl⟩, Sum.inl p, ⟨p, hp, rfl⟩, atomRun_path M hpath⟩,
      by rw [inputOf_atomRun, hin]⟩

lemma wEval_atom (v : List B) : (atom M).wEval v = M.wEval v := by
  rw [LabAut.wEval, LabAut.wEval, acceptingOn_atom]
  refine (finsum_mem_eq_of_bijOn atomRun ?_ ?_).symm
  · exact ⟨fun ts hts => ⟨ts, hts, rfl⟩, fun a _ b _ h => atomRun_injective h, fun x hx => hx⟩
  · intro ts _
    exact (weightOf_atomRun ts).symm

lemma finitelyManyRuns_atom (hfin : M.FinitelyManyRuns) : (atom M).FinitelyManyRuns := by
  intro v
  rw [acceptingOn_atom]
  exact (hfin v).image _

lemma atomic_atom : Atomic (atom M) := by
  rintro tr (⟨t, ht, rfl⟩ | ⟨t, ht, b, y, hsuf, rfl⟩) <;> simp

lemma uniqueEmptyRun_atom (hu : UniqueEmptyRun M) : UniqueEmptyRun (atom M) := by
  rintro x ⟨q, hq, rfl⟩ y ⟨q', hq', rfl⟩ ⟨p, hp, hpe⟩ ⟨p', hp', hpe'⟩
  cases hpe; cases hpe'
  rw [hu q hq q' hq' hp hp']

lemma init_atom_finite (h : M.init.Finite) : (atom M).init.Finite := h.image _

end Atomize

/-! ## Restricting to the useful states -/

section Restrict

variable {Q : Type} [Semiring S] (M : LabAut B S Q)

/-- The underlying transition of a transition of the restricted automaton. -/
def unsub (tr : {q : Q // Useful M q} × List B × S × {q : Q // Useful M q}) :
    Q × List B × S × Q := (tr.1.val, tr.2.1, tr.2.2.1, tr.2.2.2.val)

/-- The automaton restricted to the states that lie on an accepting run. -/
def restrict : LabAut B S {q : Q // Useful M q} where
  init := {q | q.val ∈ M.init}
  final := {q | q.val ∈ M.final}
  δ := (unsub M) ⁻¹' M.δ
  δ_finite := by
    refine Set.Finite.preimage ?_ M.δ_finite
    intro a _ b _ hab
    simp only [unsub, Prod.mk.injEq] at hab
    exact Prod.ext (Subtype.ext hab.1) (Prod.ext hab.2.1 (Prod.ext hab.2.2.1
      (Subtype.ext hab.2.2.2)))

omit [Semiring S] in
lemma unsub_injective : Function.Injective (unsub M) := by
  intro a b hab
  simp only [unsub, Prod.mk.injEq] at hab
  exact Prod.ext (Subtype.ext hab.1) (Prod.ext hab.2.1 (Prod.ext hab.2.2.1
    (Subtype.ext hab.2.2.2)))

omit [Semiring S] in
lemma inputOf_map_unsub (ts : List ({q : Q // Useful M q} × List B × S × {q : Q // Useful M q})) :
    inputOf (ts.map (unsub M)) = inputOf ts := by
  simp [inputOf, List.map_map, Function.comp_def, unsub]

lemma weightOf_map_unsub (ts : List ({q : Q // Useful M q} × List B × S × {q : Q // Useful M q})) :
    weightOf (ts.map (unsub M)) = weightOf ts := by
  simp [weightOf, labelsOf, List.map_map, Function.comp_def, unsub]

omit [Semiring S] in
lemma unsub_path {q p : {x : Q // Useful M x}}
    {ts : List ({x : Q // Useful M x} × List B × S × {x : Q // Useful M x})}
    (h : (restrict M).Path q ts p) : M.Path q.val (ts.map (unsub M)) p.val := by
  induction h with
  | nil q => exact LabAut.Path.nil _
  | @cons q u l q' ts p ht _ ih =>
      exact LabAut.Path.cons (M := M) (q := q.val) (u := u) (l := l) (q' := q'.val) ht ih

omit [Semiring S] in
lemma useful_step {q q' p : Q} {u : List B} {l : S}
    {ts : List (Q × List B × S × Q)} (hq : Useful M q) (ht : (q, u, l, q') ∈ M.δ)
    (hpath : M.Path q' ts p) (hp : Useful M p) : Useful M q' := by
  obtain ⟨q₀, hq₀, -, -, ts₁, -, hts₁, -⟩ := hq
  obtain ⟨-, -, p', hp', -, ts₂, -, hts₂⟩ := hp
  refine ⟨q₀, hq₀, p', hp', ts₁ ++ [(q, u, l, q')], ts ++ ts₂, ?_, hpath.append hts₂⟩
  exact hts₁.append (LabAut.Path.cons ht (LabAut.Path.nil q'))

omit [Semiring S] in
lemma sub_path {q p : Q} {ts : List (Q × List B × S × Q)} (h : M.Path q ts p) :
    ∀ (hq : Useful M q) (hp : Useful M p),
      ∃ ts', (restrict M).Path ⟨q, hq⟩ ts' ⟨p, hp⟩ ∧ ts'.map (unsub M) = ts := by
  induction h with
  | nil q => intro hq hp; exact ⟨[], LabAut.Path.nil _, rfl⟩
  | @cons q u l q' ts p ht hpath ih =>
      intro hq hp
      have hq' : Useful M q' := useful_step M hq ht hpath hp
      obtain ⟨ts', hts', hmap⟩ := ih hq' hp
      refine ⟨(⟨q, hq⟩, u, l, ⟨q', hq'⟩) :: ts', ?_, by simp [unsub, hmap]⟩
      exact LabAut.Path.cons (M := restrict M) (q := ⟨q, hq⟩) (u := u) (l := l)
        (q' := ⟨q', hq'⟩) ht hts'

omit [Semiring S] in
lemma acceptingOn_restrict (v : List B) :
    M.acceptingOn v = (fun ts => ts.map (unsub M)) '' (restrict M).acceptingOn v := by
  apply Set.Subset.antisymm
  · rintro ts ⟨⟨q, hq, p, hp, hpath⟩, hin⟩
    have huq : Useful M q := ⟨q, hq, p, hp, [], ts, LabAut.Path.nil q, hpath⟩
    have hup : Useful M p := ⟨q, hq, p, hp, ts, [], hpath, LabAut.Path.nil p⟩
    obtain ⟨ts', hts', hmap⟩ := sub_path M hpath huq hup
    refine ⟨ts', ⟨⟨⟨q, huq⟩, hq, ⟨p, hup⟩, hp, hts'⟩, ?_⟩, hmap⟩
    rw [← inputOf_map_unsub M ts', hmap]
    exact hin
  · rintro ts ⟨ts', ⟨⟨q, hq, p, hp, hpath⟩, hin⟩, rfl⟩
    exact ⟨⟨q.val, hq, p.val, hp, unsub_path M hpath⟩, by rw [inputOf_map_unsub]; exact hin⟩

lemma wEval_restrict (v : List B) : (restrict M).wEval v = M.wEval v := by
  rw [LabAut.wEval, LabAut.wEval, acceptingOn_restrict M v]
  refine finsum_mem_eq_of_bijOn (fun ts => ts.map (unsub M)) ?_ ?_
  · refine ⟨fun ts hts => ⟨ts, hts, rfl⟩, fun a _ b _ hab => ?_, fun x hx => hx⟩
    exact List.map_injective_iff.mpr (unsub_injective M) hab
  · intro ts _
    exact (weightOf_map_unsub M ts).symm

omit [Semiring S] in
lemma finitelyManyRuns_restrict (hfin : M.FinitelyManyRuns) : (restrict M).FinitelyManyRuns := by
  intro v
  refine Set.Finite.of_finite_image (f := fun ts => ts.map (unsub M)) ?_ ?_
  · rw [← acceptingOn_restrict M v]; exact hfin v
  · intro a _ b _ hab
    exact List.map_injective_iff.mpr (unsub_injective M) hab

omit [Semiring S] in
lemma allUseful_restrict : AllUseful (restrict M) := by
  rintro ⟨q, hq⟩
  obtain ⟨q₀, hq₀, p, hp, ts₁, ts₂, hts₁, hts₂⟩ := hq
  have huq : Useful M q := ⟨q₀, hq₀, p, hp, ts₁, ts₂, hts₁, hts₂⟩
  have huq₀ : Useful M q₀ :=
    ⟨q₀, hq₀, p, hp, [], ts₁ ++ ts₂, LabAut.Path.nil q₀, hts₁.append hts₂⟩
  have hup : Useful M p :=
    ⟨q₀, hq₀, p, hp, ts₁ ++ ts₂, [], hts₁.append hts₂, LabAut.Path.nil p⟩
  obtain ⟨us₁, hus₁, -⟩ := sub_path M hts₁ huq₀ huq
  obtain ⟨us₂, hus₂, -⟩ := sub_path M hts₂ huq hup
  exact ⟨⟨q₀, huq₀⟩, hq₀, ⟨p, hup⟩, hp, us₁, us₂, hus₁, hus₂⟩

omit [Semiring S] in
lemma atomic_restrict (h : Atomic M) : Atomic (restrict M) := by
  intro tr htr
  exact h _ htr

omit [Semiring S] in
lemma uniqueEmptyRun_restrict (h : UniqueEmptyRun M) : UniqueEmptyRun (restrict M) := by
  intro x hx y hy hxf hyf
  exact Subtype.ext (h x.val hx y.val hy hxf hyf)

omit [Semiring S] in
lemma init_restrict_finite (h : M.init.Finite) : (restrict M).init.Finite := by
  refine Set.Finite.preimage ?_ h
  intro a _ b _ hab
  exact Subtype.ext hab

omit [Semiring S] in
/-- If the last transition of a nonempty path exists, its target is the end of
the path. -/
lemma path_target_mem {q p : Q} {ts : List (Q × List B × S × Q)} (h : M.Path q ts p) :
    q = p ∨ ∃ t ∈ M.δ, t.2.2.2 = p := by
  induction h with
  | nil q => exact Or.inl rfl
  | @cons q u l q' ts p ht _ ih =>
      rcases ih with rfl | ⟨t, htm, htp⟩
      · exact Or.inr ⟨(q, u, l, q'), ht, rfl⟩
      · exact Or.inr ⟨t, htm, htp⟩

omit [Semiring S] in
/-- There are finitely many useful states. -/
lemma useful_finite (h : M.init.Finite) : {q : Q | Useful M q}.Finite := by
  refine (h.union (M.δ_finite.image (fun t => t.2.2.2))).subset ?_
  rintro q ⟨q₀, hq₀, p, hp, ts₁, ts₂, hts₁, hts₂⟩
  rcases path_target_mem M hts₁ with rfl | ⟨t, htm, htp⟩
  · exact Or.inl hq₀
  · exact Or.inr ⟨t, htm, htp⟩

instance instFiniteUseful (h : M.init.Finite) : Finite {q : Q // Useful M q} :=
  (useful_finite M h).to_subtype

end Restrict

end WNF

end Lax132576Proofs.Transducers
