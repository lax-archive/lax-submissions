/- The hard implication of Theorem `thm:machine-independent-rational-functions`: a continuous
function whose equivalence relation `BoundedVarRel` has finite index is rational.

The proof follows the book.  Let `∼` be the relation `BoundedVarRel f`, and let
`Cls f` be its (finite) set of equivalence classes.  An input string
`w = a₁ ⋯ aₙ` is *annotated* by the classes of its suffixes:

  `ann w = (a₁, [a₂ ⋯ aₙ]) (a₂, [a₃ ⋯ aₙ]) ⋯ (aₙ, [ε])`.

The map `w ↦ ann w` is a rational relation (indeed it is computed by an nfa with
output which guesses the class of the remaining suffix), and the partial
function `g` which maps a correctly annotated string `u` to `f` of its first
components is subsequential: it is continuous because the correctly annotated
strings form a regular language and `f` is continuous, and it has bounded
variation because the annotation of the last position of a common prefix
determines the class of the two suffixes.  Composing the two rational relations
gives a rational relation whose graph is that of `f`.
-/
import Lax132576Proofs.Source.PartB.RatIndex
import Lax132576Proofs.Source.PartB.SubseqRat
import Lax132576Proofs.Source.PartB.SubseqChar
import Lax132576Proofs.Source.PartB.RatComp
import Lax132576Proofs.Source.PartB.RatCont
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace RatAnnot

variable {A B : Type}

/-! ### The equivalence classes of `BoundedVarRel` -/

/-- The set of equivalence classes of the relation `BoundedVarRel f`. -/
def Cls (f : List A → List B) : Type :=
  {C : Set (List A) // ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}

/-- The equivalence class of a string. -/
def cls (f : List A → List B) (w : List A) : Cls f :=
  ⟨{w₂ | BoundedVarRel f w w₂}, ⟨w, rfl⟩⟩

variable {f : List A → List B}

lemma cls_eq_iff {w w' : List A} : cls f w = cls f w' ↔ BoundedVarRel f w w' := by
  constructor
  · intro h
    have h' : {w₂ | BoundedVarRel f w w₂} = {w₂ | BoundedVarRel f w' w₂} := congrArg Subtype.val h
    have : w' ∈ {w₂ | BoundedVarRel f w w₂} := by
      rw [h']; exact BoundedVarRel.refl w'
    exact this
  · intro h
    refine Subtype.ext ?_
    ext w₂
    exact ⟨fun h2 => h.symm.trans h2, fun h2 => h.trans h2⟩

/-- A representative of an equivalence class. -/
noncomputable def rep (q : Cls f) : List A := q.2.choose

lemma cls_rep (q : Cls f) : cls f (rep q) = q := Subtype.ext q.2.choose_spec.symm

/-- Prepending a letter to (a representative of) a class. -/
noncomputable def clsCons (a : A) (q : Cls f) : Cls f := cls f (a :: rep q)

lemma clsCons_cls (a : A) (w : List A) : clsCons a (cls f w) = cls f (a :: w) := by
  have h : BoundedVarRel f (rep (cls f w)) w := cls_eq_iff.1 (cls_rep (cls f w))
  exact cls_eq_iff.2 (h.cons a)

/-! ### Annotated strings -/

/-- The annotation of a string: every letter is decorated with the class of the
suffix that follows it. -/
def ann (f : List A → List B) : List A → List (A × Cls f)
  | [] => []
  | a :: w => (a, cls f w) :: ann f w

@[simp] lemma ann_nil : ann f [] = [] := rfl

@[simp] lemma ann_cons (a : A) (w : List A) : ann f (a :: w) = (a, cls f w) :: ann f w := rfl

@[simp] lemma ann_map_fst (w : List A) : (ann f w).map Prod.fst = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- A string of annotated letters is *consistent* if every letter is decorated
with the class of the suffix that follows it. -/
def Consistent (f : List A → List B) : List (A × Cls f) → Prop
  | [] => True
  | p :: u => p.2 = cls f (u.map Prod.fst) ∧ Consistent f u

@[simp] lemma consistent_nil : Consistent f ([] : List (A × Cls f)) := trivial

@[simp] lemma consistent_cons (p : A × Cls f) (u : List (A × Cls f)) :
    Consistent f (p :: u) ↔ p.2 = cls f (u.map Prod.fst) ∧ Consistent f u := Iff.rfl

lemma consistent_ann (w : List A) : Consistent f (ann f w) := by
  induction w with
  | nil => trivial
  | cons a w ih => exact ⟨by simp, ih⟩

/-- In a consistent string, the class decorating a position is the class of the
suffix that follows it. -/
lemma consistent_split (x : List (A × Cls f)) (p : A × Cls f) (y : List (A × Cls f))
    (h : Consistent f (x ++ p :: y)) : p.2 = cls f (y.map Prod.fst) := by
  induction x with
  | nil => exact h.1
  | cons r x ih => exact ih h.2

/-! ### The partial function on annotated strings -/

open Classical in
/-- The partial function computed on annotated strings: consistent strings are
mapped to the value of `f` on the underlying string. -/
noncomputable def g (f : List A → List B) (u : List (A × Cls f)) : Option (List B) :=
  if Consistent f u then some (f (u.map Prod.fst)) else none

lemma g_eq_some_iff (u : List (A × Cls f)) (v : List B) :
    g f u = some v ↔ Consistent f u ∧ v = f (u.map Prod.fst) := by
  classical
  unfold g
  by_cases h : Consistent f u
  · rw [if_pos h]
    simp [h, eq_comm]
  · rw [if_neg h]
    simp [h]

lemma g_ann (w : List A) : g f (ann f w) = some (f w) := by
  rw [g_eq_some_iff]
  exact ⟨consistent_ann w, by simp⟩

/-! ### Regularity of the language of consistent strings -/

/-- Pulling back a regular language along the map that forgets the
annotations. -/
lemma isRegular_map_fst {K : Language A} (hK : K.IsRegular) :
    Language.IsRegular ({u : List (A × Cls f) | u.map Prod.fst ∈ K} : Language (A × Cls f)) := by
  obtain ⟨σ, hσ, D, rfl⟩ := hK
  refine ⟨σ, hσ, ⟨fun q p => D.step q p.1, D.start, D.accept⟩, ?_⟩
  have key : ∀ (u : List (A × Cls f)) (q : σ),
      DFA.evalFrom ⟨fun q p => D.step q p.1, D.start, D.accept⟩ q u
        = D.evalFrom q (u.map Prod.fst) := by
    intro u
    induction u with
    | nil => intro q; rfl
    | cons p u ih =>
      intro q
      simp only [List.map_cons, DFA.evalFrom, List.foldl_cons] at *
      exact ih (D.step q p.1)
  ext u
  simp only [DFA.mem_accepts, DFA.eval]
  rw [key u]
  rfl

open Classical in
/-- The transition function of the automaton recognising consistent strings.
The state records the class decorating the previous position, if any; the outer
`none` is an error state. -/
noncomputable def consStep (f : List A → List B) :
    Option (Option (Cls f)) → (A × Cls f) → Option (Option (Cls f))
  | none, _ => none
  | some none, (_, q) => some (some q)
  | some (some p), (a, q) => if p = clsCons a q then some (some q) else none

/-- The automaton recognising consistent strings. -/
noncomputable def consDFA (f : List A → List B) : DFA (A × Cls f) (Option (Option (Cls f))) where
  step := consStep f
  start := some none
  accept := {some none, some (some (cls f []))}

lemma consDFA_sink (u : List (A × Cls f)) : (consDFA f).evalFrom none u = none := by
  induction u with
  | nil => rfl
  | cons p u ih =>
    simp only [DFA.evalFrom, List.foldl_cons] at *
    exact ih

lemma consDFA_eval_some (p : Cls f) (u : List (A × Cls f)) :
    (consDFA f).evalFrom (some (some p)) u ∈ (consDFA f).accept
      ↔ (p = cls f (u.map Prod.fst) ∧ Consistent f u) := by
  classical
  induction u generalizing p with
  | nil =>
    simp only [List.map_nil, consistent_nil, and_true]
    have hev : (consDFA f).evalFrom (some (some p)) [] = some (some p) := rfl
    rw [hev]
    constructor
    · intro h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact (Option.some_injective _ (Option.some_injective _ h))
    · intro h
      exact Or.inr (congrArg (fun s => some (some s)) h)
  | cons r u ih =>
    have hstep : (consDFA f).evalFrom (some (some p)) (r :: u)
        = (consDFA f).evalFrom (consStep f (some (some p)) r) u := by
      simp [DFA.evalFrom, consDFA]
    rw [hstep]
    obtain ⟨a, q⟩ := r
    by_cases hp : p = clsCons a q
    · have : consStep f (some (some p)) (a, q) = some (some q) := by
        simp only [consStep]; rw [if_pos hp]
      rw [this, ih q]
      simp only [List.map_cons, consistent_cons]
      constructor
      · rintro ⟨hq, hcons⟩
        refine ⟨?_, hq, hcons⟩
        rw [hp, hq, clsCons_cls]
      · rintro ⟨hpc, hq, hcons⟩
        exact ⟨hq, hcons⟩
    · have : consStep f (some (some p)) (a, q) = none := by
        simp only [consStep]; rw [if_neg hp]
      rw [this, consDFA_sink]
      constructor
      · intro h
        exfalso
        rcases h with h | h <;> simp at h
      · rintro ⟨hpc, hq, hcons⟩
        refine absurd ?_ hp
        simp only [List.map_cons] at hpc
        rw [hpc, show q = cls f (List.map Prod.fst u) from hq, clsCons_cls]

lemma consDFA_accepts : (consDFA f).accepts = {u : List (A × Cls f) | Consistent f u} := by
  classical
  ext u
  simp only [DFA.mem_accepts, DFA.eval]
  cases u with
  | nil => exact iff_of_true (Or.inl rfl) (consistent_nil (f := f))
  | cons r u =>
    obtain ⟨a, q⟩ := r
    have hstep : (consDFA f).evalFrom (consDFA f).start ((a, q) :: u)
        = (consDFA f).evalFrom (some (some q)) u := by
      simp [DFA.evalFrom, consDFA, consStep]
    rw [hstep, consDFA_eval_some]
    exact Iff.rfl

lemma isRegular_consistent [Finite (Cls f)] :
    Language.IsRegular ({u : List (A × Cls f) | Consistent f u} : Language (A × Cls f)) := by
  classical
  haveI : Fintype (Cls f) := Fintype.ofFinite _
  exact ⟨Option (Option (Cls f)), inferInstance, consDFA f, consDFA_accepts⟩

/-! ### `g` is subsequential -/

lemma partialContinuous_g [Finite (Cls f)] (hcont : Continuous f) : PartialContinuous (g f) := by
  classical
  intro L hL
  have h1 : Language.IsRegular ({u : List (A × Cls f) | Consistent f u} : Language (A × Cls f)) :=
    isRegular_consistent
  have h2 : Language.IsRegular
      ({u : List (A × Cls f) | u.map Prod.fst ∈ {w : List A | f w ∈ L}} : Language (A × Cls f)) :=
    isRegular_map_fst (hcont L hL)
  have hset : {u : List (A × Cls f) | ∃ v, g f u = some v ∧ v ∈ L}
      = ({u : List (A × Cls f) | Consistent f u} : Language (A × Cls f))
        ⊓ ({u : List (A × Cls f) | u.map Prod.fst ∈ {w : List A | f w ∈ L}} :
            Language (A × Cls f)) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.inf_eq_inter, Set.mem_inter_iff]
    constructor
    · rintro ⟨v, hv, hvL⟩
      obtain ⟨hc, rfl⟩ := (g_eq_some_iff u v).1 hv
      exact ⟨hc, hvL⟩
    · rintro ⟨hc, hL'⟩
      exact ⟨f (u.map Prod.fst), (g_eq_some_iff u _).2 ⟨hc, rfl⟩, hL'⟩
  rw [hset]
  exact h1.inf h2

lemma boundedVariation_g :
    ∀ u₁ u₂ : List (A × Cls f), ∃ K : ℕ, ∀ (u : List (A × Cls f)) (v₁ v₂ : List B),
      g f (u ++ u₁) = some v₁ → g f (u ++ u₂) = some v₂ → leftDist v₁ v₂ ≤ K := by
  classical
  intro u₁ u₂
  set w₁ := u₁.map Prod.fst with hw₁
  set w₂ := u₂.map Prod.fst with hw₂
  refine ⟨leftDist (f w₁) (f w₂)
      + (if h : BoundedVarRel f w₁ w₂ then h.choose else 0), ?_⟩
  intro u v₁ v₂ h1 h2
  obtain ⟨hc1, rfl⟩ := (g_eq_some_iff _ v₁).1 h1
  obtain ⟨hc2, rfl⟩ := (g_eq_some_iff _ v₂).1 h2
  rcases List.eq_nil_or_concat u with rfl | ⟨x, p, rfl⟩
  · simp only [List.nil_append, ← hw₁, ← hw₂]
    exact Nat.le_add_right _ _
  · simp only [List.concat_eq_append] at hc1 hc2 ⊢
    have hs1 : p.2 = cls f w₁ := by
      have := consistent_split x p u₁ (by simpa using hc1)
      simpa [hw₁] using this
    have hs2 : p.2 = cls f w₂ := by
      have := consistent_split x p u₂ (by simpa using hc2)
      simpa [hw₂] using this
    have hrel : BoundedVarRel f w₁ w₂ := cls_eq_iff.1 (hs1.symm.trans hs2)
    have hK := hrel.choose_spec ((x ++ [p]).map Prod.fst)
    have he1 : ((x ++ [p] ++ u₁).map Prod.fst)
        = ((x ++ [p]).map Prod.fst) ++ w₁ := by simp [hw₁]
    have he2 : ((x ++ [p] ++ u₂).map Prod.fst)
        = ((x ++ [p]).map Prod.fst) ++ w₂ := by simp [hw₂]
    rw [he1, he2]
    refine le_trans hK ?_
    rw [dif_pos hrel]
    exact Nat.le_add_left _ _

lemma isSubsequential_g [Finite A] [Finite B] [Finite (Cls f)] (hcont : Continuous f) :
    IsSubsequential (g f) := by
  haveI : Finite (A × Cls f) := inferInstance
  exact (isSubsequential_iff_aux (g f)).2 ⟨partialContinuous_g hcont, boundedVariation_g⟩

/-! ### The annotation is a rational relation -/

/-- The nfa with output computing the annotation: it guesses the class of the
suffix that remains to be read. -/
noncomputable def annAut (f : List A → List B) [Finite A] [Finite (Cls f)] :
    NFAO A (A × Cls f) (Cls f) where
  init := Set.univ
  final := {cls f []}
  δ := {t | ∃ (a : A) (q : Cls f), t = (clsCons a q, [a], [(a, q)], q)}
  δ_finite := by
    refine Set.Finite.subset (Set.finite_range
      (fun p : A × Cls f => ((clsCons p.1 p.2, [p.1], [(p.1, p.2)], p.2) :
        Cls f × List A × List (A × Cls f) × Cls f))) ?_
    rintro t ⟨a, q, rfl⟩
    exact ⟨(a, q), rfl⟩

variable [Finite A] [Finite (Cls f)]

lemma annAut_mem (a : A) (q : Cls f) :
    ((clsCons a q, [a], [(a, q)], q) : Cls f × List A × List (A × Cls f) × Cls f)
      ∈ (annAut f).δ := ⟨a, q, rfl⟩

lemma annAut_relFrom (q : Cls f) (w : List A) (u : List (A × Cls f)) :
    (annAut f).relFrom q w u (cls f []) ↔ (q = cls f w ∧ u = ann f w) := by
  constructor
  · intro h
    refine NFAO.relFrom_induction (M := annAut f)
      (motive := fun q w u => q = cls f w ∧ u = ann f w) ⟨rfl, rfl⟩ ?_ h
    rintro q q' v x w' u' ⟨a, p, ht⟩ _ ih
    have hq : q = clsCons a p := by have := congrArg (fun t => t.1) ht; simpa using this
    have hv : v = [a] := by have := congrArg (fun t => t.2.1) ht; simpa using this
    have hx : x = [(a, p)] := by have := congrArg (fun t => t.2.2.1) ht; simpa using this
    have hq' : q' = p := by have := congrArg (fun t => t.2.2.2) ht; simpa using this
    subst hv; subst hx; subst hq'
    obtain ⟨hq1, hq2⟩ := ih
    constructor
    · rw [hq, hq1, clsCons_cls]
      rfl
    · rw [hq2]
      simp [hq1]
  · rintro ⟨rfl, rfl⟩
    induction w with
    | nil => exact (annAut f).relFrom_nil _
    | cons a w ih =>
      have h := NFAO.relFrom_step (M := annAut f) (annAut_mem a (cls f w)) ih
      rw [clsCons_cls] at h
      simpa using h

lemma isRationalRel_ann :
    IsRationalRel (fun (w : List A) (u : List (A × Cls f)) => u = ann f w) := by
  refine ⟨Cls f, inferInstance, annAut f, fun w u => ?_⟩
  rw [NFAO.rel_iff_relFrom]
  constructor
  · intro h
    exact ⟨cls f w, trivial, cls f [], rfl, (annAut_relFrom _ w u).2 ⟨rfl, h⟩⟩
  · rintro ⟨q, -, p, hp, hrel⟩
    have hp' : p = cls f [] := hp
    subst hp'
    exact ((annAut_relFrom q w u).1 hrel).2

end RatAnnot

/-- **The hard half of Theorem `thm:machine-independent-rational-functions`.**  A continuous
function whose relation `BoundedVarRel` has finite index is rational. -/
theorem isRationalFun_of_finiteIndex {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hcont : Continuous f)
    (hfin : {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite) :
    IsRationalFun f := by
  classical
  haveI : Finite (RatAnnot.Cls f) := hfin.to_subtype
  have h1 : IsRationalRel (fun (w : List A) (u : List (A × RatAnnot.Cls f)) => u = RatAnnot.ann f w) :=
    RatAnnot.isRationalRel_ann
  have h2 : IsRationalRel (fun (u : List (A × RatAnnot.Cls f)) (v : List B) =>
      RatAnnot.g f u = some v) :=
    isRationalRel_of_isSubsequential (RatAnnot.isSubsequential_g hcont)
  have h3 := rationalRel_comp_aux h1 h2
  obtain ⟨Q, hQ, M, hM⟩ := h3
  refine ⟨Q, hQ, M, fun w v => ?_⟩
  rw [← hM w v]
  constructor
  · rintro rfl
    exact ⟨RatAnnot.ann f w, rfl, RatAnnot.g_ann w⟩
  · rintro ⟨u, rfl, hu⟩
    rw [RatAnnot.g_ann w] at hu
    exact (Option.some_injective _ hu).symm

/-- **Theorem `thm:machine-independent-rational-functions`.**  A function is rational if and only if
it is continuous and the equivalence relation `BoundedVarRel f` has finite index. -/
theorem isRationalFun_iff_aux {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsRationalFun f ↔
      (Continuous f ∧
        {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite) := by
  constructor
  · intro hf
    refine ⟨fun L hL => ?_, finiteIndex_of_isRationalFun hf⟩
    have := rationalRel_continuous_aux hf L hL
    have hset : {w : List A | ∃ v, v = f w ∧ v ∈ L} = {w : List A | f w ∈ L} := by
      ext w; simp
    rwa [hset] at this
  · rintro ⟨hcont, hfin⟩
    exact isRationalFun_of_finiteIndex hcont hfin

end Lax132576Proofs.Transducers
