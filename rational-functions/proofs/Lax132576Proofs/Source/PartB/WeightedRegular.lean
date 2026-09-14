/-
Weighted automata over the semiring of languages, and the hard implication of
Theorem `thm:characterisation-rational-functions-weighted-automata`.

Over the semiring of languages (with union as addition and concatenation as
multiplication) the function `v ↦ {v}` is computed by a weighted automaton.  If
weighted automata are closed under pre-composition with a function
`f : A* → B*`, then `w ↦ {f w}` is computed by a weighted automaton `M` over the
semiring of languages.  Since the value of `M` on `w` is the union, over the
accepting runs, of the concatenation of the labels, and since this union is the
singleton `{f w}`, all the labels occurring in a run whose value is nonempty are
singletons.  Keeping only the transitions labelled by a singleton language turns
`M` into an ordinary nfa with output computing `f`, so `f` is rational.
-/
import Lax132576Proofs.Source.PartB.WeightedPrecomp
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace WLang

open LabAut NFAO WNF

variable {A B : Type}

/-! ### Sums and products of languages -/

lemma mem_finset_sum {ι : Type} (s : Finset ι) (L : ι → Language B) (x : List B) :
    x ∈ ∑ i ∈ s, L i ↔ ∃ i ∈ s, x ∈ L i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Language.mem_add]
      simp [ih]

lemma mem_wEval_iff {Q : Type} (M : LabAut A (Language B) Q) (hfin : M.FinitelyManyRuns)
    (w : List A) (x : List B) :
    x ∈ M.wEval w ↔ ∃ ts ∈ M.acceptingOn w, x ∈ weightOf ts := by
  classical
  have hcoe : M.wEval w = ∑ ts ∈ (hfin w).toFinset, weightOf ts := by
    rw [LabAut.wEval, ← finsum_mem_coe_finset weightOf (hfin w).toFinset,
      (hfin w).coe_toFinset]
  rw [hcoe, mem_finset_sum]
  constructor
  · rintro ⟨ts, hts, hx⟩
    exact ⟨ts, (hfin w).mem_toFinset.mp hts, hx⟩
  · rintro ⟨ts, hts, hx⟩
    exact ⟨ts, (hfin w).mem_toFinset.mpr hts, hx⟩

lemma singleton_mul_singleton (x y : List B) :
    ({x} : Language B) * {y} = {x ++ y} := by
  ext z
  simp only [Language.mem_mul]
  constructor
  · rintro ⟨a, rfl, b, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨x, rfl, y, rfl, rfl⟩

/-- If the concatenation of a list of languages is nonempty and contained in a
singleton, then all these languages are singletons. -/
lemma singleton_of_prod_subset : ∀ (Ls : List (Language B)) (c x : List B),
    x ∈ Ls.prod → (∀ y ∈ Ls.prod, y = c) → ∀ L ∈ Ls, ∃ u, L = {u} := by
  intro Ls
  induction Ls with
  | nil => intro c x _ _ L hL; simp at hL
  | cons L Ls ih =>
      intro c x hx hsub L' hL'
      rw [List.prod_cons, Language.mem_mul] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      -- every element of `L` equals `a`
      have hLa : L = {a} := by
        apply Set.eq_singleton_iff_unique_mem.mpr
        refine ⟨ha, fun a' ha' => ?_⟩
        have h1 : a' ++ b ∈ (L :: Ls).prod := by
          rw [List.prod_cons, Language.mem_mul]
          exact ⟨a', ha', b, hb, rfl⟩
        have h2 : a ++ b ∈ (L :: Ls).prod := by
          rw [List.prod_cons, Language.mem_mul]
          exact ⟨a, ha, b, hb, rfl⟩
        have e1 : a' ++ b = c := hsub _ h1
        have e2 : a ++ b = c := hsub _ h2
        exact List.append_cancel_right (e1.trans e2.symm)
      -- the concatenation of the remaining languages is the singleton `{b}`
      have hrest : ∀ b' ∈ Ls.prod, b' = b := by
        intro b' hb'
        have h1 : a ++ b' ∈ (L :: Ls).prod := by
          rw [List.prod_cons, Language.mem_mul]
          exact ⟨a, ha, b', hb', rfl⟩
        have h2 : a ++ b ∈ (L :: Ls).prod := by
          rw [List.prod_cons, Language.mem_mul]
          exact ⟨a, ha, b, hb, rfl⟩
        have e1 : a ++ b' = c := hsub _ h1
        have e2 : a ++ b = c := hsub _ h2
        exact List.append_cancel_left (e1.trans e2.symm)
      rcases List.mem_cons.mp hL' with rfl | hmem
      · exact ⟨a, hLa⟩
      · exact ih b b hb hrest L' hmem

/-! ### The weighted automaton computing `v ↦ {v}` -/

variable [Finite B]

/-- The weighted automaton over the semiring of languages computing `v ↦ {v}`. -/
def idAut : LabAut B (Language B) Unit where
  init := Set.univ
  final := Set.univ
  δ := Set.range (fun b : B => ((), [b], ({[b]} : Language B), ()))
  δ_finite := Set.finite_range _

/-- The unique run of `idAut` on a string. -/
def idRun (v : List B) : List (Unit × List B × Language B × Unit) :=
  v.map (fun b => ((), [b], ({[b]} : Language B), ()))

omit [Finite B] in
lemma inputOf_idRun (v : List B) : inputOf (idRun v) = v := by
  induction v with
  | nil => rfl
  | cons b y ih =>
      simp only [idRun, List.map_cons, inputOf_cons] at *
      rw [ih]
      rfl

omit [Finite B] in
lemma weightOf_idRun (v : List B) : weightOf (idRun v) = ({v} : Language B) := by
  induction v with
  | nil => rfl
  | cons b y ih =>
      simp only [idRun, List.map_cons, weightOf_cons] at *
      rw [ih, singleton_mul_singleton]
      rfl

lemma idRun_path (v : List B) : (idAut (B := B)).Path () (idRun v) () := by
  induction v with
  | nil => exact LabAut.Path.nil _
  | cons b y ih =>
      exact LabAut.Path.cons (M := idAut) (q := ()) (u := [b]) (l := ({[b]} : Language B))
        (q' := ()) ⟨b, rfl⟩ ih

lemma idAut_run_eq : ∀ (τ : List (Unit × List B × Language B × Unit)) (q p : Unit),
    (idAut (B := B)).Path q τ p → τ = idRun (inputOf τ) := by
  intro τ
  induction τ with
  | nil => intro q p _; rfl
  | cons t τ' ih =>
      intro q p hpath
      rw [path_cons_iff] at hpath
      obtain ⟨-, hmem, htail⟩ := hpath
      obtain ⟨b, hb⟩ := hmem
      have ht : t = ((), [b], ({[b]} : Language B), ()) := hb.symm
      have htail' := ih () p htail
      rw [ht, inputOf_cons]
      simp only [idRun, List.singleton_append, List.map_cons]
      exact congrArg _ htail'

lemma acceptingOn_idAut (v : List B) : (idAut (B := B)).acceptingOn v = {idRun v} := by
  apply Set.Subset.antisymm
  · rintro τ ⟨⟨q, -, p, -, hpath⟩, hin⟩
    have := idAut_run_eq τ q p hpath
    rw [hin] at this
    exact this
  · rintro τ rfl
    exact ⟨⟨(), trivial, (), trivial, idRun_path v⟩, inputOf_idRun v⟩

lemma wEval_idAut (v : List B) : (idAut (B := B)).wEval v = ({v} : Language B) := by
  rw [LabAut.wEval, acceptingOn_idAut, finsum_mem_singleton, weightOf_idRun]

lemma finitelyManyRuns_idAut : (idAut (B := B)).FinitelyManyRuns := by
  intro v
  rw [acceptingOn_idAut]
  exact Set.finite_singleton _

/-- The function `v ↦ {v}` is computed by a weighted automaton over the semiring
of languages. -/
theorem isWeighted_singleton : IsWeighted (fun v : List B => ({v} : Language B)) := by
  refine ⟨Unit, inferInstance, idAut, finitelyManyRuns_idAut, ?_⟩
  funext v
  exact wEval_idAut v

/-! ### Extracting an nfa with output -/

variable {Q : Type}

/-- The transition of a weighted automaton over languages associated with a
transition of an nfa with output. -/
def toLang (t : Q × List A × List B × Q) : Q × List A × Language B × Q :=
  (t.1, t.2.1, ({t.2.2.1} : Language B), t.2.2.2)

omit [Finite B] in
lemma lang_singleton_inj {x y : List B} (h : ({x} : Language B) = {y}) : x = y := by
  have : x ∈ ({y} : Language B) := h ▸ rfl
  exact this

omit [Finite B] in
lemma toLang_injective : Function.Injective (toLang (A := A) (B := B) (Q := Q)) := by
  intro a b hab
  simp only [toLang, Prod.mk.injEq] at hab
  exact Prod.ext hab.1 (Prod.ext hab.2.1 (Prod.ext (lang_singleton_inj hab.2.2.1) hab.2.2.2))

/-- The nfa with output consisting of the transitions of `M` whose label is a
singleton language. -/
def sing (M : LabAut A (Language B) Q) : NFAO A B Q where
  init := M.init
  final := M.final
  δ := toLang ⁻¹' M.δ
  δ_finite := Set.Finite.preimage (fun _ _ _ _ hab => toLang_injective hab) M.δ_finite

omit [Finite B] in
lemma sing_path {M : LabAut A (Language B) Q} {q p : Q}
    {ts : List (Q × List A × List B × Q)} (h : (sing M).Path q ts p) :
    M.Path q (ts.map toLang) p := by
  induction h with
  | nil q => exact LabAut.Path.nil _
  | @cons q u x q' ts p ht _ ih =>
      exact LabAut.Path.cons (M := M) (q := q) (u := u) (l := ({x} : Language B))
        (q' := q') ht ih

omit [Finite B] in
lemma inputOf_map_toLang (ts : List (Q × List A × List B × Q)) :
    inputOf (ts.map (toLang (A := A) (B := B) (Q := Q))) = inputOf ts := by
  simp [inputOf, List.map_map, Function.comp_def, toLang]

omit [Finite B] in
lemma weightOf_map_toLang (ts : List (Q × List A × List B × Q)) :
    weightOf (ts.map (toLang (A := A) (B := B) (Q := Q))) = ({outputOf ts} : Language B) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.map_cons, weightOf_cons, outputOf_cons, toLang] at *
      rw [ih, singleton_mul_singleton]

omit [Finite B] in
lemma path_of_singletons {M : LabAut A (Language B) Q} {q p : Q}
    {τ : List (Q × List A × Language B × Q)} (h : M.Path q τ p)
    (hs : ∀ t ∈ τ, ∃ x, t.2.2.1 = ({x} : Language B)) :
    ∃ ts : List (Q × List A × List B × Q),
      (sing M).Path q ts p ∧ ts.map toLang = τ := by
  induction h with
  | nil q => exact ⟨[], LabAut.Path.nil _, rfl⟩
  | @cons q u L q' τ p ht hpath ih =>
      obtain ⟨x, hx⟩ := hs (q, u, L, q') (by simp)
      obtain ⟨ts, hts, hmap⟩ := ih (fun t htmem => hs t (by simp [htmem]))
      refine ⟨(q, u, x, q') :: ts, ?_, by simp [toLang, hmap, ← hx]⟩
      refine LabAut.Path.cons (M := sing M) (q := q) (u := u) (l := x) (q' := q') ?_ hts
      show ((q, u, ({x} : Language B), q')) ∈ M.δ
      rw [← hx]
      exact ht

/-- If `w ↦ {f w}` is computed by a weighted automaton over the semiring of
languages, then `f` is a rational function. -/
theorem rationalFun_of_isWeighted_singleton {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hw : IsWeighted (fun w => ({f w} : Language B))) :
    IsRationalFun f := by
  obtain ⟨Q, hQ, M, hfin, hval⟩ := hw
  have hval' : ∀ w, M.wEval w = ({f w} : Language B) := fun w => congrFun hval w
  refine ⟨Q, hQ, sing M, fun w v => ?_⟩
  constructor
  · rintro rfl
    have hmem : f w ∈ M.wEval w := by rw [hval']; rfl
    obtain ⟨τ, hτ, hx⟩ := (mem_wEval_iff M hfin w (f w)).mp hmem
    have hsub : ∀ y ∈ weightOf τ, y = f w := by
      intro y hy
      have hy' : y ∈ M.wEval w := (mem_wEval_iff M hfin w y).mpr ⟨τ, hτ, hy⟩
      rw [hval'] at hy'
      exact hy'
    have hsing : ∀ t ∈ τ, ∃ x, t.2.2.1 = ({x} : Language B) := by
      intro t ht
      have hL : t.2.2.1 ∈ labelsOf τ := List.mem_map.mpr ⟨t, ht, rfl⟩
      exact singleton_of_prod_subset (labelsOf τ) (f w) (f w) hx hsub t.2.2.1 hL
    obtain ⟨⟨q, hq, p, hp, hpath⟩, hin⟩ := hτ
    obtain ⟨ts, hts, hmap⟩ := path_of_singletons hpath hsing
    refine ⟨ts, ⟨q, hq, p, hp, hts⟩, ?_, ?_⟩
    · rw [← inputOf_map_toLang ts, hmap]; exact hin
    · -- the output of the run is `f w`
      have hw : weightOf τ = ({outputOf ts} : Language B) := by
        rw [← hmap, weightOf_map_toLang]
      rw [hw] at hx
      exact hx.symm
  · rintro ⟨ts, ⟨q, hq, p, hp, hpath⟩, hin, rfl⟩
    have hmem : outputOf ts ∈ M.wEval w := by
      refine (mem_wEval_iff M hfin w (outputOf ts)).mpr ⟨ts.map toLang, ?_, ?_⟩
      · exact ⟨⟨q, hq, p, hp, sing_path hpath⟩, by rw [inputOf_map_toLang]; exact hin⟩
      · rw [weightOf_map_toLang]; rfl
    rw [hval'] at hmem
    exact hmem

end WLang

/-- **Theorem `thm:characterisation-rational-functions-weighted-automata`.**  A string-to-string
function is rational if and only if weighted automata are closed under pre-composition with it. -/
theorem rational_iff_weighted_precomp_aux {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔
      ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f) := by
  constructor
  · intro hf S inst h hh
    exact weighted_precomp_rational_aux hf hh
  · intro hyp
    have := hyp (Language B) inferInstance (fun v => ({v} : Language B))
      WLang.isWeighted_singleton
    exact WLang.rationalFun_of_isWeighted_singleton this

end Lax132576Proofs.Transducers
