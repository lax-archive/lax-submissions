/-
The linear representation of a weighted automaton.

For a weighted automaton in the normal form of
`RequestProject/PartB/WeightedNF.lean` (at most one state both initial and final,
every transition reading at most one letter, every state on an accepting run)
the value on an input string is given by a *linear representation*: a matrix
`mu b` for every letter `b` and a vector `beta`, such that the value on
`b₁ ⋯ bₙ` is the sum, over the initial states, of the entries of
`mu b₁ ⋯ mu bₙ *ᵥ beta`.  The matrix of a letter collects the weights of the
*right-closed* paths reading it (all their transitions but the last read
nothing), and the vector `beta` the weights of the accepting paths reading
nothing.
-/
import Lax132576Proofs.Source.PartB.WeightedNF
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace WNF

open LabAut

variable {B S : Type}

/-! ## The linear representation of a normalised weighted automaton -/

section LinRep

variable {Q : Type} [Semiring S]

/-- A path is *right-closed* if all its transitions but the last read nothing. -/
def RC (σ : List (Q × List B × S × Q)) : Prop := ∀ t ∈ σ.dropLast, t.2.1 = []

variable (M : LabAut B S Q)

/-- The right-closed paths from `q` to `q'` reading the single letter `b`. -/
def rcSet (q : Q) (b : B) (q' : Q) : Set (List (Q × List B × S × Q)) :=
  {σ | M.Path q σ q' ∧ inputOf σ = [b] ∧ RC σ}

variable [Fintype Q] [DecidableEq Q]

/-- The matrix of the letter `b` in the linear representation of `M`. -/
noncomputable def mu (b : B) : Matrix Q Q S :=
  Matrix.of fun q q' => ∑ᶠ σ ∈ rcSet M q b q', weightOf σ

/-- The final vector of the linear representation of `M`. -/
noncomputable def beta (q : Q) : S := accWeight M q []

/-- The matrix of a string in the linear representation of `M`. -/
noncomputable def muStr (v : List B) : Matrix Q Q S := (v.map (mu M)).prod

@[simp] lemma muStr_nil : muStr M ([] : List B) = 1 := rfl

lemma muStr_cons (b : B) (v : List B) : muStr M (b :: v) = mu M b * muStr M v := by
  simp [muStr]

lemma muStr_append (v w : List B) : muStr M (v ++ w) = muStr M v * muStr M w := by
  simp [muStr, List.prod_append]

/-! ### Finiteness of the sets of paths -/

omit [Fintype Q] [DecidableEq Q] [Semiring S] in
lemma paths_finite (hall : AllUseful M) (hfin : M.FinitelyManyRuns) : PathsFinite M := by
  intro q p x
  obtain ⟨q₀, hq₀, -, -, ts₁, -, hts₁, -⟩ := hall q
  obtain ⟨-, -, p', hp', -, ts₂, -, hts₂⟩ := hall p
  refine Set.Finite.of_finite_image (f := fun σ => ts₁ ++ σ ++ ts₂) ?_ ?_
  · refine (hfin (inputOf ts₁ ++ x ++ inputOf ts₂)).subset ?_
    rintro _ ⟨σ, ⟨hpath, hin⟩, rfl⟩
    refine ⟨⟨q₀, hq₀, p', hp', (hts₁.append hpath).append hts₂⟩, ?_⟩
    rw [inputOf_append, inputOf_append, hin]
  · intro a _ b _ hab
    have := List.append_cancel_right hab
    exact List.append_cancel_left this

omit [Semiring S] [Fintype Q] [DecidableEq Q] in
lemma rcSet_finite (hp : PathsFinite M) (q : Q) (b : B) (q' : Q) :
    (rcSet M q b q').Finite :=
  (hp q q' [b]).subset (fun _ hσ => ⟨hσ.1, hσ.2.1⟩)

omit [Semiring S] [DecidableEq Q] in
lemma accFrom_finite (hp : PathsFinite M) (q : Q) (v : List B) :
    (accFrom M q v).Finite := by
  refine (Set.Finite.biUnion (Set.finite_univ (α := Q))
    (fun p _ => hp q p v)).subset ?_
  rintro σ ⟨⟨p, hp, hpath⟩, hin⟩
  exact Set.mem_biUnion (Set.mem_univ p) ⟨hpath, hin⟩

/-! ### The decomposition of a run at the first letter -/

omit [Semiring S] [Fintype Q] [DecidableEq Q] in
lemma rc_decomp (hat : Atomic M) :
    ∀ {σ : List (Q × List B × S × Q)} {q p : Q} {b : B} {y : List B},
      M.Path q σ p → inputOf σ = b :: y →
      ∃ (q' : Q) (σ₁ σ₂ : List (Q × List B × S × Q)),
        σ = σ₁ ++ σ₂ ∧ σ₁ ∈ rcSet M q b q' ∧ M.Path q' σ₂ p ∧ inputOf σ₂ = y := by
  intro σ
  induction σ with
  | nil => intro q p b y _ hin; simp [inputOf] at hin
  | cons t σ ih =>
      intro q p b y hpath hin
      rw [path_cons_iff] at hpath
      obtain ⟨hsrc, hmem, htail⟩ := hpath
      rw [inputOf_cons] at hin
      have hlen := hat t hmem
      rcases ht : t.2.1 with _ | ⟨c, rest⟩
      · -- the transition reads nothing: recurse
        rw [ht] at hin
        simp only [List.nil_append] at hin
        obtain ⟨q', σ₁, σ₂, hsplit, hrc, hpath₂, hin₂⟩ := ih htail hin
        refine ⟨q', t :: σ₁, σ₂, by rw [hsplit]; rfl, ⟨?_, ?_, ?_⟩, hpath₂, hin₂⟩
        · rw [path_cons_iff]
          exact ⟨hsrc, hmem, hrc.1⟩
        · rw [inputOf_cons, ht, hrc.2.1]
          rfl
        · intro t' ht'
          rcases σ₁ with _ | ⟨t₁, σ₁'⟩
          · simp at ht'
          · rw [List.dropLast_cons_of_ne_nil (by simp)] at ht'
            rcases List.mem_cons.mp ht' with rfl | hmem'
            · exact ht
            · exact hrc.2.2 t' hmem'
      · -- the transition reads one letter, necessarily `b`
        rw [ht] at hin
        have hrest : rest = [] := by
          rw [ht] at hlen
          simpa using List.length_eq_zero_iff.mp (by simpa using hlen)
        subst hrest
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hin
        obtain ⟨rfl, hin'⟩ := hin
        refine ⟨t.2.2.2, [t], σ, rfl, ⟨?_, ?_, ?_⟩, htail, hin'⟩
        · rw [path_cons_iff]
          exact ⟨hsrc, hmem, LabAut.Path.nil _⟩
        · rw [inputOf_cons, ht]; rfl
        · intro t' ht'; simp at ht'

omit [Fintype Q] [DecidableEq Q] [Semiring S] in
lemma rc_unique {b : B} {σ₁ σ₂ σ₁' σ₂' : List (Q × List B × S × Q)}
    (h1 : inputOf σ₁ = [b]) (hrc : RC σ₁) (h1' : inputOf σ₁' = [b]) (hrc' : RC σ₁')
    (h : σ₁ ++ σ₂ = σ₁' ++ σ₂') : σ₁ = σ₁' := by
  -- an auxiliary claim: a strictly longer right-closed decomposition is impossible
  have key : ∀ (a c : List (Q × List B × S × Q)), inputOf a = [b] → inputOf c = [b] → RC c →
      a <+: c → a = c := by
    intro a c ha hc hrcc ⟨ρ, hρ⟩
    rcases hρnil : ρ with _ | ⟨r, ρ'⟩
    · rw [hρnil] at hρ; simpa using hρ
    · exfalso
      have hin : inputOf a ++ inputOf ρ = [b] := by
        rw [← inputOf_append, hρ]; exact hc
      have hρin : inputOf ρ = [] := by
        rw [ha] at hin
        simpa using hin
      have hsub : ∀ t ∈ a, t ∈ c.dropLast := by
        intro t hta
        rw [← hρ, hρnil]
        rw [List.dropLast_append_of_ne_nil (by simp)]
        exact List.mem_append_left _ hta
      have : inputOf a = [] := by
        have : ∀ t ∈ a, t.2.1 = [] := fun t ht => hrcc t (hsub t ht)
        simp only [inputOf, List.flatten_eq_nil_iff, List.mem_map]
        rintro l ⟨t, ht, rfl⟩
        exact this t ht
      rw [ha] at this
      simp at this
  rcases le_total σ₁.length σ₁'.length with hle | hle
  · exact key σ₁ σ₁' h1 h1' hrc'
      (List.prefix_of_prefix_length_le ⟨σ₂, rfl⟩ ⟨σ₂', h.symm⟩ hle)
  · exact (key σ₁' σ₁ h1' h1 hrc
      (List.prefix_of_prefix_length_le ⟨σ₂', h.symm⟩ ⟨σ₂, rfl⟩ hle)).symm

/-! ### The sum over the runs decomposes -/

lemma finsum_append_mul {X : Type} {s t : Set (List X)} (hs : s.Finite) (ht : t.Finite)
    (w : List X → S) (hw : ∀ a b : List X, w (a ++ b) = w a * w b)
    (hinj : Set.InjOn (fun p : List X × List X => p.1 ++ p.2) (s ×ˢ t)) :
    ∑ᶠ σ ∈ (fun p : List X × List X => p.1 ++ p.2) '' (s ×ˢ t), w σ
      = (∑ᶠ a ∈ s, w a) * (∑ᶠ b ∈ t, w b) := by
  classical
  rw [finsum_mem_image hinj]
  have hcongr : ∀ p ∈ s ×ˢ t, w (p.1 ++ p.2) = w p.1 * w p.2 := by
    intro p _
    exact hw p.1 p.2
  rw [finsum_mem_congr rfl hcongr]
  rw [← hs.coe_toFinset, ← ht.coe_toFinset, ← Finset.coe_product, finsum_mem_coe_finset,
    finsum_mem_coe_finset, finsum_mem_coe_finset, Finset.sum_product, Finset.sum_mul_sum]

omit [Semiring S] [Fintype Q] [DecidableEq Q] in
lemma accFrom_cons_eq (hat : Atomic M) (q : Q) (b : B) (y : List B) :
    accFrom M q (b :: y) =
      ⋃ q' ∈ (Set.univ : Set Q),
        (fun p : List (Q × List B × S × Q) × List (Q × List B × S × Q) => p.1 ++ p.2) ''
          (rcSet M q b q' ×ˢ accFrom M q' y) := by
  apply Set.Subset.antisymm
  · rintro σ ⟨⟨p, hp, hpath⟩, hin⟩
    obtain ⟨q', σ₁, σ₂, rfl, hrc, hpath₂, hin₂⟩ := rc_decomp M hat hpath hin
    exact Set.mem_biUnion (Set.mem_univ q') ⟨(σ₁, σ₂), ⟨hrc, ⟨p, hp, hpath₂⟩, hin₂⟩, rfl⟩
  · rintro σ hσ
    simp only [Set.mem_iUnion, Set.mem_univ, exists_prop, true_and] at hσ
    obtain ⟨q', ⟨σ₁, σ₂⟩, ⟨⟨hpath₁, hin₁, -⟩, ⟨p, hp, hpath₂⟩, hin₂⟩, rfl⟩ := hσ
    exact ⟨⟨p, hp, hpath₁.append hpath₂⟩, by rw [inputOf_append, hin₁, hin₂]; rfl⟩

omit [DecidableEq Q] in
lemma accWeight_cons (hp : PathsFinite M) (hat : Atomic M)
    (q : Q) (b : B) (y : List B) :
    accWeight M q (b :: y) = ∑ q' : Q, mu M b q q' * accWeight M q' y := by
  classical
  have hinj : ∀ q' : Q, Set.InjOn
      (fun p : List (Q × List B × S × Q) × List (Q × List B × S × Q) => p.1 ++ p.2)
      (rcSet M q b q' ×ˢ accFrom M q' y) := by
    rintro q' ⟨σ₁, σ₂⟩ ⟨⟨-, hin₁, hrc₁⟩, -⟩ ⟨σ₁', σ₂'⟩ ⟨⟨-, hin₁', hrc₁'⟩, -⟩ heq
    have h1 : σ₁ = σ₁' := rc_unique hin₁ hrc₁ hin₁' hrc₁' heq
    subst h1
    exact Prod.ext rfl (List.append_cancel_left heq)
  have hdisj : (Set.univ : Set Q).PairwiseDisjoint (fun q' =>
      (fun p : List (Q × List B × S × Q) × List (Q × List B × S × Q) => p.1 ++ p.2) ''
        (rcSet M q b q' ×ˢ accFrom M q' y)) := by
    rintro q₁ - q₂ - hne
    refine Set.disjoint_left.mpr ?_
    rintro σ ⟨⟨σ₁, σ₂⟩, ⟨⟨hpath₁, hin₁, hrc₁⟩, -⟩, rfl⟩ ⟨⟨σ₁', σ₂'⟩, ⟨⟨hpath₁', hin₁', hrc₁'⟩, -⟩, heq⟩
    apply hne
    have h1 : σ₁' = σ₁ := rc_unique hin₁' hrc₁' hin₁ hrc₁ heq
    subst h1
    have hne1 : σ₁' ≠ [] := by
      intro h; rw [h] at hin₁'; simp [inputOf] at hin₁'
    exact (path_target_eq hpath₁' hpath₁ hne1).symm
  rw [accWeight, accFrom_cons_eq M hat q b y,
    finsum_mem_biUnion hdisj Set.finite_univ
      (fun q' _ => ((rcSet_finite M hp q b q').prod
        (accFrom_finite M hp q' y)).image _)]
  have hterm : ∀ q' : Q, (∑ᶠ σ ∈ (fun p : List (Q × List B × S × Q) × List (Q × List B × S × Q) =>
      p.1 ++ p.2) '' (rcSet M q b q' ×ˢ accFrom M q' y), weightOf σ)
      = mu M b q q' * accWeight M q' y := by
    intro q'
    rw [finsum_append_mul (rcSet_finite M hp q b q') (accFrom_finite M hp q' y)
      weightOf weightOf_append (hinj q')]
    rfl
  rw [finsum_mem_congr rfl (fun q' _ => hterm q'), finsum_mem_univ, finsum_eq_sum_of_fintype]

lemma accWeight_eq_muStr (hp : PathsFinite M) (hat : Atomic M) :
    ∀ (v : List B) (q : Q), accWeight M q v = ∑ q' : Q, muStr M v q q' * beta M q' := by
  intro v
  induction v with
  | nil =>
      intro q
      simp only [muStr_nil, Matrix.one_apply]
      rw [Finset.sum_eq_single q (fun q' _ hne => by simp [Ne.symm hne]) (by simp)]
      simp [beta]
  | cons b y ih =>
      intro q
      rw [accWeight_cons M hp hat q b y]
      have : ∀ q' : Q, mu M b q q' * accWeight M q' y
          = ∑ q'' : Q, mu M b q q' * (muStr M y q' q'' * beta M q'') := by
        intro q'
        rw [ih q', Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun q' _ => this q'), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q'' _ => ?_)
      rw [muStr_cons, Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun q' _ => by rw [mul_assoc])

/-- The value of a normalised weighted automaton is given by its linear
representation. -/
theorem wEval_eq_linRep (hu : UniqueEmptyRun M) (hp : PathsFinite M) (hfin : M.FinitelyManyRuns)
    (hat : Atomic M) (v : List B) :
    M.wEval v = ∑ᶠ q ∈ M.init, ∑ q' : Q, muStr M v q q' * beta M q' := by
  rw [wEval_eq_finsum_accWeight hu hfin v]
  exact finsum_mem_congr rfl (fun q _ => accWeight_eq_muStr M hp hat v q)

end LinRep

/-! ## The linear representation of an arbitrary weighted automaton -/

/-- Every function computed by a weighted automaton has a *linear
representation*: a finite set of states, a set `I` of initial states, a matrix
for every letter and a final vector, such that the value on a string is obtained
by multiplying the matrices of its letters. -/
theorem exists_linRep {B S : Type} [Semiring S] {h : List B → S} (hw : IsWeighted h) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (I : Finset Q) (m : B → Matrix Q Q S)
      (bta : Q → S),
      ∀ v : List B, h v = ∑ q ∈ I, ∑ q' : Q, ((v.map m).prod) q q' * bta q' := by
  classical
  obtain ⟨Q₀, hQ₀, M₀, hfin₀, hval⟩ := hw
  -- make the empty run unique
  set M₁ := initCopy M₀ with hM₁
  have hfin₁ : M₁.FinitelyManyRuns := finitelyManyRuns_initCopy M₀ hfin₀
  have hue₁ : UniqueEmptyRun M₁ := uniqueEmptyRun_initCopy M₀
  have hinit₁ : M₁.init.Finite := Set.toFinite _
  -- atomise
  set M₂ := atom M₁ with hM₂
  have hfin₂ : M₂.FinitelyManyRuns := finitelyManyRuns_atom M₁ hfin₁
  have hue₂ : UniqueEmptyRun M₂ := uniqueEmptyRun_atom M₁ hue₁
  have hat₂ : Atomic M₂ := atomic_atom M₁
  have hinit₂ : M₂.init.Finite := init_atom_finite M₁ hinit₁
  -- restrict to the useful states
  set M₃ := restrict M₂ with hM₃
  have hfin₃ : M₃.FinitelyManyRuns := finitelyManyRuns_restrict M₂ hfin₂
  have hue₃ : UniqueEmptyRun M₃ := uniqueEmptyRun_restrict M₂ hue₂
  have hat₃ : Atomic M₃ := atomic_restrict M₂ hat₂
  have hall₃ : AllUseful M₃ := allUseful_restrict M₂
  have hinit₃ : M₃.init.Finite := init_restrict_finite M₂ hinit₂
  have hQ₃ : Finite {q // Useful M₂ q} := instFiniteUseful M₂ hinit₂
  letI : Fintype {q // Useful M₂ q} := Fintype.ofFinite _
  have hvals : ∀ v, M₃.wEval v = h v := by
    intro v
    rw [wEval_restrict M₂ v, wEval_atom M₁ v, wEval_initCopy M₀ v, hval]
  refine ⟨{q // Useful M₂ q}, inferInstance, inferInstance, hinit₃.toFinset, mu M₃, beta M₃,
    fun v => ?_⟩
  have hcoe : ∑ᶠ q ∈ M₃.init, (∑ q' : {q // Useful M₂ q}, muStr M₃ v q q' * beta M₃ q')
      = ∑ q ∈ hinit₃.toFinset, ∑ q' : {q // Useful M₂ q}, muStr M₃ v q q' * beta M₃ q' := by
    rw [← finsum_mem_coe_finset (fun q => ∑ q' : {q // Useful M₂ q}, muStr M₃ v q q' * beta M₃ q')
      hinit₃.toFinset, hinit₃.coe_toFinset]
  rw [← hvals v, wEval_eq_linRep M₃ hue₃ (paths_finite M₃ hall₃ hfin₃) hfin₃ hat₃ v, hcoe]
  rfl

end WNF

end Lax132576Proofs.Transducers
