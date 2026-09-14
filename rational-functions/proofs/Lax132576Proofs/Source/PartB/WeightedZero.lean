/- The zeroness criterion for weighted automata over a field (the mathematical content of Theorems
`thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata` of *Transducers*).

A weighted automaton over a field is described by a linear representation (Lemma
`lem:closure-weighted-automata-precomposition`, `exists_linRep`): a finite set of states `Q`, an
initial set `I`, a matrix `m a` for every letter and a final vector `bta`, with

  `h v = ∑_{q ∈ I} ∑_{q'} (m v₁ ⋯ m v_k) q q' * bta q'`.

Schützenberger's argument shows that such a function is identically zero as soon
as it vanishes on all inputs of length at most the number of states: the
subspaces spanned by the row vectors `u₀ · m v` for `|v| ≤ k` form an increasing
chain, which must stabilise after at most `|Q|` steps, and the final vector
annihilates the stabilised subspace.

This is the key step of the decision procedures of Theorems `thm:equivalence-weighted-automata` and
`thm:zeroness-weighted-automata` (the decidability statements themselves, which require the
computability of the resulting algorithm, are still open in this development). -/
import Lax132576Proofs.Source.PartB.WeightedLinRep
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace WZero

variable {B Q K : Type} [Field K] [Fintype Q] [DecidableEq Q]

/-- The initial row vector of a linear representation. -/
def u0 (I : Finset Q) : Q → K := fun q => if q ∈ I then 1 else 0

/-- The matrix of a string. -/
def mstr (m : B → Matrix Q Q K) (v : List B) : Matrix Q Q K := (v.map m).prod

lemma mstr_append_single (m : B → Matrix Q Q K) (v : List B) (a : B) :
    mstr m (v ++ [a]) = mstr m v * m a := by
  simp [mstr]

/-- The linear functional given by the final vector. -/
def phi (bta : Q → K) : (Q → K) →ₗ[K] K where
  toFun u := ∑ q, u q * bta q
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum, mul_assoc]

omit [DecidableEq Q] in
lemma phi_apply (bta : Q → K) (u : Q → K) : phi bta u = ∑ q, u q * bta q := rfl

/-- The value of the linear representation on a string, written with the row
vector and the linear functional. -/
lemma linRep_eq_phi (I : Finset Q) (m : B → Matrix Q Q K) (bta : Q → K) (v : List B) :
    ∑ q ∈ I, ∑ q' : Q, (mstr m v) q q' * bta q'
      = phi bta (Matrix.vecMul (u0 I) (mstr m v)) := by
  classical
  have h1 : phi bta (Matrix.vecMul (u0 I) (mstr m v))
      = ∑ q' : Q, ∑ q : Q, u0 I q * ((mstr m v) q q' * bta q') := by
    rw [phi_apply]
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, mul_assoc]
  have h2 : ∀ q : Q, ∑ q' : Q, u0 I q * ((mstr m v) q q' * bta q')
      = if q ∈ I then ∑ q' : Q, (mstr m v) q q' * bta q' else 0 := by
    intro q
    by_cases hq : q ∈ I <;> simp [u0, hq]
  rw [h1]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun q _ => h2 q), Finset.sum_ite_mem, Finset.univ_inter]

/-- The subspace spanned by the row vectors of the strings of length at most
`k`. -/
def SS (I : Finset Q) (m : B → Matrix Q Q K) (k : ℕ) : Submodule K (Q → K) :=
  Submodule.span K {u : Q → K | ∃ v : List B, v.length ≤ k ∧ u = Matrix.vecMul (u0 I) (mstr m v)}

lemma mem_SS (I : Finset Q) (m : B → Matrix Q Q K) {k : ℕ} {v : List B} (hv : v.length ≤ k) :
    Matrix.vecMul (u0 I) (mstr m v) ∈ SS I m k :=
  Submodule.subset_span ⟨v, hv, rfl⟩

lemma SS_mono (I : Finset Q) (m : B → Matrix Q Q K) : Monotone (SS I m) := by
  intro k l hkl
  refine Submodule.span_mono ?_
  rintro u ⟨v, hv, rfl⟩
  exact ⟨v, hv.trans hkl, rfl⟩

/-- Multiplying by the matrix of one more letter takes the `k`-th subspace into
the `(k+1)`-st one. -/
lemma vecMul_mem_SS_succ (I : Finset Q) (m : B → Matrix Q Q K) (a : B) {k : ℕ} {u : Q → K}
    (hu : u ∈ SS I m k) : Matrix.vecMul u (m a) ∈ SS I m (k + 1) := by
  have hle : SS I m k ≤ Submodule.comap (Matrix.vecMulLinear (m a)) (SS I m (k + 1)) := by
    refine Submodule.span_le.2 ?_
    rintro u' ⟨v, hv, rfl⟩
    have : Matrix.vecMulLinear (m a) (Matrix.vecMul (u0 I) (mstr m v))
        = Matrix.vecMul (u0 I) (mstr m (v ++ [a])) := by
      simp [Matrix.vecMulLinear, mstr_append_single, Matrix.vecMul_vecMul]
    simp only [SetLike.mem_coe, Submodule.mem_comap, this]
    exact mem_SS I m (by simpa using Nat.succ_le_succ hv)
  have := hle hu
  simpa [Matrix.vecMulLinear] using this

/-- Once the chain of subspaces stops growing, it is constant. -/
lemma SS_stab (I : Finset Q) (m : B → Matrix Q Q K) {k : ℕ} (hk : SS I m k = SS I m (k + 1)) :
    ∀ j, k ≤ j → SS I m j = SS I m k := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    refine le_antisymm ?_ (SS_mono I m (Nat.le_succ_of_le hj))
    refine Submodule.span_le.2 ?_
    rintro u ⟨v, hv, rfl⟩
    rcases Nat.lt_or_ge v.length (j + 1) with hlt | hge
    · have : Matrix.vecMul (u0 I) (mstr m v) ∈ SS I m j :=
        mem_SS I m (Nat.lt_succ_iff.1 hlt)
      rw [ih] at this
      exact this
    · have hvlen : v.length = j + 1 := le_antisymm hv hge
      obtain ⟨v', a, rfl⟩ : ∃ (v' : List B) (a : B), v = v' ++ [a] := by
        rcases List.eq_nil_or_concat v with rfl | ⟨x, a, rfl⟩
        · simp at hvlen
        · exact ⟨x, a, by simp⟩
      have hv' : v'.length ≤ j := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hvlen
        omega
      have h1 : Matrix.vecMul (u0 I) (mstr m v') ∈ SS I m k := by
        have := mem_SS I m hv'
        rwa [ih] at this
      have h2 : Matrix.vecMul (Matrix.vecMul (u0 I) (mstr m v')) (m a) ∈ SS I m (k + 1) :=
        vecMul_mem_SS_succ I m a h1
      rw [← hk] at h2
      have : Matrix.vecMul (u0 I) (mstr m (v' ++ [a]))
          = Matrix.vecMul (Matrix.vecMul (u0 I) (mstr m v')) (m a) := by
        rw [mstr_append_single, Matrix.vecMul_vecMul]
      rw [this]
      exact h2

/-- The chain of subspaces stabilises after at most `|Q|` steps. -/
lemma exists_SS_stab (I : Finset Q) (m : B → Matrix Q Q K) :
    ∃ k ≤ Fintype.card Q, SS I m k = SS I m (k + 1) := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ k ≤ Fintype.card Q, SS I m k < SS I m (k + 1) := fun k hk =>
    lt_of_le_of_ne (SS_mono I m (Nat.le_succ k)) (hcon k hk)
  have hrank : ∀ k ≤ Fintype.card Q + 1, k ≤ Module.finrank K (SS I m k) := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k ≤ Fintype.card Q := by omega
      have h1 : Module.finrank K (SS I m k) < Module.finrank K (SS I m (k + 1)) :=
        Submodule.finrank_lt_finrank_of_lt (hlt k hk')
      have h2 : k ≤ Module.finrank K (SS I m k) := ih (by omega)
      omega
  have hbig : Fintype.card Q + 1 ≤ Module.finrank K (SS I m (Fintype.card Q + 1)) :=
    hrank _ le_rfl
  have hsmall : Module.finrank K (SS I m (Fintype.card Q + 1)) ≤ Fintype.card Q := by
    have := Submodule.finrank_le (SS I m (Fintype.card Q + 1))
    simpa [Module.finrank_fintype_fun_eq_card] using this
  omega

end WZero

/-- **The zeroness criterion.**  A function given by a linear representation
with `n` states is identically zero as soon as it vanishes on all inputs of
length at most `n`. -/
theorem linRep_zero_of_short {B Q K : Type} [Field K] [Fintype Q] [DecidableEq Q]
    (I : Finset Q) (m : B → Matrix Q Q K) (bta : Q → K) (h : List B → K)
    (hrep : ∀ v : List B, h v = ∑ q ∈ I, ∑ q' : Q, ((v.map m).prod) q q' * bta q')
    (hshort : ∀ v : List B, v.length ≤ Fintype.card Q → h v = 0) :
    ∀ v : List B, h v = 0 := by
  classical
  have hrep' : ∀ v : List B, h v = WZero.phi bta (Matrix.vecMul (WZero.u0 I) (WZero.mstr m v)) := by
    intro v
    rw [hrep v]
    exact WZero.linRep_eq_phi I m bta v
  obtain ⟨k, hkn, hk⟩ := WZero.exists_SS_stab (K := K) I m
  have hker : WZero.SS I m k ≤ LinearMap.ker (WZero.phi bta) := by
    refine Submodule.span_le.2 ?_
    rintro u ⟨v, hv, rfl⟩
    have : h v = 0 := hshort v (hv.trans hkn)
    simpa [LinearMap.mem_ker, ← hrep' v] using this
  intro v
  have hmem : Matrix.vecMul (WZero.u0 I) (WZero.mstr m v) ∈ WZero.SS I m (max v.length k) :=
    WZero.mem_SS I m (le_max_left _ _)
  rw [WZero.SS_stab I m hk _ (le_max_right _ _)] at hmem
  have := hker hmem
  rw [hrep' v]
  simpa [LinearMap.mem_ker] using this

/-- **The zeroness criterion for weighted automata over a field.**  For every
function computed by a weighted automaton there is a bound `n` such that the
function is identically zero as soon as it vanishes on all inputs of length at
most `n`.  This is the mathematical content of Theorem `thm:zeroness-weighted-automata`. -/
theorem weighted_zero_of_short {B K : Type} [Field K] {h : List B → K} (hw : IsWeighted h) :
    ∃ n : ℕ, (∀ v : List B, v.length ≤ n → h v = 0) → ∀ v : List B, h v = 0 := by
  obtain ⟨Q, hQ, hQd, I, m, bta, hrep⟩ := WNF.exists_linRep hw
  refine ⟨Fintype.card Q, fun hshort => ?_⟩
  exact linRep_zero_of_short I m bta h hrep hshort

/-- **The equivalence criterion for two linear representations.**  Two functions
given by linear representations of dimensions `d₁` and `d₂` are equal as soon as
they agree on all inputs of length at most `d₁ + d₂`.  This is the form of
Schützenberger's criterion with an *explicit* bound, used to compute the bound
from a code in `RequestProject/PartB/WeightedBound.lean`. -/
theorem linRep_eq_of_short {B K Q₁ Q₂ : Type} [Field K] [Fintype Q₁] [DecidableEq Q₁]
    [Fintype Q₂] [DecidableEq Q₂] {h₁ h₂ : List B → K}
    (I₁ : Finset Q₁) (m₁ : B → Matrix Q₁ Q₁ K) (bta₁ : Q₁ → K)
    (I₂ : Finset Q₂) (m₂ : B → Matrix Q₂ Q₂ K) (bta₂ : Q₂ → K)
    (hrep₁ : ∀ v : List B, h₁ v = ∑ q ∈ I₁, ∑ q' : Q₁, ((v.map m₁).prod) q q' * bta₁ q')
    (hrep₂ : ∀ v : List B, h₂ v = ∑ q ∈ I₂, ∑ q' : Q₂, ((v.map m₂).prod) q q' * bta₂ q') :
    (∀ v : List B, v.length ≤ Fintype.card Q₁ + Fintype.card Q₂ → h₁ v = h₂ v) → h₁ = h₂ := by
  classical
  -- the direct sum of the two linear representations computes the difference
  set m : B → Matrix (Q₁ ⊕ Q₂) (Q₁ ⊕ Q₂) K :=
    fun a => Matrix.fromBlocks (m₁ a) 0 0 (m₂ a) with hm
  set bta : Q₁ ⊕ Q₂ → K := Sum.elim bta₁ (fun q => -bta₂ q) with hbta
  have hprod : ∀ v : List B,
      (v.map m).prod = Matrix.fromBlocks ((v.map m₁).prod) 0 0 ((v.map m₂).prod) := by
    intro v
    induction v with
    | nil => simp [Matrix.fromBlocks_one]
    | cons a v ih =>
      have hma : m a = Matrix.fromBlocks (m₁ a) 0 0 (m₂ a) := by rw [hm]
      rw [List.map_cons, List.prod_cons, ih, hma, Matrix.fromBlocks_multiply]
      simp
  have hrep : ∀ v : List B, (h₁ v - h₂ v)
      = ∑ q ∈ I₁.disjSum I₂, ∑ q' : Q₁ ⊕ Q₂, ((v.map m).prod) q q' * bta q' := by
    intro v
    rw [Finset.sum_disjSum]
    have e1 : ∀ q : Q₁, ∑ q' : Q₁ ⊕ Q₂, ((v.map m).prod) (Sum.inl q) q' * bta q'
        = ∑ q' : Q₁, ((v.map m₁).prod) q q' * bta₁ q' := by
      intro q
      rw [hprod v, Fintype.sum_sum_type]
      simp [hbta]
    have e2 : ∀ q : Q₂, ∑ q' : Q₁ ⊕ Q₂, ((v.map m).prod) (Sum.inr q) q' * bta q'
        = -∑ q' : Q₂, ((v.map m₂).prod) q q' * bta₂ q' := by
      intro q
      rw [hprod v, Fintype.sum_sum_type]
      simp [hbta, Finset.sum_neg_distrib, mul_neg]
    rw [Finset.sum_congr rfl (fun q _ => e1 q), Finset.sum_congr rfl (fun q _ => e2 q),
      Finset.sum_neg_distrib, hrep₁ v, hrep₂ v]
    ring
  refine fun hshort => ?_
  have hcard : Fintype.card (Q₁ ⊕ Q₂) = Fintype.card Q₁ + Fintype.card Q₂ := Fintype.card_sum
  have hzero := linRep_zero_of_short (I₁.disjSum I₂) m bta (fun v => h₁ v - h₂ v) hrep
    (fun v hv => by
      show h₁ v - h₂ v = 0
      rw [hshort v (by rw [hcard] at hv; exact hv)]
      ring)
  funext v
  exact sub_eq_zero.mp (hzero v)

/-- **The equivalence criterion for weighted automata over a field.**  For every
two functions computed by weighted automata there is a bound `n` such that the
two functions are equal as soon as they agree on all inputs of length at most
`n`.  This is the mathematical content of Theorem `thm:equivalence-weighted-automata`. -/
theorem weighted_eq_of_short {B K : Type} [Field K] {h₁ h₂ : List B → K}
    (hw₁ : IsWeighted h₁) (hw₂ : IsWeighted h₂) :
    ∃ n : ℕ, (∀ v : List B, v.length ≤ n → h₁ v = h₂ v) → h₁ = h₂ := by
  classical
  obtain ⟨Q₁, hQ₁, hQd₁, I₁, m₁, bta₁, hrep₁⟩ := WNF.exists_linRep hw₁
  obtain ⟨Q₂, hQ₂, hQd₂, I₂, m₂, bta₂, hrep₂⟩ := WNF.exists_linRep hw₂
  exact ⟨Fintype.card Q₁ + Fintype.card Q₂,
    linRep_eq_of_short I₁ m₁ bta₁ I₂ m₂ bta₂ hrep₁ hrep₂⟩

end Lax132576Proofs.Transducers
