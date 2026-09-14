/-
The proof of Theorem `thm:decidable-equivalence-regular` of the book (*Transducers*, M. Bojańczyk):
equivalence of regular functions, by a reduction to equivalence -- equivalently,
to zeroness -- of weighted automata over the field of rationals.

The book's proof goes through the *prime decomposition* of a regular function:
the class of functions that can be post-composed with weighted automata,
i.e.

  `{ f : A* → B* | for every weighted automaton g : B* → S, the function f · g
     is a weighted automaton }`,

is closed under composition, contains the rational functions (Lemma
`lem:closure-weighted-automata-precomposition`, `Transducers.weighted_precomp_rational`) and
contains the two remaining prime functions, map reverse and map duplicate.  The two prime cases are
the constructions of `RequestProject/PartC/WeightedMapLift.lean`.  Since a regular function is by
definition a composition of primes, the class contains all regular functions: this is
`Transducers.isWeighted_comp_regular` below.

Post-composing with an *injective* weighted automaton `ι : B* → ℚ` then represents a regular
function faithfully by a weighted automaton over `ℚ`, so equivalence of regular functions reduces to
equivalence of weighted automata over `ℚ`, which is decided by Schützenberger's criterion
(`Transducers.weighted_eq_of_short`, the mathematical content of Theorem
`thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata`).  The conclusion,
`Transducers.regularFun_eq_of_short`, is the decision procedure of Theorem
`thm:decidable-equivalence-regular` in semantic form: two regular functions over a finite input
alphabet are equal as soon as they agree on the (finitely many) inputs of length at most a bound
supplied by that criterion. -/
import Lax916827Proofs.Source.PartC.WeightedMapLift
import Lax916827Proofs.Source.PartC.RegularDef
import Lax132576Proofs.Source.PartB.Iota
import Lax132576Proofs.Source.PartB.WeightedZero
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

open WPre WLin WMap

/-! ## The two prime functions -/

/-- Weighted automata over a commutative semiring are closed under
pre-composition with map reverse. -/
theorem isWeighted_comp_mapReverse {A₀ S : Type} [Finite A₀] [CommSemiring S]
    {h : List (Option A₀) → S} (hh : IsWeighted h) : IsWeighted (h ∘ mapReverse A₀) :=
  isWeighted_comp_mapLift (matLin_reverse (A₀ := A₀) (S := S)) hh

/-- Weighted automata over a commutative semiring are closed under
pre-composition with map duplicate. -/
theorem isWeighted_comp_mapDuplicate {A₀ S : Type} [Finite A₀] [CommSemiring S]
    {h : List (Option A₀) → S} (hh : IsWeighted h) : IsWeighted (h ∘ mapDuplicate A₀) :=
  isWeighted_comp_mapLift (matLin_dup (A₀ := A₀) (S := S)) hh

/-! ## Regular functions -/

/-- Auxiliary form of `Transducers.isWeighted_comp_regular`, carrying the
finiteness of the two alphabets as explicit hypotheses so that the induction on
the composition tree has access to the finiteness of the intermediate
alphabets. -/
theorem isWeighted_comp_regular_aux {A B : Type} {f : List A → List B} (hf : IsRegularFun f) :
    Finite A → Finite B →
      ∀ {S : Type} [CommSemiring S] (h : List B → S), IsWeighted h → IsWeighted (h ∘ f) := by
  induction hf with
  | @base A B f hbase =>
      intro hA hB S _ h hh
      haveI := hA; haveI := hB
      rcases hbase with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact weighted_precomp_rational hrat hh
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ :=
          Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h₁ : IsWeighted (h ∘ (fun x : List (Option A₀) => x.map e'.symm)) :=
          weighted_precomp_rational (isRationalFun_map (e'.symm : Option A₀ → B)) hh
        have h₂ := isWeighted_comp_mapReverse (A₀ := A₀) h₁
        have h₃ := weighted_precomp_rational (isRationalFun_map (e : A → Option A₀)) h₂
        have hcomp : h ∘ f
            = ((h ∘ fun x : List (Option A₀) => x.map e'.symm) ∘ mapReverse A₀)
              ∘ (fun w : List A => w.map e) := by
          funext w
          simp only [Function.comp_apply, hfe w]
        rw [hcomp]
        exact h₃
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ :=
          Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h₁ : IsWeighted (h ∘ (fun x : List (Option A₀) => x.map e'.symm)) :=
          weighted_precomp_rational (isRationalFun_map (e'.symm : Option A₀ → B)) hh
        have h₂ := isWeighted_comp_mapDuplicate (A₀ := A₀) h₁
        have h₃ := weighted_precomp_rational (isRationalFun_map (e : A → Option A₀)) h₂
        have hcomp : h ∘ f
            = ((h ∘ fun x : List (Option A₀) => x.map e'.symm) ∘ mapDuplicate A₀)
              ∘ (fun w : List A => w.map e) := by
          funext w
          simp only [Function.comp_apply, hfe w]
        rw [hcomp]
        exact h₃
  | id A => intro _ _ S _ h hh; exact hh
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC S _ h hh
      haveI := hA; haveI := hB; haveI := hC
      exact ihf hA hB (h ∘ g) (ihg hB hC h hh)

/-- **Weighted automata are closed under pre-composition with regular functions.**  This is the
heart of the book's proof of Theorem `thm:decidable-equivalence-regular`: the class of functions
that can be post-composed with weighted automata is closed under composition, and contains the three
kinds of prime regular functions. -/
theorem isWeighted_comp_regular {A B S : Type} [Finite A] [Finite B] [CommSemiring S]
    {f : List A → List B} (hf : IsRegularFun f) {h : List B → S} (hh : IsWeighted h) :
    IsWeighted (h ∘ f) :=
  isWeighted_comp_regular_aux hf ‹_› ‹_› h hh

/-! ## An injective weighted automaton over the rationals -/

namespace IotaW

variable {B : Type}

/-- The matrix of a letter in the linear representation of the numerical
encoding of strings. -/
noncomputable def iotaMat (K : ℕ) (phi : B → ℕ) (b : B) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(K : ℚ), ((phi b : ℚ) + 1); 0, 1]

lemma mStr_iotaMat (K : ℕ) (phi : B → ℕ) (v : List B) :
    mStr (iotaMat K phi) v
      = !![((K : ℚ) ^ v.length), ((Iota.iota K (v.map phi) : ℕ) : ℚ); 0, 1] := by
  induction v with
  | nil => simp [mStr, Matrix.one_fin_two]
  | cons b v ih =>
      rw [WMap.mStr_cons, ih, iotaMat]
      rw [Matrix.mul_fin_two]
      have h1 : (Iota.iota K ((b :: v).map phi) : ℕ)
          = (phi b + 1) + K * Iota.iota K (v.map phi) := by
        simp [Iota.iota_cons]
      rw [h1]
      push_cast
      congr 1
      ring_nf
      simp [pow_succ]
      ring

/-- The numerical encoding of strings is computed by a weighted automaton over
the rationals. -/
theorem isWeighted_iota [Finite B] (K : ℕ) (phi : B → ℕ) :
    IsWeighted (fun v : List B => ((Iota.iota K (v.map phi) : ℕ) : ℚ)) := by
  classical
  have h := WLin.isWeighted_of_linRep (iotaMat K phi) ({0} : Finset (Fin 2))
    (fun q : Fin 2 => if q = 1 then (1 : ℚ) else 0)
  have heq : (fun v : List B => val (iotaMat K phi) ({0} : Finset (Fin 2))
      (fun q : Fin 2 => if q = 1 then (1 : ℚ) else 0) v)
      = fun v : List B => ((Iota.iota K (v.map phi) : ℕ) : ℚ) := by
    funext v
    rw [val, Finset.sum_singleton, tailVal, mStr_iotaMat]
    simp
  rwa [heq] at h

end IotaW

/-- **An injective weighted automaton.**  Over a finite alphabet there is an
injective function `B* → ℚ` that is computed by a weighted automaton; strings
are encoded by their digits in a large enough base, as in the book's
observation (a) in the proof of Theorem `thm:equivalence-rational-functions`. -/
theorem exists_injective_weighted (B : Type) [Finite B] :
    ∃ iota : List B → ℚ, IsWeighted iota ∧ Function.Injective iota := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  obtain ⟨n, ⟨e⟩⟩ : ∃ n, Nonempty (B ≃ Fin n) := ⟨Fintype.card B, ⟨Fintype.equivFin B⟩⟩
  set phi : B → ℕ := fun b => ((e b : Fin n) : ℕ) with hphi
  have hphi_inj : Function.Injective phi := by
    intro b b' hbb'
    have : (e b : Fin n) = e b' := Fin.ext hbb'
    exact e.injective this
  set K : ℕ := n + 1 with hK
  have hlt : ∀ b : B, phi b + 1 < K := by
    intro b
    have h1 : phi b = ((e b : Fin n) : ℕ) := rfl
    have h2 : ((e b : Fin n) : ℕ) < n := (e b).isLt
    rw [h1, hK]
    omega
  refine ⟨fun v => ((Iota.iota K (v.map phi) : ℕ) : ℚ), IotaW.isWeighted_iota K phi, ?_⟩
  intro v v' hvv'
  have hq : ((Iota.iota K (v.map phi) : ℕ) : ℚ) = ((Iota.iota K (v'.map phi) : ℕ) : ℚ) := hvv'
  have hnat : Iota.iota K (v.map phi) = Iota.iota K (v'.map phi) := by
    exact_mod_cast hq
  have hmem : ∀ (u : List B) (x : ℕ), x ∈ u.map phi → x + 1 < K := by
    intro u x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact hlt b
  have : v.map phi = v'.map phi :=
    Iota.iota_inj (hmem v) (hmem v') hnat
  exact List.map_injective_iff.mpr hphi_inj this

/-! ## Theorem `thm:decidable-equivalence-regular`: equivalence of regular functions -/

/-- **Theorem `thm:decidable-equivalence-regular` (semantic form).**  For two regular functions over
finite alphabets there is a bound `n` such that the two functions are equal as soon as they agree on
all inputs of length at most `n`.  Since the input alphabet is finite, there are finitely many such
inputs, so this is the decision procedure of the book: post-compose the two functions with an
injective weighted automaton, which by `Transducers.isWeighted_comp_regular` yields two weighted
automata over `ℚ`, and apply the equivalence (zeroness) criterion for weighted automata over a
field. -/
theorem regularFun_eq_of_short {A B : Type} [Finite A] [Finite B]
    {f g : List A → List B} (hf : IsRegularFun f) (hg : IsRegularFun g) :
    ∃ n : ℕ, (∀ w : List A, w.length ≤ n → f w = g w) → f = g := by
  classical
  obtain ⟨iota, hiotaW, hiotaInj⟩ := exists_injective_weighted B
  have hF : IsWeighted (iota ∘ f) := isWeighted_comp_regular hf hiotaW
  have hG : IsWeighted (iota ∘ g) := isWeighted_comp_regular hg hiotaW
  obtain ⟨n, hn⟩ := weighted_eq_of_short hF hG
  refine ⟨n, fun hshort => ?_⟩
  have hFG : iota ∘ f = iota ∘ g := hn (fun w hw => by simp [Function.comp, hshort w hw])
  funext w
  exact hiotaInj (congrFun hFG w)

/-- **Theorem `thm:decidable-equivalence-regular` (reduction form).**  Two regular functions over
finite alphabets are equal if and only if the two weighted automata over `ℚ` obtained by
post-composing them with an injective weighted automaton are equal.  This is exactly the reduction
drawn in the book, whose right hand side is decidable by Theorem
`thm:equivalence-weighted-automata`. -/
theorem regularFun_eq_iff_weighted_eq {A B : Type} [Finite A] [Finite B]
    {f g : List A → List B} (hf : IsRegularFun f) (hg : IsRegularFun g) :
    ∃ F G : List A → ℚ, IsWeighted F ∧ IsWeighted G ∧ (f = g ↔ F = G) := by
  obtain ⟨iota, hiotaW, hiotaInj⟩ := exists_injective_weighted B
  refine ⟨iota ∘ f, iota ∘ g, isWeighted_comp_regular hf hiotaW,
    isWeighted_comp_regular hg hiotaW, ?_⟩
  constructor
  · intro hfg; rw [hfg]
  · intro hFG
    funext w
    exact hiotaInj (congrFun hFG w)

/-- **Theorem `thm:decidable-equivalence-regular` (zeroness form).**  Two regular functions over
finite alphabets are equal if and only if a single weighted automaton over `ℚ` -- the difference of
the two automata obtained from the reduction -- is identically zero.  This is the book's remark that
the essential problem is zeroness, since weighted automata can be subtracted from each other. -/
theorem regularFun_eq_iff_weighted_zero {A B : Type} [Finite A] [Finite B]
    {f g : List A → List B} (hf : IsRegularFun f) (hg : IsRegularFun g) :
    ∃ H : List A → ℚ, IsWeighted H ∧ (f = g ↔ ∀ w, H w = 0) := by
  obtain ⟨iota, hiotaW, hiotaInj⟩ := exists_injective_weighted B
  refine ⟨fun w => iota (f w) - iota (g w),
    WLin.isWeighted_sub (isWeighted_comp_regular hf hiotaW)
      (isWeighted_comp_regular hg hiotaW), ?_⟩
  constructor
  · intro hfg w; rw [hfg]; ring
  · intro hzero
    funext w
    exact hiotaInj (sub_eq_zero.mp (hzero w))

end Lax916827Proofs.Transducers
