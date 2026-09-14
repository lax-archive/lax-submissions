/-
The marked sum of two arbitrary regular functions, and the passage from the
marked sum to the statement of Claim `claim:conditional` of *Transducers* (M. Bojańczyk).

The marked sum is built by induction on the composition tree of the two regular
functions: the base cases are in `RequestProject/PartC/SumShape.lean` (a
rational function) and in `RequestProject/PartC/SumPrime.lean` (map reverse and
map duplicate), and the induction step is closure under composition.

Once the marked sum `F` of `f₁` and `f₂` is available, the function asked for by
Claim `claim:conditional` is obtained by composing `F` with two rational functions: the first
one prepends the marker that says whether the input is a nonempty string over
the second alphabet, and the second one deletes the marker of the output (and
replaces the outputs that are not marked strings by a fixed string using both
output alphabets).
-/
import Lax916827Proofs.Source.PartC.SumPrime
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## The marked sum of two regular functions -/

/-- The marked sum of a regular function with the identity.  The finiteness of
the two alphabets is carried as an explicit hypothesis, so that the induction on
the composition tree has access to the finiteness of the intermediate
alphabets. -/
theorem msum_left {A B : Type} {f : List A → List B} (hf : IsRegularFun f)
    (A₂ : Type) [Finite A₂] : Finite A → Finite B → MSum f (id : List A₂ → List A₂) := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact msum_rat_id hrat
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 := msum_rat_id (A₂ := A₂) (isRationalFun_map (e : A → Option A₀))
        have h2 := msum_mapReverse_id A₀ A₂
        have h3 := msum_rat_id (A₂ := A₂) (isRationalFun_map (e'.symm : Option A₀ → B))
        exact (msum_comp (msum_comp h1 h2) h3).congr (fun u => (hfe u).symm) (fun _ => rfl)
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 := msum_rat_id (A₂ := A₂) (isRationalFun_map (e : A → Option A₀))
        have h2 := msum_mapDuplicate_id A₀ A₂
        have h3 := msum_rat_id (A₂ := A₂) (isRationalFun_map (e'.symm : Option A₀ → B))
        exact (msum_comp (msum_comp h1 h2) h3).congr (fun u => (hfe u).symm) (fun _ => rfl)
  | id A =>
      intro hA _
      haveI := hA
      exact msum_id_id
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      haveI := hA; haveI := hB; haveI := hC
      exact (msum_comp (ihf hA hB) (ihg hB hC)).congr (fun _ => rfl) (fun _ => rfl)

/-- The marked sum of two regular functions. -/
theorem msum_of_regular {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (h₁ : IsRegularFun f₁) (h₂ : IsRegularFun f₂) : MSum f₁ f₂ := by
  have hl : MSum (id : List A₁ → List A₁) f₂ := msum_swap (msum_left h₂ A₁ ‹_› ‹_›)
  have hr : MSum f₁ (id : List B₂ → List B₂) := msum_left h₁ B₂ ‹_› ‹_›
  exact (msum_comp hl hr).congr (fun _ => rfl) (fun _ => rfl)

/-! ## From the marked sum to the disjoint sum -/

namespace SumTo

variable {A₁ A₂ B₁ B₂ : Type}

/-- The states of the automaton testing that a string is nonempty and uses only
letters of the second alphabet. -/
inductive PreSt | init | good | bad
  deriving DecidableEq, Fintype

/-- The transition function of that automaton. -/
def preStep : PreSt → (A₁ ⊕ A₂) → PreSt
  | PreSt.init, Sum.inr _ => PreSt.good
  | PreSt.good, Sum.inr _ => PreSt.good
  | _, _ => PreSt.bad

lemma preStep_bad (w : List (A₁ ⊕ A₂)) : strTrans preStep w PreSt.bad = PreSt.bad := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simpa [strTrans, preStep] using ih

lemma preStep_good (v : List A₂) :
    strTrans (preStep (A₁ := A₁)) (v.map Sum.inr) PreSt.good = PreSt.good := by
  induction v with
  | nil => rfl
  | cons c v ih => simpa [strTrans, preStep] using ih

/-- The rational preprocessing: prepend the marker saying whether the input is a
nonempty string over the second alphabet. -/
def pre (w : List (A₁ ⊕ A₂)) : List (Bool ⊕ A₁ ⊕ A₂) :=
  if strTrans preStep w PreSt.init = PreSt.good then Sum.inl true :: w.map Sum.inr
  else Sum.inl false :: w.map Sum.inr

lemma pre_mapInl {u : List A₁} (hu : u ≠ []) : pre (A₂ := A₂) (u.map Sum.inl) = mkL A₂ u := by
  cases u with
  | nil => exact absurd rfl hu
  | cons a u =>
      have h : strTrans (preStep (A₁ := A₁) (A₂ := A₂)) ((a :: u).map Sum.inl) PreSt.init
          = PreSt.bad := by
        show strTrans preStep (u.map Sum.inl) (preStep PreSt.init (Sum.inl a)) = PreSt.bad
        exact preStep_bad _
      rw [pre, if_neg (by rw [h]; simp)]
      simp [mkL, List.map_map, Function.comp_def]

lemma pre_mapInr {v : List A₂} (hv : v ≠ []) : pre (A₁ := A₁) (v.map Sum.inr) = mkR A₁ v := by
  cases v with
  | nil => exact absurd rfl hv
  | cons c v =>
      have h : strTrans (preStep (A₁ := A₁) (A₂ := A₂)) ((c :: v).map Sum.inr) PreSt.init
          = PreSt.good := by
        show strTrans preStep (v.map Sum.inr) (preStep PreSt.init (Sum.inr c)) = PreSt.good
        exact preStep_good v
      rw [pre, if_pos h]
      simp [mkR, List.map_map, Function.comp_def]

lemma pre_ne_mkL {w : List (A₁ ⊕ A₂)} (h : ¬ ∃ u : List A₁, w = u.map Sum.inl) :
    ∀ u : List A₁, pre w ≠ mkL A₂ u := by
  intro u hu
  refine h ⟨u, ?_⟩
  have hmap : w.map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂)
      = u.map (fun a => Sum.inr (Sum.inl a)) := by
    rw [pre] at hu
    split at hu <;> · simp only [mkL, List.cons.injEq] at hu; exact hu.2
  have : w.map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂)
      = (u.map Sum.inl).map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂) := by
    rw [hmap, List.map_map]; rfl
  exact List.map_injective_iff.2 (fun x y hxy => by simpa using hxy) this

lemma pre_ne_mkR {w : List (A₁ ⊕ A₂)} (h : ¬ ∃ v : List A₂, w = v.map Sum.inr) :
    ∀ v : List A₂, pre w ≠ mkR A₁ v := by
  intro v hv
  refine h ⟨v, ?_⟩
  have hmap : w.map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂)
      = v.map (fun a => Sum.inr (Sum.inr a)) := by
    rw [pre] at hv
    split at hv <;> · simp only [mkR, List.cons.injEq] at hv; exact hv.2
  have : w.map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂)
      = (v.map Sum.inr).map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂) := by
    rw [hmap, List.map_map]; rfl
  exact List.map_injective_iff.2 (fun x y hxy => by simpa using hxy) this

lemma isRationalFun_markCons [Finite A₁] [Finite A₂] (b : Bool) :
    IsRationalFun (fun w : List (A₁ ⊕ A₂) => (Sum.inl b : Bool ⊕ A₁ ⊕ A₂) :: w.map Sum.inr) := by
  have h := isRationalFun_comp
    (isRationalFun_map (Sum.inr : A₁ ⊕ A₂ → Bool ⊕ A₁ ⊕ A₂))
    (isRationalFun_cons (Sum.inl b : Bool ⊕ A₁ ⊕ A₂))
  exact h

lemma isRationalFun_pre [Finite A₁] [Finite A₂] :
    IsRationalFun (pre : List (A₁ ⊕ A₂) → List (Bool ⊕ A₁ ⊕ A₂)) :=
  isRationalFun_ite preStep PreSt.init (fun s => s = PreSt.good)
    (isRationalFun_markCons true) (isRationalFun_markCons false)

/-- The homomorphism deleting the marker of an output. -/
def postHom : (Bool ⊕ B₁ ⊕ B₂) → List (B₁ ⊕ B₂)
  | Sum.inl _ => []
  | Sum.inr y => [y]

/-- The rational postprocessing: delete the marker, or produce the fixed string
`botOut` if the output is not a marked string. -/
def post (botOut : List (B₁ ⊕ B₂)) (w : List (Bool ⊕ B₁ ⊕ B₂)) : List (B₁ ⊕ B₂) :=
  if shp w = Shp.inL ∨ shp w = Shp.inR then homOf postHom w else botOut

lemma post_mkL (botOut : List (B₁ ⊕ B₂)) (v : List B₁) :
    post botOut (mkL B₂ v) = v.map Sum.inl := by
  rw [post, if_pos (Or.inl (shp_mkL v))]
  have key : ∀ v : List B₁,
      homOf (postHom (B₁ := B₁) (B₂ := B₂)) (v.map (fun b => Sum.inr (Sum.inl b)))
        = v.map Sum.inl := by
    intro v
    induction v with
    | nil => rfl
    | cons b v ih => simpa [homOf, postHom] using ih
  simpa [mkL, homOf, postHom] using key v

lemma post_mkR (botOut : List (B₁ ⊕ B₂)) (v : List B₂) :
    post botOut (mkR B₁ v) = v.map Sum.inr := by
  rw [post, if_pos (Or.inr (shp_mkR v))]
  have key : ∀ v : List B₂,
      homOf (postHom (B₁ := B₁) (B₂ := B₂)) (v.map (fun b => Sum.inr (Sum.inr b)))
        = v.map Sum.inr := by
    intro v
    induction v with
    | nil => rfl
    | cons b v ih => simpa [homOf, postHom] using ih
  simpa [mkR, homOf, postHom] using key v

lemma post_bad (botOut : List (B₁ ⊕ B₂)) {w : List (Bool ⊕ B₁ ⊕ B₂)}
    (h₁ : ∀ v : List B₁, w ≠ mkL B₂ v) (h₂ : ∀ v : List B₂, w ≠ mkR B₁ v) :
    post botOut w = botOut := by
  have hL : shp w ≠ Shp.inL := fun h => by
    obtain ⟨v, hv⟩ := (shp_eq_inL_iff w).1 h; exact h₁ v hv
  have hR : shp w ≠ Shp.inR := fun h => by
    obtain ⟨v, hv⟩ := (shp_eq_inR_iff w).1 h; exact h₂ v hv
  rw [post, if_neg (by tauto)]

lemma isRationalFun_post [Finite B₁] [Finite B₂] (botOut : List (B₁ ⊕ B₂)) :
    IsRationalFun (post botOut : List (Bool ⊕ B₁ ⊕ B₂) → List (B₁ ⊕ B₂)) :=
  isRationalFun_ite shpStep Shp.start (fun s => s = Shp.inL ∨ s = Shp.inR)
    (isRationalFun_homOf postHom) (isRationalFun_const _)

end SumTo

/-- **Claim `claim:conditional`** (corrected on the empty input).  See
`RequestProject/PartC/RegSum.lean` for the statement of the claim and for the
discussion of the correction. -/
theorem msum_to_sum {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    [Nonempty B₁] [Nonempty B₂] {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, u ≠ [] → F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, u ≠ [] → F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) := by
  classical
  obtain ⟨F, hFreg, hFL, hFR, bot, hbotL, hbotR, hbot⟩ := msum_of_regular hf₁ hf₂
  set b₁ : B₁ := Classical.arbitrary B₁ with hb₁
  set b₂ : B₂ := Classical.arbitrary B₂ with hb₂
  set botOut : List (B₁ ⊕ B₂) := [Sum.inl b₁, Sum.inr b₂] with hbotOut
  have hreg : IsRegularFun (fun w : List (A₁ ⊕ A₂) => SumTo.post botOut (F (SumTo.pre w))) :=
    ((IsRegularFun.of_rational SumTo.isRationalFun_pre).comp hFreg).comp'
      (IsRegularFun.of_rational (SumTo.isRationalFun_post botOut)) (fun _ => rfl)
  refine ⟨botOut, fun w => SumTo.post botOut (F (SumTo.pre w)), ⟨b₁, by simp [hbotOut]⟩,
    ⟨b₂, by simp [hbotOut]⟩, hreg, fun u hu => ?_, fun u hu => ?_, fun w hw₁ hw₂ => ?_⟩
  · show SumTo.post botOut (F (SumTo.pre (u.map Sum.inl))) = _
    rw [SumTo.pre_mapInl hu, hFL u, SumTo.post_mkL]
  · show SumTo.post botOut (F (SumTo.pre (u.map Sum.inr))) = _
    rw [SumTo.pre_mapInr hu, hFR u, SumTo.post_mkR]
  · show SumTo.post botOut (F (SumTo.pre w)) = _
    rw [hbot (SumTo.pre w) (SumTo.pre_ne_mkL hw₁) (SumTo.pre_ne_mkR hw₂)]
    exact SumTo.post_bad botOut hbotL hbotR

end Lax916827Proofs.Transducers
