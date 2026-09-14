/-
**The computable equivalence bound for codes of two-way transducers.**

This file discharges the hypothesis `Transducers.EffectiveTwoWayBound` of
`RequestProject/PartC/EffectiveReg.lean`, the last hypothesis of Theorem
`thm:decidable-equivalence-regular` of *Transducers* (M. Bojańczyk).

`RequestProject/PartC/RegCodeBound.lean` already proves that an equivalence
bound *exists* for every pair of codes, but the bound it produces comes out of a
chain of existential statements over abstract finite types and so carries no
size information.  The explicit bound proved in
`RequestProject/PartC/RegShort.lean` (`Transducers.RegHankel.twoWay_eq_of_short`)
replaces that chain: two two-way transducers over a finite input alphabet with
`q₁` and `q₂` states agree everywhere as soon as they agree on the inputs of
length at most `idxBound a q₁ + idxBound a q₂`, an arithmetic expression in the
size `a` of the alphabet and in `q₁`, `q₂`.

All that is left here is to read those three numbers off the two codes -- the
letters, the output letters and the states occurring in a code are read off its
transition table, and there are at most two of each per entry -- and to check
that the resulting formula is primitive recursive.  The bookkeeping that turns
the resulting statement about the two coded transducers *read over the finite
test alphabet* into a statement about the coded relations over all of `ℕ` is
exactly the one of `Transducers.RegDec.exists_bound`, and is repeated here with
the explicit bound in place of the abstract one.
-/
import Lax916827Proofs.Source.PartC.RegCodeBound
import Lax916827Proofs.Source.PartC.RegShort
import Lax916827Proofs.Source.PartC.EffectiveReg
import Lax132576Proofs.Source.PartB.PairPrimrec
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegDec

/-! ## Counting the letters and the states of a code -/

/-- A finite alphabet given as a list has at most as many letters as the list
has entries. -/
lemma card_Ltr_le (L : List ℕ) : Fintype.card (Ltr L) ≤ L.length := by
  classical
  have h : Fintype.card (Ltr L) = L.toFinset.card := by
    rw [← Fintype.card_coe L.toFinset]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
  rw [h]
  exact List.toFinset_card_le L

/-- A code lists two input letters per entry. -/
lemma length_alphabet (c : TwoWayCode) : (alphabet c).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons t l ih => simp [alphabet, List.flatMap_cons] at ih ⊢; omega

/-- The test alphabet of two codes has two letters per entry of either code,
plus the fresh letter. -/
lemma length_testAlphabet (p : TwoWayCode × TwoWayCode) :
    (testAlphabet p).length = 2 * p.1.length + 2 * p.2.length + 1 := by
  simp [testAlphabet, length_alphabet]

/-- A code mentions at most two states per entry, plus the initial state. -/
lemma length_stAlph_le (c : TwoWayCode) : (stAlph c).length ≤ 2 * c.length + 1 := by
  have key : ∀ l : TwoWayCode, (l.flatMap (fun t => t.1.2.1 ::
      Sum.elim (fun _ : List ℕ => []) (fun z : ℕ × List ℕ × Bool => [z.1]) t.2)).length
        ≤ 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
        have ht : (Sum.elim (fun _ : List ℕ => ([] : List ℕ))
            (fun z : ℕ × List ℕ × Bool => [z.1]) t.2).length ≤ 1 := by
          cases t.2 <;> simp
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_cons]
        omega
  have := key c
  simp only [stAlph, List.length_cons]
  omega

/-! ## The bound -/

/-- **The equivalence bound of Theorem `thm:decidable-equivalence-regular`, as an explicit
function of the two codes.** -/
def codeBound (c₁ c₂ : TwoWayCode) : ℕ :=
  RegHankel.idxBound (2 * c₁.length + 2 * c₂.length + 1) (2 * c₁.length + 1)
    + RegHankel.idxBound (2 * c₁.length + 2 * c₂.length + 1) (2 * c₂.length + 1)

/-- **The explicit bound works.**  Two total coded two-way transducers that
agree on all inputs of length at most `codeBound c₁ c₂` compute the same
relation.

This is `Transducers.RegDec.exists_bound` with the abstract bound replaced by
the explicit one of `Transducers.RegHankel.twoWay_eq_of_short`. -/
theorem codeBound_spec (c₁ c₂ : TwoWayCode) (h₁ : TwoWayCodeTotal c₁)
    (h₂ : TwoWayCodeTotal c₂)
    (hshort : ∀ w : List ℕ, w.length ≤ codeBound c₁ c₂ →
      twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) :
    twoWayCodeRel c₁ = twoWayCodeRel c₂ := by
  classical
  set L := testAlphabet (c₁, c₂) with hLdef
  set O := outAlph c₁ ++ outAlph c₂ with hOdef
  have hO : 0 ∈ O := List.mem_append.2 (Or.inl (zero_mem_outAlph c₁))
  have hs₁ : ∀ y ∈ outAlph c₁, y ∈ O := fun y hy => List.mem_append.2 (Or.inl hy)
  have hs₂ : ∀ y ∈ outAlph c₂, y ∈ O := fun y hy => List.mem_append.2 (Or.inr hy)
  have hA : Fintype.card (Ltr L) ≤ 2 * c₁.length + 2 * c₂.length + 1 := by
    refine le_trans (card_Ltr_le L) ?_
    rw [hLdef, length_testAlphabet]
  have hQ₁ : Fintype.card (StT c₁) ≤ 2 * c₁.length + 1 :=
    le_trans (card_Ltr_le _) (length_stAlph_le c₁)
  have hQ₂ : Fintype.card (StT c₂) ≤ 2 * c₂.length + 1 :=
    le_trans (card_Ltr_le _) (length_stAlph_le c₂)
  -- the two coded transducers compute the same function over the finite alphabets
  have hf : finFun c₁ L O hO hs₁ h₁ = finFun c₂ L O hO hs₂ h₂ := by
    funext w
    refine RegHankel.twoWay_eq_of_short (finAut c₁ L O hO) (finAut c₂ L O hO)
      (finFun_computes hO hs₁ h₁) (finFun_computes hO hs₂ h₂) hA hQ₁ hQ₂
      (le_refl (codeBound c₁ c₂)) (fun u hu => ?_) w
    have hlen : (u.map Subtype.val).length ≤ codeBound c₁ c₂ := by simpa using hu
    have heq := hshort (u.map Subtype.val) hlen
    have hc1 : twoWayCodeRel c₁ (u.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ u).map Subtype.val) :=
      (computes_finAut_iff hO hs₁ u _).1 (finFun_computes hO hs₁ h₁ u)
    have hc2 : twoWayCodeRel c₂ (u.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ u).map Subtype.val) := heq ▸ hc1
    exact TwoWay.computes_unique ((computes_finAut_iff hO hs₂ u _).2 hc2)
      (finFun_computes hO hs₂ h₂ u)
  -- hence they compute the same relation on the strings over `L` ...
  have key : ∀ (w : List (Ltr L)) (v : List ℕ),
      twoWayCodeRel c₁ (w.map Subtype.val) v ↔ twoWayCodeRel c₂ (w.map Subtype.val) v := by
    intro w v
    have hc1 : twoWayCodeRel c₁ (w.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ w).map Subtype.val) :=
      (computes_finAut_iff hO hs₁ w _).1 (finFun_computes hO hs₁ h₁ w)
    have hc2 : twoWayCodeRel c₂ (w.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ w).map Subtype.val) := by
      rw [hf]
      exact (computes_finAut_iff hO hs₂ w _).1 (finFun_computes hO hs₂ h₂ w)
    constructor
    · intro h
      have : v = (finFun c₁ L O hO hs₁ h₁ w).map Subtype.val :=
        TwoWay.computes_unique h hc1
      rw [this]
      exact hc2
    · intro h
      have : v = (finFun c₁ L O hO hs₁ h₁ w).map Subtype.val :=
        TwoWay.computes_unique h hc2
      rw [this]
      exact hc1
  -- ... and therefore, by blindness to the letters outside the two codes, everywhere
  funext w v
  have hmem : ∀ x ∈ w.map (sanLetter (c₁, c₂)), x ∈ L := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact sanLetter_mem_testAlphabet (c₁, c₂) y
  set w' : List (Ltr L) := (w.map (sanLetter (c₁, c₂))).attachWith (· ∈ L) hmem with hw'
  have hval : w'.map Subtype.val = w.map (sanLetter (c₁, c₂)) := by simp [hw']
  have e₁ := twoWayCodeRel_map (blind_sanLetter_left (c₁, c₂)) w v
  have e₂ := twoWayCodeRel_map (blind_sanLetter_right (c₁, c₂)) w v
  have hkey := key w' v
  rw [hval] at hkey
  simp only [eq_iff_iff]
  rw [← e₁, ← e₂]
  exact hkey

/-! ## Computability of the bound -/

lemma primrec_codeBound : Primrec₂ codeBound := by
  have hpow : ∀ {α : Type} [Primcodable α] {f g : α → ℕ}, Primrec f → Primrec g →
      Primrec (fun a => (f a) ^ (g a)) := by
    intro α _ f g hf hg
    exact PairWeighted.primrec_pow.comp hf hg
  have hl₁ : Primrec (fun p : TwoWayCode × TwoWayCode => p.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hl₂ : Primrec (fun p : TwoWayCode × TwoWayCode => p.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have ha : Primrec (fun p : TwoWayCode × TwoWayCode =>
      2 * p.1.length + 2 * p.2.length + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hl₁)
        (Primrec.nat_mul.comp (Primrec.const 2) hl₂)) (Primrec.const 1)
  have hq : ∀ f : TwoWayCode × TwoWayCode → ℕ, Primrec f →
      Primrec (fun p : TwoWayCode × TwoWayCode => 2 * f p + 1) := by
    intro f hf
    exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hf) (Primrec.const 1)
  have hidx : ∀ f g : TwoWayCode × TwoWayCode → ℕ, Primrec f → Primrec g →
      Primrec (fun p : TwoWayCode × TwoWayCode => RegHankel.idxBound (f p) (g p)) := by
    intro f g hf hg
    simp only [RegHankel.idxBound]
    refine Primrec.nat_mul.comp (Primrec.nat_add.comp hf (Primrec.const 1)) ?_
    refine Primrec.nat_mul.comp
      (hpow (Primrec.nat_add.comp hg (Primrec.const 1))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hg) (Primrec.const 2))) ?_
    exact Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hg) (Primrec.const 1))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hg) (Primrec.const 2))
  have : Primrec (fun p : TwoWayCode × TwoWayCode => codeBound p.1 p.2) := by
    simp only [codeBound]
    exact Primrec.nat_add.comp (hidx _ _ ha (hq _ hl₁)) (hidx _ _ ha (hq _ hl₂))
  exact this

end RegDec

/-- **A computable equivalence bound for codes of two-way transducers.**  This
discharges the hypothesis `Transducers.EffectiveTwoWayBound`. -/
theorem effectiveTwoWayBound : EffectiveTwoWayBound :=
  ⟨RegDec.codeBound, RegDec.primrec_codeBound.to_comp,
    fun c₁ c₂ h₁ h₂ hshort => RegDec.codeBound_spec c₁ c₂ h₁ h₂ hshort⟩

end Lax916827Proofs.Transducers
