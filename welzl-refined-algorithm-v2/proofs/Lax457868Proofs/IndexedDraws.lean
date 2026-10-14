import Mathlib.Tactic
import Lax457868Proofs.FairBitIndices
import Lax457868Proofs.SamplerUniformDraws

/-!
A finite fair-bit tape can drive repeated draws from an actual finite set.
Each accepted index selects the corresponding entry of `X.toList`; the finite
sample space therefore consists of the sampler's concrete indexed inputs.
-/

namespace Lax457868Proofs.IndexedDraws

open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.SamplerUniformDraws

variable {α : Type*} [DecidableEq α]

/-- One ordered collection of `r` independent finite fair-bit retry tapes. -/
abbrev DrawBitTape (X : Finset α) (r t : ℕ) :=
  Fin r → BitTape X.card t

/-- Interpret an index as the corresponding actual entry in `X.toList`. -/
noncomputable def indexedValue (X : Finset α) (i : Fin X.card) : {x // x ∈ X} := by
  let j : Fin X.toList.length := ⟨i.val, by simpa using i.isLt⟩
  exact ⟨X.toList.get j, Finset.mem_toList.mp (List.get_mem _ j)⟩

/-- The ordered list indexing is a bijection between positions and elements. -/
noncomputable def indexedValueEquiv (X : Finset α) : Fin X.card ≃ {x // x ∈ X} :=
  Equiv.ofBijective (indexedValue X) (by
    constructor
    · intro i j hij
      have hget : X.toList.get
          ⟨i.val, by simpa using i.isLt⟩ = X.toList.get
          ⟨j.val, by simpa using j.isLt⟩ := congrArg Subtype.val hij
      have hidx := (List.nodup_iff_injective_get.mp (Finset.nodup_toList X)) hget
      have hval : i.val = j.val :=
        congrArg (fun z : Fin X.toList.length => z.val) hidx
      exact Fin.ext hval
    · intro x
      have hx : (x : α) ∈ X.toList := Finset.mem_toList.mpr x.property
      obtain ⟨j, hget⟩ := List.mem_iff_get.mp hx
      let i : Fin X.card := ⟨j.val, by simpa using j.isLt⟩
      refine ⟨i, ?_⟩
      apply Subtype.ext
      have hj : (⟨i.val, by simpa using i.isLt⟩ : Fin X.toList.length) = j := by
        apply Fin.ext
        rfl
      change X.toList.get ⟨i.val, by simpa using i.isLt⟩ = x.val
      rw [hj]
      exact hget)

/-- The indexed value at a position is exactly the `Finset.toList` lookup. -/
lemma indexedValue_eq_get (X : Finset α) (i : Fin X.card) :
    (indexedValue X i).val = X.toList.get
      ⟨i.val, by simpa using i.isLt⟩ := rfl

/-- Decode each requested index by the existing capped fair-bit selector and
return the corresponding actual member of `X`. -/
noncomputable def selectIndexedDraw (X : Finset α) (hX : 0 < X.card) (t : ℕ)
    (bits : BitTape X.card t) : Option {x // x ∈ X} :=
  (selectBitIndex X.card hX t bits).map (indexedValue X)

/-- A complete draw tape whose every coordinate succeeds, with replacement. -/
noncomputable def successfulDrawTape (X : Finset α) (hX : 0 < X.card) (r t : ℕ)
    (bits : DrawBitTape X r t) : Option (Tape X r) := by
  classical
  let draws : Fin r → Option {x // x ∈ X} := fun i => selectIndexedDraw X hX t (bits i)
  if h : ∀ i, ∃ x, draws i = some x then
    exact some fun i => Classical.choose (h i)
  else
    exact none

/-- Successful output has precisely the requested number of actual draws. -/
lemma successfulDrawTape_eq_some_iff (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (bits : DrawBitTape X r t) (draws : Tape X r) :
    successfulDrawTape X hX r t bits = some draws ↔
      ∀ i, selectIndexedDraw X hX t (bits i) = some (draws i) := by
  classical
  unfold successfulDrawTape
  let f : Fin r → Option {x // x ∈ X} := fun i => selectIndexedDraw X hX t (bits i)
  change (if h : ∀ i, ∃ x, f i = some x then
      some (fun i => Classical.choose (h i)) else none) = some draws ↔
    ∀ i, f i = some (draws i)
  by_cases h : ∀ i, ∃ x, f i = some x
  · rw [dif_pos h]
    constructor
    · intro hout
      have hfun : (fun i => Classical.choose (h i)) = draws := Option.some.inj hout
      intro i
      rw [← hfun]
      exact Classical.choose_spec (h i)
    · intro hall
      have hfun : (fun i => Classical.choose (h i)) = draws := by
        funext i
        apply Option.some.inj
        exact (Classical.choose_spec (h i)).symm.trans (hall i)
      exact congrArg (fun f => some f) hfun
  · constructor
    · rw [dif_neg h]
      simp
    · intro hall
      have hall' : ∀ i, ∃ x, f i = some x := fun i => ⟨draws i, hall i⟩
      rw [dif_neg h]
      exact (h hall').elim

/-- The output is absent exactly when at least one requested coordinate fails
to decode within its cap. -/
lemma successfulDrawTape_eq_none_iff (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (bits : DrawBitTape X r t) :
    successfulDrawTape X hX r t bits = none ↔
      ¬ ∀ i, ∃ x, selectIndexedDraw X hX t (bits i) = some x := by
  classical
  unfold successfulDrawTape
  let f : Fin r → Option {x // x ∈ X} := fun i => selectIndexedDraw X hX t (bits i)
  change (if h : ∀ i, ∃ x, f i = some x then
      some (fun i => Classical.choose (h i)) else none) = none ↔
    ¬ ∀ i, ∃ x, f i = some x
  by_cases h : ∀ i, ∃ x, f i = some x
  · simp [h]
  · simp [h]

/-- Ordered output tapes use one sampler draw at every position and allow
repetitions, exactly as `SamplerUniformDraws.Tape`. -/
noncomputable def drawFiber (X : Finset α) (hX : 0 < X.card) (r t : ℕ)
    (draws : Tape X r) : Finset (DrawBitTape X r t) :=
  Finset.univ.filter fun bits =>
    ∀ k, selectIndexedDraw X hX t (bits k) = some (draws k)

/-- The actual indexed-selector fiber is exactly the set of tapes whose
successful result is the specified ordered sampler draw tape. -/
lemma mem_drawFiber_iff (X : Finset α) (hX : 0 < X.card) (r t : ℕ)
    (draws : Tape X r) (bits : DrawBitTape X r t) :
    bits ∈ drawFiber X hX r t draws ↔
      successfulDrawTape X hX r t bits = some draws := by
  simp [drawFiber, successfulDrawTape_eq_some_iff]

/-- Change a block tape by swapping the two requested indices independently
at each sampler coordinate. -/
noncomputable def swapDrawBitTape (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (a b : Tape X r) (bits : DrawBitTape X r t) : DrawBitTape X r t :=
  fun k => swapBitTape X.card hX
    ((indexedValueEquiv X).symm (a k)) ((indexedValueEquiv X).symm (b k)) t (bits k)

/-- Coordinatewise swaps restore the original fair-bit tape. -/
lemma swapDrawBitTape_involutive (X : Finset α) (hX : 0 < X.card)
    (r t : ℕ) (a b : Tape X r) (bits : DrawBitTape X r t) :
    swapDrawBitTape X hX r t a b (swapDrawBitTape X hX r t a b bits) = bits := by
  funext k
  exact swapBitTape_involutive X.card hX
    ((indexedValueEquiv X).symm (a k)) ((indexedValueEquiv X).symm (b k)) t (bits k)

/-- List-indexed values respect the transposition of their two positions. -/
lemma indexedValue_swap (X : Finset α) (i j k : Fin X.card) :
    indexedValue X (swapFinIndex i j k) =
      if indexedValue X k = indexedValue X i then indexedValue X j
      else if indexedValue X k = indexedValue X j then indexedValue X i
      else indexedValue X k := by
  by_cases hki : k = i
  · subst k
    simp [swapFinIndex]
  · by_cases hkj : k = j
    · subst k
      have hji : j ≠ i := by intro h; exact hki h
      have hv : indexedValue X j ≠ indexedValue X i := by
        intro he
        exact hji ((indexedValueEquiv X).injective he)
      simp [swapFinIndex, hji, hv]
    · have hki' : indexedValue X k ≠ indexedValue X i := by
        intro he
        exact hki ((indexedValueEquiv X).injective he)
      have hkj' : indexedValue X k ≠ indexedValue X j := by
        intro he
        exact hkj ((indexedValueEquiv X).injective he)
      simp [swapFinIndex, hki, hkj, hki', hkj']

/-- The fair-bit coordinate swap transports each selected element from `a` to
`b` and, more generally, transports any output in `X` by the same transposition. -/
lemma selectIndexedDraw_swap (X : Finset α) (hX : 0 < X.card) (t : ℕ)
    (a b : {x // x ∈ X}) (bits : BitTape X.card t) :
    selectIndexedDraw X hX t
        (swapBitTape X.card hX ((indexedValueEquiv X).symm a)
          ((indexedValueEquiv X).symm b) t bits) =
      (selectIndexedDraw X hX t bits).map
        (fun x => if x = a then b else if x = b then a else x) := by
  unfold selectIndexedDraw
  rw [selectBitIndex_swap]
  cases h : selectBitIndex X.card hX t bits with
  | none => rfl
  | some i =>
      simp only [Option.map_some]
      have hval := indexedValue_swap X ((indexedValueEquiv X).symm a)
        ((indexedValueEquiv X).symm b) i
      have hA : indexedValue X ((indexedValueEquiv X).symm a) = a :=
        Equiv.apply_symm_apply (indexedValueEquiv X) a
      have hB : indexedValue X ((indexedValueEquiv X).symm b) = b :=
        Equiv.apply_symm_apply (indexedValueEquiv X) b
      rw [hA, hB] at hval
      exact congrArg some hval

/-- Every two legal ordered draw outcomes have equally large joint fair-bit
fibers. The bijection swaps their requested indexed-list entries separately at
each coordinate. -/
lemma card_drawFiber_eq (X : Finset α) (hX : 0 < X.card) (r t : ℕ)
    (a b : Tape X r) : (drawFiber X hX r t a).card = (drawFiber X hX r t b).card := by
  classical
  apply Finset.card_bij (s := drawFiber X hX r t a) (t := drawFiber X hX r t b)
    (fun bits _ => swapDrawBitTape X hX r t a b bits)
  · intro bits hbits
    simp only [drawFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hbits ⊢
    intro k
    simpa [swapDrawBitTape, hbits k] using
      selectIndexedDraw_swap X hX t (a k) (b k) (bits k)
  · intro bits hbits other hother heq
    have h := congrArg (swapDrawBitTape X hX r t a b) heq
    simpa [swapDrawBitTape_involutive] using h
  · intro bits hbits
    simp only [drawFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hbits ⊢
    refine ⟨swapDrawBitTape X hX r t a b bits, ?_, swapDrawBitTape_involutive X hX r t a b bits⟩
    intro k
    have hswap := selectIndexedDraw_swap X hX t (a k) (b k) (bits k)
    rw [hbits k] at hswap
    by_cases hba : b k = a k <;> simpa [swapDrawBitTape, hba] using hswap

/-- Every legal ordered draw tape has a positive fair-bit fiber once each
coordinate has at least one retry available. -/
lemma drawFiber_nonempty (X : Finset α) (hX : 0 < X.card) (r t : ℕ)
    (ht : 0 < t) (draws : Tape X r) : (drawFiber X hX r t draws).Nonempty := by
  classical
  let bits : DrawBitTape X r t := fun k =>
    Classical.choose (indexFiber_nonempty X.card hX ht
      ((indexedValueEquiv X).symm (draws k)))
  have hbits (k : Fin r) :
      selectBitIndex X.card hX t (bits k) =
        some ((indexedValueEquiv X).symm (draws k)) := by
    have hmem := Classical.choose_spec (indexFiber_nonempty X.card hX ht
      ((indexedValueEquiv X).symm (draws k)))
    simpa [bits, indexFiber] using hmem
  refine ⟨bits, ?_⟩
  simp only [drawFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  intro k
  change (selectBitIndex X.card hX t (bits k)).map (indexedValue X) = some (draws k)
  rw [hbits k]
  have hval : indexedValue X ((indexedValueEquiv X).symm (draws k)) = draws k :=
    Equiv.apply_symm_apply (indexedValueEquiv X) (draws k)
  simpa [hval]

end Lax457868Proofs.IndexedDraws
