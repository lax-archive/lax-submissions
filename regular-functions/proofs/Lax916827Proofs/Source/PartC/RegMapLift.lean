/-
The first item of Lemma `lem:regular-closure-properties` of *Transducers* (M. Bojańczyk): regular
functions are closed under map lifting.

Since the map lifting commutes with composition (`mapLift_comp'`), it is enough
to lift the prime regular functions: the map lifting of a rational function is
rational (`isRationalFun_mapLift`, in `RequestProject/PartC/MapLiftRat.lean`),
and the map lifting of map reverse (resp. map duplicate) is regular
(`isRegularFun_mapLift_mapReverse` and `isRegularFun_mapLift_mapDuplicate`, in
`RequestProject/PartC/MapLiftPrime.lean`).  The map lifting of a
letter-to-letter map is again a letter-to-letter map, which takes care of the
recodings that appear in the two prime cases.
-/
import Lax916827Proofs.Source.PartC.MapLiftRat
import Lax916827Proofs.Source.PartC.MapLiftPrime
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- **Lemma `lem:regular-closure-properties` (map lifting).**  The map lifting of a regular function
is regular.  The finiteness of the two alphabets is carried as an explicit hypothesis, so that the
induction on the composition tree has access to the finiteness of the intermediate alphabets. -/
theorem isRegularFun_mapLift_aux {A B : Type} {f : List A → List B} (hf : IsRegularFun f) :
    Finite A → Finite B → IsRegularFun (mapLift f) := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact IsRegularFun.of_rational (isRationalFun_mapLift hrat)
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 : IsRegularFun (fun w : List (Option A) =>
            w.map (Option.map (e : A → Option A₀))) := isRegularFun_map _
        have h3 : IsRegularFun (fun w : List (Option (Option A₀)) =>
            w.map (Option.map (e'.symm : Option A₀ → B))) := isRegularFun_map _
        refine (h1.comp (isRegularFun_mapLift_mapReverse A₀)).comp' h3 (fun w => ?_)
        have hfeq : f = (fun v : List (Option A₀) => v.map (e'.symm : Option A₀ → B)) ∘
            ((mapReverse A₀) ∘ (fun v : List A => v.map (e : A → Option A₀))) := by
          funext v; exact hfe v
        rw [hfeq, mapLift_comp', mapLift_comp']
        show mapLift (fun v : List (Option A₀) => v.map (e'.symm : Option A₀ → B))
          (mapLift (mapReverse A₀)
            (mapLift (fun v : List A => v.map (e : A → Option A₀)) w)) = _
        rw [mapLift_letterMap, mapLift_letterMap]
        rfl
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 : IsRegularFun (fun w : List (Option A) =>
            w.map (Option.map (e : A → Option A₀))) := isRegularFun_map _
        have h3 : IsRegularFun (fun w : List (Option (Option A₀)) =>
            w.map (Option.map (e'.symm : Option A₀ → B))) := isRegularFun_map _
        refine (h1.comp (isRegularFun_mapLift_mapDuplicate A₀)).comp' h3 (fun w => ?_)
        have hfeq : f = (fun v : List (Option A₀) => v.map (e'.symm : Option A₀ → B)) ∘
            ((mapDuplicate A₀) ∘ (fun v : List A => v.map (e : A → Option A₀))) := by
          funext v; exact hfe v
        rw [hfeq, mapLift_comp', mapLift_comp']
        show mapLift (fun v : List (Option A₀) => v.map (e'.symm : Option A₀ → B))
          (mapLift (mapDuplicate A₀)
            (mapLift (fun v : List A => v.map (e : A → Option A₀)) w)) = _
        rw [mapLift_letterMap, mapLift_letterMap]
        rfl
  | id A =>
      intro _ _
      rw [mapLift_id]
      exact isRegularFun_id
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      haveI := hA; haveI := hB; haveI := hC
      rw [mapLift_comp']
      exact (ihf hA hB).comp (ihg hB hC)

/-- **Lemma `lem:regular-closure-properties` (map lifting).**  The map lifting of a regular function
is regular. -/
theorem isRegularFun_mapLift {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsRegularFun (mapLift f) :=
  isRegularFun_mapLift_aux hf ‹_› ‹_›

end Lax916827Proofs.Transducers
