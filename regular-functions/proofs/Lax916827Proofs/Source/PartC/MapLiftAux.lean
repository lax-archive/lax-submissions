/-
General facts about the map lifting (Definition `def:map-lifting`), used in the proof of
Lemma `lem:regular-closure-properties` of *Transducers* (M. Bojańczyk).

`RequestProject/PartA/MapLift.lean` proves that the map lifting commutes with
composition for functions that are computed letter by letter (`OneStep`).  Here
the same fact is proved for arbitrary functions, which is what is needed for
regular functions: the point is that the blocks of `mapLift f w` are exactly the
images under `f` of the blocks of `w`.
-/
import Lax916827Proofs.Source.PartC.RegularDef
import Lax765601Proofs.Source.PartA.MapLift
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B C : Type}

/-- The blocks of a string that is assembled from a nonempty list of blocks are
the blocks that it was assembled from. -/
lemma splitSep_intercalate (xs : List (List A)) (hxs : xs ≠ []) :
    splitSep (List.intercalate [none] (xs.map (fun u => u.map some))) = xs := by
  induction xs with
  | nil => exact absurd rfl hxs
  | cons u xs ih =>
      by_cases hxs' : xs = []
      · subst hxs'
        have h0 : splitSep ([] : List (Option A)) = [[]] := rfl
        have := splitSep_map_some_append u ([] : List (Option A)) [] [] h0
        simpa [List.intercalate] using this
      · have hne : (xs.map (fun u : List A => u.map some)) ≠ [] := by
          simpa using hxs'
        rw [List.map_cons, intercalate_cons_cons _ _ _ hne]
        have h1 : (u.map some) ++ [none] ++
            List.intercalate [none] (xs.map (fun u : List A => u.map some))
            = (u.map some) ++ (none ::
              List.intercalate [none] (xs.map (fun u : List A => u.map some))) := by
          simp
        rw [h1]
        have h2 : splitSep (none ::
            List.intercalate [none] (xs.map (fun u : List A => u.map some)))
            = [] :: splitSep (List.intercalate [none] (xs.map (fun u : List A => u.map some))) :=
          rfl
        rw [splitSep_map_some_append u _ [] _ h2, ih hxs']
        simp

/-- The blocks of `mapLift f w` are the images under `f` of the blocks of `w`. -/
lemma splitSep_mapLift (f : List A → List B) (w : List (Option A)) :
    splitSep (mapLift f w) = (splitSep w).map f := by
  have hne : (splitSep w).map f ≠ [] := by
    simpa using splitSep_ne_nil w
  have := splitSep_intercalate ((splitSep w).map f) hne
  simpa [mapLift, List.map_map, Function.comp_def] using this

/-- The map lifting commutes with composition (no assumption on the
functions). -/
lemma mapLift_comp' (f : List A → List B) (g : List B → List C) :
    mapLift (g ∘ f) = mapLift g ∘ mapLift f := by
  funext w
  show mapLift (g ∘ f) w = mapLift g (mapLift f w)
  rw [mapLift, mapLift, splitSep_mapLift]
  simp [List.map_map, Function.comp_def]

/-! ## The map lifting and letter-to-letter maps -/

/-- Intercalation commutes with a letter-to-letter map. -/
lemma map_intercalate {α β : Type} (h : α → β) (sep : List α) (xs : List (List α)) :
    (List.intercalate sep xs).map h = List.intercalate (sep.map h) (xs.map (List.map h)) := by
  induction xs with
  | nil => simp [List.intercalate]
  | cons x xs ih =>
      by_cases hxs : xs = []
      · subst hxs; simp [List.intercalate]
      · rw [intercalate_cons_cons _ _ _ hxs, List.map_cons,
          intercalate_cons_cons _ _ _ (by simpa using hxs)]
        simp [ih]

/-- Splitting into blocks commutes with a letter-to-letter map. -/
lemma splitSep_map_optionMap (h : A → B) (w : List (Option A)) :
    splitSep (w.map (Option.map h)) = (splitSep w).map (List.map h) := by
  induction w with
  | nil => simp [splitSep]
  | cons x w ih =>
      cases x with
      | none => simpa [splitSep] using ih
      | some a =>
          cases hw : splitSep w with
          | nil => exact absurd hw (splitSep_ne_nil w)
          | cons c cs =>
              have h2 : splitSep (w.map (Option.map h)) = c.map h :: cs.map (List.map h) := by
                rw [ih, hw]; simp
              simp only [List.map_cons, Option.map_some]
              rw [splitSep, h2, splitSep, hw]
              simp

/-- The map lifting commutes with a letter-to-letter map, provided the lifted
functions do. -/
lemma mapLift_map_optionMap {f : List A → List A} {g : List B → List B} (h : A → B)
    (hcomm : ∀ l : List A, g (l.map h) = (f l).map h) (w : List (Option A)) :
    mapLift g (w.map (Option.map h)) = (mapLift f w).map (Option.map h) := by
  rw [mapLift, mapLift, splitSep_map_optionMap, map_intercalate]
  congr 1
  simp only [List.map_map]
  exact List.map_congr_left (fun u _ => by
    simp [Function.comp_def, hcomm u, List.map_map])

/-! ## Decomposition of a string at its first separator -/

/-- Every string over `A + 1` either has no separator, or splits as a first
block, a separator, and a strictly shorter rest. -/
lemma sep_decomp (w : List (Option A)) :
    (∃ u : List A, w = u.map some) ∨
      (∃ (u : List A) (w' : List (Option A)),
        w = u.map some ++ none :: w' ∧ w'.length < w.length) := by
  induction w with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons x w ih =>
      cases x with
      | none => exact Or.inr ⟨[], w, by simp, by simp⟩
      | some a =>
          rcases ih with ⟨u, rfl⟩ | ⟨u, w', rfl, hlen⟩
          · exact Or.inl ⟨a :: u, rfl⟩
          · exact Or.inr ⟨a :: u, w', by simp, by simpa using Nat.lt_succ_of_lt hlen⟩

/-- The map lifting of a letter-to-letter map. -/
lemma mapLift_letterMap (h : A → B) (w : List (Option A)) :
    mapLift (fun l : List A => l.map h) w = w.map (Option.map h) := by
  have h1 : mapLift (id : List A → List A) w = w := congrFun mapLift_id w
  calc mapLift (fun l : List A => l.map h) w
      = (mapLift (id : List A → List A) w).map (Option.map h) := by
        rw [mapLift, mapLift, map_intercalate]
        congr 1; simp [List.map_map, Function.comp_def]
    _ = w.map (Option.map h) := by rw [h1]

end Lax916827Proofs.Transducers
