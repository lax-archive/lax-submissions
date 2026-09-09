import Lax214022Proofs.HardCographs
import Lax214022Proofs.ListCrossings

/-!
# The ternary order obstruction

Place the universal root in an arbitrary order. At most two of the three
branches occur immediately next to it, so one branch is separated from the
root by a non-neighbor on every nonempty side. Restrict the order to that
branch and apply induction. The root then contributes one additional change
to the selected neighborhood row.
-/

namespace Lax214022Proofs.LowerObstruction

open Lax214022Proofs.HardCographs
open Lax214022Proofs.ListCrossings

noncomputable section

local instance graphAdjDecidable (k : ℕ) : DecidableRel (graph k).Adj :=
  Classical.decRel _

def defaultVertex : (k : ℕ) → Vertex k
  | 0 => ⟨0, by omega⟩
  | _ + 1 => none

def branchOf {k : ℕ} : Vertex (k + 1) → Option (Fin 3)
  | none => none
  | some (i, _) => some i

def branchList {k : ℕ} (i : Fin 3) (L : List (Vertex (k + 1))) :
    List (Vertex k) :=
  L.filterMap fun x =>
    match x with
    | none => none
    | some (j, v) => if j = i then some v else none

@[simp] theorem branchList_append {k : ℕ} (i : Fin 3)
    (A B : List (Vertex (k + 1))) :
    branchList i (A ++ B) = branchList i A ++ branchList i B := by
  simp [branchList]

@[simp] theorem mem_branchList_iff {k : ℕ} (i : Fin 3)
    (L : List (Vertex (k + 1))) (v : Vertex k) :
    v ∈ branchList i L ↔ some (i, v) ∈ L := by
  simp only [branchList, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hfx⟩
    cases x with
    | none => simp at hfx
    | some x =>
        rcases x with ⟨j, w⟩
        by_cases hji : j = i
        · subst j
          simp at hfx
          subst w
          exact hx
        · simp [hji] at hfx
  · intro hv
    exact ⟨some (i, v), hv, by simp⟩

theorem nodup_branchList {k : ℕ} (i : Fin 3)
    {L : List (Vertex (k + 1))} (hL : L.Nodup) :
    (branchList i L).Nodup := by
  apply hL.filterMap
  intro a a' b hb hb'
  cases a with
  | none => simp at hb
  | some a =>
      rcases a with ⟨j, v⟩
      cases a' with
      | none => simp at hb'
      | some a' =>
          rcases a' with ⟨j', v'⟩
          simp only [Option.mem_def] at hb hb'
          split at hb <;> split at hb' <;> simp_all

theorem exists_branch_avoiding (a b : Option (Fin 3)) :
    ∃ i : Fin 3, a ≠ some i ∧ b ≠ some i := by
  fin_cases a <;> fin_cases b <;> decide

private theorem internal_row_sublist {k : ℕ} (i : Fin 3) (v : Vertex k) :
    ∀ L : List (Vertex (k + 1)),
      (branchList i L).map (fun x => decide ((graph k).Adj v x))
        |>.Sublist
      (L.map fun x => decide ((graph (k + 1)).Adj (some (i, v)) x)) := by
  intro L
  induction L with
  | nil => exact List.Sublist.slnil
  | cons x L ih =>
      cases x with
      | none =>
          simpa [branchList] using ih.cons true
      | some x =>
          rcases x with ⟨j, w⟩
          by_cases hji : j = i
          · subst j
            simpa [branchList] using ih.cons_cons
          · simpa [branchList, hji] using ih.cons
              (decide ((graph (k + 1)).Adj (some (i, v)) (some (j, w))))

private theorem row_ends_false_or_nil {k : ℕ} (i : Fin 3) (v : Vertex k)
    (A : List (Vertex (k + 1))) (hroot : none ∉ A)
    (havoid : A.getLast?.bind branchOf ≠ some i) :
    A.map (fun x => decide ((graph (k + 1)).Adj (some (i, v)) x)) = [] ∨
      ∃ A', A.map (fun x =>
        decide ((graph (k + 1)).Adj (some (i, v)) x)) = A' ++ [false] := by
  cases A with
  | nil => exact Or.inl rfl
  | cons x A =>
      right
      let y := (x :: A).getLast (by simp)
      let P := (x :: A).dropLast
      have hy : P ++ [y] = x :: A :=
        List.dropLast_append_getLast (by simp)
      have hyroot : y ≠ none := by
        intro hynone
        have hymem : y ∈ x :: A := by
          rw [← hy]
          exact List.mem_append_right _ (List.mem_singleton_self y)
        exact hroot (hynone ▸ hymem)
      cases hycase : y with
      | none => exact (hyroot hycase).elim
      | some yw =>
          rcases yw with ⟨j, w⟩
          have hji : j ≠ i := by
            intro h
            subst j
            apply havoid
            rw [← hy]
            simp [hycase, branchOf]
          have hij : i ≠ j := Ne.symm hji
          refine ⟨P.map (fun z =>
            decide ((graph (k + 1)).Adj (some (i, v)) z)), ?_⟩
          rw [← hy, List.map_append]
          simp [hycase, hij]

private theorem row_starts_false_or_nil {k : ℕ} (i : Fin 3) (v : Vertex k)
    (B : List (Vertex (k + 1))) (hroot : none ∉ B)
    (havoid : B.head?.bind branchOf ≠ some i) :
    B.map (fun x => decide ((graph (k + 1)).Adj (some (i, v)) x)) = [] ∨
      ∃ B', B.map (fun x =>
        decide ((graph (k + 1)).Adj (some (i, v)) x)) = false :: B' := by
  cases B with
  | nil => exact Or.inl rfl
  | cons y B =>
      right
      have hyroot : y ≠ none := by
        intro hy'
        subst y
        exact hroot (List.mem_cons_self)
      obtain ⟨j, w, rfl⟩ : ∃ j w, y = some (j, w) := by
        cases y with
        | none => exact (hyroot rfl).elim
        | some y => exact ⟨y.1, y.2, rfl⟩
      have hji : j ≠ i := by
        intro h
        subst j
        apply havoid
        simp [branchOf]
      have hij : i ≠ j := Ne.symm hji
      refine ⟨B.map (fun z =>
        decide ((graph (k + 1)).Adj (some (i, v)) z)), ?_⟩
      simp [hij]

/-- Every complete list layout of the height-k hard graph has a neighborhood
row with at least k changes. -/
theorem exists_row_with_k_changes (k : ℕ) (L : List (Vertex k))
    (hL : L.Nodup) (hall : ∀ v : Vertex k, v ∈ L) :
    ∃ v : Vertex k, k ≤ crossingCountInList ((graph k).Adj v) L := by
  induction k with
  | zero =>
      exact ⟨⟨0, by omega⟩, Nat.zero_le _⟩
  | succ k ih =>
      have hroot : (none : Vertex (k + 1)) ∈ L := hall none
      obtain ⟨A, B, hdecomp⟩ := List.mem_iff_append.mp hroot
      subst L
      have hparts := List.nodup_append.mp hL
      have htail := List.nodup_cons.mp hparts.2.1
      have hrootA : (none : Vertex (k + 1)) ∉ A := by
        exact fun h => (hparts.2.2 none h none List.mem_cons_self) rfl
      have hrootB : (none : Vertex (k + 1)) ∉ B := htail.1
      obtain ⟨i, hprev, hnext⟩ :=
        exists_branch_avoiding (A.getLast?.bind branchOf)
          (B.head?.bind branchOf)
      have hbranchNodup : (branchList i (A ++ B)).Nodup := by
        apply nodup_branchList
        apply List.Nodup.append hparts.1 htail.2
        intro x hxA hxB
        exact (hparts.2.2 x hxA x (List.mem_cons_of_mem none hxB)) rfl
      have hbranchAll : ∀ v : Vertex k, v ∈ branchList i (A ++ B) := by
        intro v
        rw [mem_branchList_iff]
        have hvfull := hall (some (i, v))
        rcases List.mem_append.mp hvfull with hvA | hvrootB
        · exact List.mem_append_left B hvA
        · rcases List.mem_cons.mp hvrootB with heq | hvB
          · cases heq
          · exact List.mem_append_right A hvB
      obtain ⟨v, hv⟩ := ih (branchList i (A ++ B)) hbranchNodup hbranchAll
      let C := (branchList i A).map (fun x => decide ((graph k).Adj v x))
      let D := (branchList i B).map (fun x => decide ((graph k).Adj v x))
      let RA := A.map (fun x =>
        decide ((graph (k + 1)).Adj (some (i, v)) x))
      let RB := B.map (fun x =>
        decide ((graph (k + 1)).Adj (some (i, v)) x))
      have hCD : k ≤ changes (C ++ D) := by
        unfold crossingCountInList at hv
        have hbl := branchList_append i A B
        have hmap := congrArg
          (List.map fun x => decide ((graph k).Adj v x)) hbl
        rw [List.map_append] at hmap
        change _ = C ++ D at hmap
        exact hv.trans_eq (congrArg changes hmap)
      have hCRA : C.Sublist RA := internal_row_sublist i v A
      have hDRB : D.Sublist RB := internal_row_sublist i v B
      have hRA := row_ends_false_or_nil i v A hrootA hprev
      have hRB := row_starts_false_or_nil i v B hrootB hnext
      have hne : C ++ D ≠ [] := by
        intro hnil
        have : branchList i (A ++ B) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro x hx
          have hxAorB : x ∈ branchList i A ∨ x ∈ branchList i B := by
            have hxfull := (mem_branchList_iff i (A ++ B) x).mp hx
            rcases List.mem_append.mp hxfull with hxA | hxB
            · exact Or.inl ((mem_branchList_iff i A x).mpr hxA)
            · exact Or.inr ((mem_branchList_iff i B x).mpr hxB)
          have hpartsNil := List.append_eq_nil_iff.mp hnil
          rcases hxAorB with hxA | hxB
          · have : C ≠ [] := by simp [C, List.ne_nil_of_mem hxA]
            exact this hpartsNil.1
          · have : D ≠ [] := by simp [D, List.ne_nil_of_mem hxB]
            exact this hpartsNil.2
        have hv0 := hbranchAll (defaultVertex k)
        simp [this] at hv0
      refine ⟨some (i, v), ?_⟩
      unfold crossingCountInList
      have hmapfull :
          (A ++ none :: B).map (fun x =>
            decide ((graph (k + 1)).Adj (some (i, v)) x)) =
            RA ++ true :: RB := by
        calc
          _ = A.map (fun x =>
                decide ((graph (k + 1)).Adj (some (i, v)) x)) ++
              (none :: B).map (fun x =>
                decide ((graph (k + 1)).Adj (some (i, v)) x)) :=
            List.map_append
          _ = RA ++ decide ((graph (k + 1)).Adj (some (i, v)) none) :: RB := rfl
          _ = RA ++ true :: RB := by
            congr 2
            simp
      rw [hmapfull]
      change k + 1 ≤ changes (RA ++ true :: RB)
      have hgain := changes_isolated_true_gain hCRA hDRB hRA hRB hne
      omega

end

end Lax214022Proofs.LowerObstruction
