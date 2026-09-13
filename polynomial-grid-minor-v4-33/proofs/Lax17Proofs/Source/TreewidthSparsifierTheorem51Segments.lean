import Lax17Proofs.Source.TreewidthSparsifierTheorem51RailPaths

namespace Lax17Proofs

universe u v w

/-!
# Heavy red-rail segments for Theorem 5.1

Step 2 of `treewidth-sparsifier.pdf`, Theorem 5.1 partitions every red rail
greedily.  A segment is heavy when it contains a prescribed number of branch
vertices from one physical round.  The elementary list lemma below is the
formal version of the paper's "minimal heavy prefix" construction.

The list elements are left abstract and `colour` records the physical round
responsible for an element.  This lets the same proof be applied to
`railBranchEvents`.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Theorem51

namespace HeavySegments


variable {α : Type u} {κ : Type v} [DecidableEq κ]

/-- Number of elements of colour `c` in a list. -/
def colourCount (colour : α → κ) (c : κ) (xs : List α) : ℕ :=
  (xs.map colour).count c

/-- A list is `B`-heavy if one colour occurs at least `B` times. -/
def Heavy (colour : α → κ) (B : ℕ) (xs : List α) : Prop :=
  ∃ c : κ, B ≤ colourCount colour c xs

@[simp] theorem colourCount_nil (colour : α → κ) (c : κ) :
    colourCount colour c [] = 0 := by
  simp [colourCount]

theorem colourCount_append (colour : α → κ) (c : κ)
    (xs ys : List α) :
    colourCount colour c (xs ++ ys) =
      colourCount colour c xs + colourCount colour c ys := by
  simp [colourCount]

theorem length_eq_sum_colourCount
    [Fintype κ] (colour : α → κ) (xs : List α) :
    xs.length = ∑ c : κ, colourCount colour c xs := by
  induction xs with
  | nil => simp [colourCount]
  | cons x xs ih =>
      simp only [List.length_cons, colourCount, List.map_cons,
        List.count_cons, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.sum_add_distrib]
      simp [ih, colourCount]

theorem colourCount_singleton_le_one (colour : α → κ)
    (c : κ) (x : α) :
    colourCount colour c [x] ≤ 1 := by
  simpa [colourCount] using
    (List.count_le_length (a := c) (l := [colour x]))

theorem not_heavy_iff (colour : α → κ) (B : ℕ) (xs : List α) :
    ¬ Heavy colour B xs ↔
      ∀ c : κ, colourCount colour c xs < B := by
  simp only [Heavy, not_exists, not_le]

theorem Heavy.append_left (colour : α → κ) {B : ℕ}
    {xs : List α} (hxs : Heavy colour B xs) (ys : List α) :
    Heavy colour B (xs ++ ys) := by
  rcases hxs with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [colourCount_append]
  omega

/-- Every member except possibly the last satisfies `p`. -/
def AllButLast (p : α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => p x ∧ AllButLast p (y :: xs)

@[simp] theorem allButLast_nil (p : α → Prop) :
    AllButLast p [] := by
  simp [AllButLast]

@[simp] theorem allButLast_singleton (p : α → Prop) (x : α) :
    AllButLast p [x] := by
  simp [AllButLast]

@[simp] theorem allButLast_cons_cons (p : α → Prop)
    (x y : α) (xs : List α) :
    AllButLast p (x :: y :: xs) ↔
      p x ∧ AllButLast p (y :: xs) := by
  rfl

/-- The shortest heavy prefix is nonempty, is no longer than the original
list, and contains at most `B` elements of every colour. -/
theorem exists_minimal_heavy_prefix
    (colour : α → κ) {B : ℕ} (hB : 0 < B)
    (xs : List α) (hxs : Heavy colour B xs) :
    ∃ n : ℕ,
      0 < n ∧
        n ≤ xs.length ∧
          Heavy colour B (xs.take n) ∧
            ∀ c : κ, colourCount colour c (xs.take n) ≤ B := by
  classical
  let p : ℕ → Prop := fun n => Heavy colour B (xs.take n)
  have hex : ∃ n, p n := by
    refine ⟨xs.length, ?_⟩
    simpa [p] using hxs
  let n := Nat.find hex
  have hnHeavy : p n := Nat.find_spec hex
  have hnLe : n ≤ xs.length := by
    exact Nat.find_min' hex (by simpa [p] using hxs)
  have hnPos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hempty : Heavy colour B [] := by
      simpa [p, hn0] using hnHeavy
    rcases hempty with ⟨c, hc⟩
    simp [colourCount] at hc
    omega
  refine ⟨n, hnPos, hnLe, hnHeavy, ?_⟩
  intro c
  let m := n - 1
  have hmLt : m < n := by
    dsimp [m]
    omega
  have hmNot : ¬p m := Nat.find_min hex hmLt
  have hmCount :
      colourCount colour c (xs.take m) < B :=
    (not_heavy_iff colour B (xs.take m)).mp (by
      simpa [p] using hmNot) c
  have hmIndex : m < xs.length := hmLt.trans_le hnLe
  have htake :
      xs.take n = xs.take m ++ [xs[m]] := by
    have hnEq : n = m + 1 := by
      dsimp [m]
      omega
    rw [hnEq, ← List.take_concat_get hmIndex,
      List.concat_eq_append]
  rw [htake, colourCount_append]
  have hlast :
      colourCount colour c [xs[m]] ≤ 1 :=
    colourCount_singleton_le_one colour c xs[m]
  omega

/-- Proof data for the raw greedy decomposition.  Every completed segment is
heavy; only the final remainder is allowed to be non-heavy. -/
structure RawDecomposition
    (colour : α → κ) (B : ℕ) (xs : List α) where
  segments : List (List α)
  flatten_segments : segments.flatten = xs
  segments_nonempty : ∀ s ∈ segments, s ≠ []
  bounded :
    ∀ s ∈ segments, ∀ c : κ, colourCount colour c s ≤ B
  allButLast_heavy :
    AllButLast (Heavy colour B) segments

/-- Greedy decomposition into minimal heavy prefixes and one possible final
non-heavy remainder. -/
theorem exists_rawDecomposition
    (colour : α → κ) {B : ℕ} (hB : 0 < B) :
    (xs : List α) → xs ≠ [] →
      Nonempty (RawDecomposition colour B xs)
  | xs, hxsNonempty => by
      by_cases hheavy : Heavy colour B xs
      · obtain ⟨n, hnPos, hnLe, hnHeavy, hnBound⟩ :=
          exists_minimal_heavy_prefix colour hB xs hheavy
        let head := xs.take n
        let tail := xs.drop n
        by_cases htail : tail = []
        · refine ⟨{
            segments := [head]
            flatten_segments := ?_
            segments_nonempty := ?_
            bounded := ?_
            allButLast_heavy := ?_
          }⟩
          · simpa [head, tail, htail] using List.take_append_drop n xs
          · intro s hs
            have hsHead : s = head := by simpa using hs
            subst s
            apply List.ne_nil_of_length_pos
            simp [head, hnLe, hnPos]
          · intro s hs c
            have hsHead : s = head := by simpa using hs
            subst s
            exact hnBound c
          · simp
        · have htailLen : tail.length < xs.length := by
            dsimp [tail]
            rw [List.length_drop]
            omega
          obtain ⟨D⟩ :=
            exists_rawDecomposition colour hB tail htail
          refine ⟨{
            segments := head :: D.segments
            flatten_segments := ?_
            segments_nonempty := ?_
            bounded := ?_
            allButLast_heavy := ?_
          }⟩
          · simp only [List.flatten_cons, D.flatten_segments, head, tail]
            exact List.take_append_drop n xs
          · intro s hs
            rcases List.mem_cons.mp hs with rfl | hs
            · apply List.ne_nil_of_length_pos
              simp [head, hnLe, hnPos]
            · exact D.segments_nonempty s hs
          · intro s hs c
            rcases List.mem_cons.mp hs with rfl | hs
            · exact hnBound c
            · exact D.bounded s hs c
          · have hDne : D.segments ≠ [] := by
              intro hnil
              have : tail = [] := by
                rw [← D.flatten_segments, hnil]
                rfl
              exact htail this
            cases hs : D.segments with
            | nil => exact False.elim (hDne hs)
            | cons d ds =>
                cases ds with
                | nil =>
                    simp [AllButLast, head, hnHeavy]
                | cons e es =>
                    simpa [AllButLast, head, hnHeavy, hs] using
                      D.allButLast_heavy
      · refine ⟨{
          segments := [xs]
          flatten_segments := by simp
          segments_nonempty := by
            intro s hs
            have hsx : s = xs := by simpa using hs
            simpa [hsx] using hxsNonempty
          bounded := ?_
          allButLast_heavy := by simp
        }⟩
        · intro s hs c
          have hsx : s = xs := by simpa using hs
          subst s
          exact Nat.le_of_lt ((not_heavy_iff colour B xs).mp hheavy c)
termination_by xs _ => xs.length
decreasing_by
  simpa [tail] using htailLen

/-- Merge the possible final non-heavy remainder into its predecessor. -/
def mergeFinal : List (List α) → List (List α)
  | [] => []
  | [x] => [x]
  | [x, y] => [x ++ y]
  | x :: y :: z :: xs => x :: mergeFinal (y :: z :: xs)

@[simp] theorem mergeFinal_nil :
    mergeFinal ([] : List (List α)) = [] := rfl

@[simp] theorem mergeFinal_singleton (x : List α) :
    mergeFinal [x] = [x] := rfl

@[simp] theorem mergeFinal_pair (x y : List α) :
    mergeFinal [x, y] = [x ++ y] := rfl

@[simp] theorem mergeFinal_cons_three (x y z : List α)
    (xs : List (List α)) :
    mergeFinal (x :: y :: z :: xs) =
      x :: mergeFinal (y :: z :: xs) := rfl

theorem mergeFinal_flatten :
    ∀ xss : List (List α), (mergeFinal xss).flatten = xss.flatten
  | [] => by simp
  | [x] => by simp
  | [x, y] => by simp
  | x :: y :: z :: xs => by
      simp only [mergeFinal_cons_three, List.flatten_cons]
      rw [mergeFinal_flatten (y :: z :: xs)]
      simp [List.append_assoc]

theorem mergeFinal_nonempty_members
    : ∀ xss : List (List α),
      (∀ s ∈ xss, s ≠ []) →
        ∀ s ∈ mergeFinal xss, s ≠ []
  | [], _ => by simp
  | [x], hne => by simpa using hne
  | [x, y], hne => by
      intro s hs
      have hsxy : s = x ++ y := by simpa using hs
      subst s
      intro hnil
      have hxnil : x = [] := (List.append_eq_nil_iff.mp hnil).1
      exact hne x (by simp) hxnil
  | x :: y :: z :: xs, hne => by
      intro s hs
      rcases List.mem_cons.mp hs with hsEq | hs
      · subst s
        exact hne _ (by simp)
      · exact mergeFinal_nonempty_members (y :: z :: xs)
          (fun t ht => hne t (List.mem_cons_of_mem _ ht)) s hs
termination_by xss _ => xss.length

theorem mergeFinal_bounded
    (colour : α → κ) {B : ℕ} :
    ∀ xss : List (List α),
      (∀ s ∈ xss, ∀ c : κ, colourCount colour c s ≤ B) →
        ∀ s ∈ mergeFinal xss, ∀ c : κ,
          colourCount colour c s ≤ 2 * B
  | [], _ => by simp
  | [x], hbound => by
      intro s hs c
      have hsx : s = x := by simpa using hs
      subst s
      exact (hbound x (by simp) c).trans (by omega)
  | [x, y], hbound => by
      intro s hs c
      have hsxy : s = x ++ y := by simpa using hs
      subst s
      rw [colourCount_append]
      have hx := hbound x (by simp) c
      have hy := hbound y (by simp) c
      omega
  | x :: y :: z :: xs, hbound => by
      intro s hs c
      rcases List.mem_cons.mp hs with hsEq | hs
      · subst s
        exact (hbound _ (by simp) c).trans (by omega)
      · exact mergeFinal_bounded colour (y :: z :: xs)
          (fun t ht d => hbound t (List.mem_cons_of_mem _ ht) d) s hs c
termination_by xss _ => xss.length

theorem mergeFinal_all_heavy
    (colour : α → κ) {B : ℕ} :
    ∀ xss : List (List α),
      1 < xss.length →
        AllButLast (Heavy colour B) xss →
          ∀ s ∈ mergeFinal xss, Heavy colour B s
  | [], hmany, _ => by simp at hmany
  | [x], hmany, _ => by simp at hmany
  | [x, y], _hmany, hheavy => by
      intro s hs
      have hsxy : s = x ++ y := by simpa using hs
      subst s
      exact hheavy.1.append_left colour y
  | x :: y :: z :: xs, _hmany, hheavy => by
      intro s hs
      rcases List.mem_cons.mp hs with hsEq | hs
      · subst s
        exact hheavy.1
      · exact mergeFinal_all_heavy colour (y :: z :: xs)
          (by simp) hheavy.2 s hs
termination_by xss _ _ => xss.length

theorem one_lt_length_of_one_lt_mergeFinal_length
    (xss : List (List α))
    (h : 1 < (mergeFinal xss).length) :
    1 < xss.length := by
  induction xss using List.rec with
  | nil => simp at h
  | cons x xs =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
          cases ys with
          | nil => simp at h
          | cons z zs => simp

/-- The completed source decomposition.  It always has at least one segment;
if it has more than one, every segment is heavy.  Each colour occurs at most
`2 * B` times in a segment because only the final remainder is merged. -/
structure Decomposition
    (colour : α → κ) (B : ℕ) (xs : List α) where
  segments : List (List α)
  segments_nonempty : segments ≠ []
  members_nonempty_of_input :
    xs ≠ [] → ∀ s ∈ segments, s ≠ []
  flatten_segments : segments.flatten = xs
  bounded :
    ∀ s ∈ segments, ∀ c : κ,
      colourCount colour c s ≤ 2 * B
  all_heavy_if_split :
    1 < segments.length →
      ∀ s ∈ segments, Heavy colour B s

/-- Every list admits the heavy-segment decomposition used in source Step 2. -/
theorem exists_decomposition
    (colour : α → κ) {B : ℕ} (hB : 0 < B)
    (xs : List α) :
    Nonempty (Decomposition colour B xs) := by
  by_cases hxs : xs = []
  · subst xs
    refine ⟨{
      segments := [[]]
      segments_nonempty := by simp
      members_nonempty_of_input := by simp
      flatten_segments := by simp
      bounded := by simp [colourCount]
      all_heavy_if_split := by simp
    }⟩
  · obtain ⟨D⟩ := exists_rawDecomposition colour hB xs hxs
    refine ⟨{
      segments := mergeFinal D.segments
      segments_nonempty := ?_
      members_nonempty_of_input := ?_
      flatten_segments := ?_
      bounded := ?_
      all_heavy_if_split := ?_
    }⟩
    · intro hnil
      have hflat : xs = [] := by
        rw [← D.flatten_segments, ← mergeFinal_flatten D.segments,
          hnil]
        rfl
      exact hxs hflat
    · intro _hxs
      exact mergeFinal_nonempty_members D.segments D.segments_nonempty
    · exact (mergeFinal_flatten D.segments).trans D.flatten_segments
    · exact mergeFinal_bounded colour D.segments D.bounded
    · intro hmany
      exact mergeFinal_all_heavy colour D.segments
        (one_lt_length_of_one_lt_mergeFinal_length D.segments hmany)
        D.allButLast_heavy

end HeavySegments

open HeavySegments


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V} {ell h count : ℕ}
variable {P : StrongPathOfSetsSystem G ell h}

namespace BuildState.ExpanderBlocks

/-- The source Step-2 segmentation of the branch events on one red rail. -/
noncomputable def railBranchSegmentation
    (E : ExpanderBlocks P count) (x : Fin h)
    (B : ℕ) (hB : 0 < B) :
    Decomposition Prod.fst B (E.railBranchEvents x) :=
  Classical.choice
    (exists_decomposition Prod.fst hB (E.railBranchEvents x))

@[simp] theorem railBranchSegmentation_flatten
    (E : ExpanderBlocks P count) (x : Fin h)
    (B : ℕ) (hB : 0 < B) :
    (E.railBranchSegmentation x B hB).segments.flatten =
      E.railBranchEvents x :=
  (E.railBranchSegmentation x B hB).flatten_segments

theorem railBranchSegment_round_count_le
    (E : ExpanderBlocks P count) (x : Fin h)
    (B : ℕ) (hB : 0 < B)
    (s : List (Fin E.finalState.records.length × V))
    (hs : s ∈ (E.railBranchSegmentation x B hB).segments)
    (j : Fin E.finalState.records.length) :
    colourCount Prod.fst j s ≤ 2 * B :=
  (E.railBranchSegmentation x B hB).bounded s hs j

/-- Consequently a rail segment contains at most `2 * B` branch events per
record and at most `2 * B * records` branch events in total. -/
theorem railBranchSegment_length_le
    (E : ExpanderBlocks P count) (x : Fin h)
    (B : ℕ) (hB : 0 < B)
    (s : List (Fin E.finalState.records.length × V))
    (hs : s ∈ (E.railBranchSegmentation x B hB).segments) :
    s.length ≤ 2 * B * E.finalState.records.length := by
  rw [length_eq_sum_colourCount Prod.fst s]
  calc
    ∑ j : Fin E.finalState.records.length,
        colourCount Prod.fst j s ≤
        ∑ _j : Fin E.finalState.records.length, 2 * B :=
      Finset.sum_le_sum fun j _ =>
        E.railBranchSegment_round_count_le x B hB s hs j
    _ = 2 * B * E.finalState.records.length := by
      simp [Nat.mul_comm]

theorem railBranchSegment_heavy_of_split
    (E : ExpanderBlocks P count) (x : Fin h)
    (B : ℕ) (hB : 0 < B)
    (hmany :
      1 < (E.railBranchSegmentation x B hB).segments.length)
    (s : List (Fin E.finalState.records.length × V))
    (hs : s ∈ (E.railBranchSegmentation x B hB).segments) :
    ∃ j : Fin E.finalState.records.length,
      B ≤ colourCount Prod.fst j s :=
  (E.railBranchSegmentation x B hB).all_heavy_if_split
    hmany s hs

end BuildState.ExpanderBlocks

end Theorem51
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
