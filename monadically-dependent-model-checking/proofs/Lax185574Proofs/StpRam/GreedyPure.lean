import Lax185574Proofs.StpRam.Spec
import Lax185574Proofs.StpRam.BallCmd

/-!
The greedy scan of lem:compute-stp on numbers, with and without the cap
at `k + q`.

The program scans the vertices `0, …, n − 1` and stops adding vertices
once it has `cap` of them. `greedyN` is this capped scan, `greedyU` the
uncapped one. The capped scan is the prefix of length `cap` of the
uncapped one (`foldl_cap`), and the uncapped scan, with the
test of the distance matrix `DT`, is the greedy scan `greedyW` of
`Lax185574Proofs.StpRam.Spec` read on numbers (`map_greedyW_D`).
-/

namespace Lax185574Proofs.StpRam

open Lax185574Proofs.TreeAlgo

open Classical in
/-- One step of the capped scan. -/
noncomputable def gstepN (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap : ℕ) (S : List ℕ) (v : ℕ) :
    List ℕ :=
  if S.length < cap ∧ P v ∧ ∀ s ∈ S, ¬ Bl s v then S ++ [v] else S

open Classical in
/-- One step of the uncapped scan. -/
noncomputable def gstepU (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (S : List ℕ) (v : ℕ) : List ℕ :=
  if P v ∧ ∀ s ∈ S, ¬ Bl s v then S ++ [v] else S

/-- The capped scan of the first `j` vertices. -/
noncomputable def greedyN (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap j : ℕ) : List ℕ :=
  (List.range j).foldl (gstepN P Bl cap) []

theorem foldl_gstepU_prefix (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) :
    ∀ (l S : List ℕ), ∃ x, l.foldl (gstepU P Bl) S = S ++ x
  | [], S => ⟨[], by simp⟩
  | v :: l, S => by
    obtain ⟨x, hx⟩ := foldl_gstepU_prefix P Bl l (gstepU P Bl S v)
    rw [List.foldl_cons, hx]
    unfold gstepU
    split_ifs
    · exact ⟨[v] ++ x, by simp⟩
    · exact ⟨x, rfl⟩

theorem foldl_gstepN_full (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap : ℕ) :
    ∀ (l S : List ℕ), S.length = cap → l.foldl (gstepN P Bl cap) S = S
  | [], S, _ => rfl
  | v :: l, S, h => by
    rw [List.foldl_cons]
    have : gstepN P Bl cap S v = S := by unfold gstepN; rw [if_neg (by omega)]
    rw [this, foldl_gstepN_full P Bl cap l S h]

/-- **The cap.** -/
theorem foldl_cap (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap : ℕ) :
    ∀ (l S : List ℕ), S.length ≤ cap →
      l.foldl (gstepN P Bl cap) S = (l.foldl (gstepU P Bl) S).take cap
  | [], S, h => by simp [List.take_of_length_le h]
  | v :: l, S, h => by
    rcases Nat.lt_or_ge S.length cap with hlt | hge
    · have he : gstepN P Bl cap S v = gstepU P Bl S v := by
        unfold gstepN gstepU
        by_cases hc : P v ∧ ∀ s ∈ S, ¬ Bl s v
        · rw [if_pos ⟨hlt, hc⟩, if_pos hc]
        · rw [if_neg (fun h => hc h.2), if_neg hc]
      rw [List.foldl_cons, List.foldl_cons, he]
      refine foldl_cap P Bl cap l _ ?_
      unfold gstepU
      split_ifs
      · rw [List.length_append, List.length_singleton]; omega
      · omega
    · have hS : S.length = cap := by omega
      rw [foldl_gstepN_full P Bl cap _ S hS]
      obtain ⟨x, hx⟩ := foldl_gstepU_prefix P Bl (v :: l) S
      rw [hx, ← hS, List.take_left]

theorem length_greedyN (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap j : ℕ) :
    (greedyN P Bl cap j).length = min ((List.range j).foldl (gstepU P Bl) []).length cap := by
  unfold greedyN
  rw [foldl_cap P Bl cap _ [] (Nat.zero_le _), List.length_take, Nat.min_comm]

theorem greedyN_succ (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap j : ℕ) :
    greedyN P Bl cap (j + 1) = gstepN P Bl cap (greedyN P Bl cap j) j := by
  simp [greedyN, List.range_succ, List.foldl_append]

theorem length_greedyN_le (P : ℕ → Prop) (Bl : ℕ → ℕ → Prop) (cap j : ℕ) :
    (greedyN P Bl cap j).length ≤ cap := by
  rw [length_greedyN]; omega

/-! ### The scan on vertices and on numbers -/

theorem foldl_map_val {n : ℕ} {f : List (Fin n) → Fin n → List (Fin n)} {g : List ℕ → ℕ → List ℕ}
    (h : ∀ S v, (f S v).map Fin.val = g (S.map Fin.val) v.val) :
    ∀ (l : List (Fin n)) (S : List (Fin n)),
      (l.foldl f S).map Fin.val = (l.map Fin.val).foldl g (S.map Fin.val)
  | [], S => rfl
  | v :: l, S => by rw [List.foldl_cons, foldl_map_val h l, h]; rfl

/-! ### The scan with the distance matrix -/

/-- The test of the distance matrix, with entries `g (u · n + v)` in the
code of `Lax185574Proofs.DistMatrix.dcode`: `u` and `v` are within
distance `r`. -/
def DT (g : ℕ → ℕ) (n u v r : ℕ) : Prop := 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1

theorem map_greedyW_D {n : ℕ} {adj : Fin n → List (Fin n)} {g : ℕ → ℕ}
    (hD : ∀ (s v : Fin n) (r : ℕ), DT g n s v r ↔ v ∈ ballFrom adj s r)
    (A : List (List ℕ)) (i r : ℕ) (u : List ℕ) :
    (greedyW adj A i r u).map Fin.val =
      (List.range n).foldl (gstepU (fun v => lw A n i v = u) (fun s v => DT g n s v r)) [] := by
  unfold greedyW
  have hfin : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) (fun i h1 h2 => by simp)
  have hstep : ∀ (S : List (Fin n)) (v : Fin n),
      (if lw A n i v.val = u ∧ ∀ s ∈ S, v ∉ ballFrom adj s r then S ++ [v] else S).map Fin.val =
        gstepU (fun v => lw A n i v = u) (fun s v => DT g n s v r) (S.map Fin.val) v.val := by
    intro S v
    unfold gstepU
    have : (∀ s ∈ S, v ∉ ballFrom adj s r) ↔ ∀ s ∈ S.map Fin.val, ¬ DT g n s v r := by
      simp only [List.mem_map]
      constructor
      · rintro h _ ⟨s, hs, rfl⟩
        exact (hD s v r).not.mpr (h s hs)
      · intro h s hs
        exact (hD s v r).not.mp (h s ⟨s, hs, rfl⟩)
    by_cases hc : lw A n i v.val = u ∧ ∀ s ∈ S, v ∉ ballFrom adj s r
    · rw [if_pos hc, if_pos ⟨hc.1, this.mp hc.2⟩]; simp
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, this.mpr h.2⟩)]
  rw [foldl_map_val hstep, hfin]
  rfl

/-- **The capped scan with the distance matrix computes the value.** -/
theorem length_greedyN_eq_D {n : ℕ} {adj : Fin n → List (Fin n)} {g : ℕ → ℕ}
    (hD : ∀ (s v : Fin n) (r : ℕ), DT g n s v r ↔ v ∈ ballFrom adj s r)
    (A : List (List ℕ)) (i r cap : ℕ) (u : List ℕ) :
    (greedyN (fun v => lw A n i v = u) (fun s v => DT g n s v r) cap n).length =
      min (greedyW adj A i r u).length cap := by
  rw [length_greedyN, ← map_greedyW_D hD, List.length_map]

end Lax185574Proofs.StpRam
