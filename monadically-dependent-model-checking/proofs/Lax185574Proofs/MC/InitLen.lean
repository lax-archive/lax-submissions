import Lax185574Proofs.MC.InitWord
import Lax185574Proofs.Words.Read

/-!
The word of an initial tree, level by level, and its length.

`initWord k q ℓ c` is built from the bottom: the node of depth `d` has
rank `(K - d, d)` and arity `ℓ + q - d` with `K = k + q`, so
`ρ⁻ = 9 ^ ((K + 1) d)` and `ρ⁺ = 9 ^ (K (d + 1))` depend on `d` only.
`atomsOut` is the list of frames of the atoms in the order of
`atomWords`, `levelWord` adds the extensions on top of the word of the
level below, and `lvlLen` is the length, which does not depend on the
color.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The frames of the atoms of arity `ℓ` with the bounds `rm` and `rp`
and the color `c`. -/
def atomsOut (ℓ rm rp c : ℕ) : List ℕ :=
  ((List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j => [3, 0, i, j]) ++
  ((List.range ℓ).flatMap fun i => [3, 3, c, i]) ++
  ((List.range (rm + 1)).flatMap fun r =>
    (List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j => [4, 4, r, i, j]) ++
  ((List.range rp).flatMap fun r => (List.range ℓ).flatMap fun i => [4, 5, r + 1, c, i])

/-- The number of atoms. -/
def atomsCnt (ℓ rm rp : ℕ) : ℕ := ℓ * ℓ + ℓ + (rm + 1) * (ℓ * ℓ) + rp * ℓ

theorem frames_eq (ws : List (List ℕ)) : frames ws = ws.flatMap fun u => u.length :: u := by
  simp [frames, List.flatMap]

theorem toWord_atomWords (k q ℓ c : ℕ) :
    toWord (atomWords k q ℓ c) =
      atomsCnt ℓ (rhoMinus k q) (rhoPlus k q) :: atomsOut ℓ (rhoMinus k q) (rhoPlus k q) c := by
  rw [toWord_words, frames_eq]
  congr 1
  · simp [atomWords, atomsCnt, List.length_flatMap, List.sum_replicate]; ring
  · simp [atomWords, atomsOut, List.flatMap_append, List.flatMap_assoc, List.flatMap_map]

theorem length_atomsOut (ℓ rm rp c : ℕ) :
    (atomsOut ℓ rm rp c).length = 4 * (ℓ * ℓ) + 4 * ℓ + 5 * ((rm + 1) * (ℓ * ℓ)) + 5 * (rp * ℓ) := by
  simp [atomsOut, List.length_flatMap, List.sum_replicate]; ring

/-- The extensions on top of the word `W` of the child. -/
def extsOut (ℓ : ℕ) (W : List ℕ) : List ℕ :=
  (List.range ℓ).flatMap fun i => (W.length + 1) :: i :: W

/-- The word of a node of depth `d + 1` from the word `W` of its child. -/
def levelWord (ℓ rm rp c : ℕ) (W : List ℕ) : List ℕ :=
  atomsCnt ℓ rm rp :: atomsOut ℓ rm rp c ++ ℓ :: extsOut ℓ W

theorem initWord_succ (k q ℓ c : ℕ) :
    initWord k (q + 1) ℓ c = levelWord ℓ (rhoMinus k (q + 1)) (rhoPlus k (q + 1)) c
      (initWord (k + 1) q (ℓ + 1) c) := by
  rw [initWord, toWord_atomWords, toWord_words, frames_eq]
  simp [levelWord, extsOut, List.flatMap_map]

theorem initWord_zero (k ℓ c : ℕ) :
    initWord k 0 ℓ c = atomsCnt ℓ (rhoMinus k 0) (rhoPlus k 0) ::
      atomsOut ℓ (rhoMinus k 0) (rhoPlus k 0) c := by
  rw [initWord, toWord_atomWords]

/-- The bounds of the node of depth `d` when the top has `k + q = K`. -/
def rmD (K d : ℕ) : ℕ := 9 ^ ((K + 1) * d)
def rpD (K d : ℕ) : ℕ := 9 ^ (K * (d + 1))

theorem rhoMinus_eq {K d : ℕ} (h : d ≤ K) : rhoMinus (K - d) d = rmD K d := by
  simp only [rhoMinus, rmD]; congr 2; omega

theorem rhoPlus_eq {K d : ℕ} (h : d ≤ K) : rhoPlus (K - d) d = rpD K d := by
  simp only [rhoPlus, rpD]; congr 2; omega

/-- The length of an atom word with its count. -/
def alen (ℓ rm rp : ℕ) : ℕ :=
  1 + 4 * (ℓ * ℓ) + 4 * ℓ + 5 * ((rm + 1) * (ℓ * ℓ)) + 5 * (rp * ℓ)

/-- The word of the node of depth `d`, with top rank `(K - q, q)` and
top arity `ℓ`. -/
def lvlWord (K q ℓ c : ℕ) : ℕ → List ℕ
  | 0 => atomsCnt (ℓ + q) (rmD K 0) (rpD K 0) :: atomsOut (ℓ + q) (rmD K 0) (rpD K 0) c
  | d + 1 => levelWord (ℓ + q - (d + 1)) (rmD K (d + 1)) (rpD K (d + 1)) c (lvlWord K q ℓ c d)

/-- Its length. -/
def lvlLen (K q ℓ : ℕ) : ℕ → ℕ
  | 0 => alen (ℓ + q) (rmD K 0) (rpD K 0)
  | d + 1 => alen (ℓ + q - (d + 1)) (rmD K (d + 1)) (rpD K (d + 1)) + 1 +
      (ℓ + q - (d + 1)) * (lvlLen K q ℓ d + 2)

theorem length_lvlWord (K q ℓ c : ℕ) : ∀ d, (lvlWord K q ℓ c d).length = lvlLen K q ℓ d
  | 0 => by simp [lvlWord, lvlLen, alen, length_atomsOut]; ring
  | d + 1 => by
      simp only [lvlWord, lvlLen, levelWord, extsOut, List.length_cons, List.length_append,
        length_atomsOut, List.length_flatMap, List.length_range, length_lvlWord K q ℓ c d,
        List.map_const', List.sum_replicate, alen]
      ring

/-- **The levels give the initial tree.** -/
theorem lvlWord_eq (k q ℓ c : ℕ) :
    ∀ d, d ≤ q → lvlWord (k + q) q ℓ c d = initWord (k + q - d) d (ℓ + q - d) c
  | 0, _ => by
      rw [lvlWord, initWord_zero, rhoMinus_eq (by omega), rhoPlus_eq (by omega)]
      simp
  | d + 1, h => by
      rw [lvlWord, lvlWord_eq k q ℓ c d (by omega)]
      have e1 : k + q - d = k + q - (d + 1) + 1 := by omega
      have e2 : ℓ + q - d = ℓ + q - (d + 1) + 1 := by omega
      rw [e1, e2, initWord_succ, rhoMinus_eq (by omega), rhoPlus_eq (by omega)]

theorem lvlWord_top (k q ℓ c : ℕ) : lvlWord (k + q) q ℓ c q = initWord k q ℓ c := by
  rw [lvlWord_eq k q ℓ c q le_rfl]; simp

end Lax185574Proofs.MC
