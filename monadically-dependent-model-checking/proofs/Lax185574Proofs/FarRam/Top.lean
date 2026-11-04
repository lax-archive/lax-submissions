import Lax185574Proofs.FarRam.Bnd
import Lax185574.ToFarTree
import Lax185574.Restriction


namespace Lax185574Proofs.FarRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing Lax185574.TypeTrees
open Lax185574.PartialGraphs Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574Proofs.TreeAlgo Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax3.DistFO (rhoMinus)

variable {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n)

theorem wl_zero (S : List (List ℕ)) : wl k (node G k (q + 1) u) S 0 = S := by simp [wl]

/-- The input of round `j` of the script. -/
theorem round_in (S : List (List ℕ)) (x : List ℕ)
    (hx : x = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u) ++ toWord S) (B : ℕ)
    (hB : 1764 * ySz x ^ 4 ≤ B) (j : ℕ) (hj : j ≤ (Node.exts (node G k (q + 1) u)).words.length) :
    ∃ tg sl hdr rin, lpU x (scA k (node G k (q + 1) u) x S j) (scB k (node G k (q + 1) u) j) =
      gIn tg sl k (node G k (q + 1) u) hdr (wl k (node G k (q + 1) u) S j) rin ∧
      GBnd tg sl k (node G k (q + 1) u) hdr (wl k (node G k (q + 1) u) S j) rin S.length j B := by
  cases j with
  | zero =>
    refine ⟨0, x.length, [], [0], ?_, ?_⟩
    · rw [lpU_zero k _ x S hx, wl_zero]; rfl
    · rw [wl_zero]; exact gbnd_zero G k q u S x hx B hB
  | succ j =>
    refine ⟨1, _, [0, j + 1, S.length], [], lpU_succ k _ x S hx j, ?_⟩
    exact gbnd_succ G k q u S x hx B hB j (by omega)

theorem far_answer (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    toWord (farList (toWord (node G k (q + 1) u))
      ((wl k (node G k (q + 1) u) (stp G k (q + 1)).words (Node.exts (node G k (q + 1) u)).words.length).drop
        (stp G k (q + 1)).words.length) k q ℓ
      ((wl k (node G k (q + 1) u) (stp G k (q + 1)).words (Node.exts (node G k (q + 1) u)).words.length).take
        (stp G k (q + 1)).words.length)) = toWord (ftree G k (q + 1) u) := by
  set t := node G k (q + 1) u
  set S := (stp G k (q + 1)).words
  have hd : (wl k t S (Node.exts t).words.length).drop S.length =
      (List.range (Node.exts t).words.length).map (ansW k t) := by simp [wl]
  have htk : (wl k t S (Node.exts t).words.length).take S.length = S := by simp [wl]
  rw [hd, htk, farList_eq (rest := []) (by simp; rfl) (ansOK_genuine G k q u) (stp G k (q + 1)) (stp_fun G k (q + 1)),
    ← farTree_tree k q u hℓ hℓk]
  rfl

theorem wd_wl_three (S : List (List ℕ)) (hS : ∀ w ∈ S, 3 ≤ w.length) (j : ℕ) :
    ∀ i < S.length, 3 ≤ (wd (wl k (node G k (q + 1) u) S j) i).length := by
  intro i hi
  have h1 : i < (wl k (node G k (q + 1) u) S j).length := by simp [wl]; omega
  rw [wd_eq h1]
  have : (wl k (node G k (q + 1) u) S j)[i] = S[i] := by simp [wl, List.getElem_append_left hi]
  rw [this]; exact hS _ (List.getElem_mem hi)

end Lax185574Proofs.FarRam
