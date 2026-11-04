import Lax185574Proofs.ResolveRam.Glue.CFEClause
import Lax185574Proofs.ResolveRam.SizeGlue.State
import Lax185574Proofs.ResolveRam.SizeGlue.Calls

/-!
The time of the last round of the glue program of lem:resolve-lift.

The time `tFin` of the last round is linear in the lengths of the input,
the state, the answer and the output of the round, plus the piece of the
resolved graph, which costs `cH (|x| + 1)`. With the size bounds
on these words this is at most `C (n + 1)² Y ^ A` with
`Y = M + T + 1`, plus the cost `KB` of the case of the round and terms in
`K` and the rank (`tFin_le`). No entry of the input enters the bound.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

theorem fe_pow_le {Y a A : ℕ} (hY : 1 ≤ Y) (h : a ≤ A) : Y ^ a ≤ Y ^ A := Nat.pow_le_pow_right hY h

/-- **The time of the last round.** -/
theorem tFin_le (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (Lay : Layout) (K KB : ℕ) (n : ℕ)
    (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (j : ℕ), 1 ≤ n →
    j + 1 = (rcalls G P Q s k₀ q₀).length →
    tFin Lay K KB ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
        k₀ q₀ (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
        (feK n (xIn G k₀ q₀ P Q s).length (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
          (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) (0 :: zOut G k₀ q₀ P Q s)) ≤
      Lay.const * (C * (n + 1) * (n + 1) *
          (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A +
        KB + 30 * K + 23 * ((k₀ + q₀ + 1) * (q₀ + 1))) + 5 := by
  obtain ⟨C1, A1, hst⟩ := stOf_cur_len k₀ q₀ hk
  obtain ⟨C2, A2, hb⟩ := rcall_le_nY (k₀ := k₀) (q₀ := q₀) hk
  obtain ⟨C3, A3, hz⟩ := zOut_le k₀ q₀ hk
  refine ⟨100 * C1 + 100 * C2 + 50 * C3 + 12 * cH + 2000, A1 + A2 + A3 + 1,
    fun Lay K KB n G P Q s j hn hj => ?_⟩
  have ex := xIn_len_le' k₀ q₀ G P Q s
  have est := hst n G P Q s j (by omega)
  obtain ⟨hv, hf, hc⟩ := fe_cur G P Q s k₀ q₀ hn hj
  have hne : callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ≠ .stp := by
    obtain ⟨i, m, hcm, hi, hm⟩ := fe_last G P Q s k₀ q₀ hv hf
    rw [hcm, callOf_up' (by omega) (by omega)]; split_ifs <;> simp
  have eb := hb n G P Q s _ (List.mem_of_getElem? hc) hne
  have ez := hz n G P Q s
  set H := resolveBy G s P Q
  set Y := maxTreeSize G k₀ q₀ + treeCount G H k₀ q₀ + 1
  set A := A1 + A2 + A3 + 1
  set c := cur G P Q s k₀ q₀ j
  set x := xIn G k₀ q₀ P Q s
  set st := stOf G P Q s k₀ q₀ c
  set b := rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)
  set ws := (swAt G P Q s k₀ q₀ c).ws
  set o := 0 :: zOut G k₀ q₀ P Q s
  set B := (n + 1) * (n + 1) * Y ^ A
  have hY : 1 ≤ Y := by simp only [Y]; omega
  have hN : 1 ≤ n + 1 := by omega
  have hYA : 1 ≤ Y ^ A := Nat.one_le_pow _ _ hY
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- the input
  have hx : x.length + 1 ≤ 12 * B := by
    have h2 : maxTreeSize G k₀ q₀ + 1 ≤ Y ^ A :=
      le_trans (show maxTreeSize G k₀ q₀ + 1 ≤ Y by simp only [Y]; omega)
        (by simpa using fe_pow_le hY (show 1 ≤ A by simp only [A]; omega))
    have h3 : x.length ≤ 11 * B := by
      refine le_trans ex ?_
      simp only [B]
      calc 11 * (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1)
          = 11 * ((n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1)) := by ring
        _ ≤ 11 * ((n + 1) * (n + 1) * Y ^ A) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    omega
  -- the state
  have hst' : st.length ≤ C1 * B := by
    have h1 := est
    calc st.length ≤ C1 * (n + 1) * Y ^ A1 := h1
      _ ≤ C1 * (n + 1) * Y ^ A := Nat.mul_le_mul_left _ (fe_pow_le hY (by simp only [A]; omega))
      _ ≤ C1 * B := by
        simp only [B]
        have : (n + 1) * Y ^ A ≤ (n + 1) * (n + 1) * Y ^ A := by
          rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
        calc C1 * (n + 1) * Y ^ A = C1 * ((n + 1) * Y ^ A) := by ring
          _ ≤ C1 * ((n + 1) * (n + 1) * Y ^ A) := Nat.mul_le_mul_left _ this
  -- the answer
  have hb' : b.length ≤ C2 * B := by
    have h2 : b.length ≤ C2 * (n + 1) * Y ^ A2 := by omega
    calc b.length ≤ C2 * (n + 1) * Y ^ A2 := h2
      _ ≤ C2 * (n + 1) * Y ^ A := Nat.mul_le_mul_left _ (fe_pow_le hY (by simp only [A]; omega))
      _ ≤ C2 * B := by
        simp only [B]
        have : (n + 1) * Y ^ A ≤ (n + 1) * (n + 1) * Y ^ A := by
          rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
        calc C2 * (n + 1) * Y ^ A = C2 * ((n + 1) * Y ^ A) := by ring
          _ ≤ C2 * ((n + 1) * (n + 1) * Y ^ A) := Nat.mul_le_mul_left _ this
  -- the output
  have ho : o.length ≤ C3 * B + 1 := by
    have h1 := ez
    have : (zOut G k₀ q₀ P Q s).length ≤ C3 * B := by
      calc (zOut G k₀ q₀ P Q s).length ≤ C3 * (n + 1) * (n + 1) * Y ^ A3 := h1
        _ ≤ C3 * (n + 1) * (n + 1) * Y ^ A := Nat.mul_le_mul_left _ (fe_pow_le hY (by simp only [A]; omega))
        _ = C3 * B := by simp only [B]; ring
    simp only [o, List.length_cons]; omega
  -- the library is the state
  have hws : total ws ≤ st.length := by
    have := length_toWord_words ws
    have e : st = scW G P Q s k₀ q₀ c ++ toWord ws := rfl
    rw [e, List.length_append]; omega
  have hwx : (x.take (winOf G P Q s k₀ q₀ c)).length ≤ x.length := by
    simp only [List.length_take]; omega
  have hcH : cH * (x.length + 1) ≤ 12 * (cH * B) := by
    calc cH * (x.length + 1) ≤ cH * (12 * B) := Nat.mul_le_mul_left _ hx
      _ = 12 * (cH * B) := by ring
  have hC : (100 * C1 + 100 * C2 + 50 * C3 + 12 * cH + 2000) * (n + 1) * (n + 1) * Y ^ A =
      100 * (C1 * B) + 100 * (C2 * B) + 50 * (C3 * B) + 12 * (cH * B) + 2000 * B := by
    simp only [B]; ring
  unfold tFin
  rw [hC]
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5
  unfold preK feK
  omega

end Lax185574Proofs.ResolveRam.Glue
