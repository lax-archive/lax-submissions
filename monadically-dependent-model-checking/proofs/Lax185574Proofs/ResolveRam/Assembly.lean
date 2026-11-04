import Lax185574Proofs.ResolveRam.TimeMain
import Lax185574Proofs.ResolveRam.OutputSize
import Lax185574Proofs.RamLoop
import Lax185574Proofs.ResolveRam.SizeAll

/-!
Assembly of lem:resolve-lift from the glue program and the size bounds.
`resolve_of_glue` uses the size bounds `sizeHyp`.

The program is the loop driver of the glue program `Gp` of `RGlueHyp`
and the switch of the five callees, with `D = sI + 4`. The exponent is
`eRes`. For each rank the constant and the degree are those of
`resolve_time`, enlarged by those of `output_size`. Every halting run at
an admissible word length is right by `resolve_sound_adm`, the composite
halts within the bound by `resolve_time`, and the trees of the output
are small by `output_size`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574.DistanceMatrix

theorem rBound_eq {n : ℕ} (G : PartialGraph (Fin n)) (k q P Q : ℕ) (s : Bool) (c a : ℕ) :
    rBound G k q P Q s c a = c * (n + 1) ^ 2 *
      (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a := by
  unfold rBound; ring

theorem rBound_mono {n : ℕ} (G : PartialGraph (Fin n)) (k q P Q : ℕ) (s : Bool) {c c' a a' : ℕ}
    (hc : c ≤ c') (ha : a ≤ a') : rBound G k q P Q s c a ≤ rBound G k q P Q s c' a' := by
  unfold rBound
  have : (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a ≤
      (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a' :=
    Nat.pow_le_pow_right (by omega) ha
  gcongr

/-- **lem:resolve-lift from its parts.** -/
theorem resolve_of_parts (hG : RGlueHyp) (hS : SizeHyp) :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
        Computes p e c (G, distMatrix G, P, Q, s, family G k q)
          (resolveBy G s P Q, distMatrix (resolveBy G s P Q), family (resolveBy G s P Q) k q)
          (fun _ => c * (n + 1) ^ 2 *
            (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a) ∧
        ∀ b : Fin n, wordLength (tree (resolveBy G s P Q) k q ![b]) ≤
          c * (treeCount G (resolveBy G s P Q) k q + 1) ^ a := by
  obtain ⟨sI, hGl⟩ := hG
  set D := sI + 4 with hD
  obtain ⟨Gp, hGp⟩ := hGl eSh eFt eCo eCa eSt D le_rfl
  obtain ⟨sw, Ks, hsw⟩ := switch5 pSh pFt pCo pCa pSt D (by omega)
  obtain ⟨P0, KL, hP0⟩ := loop_sound Gp sw
  refine ⟨P0, eRes, fun k q => ?_⟩
  by_cases hk : 1 ≤ k
  swap
  · exact ⟨0, 0, fun _ _ _ _ _ h => absurd h hk⟩
  obtain ⟨cG, aG, hgl⟩ := hGp k q
  obtain ⟨C, A, hcb⟩ := hS k q hk
  obtain ⟨co, ao, hout⟩ := output_size k q hk
  refine ⟨cRes k q Ks KL D C cG + co, aRes A aG + ao, fun n G P Q s _ => ⟨fun w hadm => ?_,
    fun b => ?_⟩⟩
  · have hadm' : WordAdmissible eRes (cRes k q Ks KL D C cG) w (xIn G k q P Q s) :=
      adm_mono hadm (by omega)
    refine ⟨fun y t hr => ?_, fun hT => ?_⟩
    · -- soundness
      have hX := adm_X G k q hadm'
      have hs : sCst k q Ks D * ySz (xIn G k q P Q s) ≤ 2 ^ w := by
        refine le_trans ?_ hX
        have h1 : sCst k q Ks D ≤ cRes k q Ks KL D C cG := by unfold cRes; omega
        have h2 : ySz (xIn G k q P Q s) ≤ ySz (xIn G k q P Q s) ^ eRes :=
          Nat.le_self_pow (by unfold eRes; omega) _
        exact Nat.mul_le_mul h1 h2
      exact resolve_sound_adm G k q hsw hP0 (by omega) hk (hgl n G P Q s hk) hs y t hr
    · -- halting within the bound
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have hmono := rBound_mono G k q P Q s (c := cRes k q Ks KL D C cG)
        (c' := cRes k q Ks KL D C cG + co) (a := aRes A aG) (a' := aRes A aG + ao) (by omega)
        (by omega)
      have he := rBound_eq G k q P Q s (cRes k q Ks KL D C cG + co) (aRes A aG + ao)
      obtain ⟨t, ht, hr⟩ := resolve_time G k q hsw hP0 (by omega) hk (hgl n G P Q s hk)
        (hcb n G P Q s) hadm' (le_trans hmono (le_trans he.le hT))
      exact ⟨t, le_trans ht (le_trans hmono he.le), hr⟩
  · refine le_trans (hout n G P Q s b) ?_
    have : (treeCount G (resolveBy G s P Q) k q + 1) ^ ao ≤
        (treeCount G (resolveBy G s P Q) k q + 1) ^ (aRes A aG + ao) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    gcongr
    omega

/-- **lem:resolve-lift from the glue program.** -/
theorem resolve_of_glue (hG : RGlueHyp) :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
        Computes p e c (G, distMatrix G, P, Q, s, family G k q)
          (resolveBy G s P Q, distMatrix (resolveBy G s P Q), family (resolveBy G s P Q) k q)
          (fun _ => c * (n + 1) ^ 2 *
            (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a) ∧
        ∀ b : Fin n, wordLength (tree (resolveBy G s P Q) k q ![b]) ≤
          c * (treeCount G (resolveBy G s P Q) k q + 1) ^ a :=
  resolve_of_parts hG sizeHyp

end Lax185574Proofs.ResolveRam
