import Lax185574Proofs.MC.Brute.Loop
import Lax185574Proofs.MC.Brute.Graph
import Lax185574Proofs.MC.Brute.Seq
import Lax185574Proofs.MC.Brute.Code
import Lax185574Proofs.MC.Brute.Ends
import Lax185574.ConstructionModelChecking
import Lax185574Proofs.LegacyInputs

/-!
The preparation phase of the brute-force thread.

`preCmd` reads the header of the graph, builds the adjacency matrix,
skips the sequence, reads the code of the sentence and computes the
ends of its subformulas. `pre_run` gives the run on an input word of
thm:mc when all values fit below `W`, which `(|x| + 2)² ≤ W` ensures.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MainRam Lax185574Proofs.Compose Lax271696.GraphEncoding
open Lax3.FirstOrder Lax185574.InstanceEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionModelChecking
open Classical

/-- The preparation. -/
def preCmd : Com :=
  .seq (.read "n") (.seq (.read "E") (.seq grBody (.seq skipSeq (.seq rdFml endsCmd))))

/-- The array lengths. -/
def bExt (n E B : ℕ) : String → ℕ := fun a =>
  if a = "of" then n + 1 else if a = "tg" then 2 * E else if a = "A" then n * n else B

/-- The facts after the preparation. -/
structure PreOK (B W n : ℕ) (G : SimpleGraph (Fin n)) (φ : FO 0) (σ : Env) : Prop where
  hW : σ.vars "W" = W
  hov : σ.vars "ovf" = 0
  hn : σ.vars "bfn" = n
  lc : (σ.arrs "bfc").length = B
  cd : ∀ i, (σ.arrs "bfc").getD i 0 = (code φ).getD i 0
  le : (σ.arrs "bfe").length = B
  ve : ∀ i, (σ.arrs "bfe").getD i 0 < B
  good : Good (σ.arrs "bfc") (σ.arrs "bfe") (code φ).length 0
  lA : (σ.arrs "bfA").length = B
  vA : ∀ i, (σ.arrs "bfA").getD i 0 ≤ 1
  adj : ∀ u v : Fin n, adjOf σ n u v = decide (G.Adj u v)
  stk : ∀ a ∈ ["bfk", "bfa", "bfw", "bfg"], σ.arrs a = List.replicate B 0

theorem replicate_getD (B i : ℕ) : (List.replicate B 0).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

/-- The frame names of the phases. -/
macro "frm" : tactic => `(tactic| simp [grBody, readArr, adjPh, adjRow, adjBody, cpA, forUp, skipSeq,
  skipLoop, rdK, rdFml, rdBody, rdOp, endsCmd, endBody, Com.wvars, Com.warrs])

theorem code_getD_lt {φ : FO 0} {B : ℕ} (h : ∀ v ∈ code φ, v < B) (hB : 0 < B) (i : ℕ) :
    (code φ).getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : (code φ)[i]? with
  | none => simpa
  | some v => simpa using h v (List.mem_of_getElem? hc)

theorem pre_run {n : ℕ} {G : SimpleGraph (Fin n)} {s : List (Lax185574.PartialGraphs.PartialGraph (Fin n))}
    {φ : FO 0} {g y : List ℕ} (hg : EncodesGraph g n G) (hy : EncodesSequence y s) {B W : ℕ}
    (hB : B = W + 1) (hxW : ∀ v ∈ g ++ y ++ code φ, v ≤ W)
    (hfit : ((g ++ y ++ code φ).length + 2) ^ 2 ≤ W) :
    ∃ σ', Run B preCmd ((initEnv (bExt n (edgeCount g) B) (g ++ y ++ code φ)).setVar "W" W) σ'
      (400 * (n * n + (g ++ y ++ code φ).length) + 300) ∧ PreOK B W n G φ σ' := by
  obtain ⟨σs, rfl, -⟩ := hy
  set E := edgeCount g with hEd
  set L := (code φ).length with hLd
  have hgl : g.length = 3 + n + 2 * E := hg.length_eq
  set X := (g ++ toWord σs ++ code φ).length with hXd
  have hX : X = g.length + (toWord σs).length + L := by simp [X, L]
  have hXW : X + 6 ≤ W := by nlinarith
  have hnn : n * n + 2 * E + 2 < B := by
    have : (n + 2 * E + 3) ^ 2 ≤ (X + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hLB : L + 6 ≤ W := by omega
  obtain ⟨hgs, hofl, htgl⟩ := graph_split hg
  rw [← hEd] at hgs htgl
  set σ0 := (initEnv (bExt n E B) (g ++ toWord σs ++ code φ)).setVar "W" W with hσ0
  have arr0 : ∀ a, σ0.arrs a = List.replicate (bExt n E B a) 0 := fun a => rfl
  have hinp0 : σ0.inp = n :: E :: (ofL g n ++ (tgL g n ++ (toWord σs ++ code φ))) := by
    show g ++ toWord σs ++ code φ = _
    conv_lhs => rw [hgs]
    simp
  set σ1 : Env := { σ0.setVar "n" n with inp := E :: (ofL g n ++ (tgL g n ++ (toWord σs ++ code φ))) }
  set σ2 : Env := { σ1.setVar "E" E with inp := ofL g n ++ (tgL g n ++ (toWord σs ++ code φ)) }
  have r1 : Run B (.read "n") σ0 σ1 1 := Run.read hinp0
  have r2 : Run B (.read "E") σ1 σ2 1 := Run.read rfl
  have arr2 : ∀ a, σ2.arrs a = List.replicate (bExt n E B a) 0 := fun a => by
    simp only [σ2, σ1, arrs_setVar]; exact arr0 a
  have hgB : ∀ a ∈ g, a < B := fun a ha => by have := hxW a (by simp [ha]); omega
  -- the matrix
  obtain ⟨σ3, r3, hi3, hn3, hl3, hv3, ha3⟩ := grBody_run (B := B) hg (σ := σ2) (by simp [σ2, σ1])
    (by simp [σ2, hEd]) rfl (by rw [← hEd]; exact hnn) hgB (by rw [arr2]; simp [bExt, replicate_eq_arrOf])
    (by rw [arr2]; simp [bExt, replicate_eq_arrOf, hEd]) (by rw [arr2]; simp [bExt, replicate_eq_arrOf])
    (by rw [arr2]; simp [bExt]) (fun i => by rw [arr2]; exact replicate_getD _ _)
  have fa3 : ∀ a ∈ ["bfc", "bfe", "bfk", "bfa", "bfw", "bfg"], σ3.arrs a = List.replicate B 0 := by
    intro a ha
    rw [r3.frame_arr a (by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> frm),
      arr2]
    simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bExt]
  have hW3 : σ3.vars "W" = W := by rw [r3.frame_var "W" (by frm)]; simp [σ2, σ1, σ0]
  have hov3 : σ3.vars "ovf" = 0 := by rw [r3.frame_var "ovf" (by frm)]; simp [σ2, σ1, σ0, initEnv]
  -- the sequence
  obtain ⟨σ4, r4, hi4⟩ := skipSeq_run (B := B) σs (rest := code φ)
    (fun v hv => by have := hxW v (by simp [hv]); omega) (σ := σ3) hi3
  have fa4 : ∀ a ∈ ["bfc", "bfe", "bfk", "bfa", "bfw", "bfg", "bfA"], σ4.arrs a = σ3.arrs a :=
    fun a _ => r4.frame_arr a (by frm)
  have hW4 : σ4.vars "W" = W := by rw [r4.frame_var "W" (by frm), hW3]
  have hov4 : σ4.vars "ovf" = 0 := by rw [r4.frame_var "ovf" (by frm), hov3]
  have hn4 : σ4.vars "bfn" = n := by rw [r4.frame_var "bfn" (by frm), hn3]
  -- the code
  have hcB : ∀ v ∈ code φ, v < B := fun v hv => by have := hxW v (by simp [hv]); omega
  have hc4 : σ4.arrs "bfc" = List.replicate B 0 := by rw [fa4 _ (by simp), fa3 _ (by simp)]
  obtain ⟨σ5, r5, hW5, hlc5, hcase⟩ := rdFml_run (B := B) (W := W) φ (rest := []) hB hcB (σ := σ4)
    hW4 hov4 (by rw [hi4]; simp) (by rw [hc4]; simp) (fun i => by rw [hc4]; exact replicate_getD _ _)
    (by omega)
  rcases hcase with ⟨hov5, hi5, hl5, hcd5⟩ | ⟨-, hbad⟩
  swap
  · omega
  have fa5 : ∀ a ∈ ["bfe", "bfk", "bfa", "bfw", "bfg", "bfA"], σ5.arrs a = σ4.arrs a :=
    fun a ha => r5.frame_arr a (by simp [rdFml, rdBody, rdOp, Com.warrs]; rintro rfl; simp at ha)
  have hn5 : σ5.vars "bfn" = n := by rw [r5.frame_var "bfn" (by frm), hn4]
  -- the ends
  have he5 : σ5.arrs "bfe" = List.replicate B 0 := by
    rw [fa5 _ (by simp), fa4 _ (by simp), fa3 _ (by simp)]
  obtain ⟨σ6, r6, hle6, hve6, hgood6⟩ := ends_run (B := B) (L := L) (C := σ5.arrs "bfc") (σ := σ5)
    (by omega) hl5 rfl hlc5 (fun i => by rw [hcd5 i]; exact code_getD_lt hcB (by omega) i)
    (by rw [he5]; simp) (fun i => by rw [he5]; exact replicate_getD _ _)
  have fc6 : σ6.arrs "bfc" = σ5.arrs "bfc" := r6.frame_arr "bfc" (by frm)
  have fA6 : σ6.arrs "bfA" = σ3.arrs "bfA" := by
    rw [r6.frame_arr "bfA" (by frm), fa5 _ (by simp), fa4 _ (by simp)]
  refine ⟨σ6, ?_, ⟨by rw [r6.frame_var "W" (by frm), hW5], by rw [r6.frame_var "ovf" (by frm), hov5],
    by rw [r6.frame_var "bfn" (by frm), hn5], by rw [fc6, hlc5], fun i => by rw [fc6, hcd5 i],
    hle6, hve6, by rw [fc6]; exact hgood6, by rw [fA6, hl3], fun i => by rw [fA6]; exact hv3 i,
    fun u v => by unfold adjOf; rw [fA6]; exact ha3 u v, fun a ha => ?_⟩⟩
  · unfold preCmd
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    have := hX
    generalize n * n = nn
    omega
  · rw [r6.frame_arr a (by simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> frm),
      fa5 _ (by simp at ha ⊢; tauto), fa4 _ (by simp at ha ⊢; tauto), fa3 _ (by simp at ha ⊢; tauto)]

end Lax185574Proofs.MC.Brute
