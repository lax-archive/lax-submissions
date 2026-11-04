import Lax185574Proofs.MainRam.ValidRest
import Lax185574Proofs.MainRam.Instances

/-!
**The validation program.** The run of the whole command, and the
specification `ValidSpec` of the compiled program.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Simulation
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax271696.GraphEncoding Lax185574Proofs.Compose
open Lax3.FirstOrder Lax185574.WordEncoding
open Classical

/-- The array lengths of the validation program. -/
def vExt (n E ly lf : ℕ) : String → ℕ := fun a =>
  if a = "Y" then ly else if a = "of" then n + 1 else if a = "tg" then 2 * E else
  if a = "F" then lf else if a = "A" ∨ a = "S" ∨ a = "S2" then n * n else
  if a = "col" ∨ a = "c2" then n else 0

set_option maxHeartbeats 2000000 in
theorem vCom_run {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G)
    (φ : FO 0) (y : List ℕ) (hy : ∀ a ∈ y, a ≤ y.length + (g ++ toWord φ).length + 2) :
    ∃ σ', Run (4 * (y.length + (g ++ toWord φ).length + 2) ^ 2 + 9) vCom
      (initEnv (vExt n (edgeCount g) y.length (toWord φ).length)
        (y.length :: ((g ++ toWord φ).length + 1) :: (y ++ (g ++ toWord φ)))) σ'
      (1000 * ((y.length + 1) * (n + 1) ^ 2 + (g ++ toWord φ).length + 1)) ∧
      σ'.out = vOut n G φ g y := by
  set x := g ++ toWord φ with hx
  set φw := toWord φ with hφw
  set E := edgeCount g with hE
  set X := x.length with hX
  set Lb := y.length + X + 2 with hLb
  set Λ := Lb ^ 2 with hΛ
  set B := 4 * Λ + 9 with hBdef
  have hLbΛ : Lb ≤ Λ := Nat.le_self_pow (by norm_num) _
  have hxl : (g ++ φw).length = X := rfl
  have hxl' : (g ++ toWord φ).length = X := rfl
  have hgl : g.length = 3 + n + 2 * E := hg.length_eq
  have hXg : X = g.length + φw.length := by simp [hX, hx, hφw]
  have hnX : n ≤ X := by omega
  have hEX : 2 * E ≤ X := by omega
  have hnn : n * n + n ≤ Λ := by
    have : (n + 1) ^ 2 ≤ Lb ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  have hxe := instance_entries_le hg φ
  have hyΛ : ∀ a ∈ y, a ≤ Λ := fun a ha => le_trans (hy a ha) (by omega)
  have hlΛ : y.length ≤ Λ := by omega
  obtain ⟨hgs, hofl, htgl⟩ := graph_split hg
  set ext := vExt n E y.length φw.length with hext
  set σ0 := initEnv ext (y.length :: (X + 1) :: (y ++ x)) with hσ0
  have arr0 : ∀ a, σ0.arrs a = arrOf (ext a) (fun _ => 0) := fun a => by
    simp [hσ0, initEnv, replicate_eq_arrOf]
  -- reading
  obtain ⟨σ1, r1, hL1, hn1, hE1, hnF1, hY1, hof1, htg1, hF1, ha1, ho1⟩ := readPh_run (B := B)
    (φw := φw) (y := y) hg (σ := σ0) rfl (by omega) (fun a ha => by have := hy a ha; omega)
    (fun a ha => by have := hxe a ha; omega)
    (by rw [arr0]; simp [hext, vExt]) (by rw [arr0]; simp [hext, vExt])
    (by rw [arr0]; simp [hext, vExt]; rfl) (by rw [arr0]; simp [hext, vExt])
  -- the adjacency matrix
  set o : ℕ → ℕ := fun i => (ofL g n).getD i 0 with ho
  set t : ℕ → ℕ := fun j => (tgL g n).getD j 0 with ht
  have hmono : ∀ u < n, o u ≤ o (u + 1) := fun u hu => by
    have := hg.offset_mono u hu
    rwa [offset_eq hg (by omega), offset_eq hg (by omega)] at this
  have hlast : o n = 2 * E := by
    have := hg.offset_last; rwa [offset_eq hg le_rfl] at this
  have hoB : ∀ i ≤ n, o i ≤ 2 * E := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self => exact le_of_eq hlast
    | of_succ k hk ih => exact le_trans (hmono k hk) ih
  have htB : ∀ j < 2 * E, t j < n := fun j hj => by
    have := hg.target_lt j hj; rwa [target_eq hg] at this
  obtain ⟨σ2, r2, hA2, hn2, ha2, ho2, -⟩ := adjPh_run (B := B) (N := n) (D := 2 * E) (o := o)
    (t := t) (by nlinarith) hmono hoB htB hn1
    (by rw [hof1]; conv_lhs => rw [list_eq_arrOf (ofL g n), hofl])
    (by rw [htg1]; conv_lhs => rw [list_eq_arrOf (tgL g n), htgl])
    (by rw [ha1 "A" (by decide) (by decide) (by decide) (by decide), arr0]; simp [hext, vExt])
  have hL2 : σ2.vars "L" = y.length := by rw [r2.frame_var "L" (by decide), hL1]
  have hE2 : σ2.vars "E" = E := by rw [r2.frame_var "E" (by decide), hE1]
  have hnF2 : σ2.vars "nF" = φw.length := by rw [r2.frame_var "nF" (by decide), hnF1]
  have harr2 : ∀ a, a ≠ "A" → a ≠ "Y" → a ≠ "of" → a ≠ "tg" → a ≠ "F" →
      σ2.arrs a = arrOf (ext a) (fun _ => 0) := fun a h0 h1 h2 h3 h4 => by
    rw [ha2 a h0, ha1 a h1 h2 h3 h4, arr0]
  -- the shape
  obtain ⟨σ3, r3, hok3, hm3, fv3, fa3, -, ho3⟩ := parsePh_run (B := B) (Λ := Λ) hn2 hL2
    (by rw [ha2 _ (by decide), hY1]) hyΛ hlΛ (by omega) (by omega)
  have hn3 : σ3.vars "n" = n := by rw [fv3 _ (by decide) (by decide), hn2]
  -- the checks
  obtain ⟨σ4, r4, hok4, hn4, hE4, hL4, hnF4, fa4, ho4⟩ : ∃ σ4, Run B (.ite (.eq (.var "ok")
      (.lit 1)) restPh .skip) σ3 σ4 (y.length * (n * (n * 120 + 108) + 160) +
        n * (n * 400 + 100) + 120) ∧
      σ4.vars "ok" = (if Checks G g y then 1 else 0) ∧ σ4.vars "n" = n ∧ σ4.vars "E" = E ∧
      σ4.vars "L" = y.length ∧ σ4.vars "nF" = φw.length ∧
      (∀ a, a ∈ ["Y", "of", "tg", "F"] → σ4.arrs a = σ3.arrs a) ∧ σ4.out = σ3.out := by
    have hE3 : σ3.vars "E" = E := by rw [fv3 _ (by decide) (by decide), hE2]
    have hL3 : σ3.vars "L" = y.length := by rw [fv3 _ (by decide) (by decide), hL2]
    have hnF3 : σ3.vars "nF" = φw.length := by rw [fv3 _ (by decide) (by decide), hnF2]
    have hc := evalB_condEq' (B := B) (σ := σ3) (e := .var "ok") (f := .lit 1)
      (evalB_var (by rw [hok3]; have := Lax185574Proofs.Conversions.Ram.ind_le_one (Shape n y); omega))
      (evalB_lit (by omega))
    by_cases hS : Shape n y
    · rw [hok3, Lax185574Proofs.Conversions.Ram.ind, if_pos hS] at hc
      obtain ⟨σ4, r4', hok4⟩ := restPh_run (B := B) (Λ := Λ) (G := G) (g := g) (y := y) hn3
        (hm3 hS) (by rw [fa3, ha2 _ (by decide), hY1])
        (by rw [fa3, harr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)];
            simp [hext, vExt])
        (by rw [fa3, harr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)];
            simp [hext, vExt])
        (by rw [fa3, harr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)];
            simp [hext, vExt])
        (by rw [fa3, harr2 _ (by decide) (by decide) (by decide) (by decide) (by decide)];
            simp [hext, vExt])
        (by rw [fa3, hA2]) (by rw [hok3, Lax185574Proofs.Conversions.Ram.ind, if_pos hS]) hS hyΛ hlΛ
        hnn (by omega)
      refine ⟨σ4, (Run.ite_true hc r4').mono (by simp; omega), hok4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [r4'.frame_var "n" (by decide), hn3]
      · rw [r4'.frame_var "E" (by decide), hE3]
      · rw [r4'.frame_var "L" (by decide), hL3]
      · rw [r4'.frame_var "nF" (by decide), hnF3]
      · intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> exact r4'.frame_arr _ (by decide)
      · exact r4'.out_eq (by decide)
    · rw [hok3, Lax185574Proofs.Conversions.Ram.ind, if_neg hS] at hc
      have hC : ¬ Checks G g y := fun h => hS h.1
      refine ⟨σ3, (Run.ite_false hc Run.skip).mono (by simp), by rw [hok3,
        Lax185574Proofs.Conversions.Ram.ind, if_neg hS,
        if_neg hC], hn3, hE3, hL3, hnF3, fun _ _ => rfl, rfl⟩
  -- the output
  have hY4 : σ4.arrs "Y" = y := by rw [fa4 _ (by decide), fa3, ha2 _ (by decide), hY1]
  have hof4 : σ4.arrs "of" = ofL g n := by rw [fa4 _ (by decide), fa3, ha2 _ (by decide), hof1]
  have htg4 : σ4.arrs "tg" = tgL g n := by rw [fa4 _ (by decide), fa3, ha2 _ (by decide), htg1]
  have hF4 : σ4.arrs "F" = φw := by rw [fa4 _ (by decide), fa3, ha2 _ (by decide), hF1]
  have hgent : ∀ a ∈ ofL g n ++ tgL g n ++ y ++ φw, a < B := by
    intro a ha
    simp only [List.mem_append] at ha
    rcases ha with ((ha | ha) | ha) | ha
    · have : a ∈ x := by rw [hx, hgs]; simp [ha]
      have := hxe a this; omega
    · have : a ∈ x := by rw [hx, hgs]; simp [ha]
      have := hxe a this; omega
    · have := hy a ha; omega
    · have : a ∈ x := by rw [hx]; simp [ha]
      have := hxe a this; omega
  obtain ⟨σ5, r5, ho5⟩ := outPh_run (B := B) (n := n) (E := E) (ofv := ofL g n) (tgv := tgL g n)
    (y := y) (φw := φw) (by rw [hok4]; split_ifs <;> omega) hn4 hE4 hL4 hnF4 hof4 htg4 hY4 hF4
    hofl (by omega) (by omega) hgent
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ?_⟩
  · have hφX : φw.length ≤ X := by omega
    have h1 : y.length * (n * (n * 120 + 108) + 160) ≤ 400 * (y.length * (n + 1) ^ 2) := by
      have : n * (n * 120 + 108) + 160 ≤ 400 * (n + 1) ^ 2 := by nlinarith
      calc y.length * (n * (n * 120 + 108) + 160) ≤ y.length * (400 * (n + 1) ^ 2) :=
            Nat.mul_le_mul_left _ this
        _ = 400 * (y.length * (n + 1) ^ 2) := by ring
    have h2 : n * (n * 400 + 100) ≤ 500 * (n + 1) ^ 2 := by nlinarith
    have h3 : (y.length + 1) * (n + 1) ^ 2 = y.length * (n + 1) ^ 2 + (n + 1) ^ 2 := by ring
    have h4 : n ≤ (n + 1) ^ 2 := by nlinarith
    have h5 : y.length ≤ y.length * (n + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  · rw [ho5, ho4, ho3, ho2, ho1]
    simp only [hσ0, initEnv, List.nil_append]
    unfold vOut
    rw [hok4]
    by_cases hv : ValidScript n G y
    · rw [if_pos ((validScript_iff_checks hg y).1 hv), if_pos rfl, if_pos hv]
      conv_rhs => rw [hgs]
      simp [hφw, List.append_assoc, hE]
    · rw [if_neg (fun h => hv ((validScript_iff_checks hg y).2 h)), if_neg (by omega), if_neg hv]
      simp [dummyWord, hφw]

/-- **The validation program.** -/
theorem validSpec : ValidSpec (compileProgram vLayout vCom) (vLayout.const * 1000 + 100) := by
  intro v n G φ g y hg hy hc
  obtain ⟨σ', hr, hout⟩ := vCom_run hg φ y hy
  obtain ⟨k, hk, hbs⟩ := hr
  set Lb := y.length + (g ++ toWord φ).length + 2 with hLb
  have hL4 : 4 ≤ Lb ^ 2 := by nlinarith
  have hc' : 100 * Lb ^ 2 ≤ 2 ^ v :=
    le_trans (Nat.mul_le_mul_right _ (by omega)) hc
  have hfit : vLayout.FitsWords (4 * Lb ^ 2 + 9) v :=
    ⟨by omega, by omega, by simp [Layout.span, vLayout]; omega⟩
  have hxe := instance_entries_le hg φ
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo hfit vCom_ok (fun a ha => by
    simp only [List.mem_cons, List.mem_append] at ha
    have hLbsq : Lb ≤ Lb ^ 2 := Nat.le_self_pow (by norm_num) _
    rcases ha with rfl | rfl | ha | ha
    · omega
    · omega
    · have := hy a ha; omega
    · have := hxe a (List.mem_append.2 ha); omega) hbs
  rw [hout] at hrun
  refine ⟨t, le_trans ht ?_, hrun⟩
  set W := (y.length + 1) * (n + 1) ^ 2 + (g ++ toWord φ).length + 1
  have h1 : vLayout.const * k ≤ vLayout.const * (1000 * W) := Nat.mul_le_mul_left _ hk
  have h2 : (vLayout.const * 1000 + 100) * W = vLayout.const * (1000 * W) + 100 * W := by ring
  have h3 : 1 ≤ W := by omega
  omega

end Lax185574Proofs.MainRam
