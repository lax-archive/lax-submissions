import Lax185574Proofs.ResolveRam.Glue.Room
import Lax185574Proofs.ResolveRam.Glue.EnvLt

/-!
The room check of a later round with saturating sums.

`rmLs` computes the size `sOf` of the library, the answer, the buffer,
the input and the maxima as `rmL` does, but adds with saturation, so its
run needs no bound on the sizes: all values of a bounded run are below
the bound (`EnvLt`). It sets `ovf` unless `2^24 R^4 S^2 < W`, with the
size `S` (`rmLs_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- The maxima of the library and the answer, and of the window. -/
def rmM : Com :=
  .seq (mxSeg "a" "z0" "lt") (.seq (.assign "rA" (.var "mx")) (.seq (mxSeg "y" "z0" "bl")
  (.seq (.assign "rY" (.var "mx")) max3)))

/-- `rS := rS + x₁ + … ` with saturation. -/
def satSum : List String → Com
  | [] => .skip
  | x :: xs => .seq (satAdd "rS" x "rS") (satSum xs)

/-- The size, with saturation. -/
def rmSs : Com :=
  .seq rmM (.seq (.assign "rS" (.lit 64)) (satSum ["lt", "lt", "m", "m", "bl", "po", "nx", "rM"]))

/-- The room check during a round, with saturating sums. -/
def rmLs : Com := .seq rmSs rmB

theorem satSum_run {W : ℕ} {xs : List String} {τ : Env} (hW : τ.vars "W" = W) (hx : "rS" ∉ xs)
    (hv : ∀ x ∈ xs, τ.vars x ≤ W) (hS : τ.vars "rS" ≤ W) :
    ∃ τ', Run (W + 1) (satSum xs) τ τ' (10 * xs.length + 1) ∧
      Only "rS" (min (τ.vars "rS" + (xs.map τ.vars).sum) W) τ τ' := by
  induction xs generalizing τ with
  | nil =>
    exact ⟨τ, Run.skip.mono (by simp), ⟨by simp; omega, fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons x xs ih =>
    have hxS : x ≠ "rS" := fun h => hx (by simp [h])
    have r1 := satAdd_run (B := W + 1) (x := "rS") (y := x) (z := "rS") hW (by omega) hS (hv x (by simp))
    set τ1 := τ.setVar "rS" (min (τ.vars "rS" + τ.vars x) W)
    have o1 := Only.of_setVar τ "rS" (min (τ.vars "rS" + τ.vars x) W)
    obtain ⟨τ2, r2, o2⟩ := ih (τ := τ1) (by rw [o1.vars "W" (by decide), hW])
      (fun h => hx (by simp [h])) (fun y hy => by
        rw [o1.vars y (fun h => hx (by simp [← h, hy]))]; exact hv y (by simp [hy])) (by rw [o1.self]; omega)
    have hm : xs.map τ1.vars = xs.map τ.vars :=
      List.map_congr_left fun y hy => o1.vars y (fun h => hx (by simp [← h, hy]))
    refine ⟨τ2, (Run.seq r1 r2).mono (by simp; omega), ⟨?_, fun y hy => by rw [o2.vars y hy, o1.vars y hy],
      by rw [o2.arrs, o1.arrs], by rw [o2.out, o1.out], by rw [o2.inp, o1.inp]⟩⟩
    rw [o2.self, hm, o1.self]
    simp only [List.map_cons, List.sum_cons]
    rw [min_add_right]; congr 1; omega

theorem seg_y {b : List ℕ} {τ : Env} (hy : SegAt "y" 0 b τ) : seg (τ.arrs "y") 0 b.length = b := by
  apply List.ext_getElem?; intro j
  simp only [seg, List.drop_zero]
  rcases Nat.lt_or_ge j b.length with h | h
  · rw [List.getElem?_take_of_lt h, show (τ.arrs "y")[j]? = some b[j] by simpa using hy j h,
      List.getElem?_eq_getElem h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none h]

theorem rmM_run {W : ℕ} {ws : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hL : Lib ws τ) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ)
    (harr : ArrW W τ) (he : EnvLt (W + 1) τ) :
    ∃ τ', Run (W + 1) rmM τ τ' (30 * total ws + 30 * b.length + 100) ∧
      τ'.vars "rM" = max (max (τ.vars "mw") (maxEntry ws.flatten)) (maxEntry b) ∧
      (∀ y, y ∉ ["mx", "ci", "rA", "rY", "rM"] → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hT := hL.lt
  have hTW : total ws ≤ W := by have := he.vars "lt"; omega
  have hbW : b.length ≤ W := by have := he.vars "bl"; omega
  have hsa := seg_lib hL.at_
  have hsy := seg_y hy
  have hva : ∀ v ∈ ws.flatten, v < W + 1 := fun v hv => he.arrs "a" v (by
    rw [← hsa, seg] at hv; exact List.mem_of_mem_drop (List.mem_of_mem_take hv))
  have hvb : ∀ v ∈ b, v < W + 1 := fun v hv => he.arrs "y" v (by
    rw [← hsy, seg] at hv; exact List.mem_of_mem_drop (List.mem_of_mem_take hv))
  have hmA : maxEntry ws.flatten ≤ W := maxEntry_le fun v hv => by have := hva v hv; omega
  have hmB : maxEntry b ≤ W := maxEntry_le fun v hv => by have := hvb v hv; omega
  obtain ⟨τ1, r1, m1⟩ := mxSeg_run (B := W + 1) (ar := "a") (s := "z0") (l := "lt") (σ := τ)
    (a := 0) (N := total ws) hz hT (by decide) (by decide) (by decide) (by decide)
    (by rw [harr]; omega) (by omega) (by rw [hsa]; exact hva)
  rw [hsa] at m1
  have a1 : τ1.arrs = τ.arrs := r1.frame_arrs_eqOn (by simp [mxSeg, mxBody, forUp, Com.warrs])
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "rA") (ev_var (B := W + 1) m1 (by omega))
  obtain ⟨τ3, r3, m3⟩ := mxSeg_run (B := W + 1) (ar := "y") (s := "z0") (l := "bl") (σ := τ2)
    (a := 0) (N := b.length)
    (by simp (disch := decide) only [o2.vars, r1.frame_var "z0" (by decide), hz])
    (by simp (disch := decide) only [o2.vars, r1.frame_var "bl" (by decide), hbl])
    (by decide) (by decide) (by decide) (by decide)
    (by rw [o2.arrs, a1, harr]; omega) (by omega)
    (by rw [o2.arrs, a1, hsy]; exact hvb)
  rw [o2.arrs, a1, hsy] at m3
  obtain ⟨τ4, r4, o4⟩ := asg_run (x := "rY") (ev_var (B := W + 1) m3 (by omega))
  have e4 : ∀ y, y ∉ ["mx", "ci", "rA", "rY"] → τ4.vars y = τ.vars y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [o4.vars y hy.2.2.2, r3.frame_var y (by simp [mxSeg, mxBody, forUp, Com.wvars]; tauto),
      o2.vars y hy.2.2.1, r1.frame_var y (by simp [mxSeg, mxBody, forUp, Com.wvars]; tauto)]
  obtain ⟨τ5, r5, o5⟩ := max3_run (W := W) (τ := τ4) (a := τ.vars "mw") (b := maxEntry ws.flatten)
    (c := maxEntry b) (by rw [e4 "mw" (by decide)])
    (by rw [o4.vars "rA" (by decide), r3.frame_var "rA" (by decide), o2.self])
    o4.self ⟨by have := he.vars "mw"; omega, by omega, by omega⟩
  have hrun : Run (W + 1) rmM τ τ5 (30 * total ws + 30 * b.length + 100) := by
    unfold rmM
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono (by simp only [Expr.size]; omega)
  refine ⟨τ5, hrun, o5.self, fun y hy => ?_, ?_, hrun.out_eq (by decide), hrun.frame_inp (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [o5.vars y hy.2.2.2.2, e4 y (by simp; tauto)]
  · rw [o5.arrs, o4.arrs, r3.frame_arrs_eqOn (by simp [mxSeg, mxBody, forUp, Com.warrs]), o2.arrs, a1]

/-- The size that the room check computes, from the scalars. -/
def sOfV (τ : Env) (ws : List (List ℕ)) (b : List ℕ) : ℕ :=
  sOf (total ws) ws.length b.length (τ.vars "po") (τ.vars "nx") (τ.vars "mw") (maxEntry ws.flatten) (maxEntry b)

/-- **The room check during a round, with saturating sums.** -/
theorem rmLs_run {W R : ℕ} {ws : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (hW24 : 2 ^ 24 < W) (hR : τ.vars "rR" = min R W)
    (hL : Lib ws τ) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ)
    (harr : ArrW W τ) (he : EnvLt (W + 1) τ) :
    ∃ τ', Run (W + 1) rmLs τ τ' (30 * total ws + 30 * b.length + 500) ∧
      τ'.vars "ovf" = (if 2 ^ 24 * R * R * R * R * sOfV τ ws b * sOfV τ ws b < W
        then τ.vars "ovf" else 1) ∧
      (∀ y, y ∉ rmLs.wvars → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  obtain ⟨τ1, r1, m1, f1, a1, u1, i1⟩ := rmM_run hL hz hbl hy harr he
  obtain ⟨τ2, r2, o2⟩ := asg_run (x := "rS") (B := W + 1) (σ := τ1) (evalB_lit (n := 64) (by omega))
  have hv : ∀ y ∈ ["lt", "lt", "m", "m", "bl", "po", "nx", "rM"], τ2.vars y ≤ W := by
    intro y hy
    rw [o2.vars y (by intro h; subst h; simp at hy)]
    have := (Run.envLt r1 he).vars y; omega
  obtain ⟨τ3, r3, o3⟩ := satSum_run (W := W) (xs := ["lt", "lt", "m", "m", "bl", "po", "nx", "rM"]) (τ := τ2)
    (by rw [o2.vars "W" (by decide), f1 "W" (by decide), hW]) (by decide) hv
    (by rw [o2.self]; omega)
  have g : ∀ y, y ∉ ["mx", "ci", "rA", "rY", "rM", "rS"] → τ2.vars y = τ.vars y := fun y hy => by
    rw [o2.vars y (fun h => hy (by simp [h])), f1 y (fun h => hy (by simp at h ⊢; tauto))]
  have hS : τ3.vars "rS" = min (sOfV τ ws b) W := by
    rw [o3.self, o2.self]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [g "lt" (by decide), g "m" (by decide), g "bl" (by decide), g "po" (by decide), g "nx" (by decide),
      o2.vars "rM" (by decide), m1, hL.lt, hL.m, hbl, sOfV, sOf]
    congr 1; omega
  obtain ⟨τ4, r4, h4, f4, a4, u4, i4⟩ := rmB_run (W := W) (R := R) (S := min (sOfV τ ws b) W) (τ := τ3)
    (by rw [o3.vars "W" (by decide), g "W" (by decide), hW]) hW24
    (by rw [o3.vars "rR" (by decide), g "rR" (by decide), hR]) hS (by omega)
  have hrun : Run (W + 1) rmLs τ τ4 (30 * total ws + 30 * b.length + 500) := by
    unfold rmLs rmSs
    exact (Run.seq (Run.seq r1 (Run.seq r2 r3)) r4).mono (by simp only [Expr.size, List.length_cons, List.length_nil]; omega)
  refine ⟨τ4, hrun, ?_, fun y hy => hrun.frame_var y hy, by rw [a4, o3.arrs, o2.arrs, a1],
    by rw [u4, o3.out, o2.out, u1], by rw [i4, o3.inp, o2.inp, i1]⟩
  rw [h4, o3.vars "ovf" (by decide), g "ovf" (by decide)]
  by_cases hs : sOfV τ ws b ≤ W
  · rw [min_eq_left hs]
  · rw [min_eq_right (by omega)]
    have h1 : ¬ 2 ^ 24 * R * R * R * R * W * W < W ∨ R = 0 := by
      rcases Nat.eq_zero_or_pos R with h | h
      · exact Or.inr h
      · left; have : W ≤ 2 ^ 24 * R * R * R * R * W * W := by
          have : 1 ≤ 2 ^ 24 * R * R * R * R * W := Nat.pos_of_ne_zero (by simp; omega)
          nlinarith
        omega
    rcases h1 with h1 | h1
    · have h2 : ¬ 2 ^ 24 * R * R * R * R * sOfV τ ws b * sOfV τ ws b < W := by
        have : W * W ≤ sOfV τ ws b * sOfV τ ws b := Nat.mul_le_mul (by omega) (by omega)
        intro h; apply h1
        calc 2 ^ 24 * R * R * R * R * W * W = 2 ^ 24 * R * R * R * R * (W * W) := by ring
          _ ≤ 2 ^ 24 * R * R * R * R * (sOfV τ ws b * sOfV τ ws b) := Nat.mul_le_mul_left _ this
          _ = _ := by ring
          _ < W := h
      rw [if_neg h1, if_neg h2]
    · subst h1; simp

end Lax185574Proofs.ResolveRam.Glue
