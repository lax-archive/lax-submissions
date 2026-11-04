import Lax185574Proofs.ResolveRam.Glue.TailR
import Lax185574Proofs.ResolveRam.Glue.Top0

/-!
The start of a later round of the glue program of lem:resolve-lift.

A later round reads its input (`rdIn`), computes the radius bound
(`rmR`) and checks the room (`rmLs`); the case of the round runs only if
the check passed (`rdPre body`). `preR_run`: after the start, the
scalars of the state, the library, the answer, the window and the radius
bound are in place (`PreR`), and `ovf` is set exactly when the room
check fails. `topJ_run`: the glue command on the input of a later round
runs `rdPre body` after the tag, or sets `ovf` if `W` is not above the
constant `K`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- A later round: the start, then the case if the room check passed. -/
def rdPre (body : Com) : Com := .seq (.seq rdIn (.seq rmR rmLs)) (gate body)

/-- The environment after the start of a later round. -/
structure PreR (W R : ℕ) (sc : List ℕ) (ws : List (List ℕ)) (wx b : List ℕ) (τ : Env) : Prop where
  hW : τ.vars "W" = W
  harr : ArrW W τ
  hlt : EnvLt (W + 1) τ
  hsc : ∀ i (h : i < 17), τ.vars (scR[i]'(by simp [scR]; omega)) = sc.getD i 0
  hlib : Lib ws τ
  hbl : τ.vars "bl" = b.length
  hy : SegAt "y" 0 b τ
  hx : PreAt "x" wx τ
  hmw : τ.vars "mw" = maxEntry wx
  hrR : τ.vars "rR" = min R W
  hpo : τ.vars "po" = 0
  hout : τ.out = []
  hinp : τ.inp = []
  hroom : τ.vars "ovf" = if RoomOK W R τ ws b then 0 else 1

/-- The cost of the start of a later round. -/
def preK (wx st b : List ℕ) (k₀ q₀ W : ℕ) (ws : List (List ℕ)) : ℕ :=
  30 * (wx.length + st.length + b.length) + 100 + (23 * ((k₀ + q₀ + 1) * (q₀ + 1)) + 100) +
    (30 * total ws + 30 * b.length + 500)

set_option maxHeartbeats 400000 in
/-- **The start of a later round.** -/
theorem preR_run {W t : ℕ} {wx sc b : List ℕ} {ws : List (List ℕ)} {τ : Env}
    (hW : τ.vars "W" = W) (htg : τ.vars "tg" = t) (hwx : wx.length = t - 1) (hsc : sc.length = 17)
    (hws : 1 ≤ ws.length) (hz : sc.getD 0 0 = 0)
    (hinp : τ.inp = (sc ++ toWord ws).length :: wx ++ (sc ++ toWord ws) ++ (b.length :: b))
    (harr : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hW24 : 2 ^ 24 < W) (hpo : τ.vars "po" = 0)
    (hovf : τ.vars "ovf" = 0) (hout : τ.out = [])
    (hu : ∀ e ∈ [t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b),
      64 * e < W + 1) :
    ∃ τ' k, Run (W + 1) (.seq rdIn (.seq rmR rmLs)) τ τ' k ∧
      k ≤ preK wx (sc ++ toWord ws) b (sc.getD 7 0) (sc.getD 8 0) W ws ∧
      PreR W (Lax3.DistFO.rhoPlus (sc.getD 7 0 + 1) (sc.getD 8 0) + 2) sc ws wx b τ' := by
  obtain ⟨τ1, r1, s1, t1, m1, c1, L1, b1, y1, x1, a1, i1, u1, f1⟩ :=
    rdIn_run (W := W) htg hwx hsc hws hinp harr (by omega) hu
  have hsc1 : ∀ i (h : i < 17), τ1.vars (scR[i]'(by simp [scR]; omega)) = sc.getD i 0 := c1
  have hk : τ1.vars "gK" = sc.getD 7 0 := hsc1 7 (by omega)
  have hq : τ1.vars "gq" = sc.getD 8 0 := hsc1 8 (by omega)
  have hk64 : 64 * sc.getD 7 0 < W + 1 := hu _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))))
  have hq64 : 64 * sc.getD 8 0 < W + 1 := hu _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_append_left _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))))
  have hW1 : τ1.vars "W" = W := by rw [f1 "W" (by decide), hW]
  obtain ⟨τ2, r2, R2, f2, a2, u2, i2⟩ := rmR_run (W := W) (k₀ := sc.getD 7 0) (q₀ := sc.getD 8 0) hW1
    (by omega) hk hq (by omega)
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt r2 hl1
  have g2 : ∀ y, y ∉ rmR.wvars → y ∉ rdIn.wvars → τ2.vars y = τ.vars y := fun y h h' => by
    rw [f2 y h, f1 y h']
  have L2 : Lib ws τ2 := L1.of (f2 "m" (by decide)) (f2 "lt" (by decide)) (by rw [a2]) (by rw [a2]) (by rw [a2])
  have ar2 : ArrW W τ2 := fun b' => by rw [a2]; exact a1 b'
  obtain ⟨τ3, r3, ov3, f3, a3, u3, i3⟩ := rmLs_run (R := Lax3.DistFO.rhoPlus (sc.getD 7 0 + 1) (sc.getD 8 0) + 2)
    (by rw [f2 "W" (by decide), hW1]) hW24 R2 L2 (by rw [f2 "z0" (by decide)]; exact (hsc1 0 (by omega)).trans hz)
    (by rw [f2 "bl" (by decide), b1]) (fun j hj => by rw [a2]; exact y1 j hj) ar2 hl2
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have g3 : ∀ y, y ∉ rmLs.wvars → y ∉ rmR.wvars → y ∉ rdIn.wvars → τ3.vars y = τ.vars y := fun y h h' h'' => by
    rw [f3 y h, g2 y h' h'']
  have e3 : ∀ y, y ∉ rmLs.wvars → y ∉ rmR.wvars → τ3.vars y = τ1.vars y := fun y h h' => by
    rw [f3 y h, f2 y h']
  have hscV : ∀ y ∈ scR, y ∉ rmLs.wvars ∧ y ∉ rmR.wvars := by decide
  have hsv : sOfV τ3 ws b = sOfV τ2 ws b := by
    simp only [sOfV]; rw [f3 "po" (by decide), f3 "nx" (by decide), f3 "mw" (by decide)]
  have hrun : Run (W + 1) (.seq rdIn (.seq rmR rmLs)) τ τ3
      (preK wx (sc ++ toWord ws) b (sc.getD 7 0) (sc.getD 8 0) W ws) := by
    refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    have := min_le_left ((sc.getD 7 0 + sc.getD 8 0 + 1) * (sc.getD 8 0 + 1)) W
    simp only [preK]; omega
  refine ⟨τ3, _, hrun, le_rfl, ⟨by rw [f3 "W" (by decide), f2 "W" (by decide), hW1], fun b' => by rw [a3]; exact ar2 b',
    hl3, fun i h => ?_, ?_, by rw [e3 "bl" (by decide) (by decide), b1],
    fun j hj => by rw [a3, a2]; exact y1 j hj, fun j hj => by rw [a3, a2]; exact x1 j hj,
    by rw [e3 "mw" (by decide) (by decide), m1], by rw [f3 "rR" (by decide), R2],
    by rw [g3 "po" (by decide) (by decide) (by decide), hpo], by rw [u3, u2, u1, hout],
    by rw [i3, i2, i1], ?_⟩⟩
  · have hm : scR[i]'(by simp [scR]; omega) ∈ scR := List.getElem_mem _
    rw [e3 _ (hscV _ hm).1 (hscV _ hm).2, hsc1 i h]
  · exact L2.of (f3 "m" (by decide)) (f3 "lt" (by decide)) (by rw [a3]) (by rw [a3]) (by rw [a3])
  · rw [ov3, f2 "ovf" (by decide), f1 "ovf" (by decide), hovf]
    simp only [RoomOK, hsv]

/-- **The glue command on the input of a later round.** If `W` is above
`K`, the command runs `rJ` after the tag. -/
theorem topJ_run {K e d W t : ℕ} (rJ : Com) (ext : String → ℕ) {rest : List ℕ} (ht : t ≠ 0)
    (hW1 : 1 ≤ W) (htW : t < W + 1) :
    ∃ σ2, σ2.vars "W" = W ∧ σ2.vars "tg" = t ∧ σ2.vars "gk" = min K W ∧ σ2.vars "ovf" = 0 ∧ σ2.vars "po" = 0 ∧
      σ2.arrs = (initEnv ext (t :: rest)).arrs ∧ σ2.inp = rest ∧ σ2.out = [] ∧
      (∀ y, y ≠ "gk" → y ≠ "tg" → y ≠ "W" → σ2.vars y = 0) ∧
      (K < W → ∀ σ' k, Run (W + 1) rJ σ2 σ' k →
        Run (W + 1) (glueTop K e d rJ) ((initEnv ext (t :: rest)).setVar "W" W) σ' (k + 30 * K + 50)) ∧
      (¬ K < W → ∃ σ' k, Run (W + 1) (glueTop K e d rJ) ((initEnv ext (t :: rest)).setVar "W" W) σ' k ∧
        σ'.vars "ovf" = 1 ∧ k ≤ 30 * K + 50) := by
  set σ0 := (initEnv ext (t :: rest)).setVar "W" W
  have hW0 : σ0.vars "W" = W := by simp [σ0]
  obtain ⟨σ1, r1, h1, f1, a1, o1, i1⟩ := satLit_run (B := W + 1) (z := "gk") (by decide) (by omega)
    hW1 K σ0 hW0
  have hc : (Cond.lt (.var "gk") (.var "W")).evalB (W + 1) σ1 = some (decide (min K W < W)) :=
    evalB_condLt (ev_var (x := "gk") (v := min K W) h1 (by omega))
      (ev_var (x := "W") (v := W) (by rw [f1 "W" (by decide), hW0]) (by omega))
  set σ2 : Env := { σ1.setVar "tg" t with inp := rest }
  have r2 : Run (W + 1) (.read "tg") σ1 σ2 1 := Run.read (by rw [i1]; simp [σ0, initEnv])
  have v2 : ∀ y, y ≠ "tg" → σ2.vars y = σ1.vars y := fun y hy => by simp [σ2, hy]
  have hc2 : (Cond.eq (.var "tg") (.lit 0)).evalB (W + 1) σ2 = some false := by
    rw [evalB_condEq (ev_var (x := "tg") (v := t) (by simp [σ2]) (by omega)) (evalB_lit (n := 0) (by omega))]
    simp [ht]
  refine ⟨σ2, by rw [v2 "W" (by decide), f1 "W" (by decide), hW0], by simp [σ2],
    by rw [v2 "gk" (by decide), h1],
    by rw [v2 "ovf" (by decide), f1 "ovf" (by decide)]; simp [σ0, initEnv],
    by rw [v2 "po" (by decide), f1 "po" (by decide)]; simp [σ0, initEnv],
    by simp [σ2, a1, σ0], rfl, by simp [σ2, o1, σ0, initEnv],
    fun y h1 h2 h3 => by rw [v2 y h2, f1 y h1]; simp [σ0, initEnv, h3], fun hKW σ' k hr => ?_, fun hKW => ?_⟩
  · have hc' : (Cond.lt (.var "gk") (.var "W")).evalB (W + 1) σ1 = some true := by
      rw [hc]; simp; omega
    unfold glueTop
    refine (Run.seq r1 (Run.ite_true hc' (Run.seq r2 (Run.ite_false hc2 hr)))).mono ?_
    simp only [Cond.size, Expr.size]; omega
  · have hc' : (Cond.lt (.var "gk") (.var "W")).evalB (W + 1) σ1 = some false := by
      rw [hc]; simp; omega
    refine ⟨σ1.setVar "ovf" 1, _, ?_, by simp, le_refl _⟩
    unfold glueTop
    refine (Run.seq r1 (Run.ite_false hc' (Run.assign (evalB_lit (by omega))))).mono ?_
    simp only [Cond.size, Expr.size]; omega

end Lax185574Proofs.ResolveRam.Glue
