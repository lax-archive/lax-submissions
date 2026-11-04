import Lax185574Proofs.ResolveRam.Glue.CR1Kit
import Lax185574Proofs.ResolveRam.Glue.PCT5
import Lax185574Proofs.ResolveRam.Glue.PLv2

/-!
The first part of the round of the glue program of lem:resolve-lift that
receives the answer of the scatter type (round `1`).

`r1A z` writes into the buffer the lengths of the levels `n :: 0^z`
(`llP`), the color table (piece CT) and, after a room check, the item
words of level `0` (piece LV0). After a second room check it appends
these words to the library, then the words of the scatter type from the
answer, and keeps their number in `NSG` (`r1A_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoPlus)

/-- The zeros of the lengths of the levels. -/
def llZ : ℕ → Com
  | 0 => .skip
  | _ => push1 "OB" "po" (.lit 0)

/-- Write the frame of the lengths `n :: 0^z` into the buffer. -/
def llP (z : ℕ) : Com :=
  .seq (push1 "OB" "po" (.lit (z + 1))) (.seq (push1 "OB" "po" (.var "gn")) (llZ z))

theorem llP_run {W z m : ℕ} {τ : Env} (hz : z ≤ 1) (hF : Filled "OB" "po" [] τ) (hgn : τ.vars "gn" = m)
    (hOB : (τ.arrs "OB").length = W + 1) (h4 : 4 < W) (hm : m < W + 1) :
    ∃ τ', Run (W + 1) (llP z) τ τ' 30 ∧ Filled "OB" "po" (frames [m :: List.replicate z 0]) τ' ∧
      (∀ y, y ≠ "po" → τ'.vars y = τ.vars y) ∧ (∀ b, b ≠ "OB" → τ'.arrs b = τ.arrs b) ∧
      (τ'.arrs "OB").length = W + 1 ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  obtain ⟨τ1, r1, F1, v1, a1, l1, o1, i1⟩ := push1_run (B := W + 1) (e := .lit (z + 1)) (v := z + 1) hF
    (evalB_lit (by omega)) (by rw [hOB]; simp) (by simp; omega)
  obtain ⟨τ2, r2, F2, v2, a2, l2, o2, i2⟩ := push1_run (B := W + 1) (e := .var "gn") (v := m) F1
    (ev_var (by rw [v1 "gn" (by decide), hgn]) hm) (by rw [l1, hOB]; simp; omega) (by simp; omega)
  rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl
  · refine ⟨τ2, (Run.seq r1 (Run.seq r2 (Run.skip (σ := τ2)))).mono ?_, by simpa [frames] using F2,
      fun y hy => by rw [v2 y hy, v1 y hy], fun b hb => by rw [a2 b hb, a1 b hb], by rw [l2, l1, hOB],
      by rw [o2, o1], by rw [i2, i1]⟩
    simp [Expr.size]
  · obtain ⟨τ3, r3, F3, v3, a3, l3, o3, i3⟩ := push1_run (B := W + 1) (e := .lit 0) (v := 0) F2
      (evalB_lit (by omega)) (by rw [l2, l1, hOB]; simp; omega) (by simp; omega)
    refine ⟨τ3, (Run.seq r1 (Run.seq r2 r3)).mono ?_, by simpa [frames] using F3,
      fun y hy => by rw [v3 y hy, v2 y hy, v1 y hy], fun b hb => by rw [a3 b hb, a2 b hb, a1 b hb],
      by rw [l3, l2, l1, hOB], by rw [o3, o2, o1], by rw [i3, i2, i1]⟩
    simp [Expr.size]

/-- The first part of round `1`. -/
noncomputable def r1A (z : ℕ) : Com :=
  .seq (llP z) (.seq ctCmd (.seq rmLs (gate (.seq lv0Cmd (.seq rmLs (gate
    (.seq (asgs [("ls", .lit 0), ("lN", .add (.var "pc") (.lit 2))]) (.seq (lbFr "OB")
    (.seq (asgs [("ls", .lit (preLen .stp + 1)), ("lN", .get "y" (.lit (preLen .stp))),
      ("NSG", .get "y" (.lit (preLen .stp)))]) (lbFr "y"))))))))))

/-- The scalars that `r1A` may write. -/
def r1AV : List String :=
  ["po", "ls", "lN", "NSG", "fk", "ci", "lt", "m", "lL", "pc"] ++ ctCV ++ rmLs.wvars ++ lv0V

/-- The constant of the piece CT. -/
noncomputable def cCT : ℕ := ctCmd_spec.choose

/-- The constant of the piece LV0. -/
noncomputable def cLV : ℕ := lv0Cmd_spec.choose

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The words that `r1A` writes into the buffer. -/
noncomputable def midR1 (z : ℕ) : List (List ℕ) := [n :: List.replicate z 0, ctW G P Q] ++ lvW G P Q s k₀ q₀ 0

/-- The library after `r1A`. -/
noncomputable def libR1 (z : ℕ) : List (List ℕ) :=
  (swAt G P Q s k₀ q₀ .stp).ws ++ midR1 G P Q s k₀ q₀ z ++ (Lax185574.ScatterTypes.stp G k₀ q₀).words

/-- The cost of `r1A`. -/
noncomputable def kR1A (z : ℕ) : ℕ :=
  cCT * ((xIn G k₀ q₀ P Q s).length + 1) + cLV * ((xIn G k₀ q₀ P Q s).length + 1) +
    60 * (rY G k₀ q₀ .stp).length + 60 * (total (libR1 G P Q s k₀ q₀ z) + (libR1 G P Q s k₀ q₀ z).length) + 3000

theorem ws_stp : (swAt G P Q s k₀ q₀ .stp).ws = [[], [], [], []] := by simp [swAt, SW.ws]

theorem scW_stp : scW G P Q s k₀ q₀ .stp = [0, ySz (xIn G k₀ q₀ P Q s), (xIn G k₀ q₀ P Q s).length, n, P, Q,
    if s then 1 else 0, k₀, q₀, 0, 0, 0, 0, 0, 0, 0, 0] := by simp [scW, curW, swAt]

theorem winOf_stp : winOf G P Q s k₀ q₀ .stp = (xIn G k₀ q₀ P Q s).length := by simp [winOf]

theorem lvW_zero : lvW G P Q s k₀ q₀ 0 = (List.finRange n).map fun b => itemW ((0, 0), family G k₀ q₀ b) := by
  simp [lvW, lvR, levels, famItems]

/-- The answer of the scatter type. -/
theorem rY_stp : ∃ pre, rY G k₀ q₀ .stp = pre ++ ((Lax185574.ScatterTypes.stp G k₀ q₀).words.length ::
    frames (Lax185574.ScatterTypes.stp G k₀ q₀).words) ∧ pre.length = preLen .stp := by
  obtain ⟨pre, post, h, h1, h2⟩ := rY_split G k₀ q₀ .stp
  have hp : post = [] := by
    have : dLen .stp = preLen .stp := by simp [dLen, preLen]
    rw [this, ← h1] at h2
    exact List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨pre, ?_, h1⟩
  rw [h, hp, List.append_nil]
  congr 1
  exact toWord_words _

theorem mem_frames_of {L : List (List ℕ)} {w : List ℕ} {v : ℕ} (hw : w ∈ L) (hv : v ∈ w) : v ∈ frames L :=
  List.mem_flatten.2 ⟨w.length :: w, List.mem_map.2 ⟨w, hw, rfl⟩, List.mem_cons_of_mem _ hv⟩

theorem filled_val {W : ℕ} {F : List ℕ} {τ : Env} (hF : Filled "OB" "po" F τ) (hl : EnvLt (W + 1) τ) :
    ∀ v ∈ F, v ≤ W := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have := hl.arrs "OB" _ (List.mem_of_getElem? (hF.get j hj))
  omega

set_option maxHeartbeats 3200000 in
/-- **The first part of round `1`.** -/
theorem r1A_run {z W R : ℕ} {τ0 : Env} (hz : z ≤ 1) (hR : 1 ≤ R) (hkq : kq0 < W)
    (P0 : PreR W R (scW G P Q s k₀ q₀ .stp) (swAt G P Q s k₀ q₀ .stp).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp)) (rY G k₀ q₀ .stp) τ0)
    (hov : τ0.vars "ovf" = 0) :
    ∃ τ K, Run (W + 1) (r1A z) τ0 τ K ∧ K ≤ kR1A G P Q s k₀ q₀ z ∧
      (τ.vars "ovf" = 0 → Lib (libR1 G P Q s k₀ q₀ z) τ ∧
        τ.vars "NSG" = (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) ∧
      (∀ y, y ∉ r1AV → τ.vars y = τ0.vars y) ∧ τ.arrs "y" = τ0.arrs "y" ∧ ArrW W τ ∧
      EnvLt (W + 1) τ ∧ τ.out = τ0.out ∧ τ.inp = τ0.inp ∧
      (∀ Lb : List (List ℕ), (libR1 G P Q s k₀ q₀ z).Sublist Lb →
        BigRoom W R Lb (rY G k₀ q₀ .stp) (τ0.vars "nx") (τ0.vars "mw") → τ.vars "ovf" = 0) := by
  set x := xIn G k₀ q₀ P Q s with hxdef
  set b := rY G k₀ q₀ .stp with hbdef
  set ws := (swAt G P Q s k₀ q₀ .stp).ws with hwsdef
  set ct := ctW G P Q with hct
  set LV := lvW G P Q s k₀ q₀ 0 with hLV
  set SG := (Lax185574.ScatterTypes.stp G k₀ q₀).words with hSG
  set LLw : List ℕ := n :: List.replicate z 0 with hLLw
  set M := midR1 G P Q s k₀ q₀ z with hM
  have hMd : M = [LLw, ct] ++ LV := rfl
  have hlib : libR1 G P Q s k₀ q₀ z = ws ++ M ++ SG := rfl
  have hws : ws = [[], [], [], []] := ws_stp G P Q s k₀ q₀
  have hwt : total ws = 0 := by rw [hws]; rfl
  have hwl : ws.length = 4 := by rw [hws]; rfl
  have hl0 := P0.hlt
  have hkq24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  have hsc : ∀ j (h : j < 17), τ0.vars (scR[j]'(by simp [scR]; omega)) =
      (scW G P Q s k₀ q₀ .stp).getD j 0 := P0.hsc
  have hnx : τ0.vars "nx" = x.length := by simpa [scR, scW_stp] using hsc 2 (by omega)
  have hgn : τ0.vars "gn" = n := by simpa [scR, scW_stp] using hsc 3 (by omega)
  have hgP : τ0.vars "gP" = P := by simpa [scR, scW_stp] using hsc 4 (by omega)
  have hgQ : τ0.vars "gQ" = Q := by simpa [scR, scW_stp] using hsc 5 (by omega)
  have hx : PreAt "x" x τ0 := by
    have := P0.hx; rwa [winOf_stp, List.take_length] at this
  have hmw : τ0.vars "mw" = maxEntry x := by
    have := P0.hmw; rwa [winOf_stp, List.take_length] at this
  have hroom0 : RoomOK W R τ0 ws b := by
    have := P0.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hS0 := room_bound hroom0 hR
  obtain ⟨hS01, hS02, hS03, hS04⟩ := sOfV_ge (τ := τ0) (ws := ws) (b := b)
  have hbW : b.length < W + 1 := by rw [← P0.hbl]; exact hl0.vars _
  have hnW : n < W + 1 := by rw [← hgn]; exact hl0.vars _
  have hbv : ∀ v ∈ b, v ≤ W := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := P0.hy j hj
    have := hl0.arrs "y" _ (List.mem_of_getElem? (by simpa using this))
    omega
  -- step 1: the lengths of the levels
  obtain ⟨τ1, r1, F1, v1, a1, l1, o1, i1⟩ := llP_run (W := W) (z := z) (m := n) (τ := τ0) hz
    ⟨by simp [P0.hpo], fun i h => absurd h (by simp)⟩ hgn (P0.harr "OB") (by omega) hnW
  have ar1 : ArrW W τ1 := fun b' => by
    by_cases h : b' = "OB"
    · subst h; exact l1
    · rw [a1 b' h]; exact P0.harr b'
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hl0
  -- step 2: the color table
  have hroom1 : Room W 0 (ySz x + (frames [LLw]).length) := by
    refine room_of_ok hroom0 (by omega) ?_
    have : (frames [LLw]).length = z + 2 := by simp [frames, hLLw]; try omega
    rw [this]
    have : ySz x = x.length + maxEntry x + 1 := rfl
    omega
  obtain ⟨τ2, r2, F2, P2⟩ := ctCmd_spec.choose_spec W k₀ q₀ G P Q s τ1 (frames [LLw])
    (by rw [v1 "W" (by decide), P0.hW]) ar1 (fun j hj => by rw [a1 "x" (by decide)]; exact hx j hj)
    (by rw [v1 "nx" (by decide), hnx]) (by rw [v1 "gn" (by decide), hgn]) (by rw [v1 "gP" (by decide), hgP])
    (by rw [v1 "gQ" (by decide), hgQ]) F1 hroom1
  change Run (W + 1) ctCmd τ1 τ2 (cCT * (x.length + 1)) at r2
  have nV : ∀ y, y ∉ r1AV → y ≠ "po" ∧ y ∉ ctCV ∧ y ∉ rmLs.wvars ∧ y ∉ lv0V ∧
      y ∉ ["ls", "lN", "NSG", "fk", "ci", "lt", "m", "lL"] := by
    intro y hy
    refine ⟨fun h => hy (by simp [r1AV, h]), fun h => hy (by simp [r1AV, h]),
      fun h => hy (by simp [r1AV, h]), fun h => hy (by simp [r1AV, h]), fun h => hy ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have fr2 : ∀ y, y ≠ "po" → y ∉ ctCV → τ2.vars y = τ0.vars y := fun y h1 h2 => by
    rw [P2.vars y h2, v1 y h1]
  have ka2 : ∀ b', b' ∈ keepA → τ2.arrs b' = τ0.arrs b' := fun b' hb => by
    rw [P2.arrs b' hb, a1 b' (by simp [keepA] at hb; rcases hb with h | h | h | h | h <;> subst h <;> decide)]
  have ar2 : ArrW W τ2 := fun b' => by rw [P2.len]; exact ar1 b'
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt r2 hl1
  have L2 : Lib ws τ2 := P0.hlib.of (fr2 "m" (by decide) (by decide)) (fr2 "lt" (by decide) (by decide))
    (ka2 "a" (by decide)) (ka2 "st" (by decide)) (ka2 "ln" (by decide))
  have hz0 : τ0.vars "z0" = 0 := by simpa [scR, scW_stp] using hsc 0 (by omega)
  have hy2 : SegAt "y" 0 b τ2 := fun j hj => by rw [ka2 "y" (by decide)]; exact P0.hy j hj
  have hct1 : (frames [ct]) = ct.length :: ct := by simp [frames]
  set pre := frames [LLw] ++ (ct.length :: ct) with hpre
  have hprel : pre.length = z + 3 + ct.length := by simp [pre, frames, hLLw]; omega
  -- step 3: the room check
  obtain ⟨τ3, r3, ov3, f3, a3, u3, i3⟩ := rmLs_run (R := R) (ws := ws) (b := b) (τ := τ2)
    (by rw [fr2 "W" (by decide) (by decide), P0.hW]) (by omega)
    (by rw [fr2 "rR" (by decide) (by decide), P0.hrR]) L2 (by rw [fr2 "z0" (by decide) (by decide), hz0])
    (by rw [fr2 "bl" (by decide) (by decide), P0.hbl]) hy2 ar2 hl2
  rw [fr2 "ovf" (by decide) (by decide), hov] at ov3
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have hnx2 : τ2.vars "nx" = τ0.vars "nx" := fr2 "nx" (by decide) (by decide)
  have hmw2 : τ2.vars "mw" = τ0.vars "mw" := fr2 "mw" (by decide) (by decide)
  have hpo2 : τ2.vars "po" = pre.length := F2.pos
  have hsubW : ∀ Lb, (libR1 G P Q s k₀ q₀ z).Sublist Lb → ws.Sublist Lb := fun Lb h =>
    ((List.sublist_append_left ws M).trans (List.sublist_append_left _ SG)).trans h
  have hsubM : ∀ Lb, (libR1 G P Q s k₀ q₀ z).Sublist Lb → M.Sublist Lb := fun Lb h =>
    ((List.sublist_append_right ws M).trans (List.sublist_append_left _ SG)).trans h
  have htM : total M = LLw.length + ct.length + total LV := by
    rw [hMd, total_append, total_cons, total_cons]; simp [total]
  have hLVl : LV.length = n := by rw [hLV, lvW_zero]; simp
  have hMl : M.length = n + 2 := by rw [hMd]; simp [hLVl]; try omega
  have hLLl : LLw.length = z + 1 := by simp [hLLw]
  have hk : kR1A G P Q s k₀ q₀ z = cCT * (x.length + 1) + cLV * (x.length + 1) + 60 * b.length +
      60 * (total M + total SG + M.length + SG.length + 4) + 3000 := by
    unfold kR1A
    rw [hlib, total_append, total_append, hwt, List.length_append, List.length_append, hwl]
    ring
  by_cases hr3 : RoomOK W R τ2 ws b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ2 ws b * sOfV τ2 ws b < W from hr3)] at ov3
    have hrun : Run (W + 1) (r1A z) τ0 τ3 _ :=
      Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_skip (by rw [ov3]; omega) (by rw [ov3]; omega))))
    refine ⟨τ3, _, hrun, ?_, fun h => by rw [ov3] at h; omega, fun y hy => ?_, by rw [a3, ka2 "y" (by decide)],
      fun b' => by rw [a3]; exact ar2 b', hl3, by rw [u3, P2.out, o1], by rw [i3, P2.inp, i1],
      fun Lb hsub hB => absurd (roomOK_of_big (hsubW Lb hsub) ?_ (by rw [hnx2, hmw2]; exact hB)) hr3⟩
    · rw [hk, hwt]
      generalize cCT * (x.length + 1) = A
      generalize cLV * (x.length + 1) = B
      generalize b.length = bl
      generalize total M + total SG + M.length + SG.length + 4 = T
      clear * -
      omega
    · obtain ⟨h1, h2, h3, -, -⟩ := nV y hy
      rw [f3 y h3, fr2 y h1 h2]
    · rw [hpo2, hprel]
      have := total_le_of_sub (hsubM Lb hsub)
      omega
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ2 ws b * sOfV τ2 ws b < W from hr3)] at ov3
  have hS3 := room_bound hr3 hR
  obtain ⟨hS31, hS32, hS33, hS34⟩ := sOfV_ge (τ := τ2) (ws := ws) (b := b)
  have fr3 : ∀ y, y ≠ "po" → y ∉ ctCV → y ∉ rmLs.wvars → τ3.vars y = τ0.vars y := fun y h1 h2 h3 => by
    rw [f3 y h3, fr2 y h1 h2]
  have ar3 : ArrW W τ3 := fun b' => by rw [a3]; exact ar2 b'
  have F3 : Filled "OB" "po" pre τ3 := ⟨by rw [f3 "po" (by decide), F2.pos], fun j hj => by
    rw [a3]; exact F2.get j hj⟩
  -- step 4: the item words of level 0
  have hroom4 : Room W 0 (ySz x + pre.length) := by
    refine room_of_ok hr3 (by omega) ?_
    have : ySz x = x.length + maxEntry x + 1 := rfl
    rw [hnx2, hnx, hpo2] at hS31
    rw [hmw2, hmw] at hS34
    omega
  obtain ⟨τ4, r4, F4, pc4, P4⟩ := lv0Cmd_spec.choose_spec W k₀ q₀ G P Q s τ3 pre
    (by rw [fr3 "W" (by decide) (by decide) (by decide), P0.hW]) ar3
    (fun j hj => by rw [a3, ka2 "x" (by decide)]; exact hx j hj)
    (by rw [fr3 "nx" (by decide) (by decide) (by decide), hnx]) (by rw [fr3 "gn" (by decide) (by decide) (by decide), hgn])
    F3 hroom4
  change Run (W + 1) lv0Cmd τ3 τ4 (cLV * (x.length + 1)) at r4
  rw [← lvW_zero] at F4
  have hFM : pre ++ frames LV = frames M := by
    rw [hMd, frames_append, hpre, ← hct1, ← frames_append]; rfl
  rw [hFM] at F4
  have fr4 : ∀ y, y ≠ "po" → y ∉ ctCV → y ∉ rmLs.wvars → y ∉ lv0V → τ4.vars y = τ0.vars y :=
    fun y h1 h2 h3 h4 => by rw [P4.vars y h4, fr3 y h1 h2 h3]
  have ka4 : ∀ b', b' ∈ keepA → τ4.arrs b' = τ0.arrs b' := fun b' hb => by
    rw [P4.arrs b' hb, a3, ka2 b' hb]
  have ar4 : ArrW W τ4 := fun b' => by rw [P4.len]; exact ar3 b'
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have L4 : Lib ws τ4 := P0.hlib.of (fr4 "m" (by decide) (by decide) (by decide) (by decide))
    (fr4 "lt" (by decide) (by decide) (by decide) (by decide))
    (ka4 "a" (by decide)) (ka4 "st" (by decide)) (ka4 "ln" (by decide))
  have hpo4 : τ4.vars "po" = total M + M.length := by rw [F4.pos, length_frames]
  -- step 5: the second room check
  obtain ⟨τ5, r5, ov5, f5, a5, u5, i5⟩ := rmLs_run (R := R) (ws := ws) (b := b) (τ := τ4)
    (by rw [fr4 "W" (by decide) (by decide) (by decide) (by decide), P0.hW]) (by omega)
    (by rw [fr4 "rR" (by decide) (by decide) (by decide) (by decide), P0.hrR]) L4
    (by rw [fr4 "z0" (by decide) (by decide) (by decide) (by decide), hz0])
    (by rw [fr4 "bl" (by decide) (by decide) (by decide) (by decide), P0.hbl])
    (fun j hj => by rw [ka4 "y" (by decide)]; exact P0.hy j hj) ar4 hl4
  rw [P4.vars "ovf" (by decide), ov3] at ov5
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 hl4
  have hnx4 : τ4.vars "nx" = τ0.vars "nx" := fr4 "nx" (by decide) (by decide) (by decide) (by decide)
  have hmw4 : τ4.vars "mw" = τ0.vars "mw" := fr4 "mw" (by decide) (by decide) (by decide) (by decide)
  by_cases hr5 : RoomOK W R τ4 ws b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ4 ws b * sOfV τ4 ws b < W from hr5)] at ov5
    have hrun : Run (W + 1) (r1A z) τ0 τ5 _ :=
      Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_run ov3 (by omega) (Run.seq r4 (Run.seq r5
        (gate_skip (by rw [ov5]; omega) (by rw [ov5]; omega)))))))
    refine ⟨τ5, _, hrun, ?_, fun h => by rw [ov5] at h; omega, fun y hy => ?_, by rw [a5, ka4 "y" (by decide)],
      fun b' => by rw [a5]; exact ar4 b', hl5, by rw [u5, P4.out, u3, P2.out, o1], by rw [i5, P4.inp, i3, P2.inp, i1],
      fun Lb hsub hB => absurd (roomOK_of_big (hsubW Lb hsub) ?_ (by rw [hnx4, hmw4]; exact hB)) hr5⟩
    · rw [hk, hwt]
      generalize cCT * (x.length + 1) = A
      generalize cLV * (x.length + 1) = B
      generalize b.length = bl
      generalize total M + total SG + M.length + SG.length + 4 = T
      clear * -
      omega
    · obtain ⟨h1, h2, h3, h4, -⟩ := nV y hy
      rw [f5 y h3, fr4 y h1 h2 h3 h4]
    · rw [hpo4]
      have := total_le_of_sub (hsubM Lb hsub)
      have := (hsubM Lb hsub).length_le
      omega
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ4 ws b * sOfV τ4 ws b < W from hr5)] at ov5
  have hS5 := room_bound hr5 hR
  obtain ⟨hS51, hS52, hS53, hS54⟩ := sOfV_ge (τ := τ4) (ws := ws) (b := b)
  rw [hpo4, hwt, hwl] at hS51
  have fr5 : ∀ y, y ≠ "po" → y ∉ ctCV → y ∉ rmLs.wvars → y ∉ lv0V → τ5.vars y = τ0.vars y :=
    fun y h1 h2 h3 h4 => by rw [f5 y h3, fr4 y h1 h2 h3 h4]
  have ar5 : ArrW W τ5 := fun b' => by rw [a5]; exact ar4 b'
  have L5 : Lib ws τ5 := L4.of (f5 "m" (by decide)) (f5 "lt" (by decide)) (by rw [a5]) (by rw [a5]) (by rw [a5])
  -- step 6: the words of the buffer
  have hpc5 : τ5.vars "pc" = n := by rw [f5 "pc" (by decide), pc4]
  obtain ⟨τ6, r6, s6, g6, a6, o6, i6⟩ := asgs_run (B := W + 1) (τ := τ5)
    (l := [("ls", .lit 0), ("lN", .add (.var "pc") (.lit 2))]) (f := fun y => if y = "ls" then 0 else n + 2)
    (by
      intro pr hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · simp only [if_true]; exact evalB_lit (by omega)
      · simp only [show ("lN" : String) ≠ "ls" by decide, if_false]
        exact ev_add (ev_var hpc5 (by omega)) (evalB_lit (by omega)) (by omega))
    (by simp [exRv])
  have L6 : Lib ws τ6 := L5.of (g6 "m" (by decide)) (g6 "lt" (by decide)) (by rw [a6]) (by rw [a6]) (by rw [a6])
  have hl6 : EnvLt (W + 1) τ6 := Run.envLt r6 hl5
  have hseg6 : SegAt "OB" 0 (frames M) τ6 := fun j hj => by
    rw [a6, a5, Nat.zero_add]; exact F4.get j hj
  have hMv : ∀ w ∈ M, ∀ v ∈ w, v ≤ W := fun w hw v hv =>
    filled_val F4 hl4 v (mem_frames_of hw hv)
  obtain ⟨τ7, r7, L7, ls7, f7, a7, l7, o7, i7⟩ := lbFr_run (W := W) (src := "OB") (L := M) (p := 0) L6
    (by rw [s6 "ls" (by simp)]; simp) (by rw [s6 "lN" (by simp), hMl]; simp) hseg6 (by decide)
    (by rw [a6, ar5 "a"]; omega) (by rw [a6, ar5 "st"]; omega) (by rw [a6, ar5 "ln"]; omega)
    (by omega) hMv
  have hl7 : EnvLt (W + 1) τ7 := Run.envLt r7 hl6
  -- step 7: the words of the scatter type
  obtain ⟨pB, hbsp, hpBl⟩ := rY_stp G k₀ q₀
  rw [← hSG] at hbsp
  have hbl' : b.length = preLen .stp + 1 + (frames SG).length := by
    rw [hbdef, hbsp]; simp only [List.length_append, List.length_cons, hpBl]; omega
  have hy7 : τ7.arrs "y" = τ0.arrs "y" := by rw [a7 "y" (by decide), a6, a5, ka4 "y" (by decide)]
  have hyb : ∀ j (hj : j < b.length), (τ7.arrs "y")[j]? = some b[j] := fun j hj => by
    rw [hy7]; simpa using P0.hy j hj
  have hb0 : b[preLen .stp]'(by omega) = SG.length := by
    simp only [hbdef, hbsp]
    rw [List.getElem_append_right (by omega)]
    simp [hpBl]
  have hbS : ∀ j (hj : j < (frames SG).length), b[preLen .stp + 1 + j]'(by omega) = (frames SG)[j] := by
    intro j hj
    simp only [hbdef, hbsp]
    rw [List.getElem_append_right (by omega)]
    simp [hpBl, show preLen .stp + 1 + j - preLen .stp = j + 1 by omega]
  have hSGv : SG.length < W + 1 := by
    have := hbv _ (List.getElem_mem (show preLen .stp < b.length by omega)); rw [hb0] at this; omega
  have evy : (Expr.get "y" (.lit (preLen .stp))).evalB (W + 1) τ7 = some SG.length :=
    evalB_get (evalB_lit (by omega)) (by rw [hyb _ (by omega), hb0]) hSGv
  obtain ⟨τ8, r8, s8, g8, a8, o8, i8⟩ := asgs_run (B := W + 1) (τ := τ7)
    (l := [("ls", .lit (preLen .stp + 1)), ("lN", .get "y" (.lit (preLen .stp))),
      ("NSG", .get "y" (.lit (preLen .stp)))]) (f := fun y => if y = "ls" then preLen .stp + 1 else SG.length)
    (by
      intro pr hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simp only [if_true]; exact evalB_lit (by omega)
      · simp only [show ("lN" : String) ≠ "ls" by decide, if_false]; exact evy
      · simp only [show ("NSG" : String) ≠ "ls" by decide, if_false]; exact evy)
    (by simp [exRv])
  have L8 : Lib (ws ++ M) τ8 := L7.of (g8 "m" (by decide)) (g8 "lt" (by decide)) (by rw [a8]) (by rw [a8])
    (by rw [a8])
  have hl8 : EnvLt (W + 1) τ8 := Run.envLt r8 hl7
  have hseg8 : SegAt "y" (preLen .stp + 1) (frames SG) τ8 := fun j hj => by
    rw [a8, hyb _ (by omega), hbS j hj]
  have hSGb : ∀ w ∈ SG, ∀ v ∈ w, v ≤ W := fun w hw v hv => by
    have hm := mem_frames_of hw hv
    apply hbv
    rw [hbdef, hbsp]; simp [hm]
  have hAr7 : ∀ b', (τ7.arrs b').length = W + 1 := fun b' => by rw [l7, a6]; exact ar5 b'
  have hwM : total (ws ++ M) + (ws ++ M).length = total M + M.length + 4 := by
    rw [total_append, hwt, List.length_append, hwl]; omega
  have hfS := length_frames SG
  obtain ⟨τ9, r9, L9, ls9, f9, a9, l9, o9, i9⟩ := lbFr_run (W := W) (src := "y") (ws := ws ++ M) (L := SG)
    (p := preLen .stp + 1) L8 (by rw [s8 "ls" (by simp)]; simp)
    (by rw [s8 "lN" (by simp)]; simp) hseg8 (by decide)
    (by rw [a8, hAr7 "a"]; omega) (by rw [a8, hAr7 "st"]; omega) (by rw [a8, hAr7 "ln"]; omega)
    (by omega) hSGb
  have hrun : Run (W + 1) (r1A z) τ0 τ9 _ :=
    Run.seq r1 (Run.seq r2 (Run.seq r3 (gate_run ov3 (by omega) (Run.seq r4 (Run.seq r5
      (gate_run ov5 (by omega) (Run.seq r6 (Run.seq r7 (Run.seq r8 r9)))))))))
  have hov9 : τ9.vars "ovf" = 0 := by
    rw [f9 "ovf" (by decide), g8 "ovf" (by decide), f7 "ovf" (by decide), g6 "ovf" (by decide), ov5]
  refine ⟨τ9, _, hrun, ?_, fun _ => ⟨by rw [hlib]; exact L9, ?_⟩, fun y hy => ?_, ?_,
    fun b' => by rw [l9, a8]; exact hAr7 b', Run.envLt hrun hl0, ?_, ?_, fun _ _ _ => hov9⟩
  · rw [hk]
    simp only [asgK, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [hwt]
    omega
  · rw [f9 "NSG" (by decide), s8 "NSG" (by simp)]; simp
  · obtain ⟨h1, h2, h3, h4, h5⟩ := nV y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h5
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := h5
    rw [f9 y (by simp [n4, n5, n7, n8, n6, n1]), g8 y (by simp [n1, n2, n3]), f7 y (by simp [n4, n5, n7, n8, n6, n1]),
      g6 y (by simp [n1, n2]), fr5 y h1 h2 h3 h4]
  · rw [a9 "y" (by decide), a8, hy7]
  · rw [o9, o8, o7, o6, u5, P4.out, u3, P2.out, o1]
  · rw [i9, i8, i7, i6, i5, P4.inp, i3, P2.inp, i1]

end Lax185574Proofs.ResolveRam.Glue
