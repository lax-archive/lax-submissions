import Lax185574Proofs.ResolveRam.Glue.CaseKit
import Lax185574Proofs.ResolveRam.Glue.PEx7

/-!
The expansion of an item in the case of a later round that finishes an
item on the way down.

The library is the old state `ws` followed by the empty word and the
answers `C` of the compositions of the item. `finE` sets the scalars of
the piece Ex (the compositions at `cl`, `cn`, the color table at `0`,
the item word at `4 + |SG| + |FA| + |CO| + offL d + i`), checks the
room, runs the piece, checks the room again and appends the frames of
the expansion `E` to the library (`finE_run`). It sets `ovf` only when
a room check fails, which does not happen when the final library of the
round is small.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- The constants of the piece Ex. -/
noncomputable def cEx : ℕ := exCmd_spec.choose
noncomputable def aEx : ℕ := exCmd_spec.choose_spec.choose

theorem exSpec' : ∀ (W : ℕ) (τ : Env) (ws : List (List ℕ)) (pre : List ℕ)
    (oc ow cl cn i P Q sg p g k q ℓ : ℕ) (t : Node (q + 1) ℓ) (hoc : oc < ws.length)
    (how : ow < ws.length),
    τ.vars "W" = W → ArrW W τ → WordsAt ws τ → τ.vars "oc" = oc → τ.vars "ow" = ow →
    τ.vars "cl" = cl → τ.vars "cn" = cn → cl + cn ≤ ws.length → τ.vars "ii" = i →
    τ.vars "gP" = P → τ.vars "gQ" = Q → P ≤ W → Q ≤ W → τ.vars "gS" = sg → sg ≤ 1 → IsCT ws[oc] →
    ws[ow] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩) →
    (∀ w ∈ (ws.drop cl).take cn, ∃ ν : TypeTree, w = toWord ν) → Filled "OB" "po" pre τ →
    Room W (rhoPlus (k + 1) q) (ySz (toWord ws) + i + pre.length + ℓ) →
    ∃ τ', Run (W + 1) exCmd τ τ' (cEx * (ws[oc].length + 1) *
        (ws[ow].length + ℓ + total ((ws.drop cl).take cn) + cn + rhoPlus (k + 1) q + 1) ^ aEx) ∧
      Filled "OB" "po" (pre ++ frames ((exW (dwOf P Q sg ws[oc]) k q ℓ (toWord t)
        ((ws.drop cl).take cn)).map (i :: ·))) τ' ∧
      τ'.vars "pc" = (exW (dwOf P Q sg ws[oc]) k q ℓ (toWord t) ((ws.drop cl).take cn)).length ∧
      PFr exV τ τ' :=
  exCmd_spec.choose_spec.choose_spec

/-- The scalars of the piece Ex. -/
def finA1 : List (String × Expr) :=
  [("cl", .add (.var "m0") (.lit 1)), ("cn", .sub (.sub (.var "m") (.var "m0")) (.lit 1)), ("oc", .lit 0),
    ("po", .lit 0)]

/-- The index of the item word. -/
def finA2 : List (String × Expr) :=
  [("ow", .add (.add (.add (.add (.add (.lit 4) (.var "nSG")) (.var "nFA")) (.var "nCO")) (.var "oL")) (.var "ii"))]

/-- The scalars of the copy of the expansion. -/
def finA3 : List (String × Expr) := [("e0", .var "m"), ("ls", .lit 0), ("lN", .var "pc")]

/-- **The expansion of the item.** -/
noncomputable def finE : Com :=
  .seq (asgs finA1) (.seq sumLL (.seq (asgs finA2) (.seq rmLs (gate (.seq exCmd (.seq rmLs
    (gate (.seq (asgs finA3) (lbFr "OB")))))))))

/-- The scalars that `finE` may write. -/
def finEV : List String :=
  ["cl", "cn", "oc", "po", "oL", "fk", "ow", "e0", "ls", "lN", "ci", "lt", "m", "lL"] ++ rmLs.wvars ++ exV

/-- The cost of `finE`. -/
def kFinE (ws : List (List ℕ)) (b : List ℕ) (d KE : ℕ) (E : List (List ℕ)) : ℕ :=
  2 * (30 * total ws + 30 * b.length + 500) + d * 20 + KE + (18 * total E + 60 * E.length) + 300

theorem ell_le_item {p g k q ℓ : ℕ} {t : Node (q + 1) ℓ} :
    ℓ ∈ itemW ((p, g), (⟨k, q + 1, ℓ, t⟩ : TypeTree)) := by
  simp [itemW, Lax185574Proofs.FarRam.toWord_typeTree]

set_option maxHeartbeats 3200000 in
/-- **The expansion of the item.** -/
theorem finE_run {W R d i oL p g k q ℓ nS nF nC P Q sg : ℕ} {t : Node (q + 1) ℓ}
    {ws C : List (List ℕ)} {b : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (hW24 : 2 ^ 24 < W) (har : ArrW W τ) (hlt : EnvLt (W + 1) τ)
    (hL : Lib (ws ++ [] :: C) τ) (hm0 : τ.vars "m0" = ws.length)
    (hrR : τ.vars "rR" = min R W) (hz : τ.vars "z0" = 0) (hbl : τ.vars "bl" = b.length)
    (hy : SegAt "y" 0 b τ) (hov : τ.vars "ovf" = 0)
    (hdd : τ.vars "dd" = d) (hii : τ.vars "ii" = i) (hS : τ.vars "nSG" = nS) (hF : τ.vars "nFA" = nF)
    (hC : τ.vars "nCO" = nC) (h4 : 4 ≤ ws.length) (hd3 : d ≤ ws[3].length)
    (hoL : (ws[3].take d).sum = oL) (hiw : 4 + nS + nF + nC + oL + i < ws.length)
    (hitem : ws[4 + nS + nF + nC + oL + i] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩))
    (hct : IsCT ws[0]) (hgP : τ.vars "gP" = P) (hgQ : τ.vars "gQ" = Q) (hgS : τ.vars "gS" = sg)
    (hsg : sg ≤ 1) (hCw : ∀ w ∈ C, ∃ ν : TypeTree, w = toWord ν)
    (hRk : rhoPlus (k + 1) q + 1 ≤ R) :
    ∃ τ' K, Run (W + 1) finE τ τ' K ∧
      K ≤ kFinE (ws ++ [] :: C) b d (cEx * (ws[0].length + 1) *
        (ws[4 + nS + nF + nC + oL + i].length + ℓ + total C + C.length + rhoPlus (k + 1) q + 1) ^ aEx)
        ((exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).map (i :: ·)) ∧
      (τ'.vars "ovf" = 0 →
        Lib (ws ++ [] :: C ++ (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).map (i :: ·)) τ' ∧
        τ'.vars "e0" = ws.length + 1 + C.length ∧
        τ'.vars "pc" = (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).length ∧
        τ'.vars "oL" = oL ∧ τ'.vars "ow" = 4 + nS + nF + nC + oL + i ∧
        ∃ S, total (ws ++ [] :: C ++ (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).map (i :: ·)) +
          (ws ++ [] :: C ++ (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).map (i :: ·)).length + b.length + 64 ≤ S ∧
          maxEntry ws.flatten ≤ S ∧ 2 ^ 24 * R * R * R * R * S * S < W) ∧
      (∀ y, y ∉ finEV → τ'.vars y = τ.vars y) ∧ τ'.arrs "y" = τ.arrs "y" ∧ τ'.arrs "x" = τ.arrs "x" ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp ∧
      (∀ Lb : List (List ℕ),
        (ws ++ [] :: C ++ (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).map (i :: ·)).Sublist Lb →
        BigRoom W R Lb b (τ.vars "nx") (τ.vars "mw") → τ'.vars "ovf" = 0) := by
  set L1 := ws ++ [] :: C with hL1
  set iw := 4 + nS + nF + nC + oL + i
  set E := (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).map (i :: ·) with hE
  have hL1l : L1.length = ws.length + 1 + C.length := by simp [L1]; omega
  have hm : τ.vars "m" = ws.length + 1 + C.length := by rw [hL.m, hL1l]
  have hR1 : 1 ≤ R := by omega
  -- step 1
  let f1 : String → ℕ := fun y => if y = "cl" then ws.length + 1 else if y = "cn" then C.length else 0
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ) (l := finA1) (f := f1)
    (by
      intro pr hp
      simp only [finA1, List.mem_cons, List.mem_nil_iff, or_false] at hp
      have hmW := hlt.vars "m"
      rcases hp with rfl | rfl | rfl | rfl
      · rw [show f1 "cl" = ws.length + 1 by simp [f1]]
        exact ev_add (ev_var hm0 (by omega)) (evalB_lit (by omega)) (by omega)
      · rw [show f1 "cn" = C.length by simp [f1]]
        have := ev_sub (ev_sub (ev_var hm (by omega)) (ev_var hm0 (by omega)) (B := W + 1) (by omega))
          (evalB_lit (n := 1) (by omega)) (by omega)
        rw [show ws.length + 1 + C.length - ws.length - 1 = C.length by omega] at this
        exact this
      · rw [show f1 "oc" = 0 by simp [f1]]; exact evalB_lit (by omega)
      · rw [show f1 "po" = 0 by simp [f1]]; exact evalB_lit (by omega))
    (by decide)
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  have ar1 : ArrW W τ1 := fun b' => by rw [a1]; exact har b'
  have hw1 : WordsAt L1 τ1 := hL.at_.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1])
  -- step 2
  have hL13 : 3 < L1.length := by omega
  have h3 : L1[3] = ws[3] := by simp only [L1]; rw [List.getElem_append_left (by omega)]
  obtain ⟨τ2, r2, oL2, f2, a2, o2, i2⟩ := sumLL_run (W := W) (d := d) hw1 hL13
    (by rw [g1 "dd" (by decide), hdd]) (by rw [h3]; exact hd3)
    (by
      rw [h3, hoL]
      have : oL ≤ iw := by omega
      have := hlt.vars "m"; omega)
    hl1 ar1 (by omega)
  rw [h3, hoL] at oL2
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt r2 hl1
  have v2 : ∀ y, y ∉ finA1.map Prod.fst → y ≠ "oL" → y ≠ "fk" → τ2.vars y = τ.vars y := fun y h1 h2 h3 => by
    rw [f2 y h2 h3, g1 y h1]
  -- step 3
  have ev2 : ∀ y v, y ∉ finA1.map Prod.fst → y ≠ "oL" → y ≠ "fk" → τ.vars y = v →
      (Expr.var y).evalB (W + 1) τ2 = some v := fun y v h1 h2 h3 h =>
    ev_var (by rw [v2 y h1 h2 h3, h]) (by rw [← h, ← v2 y h1 h2 h3]; exact hl2.vars _)
  obtain ⟨τ3, r3, s3, g3, a3, o3, i3⟩ := asgs_run (B := W + 1) (τ := τ2) (l := finA2) (f := fun _ => iw)
    (by
      intro pr hp
      simp only [finA2, List.mem_cons, List.mem_nil_iff, or_false] at hp
      subst hp
      have hiwW : iw < W + 1 := by have := hlt.vars "m"; omega
      exact ev_add (ev_add (ev_add (ev_add (ev_add (evalB_lit (by omega))
        (ev2 "nSG" _ (by decide) (by decide) (by decide) hS) (by omega))
        (ev2 "nFA" _ (by decide) (by decide) (by decide) hF) (by omega))
        (ev2 "nCO" _ (by decide) (by decide) (by decide) hC) (by omega))
        (ev_var oL2 (by omega)) (by omega)) (ev2 "ii" _ (by decide) (by decide) (by decide) hii) (by omega))
    (by decide)
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 hl2
  have ar3 : ArrW W τ3 := fun b' => by rw [a3, a2]; exact ar1 b'
  have v3 : ∀ y, y ∉ finA1.map Prod.fst → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" → τ3.vars y = τ.vars y :=
    fun y h1 h2 h3 h4 => by rw [g3 y (by simpa [finA2] using h4), v2 y h1 h2 h3]
  have L3 : Lib L1 τ3 := hL.of (by rw [v3 "m" (by decide) (by decide) (by decide) (by decide)])
    (by rw [v3 "lt" (by decide) (by decide) (by decide) (by decide)]) (by rw [a3, a2, a1])
    (by rw [a3, a2, a1]) (by rw [a3, a2, a1])
  have hy3 : SegAt "y" 0 b τ3 := fun j hj => by rw [a3, a2, a1]; exact hy j hj
  -- step 4: the room check
  obtain ⟨τ4, r4, ov4, f4, a4, u4, i4⟩ := rmLs_run (R := R) (ws := L1) (b := b) (τ := τ3)
    (by rw [v3 "W" (by decide) (by decide) (by decide) (by decide), hW]) hW24
    (by rw [v3 "rR" (by decide) (by decide) (by decide) (by decide), hrR]) L3
    (by rw [v3 "z0" (by decide) (by decide) (by decide) (by decide), hz])
    (by rw [v3 "bl" (by decide) (by decide) (by decide) (by decide), hbl]) hy3 ar3 hl3
  rw [v3 "ovf" (by decide) (by decide) (by decide) (by decide), hov] at ov4
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt r4 hl3
  have hpo3 : τ3.vars "po" = 0 := by
    rw [g3 "po" (by decide), f2 "po" (by decide) (by decide), s1 "po" (by decide)]; simp [f1]
  have hnx3 : τ3.vars "nx" = τ.vars "nx" := v3 "nx" (by decide) (by decide) (by decide) (by decide)
  have hmw3 : τ3.vars "mw" = τ.vars "mw" := v3 "mw" (by decide) (by decide) (by decide) (by decide)
  have hEl : E.length = (exW (dwOf P Q sg ws[0]) k q ℓ (toWord t) C).length := by simp [E]
  -- the frame facts of the failure branches
  have frV : ∀ y, y ∉ finEV → y ∉ finA1.map Prod.fst ∧ y ≠ "oL" ∧ y ≠ "fk" ∧ y ≠ "ow" ∧ y ∉ rmLs.wvars := by
    intro y hy
    simp only [finEV, List.mem_append, not_or] at hy
    refine ⟨fun h => hy.1.1 ?_, fun h => hy.1.1 (by simp [h]), fun h => hy.1.1 (by simp [h]),
      fun h => hy.1.1 (by simp [h]), hy.1.2⟩
    simp [finA1] at h; rcases h with h | h | h | h <;> simp [h]
  by_cases hr4 : RoomOK W R τ3 L1 b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ3 L1 b * sOfV τ3 L1 b < W from hr4)] at ov4
    have hrun : Run (W + 1) finE τ τ4 _ :=
      Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (gate_skip (by rw [ov4]; omega) (by rw [ov4]; omega)))))
    refine ⟨τ4, _, hrun, ?_, fun h => by rw [ov4] at h; omega, fun y hy => ?_, by rw [a4, a3, a2, a1],
      by rw [a4, a3, a2, a1], fun b' => by rw [a4]; exact ar3 b', hl4, by rw [u4, o3, o2, o1],
      by rw [i4, i3, i2, i1], fun Lb hsub hB => absurd (roomOK_of_big
        ((List.sublist_append_left _ _).trans hsub) (by rw [hpo3]; omega) (by rw [hnx3, hmw3]; exact hB)) hr4⟩
    · have hA : asgK finA1 = 15 := by decide
      have hA2 : asgK finA2 = 13 := by decide
      rw [hA, hA2]; unfold kFinE; omega
    · obtain ⟨a, b1, c, e, f⟩ := frV y hy
      rw [f4 y f, v3 y a b1 c e]
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ3 L1 b * sOfV τ3 L1 b < W from hr4)] at ov4
  obtain ⟨hT1, hT2, hT3, hT4⟩ := sOfV_ge (τ := τ3) (ws := L1) (b := b)
  have hS3 := room_bound hr4 hR1
  -- step 5: the piece
  have v4 : ∀ y, y ∉ rmLs.wvars → y ∉ finA1.map Prod.fst → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" →
      τ4.vars y = τ.vars y := fun y h0 h1 h2 h3 h4 => by rw [f4 y h0, v3 y h1 h2 h3 h4]
  have hiwL : iw < L1.length := by omega
  have hitL : L1[iw] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩) := by
    simp only [L1]; rw [List.getElem_append_left hiw]; exact hitem
  have h0L : L1[0] = ws[0] := by simp only [L1]; rw [List.getElem_append_left (by omega)]
  have hCL : (L1.drop (ws.length + 1)).take C.length = C := by simp [L1]
  have hPW : P ≤ W := by rw [← hgP]; have := hlt.vars "gP"; omega
  have hQW : Q ≤ W := by rw [← hgQ]; have := hlt.vars "gQ"; omega
  have hiws : i ≤ ws.length := by omega
  have hℓ : ℓ ≤ maxEntry L1.flatten := by
    have hm : ℓ ∈ L1[iw] := by rw [hitL]; exact ell_le_item
    exact le_maxEntry (List.mem_flatten.2 ⟨_, List.getElem_mem _, hm⟩)
  have hroom : Room W (rhoPlus (k + 1) q) (ySz (toWord L1) + i + ([] : List ℕ).length + ℓ) := by
    refine room_of_ok hr4 hRk ?_
    have := ySz_toWord_le L1
    simp only [List.length_nil]
    have : ws.length ≤ L1.length := by omega
    omega
  obtain ⟨τ5, r5, F5, pc5, P5⟩ := exSpec' W τ4 L1 [] 0 iw (ws.length + 1) C.length i P Q sg p g k q ℓ t
    (by omega) hiwL (by rw [v4 "W" (by decide) (by decide) (by decide) (by decide) (by decide), hW])
    (fun b' => by rw [a4]; exact ar3 b') (L3.at_.of_arrs (by rw [a4]) (by rw [a4]) (by rw [a4]))
    (by rw [f4 "oc" (by decide), g3 "oc" (by decide), f2 "oc" (by decide) (by decide), s1 "oc" (by decide)]; simp [f1])
    (by rw [f4 "ow" (by decide), s3 "ow" (by decide)])
    (by rw [f4 "cl" (by decide), g3 "cl" (by decide), f2 "cl" (by decide) (by decide), s1 "cl" (by decide)]; simp [f1])
    (by rw [f4 "cn" (by decide), g3 "cn" (by decide), f2 "cn" (by decide) (by decide), s1 "cn" (by decide)]; simp [f1])
    (by omega) (by rw [v4 "ii" (by decide) (by decide) (by decide) (by decide) (by decide), hii])
    (by rw [v4 "gP" (by decide) (by decide) (by decide) (by decide) (by decide), hgP])
    (by rw [v4 "gQ" (by decide) (by decide) (by decide) (by decide) (by decide), hgQ]) hPW hQW
    (by rw [v4 "gS" (by decide) (by decide) (by decide) (by decide) (by decide), hgS]) hsg
    (by rw [h0L]; exact hct) hitL (by rw [hCL]; exact hCw)
    ⟨by rw [f4 "po" (by decide), hpo3]; rfl, fun j hj => absurd hj (by simp)⟩ hroom
  rw [hCL, h0L] at F5 pc5 r5
  rw [hitL] at r5
  rw [← hE] at F5
  simp only [List.nil_append] at F5
  have hl5 : EnvLt (W + 1) τ5 := Run.envLt r5 hl4
  have ar5 : ArrW W τ5 := fun b' => by rw [P5.len, a4]; exact ar3 b'
  have v5 : ∀ y, y ∉ exV → y ∉ rmLs.wvars → y ∉ finA1.map Prod.fst → y ≠ "oL" → y ≠ "fk" → y ≠ "ow" →
      τ5.vars y = τ.vars y := fun y h h0 h1 h2 h3 h4 => by rw [P5.vars y h, v4 y h0 h1 h2 h3 h4]
  have ha5 : ∀ b', b' ∈ keepA → τ5.arrs b' = τ.arrs b' := fun b' hb => by
    rw [P5.arrs b' hb, a4, a3, a2, a1]
  have L5 : Lib L1 τ5 := hL.of (by rw [v5 "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v5 "lt" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (ha5 "a" (by decide)) (ha5 "st" (by decide)) (ha5 "ln" (by decide))
  -- step 6: the second room check
  obtain ⟨τ6, r6, ov6, f6, a6, u6, i6⟩ := rmLs_run (R := R) (ws := L1) (b := b) (τ := τ5)
    (by rw [v5 "W" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hW]) hW24
    (by rw [v5 "rR" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrR]) L5
    (by rw [v5 "z0" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hz])
    (by rw [v5 "bl" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbl])
    (fun j hj => by rw [ha5 "y" (by decide)]; exact hy j hj) ar5 hl5
  rw [P5.vars "ovf" (by decide), ov4] at ov6
  have hl6 : EnvLt (W + 1) τ6 := Run.envLt r6 hl5
  have hpo5 : τ5.vars "po" = (frames E).length := F5.pos
  have hnx5 : τ5.vars "nx" = τ.vars "nx" := v5 "nx" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmw5 : τ5.vars "mw" = τ.vars "mw" := v5 "mw" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hK5 : asgK finA1 = 15 ∧ asgK finA2 = 13 ∧ asgK finA3 = 7 := by decide
  have frV' : ∀ y, y ∉ finEV → y ∉ exV ∧ y ∉ rmLs.wvars ∧ y ∉ finA1.map Prod.fst ∧ y ≠ "oL" ∧ y ≠ "fk" ∧
      y ≠ "ow" := by
    intro y hy
    obtain ⟨a, b1, c, e, f⟩ := frV y hy
    refine ⟨fun h => hy (by simp [finEV, h]), f, a, b1, c, e⟩
  by_cases hr6 : RoomOK W R τ5 L1 b
  swap
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ5 L1 b * sOfV τ5 L1 b < W from hr6)] at ov6
    have hrun : Run (W + 1) finE τ τ6 _ :=
      Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (gate_run ov4 (by omega)
        (Run.seq r5 (Run.seq r6 (gate_skip (by rw [ov6]; omega) (by rw [ov6]; omega))))))))
    refine ⟨τ6, _, hrun, ?_, fun h => by rw [ov6] at h; omega, fun y hy => ?_, by rw [a6]; exact ha5 "y" (by decide),
      by rw [a6]; exact ha5 "x" (by decide), fun b' => by rw [a6]; exact ar5 b', hl6,
      by rw [u6, P5.out, u4, o3, o2, o1], by rw [i6, P5.inp, i4, i3, i2, i1], fun Lb hsub hB => absurd (roomOK_of_big
        ((List.sublist_append_left _ _).trans hsub) ?_ (by rw [hnx5, hmw5]; exact hB)) hr6⟩
    · rw [hK5.1, hK5.2.1, hitem]; unfold kFinE
      have := Nat.zero_le ((18 * total E + 60 * E.length)); omega
    · obtain ⟨a, b1, c, e, f, h⟩ := frV' y hy
      rw [f6 y b1, v5 y a b1 c e f h]
    · rw [hpo5, length_frames]
      have h1 := total_le_of_sub hsub
      have h2 := hsub.length_le
      simp only [total_append, List.length_append] at h1 h2
      omega
  rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ5 L1 b * sOfV τ5 L1 b < W from hr6)] at ov6
  obtain ⟨hU1, hU2, hU3, hU4⟩ := sOfV_ge (τ := τ5) (ws := L1) (b := b)
  rw [hpo5, length_frames] at hU1
  have hS5 := room_bound hr6 hR1
  have ar6 : ArrW W τ6 := fun b' => by rw [a6]; exact ar5 b'
  have L6 : Lib L1 τ6 := L5.of (by rw [f6 "m" (by decide)]) (by rw [f6 "lt" (by decide)]) (by rw [a6])
    (by rw [a6]) (by rw [a6])
  -- step 7
  have hpc6 : τ6.vars "pc" = E.length := by rw [f6 "pc" (by decide), pc5, hEl]
  have hm6 : τ6.vars "m" = L1.length := L6.m
  obtain ⟨τ7, r7, s7, g7, a7, o7, i7⟩ := asgs_run (B := W + 1) (τ := τ6) (l := finA3)
    (f := fun y => if y = "e0" then L1.length else if y = "ls" then 0 else E.length)
    (by
      intro pr hp
      simp only [finA3, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simp only [if_true]; exact ev_var hm6 (by rw [← hm6]; exact hl6.vars _)
      · simp only [show ("ls" : String) ≠ "e0" by decide, if_false, if_true]; exact evalB_lit (by omega)
      · simp only [show ("lN" : String) ≠ "e0" by decide, show ("lN" : String) ≠ "ls" by decide, if_false]
        exact ev_var hpc6 (by rw [← hpc6]; exact hl6.vars _))
    (by decide)
  have hl7 : EnvLt (W + 1) τ7 := Run.envLt r7 hl6
  have L7 : Lib L1 τ7 := L6.of (by rw [g7 "m" (by decide)]) (by rw [g7 "lt" (by decide)]) (by rw [a7])
    (by rw [a7]) (by rw [a7])
  -- step 8: the copy
  have hOB : τ7.arrs "OB" = τ5.arrs "OB" := by rw [a7, a6]
  have hseg : SegAt "OB" 0 (frames E) τ7 := fun j hj => by rw [hOB, Nat.zero_add]; exact F5.get j hj
  have hEv : ∀ w ∈ E, ∀ v ∈ w, v ≤ W := by
    intro w hw v hv
    have hm : v ∈ frames E := by
      simp only [frames, List.mem_flatten, List.mem_map]
      exact ⟨_, ⟨w, hw, rfl⟩, List.mem_cons_of_mem _ hv⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
    have := hl5.arrs "OB" _ (List.mem_of_getElem? (F5.get j hj))
    omega
  have hfl := length_frames E
  obtain ⟨τ8, r8, L8, -, f8, a8, l8, o8, i8⟩ := lbFr_run (W := W) (src := "OB") (L := E) (p := 0) L7
    (by rw [s7 "ls" (by simp [finA3])]; simp) (by rw [s7 "lN" (by simp [finA3])]; simp) hseg (by decide)
    (by rw [a7, ar6 "a"]; omega) (by rw [a7, ar6 "st"]; omega) (by rw [a7, ar6 "ln"]; omega)
    (by omega) hEv
  have hrun : Run (W + 1) finE τ τ8 _ :=
    Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (gate_run ov4 (by omega)
      (Run.seq r5 (Run.seq r6 (gate_run ov6 (by omega) (Run.seq r7 r8))))))))
  have hl8 : EnvLt (W + 1) τ8 := Run.envLt hrun hlt
  have v8 : ∀ y, y ∉ finEV → τ8.vars y = τ.vars y := fun y hy => by
    obtain ⟨a, b1, c, e, f, h⟩ := frV' y hy
    rw [f8 y (fun hh => hy (by simp at hh; rcases hh with hh | hh | hh | hh | hh | hh <;> simp [finEV, hh])),
      g7 y (fun hh => hy (by simp [finA3] at hh; rcases hh with hh | hh | hh <;> simp [finEV, hh])), f6 y b1,
      v5 y a b1 c e f h]
  refine ⟨τ8, _, hrun, ?_, fun _ => ⟨?_, ?_, ?_, ?_, ?_, sOfV τ5 L1 b, ?_,
    le_trans (maxEntry_flatten_sub (List.sublist_append_left _ _)) hU2, hr6⟩, v8, ?_, ?_, fun b' => by rw [l8, a7]; exact ar6 b',
    hl8, by rw [o8, o7, u6, P5.out, u4, o3, o2, o1], by rw [i8, i7, i6, P5.inp, i4, i3, i2, i1],
    fun _ _ _ => by rw [f8 "ovf" (by decide), g7 "ovf" (by decide), ov6]⟩
  · rw [hK5.1, hK5.2.1, hK5.2.2, hitem]; unfold kFinE; omega
  · exact L8
  · rw [f8 "e0" (by decide), s7 "e0" (by simp [finA3])]; simp [hL1l]
  · rw [f8 "pc" (by decide), g7 "pc" (by decide), hpc6, hEl]
  · rw [f8 "oL" (by decide), g7 "oL" (by decide), f6 "oL" (by decide), P5.vars "oL" (by decide),
      f4 "oL" (by decide), g3 "oL" (by decide), oL2]
  · rw [f8 "ow" (by decide), g7 "ow" (by decide), f6 "ow" (by decide), P5.vars "ow" (by decide),
      f4 "ow" (by decide), s3 "ow" (by decide)]
  · simp only [total_append, List.length_append]; omega
  · rw [a8 "y" (by decide), a7, a6]; exact ha5 "y" (by decide)
  · rw [a8 "x" (by decide), a7, a6]; exact ha5 "x" (by decide)

end Lax185574Proofs.ResolveRam.Glue
