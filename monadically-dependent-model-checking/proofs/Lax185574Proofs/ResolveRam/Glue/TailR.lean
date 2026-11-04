import Lax185574Proofs.ResolveRam.Glue.RoomS
import Lax185574Proofs.ResolveRam.Glue.OutEq

/-!
The end of a later round that issues a call.

A step of a round runs only if no check failed so far (`gate`). After
the case of the round, `tailR` checks the room once more (`rmLs`) and
then writes the head, the state and the query (`tailC`). From the
scalars that the case leaves (`TailIn`) the run writes `hdW ++ kW`
unless a check fails, and the checks pass when the library is small and
the guard and the entry check pass (`tailR_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- Run `c` only if no check failed. -/
def gate (c : Com) : Com := .ite (.eq (.var "ovf") (.lit 0)) c .skip

theorem gate_run {W k : ℕ} {c : Com} {τ τ' : Env} (h0 : τ.vars "ovf" = 0) (hW : 1 ≤ W)
    (h : Run (W + 1) c τ τ' k) : Run (W + 1) (gate c) τ τ' (k + 4) :=
  (Run.ite_true (by rw [evalB_condEq (ev_var h0 (by omega)) (evalB_lit (by omega))]; rfl) h).mono
    (by simp [Cond.size]; omega)

theorem gate_skip {W : ℕ} {c : Com} {τ : Env} (h0 : τ.vars "ovf" ≠ 0) (hW : τ.vars "ovf" < W + 1) :
    Run (W + 1) (gate c) τ τ 5 := by
  have := evalB_condEq (B := W + 1) (σ := τ) (e := .var "ovf") (f := .lit 0) (ev_var rfl hW)
    (evalB_lit (by omega))
  exact (Run.ite_false (by rw [this]; cases hv : τ.vars "ovf" with
      | zero => exact absurd hv h0
      | succ m => rfl)
    Run.skip).mono (by simp [Cond.size])

/-- The real query is at most twice the library. -/
theorem kindOK_len {W k : ℕ} {L : List (List ℕ)} {w : List ℕ} {τ : Env} (h : KindOK W L k w τ) :
    w.length ≤ 2 * total L + L.length + 8 := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := h
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · obtain ⟨iw, hiw, -, -, rfl⟩ := k0 rfl
    have := len_le_total hiw; simp; omega
  · obtain ⟨iw, hiw, lo, N, m, -, -, -, -, -, -, -, -, rfl⟩ := k1 rfl
    have := len_le_total hiw
    have := size_sub (selW_sub L lo N (cutSel m))
    rw [List.length_append, length_toWord_words]; simp; omega
  · obtain ⟨is, jf, h1, h2, -, -, rfl⟩ := k2 rfl
    have := len_le_total h1; have := len_le_total h2; simp; omega
  · obtain ⟨ie, hie, -, rfl⟩ := k3 rfl
    have := len_le_total hie; omega

/-- The entries of the real query are entries of the library or lengths. -/
theorem kindOK_val {W k : ℕ} {L : List (List ℕ)} {w : List ℕ} {τ : Env} (h : KindOK W L k w τ)
    (hs : LibSmall W L) : ∀ v ∈ w, v ≤ W := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := h
  have hL : ∀ i (hi : i < L.length), ∀ v ∈ L[i], v ≤ W := fun i hi v hv => hs.2 _ (List.getElem_mem hi) v hv
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · obtain ⟨iw, hiw, -, -, rfl⟩ := k0 rfl
    exact fun v hv => hL iw hiw v (List.mem_of_mem_drop hv)
  · obtain ⟨iw, hiw, lo, N, m, -, -, -, -, -, -, -, -, rfl⟩ := k1 rfl
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hL iw hiw v (List.mem_of_mem_drop hv)
    · have := size_sub (selW_sub L lo N (cutSel m))
      exact mem_toWord_bound hv (by have := hs.1; omega)
        (fun w hw x hx => hs.2 w ((selW_sub L lo N (cutSel m)).subset hw) x hx)
  · obtain ⟨is, jf, h1, h2, -, -, rfl⟩ := k2 rfl
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hL is h1 v hv
    · exact hL jf h2 v hv
  · obtain ⟨ie, hie, -, rfl⟩ := k3 rfl
    exact hL ie hie

/-- The entries of the library are below the bound. -/
theorem lib_lt {W : ℕ} {L : List (List ℕ)} {τ : Env} (h : WordsAt L τ) (he : EnvLt (W + 1) τ) :
    ∀ w ∈ L, ∀ v ∈ w, v ≤ W := by
  intro w hw v hv
  have hsa := seg_lib h
  have : v ∈ L.flatten := List.mem_flatten.2 ⟨w, hw, hv⟩
  rw [← hsa, seg] at this
  have := he.arrs "a" v (List.mem_of_mem_drop (List.mem_of_mem_take this))
  omega

/-- The constant that the fixed queries need. -/
noncomputable def kq0 : ℕ := 2 ^ 24 * (qLen + maxEntry (qA0 ++ qB0 ++ qC0 ++ qE0 ++ qF0) + 64)

/-- What the case of a round leaves for the end of the round. -/
structure TailIn (W R X : ℕ) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (k : ℕ) (w b : List ℕ) (τ : Env) :
    Prop where
  hW : τ.vars "W" = W
  hbig : kq0 < W
  harr : ArrW W τ
  hlt : EnvLt (W + 1) τ
  hrR : τ.vars "rR" = min R W
  hR1 : 1 ≤ R
  hlib : Lib L τ
  hz0 : τ.vars "z0" = 0
  hbl : τ.vars "bl" = b.length
  hy : SegAt "y" 0 b τ
  hgX : τ.vars "gX" = X
  hovf : τ.vars "ovf" = 0
  hkind : KindOK W L k w τ
  hqk : τ.vars "qk" = k
  hPR : PreAt "PR" (prW ps) τ
  hnp : τ.vars "np" = ps.length
  hps : ∀ p ∈ ps, p.1 + p.2 ≤ L.length
  hpsl : ps.length ≤ 12

/-- The end of a round with a call. -/
noncomputable def tailR (eS eF eC eK dS dF dC dK : ℕ) : Com :=
  .seq rmLs (gate (tailC eS eF eC eK dS dF dC dK))

/-- The room check passes. -/
def RoomOK (W R : ℕ) (τ : Env) (L : List (List ℕ)) (b : List ℕ) : Prop :=
  2 ^ 24 * R * R * R * R * sOfV τ L b * sOfV τ L b < W

instance (W R : ℕ) (τ : Env) (L : List (List ℕ)) (b : List ℕ) : Decidable (RoomOK W R τ L b) := by
  unfold RoomOK; infer_instance

/-- The cost of the end of a round. It is linear in the size of the library
`L`, the answer `b` and the output `o`. -/
noncomputable def tailK (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (o : List ℕ) (b : List ℕ) (e d : ℕ) : ℕ :=
  30 * total L + 30 * b.length + 500 + 4 + (100 * ps.length + 800 * (total L + L.length + qLen + 10) +
    112 * o.length + 60 * (e + 1) + 30 * 2 ^ d + 8 * qLen + 2000)

/-- The output of a round holds the words of its plan. -/
theorem planW_le_hdW (τ : Env) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (o : List ℕ) :
    total (planW L ps) + (planW L ps).length ≤ (hdW τ L ps ++ o).length := by
  have := length_toWord_words (planW L ps)
  simp only [hdW, List.length_append, List.length_cons, List.length_map]
  omega

set_option maxHeartbeats 400000 in
/-- **The end of a round with a call.** -/
theorem tailR_run {W R X k eS eF eC eK dS dF dC dK : ℕ} {L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    {w b : List ℕ} {τ : Env} (h : TailIn W R X L ps k w b τ) :
    ∃ τ' K, Run (W + 1) (tailR eS eF eC eK dS dF dC dK) τ τ' K ∧
      K ≤ tailK L ps (hdW τ L ps ++ kW k w) b (kE eS eF eC eK k) (kD dS dF dC dK k) ∧
      (τ'.vars "ovf" = 0 → τ'.out = τ.out ++ (hdW τ L ps ++ kW k w) ∧
        guardOK W (kE eS eF eC eK k) (kD dS dF dC dK k) X w ∧
        maxEntry (hdW τ L ps ++ kW k w) < W / 32 / 32) ∧
      (RoomOK W R τ L b → guardOK W (kE eS eF eC eK k) (kD dS dF dC dK k) X w →
        maxEntry (hdW τ L ps ++ kW k w) < W / 32 / 32 → τ'.vars "ovf" = 0) := by
  obtain ⟨hW, hbig, harr, hlt, hrR, hR1, hlib, hz0, hbl, hy, hgX, hovf, hkind, hqk, hPR, hnp, hps,
    hpsl⟩ := h
  set A := qLen + maxEntry (qA0 ++ qB0 ++ qC0 ++ qE0 ++ qF0)
  have hkA : kq0 = 2 ^ 24 * (A + 64) := rfl
  have hW24 : 2 ^ 24 < W := by
    have : 2 ^ 24 ≤ 2 ^ 24 * (A + 64) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hqW : 2 ^ 24 * qLen ≤ W := by
    have : 2 ^ 24 * qLen ≤ 2 ^ 24 * (A + 64) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hFv : ∀ v ∈ qA0 ++ qB0 ++ qC0 ++ qE0 ++ qF0, v ≤ W := by
    intro v hv
    have h1 := le_maxEntry hv
    have : maxEntry (qA0 ++ qB0 ++ qC0 ++ qE0 ++ qF0) ≤ 2 ^ 24 * (A + 64) :=
      le_trans (show _ ≤ A + 64 by omega) (Nat.le_mul_of_pos_left _ (by omega))
    omega
  obtain ⟨τ1, r1, ov1, f1, a1, u1, i1⟩ := rmLs_run (R := R) hW hW24 hrR hlib hz0 hbl hy harr hlt
  rw [hovf] at ov1
  have hl1 : EnvLt (W + 1) τ1 := Run.envLt r1 hlt
  by_cases hroom : RoomOK W R τ L b
  · rw [if_pos (show 2 ^ 24 * R * R * R * R * sOfV τ L b * sOfV τ L b < W from hroom)] at ov1
    set S := sOfV τ L b
    have hS : 2 * total L + 2 * L.length + 64 ≤ S := by simp only [S, sOfV, sOf]; omega
    have hSS : 2 ^ 24 * S * S < W := by
      have h1 : 1 ≤ R * R * R * R := Nat.one_le_iff_ne_zero.2 (by positivity)
      have : 2 ^ 24 * S * S ≤ 2 ^ 24 * R * R * R * R * S * S := by
        have := Nat.mul_le_mul_left (2 ^ 24 * S * S) h1
        calc 2 ^ 24 * S * S = 2 ^ 24 * S * S * 1 := by ring
          _ ≤ 2 ^ 24 * S * S * (R * R * R * R) := this
          _ = _ := by ring
      exact lt_of_le_of_lt this hroom
    have hS64 : 2 ^ 30 * S ≤ W := by
      have : 64 * S ≤ S * S := Nat.mul_le_mul_right _ (by omega)
      have : 2 ^ 30 * S ≤ 2 ^ 24 * S * S := by
        calc 2 ^ 30 * S = 2 ^ 24 * (64 * S) := by ring
          _ ≤ 2 ^ 24 * (S * S) := Nat.mul_le_mul_left _ this
          _ = _ := by ring
      omega
    have xs_ok : ∀ y, y ∉ rmLs.wvars.filter (· != "ovf") → τ1.vars y = τ.vars y := by
      intro y hy
      by_cases hyo : y = "ovf"
      · subst hyo; rw [ov1, hovf]
      · exact f1 y (fun hm => hy (List.mem_filter.2 ⟨hm, by simpa using hyo⟩))
    have O1 : OFr τ τ1 (rmLs.wvars.filter (· != "ovf")) :=
      ⟨xs_ok, fun b' _ => by rw [a1], by rw [a1], u1, i1⟩
    have hlibok : LibOK W L τ := ⟨hlib.at_, harr, hW⟩
    have hq1 : QInv W X k L w τ1 := QInv.ofr ⟨hgX, hovf, hlibok, hkind, hqk⟩ O1 (by decide)
    have hs : LibSmall W L := ⟨by omega, lib_lt hlib.at_ hlt⟩
    have hhd : hdW τ1 L ps = hdW τ L ps := by
      simp only [hdW]
      rw [xs_ok "Nt" (by decide), xs_ok "Nw" (by decide),
        List.map_congr_left (fun y hy => xs_ok y (by revert y; decide))]
    have hBig : 64 * ((ps.length + 4) * (total L + L.length + qLen + 64)) ≤ W := by
      have : (ps.length + 4) * (total L + L.length + qLen + 64) ≤ 16 * (total L + L.length + qLen + 64) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨σ', K, r2, hK, o2, ov2⟩ := tailC_run (W := W) (X := X) (k := k) (eS := eS) (eF := eF) (eC := eC)
      (eK := eK) (dS := dS) (dF := dF) (dC := dC) (dK := dK) (L := L) (ps := ps) (w := w) (τ := τ1)
      (by rw [xs_ok "W" (by decide), hW]) (by omega) hq1 hs
      (fun i hi => by rw [a1]; exact hPR i hi) (by rw [xs_ok "np" (by decide), hnp]) hps
      (fun y _ => by have := hl1.vars y; omega) (by rw [← hgX]; have := hlt.vars "gX"; omega) hBig hFv
      (kindOK_len hkind) (kindOK_val hkind hs)
    rw [hhd] at hK o2 ov2
    have hpl := planW_le_hdW τ L ps (kW k w)
    refine ⟨σ', _, Run.seq r1 (gate_run ov1 (by omega) r2), ?_, fun h0 => ?_, fun _ hg he => ?_⟩
    · unfold tailK; unfold slotK at hK; omega
    · rw [ov2] at h0
      split_ifs at h0 with hc
      · exact ⟨by rw [o2, u1], hc.1, hc.2⟩
    · rw [ov2, if_pos ⟨hg, he⟩]
  · rw [if_neg (show ¬ 2 ^ 24 * R * R * R * R * sOfV τ L b * sOfV τ L b < W from hroom)] at ov1
    refine ⟨τ1, _, Run.seq r1 (gate_skip (by rw [ov1]; omega) (by rw [ov1]; omega)), ?_,
      fun h0 => by rw [ov1] at h0; omega, fun hr => absurd hr hroom⟩
    unfold tailK; omega

end Lax185574Proofs.ResolveRam.Glue
