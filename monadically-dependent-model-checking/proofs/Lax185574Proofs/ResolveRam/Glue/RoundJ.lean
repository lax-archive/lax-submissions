import Lax185574Proofs.ResolveRam.Glue.PreR

/-!
A later round of the glue program of lem:resolve-lift that issues a call.

The later round `roundJ body fE` starts with `rdPre`, runs the case
`body`, and ends with `fE` if the new phase is the end (`Nph = 3`) and
with `tailR` otherwise. `BodyCall` is what a case must do: from the
environment after the start, either set `ovf` or leave the scalars of
the end (`TailIn`) for the library `L` and the plan `ps`, with the
scalars of the new head, and not set `ovf` when the library is small
(`BigRoom`). `roundJ_run`: the glue command then outputs the head, the
state and the query of the switch, or sets `ovf`, and does not set `ovf`
when the checks pass.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- A later round. -/
noncomputable def roundJ (body fE : Com) (eS eF eC eK dS dF dC dK : ℕ) : Com :=
  rdPre (.seq body (gate (.ite (.eq (.var "Nph") (.lit 3)) fE (tailR eS eF eC eK dS dF dC dK))))

/-- The size that bounds every room check of a round with the library `L`. -/
def sBig (L : List (List ℕ)) (b : List ℕ) (nx mw : ℕ) : ℕ :=
  sOf (total L) L.length b.length (2 * total L + L.length + 8) nx mw (maxEntry L.flatten) (maxEntry b)

/-- The room for a round with the library `L`. -/
def BigRoom (W R : ℕ) (L : List (List ℕ)) (b : List ℕ) (nx mw : ℕ) : Prop :=
  2 ^ 24 * R * R * R * R * sBig L b nx mw * sBig L b nx mw < W

/-- What the case of a round with a call does. -/
def BodyCall (body : Com) (W R X : ℕ) (sc : List ℕ) (ws : List (List ℕ)) (wx b : List ℕ)
    (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (k : ℕ) (w : List ℕ) (Nt Nw : ℕ) (nsc : List ℕ) (KB : ℕ) :
    Prop :=
  ∀ τ, PreR W R sc ws wx b τ → τ.vars "ovf" = 0 → kq0 < W →
    ∃ τ' kb, Run (W + 1) body τ τ' kb ∧ kb ≤ KB ∧
      (τ'.vars "ovf" = 0 → TailIn W R X L ps k w b τ' ∧ τ'.vars "Nt" = Nt ∧ τ'.vars "Nw" = Nw ∧
        hsV.map τ'.vars = nsc ∧ τ'.vars "po" = 0 ∧ τ'.vars "nx" = τ.vars "nx" ∧
        τ'.vars "mw" = τ.vars "mw" ∧ τ'.out = []) ∧
      (BigRoom W R L b (τ.vars "nx") (τ.vars "mw") → τ'.vars "ovf" = 0)

/-- The output of a round with a call, from the scalars of the new head. -/
noncomputable def hdC (Nt Nw : ℕ) (nsc : List ℕ) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) : List ℕ :=
  Nt :: (17 + (toWord (planW L ps)).length) :: Nw :: (nsc ++ toWord (planW L ps))

theorem sOf_mono {a b c d e f g h a' b' c' d' e' f' g' h' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c')
    (h4 : d ≤ d') (h5 : e ≤ e') (h6 : f ≤ f') (h7 : g ≤ g') (h8 : h ≤ h') :
    sOf a b c d e f g h ≤ sOf a' b' c' d' e' f' g' h' := by
  unfold sOf
  have : max (max f g) h ≤ max (max f' g') h' := max_le_max (max_le_max h6 h7) h8
  omega

theorem maxEntry_flatten_sub {l L : List (List ℕ)} (h : l.Sublist L) :
    maxEntry l.flatten ≤ maxEntry L.flatten :=
  maxEntry_le fun v hv => le_maxEntry ((h.flatten).subset hv)

theorem roomOK_of_big {W R : ℕ} {L ws : List (List ℕ)} {b : List ℕ} {τ : Env} (hs : ws.Sublist L)
    (hpo : τ.vars "po" ≤ 2 * total L + L.length + 8) (h : BigRoom W R L b (τ.vars "nx") (τ.vars "mw")) :
    RoomOK W R τ ws b := by
  have hS : sOfV τ ws b ≤ sBig L b (τ.vars "nx") (τ.vars "mw") :=
    sOf_mono (total_le_of_sub hs) hs.length_le le_rfl hpo le_rfl le_rfl (maxEntry_flatten_sub hs) le_rfl
  unfold RoomOK
  unfold BigRoom at h
  refine lt_of_le_of_lt ?_ h
  have := Nat.mul_le_mul hS hS
  calc 2 ^ 24 * R * R * R * R * sOfV τ ws b * sOfV τ ws b
      = 2 ^ 24 * R * R * R * R * (sOfV τ ws b * sOfV τ ws b) := by ring
    _ ≤ 2 ^ 24 * R * R * R * R * (sBig L b (τ.vars "nx") (τ.vars "mw") * sBig L b (τ.vars "nx") (τ.vars "mw")) :=
      Nat.mul_le_mul_left _ this
    _ = _ := by ring

/-- The array lengths of a later round. -/
def extJ (W : ℕ) : String → ℕ := fun _ => W + 1

theorem envLt_of {W : ℕ} {σ : Env} (hv : ∀ y, σ.vars y < W + 1) (ha : ∀ a, ∀ v ∈ σ.arrs a, v < W + 1)
    (hi : ∀ v ∈ σ.inp, v < W + 1) : EnvLt (W + 1) σ := ⟨hv, ha, hi⟩

set_option maxHeartbeats 800000 in
/-- **A later round with a call.** -/
theorem roundJ_run {K e d W t R X k KB Nt Nw : ℕ} {eS eF eC eK dS dF dC dK : ℕ} (body fE : Com)
    {sc wx b w nsc : List ℕ} {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (ht : t ≠ 0) (hwx : wx.length = t - 1) (hsc : sc.length = 17) (hws : 1 ≤ ws.length)
    (hz : sc.getD 0 0 = 0) (hK : kq0 ≤ K) (hR : R = Lax3.DistFO.rhoPlus (sc.getD 7 0 + 1) (sc.getD 8 0) + 2)
    (hu : ∀ v ∈ [t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b), 64 * v < W + 1)
    (hbody : BodyCall body W R X sc ws wx b L ps k w Nt Nw nsc KB)
    (hN3 : nsc.getD 9 0 ≠ 3) (hsub : ws.Sublist L) :
    ∃ σ' k', Run (W + 1) (glueTop K e d (roundJ body fE eS eF eC eK dS dF dC dK))
        ((initEnv (extJ W) ([t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++
          (b.length :: b))).setVar "W" W) σ' k' ∧
      k' ≤ 30 * K + 50 + preK wx (sc ++ toWord ws) b (sc.getD 7 0) (sc.getD 8 0) W ws + 4 + KB + 4 + 10 +
        tailK L ps (hdC Nt Nw nsc L ps ++ kW k w) b (kE eS eF eC eK k) (kD dS dF dC dK k) ∧
      (σ'.vars "ovf" = 0 → σ'.out = hdC Nt Nw nsc L ps ++ kW k w ∧ K < W ∧
        guardOK W (kE eS eF eC eK k) (kD dS dF dC dK k) X w ∧
        maxEntry (hdC Nt Nw nsc L ps ++ kW k w) < W / 32 / 32) ∧
      (K < W → BigRoom W R L b (sc.getD 2 0) (maxEntry wx) →
        guardOK W (kE eS eF eC eK k) (kD dS dF dC dK k) X w →
        maxEntry (hdC Nt Nw nsc L ps ++ kW k w) < W / 32 / 32 → σ'.vars "ovf" = 0) := by
  have hW1 : 1 ≤ W := by have := hu t (by simp); omega
  have ht1 : t < W + 1 := by have := hu t (by simp); omega
  set rest := (sc ++ toWord ws).length :: wx ++ (sc ++ toWord ws) ++ (b.length :: b) with hrest
  have hu' : [t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b) = t :: rest := by
    simp [hrest]
  rw [hu']
  obtain ⟨σ2, hW2, ht2, hgk2, hov2, hpo2, ha2, hi2, ho2, hv2, hrun2, hfail2⟩ :=
    topJ_run (K := K) (e := e) (d := d) (roundJ body fE eS eF eC eK dS dF dC dK) (extJ W) (rest := rest) ht hW1 ht1
  have hk24 : 2 ^ 24 ≤ kq0 := by
    unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  by_cases hKW : K < W
  swap
  · obtain ⟨σ', k', r', ov', hk'⟩ := hfail2 hKW
    exact ⟨σ', k', r', by omega, fun h => by rw [ov'] at h; omega, fun h => absurd h hKW⟩
  have hl2 : EnvLt (W + 1) σ2 := by
    refine ⟨fun y => ?_, fun a v hv => ?_, fun v hv => ?_⟩
    · by_cases h1 : y = "gk"
      · subst h1; rw [hgk2]; omega
      by_cases h2 : y = "tg"
      · subst h2; rw [ht2]; exact ht1
      by_cases h3 : y = "W"
      · subst h3; rw [hW2]; omega
      rw [hv2 y h1 h2 h3]; omega
    · rw [ha2] at hv; simp [initEnv, List.mem_replicate] at hv; omega
    · rw [hi2] at hv; exact (by have := hu v (by rw [hu']; exact List.mem_cons_of_mem _ hv); omega)
  have har2 : ArrW W σ2 := fun a => by rw [ha2]; simp [initEnv, extJ]
  obtain ⟨τ1, k1, r1, hk1, P1⟩ := preR_run (W := W) (t := t) (wx := wx) (sc := sc) (b := b) (ws := ws)
    hW2 ht2 hwx hsc hws hz hi2 har2 hl2 (by omega) hpo2 hov2 ho2 hu
  rw [← hR] at P1
  have hnx : τ1.vars "nx" = sc.getD 2 0 := P1.hsc 2 (by omega)
  have hmw : τ1.vars "mw" = maxEntry wx := P1.hmw
  by_cases hov1 : τ1.vars "ovf" = 0
  swap
  · -- the room check of the start fails
    have hl1 := P1.hlt
    refine ⟨τ1, _, hrun2 hKW τ1 _ (Run.seq r1 (gate_skip hov1 (hl1.vars _))), ?_,
      fun h => absurd h hov1, fun _ hB _ _ => ?_⟩
    · have := Nat.zero_le (KB + tailK L ps (hdC Nt Nw nsc L ps ++ kW k w) b (kE eS eF eC eK k) (kD dS dF dC dK k))
      omega
    · have hr := roomOK_of_big (τ := τ1) hsub (by rw [P1.hpo]; omega) (by rw [hnx, hmw]; exact hB)
      have := P1.hroom; rw [if_pos hr] at this; exact absurd this hov1
  obtain ⟨τ3, kb, r3, hkb, hok3, hbig3⟩ := hbody τ1 P1 hov1 (by omega)
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 P1.hlt
  by_cases hov3 : τ3.vars "ovf" = 0
  swap
  · refine ⟨τ3, _, hrun2 hKW τ3 _ (Run.seq r1 (gate_run hov1 hW1 (Run.seq r3 (gate_skip hov3 (hl3.vars _))))),
      ?_, fun h => absurd h hov3, fun _ hB _ _ => absurd (hbig3 (by rw [hnx, hmw]; exact hB)) hov3⟩
    have := Nat.zero_le (tailK L ps (hdC Nt Nw nsc L ps ++ kW k w) b (kE eS eF eC eK k) (kD dS dF dC dK k))
    omega
  obtain ⟨TI, hNt, hNw, hns, hpo3, hnx3, hmw3, hout3⟩ := hok3 hov3
  have hhd : hdW τ3 L ps = hdC Nt Nw nsc L ps := by simp only [hdW, hdC, hNt, hNw, hns]
  have hN : τ3.vars "Nph" = nsc.getD 9 0 := by
    have := congrArg (fun l => l.getD 9 0) hns
    simpa [hsV] using this
  have hc : (Cond.eq (.var "Nph") (.lit 3)).evalB (W + 1) τ3 = some false := by
    rw [evalB_condEq (ev_var hN (by rw [← hN]; exact hl3.vars _)) (evalB_lit (n := 3) (by
      have := TI.hbig; omega))]
    have : (nsc.getD 9 0 == 3) = false := by simpa using hN3
    rw [this]
  obtain ⟨τ4, k4, r4, hk4, hsnd, hcmp⟩ := tailR_run (eS := eS) (eF := eF) (eC := eC) (eK := eK) (dS := dS)
    (dF := dF) (dC := dC) (dK := dK) TI
  rw [hhd] at hk4 hsnd hcmp
  refine ⟨τ4, _, hrun2 hKW τ4 _ (Run.seq r1 (gate_run hov1 hW1 (Run.seq r3 (gate_run hov3 hW1
    ((Run.ite_false hc r4).mono le_rfl))))), ?_, fun h0 => ?_, fun _ hB hg he => ?_⟩
  · simp only [Cond.size, Expr.size]; omega
  · obtain ⟨o4, g4, e4⟩ := hsnd h0
    exact ⟨by rw [o4, hout3]; simp, hKW, g4, e4⟩
  · refine hcmp ?_ hg he
    exact roomOK_of_big (List.Sublist.refl L) (by rw [hpo3]; omega) (by rw [hnx3, hmw3, hnx, hmw]; exact hB)

end Lax185574Proofs.ResolveRam.Glue
