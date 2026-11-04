import Lax185574Proofs.ResolveRam.Glue.CFESem

/-!
The last round of the glue program of lem:resolve-lift.

In the last round the case of the round only sets the new phase `Nph` to
`3` (`BodyFin`), so that the round ends with `fE` instead of `tailR`.
`bodyFin_nph`: the assignment `Nph := 3` is such a case, and so is a
case behind tests that select it (`bodyFin_ite_true`,
`bodyFin_ite_false`). `preR_nph`: setting `Nph` keeps the environment after the start of the
round. `fECmd_run`: in the last round the end command `fECmd` writes `0`
followed by the output of lem:resolve-lift. `roundJ_fin`: the glue
command on the input of the last round writes the output of the end
command, or sets `ovf`, and does not set `ovf` when the checks pass.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo

/-- What the case of the last round does: it only sets `Nph` to `3`. -/
def BodyFin (body : Com) (W R : ℕ) (sc : List ℕ) (ws : List (List ℕ)) (wx b : List ℕ) (KB : ℕ) : Prop :=
  ∀ τ, PreR W R sc ws wx b τ → τ.vars "ovf" = 0 → kq0 < W →
    ∃ kb ≤ KB, Run (W + 1) body τ (τ.setVar "Nph" 3) kb

/-- An environment that differs from `τ` only by `Nph = 3` is `τ.setVar "Nph" 3`. -/
theorem env_nph {τ τ' : Env} (h3 : τ'.vars "Nph" = 3) (hv : ∀ y, y ≠ "Nph" → τ'.vars y = τ.vars y)
    (ha : τ'.arrs = τ.arrs) (ho : τ'.out = τ.out) (hi : τ'.inp = τ.inp) : τ' = τ.setVar "Nph" 3 := by
  cases τ'
  cases τ
  simp only [Env.setVar, Env.mk.injEq] at h3 hv ha ho hi ⊢
  refine ⟨funext fun y => ?_, ha, hi, ho⟩
  by_cases hy : y = "Nph"
  · subst hy; simp [h3]
  · simp [hy, hv y hy]

/-- **The case of the last round.** -/
theorem bodyFin_nph {W R : ℕ} {sc : List ℕ} {ws : List (List ℕ)} {wx b : List ℕ} :
    BodyFin (asgs [("Nph", .lit 3)]) W R sc ws wx b (asgK [("Nph", .lit 3)]) := by
  intro τ _ _ hW
  have h24 : 2 ^ 24 ≤ kq0 := by unfold kq0; exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨τ', r, h1, h2, ha, ho, hi⟩ := asgs_run (B := W + 1) (τ := τ) (l := [("Nph", .lit 3)])
    (f := fun _ => 3) (by intro p hp; simp at hp; subst hp; exact evalB_lit (by omega)) (by decide)
  refine ⟨_, le_rfl, ?_⟩
  rwa [← env_nph (h1 "Nph" (by simp)) (fun y hy => h2 y (by simpa using hy)) ha ho hi]

theorem bodyFin_mono {body : Com} {W R KB KB' : ℕ} {sc : List ℕ} {ws : List (List ℕ)} {wx b : List ℕ}
    (h : BodyFin body W R sc ws wx b KB) (hK : KB ≤ KB') : BodyFin body W R sc ws wx b KB' := by
  intro τ P0 hov hkq
  obtain ⟨kb, hkb, r⟩ := h τ P0 hov hkq
  exact ⟨kb, by omega, r⟩

theorem bodyFin_ite_true {body c2 : Com} {b : Cond} {W R KB : ℕ} {sc : List ℕ} {ws : List (List ℕ)}
    {wx bb : List ℕ} (hb : ∀ τ, PreR W R sc ws wx bb τ → b.evalB (W + 1) τ = some true)
    (h : BodyFin body W R sc ws wx bb KB) : BodyFin (.ite b body c2) W R sc ws wx bb (1 + b.size + KB) := by
  intro τ P0 hov hkq
  obtain ⟨kb, hkb, r⟩ := h τ P0 hov hkq
  exact ⟨_, by omega, Run.ite_true (hb τ P0) r⟩

theorem bodyFin_ite_false {body c1 : Com} {b : Cond} {W R KB : ℕ} {sc : List ℕ} {ws : List (List ℕ)}
    {wx bb : List ℕ} (hb : ∀ τ, PreR W R sc ws wx bb τ → b.evalB (W + 1) τ = some false)
    (h : BodyFin body W R sc ws wx bb KB) : BodyFin (.ite b c1 body) W R sc ws wx bb (1 + b.size + KB) := by
  intro τ P0 hov hkq
  obtain ⟨kb, hkb, r⟩ := h τ P0 hov hkq
  exact ⟨_, by omega, Run.ite_false (hb τ P0) r⟩

theorem nph_scR : ∀ i (h : i < 17), scR[i]'(by simp [scR]; omega) ≠ "Nph" := by decide

/-- **Setting the new phase keeps the start of the round.** -/
theorem preR_nph {W R : ℕ} {sc : List ℕ} {ws : List (List ℕ)} {wx b : List ℕ} {τ : Env}
    (h : PreR W R sc ws wx b τ) (hW : 3 ≤ W) : PreR W R sc ws wx b (τ.setVar "Nph" 3) := by
  have hs : sOfV (τ.setVar "Nph" 3) ws b = sOfV τ ws b := by simp [sOfV]
  refine ⟨by simp [h.hW], fun b' => by simpa using h.harr b', ⟨fun y => ?_, fun a v hv => h.hlt.arrs a v
    (by simpa using hv), fun v hv => h.hlt.inp v (by simpa using hv)⟩, fun i hi => ?_,
    h.hlib.of (by simp) (by simp) (by simp) (by simp) (by simp), by simp [h.hbl],
    fun j hj => by simpa using h.hy j hj, fun j hj => by simpa using h.hx j hj, by simp [h.hmw],
    by simp [h.hrR], by simp [h.hpo], by simp [h.hout], by simp [h.hinp], ?_⟩
  · by_cases hy : y = "Nph"
    · subst hy; simp; omega
    · have := h.hlt.vars y; simp [hy]; omega
  · simp only [vars_setVar]
    rw [if_neg (nph_scR i hi)]; exact h.hsc i hi
  · simp only [vars_setVar, show ("ovf" : String) ≠ "Nph" by decide, if_false]
    rw [h.hroom]
    simp only [RoomOK, hs]

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- **The end command in the last round.** -/
theorem fECmd_run (hk : 1 ≤ k₀) (hn : 1 ≤ n) {j W R : ℕ} (hj : j + 1 = (rcalls G P Q s k₀ q₀).length)
    {τ : Env}
    (hP : PreR W R (scW G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
      ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) τ)
    (hov : τ.vars "ovf" = 0) (hR1 : 1 ≤ R) :
    ∃ τ' k, Run (W + 1) fECmd τ τ' k ∧
      k ≤ feK n (xIn G k₀ q₀ P Q s).length (swAt G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).ws
        (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j))) (0 :: zOut G k₀ q₀ P Q s) ∧
      τ'.out = 0 :: zOut G k₀ q₀ P Q s ∧
      τ'.vars "ovf" = if maxEntry (0 :: zOut G k₀ q₀ P Q s) < W / 32 / 32 then 0 else 1 := by
  obtain ⟨hv, hf, -⟩ := fe_cur G P Q s k₀ q₀ hn hj
  rw [fe_winOf G P Q s k₀ q₀ hf, List.take_length] at hP
  obtain ⟨i, m, hc, hi, hm⟩ := fe_last G P Q s k₀ q₀ hv hf
  rw [hc] at hP ⊢
  have hi' : i < (lvR G P Q s k₀ q₀ 0).length := by omega
  obtain ⟨ws', hcl⟩ : ∃ ws', callOf G P Q s k₀ q₀ (.up 0 i m) = .canon ws' := by
    rw [callOf_up' hi' (by omega)]; split_ifs <;> exact ⟨_, rfl⟩
  have hit := fe_item (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) (m := m) hi'
  have hgd : (swAt G P Q s k₀ q₀ (.up 0 i m)).ws.getD (4 + (swAt G P Q s k₀ q₀ (.up 0 i m)).SG.length +
      (swAt G P Q s k₀ q₀ (.up 0 i m)).FA.length + (swAt G P Q s k₀ q₀ (.up 0 i m)).CO.length + i) [] =
      itemW (lvR G P Q s k₀ q₀ 0)[i] := by
    rw [List.getD_eq_getElem?_getD, hit]; rfl
  have hlen := fe_len_outP (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi'
  have hws := congrArg List.length (fe_ws (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) i m)
  simp only [List.length_append] at hws
  obtain ⟨τ', k, r, hk', ho, hov'⟩ := fECmd_gen (i := i) hP hov hR1 (by simp [scW]) (by simp [scW])
    (by simp [scW]) (by simp [scW]) (by simp [scW]) (by simp [scW, curW]) (by omega)
    (by simp [scW, curW]) (List.getElem?_eq_some_iff.1 hit).1 (by rw [hgd]; exact fe_len_item _)
    (by simp [SW.ws]) (by rw [hcl]; exact fe_dl ws')
  rw [fe_out G P Q s k₀ q₀ hk hi hm] at hk' ho hov'
  exact ⟨τ', k, r, hk', ho, hov'⟩

/-- **The last round.** -/
theorem roundJ_fin {K e d W t R KB KF : ℕ} {eS eF eC eK dS dF dC dK : ℕ} (body fE : Com)
    {sc wx b o : List ℕ} {ws : List (List ℕ)}
    (ht : t ≠ 0) (hwx : wx.length = t - 1) (hsc : sc.length = 17) (hws : 1 ≤ ws.length)
    (hz : sc.getD 0 0 = 0) (hK : kq0 ≤ K) (hR : R = Lax3.DistFO.rhoPlus (sc.getD 7 0 + 1) (sc.getD 8 0) + 2)
    (hu : ∀ v ∈ [t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++ (b.length :: b), 64 * v < W + 1)
    (hbody : BodyFin body W R sc ws wx b KB)
    (hfE : ∀ τ, PreR W R sc ws wx b τ → τ.vars "ovf" = 0 →
      ∃ τ' k, Run (W + 1) fE (τ.setVar "Nph" 3) τ' k ∧ k ≤ KF ∧ τ'.out = o ∧
        τ'.vars "ovf" = if maxEntry o < W / 32 / 32 then 0 else 1) :
    ∃ σ' k', Run (W + 1) (glueTop K e d (roundJ body fE eS eF eC eK dS dF dC dK))
        ((initEnv (extJ W) ([t, (sc ++ toWord ws).length] ++ wx ++ (sc ++ toWord ws) ++
          (b.length :: b))).setVar "W" W) σ' k' ∧
      k' ≤ 30 * K + 50 + preK wx (sc ++ toWord ws) b (sc.getD 7 0) (sc.getD 8 0) W ws + KB + KF + 30 ∧
      (σ'.vars "ovf" = 0 → σ'.out = o ∧ K < W ∧ maxEntry o < W / 32 / 32) ∧
      (K < W → BigRoom W R ws b (sc.getD 2 0) (maxEntry wx) → maxEntry o < W / 32 / 32 →
        σ'.vars "ovf" = 0) := by
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
      fun h => absurd h hov1, fun _ hB _ => ?_⟩
    · omega
    · have hr := roomOK_of_big (τ := τ1) (List.Sublist.refl ws) (by rw [P1.hpo]; omega)
        (by rw [hnx, hmw]; exact hB)
      have := P1.hroom; rw [if_pos hr] at this; exact absurd this hov1
  obtain ⟨kb, hkb, r3⟩ := hbody τ1 P1 hov1 (by omega)
  set τ3 := τ1.setVar "Nph" 3
  have hl3 : EnvLt (W + 1) τ3 := Run.envLt r3 P1.hlt
  have hov3 : τ3.vars "ovf" = 0 := by simp [τ3, hov1]
  obtain ⟨τ4, k4, r4, hk4, ho4, hov4⟩ := hfE τ1 P1 hov1
  have hc : (Cond.eq (.var "Nph") (.lit 3)).evalB (W + 1) τ3 = some true := by
    rw [evalB_condEq (ev_var (show τ3.vars "Nph" = 3 by simp [τ3]) (by omega)) (evalB_lit (n := 3) (by omega))]
    rfl
  refine ⟨τ4, _, hrun2 hKW τ4 _ (Run.seq r1 (gate_run hov1 hW1 (Run.seq r3 (gate_run hov3 hW1
    (Run.ite_true hc r4))))), ?_, fun h0 => ?_, fun _ _ he => ?_⟩
  · simp only [Cond.size, Expr.size]; omega
  · refine ⟨ho4, hKW, ?_⟩
    rw [hov4] at h0
    split_ifs at h0 with hh
    · exact hh
  · rw [hov4, if_pos he]

end Lax185574Proofs.ResolveRam.Glue
