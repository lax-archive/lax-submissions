import Lax185574Proofs.ResolveRam.Sound

/-!
The times of the five slots in a call.

`realT c` is the time bound of the callee that does the work of the call
`c`, read off its concept at the rank of the call. `dFix` bounds the
time of the fixed queries and the constants that their admissibility
needs. `slots_run`: under the guard of the call, with room for `cBig`,
`dFix` and `realT c`, the five slots halt with the answer `rY c` of the
call within `realT c + 4 dFix` steps in total.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.DistanceMatrix
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

/-- The time bound of the callee that does the work of a call. -/
noncomputable def realT : RCall → ℕ
  | .stp => cSt k₀ q₀ * (n + 1) ^ 2 * (maxTreeSize G k₀ q₀ + 1) ^ aSt k₀ q₀
  | .shift τ => cSh τ.k (τ.q - 1) * (wordLength τ + 1) ^ aSh τ.k (τ.q - 1)
  | .ftree τ => cFt τ.k (τ.q - 1) * (wordLength (stp G τ.k τ.q) + 1) *
      (wordLength τ + 1) ^ aFt τ.k (τ.q - 1)
  | .compose σ ν => cCo σ.k σ.q * (wordLength (σ, ν) + 1) ^ aCo σ.k σ.q
  | .canon ws => cCa * (wordLength ws + 1) ^ aCa

/-- The bound of the times of the fixed queries, at least `fixBig`. -/
noncomputable def dFix : ℕ :=
  fixBig + cSh 1 0 * (qA0.length + 1) ^ aSh 1 0 +
    cFt 1 0 * (wordLength (stp G1 1 (0 + 1)) + 1) *
      (wordLength (tree G1 1 (0 + 1) ![(0 : Fin 1)]) + 1) ^ aFt 1 0 +
    cCo 2 0 * (qC0.length + 1) ^ aCo 2 0 + cCa * (qE0.length + 1) ^ aCa +
    cSt 1 0 * (1 + 1) ^ 2 * (maxTreeSize G1 1 0 + 1) ^ aSt 1 0 + 1

theorem fixBig_le_dFix : fixBig ≤ dFix := by unfold dFix; omega

theorem fixA {v : ℕ} (h : dFix ≤ 2 ^ v) : ∃ t ≤ dFix, RunsTo v pSh qA0 yA0 t := by
  have h1 : fixCst eSh (cSh 1 0) qA0 ≤ 2 ^ v := by unfold dFix fixBig at h; omega
  have h2 : cSh 1 0 * (qA0.length + 1) ^ aSh 1 0 ≤ 2 ^ v := by unfold dFix at h; omega
  obtain ⟨t, ht, hr⟩ := ((hSh' 1 0 1 G1 1 ![0] le_rfl le_rfl) v (adm_of_fix h1)).2 h2 _ rfl
  refine ⟨t, le_trans ht ?_, hr⟩
  change cSh 1 0 * (qA0.length + 1) ^ aSh 1 0 ≤ dFix
  unfold dFix; omega

theorem fixB {v : ℕ} (h : dFix ≤ 2 ^ v) : ∃ t ≤ dFix, RunsTo v pFt qB0 yB0 t := by
  have h1 : fixCst eFt (cFt 1 0) qB0 ≤ 2 ^ v := by unfold dFix fixBig at h; omega
  have h2 : cFt 1 0 * (wordLength (stp G1 1 (0 + 1)) + 1) *
      (wordLength (tree G1 1 (0 + 1) ![(0 : Fin 1)]) + 1) ^ aFt 1 0 ≤ 2 ^ v := by
    unfold dFix at h; omega
  obtain ⟨t, ht, hr⟩ := ((hFt' 1 0 1 G1 1 ![0] le_rfl le_rfl) v (adm_of_fix h1)).2 h2 _ rfl
  refine ⟨t, le_trans ht ?_, hr⟩
  beta_reduce
  unfold dFix; omega

theorem fixC {v : ℕ} (h : dFix ≤ 2 ^ v) : ∃ t ≤ dFix, RunsTo v pCo qC0 yC0 t := by
  have h1 : fixCst eCo (cCo 2 0) qC0 ≤ 2 ^ v := by unfold dFix fixBig at h; omega
  have h2 : cCo 2 0 * (qC0.length + 1) ^ aCo 2 0 ≤ 2 ^ v := by unfold dFix at h; omega
  obtain ⟨t, ht, hr⟩ := ((hCo' 2 0 2 G2 1 1 ![0] ![1] le_rfl le_rfl le_rfl
    (fun i j => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact g2_far _))
    v (adm_of_fix h1)).2 h2 _ rfl
  refine ⟨t, le_trans ht ?_, hr⟩
  change cCo 2 0 * (qC0.length + 1) ^ aCo 2 0 ≤ dFix
  unfold dFix; omega

theorem fixE {v : ℕ} (h : dFix ≤ 2 ^ v) : ∃ t ≤ dFix, RunsTo v pCa qE0 yE0 t := by
  have h1 : fixCst eCa cCa qE0 ≤ 2 ^ v := by unfold dFix fixBig at h; omega
  have h2 : cCa * (qE0.length + 1) ^ aCa ≤ 2 ^ v := by unfold dFix at h; omega
  obtain ⟨t, ht, hr⟩ := ((hCa RawW ([] : List RawW)) v (adm_of_fix h1)).2 h2 _ rfl
  refine ⟨t, le_trans ht ?_, ?_⟩
  · change cCa * (qE0.length + 1) ^ aCa ≤ dFix
    unfold dFix; omega
  · have e := (canonW_raw []).1
    simp only [List.map_nil] at e
    beta_reduce at hr
    rw [e] at hr
    exact hr

theorem fixF {v : ℕ} (h : dFix ≤ 2 ^ v) : ∃ t ≤ dFix, RunsTo v pSt qF0 yF0 t := by
  have h1 : fixCst eSt (cSt 1 0) qF0 ≤ 2 ^ v := by unfold dFix fixBig at h; omega
  have h2 : cSt 1 0 * (1 + 1) ^ 2 * (maxTreeSize G1 1 0 + 1) ^ aSt 1 0 ≤ 2 ^ v := by
    unfold dFix at h; omega
  obtain ⟨t, ht, hr⟩ := ((hSt' 1 0 1 G1 le_rfl le_rfl) v (adm_of_fix h1)).2 h2 _ rfl
  refine ⟨t, le_trans ht ?_, hr⟩
  beta_reduce
  unfold dFix; omega

theorem adm_mono {e c c' v : ℕ} {u : List ℕ} (h : WordAdmissible e c' v u) (hc : c ≤ c') :
    WordAdmissible e c v u :=
  fun x hx => le_trans (Nat.mul_le_mul_right _ hc) (h x hx)

variable {G k₀ q₀}

theorem run_shift {τ : TypeTree} (hc : CallInst G k₀ q₀ (.shift τ)) {v : ℕ}
    (ha : WordAdmissible eSh (cBig k₀ q₀) v (toWord τ)) (hT : realT G k₀ q₀ (.shift τ) ≤ 2 ^ v) :
    ∃ t ≤ realT G k₀ q₀ (.shift τ), RunsTo v pSh (toWord τ) (toWord (shOf G τ)) t := by
  obtain ⟨d, hd, ℓ, u, h1, hk, rfl⟩ := hc
  have e : realT G k₀ q₀ (.shift (tree G (k₀ + d) (q₀ - d - 1 + 1) u)) =
      cSh (k₀ + d) (q₀ - d - 1) * (wordLength (tree G (k₀ + d) (q₀ - d - 1 + 1) u) + 1) ^
        aSh (k₀ + d) (q₀ - d - 1) := by simp [realT, tree]
  rw [e] at hT ⊢
  obtain ⟨t, ht, hr⟩ := ((hSh' (k₀ + d) (q₀ - d - 1) n G ℓ u h1 hk) v
    (adm_mono ha (le_cBig hd).1)).2 hT _ rfl
  rw [shOf_tree G u h1 hk]
  exact ⟨t, ht, hr⟩

theorem run_ftree {τ : TypeTree} (hc : CallInst G k₀ q₀ (.ftree τ)) {v : ℕ}
    (ha : WordAdmissible eFt (cBig k₀ q₀) v (toWord (τ, stpCut (τ.k + 1) (stp G k₀ q₀))))
    (hT : realT G k₀ q₀ (.ftree τ) ≤ 2 ^ v) :
    ∃ t ≤ realT G k₀ q₀ (.ftree τ), RunsTo v pFt (toWord (τ, stpCut (τ.k + 1) (stp G k₀ q₀)))
      (toWord ((faOf G τ).map toWord)) t := by
  obtain ⟨d, hd, ℓ, u, h1, hk, rfl⟩ := hc
  have hst : stpCut ((tree G (k₀ + d) (q₀ - d - 1 + 1) u).k + 1) (stp G k₀ q₀) =
      stp G (k₀ + d) (q₀ - d - 1 + 1) := stpCut_stp' G (by simp [tree]) (by simp [tree]; omega)
  rw [hst] at ha ⊢
  have e : realT G k₀ q₀ (.ftree (tree G (k₀ + d) (q₀ - d - 1 + 1) u)) =
      cFt (k₀ + d) (q₀ - d - 1) * (wordLength (stp G (k₀ + d) (q₀ - d - 1 + 1)) + 1) *
        (wordLength (tree G (k₀ + d) (q₀ - d - 1 + 1) u) + 1) ^ aFt (k₀ + d) (q₀ - d - 1) := by
    simp [realT, tree]
  rw [e] at hT ⊢
  obtain ⟨t, ht, hr⟩ := ((hFt' (k₀ + d) (q₀ - d - 1) n G ℓ u h1 hk) v
    (adm_mono ha (le_cBig hd).2.1)).2 hT _ rfl
  rw [toWord_faOf G u h1 hk]
  exact ⟨t, ht, hr⟩

theorem run_compose {σ ν : TypeTree} (hc : CallInst G k₀ q₀ (.compose σ ν)) {v : ℕ}
    (ha : WordAdmissible eCo (cBig k₀ q₀) v (toWord (σ, ν)))
    (hT : realT G k₀ q₀ (.compose σ ν) ≤ 2 ^ v) :
    ∃ t ≤ realT G k₀ q₀ (.compose σ ν), RunsTo v pCo (toWord (σ, ν)) (toWord (coOf G σ ν)) t := by
  obtain ⟨d, hd, ℓ, u, b, h1, hk, hb, rfl, rfl⟩ := hc
  have e : realT G k₀ q₀ (.compose (tree G (k₀ + d + 1) (q₀ - d - 1) u)
      (tree G (k₀ + d + 1) (q₀ - d - 1) ![b])) =
      cCo (k₀ + d + 1) (q₀ - d - 1) * (wordLength (tree G (k₀ + d + 1) (q₀ - d - 1) u,
        tree G (k₀ + d + 1) (q₀ - d - 1) ![b]) + 1) ^ aCo (k₀ + d + 1) (q₀ - d - 1) := by
    simp [realT, tree]
  rw [e] at hT ⊢
  obtain ⟨t, ht, hr⟩ := ((hCo' (k₀ + d + 1) (q₀ - d - 1) n G ℓ 1 u ![b] h1 le_rfl (by omega)
    (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i)) v
    (adm_mono ha (le_cBig hd).2.2)).2 hT _ rfl
  rw [coOf_tree G u b h1 hk hb]
  rw [Fin.append_right_eq_snoc] at hr
  exact ⟨t, ht, hr⟩

theorem run_canon (ws : List (List ℕ)) {v : ℕ}
    (ha : WordAdmissible eCa (cBig k₀ q₀) v (toWord ws)) (hT : realT G k₀ q₀ (.canon ws) ≤ 2 ^ v) :
    ∃ t ≤ realT G k₀ q₀ (.canon ws), RunsTo v pCa (toWord ws) (canonW ws) t := by
  obtain ⟨h1, h2⟩ := canonW_raw ws
  have hs := hCa RawW (ws.map RawW.mk)
  rw [h2] at hs
  have ha' := adm_mono ha (show cCa ≤ cBig k₀ q₀ by unfold cBig; omega)
  obtain ⟨t, ht, hr⟩ := (hs v ha').2 (by simpa [realT, wordLength] using hT) _ rfl
  rw [h1] at hr
  exact ⟨t, by simpa [realT, wordLength] using ht, hr⟩

theorem run_stp (hk : 1 ≤ k₀) (hn : 1 ≤ n) {v : ℕ}
    (ha : WordAdmissible eSt (cBig k₀ q₀) v (toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀)))
    (hT : realT G k₀ q₀ .stp ≤ 2 ^ v) :
    ∃ t ≤ realT G k₀ q₀ .stp, RunsTo v pSt (toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀))
      (toWord (stp G k₀ q₀)) t :=
  ((hSt' k₀ q₀ n G hk hn) v (adm_mono ha (show cSt k₀ q₀ ≤ cBig k₀ q₀ by unfold cBig; omega))).2
    hT _ rfl

/-- **The runs of the slots in a call.** -/
theorem slots_run (hk : 1 ≤ k₀) {P Q : ℕ} {s : Bool} {c : RCall}
    (hc : c ∈ rcalls G P Q s k₀ q₀) {X v sQ : ℕ}
    (hg : RGuard G k₀ q₀ eSh eFt eCo eCa eSt X v sQ c) {wA wB wC wE wF : ℕ}
    (hwA : v - sQ ≤ wA) (hwB : v - sQ ≤ wB) (hwC : v - sQ ≤ wC) (hwE : v - sQ ≤ wE)
    (hwF : v - sQ ≤ wF) (hB : BigOK k₀ q₀ X (v - sQ)) (hfix : dFix ≤ 2 ^ (v - sQ))
    (hT : realT G k₀ q₀ c ≤ 2 ^ (v - sQ)) :
    ∃ (yA' yB' yC' yE' yF' : List ℕ) (tA tB tC tE tF : ℕ),
      RunsTo wA pSh (qA c) yA' tA ∧ RunsTo wB pFt (qB G k₀ q₀ c) yB' tB ∧
      RunsTo wC pCo (qC c) yC' tC ∧ RunsTo wE pCa (qE c) yE' tE ∧
      RunsTo wF pSt (qF G k₀ q₀ c) yF' tF ∧ yA' ++ yB' ++ yC' ++ yE' ++ yF' = rY G k₀ q₀ c ∧
      tA + tB + tC + tE + tF ≤ realT G k₀ q₀ c + 4 * dFix := by
  have hci := callInst G P Q s k₀ q₀ hk c hc
  have hp : ∀ w, v - sQ ≤ w → 2 ^ (v - sQ) ≤ 2 ^ w := fun w hw => two_pow_mono hw
  have hBw : ∀ w, v - sQ ≤ w → BigOK k₀ q₀ X w := fun w hw => by
    rcases hB with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (hp w hw))
  have fA := fixA (le_trans hfix (hp _ hwA))
  have fB := fixB (le_trans hfix (hp _ hwB))
  have fC := fixC (le_trans hfix (hp _ hwC))
  have fE := fixE (le_trans hfix (hp _ hwE))
  have fF := fixF (le_trans hfix (hp _ hwF))
  obtain ⟨t1, ht1, r1⟩ := fA
  obtain ⟨t2, ht2, r2⟩ := fB
  obtain ⟨t3, ht3, r3⟩ := fC
  obtain ⟨t4, ht4, r4⟩ := fE
  obtain ⟨t5, ht5, r5⟩ := fF
  cases c with
  | stp =>
    have hn : 1 ≤ n := hci
    obtain ⟨t, ht, hr⟩ := run_stp hk hn (adm_real G hg hwF (hBw _ hwF)) (le_trans hT (hp _ hwF))
    exact ⟨_, _, _, _, _, _, _, _, _, _, r1, r2, r3, r4, hr, rfl, by omega⟩
  | shift τ =>
    obtain ⟨t, ht, hr⟩ := run_shift hci (adm_real G hg hwA (hBw _ hwA)) (le_trans hT (hp _ hwA))
    exact ⟨_, _, _, _, _, _, _, _, _, _, hr, r2, r3, r4, r5, rfl, by omega⟩
  | ftree τ =>
    obtain ⟨t, ht, hr⟩ := run_ftree hci (adm_real G hg hwB (hBw _ hwB)) (le_trans hT (hp _ hwB))
    exact ⟨_, _, _, _, _, _, _, _, _, _, r1, hr, r3, r4, r5, rfl, by omega⟩
  | compose σ ν =>
    obtain ⟨t, ht, hr⟩ := run_compose hci (adm_real G hg hwC (hBw _ hwC)) (le_trans hT (hp _ hwC))
    exact ⟨_, _, _, _, _, _, _, _, _, _, r1, r2, hr, r4, r5, rfl, by omega⟩
  | canon ws =>
    obtain ⟨t, ht, hr⟩ := run_canon (G := G) (k₀ := k₀) (q₀ := q₀) ws
      (adm_real G hg hwE (hBw _ hwE)) (le_trans hT (hp _ hwE))
    exact ⟨_, _, _, _, _, _, _, _, _, _, r1, r2, r3, hr, r5, rfl, by omega⟩

end Lax185574Proofs.ResolveRam
