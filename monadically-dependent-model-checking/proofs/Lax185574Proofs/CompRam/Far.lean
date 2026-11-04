import Lax185574Proofs.CompRam.Assembly

/-!
**Far composition from a glue program** (`far_of_glue`).
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax808846.RamComputes Lax185574.Computing Lax185574.WordEncoding
open Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus)

theorem count_le_xT {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
    {u₂ : Fin l2 → Fin n} :
    Node.count (node G k q u₁) + Node.count (node G k q u₂) ≤ (xT G k q u₁ u₂).length := by
  have h1 := count_le_word (node G k q u₁)
  have h2 := count_le_word (node G k q u₂)
  rw [xT_eq]; simp; omega

theorem pow_le_two_pow {c Z e w : ℕ} (hZ : 1 ≤ Z) (h : c * Z ^ e ≤ 2 ^ w) : c ≤ 2 ^ w :=
  le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h

theorem sub3_le {B w : ℕ} (hw : 3 ≤ w) (h : 8 * B ≤ 2 ^ w) : B ≤ 2 ^ (w - 3) := by
  have : 2 ^ w = 8 * 2 ^ (w - 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  omega

set_option maxHeartbeats 1000000 in
/-- **Far composition from a glue program.** -/
theorem far_of_glue (hGl : GlueHyp)
    (hR : ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (J : List (Fin ℓ)), ℓ ≤ k → J.Nodup →
        Computes p e c (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
          (fun m => c * (m + 1) ^ a))
    (hS : ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
        1 ≤ ℓ → ℓ ≤ k →
        Computes p e c (tree G k (q + 1) u) (tree G (k + 1) q u)
          (fun m => c * (m + 1) ^ a))
    (hC : ∃ (p : Program) (e c a : ℕ),
      ∀ (α : Type) [WordEncoding α] (l : List α),
        Computes p e c (l.map toWord) (finsetOf {x | x ∈ l}) (fun m => c * (m + 1) ^ a)) :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ) (u₁ : Fin ℓ₁ → Fin n)
        (u₂ : Fin ℓ₂ → Fin n),
        1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
        (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
        Computes p e c (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨pR, eR, hR⟩ := hR
  obtain ⟨pS, eS, hS⟩ := hS
  obtain ⟨pC, eC, cC, aC, hC⟩ := hC
  obtain ⟨sI, hGl⟩ := hGl
  obtain ⟨Gp, cG, E, hE1, hG⟩ := hGl eR eS eC (sI + 4) le_rfl
  obtain ⟨sw, Ks, hsw⟩ := switch pR pS pC (sI + 4) (by omega)
  obtain ⟨p, KL, hL⟩ := loop_sound Gp sw
  refine ⟨p, 2 * E + 2, fun k q => ?_⟩
  obtain ⟨C, A, hRun⟩ := cRun_of hR hS hC (k + q + 1)
  have hK1 : 1 ≤ k + q + 1 := by omega
  set K := k + q + 1 with hK
  set sQ := sI + 4 + 20 with hsQ
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = crunBig eR eS eC C A := ⟨_, rfl⟩
  -- the polynomial bounds
  have hLf := pb_Lf K q
  obtain ⟨cV, aV, hV⟩ : PB fun X => (10 * X ^ (q + 1) + 3) ^ 2 * (2 ^ (sQ + 20) *
      (cG * (3 * Lf K q X + 1) ^ E + Cb + C * (Lf K q X + 1) ^ A + Ks + Lf K q X + 1)) :=
    ((((PB.xpow (q + 1)).cmul 10).add (PB.const 3)).pow 2).mul
      (((((((((hLf.cmul 3).add (PB.const 1)).pow E).cmul cG).add (PB.const Cb)).add
        (((hLf.add (PB.const 1)).pow A).cmul C)).add (PB.const Ks)).add hLf).add (PB.const 1)
        |>.cmul (2 ^ (sQ + 20)))
  obtain ⟨cT, aT, hT⟩ : PB fun X => KL * ((5 * X ^ (q + 1) + 1) *
      (cG * (2 * Lf K q X + 1) ^ 2 + Ks * (C * (Lf K q X + 1) ^ A + Cb + Lf K q X + 1) + 2) +
        Lf K q X + 1) :=
    (((((PB.xpow (q + 1)).cmul 5).add (PB.const 1)).mul
      ((((((hLf.cmul 2).add (PB.const 1)).pow 2).cmul cG).add
        (((((hLf.add (PB.const 1)).pow A).cmul C).add (PB.const Cb) |>.add hLf |>.add
          (PB.const 1)).cmul Ks)).add (PB.const 2))).add hLf |>.add (PB.const 1)).cmul KL
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = ((Cb + Ks + 1) * 2 ^ (sQ + 20)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 16 * (cV ^ 2 + 1) * (cT + 1) * (8 * Bs + 8 * 2 ^ sI + 256) := ⟨_, rfl⟩
  have hc1 : 16 * (cV ^ 2 + 1) ≤ c := by
    rw [hc, Nat.mul_assoc (16 * (cV ^ 2 + 1))]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hc2 : 8 * Bs + 8 * 2 ^ sI + 256 ≤ c := by
    rw [hc]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
  have hcT : cT ≤ c := by
    have : cT + 1 ≤ (16 * (cV ^ 2 + 1)) * (cT + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have : (16 * (cV ^ 2 + 1)) * (cT + 1) ≤ c := by
      rw [hc]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  refine ⟨c, 2 * aV + aT, fun n G ℓ₁ ℓ₂ u₁ u₂ h1 h2 hk hfar => ?_⟩
  have hI : Inst G k q u₁ u₂ := ⟨h1, h2, hk, hfar⟩
  obtain ⟨hxw, m, hm, hend, hreach, hcall⟩ := inst_script hI
  intro w hadm
  rw [← hxw] at hadm
  simp only [wordLength]
  rw [← hxw]
  set x := xT G k q u₁ u₂ with hx
  set M := maxEntry x with hM
  set Z := x.length + M + 1 with hZ
  have hxne : x ≠ [] := by rw [hx, xT_eq]; simp
  have hadm' : c * Z ^ (2 * E + 2) ≤ 2 ^ w := hadm M (maxEntry_mem hxne)
  have hZ1 : 1 ≤ Z := by omega
  have hZe : Z ≤ Z ^ (2 * E + 2) := Nat.le_self_pow (by omega) Z
  have hcw : c * Z ≤ 2 ^ w := le_trans (Nat.mul_le_mul_left _ hZe) hadm'
  have hcw' : c ≤ 2 ^ w := pow_le_two_pow (e := 1) hZ1 (by simpa using hcw)
  have hw8 : 8 ≤ w := by
    by_contra hlt
    have : 2 ^ w ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hxw1 : x.length < 2 ^ (w - 1) := by
    have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have : 2 * Z ≤ c * Z := Nat.mul_le_mul_right _ (by omega)
    omega
  have hbig : Bs ≤ 2 ^ (w - 3) := sub3_le (by omega) (by omega)
  have hx0 : (x.length + M + 1) * 2 ^ sI ≤ 2 ^ (w - 3) := by
    refine sub3_le (by omega) ?_
    have : 8 * 2 ^ sI * Z ≤ c * Z := Nat.mul_le_mul_right _ (by omega)
    rw [← hZ]; nlinarith
  rw [hBs, hCb] at hbig
  refine ⟨fun y t hrun => comp_sound (cSound_of_cRun hRun hK1) hsw hL hG le_rfl (by omega) hI le_rfl
    hw8 hxw1 hbig hx0 y t hrun, fun hTw y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  -- the run
  set X := x.length + 1 with hXdef
  have hX1 : 1 ≤ X := by omega
  have hTw' : c * X ^ (2 * aV + aT) ≤ 2 ^ w := hTw
  have hmX : m + 1 ≤ 5 * X ^ (q + 1) := by
    have := count_le_xT (G := G) (k := k) (q := q) (u₁ := u₁) (u₂ := u₂)
    rw [← hx] at this
    calc m + 1 ≤ 5 * (Node.count (node G k q u₁) + Node.count (node G k q u₂)) ^ (q + 1) := hm
      _ ≤ 5 * X ^ (q + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  obtain ⟨Lx, hLx⟩ : ∃ Lx, Lx = Lf K q X := ⟨_, rfl⟩
  have hLL : Lsz (szP G k q u₁ u₂) m ≤ Lx := by
    rw [hLx]; exact Lsz_mono (by rw [← hx]; omega) (by omega)
  obtain ⟨V, hVdef⟩ : ∃ V, V = (10 * X ^ (q + 1) + 3) ^ 2 * (2 ^ (sQ + 20) *
      (cG * (3 * Lx + 1) ^ E + Cb + C * (Lx + 1) ^ A + Ks + Lx + 1)) := ⟨_, rfl⟩
  have hVX : V ≤ cV * X ^ aV := by rw [hVdef, hLx]; exact hV X hX1
  have hVb : 8 * (V * Z ^ E) ≤ 2 ^ w :=
    room_arith (a := 2 * aV + aT) (e := 2 * E + 2) hVX hX1 hZ1 hc1 (by omega) (by omega)
      (le_trans (Nat.mul_le_mul_right _ le_rfl) (le_trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hX1 (by omega))) hTw')) hadm'
  have hcap8 := lpCap_eq (w := w) (by omega)
  have hroom : ∀ i ≤ 2 * m + 2, lpSize w i ≠ 0 ∧
      bigR eR eS eC C A Ks sQ cG E (Lsz (szP G k q u₁ u₂) m) M ≤ 2 ^ lpV w i := by
    intro i hi
    have hb := bigR_le (eR := eR) (eS := eS) (eC := eC) (C := C) (A := A) (Ks := Ks) (sQ := sQ)
      (cG := cG) hE1 hLL (M := M) (Z := Z) (by omega)
    rw [← hCb] at hb
    refine lp_room ?_ ?_
    · simp only [bigR]; rw [← hCb]
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
    · have hi2 : (i + 1) ^ 2 ≤ (10 * X ^ (q + 1) + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have : (i + 1) ^ 2 * bigR eR eS eC C A Ks sQ cG E (Lsz (szP G k q u₁ u₂) m) M ≤ V * Z ^ E := by
        rw [hVdef, Nat.mul_assoc]
        exact Nat.mul_le_mul hi2 hb
      omega
  have hcap : Lsz (szP G k q u₁ u₂) m ≤ lpCap w := by
    have hp1 : 1 ≤ (10 * X ^ (q + 1) + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hp2 : 1 ≤ 2 ^ (sQ + 20) := Nat.one_le_two_pow
    have h1 : Lx ≤ V := by
      generalize hW : cG * (3 * Lx + 1) ^ E + Cb + C * (Lx + 1) ^ A + Ks = Wt at hVdef
      generalize (10 * X ^ (q + 1) + 3) ^ 2 = P1 at hVdef hp1
      generalize 2 ^ (sQ + 20) = P2 at hVdef hp2
      subst hVdef
      have : Lx ≤ P2 * (Wt + Lx + 1) := le_trans (by omega) (Nat.le_mul_of_pos_left _ hp2)
      exact le_trans this (Nat.le_mul_of_pos_left _ hp1)
    have h2 : V ≤ V * Z ^ E := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hZ1)
    omega
  obtain ⟨t, ht, hrun⟩ := comp_run hRun hK1 hsw hL hG le_rfl (by omega) hI le_rfl hend hreach hcall
    (size_ok hI hend hcall) hw8 hxw1 hroom hcap
  refine ⟨t, le_trans ht ?_, hrun⟩
  -- the time
  have hrt := roundT_mono (eR := eR) (eS := eS) (eC := eC) (C := C) (A := A) (Ks := Ks) (cG := cG) hLL
  have h1 : KL * ((m + 1) * roundT eR eS eC C A Ks cG (Lsz (szP G k q u₁ u₂) m) +
      Lsz (szP G k q u₁ u₂) m + 1) ≤ KL * ((5 * X ^ (q + 1) + 1) *
        (cG * (2 * Lx + 1) ^ 2 + Ks * (C * (Lx + 1) ^ A + Cb + Lx + 1) + 2) + Lx + 1) := by
    apply Nat.mul_le_mul_left
    have : (m + 1) * roundT eR eS eC C A Ks cG (Lsz (szP G k q u₁ u₂) m) ≤
        (5 * X ^ (q + 1) + 1) * roundT eR eS eC C A Ks cG Lx := Nat.mul_le_mul (by omega) hrt
    have e : roundT eR eS eC C A Ks cG Lx =
        cG * (2 * Lx + 1) ^ 2 + Ks * (C * (Lx + 1) ^ A + Cb + Lx + 1) + 2 := by
      simp only [roundT]; rw [← hCb]
    rw [e] at this
    omega
  have h2 : KL * ((5 * X ^ (q + 1) + 1) *
      (cG * (2 * Lx + 1) ^ 2 + Ks * (C * (Lx + 1) ^ A + Cb + Lx + 1) + 2) + Lx + 1) ≤
      cT * X ^ aT := by rw [hLx]; exact hT X hX1
  have h3 : cT * X ^ aT ≤ c * X ^ (2 * aV + aT) :=
    Nat.mul_le_mul hcT (Nat.pow_le_pow_right hX1 (by omega))
  exact le_trans h1 (le_trans h2 (le_trans h3 (le_of_eq (by rw [hXdef, hx]))))

end Lax185574Proofs.CompRam
