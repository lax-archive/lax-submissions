import Lax185574Proofs.ResolveRam.LenTrees
import Lax185574Proofs.MC.Bounds.WordSizes

/-!
The lengths of the queries and the answers of the calls.

`realY c` is the answer of the slot that does the work of the call `c`.
The query and the answer of the switch are those of the working slot and
fixed words (`rQY_len`). The answer of the working slot is no longer
than its time bound `realT c` (`realY_le`), since every call is an
instance of its callee.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.TypeTreeSizes Lax185574Proofs.Simulate
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

/-- The answer of the slot that does the work of a call. -/
noncomputable def realY : RCall → List ℕ
  | .stp => toWord (stp G k₀ q₀)
  | .shift τ => toWord (shOf G τ)
  | .ftree τ => toWord ((faOf G τ).map toWord)
  | .compose σ ν => toWord (coOf G σ ν)
  | .canon ws => canonW ws

/-- The lengths of the fixed words. -/
noncomputable def fixLen : ℕ :=
  qA0.length + qB0.length + qC0.length + qE0.length + qF0.length + yA0.length + yB0.length +
    yC0.length + yE0.length + yF0.length + 6

theorem rQY_len (c : RCall) : (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length ≤
    fixLen + (realQ G k₀ q₀ c).length + (realY G k₀ q₀ c).length := by
  have hl : ∀ qA qB qC qE qF : List ℕ, (sw5In qA qB qC qE qF).length =
      6 + qA.length + qB.length + qC.length + qE.length + qF.length := by
    intro qA qB qC qE qF
    simp only [sw5In, swIn, List.length_append, List.length_cons, List.length_nil]; omega
  unfold fixLen
  cases c <;> simp only [rQ, rY, hl, qA, qB, qC, qE, qF, yA, yB, yC, yE, yF, realQ, realY,
    List.length_append] <;> omega

variable {G k₀ q₀}

/-- **The answer is no longer than the time bound.** -/
theorem realY_le (hk : 1 ≤ k₀) {c : RCall} (hc : CallInst G k₀ q₀ c) :
    (realY G k₀ q₀ c).length ≤ realT G k₀ q₀ c := by
  cases c with
  | stp => exact wordLength_le_time' (hSt' k₀ q₀ n G hk hc)
  | shift τ =>
    obtain ⟨d, hd, ℓ, u, h1, hk', rfl⟩ := hc
    have h := wordLength_le_time' (hSh' (k₀ + d) (q₀ - d - 1) n G ℓ u h1 hk')
    have e : realT G k₀ q₀ (.shift (tree G (k₀ + d) (q₀ - d - 1 + 1) u)) =
        cSh (k₀ + d) (q₀ - d - 1) * (wordLength (tree G (k₀ + d) (q₀ - d - 1 + 1) u) + 1) ^
          aSh (k₀ + d) (q₀ - d - 1) := by simp [realT, tree]
    rw [e]
    show wordLength (shOf G _) ≤ _
    rw [shOf_tree G u h1 hk']
    exact h
  | ftree τ =>
    obtain ⟨d, hd, ℓ, u, h1, hk', rfl⟩ := hc
    have h := wordLength_le_time' (hFt' (k₀ + d) (q₀ - d - 1) n G ℓ u h1 hk')
    have e : realT G k₀ q₀ (.ftree (tree G (k₀ + d) (q₀ - d - 1 + 1) u)) =
        cFt (k₀ + d) (q₀ - d - 1) * (wordLength (stp G (k₀ + d) (q₀ - d - 1 + 1)) + 1) *
          (wordLength (tree G (k₀ + d) (q₀ - d - 1 + 1) u) + 1) ^ aFt (k₀ + d) (q₀ - d - 1) := by
      simp [realT, tree]
    rw [e]
    show (toWord ((faOf G _).map toWord)).length ≤ _
    rw [toWord_faOf G u h1 hk']
    exact h
  | compose σ ν =>
    obtain ⟨d, hd, ℓ, u, b, h1, hk', hb, rfl, rfl⟩ := hc
    have h := wordLength_le_time' (hCo' (k₀ + d + 1) (q₀ - d - 1) n G ℓ 1 u ![b] h1 le_rfl
      (by omega) (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i))
    rw [Fin.append_right_eq_snoc] at h
    have e : realT G k₀ q₀ (.compose (tree G (k₀ + d + 1) (q₀ - d - 1) u)
        (tree G (k₀ + d + 1) (q₀ - d - 1) ![b])) =
        cCo (k₀ + d + 1) (q₀ - d - 1) * (wordLength (tree G (k₀ + d + 1) (q₀ - d - 1) u,
          tree G (k₀ + d + 1) (q₀ - d - 1) ![b]) + 1) ^ aCo (k₀ + d + 1) (q₀ - d - 1) := by
      simp [realT, tree]
    rw [e]
    show wordLength (coOf G _ _) ≤ _
    rw [coOf_tree G u b h1 hk' hb]
    exact h
  | canon ws =>
    obtain ⟨h1, h2⟩ := canonW_raw ws
    have hs := hCa RawW (ws.map RawW.mk)
    rw [h2] at hs
    have h := wordLength_le_time' hs
    show (canonW ws).length ≤ cCa * (wordLength ws + 1) ^ aCa
    rw [← h1]
    exact h

/-! ### The calls on the way down -/

/-- The constants of the calls on the way down, over all levels. -/
noncomputable def cU (k₀ q₀ : ℕ) : ℕ :=
  ∑ d ∈ Finset.range q₀, (cSh (k₀ + d) (q₀ - d - 1) + cFt (k₀ + d) (q₀ - d - 1) +
    cCo (k₀ + d + 1) (q₀ - d - 1))

/-- The degrees of the calls on the way down, over all levels. -/
noncomputable def aU (k₀ q₀ : ℕ) : ℕ :=
  ∑ d ∈ Finset.range q₀, (aSh (k₀ + d) (q₀ - d - 1) + aFt (k₀ + d) (q₀ - d - 1) +
    aCo (k₀ + d + 1) (q₀ - d - 1))

theorem le_cU {d : ℕ} (hd : d < q₀) :
    cSh (k₀ + d) (q₀ - d - 1) ≤ cU k₀ q₀ ∧ cFt (k₀ + d) (q₀ - d - 1) ≤ cU k₀ q₀ ∧
      cCo (k₀ + d + 1) (q₀ - d - 1) ≤ cU k₀ q₀ ∧ aSh (k₀ + d) (q₀ - d - 1) ≤ aU k₀ q₀ ∧
      aFt (k₀ + d) (q₀ - d - 1) ≤ aU k₀ q₀ ∧ aCo (k₀ + d + 1) (q₀ - d - 1) ≤ aU k₀ q₀ := by
  have h1 := Finset.single_le_sum (f := fun d => cSh (k₀ + d) (q₀ - d - 1) +
    cFt (k₀ + d) (q₀ - d - 1) + cCo (k₀ + d + 1) (q₀ - d - 1)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hd)
  have h2 := Finset.single_le_sum (f := fun d => aSh (k₀ + d) (q₀ - d - 1) +
    aFt (k₀ + d) (q₀ - d - 1) + aCo (k₀ + d + 1) (q₀ - d - 1)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hd)
  unfold cU aU
  omega

theorem cpow_le {c a c' a' x : ℕ} (hc : c ≤ c') (ha : a ≤ a') :
    c * (x + 1) ^ a ≤ c' * (x + 1) ^ a' :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (Nat.succ_pos x) ha)

theorem lift_n {x c e A N Z : ℕ} (hZ : 1 ≤ Z) (h : x ≤ c * Z ^ e) (he : e ≤ A) :
    x ≤ c * (N + 1) * Z ^ A := by
  have h1 : Z ^ e ≤ Z ^ A := Nat.pow_le_pow_right hZ he
  have h2 : c * Z ^ A ≤ c * (N + 1) * Z ^ A := by
    rw [mul_assoc, mul_comm (N + 1), ← mul_assoc]; exact Nat.le_mul_of_pos_right _ (by omega)
  exact le_trans h (le_trans (Nat.mul_le_mul_left _ h1) h2)

theorem lift_n' {x c e A N Z : ℕ} (hZ : 1 ≤ Z) (h : x ≤ c * (N + 1) * Z ^ e) (he : e ≤ A) :
    x ≤ c * (N + 1) * Z ^ A :=
  le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ he))

theorem add_n {x y c c' N Z A : ℕ} (hx : x ≤ c * (N + 1) * Z ^ A) (hy : y ≤ c' * (N + 1) * Z ^ A) :
    x + y ≤ (c + c') * (N + 1) * Z ^ A := by
  rw [add_mul, add_mul]; omega

theorem mono_n {x c c' N Z A : ℕ} (hx : x ≤ c * (N + 1) * Z ^ A) (hc : c ≤ c') :
    x ≤ c' * (N + 1) * Z ^ A :=
  le_trans hx (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))

/-- **The calls on the way down.** -/
theorem down_le (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ d < q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ x ∈ lvR G P Q s k₀ q₀ d, ∀ c ∈ downCalls G P Q s k₀ q₀ x,
      realT G k₀ q₀ c + (realQ G k₀ q₀ c).length ≤
        C * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ A := by
  obtain ⟨c0, a0, hI⟩ := item_le_all k₀ q₀ hk
  obtain ⟨c1, a1, hV⟩ := single_le_all k₀ q₀ hk
  obtain ⟨c2, a2, hS⟩ := stp_le k₀ q₀ hk
  set cu := cU k₀ q₀
  set au := aU k₀ q₀
  set cs := cu * (c0 + 1) ^ au
  set as := a0 * au
  set cst := cu * (c2 + 1) * (c0 + 1) ^ au
  set ast := a2 + a0 * au
  set cco := cu * (cs + c1 + 1) ^ au
  set aco := (as + a1) * au
  set A := a0 + a1 + a2 + as + ast + aco
  refine ⟨cs + c0 + cst + (c0 + c2) + cco + (cs + c1), A, ?_⟩
  intro d hd n G P Q s x hx c hc
  set M := maxTreeSize G k₀ q₀ with hM
  have hZ : 1 ≤ M + 1 := by omega
  obtain ⟨hcS, hcF, hcC, haS, haF, haC⟩ := le_cU (k₀ := k₀) hd
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
  set m := q₀ - d - 1
  rw [show q₀ - d = m + 1 by omega] at hu
  have hτ := hI d hd.le n G P Q s x hx
  rw [hu] at hτ
  have hci := callInst_down G P Q s k₀ q₀ hk hd hx
  -- the shift
  have tSh : realT G k₀ q₀ (.shift (tree G (k₀ + d) (m + 1) u)) ≤ cs * (M + 1) ^ as := by
    have e : realT G k₀ q₀ (.shift (tree G (k₀ + d) (m + 1) u)) =
        cSh (k₀ + d) m * (wordLength (tree G (k₀ + d) (m + 1) u) + 1) ^ aSh (k₀ + d) m := by
      simp [realT, tree]
    rw [e]
    exact le_trans (cpow_le hcS haS) (pc_comp hτ)
  have hshm : RCall.shift x.2 ∈ downCalls G P Q s k₀ q₀ x := by simp [downCalls]
  have lSh : wordLength (tree G (k₀ + d + 1) m u) ≤ cs * (M + 1) ^ as := by
    have := realY_le hk (hci _ hshm)
    rw [hu] at this
    have e : (realY G k₀ q₀ (.shift (tree G (k₀ + d) (m + 1) u))).length =
        wordLength (tree G (k₀ + d + 1) m u) := by
      show wordLength (shOf G _) = _
      rw [show tree G (k₀ + d) (m + 1) u = tree G (k₀ + d) (m + 1) u from rfl,
        shOf_tree G u h1 hℓ]
    rw [e] at this
    exact le_trans this tSh
  have hst := hS d hd.le n G
  rw [show q₀ - d = m + 1 by omega, ← hM] at hst
  simp only [downCalls, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at hc
  rw [hu] at hc
  rcases hc with (rfl | rfl) | ⟨ν, hν, rfl⟩
  · -- the shift
    have q1 : (realQ G k₀ q₀ (.shift (tree G (k₀ + d) (m + 1) u))).length ≤ c0 * (M + 1) ^ a0 := hτ
    refine mono_n (add_n (lift_n hZ tSh (by omega)) (lift_n hZ q1 (by omega))) (by omega)
  · -- the far tree
    have e : realT G k₀ q₀ (.ftree (tree G (k₀ + d) (m + 1) u)) =
        cFt (k₀ + d) m * (wordLength (stp G (k₀ + d) (m + 1)) + 1) *
          (wordLength (tree G (k₀ + d) (m + 1) u) + 1) ^ aFt (k₀ + d) m := by
      simp [realT, tree]
    have t1 : realT G k₀ q₀ (.ftree (tree G (k₀ + d) (m + 1) u)) ≤ cst * (n + 1) * (M + 1) ^ ast := by
      rw [e]
      have p1 : wordLength (stp G (k₀ + d) (m + 1)) + 1 ≤ (c2 + 1) * (n + 1) * (M + 1) ^ a2 := by
        have : 1 ≤ (n + 1) * (M + 1) ^ a2 := Nat.one_le_iff_ne_zero.2 (by positivity)
        have e2 : (c2 + 1) * (n + 1) * (M + 1) ^ a2 = c2 * (n + 1) * (M + 1) ^ a2 +
            (n + 1) * (M + 1) ^ a2 := by ring
        omega
      have p2 : (wordLength (tree G (k₀ + d) (m + 1) u) + 1) ^ aFt (k₀ + d) m ≤
          (c0 + 1) ^ au * (M + 1) ^ (a0 * au) := by
        have := pc_comp (d := 1) (b := au) hτ
        refine le_trans (Nat.pow_le_pow_right (Nat.succ_pos _) haF) ?_
        simpa using this
      calc cFt (k₀ + d) m * (wordLength (stp G (k₀ + d) (m + 1)) + 1) *
            (wordLength (tree G (k₀ + d) (m + 1) u) + 1) ^ aFt (k₀ + d) m
          ≤ cu * ((c2 + 1) * (n + 1) * (M + 1) ^ a2) * ((c0 + 1) ^ au * (M + 1) ^ (a0 * au)) :=
            Nat.mul_le_mul (Nat.mul_le_mul hcF p1) p2
        _ = cst * (n + 1) * (M + 1) ^ ast := by
            simp only [cst, ast, pow_add]; ring
    have hcut : stpCut ((tree G (k₀ + d) (m + 1) u).k + 1) (stp G k₀ q₀) =
        stp G (k₀ + d) (m + 1) := stpCut_stp' G (by simp [tree]) (by simp [tree]; omega)
    have q1 : (realQ G k₀ q₀ (.ftree (tree G (k₀ + d) (m + 1) u))).length ≤
        (c0 + c2) * (n + 1) * (M + 1) ^ A := by
      show wordLength (tree G (k₀ + d) (m + 1) u,
        stpCut ((tree G (k₀ + d) (m + 1) u).k + 1) (stp G k₀ q₀)) ≤ _
      rw [hcut, wordLength_prod]
      exact add_n (lift_n hZ hτ (by omega)) (lift_n' hZ hst (by omega))
    refine mono_n (add_n (lift_n' hZ t1 (by omega)) q1) (by omega)
  · -- a composition
    obtain ⟨b, hb, rfl⟩ := faP_tree k₀ q₀ G hd h1 hℓ hν
    have hsh : shOf G (tree G (k₀ + d) (m + 1) u) = tree G (k₀ + d + 1) m u := shOf_tree G u h1 hℓ
    rw [hsh]
    have hν1 := hV (d + 1) hd n G b
    rw [show k₀ + (d + 1) = k₀ + d + 1 by omega, show q₀ - (d + 1) = m by omega] at hν1
    have hsum : wordLength (tree G (k₀ + d + 1) m u, tree G (k₀ + d + 1) m ![b]) ≤
        (cs + c1) * (M + 1) ^ (as + a1) := by
      rw [wordLength_prod]; exact pc_add lSh hν1
    have e : realT G k₀ q₀ (.compose (tree G (k₀ + d + 1) m u) (tree G (k₀ + d + 1) m ![b])) =
        cCo (k₀ + d + 1) m * (wordLength (tree G (k₀ + d + 1) m u,
          tree G (k₀ + d + 1) m ![b]) + 1) ^ aCo (k₀ + d + 1) m := by
      simp [realT, tree]
    have t1 : realT G k₀ q₀ (.compose (tree G (k₀ + d + 1) m u) (tree G (k₀ + d + 1) m ![b])) ≤
        cco * (M + 1) ^ aco := by
      rw [e]; exact le_trans (cpow_le hcC haC) (pc_comp hsum)
    have q1 : (realQ G k₀ q₀ (.compose (tree G (k₀ + d + 1) m u)
        (tree G (k₀ + d + 1) m ![b]))).length ≤ (cs + c1) * (M + 1) ^ (as + a1) := hsum
    refine mono_n (add_n (lift_n hZ t1 (by omega)) (lift_n hZ q1 (by omega))) (by omega)

end Lax185574Proofs.ResolveRam
