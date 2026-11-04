import Lax185574Proofs.MC.Asm.Thread

/-!
Assembly of thm:mc from its parts.

`mc_of_parts`: from a parallel combinator (`Par2Spec`), a brute-force
evaluator (`BruteSpec`) and a glue program (`GlueHyp`), the statement of
`Lax185574.ConstructionModelChecking`. The program is `par Ps Br` for
the pipeline thread `Ps` of `thread_spec`. The proof splits on
`(K + 1) ^ A ≤ |x| + 1`. If it holds and `n ≥ 1`, the pipeline thread
halts within `cP (m + 1)(n + 1)² (K + 1) ^ A` steps. Otherwise the input
is short or `n = 0`, and the brute force halts within `cb (|x| + 1)(n +
1) ^ ab` steps, which is at most a constant times `(m + 1)(K + 1) ^ (A (ab
+ 1))`. Every halting run of either thread is right, so the combinator
outputs the answer.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax808846.RamComputes Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.Width Lax185574.ConstructionModelChecking
open Lax271696.GraphEncoding
open Lax3.DistFO (rhoMinus rhoPlus)

theorem len_arith0 (m L : ℕ) : 3 * m + 6 + L ≤ (m + 1) * (L + 6) := by ring_nf; omega

theorem le_shift {a w Z : ℕ} (h : 2 ^ a * Z ≤ 2 ^ w) : Z ≤ 2 ^ (w - a) := by
  rcases Nat.eq_zero_or_pos Z with rfl | hZ
  · exact Nat.zero_le _
  have haw : a ≤ w := by
    by_contra hc
    have : 2 ^ w < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have : 2 ^ a ≤ 2 ^ a * Z := Nat.le_mul_of_pos_right _ hZ
    omega
  have e : 2 ^ w = 2 ^ a * 2 ^ (w - a) := by rw [← pow_add]; congr 1; omega
  rw [e] at h
  exact Nat.le_of_mul_le_mul_left h (by positivity)

set_option maxHeartbeats 1000000 in
open Classical in
/-- **thm:mc from its parts.** -/
theorem mc_of_parts {par : Program → Program → Program} {Kp : ℕ} (hpar : Par2Spec par Kp)
    {Br : Program} (hBr : BruteSpec Br) (hG : GlueHyp) :
    ∃ (p : Program) (e : ℕ), ∀ φ : Lax3.FirstOrder.FO 0, ∃ r d c b : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : List (PartialGraph (Fin n))) (K w : ℕ),
        IsConstructionSequence G s → width r d s ≤ K →
          ComputesInTime w p
            {x | EncodesInput x n G s φ ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
            (fun _ => if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0])
            (fun _ => c * s.length * (n + 1) ^ 2 * (K + 1) ^ b) := by
  obtain ⟨Ps, eP, hPs⟩ := thread_spec hG
  obtain ⟨eb, hBr'⟩ := hBr
  refine ⟨par Ps Br, eP + eb + 1, fun φ => ?_⟩
  obtain ⟨cP, A, hP⟩ := hPs φ
  obtain ⟨cb, ab, hb⟩ := hBr' φ
  set q := Lax3.FirstOrder.rank φ with hq
  set Lφ := (toWord φ).length with hLφ
  obtain ⟨C1, hC1⟩ : ∃ c, c = cP + cb * (Lφ + 6) + cb := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 2 ^ (Kp + 1) * (cP + cb + 1) + Kp * (C1 + 1) := ⟨_, rfl⟩
  refine ⟨rhoPlus 1 q, rhoPlus 1 q + 1 + q, c, A * (ab + 1), ?_⟩
  intro n G s K w hcs hK x ⟨hx, hadm⟩
  have hxin := hx
  obtain ⟨g, y, hg, ⟨σ, hyσ, hsσ⟩, hxe⟩ := hx
  subst hsσ
  have hx2 : x = g ++ (toWord σ ++ toWord φ) := by rw [hxe, hyσ, List.append_assoc]
  have hgl := hg.length_eq
  have hxl : x.length = g.length + (toWord σ).length + Lφ := by
    rw [hx2, hLφ, List.length_append, List.length_append, Nat.add_assoc]
  have hσl := script_length σ
  set X := x.length + maxEntry x + 1 with hXd
  have hne : x ≠ [] := List.ne_nil_of_length_pos (by rw [hxl]; omega)
  have hadmX : c * X ^ (eP + eb + 1) ≤ 2 ^ w := hadm _ (maxEntry_mem hne)
  have hX1 : 1 ≤ X := by omega
  have hXe : ∀ j, 1 ≤ X ^ j := fun j => Nat.one_le_pow _ _ hX1
  have hc1 : 2 ^ (Kp + 1) * (cP + cb + 1) ≤ c := by rw [hc]; omega
  have hc2 : Kp * (C1 + 1) ≤ c := by rw [hc]; omega
  have hcX : c ≤ c * X ^ (eP + eb + 1) := Nat.le_mul_of_pos_right _ (hXe _)
  -- word lengths
  have hKp : Kp < w := by
    have : 2 ^ (Kp + 1) ≤ 2 ^ w := by
      have : 2 ^ (Kp + 1) ≤ 2 ^ (Kp + 1) * (cP + cb + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    by_contra hc'
    have : 2 ^ w < 2 ^ (Kp + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hshift : ∀ Z, Z ≤ (cP + cb + 1) * X ^ (eP + eb + 1) → Z ≤ 2 ^ (w - Kp) := by
    intro Z hZ
    refine le_shift (le_trans (Nat.mul_le_mul_left _ hZ) ?_)
    calc 2 ^ Kp * ((cP + cb + 1) * X ^ (eP + eb + 1)) ≤ 2 ^ (Kp + 1) * (cP + cb + 1) * X ^ (eP + eb + 1) := by
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
      _ ≤ c * X ^ (eP + eb + 1) := Nat.mul_le_mul_right _ hc1
      _ ≤ 2 ^ w := hadmX
  have hxw : x.length < 2 ^ (w - Kp) := by
    have h1 : X ≤ X ^ (eP + eb + 1) := by
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (eP + eb + 1) := Nat.pow_le_pow_right hX1 (by omega)
    have := hshift (x.length + 1) (by
      calc x.length + 1 ≤ X := by omega
        _ ≤ X ^ (eP + eb + 1) := h1
        _ ≤ (cP + cb + 1) * X ^ (eP + eb + 1) := Nat.le_mul_of_pos_left _ (by omega))
    omega
  -- the two threads at `w - Kp`
  have hadmP : cP * X ^ eP ≤ 2 ^ (w - Kp) := hshift _ (by
    calc cP * X ^ eP ≤ cP * X ^ (eP + eb + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
      _ ≤ (cP + cb + 1) * X ^ (eP + eb + 1) := Nat.mul_le_mul_right _ (by omega))
  have hthr := hP n G g σ K (w - Kp) hg hcs hK (by rw [← hx2]; exact hadmP)
  rw [← hx2] at hthr
  obtain ⟨hPsound, hPrun⟩ := hthr
  have hbr := hb n G σ.run x (w - Kp) hxin (fun v hv => hshift _ (by
    have hv' : x.length + v + 1 ≤ X := by have := le_maxEntry hv; omega
    calc cb * (x.length + v + 1) ^ eb ≤ cb * X ^ (eP + eb + 1) :=
          Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left hv' _)
            (Nat.pow_le_pow_right hX1 (by omega)))
      _ ≤ (cP + cb + 1) * X ^ (eP + eb + 1) := Nat.mul_le_mul_right _ (by omega)))
  obtain ⟨hBsound, tb, htb, hBrun⟩ := hbr
  -- every halting run of the combinator is right
  obtain ⟨hfwd, hback⟩ := hpar Ps Br w x hKp hxw
  have hsound : ∀ z T, RunsTo w (par Ps Br) x z T → z = mcAns G φ := by
    intro z T hz
    obtain ⟨bb, t, ht⟩ := hback z T hz
    cases bb with
    | false => have := hPsound _ t ht; simpa using this
    | true => have := hBsound _ t ht; simpa using this
  -- the time
  set m := σ.steps.length with hm
  have hsl : σ.run.length = m + 1 := by rw [hm]; simp [Script.run]
  set Y := K + 1 with hYd
  have hY1 : 1 ≤ Y := by omega
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = (m + 1) * (n + 1) ^ 2 * Y ^ (A * (ab + 1)) := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by
    rw [hZd]; exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos m) (Nat.pow_pos (Nat.succ_pos n))) (Nat.pow_pos hY1)
  have hgood : ∃ (bb : Bool) (t : ℕ), t ≤ C1 * Z ∧
      RunsTo (w - Kp) (cond bb Br Ps) x (1 :: mcAns G φ) t := by
    by_cases hpipe : 1 ≤ n ∧ Y ^ A ≤ x.length + 1
    · obtain ⟨t, ht, hr⟩ := hPrun hpipe.1 hpipe.2
      refine ⟨false, t, le_trans ht ?_, hr⟩
      have h1 : Y ^ A ≤ Y ^ (A * (ab + 1)) := Nat.pow_le_pow_right hY1 (Nat.le_mul_of_pos_right _ (by omega))
      calc cP * (m + 1) * (n + 1) ^ 2 * Y ^ A ≤ cP * (m + 1) * (n + 1) ^ 2 * Y ^ (A * (ab + 1)) :=
            Nat.mul_le_mul_left _ h1
        _ = cP * Z := by rw [hZd]; ring
        _ ≤ C1 * Z := Nat.mul_le_mul_right _ (by rw [hC1]; omega)
    · refine ⟨true, tb, le_trans htb ?_, hBrun⟩
      by_cases hn : n = 0
      · subst hn
        have hE0 : edgeCount g = 0 := by
          have h1 := hg.offset_zero
          have h2 := hg.offset_last
          omega
        have hx3 : x.length + 1 ≤ (m + 1) * (Lφ + 6) := by
          have := len_arith0 m Lφ
          omega
        calc cb * (x.length + 1) * (0 + 1) ^ ab ≤ cb * ((m + 1) * (Lφ + 6)) := by
              simp only [zero_add, one_pow, mul_one]; exact Nat.mul_le_mul_left _ hx3
          _ ≤ cb * (Lφ + 6) * Z := by
              have : (m + 1) ≤ Z := by
                rw [hZd]; simp only [zero_add, one_pow, mul_one]
                exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hY1)
              calc cb * ((m + 1) * (Lφ + 6)) = cb * (Lφ + 6) * (m + 1) := by ring
                _ ≤ cb * (Lφ + 6) * Z := Nat.mul_le_mul_left _ this
          _ ≤ C1 * Z := Nat.mul_le_mul_right _ (by rw [hC1]; omega)
      · have hshort : x.length + 1 < Y ^ A := by
          by_contra hc'; exact hpipe ⟨by omega, by omega⟩
        have hnx : n + 1 ≤ x.length + 1 := by omega
        have h1 : (x.length + 1) * (n + 1) ^ ab ≤ Y ^ (A * (ab + 1)) := by
          calc (x.length + 1) * (n + 1) ^ ab ≤ Y ^ A * (Y ^ A) ^ ab :=
                Nat.mul_le_mul hshort.le (Nat.pow_le_pow_left (by omega) _)
            _ = Y ^ (A * (ab + 1)) := by rw [← pow_mul, ← pow_add]; congr 1; ring
        have h2 : Y ^ (A * (ab + 1)) ≤ Z := by
          rw [hZd]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos m) (Nat.pow_pos (Nat.succ_pos n)))
        calc cb * (x.length + 1) * (n + 1) ^ ab = cb * ((x.length + 1) * (n + 1) ^ ab) := by ring
          _ ≤ cb * Z := Nat.mul_le_mul_left _ (le_trans h1 h2)
          _ ≤ C1 * Z := Nat.mul_le_mul_right _ (by rw [hC1]; omega)
  obtain ⟨bb, t, ht, hr⟩ := hgood
  obtain ⟨T, hT, z, hz⟩ := hfwd bb (mcAns G φ) t hr (by unfold mcAns; split_ifs <;> simp)
  have hzz := hsound z T hz
  subst hzz
  refine ⟨T, le_trans hT ?_, hz⟩
  show Kp * (t + 1) ≤ c * σ.run.length * (n + 1) ^ 2 * (K + 1) ^ (A * (ab + 1))
  rw [hsl]
  calc Kp * (t + 1) ≤ Kp * ((C1 + 1) * Z) := Nat.mul_le_mul_left _ (by rw [Nat.succ_mul]; omega)
    _ = Kp * (C1 + 1) * Z := by ring
    _ ≤ c * Z := Nat.mul_le_mul_right _ hc2
    _ = c * (m + 1) * (n + 1) ^ 2 * (K + 1) ^ (A * (ab + 1)) := by rw [hZd]; ring

end Lax185574Proofs.MC
