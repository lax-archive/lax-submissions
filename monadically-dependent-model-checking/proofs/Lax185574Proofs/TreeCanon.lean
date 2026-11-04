import Lax185574Proofs.CanonJobs
import Lax185574Proofs.Words.TreeJobsLink
import Lax185574Proofs.RamCapped

/-!
One-pass transformations of type trees followed by restoring canonical
form, on the word RAM.

The program pipes the one-pass program `jobProg`, which writes the
transformed tree as a list of jobs with sets in arbitrary order, into the
program of `CanonJobs.canonJobs_program`, which brings the sets into
canonical form from the leaves up with the program of the canonical form
of one set (obs:canonical). `treeCanon` states that the composite
computes the header followed by `treeOut` of the root word.
-/

namespace Lax185574Proofs.TreeCanon

open Lax808846.Ram Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574Proofs.CanonJobs

/-- A bounded run appends values below the bound to the output, at most
one per unit of cost. -/
theorem BigStepB.out_lt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    ∃ o, σ'.out = σ.out ++ o ∧ (∀ v ∈ o, v < B) ∧ o.length ≤ k := by
  induction h with
  | skip => exact ⟨[], by simp, by simp, by simp⟩
  | assign _ => exact ⟨[], by simp, by simp, by simp⟩
  | store _ _ _ => exact ⟨[], by simp, by simp, by simp⟩
  | seq _ _ ih ih' =>
    obtain ⟨o, h1, h2, h3⟩ := ih
    obtain ⟨o', h1', h2', h3'⟩ := ih'
    refine ⟨o ++ o', by rw [h1', h1, List.append_assoc], fun v hv => ?_, by simp; omega⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h2 v hv
    · exact h2' v hv
  | ite_true _ _ ih =>
    obtain ⟨o, h1, h2, h3⟩ := ih
    exact ⟨o, h1, h2, by omega⟩
  | ite_false _ _ ih =>
    obtain ⟨o, h1, h2, h3⟩ := ih
    exact ⟨o, h1, h2, by omega⟩
  | while_true _ _ _ ih ih' =>
    obtain ⟨o, h1, h2, h3⟩ := ih
    obtain ⟨o', h1', h2', h3'⟩ := ih'
    refine ⟨o ++ o', by rw [h1', h1, List.append_assoc], fun v hv => ?_, by simp; omega⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact h2 v hv
    · exact h2' v hv
  | while_false _ => exact ⟨[], by simp, by simp, by simp⟩
  | read _ => exact ⟨[], by simp, by simp, by simp⟩
  | write he =>
    exact ⟨[_], rfl, fun v hv => by
      simp at hv; subst hv; exact (Expr.eval_and_lt_of_evalB he).2, by simp⟩

theorem Run.out_lt {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) :
    ∃ o, σ'.out = σ.out ++ o ∧ (∀ v ∈ o, v < B) ∧ o.length ≤ K := by
  obtain ⟨k, hk, hb⟩ := h
  obtain ⟨o, h1, h2, h3⟩ := BigStepB.out_lt hb
  exact ⟨o, h1, h2, by omega⟩

theorem maxEntry_le_of {x : List ℕ} {b : ℕ} (h : ∀ v ∈ x, v ≤ b) : maxEntry x ≤ b := by
  by_cases hx : x = []
  · subst hx; simp [maxEntry]
  · exact h _ (maxEntry_mem hx)

theorem aux_cost {a K Y : ℕ} (h : a ≤ K * Y) (hY : 1 ≤ Y) : a + 1000 ≤ (K + 1000) * Y := by
  rw [add_mul]
  have : 1000 ≤ 1000 * Y := Nat.le_mul_of_pos_right _ hY
  omega

/-- The size factor of a layout. -/
def lszOf (L : Layout) : ℕ := L.temps + 2 + L.scalars.length + L.arrays.length + 1

set_option maxHeartbeats 4000000 in
/-- **A transformation of a type tree with canonical form restored.** The
pipe of `jobProg` into the canonical form of jobs computes the header
and `treeOut` of the root word, at every word length with room for a
fixed power of the size of the input, in time a fixed power of its
length. -/
theorem treeCanon (readArgs subCmd grdCmd : Com) (L : Layout)
    (hok : Com.Ok L (jobProg readArgs subCmd grdCmd)) :
    ∃ (p : Program) (e : ℕ), ∀ Kh : ℕ, ∃ C : ℕ,
      ∀ (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop) (Ks Kg Ka : ℕ)
        (k q ℓ : ℕ) (t : Node q ℓ) (argW : List ℕ) (G olv : ℕ),
        HookFrame subCmd → HookFrame grdCmd → ArgFrame readArgs →
        SubOK subCmd sub Dat (valBound 8 2 ([k, q, ℓ] ++ toWord t ++ argW)) Ks →
        GrdOK grdCmd gsub Dat (valBound 8 2 ([k, q, ℓ] ++ toWord t ++ argW)) Kg → DatOK Dat →
        Spec (valBound 8 2 ([k, q, ℓ] ++ toWord t ++ argW))
          (fun τ => τ.inp = argW ∧ τ.vars "hl" = ℓ ∧ τ.arrs "gt" = List.replicate G 0)
          readArgs (fun _ τ' => Dat τ' ∧ τ'.vars "ol" = olv) Ka →
        (∀ dd ≤ q, ∀ tg kk v r, (v ∈ toWord t ∨ v = 0) → sub tg kk dd v = some r →
          r < valBound 8 2 ([k, q, ℓ] ++ toWord t ++ argW)) →
        (∀ dd ≤ q, ∀ i r, (i ∈ toWord t ∨ i = 0) → gsub dd i = some r →
          r < valBound 8 2 ([k, q, ℓ] ++ toWord t ++ argW)) →
        olv < valBound 8 2 ([k, q, ℓ] ++ toWord t ++ argW) →
        Ks + Kg + Ka ≤ Kh * (([k, q, ℓ] ++ toWord t ++ argW).length + 1) →
        ∀ w : ℕ, C * (([k, q, ℓ] ++ toWord t ++ argW).length +
            maxEntry ([k, q, ℓ] ++ toWord t ++ argW) + 1) ^ e ≤ 2 ^ w →
          (∀ y T, RunsTo w p ([k, q, ℓ] ++ toWord t ++ argW) y T →
            y = [k, q, olv] ++ treeOut sub gsub q 0 (toWord t ++
              List.replicate (([k, q, ℓ] ++ toWord t ++ argW).length + 1 - (toWord t).length) 0) 0) ∧
          ∃ T ≤ C * (([k, q, ℓ] ++ toWord t ++ argW).length + 1) ^ e,
            RunsTo w p ([k, q, ℓ] ++ toWord t ++ argW) ([k, q, olv] ++ treeOut sub gsub q 0 (toWord t ++
              List.replicate (([k, q, ℓ] ++ toWord t ++ argW).length + 1 - (toWord t).length) 0) 0) T := by
  obtain ⟨pCT, KC, eC, hCT⟩ := canonJobs_program
  set PJ := compileProgram L (jobProg readArgs subCmd grdCmd) with hPJ
  obtain ⟨p, KP, hp⟩ := pipe_sound PJ pCT idRw fstRw
  refine ⟨p, 5 * eC + 5, fun Kh => ?_⟩
  set H := (Kh + 1000) * 1000 with hH
  set H' := H + 10 with hH'
  set Lsz := lszOf L with hLsz
  set C0 := KC * (H' + 9) ^ eC + 8 * Lsz + KP + H' + 1 with hC0
  set C1 := L.const * H + KC * (H' + 1) ^ eC + 10 with hC1
  set C := 4 * C0 * (KP + 1) * C1 with hC
  refine ⟨C, fun sub gsub Dat Ks Kg Ka k q ℓ t argW G olv hFs hFg hFa hS hG hD hA hsub hgsub holB hKh w hadm => ?_⟩
  set x := [k, q, ℓ] ++ toWord t ++ argW with hx
  set n := x.length with hn
  set M := maxEntry x with hM
  set Z := n + M + 1 with hZ
  set Y := n + 1 with hY
  set e := 5 * eC + 5 with he
  set B := valBound 8 2 x with hB
  have hBZ : B = 8 * Z ^ 2 := rfl
  set X := toWord t ++ List.replicate (n + 1 - (toWord t).length) 0 with hX
  have htn : (toWord t).length + 3 ≤ n := by rw [hn, hx]; simp
  have hXl : X.length = n + 1 := by rw [hX]; simp; omega
  have hY1 : 1 ≤ Y := by omega
  have hYZ : Y ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  have hC0p : 1 ≤ C0 := by omega
  have hC1p : 1 ≤ C1 := by omega
  have hZe : Z ≤ Z ^ e := by
    calc Z = Z ^ 1 := (pow_one _).symm
      _ ≤ Z ^ e := Nat.pow_le_pow_right hZ1 (by omega)
  -- the room
  set D := 2 ^ (w - 2) with hDw
  have hCbig : C0 ≤ C / 4 := by
    rw [hC, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hCZ : 4 * (C0 * Z ^ e) ≤ 2 ^ w := by
    have : 4 * (C / 4) ≤ C := Nat.mul_div_le C 4
    calc 4 * (C0 * Z ^ e) ≤ 4 * (C / 4 * Z ^ e) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hCbig)
      _ = 4 * (C / 4) * Z ^ e := by ring
      _ ≤ C * Z ^ e := Nat.mul_le_mul_right _ this
      _ ≤ 2 ^ w := hadm
  have hw2 : 2 ≤ w := by
    by_contra hlt
    have : 2 ^ w ≤ 2 := by
      have : w ≤ 1 := by omega
      calc 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 := by norm_num
    have : 4 ≤ 4 * (C0 * Z ^ e) := by
      have : 1 ≤ C0 * Z ^ e := Nat.mul_le_mul hC0p (le_trans hZ1 hZe)
      omega
    omega
  have h4D : 2 ^ w = 4 * D := by
    rw [hDw, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hCD : C0 * Z ^ e ≤ D := Nat.le_of_mul_le_mul_left (h4D ▸ hCZ) (by norm_num)
  have hroom : ∀ c a, c ≤ C0 → a ≤ e → c * Z ^ a ≤ D := fun c a hc ha =>
    le_trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hZ1 ha)) hCD
  have hxD : n < D := by
    have hc1 : H' + 1 ≤ C0 := by rw [hC0]; exact Nat.le_add_left _ _
    have := hroom (H' + 1) 1 hc1 (by rw [he]; exact Nat.le_add_left _ _)
    rw [pow_one] at this
    have : n < (H' + 1) * Z := by
      have : Z ≤ (H' + 1) * Z := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  have hLszD : Lsz * B ≤ D := by
    rw [hBZ]
    have := hroom (8 * Lsz) 2 (by omega) (by omega)
    calc Lsz * (8 * Z ^ 2) = 8 * Lsz * Z ^ 2 := by ring
      _ ≤ D := this
  have hKPD : KP ≤ D := by
    have := hroom KP 0 (by omega) (by omega)
    simpa using this
  -- the one-pass program
  have hxB : ∀ v ∈ x, v < B := by
    intro v hv
    have h1 := le_maxEntry hv
    rw [hBZ]
    have : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
    omega
  have hBn : (n + 2) * (n + 2) < B := by
    rw [hBZ]
    have : n + 2 ≤ 2 * Z := by omega
    have : (n + 2) * (n + 2) ≤ 2 * Z * (2 * Z) := Nat.mul_le_mul this this
    have : 0 < Z ^ 2 := by positivity
    have : 2 * Z * (2 * Z) = 4 * Z ^ 2 := by ring
    omega
  have hq1B : q + 1 < B := by
    have hqM : q ≤ M := le_maxEntry (by rw [hx]; simp)
    have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
    rw [hBZ]; omega
  obtain ⟨σ', N, PA, DA, FA, hrun, hnodes, hscan, hp0, hd0, hN1, hNt, hout⟩ :=
    jobProg_run readArgs subCmd grdCmd sub gsub Dat B Ks Kg Ka hFs hFg hFa hS hG hD k q ℓ t argW G olv hA
      hxB hBn hsub hgsub holB hq1B
  rw [← hx, ← hn] at hrun
  rw [← hn, ← hX] at hnodes hscan hout
  set js := rawJobs sub gsub X q N PA DA FA with hjs
  set fin := rawFinal k q olv N with hfin
  set yw := toWord (js, fin) with hyw
  -- the cost and the output of the one-pass program
  have hcost : jobCost Ks Kg Ka n ≤ H * Y ^ 5 := by
    have h1 := jobCost_le Ks Kg Ka n
    have h2 : Ks + Kg + Ka + 1000 ≤ (Kh + 1000) * Y := aux_cost hKh hY1
    calc jobCost Ks Kg Ka n ≤ (Ks + Kg + Ka + 1000) * 1000 * (n + 1) ^ 4 := h1
      _ ≤ (Kh + 1000) * Y * 1000 * Y ^ 4 := by
        rw [← hY]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
      _ = H * Y ^ 5 := by rw [hH]; ring
  obtain ⟨o, ho1, ho2, ho3⟩ := Run.out_lt hrun
  have hσ0 : (initEnv (jobExt n G) x).out = [] := rfl
  rw [hσ0, List.nil_append, hout] at ho1
  rw [← ho1] at ho2 ho3
  have hyl : yw.length ≤ H * Y ^ 5 := le_trans ho3 hcost
  have hyM : maxEntry yw ≤ B := maxEntry_le_of fun v hv => (ho2 v hv).le
  obtain ⟨⟨t1, ht1, hr1⟩, hu1⟩ := glue_runsTo hok (B := B) (v := w - 2) (ext := jobExt n G)
    (by rw [hBZ]; have : 1 ≤ Z ^ 2 := Nat.one_le_pow _ _ hZ1; omega) hLszD (fun v hv => hxB v hv) hrun
  rw [hout] at hr1 hu1
  -- the canonical form of the jobs
  have hwf : JobsWF js fin := rawJobs_wf sub gsub X q N PA DA FA k olv hscan hN1
  have hXne : X ≠ [] := by rw [← List.length_pos_iff, hXl]; omega
  have hS : jobSize js fin ≤ H' * Y ^ 5 := by
    have h1 := jobSize_le js fin X.length (fun j hj => by
      rw [hjs, length_rawJobs] at hj
      exact rawJobs_query_le sub gsub X q N PA DA FA hnodes hscan hXne hj)
    have h2 : (jobsOut js fin).length ≤ n + 3 := by
      rw [hjs, hfin, rawJobs_out sub gsub X q N PA DA FA k olv hnodes hscan hp0 hd0 hN1]
      have := length_treeOut_le sub gsub q 0 ℓ X 0 t (List.replicate (n + 1 - (toWord t).length) 0)
        (by rw [hX]; simp)
      simp; omega
    have h3 : js.length = 2 * N := length_rawJobs sub gsub X q N PA DA FA
    rw [h3, hXl] at h1
    have h4 : 2 * N + 2 * (2 * N * (n + 1)) + (n + 3) ≤ 10 * Y ^ 5 := by
      have hN : N ≤ Y := by omega
      have h5 : N * (n + 1) ≤ Y * Y := Nat.mul_le_mul hN le_rfl
      have h6 : Y * Y ≤ Y ^ 5 := by
        calc Y * Y = Y ^ 2 := by ring
          _ ≤ Y ^ 5 := Nat.pow_le_pow_right hY1 (by omega)
      have h7 : Y ≤ Y ^ 5 := by
        calc Y = Y ^ 1 := (pow_one _).symm
          _ ≤ Y ^ 5 := Nat.pow_le_pow_right hY1 (by omega)
      have : 2 * (2 * N * (n + 1)) = 4 * (N * (n + 1)) := by ring
      omega
    have : yw.length = (toWord (js, fin)).length := rfl
    rw [hH']
    have e : (H + 10) * Y ^ 5 = H * Y ^ 5 + 10 * Y ^ 5 := by ring
    omega
  have hSM : jobSize js fin + maxEntry yw + 1 ≤ (H' + 9) * Z ^ 5 := by
    have h1 : Y ^ 5 ≤ Z ^ 5 := Nat.pow_le_pow_left hYZ 5
    have h2 : Z ^ 2 ≤ Z ^ 5 := Nat.pow_le_pow_right hZ1 (by omega)
    have h3 : 1 ≤ Z ^ 5 := Nat.one_le_pow _ _ hZ1
    have h4 := Nat.mul_le_mul_left H' h1
    rw [hBZ] at hyM
    have e : (H' + 9) * Z ^ 5 = H' * Z ^ 5 + 8 * Z ^ 5 + Z ^ 5 := by ring
    omega
  have hCTroom : KC * (jobSize js fin + maxEntry yw + 1) ^ eC ≤ 2 ^ (w - 2) := by
    have h1 : (jobSize js fin + maxEntry yw + 1) ^ eC ≤ (H' + 9) ^ eC * Z ^ (5 * eC) := by
      rw [pow_mul, ← mul_pow]; exact Nat.pow_le_pow_left hSM _
    have h2 := hroom (KC * (H' + 9) ^ eC) (5 * eC) (by omega) (by omega)
    calc KC * (jobSize js fin + maxEntry yw + 1) ^ eC ≤ KC * ((H' + 9) ^ eC * Z ^ (5 * eC)) :=
          Nat.mul_le_mul_left _ h1
      _ = KC * (H' + 9) ^ eC * Z ^ (5 * eC) := by ring
      _ ≤ D := h2
  obtain ⟨hCTs, t2, ht2, hr2⟩ := hCT js fin hwf (w - 2) hCTroom
  have hres : jobsOut js fin = [k, q, olv] ++ treeOut sub gsub q 0 X 0 :=
    rawJobs_out sub gsub X q N PA DA FA k olv hnodes hscan hp0 hd0 hN1
  rw [hres] at hCTs hr2
  -- the pipe
  have hyD : yw.length < D := by
    have hc1 : H' ≤ C0 := by rw [hC0]; exact Nat.le_succ_of_le (Nat.le_add_left H' _)
    have := hroom H' 5 hc1 (by rw [he]; exact Nat.le_add_left _ _)
    have : H * Y ^ 5 < H' * Z ^ 5 := by
      have : H * Y ^ 5 ≤ H * Z ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hYZ 5)
      have : 1 ≤ Z ^ 5 := Nat.one_le_pow _ _ hZ1
      have e : H' * Z ^ 5 = H * Z ^ 5 + 10 * Z ^ 5 := by rw [hH']; ring
      omega
    omega
  have hx2 : x.length < 2 ^ (w - 2) := hxD
  obtain ⟨hpf, hpb⟩ := hp w x hKPD (idRw_fits (lt_of_lt_of_le hx2 (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 2))))
  simp only [idRw_apply, idRw_cost, fstRw_apply, fstRw_cost, Matrix.cons_val_zero] at hpf hpb
  refine ⟨fun y T hy => ?_, ?_⟩
  · obtain ⟨y', t1', ht1', hyl', h1', h2'⟩ := hpb y T hy
    have := hu1 y' t1' h1'
    subst this
    obtain ⟨t2', -, h2''⟩ := h2' (fstRw_fits (lt_of_lt_of_le hyD (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 2))) (lt_of_lt_of_le hx2 (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 2))))
    exact hCTs y t2' h2''
  · obtain ⟨T, hT, hrT⟩ := hpf yw _ t1 t2 hyD.le (fstRw_fits (lt_of_lt_of_le hyD (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 2))) (lt_of_lt_of_le hx2 (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le w 2)))) hr1 hr2
    refine ⟨T, le_trans hT ?_, hrT⟩
    -- the time
    have hYe5 : Y ^ 5 ≤ Y ^ e := Nat.pow_le_pow_right hY1 (by omega)
    have hYeC : Y ^ (5 * eC) ≤ Y ^ e := Nat.pow_le_pow_right hY1 (by omega)
    have hYe1 : 1 ≤ Y ^ e := Nat.one_le_pow _ _ hY1
    have ht1b : t1 ≤ L.const * H * Y ^ e + 1 := by
      have : L.const * jobCost Ks Kg Ka n ≤ L.const * (H * Y ^ 5) := Nat.mul_le_mul_left _ hcost
      have : L.const * (H * Y ^ 5) ≤ L.const * H * Y ^ e := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hYe5
      omega
    have ht2b : t2 ≤ KC * (H' + 1) ^ eC * Y ^ e := by
      have h1 : jobSize js fin + 1 ≤ (H' + 1) * Y ^ 5 := by
        have : 1 ≤ Y ^ 5 := Nat.one_le_pow _ _ hY1
        have e : (H' + 1) * Y ^ 5 = H' * Y ^ 5 + Y ^ 5 := by ring
        omega
      have h2 : (jobSize js fin + 1) ^ eC ≤ (H' + 1) ^ eC * Y ^ (5 * eC) := by
        rw [pow_mul, ← mul_pow]; exact Nat.pow_le_pow_left h1 _
      calc t2 ≤ KC * (jobSize js fin + 1) ^ eC := ht2
        _ ≤ KC * ((H' + 1) ^ eC * Y ^ (5 * eC)) := Nat.mul_le_mul_left _ h2
        _ = KC * (H' + 1) ^ eC * Y ^ (5 * eC) := by ring
        _ ≤ KC * (H' + 1) ^ eC * Y ^ e := Nat.mul_le_mul_left _ hYeC
    have hsum : t1 + t2 + 3 + 3 ≤ C1 * Y ^ e := by
      have e : C1 * Y ^ e = L.const * H * Y ^ e + KC * (H' + 1) ^ eC * Y ^ e + 10 * Y ^ e := by
        rw [hC1]; ring
      omega
    have hCC : KP * C1 ≤ C := by
      rw [hC]
      calc KP * C1 ≤ (KP + 1) * C1 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 4 * C0 * ((KP + 1) * C1) := Nat.le_mul_of_pos_left _ (by omega)
        _ = 4 * C0 * (KP + 1) * C1 := by ring
    calc KP * (t1 + t2 + 3 + 3) ≤ KP * (C1 * Y ^ e) := Nat.mul_le_mul_left _ hsum
      _ = KP * C1 * Y ^ e := by ring
      _ ≤ C * Y ^ e := Nat.mul_le_mul_right _ hCC

end Lax185574Proofs.TreeCanon
