import Lax185574Proofs.ResolveRam.Glue.Fin

/-!
The first round of the glue program of lem:resolve-lift as one command.

After the tag, `round0 e d` reads the length of the input and the input,
locates the parts, and for `n = 0` writes `0 :: zOut`, six zeros,
otherwise the head of the position of the scatter type and the query of
the switch, with the guard of exponent `e` and factor `2 ^ d` on the
query of slot F (`round0_run`). The output is `gOut0`, and `ovf` stays
`0` exactly when the checks pass (`ok0`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574.DistanceMatrix

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem mem_mid0 {v : ℕ} (h : v ∈ mid0) : v ≤ 4 ∨ v = s3W.length ∨ v = qE0.length := by
  simp only [mid0, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

attribute [local irreducible] s3W k0 mid0

/-- The output for the empty graph. -/
def end0 : Com := .seq (.assign "po" (.lit 0)) (.seq (pushLits [0, 0, 0, 0, 0, 0]) finEnd)

/-- The first round after the tag. -/
noncomputable def round0 (e d : ℕ) : Com :=
  .seq (.read "nx") (.seq rdX (.seq locate
    (.ite (.eq (.var "gn") (.lit 0)) end0 (.seq fill0 (finCall e d)))))

/-- The output of the first round. -/
noncomputable def gOut0 : List ℕ :=
  if n = 0 then [0, 0, 0, 0, 0, 0] else hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp

/-- The checks of the first round pass. -/
noncomputable def ok0 (W e d : ℕ) : Prop :=
  if n = 0 then maxEntry [0, 0, 0, 0, 0, 0] < W / 32 / 32
  else guardOK W e d (ySz (xIn G k₀ q₀ P Q s)) (qF G k₀ q₀ .stp) ∧
    maxEntry (hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp) < W / 32 / 32

noncomputable instance (W e d : ℕ) : Decidable (ok0 G P Q s k₀ q₀ W e d) := by
  unfold ok0; split <;> infer_instance

theorem maxEntry_app (a b : List ℕ) : maxEntry (a ++ b) = max (maxEntry a) (maxEntry b) := by
  induction a with
  | nil => simp [maxEntry]
  | cons x a ih => simp only [maxEntry, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih]; omega

theorem forall_app {a b : List ℕ} {W : ℕ} (ha : ∀ v ∈ a, v ≤ W) (hb : ∀ v ∈ b, v ≤ W) :
    ∀ v ∈ a ++ b, v ≤ W := fun v hv => (List.mem_append.1 hv).elim (ha v) (hb v)

theorem maxEntry_le_of_sub {a b : List ℕ} (h : ∀ v ∈ a, v ∈ b) : maxEntry a ≤ maxEntry b :=
  maxEntry_le fun v hv => le_maxEntry (h v hv)

theorem gOut_zero (z : List ℕ) (hd : ℕ → List ℕ) (hz : n = 0 → z = [0, 0, 0, 0, 0])
    (hh : 1 ≤ n → hd 0 = hdOf G P Q s k₀ q₀ .stp) :
    gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) hd z 0 = gOut0 G P Q s k₀ q₀ := by
  unfold gOut gOut0
  by_cases hn : n = 0
  · rw [if_pos hn]
    have : rcalls G P Q s k₀ q₀ = [] := by simp [rcalls, hn]
    rw [this, hz hn]; rfl
  · rw [if_neg hn]
    have : (rcalls G P Q s k₀ q₀)[0]? = some .stp := by simp [rcalls, hn]
    rw [this, hh (by omega)]

set_option maxHeartbeats 400000 in
/-- **The first round.** -/
theorem round0_run {W e d : ℕ} {σ : Env} (hinp : σ.inp = (xIn G k₀ q₀ P Q s).length :: xIn G k₀ q₀ P Q s ++ [0])
    (hW : σ.vars "W" = W) (hovf : σ.vars "ovf" = 0) (hcap : (σ.arrs "OB").length = W + 1)
    (hxl : (xIn G k₀ q₀ P Q s).length ≤ (σ.arrs "x").length)
    (hWb : 8 * ySz (xIn G k₀ q₀ P Q s) + 2 * k0 ≤ W) :
    ∃ σ', Run (W + 1) (round0 e d) σ σ'
        (200 * ((xIn G k₀ q₀ P Q s).length + 1) + 100 * k0 + 60 * (e + 1) + 30 * 2 ^ d + 5000) ∧
      σ'.out = σ.out ++ gOut0 G P Q s k₀ q₀ ∧
      σ'.vars "ovf" = (if ok0 G P Q s k₀ q₀ W e d then 0 else 1) := by
  set X := xIn G k₀ q₀ P Q s with hXdef
  have hyX : X.length + maxEntry X + 1 = ySz X := rfl
  have hk64 : 64 + s3W.length + qE0.length ≤ k0 := by unfold k0; omega
  have hvX : ∀ v ∈ X, v < W + 1 := fun v hv => by have := le_maxEntry hv; omega
  -- read the length and the input
  set σ1 : Env := { σ.setVar "nx" X.length with inp := X ++ [0] }
  have r1 : Run (W + 1) (.read "nx") σ σ1 1 := Run.read hinp
  obtain ⟨σ2, r2, i2, m2, x2, l2, o2, v2, a2⟩ := rdX_run (B := W + 1) (x := X) (rest := [0]) (σ := σ1)
    rfl (by simp [σ1]) (by simp [σ1]; omega) (by omega) hvX
  have hX2 : PreAt "x" X σ2 := x2
  -- locate
  obtain ⟨σ3, r3, n3, p3, q3, a3, o3, i3, v3⟩ := locate_run G (B := W + 1) (X := X)
    (rest := [P, Q, if s then 1 else 0] ++ toWord (family G k₀ q₀)) hX2 (xIn_split G P Q s k₀ q₀)
    (by omega) hvX
  have hX3 : PreAt "x" X σ3 := fun i h => by rw [a3]; exact hX2 i h
  have hW3 : σ3.vars "W" = W := by
    rw [v3 _ (by decide), v2 _ (by decide)]; simp [σ1, hW]
  have hovf3 : σ3.vars "ovf" = 0 := by
    rw [v3 _ (by decide), v2 _ (by decide)]; simp [σ1, hovf]
  have hcap3 : (σ3.arrs "OB").length = W + 1 := by
    rw [a3, a2 _ (by decide)]; simp [σ1, hcap]
  have hnx3 : σ3.vars "nx" = X.length := by rw [v3 _ (by decide), v2 _ (by decide)]; simp [σ1]
  have hmx3 : σ3.vars "mx" = maxEntry X := by rw [v3 _ (by decide), m2]
  have hc : (Cond.eq (.var "gn") (.lit 0)).evalB (W + 1) σ3 = some (n == 0) :=
    evalB_condEq (ev_var n3 (by
      have : n < X.length := by rw [hXdef, xIn_split, StpRam.toWord_pg]; simp <;> omega
      omega)) (evalB_lit (by omega))
  by_cases hn : n = 0
  · -- the empty graph
    have r4 : Run (W + 1) (.assign "po" (.lit 0)) σ3 (σ3.setVar "po" 0) 2 := Run.assign (evalB_lit (by omega))
    obtain ⟨σ5, r5, F5, o5⟩ := pushLits_run (W := W) (l := [0, 0, 0, 0, 0, 0]) (Filled.empty "OB" "po" σ3)
      (by simp) (by simp [hcap3]; omega) (by simp; omega)
    have hW5 : σ5.vars "W" = W := by rw [o5.vars _ (by decide)]; simp [hW3]
    have hov5 : σ5.vars "ovf" = 0 := by rw [o5.vars _ (by decide)]; simp [hovf3]
    obtain ⟨σ6, r6, o6, ov6⟩ := finEnd_run (o := [0, 0, 0, 0, 0, 0]) hW5 (by omega) (by simpa using F5)
      (by simp; omega) (by simp) hov5
    refine ⟨σ6, ?_, ?_, ?_⟩
    · unfold round0
      refine (Run.seq r1 (Run.seq r2 (Run.seq r3
        (Run.ite_true (by rw [hc]; simp [hn]) (Run.seq r4 (Run.seq r5 r6)))))).mono ?_
      simp only [Cond.size, Expr.size, List.length_cons, List.length_nil]
      omega
    · rw [o6, o5.out]; simp [gOut0, hn, o3, o2, σ1]
    · rw [ov6]; simp [ok0, hn]
  · have hn1 : 1 ≤ n := by omega
    obtain ⟨σ4, r4, F4, qa4, ql4, gX4, o4⟩ := fill0_run G P Q s k₀ q₀ (W := W) hn1 hX3 p3 q3 n3 hnx3 hmx3
      hcap3 (by rw [← hXdef]; omega)
    simp only [← hXdef] at gX4
    have hO := out0_eq G P Q s k₀ q₀
    simp only [← hXdef] at hO
    have hOA : hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp =
        (hdOf G P Q s k₀ q₀ .stp ++ [s3W.length, qE0.length, (qF G k₀ q₀ .stp).length] ++ s3W ++ qE0) ++
          qF G k₀ q₀ .stp := by
      rw [rQ_stp]; simp
    set O := hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp with hOdef
    set qq := qF G k₀ q₀ .stp
    set pre := hdOf G P Q s k₀ q₀ .stp ++ [s3W.length, qE0.length, qq.length] ++ s3W ++ qE0
    have hOlen : O.length ≤ X.length + k0 + 30 := by
      have h1 := congrArg List.length hO
      simp only [List.length_append, List.length_cons, List.length_nil, length_mid0] at h1
      have h2 := qF_len G P Q s k₀ q₀
      simp only [← hXdef] at h2
      rw [qF_stp] at h2
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      rw [h1]; omega
    have hlO : O.length + 1 ≤ W := by
      have h1 := congrArg List.length hO
      have h2 := qF_len G P Q s k₀ q₀
      rw [qF_stp] at h2
      simp only [← hXdef] at h2
      simp only [List.length_append, List.length_cons, List.length_nil, length_mid0] at h1 h2
      rw [h1]; omega
    have hvO : ∀ v ∈ O, v ≤ W := by
      have hsub1 : ∀ v ∈ toWord G, v ∈ X := fun v hv => by
        rw [hXdef, xIn_split]; exact List.mem_append_left _ hv
      have hsub2 : ∀ v ∈ toWord (family G k₀ q₀), v ∈ X := fun v hv => by
        rw [hXdef, xIn_split]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hv))
      have hsub3 : ∀ v ∈ toWord (distMatrix G), v ∈ X := fun v hv => by
        rw [hXdef, xIn_split]; exact List.mem_append_right _ (List.mem_append_left _ hv)
      obtain ⟨h0, h1, h2, h4, h5, -⟩ := xIn_at G P Q s k₀ q₀ hn1
      simp only [← hXdef] at h0 h1 h2 h4 h5
      have g0 := getD_le_ySz X ((toWord G).length + (toWord (distMatrix G)).length)
      have g1 := getD_le_ySz X ((toWord G).length + (toWord (distMatrix G)).length + 1)
      have g2 := getD_le_ySz X ((toWord G).length + (toWord (distMatrix G)).length + 2)
      have g4 := getD_le_ySz X ((toWord G).length + (toWord (distMatrix G)).length + 4)
      have g5 := getD_le_ySz X ((toWord G).length + (toWord (distMatrix G)).length + 5)
      rw [h0] at g0; rw [h1] at g1; rw [h2] at g2; rw [h4] at g4; rw [h5] at g5
      have hnX : n ≤ X.length := by rw [hXdef, xIn_split, StpRam.toWord_pg]; simp <;> omega
      have hyW : ySz X ≤ W := by omega
      have hmX : maxEntry X + 1 ≤ ySz X := by unfold ySz; omega
      have p1 : ∀ v ∈ [X.length + 1, 22], v ≤ W := by intro v hv; simp at hv; unfold ySz at hyW; omega
      have p2 : ∀ v ∈ [X.length, 0, ySz X, X.length, n, P, Q, if s then 1 else 0, k₀, q₀], v ≤ W := by
        intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; unfold ySz at hyW; omega
      have p3 : ∀ v ∈ mid0, v ≤ W := by intro v hv; have := mem_mid0 hv; omega
      have p4 : ∀ v ∈ [X.length - 1], v ≤ W := by intro v hv; simp at hv; unfold ySz at hyW; omega
      have p5 : ∀ v ∈ s3W ++ qE0, v ≤ W := fun v hv => by have := mem_k0 hv; omega
      have p6 : ∀ v ∈ toWord G, v ≤ W := fun v hv => by have := le_maxEntry (hsub1 v hv); omega
      have p7 : ∀ v ∈ [k₀, q₀], v ≤ W := by intro v hv; simp at hv; omega
      have p8 : ∀ v ∈ toWord (family G k₀ q₀), v ≤ W := fun v hv => by
        have := le_maxEntry (hsub2 v hv); omega
      have p9 : ∀ v ∈ toWord (distMatrix G), v ≤ W := fun v hv => by
        have := le_maxEntry (hsub3 v hv); omega
      rw [hO]
      exact forall_app (forall_app (forall_app (forall_app (forall_app (forall_app (forall_app
        (forall_app p1 p2) p3) p4) p5) p6) p7) p9) p8
    have hW4 : σ4.vars "W" = W := by rw [o4.vars _ (by decide), hW3]
    have hov4 : σ4.vars "ovf" = 0 := by rw [o4.vars _ (by decide), hovf3]
    have hcap4 : (σ4.arrs "OB").length = W + 1 := by rw [o4.len, hcap3]
    have hOA' : O = pre ++ qq := hOA
    rw [hOA'] at F4 qa4 hlO hvO
    have hqa : σ4.vars "qa" = pre.length := by simp at qa4; omega
    obtain ⟨σ5, r5, o5, ov5⟩ := finCall_run (e := e) (d := d) (X := ySz X) (pre := pre)
      (q := qq) hW4 (by omega) F4 hqa ql4 gX4 hcap4 hlO hvO (by omega) hov4
    rw [← hOA'] at o5 ov5 r5 hlO
    refine ⟨σ5, ?_, ?_, ?_⟩
    · unfold round0
      refine (Run.seq r1 (Run.seq r2 (Run.seq r3
        (Run.ite_false (by rw [hc]; simp [hn]) (Run.seq r4 r5))))).mono ?_
      simp only [Cond.size, Expr.size]
      have hXr : (xIn G k₀ q₀ P Q s).length = X.length := by rw [hXdef]
      have hnX : n ≤ X.length := by rw [hXdef, xIn_split, StpRam.toWord_pg]; simp <;> omega
      have hOl' : (pre ++ qq).length = O.length := by rw [hOA']
      have hyl : X.length + 1 ≤ ySz X := by unfold ySz; omega
      omega
    · rw [o5, o4.out, o3, o2]; simp [gOut0, hn, σ1, hOdef]
    · rw [ov5]
      have hok : ok0 G P Q s k₀ q₀ W e d ↔ guardOK W e d (ySz X) qq ∧ maxEntry O < W / 32 / 32 := by
        unfold ok0; rw [if_neg hn]
      by_cases hg : guardOK W e d (ySz X) qq ∧ maxEntry O < W / 32 / 32
      · rw [if_pos hg, if_pos (hok.2 hg)]
      · rw [if_neg hg, if_neg (fun h => hg (hok.1 h))]

end Lax185574Proofs.ResolveRam.Glue
