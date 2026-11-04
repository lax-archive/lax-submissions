import Lax185574Proofs.CompRam.GRet

/-!
The build of a round of the glue command of lem:compose: reading the
input and round `0`.

Along a reached part of the trajectory every state is good
(`reached_ok`). The input of round `0` is the input word of the
composite, that of round `j + 1` the state of the machine with the
answer of the switch (`uT_succ_eq`). The command copies it into `x`,
whose other cells stay `0` (`rdN_full`). Round `0` writes the first
frame and the query of the canonical form of its atoms (`round0_run`),
and `buildCmd_run` puts the two kinds of rounds together.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574.PartialGraphs

section script

variable {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
  {u₂ : Fin l2 → Fin n}

/-- **Along a reached part of the trajectory every state is good.** -/
theorem reached_ok (hI : Inst G k q u₁ u₂) {j : ℕ} (hR : Reached G k q u₁ u₂ j) :
    ∀ i ≤ j, ROKs (szP G k q u₁ u₂) (trT G k q u₁ u₂ i) := by
  obtain ⟨h1, h2, hk, -⟩ := hI
  have hP : (szP G k q u₁ u₂).Λ + (szP G k q u₁ u₂).K + 3 ≤ (szP G k q u₁ u₂).B0 := by
    simp only [szP]; omega
  intro i
  induction i with
  | zero =>
    intro _
    have hX : ∀ v ∈ toWord (node G k q u₁), v ∈ xT G k q u₁ u₂ := fun v hv => by
      rw [xT_eq]; simp [hv]
    have hY : ∀ v ∈ toWord (node G k q u₂), v ∈ xT G k q u₁ u₂ := fun v hv => by
      rw [xT_eq]; simp [hv]
    have hlX : (toWord (node G k q u₁)).length ≤ (xT G k q u₁ u₂).length := by
      rw [xT_eq]; simp; omega
    have hlY : (toWord (node G k q u₂)).length ≤ (xT G k q u₁ u₂).length := by
      rw [xT_eq]; simp; omega
    have hf := fok_fresh (P := szP G k q u₁ u₂) (d := q) (kk := k) (l1 := l1) (l2 := l2)
      (A := toWord (node G k q u₁)) (B := toWord (node G k q u₂)) hk (by simp only [szP]; omega)
      ⟨⟨_, rfl⟩, hlX, fun e he => by have := le_maxEntry (hX e he); simp only [szP]; omega⟩
      ⟨⟨_, rfl⟩, hlY, fun e he => by have := le_maxEntry (hY e he); simp only [szP]; omega⟩
    refine ⟨⟨rfl, fun f hf' => ?_, fun f hf' => by simp at hf'⟩, _, [], rfl, Or.inl ⟨rfl, rfl⟩⟩
    simp only [List.mem_singleton] at hf'
    subst hf'
    exact hf
  | succ i ih =>
    intro hi
    obtain ⟨g, S, q', htr, -, hA⟩ := hR i (by omega)
    have := ih (by omega)
    rw [show trT G k q u₁ u₂ (i + 1) = round (g :: S) (ansOf G q') by
      unfold trT; rw [traj_succ]; unfold trT at htr; rw [htr]; rfl]
    rw [htr] at this
    exact round_ok hP this hA

theorem trT_succ_call {j : ℕ} {S : List Fr} {q' : Qry} (h : trT G k q u₁ u₂ j = .call S q') :
    trT G k q u₁ u₂ (j + 1) = round S (ansOf G q') := by
  unfold trT; rw [traj_succ]; unfold trT at h; rw [h]; rfl

theorem uT_succ_eq {j : ℕ} {S : List Fr} {q' : Qry} (h : trT G k q u₁ u₂ j = .call S q') :
    uT G k q u₁ u₂ (j + 1) = glueIn (j + 1) S (ansWord q' (ansOf G q')) :=
  sU_succ k q l1 l2 _ _ G j h

theorem trT_zero : trT G k q u₁ u₂ 0 =
    r0 k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) := rfl

end script

/-! ### Reading the input into `x` -/

theorem set_rep (l : List ℕ) {m : ℕ} (hm : 1 ≤ m) (v : ℕ) :
    (l ++ List.replicate m 0).set l.length v = (l ++ [v]) ++ List.replicate (m - 1) 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.set_append_right _ _ le_rfl]
  simp [List.replicate_succ]

/-- One store at the end of the filled part of `x`. -/
theorem pushX_run {W : ℕ} {σ : Env} {l : List ℕ} {e : Expr} {v : ℕ}
    (hx : σ.arrs "x" = l ++ List.replicate (W + 1 - l.length) 0) (hp : σ.vars "xp" = l.length)
    (he : e.evalB (W + 1) σ = some v) (hl : l.length + 1 ≤ W) :
    ∃ σ', Run (W + 1) (push1 "x" "xp" e) σ σ' (6 + e.size) ∧
      σ'.arrs "x" = (l ++ [v]) ++ List.replicate (W + 1 - (l ++ [v]).length) 0 ∧
      σ'.vars "xp" = (l ++ [v]).length ∧ (∀ y, y ≠ "xp" → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ "x" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hlen : (σ.arrs "x").length = W + 1 := by rw [hx]; simp; omega
  refine ⟨(σ.setArr "x" l.length v).setVar "xp" (l.length + 1), ?_, ?_, by simp, ?_, ?_, rfl, rfl⟩
  · refine (Run.seq (Run.store (idx := l.length) (by simp [hp]; omega) he (by omega))
      (Run.assign (by simp [hp]; omega))).mono (by simp; omega)
  · simp only [arrs_setVar, arrs_setArr, if_true, hx]
    rw [set_rep l (by omega) v]
    congr 2; simp; omega
  · intro y hy; simp [hy]
  · intro a ha; simp [ha]

/-- **Reading entries into `x`.** -/
theorem rdN_full {W : ℕ} {σ : Env} {pre u rest : List ℕ} {nv : String}
    (hn : nv ∉ ["ri", "rv", "xp"])
    (hx : σ.arrs "x" = pre ++ List.replicate (W + 1 - pre.length) 0) (hp : σ.vars "xp" = pre.length)
    (hinp : σ.inp = u ++ rest) (hN : σ.vars nv = u.length) (hB : pre.length + u.length + 1 ≤ W)
    (hv : ∀ v ∈ u, v < W + 1) :
    ∃ σ', Run (W + 1) (rdN nv) σ σ' (20 * u.length + 10) ∧
      σ'.arrs "x" = (pre ++ u) ++ List.replicate (W + 1 - (pre ++ u).length) 0 ∧
      σ'.vars "xp" = (pre ++ u).length ∧ σ'.inp = rest ∧
      (∀ y, y ∉ ["ri", "rv", "xp"] → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ "x" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out := by
  let I : ℕ → Env → Prop := fun i τ =>
    τ.arrs "x" = (pre ++ u.take i) ++ List.replicate (W + 1 - (pre ++ u.take i).length) 0 ∧
      τ.vars "xp" = (pre ++ u.take i).length ∧ τ.inp = u.drop i ++ rest ∧
      (∀ y, y ∉ ["ri", "rv", "xp"] → τ.vars y = σ.vars y) ∧
      (∀ a, a ≠ "x" → τ.arrs a = σ.arrs a) ∧ τ.out = σ.out
  have hn1 : nv ≠ "ri" := fun h => hn (by simp [h])
  obtain ⟨σ', r, hI, -⟩ := forUp_run (B := W + 1) (i := "ri") (e := V nv) (body := rdBody) (N := u.length)
    (K := 8) I (by omega)
    (fun i _ τ hτ _ => by
      have h := hτ.2.2.2.1 nv hn
      rw [← hN, ← h]; exact evalB_var (by rw [h, hN]; omega))
    ⟨by simp [hx], by simp [hp], by simp [hinp], fun y hy => by
      simp [show y ≠ "ri" from fun h => hy (by simp [h])], fun a _ => rfl, rfl⟩
    (fun i hi τ hτ hri => by
      obtain ⟨hx', hp', hin', hv', ha', ho'⟩ := hτ
      have hdi : u.drop i = u[i] :: u.drop (i + 1) := List.drop_eq_getElem_cons hi
      set τ1 : Env := { τ.setVar "rv" u[i] with inp := u.drop (i + 1) ++ rest } with hτ1
      have r1 : Run (W + 1) (.read "rv") τ τ1 1 := Run.read (by rw [hin', hdi]; rfl)
      have hlt : (pre ++ u.take i).length + 1 ≤ W := by simp; omega
      obtain ⟨τ2, r2, hx2, hp2, hv2, ha2, hi2, ho2⟩ := pushX_run (σ := τ1) (l := pre ++ u.take i)
        (e := V "rv") (v := u[i]) (by simpa [hτ1] using hx') (by simpa [hτ1] using hp')
        (by simp [hτ1]; have := hv _ (List.getElem_mem hi); omega) hlt
      have htk : pre ++ u.take i ++ [u[i]] = pre ++ u.take (i + 1) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; simp
      refine ⟨τ2, (Run.seq r1 r2).mono (le_of_eq rfl), by rw [hv2 _ (by decide)]; simp [hτ1, hri], ?_⟩
      refine ⟨by rw [arrs_setVar, hx2, htk], by rw [vars_setVar, if_neg (by decide), hp2, htk], ?_,
        fun y hy => ?_, fun a ha => ?_, ?_⟩
      · show τ2.inp = _
        simp [hi2, hτ1]
      · have h1 : y ≠ "ri" := fun h => hy (by simp [h])
        have h2 : y ≠ "rv" := fun h => hy (by simp [h])
        have h3 : y ≠ "xp" := fun h => hy (by simp [h])
        rw [vars_setVar, if_neg h1, hv2 y h3]; simp [hτ1, h2, hv' y hy]
      · rw [arrs_setVar, ha2 a ha]; simp [hτ1, ha' a ha]
      · show τ2.out = _
        rw [ho2]; simp [hτ1, ho'])
  obtain ⟨hx', hp', hin', hv', ha', ho'⟩ := hI
  refine ⟨σ', r.mono (by simp [Expr.size]; omega), by simpa using hx', by simpa using hp', by simpa using hin',
    hv', ha', ho'⟩

/-! ### Round `0` -/

theorem Run.seqs_app3 {B : ℕ} : ∀ {l1 l2 : List Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}, l1 ≠ [] → l2 ≠ [] →
    Run B (seqs l1) σ σ1 K1 → Run B (seqs l2) σ1 σ2 K2 → Run B (seqs (l1 ++ l2)) σ σ2 (K1 + K2)
  | [c], l2, _, _, _, _, _, _, h2, r1, r2 => by
    match l2, h2 with
    | d :: ds, _ => exact Run.seq r1 r2
  | c :: d :: cs, l2, _, _, _, _, _, _, h2, r1, r2 => by
    obtain ⟨k, hk, hb⟩ := r1
    cases hb with
    | seq h h' =>
      have := Run.seqs_app3 (l1 := d :: cs) (by simp) h2 (Run.of_bigStepB h') r2
      exact (Run.seq (Run.of_bigStepB h) this).mono (by omega)

/-- The setup of round `0`. -/
def r0Setup : List Com :=
  [asg "ck" (X (N 0)), asg "cd" (X (N 1)), asg "c1" (X (N 2)), asg "cAs" (N 3), asg "y" (N 3),
    asg "dd" (V "cd"), skipNode, asg "cAl" (.sub (V "y") (N 3)), asg "c2" (X (.add (V "y") (N 2))),
    asg "cBs" (.add (V "y") (N 3)), asg "y" (V "cBs"), skipNode, asg "cBl" (.sub (V "y") (V "cBs")),
    asg "jr" (N 0), asg "j1" (N 1), asg "cnt" (N 7)]

/-- The writing part of round `0`. -/
def r0Emit : List Com := [emHd, emFresh, patchL, emCaHd, emAtoms, emCaEnd]

theorem round0_eq : round0 = seqs (r0Setup ++ r0Emit) := rfl

theorem getElem_of_take {X xs : List ℕ} (h : X.take xs.length = xs) {i : ℕ} (hi : i < xs.length) :
    X[i]? = xs[i]? := by
  rw [← h, List.getElem?_take_of_lt hi]

theorem drop_of_take {X xs : List ℕ} (h : X.take xs.length = xs) {p : ℕ} (hp : p ≤ xs.length) :
    X.drop p = xs.drop p ++ X.drop xs.length := by
  conv_lhs => rw [← List.take_append_drop xs.length X, h]
  rw [List.drop_append_of_le_length hp]

set_option maxHeartbeats 1000000 in
/-- **The setup of round `0`.** -/
theorem r0Setup_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) {k q l1 l2 : ℕ} (tX : Node q l1)
    (tY : Node q l2) (hX : (σ.arrs "x").take (xIn k q l1 l2 (toWord tX) (toWord tY)).length =
      xIn k q l1 l2 (toWord tX) (toWord tY))
    (hM : (xIn k q l1 l2 (toWord tX) (toWord tY)).length ≤ M) (hk : k < M) (hq : q < M) (h1 : l1 < M)
    (h2 : l2 < M) :
    ∃ σ', Run (W + 1) (seqs r0Setup) σ σ' (40 * ((toWord tX).length + (toWord tY).length) + 300) ∧
      FreshIs M σ' q k l1 l2 (toWord tX) (toWord tY) ∧ σ'.vars "jr" = 0 ∧ σ'.vars "j1" = 1 ∧
      σ'.vars "cnt" = 7 ∧ (∀ z, z ∉ freshVars ++ ["y", "sn", "sk", "dd", "jr", "j1", "cnt"] →
        σ'.vars z = σ.vars z) ∧ (∀ a, a ≠ "OB" → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs "OB").length = (σ.arrs "OB").length ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  set A := toWord tX with hAd
  set B := toWord tY with hBd
  set xs := xIn k q l1 l2 A B with hxs
  have hR := hC.room
  have hxl : (σ.arrs "x").length = W + 1 := hC.xl
  have hlx : xs.length = 6 + A.length + B.length := by simp [hxs, xIn]; omega
  have hAA : (toWord tX).length = A.length := rfl
  have hBB : (toWord tY).length = B.length := rfl
  have g0 : (σ.arrs "x")[0]? = some k := by rw [getElem_of_take hX (by omega)]; simp [hxs, xIn]
  have g1 : (σ.arrs "x")[1]? = some q := by rw [getElem_of_take hX (by omega)]; simp [hxs, xIn]
  have g2 : (σ.arrs "x")[2]? = some l1 := by rw [getElem_of_take hX (by omega)]; simp [hxs, xIn]
  have g5 : (σ.arrs "x")[3 + A.length + 2]? = some l2 := by
    rw [getElem_of_take hX (by omega)]
    simp only [hxs, xIn, List.append_assoc]
    rw [List.getElem?_append_right (by simp <;> omega), List.getElem?_append_right (by simp <;> omega)]
    simp
  have dA : (σ.arrs "x").drop 3 = A ++ ([k, q, l2] ++ B ++ (σ.arrs "x").drop xs.length) := by
    rw [drop_of_take hX (by omega)]; simp [hxs, xIn]
  have dB : (σ.arrs "x").drop (3 + A.length + 3) = B ++ (σ.arrs "x").drop xs.length := by
    rw [drop_of_take hX (by omega)]
    simp only [hxs, xIn, List.append_assoc]
    rw [show 3 + A.length + 3 = ([k, q, l1] ++ A ++ [k, q, l2]).length by simp; omega]
    simp
  set σ1 := σ.setVar "ck" k with e1
  set σ2 := σ1.setVar "cd" q with e2
  set σ3 := σ2.setVar "c1" l1 with e3
  set σ4 := σ3.setVar "cAs" 3 with e4
  set σ5 := σ4.setVar "y" 3 with e5
  set σ6 := σ5.setVar "dd" q with e6
  have r1 : Run (W + 1) (asg "ck" (X (N 0))) σ σ1 3 :=
    (Run.assign (evalB_get (evalB_lit (by omega)) g0 (by omega))).mono (by simp)
  have r2 : Run (W + 1) (asg "cd" (X (N 1))) σ1 σ2 3 :=
    (Run.assign (evalB_get (evalB_lit (by omega)) (by simpa [e1] using g1) (by omega))).mono (by simp)
  have r3 : Run (W + 1) (asg "c1" (X (N 2))) σ2 σ3 3 :=
    (Run.assign (evalB_get (evalB_lit (by omega)) (by simpa [e1, e2] using g2) (by omega))).mono (by simp)
  have r4 : Run (W + 1) (asg "cAs" (N 3)) σ3 σ4 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  have r5 : Run (W + 1) (asg "y" (N 3)) σ4 σ5 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  have r6 : Run (W + 1) (asg "dd" (V "cd")) σ5 σ6 2 :=
    (Run.assign (by simp [e5, e4, e3, e2]; omega)).mono (by simp)
  have hC6 : Ctx W M σ6 := (((((hC.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _).setVar (by decide) _).setVar (by decide) _
  have hx6 : σ6.arrs "x" = σ.arrs "x" := by simp [e6, e5, e4, e3, e2, e1]
  obtain ⟨σ7, r7, hy7, f7⟩ := skipNode_run hC6 tX (p := 3) (by rw [hx6]; exact dA) (by simp [e6, e5])
    (by simp [e6]) hq (by omega)
  have hx7 : σ7.arrs "x" = σ.arrs "x" := by rw [f7.arrs "x" (by decide), hx6]
  set σ8 := σ7.setVar "cAl" A.length with e8
  set σ9 := σ8.setVar "c2" l2 with e9
  set σ10 := σ9.setVar "cBs" (3 + A.length + 3) with e10
  set σ11 := σ10.setVar "y" (3 + A.length + 3) with e11
  have r8 : Run (W + 1) (asg "cAl" (.sub (V "y") (N 3))) σ7 σ8 4 :=
    (Run.assign (by simp [hy7]; omega)).mono (by simp)
  have r9 : Run (W + 1) (asg "c2" (X (.add (V "y") (N 2)))) σ8 σ9 5 := by
    have hy8 : σ8.vars "y" = 3 + A.length := by rw [e8, vars_setVar, if_neg (by decide), hy7]
    refine (Run.assign (evalB_get (k := 3 + A.length + 2) ?_ (by simpa [e8, hx7] using g5) (by omega))).mono
      (by simp)
    have := evalB_bin (B := W + 1) (op := .add) (evalB_var (σ := σ8) (x := "y") (by rw [hy8]; omega))
      (evalB_lit (σ := σ8) (n := 2) (by omega)) (by simp only [Bop.apply, hy8]; omega)
    simpa [hy8] using this
  have r10 : Run (W + 1) (asg "cBs" (.add (V "y") (N 3))) σ9 σ10 4 :=
    (Run.assign (by simp [e9, e8, hy7]; omega)).mono (by simp)
  have r11 : Run (W + 1) (asg "y" (V "cBs")) σ10 σ11 2 :=
    (Run.assign (by simp [e10]; omega)).mono (by simp)
  have hC11 : Ctx W M σ11 := ((((hC.of_frame (f7.vars "W" (by decide) ▸ by simp [e6, e5, e4, e3, e2, e1])
    hx7 (by rw [f7.arrs "wp" (by decide)]; simp [e6, e5, e4, e3, e2, e1])
    (by rw [f7.len]; simp [e6, e5, e4, e3, e2, e1])).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _).setVar (by decide) _
  have hx11 : σ11.arrs "x" = σ.arrs "x" := by simp [e11, e10, e9, e8, hx7]
  have hdd : σ11.vars "dd" = q := by
    rw [show σ11.vars "dd" = σ7.vars "dd" by simp [e11, e10, e9, e8], f7.vars "dd" (by decide)]
    simp [e6]
  obtain ⟨σ12, r12, hy12, f12⟩ := skipNode_run hC11 tY (p := 3 + A.length + 3) (by rw [hx11]; exact dB)
    (by simp [e11]) hdd hq (by omega)
  set σ13 := σ12.setVar "cBl" B.length with e13
  set σ14 := σ13.setVar "jr" 0 with e14
  set σ15 := σ14.setVar "j1" 1 with e15
  set σ16 := σ15.setVar "cnt" 7 with e16
  have hcBs : σ12.vars "cBs" = 3 + A.length + 3 := by rw [f12.vars "cBs" (by decide)]; simp [e11, e10]
  have r13 : Run (W + 1) (asg "cBl" (.sub (V "y") (V "cBs"))) σ12 σ13 4 :=
    (Run.assign (by simp [hy12, hcBs]; omega)).mono (by simp)
  have r14 : Run (W + 1) (asg "jr" (N 0)) σ13 σ14 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  have r15 : Run (W + 1) (asg "j1" (N 1)) σ14 σ15 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  have r16 : Run (W + 1) (asg "cnt" (N 7)) σ15 σ16 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  have fall : OFr σ σ16 (["ck", "cd", "c1", "cAs", "y", "dd"] ++ ["y", "sn", "sk"] ++
      ["cAl", "c2", "cBs", "y"] ++ ["y", "sn", "sk"] ++ ["cBl", "jr", "j1", "cnt"]) :=
    ((((((((OFr.setVar σ "ck" k).trans (OFr.setVar σ1 "cd" q)).trans (OFr.setVar σ2 "c1" l1)).trans
      (OFr.setVar σ3 "cAs" 3)).trans (OFr.setVar σ4 "y" 3)).trans (OFr.setVar σ5 "dd" q)).trans f7 |>.trans
      ((((OFr.setVar σ7 "cAl" _).trans (OFr.setVar σ8 "c2" _)).trans (OFr.setVar σ9 "cBs" _)).trans
        (OFr.setVar σ10 "y" _))).trans f12).trans
      ((((OFr.setVar σ12 "cBl" _).trans (OFr.setVar σ13 "jr" 0)).trans (OFr.setVar σ14 "j1" 1)).trans
        (OFr.setVar σ15 "cnt" 7))
  have hx16 : σ16.arrs "x" = σ.arrs "x" := fall.arrs "x" (by decide)
  have v12 : ∀ z, z ∉ ["y", "sn", "sk"] → σ12.vars z = σ11.vars z := fun z hz => f12.vars z hz
  have v7 : ∀ z, z ∉ ["y", "sn", "sk"] → σ7.vars z = σ6.vars z := fun z hz => f7.vars z hz
  have hrun : Run (W + 1) (seqs r0Setup) σ σ16 (40 * ((toWord tX).length + (toWord tY).length) + 300) := by
    unfold r0Setup
    have r := Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r4 (Run.seqs_cons (by simp) r5 (Run.seqs_cons (by simp) r6
      (Run.seqs_cons (by simp) r7 (Run.seqs_cons (by simp) r8 (Run.seqs_cons (by simp) r9
      (Run.seqs_cons (by simp) r10 (Run.seqs_cons (by simp) r11 (Run.seqs_cons (by simp) r12
      (Run.seqs_cons (by simp) r13 (Run.seqs_cons (by simp) r14 (Run.seqs_cons (by simp) r15
      (Run.seqs_one r16)))))))))))))))
    exact r.mono (by omega)
  have c12 : ∀ z, z ∉ ["y", "sn", "sk", "cBl", "jr", "j1", "cnt"] → σ16.vars z = σ11.vars z := by
    intro z hz
    have h1 : z ≠ "cBl" := fun h => hz (by simp [h])
    have h2 : z ≠ "jr" := fun h => hz (by simp [h])
    have h3 : z ≠ "j1" := fun h => hz (by simp [h])
    have h4 : z ≠ "cnt" := fun h => hz (by simp [h])
    rw [e16, vars_setVar, if_neg h4, e15, vars_setVar, if_neg h3, e14, vars_setVar, if_neg h2, e13,
      vars_setVar, if_neg h1]
    exact v12 z (fun h => hz (by simp at h ⊢; tauto))
  have c7 : ∀ z, z ∉ ["y", "sn", "sk", "cAl", "c2", "cBs"] → σ11.vars z = σ6.vars z := by
    intro z hz
    have h1 : z ≠ "cAl" := fun h => hz (by simp [h])
    have h2 : z ≠ "c2" := fun h => hz (by simp [h])
    have h3 : z ≠ "cBs" := fun h => hz (by simp [h])
    have h4 : z ≠ "y" := fun h => hz (by simp [h])
    rw [e11, vars_setVar, if_neg h4, e10, vars_setVar, if_neg h3, e9, vars_setVar, if_neg h2, e8,
      vars_setVar, if_neg h1]
    exact v7 z (fun h => hz (by simp at h ⊢; tauto))
  have vcd : σ16.vars "cd" = q := by rw [c12 _ (by decide), c7 _ (by decide)]; simp [e6, e5, e4, e3, e2]
  have vck : σ16.vars "ck" = k := by rw [c12 _ (by decide), c7 _ (by decide)]; simp [e6, e5, e4, e3, e2, e1]
  have vc1 : σ16.vars "c1" = l1 := by rw [c12 _ (by decide), c7 _ (by decide)]; simp [e6, e5, e4, e3]
  have vcAs : σ16.vars "cAs" = 3 := by rw [c12 _ (by decide), c7 _ (by decide)]; simp [e6, e5, e4]
  have vc2 : σ16.vars "c2" = l2 := by rw [c12 _ (by decide)]; simp [e11, e10, e9]
  have vcAl : σ16.vars "cAl" = A.length := by rw [c12 _ (by decide)]; simp [e11, e10, e9, e8]
  have vcBs : σ16.vars "cBs" = 3 + A.length + 3 := by rw [c12 _ (by decide)]; simp [e11, e10]
  have vcBl : σ16.vars "cBl" = B.length := by simp [e16, e15, e14, e13]
  refine ⟨σ16, hrun, ⟨vcd, vck, vc1, vc2, ⟨by omega, by omega, by omega, by omega⟩, ?_, ?_⟩,
    by simp [e16, e15, e14], by simp [e16, e15], by simp [e16],
    fun z hz => fall.vars z (fun h => hz (by simp [freshVars] at h ⊢; tauto)), fun a ha => fall.arrs a ha, fall.len,
    fall.out, fall.inp⟩
  · refine segIs_of (a := 3) vcAs vcAl (by omega) ?_
    rw [hx16]; simp [seg, dA]
  · refine segIs_of (a := 3 + A.length + 3) vcBs vcBl (by omega) ?_
    rw [hx16]; simp [seg, dB]

theorem hd0_single (j : ℕ) (f : Fr) :
    [1, 0, 0, 0, j, 7] ++ frames (frWords f) = hd0 j [f] := by
  simp [hd0, stWords, frWords]

/-- **The writing part of round `0`.** -/
theorem r0Emit_run {W M : ℕ} {σ : Env} (hC : Ctx W M σ) (hF : Filled "OB" "po" [] σ) {k q l1 l2 : ℕ}
    (tX : Node q l1) (tY : Node q l2) (hf : FreshIs M σ q k l1 l2 (toWord tX) (toWord tY))
    (hl1 : l1 < M) (hj1 : σ.vars "j1" = 1) (hcnt : σ.vars "cnt" = 7) :
    ∃ σ' ob, Run (W + 1) (seqs r0Emit) σ σ' (100 * ((toWord tX).length + (toWord tY).length) + 700) ∧
      Built 1 (r0 k q l1 l2 (toWord tX) (toWord tY)) ob σ' ∧ ob.length ≤ 8 * M + 20 ∧
      OFr σ σ' (["po"] ++ ["ci", "po"] ++ [] ++ ["po", "sp", "dq", "qa"] ++ emAtomsVars ++ ["ql", "qk"]) := by
  have hR := hC.room
  have hM := hC.m16
  obtain ⟨τ1, r1, F1, o1⟩ := emHd_run hC hF (by rw [hj1]; omega) (by rw [hcnt]; omega) (by simp; omega)
  rw [hj1, hcnt, List.nil_append] at F1
  have hC1 := hC.ofr o1 (by decide)
  obtain ⟨τ2, r2, F2, l2', o2⟩ := emFresh_run hC1 F1 (hf.ofr o1 (by decide)) (by simp; omega)
  rw [hd0_single] at F2
  have hC2 := hC1.ofr o2 (by decide)
  have hsf : stWords [fresh q k l1 l2 (toWord tX) (toWord tY)] = frWords (fresh q k l1 l2 (toWord tX) (toWord tY)) := by simp [stWords]
  have hl0 : (hd0 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).length ≤ 4 * M + 6 := by simp [hd0, hsf] at l2' ⊢; omega
  obtain ⟨τ3, r3, F3, o3⟩ := patchL_run (W := W) F2 (by simp [hd0]) (by omega)
  have hC3 := hC2.ofr o3 (by decide)
  obtain ⟨τ4, r4, F4, sp4, qa4, dq4, o4⟩ := emCaHd_run hC3 F3 (by simp only [List.length_set]; omega)
  have hC4 := hC3.ofr o4 (by decide)
  have hf4 : FreshIs M τ4 q k l1 l2 (toWord tX) (toWord tY) :=
    (((hf.ofr o1 (by decide)).ofr o2 (by decide)).ofr o3 (by decide)).ofr o4 (by decide)
  obtain ⟨rA, hrA⟩ := atomsOf_prefix (d := q) (l := l1) ⟨tX, rfl⟩
  obtain ⟨rB, hrB⟩ := atomsOf_prefix (d := q) (l := l2) ⟨tY, rfl⟩
  have hAB : (toWord tX).length + (toWord tY).length ≤ 2 * M := by
    have := hf.hA.2.1; have := hf.hB.2.1; omega
  obtain ⟨τ5, r5, F5, l5, o5⟩ := emAtoms_run hC4 F4 hf4 hrA.symm hrB.symm hl1
    (by simp only [List.length_append, List.length_set]; simp; omega)
  have hlen4 : ((hd0 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).set 1 ((hd0 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).length - 3) ++ [5, lDSq, 0, 0, 0, 0, 0, 0]).length =
      (hdS 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).length + 8 := by simp [hdS]
  have hqa5 : τ5.vars "qa" = ((hd0 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).set 1 ((hd0 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).length - 3) ++
      [5, lDSq, 0, 0, 0, 0, 0, 0]).length := by
    rw [o5.vars "qa" (by decide), qa4]; simp
  obtain ⟨τ6, r6, F6, ql6, qk6, o6⟩ := emCaEnd_run (W := W) F5 hqa5 (by simp) (by simp at l5 ⊢; omega)
  refine ⟨τ6, _, ?_, built_ca (j := 1) (S := [fresh q k l1 l2 (toWord tX) (toWord tY)]) (ws := atomsQ (fresh q k l1 l2 (toWord tX) (toWord tY))) ?_ ?_ ?_ qk6 ?_ ql6, ?_, ?_⟩
  · have r := Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r4 (Run.seqs_cons (by simp) r5 (Run.seqs_one r6)))))
    exact r.mono (by omega)
  · rw [hlen4] at F6
    simpa [hdS, atomsQ, fresh, show (hdS 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).length + 8 - 6 = (hdS 1 [fresh q k l1 l2 (toWord tX) (toWord tY)]).length + 2 by omega] using F6
  · rw [o6.vars "sp" (by decide), o5.vars "sp" (by decide), sp4]; simp [hdS]
  · rw [o6.vars "dq" (by decide), o5.vars "dq" (by decide), dq4]
  · rw [o6.vars "qa" (by decide), o5.vars "qa" (by decide), qa4]; simp [hdS]
  · have hQ : toWord (atomsQ (fresh q k l1 l2 (toWord tX) (toWord tY))) =
        toWord (atomsOf (toWord tX) ++ (atomsOf (toWord tY)).map (renAtom l1)) := rfl
    rw [hQ]; simp only [hdS, List.length_append, List.length_set, List.length_cons, List.length_nil]
    omega
  · exact ((((o1.trans o2).trans o3).trans o4).trans o5).trans o6

/-! ### Reading the head of the input -/

/-- The reading part of the build. -/
def headL : List Com := [.read "tg", .read "L", asg "xp" (N 0), rdN "L", asg "po" (N 0)]

/-- The branch of the build by the kind of round. -/
def roundSel : Com :=
  .ite (.eq (V "tg") (N 0)) round0 (seqs [.read "ol", push1 "x" "xp" (V "ol"), rdN "ol", roundJ])

theorem buildCmd_eq : buildCmd = seqs (headL ++ [roundSel]) := rfl

/-- The head vars written by the reading part. -/
def headVars : List String := ["tg", "L", "xp", "ri", "rv", "po"]

theorem head_run {W : ℕ} {σ : Env} {t : ℕ} {u rest : List ℕ}
    (hinp : σ.inp = t :: u.length :: (u ++ rest)) (hx : σ.arrs "x" = List.replicate (W + 1) 0)
    (ht : t < W + 1) (hB : u.length + 1 ≤ W) (hv : ∀ v ∈ u, v < W + 1) :
    ∃ σ', Run (W + 1) (seqs headL) σ σ' (20 * u.length + 30) ∧ σ'.vars "tg" = t ∧
      σ'.vars "L" = u.length ∧ σ'.vars "xp" = u.length ∧ σ'.vars "po" = 0 ∧
      σ'.arrs "x" = u ++ List.replicate (W + 1 - u.length) 0 ∧ σ'.inp = rest ∧
      (∀ z, z ∉ headVars → σ'.vars z = σ.vars z) ∧ (∀ a, a ≠ "x" → σ'.arrs a = σ.arrs a) ∧
      σ'.out = σ.out := by
  set σ1 : Env := { σ.setVar "tg" t with inp := u.length :: (u ++ rest) } with e1
  set σ2 : Env := { σ1.setVar "L" u.length with inp := u ++ rest } with e2
  set σ3 := σ2.setVar "xp" 0 with e3
  have r1 : Run (W + 1) (.read "tg") σ σ1 1 := Run.read hinp
  have r2 : Run (W + 1) (.read "L") σ1 σ2 1 := Run.read rfl
  have r3 : Run (W + 1) (asg "xp" (N 0)) σ2 σ3 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  obtain ⟨σ4, r4, hx4, hp4, hi4, hv4, ha4, ho4⟩ := rdN_full (W := W) (σ := σ3) (pre := []) (u := u)
    (rest := rest) (nv := "L") (by decide) (by simp [e3, e2, e1, hx]) (by simp [e3]) (by simp [e3, e2])
    (by simp [e3, e2]) (by simpa using hB) hv
  set σ5 := σ4.setVar "po" 0 with e5
  have r5 : Run (W + 1) (asg "po" (N 0)) σ4 σ5 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  refine ⟨σ5, ?_, ?_, ?_, ?_, by simp [e5], by simpa [e5] using hx4, by simpa [e5] using hi4, ?_, ?_, ?_⟩
  · exact (Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
      (Run.seqs_cons (by simp) r4 (Run.seqs_one r5))))).mono (by omega)
  · rw [e5, vars_setVar, if_neg (by decide), hv4 _ (by decide)]; simp [e3, e2, e1]
  · rw [e5, vars_setVar, if_neg (by decide), hv4 _ (by decide)]; simp [e3, e2, e1]
  · simpa [e5] using hp4
  · intro z hz
    have h1 : z ∉ ["ri", "rv", "xp"] := fun h => hz (by simp [headVars] at h ⊢; tauto)
    have h2 : z ≠ "po" := fun h => hz (by simp [headVars, h])
    have h3 : z ≠ "L" := fun h => hz (by simp [headVars, h])
    have h4 : z ≠ "tg" := fun h => hz (by simp [headVars, h])
    have h5 : z ≠ "xp" := fun h => hz (by simp [headVars, h])
    rw [e5, vars_setVar, if_neg h2, hv4 z h1]; simp [e3, e2, e1, h3, h4, h5]
  · intro a ha; rw [e5, arrs_setVar, ha4 a ha]; simp [e3, e2, e1]
  · show σ4.out = σ.out
    rw [ho4]; simp [e3, e2, e1]

/-! ### The two kinds of rounds -/

theorem m_facts {W : ℕ} (hW : 2 ^ 30 ≤ W + 1) :
    2 ^ 16 ≤ (W + 1) / 2 ^ 14 + 1 ∧ 1024 * ((W + 1) / 2 ^ 14 + 1) ≤ W := by
  norm_num at hW ⊢; omega

theorem m_ent {W e : ℕ} (h : 2 ^ 16 * (e + 1) ≤ W + 1) : 4 * e + 4 < (W + 1) / 2 ^ 14 + 1 := by
  norm_num at h ⊢; omega

theorem m_len {W L : ℕ} (h : 2 ^ 14 * (L + 513) ≤ W + 1) : L + 513 ≤ (W + 1) / 2 ^ 14 := by
  norm_num at h ⊢; omega

/-- The context after the input is read. -/
theorem ctx_of {W M : ℕ} {σ : Env} {img : List ℕ} (hW : σ.vars "W" = W)
    (hx : σ.arrs "x" = img ++ List.replicate (W + 1 - img.length) 0) (hil : img.length ≤ W + 1)
    (hob : σ.arrs "OB" = List.replicate (W + 1) 0) (hwp : σ.arrs "wp" = List.replicate (W + 1) 0)
    (hv : ∀ v ∈ img, 4 * v + 4 < M) (hm : 2 ^ 16 ≤ M) (hr : 1024 * M ≤ W) :
    Ctx W M σ ∧ ∀ v ∈ σ.arrs "x", 4 * v + 4 < M := by
  have hx4 : ∀ v ∈ σ.arrs "x", 4 * v + 4 < M := by
    intro v hv'
    rw [hx, List.mem_append] at hv'
    rcases hv' with h | h
    · exact hv v h
    · rw [List.eq_of_mem_replicate h]; omega
  exact ⟨⟨hW, by rw [hx]; simp; omega, by rw [hob]; simp, by rw [hwp]; simp,
    fun v h => by have := hx4 v h; omega, hm, hr⟩, hx4⟩

section rounds

variable {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
  {u₂ : Fin l2 → Fin n}

/-- The initial environment of a round. -/
noncomputable def env0 (W : ℕ) (x : List ℕ) : Env := (initEnv (fun _ => W + 1) x).setVar "W" W

theorem env0_vars (W : ℕ) (x : List ℕ) (z : String) :
    (env0 W x).vars z = if z = "W" then W else 0 := by
  simp [env0, initEnv]

theorem env0_arrs (W : ℕ) (x : List ℕ) (a : String) :
    (env0 W x).arrs a = List.replicate (W + 1) 0 := by
  simp [env0, initEnv]

theorem cost0_arith {a b c d o : ℕ} (h1 : a + b ≤ d) (h2 : c = d + 3) :
    20 * d + 30 + (1 + 3 + (40 * (a + b) + 300 + (100 * (a + b) + 700))) ≤ 2000 * (c + o + 1) := by
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **Round `0`.** -/
theorem build0_run (hI : Inst G k q u₁ u₂) {W : ℕ} (hW : 2 ^ 30 ≤ W + 1)
    (hin : ∀ e ∈ uT G k q u₁ u₂ 0, 2 ^ 16 * (e + 1) ≤ W + 1)
    (hlen : 2 ^ 14 * ((uT G k q u₁ u₂ 0).length + 513) ≤ W + 1) :
    ∃ σ' ob K, Run (W + 1) buildCmd (env0 W (uT G k q u₁ u₂ 0)) σ' K ∧
      Built (0 + 1) (trT G k q u₁ u₂ 0) ob σ' ∧ σ'.vars "jr" = 0 ∧ σ'.vars "W" = W ∧
      σ'.vars "ovf" = 0 ∧ σ'.out = [] ∧ (σ'.arrs "OB").length = W + 1 ∧ 16 * ob.length ≤ W ∧
      K ≤ 2000 * ((uT G k q u₁ u₂ 0).length + ob.length + 1) := by
  set M := (W + 1) / 2 ^ 14 + 1 with hMd
  obtain ⟨hm16, hroom⟩ := m_facts hW
  set xs := xT G k q u₁ u₂ with hxs
  have hxs' : xs = xIn k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) := rfl
  have hu0 : uT G k q u₁ u₂ 0 = [0, xs.length] ++ xs ++ [0] := uT_zero
  have hxin : ∀ v ∈ xs, 2 ^ 16 * (v + 1) ≤ W + 1 := fun v hv => hin v (by rw [hu0]; simp [hv])
  have hxl : xs.length + 1 ≤ (W + 1) / 2 ^ 14 := by
    have := m_len hlen; rw [hu0] at this; simp at this; omega
  have hW' : (W + 1) / 2 ^ 14 + 1 ≤ W := by norm_num at hW ⊢; omega
  obtain ⟨σ5, r5, tg5, L5, xp5, po5, x5, i5, v5, a5, o5⟩ := head_run (W := W)
    (σ := env0 W (uT G k q u₁ u₂ 0)) (t := 0)
    (u := xs) (rest := [0]) (by rw [hu0]; simp [env0, initEnv]) (env0_arrs W _ "x") (by omega)
    (by omega) (fun v hv => by have := m_ent (hxin v hv); omega)
  obtain ⟨hC5, -⟩ := ctx_of (M := M) (σ := σ5) (img := xs)
    (by rw [v5 _ (by decide), env0_vars]; simp) x5 (by omega) (by rw [a5 _ (by decide), env0_arrs])
    (by rw [a5 _ (by decide), env0_arrs]) (fun v hv => m_ent (hxin v hv)) hm16 hroom
  have hXt : (σ5.arrs "x").take (xIn k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))).length =
      xIn k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) := by
    rw [← hxs', x5]; exact List.take_left' rfl
  have hmem : ∀ v ∈ ([k, q, l1] : List ℕ), v < M := fun v hv => by
    have := m_ent (hxin v (by
      rw [hxs, xT_eq]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hv)))); omega
  have hl2 : l2 < M := by
    have := m_ent (hxin l2 (by rw [hxs, xT_eq]; simp)); omega
  obtain ⟨σ6, r6, fr6, jr6, j16, cnt6, v6, a6, ol6, o6, i6⟩ := r0Setup_run hC5 (k := k)
    (node G k q u₁) (node G k q u₂) hXt (by rw [← hxs']; omega) (hmem k (by simp)) (hmem q (by simp))
    (hmem l1 (by simp)) hl2
  have hC6 : Ctx W M σ6 := hC5.of_frame (v6 "W" (by decide)) (a6 _ (by decide)) (a6 _ (by decide)) ol6
  have hF6 : Filled "OB" "po" [] σ6 :=
    ⟨by rw [v6 "po" (by decide), po5]; rfl, fun i h => absurd h (by simp)⟩
  obtain ⟨σ7, ob, r7, hb7, hl7, f7⟩ := r0Emit_run hC6 hF6 (node G k q u₁) (node G k q u₂) fr6
    (hmem l1 (by simp)) j16 cnt6
  have hsel : Run (W + 1) roundSel σ5 σ7 (1 + 3 + (40 * ((toWord (node G k q u₁)).length +
      (toWord (node G k q u₂)).length) + 300 + (100 * ((toWord (node G k q u₁)).length +
      (toWord (node G k q u₂)).length) + 700))) := by
    refine (Run.ite_true (by simp [tg5]) ?_).mono (le_of_eq rfl)
    rw [round0_eq]; exact Run.seqs_app3 (by simp [r0Setup]) (by simp [r0Emit]) r6 r7
  have hv0 : ∀ z, z ∉ headVars → σ5.vars z = (env0 W (uT G k q u₁ u₂ 0)).vars z := v5
  refine ⟨σ7, ob, _, Run.seqs_app3 (by simp [headL]) (by simp) r5 (Run.seqs_one hsel), hb7, ?_, ?_, ?_,
    ?_, ?_, by omega, ?_⟩
  · rw [f7.vars "jr" (by decide)]; exact jr6
  · rw [f7.vars "W" (by decide), v6 "W" (by decide), v5 _ (by decide), env0_vars]; simp
  · rw [f7.vars "ovf" (by decide), v6 "ovf" (by decide), v5 _ (by decide), env0_vars]; simp
  · rw [f7.out, o6, o5]; simp [env0, initEnv]
  · rw [f7.len, ol6, a5 _ (by decide), env0_arrs]; simp
  · have hX : (toWord (node G k q u₁)).length + (toWord (node G k q u₂)).length ≤ xs.length := by
      rw [hxs, xT_eq]; simp; omega
    have : (uT G k q u₁ u₂ 0).length = xs.length + 3 := by rw [hu0]; simp
    generalize (toWord (node G k q u₁)).length = a at *
    generalize (toWord (node G k q u₂)).length = b at *
    generalize (uT G k q u₁ u₂ 0).length = c at *
    generalize xs.length = d at *
    exact cost0_arith hX this

theorem costS_arith {a b c K o : ℕ} (hK : K ≤ 1000 * (a + 1 + b + o + 1)) (hc : c = a + 1 + b + 2) :
    20 * a + 30 + (1 + 3 + (1 + ((6 + 1) + ((20 * b + 10) + K)))) ≤ 2000 * (c + o + 1) := by
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **Round `j + 1`.** -/
theorem buildS_run (hI : Inst G k q u₁ u₂) {j : ℕ} (hR : Reached G k q u₁ u₂ (j + 1)) {W : ℕ}
    (hW : 2 ^ 30 ≤ W + 1) (hin : ∀ e ∈ uT G k q u₁ u₂ (j + 1), 2 ^ 16 * (e + 1) ≤ W + 1)
    (hlen : 2 ^ 14 * ((uT G k q u₁ u₂ (j + 1)).length + 513) ≤ W + 1) :
    ∃ σ' ob K, Run (W + 1) buildCmd (env0 W (uT G k q u₁ u₂ (j + 1))) σ' K ∧
      Built (j + 1 + 1) (trT G k q u₁ u₂ (j + 1)) ob σ' ∧ σ'.vars "jr" = j + 1 ∧ σ'.vars "W" = W ∧
      σ'.vars "ovf" = 0 ∧ σ'.out = [] ∧ (σ'.arrs "OB").length = W + 1 ∧ 16 * ob.length ≤ W ∧
      K ≤ 2000 * ((uT G k q u₁ u₂ (j + 1)).length + ob.length + 1) := by
  set M := (W + 1) / 2 ^ 14 + 1 with hMd
  obtain ⟨hm16, hroom⟩ := m_facts hW
  obtain ⟨g, S, q', htr, hfit, hA⟩ := hR j (by omega)
  set b := ansOf G q' with hb
  set o := ansWord q' b with ho
  set st := stWord (j + 1) (g :: S) with hst
  have hu : uT G k q u₁ u₂ (j + 1) = [1, st.length] ++ st ++ (o.length :: o) := uT_succ_eq htr
  have hent : ∀ v ∈ st ++ (o.length :: o), 4 * v + 4 < M := fun v hv =>
    m_ent (hin v (by
      rw [hu]
      rcases List.mem_append.1 hv with h | h
      · exact List.mem_append_left _ (List.mem_append_right _ h)
      · exact List.mem_append_right _ h))
  have hul : (uT G k q u₁ u₂ (j + 1)).length = st.length + 1 + o.length + 2 := by rw [hu]; simp; omega
  have hL1 := m_len hlen
  rw [hul] at hL1
  have hW' : (W + 1) / 2 ^ 14 + 1 ≤ W := by norm_num at hW ⊢; omega
  obtain ⟨σ5, r5, tg5, L5, xp5, po5, x5, i5, v5, a5, o5⟩ := head_run (W := W)
    (σ := env0 W (uT G k q u₁ u₂ (j + 1))) (t := 1) (u := st) (rest := o.length :: o)
    (by rw [hu]; simp [env0, initEnv]) (env0_arrs W _ "x") (by omega) (by omega)
    (fun v hv => by have := hent v (by simp [hv]); omega)
  set σ6 : Env := { σ5.setVar "ol" o.length with inp := o } with e6
  have r6 : Run (W + 1) (.read "ol") σ5 σ6 1 := Run.read i5
  obtain ⟨σ7, r7, x7, xp7, v7, a7, i7, o7⟩ := pushX_run (W := W) (σ := σ6) (l := st) (e := V "ol")
    (v := o.length) (by simpa [e6] using x5) (by simpa [e6] using xp5) (by simp [e6]; omega) (by omega)
  obtain ⟨σ8, r8, x8, xp8, i8, v8, a8, o8⟩ := rdN_full (W := W) (σ := σ7) (pre := st ++ [o.length])
    (u := o) (rest := []) (nv := "ol") (by decide) x7 xp7 (by rw [i7]; simp [e6])
    (by rw [v7 _ (by decide)]; simp [e6]) (by simp; omega)
    (fun v hv => by have := hent v (by simp [hv]); omega)
  have himg : imgJ (j + 1) (g :: S) o = st ++ [o.length] ++ o := by
    simp [imgJ, hst, toWord_listNat]
  have hvW : σ8.vars "W" = W := by
    rw [v8 _ (by decide), v7 _ (by decide)]; simp [e6]; rw [v5 _ (by decide), env0_vars]; simp
  have hvo : σ8.vars "ovf" = 0 := by
    rw [v8 _ (by decide), v7 _ (by decide)]; simp [e6]; rw [v5 _ (by decide), env0_vars]; simp
  have hob8 : σ8.arrs "OB" = List.replicate (W + 1) 0 := by
    rw [a8 _ (by decide), a7 _ (by decide)]; simp [e6]; rw [a5 _ (by decide), env0_arrs]
  have hwp8 : σ8.arrs "wp" = List.replicate (W + 1) 0 := by
    rw [a8 _ (by decide), a7 _ (by decide)]; simp [e6]; rw [a5 _ (by decide), env0_arrs]
  rw [← himg] at x8
  obtain ⟨hC8, hx48⟩ := ctx_of (M := M) (σ := σ8) (img := imgJ (j + 1) (g :: S) o) hvW x8
    (by rw [himg]; simp; omega) hob8 hwp8 (fun v hv => hent v (by rw [himg] at hv; simpa using hv))
    hm16 hroom
  have hF8 : Filled "OB" "po" [] σ8 := ⟨by
      rw [v8 _ (by decide), v7 _ (by decide)]; simp [e6, po5], fun i h => absurd h (by simp)⟩
  have hL8 : σ8.vars "L" = (stWord (j + 1) (g :: S)).length := by
    rw [v8 _ (by decide), v7 _ (by decide)]; simp [e6, L5, hst]
  have hXt : (σ8.arrs "x").take (imgJ (j + 1) (g :: S) o).length = imgJ (j + 1) (g :: S) o := by
    rw [x8]; exact List.take_left' rfl
  have hok := reached_ok hI hR
  have hcur := hok j (by omega)
  rw [htr] at hcur
  have hnext := hok (j + 1) le_rfl
  rw [trT_succ_call htr] at hnext
  have hj1 : j + 1 ∈ st := by simp [hst, stWord]
  have hjM : j + 1 + 1 < M := by have := hent (j + 1) (by simp [hj1]); omega
  obtain ⟨σ9, ob, K, r9, hb9, jr9, l9, c9, w9, ov9, -, ol9, out9⟩ := roundJ_run (szP G k q u₁ u₂)
    hC8 hx48 hXt (by rw [himg]; simp; omega) hL8 hF8 hcur hfit (pick_ansWord hfit b) hnext hjM
  have hsel : Run (W + 1) roundSel σ5 σ9 (1 + 3 + (1 + ((6 + 1) + ((20 * o.length + 10) + K)))) := by
    refine Run.ite_false (by
      rw [show (Cond.eq (V "tg") (N 0)) = Cond.eq (.var "tg") (.lit 0) from rfl,
        evalB_condEq (evalB_var (by rw [tg5]; omega)) (evalB_lit (by omega)), tg5]; rfl) ?_
    exact Run.seqs_cons (by simp) r6 (Run.seqs_cons (by simp) r7 (Run.seqs_cons (by simp) r8
      (Run.seqs_one r9)))
  refine ⟨σ9, ob, _, Run.seqs_app3 (by simp [headL]) (by simp) r5 (Run.seqs_one hsel), ?_, jr9, ?_,
    ?_, ?_, ?_, l9, ?_⟩
  · rw [trT_succ_call htr]; exact hb9
  · rw [w9, hvW]
  · rw [ov9, hvo]
  · rw [out9, o8, o7]; simp [e6]; rw [o5]; simp [env0, initEnv]
  · rw [ol9, hob8]; simp
  · have hK : K ≤ 1000 * (st.length + 1 + o.length + ob.length + 1) := by
      rw [himg] at c9; simp at c9; omega
    exact costS_arith hK hul

/-- **The build of a round.** -/
theorem buildCmd_run (hI : Inst G k q u₁ u₂) {j : ℕ} (hR : Reached G k q u₁ u₂ j) {W : ℕ}
    (hW : 2 ^ 30 ≤ W + 1) (hin : ∀ e ∈ uT G k q u₁ u₂ j, 2 ^ 16 * (e + 1) ≤ W + 1)
    (hlen : 2 ^ 14 * ((uT G k q u₁ u₂ j).length + 513) ≤ W + 1) :
    ∃ σ' ob K, Run (W + 1) buildCmd ((initEnv (fun _ => W + 1) (uT G k q u₁ u₂ j)).setVar "W" W) σ' K ∧
      Built (j + 1) (trT G k q u₁ u₂ j) ob σ' ∧ σ'.vars "jr" = j ∧ σ'.vars "W" = W ∧
      σ'.vars "ovf" = 0 ∧ σ'.out = [] ∧ (σ'.arrs "OB").length = W + 1 ∧ 16 * ob.length ≤ W ∧
      K ≤ 2000 * ((uT G k q u₁ u₂ j).length + ob.length + 1) := by
  cases j with
  | zero => exact build0_run hI hW hin hlen
  | succ j => exact buildS_run hI hR hW hin hlen

end rounds

end Lax185574Proofs.CompRam
