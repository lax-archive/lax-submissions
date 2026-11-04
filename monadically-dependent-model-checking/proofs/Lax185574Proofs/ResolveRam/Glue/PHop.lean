import Lax185574Proofs.ResolveRam.Glue.PMem
import Lax185574Proofs.FarRam.Loops

/-!
The tests `nearW` and `hop2W` of lem:resolve-lift on atom lists held in an
array.

`nearC A p X s i` sets `mb` to `1` exactly if the atom word
`[5, s + 1, X, i]` is in the list of words at the position held in `p`
(`nearC_run`), by `memScan`. `hop2C A` decides `hop2W` between position
`hi1` of the atom list at `hp1` and position `hi2` of the atom list at
`hp2`, for the radius `hs`, the colors `hP`, `hQ` and the flags `hcP`,
`hcQ` (whether `P` and `Q` occur, as `0` or `1`), with the answer in `hw`
(`hop2C_run`). It runs over all pairs of radii `s₁, s₂ ≤ s` with four
look-ups each.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

/-- The scalars of the target. -/
def mN : List String := ["tmp", "tmL", "tm0", "tm1", "tm2", "tm3"]

/-- Look up `[5, s + 1, X, i]` in the list at `p` of `A`. -/
def nearC (A p X s i : String) : Com :=
  .seq (.assign "tmp" (.var p)) (.seq (.assign "tmL" (.lit 4)) (.seq (.assign "tm0" (.lit 5))
    (.seq (.assign "tm1" (.add (.var s) (.lit 1))) (.seq (.assign "tm2" (.var X))
      (.seq (.assign "tm3" (.var i)) (memScan A))))))

theorem nearC_wvars (A p X s i : String) : ∀ y ∈ (nearC A p X s i).wvars, y ∈ mN ++ mV := by
  intro y hy
  simp only [nearC, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  have := memScan_wvars A y
  simp only [mN, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem nearC_warrs (A p X s i : String) : (nearC A p X s i).warrs = [] := by
  simp [nearC, Com.warrs, memScan_warrs]

theorem nearC_reads (A p X s i : String) : ¬ (nearC A p X s i).reads := by
  have := memScan_reads A
  simp_all [nearC, Com.reads]

theorem nearC_noWrite (A p X s i : String) : (nearC A p X s i).NoWrite := by
  have := memScan_noWrite A
  simp_all [nearC, Com.NoWrite]

/-- **The test `nearW` on a list of words in an array.** -/
theorem nearC_run {B : ℕ} {A p X s i : String} {Xa : List ℕ} {pos : ℕ} {ws : List (List ℕ)}
    {r : List ℕ} {σ : Env} (hn : ∀ y ∈ [p, X, s, i], y ∉ mN)
    (hX : σ.arrs A = Xa) (hdr : Xa.drop pos = toWord ws ++ r) (hp : σ.vars p = pos)
    (hXv : σ.vars X < B) (hsv : σ.vars s + 1 < B) (hiv : σ.vars i < B)
    (hpB : pos + (toWord ws).length + 6 < B) (hv : ∀ v ∈ toWord ws, v < B) :
    ∃ σ', Run B (nearC A p X s i) σ σ' (70 * ws.length + 60) ∧
      σ'.vars "tmb" = bv (nearW ws (σ.vars X) (σ.vars s) (σ.vars i)) ∧
      (∀ y, y ∉ mN ++ mV → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hp' := hn p (by simp)
  have hX' := hn X (by simp)
  have hs' := hn s (by simp)
  have hi' := hn i (by simp)
  simp only [mN, List.mem_cons, List.not_mem_nil, or_false, not_or] at hp' hX' hs' hi'
  have hw0 : 0 < (toWord ws).length := by rw [toWord_words]; simp
  set t : List ℕ := [5, σ.vars s + 1, σ.vars X, σ.vars i]
  set σ1 := σ.setVar "tmp" pos
  set σ2 := σ1.setVar "tmL" 4
  set σ3 := σ2.setVar "tm0" 5
  set σ4 := σ3.setVar "tm1" (σ.vars s + 1)
  set σ5 := σ4.setVar "tm2" (σ.vars X)
  set σ6 := σ5.setVar "tm3" (σ.vars i)
  have r1 : Run B (.assign "tmp" (.var p)) σ σ1 2 := Run.assign (ev_var hp (by omega))
  have r2 : Run B (.assign "tmL" (.lit 4)) σ1 σ2 2 := Run.assign (evalB_lit (by omega))
  have r3 : Run B (.assign "tm0" (.lit 5)) σ2 σ3 2 := Run.assign (evalB_lit (by omega))
  have r4 : Run B (.assign "tm1" (.add (.var s) (.lit 1))) σ3 σ4 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ3, σ2, σ1, hs'.1, hs'.2.1, hs'.2.2.1]) (by omega))
      (evalB_lit (by omega)) hsv)).mono (by simp [Expr.size])
  have r5 : Run B (.assign "tm2" (.var X)) σ4 σ5 2 :=
    Run.assign (ev_var (by simp [σ4, σ3, σ2, σ1, hX'.1, hX'.2.1, hX'.2.2.1, hX'.2.2.2.1]) hXv)
  have r6 : Run B (.assign "tm3" (.var i)) σ5 σ6 2 :=
    Run.assign (ev_var (by simp [σ5, σ4, σ3, σ2, σ1, hi'.1, hi'.2.1, hi'.2.2.1, hi'.2.2.2.1,
      hi'.2.2.2.2.1]) hiv)
  have ht : TargetAt t σ6 := ⟨Or.inr rfl, by simp [σ6, σ5, σ4, σ3, σ2, t], by simp [σ6, σ5, σ4, σ3, t],
    by simp [σ6, σ5, σ4, t], by simp [σ6, σ5, t], fun _ => by simp [σ6, t]⟩
  obtain ⟨σ7, r7, b7, v7, a7, o7, i7⟩ := memScan_run (B := B) (A := A) (σ := σ6)
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hX]) hdr (by simp [σ6, σ5, σ4, σ3, σ2, σ1]) ht
    (by intro v hv'; simp [t] at hv'; rcases hv' with rfl | rfl | rfl | rfl <;> omega) (by omega) (by omega) hv
  refine ⟨σ7, ?_, ?_, fun y hy => ?_, by rw [a7]; simp [σ6, σ5, σ4, σ3, σ2, σ1],
    by rw [o7]; simp [σ6, σ5, σ4, σ3, σ2, σ1], by rw [i7]; simp [σ6, σ5, σ4, σ3, σ2, σ1]⟩
  · unfold nearC
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono
      (by omega)
  · rw [b7]; simp [nearW, inW, bv, t]
  · simp only [List.mem_append, not_or] at hy
    rw [v7 y hy.2]
    simp only [mN, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [σ6, σ5, σ4, σ3, σ2, σ1, hy.1.1, hy.1.2.1, hy.1.2.2.1, hy.1.2.2.2.1, hy.1.2.2.2.2.1,
      hy.1.2.2.2.2.2]

/-- A look-up with its answer kept in `r`. -/
def nearSet (A p X s i r : String) : Com := .seq (nearC A p X s i) (.assign r (.var "tmb"))

theorem nearSet_run {B : ℕ} {A p X s i r : String} {Xa : List ℕ} {pos : ℕ} {ws : List (List ℕ)}
    {rr : List ℕ} {σ : Env} (hn : ∀ y ∈ [p, X, s, i], y ∉ mN)
    (hX : σ.arrs A = Xa) (hdr : Xa.drop pos = toWord ws ++ rr) (hp : σ.vars p = pos)
    (hXv : σ.vars X < B) (hsv : σ.vars s + 1 < B) (hiv : σ.vars i < B)
    (hpB : pos + (toWord ws).length + 6 < B) (hv : ∀ v ∈ toWord ws, v < B) :
    ∃ σ', Run B (nearSet A p X s i r) σ σ' (70 * ws.length + 62) ∧
      σ'.vars r = bv (nearW ws (σ.vars X) (σ.vars s) (σ.vars i)) ∧
      (∀ y, y ∉ mN ++ mV → y ≠ r → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  obtain ⟨σ1, r1, b1, f1, a1, o1, i1⟩ := nearC_run (B := B) hn hX hdr hp hXv hsv hiv hpB hv
  have hb : σ1.vars "tmb" < B := by rw [b1]; exact lt_of_le_of_lt (bv_le _) (by omega)
  refine ⟨σ1.setVar r (σ1.vars "tmb"), (Run.seq r1 (Run.assign (ev_var rfl hb))).mono (by simp [Expr.size]),
    by simp [b1], fun y hy hr => by simp [hr, f1 y hy], by simp [a1], by simp [o1], by simp [i1]⟩

/-! ### One pair of radii -/

/-- Set `v` to `1` if both conditions hold. -/
def flagIf (c1 c2 : Cond) (v : String) : Com := .ite c1 (.ite c2 (.assign v (.lit 1)) .skip) .skip

theorem flagIf_run {B : ℕ} {c1 c2 : Cond} {v : String} {τ : Env} {b1 b2 : Bool}
    (h1 : c1.evalB B τ = some b1) (h2 : b1 = true → c2.evalB B τ = some b2) (hB : 1 < B) :
    Run B (flagIf c1 c2 v) τ (if b1 && b2 then τ.setVar v 1 else τ) (c1.size + c2.size + 5) := by
  unfold flagIf
  cases b1
  · exact (Run.ite_false h1 Run.skip).mono (by omega)
  · cases b2
    · exact (Run.ite_true h1 (Run.ite_false (h2 rfl) Run.skip)).mono (by omega)
    · exact (Run.ite_true h1 (Run.ite_true (h2 rfl) (Run.assign (evalB_lit hB)))).mono
        (by simp [Expr.size]; omega)

/-- The test of one pair of radii `s₁, s₂` in `hop2W`. -/
def pairB (A₁ A₂ : List (List ℕ)) (P Q : ℕ) (cP cQ : Bool) (i j s s₁ s₂ : ℕ) : Bool :=
  (decide (s₁ + 1 + s₂ ≤ s) && ((nearW A₁ P s₁ i && nearW A₂ Q s₂ j) ||
    (nearW A₁ Q s₁ i && nearW A₂ P s₂ j))) ||
  (decide (s₁ + 2 + s₂ ≤ s) && ((nearW A₁ P s₁ i && nearW A₂ P s₂ j && cQ) ||
    (nearW A₁ Q s₁ i && nearW A₂ Q s₂ j && cP)))

theorem hop2W_pairB (Dw : DW) (A₁ : List (List ℕ)) (i : ℕ) (A₂ : List (List ℕ)) (j s : ℕ) :
    hop2W Dw A₁ i A₂ j s = (List.range (s + 1)).any fun s₁ => (List.range (s + 1)).any fun s₂ =>
      pairB A₁ A₂ Dw.P Dw.Q Dw.cP Dw.cQ i j s s₁ s₂ := rfl

/-- The first condition of a pair. -/
def pc1 : Cond := .lt (.add (.var "ta") (.var "tb")) (.var "ts")

def pc2 : Cond := .lt (.lit 0) (.add (.mul (.var "tA") (.var "tD")) (.mul (.var "tB") (.var "tC")))

def pc3 : Cond := .lt (.add (.add (.var "ta") (.var "tb")) (.lit 1)) (.var "ts")

def pc4 : Cond := .lt (.lit 0) (.add (.mul (.mul (.var "tA") (.var "tC")) (.var "tcQ"))
  (.mul (.mul (.var "tB") (.var "tD")) (.var "tcP")))

/-- One pair of radii `ta`, `tb`: four look-ups and the two tests. -/
def pairC (A₁ A₂ : String) : Com :=
  .seq (nearSet A₁ "tp1" "tP" "ta" "ti1" "tA") (.seq (nearSet A₁ "tp1" "tQ" "ta" "ti1" "tB")
  (.seq (nearSet A₂ "tp2" "tP" "tb" "ti2" "tC") (.seq (nearSet A₂ "tp2" "tQ" "tb" "ti2" "tD")
  (.seq (.assign "tv" (.lit 0)) (.seq (flagIf pc1 pc2 "tv") (flagIf pc3 pc4 "tv"))))))

/-- The scalars that `pairC` writes. -/
def pV : List String := mN ++ mV ++ ["tA", "tB", "tC", "tD", "tv"]

theorem pairC_wvars (A₁ A₂ : String) : ∀ y ∈ (pairC A₁ A₂).wvars, y ∈ pV := by
  simp only [pairC, nearSet, flagIf, nearC, memScan, memBody, memMatch, memLast, forUp, Com.wvars,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.nil_append, List.append_nil,
    or_imp, forall_and, forall_eq]
  simp [pV, mN, mV]

theorem pairC_warrs (A₁ A₂ : String) : (pairC A₁ A₂).warrs = [] := by
  simp [pairC, nearSet, flagIf, Com.warrs, nearC_warrs]

theorem pairC_reads (A₁ A₂ : String) : ¬ (pairC A₁ A₂).reads := by
  have := nearC_reads A₁ "tp1" "tP" "ta" "ti1"
  have := nearC_reads A₁ "tp1" "tQ" "ta" "ti1"
  have := nearC_reads A₂ "tp2" "tP" "tb" "ti2"
  have := nearC_reads A₂ "tp2" "tQ" "tb" "ti2"
  simp_all [pairC, nearSet, flagIf, Com.reads]

theorem pairC_noWrite (A₁ A₂ : String) : (pairC A₁ A₂).NoWrite := by
  have := nearC_noWrite A₁ "tp1" "tP" "ta" "ti1"
  have := nearC_noWrite A₁ "tp1" "tQ" "ta" "ti1"
  have := nearC_noWrite A₂ "tp2" "tP" "tb" "ti2"
  have := nearC_noWrite A₂ "tp2" "tQ" "tb" "ti2"
  simp_all [pairC, nearSet, flagIf, Com.NoWrite]

/-- The data of `hop2C`: the two atom lists, the colors, the flags, the
positions and the radius, in the scalars of `rN`. -/
structure HopAt (A₁ A₂ : String) (X₁ X₂ : List ℕ) (ws₁ ws₂ : List (List ℕ)) (p₁ p₂ : ℕ)
    (Dw : DW) (i j s : ℕ) (τ : Env) : Prop where
  a1 : τ.arrs A₁ = X₁
  a2 : τ.arrs A₂ = X₂
  p1 : τ.vars "tp1" = p₁
  p2 : τ.vars "tp2" = p₂
  P : τ.vars "tP" = Dw.P
  Q : τ.vars "tQ" = Dw.Q
  cP : τ.vars "tcP" = bv Dw.cP
  cQ : τ.vars "tcQ" = bv Dw.cQ
  i1 : τ.vars "ti1" = i
  i2 : τ.vars "ti2" = j
  s : τ.vars "ts" = s

/-- The scalars that `HopAt` reads. -/
def rN : List String := ["tp1", "tp2", "tP", "tQ", "tcP", "tcQ", "ti1", "ti2", "ts"]

theorem HopAt.congr {A₁ A₂ : String} {X₁ X₂ : List ℕ} {ws₁ ws₂ : List (List ℕ)} {p₁ p₂ : ℕ}
    {Dw : DW} {i j s : ℕ} {τ τ' : Env} (h : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ)
    (hv : ∀ y ∈ rN, τ'.vars y = τ.vars y) (ha : τ'.arrs = τ.arrs) :
    HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ' := by
  obtain ⟨a1, a2, p1, p2, P, Q, cP, cQ, i1, i2, s⟩ := h
  exact ⟨by rw [ha, a1], by rw [ha, a2], by rw [hv _ (by simp [rN]), p1], by rw [hv _ (by simp [rN]), p2],
    by rw [hv _ (by simp [rN]), P], by rw [hv _ (by simp [rN]), Q], by rw [hv _ (by simp [rN]), cP],
    by rw [hv _ (by simp [rN]), cQ], by rw [hv _ (by simp [rN]), i1], by rw [hv _ (by simp [rN]), i2],
    by rw [hv _ (by simp [rN]), s]⟩

theorem bv_mul_add (a b c d : Bool) :
    (0 < bv a * bv b + bv c * bv d) = ((a && b || c && d) = true) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [bv]

theorem bv_mul3_add (a b c d e f : Bool) :
    (0 < bv a * bv b * bv c + bv d * bv e * bv f) = ((a && b && c || d && e && f) = true) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> simp [bv]

/-- The bounds a look-up needs. -/
structure HopB (B p₁ p₂ : ℕ) (ws₁ ws₂ : List (List ℕ)) (Dw : DW) (i j s : ℕ) : Prop where
  x1 : p₁ + (toWord ws₁).length + 6 < B
  x2 : p₂ + (toWord ws₂).length + 6 < B
  v1 : ∀ v ∈ toWord ws₁, v < B
  v2 : ∀ v ∈ toWord ws₂, v < B
  P : Dw.P < B
  Q : Dw.Q < B
  i : i < B
  j : j < B
  s : 2 * s + 4 < B

theorem ite_bv (c d : Bool) : (if c = true then 1 else bv d) = bv (d || c) := by
  cases c <;> cases d <;> rfl

/-- **One pair of radii.** -/
theorem pairC_run {B : ℕ} {A₁ A₂ : String} {X₁ X₂ : List ℕ} {ws₁ ws₂ : List (List ℕ)}
    {p₁ p₂ : ℕ} {r₁ r₂ : List ℕ} {Dw : DW} {i j s s₁ s₂ : ℕ} {τ : Env}
    (hH : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ) (hd₁ : X₁.drop p₁ = toWord ws₁ ++ r₁)
    (hd₂ : X₂.drop p₂ = toWord ws₂ ++ r₂) (hb : HopB B p₁ p₂ ws₁ ws₂ Dw i j s)
    (ha : τ.vars "ta" = s₁) (hb' : τ.vars "tb" = s₂) (hs₁ : s₁ ≤ s) (hs₂ : s₂ ≤ s) :
    ∃ τ', Run B (pairC A₁ A₂) τ τ' (140 * (ws₁.length + ws₂.length) + 400) ∧
      τ'.vars "tv" = bv (pairB ws₁ ws₂ Dw.P Dw.Q Dw.cP Dw.cQ i j s s₁ s₂) ∧
      (∀ y, y ∉ pV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  obtain ⟨hx1, hx2, hv1, hv2, hPB, hQB, hiB, hjB, hsB⟩ := hb
  have kp : ∀ y ∈ rN ++ ["ta", "tb"], y ∉ mN ++ mV ∧ y ∉ ["tA", "tB", "tC", "tD", "tv"] := by decide
  have kA : ∀ y ∈ ["tA", "tB", "tC", "tD"], y ∉ mN ++ mV := by decide
  -- a look-up keeps the data
  have step : ∀ (τa τb : Env) (r : String), r ∈ ["tA", "tB", "tC", "tD"] →
      HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τa → τa.vars "ta" = s₁ → τa.vars "tb" = s₂ →
      (∀ y, y ∉ mN ++ mV → y ≠ r → τb.vars y = τa.vars y) → τb.arrs = τa.arrs →
      HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τb ∧ τb.vars "ta" = s₁ ∧ τb.vars "tb" = s₂ := by
    intro τa τb r hr hH' ha' hb'' hf hA
    have kr : ∀ y ∈ rN ++ ["ta", "tb"], τb.vars y = τa.vars y := fun y hy => by
      obtain ⟨k1, k2⟩ := kp y hy
      exact hf y k1 (fun h => k2 (by subst h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto))
    exact ⟨hH'.congr (fun y hy => kr y (List.mem_append_left _ hy)) hA,
      by rw [kr "ta" (by simp), ha'], by rw [kr "tb" (by simp), hb'']⟩
  have nn1 : ∀ y ∈ ["tp1", "tP", "ta", "ti1"], y ∉ mN := by decide
  have nn2 : ∀ y ∈ ["tp1", "tQ", "ta", "ti1"], y ∉ mN := by decide
  have nn3 : ∀ y ∈ ["tp2", "tP", "tb", "ti2"], y ∉ mN := by decide
  have nn4 : ∀ y ∈ ["tp2", "tQ", "tb", "ti2"], y ∉ mN := by decide
  obtain ⟨τ1, r1, b1, f1, a1, o1, i1⟩ := nearSet_run (B := B) (r := "tA") nn1 hH.a1 hd₁ hH.p1
    (by rw [hH.P]; exact hPB) (by rw [ha]; omega) (by rw [hH.i1]; exact hiB) hx1 hv1
  obtain ⟨H1, ha1, hb1⟩ := step τ τ1 "tA" (by simp) hH ha hb' f1 a1
  obtain ⟨τ2, r2, b2, f2, a2, o2, i2⟩ := nearSet_run (B := B) (r := "tB") nn2 H1.a1 hd₁ H1.p1
    (by rw [H1.Q]; exact hQB) (by rw [ha1]; omega) (by rw [H1.i1]; exact hiB) hx1 hv1
  obtain ⟨H2, ha2, hb2⟩ := step τ1 τ2 "tB" (by simp) H1 ha1 hb1 f2 a2
  obtain ⟨τ3, r3, b3, f3, a3, o3, i3⟩ := nearSet_run (B := B) (r := "tC") nn3 H2.a2 hd₂ H2.p2
    (by rw [H2.P]; exact hPB) (by rw [hb2]; omega) (by rw [H2.i2]; exact hjB) hx2 hv2
  obtain ⟨H3, ha3, hb3⟩ := step τ2 τ3 "tC" (by simp) H2 ha2 hb2 f3 a3
  obtain ⟨τ4, r4, b4, f4, a4, o4, i4⟩ := nearSet_run (B := B) (r := "tD") nn4 H3.a2 hd₂ H3.p2
    (by rw [H3.Q]; exact hQB) (by rw [hb3]; omega) (by rw [H3.i2]; exact hjB) hx2 hv2
  obtain ⟨H4, ha4, hb4⟩ := step τ3 τ4 "tD" (by simp) H3 ha3 hb3 f4 a4
  set nA := nearW ws₁ Dw.P s₁ i
  set nB := nearW ws₁ Dw.Q s₁ i
  set nC := nearW ws₂ Dw.P s₂ j
  set nD := nearW ws₂ Dw.Q s₂ j
  have vA : τ4.vars "tA" = bv nA := by
    rw [f4 _ (kA _ (by simp)) (by decide), f3 _ (kA _ (by simp)) (by decide),
      f2 _ (kA _ (by simp)) (by decide), b1, hH.P, ha, hH.i1]
  have vB : τ4.vars "tB" = bv nB := by
    rw [f4 _ (kA _ (by simp)) (by decide), f3 _ (kA _ (by simp)) (by decide), b2, H1.Q, ha1, H1.i1]
  have vC : τ4.vars "tC" = bv nC := by
    rw [f4 _ (kA _ (by simp)) (by decide), b3, H2.P, hb2, H2.i2]
  have vD : τ4.vars "tD" = bv nD := by rw [b4, H3.Q, hb3, H3.i2]
  set τ5 := τ4.setVar "tv" 0
  have r5 : Run B (.assign "tv" (.lit 0)) τ4 τ5 2 := Run.assign (evalB_lit (by omega))
  have bvB : ∀ b : Bool, bv b < B := fun b => lt_of_le_of_lt (bv_le b) (by omega)
  have hm : ∀ a b : Bool, bv a * bv b ≤ 1 := fun a b => by cases a <;> cases b <;> simp [bv]
  have hm3 : ∀ a b c : Bool, bv a * bv b * bv c ≤ 1 := fun a b c => by
    cases a <;> cases b <;> cases c <;> simp [bv]
  -- the scalars that the tests read are those of `τ5`, also after the first test
  have ev : ∀ τ' : Env, (∀ y ∈ ["tA", "tB", "tC", "tD", "ta", "tb", "ts", "tcP", "tcQ"],
      τ'.vars y = τ5.vars y) →
      pc1.evalB B τ' = some (decide (s₁ + s₂ < s)) ∧
      pc2.evalB B τ' = some (decide (0 < bv nA * bv nD + bv nB * bv nC)) ∧
      pc3.evalB B τ' = some (decide (s₁ + s₂ + 1 < s)) ∧
      pc4.evalB B τ' = some (decide (0 < bv nA * bv nC * bv Dw.cQ + bv nB * bv nD * bv Dw.cP)) := by
    intro τ' hτ'
    have g : ∀ y ∈ ["tA", "tB", "tC", "tD", "ta", "tb", "ts", "tcP", "tcQ"], τ'.vars y = τ4.vars y :=
      fun y hy => by
        rw [hτ' y hy]
        have : y ≠ "tv" := by intro h; subst h; simp at hy
        simp [τ5, this]
    have eA := ev_var (B := B) (by rw [g "tA" (by simp), vA]) (bvB nA)
    have eB := ev_var (B := B) (by rw [g "tB" (by simp), vB]) (bvB nB)
    have eC := ev_var (B := B) (by rw [g "tC" (by simp), vC]) (bvB nC)
    have eD := ev_var (B := B) (by rw [g "tD" (by simp), vD]) (bvB nD)
    have ecP := ev_var (B := B) (by rw [g "tcP" (by simp), H4.cP]) (bvB Dw.cP)
    have ecQ := ev_var (B := B) (by rw [g "tcQ" (by simp), H4.cQ]) (bvB Dw.cQ)
    have ea := ev_var (B := B) (by rw [g "ta" (by simp), ha4]) (show s₁ < B by omega)
    have eb := ev_var (B := B) (by rw [g "tb" (by simp), hb4]) (show s₂ < B by omega)
    have es := ev_var (B := B) (by rw [g "ts" (by simp), H4.s]) (show s < B by omega)
    refine ⟨evalB_condLt (ev_add ea eb (by omega)) es, evalB_condLt (evalB_lit (by omega))
      (ev_add (evalB_bin eA eD (lt_of_le_of_lt (hm nA nD) (by omega)))
        (evalB_bin eB eC (lt_of_le_of_lt (hm nB nC) (by omega)))
        (lt_of_le_of_lt (Nat.add_le_add (hm nA nD) (hm nB nC)) (by omega))),
      evalB_condLt (ev_add (ev_add ea eb (by omega)) (evalB_lit (by omega)) (by omega)) es,
      evalB_condLt (evalB_lit (by omega)) (ev_add
        (evalB_bin (evalB_bin eA eC (lt_of_le_of_lt (hm nA nC) (by omega))) ecQ
          (lt_of_le_of_lt (hm3 nA nC Dw.cQ) (by omega)))
        (evalB_bin (evalB_bin eB eD (lt_of_le_of_lt (hm nB nD) (by omega))) ecP
          (lt_of_le_of_lt (hm3 nB nD Dw.cP) (by omega)))
        (lt_of_le_of_lt (Nat.add_le_add (hm3 nA nC Dw.cQ) (hm3 nB nD Dw.cP)) (by omega)))⟩
  obtain ⟨c1, c2, -, -⟩ := ev τ5 (fun _ _ => rfl)
  have r6 := flagIf_run (v := "tv") c1 (fun _ => c2) (by omega)
  set τ6 := if decide (s₁ + s₂ < s) && decide (0 < bv nA * bv nD + bv nB * bv nC) then
    τ5.setVar "tv" 1 else τ5
  have h56 : ∀ y, y ≠ "tv" → τ6.vars y = τ5.vars y := fun y hy => by
    simp only [τ6]; split_ifs <;> simp [hy]
  obtain ⟨-, -, c3, c4⟩ := ev τ6 (fun y hy => h56 y (by intro h; subst h; simp at hy))
  have r7 := flagIf_run (v := "tv") c3 (fun _ => c4) (by omega)
  set τ7 := if decide (s₁ + s₂ + 1 < s) &&
    decide (0 < bv nA * bv nC * bv Dw.cQ + bv nB * bv nD * bv Dw.cP) then τ6.setVar "tv" 1 else τ6
  have hτ6v : τ6.vars "tv" = bv (decide (s₁ + s₂ < s) && (nA && nD || nB && nC)) := by
    simp only [τ6, bv_mul_add, Bool.decide_eq_true]
    split_ifs with h
    · simp only [vars_setVar, if_true]; rw [h]; rfl
    · simp only [Bool.not_eq_true] at h; rw [h]; simp [τ5]
  have a67 : τ7.arrs = τ4.arrs := by simp only [τ7, τ6, τ5]; split_ifs <;> simp
  have o67 : τ7.out = τ4.out ∧ τ7.inp = τ4.inp := by simp only [τ7, τ6, τ5]; split_ifs <;> simp
  refine ⟨τ7, ?_, ?_, fun y hy => ?_, ?_, ?_, ?_⟩
  · unfold pairC
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 r7)))))).mono ?_
    simp only [pc1, pc2, pc3, pc4, Cond.size, Expr.size]
    omega
  · have : τ7.vars "tv" = if decide (s₁ + s₂ + 1 < s) &&
        decide (0 < bv nA * bv nC * bv Dw.cQ + bv nB * bv nD * bv Dw.cP) then 1 else τ6.vars "tv" := by
      simp only [τ7]; split_ifs <;> simp
    rw [this, hτ6v]
    simp only [bv_mul3_add, Bool.decide_eq_true]
    rw [ite_bv]
    unfold pairB
    rw [show decide (s₁ + 1 + s₂ ≤ s) = decide (s₁ + s₂ < s) from decide_eq_decide.mpr (by omega),
      show decide (s₁ + 2 + s₂ ≤ s) = decide (s₁ + s₂ + 1 < s) from decide_eq_decide.mpr (by omega)]
  · have hp : y ∉ mN ++ mV ∧ y ≠ "tA" ∧ y ≠ "tB" ∧ y ≠ "tC" ∧ y ≠ "tD" ∧ y ≠ "tv" := by
      simp only [pV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      exact ⟨by simp only [List.mem_append, not_or]; exact ⟨hy.1.1, hy.1.2⟩, hy.2⟩
    have h7 : τ7.vars y = τ6.vars y := by simp only [τ7]; split_ifs <;> simp [hp.2.2.2.2.2]
    rw [h7, h56 y hp.2.2.2.2.2]
    simp only [τ5, vars_setVar, hp.2.2.2.2.2, if_false]
    rw [f4 y hp.1 hp.2.2.2.2.1, f3 y hp.1 hp.2.2.2.1, f2 y hp.1 hp.2.2.1, f1 y hp.1 hp.2.1]
  · rw [a67, a4, a3, a2, a1]
  · rw [o67.1, o4, o3, o2, o1]
  · rw [o67.2, i4, i3, i2, i1]

end Lax185574Proofs.ResolveRam.Glue
