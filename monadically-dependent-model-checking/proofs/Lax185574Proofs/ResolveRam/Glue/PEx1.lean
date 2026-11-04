import Lax185574Proofs.ResolveRam.Glue.PKid

/-!
The guards of an expansion of lem:resolve-lift.

`gEmit` appends the frame of the word `i :: g :: h₀ :: h₁ :: h₂ :: u`,
with `i`, `g`, `h₀`, `h₁`, `h₂` in `ii`, `tG`, `th0`, `th1`, `th2` and
`u` the segment of length `tsN` from `tsS` of the array `a`
(`gEmit_run`). `gLoop` runs the test `hopW` between every position
`tG < ℓ` and the new position `ℓ` of the root whose atom list is at
`tp1 = tp2` and appends a frame for every guard that passes, which are
the words of `guardW` with the index `i` in front (`gLoop_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- Append the frame of `i :: g :: h₀ :: h₁ :: h₂ :: u` and count it. -/
def gEmit : Com :=
  .seq (push1 "OB" "po" (.add (.var "tsN") (.lit 5))) (.seq (push1 "OB" "po" (.var "ii"))
    (.seq (push1 "OB" "po" (.var "tG")) (.seq (push1 "OB" "po" (.var "th0"))
      (.seq (push1 "OB" "po" (.var "th1")) (.seq (push1 "OB" "po" (.var "th2"))
        (.seq (cpSeg "a" "tsS" "tsN") (.assign "pc" (.add (.var "pc") (.lit 1)))))))))

/-- The data of an emission. -/
structure EmAt (i g h₀ h₁ h₂ s : ℕ) (u : List ℕ) (τ : Env) : Prop where
  vi : τ.vars "ii" = i
  vg : τ.vars "tG" = g
  v0 : τ.vars "th0" = h₀
  v1 : τ.vars "th1" = h₁
  v2 : τ.vars "th2" = h₂
  vs : τ.vars "tsS" = s
  vn : τ.vars "tsN" = u.length
  vseg : seg (τ.arrs "a") s u.length = u

/-- The scalars that `EmAt` reads. -/
def emN : List String := ["ii", "tG", "th0", "th1", "th2", "tsS", "tsN"]

theorem EmAt.of {i g h₀ h₁ h₂ s : ℕ} {u : List ℕ} {τ τ' : Env} (h : EmAt i g h₀ h₁ h₂ s u τ)
    (hv : ∀ y ∈ emN, τ'.vars y = τ.vars y) (ha : τ'.arrs "a" = τ.arrs "a") : EmAt i g h₀ h₁ h₂ s u τ' := by
  obtain ⟨a, b, c, d, e, f, n, sg⟩ := h
  exact ⟨by rw [hv _ (by simp [emN]), a], by rw [hv _ (by simp [emN]), b], by rw [hv _ (by simp [emN]), c],
    by rw [hv _ (by simp [emN]), d], by rw [hv _ (by simp [emN]), e], by rw [hv _ (by simp [emN]), f],
    by rw [hv _ (by simp [emN]), n], by rw [ha, sg]⟩

/-- **Appending a word.** -/
theorem gEmit_run {W : ℕ} {pre : List ℕ} {i g h₀ h₁ h₂ s c : ℕ} {u : List ℕ} {τ : Env}
    (hE : EmAt i g h₀ h₁ h₂ s u τ) (hF : Filled "OB" "po" pre τ) (hpc : τ.vars "pc" = c)
    (hOB : (τ.arrs "OB").length = W + 1) (ha : s + u.length ≤ (τ.arrs "a").length)
    (hB : pre.length + u.length + 6 ≤ W) (hs : s + u.length ≤ W)
    (hv : ∀ x ∈ i :: g :: h₀ :: h₁ :: h₂ :: u, x ≤ W) (hc : c + 1 ≤ W) :
    ∃ τ', Run (W + 1) gEmit τ τ' (20 * u.length + 80) ∧
      Filled "OB" "po" (pre ++ frames [i :: g :: h₀ :: h₁ :: h₂ :: u]) τ' ∧ τ'.vars "pc" = c + 1 ∧
      OFr τ τ' ["po", "ci", "pc"] := by
  have hvi : i ≤ W := hv i (by simp)
  have hvg : g ≤ W := hv g (by simp)
  have hv0 : h₀ ≤ W := hv h₀ (by simp)
  have hv1 : h₁ ≤ W := hv h₁ (by simp)
  have hv2 : h₂ ≤ W := hv h₂ (by simp)
  obtain ⟨τ1, r1, F1, o1⟩ := push1_ofr (W := W) (e := .add (.var "tsN") (.lit 5)) (v := u.length + 5) hF
    (ev_add (ev_var hE.vn (by omega)) (evalB_lit (by omega)) (by omega)) (by rw [hOB]; omega) (by omega)
  have k1 : ∀ y ∈ emN ++ ["pc"], τ1.vars y = τ.vars y := fun y hy => o1.vars y (by
    simp [emN] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨τ2, r2, F2, o2⟩ := push1_ofr (W := W) (e := .var "ii") (v := i) F1
    (ev_var (by rw [k1 "ii" (by simp [emN]), hE.vi]) (by omega)) (by rw [o1.len, hOB]; simp; omega)
    (by simp; omega)
  have k2 : ∀ y ∈ emN ++ ["pc"], τ2.vars y = τ.vars y := fun y hy => by
    rw [o2.vars y (by simp [emN] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k1 y hy]
  obtain ⟨τ3, r3, F3, o3⟩ := push1_ofr (W := W) (e := .var "tG") (v := g) F2
    (ev_var (by rw [k2 "tG" (by simp [emN]), hE.vg]) (by omega)) (by rw [o2.len, o1.len, hOB]; simp; omega)
    (by simp; omega)
  have k3 : ∀ y ∈ emN ++ ["pc"], τ3.vars y = τ.vars y := fun y hy => by
    rw [o3.vars y (by simp [emN] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k2 y hy]
  obtain ⟨τ4, r4, F4, o4⟩ := push1_ofr (W := W) (e := .var "th0") (v := h₀) F3
    (ev_var (by rw [k3 "th0" (by simp [emN]), hE.v0]) (by omega))
    (by rw [o3.len, o2.len, o1.len, hOB]; simp; omega) (by simp; omega)
  have k4 : ∀ y ∈ emN ++ ["pc"], τ4.vars y = τ.vars y := fun y hy => by
    rw [o4.vars y (by simp [emN] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k3 y hy]
  obtain ⟨τ5, r5, F5, o5⟩ := push1_ofr (W := W) (e := .var "th1") (v := h₁) F4
    (ev_var (by rw [k4 "th1" (by simp [emN]), hE.v1]) (by omega))
    (by rw [o4.len, o3.len, o2.len, o1.len, hOB]; simp; omega) (by simp; omega)
  have k5 : ∀ y ∈ emN ++ ["pc"], τ5.vars y = τ.vars y := fun y hy => by
    rw [o5.vars y (by simp [emN] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k4 y hy]
  obtain ⟨τ6, r6, F6, o6⟩ := push1_ofr (W := W) (e := .var "th2") (v := h₂) F5
    (ev_var (by rw [k5 "th2" (by simp [emN]), hE.v2]) (by omega))
    (by rw [o5.len, o4.len, o3.len, o2.len, o1.len, hOB]; simp; omega) (by simp; omega)
  have k6 : ∀ y ∈ emN ++ ["pc"], τ6.vars y = τ.vars y := fun y hy => by
    rw [o6.vars y (by simp [emN] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k5 y hy]
  have a6 : τ6.arrs "a" = τ.arrs "a" := by
    rw [o6.arrs _ (by decide), o5.arrs _ (by decide), o4.arrs _ (by decide), o3.arrs _ (by decide),
      o2.arrs _ (by decide), o1.arrs _ (by decide)]
  have l6 : (τ6.arrs "OB").length = W + 1 := by rw [o6.len, o5.len, o4.len, o3.len, o2.len, o1.len, hOB]
  obtain ⟨τ7, r7, F7, o7⟩ := cpSeg_ofr (W := W) (src := "a") (s := "tsS") (l := "tsN") (a := s)
    (N := u.length) (σ := τ6) (by decide) (by rw [k6 "tsS" (by simp [emN]), hE.vs])
    (by rw [k6 "tsN" (by simp [emN]), hE.vn]) (by decide) (by decide) (by decide) (by decide) F6
    (by rw [a6]; exact ha) (by rw [l6]; simp; omega) hs (by simp; omega)
    (by rw [a6, hE.vseg]; intro x hx; exact hv x (by simp [hx]))
  rw [a6, hE.vseg] at F7
  have hpc7 : τ7.vars "pc" = c := by rw [o7.vars _ (by decide), k6 "pc" (by simp), hpc]
  set τ8 := τ7.setVar "pc" (c + 1)
  have r8 : Run (W + 1) (.assign "pc" (.add (.var "pc") (.lit 1))) τ7 τ8 4 :=
    (Run.assign (ev_add (ev_var hpc7 (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  refine ⟨τ8, ?_, ?_, by simp [τ8], ?_⟩
  · unfold gEmit
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono ?_
    simp only [Expr.size]; omega
  · have : frames [i :: g :: h₀ :: h₁ :: h₂ :: u] = [u.length + 5, i, g, h₀, h₁, h₂] ++ u := by
      rw [frames_single]; simp
    rw [this]
    simpa [List.append_assoc] using F7.setVar (y := "pc") (by decide) (c + 1)
  · exact (((((((o1.trans o2).trans o3).trans o4).trans o5).trans o6).trans o7).trans
      (OFr.setVar τ7 "pc" _)).mono (by decide)

/-- One guard. -/
def gBody : Com :=
  .seq (.assign "ti1" (.var "tG")) (.seq (hop2C "a" "a") (.ite (.eq (.var "tw") (.lit 1)) gEmit .skip))

/-- The guards `tG < tL`. -/
def gLoop : Com := forUp "tG" (.var "tL") gBody

/-- The scalars that `gLoop` writes. -/
def gLV : List String := hV ++ ["ti1", "po", "ci", "pc", "tG"]

/-- The words of the guards of the word `cw`, with the index `i` in front. -/
def gWords (Dw : DW) (R ℓ : ℕ) (A : List (List ℕ)) (cw : List ℕ) (i j : ℕ) : List (List ℕ) :=
  ((List.range j).filterMap fun g => if hopW Dw A R g ℓ then some (g :: cw) else none).map (i :: ·)

theorem gWords_full (Dw : DW) (R ℓ : ℕ) (A : List (List ℕ)) (cw : List ℕ) (i : ℕ) :
    gWords Dw R ℓ A cw i ℓ = (guardW Dw R ℓ A cw).map (i :: ·) := rfl

theorem gWords_succ (Dw : DW) (R ℓ : ℕ) (A : List (List ℕ)) (cw : List ℕ) (i j : ℕ) :
    gWords Dw R ℓ A cw i (j + 1) = gWords Dw R ℓ A cw i j ++
      (if hopW Dw A R j ℓ then [i :: j :: cw] else []) := by
  unfold gWords
  rw [List.range_succ, List.filterMap_append, List.map_append]
  by_cases h : hopW Dw A R j ℓ <;> simp [h]

theorem length_frames_gWords (Dw : DW) (R ℓ : ℕ) (A : List (List ℕ)) (cw : List ℕ) (i : ℕ) :
    ∀ j, (frames (gWords Dw R ℓ A cw i j)).length = (gWords Dw R ℓ A cw i j).length * (cw.length + 3) ∧
      (gWords Dw R ℓ A cw i j).length ≤ j
  | 0 => by simp [gWords, frames]
  | j + 1 => by
    obtain ⟨h1, h2⟩ := length_frames_gWords Dw R ℓ A cw i j
    rw [gWords_succ, frames_append, List.length_append, List.length_append, h1]
    by_cases h : hopW Dw A R j ℓ
    · rw [if_pos h, frames_single]
      simp only [List.length_append, List.length_cons, List.length_nil]
      constructor
      · ring
      · omega
    · rw [if_neg h]
      simp only [frames, List.map_nil, List.flatten_nil, List.length_nil, List.length_append]
      exact ⟨by ring, by omega⟩

theorem hopAt_re {A₁ A₂ : String} {X₁ X₂ : List ℕ} {ws₁ ws₂ : List (List ℕ)} {p₁ p₂ : ℕ}
    {Dw : DW} {i j s c : ℕ} {τ τ' : Env} (h : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ)
    (hv : ∀ y ∈ rN, y ≠ "ti1" → τ'.vars y = τ.vars y) (ha1 : τ'.arrs A₁ = τ.arrs A₁)
    (ha2 : τ'.arrs A₂ = τ.arrs A₂) (hc : τ'.vars "ti1" = c) : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw c j s τ' := by
  obtain ⟨a1, a2, p1, p2, P, Q, cP, cQ, -, i2, s'⟩ := h
  exact ⟨by rw [ha1, a1], by rw [ha2, a2], by rw [hv _ (by simp [rN]) (by decide), p1],
    by rw [hv _ (by simp [rN]) (by decide), p2], by rw [hv _ (by simp [rN]) (by decide), P],
    by rw [hv _ (by simp [rN]) (by decide), Q], by rw [hv _ (by simp [rN]) (by decide), cP],
    by rw [hv _ (by simp [rN]) (by decide), cQ], hc, by rw [hv _ (by simp [rN]) (by decide), i2],
    by rw [hv _ (by simp [rN]) (by decide), s']⟩

theorem emAt_re {i g g' h₀ h₁ h₂ s : ℕ} {u : List ℕ} {τ τ' : Env} (h : EmAt i g h₀ h₁ h₂ s u τ)
    (hv : ∀ y ∈ emN, y ≠ "tG" → τ'.vars y = τ.vars y) (ha : τ'.arrs "a" = τ.arrs "a")
    (hg : τ'.vars "tG" = g') : EmAt i g' h₀ h₁ h₂ s u τ' := by
  obtain ⟨a, b, c, d, e, f, n, sg⟩ := h
  exact ⟨by rw [hv _ (by simp [emN]) (by decide), a], hg, by rw [hv _ (by simp [emN]) (by decide), c],
    by rw [hv _ (by simp [emN]) (by decide), d], by rw [hv _ (by simp [emN]) (by decide), e],
    by rw [hv _ (by simp [emN]) (by decide), f], by rw [hv _ (by simp [emN]) (by decide), n], by rw [ha, sg]⟩

/-- **The guards of a word.** -/
theorem gLoop_run {W : ℕ} {Xa : List ℕ} {A : List (List ℕ)} {p : ℕ} {r : List ℕ} {Dw : DW}
    {ℓ R i h₀ h₁ h₂ s c : ℕ} {u : List ℕ} {pre : List ℕ} {τ : Env}
    (hH : HopAt "a" "a" Xa Xa A A p p Dw (τ.vars "ti1") ℓ R τ) (hd : Xa.drop p = toWord A ++ r)
    (hE : EmAt i (τ.vars "tG") h₀ h₁ h₂ s u τ) (hL : τ.vars "tL" = ℓ) (hF : Filled "OB" "po" pre τ)
    (hpc : τ.vars "pc" = c) (hOB : (τ.arrs "OB").length = W + 1) (ha : s + u.length ≤ (τ.arrs "a").length)
    (hB : pre.length + ℓ * (u.length + 6) ≤ W) (hs : s + u.length ≤ W)
    (hv : ∀ x ∈ i :: h₀ :: h₁ :: h₂ :: u, x ≤ W) (hc : c + ℓ + 1 ≤ W)
    (hB₁ : p + (toWord A).length + 6 < W + 1) (hv₁ : ∀ v ∈ toWord A, v < W + 1)
    (hPB : Dw.P < W + 1) (hQB : Dw.Q < W + 1) (hℓ : ℓ + 1 < W + 1) (hR : 2 * R + 4 < W + 1) :
    ∃ τ', Run (W + 1) gLoop τ τ' (ℓ * (hopK (A.length + A.length) R + 20 * u.length + 100) + 10) ∧
      Filled "OB" "po" (pre ++ frames ((guardW Dw R ℓ A ([h₀, h₁, h₂] ++ u)).map (i :: ·))) τ' ∧
      τ'.vars "pc" = c + (guardW Dw R ℓ A ([h₀, h₁, h₂] ++ u)).length ∧ OFr τ τ' gLV := by
  set cw := [h₀, h₁, h₂] ++ u
  have hcw : cw.length = u.length + 3 := by simp [cw]
  let I : ℕ → Env → Prop := fun j ρ =>
    Filled "OB" "po" (pre ++ frames (gWords Dw R ℓ A cw i j)) ρ ∧
    ρ.vars "pc" = c + (gWords Dw R ℓ A cw i j).length ∧ OFr τ ρ gLV
  have kE : ∀ y ∈ emN, y ≠ "tG" → y ∉ gLV := by decide
  have kH : ∀ y ∈ rN, y ≠ "ti1" → y ∉ gLV := by decide
  obtain ⟨τ', r', ⟨F', c', o'⟩, -⟩ := forUp_run (B := W + 1) (i := "tG") (e := .var "tL") (body := gBody)
    (N := ℓ) (K := hopK (A.length + A.length) R + 20 * u.length + 90) I (σ := τ) (by omega)
    (fun j _ ρ hI _ => ev_var (by rw [hI.2.2.vars _ (by decide), hL]) (by omega))
    ⟨by simpa [gWords, frames] using hF.setVar (y := "tG") (by decide) 0, by simp [gWords, hpc],
      (OFr.setVar τ "tG" 0).mono (by decide)⟩
    (by
      rintro j hj ρ ⟨Fρ, cρ, oρ⟩ hjρ
      set ρ1 := ρ.setVar "ti1" j
      have r1 : Run (W + 1) (.assign "ti1" (.var "tG")) ρ ρ1 2 := Run.assign (ev_var hjρ (by omega))
      have H1 : HopAt "a" "a" Xa Xa A A p p Dw j ℓ R ρ1 :=
        hopAt_re hH (fun y hy hne => by simp only [ρ1, vars_setVar, hne, if_false]; exact oρ.vars y (kH y hy hne))
          (by simp only [ρ1, arrs_setVar]; rw [oρ.arrs "a" (by decide)])
          (by simp only [ρ1, arrs_setVar]; rw [oρ.arrs "a" (by decide)]) (by simp [ρ1])
      obtain ⟨ρ2, r2, w2, f2, a2, o2, i2⟩ := hop2C_run H1 hd hd
        ⟨hB₁, hB₁, hv₁, hv₁, hPB, hQB, by omega, by omega, hR⟩
      have k2 : ∀ y, y ∉ hV → y ≠ "ti1" → ρ2.vars y = ρ.vars y := fun y h1 h2 => by
        rw [f2 y h1]; simp [ρ1, h2]
      have hlen := length_frames_gWords Dw R ℓ A cw i j
      have hcap : pre.length + (frames (gWords Dw R ℓ A cw i j)).length + u.length + 6 ≤ W := by
        rw [hlen.1, hcw, show u.length + 3 + 3 = u.length + 6 by omega]
        have := Nat.mul_le_mul_right (u.length + 6) (show (gWords Dw R ℓ A cw i j).length + 1 ≤ ℓ by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have cw2 : (Cond.eq (.var "tw") (.lit 1)).evalB (W + 1) ρ2 = some (hopW Dw A R j ℓ) := by
        rw [evalB_condEq (ev_var w2 (lt_of_le_of_lt (bv_le _) (by omega))) (evalB_lit (by omega))]
        unfold hopW; cases hop2W Dw A j A ℓ R <;> rfl
      have hsucc := gWords_succ Dw R ℓ A cw i j
      have hpc2 : ρ2.vars "pc" = c + (gWords Dw R ℓ A cw i j).length := by rw [k2 _ (by decide) (by decide), cρ]
      have F2 : Filled "OB" "po" (pre ++ frames (gWords Dw R ℓ A cw i j)) ρ2 :=
        Fρ.congr (k2 _ (by decide) (by decide)) (by rw [a2]; simp [ρ1])
      have hK : 2 + (hopK (A.length + A.length) R + (7 + (20 * u.length + 80))) ≤
          hopK (A.length + A.length) R + 20 * u.length + 90 := by omega
      by_cases hh : hopW Dw A R j ℓ = true
      · have E2 : EmAt i j h₀ h₁ h₂ s u ρ2 :=
          emAt_re hE (fun y hy hne => by rw [k2 y (fun h => kE y hy hne (List.mem_append_left _ h)) (by
              intro h; subst h; simp [emN] at hy), oρ.vars y (kE y hy hne)])
            (by rw [a2]; simp only [ρ1, arrs_setVar]; exact oρ.arrs "a" (by decide)) (by rw [k2 _ (by decide) (by decide), hjρ])
        obtain ⟨ρ3, r3, F3, c3, o3⟩ := gEmit_run (W := W) E2 F2 hpc2
          (by rw [a2]; simp only [ρ1, arrs_setVar]; rw [oρ.len, hOB])
          (by rw [a2]; simp only [ρ1, arrs_setVar]; rw [oρ.arrs "a" (by decide)]; exact ha)
          (by simp only [List.length_append]; omega) hs
          (fun x hx => by
              rcases List.mem_cons.1 hx with h | hx
              · subst h; exact hv _ (List.mem_cons_self ..)
              rcases List.mem_cons.1 hx with h | hx
              · omega
              · exact hv x (List.mem_cons_of_mem _ hx))
          (by have := hlen.2; omega)
        refine ⟨ρ3, ?_, by rw [o3.vars _ (by decide), k2 _ (by decide) (by decide), hjρ], ?_, ?_, ?_⟩
        · unfold gBody
          exact (Run.seq r1 (Run.seq r2 (Run.ite_true (by rw [cw2, hh]) r3))).mono (by simp [Cond.size, Expr.size]; omega)
        · rw [hsucc, if_pos hh, frames_append, ← List.append_assoc]
          exact F3.setVar (by decide) _
        · simp only [vars_setVar, show ("pc" : String) ≠ "tG" by decide, if_false]
          rw [c3, hsucc, if_pos hh]; simp; omega
        · exact (oρ.trans (((OFr.setVar ρ "ti1" j).trans (ofr_of_test f2 a2 o2 i2)).trans
            (o3.trans (OFr.setVar ρ3 "tG" _)))).mono (by decide)
      · have hh' : hopW Dw A R j ℓ = false := by simpa using hh
        refine ⟨ρ2, ?_, by rw [k2 _ (by decide) (by decide), hjρ], ?_, ?_, ?_⟩
        · unfold gBody
          exact (Run.seq r1 (Run.seq r2 (Run.ite_false (by rw [cw2, hh']) Run.skip))).mono
            (by simp [Cond.size, Expr.size]; omega)
        · rw [hsucc, if_neg hh, List.append_nil]; exact F2.setVar (by decide) _
        · simp only [vars_setVar, show ("pc" : String) ≠ "tG" by decide, if_false]
          rw [hpc2, hsucc, if_neg hh, List.append_nil]
        · exact (oρ.trans (((OFr.setVar ρ "ti1" j).trans (ofr_of_test f2 a2 o2 i2)).trans
            (OFr.setVar ρ2 "tG" _))).mono (by decide))
  refine ⟨τ', r'.mono ?_, by rw [← gWords_full]; exact F', by rw [c', gWords_full, List.length_map], o'⟩
  have := Nat.mul_le_mul_left ℓ (show hopK (A.length + A.length) R + 20 * u.length + 90 + Expr.size (.var "tL") + 7 ≤
    hopK (A.length + A.length) R + 20 * u.length + 100 by simp [Expr.size])
  simp only [Expr.size] at this ⊢
  omega

end Lax185574Proofs.ResolveRam.Glue
