import Lax185574Proofs.ResolveRam.Glue.PAt3

/-!
The loops over the candidates `[d, i, j]` and `[3, Y, i]` of the atom
words of lem:resolve-lift.

The data that the loops read are fixed in the scalars `aN` (`AtD`): the
atom list of the tree at `tp1` (and `tp2`), the colors, their flags and
the sign, the arity `tL`, the number `tnc` of colors of the table and its
start `tcb0`, and the two radii. `pairLoop d T` runs over the pairs of
positions and emits the candidates `[d, i, j]` that pass, with the extra
test `T` (`pairLoop_run`). `colLoop` does the same for the candidates
`[3, Y, i]`, with the colors `Y` read from the table (`colLoop_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- The data of the loops. -/
structure AtD (Xa : List ℕ) (p₁ : ℕ) (Dw : DW) (ℓ nc cb Rm Rp : ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = Xa
  p1 : τ.vars "tp1" = p₁
  p2 : τ.vars "tp2" = p₁
  P : τ.vars "tP" = Dw.P
  Q : τ.vars "tQ" = Dw.Q
  cP : τ.vars "tcP" = bv Dw.cP
  cQ : τ.vars "tcQ" = bv Dw.cQ
  sg : τ.vars "tsg" = bv Dw.sg
  L : τ.vars "tL" = ℓ
  nc : τ.vars "tnc" = nc
  cb : τ.vars "tcb0" = cb
  Rm : τ.vars "tRm" = Rm
  Rp : τ.vars "tRp" = Rp

/-- The scalars that `AtD` reads. -/
def aN : List String := ["tp1", "tp2", "tP", "tQ", "tcP", "tcQ", "tsg", "tL", "tnc", "tcb0", "tRm", "tRp"]

theorem AtD.ofr {Xa : List ℕ} {p₁ : ℕ} {Dw : DW} {ℓ nc cb Rm Rp : ℕ} {τ τ' : Env} {Vs : List String}
    (h : AtD Xa p₁ Dw ℓ nc cb Rm Rp τ) (o : OFr τ τ' Vs) (hn : ∀ y ∈ aN, y ∉ Vs) :
    AtD Xa p₁ Dw ℓ nc cb Rm Rp τ' := by
  obtain ⟨a, p1, p2, P, Q, cP, cQ, sg, L, nc, cb, Rm, Rp⟩ := h
  exact ⟨by rw [o.arrs "a" (by decide), a], by rw [o.vars _ (hn _ (by simp [aN])), p1],
    by rw [o.vars _ (hn _ (by simp [aN])), p2], by rw [o.vars _ (hn _ (by simp [aN])), P],
    by rw [o.vars _ (hn _ (by simp [aN])), Q], by rw [o.vars _ (hn _ (by simp [aN])), cP],
    by rw [o.vars _ (hn _ (by simp [aN])), cQ], by rw [o.vars _ (hn _ (by simp [aN])), sg],
    by rw [o.vars _ (hn _ (by simp [aN])), L], by rw [o.vars _ (hn _ (by simp [aN])), nc],
    by rw [o.vars _ (hn _ (by simp [aN])), cb], by rw [o.vars _ (hn _ (by simp [aN])), Rm],
    by rw [o.vars _ (hn _ (by simp [aN])), Rp]⟩

theorem filter_single (f : List ℕ → Bool) (c : List ℕ) : [c].filter f = if f c then [c] else [] := by
  simp only [List.filter_cons, List.filter_nil]

theorem notMem_append {y : String} {l₁ l₂ : List String} (h₁ : y ∉ l₁) (h₂ : y ∉ l₂) : y ∉ l₁ ++ l₂ := by
  simp only [List.mem_append, not_or]; exact ⟨h₁, h₂⟩

/-- The extra test `T` decides `ex`, from any state with the data. -/
def TSpec (W : ℕ) (T : Com) (KT : ℕ) (VT : List String) (D : Env → Prop) (ex : Bool) : Prop :=
  ∀ τ1 : Env, D τ1 → τ1.vars "tF" = 0 →
    ∃ τ2, Run (W + 1) T τ1 τ2 KT ∧ τ2.vars "tF" = bv ex ∧ OFr τ1 τ2 VT ∧ τ2.arrs = τ1.arrs

/-- **One candidate.** The data survive the look-up. -/
theorem cand_run {W KT : ℕ} {T : Com} {VT : List String} {ex : Bool} {setC : Com} {Ks : ℕ}
    {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {ℓ nc cb Rm Rp : ℕ} {pre c : List ℕ}
    {L : List (List ℕ)} {τ : Env} (f : List ℕ → Bool) (D : Env → Prop)
    (hD : AtD Xa p₁ Dw ℓ nc cb Rm Rp τ) (hd : Xa.drop p₁ = toWord A ++ rr)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1)
    (hcv : ∀ v ∈ c, v ≤ W) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ [c].filter f)).length ≤ W) (hW5 : 5 ≤ W)
    (hf : f c = (inW A c || ex))
    (hS : ∃ τ1, Run (W + 1) setC τ τ1 Ks ∧ TdAt c τ1 ∧ OFr τ τ1 tdN ∧ τ1.arrs = τ.arrs)
    (hDs : ∀ τ1 τ2, D τ1 → OFr τ1 τ2 lkV → τ2.arrs = τ1.arrs → D τ2)
    (hD0 : ∀ τ1, OFr τ τ1 tdN → τ1.arrs = τ.arrs → TdAt c τ1 → D τ1)
    (hT : TSpec W T KT VT D ex) (hVT : ∀ y ∈ VT, y ∉ tdN ∧ y ≠ "po" ∧ y ≠ "fc") :
    ∃ τ', Run (W + 1) (.seq setC (emitC T)) τ τ' (Ks + 70 * A.length + KT + 120) ∧
      Em pre (L ++ [c].filter f) τ' ∧ OFr τ τ' (tdN ++ (lkV ++ VT ++ ["po", "fc"])) := by
  obtain ⟨τ1, r1, c1, o1, a1⟩ := hS
  have hE1 : Em pre L τ1 := hE.congr (o1.vars "po" (by decide)) (o1.vars "fc" (by decide)) (by rw [a1])
  have hD1 := hD0 τ1 o1 a1 c1
  obtain ⟨τ2, r2, E2, o2⟩ := emitC_run (T := T) (extra := ex) (KT := KT) (VT := VT)
    (by rw [a1]; exact hD.a) hd (by rw [o1.vars "tp1" (by decide)]; exact hD.p1) c1 hcv (by omega) hv hE1
    (by rw [a1, hOB]) (by rw [← hf, ← filter_single]; exact hB) hW5
    (fun τ' o' a' hF => hT τ' (hDs τ1 τ' hD1 o' a') hF) hVT
  rw [← hf, ← filter_single] at E2
  exact ⟨τ2, (Run.seq r1 r2).mono (by omega), E2, o1.trans o2⟩

theorem app_single_sub {V : List String} {x : String} (hx : x ∈ V) : V ++ [x] ⊆ V := by
  intro y hy
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with h | rfl
  · exact h
  · exact hx

theorem app_sub {V U : List String} (h : ∀ y ∈ U, y ∈ V) : V ++ U ⊆ V := by
  intro y hy
  rcases List.mem_append.1 hy with h' | h'
  · exact h'
  · exact h y h'

/-! ### The pairs of positions -/

/-- The loop over the candidates `[d, i, j]`. -/
def pairLoop (d : ℕ) (T : Com) : Com :=
  forUp "tqi" (.var "tL") (forUp "tqj" (.var "tL") (.seq (setD3 d "tqi" "tqj") (emitC T)))

/-- The scalars that `pairLoop d T` writes. -/
def plV (VT : List String) : List String := ["tqi", "tqj"] ++ (tdN ++ (lkV ++ VT ++ ["po", "fc"]))

theorem plV_aN {VT : List String} (hVT : ∀ y ∈ VT, y ∉ aN) : ∀ y ∈ aN, y ∉ plV VT := by
  intro y hy
  have k1 : ∀ y ∈ aN, y ∉ ["tqi", "tqj"] := by decide
  have k2 : ∀ y ∈ aN, y ∉ tdN := by decide
  have k3 : ∀ y ∈ aN, y ∉ lkV := by decide
  have k4 : ∀ y ∈ aN, y ∉ ["po", "fc"] := by decide
  exact notMem_append (k1 y hy) (notMem_append (k2 y hy) (notMem_append (notMem_append (k3 y hy)
    (fun h => hVT y h hy)) (k4 y hy)))

/-- **The candidates `[d, i, j]`.** -/
theorem pairLoop_run {W d KT : ℕ} {T : Com} {VT : List String} (ex : ℕ → ℕ → Bool)
    {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {ℓ nc cb Rm Rp : ℕ} {pre : List ℕ}
    {L : List (List ℕ)} {τ : Env} (f : List ℕ → Bool)
    (hD : AtD Xa p₁ Dw ℓ nc cb Rm Rp τ) (hd : Xa.drop p₁ = toWord A ++ rr)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1)
    (hdW : d ≤ W) (hℓ : ℓ ≤ W) (hW5 : 5 ≤ W) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ (pB d ℓ).filter f)).length ≤ W)
    (hf : ∀ i j, f [d, i, j] = (inW A [d, i, j] || ex i j))
    (hT : ∀ i j, i < ℓ → j < ℓ → TSpec W T KT VT
      (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ ρ.vars "td1" = i ∧ ρ.vars "td2" = j) (ex i j))
    (hVT : ∀ y ∈ VT, y ∉ tdN ∧ y ≠ "po" ∧ y ≠ "fc" ∧ y ∉ aN ∧ y ≠ "tqi" ∧ y ≠ "tqj") :
    ∃ τ', Run (W + 1) (pairLoop d T) τ τ' (ℓ * (ℓ * (70 * A.length + KT + 138) + 14) + 6) ∧
      Em pre (L ++ (pB d ℓ).filter f) τ' ∧ OFr τ τ' (plV VT) := by
  have hVa := plV_aN (VT := VT) (fun y h => (hVT y h).2.2.2.1)
  have hsub : ∀ y ∈ tdN ++ (lkV ++ VT ++ ["po", "fc"]), y ∈ plV VT := fun y h => by
    simp only [plV, List.mem_append] at h ⊢; tauto
  have hpf : (pB d ℓ).filter f =
      (List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j => [[d, i, j]].filter f := by
    simp [pB, List.filter_flatMap]
  rw [hpf] at hB ⊢
  obtain ⟨σ', r, ⟨-, o'⟩, E'⟩ := emLoop_run (W := W) (N := ℓ) (K := ℓ * (70 * A.length + KT + 138) + 6)
    (v := "tqi") (e := .var "tL") (body := forUp "tqj" (.var "tL") (.seq (setD3 d "tqi" "tqj") (emitC T)))
    (fun i => (List.range ℓ).flatMap fun j => [[d, i, j]].filter f)
    (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ OFr τ ρ (plV VT)) (σ := τ) (by decide) (by decide)
    (by omega) (fun ρ hρ => ev_var hρ.1.L (by omega))
    (fun ρ x hρ => ⟨hρ.1.ofr (OFr.setVar ρ "tqi" x) (fun y hy h => by simp at h; subst h; revert hy; decide),
      (hρ.2.trans (OFr.setVar ρ "tqi" x)).mono (app_single_sub (by simp [plV]))⟩)
    ⟨hD, (OFr.refl τ).mono (by simp)⟩ hE hB
    (by
      rintro i hi L' ρ ⟨Dρ, oρ⟩ hiρ Eρ hb
      obtain ⟨σ2, r2, ⟨D2, o2, i2⟩, E2⟩ := emLoop_run (W := W) (N := ℓ) (K := 70 * A.length + KT + 130)
        (v := "tqj") (e := .var "tL") (body := .seq (setD3 d "tqi" "tqj") (emitC T))
        (fun j => [[d, i, j]].filter f)
        (fun ρ' => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ' ∧ OFr τ ρ' (plV VT) ∧ ρ'.vars "tqi" = i) (σ := ρ)
        (by decide) (by decide) (by omega) (fun ρ' hρ' => ev_var hρ'.1.L (by omega))
        (fun ρ' x hρ' => ⟨hρ'.1.ofr (OFr.setVar ρ' "tqj" x) (fun y hy h => by simp at h; subst h; revert hy; decide),
          (hρ'.2.1.trans (OFr.setVar ρ' "tqj" x)).mono (app_single_sub (by simp [plV])), by simp [hρ'.2.2]⟩)
        ⟨Dρ, oρ, hiρ⟩ Eρ hb
        (by
          rintro j hj L'' ρ' ⟨Dρ', oρ', iρ'⟩ hjρ' Eρ' hb'
          have hOB' : (ρ'.arrs "OB").length = W + 1 := by rw [oρ'.len, hOB]
          obtain ⟨τ', r', E', o''⟩ := cand_run (T := T) (VT := VT) (ex := ex i j) (setC := setD3 d "tqi" "tqj")
            (Ks := 10) (c := [d, i, j]) f
            (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ ρ.vars "td1" = i ∧ ρ.vars "td2" = j) Dρ' hd hB1 hv
            (by intro v hv'; simp at hv'; rcases hv' with rfl | rfl | rfl <;> omega) Eρ' hOB' hb' hW5 (hf i j)
            (by
              obtain ⟨τ1, r1, c1, o1, a1⟩ := setD3_run (B := W + 1) (d := d) (y1 := "tqi") (y2 := "tqj")
                (τ := ρ') (by decide) (by decide) (by omega) (by rw [iρ']; omega) (by rw [hjρ']; omega)
                (by omega)
              rw [iρ', hjρ'] at c1
              exact ⟨τ1, r1, c1, o1, a1⟩)
            (fun τ1 τ2 ⟨D1, t1, t2⟩ o a => ⟨D1.ofr o (by decide), by rw [o.vars "td1" (by decide), t1],
              by rw [o.vars "td2" (by decide), t2]⟩)
            (fun τ1 o a c1 => ⟨Dρ'.ofr o (by decide), by rw [c1.2.2.2.1]; rfl, by rw [c1.2.2.2.2.1]; rfl⟩)
            (hT i j hi hj) (fun y h => ⟨(hVT y h).1, (hVT y h).2.1, (hVT y h).2.2.1⟩)
          have hnij : ∀ y ∈ ["tqi", "tqj"], y ∉ tdN ++ (lkV ++ VT ++ ["po", "fc"]) := by
            intro y hy
            refine notMem_append (by revert y; decide) (notMem_append (notMem_append (by revert y; decide)
              (fun h => ?_)) (by revert y; decide))
            simp at hy; rcases hy with rfl | rfl
            · exact (hVT _ h).2.2.2.2.1 rfl
            · exact (hVT _ h).2.2.2.2.2 rfl
          refine ⟨τ', r'.mono (by omega), by rw [o''.vars "tqj" (hnij _ (by simp)), hjρ'],
            ⟨Dρ'.ofr o'' (fun y hy h => hVa y hy (hsub y h)), (oρ'.trans o'').mono (app_sub hsub),
              by rw [o''.vars "tqi" (hnij _ (by simp)), iρ']⟩, E'⟩)
      refine ⟨σ2, r2, by rw [i2], ⟨D2, o2⟩, by simpa using E2⟩)
  refine ⟨σ', r.mono ?_, by simpa using E', o'⟩
  simp only [Expr.size]
  nlinarith

end Lax185574Proofs.ResolveRam.Glue
