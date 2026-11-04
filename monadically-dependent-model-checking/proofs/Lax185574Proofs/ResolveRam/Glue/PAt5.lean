import Lax185574Proofs.ResolveRam.Glue.PAt4

/-!
The inner loop over the positions of the candidates, and the loop over
the candidates `[3, Y, i]`, for the atom words of lem:resolve-lift.

`iLoop v S T` runs over `v < ℓ`: it writes the candidate with `S` and
emits it if it passes, with the extra test `T` (`iLoop_run`). The
property `K` holds the data of the outer loops. `colLoop` runs over the
colors `Y` of the table and emits the candidates `[3, Y, i]` that are
atoms (`colLoop_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- The inner loop over `v < ℓ`. -/
def iLoop (v : String) (S T : Com) : Com := forUp v (.var "tL") (.seq S (emitC T))

/-- The scalars that `iLoop v S T` writes. -/
def ilV (v : String) (VT : List String) : List String := [v] ++ (tdN ++ (lkV ++ VT ++ ["po", "fc"]))

/-- The scalars of the loops over the candidates. -/
def qV : List String := ["tqs", "tqi", "tqj", "tqm", "tqY", "tx", "tz"]

theorem notMem_ilV {y v : String} {VT : List String} (h1 : y ≠ v) (h2 : y ∉ tdN) (h3 : y ∉ lkV)
    (h4 : y ∉ VT) (h5 : y ∉ ["po", "fc"]) : y ∉ ilV v VT :=
  notMem_append (by simpa using h1) (notMem_append h2 (notMem_append (notMem_append h3 h4) h5))

theorem aN_ilV {v : String} {VT : List String} (hv : v ∉ aN) (hVT : ∀ y ∈ VT, y ∉ aN) :
    ∀ y ∈ aN, y ∉ ilV v VT := by
  intro y hy
  have k2 : ∀ y ∈ aN, y ∉ tdN := by decide
  have k3 : ∀ y ∈ aN, y ∉ lkV := by decide
  have k4 : ∀ y ∈ aN, y ∉ ["po", "fc"] := by decide
  exact notMem_ilV (by intro h; subst h; exact hv hy) (k2 y hy) (k3 y hy) (fun h => hVT y h hy) (k4 y hy)

/-- **The inner loop.** -/
theorem iLoop_run {W KT Ks : ℕ} {v : String} {S T : Com} {VT : List String} (c : ℕ → List ℕ)
    (ex : ℕ → Bool) (K : Env → Prop) {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW}
    {ℓ nc cb Rm Rp : ℕ} {pre : List ℕ} {L : List (List ℕ)} {τ : Env} (f : List ℕ → Bool)
    (hv1 : v ∉ aN) (hv2 : v ∉ tdN ++ lkV ++ ["po", "fc"])
    (hD : AtD Xa p₁ Dw ℓ nc cb Rm Rp τ) (hK : K τ) (hKs : ∀ ρ ρ', K ρ → OFr ρ ρ' (ilV v VT) → K ρ')
    (hd : Xa.drop p₁ = toWord A ++ rr) (hB1 : p₁ + (toWord A).length + 6 < W + 1)
    (hv : ∀ v ∈ toWord A, v < W + 1) (hℓ : ℓ ≤ W) (hW5 : 5 ≤ W) (hE : Em pre L τ)
    (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ (List.range ℓ).flatMap fun i => [c i].filter f)).length ≤ W)
    (hcv : ∀ i < ℓ, ∀ u ∈ c i, u ≤ W) (hf : ∀ i, f (c i) = (inW A (c i) || ex i))
    (hS : ∀ i < ℓ, ∀ ρ, AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ → K ρ → ρ.vars v = i →
      ∃ τ1, Run (W + 1) S ρ τ1 Ks ∧ TdAt (c i) τ1 ∧ OFr ρ τ1 tdN ∧ τ1.arrs = ρ.arrs)
    (hT : ∀ i < ℓ, TSpec W T KT VT (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ K ρ ∧ TdAt (c i) ρ) (ex i))
    (hVT : ∀ y ∈ VT, y ∉ tdN ∧ y ≠ "po" ∧ y ≠ "fc" ∧ y ∉ aN ∧ y ≠ v) :
    ∃ τ', Run (W + 1) (iLoop v S T) τ τ' (ℓ * (Ks + 70 * A.length + KT + 128) + 6) ∧
      Em pre (L ++ (List.range ℓ).flatMap fun i => [c i].filter f) τ' ∧ OFr τ τ' (ilV v VT) := by
  have hVa : ∀ y ∈ aN, y ∉ ilV v VT := by
    intro y hy
    have k2 : ∀ y ∈ aN, y ∉ tdN := by decide
    have k3 : ∀ y ∈ aN, y ∉ lkV := by decide
    have k4 : ∀ y ∈ aN, y ∉ ["po", "fc"] := by decide
    exact notMem_append (by simp; intro h; subst h; exact hv1 hy) (notMem_append (k2 y hy)
      (notMem_append (notMem_append (k3 y hy) (fun h => (hVT y h).2.2.2.1 hy)) (k4 y hy)))
  have hsub : ∀ y ∈ tdN ++ (lkV ++ VT ++ ["po", "fc"]), y ∈ ilV v VT := fun y h => by
    simp only [ilV, List.mem_append] at h ⊢; tauto
  have hlk : lkV ⊆ ilV v VT := fun y h => by simp only [ilV, List.mem_append]; tauto
  have htd : tdN ⊆ ilV v VT := fun y h => by simp only [ilV, List.mem_append]; tauto
  have hnv : v ∉ tdN ++ (lkV ++ VT ++ ["po", "fc"]) := by
    simp only [List.mem_append, not_or] at hv2 ⊢
    exact ⟨hv2.1.1, ⟨hv2.1.2, fun h => (hVT v h).2.2.2.2 rfl⟩, hv2.2⟩
  obtain ⟨σ', r, ⟨-, -, o'⟩, E'⟩ := emLoop_run (W := W) (N := ℓ) (K := Ks + 70 * A.length + KT + 120)
    (v := v) (e := .var "tL") (body := .seq S (emitC T)) (fun i => [c i].filter f)
    (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ K ρ ∧ OFr τ ρ (ilV v VT)) (σ := τ)
    (by intro h; subst h; simp at hv2) (by intro h; subst h; simp at hv2)
    (by omega) (fun ρ hρ => ev_var hρ.1.L (by omega))
    (fun ρ x hρ => ⟨hρ.1.ofr (OFr.setVar ρ v x) (fun y hy h => by simp at h; subst h; exact hv1 hy),
      hKs ρ _ hρ.2.1 ((OFr.setVar ρ v x).mono (by simp [ilV])),
      (hρ.2.2.trans (OFr.setVar ρ v x)).mono (app_single_sub (by simp [ilV]))⟩)
    ⟨hD, hK, (OFr.refl τ).mono (by simp)⟩ hE hB
    (by
      rintro i hi L' ρ ⟨Dρ, Kρ, oρ⟩ hiρ Eρ hb
      have hOB' : (ρ.arrs "OB").length = W + 1 := by rw [oρ.len, hOB]
      obtain ⟨τ', r', E'', o''⟩ := cand_run (T := T) (VT := VT) (ex := ex i) (setC := S) (Ks := Ks)
        (c := c i) f (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ K ρ ∧ TdAt (c i) ρ) Dρ hd hB1 hv
        (hcv i hi) Eρ hOB' hb hW5 (hf i) (hS i hi ρ Dρ Kρ hiρ)
        (fun τ1 τ2 ⟨D1, K1, t1⟩ o a => ⟨D1.ofr o (by decide), hKs τ1 τ2 K1 (o.mono hlk),
          t1.congr (fun y hy => o.vars y (by revert hy; revert y; decide))⟩)
        (fun τ1 o a c1 => ⟨Dρ.ofr o (by decide), hKs ρ τ1 Kρ (o.mono htd), c1⟩)
        (hT i hi) (fun y h => ⟨(hVT y h).1, (hVT y h).2.1, (hVT y h).2.2.1⟩)
      exact ⟨τ', r', by rw [o''.vars v hnv, hiρ],
        ⟨Dρ.ofr o'' (fun y hy h => hVa y hy (hsub y h)), hKs ρ τ' Kρ (o''.mono hsub),
          (oρ.trans o'').mono (app_sub hsub)⟩, E''⟩)
  refine ⟨σ', r.mono ?_, by simpa using E', o'⟩
  simp only [Expr.size]
  nlinarith

/-! ### The colors -/

/-- The loop over the candidates `[3, Y, i]`. -/
def colLoop : Com :=
  forUp "tqm" (.var "tnc") (.seq (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
    (iLoop "tqi" (setD3 3 "tqY" "tqi") .skip))

/-- The scalars that `colLoop` writes. -/
def clV : List String := ["tqm", "tqY"] ++ ilV "tqi" []

/-- The skip as an extra test that fails. -/
theorem skip_tspec (W : ℕ) (D : Env → Prop) : TSpec W .skip 1 [] D false :=
  fun τ1 _ hF => ⟨τ1, Run.skip, by simp [hF, bv], (OFr.refl τ1).mono (by simp), rfl⟩

/-- **The candidates `[3, Y, i]`.** -/
theorem colLoop_run {W : ℕ} {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {ℓ cb Rm Rp : ℕ}
    {cs pre : List ℕ} {L : List (List ℕ)} {τ : Env} (f : List ℕ → Bool)
    (hD : AtD Xa p₁ Dw ℓ cs.length cb Rm Rp τ) (hd : Xa.drop p₁ = toWord A ++ rr)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) (hℓ : ℓ ≤ W)
    (hW5 : 5 ≤ W) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ (cB cs ℓ).filter f)).length ≤ W)
    (hcol : ∀ m < cs.length, Xa[cb + m * 3]? = some (cs.getD m 0))
    (hcsW : ∀ Y ∈ cs, Y ≤ W) (hcb : cb + 3 * cs.length ≤ W)
    (hf : ∀ Y i, f [3, Y, i] = inW A [3, Y, i]) :
    ∃ τ', Run (W + 1) colLoop τ τ' (cs.length * (ℓ * (70 * A.length + 139) + 21) + 6) ∧
      Em pre (L ++ (cB cs ℓ).filter f) τ' ∧ OFr τ τ' clV := by
  have hcf : (cB cs ℓ).filter f = (List.range cs.length).flatMap fun m =>
      (List.range ℓ).flatMap fun i => [[3, cs.getD m 0, i]].filter f := by
    simp [cB, List.filter_flatMap]
  have hgW : ∀ m, cs.getD m 0 ≤ W := fun m => by
    rcases Nat.lt_or_ge m cs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hcsW _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; omega
  have hVa : ∀ y ∈ aN, y ∉ clV := by decide
  rw [hcf] at hB ⊢
  obtain ⟨σ', r, ⟨-, o'⟩, E'⟩ := emLoop_run (W := W) (N := cs.length)
    (K := 7 + (ℓ * (10 + 70 * A.length + 1 + 128) + 6)) (v := "tqm") (e := .var "tnc")
    (body := .seq (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
      (iLoop "tqi" (setD3 3 "tqY" "tqi") .skip))
    (fun m => (List.range ℓ).flatMap fun i => [[3, cs.getD m 0, i]].filter f)
    (fun ρ => AtD Xa p₁ Dw ℓ cs.length cb Rm Rp ρ ∧ OFr τ ρ clV) (σ := τ) (by decide) (by decide)
    (by omega) (fun ρ hρ => ev_var hρ.1.nc (by omega))
    (fun ρ x hρ => ⟨hρ.1.ofr (OFr.setVar ρ "tqm" x) (by decide),
      (hρ.2.trans (OFr.setVar ρ "tqm" x)).mono (app_single_sub (by decide))⟩)
    ⟨hD, (OFr.refl τ).mono (by simp)⟩ hE hB
    (by
      rintro m hm L' ρ ⟨Dρ, oρ⟩ hmρ Eρ hb
      set Y := cs.getD m 0
      set τ1 := ρ.setVar "tqY" Y
      have r1 : Run (W + 1) (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
          ρ τ1 7 :=
        (Run.assign (evalB_get (ev_add (ev_var Dρ.cb (by omega)) (evalB_bin (ev_var hmρ (by omega))
          (evalB_lit (n := 3) (by omega)) (by simp only [Bop.apply]; omega)) (by simp only [Bop.apply]; omega))
          (by rw [Dρ.a]; exact hcol m hm) (by have := hgW m; omega))).mono (by simp [Expr.size])
      have D1 : AtD Xa p₁ Dw ℓ cs.length cb Rm Rp τ1 := Dρ.ofr (OFr.setVar ρ "tqY" Y) (by decide)
      have o1 : OFr τ τ1 clV := (oρ.trans (OFr.setVar ρ "tqY" Y)).mono (app_single_sub (by decide))
      have hOB1 : (τ1.arrs "OB").length = W + 1 := by rw [o1.len, hOB]
      obtain ⟨τ2, r2, E2, oil⟩ := iLoop_run (W := W) (KT := 1) (Ks := 10) (v := "tqi")
        (S := setD3 3 "tqY" "tqi") (T := .skip) (VT := []) (fun i => [3, Y, i]) (fun _ => false)
        (fun ρ' => OFr τ ρ' clV ∧ ρ'.vars "tqm" = m ∧ ρ'.vars "tqY" = Y) f (by decide) (by decide)
        D1 ⟨o1, by simp [τ1, hmρ], by simp [τ1]⟩
        (fun ρ ρ' ⟨oa, ma, ya⟩ ob => ⟨(oa.trans ob).mono (app_sub (by decide)),
          by rw [ob.vars "tqm" (by decide), ma], by rw [ob.vars "tqY" (by decide), ya]⟩)
        hd hB1 hv hℓ hW5 (Eρ.setVar (by decide) (by decide) Y) hOB1 (by simpa using hb)
        (fun i hi u hu => by simp at hu; rcases hu with rfl | rfl | rfl <;> [omega; exact hgW m; omega])
        (fun i => by simp [hf])
        (fun i hi ρ' _ ⟨_, _, yρ⟩ iρ => by
          obtain ⟨τ3, r3, c3, o3, a3⟩ := setD3_run (B := W + 1) (d := 3) (y1 := "tqY") (y2 := "tqi")
            (τ := ρ') (by decide) (by decide) (by omega) (by rw [yρ]; have := hgW m; omega)
            (by rw [iρ]; omega) (by omega)
          rw [yρ, iρ] at c3
          exact ⟨τ3, r3, c3, o3, a3⟩)
        (fun i _ => skip_tspec W _) (fun y h => absurd h (by simp))
      have o2 : OFr τ τ2 clV := (o1.trans oil).mono (app_sub (by decide))
      have m2 : τ2.vars "tqm" = m := by rw [oil.vars "tqm" (by decide)]; simp [τ1, hmρ]
      exact ⟨τ2, (Run.seq r1 r2).mono (by omega), m2, ⟨hD.ofr o2 hVa, o2⟩, E2⟩)
  refine ⟨σ', r.mono ?_, E', o'⟩
  simp only [Expr.size]
  nlinarith

end Lax185574Proofs.ResolveRam.Glue
