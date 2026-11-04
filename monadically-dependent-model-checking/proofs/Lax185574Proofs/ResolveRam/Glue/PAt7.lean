import Lax185574Proofs.ResolveRam.Glue.PAt6

/-!
The loop over the candidates `[5, s, Y, i]` of the atom words of
lem:resolve-lift: the radii `s ≤ rhoPlus k q` in `tRp`, the colors `Y`
of the table with their two entries in `tx` and `tz`, and the positions,
with the extra test `uT` (`eLoop_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- Load the entry `k` of the triple `tqm` of the color table into `x`. -/
def ldC (x : String) (k : ℕ) : Com :=
  .assign x (.get "a" (.add (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3))) (.lit k)))

/-- The loop over the candidates `[5, s, Y, i]`. -/
def eLoop : Com :=
  forUp "tqs" (.add (.var "tRp") (.lit 1)) (forUp "tqm" (.var "tnc")
    (.seq (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
      (.seq (ldC "tx" 1) (.seq (ldC "tz" 2) (iLoop "tqi" (setD4 5 "tqs" "tqY" "tqi") uT)))))

/-- The scalars that `eLoop` writes. -/
def elV : List String := ["tqs", "tqm", "tqY", "tx", "tz"] ++ ilV "tqi" uV

set_option maxRecDepth 10000 in
theorem uV_ok : ∀ y ∈ uV, y ∉ tdN ∧ y ≠ "po" ∧ y ≠ "fc" ∧ y ∉ aN ∧ y ∉ qV := by decide

theorem notMem_uV {y : String} (h : y ∈ qV) : y ∉ uV := fun h' => (uV_ok y h').2.2.2.2 h

/-- The extra test of `[5, s, Y, i]`, as a `TSpec`. -/
theorem uT_tspec {W : ℕ} {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW}
    {ℓ nc cb Rm Rp : ℕ} {K : Env → Prop} {s Y i : ℕ} (hd : Xa.drop p₁ = toWord A ++ rr)
    (hK : ∀ ρ, K ρ → ρ.vars "tx" = Dw.tP Y ∧ ρ.vars "tz" = Dw.tQ Y)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1)
    (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hiW : i ≤ W) (hxW : Dw.tP Y ≤ W) (hzW : Dw.tQ Y ≤ W)
    (hs : s ≤ Rp) (hRW : 2 * Rp + 4 ≤ W) :
    TSpec W uT (hopK (A.length + A.length) Rp + 20) uV
      (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ K ρ ∧ TdAt [5, s, Y, i] ρ)
      (decide (1 ≤ s) && uHopW Dw A (s - 1) Y i) := by
  rintro τ1 ⟨D1, K1, t1⟩ hF
  obtain ⟨-, -, -, h1, -, h3⟩ := t1
  change τ1.vars "td1" = s at h1
  change τ1.vars "td3" = i at h3
  obtain ⟨hx, hz⟩ := hK τ1 K1
  obtain ⟨τ2, r2, f2, o2, a2⟩ := uT_run (W := W) D1.a hd D1.p1 D1.P D1.Q D1.cP D1.cQ h1 h3 hx hz hF
    hPW hQW hiW (by omega) hxW hzW hB1 hv
  exact ⟨τ2, r2.mono (by have := hopK_mono_s (L := A.length + A.length) hs; omega), f2, o2, a2⟩

/-- **The candidates `[5, s, Y, i]`.** -/
theorem eLoop_run {W : ℕ} {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {ℓ cb Rm Rp : ℕ}
    {cs pre : List ℕ} {L : List (List ℕ)} {τ : Env} (f : List ℕ → Bool)
    (hD : AtD Xa p₁ Dw ℓ cs.length cb Rm Rp τ) (hd : Xa.drop p₁ = toWord A ++ rr)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) (hℓ : ℓ ≤ W)
    (hW5 : 5 ≤ W) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ (eB Rp cs ℓ).filter f)).length ≤ W)
    (hcol : ∀ m < cs.length, Xa[cb + m * 3]? = some (cs.getD m 0) ∧
      Xa[cb + m * 3 + 1]? = some (Dw.tP (cs.getD m 0)) ∧ Xa[cb + m * 3 + 2]? = some (Dw.tQ (cs.getD m 0)))
    (hcsW : ∀ m, cs.getD m 0 ≤ W ∧ Dw.tP (cs.getD m 0) ≤ W ∧ Dw.tQ (cs.getD m 0) ≤ W)
    (hcb : cb + 3 * cs.length ≤ W) (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hRW : 2 * Rp + 4 ≤ W)
    (hf : ∀ s Y i, f [5, s, Y, i] = (inW A [5, s, Y, i] || (decide (1 ≤ s) && uHopW Dw A (s - 1) Y i))) :
    ∃ τ', Run (W + 1) eLoop τ τ' ((Rp + 1) * (cs.length * (ℓ * (70 * A.length +
        hopK (A.length + A.length) Rp + 158) + 40) + 16) + 8) ∧
      Em pre (L ++ (eB Rp cs ℓ).filter f) τ' ∧ OFr τ τ' elV := by
  set KT := hopK (A.length + A.length) Rp + 20
  have hef : (eB Rp cs ℓ).filter f = (List.range (Rp + 1)).flatMap fun s =>
      (List.range cs.length).flatMap fun m => (List.range ℓ).flatMap fun i =>
        [[5, s, cs.getD m 0, i]].filter f := by
    simp [eB, List.filter_flatMap]
  have hVa : ∀ y ∈ aN, y ∉ elV := fun y hy => notMem_append (by revert hy; revert y; decide)
    (aN_ilV (by decide) (fun y h => (uV_ok y h).2.2.2.1) y hy)
  have hil : ilV "tqi" uV ⊆ elV := fun y h => List.mem_append_right _ h
  have nil : ∀ y ∈ ["tqs", "tqm", "tqY", "tx", "tz"], y ∉ ilV "tqi" uV := by
    intro y hy
    exact notMem_ilV (by revert hy; revert y; decide) (by revert hy; revert y; decide)
      (by revert hy; revert y; decide) (notMem_uV (by revert hy; revert y; decide))
      (by revert hy; revert y; decide)
  rw [hef] at hB ⊢
  obtain ⟨σ', r, ⟨-, o'⟩, E'⟩ := emLoop_run (W := W) (N := Rp + 1)
    (K := cs.length * (7 + (9 + (9 + (ℓ * (10 + 70 * A.length + KT + 128) + 6))) + (Expr.var "tnc").size + 7) +
      (Expr.var "tnc").size + 5)
    (v := "tqs") (e := .add (.var "tRp") (.lit 1))
    (body := forUp "tqm" (.var "tnc")
      (.seq (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
        (.seq (ldC "tx" 1) (.seq (ldC "tz" 2) (iLoop "tqi" (setD4 5 "tqs" "tqY" "tqi") uT)))))
    (fun s => (List.range cs.length).flatMap fun m => (List.range ℓ).flatMap fun i =>
      [[5, s, cs.getD m 0, i]].filter f)
    (fun ρ => AtD Xa p₁ Dw ℓ cs.length cb Rm Rp ρ ∧ OFr τ ρ elV) (σ := τ) (by decide) (by decide)
    (by omega) (fun ρ hρ => ev_add (ev_var hρ.1.Rp (by omega)) (evalB_lit (by omega)) (by omega))
    (fun ρ x hρ => ⟨hρ.1.ofr (OFr.setVar ρ "tqs" x) (by decide),
      (hρ.2.trans (OFr.setVar ρ "tqs" x)).mono (app_single_sub (by simp [elV]))⟩)
    ⟨hD, (OFr.refl τ).mono (by simp)⟩ hE hB
    (by
      rintro s hs L' ρ ⟨Dρ, oρ⟩ hsρ Eρ hb
      obtain ⟨σ2, r2, ⟨D2, o2, s2⟩, E2⟩ := emLoop_run (W := W) (N := cs.length)
        (K := 7 + (9 + (9 + (ℓ * (10 + 70 * A.length + KT + 128) + 6)))) (v := "tqm") (e := .var "tnc")
        (body := .seq (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
          (.seq (ldC "tx" 1) (.seq (ldC "tz" 2) (iLoop "tqi" (setD4 5 "tqs" "tqY" "tqi") uT))))
        (fun m => (List.range ℓ).flatMap fun i => [[5, s, cs.getD m 0, i]].filter f)
        (fun ρ' => AtD Xa p₁ Dw ℓ cs.length cb Rm Rp ρ' ∧ OFr τ ρ' elV ∧ ρ'.vars "tqs" = s) (σ := ρ)
        (by decide) (by decide) (by omega) (fun ρ' hρ' => ev_var hρ'.1.nc (by omega))
        (fun ρ' x hρ' => ⟨hρ'.1.ofr (OFr.setVar ρ' "tqm" x) (by decide),
          (hρ'.2.1.trans (OFr.setVar ρ' "tqm" x)).mono (app_single_sub (by simp [elV])),
          by simp [hρ'.2.2]⟩)
        ⟨Dρ, oρ, hsρ⟩ Eρ hb
        (by
          rintro m hm L'' ρ' ⟨Dρ', oρ', sρ'⟩ hmρ' Eρ' hb'
          obtain ⟨c0, c1, c2⟩ := hcol m hm
          obtain ⟨bY, bx, bz⟩ := hcsW m
          set Y := cs.getD m 0
          have ea : ∀ ρa : Env, AtD Xa p₁ Dw ℓ cs.length cb Rm Rp ρa → ρa.vars "tqm" = m →
              (Expr.add (.var "tcb0") (.mul (.var "tqm") (.lit 3))).evalB (W + 1) ρa = some (cb + m * 3) :=
            fun ρa Da ma => ev_add (ev_var Da.cb (by omega)) (evalB_bin (ev_var ma (by omega))
              (evalB_lit (n := 3) (by omega)) (by simp only [Bop.apply]; omega)) (by omega)
          set τ1 := ρ'.setVar "tqY" Y
          have r1 : Run (W + 1) (.assign "tqY" (.get "a" (.add (.var "tcb0") (.mul (.var "tqm") (.lit 3)))))
              ρ' τ1 7 :=
            (Run.assign (evalB_get (ea ρ' Dρ' hmρ') (by rw [Dρ'.a]; exact c0) (by omega))).mono
              (by simp [Expr.size])
          have D1 : AtD Xa p₁ Dw ℓ cs.length cb Rm Rp τ1 := Dρ'.ofr (OFr.setVar ρ' "tqY" Y) (by decide)
          set τ2 := τ1.setVar "tx" (Dw.tP Y)
          have r2 : Run (W + 1) (ldC "tx" 1) τ1 τ2 9 :=
            (Run.assign (evalB_get (ev_add (ea τ1 D1 (by simpa [τ1] using hmρ')) (evalB_lit (n := 1) (by omega))
              (by omega)) (by rw [D1.a]; exact c1) (by omega))).mono (by simp [Expr.size])
          have D2 : AtD Xa p₁ Dw ℓ cs.length cb Rm Rp τ2 := D1.ofr (OFr.setVar τ1 "tx" _) (by decide)
          set τ3 := τ2.setVar "tz" (Dw.tQ Y)
          have r3 : Run (W + 1) (ldC "tz" 2) τ2 τ3 9 :=
            (Run.assign (evalB_get (ev_add (ea τ2 D2 (by simpa [τ2, τ1] using hmρ')) (evalB_lit (n := 2) (by omega))
              (by omega)) (by rw [D2.a]; exact c2) (by omega))).mono (by simp [Expr.size])
          have D3 : AtD Xa p₁ Dw ℓ cs.length cb Rm Rp τ3 := D2.ofr (OFr.setVar τ2 "tz" _) (by decide)
          have o3 : OFr τ τ3 elV := ((((oρ'.trans (OFr.setVar ρ' "tqY" Y)).trans (OFr.setVar τ1 "tx" _)).trans
            (OFr.setVar τ2 "tz" _)).mono (by
              intro y hy; simp only [List.mem_append, List.mem_singleton] at hy
              rcases hy with ((h | rfl) | rfl) | rfl
              · exact h
              all_goals simp [elV]))
          have hOB3 : (τ3.arrs "OB").length = W + 1 := by rw [o3.len, hOB]
          have E3 : Em pre L'' τ3 := ((Eρ'.setVar (by decide) (by decide) _).setVar (by decide) (by decide) _).setVar
            (by decide) (by decide) _
          obtain ⟨τ4, r4, E4, o4⟩ := iLoop_run (W := W) (KT := KT) (Ks := 10) (v := "tqi")
            (S := setD4 5 "tqs" "tqY" "tqi") (T := uT) (VT := uV) (fun i => [5, s, Y, i])
            (fun i => decide (1 ≤ s) && uHopW Dw A (s - 1) Y i)
            (fun ρ'' => OFr τ ρ'' elV ∧ ρ''.vars "tqs" = s ∧ ρ''.vars "tqm" = m ∧ ρ''.vars "tqY" = Y ∧
              ρ''.vars "tx" = Dw.tP Y ∧ ρ''.vars "tz" = Dw.tQ Y) f (by decide) (by decide)
            D3 ⟨o3, by simp [τ3, τ2, τ1, sρ'], by simp [τ3, τ2, τ1, hmρ'], by simp [τ3, τ2, τ1],
              by simp [τ3, τ2], by simp [τ3]⟩
            (fun ρa ρb ⟨oa, sa, ma, ya, xa, za⟩ ob => ⟨(oa.trans ob).mono (app_sub hil),
              by rw [ob.vars "tqs" (nil _ (by simp)), sa], by rw [ob.vars "tqm" (nil _ (by simp)), ma],
              by rw [ob.vars "tqY" (nil _ (by simp)), ya], by rw [ob.vars "tx" (nil _ (by simp)), xa],
              by rw [ob.vars "tz" (nil _ (by simp)), za]⟩)
            hd hB1 hv hℓ hW5 E3 hOB3 (by simpa using hb')
            (fun i hi u hu => by simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> omega)
            (fun i => hf s Y i)
            (fun i hi ρa _ ⟨_, sa, _, ya, _, _⟩ ia => by
              obtain ⟨τ5, r5, c5, o5, a5⟩ := setD4_run (B := W + 1) (d := 5) (y1 := "tqs") (y2 := "tqY")
                (y3 := "tqi") (τ := ρa) (by decide) (by decide) (by decide) (by omega)
                (by rw [sa]; omega) (by rw [ya]; omega) (by rw [ia]; omega) (by omega)
              rw [sa, ya, ia] at c5
              exact ⟨τ5, r5, c5, o5, a5⟩)
            (fun i hi => uT_tspec hd (fun ρ hρ => ⟨hρ.2.2.2.2.1, hρ.2.2.2.2.2⟩) hB1 hv hPW hQW (by omega)
              bx bz (by omega) hRW)
            (fun y h => have k := uV_ok y h
              ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, fun e => k.2.2.2.2 (by rw [e]; simp [qV])⟩)
          have o5 : OFr τ τ4 elV := (o3.trans o4).mono (app_sub hil)
          refine ⟨τ4, (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono le_rfl,
            by rw [o4.vars "tqm" (nil _ (by simp))]; simp [τ3, τ2, τ1, hmρ'],
            ⟨hD.ofr o5 hVa, o5, by rw [o4.vars "tqs" (nil _ (by simp))]; simp [τ3, τ2, τ1, sρ']⟩, E4⟩)
      exact ⟨σ2, r2, by rw [s2], ⟨D2, o2⟩, by simpa using E2⟩)
  refine ⟨σ', r.mono ?_, by simpa using E', o'⟩
  simp only [Expr.size, KT]
  nlinarith

end Lax185574Proofs.ResolveRam.Glue
