import Lax185574Proofs.ResolveRam.Glue.PAt5

/-!
The loop over the candidates `[4, s, i, j]` of the atom words of
lem:resolve-lift: the radii `s ≤ rhoMinus k q` in `tRm`, then the pairs
of positions, with the extra test `hopT` (`dLoop_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- The loop over the candidates `[4, s, i, j]`. -/
def dLoop : Com :=
  forUp "tqs" (.add (.var "tRm") (.lit 1))
    (forUp "tqi" (.var "tL") (iLoop "tqj" (setD4 4 "tqs" "tqi" "tqj") hopT))

/-- The scalars that `dLoop` writes. -/
def dlV : List String := ["tqs", "tqi"] ++ ilV "tqj" hoV

/-- The extra test of a distance bound, as a `TSpec`. -/
theorem hopT_tspec {W : ℕ} {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW}
    {ℓ nc cb Rm Rp : ℕ} {K : Env → Prop} {s i j : ℕ} (hd : Xa.drop p₁ = toWord A ++ rr)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1)
    (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hiW : i ≤ W) (hjW : j ≤ W) (hs : s ≤ Rm) (hRW : 2 * Rm + 4 ≤ W) :
    TSpec W hopT (hopK (A.length + A.length) Rm + 10) hoV
      (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ K ρ ∧ TdAt [4, s, i, j] ρ) (hopW Dw A s i j) := by
  rintro τ1 ⟨D1, -, t1⟩ -
  obtain ⟨-, -, -, h1, h2, h3⟩ := t1
  change τ1.vars "td1" = s at h1
  change τ1.vars "td2" = i at h2
  change τ1.vars "td3" = j at h3
  obtain ⟨τ2, r2, f2, o2, a2⟩ := hopT_run (W := W) D1.a hd D1.p1 D1.p2 D1.P D1.Q D1.cP D1.cQ h1 h2 h3
    hPW hQW hiW hjW (by omega) hB1 hv
  exact ⟨τ2, r2.mono (by have := hopK_mono_s (L := A.length + A.length) hs; omega), f2, o2, a2⟩

set_option maxRecDepth 10000 in
theorem hoV_ok : ∀ y ∈ hoV, y ∉ tdN ∧ y ≠ "po" ∧ y ≠ "fc" ∧ y ∉ aN ∧ y ∉ qV := by decide

theorem notMem_hoV {y : String} (h : y ∈ qV) : y ∉ hoV := fun h' => (hoV_ok y h').2.2.2.2 h

/-- **The candidates `[4, s, i, j]`.** -/
theorem dLoop_run {W : ℕ} {Xa rr : List ℕ} {A : List (List ℕ)} {p₁ : ℕ} {Dw : DW} {ℓ nc cb Rm Rp : ℕ}
    {pre : List ℕ} {L : List (List ℕ)} {τ : Env} (f : List ℕ → Bool)
    (hD : AtD Xa p₁ Dw ℓ nc cb Rm Rp τ) (hd : Xa.drop p₁ = toWord A ++ rr)
    (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) (hℓ : ℓ ≤ W)
    (hW5 : 5 ≤ W) (hE : Em pre L τ) (hOB : (τ.arrs "OB").length = W + 1)
    (hB : pre.length + 1 + (frames (L ++ (dB Rm ℓ).filter f)).length ≤ W)
    (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hRW : 2 * Rm + 4 ≤ W)
    (hf : ∀ s i j, f [4, s, i, j] = (inW A [4, s, i, j] || hopW Dw A s i j)) :
    ∃ τ', Run (W + 1) dLoop τ τ' ((Rm + 1) * (ℓ * (ℓ * (70 * A.length + hopK (A.length + A.length) Rm +
        148) + 14) + 16) + 8) ∧
      Em pre (L ++ (dB Rm ℓ).filter f) τ' ∧ OFr τ τ' dlV := by
  set KT := hopK (A.length + A.length) Rm + 10
  have hdf : (dB Rm ℓ).filter f = (List.range (Rm + 1)).flatMap fun s => (List.range ℓ).flatMap fun i =>
      (List.range ℓ).flatMap fun j => [[4, s, i, j]].filter f := by
    simp [dB, List.filter_flatMap]
  have hVa : ∀ y ∈ aN, y ∉ dlV := fun y hy => notMem_append (by revert hy; revert y; decide)
    (aN_ilV (by decide) (fun y h => (hoV_ok y h).2.2.2.1) y hy)
  have hil : ilV "tqj" hoV ⊆ dlV := fun y h => List.mem_append_right _ h
  have nil : ∀ y ∈ ["tqs", "tqi"], y ∉ ilV "tqj" hoV := by
    intro y hy
    exact notMem_ilV (by revert hy; revert y; decide) (by revert hy; revert y; decide)
      (by revert hy; revert y; decide) (notMem_hoV (by revert hy; revert y; decide))
      (by revert hy; revert y; decide)
  rw [hdf] at hB ⊢
  obtain ⟨σ', r, ⟨-, o'⟩, E'⟩ := emLoop_run (W := W) (N := Rm + 1)
    (K := ℓ * (ℓ * (10 + 70 * A.length + KT + 128) + 6 + (Expr.var "tL").size + 7) + (Expr.var "tL").size + 5)
    (v := "tqs")
    (e := .add (.var "tRm") (.lit 1))
    (body := forUp "tqi" (.var "tL") (iLoop "tqj" (setD4 4 "tqs" "tqi" "tqj") hopT))
    (fun s => (List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j => [[4, s, i, j]].filter f)
    (fun ρ => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ ∧ OFr τ ρ dlV) (σ := τ) (by decide) (by decide)
    (by omega) (fun ρ hρ => ev_add (ev_var hρ.1.Rm (by omega)) (evalB_lit (by omega)) (by omega))
    (fun ρ x hρ => ⟨hρ.1.ofr (OFr.setVar ρ "tqs" x) (by decide),
      (hρ.2.trans (OFr.setVar ρ "tqs" x)).mono (app_single_sub (by decide))⟩)
    ⟨hD, (OFr.refl τ).mono (by simp)⟩ hE hB
    (by
      rintro s hs L' ρ ⟨Dρ, oρ⟩ hsρ Eρ hb
      obtain ⟨σ2, r2, ⟨D2, o2, s2⟩, E2⟩ := emLoop_run (W := W) (N := ℓ)
        (K := ℓ * (10 + 70 * A.length + KT + 128) + 6) (v := "tqi") (e := .var "tL")
        (body := iLoop "tqj" (setD4 4 "tqs" "tqi" "tqj") hopT)
        (fun i => (List.range ℓ).flatMap fun j => [[4, s, i, j]].filter f)
        (fun ρ' => AtD Xa p₁ Dw ℓ nc cb Rm Rp ρ' ∧ OFr τ ρ' dlV ∧ ρ'.vars "tqs" = s) (σ := ρ)
        (by decide) (by decide) (by omega) (fun ρ' hρ' => ev_var hρ'.1.L (by omega))
        (fun ρ' x hρ' => ⟨hρ'.1.ofr (OFr.setVar ρ' "tqi" x) (by decide),
          (hρ'.2.1.trans (OFr.setVar ρ' "tqi" x)).mono (app_single_sub (by decide)), by simp [hρ'.2.2]⟩)
        ⟨Dρ, oρ, hsρ⟩ Eρ hb
        (by
          rintro i hi L'' ρ' ⟨Dρ', oρ', sρ'⟩ hiρ' Eρ' hb'
          have hOB' : (ρ'.arrs "OB").length = W + 1 := by rw [oρ'.len, hOB]
          obtain ⟨τ3, r3, E3, o3⟩ := iLoop_run (W := W) (KT := KT) (Ks := 10) (v := "tqj")
            (S := setD4 4 "tqs" "tqi" "tqj") (T := hopT) (VT := hoV) (fun j => [4, s, i, j])
            (fun j => hopW Dw A s i j)
            (fun ρ'' => OFr τ ρ'' dlV ∧ ρ''.vars "tqs" = s ∧ ρ''.vars "tqi" = i) f (by decide) (by decide)
            Dρ' ⟨oρ', sρ', hiρ'⟩
            (fun ρa ρb ⟨oa, sa, ia⟩ ob => ⟨(oa.trans ob).mono (app_sub hil),
              by rw [ob.vars "tqs" (nil _ (by simp)), sa], by rw [ob.vars "tqi" (nil _ (by simp)), ia]⟩)
            hd hB1 hv hℓ hW5 Eρ' hOB' hb'
            (fun j hj u hu => by simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> omega)
            (fun j => hf s i j)
            (fun j hj ρa _ ⟨_, sa, ia⟩ ja => by
              obtain ⟨τ4, r4, c4, o4, a4⟩ := setD4_run (B := W + 1) (d := 4) (y1 := "tqs") (y2 := "tqi")
                (y3 := "tqj") (τ := ρa) (by decide) (by decide) (by decide) (by omega)
                (by rw [sa]; omega) (by rw [ia]; omega) (by rw [ja]; omega) (by omega)
              rw [sa, ia, ja] at c4
              exact ⟨τ4, r4, c4, o4, a4⟩)
            (fun j hj => hopT_tspec hd hB1 hv hPW hQW (by omega) (by omega) (by omega) hRW)
            (fun y h => have k := hoV_ok y h
              ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, fun e => k.2.2.2.2 (by rw [e]; simp [qV])⟩)
          have o4 : OFr τ τ3 dlV := (oρ'.trans o3).mono (app_sub hil)
          exact ⟨τ3, r3, by rw [o3.vars "tqi" (nil _ (by simp)), hiρ'],
            ⟨hD.ofr o4 hVa, o4, by rw [o3.vars "tqs" (nil _ (by simp)), sρ']⟩, E3⟩)
      exact ⟨σ2, r2, by rw [s2], ⟨D2, o2⟩, by simpa using E2⟩)
  refine ⟨σ', r.mono ?_, by simpa using E', o'⟩
  simp only [Expr.size, KT]
  nlinarith

end Lax185574Proofs.ResolveRam.Glue
