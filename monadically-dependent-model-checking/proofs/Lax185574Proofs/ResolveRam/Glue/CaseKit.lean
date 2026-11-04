import Lax185574Proofs.ResolveRam.Glue.CComp

/-!
Tools for the cases of a later round of the glue program of
lem:resolve-lift.

`tailIn_of`: the scalars that the end of a round needs (`TailIn`) from
the environment at the start of the case (`PreR`) and the facts that
the case establishes. `hsV_of`: the scalars of the new head from the
nine scalars of the instance and the eight scalars of the new position.
`bodyCall_ite_true`/`_false`: a case behind a test of the dispatcher.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam

/-- **The scalars for the end of a round.** -/
theorem tailIn_of {W R X k : ℕ} {sc wx b w : List ℕ} {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    {τ0 τ : Env} (P0 : PreR W R sc ws wx b τ0) (hX : sc.getD 1 0 = X) (hz : sc.getD 0 0 = 0)
    (hkq : kq0 < W) (hR : 1 ≤ R) (hlt : EnvLt (W + 1) τ) (har : ArrW W τ)
    (hfr : ∀ y ∈ ["W", "rR", "bl", "gX", "z0"], τ.vars y = τ0.vars y)
    (hy : τ.arrs "y" = τ0.arrs "y") (hlib : Lib L τ) (hov : τ.vars "ovf" = 0)
    (hkind : KindOK W L k w τ) (hqk : τ.vars "qk" = k) (hPR : PreAt "PR" (prW ps) τ)
    (hnp : τ.vars "np" = ps.length) (hps : ∀ p ∈ ps, p.1 + p.2 ≤ L.length) (hpsl : ps.length ≤ 12) :
    TailIn W R X L ps k w b τ := by
  have h0 : τ0.vars "z0" = sc.getD 0 0 := P0.hsc 0 (by omega)
  have h1 : τ0.vars "gX" = sc.getD 1 0 := P0.hsc 1 (by omega)
  refine ⟨?_, hkq, har, hlt, ?_, hR, hlib, ?_, ?_, ?_, ?_, hov, hkind, hqk, hPR, hnp, hps, hpsl⟩
  · rw [hfr "W" (by simp), P0.hW]
  · rw [hfr "rR" (by simp), P0.hrR]
  · rw [hfr "z0" (by simp), h0, hz]
  · rw [hfr "bl" (by simp), P0.hbl]
  · intro j hj; rw [hy]; exact P0.hy j hj
  · rw [hfr "gX" (by simp), h1, hX]

/-- **The scalars of the new head.** -/
theorem hsV_of {τ : Env} {sc : List ℕ} (hl : 9 ≤ sc.length)
    (g : ∀ j (h : j < 9), τ.vars (scR[j]'(by simp [scR]; omega)) = sc.getD j 0)
    {a1 a2 a3 a4 a5 a6 a7 a8 : ℕ} (h1 : τ.vars "Nph" = a1) (h2 : τ.vars "Nd" = a2)
    (h3 : τ.vars "Ni" = a3) (h4 : τ.vars "Nm" = a4) (h5 : τ.vars "NSG" = a5) (h6 : τ.vars "NFA" = a6)
    (h7 : τ.vars "NCO" = a7) (h8 : τ.vars "NLV" = a8) :
    hsV.map τ.vars = sc.take 9 ++ [a1, a2, a3, a4, a5, a6, a7, a8] := by
  match sc, hl with
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: r, _ =>
    have e0 := g 0 (by omega); have e1 := g 1 (by omega); have e2 := g 2 (by omega)
    have e3 := g 3 (by omega); have e4 := g 4 (by omega); have e5 := g 5 (by omega)
    have e6 := g 6 (by omega); have e7 := g 7 (by omega); have e8 := g 8 (by omega)
    simp only [scR, List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ,
      List.getD_cons_zero] at e0 e1 e2 e3 e4 e5 e6 e7 e8
    simp [hsV, e0, e1, e2, e3, e4, e5, e6, e7, e8, h1, h2, h3, h4, h5, h6, h7, h8]


/-- The size of the word of a library. -/
theorem ySz_toWord_le (ws : List (List ℕ)) :
    ySz (toWord ws) ≤ 2 * total ws + 2 * ws.length + maxEntry ws.flatten + 2 := by
  have hm1 : maxEntry (toWord ws) ≤ total ws + ws.length + maxEntry ws.flatten :=
    maxEntry_le fun v hv => mem_toWord_bound hv (by omega) (fun w hw x hx => by
      have := le_maxEntry (List.mem_flatten.2 ⟨w, hw, hx⟩); omega)
  have hl1 := length_toWord_words ws
  unfold ySz; omega

/-- **The room of a piece from a passed room check.** -/
theorem room_of_ok {W R R' S : ℕ} {τ : Env} {ws : List (List ℕ)} {b : List ℕ} (h : RoomOK W R τ ws b)
    (hR : R' + 1 ≤ R) (hS : S + 1 ≤ 5 * sOfV τ ws b) : Room W R' S := by
  set So := sOfV τ ws b
  unfold RoomOK at h
  unfold Room
  have hR1 : 1 ≤ R := by omega
  calc 2 ^ 16 * (R' + 1) ^ 2 * (S + 1) ^ 2 ≤ 2 ^ 16 * R ^ 2 * (5 * So) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hR 2)) (Nat.pow_le_pow_left hS 2)
    _ ≤ 2 ^ 24 * R * R * R * R * So * So := by
        have : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hR1 (by omega)
        have := Nat.mul_le_mul_right (So * So) (Nat.mul_le_mul_left (2 ^ 16 * 25) this)
        nlinarith
    _ ≤ W := h.le

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The scalars of a position from the nine scalars of the instance. -/
theorem scW_eq (c c' : Cur) :
    scW G P Q s k₀ q₀ c' = (scW G P Q s k₀ q₀ c).take 9 ++ (curW c' ++
      [(swAt G P Q s k₀ q₀ c').SG.length, (swAt G P Q s k₀ q₀ c').FA.length,
        (swAt G P Q s k₀ q₀ c').CO.length, (swAt G P Q s k₀ q₀ c').LV.length]) := by
  simp [scW]

/-! ### Cases behind a test -/

theorem bodyCall_ite_true {body c2 : Com} {b : Cond} {W R X Nt Nw KB k : ℕ} {sc wx bb w nsc : List ℕ}
    {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hb : ∀ τ, PreR W R sc ws wx bb τ → b.evalB (W + 1) τ = some true)
    (h : BodyCall body W R X sc ws wx bb L ps k w Nt Nw nsc KB) :
    BodyCall (.ite b body c2) W R X sc ws wx bb L ps k w Nt Nw nsc (1 + b.size + KB) := by
  intro τ P0 hov hkq
  obtain ⟨τ', kb, r, hkb, h1, h2⟩ := h τ P0 hov hkq
  exact ⟨τ', _, Run.ite_true (hb τ P0) r, by omega, h1, h2⟩

theorem bodyCall_ite_false {body c1 : Com} {b : Cond} {W R X Nt Nw KB k : ℕ} {sc wx bb w nsc : List ℕ}
    {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hb : ∀ τ, PreR W R sc ws wx bb τ → b.evalB (W + 1) τ = some false)
    (h : BodyCall body W R X sc ws wx bb L ps k w Nt Nw nsc KB) :
    BodyCall (.ite b c1 body) W R X sc ws wx bb L ps k w Nt Nw nsc (1 + b.size + KB) := by
  intro τ P0 hov hkq
  obtain ⟨τ', kb, r, hkb, h1, h2⟩ := h τ P0 hov hkq
  exact ⟨τ', _, Run.ite_false (hb τ P0) r, by omega, h1, h2⟩

theorem bodyCall_mono {body : Com} {W R X Nt Nw KB KB' k : ℕ} {sc wx bb w nsc : List ℕ}
    {ws L : List (List ℕ)} {ps : List (ℕ × ℕ)} (h : BodyCall body W R X sc ws wx bb L ps k w Nt Nw nsc KB)
    (hK : KB ≤ KB') : BodyCall body W R X sc ws wx bb L ps k w Nt Nw nsc KB' := by
  intro τ P0 hov hkq
  obtain ⟨τ', kb, r, hkb, h1, h2⟩ := h τ P0 hov hkq
  exact ⟨τ', kb, r, by omega, h1, h2⟩

/-- A scalar of the state in a test of the dispatcher. -/
theorem preR_var {W R : ℕ} {sc wx bb : List ℕ} {ws : List (List ℕ)} {τ : Env}
    (P0 : PreR W R sc ws wx bb τ) (j : ℕ) (hj : j < 17) :
    (Expr.var (scR[j]'(by simp [scR]; omega))).evalB (W + 1) τ = some (sc.getD j 0) :=
  ev_var (P0.hsc j hj) (by rw [← P0.hsc j hj]; exact P0.hlt.vars _)

end Lax185574Proofs.ResolveRam.Glue
