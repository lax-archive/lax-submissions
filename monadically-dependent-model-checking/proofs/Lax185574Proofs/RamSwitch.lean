import Lax185574Proofs.RamCapped

/-!
Three callees in one program.

The loop driver has a single callee. The model-checking program calls
three opaque programs `A`, `B` and `C` (merge lift, resolve lift and
evaluation), so its callee runs all three, each on its own query, and
returns the three outputs one after the other. A caller that needs only
one of them gives the others small fixed queries.

The query is `[a, b, c] ++ qA ++ qB ++ qC` with `a = |qA|`, `b = |qB|`
and `c = |qC|`. The program is `pipe A' (pipe B' (pipe C' (catProg 2)))`
with `X' = capped X D`. The rewrites pass the queries not yet answered
and the outputs already computed from stage to stage, and the last
stage copies `y ++ z ++ u`. Since every output is capped, a halting run
has a short output with small entries, whatever the callees do, and the
stages after a callee stay faithful.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim Lax185574Proofs.RamCat
open Lax808846Proofs.Machine Lax185574Proofs.RamExec

/-- `x ↦ qA`. -/
def swR₁ : Rewrite 1 := [.slice 0 (.lit 3) (some (.entry 0 0))]
/-- `![y, x] ↦ [b, c] ++ qB ++ qC ++ y`. -/
def swR₁' : Rewrite 2 :=
  [.expr (.entry 1 1), .expr (.entry 1 2), .slice 1 (.add (.lit 3) (.entry 1 0)) none,
    .slice 0 (.lit 0) none]
/-- `[b, c] ++ qB ++ … ↦ qB`. -/
def swR₂ : Rewrite 1 := [.slice 0 (.lit 2) (some (.entry 0 0))]
/-- `![z, x₁] ↦ [c] ++ qC ++ y ++ z`. -/
def swR₂' : Rewrite 2 :=
  [.expr (.entry 1 1), .slice 1 (.add (.lit 2) (.entry 1 0)) none, .slice 0 (.lit 0) none]
/-- `[c] ++ qC ++ … ↦ qC`. -/
def swR₃ : Rewrite 1 := [.slice 0 (.lit 1) (some (.entry 0 0))]
/-- `![u, x₂] ↦ y ++ z ++ u`. -/
def swR₃' : Rewrite 2 := [.slice 1 (.add (.lit 1) (.entry 1 0)) none, .slice 0 (.lit 0) none]

section
variable (qA qB qC y z u : List ℕ)

/-- The query. -/
def swIn : List ℕ := [qA.length, qB.length, qC.length] ++ qA ++ qB ++ qC
/-- The input of the second stage. -/
def swX₁ : List ℕ := [qB.length, qC.length] ++ qB ++ qC ++ y
/-- The input of the third stage. -/
def swX₂ : List ℕ := [qC.length] ++ qC ++ y ++ z

theorem swR₁_apply : swR₁.apply (fun _ => swIn qA qB qC) = qA := by
  simp [swR₁, swIn, Rewrite.apply, Segment.apply, HExpr.eval]

theorem drop3 (a b c : ℕ) (l r : List ℕ) : List.drop (3 + l.length) (a :: b :: c :: (l ++ r)) = r := by
  rw [Nat.add_comm]; exact List.drop_left

theorem drop2 (a b : ℕ) (l r : List ℕ) : List.drop (2 + l.length) (a :: b :: (l ++ r)) = r := by
  rw [Nat.add_comm]; exact List.drop_left

theorem drop1 (a : ℕ) (l r : List ℕ) : List.drop (1 + l.length) (a :: (l ++ r)) = r := by
  rw [Nat.add_comm]; exact List.drop_left

theorem swR₁'_apply : swR₁'.apply ![y, swIn qA qB qC] = swX₁ qB qC y := by
  simp [swR₁', swIn, swX₁, Rewrite.apply, Segment.apply, HExpr.eval, drop3]

theorem swR₂_apply : swR₂.apply (fun _ => swX₁ qB qC y) = qB := by
  simp [swR₂, swX₁, Rewrite.apply, Segment.apply, HExpr.eval]

theorem swR₂'_apply : swR₂'.apply ![z, swX₁ qB qC y] = swX₂ qC y z := by
  simp [swR₂', swX₁, swX₂, Rewrite.apply, Segment.apply, HExpr.eval, drop2]

theorem swR₃_apply : swR₃.apply (fun _ => swX₂ qC y z) = qC := by
  simp [swR₃, swX₂, Rewrite.apply, Segment.apply, HExpr.eval]

theorem swR₃'_apply : swR₃'.apply ![u, swX₂ qC y z] = y ++ z ++ u := by
  simp [swR₃', swX₂, Rewrite.apply, Segment.apply, HExpr.eval, drop1]

end

theorem swR_cost₁ (xs : Fin 1 → List ℕ) : swR₁.cost xs ≤ 8 ∧ swR₂.cost xs ≤ 8 ∧ swR₃.cost xs ≤ 8 := by
  simp [swR₁, swR₂, swR₃, Rewrite.cost, Segment.cost, HExpr.cost]

theorem swR_cost₂ (xs : Fin 2 → List ℕ) :
    swR₁'.cost xs ≤ 16 ∧ swR₂'.cost xs ≤ 16 ∧ swR₃'.cost xs ≤ 16 := by
  simp [swR₁', swR₂', swR₃', Rewrite.cost, Segment.cost, HExpr.cost]

theorem catLim_lt_pow {v E : ℕ} (h : E ≤ v) : catLim v E < 2 ^ (v - E) := by
  have hv : 2 ^ v = 2 ^ E * 2 ^ (v - E) := by rw [← pow_add]; congr 1; omega
  simp only [catLim]
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  have : 1 ≤ 2 ^ v := Nat.one_le_two_pow
  calc 2 ^ v - 1 < 2 ^ v := by omega
    _ = 2 ^ (v - E) * 2 ^ E := by rw [hv, Nat.mul_comm]

theorem pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- **Three callees.** -/
theorem switch (A B C : Program) (D : ℕ) (hD : 4 ≤ D) : ∃ (p : Program) (K : ℕ),
    ∀ (w : ℕ) (qA qB qC : List ℕ), K ≤ 2 ^ (w - 8 - D) →
      (swIn qA qB qC).length < 2 ^ (w - 10 - D) → D + 14 ≤ w →
      (∀ y z u tA tB tC, RunsTo (w - 4 - D) A qA y tA → RunsTo (w - 6 - D) B qB z tB →
        RunsTo (w - 8 - D) C qC u tC → y.length ≤ catLim (w - 4) (D + 2) →
        z.length ≤ catLim (w - 6) (D + 2) → u.length ≤ catLim (w - 8) (D + 2) →
        ∃ t ≤ K * (tA + tB + tC + y.length + z.length + u.length + 1),
          RunsTo w p (swIn qA qB qC) (y ++ z ++ u) t) ∧
      (∀ o T, RunsTo w p (swIn qA qB qC) o T →
        ∃ y z u tA tB tC, RunsTo (w - 4 - D) A qA y tA ∧ RunsTo (w - 6 - D) B qB z tB ∧
          RunsTo (w - 8 - D) C qC u tC ∧ o = y ++ z ++ u ∧
          y.length ≤ catLim (w - 4) (D + 2) ∧ z.length ≤ catLim (w - 6) (D + 2) ∧
          u.length ≤ catLim (w - 8) (D + 2)) := by
  obtain ⟨pA, KA, hA⟩ := capped A D
  obtain ⟨pB, KB, hB⟩ := capped B D
  obtain ⟨pC, KC, hC⟩ := capped C D
  obtain ⟨p₃, K₃, h₃⟩ := pipe_sound pC (catProg 2) swR₃ swR₃'
  obtain ⟨p₂, K₂, h₂⟩ := pipe_sound pB p₃ swR₂ swR₂'
  obtain ⟨p, K₁, h₁⟩ := pipe_sound pA p₂ swR₁ swR₁'
  set Kt := K₁ * (KA + K₂ * (KB + K₃ * (KC + 31) + 24) + 24) with hKt
  refine ⟨p, Kt + K₁ + K₂ + K₃ + KA + KB + KC + 1, fun w qA qB qC hK hx hw => ?_⟩
  -- word lengths
  have p8 : 2 ^ (w - 8 - D) ≤ 2 ^ (w - 6) := pow_mono (by omega)
  have p6 : 2 ^ (w - 6) ≤ 2 ^ (w - 4) := pow_mono (by omega)
  have p4 : 2 ^ (w - 4) ≤ 2 ^ (w - 2) := pow_mono (by omega)
  have p2 : 2 ^ (w - 2) ≤ 2 ^ w := pow_mono (by omega)
  have q10 : 2 ^ (w - 10 - D) ≤ 2 ^ (w - 8 - D) := pow_mono (by omega)
  have q8 : 2 ^ (w - 8 - D) ≤ 2 ^ (w - 6 - D) := pow_mono (by omega)
  have q6 : 2 ^ (w - 6 - D) ≤ 2 ^ (w - 4 - D) := pow_mono (by omega)
  have q4 : 2 ^ (w - 4 - D) ≤ 2 ^ (w - 6) := pow_mono (by omega)
  have q6' : 2 ^ (w - 6 - D) ≤ 2 ^ (w - 10) := pow_mono (by omega)
  have r16 : 2 ^ (w - 6) = 16 * 2 ^ (w - 10) := by
    rw [show w - 6 = 4 + (w - 10) by omega, pow_add]; norm_num
  have cy := catLim_lt_pow (v := w - 4) (E := D + 2) (by omega)
  have cz := catLim_lt_pow (v := w - 6) (E := D + 2) (by omega)
  have cu := catLim_lt_pow (v := w - 8) (E := D + 2) (by omega)
  rw [show w - 4 - (D + 2) = w - 6 - D by omega] at cy
  rw [show w - 6 - (D + 2) = w - 8 - D by omega] at cz
  rw [show w - 8 - (D + 2) = w - 10 - D by omega] at cu
  have hKA : KA ≤ 2 ^ (w - 2 - 2 - D) := by rw [show w - 2 - 2 - D = w - 4 - D by omega]; omega
  have hKB : KB ≤ 2 ^ (w - 4 - 2 - D) := by rw [show w - 4 - 2 - D = w - 6 - D by omega]; omega
  have hKC : KC ≤ 2 ^ (w - 6 - 2 - D) := by rw [show w - 6 - 2 - D = w - 8 - D by omega]; omega
  have hlen : (swIn qA qB qC).length = 3 + qA.length + qB.length + qC.length := by
    simp [swIn]; omega
  obtain ⟨hAf, hAb⟩ := hA (w - 2) qA hKA
    (by rw [show w - 2 - 2 - D = w - 4 - D by omega]; omega) (by omega)
  obtain ⟨hBf, hBb⟩ := hB (w - 4) qB hKB
    (by rw [show w - 4 - 2 - D = w - 6 - D by omega]; omega) (by omega)
  obtain ⟨hCf, hCb⟩ := hC (w - 6) qC hKC
    (by rw [show w - 6 - 2 - D = w - 8 - D by omega]; omega) (by omega)
  simp only [show w - 2 - 2 - D = w - 4 - D by omega, show w - 2 - 2 = w - 4 by omega,
    show w - 4 - 2 - D = w - 6 - D by omega, show w - 4 - 2 = w - 6 by omega,
    show w - 6 - 2 - D = w - 8 - D by omega, show w - 6 - 2 = w - 8 by omega] at hAf hAb hBf hBb hCf hCb
  -- the rewrites fit
  have F₁ : swR₁.Fits w (fun _ => swIn qA qB qC) := by
    refine ⟨fun _ => by dsimp only; omega, by rw [swR₁_apply]; omega, fun seg hseg => ?_⟩
    simp only [swR₁, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    subst hseg
    simp only [Segment.Fits, HExpr.Fits, HExpr.eval, swIn]
    simp; omega
  have F₁' : ∀ y : List ℕ, y.length < 2 ^ (w - 6 - D) → swR₁'.Fits w ![y, swIn qA qB qC] := by
    intro y hy
    refine ⟨fun i => by fin_cases i <;> simp <;> omega, by rw [swR₁'_apply]; simp [swX₁]; omega,
      fun seg hseg => ?_⟩
    simp only [swR₁', List.mem_cons, List.mem_nil_iff, or_false] at hseg
    rcases hseg with rfl | rfl | rfl | rfl <;>
      simp [Segment.Fits, HExpr.Fits, HExpr.eval, swIn] <;> omega
  have F₂ : ∀ y : List ℕ, y.length < 2 ^ (w - 6 - D) →
      swR₂.Fits (w - 2) (fun _ => swX₁ qB qC y) := by
    intro y hy
    refine ⟨fun _ => by dsimp only; simp [swX₁]; omega, by rw [swR₂_apply]; omega, fun seg hseg => ?_⟩
    simp only [swR₂, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    subst hseg
    simp [Segment.Fits, HExpr.Fits, HExpr.eval, swX₁]; omega
  have F₂' : ∀ y z : List ℕ, y.length < 2 ^ (w - 6 - D) → z.length < 2 ^ (w - 8 - D) →
      swR₂'.Fits (w - 2) ![z, swX₁ qB qC y] := by
    intro y z hy hz
    refine ⟨fun i => by fin_cases i <;> simp [swX₁] <;> omega,
      by rw [swR₂'_apply]; simp [swX₂]; omega, fun seg hseg => ?_⟩
    simp only [swR₂', List.mem_cons, List.mem_nil_iff, or_false] at hseg
    rcases hseg with rfl | rfl | rfl <;>
      simp [Segment.Fits, HExpr.Fits, HExpr.eval, swX₁] <;> omega
  have F₃ : ∀ y z : List ℕ, y.length < 2 ^ (w - 6 - D) → z.length < 2 ^ (w - 8 - D) →
      swR₃.Fits (w - 4) (fun _ => swX₂ qC y z) := by
    intro y z hy hz
    refine ⟨fun _ => by dsimp only; simp [swX₂]; omega, by rw [swR₃_apply]; omega, fun seg hseg => ?_⟩
    simp only [swR₃, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    subst hseg
    simp [Segment.Fits, HExpr.Fits, HExpr.eval, swX₂]; omega
  have F₃' : ∀ y z u : List ℕ, y.length < 2 ^ (w - 6 - D) → z.length < 2 ^ (w - 8 - D) →
      u.length < 2 ^ (w - 10 - D) → swR₃'.Fits (w - 4) ![u, swX₂ qC y z] := by
    intro y z u hy hz hu
    refine ⟨fun i => by fin_cases i <;> simp [swX₂] <;> omega,
      by rw [swR₃'_apply]; simp; omega, fun seg hseg => ?_⟩
    simp only [swR₃', List.mem_cons, List.mem_nil_iff, or_false] at hseg
    rcases hseg with rfl | rfl <;>
      simp [Segment.Fits, HExpr.Fits, HExpr.eval, swX₂] <;> omega
  have hK₃ : K₃ ≤ 2 ^ (w - 4 - 2) := by rw [show w - 4 - 2 = w - 6 by omega]; omega
  have hK₂ : K₂ ≤ 2 ^ (w - 2 - 2) := by rw [show w - 2 - 2 = w - 4 by omega]; omega
  obtain ⟨h₁f, h₁b⟩ := h₁ w (swIn qA qB qC) (by omega) F₁
  rw [swR₁_apply] at h₁f h₁b
  have hcost₁ := swR_cost₁ (fun _ => swIn qA qB qC)
  -- the copy at the end
  have hcat : ∀ y z u : List ℕ, (∀ e ∈ y ++ z ++ u, e < 2 ^ (w - 6)) →
      y.length < 2 ^ (w - 6 - D) → z.length < 2 ^ (w - 8 - D) → u.length < 2 ^ (w - 10 - D) →
      RunsTo (w - 6) (catProg 2) (y ++ z ++ u) (y ++ z ++ u)
        (4 + 7 * (y ++ z ++ u).length + 2) := by
    intro y z u he hy hz hu
    have h := cat_fwd (w := w - 6) (E := 2) (x := y ++ z ++ u) (by omega) (by omega)
      (by
        have : 1 ≤ 2 ^ (w - 10) := Nat.one_le_two_pow
        simp only [catLim, List.length_append, show (2 : ℕ) ^ 2 = 4 by norm_num]; omega)
    rwa [map_mod_of_lt he] at h
  refine ⟨fun y z u tA tB tC hy hz hu hyl hzl hul => ?_, fun o T ho => ?_⟩
  · obtain ⟨tA', eA₀, runA⟩ := hAf y tA hy hyl
    obtain ⟨tB', eB₀, runB⟩ := hBf z tB hz hzl
    obtain ⟨tC', eC₀, runC⟩ := hCf u tC hu hul
    have he : ∀ e ∈ y ++ z ++ u, e < 2 ^ (w - 6) := by
      intro e he
      simp only [List.mem_append] at he
      rcases he with (he | he) | he
      · exact lt_of_lt_of_le (runsTo_out_lt hy e he) q4
      · exact lt_of_lt_of_le (runsTo_out_lt hz e he) (by omega)
      · exact lt_of_lt_of_le (runsTo_out_lt hu e he) (by omega)
    have rcat := hcat y z u he (by omega) (by omega) (by omega)
    obtain ⟨h₃f, -⟩ := h₃ (w - 4) (swX₂ qC y z) hK₃ (F₃ y z (by omega) (by omega))
    rw [swR₃_apply, show w - 4 - 2 = w - 6 by omega] at h₃f
    obtain ⟨t₃, ht₃, r₃⟩ := h₃f u (y ++ z ++ u) tC' _ (by omega)
      (F₃' y z u (by omega) (by omega) (by omega)) runC (by rw [swR₃'_apply]; exact rcat)
    obtain ⟨h₂f, -⟩ := h₂ (w - 2) (swX₁ qB qC y) hK₂ (F₂ y (by omega))
    rw [swR₂_apply, show w - 2 - 2 = w - 4 by omega] at h₂f
    obtain ⟨t₂, ht₂, r₂⟩ := h₂f z (y ++ z ++ u) tB' t₃ (by omega)
      (F₂' y z (by omega) (by omega)) runB (by rw [swR₂'_apply]; exact r₃)
    obtain ⟨t₁, ht₁, r₁⟩ := h₁f y (y ++ z ++ u) tA' t₂ (by omega)
      (F₁' y (by omega)) runA (by rw [swR₁'_apply]; exact r₂)
    refine ⟨t₁, le_trans ht₁ ?_, r₁⟩
    have c₂ := swR_cost₂ ![y, swIn qA qB qC]
    have c₂' := swR_cost₂ ![z, swX₁ qB qC y]
    have c₂'' := swR_cost₂ ![u, swX₂ qC y z]
    have c₁' := swR_cost₁ (fun _ => swX₁ qB qC y)
    have c₁'' := swR_cost₁ (fun _ => swX₂ qC y z)
    set S := tA + tB + tC + y.length + z.length + u.length + 1 with hS
    have eA : tA' ≤ KA * S := le_trans eA₀ (Nat.mul_le_mul_left _ (by omega))
    have eB : tB' ≤ KB * S := le_trans eB₀ (Nat.mul_le_mul_left _ (by omega))
    have eC : tC' ≤ KC * S := le_trans eC₀ (Nat.mul_le_mul_left _ (by omega))
    have ecat : 4 + 7 * (y ++ z ++ u).length + 2 ≤ 7 * S := by simp; omega
    have e₃ : t₃ ≤ K₃ * ((KC + 31) * S) := by
      refine le_trans ht₃ (Nat.mul_le_mul_left _ ?_)
      have : (KC + 31) * S = KC * S + 31 * S := by ring
      omega
    have e₂ : t₂ ≤ K₂ * ((KB + K₃ * (KC + 31) + 24) * S) := by
      refine le_trans ht₂ (Nat.mul_le_mul_left _ ?_)
      have : (KB + K₃ * (KC + 31) + 24) * S = KB * S + K₃ * ((KC + 31) * S) + 24 * S := by ring
      omega
    have e₁ : K₁ * (tA' + t₂ + swR₁.cost (fun _ => swIn qA qB qC) +
        swR₁'.cost ![y, swIn qA qB qC]) ≤ Kt * S := by
      rw [hKt, Nat.mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have : (KA + K₂ * (KB + K₃ * (KC + 31) + 24) + 24) * S =
          KA * S + K₂ * ((KB + K₃ * (KC + 31) + 24) * S) + 24 * S := by ring
      omega
    have : Kt * S ≤ (Kt + K₁ + K₂ + K₃ + KA + KB + KC + 1) * S :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · obtain ⟨y, tA', -, -, runA, r₁⟩ := h₁b o T ho
    obtain ⟨tA, -, hy, hyl⟩ := hAb y tA' runA
    obtain ⟨t₂, -, r₂⟩ := r₁ (F₁' y (by omega))
    rw [swR₁'_apply] at r₂
    obtain ⟨-, h₂b⟩ := h₂ (w - 2) (swX₁ qB qC y) hK₂ (F₂ y (by omega))
    rw [swR₂_apply, show w - 2 - 2 = w - 4 by omega] at h₂b
    obtain ⟨z, tB', -, -, runB, r₂'⟩ := h₂b o t₂ r₂
    obtain ⟨tB, -, hz, hzl⟩ := hBb z tB' runB
    obtain ⟨t₃, -, r₃⟩ := r₂' (F₂' y z (by omega) (by omega))
    rw [swR₂'_apply] at r₃
    obtain ⟨-, h₃b⟩ := h₃ (w - 4) (swX₂ qC y z) hK₃ (F₃ y z (by omega) (by omega))
    rw [swR₃_apply, show w - 4 - 2 = w - 6 by omega] at h₃b
    obtain ⟨u, tC', -, -, runC, r₃'⟩ := h₃b o t₃ r₃
    obtain ⟨tC, -, hu, hul⟩ := hCb u tC' runC
    obtain ⟨t₄, -, r₄⟩ := r₃' (F₃' y z u (by omega) (by omega) (by omega))
    rw [swR₃'_apply] at r₄
    obtain ⟨-, rfl⟩ := cat_back (w := w - 6) (E := 2) (by omega) (by omega) r₄
    have he : ∀ e ∈ y ++ z ++ u, e < 2 ^ (w - 6) := by
      intro e he
      simp only [List.mem_append] at he
      rcases he with (he | he) | he
      · exact lt_of_lt_of_le (runsTo_out_lt hy e he) q4
      · exact lt_of_lt_of_le (runsTo_out_lt hz e he) (by omega)
      · exact lt_of_lt_of_le (runsTo_out_lt hu e he) (by omega)
    rw [map_mod_of_lt he]
    exact ⟨y, z, u, tA, tB, tC, hy, hz, hu, rfl, hyl, hzl, hul⟩

end Lax185574Proofs.Simulate
