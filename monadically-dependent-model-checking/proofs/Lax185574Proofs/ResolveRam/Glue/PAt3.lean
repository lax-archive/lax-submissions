import Lax185574Proofs.ResolveRam.Glue.PAt2

/-!
The extra test of the new atoms `[5, s, Y, i]`, and the candidate words
in the order of the loops, for the atom words of lem:resolve-lift.

`uT` is the extra test of the candidate `[5, s, Y, i]`: for `s ≥ 1` it
runs `uHopC` at radius `s - 1`, with the entries of the color table at
`Y` in `tx` and `tz` (`uT_run`). `candW_eq` writes the candidate words
as nested lists over ranges, the shape of the loops of the program.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574Proofs.ResolveRam
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The extra test of `[5, s, Y, i]`. -/
def uT : Com :=
  .ite (.lt (.lit 0) (.var "td1")) (.seq (.assign "ts" (.sub (.var "td1") (.lit 1)))
    (.seq (.assign "ti1" (.var "td3")) (.seq uHopC (.assign "tF" (.var "tw"))))) .skip

/-- The scalars that `uT` writes. -/
def uV : List String := ["ts", "ti1"] ++ hV ++ ["tF"]

theorem hopK_mono_s {L s t : ℕ} (h : s ≤ t) : hopK L s ≤ hopK L t := by
  unfold hopK
  apply Nat.mul_le_mul_right
  exact Nat.mul_le_mul (by omega) (by omega)

/-- **The extra test of `[5, s, Y, i]`.** -/
theorem uT_run {W : ℕ} {A : List (List ℕ)} {Xa rr : List ℕ} {p₁ : ℕ} {Dw : DW} {s Y i : ℕ}
    {τ : Env} (ha : τ.arrs "a" = Xa) (hd : Xa.drop p₁ = toWord A ++ rr) (hp : τ.vars "tp1" = p₁)
    (hP : τ.vars "tP" = Dw.P) (hQ : τ.vars "tQ" = Dw.Q)
    (hcP : τ.vars "tcP" = bv Dw.cP) (hcQ : τ.vars "tcQ" = bv Dw.cQ)
    (hs : τ.vars "td1" = s) (hi : τ.vars "td3" = i) (hx : τ.vars "tx" = Dw.tP Y)
    (hz : τ.vars "tz" = Dw.tQ Y) (hF : τ.vars "tF" = 0)
    (hPW : Dw.P ≤ W) (hQW : Dw.Q ≤ W) (hiW : i ≤ W) (hsW : 2 * s + 4 ≤ W) (hxW : Dw.tP Y ≤ W)
    (hzW : Dw.tQ Y ≤ W) (hB1 : p₁ + (toWord A).length + 6 < W + 1) (hv : ∀ v ∈ toWord A, v < W + 1) :
    ∃ τ', Run (W + 1) uT τ τ' (hopK (A.length + A.length) s + 20) ∧
      τ'.vars "tF" = bv (decide (1 ≤ s) && uHopW Dw A (s - 1) Y i) ∧ OFr τ τ' uV ∧
      τ'.arrs = τ.arrs := by
  have hc := evalB_condLt (B := W + 1) (σ := τ) (evalB_lit (n := 0) (by omega)) (ev_var hs (by omega))
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    refine ⟨τ, (Run.ite_false (by rw [hc]; rfl) Run.skip).mono (by simp [Cond.size, Expr.size]),
      by simp [hF, bv], (OFr.refl τ).mono (by simp), rfl⟩
  set τ1 := (τ.setVar "ts" (s - 1)).setVar "ti1" i
  have hU : UAt Xa A p₁ Dw i (s - 1) (Dw.tP Y) (Dw.tQ Y) τ1 :=
    ⟨by simp [τ1, ha], by simp [τ1, hp], by simp [τ1, hP], by simp [τ1, hQ], by simp [τ1, hcP],
      by simp [τ1, hcQ], by simp [τ1], by simp [τ1], by simp [τ1, hx], by simp [τ1, hz]⟩
  obtain ⟨τ2, r2, w2, f2, a2, o2, i2⟩ := uHopC_run (B := W + 1) hU hd
    ⟨hB1, hv, by omega, by omega, by omega, by omega, by omega, by omega⟩
  set b := (List.range (s - 1 + 1)).any fun s₁ => (List.range (s - 1 + 1)).any fun s₂ =>
    pairUB A Dw.P Dw.Q Dw.cP Dw.cQ (tabV (Dw.tP Y)) (tabV (Dw.tQ Y)) i (s - 1) s₁ s₂
  have hb : bv b < W + 1 := by have := bv_le b; omega
  set τ3 := τ2.setVar "tF" (bv b)
  have r3 : Run (W + 1) (.assign "tF" (.var "tw")) τ2 τ3 2 := Run.assign (ev_var w2 hb)
  refine ⟨τ3, ?_, ?_, ?_, by simp [τ3, a2, τ1]⟩
  · refine (Run.ite_true (by rw [hc]; simp [h0]) (Run.seq (Run.assign (ev_sub (ev_var hs (by omega))
      (evalB_lit (by omega)) (by omega))) (Run.seq (Run.assign (ev_var (v := i) (by simp [hi])
        (by omega))) (Run.seq r2 r3)))).mono ?_
    have := hopK_mono_s (L := A.length + A.length) (show s - 1 ≤ s by omega)
    simp [Cond.size, Expr.size]; omega
  · simp only [τ3, vars_setVar, if_true]
    rw [uHopW_pairUB]
    simp [b, show 1 ≤ s from h0]
  · refine ⟨fun y hy => ?_, fun b _ => by simp [τ3, a2, τ1], by simp [τ3, a2, τ1], by simp [τ3, o2, τ1],
      by simp [τ3, i2, τ1]⟩
    simp only [uV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [τ3, vars_setVar, hy.2, if_false]
    rw [f2 y hy.1.2]
    simp [τ1, hy.1.1.1, hy.1.1.2]

/-! ### The candidate words as nested lists -/

theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem flatMap_finRange {α : Type*} (n : ℕ) (F : ℕ → List α) :
    (List.finRange n).flatMap (fun i => F i.val) = (List.range n).flatMap F := by
  rw [← map_val_finRange, List.flatMap_map]

theorem map_finRange {α : Type*} (n : ℕ) (F : ℕ → α) :
    (List.finRange n).map (fun i => F i.val) = (List.range n).flatMap fun i => [F i] := by
  have : ∀ l : List ℕ, l.flatMap (fun i => [F i]) = l.map F := by intro l; induction l <;> simp_all
  rw [this, ← map_val_finRange, List.map_map]; rfl

theorem flatMap_getD {α : Type*} (l : List ℕ) (F : ℕ → List α) :
    l.flatMap F = (List.range l.length).flatMap fun m => F (l.getD m 0) := by
  have : l = (List.range l.length).map fun m => l.getD m 0 := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [List.getElem?_eq_getElem h1]
  conv_lhs => rw [this]
  rw [List.flatMap_map]

/-- The candidates `[d, i, j]` for the pairs of positions. -/
def pB (d ℓ : ℕ) : List (List ℕ) := (List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j => [[d, i, j]]

/-- The candidates `[3, Y, i]`. -/
def cB (cs : List ℕ) (ℓ : ℕ) : List (List ℕ) :=
  (List.range cs.length).flatMap fun m => (List.range ℓ).flatMap fun i => [[3, cs.getD m 0, i]]

/-- The candidates `[4, s, i, j]`. -/
def dB (R ℓ : ℕ) : List (List ℕ) :=
  (List.range (R + 1)).flatMap fun s => (List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j =>
    [[4, s, i, j]]

/-- The candidates `[5, s, Y, i]`. -/
def eB (R : ℕ) (cs : List ℕ) (ℓ : ℕ) : List (List ℕ) :=
  (List.range (R + 1)).flatMap fun s => (List.range cs.length).flatMap fun m =>
    (List.range ℓ).flatMap fun i => [[5, s, cs.getD m 0, i]]

theorem pairs_code {ℓ : ℕ} (f : Fin ℓ → Fin ℓ → DistFO ℓ) (G : ℕ → ℕ → List ℕ)
    (hf : ∀ i j : Fin ℓ, DistFO.code (f i j) = G i j) :
    ((pairsL ℓ).map fun p => f p.1 p.2).map DistFO.code =
      (List.range ℓ).flatMap fun i => (List.range ℓ).flatMap fun j => [G i j] := by
  unfold pairsL
  rw [List.map_flatMap, List.map_flatMap, ← flatMap_finRange]
  congr 1; funext i
  rw [List.map_map, List.map_map, ← map_finRange]
  congr 1; funext j
  exact hf i j

theorem cols_code {ℓ : ℕ} (cs : List ℕ) (f : ℕ → Fin ℓ → DistFO ℓ) (G : ℕ → ℕ → List ℕ)
    (hf : ∀ Y (i : Fin ℓ), DistFO.code (f Y i) = G Y i) :
    (cs.flatMap fun Y => (List.finRange ℓ).map fun i => f Y i).map DistFO.code =
      (List.range cs.length).flatMap fun m => (List.range ℓ).flatMap fun i => [G (cs.getD m 0) i] := by
  rw [List.map_flatMap, flatMap_getD]
  congr 1; funext m
  rw [List.map_map, ← map_finRange]
  congr 1; funext i
  exact hf _ i

/-- **The candidate words in the order of the loops.** -/
theorem candW_eq (k q ℓ : ℕ) (cs : List ℕ) :
    candW k q ℓ cs = pB 0 ℓ ++ pB 1 ℓ ++ pB 2 ℓ ++ cB cs ℓ ++ dB (rhoMinus k q) ℓ ++
      eB (rhoPlus k q) cs ℓ := by
  simp only [candW, candL, List.map_append]
  rw [pairs_code _ (fun i j => [0, i, j]) (fun _ _ => rfl),
    pairs_code _ (fun i j => [1, i, j]) (fun _ _ => rfl),
    pairs_code _ (fun i j => [2, i, j]) (fun _ _ => rfl),
    cols_code cs _ (fun Y i => [3, Y, i]) (fun _ _ => rfl), List.map_flatMap, List.map_flatMap]
  unfold pB cB dB eB
  congr 2
  · congr 1; funext s; exact pairs_code _ (fun i j => [4, s, i, j]) (fun _ _ => rfl)
  · funext s; exact cols_code cs _ (fun Y i => [5, s, Y, i]) (fun _ _ => rfl)

end Lax185574Proofs.ResolveRam.Glue
