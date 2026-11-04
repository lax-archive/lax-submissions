import Lax185574Proofs.CompRam.Fixed
import Lax185574Proofs.Words.ForLoop

/-!
Writing the atom list `atL ℓ R₁ R₂` by loops.

`wAtL ℓ R₁ R₂` appends `toWord (atL ℓ R₁ R₂)` to the output: the count,
then the frames of the equalities, the colors, the binary and the unary
distance atoms, each block by nested counting loops over the radius and
the positions (`wAtL_run`). It uses the scalars `fi`, `fj`, `fr` and
writes no array. The fixed question `dSq` of the rank shift is written
this way by `wDSq` (`wDSq_run`), within `40000` steps.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding

/-! ### Writing a list of values -/

/-- Write the values of a list of expressions. -/
def wList : List Expr → Com
  | [] => .skip
  | e :: es => .seq (.write e) (wList es)

/-- The cost of `wList`. -/
def wCost (es : List Expr) : ℕ := (es.map fun e => 1 + e.size).sum + 1

theorem wList_run {B : ℕ} : ∀ {es : List Expr} {vs : List ℕ} {σ : Env},
    List.Forall₂ (fun e v => ∀ o, e.evalB B { σ with out := o } = some v) es vs →
    Run B (wList es) σ { σ with out := σ.out ++ vs } (wCost es)
  | [], [], σ, .nil => by
    simp only [wList, wCost, List.map_nil, List.sum_nil, List.append_nil]
    exact Run.skip
  | e :: es, v :: vs, σ, .cons h hs => by
    have h1 := Run.write (B := B) (σ := σ) (e := e) (v := v) (by simpa using h σ.out)
    have h2 := wList_run (B := B) (σ := { σ with out := σ.out ++ [v] }) (es := es) (vs := vs)
      (hs.imp fun _ _ h' o => h' o)
    simp only [List.append_assoc, List.singleton_append] at h2
    refine (Run.seq h1 h2).mono ?_
    simp [wCost]; omega

/-! ### Counting loops that write -/

theorem forUp_out {B : ℕ} {i : String} {N K : ℕ} {body : Com} (f : ℕ → List ℕ)
    (P : Env → Prop) {σ : Env} (hN : N < B) (hP : ∀ τ v, P τ → P (τ.setVar i v))
    (hb : ∀ k < N, ∀ τ, P τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' K ∧ τ'.vars i = k ∧ P τ' ∧ τ'.out = τ.out ++ f k)
    (hσ : P σ) :
    ∃ σ', Run B (forUp i (.lit N) body) σ σ' (N * (K + 8) + 6) ∧ P σ' ∧
      σ'.out = σ.out ++ (List.range N).flatMap f := by
  obtain ⟨σ', hr, ⟨hP', ho⟩, -⟩ := forUp_run (B := B) (i := i) (e := .lit N) (body := body) (N := N)
    (K := K) (fun k τ => P τ ∧ τ.out = σ.out ++ (List.range k).flatMap f) hN
    (fun _ _ _ _ _ => evalB_lit hN) ⟨hP σ 0 hσ, by simp⟩
    (fun k hk τ ⟨hτ, ho⟩ hi => by
      obtain ⟨τ', hr, hi', hP', ho'⟩ := hb k hk τ hτ hi
      refine ⟨τ', hr, hi', hP τ' _ hP', ?_⟩
      simp only [out_setVar, ho', ho, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc])
  exact ⟨σ', hr.mono (by simp [Expr.size]), hP', ho⟩

/-! ### The four blocks -/

/-- The equalities. -/
def wEq (ℓ : ℕ) : Com :=
  forUp "fi" (.lit ℓ) (forUp "fj" (.lit ℓ) (wList [.lit 3, .lit 0, .var "fi", .var "fj"]))

/-- The colors. -/
def wCol (ℓ : ℕ) : Com := forUp "fi" (.lit ℓ) (wList [.lit 3, .lit 3, .lit 0, .var "fi"])

/-- The binary distance atoms. -/
def wDist (ℓ R : ℕ) : Com :=
  forUp "fr" (.lit (R + 1)) (forUp "fi" (.lit ℓ) (forUp "fj" (.lit ℓ)
    (wList [.lit 4, .lit 4, .var "fr", .var "fi", .var "fj"])))

/-- The unary distance atoms. -/
def wDcol (ℓ R : ℕ) : Com :=
  forUp "fr" (.lit R) (forUp "fi" (.lit ℓ)
    (wList [.lit 4, .lit 5, .add (.var "fr") (.lit 1), .lit 0, .var "fi"]))

/-- The number of atoms of `atL`. -/
def atN (ℓ R₁ R₂ : ℕ) : ℕ := ℓ * ℓ + ℓ + (R₁ + 1) * (ℓ * ℓ) + R₂ * ℓ

/-- The atom list with its count. -/
def wAtL (ℓ R₁ R₂ : ℕ) : Com :=
  .seq (.write (.lit (atN ℓ R₁ R₂))) (.seq (wEq ℓ) (.seq (wCol ℓ) (.seq (wDist ℓ R₁) (wDcol ℓ R₂))))

/-- The flattened frames of a list of words. -/
def frs (ws : List (List ℕ)) : List ℕ := (ws.map toWord).flatten

theorem frs_flatMap {α : Type*} (L : List α) (g : α → List (List ℕ)) :
    frs (L.flatMap g) = L.flatMap fun a => frs (g a) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [frs, List.flatMap_cons, List.map_append, List.flatten_append] at ih ⊢; rw [ih]

theorem frs_map {α : Type*} (L : List α) (g : α → List ℕ) :
    frs (L.map g) = L.flatMap fun a => toWord (g a) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [frs, List.map_cons, List.flatten_cons, List.flatMap_cons] at ih ⊢; rw [ih]

theorem frs_append (a b : List (List ℕ)) : frs (a ++ b) = frs a ++ frs b := by
  simp [frs]

theorem length_atL (ℓ R₁ R₂ : ℕ) : (atL ℓ R₁ R₂).length = atN ℓ R₁ R₂ := by
  simp [atL, atEq, atCol, atDist, atDcol, atN, List.length_flatMap, List.map_const',
    List.sum_replicate]
  ring

theorem toWord_atL (ℓ R₁ R₂ : ℕ) : toWord (atL ℓ R₁ R₂) = atN ℓ R₁ R₂ :: frs (atL ℓ R₁ R₂) := by
  show (atL ℓ R₁ R₂).length :: _ = _
  rw [length_atL]; rfl

/-- The cost of `wAtL`. -/
def wAtLCost (ℓ R₁ R₂ : ℕ) : ℕ :=
  2 + (ℓ * ((ℓ * 17 + 6) + 8) + 6) + (ℓ * 17 + 6) + ((R₁ + 1) * ((ℓ * ((ℓ * 19 + 6) + 8) + 6) + 8) + 6) +
    (R₂ * ((ℓ * 21 + 6) + 8) + 6)

/-- The frame of equalities with first position `i`. -/
theorem wEq_body {B ℓ i : ℕ} (hB : ℓ + 4 < B) (hi : i < ℓ) {τ : Env} (hτ : τ.vars "fi" = i) :
    ∃ τ', Run B (forUp "fj" (.lit ℓ) (wList [.lit 3, .lit 0, .var "fi", .var "fj"])) τ τ'
        (ℓ * 17 + 6) ∧ τ'.vars "fi" = i ∧ τ'.inp = τ.inp ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ frs ((List.range ℓ).map fun j => [0, i, j]) := by
  obtain ⟨τ', r, ⟨e1, e2, e3⟩, o⟩ := forUp_out (B := B) (i := "fj") (N := ℓ) (K := 9)
    (body := wList [.lit 3, .lit 0, .var "fi", .var "fj"]) (fun j => [3, 0, i, j])
    (fun ρ => ρ.vars "fi" = i ∧ ρ.inp = τ.inp ∧ ρ.arrs = τ.arrs) (σ := τ) (by omega)
    (fun ρ v h => by simpa using h)
    (fun j hj ρ ⟨h1, h2, h3⟩ hρj => ⟨_, (wList_run (.cons (fun o => evalB_lit (by omega))
        (.cons (fun o => evalB_lit (by omega)) (.cons (fun o => evalB_var (by simp; omega))
          (.cons (fun o => evalB_var (by simp; omega)) .nil))))).mono (by simp [wCost, Expr.size]),
      by simp [hρj], ⟨by simp [h1], by simp [h2], by simp [h3]⟩, by simp [h1, hρj]⟩)
    ⟨hτ, rfl, rfl⟩
  exact ⟨τ', r.mono (by omega), e1, e2, e3, by rw [o, frs_map]; rfl⟩

/-- The frames of binary distance atoms with radius `r` and first position `i`. -/
theorem wDist_inner {B ℓ r i : ℕ} (hB : ℓ + r + 5 < B) (hi : i < ℓ) {τ : Env}
    (hτ : τ.vars "fi" = i) (hτr : τ.vars "fr" = r) :
    ∃ τ', Run B (forUp "fj" (.lit ℓ) (wList [.lit 4, .lit 4, .var "fr", .var "fi", .var "fj"])) τ τ'
        (ℓ * 19 + 6) ∧ τ'.vars "fi" = i ∧ τ'.vars "fr" = r ∧ τ'.inp = τ.inp ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ frs ((List.range ℓ).map fun j => [4, r, i, j]) := by
  obtain ⟨τ', run, ⟨e1, e0, e2, e3⟩, o⟩ := forUp_out (B := B) (i := "fj") (N := ℓ) (K := 11)
    (body := wList [.lit 4, .lit 4, .var "fr", .var "fi", .var "fj"]) (fun j => [4, 4, r, i, j])
    (fun ρ => ρ.vars "fi" = i ∧ ρ.vars "fr" = r ∧ ρ.inp = τ.inp ∧ ρ.arrs = τ.arrs) (σ := τ)
    (by omega) (fun ρ v h => by simpa using h)
    (fun j hj ρ ⟨h1, h0, h2, h3⟩ hρj => ⟨_, (wList_run (.cons (fun o => evalB_lit (by omega))
        (.cons (fun o => evalB_lit (by omega)) (.cons (fun o => evalB_var (by simp; omega))
          (.cons (fun o => evalB_var (by simp; omega)) (.cons (fun o => evalB_var (by simp; omega))
            .nil)))))).mono (by simp [wCost, Expr.size]),
      by simp [hρj], ⟨by simp [h1], by simp [h0], by simp [h2], by simp [h3]⟩, by simp [h1, h0, hρj]⟩)
    ⟨hτ, hτr, rfl, rfl⟩
  exact ⟨τ', run.mono (by omega), e1, e0, e2, e3, by rw [o, frs_map]; rfl⟩

/-- **Writing the atom list.** -/
theorem wAtL_run {B ℓ R₁ R₂ : ℕ} (hB : atN ℓ R₁ R₂ + ℓ + R₁ + R₂ + 6 < B) (σ : Env) :
    ∃ σ', Run B (wAtL ℓ R₁ R₂) σ σ' (wAtLCost ℓ R₁ R₂) ∧
      σ'.out = σ.out ++ toWord (atL ℓ R₁ R₂) ∧ σ'.inp = σ.inp ∧ σ'.arrs = σ.arrs := by
  have hl : ℓ < B := by omega
  -- the count
  have r0 := Run.write (B := B) (σ := σ) (e := .lit (atN ℓ R₁ R₂)) (v := atN ℓ R₁ R₂)
    (evalB_lit (by omega))
  -- equalities
  obtain ⟨σ1, r1, ⟨i1, a1⟩, o1⟩ := forUp_out (B := B) (i := "fi") (N := ℓ) (K := ℓ * 17 + 6)
    (body := forUp "fj" (.lit ℓ) (wList [.lit 3, .lit 0, .var "fi", .var "fj"]))
    (fun i => frs ((List.range ℓ).map fun j => [0, i, j])) (fun τ => τ.inp = σ.inp ∧ τ.arrs = σ.arrs)
    (σ := { σ with out := σ.out ++ [atN ℓ R₁ R₂] }) hl (fun τ v h => by simpa using h)
    (fun i hi τ ⟨hi1, ha1⟩ hτi => by
      obtain ⟨τ', r, e1, e2, e3, o⟩ := wEq_body (B := B) (by omega) hi hτi
      exact ⟨τ', r, e1, ⟨e2.trans hi1, e3.trans ha1⟩, o⟩)
    ⟨rfl, rfl⟩
  -- colors
  obtain ⟨σ2, r2, ⟨i2, a2⟩, o2⟩ := forUp_out (B := B) (i := "fi") (N := ℓ) (K := 9)
    (body := wList [.lit 3, .lit 3, .lit 0, .var "fi"]) (fun i => [3, 3, 0, i])
    (fun τ => τ.inp = σ.inp ∧ τ.arrs = σ.arrs) (σ := σ1) hl (fun τ v h => by simpa using h)
    (fun i hi τ ⟨hi1, ha1⟩ hτi => ⟨_, (wList_run (.cons (fun o => evalB_lit (by omega))
        (.cons (fun o => evalB_lit (by omega)) (.cons (fun o => evalB_lit (by omega))
          (.cons (fun o => evalB_var (by simp; omega)) .nil))))).mono (by simp [wCost, Expr.size]),
      by simp [hτi], ⟨by simp [hi1], by simp [ha1]⟩, by simp [hτi]⟩)
    ⟨i1, a1⟩
  -- binary distance atoms
  obtain ⟨σ3, r3, ⟨i3, a3⟩, o3⟩ := forUp_out (B := B) (i := "fr") (N := R₁ + 1)
    (K := ℓ * ((ℓ * 19 + 6) + 8) + 6)
    (body := forUp "fi" (.lit ℓ) (forUp "fj" (.lit ℓ)
      (wList [.lit 4, .lit 4, .var "fr", .var "fi", .var "fj"])))
    (fun r => frs ((List.range ℓ).flatMap fun i => (List.range ℓ).map fun j => [4, r, i, j]))
    (fun τ => τ.inp = σ.inp ∧ τ.arrs = σ.arrs) (σ := σ2) (by omega) (fun τ v h => by simpa using h)
    (fun r hr τ ⟨hi1, ha1⟩ hτr => by
      obtain ⟨τ', run, ⟨e0, e2, e3⟩, o⟩ := forUp_out (B := B) (i := "fi") (N := ℓ)
        (K := ℓ * 19 + 6)
        (body := forUp "fj" (.lit ℓ) (wList [.lit 4, .lit 4, .var "fr", .var "fi", .var "fj"]))
        (fun i => frs ((List.range ℓ).map fun j => [4, r, i, j]))
        (fun ρ => ρ.vars "fr" = r ∧ ρ.inp = σ.inp ∧ ρ.arrs = σ.arrs) (σ := τ) hl
        (fun ρ v h => by simpa using h)
        (fun i hi ρ ⟨h0, h1, h2⟩ hρi => by
          obtain ⟨ρ', run', e1, e0', e2', e3', o'⟩ := wDist_inner (B := B) (r := r) (by omega) hi hρi h0
          exact ⟨ρ', run', e1, ⟨e0', e2'.trans h1, e3'.trans h2⟩, o'⟩)
        ⟨hτr, hi1, ha1⟩
      exact ⟨τ', run, e0, ⟨e2, e3⟩, by rw [o, frs_flatMap]⟩)
    ⟨i2, a2⟩
  -- unary distance atoms
  obtain ⟨σ4, r4, ⟨i4, a4⟩, o4⟩ := forUp_out (B := B) (i := "fr") (N := R₂)
    (K := ℓ * 21 + 6)
    (body := forUp "fi" (.lit ℓ) (wList [.lit 4, .lit 5, .add (.var "fr") (.lit 1), .lit 0, .var "fi"]))
    (fun r => frs ((List.range ℓ).map fun i => [5, r + 1, 0, i]))
    (fun τ => τ.inp = σ.inp ∧ τ.arrs = σ.arrs) (σ := σ3) (by omega) (fun τ v h => by simpa using h)
    (fun r hr τ ⟨hi1, ha1⟩ hτr => by
      obtain ⟨τ', run, ⟨e0, e2, e3⟩, o⟩ := forUp_out (B := B) (i := "fi") (N := ℓ) (K := 13)
        (body := wList [.lit 4, .lit 5, .add (.var "fr") (.lit 1), .lit 0, .var "fi"])
        (fun i => [4, 5, r + 1, 0, i])
        (fun ρ => ρ.vars "fr" = r ∧ ρ.inp = σ.inp ∧ ρ.arrs = σ.arrs) (σ := τ) hl
        (fun ρ v h => by simpa using h)
        (fun i hi ρ ⟨h0, h1, h2⟩ hρi => ⟨_, (wList_run (.cons (fun o => evalB_lit (by omega))
            (.cons (fun o => evalB_lit (by omega))
              (.cons (fun o => evalB_bin (evalB_var (by show ρ.vars "fr" < B; omega))
                (evalB_lit (by omega)) (by show ρ.vars "fr" + 1 < B; omega))
              (.cons (fun o => evalB_lit (by omega)) (.cons (fun o => evalB_var (by simp; omega))
                .nil)))))).mono (by simp [wCost, Expr.size]),
          by simp [hρi], ⟨by simp [h0], by simp [h1], by simp [h2]⟩, by simp [h0, hρi]⟩)
        ⟨hτr, hi1, ha1⟩
      exact ⟨τ', run, e0, ⟨e2, e3⟩, by rw [o, frs_map]; rfl⟩)
    ⟨i3, a3⟩
  refine ⟨σ4, ?_, ?_, i4, a4⟩
  · unfold wAtL wEq wCol wDist wDcol
    exact (Run.seq r0 (Run.seq r1 (Run.seq r2 (Run.seq r3 r4)))).mono
      (le_of_eq (by simp only [wAtLCost, Expr.size]; ring))
  · rw [o4, o3, o2, o1, toWord_atL]
    simp only [atL, frs_append, atEq, atCol, atDist, atDcol, frs_flatMap, frs_map, List.append_assoc,
      List.cons_append]
    rfl

/-! ### The fixed question -/

theorem flatten_map_nat (L : List ℕ) : (L.map toWord).flatten = L := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.flatten_cons, ih]; rfl

set_option maxRecDepth 8000 in
theorem length_toWord_atL2 : (toWord (atL 2 1 81)).length = 875 := by
  rw [length_toWord_words]; decide

theorem toWord_ext_word : toWord [0 :: toWord (atL 2 1 81)] = [1, 876, 0] ++ toWord (atL 2 1 81) := by
  show [0 :: toWord (atL 2 1 81)].length ::
    ([(0 :: toWord (atL 2 1 81)).length :: ((0 :: toWord (atL 2 1 81)).map toWord).flatten]).flatten = _
  have h : ((0 :: toWord (atL 2 1 81)).map toWord).flatten = 0 :: toWord (atL 2 1 81) := by
    rw [List.map_cons, List.flatten_cons]
    exact congrArg _ (flatten_map_nat _)
  rw [h]
  simp only [List.length_cons, List.length_nil, length_toWord_atL2, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  rfl

/-- Write the fixed question `dSq` of the rank shift. -/
def wDSq : Com :=
  .seq (wList [.lit 1, .lit 1, .lit 1]) (.seq (wAtL 1 729 6561)
    (.seq (wList [.lit 1, .lit 876, .lit 0]) (wAtL 2 1 81)))

/-- The cost of `wDSq`. -/
def wDSqCost : ℕ := 14 + wAtLCost 1 729 6561 + wAtLCost 2 1 81

theorem wDSqCost_le : wDSqCost ≤ 300000 := by
  norm_num [wDSqCost, wAtLCost]

/-- **Writing the fixed question.** -/
theorem wDSq_run {B : ℕ} (hB : 20000 ≤ B) (σ : Env) :
    ∃ σ', Run B wDSq σ σ' wDSqCost ∧ σ'.out = σ.out ++ dSq ∧ σ'.inp = σ.inp ∧ σ'.arrs = σ.arrs := by
  have r1 := wList_run (B := B) (σ := σ) (es := [.lit 1, .lit 1, .lit 1]) (vs := [1, 1, 1])
    (.cons (fun _ => evalB_lit (by omega)) (.cons (fun _ => evalB_lit (by omega))
      (.cons (fun _ => evalB_lit (by omega)) .nil)))
  obtain ⟨σ2, r2, o2, i2, a2⟩ := wAtL_run (B := B) (ℓ := 1) (R₁ := 729) (R₂ := 6561)
    (by simp only [atN]; omega) { σ with out := σ.out ++ [1, 1, 1] }
  have r3 := wList_run (B := B) (σ := σ2) (es := [.lit 1, .lit 876, .lit 0]) (vs := [1, 876, 0])
    (.cons (fun _ => evalB_lit (by omega)) (.cons (fun _ => evalB_lit (by omega))
      (.cons (fun _ => evalB_lit (by omega)) .nil)))
  obtain ⟨σ4, r4, o4, i4, a4⟩ := wAtL_run (B := B) (ℓ := 2) (R₁ := 1) (R₂ := 81)
    (by simp only [atN]; omega) { σ2 with out := σ2.out ++ [1, 876, 0] }
  refine ⟨σ4, (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by
    simp only [wDSqCost, wCost, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega),
    ?_, by rw [i4]; exact i2, by rw [a4]; exact a2⟩
  rw [o4, o2, dSq_eq, toWord_ext_word]
  simp only [List.append_assoc]

end Lax185574Proofs.CompRam
