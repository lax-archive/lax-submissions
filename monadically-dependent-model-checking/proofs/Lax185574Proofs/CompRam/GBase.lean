import Lax185574Proofs.CompRam.GCode
import Lax185574Proofs.CompRam.SizeBasic

/-!
The predicates of the proof of the glue command of lem:compose.

`Ctx W M σ`: the scalar `W`, the arrays `x`, `wp`, `OB` of length
`W + 1`, the entries of `x` below `M`, and room: `2^16 ≤ M` and
`1024 M ≤ W`. `SegIs M σ s l w`: the scalars `s`, `l` describe a
segment of `x` inside its first `M` cells that holds the word `w`.
`SlotIs M σ f`: the scalars `g…` describe the frame `f` as `emFr`
reads them. The last word of the list `EX` may be given separately
(`gx = 1`) as `gg :: R₁ ++ R₂`. `FreshIs M σ d kk l1 l2 A B`: the
scalars `c…` describe a new frame.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding

/-- The context of a round. -/
structure Ctx (W M : ℕ) (σ : Env) : Prop where
  hW : σ.vars "W" = W
  xl : (σ.arrs "x").length = W + 1
  ol : (σ.arrs "OB").length = W + 1
  wl : (σ.arrs "wp").length = W + 1
  xv : ∀ v ∈ σ.arrs "x", v < M
  m16 : 2 ^ 16 ≤ M
  room : 1024 * M ≤ W

theorem Ctx.of_frame {W M : ℕ} {σ σ' : Env} (h : Ctx W M σ) (hW : σ'.vars "W" = σ.vars "W")
    (hx : σ'.arrs "x" = σ.arrs "x") (hwp : σ'.arrs "wp" = σ.arrs "wp")
    (hOB : (σ'.arrs "OB").length = (σ.arrs "OB").length) : Ctx W M σ' :=
  ⟨by rw [hW, h.hW], by rw [hx, h.xl], by rw [hOB, h.ol], by rw [hwp, h.wl],
    by rw [hx]; exact h.xv, h.m16, h.room⟩

theorem Ctx.ofr {W M : ℕ} {σ σ' : Env} {xs : List String} (h : Ctx W M σ) (hf : OFr σ σ' xs)
    (hW : "W" ∉ xs) : Ctx W M σ' :=
  h.of_frame (hf.vars "W" hW) (hf.arrs "x" (by decide)) (hf.arrs "wp" (by decide)) hf.len

theorem Ctx.setVar {W M : ℕ} {σ : Env} (h : Ctx W M σ) {y : String} (hy : y ≠ "W") (v : ℕ) :
    Ctx W M (σ.setVar y v) :=
  h.of_frame (by simp [Ne.symm hy]) (by simp) (by simp) (by simp)

/-- A segment of `x` inside its first `M` cells holds `w`. -/
def SegIs (M : ℕ) (σ : Env) (s l : String) (w : List ℕ) : Prop :=
  σ.vars l = w.length ∧ σ.vars s + w.length ≤ M ∧ seg (σ.arrs "x") (σ.vars s) w.length = w

/-- The scalars of the list `EX` of the frame. -/
def ExIs (M : ℕ) (σ : Env) (EX : List (List ℕ)) : Prop :=
  (σ.vars "gx" = 0 ∧ SegIs M σ "gEs" "gEl" (toWord EX)) ∨
  (σ.vars "gx" = 1 ∧ σ.vars "gg" < 2 * M ∧ ∃ E0 R1 R2, EX = E0 ++ [σ.vars "gg" :: (R1 ++ R2)] ∧
    SegIs M σ "gEs" "gEl" (toWord E0) ∧ SegIs M σ "r1s" "r1l" R1 ∧ SegIs M σ "r2s" "r2l" R2)

/-- The scalars `g…` describe the frame `f`. -/
structure SlotIs (M : ℕ) (σ : Env) (f : Fr) : Prop where
  d : σ.vars "gd" = f.d
  kk : σ.vars "gk" = f.kk
  l1 : σ.vars "g1" = f.l1
  l2 : σ.vars "g2" = f.l2
  ph : σ.vars "gp" = f.ph
  i : σ.vars "gi" = f.i
  nums : f.d < 2 * M ∧ f.kk < 2 * M ∧ f.l1 < 2 * M ∧ f.l2 < 2 * M ∧ f.ph < 2 * M ∧ f.i < 2 * M
  A : SegIs M σ "gAs" "gAl" f.A
  B : SegIs M σ "gBs" "gBl" f.B
  SA : SegIs M σ "gSs" "gSl" f.SA
  SB : SegIs M σ "gTs" "gTl" f.SB
  AT : SegIs M σ "gUs" "gUl" f.AT
  EX : ExIs M σ f.EX

/-- The scalars `c…` describe the new frame `fresh d kk l1 l2 A B`. -/
structure FreshIs (M : ℕ) (σ : Env) (d kk l1 l2 : ℕ) (A B : List ℕ) : Prop where
  hd : σ.vars "cd" = d
  hk : σ.vars "ck" = kk
  h1 : σ.vars "c1" = l1
  h2 : σ.vars "c2" = l2
  nums : d < 2 * M ∧ kk < 2 * M ∧ l1 < 2 * M ∧ l2 < 2 * M
  hA : SegIs M σ "cAs" "cAl" A
  hB : SegIs M σ "cBs" "cBl" B

/-- The word of the query of a restriction, by numbers. -/
def reW (kk d l1 l2 : ℕ) (R : List ℕ) : List ℕ :=
  [kk + 1, d - 1, l1 + 1 + l2] ++ R ++ ((l1 + l2 + 1) :: jList l1 l2)

theorem reQuery_eq (p : Fr) (R : List ℕ) : reQuery p R = reW p.kk p.d p.l1 p.l2 R := rfl

/-! ### Filling in a cell of the buffer -/

theorem _root_.Lax185574Proofs.MC.Filled.set {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ) {k : ℕ}
    (hk : k < l.length) (v : ℕ) : Filled a pv (l.set k v) (τ.setArr a k v) := by
  refine ⟨by simp [h.pos], fun i hi => ?_⟩
  simp only [List.length_set] at hi
  simp only [Env.setArr, if_true]
  rw [List.getElem?_set, List.getElem_set]
  have hl := h.length_le
  by_cases hik : k = i
  · subst hik; simp [show k < (τ.arrs a).length by omega]
  · rw [if_neg hik, if_neg hik]; exact h.get i hi

/-- Fill in cell `k` of the buffer. -/
theorem store_filled {W : ℕ} {l : List ℕ} {τ : Env} {ie e : Expr} {k v : ℕ}
    (h : Filled "OB" "po" l τ) (hi : ie.evalB (W + 1) τ = some k) (he : e.evalB (W + 1) τ = some v)
    (hk : k < l.length) :
    ∃ τ', Run (W + 1) (.store "OB" ie e) τ τ' (1 + ie.size + e.size) ∧
      Filled "OB" "po" (l.set k v) τ' ∧ OFr τ τ' [] := by
  have hl := h.length_le
  refine ⟨τ.setArr "OB" k v, Run.store hi he (by omega), h.set hk v, ⟨fun y _ => rfl,
    fun b hb => by simp [Env.setArr, hb], by simp [Env.setArr], rfl, rfl⟩⟩

end Lax185574Proofs.CompRam
