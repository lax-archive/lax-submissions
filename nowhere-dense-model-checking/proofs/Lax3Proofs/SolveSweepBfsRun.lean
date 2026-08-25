import Lax3Proofs.SolveSweepBfs

/-!
# F6c12 (residual 4-i-a) — the frontier loop, and `PeelBfsIn`

`SolveSweepBfs` owns one centre's turn as a *program* (`bfsTurnCom`)
together with everything the turn must produce (§5), may spend (§3, §4)
and may touch (§6). What it leaves open is the induction over levels:
that the list the passes build **is** the ball, with no duplicate and
nothing extra. This file is that induction, and the `Run` accounting it
carries.

## What the induction says

The reached list is `lm[b .. b + bf.c)` with `b = lo["sw.i"]`; `BfsRow`
is the invariant that pins it — duplicate-free, laid out in `lm`, with
`co` its indicator on the carrier. One level pass expands the entries
below `bf.e` and appends the unvisited neighbours it finds, so

    set (row after k+1 passes) = set (row after k) ∪ N(expanded prefix)

which is `ball_succ` once the prefix is the previous ball. `bfsLevels`
runs that up to `2·R` passes; `bfsTurn_reached` reads off the two facts
the turn owes: the row enumerates `ball H (2R) u`, which is the cluster
(`cluster_eq_ball_peelSet`), and the *expanded* prefix is
`ball H (2R-1) u`, which is what `bfsExpanded_le_edgeTerm` prices.
Duplicate-freeness is not decoration: it is what makes `bf.c` the
cardinality `|X_u|` that `peelTurn`'s mass summand is stated at, rather
than a count of pushes.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax12.ColoringNumbers
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.WalkDistance

/-! ## §1 The reached row

The pass's whole state, as far as the frontier is concerned: a
duplicate-free list of vertices, laid out in `lm` from the row's anchor,
counted by `bf.c`, with `co` its indicator on the carrier. -/

/-- **The reached row.** `L` is the list the pass has pushed so far:
`bf.c` counts it, `lm[base .. base + |L|)` spells it out, `co` marks
exactly its members, and it repeats nothing. -/
def BfsRow (co lm : String) {N : ℕ} (base : ℕ) (c₀ l₀ : ℕ → ℕ) (L : List (Fin N))
    (σ : Env) : Prop :=
  σ.vars "bf.b" = base ∧
  σ.vars "bf.c" = L.length ∧
  L.Nodup ∧
  base + L.length ≤ (σ.arrs lm).length ∧
  (∀ (t : ℕ) (h : t < L.length), (σ.arrs lm).getD (base + t) 0 = ((L[t] : Fin N) : ℕ)) ∧
  N ≤ (σ.arrs co).length ∧
  (∀ v : Fin N, (σ.arrs co).getD (v : ℕ) 0 = if v ∈ L then 1 else 0) ∧
  (∀ v : ℕ, N ≤ v → (σ.arrs co).getD v 0 = c₀ v) ∧
  (∀ m : ℕ, m < base → (σ.arrs lm).getD m 0 = l₀ m)

theorem BfsRow.b {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) : σ.vars "bf.b" = base := h.1

theorem BfsRow.c {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) : σ.vars "bf.c" = L.length := h.2.1

theorem BfsRow.nodup {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) : L.Nodup := h.2.2.1

theorem BfsRow.fits {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) : base + L.length ≤ (σ.arrs lm).length := h.2.2.2.1

theorem BfsRow.cell {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) {t : ℕ} (ht : t < L.length) :
    (σ.arrs lm).getD (base + t) 0 = ((L[t] : Fin N) : ℕ) := h.2.2.2.2.1 t ht

theorem BfsRow.coLen {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) : N ≤ (σ.arrs co).length := h.2.2.2.2.2.1

theorem BfsRow.mark {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) (v : Fin N) :
    (σ.arrs co).getD (v : ℕ) 0 = if v ∈ L then 1 else 0 := h.2.2.2.2.2.2.1 v

/-- Outside the carrier the flag array is untouched: the pass writes
`co` only at vertex indices, which is what lets the clean-up be priced
against the carrier and still hand back the descriptor. -/
theorem BfsRow.outside {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ}
    {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) {v : ℕ} (hv : N ≤ v) :
    (σ.arrs co).getD v 0 = c₀ v := h.2.2.2.2.2.2.2.1 v hv

/-- Below the row's anchor the log is untouched: the earlier rows the
sweep has already written stay where they are, which is
`logPart_succ`'s `holdrow`. -/
theorem BfsRow.below {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ}
    {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) {m : ℕ} (hm : m < base) :
    (σ.arrs lm).getD m 0 = l₀ m := h.2.2.2.2.2.2.2.2 m hm

/-- The visited test `co[w] < 1` is exact against the row. -/
theorem BfsRow.lt_one_iff {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ}
    {L : List (Fin N)} {σ : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) (v : Fin N) :
    (σ.arrs co).getD (v : ℕ) 0 < 1 ↔ v ∉ L := by
  rw [h.mark v]
  by_cases hv : v ∈ L <;> simp [hv]

/-- The row transports along agreement on the two arrays and the two
scalars it reads. -/
theorem BfsRow.of_eq {co lm : String} {N base : ℕ} {c₀ l₀ : ℕ → ℕ}
    {L : List (Fin N)} {σ σ' : Env}
    (h : BfsRow co lm base c₀ l₀ L σ) (hb : σ'.vars "bf.b" = σ.vars "bf.b")
    (hc : σ'.vars "bf.c" = σ.vars "bf.c") (hco : σ'.arrs co = σ.arrs co)
    (hlm : σ'.arrs lm = σ.arrs lm) : BfsRow co lm base c₀ l₀ L σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨by rw [hb, h1], by rw [hc, h2], h3, by rw [hlm]; exact h4,
    by rw [hlm]; exact h5, by rw [hco]; exact h6, by rw [hco]; exact h7,
    by rw [hco]; exact h8, by rw [hlm]; exact h9⟩

/-- **A duplicate-free row of members of a set is no longer than the
set.** This is what turns the pass's count into `peelTurn`'s `|X_u|`. -/
theorem length_le_ncard_of_nodup {N : ℕ} {L : List (Fin N)} (hL : L.Nodup)
    {X : Set (Fin N)} (hX : ∀ z ∈ L, z ∈ X) : L.length ≤ X.ncard := by
  classical
  have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL
  have h2 : L.toFinset ⊆ X.toFinset := by
    intro z hz
    rw [Set.mem_toFinset]
    exact hX z (List.mem_toFinset.mp hz)
  have h3 : L.toFinset.card ≤ X.toFinset.card := Finset.card_le_card h2
  rw [h1] at h3
  rwa [Set.ncard_eq_toFinset_card' X]

/-- **A duplicate-free row that enumerates a set has the set's
cardinality** — the equality the mass summand is stated at. -/
theorem length_eq_ncard_of_nodup {N : ℕ} {L : List (Fin N)} (hL : L.Nodup)
    {X : Set (Fin N)} (hX : ∀ z : Fin N, z ∈ L ↔ z ∈ X) : L.length = X.ncard := by
  classical
  have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup hL
  have h2 : L.toFinset = X.toFinset := by
    ext z
    rw [List.mem_toFinset, Set.mem_toFinset]
    exact hX z
  rw [← h1, h2, Set.ncard_eq_toFinset_card' X]

/-! ## §2 One push

The pass's only writer. Everything it does is visible in the row it
extends and in the one `ca` cell a *marking* push may claim; the `20`
is the program text at the `Run` cost model (a store `1 + |i| + |e|`,
an assign `1 + |e|`, a branch `1 + |b| + `the branch taken), and the
plain push's `13` is taken at `20` throughout — the level passes'
`31`-per-cell is charged at the marking `38`, which is the figure `cbf`
is read off. -/

/-- **One push**, as a run. The row gains `w` at its end, `co` gains
its mark, and — in a marking push — `ca[w]` is claimed for the centre
exactly when it was still holding the sentinel. Nothing else moves:
one scalar (`bf.c`) and three arrays. -/
theorem bfsPush_run {ca co lm nn : String} (mark : Bool)
    (hcolm : co ≠ lm) (hcaco : ca ≠ co) (hcalm : ca ≠ lm) (hnnc : nn ≠ "bf.c")
    {N base B : ℕ} {c₀ l₀ : ℕ → ℕ} {L : List (Fin N)} {w : Fin N} {σ : Env}
    (hrow : BfsRow co lm base c₀ l₀ L σ)
    (hw : σ.vars "bf.w" = (w : ℕ))
    (hnew : w ∉ L)
    (hroom : base + L.length < (σ.arrs lm).length)
    (hcaLen : N ≤ (σ.arrs ca).length)
    (hcaVal : ∀ z : Fin N, (σ.arrs ca).getD (z : ℕ) 0 ≤ N)
    (hnnv : σ.vars nn = N)
    (hsv : σ.vars "sw.v" < N)
    (hNB : N < B) (hbcB : base + L.length + 1 < B) :
    ∃ σ', Run B (bfsPushCom ca co lm nn mark) σ σ' 20 ∧
      BfsRow co lm base c₀ l₀ (L ++ [w]) σ' ∧
      (∀ y, y ≠ "bf.c" → σ'.vars y = σ.vars y) ∧
      (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ'.arrs b = σ.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
      (mark = false → σ'.arrs ca = σ.arrs ca) ∧
      (∀ z : Fin N, (σ'.arrs ca).getD (z : ℕ) 0 =
        if mark = true ∧ z = w ∧ ¬ ((σ.arrs ca).getD (w : ℕ) 0 < N)
          then σ.vars "sw.v" else (σ.arrs ca).getD (z : ℕ) 0) := by
  classical
  obtain ⟨hb, hc, hnd, hfit, hcell, hcoL, hco, hcout, hlout⟩ := hrow
  have hwN : (w : ℕ) < N := w.isLt
  have h1B : 1 < B := by omega
  have hwB : σ.vars "bf.w" < B := by omega
  -- step 1: `co[w] := 1`
  have hr1 : Run B (.store co (.var "bf.w") (.lit 1)) σ
      (σ.setArr co (σ.vars "bf.w") 1) (1 + 1 + 1) := by
    have := Run.store (B := B) (σ := σ) (a := co) (i := .var "bf.w") (e := .lit 1)
      (evalB_var hwB) (evalB_lit h1B) (by omega)
    simpa using this
  set τ₁ : Env := σ.setArr co (σ.vars "bf.w") 1 with hτ₁
  have hτ₁v : ∀ y, τ₁.vars y = σ.vars y := fun _ => rfl
  have hτ₁lm : τ₁.arrs lm = σ.arrs lm := by rw [hτ₁, arrs_setArr, if_neg (Ne.symm hcolm)]
  have hτ₁ca : τ₁.arrs ca = σ.arrs ca := by rw [hτ₁, arrs_setArr, if_neg hcaco]
  -- step 2: `lm[b + c] := w`
  have hr2 : Run B (.store lm (.add (.var "bf.b") (.var "bf.c")) (.var "bf.w")) τ₁
      (τ₁.setArr lm (base + L.length) (σ.vars "bf.w")) (1 + 3 + 1) := by
    have hidx : (Expr.add (.var "bf.b") (.var "bf.c")).evalB B τ₁
        = some (base + L.length) := by
      have := evalB_bin (B := B) (op := .add)
        (evalB_var (x := "bf.b") (σ := τ₁) (by rw [hτ₁v, hb]; omega))
        (evalB_var (x := "bf.c") (σ := τ₁) (by rw [hτ₁v, hc]; omega))
        (by rw [hτ₁v, hτ₁v, hb, hc]; simpa using by omega)
      rw [hτ₁v, hτ₁v, hb, hc] at this
      simpa using this
    have := Run.store (B := B) (σ := τ₁) (a := lm) (i := .add (.var "bf.b") (.var "bf.c"))
      (e := .var "bf.w") hidx (evalB_var (by rw [hτ₁v]; omega)) (by rw [hτ₁lm]; omega)
    simpa using this
  set τ₂ : Env := τ₁.setArr lm (base + L.length) (σ.vars "bf.w") with hτ₂
  have hτ₂v : ∀ y, τ₂.vars y = σ.vars y := fun _ => rfl
  have hτ₂ca : τ₂.arrs ca = σ.arrs ca := by
    rw [hτ₂, arrs_setArr, if_neg hcalm, hτ₁ca]
  -- step 3: `c := c + 1`
  have hr3 : Run B (.assign "bf.c" (.add (.var "bf.c") (.lit 1))) τ₂
      (τ₂.setVar "bf.c" (L.length + 1)) (1 + 3) := by
    have hv : (Expr.add (.var "bf.c") (.lit 1)).evalB B τ₂ = some (L.length + 1) := by
      have := evalB_bin (B := B) (op := .add)
        (evalB_var (x := "bf.c") (σ := τ₂) (by rw [hτ₂v, hc]; omega))
        (evalB_lit (n := 1) (B := B) h1B) (by rw [hτ₂v, hc]; simpa using by omega)
      rw [hτ₂v, hc] at this
      simpa using this
    have := Run.assign (B := B) (σ := τ₂) (x := "bf.c") hv
    simpa using this
  set τ₃ : Env := τ₂.setVar "bf.c" (L.length + 1) with hτ₃
  have hτ₃ca : τ₃.arrs ca = σ.arrs ca := by rw [hτ₃, arrs_setVar, hτ₂ca]
  have hτ₃v : ∀ y, y ≠ "bf.c" → τ₃.vars y = σ.vars y := by
    intro y hy
    rw [hτ₃, vars_setVar, if_neg hy, hτ₂v]
  have hτ₃c : τ₃.vars "bf.c" = L.length + 1 := by rw [hτ₃, vars_setVar, if_pos rfl]
  -- the two array read-backs the row needs, once for all branches
  have hτ₃co : τ₃.arrs co = (σ.arrs co).set (w : ℕ) 1 := by
    rw [hτ₃, arrs_setVar, hτ₂, arrs_setArr, if_neg hcolm, hτ₁,
      arrs_setArr, if_pos rfl, hw]
  have hτ₃lm : τ₃.arrs lm = (σ.arrs lm).set (base + L.length) (w : ℕ) := by
    rw [hτ₃, arrs_setVar, hτ₂, arrs_setArr, if_pos rfl, hτ₁lm]
    rw [hw]
  have hτ₃oth : ∀ b, b ≠ co → b ≠ lm → τ₃.arrs b = σ.arrs b := by
    intro b h1 h2
    rw [hτ₃, arrs_setVar, hτ₂, arrs_setArr, if_neg h2, hτ₁, arrs_setArr, if_neg h1]
  have hlen : ∀ b, (τ₃.arrs b).length = (σ.arrs b).length := by
    intro b
    rw [hτ₃, arrs_setVar, hτ₂, length_arrs_setArr, hτ₁, length_arrs_setArr]
  -- the row, for any state agreeing with `τ₃` on `co`, `lm`, `bf.b`, `bf.c`
  have hrow' : ∀ ρ : Env, ρ.vars "bf.b" = base → ρ.vars "bf.c" = L.length + 1 →
      ρ.arrs co = (σ.arrs co).set (w : ℕ) 1 →
      ρ.arrs lm = (σ.arrs lm).set (base + L.length) (w : ℕ) →
      BfsRow co lm base c₀ l₀ (L ++ [w]) ρ := by
    intro ρ hrb hrc hrco hrlm
    have hndw : (L ++ [w]).Nodup :=
      ((List.perm_append_singleton w L).nodup_iff).mpr
        (List.nodup_cons.mpr ⟨hnew, hnd⟩)
    refine ⟨hrb, by rw [hrc]; simp, hndw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrlm, List.length_set, List.length_append]
      simpa using hroom
    · intro t ht
      rw [List.length_append, List.length_singleton] at ht
      rw [hrlm]
      rcases Nat.lt_or_ge t L.length with hlt | hge
      · rw [getD_set_of_ne (by omega), hcell t hlt]
        congr 1
        exact (List.getElem_append_left hlt).symm
      · have htl : t = L.length := by omega
        subst htl
        rw [getD_set_self (by omega)]
        have : (L ++ [w])[L.length] = w := by
          simp
        rw [this]
    · rw [hrco, List.length_set]; exact hcoL
    · intro v
      rw [hrco]
      by_cases hv : v = w
      · subst hv
        rw [getD_set_self (by omega), if_pos (by simp)]
      · rw [getD_set_of_ne (fun hcc => hv (Fin.val_injective hcc)), hco v]
        by_cases hvL : v ∈ L
        · rw [if_pos hvL, if_pos (by simp [hvL])]
        · rw [if_neg hvL, if_neg (by simp [hvL, hv])]
    · intro v hv
      rw [hrco, getD_set_of_ne (by have := w.isLt; omega)]
      exact hcout v hv
    · intro m hm
      rw [hrlm, getD_set_of_ne (by omega)]
      exact hlout m hm
  cases mark with
  | false =>
      refine ⟨τ₃, ?_, hrow' τ₃ (by rw [hτ₃v _ (by decide), hb]) hτ₃c hτ₃co hτ₃lm,
        hτ₃v, fun b h1 h2 _ => hτ₃oth b h1 h2, hlen, fun _ => hτ₃ca, ?_⟩
      · refine ((hr1.seq (hr2.seq (hr3.seq (Run.skip (B := B))))).mono ?_)
        omega
      · intro z; rw [hτ₃ca, if_neg (by simp)]
  | true =>
      -- the stamp test, evaluated
      have hcaw : (σ.arrs ca).getD (w : ℕ) 0 < B :=
        lt_of_le_of_lt (hcaVal w) hNB
      have htest : (Cond.lt (.get ca (.var "bf.w")) (.var nn)).evalB B τ₃
          = some (decide ((σ.arrs ca).getD (w : ℕ) 0 < N)) := by
        have hg : (Expr.get ca (.var "bf.w")).evalB B τ₃
            = some ((σ.arrs ca).getD (w : ℕ) 0) := by
          refine evalB_get (k := (w : ℕ)) ?_ ?_ hcaw
          · have := evalB_var (B := B) (x := "bf.w") (σ := τ₃)
              (by rw [hτ₃v _ (by decide), hw]; omega)
            rw [hτ₃v _ (by decide), hw] at this
            exact this
          · rw [hτ₃ca]; exact getElem?_of_lt (by omega)
        have hn : (Expr.var nn).evalB B τ₃ = some N := by
          have := evalB_var (B := B) (x := nn) (σ := τ₃)
            (by rw [hτ₃v _ hnnc, hnnv]; omega)
          rw [hτ₃v _ hnnc, hnnv] at this
          exact this
        rw [evalB_condLt hg hn]
      by_cases hclaim : (σ.arrs ca).getD (w : ℕ) 0 < N
      · refine ⟨τ₃, ?_, hrow' τ₃ (by rw [hτ₃v _ (by decide), hb]) hτ₃c hτ₃co hτ₃lm,
          hτ₃v, fun b h1 h2 _ => hτ₃oth b h1 h2, hlen, by simp, ?_⟩
        · refine ((hr1.seq (hr2.seq (hr3.seq
            (Run.ite_true (B := B) (by rw [htest, decide_eq_true hclaim]) (Run.skip))))).mono ?_)
          simp only [size_condLt, size_get, size_var, size_lit]
          omega
        · intro z; rw [hτ₃ca, if_neg (by rintro ⟨-, -, hcc⟩; exact hcc hclaim)]
      · refine ⟨τ₃.setArr ca (w : ℕ) (σ.vars "sw.v"), ?_, ?_, ?_, ?_, ?_, by simp, ?_⟩
        · have hst : Run B (.store ca (.var "bf.w") (.var "sw.v")) τ₃
              (τ₃.setArr ca (w : ℕ) (σ.vars "sw.v")) (1 + 1 + 1) := by
            have hi : (Expr.var "bf.w").evalB B τ₃ = some (w : ℕ) := by
              have := evalB_var (B := B) (x := "bf.w") (σ := τ₃)
                (by rw [hτ₃v _ (by decide), hw]; omega)
              rw [hτ₃v _ (by decide), hw] at this
              exact this
            have he : (Expr.var "sw.v").evalB B τ₃ = some (σ.vars "sw.v") := by
              have := evalB_var (B := B) (x := "sw.v") (σ := τ₃)
                (by rw [hτ₃v _ (by decide)]; omega)
              rw [hτ₃v _ (by decide)] at this
              exact this
            have := Run.store (B := B) (σ := τ₃) (a := ca) (i := .var "bf.w")
              (e := .var "sw.v") hi he (by rw [hτ₃ca]; omega)
            simpa using this
          refine ((hr1.seq (hr2.seq (hr3.seq
            (Run.ite_false (B := B) (by rw [htest, decide_eq_false hclaim]) hst)))).mono ?_)
          simp only [size_condLt, size_get, size_var]
          omega
        · refine hrow' _ ?_ ?_ ?_ ?_
          · rw [vars_setArr, hτ₃v _ (by decide), hb]
          · rw [vars_setArr, hτ₃c]
          · rw [arrs_setArr, if_neg (Ne.symm hcaco), hτ₃co]
          · rw [arrs_setArr, if_neg (Ne.symm hcalm), hτ₃lm]
        · intro y hy; rw [vars_setArr, hτ₃v y hy]
        · intro b h1 h2 h3
          rw [arrs_setArr, if_neg h3, hτ₃oth b h1 h2]
        · intro b; rw [length_arrs_setArr, hlen b]
        · intro z
          rw [arrs_setArr, if_pos rfl, hτ₃ca]
          by_cases hz : z = w
          · subst hz
            rw [getD_set_self (by omega), if_pos ⟨rfl, rfl, hclaim⟩]
          · rw [getD_set_of_ne (fun hcc => hz (Fin.val_injective hcc)),
              if_neg (by simp [hz])]

/-! ## §3 The marks, and the names

`CaRow` is the assignment array as the pass leaves it: the entry
contents `g`, with the centre `uval` written into the cells of `M` that
were still holding the sentinel. It is stated without an `if` so that
its two clauses *are* `ctrPart_succ_of_ball`'s `hhit` and `hkeep`. -/

/-- **The assignment array, part-claimed.** `g` is what the cells held
when the turn began; `M` is the set the pass has claimed so far. -/
def CaRow (ca : String) {N : ℕ} (g : Fin N → ℕ) (uval : ℕ) (M : Set (Fin N))
    (σ : Env) : Prop :=
  N ≤ (σ.arrs ca).length ∧
  (∀ z : Fin N, z ∈ M → ¬ (g z < N) → (σ.arrs ca).getD (z : ℕ) 0 = uval) ∧
  (∀ z : Fin N, (z ∉ M ∨ g z < N) → (σ.arrs ca).getD (z : ℕ) 0 = g z)

theorem CaRow.of_eq {ca : String} {N : ℕ} {g : Fin N → ℕ} {uval : ℕ}
    {M : Set (Fin N)} {σ σ' : Env} (h : CaRow ca g uval M σ)
    (hca : σ'.arrs ca = σ.arrs ca) : CaRow ca g uval M σ' := by
  rw [CaRow, hca]; exact h

/-- Every cell is at most `N` when the entry contents were, which is the
sharpening the stamp test needs (Hazard 5). -/
theorem CaRow.le {ca : String} {N : ℕ} {g : Fin N → ℕ} {uval : ℕ}
    {M : Set (Fin N)} {σ : Env} (h : CaRow ca g uval M σ) (hg : ∀ z, g z ≤ N)
    (hu : uval < N) (z : Fin N) : (σ.arrs ca).getD (z : ℕ) 0 ≤ N := by
  classical
  by_cases hz : z ∈ M
  · by_cases hgz : g z < N
    · rw [h.2.2 z (Or.inr hgz)]; exact hg z
    · rw [h.2.1 z hz hgz]; omega
  · rw [h.2.2 z (Or.inl hz)]; exact hg z

/-- **The pass's ten scratch scalars are not the carrier cell.** The
stamp test reads `nn`, and every loop must hand it back; bundling the
ten disequalities keeps the lemma statements readable. `arenaScalars_ne`
supplies them for `(arenaNames j).nN`. -/
def NnFresh (nn : String) : Prop :=
  nn ≠ "bf.b" ∧ nn ≠ "bf.c" ∧ nn ≠ "bf.h" ∧ nn ≠ "bf.e" ∧ nn ≠ "bf.v" ∧
    nn ≠ "bf.o" ∧ nn ≠ "bf.n" ∧ nn ≠ "bf.t" ∧ nn ≠ "bf.w" ∧ nn ≠ "bf.k"

/-- **The seven arrays the turn names are pairwise distinct** where it
matters: the three it writes inside a level pass (`ca`, `co`, `lm`), the
offset row `lo`, and the three adjacency arrays it only reads. -/
def BfsNames (ca co ao aj dg lo lm : String) : Prop :=
  co ≠ lm ∧ ca ≠ co ∧ ca ≠ lm ∧ ca ≠ lo ∧ co ≠ lo ∧ lm ≠ lo ∧
    ao ≠ ca ∧ ao ≠ co ∧ ao ≠ lm ∧ ao ≠ lo ∧
    aj ≠ ca ∧ aj ≠ co ∧ aj ≠ lm ∧ aj ≠ lo ∧
    dg ≠ ca ∧ dg ≠ co ∧ dg ≠ lm ∧ dg ≠ lo

/-- **There is room for one more push.** A duplicate-free row inside the
capacity set is strictly shorter than it as long as the set still holds
something unpushed — which is why no allocation clause beyond
`base + |X| ≤ |lm|` is ever needed. -/
theorem push_room {N : ℕ} {L : List (Fin N)} (hnd : L.Nodup) {X : Set (Fin N)}
    (hLX : ∀ z ∈ L, z ∈ X) {w : Fin N} (hwX : w ∈ X) (hnew : w ∉ L) :
    L.length < X.ncard := by
  classical
  have hndw : (L ++ [w]).Nodup :=
    ((List.perm_append_singleton w L).nodup_iff).mpr
      (List.nodup_cons.mpr ⟨hnew, hnd⟩)
  have := length_le_ncard_of_nodup hndw (X := X) (by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact hLX z h
    · rw [List.mem_singleton.mp h]; exact hwX)
  simpa using this

/-! ## §4 One vertex's expansion

`bfsScanCom` reads the live row of `bf.v` and pushes every neighbour it
finds unvisited. The loop is `Spec.forRangeZero`'s shape exactly — a
counter against a scalar bound — so the cost is `(34 + 4)·d + 6` and the
two prologue reads bring it to `38·d + 12`. The `34` is the body: the
neighbour read (`5`), the visited test with the marking push (`25`), the
cursor bump (`4`). -/

/-- **The scan's loop invariant.** The row so far, the marks so far, and
the running identification of the row with "what `L₀` had plus the first
`bf.t` slots of the row of `bf.v`". The last three clauses are the frame
against the state the scan started in. -/
def ScanInv (ca co lm : String) {N : ℕ} (base : ℕ) (c₀ l₀ : ℕ → ℕ) (g : Fin N → ℕ)
    (uval : ℕ) (mark : Bool) (M X : Set (Fin N)) (f : ℕ → Fin N)
    (L₀ : List (Fin N)) (o n : ℕ) (σ₀ σ : Env) : Prop :=
  ∃ L : List (Fin N),
    BfsRow co lm base c₀ l₀ L σ ∧
    CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L} else M) σ ∧
    (∀ z ∈ L, z ∈ X) ∧ (∃ D, L = L₀ ++ D) ∧
    (∀ z : Fin N, z ∈ L ↔ z ∈ L₀ ∨ ∃ s, s < σ.vars "bf.t" ∧ f s = z) ∧
    σ.vars "bf.o" = o ∧ σ.vars "bf.n" = n ∧ σ.vars "bf.t" ≤ n ∧
    (∀ y, y ≠ "bf.c" → y ≠ "bf.o" → y ≠ "bf.n" → y ≠ "bf.t" → y ≠ "bf.w" →
      σ.vars y = σ₀.vars y) ∧
    (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ.arrs b = σ₀.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ₀.arrs b).length)

set_option maxHeartbeats 1000000 in
/-- **One vertex's expansion, as a run.** From the row `L₀` and the
marks `M`, reading the live row of `v` — offset `o`, length `n`, entries
`f` — the scan appends exactly the unvisited entries, marks them iff the
pass is a marking one, and costs `38·n + 12`. Duplicate-freeness is kept
because a push happens only where `co` reads `0`. -/
theorem bfsScan_run {ca co ao aj dg lo lm nn : String} (mark : Bool)
    (hnm : BfsNames ca co ao aj dg lo lm) (hnn : NnFresh nn)
    {N base B o n : ℕ} {c₀ l₀ : ℕ → ℕ} {g : Fin N → ℕ} {uval : ℕ} {f : ℕ → Fin N}
    {X M : Set (Fin N)} {L₀ : List (Fin N)} {σ₀ : Env} {v : Fin N}
    (hNB : N < B) (honB : o + n < B) (hcapB : base + X.ncard < B)
    (hrow : BfsRow co lm base c₀ l₀ L₀ σ₀) (hca : CaRow ca g uval M σ₀)
    (hgN : ∀ z, g z ≤ N) (huN : uval < N)
    (hLX : ∀ z ∈ L₀, z ∈ X) (hfX : ∀ s, s < n → f s ∈ X)
    (hcap : base + X.ncard ≤ (σ₀.arrs lm).length)
    (hML : ∀ z, z ∈ M → z ∈ L₀)
    (hMmark : mark = true → ∀ z, z ∈ L₀ → z ∈ M)
    (hslot : ∀ s, s < n → (σ₀.arrs aj).getD (o + s) 0 = ((f s : Fin N) : ℕ))
    (hajlen : o + n ≤ (σ₀.arrs aj).length)
    (hv : σ₀.vars "bf.v" = (v : ℕ))
    (haoV : (σ₀.arrs ao).getD (v : ℕ) 0 = o) (haoLen : (v : ℕ) < (σ₀.arrs ao).length)
    (hdgV : (σ₀.arrs dg).getD (v : ℕ) 0 = n) (hdgLen : (v : ℕ) < (σ₀.arrs dg).length)
    (hnnv : σ₀.vars nn = N) (hsv : σ₀.vars "sw.v" = uval) :
    ∃ (σ' : Env) (L' : List (Fin N)),
      Run B (bfsScanCom ca co ao aj dg lm nn mark) σ₀ σ' (38 * n + 12) ∧
      BfsRow co lm base c₀ l₀ L' σ' ∧
      CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L'} else M) σ' ∧
      (∀ z ∈ L', z ∈ X) ∧ (∃ D, L' = L₀ ++ D) ∧
      (∀ z : Fin N, z ∈ L' ↔ z ∈ L₀ ∨ ∃ s, s < n ∧ f s = z) ∧
      (∀ y, y ≠ "bf.c" → y ≠ "bf.o" → y ≠ "bf.n" → y ≠ "bf.t" → y ≠ "bf.w" →
        σ'.vars y = σ₀.vars y) ∧
      (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ'.arrs b = σ₀.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ₀.arrs b).length) := by
  classical
  obtain ⟨hcolm, hcaco, hcalm, -, -, -, -, haoco, haolm, -,
    hajca, hajco, hajlm, -, hdgca, hdgco, hdglm, -⟩ := hnm
  obtain ⟨-, hnc, -, -, -, hno, hnn2, hnt, hnw, -⟩ := hnn
  have hvN : (v : ℕ) < N := v.isLt
  have hnB : n < B := by omega
  have hoB : o < B := by omega
  have h1B : 1 < B := by omega
  -- the two prologue reads
  have hr1 : Run B (.assign "bf.o" (.get ao (.var "bf.v"))) σ₀
      (σ₀.setVar "bf.o" o) (1 + 2) := by
    have hg : (Expr.get ao (.var "bf.v")).evalB B σ₀ = some o := by
      refine evalB_get (k := (v : ℕ)) ?_ ?_ hoB
      · have := evalB_var (B := B) (x := "bf.v") (σ := σ₀) (by rw [hv]; omega)
        rw [hv] at this; exact this
      · rw [getElem?_of_lt haoLen, haoV]
    have := Run.assign (B := B) (σ := σ₀) (x := "bf.o") hg
    simpa using this
  set ρ₁ : Env := σ₀.setVar "bf.o" o with hρ₁
  have hr2 : Run B (.assign "bf.n" (.get dg (.var "bf.v"))) ρ₁
      (ρ₁.setVar "bf.n" n) (1 + 2) := by
    have hg : (Expr.get dg (.var "bf.v")).evalB B ρ₁ = some n := by
      refine evalB_get (k := (v : ℕ)) ?_ ?_ hnB
      · have := evalB_var (B := B) (x := "bf.v") (σ := ρ₁)
          (by rw [hρ₁, vars_setVar, if_neg (by decide), hv]; omega)
        rw [hρ₁, vars_setVar, if_neg (by decide), hv] at this
        exact this
      · rw [hρ₁, arrs_setVar, getElem?_of_lt hdgLen, hdgV]
    have := Run.assign (B := B) (σ := ρ₁) (x := "bf.n") hg
    simpa using this
  set ρ : Env := ρ₁.setVar "bf.n" n with hρ
  have hρv : ∀ y, y ≠ "bf.o" → y ≠ "bf.n" → ρ.vars y = σ₀.vars y := by
    intro y h1 h2
    rw [hρ, vars_setVar, if_neg h2, hρ₁, vars_setVar, if_neg h1]
  have hρa : ∀ b, ρ.arrs b = σ₀.arrs b := by
    intro b; rw [hρ, arrs_setVar, hρ₁, arrs_setVar]
  -- the body of the scan
  have hbody : Spec B
      (fun σ => ScanInv ca co lm base c₀ l₀ g uval mark M X f L₀ o n σ₀ σ ∧
        σ.vars "bf.t" < n)
      (.seq (.assign "bf.w" (.get aj (.add (.var "bf.o") (.var "bf.t"))))
        (.seq (.ite (.lt (.get co (.var "bf.w")) (.lit 1))
                (bfsPushCom ca co lm nn mark) .skip)
          (.assign "bf.t" (.add (.var "bf.t") (.lit 1)))))
      (fun σ σ' => ScanInv ca co lm base c₀ l₀ g uval mark M X f L₀ o n σ₀ σ' ∧
        σ'.vars "bf.t" = σ.vars "bf.t" + 1) 34 := by
    rintro σ ⟨⟨L, hrowL, hcaL, hLX', hpre, hmem, hoo, hnn3, htn, hfrv, hfra, hfrl⟩,
      hlt⟩
    have hajσ : σ.arrs aj = σ₀.arrs aj := hfra aj hajco hajlm hajca
    have hnnσ : σ.vars nn = N := by rw [hfrv nn hnc hno hnn2 hnt hnw, hnnv]
    have hsvσ : σ.vars "sw.v" = uval := by
      rw [hfrv "sw.v" (by decide) (by decide) (by decide) (by decide) (by decide), hsv]
    have hlmσ : (σ.arrs lm).length = (σ₀.arrs lm).length := hfrl lm
    -- read the neighbour
    have hwval : (σ.arrs aj).getD (o + σ.vars "bf.t") 0 = ((f (σ.vars "bf.t") : Fin N) : ℕ) := by
      rw [hajσ]; exact hslot _ hlt
    have hr : Run B (.assign "bf.w" (.get aj (.add (.var "bf.o") (.var "bf.t")))) σ
        (σ.setVar "bf.w" ((f (σ.vars "bf.t") : Fin N) : ℕ)) (1 + 4) := by
      have hidx : (Expr.add (.var "bf.o") (.var "bf.t")).evalB B σ
          = some (o + σ.vars "bf.t") := by
        have := evalB_bin (B := B) (op := .add)
          (evalB_var (x := "bf.o") (σ := σ) (by rw [hoo]; omega))
          (evalB_var (x := "bf.t") (σ := σ) (by omega))
          (show σ.vars "bf.o" + σ.vars "bf.t" < B by rw [hoo]; omega)
        rw [hoo] at this
        simpa using this
      have hg : (Expr.get aj (.add (.var "bf.o") (.var "bf.t"))).evalB B σ
          = some ((f (σ.vars "bf.t") : Fin N) : ℕ) := by
        refine evalB_get hidx ?_ (by have := (f (σ.vars "bf.t")).isLt; omega)
        rw [← hwval]
        exact getElem?_of_lt (by rw [hajσ]; omega)
      have := Run.assign (B := B) (σ := σ) (x := "bf.w") hg
      simpa using this
    set w : Fin N := f (σ.vars "bf.t") with hwdef
    set σ₁ : Env := σ.setVar "bf.w" ((w : Fin N) : ℕ) with hσ₁
    have hσ₁v : ∀ y, y ≠ "bf.w" → σ₁.vars y = σ.vars y := by
      intro y hy; rw [hσ₁, vars_setVar, if_neg hy]
    have hσ₁a : ∀ b, σ₁.arrs b = σ.arrs b := by intro b; rw [hσ₁, arrs_setVar]
    have hrowσ₁ : BfsRow co lm base c₀ l₀ L σ₁ :=
      hrowL.of_eq (hσ₁v _ (by decide)) (hσ₁v _ (by decide)) (hσ₁a co) (hσ₁a lm)
    have hcaσ₁ : CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L} else M) σ₁ :=
      hcaL.of_eq (hσ₁a ca)
    have hML' : ∀ z, z ∈ M → z ∈ L := by
      intro z hz
      obtain ⟨D, rfl⟩ := hpre
      exact List.mem_append.mpr (Or.inl (hML z hz))
    -- the visited test
    have htest : (Cond.lt (.get co (.var "bf.w")) (.lit 1)).evalB B σ₁
        = some (decide (w ∉ L)) := by
      have hco1 : (σ₁.arrs co).getD ((w : Fin N) : ℕ) 0 < B := by
        rw [hrowσ₁.mark w]; split <;> omega
      have hg : (Expr.get co (.var "bf.w")).evalB B σ₁
          = some ((σ₁.arrs co).getD ((w : Fin N) : ℕ) 0) := by
        refine evalB_get (k := ((w : Fin N) : ℕ)) ?_ ?_ hco1
        · have := evalB_var (B := B) (x := "bf.w") (σ := σ₁)
            (by rw [hσ₁, vars_setVar, if_pos rfl]; have := w.isLt; omega)
          rw [hσ₁, vars_setVar, if_pos rfl] at this
          exact this
        · exact getElem?_of_lt (lt_of_lt_of_le w.isLt hrowσ₁.coLen)
      rw [evalB_condLt hg (evalB_lit h1B)]
      congr 1
      by_cases hwL : w ∈ L
      · rw [decide_eq_false (by rw [hrowσ₁.lt_one_iff w]; simpa using hwL),
          decide_eq_false (by simpa using hwL)]
      · rw [decide_eq_true (by rw [hrowσ₁.lt_one_iff w]; exact hwL),
          decide_eq_true hwL]
    -- the two branches, packaged as one existential over the resulting row
    have hbranch : ∃ (σ₂ : Env) (L' : List (Fin N)),
        Run B (.ite (.lt (.get co (.var "bf.w")) (.lit 1))
            (bfsPushCom ca co lm nn mark) .skip) σ₁ σ₂ 25 ∧
        BfsRow co lm base c₀ l₀ L' σ₂ ∧
        CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L'} else M) σ₂ ∧
        (∀ z : Fin N, z ∈ L' ↔ z ∈ L ∨ z = w) ∧
        (∃ D, L' = L ++ D) ∧
        (∀ y, y ≠ "bf.c" → σ₂.vars y = σ₁.vars y) ∧
        (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ₂.arrs b = σ₁.arrs b) ∧
        (∀ b, (σ₂.arrs b).length = (σ₁.arrs b).length) := by
      by_cases hwL : w ∈ L
      · refine ⟨σ₁, L, ?_, hrowσ₁, hcaσ₁, ?_, ⟨[], by simp⟩,
          fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩
        · refine (Run.ite_false (B := B) ?_ (Run.skip)).mono ?_
          · rw [htest, decide_eq_false (by simpa using hwL)]
          · simp only [size_condLt, size_get, size_var, size_lit]
            omega
        · intro z
          constructor
          · exact fun h => Or.inl h
          · rintro (h | rfl)
            · exact h
            · exact hwL
      · -- the push
        have hwM : w ∉ (if mark = true then M ∪ {z | z ∈ L} else M) := by
          by_cases hm : mark = true
          · rw [if_pos hm]
            rintro (h | h)
            · exact hwL (hML' w h)
            · exact hwL h
          · rw [if_neg hm]
            exact fun h => hwL (hML' w h)
        have hcaw : (σ₁.arrs ca).getD ((w : Fin N) : ℕ) 0 = g w :=
          hcaσ₁.2.2 w (Or.inl hwM)
        have hroom : base + L.length < (σ₁.arrs lm).length := by
          have := push_room hrowL.nodup hLX' (hfX _ hlt) hwL
          rw [hσ₁a lm]
          omega
        obtain ⟨σ₂, hrun, hrow₂, hv₂, ha₂, hl₂, hmk₂, hca₂⟩ :=
          bfsPush_run (ca := ca) (co := co) (lm := lm) (nn := nn) mark hcolm hcaco
            hcalm hnc (N := N) (base := base) (B := B) (L := L) (w := w) (σ := σ₁)
            hrowσ₁ (by rw [hσ₁, vars_setVar, if_pos rfl]) hwL hroom
            hcaσ₁.1 (fun z => hcaσ₁.le hgN huN z)
            (by rw [hσ₁v nn hnw, hnnσ])
            (by rw [hσ₁v "sw.v" (by decide), hsvσ]; exact huN)
            hNB (by
              have := push_room hrowL.nodup hLX' (hfX _ hlt) hwL
              omega)
        refine ⟨σ₂, L ++ [w], ?_, hrow₂, ?_, ?_, ⟨[w], rfl⟩, hv₂, ha₂, hl₂⟩
        · refine (Run.ite_true (B := B) ?_ hrun).mono ?_
          · rw [htest, decide_eq_true hwL]
          · simp only [size_condLt, size_get, size_var, size_lit]
            omega
        · -- the marks after the push
          have hcaw' : ∀ hg : ¬ (g w < N),
              ¬ ((σ₁.arrs ca).getD ((w : Fin N) : ℕ) 0 < N) := by
            intro hg; rw [hcaw]; exact hg
          refine ⟨by rw [hl₂ ca]; exact hcaσ₁.1, ?_, ?_⟩
          · intro z hz hgz
            rw [hca₂ z]
            by_cases hzw : z = w
            · have hmarkt : mark = true := by
                by_contra hm
                simp only [Bool.not_eq_true] at hm
                rw [if_neg (by simp [hm])] at hz
                exact hwL (hzw ▸ hML' z hz)
              have hgw : ¬ (g w < N) := by rw [← hzw]; exact hgz
              rw [if_pos ⟨hmarkt, hzw, hcaw' hgw⟩, hσ₁v "sw.v" (by decide), hsvσ]
            · rw [if_neg (by simp [hzw])]
              refine hcaσ₁.2.1 z ?_ hgz
              by_cases hm : mark = true
              · rw [if_pos hm] at hz ⊢
                rcases hz with h | h
                · exact Or.inl h
                · refine Or.inr ?_
                  simp only [Set.mem_setOf_eq] at h ⊢
                  rcases List.mem_append.mp h with h' | h'
                  · exact h'
                  · exact absurd (List.mem_singleton.mp h') hzw
              · rw [if_neg hm] at hz ⊢; exact hz
          · intro z hz
            rw [hca₂ z]
            by_cases hzw : z = w
            · have hcond : ¬ (mark = true ∧ z = w ∧
                  ¬ ((σ₁.arrs ca).getD ((w : Fin N) : ℕ) 0 < N)) := by
                rintro ⟨hmt, -, hcc⟩
                refine hcc ?_
                rw [hcaw]
                rcases hz with h | h
                · exact absurd (by
                    rw [if_pos hmt]
                    exact Or.inr (by
                      simp only [Set.mem_setOf_eq]
                      exact List.mem_append.mpr (Or.inr (by simp [hzw])))) h
                · rw [← hzw]; exact h
              rw [if_neg hcond, hzw, hcaw]
            · rw [if_neg (by simp [hzw])]
              refine hcaσ₁.2.2 z ?_
              rcases hz with h | h
              · refine Or.inl ?_
                by_cases hm : mark = true
                · rw [if_pos hm] at h ⊢
                  intro hcc
                  refine h ?_
                  rcases hcc with h' | h'
                  · exact Or.inl h'
                  · exact Or.inr (List.mem_append.mpr (Or.inl h'))
                · rw [if_neg hm] at h ⊢; exact h
              · exact Or.inr h
        · intro z
          constructor
          · intro h
            rcases List.mem_append.mp h with h' | h'
            · exact Or.inl h'
            · exact Or.inr (List.mem_singleton.mp h')
          · rintro (h | rfl)
            · exact List.mem_append.mpr (Or.inl h)
            · exact List.mem_append.mpr (Or.inr (by simp))
    obtain ⟨σ₂, L', hrun₂, hrow₂, hca₂, hmem₂, hpre₂, hv₂, ha₂, hl₂⟩ := hbranch
    -- the cursor bump
    have hr₃ : Run B (.assign "bf.t" (.add (.var "bf.t") (.lit 1))) σ₂
        (σ₂.setVar "bf.t" (σ.vars "bf.t" + 1)) (1 + 3) := by
      have hval : (Expr.add (.var "bf.t") (.lit 1)).evalB B σ₂
          = some (σ.vars "bf.t" + 1) := by
        have ht2 : σ₂.vars "bf.t" = σ.vars "bf.t" := by
          rw [hv₂ "bf.t" (by decide), hσ₁v "bf.t" (by decide)]
        have := evalB_bin (B := B) (op := .add)
          (evalB_var (x := "bf.t") (σ := σ₂) (by rw [ht2]; omega))
          (evalB_lit (n := 1) (B := B) h1B) (by rw [ht2]; simpa using by omega)
        rw [ht2] at this
        simpa using this
      have := Run.assign (B := B) (σ := σ₂) (x := "bf.t") hval
      simpa using this
    refine ⟨σ₂.setVar "bf.t" (σ.vars "bf.t" + 1), (hr.seq (hrun₂.seq hr₃)).mono (by omega),
      ⟨L', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [vars_setVar, if_pos rfl]⟩
    · exact hrow₂.of_eq (by rw [vars_setVar, if_neg (by decide)])
        (by rw [vars_setVar, if_neg (by decide)]) (by rw [arrs_setVar])
        (by rw [arrs_setVar])
    · exact hca₂.of_eq (by rw [arrs_setVar])
    · intro z hz
      rcases hmem₂ z |>.mp hz with h | rfl
      · exact hLX' z h
      · exact hfX _ hlt
    · obtain ⟨D, hD⟩ := hpre
      obtain ⟨D', hD'⟩ := hpre₂
      exact ⟨D ++ D', by rw [hD', hD, List.append_assoc]⟩
    · intro z
      rw [vars_setVar, if_pos rfl, hmem₂ z, hmem z]
      constructor
      · rintro ((h | ⟨s, hs, hfs⟩) | rfl)
        · exact Or.inl h
        · exact Or.inr ⟨s, by omega, hfs⟩
        · exact Or.inr ⟨σ.vars "bf.t", by omega, rfl⟩
      · rintro (h | ⟨s, hs, hfs⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_ge s (σ.vars "bf.t") with h' | h'
          · exact Or.inl (Or.inr ⟨s, h', hfs⟩)
          · have : s = σ.vars "bf.t" := by omega
            subst this
            exact Or.inr hfs.symm
    · rw [vars_setVar, if_neg (by decide), hv₂ _ (by decide), hσ₁v _ (by decide), hoo]
    · rw [vars_setVar, if_neg (by decide), hv₂ _ (by decide), hσ₁v _ (by decide), hnn3]
    · rw [vars_setVar, if_pos rfl]; omega
    · intro y h1 h2 h3 h4 h5
      rw [vars_setVar, if_neg h4, hv₂ y h1, hσ₁v y h5]
      exact hfrv y h1 h2 h3 h4 h5
    · intro b h1 h2 h3
      rw [arrs_setVar, ha₂ b h1 h2 h3, hσ₁a b]
      exact hfra b h1 h2 h3
    · intro b
      rw [arrs_setVar, hl₂ b, hσ₁a b]
      exact hfrl b
  -- the loop
  have hloop := Spec.forRangeZero (B := B) "bf.t" "bf.n"
    (ScanInv ca co lm base c₀ l₀ g uval mark M X f L₀ o n σ₀) n 34 hnB
    (fun _ hσ => by obtain ⟨-, -, -, -, -, -, -, -, h, -, -, -⟩ := hσ; exact h)
    (fun _ hσ => by obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -⟩ := hσ; exact h)
    hbody
  have hentry : ScanInv ca co lm base c₀ l₀ g uval mark M X f L₀ o n σ₀
      ((ρ.setVar "bf.t" 0)) := by
    refine ⟨L₀, ?_, ?_, hLX, ⟨[], by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hrow.of_eq (by rw [vars_setVar, if_neg (by decide), hρv _ (by decide) (by decide)])
        (by rw [vars_setVar, if_neg (by decide), hρv _ (by decide) (by decide)])
        (by rw [arrs_setVar, hρa]) (by rw [arrs_setVar, hρa])
    · have hMeq : (if mark = true then M ∪ {z | z ∈ L₀} else M) = M := by
        by_cases hm : mark = true
        · rw [if_pos hm]
          ext z
          exact ⟨fun h => h.elim id (fun h' => hMmark hm z h'), fun h => Or.inl h⟩
        · rw [if_neg hm]
      rw [hMeq]
      exact hca.of_eq (by rw [arrs_setVar, hρa])
    · intro z
      rw [vars_setVar, if_pos rfl]
      exact ⟨fun h => Or.inl h, fun h => h.elim id (fun ⟨_, hs, _⟩ => absurd hs (by omega))⟩
    · rw [vars_setVar, if_neg (by decide), hρ, vars_setVar, if_neg (by decide),
        hρ₁, vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_neg (by decide), hρ, vars_setVar, if_pos rfl]
    · rw [vars_setVar, if_pos rfl]; omega
    · intro y h1 h2 h3 h4 h5
      rw [vars_setVar, if_neg h4, hρv y h2 h3]
    · intro b _ _ _; rw [arrs_setVar, hρa]
    · intro b; rw [arrs_setVar, hρa]
  obtain ⟨σ', hrunL, ⟨L', hrowL, hcaL, hLX', hpre', hmem', hoo', hnn', htn', hfrv',
    hfra', hfrl'⟩, htN⟩ := hloop.run hentry
  refine ⟨σ', L', ?_, hrowL, hcaL, hLX', hpre', ?_, ?_, ?_, ?_⟩
  · refine ((hr1.seq (hr2.seq hrunL)).mono ?_)
    omega
  · intro z; rw [hmem' z, htN]
  · exact hfrv'
  · exact hfra'
  · exact hfrl'

/-! ## §5 One level pass

The frontier loop. Its cost is **not** uniform per turn — a vertex costs
its own live degree — so the loop rule used is `Run.while_potential` at
the potential

    Φ σ = Σ_{v ∈ L₀.drop bf.h} (25 + 38·deg v),

the bill for the vertices still to be expanded. One turn drops exactly
the head term, which is the turn's own cost `4 + (38·deg v + 21)`; the
loop therefore costs `Φ` at entry plus the failing test, and the pass
`Φ + 6`. That is the `6`-per-pass of `abf` and the `25`/`38` of `bbf`
and `cbf`, all three read off the program text. -/

/-- **The adjacency region, as rows.** What the scan needs of `ao`,
`aj` and `dg`: every vertex's live row is `deg v` slots long at offset
`ao[v]`, they are in range and below the word bound, and they enumerate
exactly `Nb v`. `DelAdjSt` supplies it. -/
def AdjRows (ao aj dg : String) {N : ℕ} (Nb : Fin N → Fin N → Prop)
    (deg : Fin N → ℕ) (B : ℕ) (σ : Env) : Prop :=
  N ≤ (σ.arrs ao).length ∧ N ≤ (σ.arrs dg).length ∧
  ∀ v : Fin N, ∃ (ov : ℕ) (fv : ℕ → Fin N),
    (σ.arrs ao).getD (v : ℕ) 0 = ov ∧ (σ.arrs dg).getD (v : ℕ) 0 = deg v ∧
    ov + deg v ≤ (σ.arrs aj).length ∧ ov + deg v < B ∧
    (∀ s, s < deg v → (σ.arrs aj).getD (ov + s) 0 = ((fv s : Fin N) : ℕ)) ∧
    (∀ z : Fin N, (∃ s, s < deg v ∧ fv s = z) ↔ Nb v z)

theorem AdjRows.of_eq {ao aj dg : String} {N : ℕ} {Nb : Fin N → Fin N → Prop}
    {deg : Fin N → ℕ} {B : ℕ} {σ σ' : Env} (h : AdjRows ao aj dg Nb deg B σ)
    (hao : σ'.arrs ao = σ.arrs ao) (haj : σ'.arrs aj = σ.arrs aj)
    (hdg : σ'.arrs dg = σ.arrs dg) : AdjRows ao aj dg Nb deg B σ' := by
  rw [AdjRows, hao, haj, hdg]; exact h

/-- An entry of a list at or after the drop point is in the drop. -/
theorem getElem_mem_drop {α : Type*} (l : List α) {h₀ s : ℕ} (h1 : h₀ ≤ s)
    (h2 : s < l.length) : l[s] ∈ l.drop h₀ := by
  refine List.mem_of_getElem? (i := s - h₀) ?_
  rw [List.getElem?_drop]
  have : h₀ + (s - h₀) = s := by omega
  rw [this, List.getElem?_eq_getElem h2]

/-- The potential's head term splits off. -/
theorem drop_map_sum_succ {α : Type*} (l : List α) (fn : α → ℕ) {s : ℕ}
    (hs : s < l.length) :
    ((l.drop s).map fn).sum = fn l[s] + ((l.drop (s + 1)).map fn).sum := by
  rw [List.drop_eq_getElem_cons hs, List.map_cons, List.sum_cons]

/-- **The level pass's loop invariant.** The row so far, the marks so
far, and the identification of the row with `L₀` together with the
neighbourhoods of the entries the head has passed. -/
def LevelInv (ca co lm : String) {N : ℕ} (base : ℕ) (c₀ l₀ : ℕ → ℕ) (g : Fin N → ℕ)
    (uval : ℕ) (mark : Bool) (M X : Set (Fin N)) (Nb : Fin N → Fin N → Prop)
    (L₀ : List (Fin N)) (h₀ : ℕ) (σ₀ σ : Env) : Prop :=
  ∃ L : List (Fin N),
    BfsRow co lm base c₀ l₀ L σ ∧
    CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L} else M) σ ∧
    (∀ z ∈ L, z ∈ X) ∧ (∃ D, L = L₀ ++ D) ∧
    (∀ z : Fin N, z ∈ L ↔ z ∈ L₀ ∨
      ∃ v ∈ (L₀.drop h₀).take (σ.vars "bf.h" - h₀), Nb v z) ∧
    h₀ ≤ σ.vars "bf.h" ∧ σ.vars "bf.h" ≤ L₀.length ∧
    σ.vars "bf.e" = L₀.length ∧
    (∀ y, y ≠ "bf.c" → y ≠ "bf.o" → y ≠ "bf.n" → y ≠ "bf.t" → y ≠ "bf.w" →
      y ≠ "bf.e" → y ≠ "bf.h" → y ≠ "bf.v" → σ.vars y = σ₀.vars y) ∧
    (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ.arrs b = σ₀.arrs b) ∧
    (∀ b, (σ.arrs b).length = (σ₀.arrs b).length)

set_option maxHeartbeats 1000000 in
/-- **One level pass, as a run.** The entries of `L₀` from `h₀` on are
expanded, in order, and the row gains exactly their neighbourhoods; the
cost is `6 + Σ_{v expanded} (25 + 38·deg v)`. Vertices pushed *during*
the pass sit above the frozen end `bf.e` and are not expanded by it —
the level discipline, and the reason `bfsTurnCom`'s last pass does not
read the rows of distance `2R`. -/
theorem bfsLevel_run {ca co ao aj dg lo lm nn : String} (mark : Bool)
    (hnm : BfsNames ca co ao aj dg lo lm) (hnn : NnFresh nn)
    {N base B : ℕ} {c₀ l₀ : ℕ → ℕ} {g : Fin N → ℕ} {uval : ℕ} {X M : Set (Fin N)}
    {Nb : Fin N → Fin N → Prop} {deg : Fin N → ℕ}
    {L₀ : List (Fin N)} {h₀ : ℕ} {σ₀ : Env}
    (hNB : N < B) (hcapB : base + X.ncard < B)
    (hrow : BfsRow co lm base c₀ l₀ L₀ σ₀) (hca : CaRow ca g uval M σ₀)
    (hadj : AdjRows ao aj dg Nb deg B σ₀)
    (hgN : ∀ z, g z ≤ N) (huN : uval < N)
    (hLX : ∀ z ∈ L₀, z ∈ X) (hcap : base + X.ncard ≤ (σ₀.arrs lm).length)
    (hML : ∀ z, z ∈ M → z ∈ L₀) (hMmark : mark = true → ∀ z, z ∈ L₀ → z ∈ M)
    (hfront : ∀ v ∈ L₀.drop h₀, ∀ z : Fin N, Nb v z → z ∈ X)
    (hh : σ₀.vars "bf.h" = h₀) (hh0 : h₀ ≤ L₀.length)
    (hnnv : σ₀.vars nn = N) (hsv : σ₀.vars "sw.v" = uval) :
    ∃ (σ' : Env) (L' : List (Fin N)),
      Run B (bfsLevelCom ca co ao aj dg lm nn mark) σ₀ σ'
        (6 + ((L₀.drop h₀).map (fun v => 25 + 38 * deg v)).sum) ∧
      BfsRow co lm base c₀ l₀ L' σ' ∧
      CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L'} else M) σ' ∧
      (∀ z ∈ L', z ∈ X) ∧ (∃ D, L' = L₀ ++ D) ∧
      (∀ z : Fin N, z ∈ L' ↔ z ∈ L₀ ∨ ∃ v ∈ L₀.drop h₀, Nb v z) ∧
      σ'.vars "bf.h" = L₀.length ∧
      (∀ y, y ≠ "bf.c" → y ≠ "bf.o" → y ≠ "bf.n" → y ≠ "bf.t" → y ≠ "bf.w" →
        y ≠ "bf.e" → y ≠ "bf.h" → y ≠ "bf.v" → σ'.vars y = σ₀.vars y) ∧
      (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ'.arrs b = σ₀.arrs b) ∧
      (∀ b, (σ'.arrs b).length = (σ₀.arrs b).length) := by
  classical
  obtain ⟨hcolm, hcaco, hcalm, -, -, -, haoca, haoco, haolm, -, hajca, hajco,
    hajlm, -, hdgca, hdgco, hdglm, -⟩ := id hnm
  obtain ⟨-, hnc, hnh, hne, hnv, hno, hnn2, hnt, hnw, -⟩ := id hnn
  have hL0X : L₀.length ≤ X.ncard := length_le_ncard_of_nodup hrow.nodup hLX
  have hL0B : L₀.length < B := by omega
  have h1B : 1 < B := by omega
  -- freeze the level's end
  have hr0 : Run B (.assign "bf.e" (.var "bf.c")) σ₀
      (σ₀.setVar "bf.e" L₀.length) (1 + 1) := by
    have hv : (Expr.var "bf.c").evalB B σ₀ = some L₀.length := by
      have := evalB_var (B := B) (x := "bf.c") (σ := σ₀) (by rw [hrow.c]; omega)
      rw [hrow.c] at this; exact this
    have := Run.assign (B := B) (σ := σ₀) (x := "bf.e") hv
    simpa using this
  set ρ : Env := σ₀.setVar "bf.e" L₀.length with hρ
  have hρv : ∀ y, y ≠ "bf.e" → ρ.vars y = σ₀.vars y := by
    intro y hy; rw [hρ, vars_setVar, if_neg hy]
  have hρa : ∀ b, ρ.arrs b = σ₀.arrs b := by intro b; rw [hρ, arrs_setVar]
  -- the loop
  have hdef : ∀ σ, LevelInv ca co lm base c₀ l₀ g uval mark M X Nb L₀ h₀ σ₀ σ →
      ∃ w, (Cond.lt (.var "bf.h") (.var "bf.e")).evalB B σ = some w := by
    rintro σ ⟨L, -, -, -, -, -, -, hhle, hee, -, -, -⟩
    exact evalB_condLt_vars (by omega) (by rw [hee]; omega)
  have hstep : ∀ σ, LevelInv ca co lm base c₀ l₀ g uval mark M X Nb L₀ h₀ σ₀ σ →
      (Cond.lt (.var "bf.h") (.var "bf.e")).evalB B σ = some true →
      ∃ σ' K, Run B (.seq (.assign "bf.v" (.get lm (.add (.var "bf.b") (.var "bf.h"))))
          (.seq (bfsScanCom ca co ao aj dg lm nn mark)
            (.assign "bf.h" (.add (.var "bf.h") (.lit 1))))) σ σ' K ∧
        LevelInv ca co lm base c₀ l₀ g uval mark M X Nb L₀ h₀ σ₀ σ' ∧
        1 + (Cond.lt (Expr.var "bf.h") (Expr.var "bf.e")).size + K +
          ((L₀.drop (σ'.vars "bf.h")).map (fun v => 25 + 38 * deg v)).sum ≤
          ((L₀.drop (σ.vars "bf.h")).map (fun v => 25 + 38 * deg v)).sum := by
    rintro σ ⟨L, hrowL, hcaL, hLX', hpre, hmem, hh₀, hhle, hee, hfrv, hfra, hfrl⟩ htrue
    have hlt : σ.vars "bf.h" < L₀.length := by
      have := lt_of_condLt_true htrue
      rw [hee] at this; exact this
    obtain ⟨D, hD⟩ := hpre
    set s : ℕ := σ.vars "bf.h" with hsdef
    have hsL : s < L.length := by rw [hD, List.length_append]; omega
    have hLeq : L[s] = L₀[s] := by
      simp only [hD]
      exact List.getElem_append_left hlt
    have hcellv : (σ.arrs lm).getD (base + s) 0 = ((L₀[s] : Fin N) : ℕ) := by
      rw [hrowL.cell hsL, hLeq]
    -- name the vertex
    have hr1 : Run B (.assign "bf.v" (.get lm (.add (.var "bf.b") (.var "bf.h")))) σ
        (σ.setVar "bf.v" ((L₀[s] : Fin N) : ℕ)) (1 + 4) := by
      have hidx : (Expr.add (.var "bf.b") (.var "bf.h")).evalB B σ = some (base + s) := by
        have hb0 : σ.vars "bf.b" = base := hrowL.b
        have e1 : (Expr.var "bf.b").evalB B σ = some base := by
          rw [← hb0]; exact evalB_var (by rw [hb0]; omega)
        have e2 : (Expr.var "bf.h").evalB B σ = some s := by
          rw [hsdef]; exact evalB_var (by rw [← hsdef]; omega)
        have := evalB_bin (B := B) (op := .add) e1 e2 (show base + s < B by omega)
        simpa using this
      have hg : (Expr.get lm (.add (.var "bf.b") (.var "bf.h"))).evalB B σ
          = some ((L₀[s] : Fin N) : ℕ) := by
        refine evalB_get hidx ?_ (by have := (L₀[s] : Fin N).isLt; omega)
        rw [← hcellv]
        exact getElem?_of_lt (by have := hrowL.fits; omega)
      have := Run.assign (B := B) (σ := σ) (x := "bf.v") hg
      simpa using this
    set v : Fin N := L₀[s] with hvdef
    set σ₁ : Env := σ.setVar "bf.v" ((v : Fin N) : ℕ) with hσ₁
    have hσ₁v : ∀ y, y ≠ "bf.v" → σ₁.vars y = σ.vars y := by
      intro y hy; rw [hσ₁, vars_setVar, if_neg hy]
    have hσ₁a : ∀ b, σ₁.arrs b = σ.arrs b := by intro b; rw [hσ₁, arrs_setVar]
    -- the vertex's row
    have hadjσ : AdjRows ao aj dg Nb deg B σ :=
      hadj.of_eq (hfra ao haoco haolm haoca) (hfra aj hajco hajlm hajca)
        (hfra dg hdgco hdglm hdgca)
    obtain ⟨haoLen, hdgLen, hrows⟩ := hadjσ
    obtain ⟨ov, fv, haoV, hdgV, hajlen, hovB, hslot, hfviff⟩ := hrows v
    have hvdrop : v ∈ L₀.drop h₀ := getElem_mem_drop L₀ hh₀ hlt
    have hfX : ∀ t, t < deg v → fv t ∈ X := by
      intro t ht
      exact hfront v hvdrop (fv t) ((hfviff (fv t)).mp ⟨t, ht, rfl⟩)
    -- the scan
    obtain ⟨σ₂, L', hrun₂, hrow₂, hca₂, hLX₂, hpre₂, hmem₂, hv₂, ha₂, hl₂⟩ :=
      bfsScan_run (ca := ca) (co := co) (ao := ao) (aj := aj) (dg := dg) (lo := lo)
        (lm := lm) (nn := nn) mark hnm hnn (N := N) (base := base) (B := B)
        (o := ov) (n := deg v) (g := g) (uval := uval) (f := fv) (X := X)
        (M := if mark = true then M ∪ {z | z ∈ L} else M) (L₀ := L) (σ₀ := σ₁) (v := v)
        hNB hovB hcapB
        (hrowL.of_eq (hσ₁v _ (by decide)) (hσ₁v _ (by decide)) (hσ₁a co) (hσ₁a lm))
        (hcaL.of_eq (hσ₁a ca)) hgN huN hLX' hfX
        (by rw [hσ₁a lm]; exact le_trans hcap (le_of_eq (hfrl lm).symm))
        (by
          intro z hz
          by_cases hm : mark = true
          · rw [if_pos hm] at hz
            rcases hz with h | h
            · rw [hD]; exact List.mem_append.mpr (Or.inl (hML z h))
            · exact h
          · rw [if_neg hm] at hz
            rw [hD]; exact List.mem_append.mpr (Or.inl (hML z hz)))
        (by
          intro hm z hz
          rw [if_pos hm]; exact Or.inr hz)
        (by intro t ht; rw [hσ₁a aj]; exact hslot t ht)
        (by rw [hσ₁a aj]; exact hajlen)
        (by rw [hσ₁, vars_setVar, if_pos rfl])
        (by rw [hσ₁a ao]; exact haoV) (by rw [hσ₁a ao]; omega)
        (by rw [hσ₁a dg]; exact hdgV) (by rw [hσ₁a dg]; omega)
        (by rw [hσ₁v nn hnv, hfrv nn hnc hno hnn2 hnt hnw hne hnh hnv, hnnv])
        (by rw [hσ₁v "sw.v" (by decide),
              hfrv "sw.v" (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide), hsv])
    -- bump the head
    have hr3 : Run B (.assign "bf.h" (.add (.var "bf.h") (.lit 1))) σ₂
        (σ₂.setVar "bf.h" (s + 1)) (1 + 3) := by
      have hh2 : σ₂.vars "bf.h" = s := by
        rw [hv₂ "bf.h" (by decide) (by decide) (by decide) (by decide) (by decide),
          hσ₁v "bf.h" (by decide)]
      have hval : (Expr.add (.var "bf.h") (.lit 1)).evalB B σ₂ = some (s + 1) := by
        have := evalB_bin (B := B) (op := .add)
          (evalB_var (x := "bf.h") (σ := σ₂) (by rw [hh2]; omega))
          (evalB_lit (n := 1) (B := B) h1B) (by rw [hh2]; simpa using by omega)
        rw [hh2] at this
        simpa using this
      have := Run.assign (B := B) (σ := σ₂) (x := "bf.h") hval
      simpa using this
    refine ⟨σ₂.setVar "bf.h" (s + 1), 5 + (38 * deg v + 12) + 4,
      (hr1.seq (hrun₂.seq hr3)).mono (by omega), ⟨L', ?_, ?_, hLX₂, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩, ?_⟩
    · exact hrow₂.of_eq (by rw [vars_setVar, if_neg (by decide)])
        (by rw [vars_setVar, if_neg (by decide)]) (by rw [arrs_setVar])
        (by rw [arrs_setVar])
    · have hMeq : (if mark = true then (if mark = true then M ∪ {z | z ∈ L} else M)
          ∪ {z | z ∈ L'} else (if mark = true then M ∪ {z | z ∈ L} else M))
          = (if mark = true then M ∪ {z | z ∈ L'} else M) := by
        by_cases hm : mark = true
        · rw [if_pos hm, if_pos hm, if_pos hm]
          obtain ⟨D', hD'⟩ := hpre₂
          ext z
          simp only [Set.mem_union, Set.mem_setOf_eq]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (by rw [hD']; exact List.mem_append.mpr (Or.inl h))
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
        · simp only [if_neg hm]
      rw [← hMeq]
      exact hca₂.of_eq (by rw [arrs_setVar])
    · obtain ⟨D', hD'⟩ := hpre₂
      exact ⟨D ++ D', by rw [hD', hD, List.append_assoc]⟩
    · intro z
      rw [vars_setVar, if_pos rfl, hmem₂ z, hmem z]
      have hsplit : (L₀.drop h₀).take (s + 1 - h₀)
          = (L₀.drop h₀).take (s - h₀) ++ [v] := by
        have hlen : s - h₀ < (L₀.drop h₀).length := by
          rw [List.length_drop]; omega
        have hgv : (L₀.drop h₀)[s - h₀] = v := by
          have : (L₀.drop h₀)[s - h₀]? = L₀[s]? := by
            rw [List.getElem?_drop]
            have : h₀ + (s - h₀) = s := by omega
            rw [this]
          rw [List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hlt] at this
          exact Option.some_inj.mp this
        have : s + 1 - h₀ = (s - h₀) + 1 := by omega
        rw [this, List.take_add_one, List.getElem?_eq_getElem hlen, hgv]
        rfl
      rw [hsplit]
      constructor
      · rintro ((h | ⟨y, hy, hNy⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨y, List.mem_append.mpr (Or.inl hy), hNy⟩
        · exact Or.inr ⟨v, List.mem_append.mpr (Or.inr (by simp)),
            (hfviff z).mp (by obtain ⟨t, ht, hft⟩ := h; exact ⟨t, ht, hft⟩)⟩
      · rintro (h | ⟨y, hy, hNy⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_append.mp hy with h' | h'
          · exact Or.inl (Or.inr ⟨y, h', hNy⟩)
          · rw [List.mem_singleton.mp h'] at hNy
            exact Or.inr ((hfviff z).mpr hNy)
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_pos rfl]; omega
    · rw [vars_setVar, if_neg (by decide),
        hv₂ "bf.e" (by decide) (by decide) (by decide) (by decide) (by decide),
        hσ₁v "bf.e" (by decide)]
      exact hee
    · intro y h1 h2 h3 h4 h5 h6 h7 h8
      rw [vars_setVar, if_neg h7, hv₂ y h1 h2 h3 h4 h5, hσ₁v y h8]
      exact hfrv y h1 h2 h3 h4 h5 h6 h7 h8
    · intro b h1 h2 h3
      rw [arrs_setVar, ha₂ b h1 h2 h3, hσ₁a b]
      exact hfra b h1 h2 h3
    · intro b
      rw [arrs_setVar, hl₂ b, hσ₁a b]
      exact hfrl b
    · rw [vars_setVar, if_pos rfl]
      have hsum := drop_map_sum_succ L₀ (fun v => 25 + 38 * deg v) hlt
      simp only [size_condLt, size_var]
      rw [hvdef]
      omega
  have hI0 : LevelInv ca co lm base c₀ l₀ g uval mark M X Nb L₀ h₀ σ₀ ρ := by
    refine ⟨L₀, ?_, ?_, hLX, ⟨[], by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hrow.of_eq (hρv _ (by decide)) (hρv _ (by decide)) (hρa co) (hρa lm)
    · have hMeq : (if mark = true then M ∪ {z | z ∈ L₀} else M) = M := by
        by_cases hm : mark = true
        · rw [if_pos hm]
          ext z
          exact ⟨fun h => h.elim id (fun h' => hMmark hm z h'), fun h => Or.inl h⟩
        · rw [if_neg hm]
      rw [hMeq]
      exact hca.of_eq (hρa ca)
    · intro z
      rw [hρv _ (by decide), hh]
      simp only [Nat.sub_self, List.take_zero, List.not_mem_nil, false_and]
      constructor
      · exact Or.inl
      · rintro (h | ⟨-, hc⟩)
        · exact h
        · exact absurd hc not_false
    · rw [hρv _ (by decide), hh]
    · rw [hρv _ (by decide), hh]; exact hh0
    · rw [hρ, vars_setVar, if_pos rfl]
    · intro y h1 h2 h3 h4 h5 h6 h7 h8; exact hρv y h6
    · intro b _ _ _; exact hρa b
    · intro b; rw [hρa b]
  obtain ⟨σ', K, hrunW, ⟨L', hrowL', hcaL', hLX', hpre', hmem', hh₀', hhle', hee',
    hfrv', hfra', hfrl'⟩, hfalse, hpay⟩ :=
    Run.while_potential (B := B) (LevelInv ca co lm base c₀ l₀ g uval mark M X Nb L₀ h₀ σ₀)
      (fun σ => ((L₀.drop (σ.vars "bf.h")).map (fun v => 25 + 38 * deg v)).sum)
      hdef hstep hI0
  have hhfin : σ'.vars "bf.h" = L₀.length := by
    have := le_of_condLt_false hfalse
    rw [hee'] at this
    omega
  have hΦ0 : ((L₀.drop (σ'.vars "bf.h")).map (fun v => 25 + 38 * deg v)).sum = 0 := by
    rw [hhfin, List.drop_length]
    rfl
  refine ⟨σ', L', ?_, hrowL', hcaL', hLX', hpre', ?_, hhfin, ?_, ?_, ?_⟩
  · refine (hr0.seq hrunW).mono ?_
    rw [hΦ0] at hpay
    have hρh : ρ.vars "bf.h" = h₀ := by rw [hρv _ (by decide), hh]
    rw [hρh] at hpay
    simp only [size_condLt, size_var] at hpay
    omega
  · intro z
    rw [hmem' z, hhfin]
    have : (L₀.drop h₀).take (L₀.length - h₀) = L₀.drop h₀ := by
      refine List.take_of_length_le ?_
      rw [List.length_drop]
    rw [this]
  · intro y h1 h2 h3 h4 h5 h6 h7 h8
    rw [hfrv' y h1 h2 h3 h4 h5 h6 h7 h8]
  · exact hfra'
  · exact hfrl'

/-! ## §6 The level induction

The passes are unrolled, so `iterCom k` is an induction on `k` and not
a loop; what the induction carries is the pair of sets

    (the row's set, the expanded prefix's set) = (ball (m+1), ball m),

shifted by one so that the start — the row `[u]`, nothing expanded — is
the honest `(ball 0, ∅)`. `BlS` is that shift and `ball_succ_frontier`
the step: **one pass is one radius**, and it is enough to expand the
*frontier* because the neighbours of the older layers were pushed
already. -/

/-- The ball family, shifted by one so that `BlS 0 = ∅`: the reached set
before any pass, and the expanded set at the start of the first. -/
def BlS {V : Type*} (H : SimpleGraph V) (u : V) : ℕ → Set V
  | 0 => ∅
  | (m + 1) => ball H m u

@[simp] theorem BlS_zero {V : Type*} (H : SimpleGraph V) (u : V) : BlS H u 0 = ∅ := rfl

@[simp] theorem BlS_succ {V : Type*} (H : SimpleGraph V) (u : V) (m : ℕ) :
    BlS H u (m + 1) = ball H m u := rfl

theorem BlS_mono {V : Type*} (H : SimpleGraph V) (u : V) (m : ℕ) :
    BlS H u m ⊆ BlS H u (m + 1) := by
  cases m with
  | zero => simp
  | succ p => exact ball_mono_radius H u (Nat.le_succ p)

theorem BlS_mono_le {V : Type*} (H : SimpleGraph V) (u : V) {m m' : ℕ} (h : m ≤ m') :
    BlS H u m ⊆ BlS H u m' := by
  induction m' with
  | zero => obtain rfl : m = 0 := Nat.le_zero.mp h; exact le_rfl
  | succ p ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact le_rfl
      · exact subset_trans (ih (by omega)) (BlS_mono H u p)

/-- **One pass is one radius, expanding only the frontier.** The layer
below the frontier had its neighbours pushed by the previous pass, so
expanding it again would add nothing — which is exactly why the level
discipline is sound and why the last level need not be expanded. -/
theorem ball_succ_frontier {V : Type*} (H : SimpleGraph V) (u : V) (m : ℕ) :
    BlS H u (m + 2) =
      BlS H u (m + 1) ∪ {z | ∃ v, (v ∈ BlS H u (m + 1) ∧ v ∉ BlS H u m) ∧ H.Adj v z} := by
  classical
  cases m with
  | zero =>
      rw [BlS_succ, BlS_succ, BlS_zero, ball_succ]
      ext z
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_eq_true,
        and_true]
  | succ p =>
      rw [BlS_succ, BlS_succ, BlS_succ]
      ext z
      rw [ball_succ H (p + 1) u]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (h | ⟨v, hv, hadj⟩)
        · exact Or.inl h
        · by_cases hvp : v ∈ ball H p u
          · exact Or.inl (withinDist_trans (mem_ball.mp hvp) (withinDist_of_adj hadj))
          · exact Or.inr ⟨v, ⟨hv, hvp⟩, hadj⟩
      · rintro (h | ⟨v, ⟨hv, -⟩, hadj⟩)
        · exact Or.inl h
        · exact Or.inr ⟨v, hv, hadj⟩

/-- Splitting a duplicate-free list at the head: the entries still to be
expanded are exactly the row minus the prefix already expanded. -/
theorem mem_drop_iff_of_nodup {α : Type*} [DecidableEq α] {l : List α}
    (h : l.Nodup) (i : ℕ) (z : α) : z ∈ l.drop i ↔ z ∈ l ∧ z ∉ l.take i := by
  have hsplit : l.take i ++ l.drop i = l := List.take_append_drop i l
  have hnd : (l.take i ++ l.drop i).Nodup := by rw [hsplit]; exact h
  rw [List.nodup_append] at hnd
  constructor
  · intro hz
    refine ⟨by rw [← hsplit]; exact List.mem_append.mpr (Or.inr hz), ?_⟩
    intro hzt
    exact hnd.2.2 z hzt z hz rfl
  · rintro ⟨hz, hzt⟩
    rw [← hsplit] at hz
    rcases List.mem_append.mp hz with h' | h'
    · exact absurd h' hzt
    · exact h'

set_option maxHeartbeats 1000000 in
/-- **`k` level passes.** From a row whose set is `BlS (d+1)` and whose
expanded prefix is `BlS d`, `k` passes leave the row at `BlS (d+k+1)`
and the prefix at `BlS (d+k)`, at cost `1 + 6·k + Σ_{v ∈ E} (25 + 38·deg v)`
where `E` — the list of vertices the passes expanded — is exactly the
segment of the final row between the two heads.

The `1` is `iterCom`'s tail `skip`; the `6` a pass's prologue and exit;
`E` is duplicate-free because the row is, which is what turns the sum
into a sum over a *set* of vertices at the seam. -/
theorem bfsIters_run {ca co ao aj dg lo lm nn : String} (mark : Bool)
    (hnm : BfsNames ca co ao aj dg lo lm) (hnn : NnFresh nn)
    {N base B : ℕ} {c₀ l₀ : ℕ → ℕ} {g : Fin N → ℕ} {uval : ℕ} {X : Set (Fin N)}
    {H : SimpleGraph (Fin N)} {u : Fin N} {deg : Fin N → ℕ}
    (hNB : N < B) (hcapB : base + X.ncard < B)
    (hgN : ∀ z, g z ≤ N) (huN : uval < N) :
    ∀ (k d : ℕ) (L₀ : List (Fin N)) (h₀ : ℕ) (M : Set (Fin N)) (σ₀ : Env),
      BfsRow co lm base c₀ l₀ L₀ σ₀ → CaRow ca g uval M σ₀ →
      AdjRows ao aj dg H.Adj deg B σ₀ →
      (∀ z ∈ L₀, z ∈ X) → base + X.ncard ≤ (σ₀.arrs lm).length →
      (∀ z, z ∈ M → z ∈ L₀) → (mark = true → ∀ z, z ∈ L₀ → z ∈ M) →
      (∀ v, v ∈ BlS H u (d + k) → ∀ z : Fin N, H.Adj v z → z ∈ X) →
      σ₀.vars "bf.h" = h₀ → h₀ ≤ L₀.length →
      (∀ z : Fin N, z ∈ L₀.take h₀ ↔ z ∈ BlS H u d) →
      (∀ z : Fin N, z ∈ L₀ ↔ z ∈ BlS H u (d + 1)) →
      σ₀.vars nn = N → σ₀.vars "sw.v" = uval →
      ∃ (σ' : Env) (L' : List (Fin N)) (E : List (Fin N)),
        Run B (iterCom k (bfsLevelCom ca co ao aj dg lm nn mark)) σ₀ σ'
          (1 + 6 * k + (E.map (fun v => 25 + 38 * deg v)).sum) ∧
        BfsRow co lm base c₀ l₀ L' σ' ∧
        CaRow ca g uval (if mark = true then M ∪ {z | z ∈ L'} else M) σ' ∧
        (∀ z ∈ L', z ∈ X) ∧ (∃ D, L' = L₀ ++ D) ∧
        (∀ z : Fin N, z ∈ L' ↔ z ∈ BlS H u (d + k + 1)) ∧
        (∀ z : Fin N, z ∈ L'.take (σ'.vars "bf.h") ↔ z ∈ BlS H u (d + k)) ∧
        L'.take (σ'.vars "bf.h") = L₀.take h₀ ++ E ∧
        σ'.vars "bf.h" ≤ L'.length ∧
        (∀ y, y ≠ "bf.c" → y ≠ "bf.o" → y ≠ "bf.n" → y ≠ "bf.t" → y ≠ "bf.w" →
          y ≠ "bf.e" → y ≠ "bf.h" → y ≠ "bf.v" → σ'.vars y = σ₀.vars y) ∧
        (∀ b, b ≠ co → b ≠ lm → b ≠ ca → σ'.arrs b = σ₀.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ₀.arrs b).length) := by
  classical
  obtain ⟨hcolm, hcaco, hcalm, -, -, -, haoca, haoco, haolm, -, hajca, hajco,
    hajlm, -, hdgca, hdgco, hdglm, -⟩ := id hnm
  obtain ⟨-, hnc, hnh, hne, hnv, hno, hnn2, hnt, hnw, -⟩ := id hnn
  intro k
  induction k with
  | zero =>
      intro d L₀ h₀ M σ₀ hrow hca _ hLX _ _ hMmark _ hh hh0 htake hmem1 _ _
      refine ⟨σ₀, L₀, [], ?_, hrow, ?_, hLX, ⟨[], by simp⟩, ?_, ?_, ?_, ?_,
        fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩
      · simpa using (Run.skip (B := B) (σ := σ₀))
      · have hMeq : (if mark = true then M ∪ {z | z ∈ L₀} else M) = M := by
          by_cases hm : mark = true
          · rw [if_pos hm]
            ext z
            exact ⟨fun h => h.elim id (fun h' => hMmark hm z h'), fun h => Or.inl h⟩
          · rw [if_neg hm]
        rw [hMeq]; exact hca
      · intro z; rw [show d + 0 + 1 = d + 1 from rfl]; exact hmem1 z
      · intro z; rw [hh, show d + 0 = d from rfl]; exact htake z
      · rw [hh]; simp
      · rw [hh]; exact hh0
  | succ p ih =>
      intro d L₀ h₀ M σ₀ hrow hca hadj hLX hcap hML hMmark hexp hh hh0 htake hmem1
        hnnv hsv
      -- one pass
      obtain ⟨σ₁, L₁, hrun₁, hrow₁, hca₁, hLX₁, hpre₁, hmem₁, hh₁, hfrv₁, hfra₁, hfrl₁⟩ :=
        bfsLevel_run (ca := ca) (co := co) (ao := ao) (aj := aj) (dg := dg) (lo := lo)
          (lm := lm) (nn := nn) mark hnm hnn (N := N) (base := base) (B := B)
          (g := g) (uval := uval) (X := X) (M := M) (Nb := H.Adj) (deg := deg)
          (L₀ := L₀) (h₀ := h₀) (σ₀ := σ₀)
          hNB hcapB hrow hca hadj hgN huN hLX hcap hML hMmark
          (by
            intro v hv z hadjv
            refine hexp v ?_ z hadjv
            have hvL : v ∈ L₀ := ((mem_drop_iff_of_nodup hrow.nodup h₀ v).mp hv).1
            exact BlS_mono_le H u (by omega) ((hmem1 v).mp hvL))
          hh hh0 hnnv hsv
      obtain ⟨D, hD⟩ := hpre₁
      have hL₁take : L₁.take L₀.length = L₀ := by rw [hD]; simp
      -- the row's new set
      have hmem₁' : ∀ z : Fin N, z ∈ L₁ ↔ z ∈ BlS H u (d + 1 + 1) := by
        intro z
        rw [hmem₁ z, show d + 1 + 1 = d + 2 from rfl, ball_succ_frontier H u d]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro (h | ⟨v, hv, hadjv⟩)
          · exact Or.inl ((hmem1 z).mp h)
          · refine Or.inr ⟨v, ⟨?_, ?_⟩, hadjv⟩
            · exact (hmem1 v).mp ((mem_drop_iff_of_nodup hrow.nodup h₀ v).mp hv).1
            · intro hc
              exact ((mem_drop_iff_of_nodup hrow.nodup h₀ v).mp hv).2 ((htake v).mpr hc)
        · rintro (h | ⟨v, ⟨hv1, hv2⟩, hadjv⟩)
          · exact Or.inl ((hmem1 z).mpr h)
          · refine Or.inr ⟨v, ?_, hadjv⟩
            refine (mem_drop_iff_of_nodup hrow.nodup h₀ v).mpr ⟨(hmem1 v).mpr hv1, ?_⟩
            intro hc
            exact hv2 ((htake v).mp hc)
      -- the recursion
      obtain ⟨σ', L', E', hrun', hrow', hca', hLX', hpre', hmemE, htakeE, hseg,
        hhle', hfrv', hfra', hfrl'⟩ :=
        ih (d + 1) L₁ L₀.length
          (if mark = true then M ∪ {z | z ∈ L₁} else M) σ₁
          hrow₁ hca₁
          (hadj.of_eq (hfra₁ ao haoco haolm haoca) (hfra₁ aj hajco hajlm hajca)
            (hfra₁ dg hdgco hdglm hdgca))
          hLX₁ (by rw [hfrl₁ lm]; exact hcap)
          (by
            intro z hz
            by_cases hm : mark = true
            · rw [if_pos hm] at hz
              rcases hz with h | h
              · rw [hD]; exact List.mem_append.mpr (Or.inl (hML z h))
              · exact h
            · rw [if_neg hm] at hz
              rw [hD]; exact List.mem_append.mpr (Or.inl (hML z hz)))
          (by intro hm z hz; rw [if_pos hm]; exact Or.inr hz)
          (by
            intro v hv z hadjv
            refine hexp v ?_ z hadjv
            rw [show d + (p + 1) = d + 1 + p from by omega]
            exact hv)
          hh₁ (by rw [hD, List.length_append]; omega)
          (by intro z; rw [hL₁take]; exact hmem1 z)
          hmem₁'
          (by rw [hfrv₁ nn hnc hno hnn2 hnt hnw hne hnh hnv, hnnv])
          (by
            rw [hfrv₁ "sw.v" (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide), hsv])
      refine ⟨σ', L', L₀.drop h₀ ++ E', ?_, hrow', ?_, hLX', ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · rw [iterCom_succ]
        refine (hrun₁.seq hrun').mono ?_
        rw [List.map_append, List.sum_append]
        omega
      · have hMeq : (if mark = true then (if mark = true then M ∪ {z | z ∈ L₁} else M)
            ∪ {z | z ∈ L'} else (if mark = true then M ∪ {z | z ∈ L₁} else M))
            = (if mark = true then M ∪ {z | z ∈ L'} else M) := by
          by_cases hm : mark = true
          · rw [if_pos hm, if_pos hm, if_pos hm]
            obtain ⟨D', hD'⟩ := hpre'
            ext z
            simp only [Set.mem_union, Set.mem_setOf_eq]
            constructor
            · rintro ((h | h) | h)
              · exact Or.inl h
              · exact Or.inr (by rw [hD']; exact List.mem_append.mpr (Or.inl h))
              · exact Or.inr h
            · rintro (h | h)
              · exact Or.inl (Or.inl h)
              · exact Or.inr h
          · simp only [if_neg hm]
        rw [← hMeq]; exact hca'
      · obtain ⟨D', hD'⟩ := hpre'
        exact ⟨D ++ D', by rw [hD', hD, List.append_assoc]⟩
      · intro z; rw [hmemE z, show d + 1 + p + 1 = d + (p + 1) + 1 from by omega]
      · intro z; rw [htakeE z, show d + 1 + p = d + (p + 1) from by omega]
      · rw [hseg, hL₁take, ← List.append_assoc, List.take_append_drop]
      · exact hhle'
      · intro y h1 h2 h3 h4 h5 h6 h7 h8
        rw [hfrv' y h1 h2 h3 h4 h5 h6 h7 h8, hfrv₁ y h1 h2 h3 h4 h5 h6 h7 h8]
      · intro b h1 h2 h3
        rw [hfra' b h1 h2 h3, hfra₁ b h1 h2 h3]
      · intro b
        rw [hfrl' b, hfrl₁ b]

/-! ### Array lengths are a run invariant

`sweepSt_step_of_bfs` asks the pass to hand back `co`'s allocation, and
`bfsClear_spec` — a landed contract — states no frame at all. The fact
is structural: the only array update in IMP+ is a store, and a store is
`List.set`. -/

theorem bigStep_arrs_length {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

/-- **A run never changes an array's length.** -/
theorem Run.arrs_length {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hbs⟩ := h.bigStep
  exact bigStep_arrs_length hbs a

/-! ## §7 From the loop state to the pass's hypotheses

Three bridges: the ball at radius zero (the initial push's own claim),
the slot space's word bound, and the adjacency region read as rows. The
last is where `DelAdjSt`'s soundness and completeness clauses become the
`AdjRows` the scan consumes; a *deleted* vertex needs no special case,
because `deleteVerts` isolates rather than removes and its empty
neighbourhood is exactly the `0` its live length holds. -/

/-- The ball of radius zero is the centre. -/
theorem ball_zero {V : Type*} (H : SimpleGraph V) (u : V) : ball H 0 u = {u} := by
  ext z
  rw [mem_ball]
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | nil => rfl
    | cons h q => simp at hp
  · rintro rfl
    exact withinDist_refl H 0 _

set_option maxHeartbeats 1000000 in
/-- **The deletable adjacency region, read as rows.** Every vertex's
live row enumerates its neighbourhood in the *current* structure, with
every index it uses below the word bound. A vertex of the peeled prefix
is not a special case: `deleteVerts` isolates it, so its neighbourhood
is empty and its live length `0` is the honest row. -/
theorem adjRows_of_delAdjSt {ao aj dg mt : String} {N B : ℕ}
    {G : SimpleGraph (Fin N)} {S : Set (Fin N)} {σ : Env}
    (h : DelAdjSt ao aj dg mt G S σ) (hne : Nonempty (Fin N)) (hB : N + N * N < B) :
    AdjRows ao aj dg (deleteVerts G S).Adj
      (fun v => ((deleteVerts G S).neighborSet v).ncard) B σ := by
  classical
  obtain ⟨offF, h0, hstep, haoLen, hao, hajLen, -, hdgLen, hdead, hdeg, hsound,
    hcomp⟩ := h
  refine ⟨haoLen.trans' (by omega), hdgLen, ?_⟩
  intro v
  have hdgv : (σ.arrs dg).getD (v : ℕ) 0
      = ((deleteVerts G S).neighborSet v).ncard := by
    by_cases hv : v ∈ S
    · rw [hdead v hv]
      have hempty : (deleteVerts G S).neighborSet v = ∅ := by
        ext z
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        intro hadj
        exact (Lax3Proofs.SplitterBasics.deleteVerts_adj.mp hadj).2.1 hv
      rw [hempty]
      simp
    · exact hdeg v hv
  -- the slot function
  have hex : ∀ t : ℕ, ∃ w : Fin N,
      (t < ((deleteVerts G S).neighborSet v).ncard →
        (deleteVerts G S).Adj v w ∧ (σ.arrs aj).getD (offF (v : ℕ) + t) 0 = (w : ℕ)) := by
    intro t
    by_cases ht : t < ((deleteVerts G S).neighborSet v).ncard
    · have hvS : v ∉ S := by
        intro hv
        rw [hdead v hv] at hdgv
        omega
      obtain ⟨w, hadj, haj, -⟩ := hsound v hvS t (by rw [hdgv]; exact ht)
      exact ⟨w, fun _ => ⟨hadj, haj⟩⟩
    · exact ⟨hne.some, fun hc => absurd hc ht⟩
  choose fv hfv using hex
  refine ⟨offF (v : ℕ), fv, hao (v : ℕ) (le_of_lt v.isLt), hdgv, ?_, ?_, ?_, ?_⟩
  · calc offF (v : ℕ) + ((deleteVerts G S).neighborSet v).ncard
        ≤ offF (v : ℕ) + (G.neighborSet v).ncard :=
          Nat.add_le_add_left (ncard_neighborSet_deleteVerts_le G S v) _
      _ = offF ((v : ℕ) + 1) := (hstep v).symm
      _ ≤ offF N := offF_mono hstep N (le_refl N) _ v.isLt
      _ ≤ (σ.arrs aj).length := hajLen
  · show offF (v : ℕ) + ((deleteVerts G S).neighborSet v).ncard < B
    have h1 : offF (v : ℕ) + ((deleteVerts G S).neighborSet v).ncard ≤ offF N := by
      calc offF (v : ℕ) + ((deleteVerts G S).neighborSet v).ncard
          ≤ offF (v : ℕ) + (G.neighborSet v).ncard :=
            Nat.add_le_add_left (ncard_neighborSet_deleteVerts_le G S v) _
        _ = offF ((v : ℕ) + 1) := (hstep v).symm
        _ ≤ offF N := offF_mono hstep N (le_refl N) _ v.isLt
    have h2 : offF N ≤ N * N := offF_le_sq h0 hstep N (le_refl N)
    omega
  · intro t ht
    exact ((hfv t) ht).2
  · intro z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ((hfv t) ht).1
    · intro hadj
      have hvS : v ∉ S := (Lax3Proofs.SplitterBasics.deleteVerts_adj.mp hadj).2.1
      obtain ⟨t, ht, haj⟩ := hcomp v hvS z hadj
      rw [hdgv] at ht
      refine ⟨t, ht, ?_⟩
      have := ((hfv t) ht).2
      rw [haj] at this
      exact Fin.val_injective this.symm

/-! ## §8 The turn's bill

The three constants, assembled. The pass costs

    29 (the initial push)
  + (1 + 6·R + Σ_{v expanded, marking} (25 + 38·deg v))
  + (1 + 6·R + Σ_{v expanded, plain}   (25 + 38·deg v))
  + 7 (the offset write) + (14·|X_u| + 6) (the clean-up),

which is `44 + 12·R + Σ_{v ∈ E} (25 + 38·deg v) + 14·|X_u|` with `E` the
whole expanded list. `E` enumerates `ball H (2R-1) u` without repetition,
so `|E| ≤ |X_u|` and `Σ_{v ∈ E} deg v ≤ 2·Σ_{w ∈ X_u} d_<(w)`
(`bfsExpanded_le_edgeTerm`) — and the three figures come out
`12·R + 44`, `25 + 14 = 39`, `2·38 = 76`. -/

open Classical in
/-- **The turn's cost is `peelTurn` at `(12R+44, 39, 76)`.** Nothing is
fitted: `|E| ≤ |X_u|` is duplicate-freeness, `Σ deg ≤ 2 Σ d_<` is §3's
factor `2`, and every other figure is a literal `Com` size. -/
theorem bfs_cost_le {L n₀ Λ : ℕ} (S : Setup L) (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (hR : 1 ≤ S.R) {i : ℕ} (hi : i < A.N)
    (hiu : ((π u : Fin A.N) : ℕ) = i)
    (E Lst : List (Fin A.N)) (hEnd : E.Nodup) (hLnd : Lst.Nodup)
    (hEmem : ∀ z : Fin A.N,
      z ∈ E ↔ z ∈ ball (deleteVerts A.G (peelSet π i)) (2 * S.R - 1) u)
    (hLmem : ∀ z : Fin A.N, z ∈ Lst ↔ z ∈ cluster S A π u) :
    44 + 12 * S.R
      + (E.map (fun v => 25 + 38 *
          ((deleteVerts A.G (peelSet π i)).neighborSet v).ncard)).sum
      + 14 * Lst.length
      ≤ peelTurn S A π (12 * S.R + 44) 39 76 i := by
  classical
  have hu : u = π.symm ⟨i, hi⟩ := by
    have hpu : π u = (⟨i, hi⟩ : Fin A.N) := Fin.ext hiu
    rw [← hpu, Equiv.symm_apply_apply]
  have hXball : cluster S A π u = ball (deleteVerts A.G (peelSet π i)) (2 * S.R) u := by
    have h := cluster_eq_ball_peelSet S A π u
    rw [hiu] at h
    exact h
  have hpt : peelTurn S A π (12 * S.R + 44) 39 76 i
      = (12 * S.R + 44) + 39 * (cluster S A π u).ncard
        + 76 * ∑ z ∈ Finset.univ.filter (fun z => z ∈ cluster S A π u),
            Impl.dlt A.G π z := by
    rw [peelTurn, dif_pos hi, ← hu]
  have hEF : E.toFinset
      = Finset.univ.filter
          (fun z => z ∈ ball (deleteVerts A.G (peelSet π i)) (2 * S.R - 1) u) := by
    ext z
    rw [List.mem_toFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, (hEmem z).mp h⟩, fun h => (hEmem z).mpr h.2⟩
  have hsum : (E.map (fun v => 25 + 38 *
        ((deleteVerts A.G (peelSet π i)).neighborSet v).ncard)).sum
      = ∑ z ∈ E.toFinset, (25 + 38 *
          ((deleteVerts A.G (peelSet π i)).neighborSet z).ncard) :=
    (List.sum_toFinset _ hEnd).symm
  have hsplit : ∑ z ∈ E.toFinset, (25 + 38 *
        ((deleteVerts A.G (peelSet π i)).neighborSet z).ncard)
      = 25 * E.toFinset.card
        + 38 * ∑ z ∈ E.toFinset,
            ((deleteVerts A.G (peelSet π i)).neighborSet z).ncard := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
    ring
  have hcard : E.toFinset.card = E.length := List.toFinset_card_of_nodup hEnd
  have hLlen : Lst.length = (cluster S A π u).ncard :=
    length_eq_ncard_of_nodup hLnd hLmem
  have hEle : E.length ≤ (cluster S A π u).ncard :=
    length_le_ncard_of_nodup hEnd (fun z hz => by
      rw [hXball]
      exact ball_mono_radius _ u (by omega) ((hEmem z).mp hz))
  have hedge : ∑ z ∈ E.toFinset,
        ((deleteVerts A.G (peelSet π i)).neighborSet z).ncard
      ≤ 2 * ∑ w ∈ Finset.univ.filter (fun w => w ∈ cluster S A π u),
          Impl.dlt A.G π w := by
    rw [hEF]
    have h := bfsExpanded_le_edgeTerm S A π u hR
    rw [hiu] at h
    exact h
  rw [hpt, hsum, hsplit, hcard, hLlen]
  omega

/-! ## §9 `PeelBfsIn`, discharged

Everything above, composed at the loop state. The scratch descriptor is
`BfsClean (co j) n` — "the visited flags are clear" — and it comes back
out, because the clean-up walks the row rather than the carrier. -/

set_option maxHeartbeats 4000000 in
/-- **F6c12 residual (4-i-a), discharged.** `PeelBfsIn` holds of
`bfsTurnCom` at `abf = 12·R + 44`, `bbf = 39`, `cbf = 76`, with every
clause of the contract intact.

The scratch descriptor is `BfsClean (co j) n`: the pass borrows `co` for
its visited flags and hands it back clean. That is the second program
constraint, and `bfsClear_spec` is what pays for it — `14` of `bbf`,
linear in the row and in nothing else. -/
theorem peelBfsIn_bfsTurnCom (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ao aj dg mt od lo lm : ℕ → String)
    (hq : 1 ≤ q) (hR : 1 ≤ (Headline.headlineSetup C hC φ).R)
    (hnm : ∀ j, BfsNames (ca j) (co j) (ao j) (aj j) (dg j) (lo j) (lm j))
    (hfr : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨ b = (arenaNames j).hist ∨
      b = od j ∨ b = mt j →
      b ≠ ca j ∧ b ≠ co j ∧ b ≠ lo j ∧ b ≠ lm j) :
    PeelBfsIn C hC φ ord G c w q ℓp htabF hbf Adm ca co ao aj dg mt od lo lm
      (fun j σ => BfsClean (co j) n σ)
      (fun j => bfsTurnCom (Headline.headlineSetup C hC φ).R (ca j) (co j) (ao j)
        (aj j) (dg j) (lo j) (lm j) (arenaNames j).nN)
      (12 * (Headline.headlineSetup C hC φ).R + 44) 39 76 := by
  classical
  set St := Headline.headlineSetup C hC φ with hStdef
  intro x hx j hj A hAdm hbot i hi σ hσ
  obtain ⟨hst, hswi, hswv⟩ := hσ
  obtain ⟨hAW, hordr, hcoLen, hlmLen, hSsc, hdel, hctr, hlog⟩ := hst
  obtain ⟨hcolm, hcaco, hcalm, hcalo, hcolo, hlmlo, haoca, haoco, haolm, haolo,
    hajca, hajco, hajlm, hajlo, hdgca, hdgco, hdglm, hdglo⟩ := id (hnm j)
  have hnnf : NnFresh (arenaNames j).nN := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact (arenaScalars_ne j (by decide) (by decide) (by decide)).1
  obtain ⟨hnb', hnc, hnh, hne, hnv, hno, hnn2, hnt, hnw, hnk⟩ := id hnnf
  -- the pieces of the state, named
  set π : Equiv.Perm (Fin A.N) := (ord A.N A.G).order with hπdef
  set B : ℕ := mcB q x with hBdef
  set u : Fin A.N := π.symm ⟨i, hi⟩ with hudef
  set Hc : SimpleGraph (Fin A.N) := deleteVerts A.G (peelSet π i) with hHcdef
  set base : ℕ := peelOff π (cluster St A π) i with hbasedef
  set degf : Fin A.N → ℕ := fun v => (Hc.neighborSet v).ncard with hdegfdef
  set g : Fin A.N → ℕ := fun z => (σ.arrs (ca j)).getD (z : ℕ) 0 with hgdef
  set c₀ : ℕ → ℕ := fun v => (σ.arrs (co j)).getD v 0 with hc₀def
  set l₀ : ℕ → ℕ := fun m => (σ.arrs (lm j)).getD m 0 with hl₀def
  -- word bounds
  have hAN : A.N ≤ n := by
    have h := Fintype.card_le_of_embedding A.up
    simpa using h
  have hBnd : A.N + A.N * A.N < B := arena_sq_lt_mcB hq hx A
  have hn1B : n * n + n + 1 < B := by
    have henc : EncodesGraph x n G := hx.1
    have hlen := henc.length_eq
    have h2 : (x.length + 1) * (x.length + 1) ≤ B := by
      rw [hBdef, mcB, pow_two]
      exact Nat.le_mul_of_pos_left _ hq
    have h3 : n * n + n + 1 < (x.length + 1) * (x.length + 1) := by nlinarith
    omega
  have hANB : A.N < B := by omega
  have h1B : 1 < B := by have := u.isLt; omega
  have hiu : ((π u : Fin A.N) : ℕ) = i := by rw [hudef, Equiv.apply_symm_apply]
  have hXball : cluster St A π u = ball Hc (2 * St.R) u := by
    have h := cluster_eq_ball_peelSet St A π u
    rw [hiu] at h
    exact h
  have huX : u ∈ cluster St A π u := self_mem_cluster St A π u
  -- the row's anchor and its room
  have hloLen : A.N + 1 ≤ (σ.arrs (lo j)).length := hlog.1
  have hlobase : (σ.arrs (lo j)).getD i 0 = base := hlog.2.1 i (le_refl i)
  have hroom : base + (cluster St A π u).ncard ≤ (σ.arrs (lm j)).length := by
    have hstep : peelOff π (cluster St A π) (i + 1)
        = base + (cluster St A π u).ncard := by
      have := peelOff_step π (cluster St A π) (⟨i, hi⟩ : Fin A.N)
      simpa [hbasedef, hudef] using this
    rw [← hstep]
    exact bfsRow_fits π (cluster St A π) hi hAN hlmLen
  have hcapB : base + (cluster St A π u).ncard < B := by
    have hstep : peelOff π (cluster St A π) (i + 1)
        = base + (cluster St A π u).ncard := by
      have := peelOff_step π (cluster St A π) (⟨i, hi⟩ : Fin A.N)
      simpa [hbasedef, hudef] using this
    have h1 : peelOff π (cluster St A π) (i + 1) ≤ A.N * A.N :=
      peelOff_le_sq π (cluster St A π) (by omega)
    omega
  have hbaseB : base < B := by
    have := Set.ncard_pos (s := cluster St A π u)
    omega
  -- the marks, as a `CaRow`
  have hcaLen : A.N ≤ (σ.arrs (ca j)).length := hctr.1
  have hgN : ∀ z, g z ≤ A.N := fun z => hctr.le z
  have hnnv : σ.vars (arenaNames j).nN = A.N := hAW.n_eq
  have huN : ((u : Fin A.N) : ℕ) < A.N := u.isLt
  -- the adjacency region, as rows
  have hadj : AdjRows (ao j) (aj j) (dg j) Hc.Adj degf B σ :=
    adjRows_of_delAdjSt hdel ⟨u⟩ hBnd
  -- the expansion bound
  have hexpX : ∀ m, m ≤ 2 * St.R → ∀ v, v ∈ BlS Hc u m →
      ∀ z : Fin A.N, Hc.Adj v z → z ∈ cluster St A π u := by
    intro m hm v hv z hadjvz
    cases m with
    | zero => exact absurd hv (by simp)
    | succ p =>
        rw [BlS_succ] at hv
        have hz : z ∈ ball Hc (p + 1) u :=
          withinDist_trans (mem_ball.mp hv) (withinDist_of_adj hadjvz)
        rw [hXball]
        exact ball_mono_radius Hc u (by omega) hz
  sorry

end Lax3Proofs.Prog
