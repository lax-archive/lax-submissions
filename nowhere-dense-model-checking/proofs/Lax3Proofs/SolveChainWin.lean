import Lax3Proofs.SolveBlocks

/-!
# F6c6 (part 1) — the windowed-region contract, and its one generic transport

The seam wave 13 flagged (`SolveBlocksRestrict`, module docstring,
finding 2): `ArenaSt`'s `Csr` is an **exact-length** statement
(`σ.arrs off = arrOf (N+1) _`), IMP+ array lengths are immutable, and
`Unroll`'s frame layout is **static** — level `j`'s regions are
allocated once, at the per-depth maximum, and then hold every arena of
that level in turn, each with its own (smaller) dimensions. So the
composition needs *max-size allocations with a valid prefix*, and every
landed exact-length stage `Spec` must apply to such a state.

This file is that bridge, done **once, generically**, instead of once
per stage:

* **The padding simulation** (`bigStepB_padA`): IMP+'s semantics is
  *stuck* on any out-of-range access — an out-of-range read has no
  value (`Expr.evalB`'s `[k]?`), an out-of-range store no derivation.
  So a successful run never touches any cell beyond the lengths it was
  given, and extending every array by an arbitrary tail (`padA`)
  preserves the whole derivation verbatim: same reads (they hit the
  prefix), same writes (`List.set` on the prefix), same cost. This is
  the semantic fact that makes a windowed contract *free* — it is a
  property of the language, not of any particular program.

* **The window transport** (`specWindow`): for any landed
  `Spec B P c Q K` and any window assignment `ws : String → Option ℕ`,
  the same command satisfies the same specification **relative to the
  window**: from any state whose windowed arrays fit (`FitsW`) and
  whose *truncation* (`winA`) satisfies `P`, it runs to a state whose
  truncation satisfies `Q`, with every array length preserved and
  every tail beyond a window untouched. The proof: truncate, run the
  landed spec, pad the derivation back (`padA_wtails_winA`). Nothing
  is asked of `P`, `Q` or `c` — the landed stage files are consumed
  as they are, which is what keeps the lifting cost per stage at the
  gluing (name disjointness, region congruence), not at re-proof.

* **The windowed contract** (`ArenaStW`): the head file's `ArenaSt`,
  stated of the truncation at the arena's own dimensions
  (`arenaWs`) — CSR offsets at `N+1`, targets at the slot-count
  cell's value, colors at `N·Λ`, renaming at `N`, channel at
  `N·ℓp·(hb+1)` — plus `FitsW`. The two bridges: an exact-length
  `ArenaSt` **is** a windowed one (`ArenaSt.toW` — the windows are
  the lengths and truncation is the identity), and the truncation of
  a windowed state satisfies the exact contract by definition
  (`ArenaStW.st` is a projection), which is the form a landed stage
  `Spec`'s precondition consumes through `specWindow`. `TableBitsW`
  is the same move for the table region.

* `specArrsLength`: every `Spec` may be strengthened, for free, with
  "every array length is preserved" — a run never reallocates. This is
  what lets the chain's per-level scratch descriptors be length-only
  facts that survive every stage without being restated.

Everything here is proved; no obligation is introduced.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## §1 Environment extensionality and the padding -/

/-- Two environments with the same four fields are equal. -/
theorem env_ext {σ τ : Env} (hv : σ.vars = τ.vars) (ha : σ.arrs = τ.arrs)
    (hi : σ.inp = τ.inp) (ho : σ.out = τ.out) : σ = τ := by
  cases σ; cases τ; simp_all

/-- **The padding**: every array extended by the tail `E` names for it;
scalars and tapes untouched. -/
def padA (E : String → List ℕ) (σ : Env) : Env :=
  { σ with arrs := fun b => σ.arrs b ++ E b }

@[simp] theorem vars_padA (E : String → List ℕ) (σ : Env) :
    (padA E σ).vars = σ.vars := rfl

@[simp] theorem arrs_padA (E : String → List ℕ) (σ : Env) (b : String) :
    (padA E σ).arrs b = σ.arrs b ++ E b := rfl

@[simp] theorem inp_padA (E : String → List ℕ) (σ : Env) :
    (padA E σ).inp = σ.inp := rfl

@[simp] theorem out_padA (E : String → List ℕ) (σ : Env) :
    (padA E σ).out = σ.out := rfl

/-- A successful in-range read survives the padding with its value. -/
private theorem getElem?_append_of_some {l e : List ℕ} {k v : ℕ}
    (h : l[k]? = some v) : (l ++ e)[k]? = some v := by
  have hk : k < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hk]
  exact h

/-- Bounded expression evaluation is preserved by padding: every read a
successful evaluation makes is in range, hence reads the prefix. -/
theorem evalB_padA {B : ℕ} {σ : Env} {v : ℕ} (E : String → List ℕ) :
    ∀ {e : Expr}, e.evalB B σ = some v → e.evalB B (padA E σ) = some v := by
  intro e
  induction e generalizing v with
  | lit n => intro h; exact h
  | var x => intro h; exact h
  | get a i ih =>
    intro h
    rw [Expr.evalB, Option.bind_eq_some_iff] at h
    obtain ⟨k, hk, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hfit⟩ := h
    rw [Expr.evalB, Option.bind_eq_some_iff]
    exact ⟨k, ih hk, by
      rw [Option.bind_eq_some_iff]
      exact ⟨u, getElem?_append_of_some hu, hfit⟩⟩
  | bin op e f ihe ihf =>
    intro h
    rw [Expr.evalB, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨w, hw, hfit⟩ := h
    rw [Expr.evalB, Option.bind_eq_some_iff]
    exact ⟨m, ihe hm, by
      rw [Option.bind_eq_some_iff]
      exact ⟨w, ihf hw, hfit⟩⟩

/-- Condition evaluation is preserved by padding. -/
theorem condB_padA {B : ℕ} {σ : Env} {r : Bool} (E : String → List ℕ)
    {b : Cond} (h : b.evalB B σ = some r) : b.evalB B (padA E σ) = some r := by
  cases b with
  | eq e f =>
    rw [Cond.evalB, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    rw [Cond.evalB, evalB_padA E hm, Option.bind_some, evalB_padA E hw,
      Option.map_some]
  | lt e f =>
    rw [Cond.evalB, Option.bind_eq_some_iff] at h
    obtain ⟨m, hm, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    rw [Cond.evalB, evalB_padA E hm, Option.bind_some, evalB_padA E hw,
      Option.map_some]

/-- The padding commutes with an in-range store. -/
private theorem padA_setArr {E : String → List ℕ} {σ : Env} {a : String}
    {k v : ℕ} (hk : k < (σ.arrs a).length) :
    padA E (σ.setArr a k v) = (padA E σ).setArr a k v := by
  refine env_ext rfl ?_ rfl rfl
  funext b
  show (σ.setArr a k v).arrs b ++ E b = ((padA E σ).setArr a k v).arrs b
  by_cases hb : b = a
  · subst hb
    rw [arrs_setArr, if_pos rfl, arrs_setArr, if_pos rfl, arrs_padA,
      List.set_append_left _ _ hk]
  · rw [arrs_setArr, if_neg hb, arrs_setArr, if_neg hb, arrs_padA]

/-- **The padding simulation**: a bounded big-step derivation survives
extending every array by an arbitrary tail — same final state (padded
by the same tails), same cost. Out-of-range access is stuck, so a
derivation that exists never sees past the original lengths. -/
theorem bigStepB_padA {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (E : String → List ℕ) (h : BigStepB B c σ σ' k) :
    BigStepB B c (padA E σ) (padA E σ') k := by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (evalB_padA E h)
  | @store σ a i e k v hi he hk =>
    rw [padA_setArr hk]
    refine BigStepB.store (evalB_padA E hi) (evalB_padA E he) ?_
    rw [arrs_padA, List.length_append]
    omega
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true hb _ ih => exact .ite_true (condB_padA E hb) ih
  | ite_false hb _ ih => exact .ite_false (condB_padA E hb) ih
  | while_true hb _ _ ih ih' => exact .while_true (condB_padA E hb) ih ih'
  | while_false hb => exact .while_false (condB_padA E hb)
  | read h => exact .read h
  | write h => exact .write (evalB_padA E h)

/-- A run never changes any array's length: there is no allocation. -/
theorem bigStepB_arrs_length {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) : ∀ b, (σ'.arrs b).length = (σ.arrs b).length := by
  induction h with
  | skip => exact fun _ => rfl
  | assign _ => exact fun _ => rfl
  | @store σ a i e k v _ _ _ =>
    intro b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  | seq _ _ ih ih' => exact fun b => (ih' b).trans (ih b)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact fun b => (ih' b).trans (ih b)
  | while_false _ => exact fun _ => rfl
  | read _ => exact fun _ => rfl
  | write _ => exact fun _ => rfl

/-- The padding simulation, at the `Run` judgment. -/
theorem run_padA {B K : ℕ} {c : Com} {σ σ' : Env} (E : String → List ℕ)
    (h : Run B c σ σ' K) : Run B c (padA E σ) (padA E σ') K := by
  obtain ⟨k, hk, hb⟩ := h
  exact ⟨k, hk, bigStepB_padA E hb⟩

/-- Length preservation, at the `Run` judgment. -/
theorem run_arrs_length_eq {B K : ℕ} {c : Com} {σ σ' : Env}
    (h : Run B c σ σ' K) : ∀ b, (σ'.arrs b).length = (σ.arrs b).length := by
  obtain ⟨k, _, hb⟩ := h
  exact bigStepB_arrs_length hb

/-- **Free strengthening of any `Spec` by length preservation** — the
fact that lets per-level scratch descriptors be length-only and never
restated. -/
theorem specArrsLength {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop}
    {c : Com} (h : Spec B P c Q K) :
    Spec B P c (fun σ σ' => Q σ σ' ∧
      ∀ b, (σ'.arrs b).length = (σ.arrs b).length) K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  exact ⟨σ', hr, hq, run_arrs_length_eq hr⟩

/-! ## §2 Windows -/

/-- **The truncation**: each array with a window is cut to its window
length; everything else is untouched. The truncation of a max-size
allocation is the exact-length state the landed stage `Spec`s are
stated at. -/
def winA (ws : String → Option ℕ) (σ : Env) : Env :=
  { σ with arrs := fun b => match ws b with
      | some m => (σ.arrs b).take m
      | none => σ.arrs b }

/-- The allocation fits its windows: every window is within its
array. -/
def FitsW (ws : String → Option ℕ) (σ : Env) : Prop :=
  ∀ b m, ws b = some m → m ≤ (σ.arrs b).length

/-- The tails beyond the windows — what the padding restores. -/
def wtails (ws : String → Option ℕ) (σ : Env) : String → List ℕ :=
  fun b => match ws b with
    | some m => (σ.arrs b).drop m
    | none => []

@[simp] theorem vars_winA (ws : String → Option ℕ) (σ : Env) :
    (winA ws σ).vars = σ.vars := rfl

@[simp] theorem inp_winA (ws : String → Option ℕ) (σ : Env) :
    (winA ws σ).inp = σ.inp := rfl

@[simp] theorem out_winA (ws : String → Option ℕ) (σ : Env) :
    (winA ws σ).out = σ.out := rfl

theorem arrs_winA_some {ws : String → Option ℕ} {b : String} {m : ℕ}
    (h : ws b = some m) (σ : Env) : (winA ws σ).arrs b = (σ.arrs b).take m := by
  show (match ws b with | some m => (σ.arrs b).take m | none => σ.arrs b) = _
  rw [h]

theorem arrs_winA_none {ws : String → Option ℕ} {b : String}
    (h : ws b = none) (σ : Env) : (winA ws σ).arrs b = σ.arrs b := by
  show (match ws b with | some m => (σ.arrs b).take m | none => σ.arrs b) = _
  rw [h]

/-- The truncation only looks at the window value: two window
assignments agreeing at `b` truncate `b` identically. -/
theorem arrs_winA_congr {ws ws' : String → Option ℕ} {b : String}
    (h : ws b = ws' b) (σ : Env) : (winA ws σ).arrs b = (winA ws' σ).arrs b := by
  show (match ws b with | some m => (σ.arrs b).take m | none => σ.arrs b)
    = (match ws' b with | some m => (σ.arrs b).take m | none => σ.arrs b)
  rw [h]

/-- A fitting window truncates to exactly its length. -/
theorem length_arrs_winA {ws : String → Option ℕ} {σ : Env} {b : String}
    {m : ℕ} (h : ws b = some m) (hfit : m ≤ (σ.arrs b).length) :
    ((winA ws σ).arrs b).length = m := by
  rw [arrs_winA_some h, List.length_take]
  omega

/-- Padding the truncation by the tails restores the allocation. -/
theorem padA_wtails_winA {ws : String → Option ℕ} {σ : Env} :
    padA (wtails ws σ) (winA ws σ) = σ := by
  refine env_ext rfl ?_ rfl rfl
  funext b
  show (winA ws σ).arrs b ++ wtails ws σ b = σ.arrs b
  cases hb : ws b with
  | some m =>
    rw [arrs_winA_some hb]
    show (σ.arrs b).take m ++ (match ws b with
      | some m => (σ.arrs b).drop m | none => []) = σ.arrs b
    rw [hb]
    exact List.take_append_drop m (σ.arrs b)
  | none =>
    rw [arrs_winA_none hb]
    show σ.arrs b ++ (match ws b with
      | some m => (σ.arrs b).drop m | none => []) = σ.arrs b
    rw [hb, List.append_nil]

/-- A `getD` read inside the window reads through the truncation. -/
theorem getD_take_of_lt {l : List ℕ} {i m : ℕ} (h : i < m) (d : ℕ) :
    (l.take m).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt h]

/-! ## §3 The transport -/

/-- **The one generic window transport.** Any landed exact-length
`Spec` holds, verbatim, of the max-size allocation *relative to the
window assignment `ws`*: from a fitting state whose truncation
satisfies `P`, the command runs to a fitting state whose truncation
satisfies `Q`, at the same budget — with every array length preserved
and every tail beyond a window untouched. This is the whole per-stage
lifting; what remains at a call site is gluing (evaluating `ws` at the
names in play). -/
theorem specWindow {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (h : Spec B P c Q K) (ws : String → Option ℕ) :
    Spec B (fun τ => FitsW ws τ ∧ P (winA ws τ)) c
      (fun τ τ' => FitsW ws τ' ∧ Q (winA ws τ) (winA ws τ') ∧
        (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧
        (∀ b m, ws b = some m → (τ'.arrs b).drop m = (τ.arrs b).drop m)) K := by
  rintro τ ⟨hfit, hP⟩
  obtain ⟨σ', hrun, hq⟩ := h (winA ws τ) hP
  have hlen : ∀ b, (σ'.arrs b).length = ((winA ws τ).arrs b).length :=
    run_arrs_length_eq hrun
  have hlen' : ∀ b m, ws b = some m → (σ'.arrs b).length = m := by
    intro b m hb
    rw [hlen b, length_arrs_winA hb (hfit b m hb)]
  have hwin : winA ws (padA (wtails ws τ) σ') = σ' := by
    refine env_ext rfl ?_ rfl rfl
    funext b
    cases hb : ws b with
    | some m =>
      rw [arrs_winA_some hb, arrs_padA]
      show ((σ'.arrs b ++ match ws b with
        | some m => (τ.arrs b).drop m | none => []) : List ℕ).take m = σ'.arrs b
      rw [hb]
      exact List.take_left' (hlen' b m hb)
    | none =>
      rw [arrs_winA_none hb, arrs_padA]
      show (σ'.arrs b ++ match ws b with
        | some m => (τ.arrs b).drop m | none => []) = σ'.arrs b
      rw [hb, List.append_nil]
  refine ⟨padA (wtails ws τ) σ', ?_, ?_, ?_, ?_, ?_⟩
  · have hr := run_padA (wtails ws τ) hrun
    rwa [padA_wtails_winA] at hr
  · -- the result still fits
    intro b m hb
    rw [arrs_padA, List.length_append, hlen' b m hb]
    omega
  · -- the truncations stand in `Q`
    rw [hwin]
    exact hq
  · -- every length is preserved
    intro b
    rw [arrs_padA, List.length_append, hlen b]
    cases hb : ws b with
    | some m =>
      rw [length_arrs_winA hb (hfit b m hb)]
      show m + (match ws b with
        | some m => (τ.arrs b).drop m | none => ([] : List ℕ)).length
        = (τ.arrs b).length
      rw [hb, List.length_drop]
      have := hfit b m hb
      omega
    | none =>
      rw [arrs_winA_none hb]
      show (τ.arrs b).length + (match ws b with
        | some m => (τ.arrs b).drop m | none => ([] : List ℕ)).length
        = (τ.arrs b).length
      rw [hb]
      simp
  · -- every tail beyond a window is untouched
    intro b m hb
    rw [arrs_padA, List.drop_left' (hlen' b m hb)]
    show (match ws b with
      | some m => (τ.arrs b).drop m | none => ([] : List ℕ)) = (τ.arrs b).drop m
    rw [hb]

/-! ## §4 The windowed contract -/

/-- **The window assignment of one arena region family**: the CSR
offsets at `N + 1`, the targets at the slot count `ns`, the color rows
at `N·Λ`, the renaming at `N`, the channel at `N·ℓp·(hb+1)` — exactly
the exact lengths `ArenaSt` pins. Names outside the family carry no
window. (The five names are assumed distinct where this is consumed —
the head file's `lv` mechanism supplies that.) -/
def arenaWs (nm : ArenaNames) (Λ ℓp hb N ns : ℕ) : String → Option ℕ := fun b =>
  if b = nm.off then some (N + 1)
  else if b = nm.tgt then some ns
  else if b = nm.col then some (N * Λ)
  else if b = nm.up then some N
  else if b = nm.hist then some (N * ℓp * (hb + 1))
  else none

section ArenaWsEval

variable {nm : ArenaNames} {Λ ℓp hb N ns : ℕ} {b : String}

theorem arenaWs_off : arenaWs nm Λ ℓp hb N ns nm.off = some (N + 1) := by
  rw [arenaWs, if_pos rfl]

theorem arenaWs_tgt (hot : nm.tgt ≠ nm.off) :
    arenaWs nm Λ ℓp hb N ns nm.tgt = some ns := by
  rw [arenaWs, if_neg hot, if_pos rfl]

theorem arenaWs_col (hco : nm.col ≠ nm.off) (hct : nm.col ≠ nm.tgt) :
    arenaWs nm Λ ℓp hb N ns nm.col = some (N * Λ) := by
  rw [arenaWs, if_neg hco, if_neg hct, if_pos rfl]

theorem arenaWs_up (huo : nm.up ≠ nm.off) (hut : nm.up ≠ nm.tgt)
    (huc : nm.up ≠ nm.col) : arenaWs nm Λ ℓp hb N ns nm.up = some N := by
  rw [arenaWs, if_neg huo, if_neg hut, if_neg huc, if_pos rfl]

theorem arenaWs_hist (hho : nm.hist ≠ nm.off) (hht : nm.hist ≠ nm.tgt)
    (hhc : nm.hist ≠ nm.col) (hhu : nm.hist ≠ nm.up) :
    arenaWs nm Λ ℓp hb N ns nm.hist = some (N * ℓp * (hb + 1)) := by
  rw [arenaWs, if_neg hho, if_neg hht, if_neg hhc, if_neg hhu, if_pos rfl]

/-- A name outside the five regions carries no window. -/
theorem arenaWs_none (h1 : b ≠ nm.off) (h2 : b ≠ nm.tgt) (h3 : b ≠ nm.col)
    (h4 : b ≠ nm.up) (h5 : b ≠ nm.hist) : arenaWs nm Λ ℓp hb N ns b = none := by
  rw [arenaWs, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- Only the five region names carry windows. -/
theorem arenaWs_some_elim {m : ℕ} (h : arenaWs nm Λ ℓp hb N ns b = some m) :
    b = nm.off ∨ b = nm.tgt ∨ b = nm.col ∨ b = nm.up ∨ b = nm.hist := by
  by_cases h1 : b = nm.off
  · exact Or.inl h1
  by_cases h2 : b = nm.tgt
  · exact Or.inr (Or.inl h2)
  by_cases h3 : b = nm.col
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : b = nm.up
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : b = nm.hist
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  rw [arenaWs_none h1 h2 h3 h4 h5] at h
  cases h

end ArenaWsEval

/-- **The windowed per-frame contract**: the level's regions are
allocations of *at least* the arena's dimensions (`FitsW`), and their
prefixes at exactly those dimensions satisfy the landed exact-length
contract `ArenaSt`. The slot count is the level's `nS` cell, as in
`ArenaSt` itself. -/
def ArenaStW (nm : ArenaNames) {Λ n₀ ℓp : ℕ} (hb : ℕ) (A : Impl.MArena Λ n₀ ℓp)
    (σ : Env) : Prop :=
  FitsW (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ ∧
    ArenaSt nm hb A (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ)

/-- The exact contract of the truncation — the projection a landed
stage `Spec`'s precondition consumes through `specWindow`. -/
theorem ArenaStW.st {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaStW nm hb A σ) :
    ArenaSt nm hb A (winA (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ) := h.2

theorem ArenaStW.fits {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaStW nm hb A σ) :
    FitsW (arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS)) σ := h.1

/-- The carrier cell, read through the windowed contract (the
truncation does not touch scalars). -/
theorem ArenaStW.n_eq {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaStW nm hb A σ) :
    σ.vars nm.nN = A.N := h.2.n_eq

/-- `ArenaSt` reads exactly five arrays and two scalars: it transports
along agreement on them. -/
theorem arenaSt_of_eq {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ σ' : Env} (h : ArenaSt nm hb A σ)
    (hn : σ'.vars nm.nN = σ.vars nm.nN) (hs : σ'.vars nm.nS = σ.vars nm.nS)
    (ho : σ'.arrs nm.off = σ.arrs nm.off) (ht : σ'.arrs nm.tgt = σ.arrs nm.tgt)
    (hc : σ'.arrs nm.col = σ.arrs nm.col) (hu : σ'.arrs nm.up = σ.arrs nm.up)
    (hh : σ'.arrs nm.hist = σ.arrs nm.hist) : ArenaSt nm hb A σ' := by
  obtain ⟨hne, ⟨off, tgt, hcsr, h0, hnd, hadj⟩, hcol, hup, hhist⟩ := h
  refine ⟨hn.trans hne, ⟨off, tgt, ?_, h0, hnd, hadj⟩, ?_, ?_, ?_⟩
  · rw [hs]
    exact hcsr.of_eq ho ht
  · exact ⟨by rw [hc]; exact hcol.1, fun v cc => by rw [hc]; exact hcol.2 v cc⟩
  · exact ⟨by rw [hu]; exact hup.1, fun v => by rw [hu]; exact hup.2 v⟩
  · refine ⟨by rw [hh]; exact hhist.1, fun v p => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hhist.2 v p
    exact ⟨h1, by rw [hh]; exact h2, fun i hi => by rw [hh]; exact h3 i hi⟩

/-- The five exact lengths `ArenaSt` pins, read off it. -/
theorem ArenaSt.lengths {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaSt nm hb A σ) :
    (σ.arrs nm.off).length = A.N + 1 ∧
    (σ.arrs nm.tgt).length = σ.vars nm.nS ∧
    (σ.arrs nm.col).length = A.N * Λ ∧
    (σ.arrs nm.up).length = A.N ∧
    (σ.arrs nm.hist).length = A.N * ℓp * (hb + 1) := by
  obtain ⟨-, ⟨off, tgt, hcsr, -, -, -⟩, hcol, hup, hhist⟩ := h
  exact ⟨by rw [hcsr.1, length_arrOf], by rw [hcsr.2.1, length_arrOf],
    hcol.1, hup.1, hhist.1⟩

/-- **Bridge 1 (weakening)**: an exact-length `ArenaSt` is a windowed
one — the windows are the lengths, and truncation at the exact lengths
is the identity on the five arrays. The five array names must be
pairwise distinct (the head file's name mechanism supplies this). -/
theorem ArenaSt.toW {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env} (h : ArenaSt nm hb A σ)
    (hnd : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup) :
    ArenaStW nm hb A σ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd
  obtain ⟨⟨hot, hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd
  obtain ⟨hoffL, htgtL, hcolL, hupL, hhistL⟩ := h.lengths
  set ws := arenaWs nm Λ ℓp hb A.N (σ.vars nm.nS) with hws
  -- the five window values
  have hwoff : ws nm.off = some (A.N + 1) := by rw [hws, arenaWs, if_pos rfl]
  have hwtgt : ws nm.tgt = some (σ.vars nm.nS) := by
    rw [hws, arenaWs, if_neg (Ne.symm hot), if_pos rfl]
  have hwcol : ws nm.col = some (A.N * Λ) := by
    rw [hws, arenaWs, if_neg (Ne.symm hoc), if_neg (Ne.symm htc), if_pos rfl]
  have hwup : ws nm.up = some A.N := by
    rw [hws, arenaWs, if_neg (Ne.symm hou), if_neg (Ne.symm htu),
      if_neg (Ne.symm hcu), if_pos rfl]
  have hwhist : ws nm.hist = some (A.N * ℓp * (hb + 1)) := by
    rw [hws, arenaWs, if_neg (Ne.symm hoh), if_neg (Ne.symm hth),
      if_neg (Ne.symm hch), if_neg (Ne.symm huh), if_pos rfl]
  -- fits: only the five names carry windows, at exactly the lengths
  have hfit : FitsW ws σ := by
    intro b m hb
    rw [hws, arenaWs] at hb
    by_cases h1 : b = nm.off
    · rw [if_pos h1] at hb; cases hb; rw [h1, hoffL]
    rw [if_neg h1] at hb
    by_cases h2 : b = nm.tgt
    · rw [if_pos h2] at hb; cases hb; rw [h2, htgtL]
    rw [if_neg h2] at hb
    by_cases h3 : b = nm.col
    · rw [if_pos h3] at hb; cases hb; rw [h3, hcolL]
    rw [if_neg h3] at hb
    by_cases h4 : b = nm.up
    · rw [if_pos h4] at hb; cases hb; rw [h4, hupL]
    rw [if_neg h4] at hb
    by_cases h5 : b = nm.hist
    · rw [if_pos h5] at hb; cases hb; rw [h5, hhistL]
    rw [if_neg h5] at hb
    cases hb
  -- truncation at the exact length is the identity
  have htake : ∀ (b : String) (m : ℕ), ws b = some m → (σ.arrs b).length = m →
      (winA ws σ).arrs b = σ.arrs b := by
    intro b m hb hl
    rw [arrs_winA_some hb, ← hl, List.take_length]
  refine ⟨hfit, arenaSt_of_eq h rfl rfl ?_ ?_ ?_ ?_ ?_⟩
  · exact htake _ _ hwoff hoffL
  · exact htake _ _ hwtgt htgtL
  · exact htake _ _ hwcol hcolL
  · exact htake _ _ hwup hupL
  · exact htake _ _ hwhist hhistL

/-! ## §5 The windowed table region -/

open Lax3.DistFO in
open Classical in
/-- **The windowed table region**: `TableBits` with the exact length
relaxed to a valid prefix — one bit per `(v, β)` with `β` over the
level's schedule family, row-major, inside an allocation of at least
`N·|Fl|` cells. -/
def TableBitsW (a : String) {N Λ : ℕ} (Fl : List (DistFO Λ 1))
    (T : Fin N → DistFO Λ 1 → Prop) (σ : Env) : Prop :=
  N * Fl.length ≤ (σ.arrs a).length ∧
    ∀ (v : Fin N) (i : ℕ), ∀ hi : i < Fl.length,
      (σ.arrs a).getD ((v : ℕ) * Fl.length + i) 0 = if T v Fl[i] then 1 else 0

open Lax3.DistFO in
/-- A row-major table index is inside the region. -/
theorem tableIdx_lt {N F : ℕ} (v : Fin N) {i : ℕ} (hi : i < F) :
    (v : ℕ) * F + i < N * F := by
  have h1 : (v : ℕ) * F + i < ((v : ℕ) + 1) * F := by
    rw [Nat.succ_mul]
    omega
  exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right F v.2)

open Lax3.DistFO in
/-- Bridge (weakening): an exact table region is a windowed one. -/
theorem tableBitsW_of_exact {a : String} {N Λ : ℕ} {Fl : List (DistFO Λ 1)}
    {T : Fin N → DistFO Λ 1 → Prop} {σ : Env} (h : TableBits a Fl T σ) :
    TableBitsW a Fl T σ :=
  ⟨le_of_eq h.1.symm, h.2⟩

open Lax3.DistFO in
/-- Bridge (reading back through a window): an exact table region *of
the truncation*, at a window of exactly the table's size, is a windowed
table region of the allocation. This is how a landed stage's
`TableBits` postcondition lands on the windowed contract after
`specWindow`. -/
theorem tableBitsW_of_win {ws : String → Option ℕ} {a : String} {N Λ : ℕ}
    {Fl : List (DistFO Λ 1)} {T : Fin N → DistFO Λ 1 → Prop} {σ : Env}
    (hws : ws a = some (N * Fl.length)) (hfit : FitsW ws σ)
    (h : TableBits a Fl T (winA ws σ)) : TableBitsW a Fl T σ := by
  refine ⟨hfit a _ hws, fun v i hi => ?_⟩
  have hidx : (v : ℕ) * Fl.length + i < N * Fl.length := tableIdx_lt v hi
  have hread := h.2 v i hi
  rwa [arrs_winA_some hws, getD_take_of_lt hidx] at hread

open Lax3.DistFO in
/-- Bridge (into a stage): the truncation of a windowed table region,
at the window of exactly the table's size, satisfies the exact
predicate — the form a landed stage's precondition consumes. -/
theorem tableBits_win_of_W {ws : String → Option ℕ} {a : String} {N Λ : ℕ}
    {Fl : List (DistFO Λ 1)} {T : Fin N → DistFO Λ 1 → Prop} {σ : Env}
    (hws : ws a = some (N * Fl.length)) (h : TableBitsW a Fl T σ) :
    TableBits a Fl T (winA ws σ) := by
  refine ⟨?_, fun v i hi => ?_⟩
  · exact length_arrs_winA hws h.1
  · rw [arrs_winA_some hws, getD_take_of_lt (tableIdx_lt v hi)]
    exact h.2 v i hi

open Lax3.DistFO in
/-- The windowed table region transports along the table's pointwise
propositional equality — how `Unroll.unrollAux`'s equations move
through it. -/
theorem tableBitsW_congr {a : String} {N Λ : ℕ} {Fl : List (DistFO Λ 1)}
    {T T' : Fin N → DistFO Λ 1 → Prop} {σ : Env}
    (h : TableBitsW a Fl T σ) (hT : ∀ v β, T v β ↔ T' v β) :
    TableBitsW a Fl T' σ := by
  classical
  refine ⟨h.1, fun v i hi => ?_⟩
  rw [h.2 v i hi]
  exact if_congr (hT v Fl[i]) rfl rfl

end Lax3Proofs.Prog
