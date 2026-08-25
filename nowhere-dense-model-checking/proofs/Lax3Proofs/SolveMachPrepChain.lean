import Lax3Proofs.SolveMachPrepComp3

/-!
# F6c12 (residual 1) — the child-building pass, composed: the chain

`SolveMachPrepComp{,2,3}` supplied every *part* of the composition —
the name pool, the command `prepC`, the budget, the level's scratch
descriptor `prepScr`, the allocation/name/word-bound audits, the write
set in closed form, and all nine stages wrapped at `prepC`'s own
names. What was still missing is the composition itself: the fourteen
`Spec.seq` steps, their fourteen `hmid` obligations, and the budget
summation.

This file supplies it, and concludes **`ChildLoadPartsScr`** — the
residual `SolveMachPrepSeam` reduced the whole prep segment to.

## §1 The glue the chain needs

Four small facts no landed object provides:

* `Spec.exists2` — a precondition with two existentially bound tables
  (the profiles stage produces `Dp`/`Dc`; the three stages after it
  consume them) is discharged by a family of `Spec`s, one per pair;
* `prepScr_frameC` — the descriptor rides any command that writes
  neither a rank scratch of level `≥ j` nor a carrier cell. This is
  what carries `prepScr` across **eleven** of the fourteen steps; the
  restrict stage is the twelfth, and re-establishes it from its own
  postcondition (`prepScr_out`);
* the four scalar-load blocks, as `Spec`s with a state *equality*
  postcondition — `store` is `List.set` and `setVar` moves one cell, so
  the equality is the cheapest thing to transport;
* `prepMidH` — the pre-isolation child with its channel rows replaced.
  The supports stage patches one column, so the arena the *profiles*
  stage and the *isolation* run on is not the one `restrictCom` left,
  and the two stage wrappers of `SolveMachPrepComp3` are stated at the
  latter. §2 restates those two at an arbitrary channel family, which
  is all their contracts ever needed (`profilesCom_specW` and
  `isolateCom_specW` are generic in the arena).

## §3 The chain

Fourteen steps, composed inside-out. Every intermediate postcondition
is the **same** predicate — the pass's deliverable, a statement about
the exit state alone — so the fourteen `hpost` obligations are
identities and all the work is in the fourteen `hmid`s. The frame
clauses `ChildLoadPartsScr` demands are *not* threaded through the
chain: they are read off the syntax of the whole of `prepC` at the end
(`Spec.frameA` with `SolveMachPrepComp3` §5), which is exactly what
that section exists for.

## Hazards honoured

No stage, radius or budget moves. The BFS and the supports pass run at
`2 * S.R`; the profiles stage runs at the pre-isolation child and the
**parent's** palette; the budget is `prepKP`, whose `prepKP_le` fits
§7's envelope with no `A.N` term. The only *new* arithmetic is the
summation of the fourteen step costs against `prepPassK + prepLoadK`,
and it is a `Nat` inequality between the same figures.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §1 The glue -/

section Glue

variable {B : ℕ} {c : Com} {Q : Env → Env → Prop} {K : ℕ}

/-- **A precondition with two bound tables.** The profiles stage names
its two output families as readings of its regions; the colour writer,
the isolation and the closing move all run at *those* tables. The
chain therefore carries them existentially, and this is the rule that
consumes such a precondition. -/
theorem Spec.exists2 {α β : Sort*} {P : α → β → Env → Prop}
    (h : ∀ a b, Spec B (P a b) c Q K) :
    Spec B (fun σ => ∃ a b, P a b σ) c Q K :=
  fun _ hσ => h hσ.choose hσ.choose_spec.choose _ hσ.choose_spec.choose_spec

/-- The one-table form: the BFS names the distance table the supports
pass runs at. -/
theorem Spec.exists1 {α : Sort*} {P : α → Env → Prop}
    (h : ∀ a, Spec B (P a) c Q K) :
    Spec B (fun σ => ∃ a, P a σ) c Q K :=
  fun _ hσ => h hσ.choose _ hσ.choose_spec

/-- **A state-independent side condition, read out of the
precondition.** The stage wrappers take the profile witness and its two
value bounds as *arguments*, while the chain carries them inside the
precondition (they mention the bound tables); this is the one step that
moves one from the second place to the first. -/
theorem Spec.imp {P : Env → Prop} {p : Prop} (h : p → Spec B P c Q K)
    (hp : ∀ σ, P σ → p) : Spec B P c Q K :=
  fun σ hσ => h (hp σ hσ) σ hσ

end Glue

section Descriptor

variable {L : ℕ}

/-- **The descriptor's frame law, at the pass's own names.** `prepScr`
reads exactly three things beyond array *lengths*: the rank scratches
of levels `≥ j`, and every level's carrier cell. A command that leaves
those alone carries the whole descriptor.

This is what crosses eleven of the fourteen steps; only `restrictCom`
writes a rank scratch, and only `restrictCom` writes a carrier cell. -/
theorem prepScr_frameC {S : Setup L} {ℓp hbf : ℕ → ℕ} {n₀ j : ℕ}
    {σ σ' : Env} (h : prepScr S ℓp hbf n₀ j σ)
    (hlen : ∀ b, (σ'.arrs b).length = (σ.arrs b).length)
    (hra : ∀ i, j ≤ i → σ'.arrs (pcRa i) = σ.arrs (pcRa i))
    (hnN : ∀ i, σ'.vars (arenaNames i).nN = σ.vars (arenaNames i).nN) :
    prepScr S ℓp hbf n₀ j σ' :=
  prepScr_out h hlen (fun i hi => hra i (le_of_lt hi))
    (rankScr_frame (prepScr_rank h) (hra j le_rfl) (hnN j))
    (fun i => by rw [hnN i]; exact h.2.2.2.1 i)

end Descriptor

/-! ## §2 The scalar-load blocks -/

section Loads

variable {B : ℕ} {P : Env → Prop}

/-- One literal load. Cost `1 + 1`, the whole of what a `.lit` costs. -/
theorem assignLit_spec (x : String) {v : ℕ} (hv : v < B) :
    Spec B P (.assign x (.lit v)) (fun σ σ' => σ' = σ.setVar x v) 2 := by
  have h := Spec.assign (B := B) (P := P) (x := x) (e := .lit v)
    (f := fun _ => v) (fun _ _ => evalB_lit hv)
  exact h.mono (by norm_num [Expr.size])

/-- One cell-to-cell move. -/
theorem assignVar_spec (x y : String) (hv : ∀ σ, P σ → σ.vars y < B) :
    Spec B P (.assign x (.var y))
      (fun σ σ' => σ' = σ.setVar x (σ.vars y)) 2 := by
  have h := Spec.assign (B := B) (P := P) (x := x) (e := .var y)
    (f := fun σ => σ.vars y) (fun σ hσ => evalB_var (hv σ hσ))
  exact h.mono (by norm_num [Expr.size])

variable {L : ℕ}

/-- The restrict stage's three schedule cells. -/
theorem prepRestrictCells_spec (S : Setup L) (ℓp hbf : ℕ → ℕ) (j : ℕ)
    (h1 : S.pal j < B) (h2 : ℓp j < B) (h3 : hbf j < B) :
    Spec B (fun _ => True) (prepRestrictCells S ℓp hbf j)
      (fun σ σ' => σ'.vars "rs.l" = S.pal j ∧ σ'.vars "rs.p" = ℓp j ∧
        σ'.vars "rs.h" = hbf j ∧
        (∀ y, y ≠ "rs.l" → y ≠ "rs.p" → y ≠ "rs.h" →
          σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 6 := by
  refine Spec.post (Spec.seq'
      (assignLit_spec (B := B) (P := fun _ => True) "rs.l" h1)
      (Spec.seq' (assignLit_spec (B := B) (P := fun _ => True) "rs.p" h2)
        (assignLit_spec (B := B) (P := fun _ => True) "rs.h" h3)
        (fun _ _ _ _ => trivial))
      (fun _ _ _ _ => trivial)) ?_
  rintro σ σ'' - ⟨τ, rfl, τ', rfl, rfl⟩
  exact ⟨by simp [vars_setVar], by simp [vars_setVar],
    by simp [vars_setVar],
    fun y k1 k2 k3 => by simp [vars_setVar, k1, k2, k3],
    fun a => by simp [arrs_setVar]⟩

/-- The batch builder's two schedule cells. -/
theorem prepBatchCells_spec (S : Setup L) (j : ℕ)
    (h1 : j < B) (h2 : S.width < B) :
    Spec B (fun _ => True) (prepBatchCells S j)
      (fun σ σ' => σ'.vars pcJr = j ∧ σ'.vars pcMw = S.width ∧
        (∀ y, y ≠ pcJr → y ≠ pcMw → σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 4 := by
  have hne : pcJr ≠ pcMw := lv_ne_of_base_ne (by decide) (by decide) _ _
  refine Spec.post (Spec.seq'
      (assignLit_spec (B := B) (P := fun _ => True) pcJr h1)
      (assignLit_spec (B := B) (P := fun _ => True) pcMw h2)
      (fun _ _ _ _ => trivial)) ?_
  rintro σ σ'' - ⟨τ, rfl, rfl⟩
  exact ⟨by simp [vars_setVar, hne], by simp [vars_setVar],
    fun y k1 k2 => by simp [vars_setVar, k1, k2],
    fun a => by simp [arrs_setVar]⟩

/-- The three cells the BFS block reads, as a precondition on the state
it runs in. -/
def BfsCellsPre (j : ℕ) (B : ℕ) (σ : Env) : Prop :=
  σ.vars (arenaNames (j + 1)).nN < B ∧
    σ.vars (arenaNames (j + 1)).nS < B ∧ σ.vars pcCc < B

theorem bfsCellsPre_setVar {j B : ℕ} {σ : Env} (h : BfsCellsPre j B σ)
    {x : String} (hx1 : (arenaNames (j + 1)).nN ≠ x)
    (hx2 : (arenaNames (j + 1)).nS ≠ x) (hx3 : pcCc ≠ x) (v : ℕ) :
    BfsCellsPre j B (σ.setVar x v) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vars_setVar, if_neg hx1]; exact h.1
  · rw [vars_setVar, if_neg hx2]; exact h.2.1
  · rw [vars_setVar, if_neg hx3]; exact h.2.2

/-- The BFS's four input cells: the child's two cells, the radius
`2 * S.R` — never `S.R` — and the connector's own child name. -/
theorem prepBfsCells_spec (S : Setup L) (j : ℕ) (h3 : 2 * S.R < B) :
    Spec B (BfsCellsPre j B) (prepBfsCells S j)
      (fun σ σ' => σ'.vars "bf.n" = σ.vars (arenaNames (j + 1)).nN ∧
        σ'.vars "bf.m" = σ.vars (arenaNames (j + 1)).nS ∧
        σ'.vars "bf.r" = 2 * S.R ∧ σ'.vars "bf.v" = σ.vars pcCc ∧
        (∀ y, y ≠ "bf.n" → y ≠ "bf.m" → y ≠ "bf.r" → y ≠ "bf.v" →
          σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 8 := by
  have hn1 : (arenaNames (j + 1)).nN ≠ "bf.n" :=
    lv_ne_lit (by decide) (by decide) _
  have hn2 : (arenaNames (j + 1)).nN ≠ "bf.m" :=
    lv_ne_lit (by decide) (by decide) _
  have hn3 : (arenaNames (j + 1)).nN ≠ "bf.r" :=
    lv_ne_lit (by decide) (by decide) _
  have hn4 : (arenaNames (j + 1)).nN ≠ "bf.v" :=
    lv_ne_lit (by decide) (by decide) _
  have hs1 : (arenaNames (j + 1)).nS ≠ "bf.n" :=
    lv_ne_lit (by decide) (by decide) _
  have hs2 : (arenaNames (j + 1)).nS ≠ "bf.m" :=
    lv_ne_lit (by decide) (by decide) _
  have hs3 : (arenaNames (j + 1)).nS ≠ "bf.r" :=
    lv_ne_lit (by decide) (by decide) _
  have hs4 : (arenaNames (j + 1)).nS ≠ "bf.v" :=
    lv_ne_lit (by decide) (by decide) _
  have hc1 : pcCc ≠ "bf.n" := lv_ne_lit (by decide) (by decide) _
  have hc2 : pcCc ≠ "bf.m" := lv_ne_lit (by decide) (by decide) _
  have hc3 : pcCc ≠ "bf.r" := lv_ne_lit (by decide) (by decide) _
  have hc4 : pcCc ≠ "bf.v" := lv_ne_lit (by decide) (by decide) _
  refine Spec.post (Spec.seq'
      (assignVar_spec (B := B) (P := BfsCellsPre j B) "bf.n" _
        (fun _ hσ => hσ.1))
      (Spec.seq'
        (assignVar_spec (B := B) (P := BfsCellsPre j B) "bf.m" _
          (fun _ hσ => hσ.2.1))
        (Spec.seq'
          (assignLit_spec (B := B) (P := BfsCellsPre j B) "bf.r" h3)
          (assignVar_spec (B := B) (P := BfsCellsPre j B) "bf.v" _
            (fun _ hσ => hσ.2.2))
          ?_)
        ?_)
      ?_) ?_
  · rintro σ σ' hσ rfl
    exact bfsCellsPre_setVar hσ hn3 hs3 hc3 _
  · rintro σ σ' hσ rfl
    exact bfsCellsPre_setVar hσ hn2 hs2 hc2 _
  · rintro σ σ' hσ rfl
    exact bfsCellsPre_setVar hσ hn1 hs1 hc1 _
  · rintro σ σ'' - ⟨τ, rfl, τ', rfl, τ'', rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a => by simp only [arrs_setVar]⟩
    · simp [vars_setVar, hn1, hn2, hn3, hn4, hs1, hs2, hs3, hs4,
        hc1, hc2, hc3, hc4]
    · simp [vars_setVar, hn1, hn2, hn3, hn4, hs1, hs2, hs3, hs4,
        hc1, hc2, hc3, hc4]
    · simp [vars_setVar, hn1, hn2, hn3, hn4, hs1, hs2, hs3, hs4,
        hc1, hc2, hc3, hc4]
    · simp [vars_setVar, hn1, hn2, hn3, hn4, hs1, hs2, hs3, hs4,
        hc1, hc2, hc3, hc4]
    · intro y k1 k2 k3 k4
      simp [vars_setVar, k1, k2, k3, k4]

/-- The two cells the supports block reads. -/
def SupCellsPre (j : ℕ) (B : ℕ) (σ : Env) : Prop :=
  σ.vars (arenaNames (j + 1)).nN < B ∧ σ.vars (arenaNames (j + 1)).nS < B

theorem supCellsPre_setVar {j B : ℕ} {σ : Env} (h : SupCellsPre j B σ)
    {x : String} (hx1 : (arenaNames (j + 1)).nN ≠ x)
    (hx2 : (arenaNames (j + 1)).nS ≠ x) (v : ℕ) :
    SupCellsPre j B (σ.setVar x v) := by
  refine ⟨?_, ?_⟩
  · rw [vars_setVar, if_neg hx1]; exact h.1
  · rw [vars_setVar, if_neg hx2]; exact h.2

/-- The supports pass's six input cells: again the radius `2 * S.R`,
and the written column `j` — the round-count pin's value of
`A.hist.length`, a compile-time constant. -/
theorem prepSupCells_spec (S : Setup L) (ℓp hbf : ℕ → ℕ) (j : ℕ)
    (h3 : 2 * S.R < B) (h4 : ℓp j < B) (h5 : hbf j < B) (h6 : j < B) :
    Spec B (SupCellsPre j B) (prepSupCells S ℓp hbf j)
      (fun σ σ' => σ'.vars "sp.n" = σ.vars (arenaNames (j + 1)).nN ∧
        σ'.vars "sp.m" = σ.vars (arenaNames (j + 1)).nS ∧
        σ'.vars "sp.r" = 2 * S.R ∧ σ'.vars "sp.l" = ℓp j ∧
        σ'.vars "sp.h" = hbf j ∧ σ'.vars "sp.p" = j ∧
        (∀ y, y ≠ "sp.n" → y ≠ "sp.m" → y ≠ "sp.r" → y ≠ "sp.l" →
          y ≠ "sp.h" → y ≠ "sp.p" → σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 12 := by
  have hn1 : (arenaNames (j + 1)).nN ≠ "sp.n" :=
    lv_ne_lit (by decide) (by decide) _
  have hn2 : (arenaNames (j + 1)).nN ≠ "sp.m" :=
    lv_ne_lit (by decide) (by decide) _
  have hn3 : (arenaNames (j + 1)).nN ≠ "sp.r" :=
    lv_ne_lit (by decide) (by decide) _
  have hn4 : (arenaNames (j + 1)).nN ≠ "sp.l" :=
    lv_ne_lit (by decide) (by decide) _
  have hn5 : (arenaNames (j + 1)).nN ≠ "sp.h" :=
    lv_ne_lit (by decide) (by decide) _
  have hn6 : (arenaNames (j + 1)).nN ≠ "sp.p" :=
    lv_ne_lit (by decide) (by decide) _
  have hs1 : (arenaNames (j + 1)).nS ≠ "sp.n" :=
    lv_ne_lit (by decide) (by decide) _
  have hs2 : (arenaNames (j + 1)).nS ≠ "sp.m" :=
    lv_ne_lit (by decide) (by decide) _
  have hs3 : (arenaNames (j + 1)).nS ≠ "sp.r" :=
    lv_ne_lit (by decide) (by decide) _
  have hs4 : (arenaNames (j + 1)).nS ≠ "sp.l" :=
    lv_ne_lit (by decide) (by decide) _
  have hs5 : (arenaNames (j + 1)).nS ≠ "sp.h" :=
    lv_ne_lit (by decide) (by decide) _
  have hs6 : (arenaNames (j + 1)).nS ≠ "sp.p" :=
    lv_ne_lit (by decide) (by decide) _
  refine Spec.post (Spec.seq'
      (assignVar_spec (B := B) (P := SupCellsPre j B) "sp.n" _
        (fun _ hσ => hσ.1))
      (Spec.seq'
        (assignVar_spec (B := B) (P := SupCellsPre j B) "sp.m" _
          (fun _ hσ => hσ.2))
        (Spec.seq'
          (assignLit_spec (B := B) (P := SupCellsPre j B) "sp.r" h3)
          (Spec.seq'
            (assignLit_spec (B := B) (P := SupCellsPre j B) "sp.l" h4)
            (Spec.seq'
              (assignLit_spec (B := B) (P := SupCellsPre j B) "sp.h" h5)
              (assignLit_spec (B := B) (P := SupCellsPre j B) "sp.p" h6)
              ?_)
            ?_)
          ?_)
        ?_)
      ?_) ?_
  · rintro σ σ' hσ rfl; exact supCellsPre_setVar hσ hn5 hs5 _
  · rintro σ σ' hσ rfl; exact supCellsPre_setVar hσ hn4 hs4 _
  · rintro σ σ' hσ rfl; exact supCellsPre_setVar hσ hn3 hs3 _
  · rintro σ σ' hσ rfl; exact supCellsPre_setVar hσ hn2 hs2 _
  · rintro σ σ' hσ rfl; exact supCellsPre_setVar hσ hn1 hs1 _
  · rintro σ σ'' - ⟨τ1, rfl, τ2, rfl, τ3, rfl, τ4, rfl, τ5, rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => by simp only [arrs_setVar]⟩
    case refine_7 =>
      intro y k1 k2 k3 k4 k5 k6
      simp [vars_setVar, k1, k2, k3, k4, k5, k6]
    all_goals
      simp [vars_setVar, hn1, hn2, hn3, hn4, hn5, hn6,
        hs1, hs2, hs3, hs4, hs5, hs6]

end Loads

/-! ## §3 The two stages, at an arbitrary channel family

`supportsCom` patches one column of the channel region, so the arena
the *profiles* stage measures and the one the *isolation* sweeps is not
the arena `restrictCom` left. Both underlying contracts
(`profilesCom_specW`, `isolateCom_specW`) are generic in the arena, and
neither reads the channel field at all; these are `SolveMachPrepComp3`'s
two wrappers with the channel family opened up. Nothing is weakened —
taking `hst := Ch.hist` recovers the landed statement. -/

section PatchedStages

variable {L n₀ B : ℕ}

open Classical in
/-- **The profiles stage at the patched child.** Verbatim
`prep_profilesStage` with the channel rows a parameter: the stage's
dimensions, colours and graph are the pre-isolation child's, and the
channel field enters none of them. -/
theorem prep_profilesStageH {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ) (hj : j ≤ S.depth)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (hst : Fin (childN S A π u) → Fin (ℓp j) →
      List (Fin (childN S A π u))) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A π u) with hist := hst }) σ ∧
          (∀ i : Fin S.width, (σ.arrs pcBi).getD (i : ℕ) 0
            = ((batchFn S A π u i : Fin (childN S A π u)) : ℕ)) ∧
          prepScr S ℓp hbf n₀ j σ)
      (profilesCom (prepProfNames j) S.width (S.pal j) S.R)
      (fun σ σ' => ArenaStW (prepMid j) (hbf j)
          ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
            (cluster S A π u) with hist := hst }) σ' ∧
        σ'.vars (arenaNames (j + 1)).nS = σ.vars (arenaNames (j + 1)).nS ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ i : Fin S.width, ∀ v : Fin (childN S A π u),
          (σ'.arrs (pcPd (i : ℕ))).getD (v : ℕ) 0 ≤ S.R + 1) ∧
        (∀ c : Fin (S.pal j + 1), ∀ v : Fin (childN S A π u + 1),
          (σ'.arrs (pcPu (c : ℕ))).getD (v : ℕ) 0 ≤ S.R + 2) ∧
        Impl.ProfileTablesMS (preG S A π u) (batchFn S A π u)
          (childColR S A π u) S.R
          (fun i v => (σ'.arrs (pcPd (i : ℕ))).getD (v : ℕ) 0)
          (fun c v => (σ'.arrs (pcPu (c : ℕ))).getD (v : ℕ) 0))
      (profilesK S.width (S.pal j + 1) (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v) S.R) :=
  (profilesCom_specW (B := B)
      (A := { (Impl.ofArena A (chanTab S ℓp j A)).restrict
        (cluster S A π u) with hist := hst })
      (nm := prepMid j) (ba := pcBi) (xb := pcXb) (vo := pcVo)
      (pdF := pcPd) (vtF := pcVt) (puF := pcPu) (batchFn S A π u)
      (prep_profNames_ok j S.width (S.pal j + 1))
      (prepWB_childN hwb A π u) (prepWB_profNs hwb A π u)
      (prepWB_R hwb) (prepWB_width hwb) (prepWB_childPal hwb hj A π u)
      (prepMid_nodup5 j) (prep_bi_notMem3 j) (prep_xb_notMemP j)
      (prep_vo_notMemP j) (fun t _ => prep_pd_notMemP j t)
      (fun c _ => prep_vt_notMemP j c)
      (fun c _ => prep_pu_notMemP j c)).pre
    (fun _ hσ =>
      ⟨hσ.1, prepScr_batchWidth hσ.2.2, hσ.2.1,
        prepScr_xb_len S ℓp hbf j π u hσ.2.2,
        prepScr_vo_len S ℓp hbf j π u hσ.2.2,
        fun t ht => prepScr_pd_len S ℓp hbf j π u hσ.2.2 t ht,
        fun c => prepScr_vt_len S ℓp hbf j π u hσ.2.2 c,
        fun c hc => prepScr_pu_len S ℓp hbf j π u hσ.2.2 c hc⟩)

open Lax12.UniformQuasiWideness (deleteVerts) in
open Classical in
/-- **The isolation at the recoloured, patched child.** Verbatim
`prep_isolateStage` with the channel rows and the colouring opened up:
by the time the isolation runs, the channel has been patched *and* the
palette moved, and neither is the arena `restrictCom` left.

The conclusion is stated at `machChild` outright — `isolate_recol_eq_machChild`
is `rfl`, so the assembled child is literally the isolation's output
arena. -/
theorem prep_isolateStageR {S : Setup L} {ℓp hbf : ℕ → ℕ}
    (hwb : PrepWB S ℓp hbf n₀ B) (j : ℕ)
    (A : Arena (S.pal j) n₀) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (Dp : Fin S.width → Fin (childN S A π u) → ℕ)
    (Dc : Fin (relPal (S.pal j)) → Fin (childN S A π u + 1) → ℕ)
    (hst : Fin (childN S A π u) → Fin (ℓp j) →
      List (Fin (childN S A π u))) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            (recol ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
                (cluster S A π u) with hist := hst })
              (Impl.recordProfilesMS S.R (childColR S A π u) Dp Dc)) σ ∧
          FinBitsW pcBb (Set.range (batchFn S A π u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (isolateCom (prepMid j) (arenaNames (j + 1)).off
        (arenaNames (j + 1)).tgt pcNo pcBb)
      (fun σ σ' =>
        ArenaStW (prepOut j) (hbf j) (machChild S A π u Dp Dc hst) σ' ∧
        σ'.vars pcNo = ∑ v : Fin (childN S A π u),
          (deleteVerts (preG S A π u)
            (Set.range (batchFn S A π u))).degree v ∧
        σ'.vars (arenaNames (j + 1)).nS = σ.vars (arenaNames (j + 1)).nS ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (isolateK (childN S A π u)
        (∑ v : Fin (childN S A π u), (preG S A π u).degree v)) :=
  ((isolateCom_specW (B := B)
      (Bar := recol ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
          (cluster S A π u) with hist := hst })
        (Impl.recordProfilesMS S.R (childColR S A π u) Dp Dc))
      (W := Set.range (batchFn S A π u)) (nmI := prepMid j)
      (oaO := (arenaNames (j + 1)).off) (taO := (arenaNames (j + 1)).tgt)
      (nsO := pcNo) (ba := pcBb)
      (by have := prepWB_childN hwb A π u
          show childN S A π u < B; omega)
      (prepWB_childNN hwb A π u)
      (prepMid_nodup5 j) (prep_bb_notMem5 j) (prep_oaO_notMem5 j)
      (prep_taO_notMem5 j) (prep_isoOff_ne_bb j)
      (prep_isoTgt_ne_bb j) (prep_isoTgt_ne_isoOff j)
      prep_no_notMem_rs (prep_no_ne_nN j) (prep_no_ne_nS j)
      (prep_nN_notMem_rs (j + 1)) (prep_nS_notMem_rs (j + 1))).pre
    (fun σ hσ =>
      ⟨hσ.1, hσ.2.1, prepScr_bb_len S ℓp hbf j π u hσ.2.2,
        prepScr_isoOff_len S ℓp hbf j π u hσ.2.2,
        prepScr_isoTgt_len S ℓp hbf j π u hσ.2.2⟩)).post
    (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.2⟩)

end PatchedStages

/-! ## §4 The chain

Fourteen steps, composed inside-out. `PrepDeliv` is the postcondition
of **every** one of them — it speaks only of the exit state, so the
fourteen `hpost` obligations are identities and all the content is in
the fourteen `hmid`s. -/

section Chain

variable {L n₀ B : ℕ}

open Classical in
/-- **What the pass delivers**, as a predicate on the exit state alone:
the assembled child at the level's own regions, its `ProfileTablesMS`
witness carried existentially, and the level's scratch descriptor
standing. This is `ChildLoadPartsScr`'s postcondition minus the three
frame clauses, which are read off the syntax at the end. -/
def PrepDeliv (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) {n₀ : ℕ} (j : ℕ) (A : Arena (S.pal j) n₀)
    (u : Fin A.N) (σ' : Env) : Prop :=
  (∃ (Dp : Fin S.width → Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
     (Dc : Fin (relPal (S.pal j)) →
        Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
    Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
        (batchFn S A ((ord A.N A.G).order) u)
        (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
      ArenaStW (arenaNames (j + 1)) (hbf (j + 1))
        (machChild S A ((ord A.N A.G).order) u Dp Dc
          (chanTabChild S ord ℓp j A u)) σ') ∧
  prepScr S ℓp hbf n₀ j σ'

open Classical in
/-- **Step 14** — the closing scalar move. `isolateCom_specW` forbids
its slot-count output cell from being the deliverable's, so the pass
ends by moving one cell; `arenaStW_setVar_nS` is that move, and the
column and row pins are consumed here, at the hand-over. -/
theorem prepChain14 (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp hbf : ℕ → ℕ) (j : ℕ)
    (hcol : ℓp (j + 1) = ℓp j) (hbd : hbf (j + 1) = hbf j)
    (hnB : n₀ * n₀ + 2 * n₀ + 3 < B)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    Spec B
      (fun σ => ∃ (Dp : Fin S.width →
            Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
          (Dc : Fin (relPal (S.pal j)) →
            Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
        Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          ArenaStW (prepOut j) (hbf j)
            (machChild S A ((ord A.N A.G).order) u Dp Dc
              (fun a (e : Fin (ℓp j)) =>
                childChan S A ((ord A.N A.G).order) u a (e : ℕ))) σ ∧
          σ.vars pcNo ≤ n₀ * n₀ ∧
          prepScr S ℓp hbf n₀ j σ)
      (.assign (arenaNames (j + 1)).nS (.var pcNo))
      (fun _ σ' => PrepDeliv S ord ℓp hbf j A u σ')
      2 := by
  refine Spec.exists2 (fun Dp Dc => ?_)
  refine (assignVar_spec (B := B) _ _ (fun σ hσ => ?_)).post ?_
  · have := hσ.2.2.1; omega
  · rintro σ σ' ⟨hPT, hAW, -, hscr⟩ rfl
    refine ⟨⟨Dp, Dc, hPT, ?_⟩, ?_⟩
    · rw [hbd]
      refine arenaStW_machChild_chanTabChild S ord ℓp j A u hcol ?_
      exact arenaStW_setVar_nS (prep_nN_ne_nS (j + 1)) hAW
    · refine prepScr_frameC hscr (fun b => by rw [arrs_setVar])
        (fun i _ => by rw [arrs_setVar]) (fun i => ?_)
      rw [vars_setVar, if_neg]
      exact lv_ne_of_base_ne (by decide) (by decide) _ _

open Classical in
/-- **Steps 13–14** — the isolation and the closing move. -/
theorem prepChain13 (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {ℓp hbf : ℕ → ℕ} (j : ℕ)
    (hcol : ℓp (j + 1) = ℓp j) (hbd : hbf (j + 1) = hbf j)
    (hwb : PrepWB S ℓp hbf n₀ B)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    Spec B
      (fun σ => ∃ (Dp : Fin S.width →
            Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
          (Dc : Fin (relPal (S.pal j)) →
            Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
        Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          ArenaStW (prepMid j) (hbf j)
            (recol ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
                (cluster S A ((ord A.N A.G).order) u) with
                hist := fun a (e : Fin (ℓp j)) =>
                  childChan S A ((ord A.N A.G).order) u a (e : ℕ) })
              (Impl.recordProfilesMS S.R
                (childColR S A ((ord A.N A.G).order) u) Dp Dc)) σ ∧
          FinBitsW pcBb
            (Set.range (batchFn S A ((ord A.N A.G).order) u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (.seq (isolateCom (prepMid j) (arenaNames (j + 1)).off
          (arenaNames (j + 1)).tgt pcNo pcBb)
        (.assign (arenaNames (j + 1)).nS (.var pcNo)))
      (fun _ σ' => PrepDeliv S ord ℓp hbf j A u σ')
      (isolateK (childN S A ((ord A.N A.G).order) u)
        (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
          (preG S A ((ord A.N A.G).order) u).degree v) + 2) := by
  refine Spec.exists2 (fun Dp Dc => ?_)
  refine Spec.seq (Spec.pre (Spec.frameA
      (prep_isolateStageR hwb j A ((ord A.N A.G).order) u Dp Dc
        (fun a (e : Fin (ℓp j)) =>
          childChan S A ((ord A.N A.G).order) u a (e : ℕ))))
      (fun σ hσ => ⟨hσ.2.1, hσ.2.2.1, hσ.2.2.2⟩))
    (prepChain14 S ord ℓp hbf j hcol hbd hwb.carrier A u) ?_
    (fun _ _ _ _ _ h => h)
  rintro σ σ' ⟨hPT, -, -, hscr⟩ ⟨⟨hAW, hno, -, -⟩, harr, hvar, hlen⟩
  refine ⟨Dp, Dc, hPT, hAW, ?_, ?_⟩
  · rw [hno]
    exact le_trans (prep_sum_degree_le_sq _)
      (Nat.mul_le_mul (prep_childN_le_root S A _ u) (prep_childN_le_root S A _ u))
  · refine prepScr_frameC hscr hlen (fun i _ => harr _ ?_) (fun i => hvar _ ?_)
    · rw [warrs_isolateCom]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _,
        lv_ne_of_base_ne (by decide) (by decide) _ _⟩
    · intro hmem
      rcases wvars_isolateCom_subset (prepMid j) _ _ pcNo pcBb _ hmem with h | h
      · exact prep_nN_notMem_rs i h
      · exact lv_ne_of_base_ne (by decide) (by decide) i 0 h

open Classical in
/-- A windowed bit region reads one array. -/
theorem finBitsW_of_eq {a : String} {n : ℕ} {X : Set (Fin n)} {σ σ' : Env}
    (h : FinBitsW a X σ) (heq : σ'.arrs a = σ.arrs a) : FinBitsW a X σ' :=
  ⟨by rw [heq]; exact h.1, fun v => by rw [heq]; exact h.2 v⟩

open Classical in
/-- **Steps 12–14** — the colour writer, then the isolation and the
move. The palette move happens here: `arenaStW_recol_frame` reads the
four unchanged regions at the pre-write state and the colour cells at
the post-write state, which is the shape the composition has. -/
theorem prepChain12 (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {ℓp hbf : ℕ → ℕ} (j : ℕ) (hj : j ≤ S.depth)
    (hcol : ℓp (j + 1) = ℓp j) (hbd : hbf (j + 1) = hbf j)
    (hwb : PrepWB S ℓp hbf n₀ B)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    Spec B
      (fun σ => ∃ (Dp : Fin S.width →
            Fin (childN S A ((ord A.N A.G).order) u) → ℕ)
          (Dc : Fin (relPal (S.pal j)) →
            Fin (childN S A ((ord A.N A.G).order) u + 1) → ℕ),
        Impl.ProfileTablesMS (preG S A ((ord A.N A.G).order) u)
            (batchFn S A ((ord A.N A.G).order) u)
            (childColR S A ((ord A.N A.G).order) u) S.R Dp Dc ∧
          (∀ (i : Fin S.width)
            (x : Fin (childN S A ((ord A.N A.G).order) u)),
            Dp i x ≤ S.R + 1) ∧
          (∀ (c : Fin (relPal (S.pal j)))
            (x : Fin (childN S A ((ord A.N A.G).order) u + 1)),
            Dc c x ≤ S.R + 2) ∧
          σ.vars (arenaNames (j + 1)).nN
            = childN S A ((ord A.N A.G).order) u ∧
          (∀ (i : Fin S.width)
            (x : Fin (childN S A ((ord A.N A.G).order) u)),
            (σ.arrs (pcPd (i : ℕ))).getD (x : ℕ) 0 = Dp i x) ∧
          (∀ (c : Fin (relPal (S.pal j)))
            (x : Fin (childN S A ((ord A.N A.G).order) u)),
            (σ.arrs (pcPu (c : ℕ))).getD (x : ℕ) 0 = Dc c x.castSucc) ∧
          ArenaStW (prepMid j) (hbf j)
            ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
                (cluster S A ((ord A.N A.G).order) u) with
                hist := fun a (e : Fin (ℓp j)) =>
                  childChan S A ((ord A.N A.G).order) u a (e : ℕ) }) σ ∧
          FinBitsW pcBb
            (Set.range (batchFn S A ((ord A.N A.G).order) u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (.seq (colWriteCom (arenaNames (j + 1)).col (arenaNames (j + 1)).nN
          pcPd pcPu pcW pcDd pcVv (relPal (S.pal j)) S.width S.R)
        (.seq (isolateCom (prepMid j) (arenaNames (j + 1)).off
            (arenaNames (j + 1)).tgt pcNo pcBb)
          (.assign (arenaNames (j + 1)).nS (.var pcNo))))
      (fun _ σ' => PrepDeliv S ord ℓp hbf j A u σ')
      (colWriteK (childN S A ((ord A.N A.G).order) u)
          (relPal (S.pal j)) S.width S.R
        + (isolateK (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) + 2)) := by
  refine Spec.exists2 (fun Dp Dc => ?_)
  refine Spec.imp (fun hprof => ?_) (fun σ hσ => hσ.1)
  refine Spec.imp (fun hpdle => ?_) (fun σ hσ => hσ.2.1)
  refine Spec.imp (fun hpule => ?_) (fun σ hσ => hσ.2.2.1)
  refine Spec.seq (Spec.pre (Spec.frameA
      (prep_colWriteStage hwb j hj A ((ord A.N A.G).order) u
        hprof hpdle hpule
        (fun a (e : Fin (ℓp j)) =>
          childChan S A ((ord A.N A.G).order) u a (e : ℕ))))
      (fun σ hσ => ⟨hσ.2.2.2.1, hσ.2.2.2.2.1, hσ.2.2.2.2.2.1,
        hσ.2.2.2.2.2.2.2.2⟩))
    (prepChain13 S ord j hcol hbd hwb A u) ?_ (fun _ _ _ _ _ h => h)
  rintro σ σ' ⟨hPT, -, -, -, -, -, hAW, hbits, hscr⟩
    ⟨⟨hcells, hlen, harr, hvar⟩, -, -, -⟩
  have hcolne : ∀ b : String, b ≠ (arenaNames (j + 1)).col →
      σ'.arrs b = σ.arrs b := harr
  have hvarne : ∀ y : String, y ≠ pcVv → y ≠ pcW → y ≠ pcDd →
      σ'.vars y = σ.vars y := hvar
  have hscr' : prepScr S ℓp hbf n₀ j σ' := by
    refine prepScr_frameC hscr hlen (fun i _ => hcolne _ ?_)
      (fun i => hvarne _ ?_ ?_ ?_) <;>
      exact lv_ne_of_base_ne (by decide) (by decide) _ _
  refine ⟨Dp, Dc, hPT, ?_, finBitsW_of_eq hbits
      (hcolne _ (lv_ne_of_base_ne (by decide) (by decide) _ _)), hscr'⟩
  refine arenaStW_recol_frame hAW (prepMid_nodup5 j)
    (hvarne _ (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _))
    (hvarne _ (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _))
    (hcolne _ (lv_ne_of_base_ne (by decide) (by decide) _ _))
    (hcolne _ (lv_ne_of_base_ne (by decide) (by decide) _ _))
    (hcolne _ (lv_ne_of_base_ne (by decide) (by decide) _ _))
    (hcolne _ (lv_ne_of_base_ne (by decide) (by decide) _ _))
    ?_ hcells
  exact prepScr_col_len_write S ℓp hbf j ((ord A.N A.G).order) u hscr'

/-- The profiles stage writes only its own two scratch regions and the
three table families. -/
theorem prep_notMem_prof_warrs (j mb Λl R : ℕ) {b : String}
    (h1 : b ≠ pcXb) (h2 : b ≠ pcVo) (h3 : ∀ t, b ≠ pcPd t)
    (h4 : ∀ c, b ≠ pcVt c) (h5 : ∀ c, b ≠ pcPu c) :
    b ∉ (profilesCom (prepProfNames j) mb Λl R).warrs := by
  intro hb
  rcases warrs_profilesCom_subset (prepProfNames j) mb Λl R b hb with
    h | h | ⟨t, -, h⟩ | ⟨c, -, h⟩ | ⟨c, -, h⟩
  · exact h1 h
  · exact h2 h
  · exact h3 t h
  · exact h4 c h
  · exact h5 c h

open Classical in
/-- **Steps 11–14** — the profiles stage, which names the two tables
the rest of the pass runs at. It measures the **pre-isolation** child
at the **parent's** palette; the batch region's exact length is the one
precondition no run could have established. -/
theorem prepChain11 (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {ℓp hbf : ℕ → ℕ} (j : ℕ) (hj : j ≤ S.depth)
    (hcol : ℓp (j + 1) = ℓp j) (hbd : hbf (j + 1) = hbf j)
    (hwb : PrepWB S ℓp hbf n₀ B)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
                (cluster S A ((ord A.N A.G).order) u) with
                hist := fun a (e : Fin (ℓp j)) =>
                  childChan S A ((ord A.N A.G).order) u a (e : ℕ) }) σ ∧
          (∀ i : Fin S.width, (σ.arrs pcBi).getD (i : ℕ) 0
            = ((batchFn S A ((ord A.N A.G).order) u i :
                Fin (childN S A ((ord A.N A.G).order) u)) : ℕ)) ∧
          σ.vars (arenaNames (j + 1)).nN
            = childN S A ((ord A.N A.G).order) u ∧
          FinBitsW pcBb
            (Set.range (batchFn S A ((ord A.N A.G).order) u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (.seq (profilesCom (prepProfNames j) S.width (S.pal j) S.R)
        (.seq (colWriteCom (arenaNames (j + 1)).col (arenaNames (j + 1)).nN
            pcPd pcPu pcW pcDd pcVv (relPal (S.pal j)) S.width S.R)
          (.seq (isolateCom (prepMid j) (arenaNames (j + 1)).off
              (arenaNames (j + 1)).tgt pcNo pcBb)
            (.assign (arenaNames (j + 1)).nS (.var pcNo)))))
      (fun _ σ' => PrepDeliv S ord ℓp hbf j A u σ')
      (profilesK S.width (S.pal j + 1)
          (childN S A ((ord A.N A.G).order) u)
          (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
            (preG S A ((ord A.N A.G).order) u).degree v) S.R
        + (colWriteK (childN S A ((ord A.N A.G).order) u)
            (relPal (S.pal j)) S.width S.R
          + (isolateK (childN S A ((ord A.N A.G).order) u)
              (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
                (preG S A ((ord A.N A.G).order) u).degree v) + 2))) := by
  refine Spec.seq (Spec.pre (Spec.frameA
      (prep_profilesStageH hwb j hj A ((ord A.N A.G).order) u
        (fun a (e : Fin (ℓp j)) =>
          childChan S A ((ord A.N A.G).order) u a (e : ℕ))))
      (fun σ hσ => ⟨hσ.1, hσ.2.1, hσ.2.2.2.2⟩))
    (prepChain12 S ord j hj hcol hbd hwb A u) ?_
    (fun _ _ _ _ _ h => h)
  rintro σ σ' ⟨-, -, hnN, hbits, hscr⟩
    ⟨⟨hAW, -, hlen, hpdle, hpule, hPT⟩, harr, hvar, -⟩
  have hnp : ∀ b : String, b ≠ pcXb → b ≠ pcVo → (∀ t, b ≠ pcPd t) →
      (∀ c, b ≠ pcVt c) → (∀ c, b ≠ pcPu c) → σ'.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 h5 =>
      harr b (prep_notMem_prof_warrs j S.width (S.pal j) S.R h1 h2 h3 h4 h5)
  have hvp : ∀ y : String, y ∉ profScalars → σ'.vars y = σ.vars y :=
    fun y hy => hvar y (fun hmem =>
      hy (wvars_profilesCom_subset (prepProfNames j) S.width (S.pal j) S.R
        y hmem))
  have hclash : ∀ b : String, ∀ t : ℕ, b ≠ pcPd t → True := fun _ _ _ => trivial
  have hbb : σ'.arrs pcBb = σ.arrs pcBb :=
    hnp _ (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (fun _ => lv_ne_of_base_ne (by decide) (by decide) _ _)
      (fun _ => lv_ne_of_base_ne (by decide) (by decide) _ _)
      (fun _ => lv_ne_of_base_ne (by decide) (by decide) _ _)
  refine ⟨_, _, hPT, hpdle, hpule, ?_, fun _ _ => rfl, fun _ _ => rfl,
    hAW, finBitsW_of_eq hbits hbb, ?_⟩
  · rw [hvp _ (prep_nN_notMem_prof (j + 1))]; exact hnN
  · refine prepScr_frameC hscr hlen (fun i _ => hnp _ ?_ ?_ ?_ ?_ ?_)
      (fun i => hvp _ (prep_nN_notMem_prof i)) <;>
      first
        | exact lv_ne_of_base_ne (by decide) (by decide) _ _
        | exact fun _ => lv_ne_of_base_ne (by decide) (by decide) _ _

/-- The supports pass writes only its parent region and the channel
region. -/
theorem prep_notMem_sup_warrs (j : ℕ) {b : String} (h1 : b ≠ pcPa)
    (h2 : b ≠ (arenaNames (j + 1)).hist) :
    b ∉ (supportsCom pcOi pcTi pcDa pcPa (arenaNames (j + 1)).hist).warrs := by
  rw [warrs_supportsCom]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1, h1, h2, h2, h2, h2⟩

open Classical in
/-- **Steps 10–14** — the supports pass. It writes one column of the
channel region, the one the round-count pin makes the numeral `j`, at
radius `2 * S.R`; `supportsPatch_eq_childChan_chanTab` is the identity
that turns the patched family into the driver's own `childChan`. -/
theorem prepChain10 (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {ℓp hbf : ℕ → ℕ} {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    (hp : PrepPins S ℓp (chanTab S ℓp) hbf Adm)
    (j : ℕ) (hj : j ≤ S.depth) (hjd : j < S.depth)
    (hcol : ℓp (j + 1) = ℓp j) (hbd : hbf (j + 1) = hbf j)
    (hwb : PrepWB S ℓp hbf n₀ B)
    (A : Arena (S.pal j) n₀) (hAdm : Adm j A) (hrowb : 2 * S.R + 1 ≤ hbf j)
    (u : Fin A.N)
    {D : Fin (childN S A ((ord A.N A.G).order) u) → ℕ}
    (hD : Lax3Proofs.Impl.BallTable (preG S A ((ord A.N A.G).order) u)
      (centreChild S A ((ord A.N A.G).order) u) (2 * S.R) D)
    (hDd : ∀ v : Fin (childN S A ((ord A.N A.G).order) u),
      D v ≤ 2 * S.R + 1) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A ((ord A.N A.G).order) u)) σ ∧
          σ.vars "sp.n" = childN S A ((ord A.N A.G).order) u ∧
          σ.vars "sp.m" = σ.vars (arenaNames (j + 1)).nS ∧
          σ.vars "sp.r" = 2 * S.R ∧ σ.vars "sp.l" = ℓp j ∧
          σ.vars "sp.h" = hbf j ∧ σ.vars "sp.p" = j ∧
          (∀ v : Fin (childN S A ((ord A.N A.G).order) u),
            (σ.arrs pcDa).getD (v : ℕ) 0 = D v) ∧
          (∀ i : Fin S.width, (σ.arrs pcBi).getD (i : ℕ) 0
            = ((batchFn S A ((ord A.N A.G).order) u i :
                Fin (childN S A ((ord A.N A.G).order) u)) : ℕ)) ∧
          σ.vars (arenaNames (j + 1)).nN
            = childN S A ((ord A.N A.G).order) u ∧
          FinBitsW pcBb
            (Set.range (batchFn S A ((ord A.N A.G).order) u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (.seq (supportsCom pcOi pcTi pcDa pcPa (arenaNames (j + 1)).hist)
        (.seq (profilesCom (prepProfNames j) S.width (S.pal j) S.R)
          (.seq (colWriteCom (arenaNames (j + 1)).col
              (arenaNames (j + 1)).nN pcPd pcPu pcW pcDd pcVv
              (relPal (S.pal j)) S.width S.R)
            (.seq (isolateCom (prepMid j) (arenaNames (j + 1)).off
                (arenaNames (j + 1)).tgt pcNo pcBb)
              (.assign (arenaNames (j + 1)).nS (.var pcNo))))))
      (fun _ σ' => PrepDeliv S ord ℓp hbf j A u σ')
      (supportsK (childN S A ((ord A.N A.G).order) u)
          (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
            (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R)
        + (profilesK S.width (S.pal j + 1)
            (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) S.R
          + (colWriteK (childN S A ((ord A.N A.G).order) u)
              (relPal (S.pal j)) S.width S.R
            + (isolateK (childN S A ((ord A.N A.G).order) u)
                (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
                  (preG S A ((ord A.N A.G).order) u).degree v) + 2)))) := by
  have hpatch := supportsPatch_eq_childChan_chanTab S ℓp j A
    ((ord A.N A.G).order) u ⟨j, prep_col_lt hp j hjd hAdm⟩
    (hp.round j A hAdm).symm hD hDd
  refine Spec.seq (Spec.pre (Spec.frameA
      (prep_supportsStage hwb hp j hj hjd A hAdm hrowb
        ((ord A.N A.G).order) u hD hDd))
      (fun σ hσ => ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1,
        hσ.2.2.2.2.2.1, hσ.2.2.2.2.2.2.1, hσ.2.2.2.2.2.2.2.1,
        hσ.2.2.2.2.2.2.2.2.2.2.2⟩))
    (prepChain11 S ord j hj hcol hbd hwb A u) ?_ (fun _ _ _ _ _ h => h)
  rintro σ σ' ⟨-, -, -, -, -, -, -, -, hbi, hnN, hbits, hscr⟩
    ⟨⟨hAW, -, -, -, hlen⟩, harr, hvar, -⟩
  have hnp : ∀ b : String, b ≠ pcPa → b ≠ (arenaNames (j + 1)).hist →
      σ'.arrs b = σ.arrs b :=
    fun b h1 h2 => harr b (prep_notMem_sup_warrs j h1 h2)
  have hvp : ∀ y : String, y ∉ spScalars → σ'.vars y = σ.vars y :=
    fun y hy => hvar y (fun hmem =>
      hy (wvars_supportsCom_subset pcOi pcTi pcDa pcPa
        (arenaNames (j + 1)).hist y hmem))
  have harena := congrArg
    (fun h : Fin (childN S A ((ord A.N A.G).order) u) → Fin (ℓp j) →
        List (Fin (childN S A ((ord A.N A.G).order) u)) =>
      ArenaStW (prepMid j) (hbf j)
        ({ (Impl.ofArena A (chanTab S ℓp j A)).restrict
            (cluster S A ((ord A.N A.G).order) u) with hist := h }) σ')
    hpatch
  refine ⟨cast harena hAW, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hnp pcBi (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _)]
    exact hbi i
  · rw [hvp _ (prep_nN_notMem_sp (j + 1))]; exact hnN
  · exact finBitsW_of_eq hbits (hnp pcBb
      (lv_ne_of_base_ne (by decide) (by decide) _ _)
      (lv_ne_of_base_ne (by decide) (by decide) _ _))
  · refine prepScr_frameC hscr hlen (fun i _ => hnp _ ?_ ?_)
      (fun i => hvp _ (prep_nN_notMem_sp i)) <;>
      exact lv_ne_of_base_ne (by decide) (by decide) _ _

open Classical in
/-- **Steps 9–14** — the supports pass's six input cells, then the
supports pass. -/
theorem prepChain9 (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {ℓp hbf : ℕ → ℕ} {Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop}
    (hp : PrepPins S ℓp (chanTab S ℓp) hbf Adm)
    (j : ℕ) (hj : j ≤ S.depth) (hjd : j < S.depth)
    (hcol : ℓp (j + 1) = ℓp j) (hbd : hbf (j + 1) = hbf j)
    (hwb : PrepWB S ℓp hbf n₀ B)
    (A : Arena (S.pal j) n₀) (hAdm : Adm j A) (hrowb : 2 * S.R + 1 ≤ hbf j)
    (u : Fin A.N)
    {D : Fin (childN S A ((ord A.N A.G).order) u) → ℕ}
    (hD : Lax3Proofs.Impl.BallTable (preG S A ((ord A.N A.G).order) u)
      (centreChild S A ((ord A.N A.G).order) u) (2 * S.R) D)
    (hDd : ∀ v : Fin (childN S A ((ord A.N A.G).order) u),
      D v ≤ 2 * S.R + 1) :
    Spec B
      (fun σ => ArenaStW (prepMid j) (hbf j)
            ((Impl.ofArena A (chanTab S ℓp j A)).restrict
              (cluster S A ((ord A.N A.G).order) u)) σ ∧
          σ.vars (arenaNames (j + 1)).nN
            = childN S A ((ord A.N A.G).order) u ∧
          σ.vars (arenaNames (j + 1)).nS
            = ∑ v : Fin (childN S A ((ord A.N A.G).order) u),
                (preG S A ((ord A.N A.G).order) u).degree v ∧
          (∀ v : Fin (childN S A ((ord A.N A.G).order) u),
            (σ.arrs pcDa).getD (v : ℕ) 0 = D v) ∧
          (∀ i : Fin S.width, (σ.arrs pcBi).getD (i : ℕ) 0
            = ((batchFn S A ((ord A.N A.G).order) u i :
                Fin (childN S A ((ord A.N A.G).order) u)) : ℕ)) ∧
          FinBitsW pcBb
            (Set.range (batchFn S A ((ord A.N A.G).order) u)) σ ∧
          prepScr S ℓp hbf n₀ j σ)
      (.seq (prepSupCells S ℓp hbf j)
        (.seq (supportsCom pcOi pcTi pcDa pcPa (arenaNames (j + 1)).hist)
          (.seq (profilesCom (prepProfNames j) S.width (S.pal j) S.R)
            (.seq (colWriteCom (arenaNames (j + 1)).col
                (arenaNames (j + 1)).nN pcPd pcPu pcW pcDd pcVv
                (relPal (S.pal j)) S.width S.R)
              (.seq (isolateCom (prepMid j) (arenaNames (j + 1)).off
                  (arenaNames (j + 1)).tgt pcNo pcBb)
                (.assign (arenaNames (j + 1)).nS (.var pcNo)))))))
      (fun _ σ' => PrepDeliv S ord ℓp hbf j A u σ')
      (12 + (supportsK (childN S A ((ord A.N A.G).order) u)
          (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
            (preG S A ((ord A.N A.G).order) u).degree v) (2 * S.R)
        + (profilesK S.width (S.pal j + 1)
            (childN S A ((ord A.N A.G).order) u)
            (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
              (preG S A ((ord A.N A.G).order) u).degree v) S.R
          + (colWriteK (childN S A ((ord A.N A.G).order) u)
              (relPal (S.pal j)) S.width S.R
            + (isolateK (childN S A ((ord A.N A.G).order) u)
                (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
                  (preG S A ((ord A.N A.G).order) u).degree v) + 2))))) := by
  have hcNB : childN S A ((ord A.N A.G).order) u < B := by
    have := prepWB_childN hwb A ((ord A.N A.G).order) u; omega
  have hcnsB : (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
      (preG S A ((ord A.N A.G).order) u).degree v) < B := by
    have := prepWB_profNs hwb A ((ord A.N A.G).order) u; omega
  refine Spec.seq (Spec.pre
      (prepSupCells_spec (B := B) S ℓp hbf j
        (by have := prepWB_twoR hwb; omega) (prepWB_lp hwb hj)
        (by have := prepWB_hb hwb hj; omega) (prepWB_level hwb hj))
      (fun σ hσ => ⟨by rw [hσ.2.1]; exact hcNB, by rw [hσ.2.2.1]; exact hcnsB⟩))
    (prepChain10 S ord hp j hj hjd hcol hbd hwb A hAdm hrowb u hD hDd) ?_
    (fun _ _ _ _ _ h => h)
  rintro σ σ' ⟨hAW, hnN, hnS, hda, hbi, hbits, hscr⟩
    ⟨e1, e2, e3, e4, e5, e6, hvp, hap⟩
  have hkeep : ∀ y : String, y ∉ spScalars → σ'.vars y = σ.vars y := by
    intro y hy
    refine hvp y ?_ ?_ ?_ ?_ ?_ ?_ <;> (rintro rfl; exact hy (by decide))
  refine ⟨arenaStW_of_eq hAW (hkeep _ (prep_nN_notMem_sp (j + 1)))
      (hkeep _ (prep_nS_notMem_sp (j + 1))) (hap _) (hap _) (hap _) (hap _)
      (hap _), ?_, ?_, e3, e4, e5, e6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, hnN]
  · rw [e2, hkeep _ (prep_nS_notMem_sp (j + 1))]
  · intro v; rw [hap]; exact hda v
  · intro i; rw [hap]; exact hbi i
  · rw [hkeep _ (prep_nN_notMem_sp (j + 1))]; exact hnN
  · exact finBitsW_of_eq hbits (hap _)
  · exact prepScr_frameC hscr (fun b => by rw [hap]) (fun i _ => hap _)
      (fun i => hkeep _ (prep_nN_notMem_sp i))

end Chain

end Lax3Proofs.Prog
