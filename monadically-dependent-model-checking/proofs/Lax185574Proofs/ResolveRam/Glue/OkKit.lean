import Lax185574Proofs.MC.Glue.Out

/-!
Tools for the check that the glue program of lem:resolve-lift compiles.

`com_ok_mono`: a command that compiles in a layout compiles in every
larger layout. `satLit_ok'` and `pushL_ok'` are the checks of the
commands whose shape depends on a number or a list, in any layout that
has their names.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax185574Proofs.MC Lax185574Proofs.MC.Glue

theorem expr_ok_mono {L L' : Layout} (hs : L.scalars ⊆ L'.scalars) (ha : L.arrays ⊆ L'.arrays)
    (ht : L.temps ≤ L'.temps) : ∀ (e : Expr) (d : ℕ), Expr.Ok L e d → Expr.Ok L' e d
  | .lit _, _, _ => trivial
  | .var _, _, h => by simp only [Expr.Ok] at h ⊢; exact hs h
  | .get _ i, d, h => by
    simp only [Expr.Ok] at h ⊢
    exact ⟨ha h.1, expr_ok_mono hs ha ht i d h.2.1, lt_of_lt_of_le h.2.2 ht⟩
  | .bin _ e f, d, h => by
    simp only [Expr.Ok] at h ⊢
    exact ⟨expr_ok_mono hs ha ht f d h.1, expr_ok_mono hs ha ht e (d + 1) h.2.1, lt_of_lt_of_le h.2.2 ht⟩

/-- **A larger layout.** A command that compiles in a layout compiles in
every layout with more scalars, more arrays and more temporaries. -/
theorem com_ok_mono {L L' : Layout} {c : Com} (h : Com.Ok L c) (hs : L.scalars ⊆ L'.scalars)
    (ha : L.arrays ⊆ L'.arrays) (ht : L.temps ≤ L'.temps) : Com.Ok L' c := by
  have he := expr_ok_mono hs ha ht
  induction c with
  | skip => trivial
  | assign x e => simp only [Com.Ok] at h ⊢; exact ⟨hs h.1, he e 0 h.2⟩
  | store a i e =>
    simp only [Com.Ok] at h ⊢
    exact ⟨ha h.1, he i 0 h.2.1, he e 1 h.2.2.1, lt_of_lt_of_le h.2.2.2 ht⟩
  | seq c d ihc ihd => simp only [Com.Ok] at h ⊢; exact ⟨ihc h.1, ihd h.2⟩
  | ite b c d ihc ihd =>
    simp only [Com.Ok, Cond.Ok] at h ⊢; exact ⟨he _ 0 h.1, ihc h.2.1, ihd h.2.2⟩
  | «while» b c ih => simp only [Com.Ok, Cond.Ok] at h ⊢; exact ⟨he _ 0 h.1, ih h.2⟩
  | read x => simp only [Com.Ok] at h ⊢; exact hs h
  | write e => simp only [Com.Ok] at h ⊢; exact ⟨he e 0 h.1, lt_of_lt_of_le h.2 ht⟩

/-- The saturated literal compiles in every layout with its scalar,
`W` and two temporaries. -/
theorem satLit_ok' {L : Layout} {z : String} (hz : z ∈ L.scalars) (hW : "W" ∈ L.scalars)
    (ht : 2 ≤ L.temps) : ∀ N, Com.Ok L (satLit z N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [satLit]
    split_ifs with h1 h2
    · simp [Com.Ok, Expr.Ok, hz]
    · refine ⟨ih _ (by omega), ?_, ?_⟩
      · simp only [satAdd, Com.Ok, Cond.Ok, condExpr, Expr.Ok]; simp [hz, hW]; omega
      · simp only [satInc, Com.Ok, Cond.Ok, condExpr, Expr.Ok]; simp [hz, hW]; omega
    · refine ⟨ih _ (by omega), ?_, trivial⟩
      simp only [satAdd, Com.Ok, Cond.Ok, condExpr, Expr.Ok]; simp [hz, hW]; omega

/-- A push of a list of values compiles in every layout with its array,
its pointer and two temporaries, when every value compiles at depth `1`. -/
theorem pushL_ok' {L : Layout} {a pv : String} (ha : a ∈ L.arrays) (hpv : pv ∈ L.scalars)
    (ht : 2 ≤ L.temps) : ∀ es : List Expr, (∀ e ∈ es, Expr.Ok L e 1) → Com.Ok L (pushL a pv es)
  | [], _ => trivial
  | e :: es, h => by
    refine ⟨?_, pushL_ok' ha hpv ht es (fun e' he' => h e' (by simp [he']))⟩
    simp only [push1, Com.Ok, Expr.Ok]
    exact ⟨⟨ha, hpv, h e (by simp), by omega⟩, hpv, trivial, hpv, by omega⟩

/-- A push of a list of literals. -/
theorem pushLits_ok' {L : Layout} (ha : "OB" ∈ L.arrays) (hpv : "po" ∈ L.scalars) (ht : 2 ≤ L.temps)
    (l : List ℕ) : Com.Ok L (pushLits l) :=
  pushL_ok' ha hpv ht _ (fun e he => by
    simp only [List.mem_map] at he; obtain ⟨v, -, rfl⟩ := he; trivial)

end Lax185574Proofs.ResolveRam.Glue
