import Lax185574Proofs.MainRam.ValidOut

/-!
The validation program assembled, and the facts that connect its checks
with `ValidScript`.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Simulation
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax271696.GraphEncoding Lax185574Proofs.Compose
open Classical

def restPh : Com := .seq opPh (.seq colPh (.seq injPh (.seq stepPh (.seq finColPh finMatPh))))

def vCom : Com :=
  .seq readPh (.seq adjPh (.seq parsePh (.seq (.ite (.eq (.var "ok") (.lit 1)) restPh .skip)
    outPh)))

def vLayout : Layout where
  scalars := ["L", "X1", "cnt", "i", "v", "n", "E", "nF", "a", "j", "hi", "ok", "m", "t", "b",
    "op", "P", "Q", "k"]
  arrays := ["Y", "of", "tg", "F", "A", "col", "c2", "S", "S2"]
  temps := 16

theorem vCom_ok : Com.Ok vLayout vCom := by
  simp [vCom, restPh, readPh, readArr, adjPh, adjRow, adjBody, parsePh, opPh, chkIf, opIdx, colPh,
    rowFill, injPh, injCond, eqE, eqX, finColPh, finMatPh, finE, rm, stepPh, stepBody, mergeC, eM,
    eqColQ, resolveC, eR, btwE, matFill, outPh, outValid, outInvalid, wArr, forUp, vLayout,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr]

/-! ### The graph -/

theorem list_eq_arrOf (l : List ℕ) : l = arrOf l.length (fun i => l.getD i 0) := by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp [arrOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

theorem offset_eq {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    {i : ℕ} (hi : i ≤ n) : offset g i = (ofL g n).getD i 0 := by
  have hl := hg.length_eq
  simp only [offset, ofL, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (by omega)]

theorem target_eq {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (j : ℕ) : target g j = (tgL g n).getD j 0 := by
  simp only [target, tgL, hg.vertexCount_eq, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem inBlock_iff {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (u v : Fin n) : InBlock (fun i => (ofL g n).getD i 0) (fun j => (tgL g n).getD j 0) u v ↔
      G.Adj u v := by
  rw [hg.adj_iff u v]
  unfold InBlock
  dsimp only
  rw [← offset_eq hg (by omega), ← offset_eq hg (by have := u.isLt; omega)]
  simp only [← target_eq hg]

/-! ### The checks and `ValidScript` -/

/-- What the program checks, quantified over numbers. -/
def Checks {n : ℕ} (G : SimpleGraph (Fin n)) (g y : List ℕ) : Prop :=
  Shape n y ∧ (∀ t < numSteps n y, y.getD (n + 2 + 3 * t) 0 < 3) ∧
    (∀ u < n, ∀ v < n, ¬ (u ≠ v ∧ y.getD (u + 1) 0 = y.getD (v + 1) 0)) ∧
    (∀ v < n, (simFold n y (numSteps n y)).col v = (simFold n y (numSteps n y)).col 0) ∧
    (∀ u < n, ∀ v < n, u = v ∨ ((simFold n y (numSteps n y)).st u v = 1 ∧
      InBlock (fun i => (ofL g n).getD i 0) (fun j => (tgL g n).getD j 0) u v) ∨
      ((simFold n y (numSteps n y)).st u v = 2 ∧
      ¬ InBlock (fun i => (ofL g n).getD i 0) (fun j => (tgL g n).getD j 0) u v))

theorem validScript_iff_checks {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ}
    (hg : EncodesGraph g n G) (y : List ℕ) : ValidScript n G y ↔ Checks G g y := by
  rw [validScript_iff, parseOK_iff]
  unfold Checks
  constructor
  · rintro ⟨⟨hS, hops⟩, hinj, hcol, hfin⟩
    have hne : ∀ {u v : ℕ} (hu : u < n) (hv : v < n), u ≠ v →
        (⟨u, hu⟩ : Fin n) ≠ ⟨v, hv⟩ := fun hu hv h e => h (congrArg Fin.val e)
    refine ⟨hS, hops, fun u hu v hv h => hinj ⟨u, hu⟩ ⟨v, hv⟩ (hne hu hv h.1) h.2,
      fun v hv => hcol ⟨v, hv⟩, fun u hu v hv => ?_⟩
    by_cases huv : u = v
    · exact Or.inl huv
    · right
      rcases hfin ⟨u, hu⟩ ⟨v, hv⟩ (hne hu hv huv) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, (inBlock_iff hg ⟨u, hu⟩ ⟨v, hv⟩).2 h2⟩
      · right; exact ⟨h1, fun h => h2 ((inBlock_iff hg ⟨u, hu⟩ ⟨v, hv⟩).1 h)⟩
  · rintro ⟨hS, hops, hinj, hcol, hfin⟩
    refine ⟨⟨hS, hops⟩, fun u v huv h => hinj u u.isLt v v.isLt ⟨fun e => huv (Fin.ext e), h⟩,
      fun v => hcol v v.isLt, fun u v huv => ?_⟩
    rcases hfin u u.isLt v v.isLt with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (Fin.ext h) huv
    · left; exact ⟨h1, (inBlock_iff hg u v).1 h2⟩
    · right; exact ⟨h1, fun h => h2 ((inBlock_iff hg u v).2 h)⟩

end Lax185574Proofs.MainRam
