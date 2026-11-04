import Lax185574Proofs.CompRam.CalleeRun
import Lax185574Proofs.CompRam.Spec

/-!
The specification of the glue program of lem:compose.

An instance is a pair of far tuples `u₁`, `u₂` of a partial graph `G`
(`Inst`). The loop driver runs along the script `sA`, `sB` of the
trajectory from `r0` of the two root words. Round `j` of the glue reads
`uT j = lpU x (sA j) (sB j)` and writes `sA (j + 1)`. The glue only has
to behave in rounds that the machine reaches (`Reached j`: every state
before round `j` is a call whose top frame fits its question and whose
question has an answer).

`GlueSpec`: at every word length `v ≥ sI` at which the entries of the
input are below `2 ^ (v - sI)`, every halting run of round `j` writes
`sA (j + 1)` with entries below `2 ^ (v - sI - 4)`, has checked the guard
of the new question at `v - sQ`, and has checked the round test
`(2 j + 1)^4 ≤ 2 ^ (v - sQ)`. The round test makes the word length of a
halting round at least half of that of the driver, so that the
constants of the callees fit whenever the input of the composite is
admissible, however many rounds the machine needs. If
`cG (|in| + |out| + max + 1)^E ≤ 2 ^ (v - sQ)`, the round halts within
`cG (|in| + |out| + 1)^2` steps.
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus)

section inst

variable {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {l1 l2 : ℕ} (u₁ : Fin l1 → Fin n)
  (u₂ : Fin l2 → Fin n)

/-- The two tuples are an instance of far composition. -/
def Inst : Prop :=
  1 ≤ l1 ∧ 1 ≤ l2 ∧ l1 + l2 ≤ k ∧ ∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)

/-- The input word of the composite. -/
noncomputable def xT : List ℕ := xIn k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))

/-- The trajectory of the machine. -/
noncomputable def trT (j : ℕ) : Res :=
  traj G (r0 k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))) j

/-- The states of the driver. -/
noncomputable def aT (j : ℕ) : List ℕ :=
  sA G k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) j

/-- The callee outputs of the driver. -/
noncomputable def bT (j : ℕ) : List ℕ :=
  sB G k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) j

/-- The input of round `j` of the glue. -/
noncomputable def uT (j : ℕ) : List ℕ := lpU (xT G k q u₁ u₂) (aT G k q u₁ u₂ j) (bT G k q u₁ u₂ j)

/-- Round `j` is reached. -/
def Reached (j : ℕ) : Prop :=
  ∀ i < j, ∃ g S q', trT G k q u₁ u₂ i = .call (g :: S) q' ∧ Fits g.ph q' ∧ Ans G q' (ansOf G q')

end inst

/-- The guard of the question of a state. -/
def QGuard (eR eS eC v : ℕ) : Res → Prop
  | .call _ q => CGuard eR eS eC v q
  | _ => True

/-- **The specification of the glue program.** -/
structure GlueSpec (Gp : Program) (sI sQ eR eS eC cG E : ℕ) : Prop where
  sound : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (u₁ : Fin l1 → Fin n)
      (u₂ : Fin l2 → Fin n), Inst G k q u₁ u₂ → ∀ j, Reached G k q u₁ u₂ j → ∀ v, sI ≤ v →
      (∀ e ∈ uT G k q u₁ u₂ j, e < 2 ^ (v - sI)) →
      ∀ o t, RunsTo v Gp (uT G k q u₁ u₂ j) o t →
        o = aT G k q u₁ u₂ (j + 1) ∧ (∀ e ∈ o, e < 2 ^ (v - sI - 4)) ∧
          (2 * j + 1) ^ 4 ≤ 2 ^ (v - sQ) ∧ QGuard eR eS eC (v - sQ) (trT G k q u₁ u₂ j)
  run : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (u₁ : Fin l1 → Fin n)
      (u₂ : Fin l2 → Fin n), Inst G k q u₁ u₂ → ∀ j, Reached G k q u₁ u₂ j → ∀ v, sI ≤ v →
      (∀ e ∈ uT G k q u₁ u₂ j, e < 2 ^ (v - sI)) →
      cG * ((uT G k q u₁ u₂ j).length + (aT G k q u₁ u₂ (j + 1)).length +
          maxEntry (uT G k q u₁ u₂ j ++ aT G k q u₁ u₂ (j + 1)) + 1) ^ E ≤ 2 ^ (v - sQ) →
      ∃ t ≤ cG * ((uT G k q u₁ u₂ j).length + (aT G k q u₁ u₂ (j + 1)).length + 1) ^ 2,
        RunsTo v Gp (uT G k q u₁ u₂ j) (aT G k q u₁ u₂ (j + 1)) t

/-! ### Facts about the script of an instance -/

section facts

variable {n : ℕ} {G : PartialGraph (Fin n)} {k q : ℕ} {l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
  {u₂ : Fin l2 → Fin n}

theorem uT_zero : uT G k q u₁ u₂ 0 = [0, (xT G k q u₁ u₂).length] ++ xT G k q u₁ u₂ ++ [0] :=
  lpU_first _

theorem aT_zero : aT G k q u₁ u₂ 0 = lpA0 (xT G k q u₁ u₂) := rfl

theorem bT_zero : bT G k q u₁ u₂ 0 = [] := rfl

/-- **The script of an instance.** The trajectory ends after `m` calls
with the word of the far composition, and every round up to `m` is
reached. -/
theorem inst_script (h : Inst G k q u₁ u₂) :
    xT G k q u₁ u₂ = toWord (tree G k q u₁, tree G k q u₂) ∧
    ∃ m, m + 1 ≤ 5 * (Node.count (node G k q u₁) + Node.count (node G k q u₂)) ^ (q + 1) ∧
      trT G k q u₁ u₂ m = .done (toWord (tree G k q (Fin.append u₁ u₂))) ∧
      Reached G k q u₁ u₂ m ∧ ∀ j < m, ∃ g S q', trT G k q u₁ u₂ j = .call (g :: S) q' ∧
        Fits g.ph q' ∧ Ans G q' (ansOf G q') ∧ RankLe (k + q + 1) q' := by
  obtain ⟨h1, h2, hk, hfar⟩ := h
  obtain ⟨hx, m, hm, hend, hcall⟩ := script_facts G k q l1 l2 u₁ u₂ h1 h2 hk hfar
  refine ⟨hx, m, hm, hend, fun i hi => ?_, hcall⟩
  obtain ⟨g, S, q', e, hf, hA, -⟩ := hcall i hi
  exact ⟨g, S, q', e, hf, hA⟩

theorem aT_succ (j : ℕ) : aT G k q u₁ u₂ (j + 1) = outW (j + 1) (trT G k q u₁ u₂ j) := rfl

theorem bT_succ (j : ℕ) : bT G k q u₁ u₂ (j + 1) = ansR G (trT G k q u₁ u₂ j) := rfl

theorem lpQ_aT {j : ℕ} {S : List Fr} {q' : Qry} (h : trT G k q u₁ u₂ j = .call S q') :
    lpQ (aT G k q u₁ u₂ (j + 1)) = qWord q' := by
  rw [aT_succ, h]; exact lpQ_outW _ _ _

theorem head_aT {j : ℕ} {S : List Fr} {q' : Qry} (h : trT G k q u₁ u₂ j = .call S q') :
    (aT G k q u₁ u₂ (j + 1)).head? ≠ some 0 ∧ aT G k q u₁ u₂ (j + 1) ≠ [] := by
  rw [aT_succ, h]; exact ⟨by simp [outW], by simp [outW]⟩

theorem bT_call {j : ℕ} {S : List Fr} {q' : Qry} (h : trT G k q u₁ u₂ j = .call S q') :
    bT G k q u₁ u₂ (j + 1) = ansWord q' (ansOf G q') := by
  rw [bT_succ, h]; rfl

theorem aT_done {m : ℕ} {z : List ℕ} (h : trT G k q u₁ u₂ m = .done z) :
    aT G k q u₁ u₂ (m + 1) = 0 :: z := by
  rw [aT_succ, h]; rfl

end facts

end Lax185574Proofs.CompRam
