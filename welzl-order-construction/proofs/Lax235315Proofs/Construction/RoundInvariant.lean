import Lax235315Proofs.Construction.BitArrays
import Lax235315Proofs.Construction.ActiveBookkeeping
import Lax235315Proofs.Construction.Iterations

/-! Persistent source state for the reduction loop. The frontier ties the
numeric counters to actual activity arrays and the checked shrinking history. -/

namespace Lax235315Proofs.Construction.RoundInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.DriverSetup
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.BitArrays
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.Iterations
open Lax235315Proofs.Construction.RadixEight

/-- Read the represented numeric array with the source's default value. -/
def view (σ : Env) (a : String) (i : ℕ) : ℕ := (σ.arrs a).getD i 0

lemma view_of_array {σ : Env} {a : String} {n : ℕ} {f : ℕ → ℕ}
    (h : σ.arrs a = arrOf n f) {i : ℕ} (hi : i < n) : view σ a i = f i := by
  simp [view, h, List.getD_eq_getElem?_getD, getElem?_arrOf f hi]

lemma array_shape {σ : Env} {a : String} {n : ℕ}
    (h : (σ.arrs a).length = n) : σ.arrs a = arrOf n (view σ a) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · rw [getElem?_arrOf _ hi]
    have hi' : i < (σ.arrs a).length := by omega
    simp [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

def InputBits (σ : Env) : Prop := ∀ v ∈ σ.inp, v ≤ 1

lemma inputBits_bigStep {B k : ℕ} {c : Com} {σ σ' : Env}
    (hr : BigStepB B c σ σ' k) (h : InputBits σ) : InputBits σ' := by
  induction hr with
  | skip => exact h
  | assign he => exact h
  | store hi he hk => exact h
  | seq h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | ite_true hb hc ih => exact ih h
  | ite_false hb hc ih => exact ih h
  | while_true hb hc hw ihc ihw => exact ihw (ihc h)
  | while_false hb => exact h
  | @read σ a v rest hin =>
    intro x hx
    exact h x (by rw [hin]; simp [hx])
  | write he => exact h

lemma inputBits_run {B C : ℕ} {c : Com} {σ σ' : Env}
    (hr : Run B c σ σ' C) (h : InputBits σ) : InputBits σ' := by
  obtain ⟨k, _, hr⟩ := hr
  exact inputBits_bigStep hr h

/-- Static graph data, storage bounds and unconsumed random bits. -/
structure Workspace (B c n : ℕ) (x : List ℕ) (σ : Env) : Prop where
  bounded : ValuesBounded B σ
  parameter : σ.vars "c" = c
  vertices : σ.vars "n" = n
  edges : σ.vars "m" = edgeCount x
  logarithm : σ.vars "L" = Nat.clog 2 n
  radixSize : σ.vars "qpow" = 2 ^ Nat.clog 2 n
  offsets : σ.arrs "off" = arrOf (n + 1) (offset x)
  targets : σ.arrs "tgt" = arrOf (2 * edgeCount x) (target x)
  lengths : ∀ a, (σ.arrs a).length = welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a
  randomInput : InputBits σ
  output : σ.out = []

lemma Workspace.vertex_array {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Workspace B c n x σ) {a : String}
    (hoff : a ≠ "off") (htgt : a ≠ "tgt") (hcount : a ≠ "count") :
    σ.arrs a = arrOf n (view σ a) :=
  array_shape (by rw [h.lengths, welzlExt_other _ _ _ hoff htgt hcount])

lemma Workspace.value_bound {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Workspace B c n x σ) {a : String} {i : ℕ}
    (hi : i < (σ.arrs a).length) : view σ a i < B := by
  apply h.bounded.arrays a
  simp only [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- Successful frontier before an attempted reduction. The exact log-content
certificate is kept separately; this invariant accounts for its occupied size. -/
structure Frontier (B c n : ℕ) (x : List ℕ) (σ : Env) : Prop where
  workspace : Workspace B c n x σ
  success : σ.vars "good" = 1
  activeCount : σ.vars "acount" = (activeVertices n (view σ "activeA")).card
  nonemptyA : 0 < n → (activeVertices n (view σ "activeA")).Nonempty
  nonemptyB : 0 < n → (activeVertices n (view σ "activeB")).Nonempty
  activeABits : ArrayBits "activeA" σ
  activeBBits : ArrayBits "activeB" σ
  nextABits : ArrayBits "nextA" σ
  nextBBits : ArrayBits "nextB" σ
  conservation : σ.vars "removedCount" + σ.vars "acount" = n
  shrinking : ShrinkingRun (c ^ 2) (12 * c ^ 2 * Nat.clog 2 n)
    n (σ.vars "round") (σ.vars "acount")

lemma activeVertices_of_ones {n : ℕ} {σ : Env} {a : String}
    (ha : σ.arrs a = arrOf n (fun _ => 1)) :
    activeVertices n (view σ a) = Finset.range n := by
  ext i
  rw [mem_activeVertices, Finset.mem_range]
  exact ⟨And.left, fun hi => ⟨hi, view_of_array ha hi⟩⟩

/-- Deterministic setup establishes the frontier for every finite tape. -/
lemma setup_frontier {c n T : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (ρ : Fin T → Bool) :
    ∃ σ, Run (sourceBound c x) setup
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ)) σ (40 * (x.length + Nat.clog 2 n + 1)) ∧
      Frontier (sourceBound c x) c n x σ ∧ σ.inp = bitTape ρ := by
  obtain ⟨σ, hr, hready, hb⟩ := setup_ready_bounded (c := c) hx ρ
  have hbits : InputBits σ := by
    intro v hv
    rw [hready.input] at hv
    simp only [bitTape, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    split <;> omega
  have hA := activeVertices_of_ones hready.activeA
  have hB := activeVertices_of_ones hready.activeB
  refine ⟨σ, hr, ?_, hready.input⟩
  refine ⟨⟨hb, hready.parameter, hready.vertices, hready.edges,
    hready.logarithm, hready.radixSize, hready.offsets, hready.targets,
    hready.lengths, hbits, hready.output⟩, hready.success, ?_, ?_, ?_, ?_, ?_,
    BitArrays.run_preserves hr (by decide) (init_arrayBits _ _ _),
    BitArrays.run_preserves hr (by decide) (init_arrayBits _ _ _), ?_, ?_⟩
  · rw [hready.activeCount, hA, Finset.card_range]
  · intro hn; rw [hA]; exact ⟨0, Finset.mem_range.mpr hn⟩
  · intro hn; rw [hB]; exact ⟨0, Finset.mem_range.mpr hn⟩
  · intro v hv
    rw [hready.activeA] at hv
    simp [arrOf] at hv
    omega
  · intro v hv
    rw [hready.activeB] at hv
    simp [arrOf] at hv
    omega
  · simp [hready.removedCount, hready.activeCount]
  · rw [hready.round, hready.activeCount]; exact ShrinkingRun.base

/-- A reduction round cannot corrupt the input graph or workspace. -/
lemma Workspace.reductionRound {B C c n : ℕ} {x : List ℕ} {σ σ' : Env}
    (h : Workspace B c n x σ) (hr : Run B reductionRound σ σ' C) :
    Workspace B c n x σ' := by
  refine ⟨SourceBounds.run_preserves hr h.bounded,
    (hr.frame_var "c" (by decide)).trans h.parameter,
    (hr.frame_var "n" (by decide)).trans h.vertices,
    (hr.frame_var "m" (by decide)).trans h.edges,
    (hr.frame_var "L" (by decide)).trans h.logarithm,
    (hr.frame_var "qpow" (by decide)).trans h.radixSize,
    (hr.frame_arr "off" (by decide)).trans h.offsets,
    (hr.frame_arr "tgt" (by decide)).trans h.targets,
    fun a => (run_array_length_eq hr a).trans (h.lengths a),
    inputBits_run hr h.randomInput, ?_⟩
  exact (hr.out_eq (by decide)).trans h.output

end Lax235315Proofs.Construction.RoundInvariant
