import Lax235315Proofs.Construction.RecordedHistory
import Lax235315Proofs.Construction.RoundInvariant

/-! The chronological graph history attached to concrete source memory. -/
namespace Lax235315Proofs.Construction.StoredHistory
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.RecordedHistory
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.ReadKeys

/-- Every accepted reduction is connected to the actual deletion log and
round-boundary arrays. Unused log entries retain valid vertex indices too. -/
structure Stored {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (σ : Env) where
  A : ℕ → Set (Fin n)
  C : ℕ → Set (Fin n)
  boundary : ℕ → ℕ
  history : History G k (σ.vars "round") A C boundary
    (view σ "removed") (view σ "removedRep")
  initialA : A 0 = Set.univ
  initialC : C 0 = Set.univ
  currentA : A (σ.vars "round") = {v : Fin n | view σ "activeA" v.val = 1}
  currentC : C (σ.vars "round") = {v : Fin n | view σ "activeB" v.val = 1}
  starts : ∀ r < σ.vars "round", view σ "roundStart" r = boundary r
  ends : ∀ r < σ.vars "round", view σ "roundEnd" r = boundary (r + 1)
  monotone : ∀ r s, r ≤ s → s ≤ σ.vars "round" → boundary r ≤ boundary s
  capacity : ∀ r ≤ σ.vars "round", boundary r ≤ n
  used : boundary (σ.vars "round") = σ.vars "removedCount"
  removedBound : ∀ i < n, view σ "removed" i < n
  representativeBound : ∀ i < n, view σ "removedRep" i < n

/-- Scratch computations leave the stored graph history unchanged. -/
def Stored.frame {n k : ℕ} {G : SimpleGraph (Fin n)} {σ τ : Env}
    (h : Stored G k σ)
    (hround : τ.vars "round" = σ.vars "round")
    (hused : τ.vars "removedCount" = σ.vars "removedCount")
    (ha : τ.arrs "activeA" = σ.arrs "activeA")
    (hb : τ.arrs "activeB" = σ.arrs "activeB")
    (hs : τ.arrs "roundStart" = σ.arrs "roundStart")
    (he : τ.arrs "roundEnd" = σ.arrs "roundEnd")
    (hr : τ.arrs "removed" = σ.arrs "removed")
    (hp : τ.arrs "removedRep" = σ.arrs "removedRep") : Stored G k τ where
  A := h.A
  C := h.C
  boundary := h.boundary
  history := by
    have vr : view τ "removed" = view σ "removed" := by funext i; simp [view, hr]
    have vp : view τ "removedRep" = view σ "removedRep" := by funext i; simp [view, hp]
    simpa only [hround, vr, vp] using h.history
  initialA := h.initialA
  initialC := h.initialC
  currentA := by simpa only [hround, view, ha] using h.currentA
  currentC := by simpa only [hround, view, hb] using h.currentC
  starts := by simpa only [hround, view, hs] using h.starts
  ends := by simpa only [hround, view, he] using h.ends
  monotone := by simpa only [hround] using h.monotone
  capacity := by simpa only [hround] using h.capacity
  used := by simpa only [hround, hused] using h.used
  removedBound := by simpa only [view, hr] using h.removedBound
  representativeBound := by simpa only [view, hp] using h.representativeBound

/-- At zero rounds, all vertices are active and both logs contain zero. -/
def initial {n k : ℕ} (G : SimpleGraph (Fin n)) {σ : Env}
    (hround : σ.vars "round" = 0) (hused : σ.vars "removedCount" = 0)
    (ha : ∀ i < n, view σ "activeA" i = 1)
    (hb : ∀ i < n, view σ "activeB" i = 1)
    (hr : ∀ i < n, view σ "removed" i = 0)
    (hp : ∀ i < n, view σ "removedRep" i = 0) : Stored G k σ where
  A := fun _ => Set.univ
  C := fun _ => Set.univ
  boundary := fun _ => 0
  history := ⟨by intro r hr; omega⟩
  initialA := rfl
  initialC := rfl
  currentA := by ext v; simp [ha v.val v.isLt]
  currentC := by ext v; simp [hb v.val v.isLt]
  starts := by intro r hr; omega
  ends := by intro r hr; omega
  monotone := by intros; omega
  capacity := by intros; omega
  used := hused.symm
  removedBound := by intro i hi; rw [hr i hi]; omega
  representativeBound := by intro i hi; rw [hp i hi]; omega

open Lax235315Proofs.Construction.WelzlSetup
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.DriverSetup
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.MarkingMath
open Lax195003.WordRamRandomness Lax11.GraphEncoding
open Lax195003.WelzlOrdersInGraphs

/-- Setup creates the empty history in the same concrete state as its ready
workspace; the unchanged zero logs supply all vertex-index bounds. -/
lemma setup_stored_ready {c n k T : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (ρ : Fin T → Bool) :
    ∃ σ, Run (sourceBound c x) setup
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ)) σ (40 * (x.length + Nat.clog 2 n + 1)) ∧
      Ready c n x (bitTape ρ) σ ∧ ValuesBounded (sourceBound c x) σ ∧
      Nonempty (Stored G k σ) := by
  obtain ⟨σ, hr, hready, hb⟩ := setup_ready_bounded hx ρ
  refine ⟨σ, hr, hready, hb, ⟨initial G hready.round hready.removedCount
    (fun i hi => view_of_array hready.activeA hi)
    (fun i hi => view_of_array hready.activeB hi) ?_ ?_⟩⟩
  · intro i hi
    apply view_of_array (f := fun _ => 0) (n := n) _ hi
    rw [hr.frame_arr "removed" (by decide)]
    simp [initEnv, welzlExt, replicate_eq_arrOf]
  · intro i hi
    apply view_of_array (f := fun _ => 0) (n := n) _ hi
    rw [hr.frame_arr "removedRep" (by decide)]
    simp [initEnv, welzlExt, replicate_eq_arrOf]

/-- At a successful terminal frontier, the stored history yields execution
of the literal output routine and exactly the paper's crossing bound. -/
lemma Stored.reconstructAndWrite_correct {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {σ : Env}
    (h : Stored G (6 * c ^ 2 * Nat.clog 2 n) σ)
    (hf : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 1 < n) (hnB : n < B)
    (hsmall : σ.vars "acount" ≤ 12 * c ^ 2 * Nat.clog 2 n) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) τ.out ∧
      τ.inp = σ.inp := by
  have arr (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt") (h₃ : a ≠ "count") :=
    hf.workspace.vertex_array h₁ h₂ h₃
  have hr := hf.shrinking.rounds_succ_le_clog hc hn
  have hlog := clog_le_vertices n
  apply h.history.reconstructAndWrite_correct h.initialA h.initialC h.currentA
    (q := 12 * c ^ 2 * Nat.clog 2 n)
  · rw [h.currentA, activeSet_ncard, ← hf.activeCount]
    exact hsmall
  · ring_nf; exact le_rfl
  · calc
      (σ.vars "round" + 1) * (12 * c ^ 2 * Nat.clog 2 n) ≤
          Nat.clog 2 n * (12 * c ^ 2 * Nat.clog 2 n) := Nat.mul_le_mul_right _ hr
      _ = 12 * c ^ 2 * (Nat.clog 2 n) ^ 2 := by ring
  · exact hf.workspace.vertices
  · rfl
  · omega
  · exact hnB
  · exact hf.workspace.output
  · exact arr "activeA" (by decide) (by decide) (by decide)
  · exact arr "nextVertex" (by decide) (by decide) (by decide)
  · exact arr "roundStart" (by decide) (by decide) (by decide)
  · exact arr "roundEnd" (by decide) (by decide) (by decide)
  · exact arr "removed" (by decide) (by decide) (by decide)
  · exact arr "removedRep" (by decide) (by decide) (by decide)
  · exact h.starts
  · exact h.ends
  · intro r hr; exact h.monotone r (r + 1) (by omega) (by omega)
  · exact h.capacity
  · exact h.removedBound
  · exact h.representativeBound
  · intro i hi
    exact hf.workspace.value_bound (by rw [hf.workspace.lengths]; exact hi)
  · intro i hi
    exact hf.workspace.value_bound (by rw [hf.workspace.lengths]; exact hi)
  · intro hnpos he
    obtain ⟨v, hv⟩ := hf.nonemptyA hnpos
    have hm := mem_activeVertices.mp hv
    have hs : v ∈ scanList (view σ "activeA") 0 n := mem_scanList.mpr ⟨by omega, by simpa using hm⟩
    rw [he] at hs
    exact List.not_mem_nil hs

/-- Append an accepted step to the concrete history. The premises are the
actual commit's counter, boundary-array, prefix and value postconditions. -/
def Stored.append {n k : ℕ} {G : SimpleGraph (Fin n)} {σ τ : Env}
    (h : Stored G k σ) {boundary' : ℕ → ℕ}
    (hround : τ.vars "round" = σ.vars "round" + 1)
    (hboundary : ∀ r ≤ σ.vars "round", boundary' r = h.boundary r)
    (hnew : boundary' (σ.vars "round" + 1) = τ.vars "removedCount")
    (hinc : σ.vars "removedCount" ≤ τ.vars "removedCount")
    (hcap : τ.vars "removedCount" ≤ n)
    (hstarts : ∀ r < τ.vars "round", view τ "roundStart" r = boundary' r)
    (hends : ∀ r < τ.vars "round", view τ "roundEnd" r = boundary' (r + 1))
    (hremoved : ∀ i < σ.vars "removedCount", view τ "removed" i = view σ "removed" i)
    (hreps : ∀ i < σ.vars "removedCount", view τ "removedRep" i = view σ "removedRep" i)
    (hremBound : ∀ i < n, view τ "removed" i < n)
    (hrepBound : ∀ i < n, view τ "removedRep" i < n)
    (s : RecordedStep G k (σ.vars "round") (h.A (σ.vars "round"))
      (h.C (σ.vars "round")) {v : Fin n | view τ "activeA" v.val = 1}
      {v : Fin n | view τ "activeB" v.val = 1} boundary'
      (view τ "removed") (view τ "removedRep")) : Stored G k τ where
  A := Function.update h.A (σ.vars "round" + 1) {v : Fin n | view τ "activeA" v.val = 1}
  C := Function.update h.C (σ.vars "round" + 1) {v : Fin n | view τ "activeB" v.val = 1}
  boundary := boundary'
  history := by
    rw [hround]
    exact h.history.append hboundary
      (fun r hr => h.monotone r (r + 1) (by omega) (by omega))
      (fun r hr => h.monotone (r + 1) (σ.vars "round") (by omega) le_rfl)
      (by simpa only [h.used] using hremoved)
      (by simpa only [h.used] using hreps) s
  initialA := by simpa using h.initialA
  initialC := by simpa using h.initialC
  currentA := by simp [hround]
  currentC := by simp [hround]
  starts := hstarts
  ends := hends
  monotone := by
    intro r t hrt ht
    by_cases he : t = σ.vars "round" + 1
    · subst t
      rw [hnew]
      by_cases hr : r = σ.vars "round" + 1
      · rw [hr, hnew]
      · have hrle : r ≤ σ.vars "round" := by omega
        rw [hboundary r hrle]
        exact (h.monotone r (σ.vars "round") hrle le_rfl).trans (h.used.symm ▸ hinc)
    · have htle : t ≤ σ.vars "round" := by omega
      rw [hboundary t htle, hboundary r (by omega)]
      exact h.monotone r t hrt htle
  capacity := by
    intro r hr
    by_cases he : r = σ.vars "round" + 1
    · rw [he, hnew]; exact hcap
    · have hrle : r ≤ σ.vars "round" := by omega
      rw [hboundary r hrle]; exact h.capacity r hrle
  used := by simpa only [hround] using hnew
  removedBound := hremBound
  representativeBound := hrepBound

end Lax235315Proofs.Construction.StoredHistory
