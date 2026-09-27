import Lax235315Proofs.Construction.ReconstructionSource
import Lax235315Proofs.Construction.RemovedRestoreBridge
import Lax235315Proofs.Construction.Correctness

/-! A history retains the mathematical meaning of each stored interval.
Reconstruction can then be proved for any enumerated terminal active set. -/
namespace Lax235315Proofs.Construction.RecordedHistory
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.ConcreteReconstruction
open Lax235315Proofs.Construction.ReconstructionSource
open Lax235315Proofs.Construction.LinkedSource
open Lax235315Proofs.Construction.RemovedRestoreBridge

/-- Extend a vertex representative to natural-number array indices. -/
def numericRepresentative {n : ℕ} (rep : Fin n → Fin n) (v : ℕ) : ℕ :=
  if h : v < n then (rep ⟨v, h⟩).val else 0

@[simp] lemma numericRepresentative_val {n : ℕ} (rep : Fin n → Fin n) (v : Fin n) :
    numericRepresentative rep v.val = (rep v).val := by
  simp [numericRepresentative, v.isLt]

/-- One checked graph reduction, tied to the exact stored deletion interval. -/
structure RecordedStep {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (A B A' B' : Set (Fin n)) (boundary removed repAt : ℕ → ℕ) where
  deleted : List (Fin n)
  representative : Fin n → Fin n
  vertices : deleted.map Fin.val =
    logSlice removed (boundary r) (boundary (r + 1) - boundary r)
  stored_representatives : ∀ i < boundary (r + 1) - boundary r,
    numericRepresentative representative (removed (boundary r + i)) = repAt (boundary r + i)
  removed_enumerates : Enumerates (A \ A') deleted
  representative_mem : ∀ v ∈ deleted, representative v ∈ A'
  reduction : ∀ small, Enumerates A' small → Nonempty (Reduction G k A B A' B' small
    (restoreAfter representative small deleted))

/-- Graph certificates for all chronologically numbered log intervals. -/
structure History {n : ℕ} (G : SimpleGraph (Fin n)) (k R : ℕ)
    (A B : ℕ → Set (Fin n)) (boundary removed repAt : ℕ → ℕ) where
  step : ∀ r < R, RecordedStep G k r (A r) (B r) (A (r + 1)) (B (r + 1))
    boundary removed repAt

def History.prefix {n k R : ℕ} {G : SimpleGraph (Fin n)}
    {A B : ℕ → Set (Fin n)} {boundary removed repAt : ℕ → ℕ}
    (h : History G k (R + 1) A B boundary removed repAt) :
    History G k R A B boundary removed repAt where
  step r hr := h.step r (by omega)

/-- Append the final reverse-restoration equation while retaining earlier ones. -/
def extendLogged {R : ℕ} {boundary removed repAt : ℕ → ℕ} {orders : ℕ → List ℕ}
    (h : LoggedRestorations R boundary removed repAt orders)
    (small : List ℕ) (rep : ℕ → ℕ)
    (hmap : ∀ i < boundary (R + 1) - boundary R,
      rep (removed (boundary R + i)) = repAt (boundary R + i))
    (hdup : (logSlice removed (boundary R) (boundary (R + 1) - boundary R)).Nodup)
    (hfresh : ∀ x ∈ logSlice removed (boundary R) (boundary (R + 1) - boundary R), x ∉ small)
    (hreps : ∀ x ∈ logSlice removed (boundary R) (boundary (R + 1) - boundary R), rep x ∈ small)
    (hrestore : orders R = restoreAfter rep small
      (logSlice removed (boundary R) (boundary (R + 1) - boundary R))) :
    LoggedRestorations (R + 1) boundary removed repAt (Function.update orders (R + 1) small) where
  representative := Function.update h.representative R rep
  map_eq r hr := by
    by_cases he : r = R
    · subst r; simpa using hmap
    · simpa [Function.update_of_ne he] using h.map_eq r (by omega)
  nodup r hr := by
    by_cases he : r = R
    · subst r; exact hdup
    · exact h.nodup r (by omega)
  fresh r hr := by
    by_cases he : r = R
    · subst r; simpa using hfresh
    · simpa [Function.update_of_ne (show r + 1 ≠ R + 1 by omega)] using h.fresh r (by omega)
  reps r hr := by
    by_cases he : r = R
    · subst r; simpa using hreps
    · simpa [Function.update_of_ne he,
        Function.update_of_ne (show r + 1 ≠ R + 1 by omega)] using h.reps r (by omega)
  restore_eq r hr := by
    by_cases he : r = R
    · subst r; simpa using hrestore
    · simpa [Function.update_of_ne he, Function.update_of_ne (show r ≠ R + 1 by omega),
        Function.update_of_ne (show r + 1 ≠ R + 1 by omega)] using h.restore_eq r (by omega)

/-- A recorded history lifts any already certified terminal order to the
initial vertex sides and supplies the exact numeric replay certificate. -/
lemma History.lift {n k q R t : ℕ} {G : SimpleGraph (Fin n)}
    {A B : ℕ → Set (Fin n)} {boundary removed repAt : ℕ → ℕ}
    (h : History G k R A B boundary removed repAt) {small : List (Fin n)}
    (hsmall : CertifiedRun G k q t (A R) (B R) small) :
    ∃ orders : ℕ → List (Fin n), orders R = small ∧
      Nonempty (LoggedRestorations R boundary removed repAt (fun r => (orders r).map Fin.val)) ∧
      CertifiedRun G k q (t + R) (A 0) (B 0) (orders 0) := by
  induction R generalizing t small with
  | zero =>
    refine ⟨fun _ => small, rfl, ⟨?_⟩, ?_⟩
    · exact ⟨fun _ x => x, by omega, by omega, by omega, by omega, by omega⟩
    · simpa using hsmall
  | succ R ih =>
    let s := h.step R (by omega)
    have henum := hsmall.enumerates G
    obtain ⟨hred⟩ := s.reduction small henum
    let big := restoreAfter s.representative small s.deleted
    have hbig : CertifiedRun G k q (t + 1) (A R) (B R) big := .step hred hsmall
    obtain ⟨orders, hlast, ⟨hlog⟩, hcert⟩ := ih h.prefix hbig
    let orders' := Function.update orders (R + 1) small
    have hnumeric : (big.map Fin.val) =
        restoreAfter (numericRepresentative s.representative) (small.map Fin.val)
          (logSlice removed (boundary R) (boundary (R + 1) - boundary R)) := by
      rw [show big = restoreAfter s.representative small s.deleted from rfl,
        restoreAfter_map Fin.val_injective s.representative
          (numericRepresentative s.representative) small s.deleted (by simp), s.vertices]
    have hdup : (logSlice removed (boundary R) (boundary (R + 1) - boundary R)).Nodup := by
      rw [← s.vertices]
      exact s.removed_enumerates.1.map Fin.val_injective
    have hfresh : ∀ x ∈ logSlice removed (boundary R) (boundary (R + 1) - boundary R),
        x ∉ small.map Fin.val := by
      intro x hx hxsmall
      rw [← s.vertices] at hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      obtain ⟨w, hw, he⟩ := List.mem_map.mp hxsmall
      have hwv : w = v := Fin.val_injective he
      subst w
      exact ((s.removed_enumerates.2 v).mp hv).2 ((henum.2 v).mp hw)
    have hreps : ∀ x ∈ logSlice removed (boundary R) (boundary (R + 1) - boundary R),
        numericRepresentative s.representative x ∈ small.map Fin.val := by
      intro x hx
      rw [← s.vertices] at hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      rw [numericRepresentative_val]
      exact List.mem_map.mpr ⟨s.representative v,
        (henum.2 _).mpr (s.representative_mem v hv), rfl⟩
    have hlog' := extendLogged hlog (small.map Fin.val) (numericRepresentative s.representative)
      s.stored_representatives hdup hfresh hreps (by rw [hlast]; exact hnumeric)
    refine ⟨orders', by simp [orders'], ⟨?_⟩, ?_⟩
    · convert hlog' using 1
      funext r
      by_cases hr : r = R + 1 <;> simp [orders', hr]
    · have hzero : orders' 0 = orders 0 := by simp [orders']
      rw [hzero]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcert

/-- A small final active set closes the base case of the entire recorded history. -/
lemma History.reconstruct {n k q R : ℕ} {G : SimpleGraph (Fin n)}
    {A B : ℕ → Set (Fin n)} {boundary removed repAt : ℕ → ℕ}
    (h : History G k R A B boundary removed repAt) {small : List (Fin n)}
    (hsmall : Enumerates (A R) small) (hcard : (A R).ncard ≤ q) :
    ∃ orders : ℕ → List (Fin n), orders R = small ∧
      Nonempty (LoggedRestorations R boundary removed repAt (fun r => (orders r).map Fin.val)) ∧
      CertifiedRun G k q R (A 0) (B 0) (orders 0) := by
  simpa using h.lift (CertifiedRun.base (B := B R) hsmall hcard)

/-- Transport a checked interval across a later log append. Only its own
boundaries and the occupied prefix matter. -/
def RecordedStep.transport {n k r base : ℕ} {G : SimpleGraph (Fin n)}
    {A B A' B' : Set (Fin n)} {boundary removed repAt boundary' removed' repAt' : ℕ → ℕ}
    (h : RecordedStep G k r A B A' B' boundary removed repAt)
    (hstart : boundary' r = boundary r) (hend : boundary' (r + 1) = boundary (r + 1))
    (hmono : boundary r ≤ boundary (r + 1)) (hbefore : boundary (r + 1) ≤ base)
    (hremoved : ∀ i < base, removed' i = removed i)
    (hrep : ∀ i < base, repAt' i = repAt i) :
    RecordedStep G k r A B A' B' boundary' removed' repAt' where
  deleted := h.deleted
  representative := h.representative
  vertices := by
    rw [hstart, hend, logSlice_eq_of_preserved_prefix hremoved (by omega)]
    exact h.vertices
  stored_representatives := by
    intro i hi
    rw [hstart, hend] at hi
    have hindex : boundary r + i < base := by omega
    rw [hstart, hremoved _ hindex, hrep _ hindex]
    exact h.stored_representatives i hi
  removed_enumerates := h.removed_enumerates
  representative_mem := h.representative_mem
  reduction := h.reduction

/-- Append a checked reduction while preserving every older recorded step. -/
def History.append {n k R : ℕ} {G : SimpleGraph (Fin n)}
    {A B : ℕ → Set (Fin n)} {A' B' : Set (Fin n)}
    {boundary removed repAt boundary' removed' repAt' : ℕ → ℕ}
    (h : History G k R A B boundary removed repAt)
    (hboundary : ∀ i ≤ R, boundary' i = boundary i)
    (hmono : ∀ r < R, boundary r ≤ boundary (r + 1))
    (hbefore : ∀ r < R, boundary (r + 1) ≤ boundary R)
    (hremoved : ∀ i < boundary R, removed' i = removed i)
    (hrep : ∀ i < boundary R, repAt' i = repAt i)
    (s : RecordedStep G k R (A R) (B R) A' B' boundary' removed' repAt') :
    History G k (R + 1) (Function.update A (R + 1) A')
      (Function.update B (R + 1) B') boundary' removed' repAt' where
  step r hr := by
    by_cases he : r = R
    · subst r
      simpa using s
    · have hrR : r < R := by omega
      have hs := (h.step r hrR).transport (hboundary r (by omega))
        (hboundary (r + 1) (by omega)) (hmono r hrR) (hbefore r hrR) hremoved hrep
      simpa [Function.update_of_ne (show r ≠ R + 1 by omega),
        Function.update_of_ne (show r + 1 ≠ R + 1 by omega)] using hs

open Lax235315Proofs.Construction.ReadKeys

/-- The terminal active-vertex scan, lifted without changing its order. -/
def activeFinList {n : ℕ} (active : ℕ → ℕ) : List (Fin n) :=
  (scanList active 0 n).attach.map fun x =>
    ⟨x.1, by have hx := mem_scanList.mp x.2; omega⟩

lemma activeFinList_map_val {n : ℕ} (active : ℕ → ℕ) :
    (activeFinList (n := n) active).map Fin.val = scanList active 0 n := by
  simp [activeFinList]

lemma mem_activeFinList {n : ℕ} {active : ℕ → ℕ} {v : Fin n} :
    v ∈ activeFinList active ↔ active v.val = 1 := by
  constructor
  · intro hv
    obtain ⟨x, hx, hval⟩ := List.mem_map.mp hv
    have hx' : x.1 = v.val := congrArg Fin.val hval
    have := (mem_scanList.mp x.2).2.2
    simpa [hx'] using this
  · intro hv
    have hm : v.val ∈ scanList active 0 n := mem_scanList.mpr ⟨by omega, by omega, hv⟩
    exact List.mem_map.mpr ⟨⟨v.val, hm⟩, List.mem_attach _ _, Fin.ext rfl⟩

lemma activeFinList_enumerates {n : ℕ} (active : ℕ → ℕ) :
    Enumerates {v : Fin n | active v.val = 1} (activeFinList active) := by
  constructor
  · apply List.Nodup.map (f := fun x : {x // x ∈ scanList active 0 n} =>
      (⟨x.1, by have hx := mem_scanList.mp x.2; omega⟩ : Fin n))
    · intro x y hxy
      exact Subtype.ext (congrArg Fin.val hxy)
    · exact List.nodup_attach.mpr (scanList_nodup active 0 n)
  · intro v
    exact mem_activeFinList

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.Correctness
open Lax195003.WelzlOrdersInGraphs

/-- Run the literal reconstruction from a recorded graph history. The
resulting source output has the crossing bound certified by that history. -/
lemma History.reconstructAndWrite_correct {B n k q R bound : ℕ} {G : SimpleGraph (Fin n)}
    {σ : Env} {A C : ℕ → Set (Fin n)}
    {boundary starts ends removed repAt active next : ℕ → ℕ}
    (h : History G k R A C boundary removed repAt)
    (hA : A 0 = Set.univ) (hC : C 0 = Set.univ)
    (hterminal : A R = {v : Fin n | active v.val = 1})
    (hsmall : (A R).ncard ≤ q) (hkq : 2 * k ≤ q)
    (hcross : (R + 1) * q ≤ bound)
    (hn : σ.vars "n" = n) (hround : σ.vars "round" = R)
    (hRn : R ≤ n) (hnB : n < B) (hout : σ.out = [])
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hstarts : σ.arrs "roundStart" = arrOf n starts)
    (hends : σ.arrs "roundEnd" = arrOf n ends)
    (hremoved : σ.arrs "removed" = arrOf n removed)
    (hreps : σ.arrs "removedRep" = arrOf n repAt)
    (hstartVals : ∀ r < R, starts r = boundary r)
    (hendVals : ∀ r < R, ends r = boundary (r + 1))
    (hmono : ∀ r < R, boundary r ≤ boundary (r + 1))
    (hcap : ∀ r ≤ R, boundary r ≤ n)
    (hremN : ∀ i < n, removed i < n) (hrepN : ∀ i < n, repAt i < n)
    (hactiveB : ∀ i < n, active i < B) (hnextB : ∀ i < n, next i < B)
    (hnonempty : 0 < n → scanList active 0 n ≠ []) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      EncodesGraphWelzlOrder G 1 bound τ.out ∧ τ.inp = σ.inp := by
  have henum : Enumerates (A R) (activeFinList active) := by
    rw [hterminal]
    exact activeFinList_enumerates active
  obtain ⟨orders, hlast, ⟨hlog⟩, hcert⟩ := h.reconstruct henum hsmall
  have hcert' : CertifiedRun G k q R Set.univ Set.univ (orders 0) := by
    simpa [hA, hC] using hcert
  have hlen : ((orders 0).map Fin.val).length = n := by
    rw [List.length_map, (hcert'.enumerates G).length_eq_ncard]
    simp
  have hbase : (orders R).map Fin.val = scanList active 0 n := by
    rw [hlast, activeFinList_map_val]
  obtain ⟨τ, hrun, houtput, hinput⟩ := reconstructAndWrite_run hn hround hRn hnB
    hactive hnext hstarts hends hremoved hreps hstartVals hendVals hmono hcap
    hremN hrepN hactiveB hnextB hbase hnonempty hlog hlen
    (by intro v hv; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv; exact v.isLt)
  refine ⟨τ, hrun, ?_, hinput⟩
  rw [houtput, hout, List.nil_append]
  exact certifiedRun_encodesGraphWelzlOrder G (orders 0) hcert' hkq hcross

end Lax235315Proofs.Construction.RecordedHistory


