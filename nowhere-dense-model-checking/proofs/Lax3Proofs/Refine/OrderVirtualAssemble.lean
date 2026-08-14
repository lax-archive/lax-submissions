import Lax3Proofs.Refine.OrderVirtualInvoke
import Lax3Proofs.RamDriverCompose

/-!
# Buffer passes for assembling one virtual augmentation row

These are the three small executable combinators used around the child row
calls: emit a fresh exact buffer, add an exact buffer to a stamp, and restore
a carrier stamp to zero.
-/

namespace Lax3Proofs.Refine.OrderVirtualAssemble

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriverAugment
  (Emits Guarded Marks stampCond emitBranch_run)
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualInvoke

/-- Closure of an underlying child-persistent predicate under every write
owned by the augmentation assembler. -/
structure AugScratchClosed (P : Env → Prop) : Prop where
  setVar : ∀ {sigma : Env} {a : String} {x : ℕ}, a ≠ "n" →
    P sigma → P (sigma.setVar a x)
  setArr : ∀ {sigma : Env} {a : String} {p x : ℕ},
    a ∈ ["vrow", "sta", "std", "ste", "avsave"] →
    P sigma → P (sigma.setArr a p x)

namespace AugScratchClosed

theorem toInvokeClosed {P : Env → Prop} (h : AugScratchClosed P) :
    AugInvokeClosed P :=
  ⟨h.setVar, fun hp => h.setArr (by simp) hp⟩

/-- Commands confined to the assembler's five arrays and private scalars
preserve the underlying persistent state. -/
theorem run {B K : ℕ} {P : Env → Prop} {c : Com} {sigma tau : Env}
    (hclose : AugScratchClosed P) (hr : Run B c sigma tau K)
    (hvars : ∀ a ∈ c.wvars, a ≠ "n")
    (harrs : ∀ a ∈ c.warrs,
      a ∈ ["vrow", "sta", "std", "ste", "avsave"])
    (hreads : ¬ c.reads) (hwrites : c.NoWrite)
    (hP : P sigma) : P tau := by
  obtain ⟨k, hk, hrun⟩ := hr
  clear hk K
  induction hrun with
  | skip => exact hP
  | assign he => exact hclose.setVar (hvars _ (by simp [Com.wvars])) hP
  | @store sigma0 a i e idx value hi he hslot =>
      exact hclose.setArr (harrs a (by simp [Com.warrs])) hP
  | @seq c0 c1 sigma0 sigma1 sigma2 k0 k1 hc hd ihc ihd =>
      have hv0 : ∀ a ∈ c0.wvars, a ≠ "n" := fun a ha =>
        hvars a (by simp [Com.wvars, ha])
      have hv1 : ∀ a ∈ c1.wvars, a ≠ "n" := fun a ha =>
        hvars a (by simp [Com.wvars, ha])
      have ha0 : ∀ a ∈ c0.warrs,
          a ∈ ["vrow", "sta", "std", "ste", "avsave"] := fun a ha =>
        harrs a (by simp [Com.warrs, ha])
      have ha1 : ∀ a ∈ c1.warrs,
          a ∈ ["vrow", "sta", "std", "ste", "avsave"] := fun a ha =>
        harrs a (by simp [Com.warrs, ha])
      have hrs : ¬ c0.reads ∧ ¬ c1.reads := by simpa [Com.reads] using hreads
      have hws : c0.NoWrite ∧ c1.NoWrite := by simpa [Com.NoWrite] using hwrites
      exact ihd hv1 ha1 hrs.2 hws.2 (ihc hv0 ha0 hrs.1 hws.1 hP)
  | @ite_true b c0 c1 sigma0 sigma1 k0 hb hc ih =>
      apply ih
      · intro a ha; exact hvars a (by simp [Com.wvars, ha])
      · intro a ha; exact harrs a (by simp [Com.warrs, ha])
      · have h : ¬ c0.reads ∧ ¬ c1.reads := by simpa [Com.reads] using hreads
        exact h.1
      · have h : c0.NoWrite ∧ c1.NoWrite := by simpa [Com.NoWrite] using hwrites
        exact h.1
      · exact hP
  | @ite_false b c0 c1 sigma0 sigma1 k0 hb hc ih =>
      apply ih
      · intro a ha; exact hvars a (by simp [Com.wvars, ha])
      · intro a ha; exact harrs a (by simp [Com.warrs, ha])
      · have h : ¬ c0.reads ∧ ¬ c1.reads := by simpa [Com.reads] using hreads
        exact h.2
      · have h : c0.NoWrite ∧ c1.NoWrite := by simpa [Com.NoWrite] using hwrites
        exact h.2
      · exact hP
  | @while_true b c0 sigma0 sigma1 sigma2 k0 k1 hb hc hw ihc ihw =>
      have hv : ∀ a ∈ c0.wvars, a ≠ "n" := fun a ha =>
        hvars a (by simpa [Com.wvars] using ha)
      have ha : ∀ a ∈ c0.warrs,
          a ∈ ["vrow", "sta", "std", "ste", "avsave"] := fun a hx =>
        harrs a (by simpa [Com.warrs] using hx)
      have hrs : ¬ c0.reads := by simpa [Com.reads] using hreads
      have hws : c0.NoWrite := by simpa [Com.NoWrite] using hwrites
      exact ihw hvars harrs hreads hwrites (ihc hv ha hrs hws hP)
  | while_false hb => exact hP
  | read h => exact False.elim (hreads (by simp [Com.reads]))
  | write he => exact False.elim (by simpa [Com.NoWrite] using hwrites)

end AugScratchClosed

/-- Carrier-linear private state of one augmentation assembler. -/
structure AugWorkspace (n : ℕ) (P : Env → Prop) (sigma : Env) : Prop where
  persistent : P sigma
  tmp_length : (sigma.arrs "vtmp").length = n
  output_length : (sigma.arrs "vrow").length = n
  save_length : (sigma.arrs "avsave").length = 1
  adjacency_zero : sigma.arrs "sta" = arrOf n (fun _ => 0)
  opposite_zero : sigma.arrs "std" = arrOf n (fun _ => 0)
  emitted_zero : sigma.arrs "ste" = arrOf n (fun _ => 0)

/-- Deduplicate a flat exact row through the shared emitted stamp. -/
def virtualFreshGuard (act : Com) : Com :=
  .ite (.eq (.get "ste" (.var "u")) (.lit 0))
    (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip

theorem virtualFreshGuard_of_emits {B n Ka : ℕ} {a₁ a₂ : String}
    {act : Com} {Acc : Finset ℕ → Env → Prop} {Cap : Finset ℕ}
    (ha₁ : a₁ ≠ "ste") (ha₂ : a₂ ≠ "ste")
    (hB1 : 1 < B) (hnB : n < B)
    (hAccSt : ∀ S tau p x, Acc S tau → Acc S (tau.setArr "ste" p x))
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) :
    Guarded B n (Ka + 8) (virtualFreshGuard act) (fun z => {z}) Cap
      (fun S tau => Marks "ste" n 1 S (fun _ => 0) tau ∧ Acc S tau) := by
  classical
  rintro S tau z ⟨hm, hA⟩ hu hzn hfe
  have ee := stampCond hm hu hzn hB1 hnB
  by_cases hzS : z ∈ S
  · refine ⟨tau, _, Run.ite_false (by rw [ee]; simp [hzS]) Run.skip, ?_, ?_,
      fun _ _ => rfl⟩
    · simp only [size_condEq, size_get, size_var, size_lit]
      omega
    · rw [Finset.union_singleton, Finset.insert_eq_self.2 hzS]
      exact ⟨hm, hA⟩
  · obtain ⟨tau', K, hr, hK, hm', hA', hfv, -⟩ :=
      emitBranch_run (sd := "ste") (M := S) ha₁ ha₂ hB1 hnB hAccSt hAcc
        hm hA hu hzn hzS (hfe (Finset.mem_singleton_self z))
    refine ⟨tau', _, Run.ite_true (by rw [ee]; simp [hzS]) hr, ?_, ?_, hfv⟩
    · simp only [size_condEq, size_get, size_var, size_lit]
      omega
    · rw [Finset.union_singleton]
      exact ⟨hm', hA'⟩

/-- Stamping another exact buffer extends an already represented marked
set by its numeric row image. -/
theorem stampBuffer_union_run {B n tail b : ℕ} {src j jend u s : String}
    {S : Finset (Fin n)} {Base : Finset ℕ} {A : ℕ → ℕ} {sigma : Env}
    (hjje : j ≠ jend) (hju : j ≠ u) (hjeu : jend ≠ u)
    (hst : s ≠ src) (hB1 : 1 < B) (hnB : n < B) (hbB : b < B)
    (hrow : SetRowRep S tail A) (hend : sigma.vars jend = tail)
    (hsrc : sigma.arrs src = arrOf n A)
    (hmarks : Marks s n b Base (fun _ => 0) sigma) :
    ∃ tau K,
      Run B (bufferScan src j jend u (.store s (.var u) (.lit b))) sigma tau K ∧
      K ≤ tail * 14 + 6 ∧
      Marks s n b (Base ∪ Lax3Proofs.RamDriverAugment.valSet S)
        (fun _ => 0) tau := by
  obtain ⟨g, hg, hgk⟩ := hmarks
  obtain ⟨tau, K, hr, hK, hnew⟩ :=
    stampBuffer_run (B := B) (n := n) (tail := tail) (b := b)
      (src := src) (j := j) (jend := jend) (u := u) (s := s)
      (S := S) (A := A) (g := g) (sigma := sigma)
      hjje hju hjeu hst hB1 hnB hbB hrow hend hsrc hg
  exact ⟨tau, K, hr, hK, Marks.trans hgk hnew⟩

/-- Clear exactly the vertices named by an exact buffer.  Starting from a
one-stamp representation of `M`, the remaining one-stamps represent the set
difference.  This is the cleanup primitive used by the recursive assembler:
it avoids a carrier scan and therefore does not borrow the elimination
engine's loop counter. -/
theorem clearBuffer_run {B n tail : ℕ} {src j jend u s : String}
    {S : Finset (Fin n)} {M : Finset ℕ} {A : ℕ → ℕ} {sigma : Env}
    (hjje : j ≠ jend) (hju : j ≠ u) (hjeu : jend ≠ u)
    (hst : s ≠ src) (hB1 : 1 < B) (hnB : n < B)
    (hrow : SetRowRep S tail A) (hend : sigma.vars jend = tail)
    (hsrc : sigma.arrs src = arrOf n A)
    (hmarks : Marks s n 1 M (fun _ => 0) sigma) :
    ∃ tau K,
      Run B (bufferScan src j jend u (.store s (.var u) (.lit 0))) sigma tau K ∧
      K ≤ tail * 14 + 6 ∧
      Marks s n 1 (M \ Lax3Proofs.RamDriverAugment.valSet S)
        (fun _ => 0) tau := by
  classical
  obtain ⟨g, hg, hgk⟩ := hmarks
  obtain ⟨tau, K, hr, hK, ⟨g', hg', hg'k⟩⟩ :=
    stampBuffer_run (B := B) (n := n) (tail := tail) (b := 0)
      (src := src) (j := j) (jend := jend) (u := u) (s := s)
      (S := S) (A := A) (g := g) (sigma := sigma)
      hjje hju hjeu hst hB1 hnB (by omega) hrow hend hsrc hg
  refine ⟨tau, K, hr, hK, ⟨g', hg', fun k hk => ?_⟩⟩
  rw [hg'k k hk, hgk k hk]
  by_cases hS : k ∈ Lax3Proofs.RamDriverAugment.valSet S
  · simp [hS]
  · by_cases hM : k ∈ M <;> simp [hS, hM]

/-- An empty one-stamp representation over a zero background is the literal
zero carrier array. -/
theorem array_zero_of_marks_empty {n : ℕ} {s : String} {sigma : Env}
    (hmarks : Marks s n 1 (∅ : Finset ℕ) (fun _ => 0) sigma) :
    sigma.arrs s = arrOf n (fun _ => 0) := by
  obtain ⟨g, hg, hgk⟩ := hmarks
  rw [hg]
  apply Lax3Proofs.RamDriverOrder.arrOf_congr
  intro k hk
  simpa using hgk k hk

/-- Restore a whole carrier-sized stamp to zero.  The run itself supplies
the frame facts used by the enclosing provider. -/
theorem zeroCarrierArray_run {B n : ℕ} {a : String} {sigma : Env}
    (hB1 : 1 < B) (hnB : n < B) (hn : sigma.vars "n" = n)
    (hlen : (sigma.arrs a).length = n) :
    ∃ tau,
      Run B (Lax3Proofs.RamDriver.fillUpto a (.var "n") (.lit 0))
        sigma tau (11 * n + 6) ∧
      tau.arrs a = arrOf n (fun _ => 0) ∧ tau.vars "n" = n := by
  obtain ⟨g, hg⟩ := Lax3Proofs.RamDriver.exists_arrOf hlen
  obtain ⟨tau, hr, ⟨g', hg', hgzero⟩, hn'⟩ :=
    (Lax3Proofs.RamDriverCompose.fillZero_spec (B := B) (n := n) (N := n)
      a (.var "n") (by omega) hnB (fun sigma hs => by
        have h := evalB_var (B := B) (x := "n") (σ := sigma)
          (by rw [hs]; exact hnB)
        rwa [hs] at h)).run ⟨⟨g, hg⟩, hn⟩
  have hzero : tau.arrs a = arrOf n (fun _ => 0) := by
    rw [hg']
    apply Lax3Proofs.RamDriverOrder.arrOf_congr
    exact hgzero
  exact ⟨tau, hr, hzero, hn'⟩

#print axioms virtualFreshGuard_of_emits
#print axioms stampBuffer_union_run
#print axioms clearBuffer_run
#print axioms array_zero_of_marks_empty
#print axioms zeroCarrierArray_run

end Lax3Proofs.Refine.OrderVirtualAssemble
