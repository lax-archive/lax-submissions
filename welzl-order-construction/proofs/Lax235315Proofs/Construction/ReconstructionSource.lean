import Lax235315Proofs.Construction.LinkedRoundsSource
import Lax235315Proofs.Construction.LinkedInitializeSource
import Lax235315Proofs.Construction.IndexedRestoreBridge

/-! Compose the literal initialization, reverse-round replay and output passes.
The log certificate states list facts about the stored intervals; it contains
no source-execution assumption. -/
namespace Lax235315Proofs.Construction.ReconstructionSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.LinkedSource
open Lax235315Proofs.Construction.LinkedReconstruction
open Lax235315Proofs.Construction.LinkedInitializeSource
open Lax235315Proofs.Construction.LinkedOutputSource
open Lax235315Proofs.Construction.LinkedRoundsSource
open Lax235315Proofs.Construction.ConcreteReconstruction
open Lax235315Proofs.Construction.ReadKeys (scanList mem_scanList)

/-- Semantic content of the recorded intervals. The order at index `r` is
obtained by restoring exactly interval `r` into the next smaller order. -/
structure LoggedRestorations (R : ℕ) (boundary removed repAt : ℕ → ℕ)
    (orders : ℕ → List ℕ) where
  representative : ℕ → ℕ → ℕ
  map_eq : ∀ r < R, ∀ i < boundary (r + 1) - boundary r,
    representative r (removed (boundary r + i)) = repAt (boundary r + i)
  nodup : ∀ r < R, (logSlice removed (boundary r) (boundary (r + 1) - boundary r)).Nodup
  fresh : ∀ r < R, ∀ x ∈ logSlice removed (boundary r) (boundary (r + 1) - boundary r),
    x ∉ orders (r + 1)
  reps : ∀ r < R, ∀ x ∈ logSlice removed (boundary r) (boundary (r + 1) - boundary r),
    representative r x ∈ orders (r + 1)
  restore_eq : ∀ r < R, orders r = restoreAfter (representative r) (orders (r + 1))
    (logSlice removed (boundary r) (boundary (r + 1) - boundary r))

def LoggedRestorations.prefix {R : ℕ} {boundary removed repAt : ℕ → ℕ}
    {orders : ℕ → List ℕ} (h : LoggedRestorations (R + 1) boundary removed repAt orders) :
    LoggedRestorations R boundary removed repAt orders where
  representative := h.representative
  map_eq r hr := h.map_eq r (by omega)
  nodup r hr := h.nodup r (by omega)
  fresh r hr := h.fresh r (by omega)
  reps r hr := h.reps r (by omega)
  restore_eq r hr := h.restore_eq r (by omega)

lemma LoggedRestorations.represents {R head : ℕ} {boundary removed repAt next : ℕ → ℕ}
    {orders : ℕ → List ℕ} (h : LoggedRestorations R boundary removed repAt orders)
    (hbase : Represents head next (orders R)) :
    Represents head (replayRounds boundary removed repAt R next) (orders 0) := by
  induction R generalizing next with
  | zero => exact hbase
  | succ R ih =>
    apply ih h.prefix
    rw [h.restore_eq R (by omega)]
    exact LinkedSource.Represents.writeLogPrefix_restoreAfter hbase (h.nodup R (by omega))
      (h.fresh R (by omega)) (h.reps R (by omega)) (h.map_eq R (by omega))

/-- Append a continuation to the four commands of the initialization pass. -/
lemma run_append_four {B K K' : ℕ} {a b c d e : Com} {σ τ υ : Env}
    (h : Run B (.seq a (.seq b (.seq c d))) σ τ K)
    (ht : Run B e τ υ K') :
    Run B (.seq a (.seq b (.seq c (.seq d e)))) σ υ (K + K') := by
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨kt, hkt, ht⟩ := ht
  cases h with
  | seq ha h =>
    cases h with
    | seq hb h =>
      cases h with
      | seq hc hd => exact ⟨_, by omega, .seq ha (.seq hb (.seq hc (.seq hd ht)))⟩

/-- Execute the whole source reconstruction. The output is the order certified
by the actual log intervals, and the source cost is at most `100 (n+1)`. -/
lemma reconstructAndWrite_run {B n R : ℕ} {σ : Env}
    {boundary starts ends removed repAt active next : ℕ → ℕ} {orders : ℕ → List ℕ}
    (hn : σ.vars "n" = n) (hround : σ.vars "round" = R)
    (hRn : R ≤ n) (hnB : n < B)
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
    (hbase : orders R = scanList active 0 n)
    (hnonempty : 0 < n → scanList active 0 n ≠ [])
    (hlog : LoggedRestorations R boundary removed repAt orders)
    (hlen : (orders 0).length = n) (hvertices : ∀ v ∈ orders 0, v < n) :
    ∃ τ, Run B reconstructAndWrite σ τ (100 * (n + 1)) ∧
      τ.out = σ.out ++ orders 0 ∧ τ.inp = σ.inp := by
  obtain ⟨σ₁, next₁, rinit, hn₁, hv₁, harr₁, hin₁, hout₁, hnext₁, hb₁, hlist₁⟩ :=
    linkedInitialize_run hnB hn hactive hnext hactiveB hnextB
  have hr₁ : σ₁.vars "round" = R :=
    (rinit.frame_var "round" (by decide)).trans hround
  obtain ⟨σ₂, rrounds, hr₂, hnext₂, hb₂⟩ := linkedRounds_run hr₁ hRn hnB
    ((harr₁ _ (by decide)).trans hstarts) ((harr₁ _ (by decide)).trans hends)
    ((harr₁ _ (by decide)).trans hremoved) ((harr₁ _ (by decide)).trans hreps)
    hnext₁ hstartVals hendVals hmono hcap hremN hrepN hb₁
  have hhead₂ : σ₂.vars "head" = σ₁.vars "head" := rrounds.frame_var "head" (by decide)
  have hn₂ : σ₂.vars "n" = n := (rrounds.frame_var "n" (by decide)).trans hn₁
  have hheadB : σ₁.vars "head" < B := by
    rcases hlist₁ with ⟨_, hh, _⟩ | ⟨_, hr, _, _⟩
    · rw [hh]; exact hnB
    · have hm := List.mem_of_mem_head? hr.2.1
      exact (by simpa using (mem_scanList.mp hm).2.1 : σ₁.vars "head" < n).trans hnB
  have hfinal : orders 0 = [] ∨
      Represents (σ₁.vars "head") (replayRounds boundary removed repAt R next₁) (orders 0) := by
    rcases hlist₁ with ⟨hempty, _, _⟩ | ⟨_, hr, _, _⟩
    · have hz : n = 0 := by by_contra h; exact hnonempty (by omega) hempty
      have hRz : R = 0 := by omega
      left
      simpa [hRz] using hbase.trans hempty
    · right
      exact hlog.represents (by rw [hbase]; exact hr)
  obtain ⟨τ, rout, _, _, _, _, hin, hout⟩ := linkedOutputAndWrite_run
    hfinal hlen hvertices hnB hheadB hb₂ hn₂ hhead₂ hnext₂ rfl rfl
  refine ⟨τ, ?_, ?_, ?_⟩
  · have hrun := run_append_four rinit (rrounds.seq rout)
    have hcost := hcap R le_rfl
    have hrun' := hrun.mono (by omega :
      40 * (n + 1) + ((24 * R + 21 * boundary R + 4) + (13 * n + 9)) ≤ 100 * (n + 1))
    exact hrun'
  · rw [hout, rrounds.out_eq (by decide), hout₁]
  · exact hin.trans ((rrounds.frame_inp (by decide)).trans hin₁)

end Lax235315Proofs.Construction.ReconstructionSource
