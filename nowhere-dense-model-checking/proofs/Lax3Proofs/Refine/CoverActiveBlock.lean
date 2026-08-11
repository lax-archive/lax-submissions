import Lax3Proofs.RamCoverActive
import Lax3Proofs.Refine.BfsBlockMask

/-!
# Queue-aligned active-cover semantics

`BfsBlockMask.bfsBlockM_spec` deliberately restores the touched distance
cells before it returns.  Its useful output is therefore not a
carrier-indexed distance array, but the duplicate-free queue `q[0..tail)`
and the aligned distances `qd[0..tail)`.

This file is the semantic seam from that output to `RawCoverInvA`.  It
constructs a mathematical total distance only for the purpose of invoking
the already-landed invariant step; the executable emitter itself needs to
walk only the returned queue.  In particular, no hypothesis below asks for
or pays for a carrier scan.
-/

namespace Lax3Proofs.Refine.CoverActiveBlock

open Lax3.ColoredGraphs
open Lax3Proofs.RamBfs (WD masked)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlock
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {B n d d₀ s w tail k q c r : ℕ} {G : SimpleGraph (Fin n)}
variable {M Q QD asg : ℕ → ℕ}

/-! ## A total mathematical reading of the queue trail -/

/-- Read the aligned distance at the (unique) queue entry for `w`; use the
search sentinel when `w` is absent.  This function is mathematical only:
the executable cover emitter reads `QD i` while it walks the touched
prefix, and never evaluates this definition by searching for `w`. -/
noncomputable def queueDist (d tail : ℕ) (Q QD : ℕ → ℕ) (w : ℕ) : ℕ :=
  if h : ∃ i, i < tail ∧ Q i = w then QD (Nat.find h) else d + 1

/-- At every threshold below the search cap, the total reading above says
exactly that a masked walk exists.  The source-alive hypothesis is the one
small difference from the general block search: an active cover centre is
alive, so the source itself is present in the queue as well. -/
theorem queueDist_le_iff_wd (hw : w < n) (hsM : M s ≠ 0) (hk : d₀ ≤ d)
    (hseg : ∀ v, v < n →
      ((∃ i, i < tail ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v)))
    (hQD : ∀ i, i < tail → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))) :
    queueDist d tail Q QD w ≤ d₀ ↔ WD G M d₀ s w := by
  classical
  constructor
  · intro hle
    by_cases hm : ∃ i, i < tail ∧ Q i = w
    · have hfind := Nat.find_spec hm
      have hwd := (hQD (Nat.find hm) hfind.1 d₀ hk).mp (by
        simpa only [queueDist, dif_pos hm] using hle)
      simpa only [hfind.2] using hwd
    · simp only [queueDist, dif_neg hm] at hle
      omega
  · intro hwd
    have hMw : M w ≠ 0 := by
      by_cases hws : w = s
      · simpa only [hws] using hsM
      · exact alive_of_wd hwd (Ne.symm hws)
    have hm : ∃ i, i < tail ∧ Q i = w :=
      (hseg w hw).mpr ⟨hMw, WD.mono hk hwd⟩
    have hfind := Nat.find_spec hm
    have hwd' : WD G M d₀ s (Q (Nat.find hm)) := by
      simpa only [hfind.2] using hwd
    have hle := (hQD (Nat.find hm) hfind.1 d₀ hk).mpr hwd'
    simpa only [queueDist, dif_pos hm] using hle

/-- The condition the executable emitter tests while walking `q`/`qd` is
the same condition as the total mathematical distance test. -/
theorem queueCatch_iff (hw : w < n) (hsM : M s ≠ 0) (hk : d₀ ≤ d)
    (hseg : ∀ v, v < n →
      ((∃ i, i < tail ∧ Q i = v) ↔ (M v ≠ 0 ∧ WD G M d s v)))
    (hQD : ∀ i, i < tail → ∀ k, k ≤ d → (QD i ≤ k ↔ WD G M k s (Q i))) :
    (∃ i, i < tail ∧ Q i = w ∧ QD i ≤ d₀) ↔ queueDist d tail Q QD w ≤ d₀ := by
  constructor
  · rintro ⟨i, hi, hQi, hdi⟩
    apply (queueDist_le_iff_wd hw hsM hk hseg hQD).mpr
    have := (hQD i hi d₀ hk).mp hdi
    simpa only [hQi] using this
  · intro hdist
    have hwd := (queueDist_le_iff_wd hw hsM hk hseg hQD).mp hdist
    have hMw : M w ≠ 0 := by
      by_cases hws : w = s
      · simpa only [hws] using hsM
      · exact alive_of_wd hwd (Ne.symm hws)
    obtain ⟨i, hi, hQi⟩ := (hseg w hw).mpr ⟨hMw, WD.mono hk hwd⟩
    refine ⟨i, hi, hQi, (hQD i hi d₀ hk).mpr ?_⟩
    simpa only [hQi] using hwd

/-! ## The assignment fold performed along the queue -/

/-- A vertex occurs in the already-walked part of the trail at a catching
distance. -/
def caughtBefore (k r : ℕ) (Q QD : ℕ → ℕ) (w : ℕ) : Prop :=
  ∃ i, i < k ∧ Q i = w ∧ QD i ≤ r

theorem caughtBefore_succ_iff :
    caughtBefore (k + 1) d₀ Q QD w ↔
      caughtBefore k d₀ Q QD w ∨ (Q k = w ∧ QD k ≤ d₀) := by
  constructor
  · rintro ⟨i, hi, hQi, hdi⟩
    rcases Nat.lt_or_ge i k with hik | hik
    · exact Or.inl ⟨i, hik, hQi, hdi⟩
    · have : i = k := by omega
      subst i
      exact Or.inr ⟨hQi, hdi⟩
  · rintro (⟨i, hi, hQi, hdi⟩ | ⟨hQk, hdk⟩)
    · exact ⟨i, by omega, hQi, hdi⟩
    · exact ⟨k, by omega, hQk, hdk⟩

/-- The assignment array after the first `k` queue entries: old claims are
stable, and an unclaimed live vertex is assigned to this centre exactly
when the walked prefix catches it. -/
noncomputable def queueCell (asg : ℕ → ℕ) (q c r k : ℕ) (Q QD : ℕ → ℕ) (w : ℕ) : ℕ := by
  classical
  exact if asg w < q then asg w else if caughtBefore k r Q QD w then c else asg w

/-- The point update executed at queue position `k`. -/
noncomputable def queueUpdate (as : ℕ → ℕ) (q c r k : ℕ) (Q QD : ℕ → ℕ) : ℕ → ℕ :=
  if QD k ≤ r then
    if as (Q k) < q then as else Lax13Proofs.Reasoning.Lib.upd as (Q k) c
  else as

/-- One executable queue update extends the closed-form assignment rule by
one entry.  This lemma does not need queue injectivity: a repeated caught
entry would merely observe the already-written claim and leave it alone. -/
theorem queueUpdate_queueCell (hcq : c < q) :
    queueUpdate (queueCell asg q c d₀ k Q QD) q c d₀ k Q QD =
      queueCell asg q c d₀ (k + 1) Q QD := by
  classical
  funext w
  by_cases hw : w = Q k
  · subst w
    by_cases hold : asg (Q k) < q
    · have hcur : queueCell asg q c d₀ k Q QD (Q k) = asg (Q k) := by
        simp [queueCell, hold]
      have hnext : queueCell asg q c d₀ (k + 1) Q QD (Q k) = asg (Q k) := by
        simp [queueCell, hold]
      by_cases hd : QD k ≤ d₀
      · simp [queueUpdate, hd, hcur, hold, hnext]
      · simp only [queueUpdate, hd, if_false, hnext]
        exact hcur
    · by_cases hprev : caughtBefore k d₀ Q QD (Q k)
      · have hnext : caughtBefore (k + 1) d₀ Q QD (Q k) :=
          caughtBefore_succ_iff.mpr (Or.inl hprev)
        have hcurv : queueCell asg q c d₀ k Q QD (Q k) = c := by
          simp [queueCell, hold, hprev]
        have hnextv : queueCell asg q c d₀ (k + 1) Q QD (Q k) = c := by
          simp [queueCell, hold, hnext]
        by_cases hd : QD k ≤ d₀
        · simp [queueUpdate, hd, hcurv, hcq, hnextv]
        · simp only [queueUpdate, hd, if_false, hnextv]
          exact hcurv
      · by_cases hd : QD k ≤ d₀
        · have hnext : caughtBefore (k + 1) d₀ Q QD (Q k) :=
            caughtBefore_succ_iff.mpr (Or.inr ⟨rfl, hd⟩)
          have hcurv : queueCell asg q c d₀ k Q QD (Q k) = asg (Q k) := by
            simp [queueCell, hold, hprev]
          have hnextv : queueCell asg q c d₀ (k + 1) Q QD (Q k) = c := by
            simp [queueCell, hold, hnext]
          simp [queueUpdate, hd, hcurv, hold, hnextv]
        · have hnext : ¬ caughtBefore (k + 1) d₀ Q QD (Q k) := by
            intro h
            rcases caughtBefore_succ_iff.mp h with hp | ⟨-, hdk⟩
            · exact hprev hp
            · exact hd hdk
          have hcurv : queueCell asg q c d₀ k Q QD (Q k) = asg (Q k) := by
            simp [queueCell, hold, hprev]
          have hnextv : queueCell asg q c d₀ (k + 1) Q QD (Q k) = asg (Q k) := by
            simp [queueCell, hold, hnext]
          simp [queueUpdate, hd, hcurv, hnextv]
  · have hnext : queueCell asg q c d₀ (k + 1) Q QD w =
        queueCell asg q c d₀ k Q QD w := by
      by_cases hold : asg w < q
      · simp [queueCell, hold]
      · by_cases hprev : caughtBefore k d₀ Q QD w
        · have hn : caughtBefore (k + 1) d₀ Q QD w :=
            caughtBefore_succ_iff.mpr (Or.inl hprev)
          simp [queueCell, hold, hprev, hn]
        · have hn : ¬ caughtBefore (k + 1) d₀ Q QD w := by
            intro h
            rcases caughtBefore_succ_iff.mp h with hp | ⟨hQ, -⟩
            · exact hprev hp
            · exact hw hQ.symm
          simp [queueCell, hold, hprev, hn]
    rw [hnext]
    unfold queueUpdate
    split
    · split
      · rfl
      · exact Lax13Proofs.Reasoning.Lib.upd_of_ne _ hw
    · rfl

/-! ## The touched-only IMP emitter -/

/-- Emit one aligned queue entry, update its first-catcher cell when its
aligned distance is at most `r`, and advance both pointers. -/
def emitQueueSlot (r : ℕ) : Com :=
  .seq (.assign "cvu" (.get "q" (.var "cvk")))
    (.seq (.assign "cvd" (.get "qd" (.var "cvk")))
      (.seq (.store "xmem" (.var "xp") (.var "cvu"))
        (.seq
          (.ite (.lt (.var "cvd") (.lit (r + 1)))
            (.ite (.lt (.get "asg" (.var "cvu")) (.var "qn"))
              .skip (.store "asg" (.var "cvu") (.var "c")))
            .skip)
          (.seq (.assign "xp" (.add (.var "xp") (.lit 1)))
            (.assign "cvk" (.add (.var "cvk") (.lit 1)))))))

/-- Walk exactly the queue prefix returned by `bfsBlockCom`. -/
def emitQueueCom (r : ℕ) : Com :=
  .seq (.assign "cvk" (.lit 0))
    (.while (.lt (.var "cvk") (.var "tail")) (emitQueueSlot r))

/-- The emitter's loop invariant.  Its arena clause is positional (entry
`i` is copied to `xp₀+i`), and its assignment array is the closed queue
fold above.  Nothing ranges over the carrier except the physical length of
the assignment array. -/
def QueueEmitInv (n na tail q c r xp₀ : ℕ) (Q QD Xm₀ asg₀ : ℕ → ℕ)
    (σ : Env) : Prop :=
  ∃ Xm : ℕ → ℕ,
    σ.vars "tail" = tail ∧ σ.vars "qn" = q ∧ σ.vars "c" = c ∧
    σ.arrs "q" = arrOf n Q ∧ σ.arrs "qd" = arrOf n QD ∧
    σ.arrs "xmem" = arrOf na Xm ∧
    σ.arrs "asg" = arrOf n (queueCell asg₀ q c r (σ.vars "cvk") Q QD) ∧
    σ.vars "cvk" ≤ tail ∧ σ.vars "xp" = xp₀ + σ.vars "cvk" ∧
    (∀ p < xp₀, Xm p = Xm₀ p) ∧
    (∀ i < σ.vars "cvk", Xm (xp₀ + i) = Q i)

/-- Every intermediate assignment value is either its entering word or the
current centre index. -/
theorem queueCell_lt (hcB : c < B) (hasgB : ∀ w < n, asg w < B)
    (hw : w < n) : queueCell asg q c r k Q QD w < B := by
  classical
  simp only [queueCell]
  split
  · exact hasgB w hw
  · split
    · exact hcB
    · exact hasgB w hw

/-- One touched queue entry, walked.  The thirty-tick bound is independent
of the carrier and includes both conditional levels. -/
theorem emitQueueSlot_spec {B n na tail q c r xp₀ : ℕ} {Q QD Xm₀ asg₀ : ℕ → ℕ}
    (hnB : n < B) (htailB : tail < B) (htailn : tail ≤ n)
    (hqB : q < B) (hcq : c < q) (hrB : r + 1 < B)
    (hxpna : xp₀ + tail ≤ na) (hxpB : xp₀ + tail < B)
    (hQlt : ∀ i < tail, Q i < n) (hQDB : ∀ i < tail, QD i < B)
    (hasgB : ∀ w < n, asg₀ w < B) :
    Spec B
      (fun σ => QueueEmitInv n na tail q c r xp₀ Q QD Xm₀ asg₀ σ ∧
        σ.vars "cvk" < tail)
      (emitQueueSlot r)
      (fun σ σ' => QueueEmitInv n na tail q c r xp₀ Q QD Xm₀ asg₀ σ' ∧
        σ'.vars "cvk" = σ.vars "cvk" + 1)
      30 := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨Xm, htail, hqn, hcvar, hq, hqd, hxmem, hasg, hkle, hxp, hkeep, hwrite⟩,
    hk⟩ := hσ
  let kk := σ.vars "cvk"
  have hkk : σ.vars "cvk" = kk := rfl
  have hkN : kk < n := lt_of_lt_of_le hk htailn
  have hkB : kk < B := lt_trans hk htailB
  have hQn : Q kk < n := hQlt kk hk
  have hQB : Q kk < B := lt_trans hQn hnB
  have hQDBk : QD kk < B := hQDB kk hk
  have hxpval : σ.vars "xp" = xp₀ + kk := hxp
  have hxpi : σ.vars "xp" < na := by rw [hxpval]; omega
  have hxpword : σ.vars "xp" < B := by rw [hxpval]; omega
  have hcurB : queueCell asg₀ q c r kk Q QD (Q kk) < B :=
    queueCell_lt (lt_trans hcq hqB) hasgB hQn
  -- `cvu := q[cvk]`.
  have e₁ : (Expr.get "q" (.var "cvk")).evalB B σ = some (Q kk) :=
    evalB_get (evalB_var hkB) (by rw [hq, getElem?_arrOf Q hkN]) hQB
  have r₁ := Run.assign (x := "cvu") e₁
  let σ₁ := σ.setVar "cvu" (Q kk)
  have hcvk₁ : σ₁.vars "cvk" = kk := by simp [σ₁, kk]
  -- `cvd := qd[cvk]`.
  have e₂ : (Expr.get "qd" (.var "cvk")).evalB B σ₁ = some (QD kk) := by
    refine evalB_get (evalB_var ?_) ?_ hQDBk
    · rw [hcvk₁]
      exact hkB
    · simp only [σ₁, arrs_setVar, hqd]
      rw [hcvk₁, getElem?_arrOf QD hkN]
  have r₂ := Run.assign (x := "cvd") e₂
  let σ₂ := σ₁.setVar "cvd" (QD kk)
  have hcvk₂ : σ₂.vars "cvk" = kk := by simp [σ₂, hcvk₁]
  have hxp₂ : σ₂.vars "xp" = xp₀ + kk := by simp [σ₂, σ₁, hxpval]
  -- Append the queue vertex to the arena.
  have e₃i : (Expr.var "xp").evalB B σ₂ = some (xp₀ + kk) := by
    simpa [hxp₂] using (evalB_var (B := B) (x := "xp") (σ := σ₂)
      (by rw [hxp₂]; omega))
  have e₃v : (Expr.var "cvu").evalB B σ₂ = some (Q kk) := by
    apply evalB_var
    simp only [σ₂, vars_setVar, if_neg (by decide : ¬ ("cvu" = "cvd")), σ₁,
      if_pos rfl]
    exact hQB
  have r₃ := Run.store (a := "xmem") e₃i e₃v (by
    simp only [σ₂, σ₁, arrs_setVar, hxmem, length_arrOf]
    omega)
  let σ₃ := σ₂.setArr "xmem" (xp₀ + kk) (Q kk)
  have hcvk₃ : σ₃.vars "cvk" = kk := by simp [σ₃, hcvk₂]
  have hxp₃ : σ₃.vars "xp" = xp₀ + kk := by simp [σ₃, hxp₂]
  have hqn₃ : σ₃.vars "qn" = q := by simp [σ₃, σ₂, σ₁, hqn]
  have hc₃ : σ₃.vars "c" = c := by simp [σ₃, σ₂, σ₁, hcvar]
  have hcvu₃ : σ₃.vars "cvu" = Q kk := by simp [σ₃, σ₂, σ₁]
  have hq₃ : σ₃.arrs "q" = arrOf n Q := by simp [σ₃, σ₂, σ₁, hq]
  have hqd₃ : σ₃.arrs "qd" = arrOf n QD := by simp [σ₃, σ₂, σ₁, hqd]
  have hasg₃ : σ₃.arrs "asg" =
      arrOf n (queueCell asg₀ q c r kk Q QD) := by
    simpa [σ₃, σ₂, σ₁, hkk] using hasg
  have hxmem₃ : σ₃.arrs "xmem" = arrOf na (upd Xm (xp₀ + kk) (Q kk)) := by
    simp [σ₃, σ₂, σ₁, hxmem, set_arrOf_eq_upd]
  -- The two-way first-catcher update.
  have hcondOuter : (Cond.lt (.var "cvd") (.lit (r + 1))).evalB B σ₃ =
      some (decide (QD kk < r + 1)) := by
    apply evalB_condLt
    · apply evalB_var
      simp only [σ₃, vars_setArr, σ₂, vars_setVar, if_pos rfl]
      exact hQDBk
    · exact evalB_lit hrB
  have hcondInner : (Cond.lt (.get "asg" (.var "cvu")) (.var "qn")).evalB B σ₃ =
      some (decide (queueCell asg₀ q c r kk Q QD (Q kk) < q)) := by
    apply evalB_condLt
    · apply evalB_get
      · apply evalB_var
        simp only [σ₃, vars_setArr, σ₂, vars_setVar,
          if_neg (by decide : ¬ ("cvu" = "cvd")), σ₁, if_pos rfl]
        exact hQB
      · rw [hasg₃, hcvu₃, getElem?_arrOf _ hQn]
      · exact hcurB
    · simpa [hqn₃] using (evalB_var (B := B) (x := "qn") (σ := σ₃)
        (by rw [hqn₃]; exact hqB))
  have hmid : ∃ σ₄ K₄,
      Run B
        (.ite (.lt (.var "cvd") (.lit (r + 1)))
          (.ite (.lt (.get "asg" (.var "cvu")) (.var "qn"))
            .skip (.store "asg" (.var "cvu") (.var "c")))
          .skip)
        σ₃ σ₄ K₄ ∧ K₄ ≤ 12 ∧
      σ₄.vars = σ₃.vars ∧ σ₄.arrs "xmem" = σ₃.arrs "xmem" ∧
      σ₄.arrs "q" = σ₃.arrs "q" ∧ σ₄.arrs "qd" = σ₃.arrs "qd" ∧
      σ₄.arrs "asg" = arrOf n (queueUpdate
        (queueCell asg₀ q c r kk Q QD) q c r kk Q QD) := by
    by_cases hd : QD kk ≤ r
    · rw [decide_eq_true (by omega)] at hcondOuter
      by_cases hclaimed : queueCell asg₀ q c r kk Q QD (Q kk) < q
      · rw [decide_eq_true hclaimed] at hcondInner
        refine ⟨σ₃, _, Run.ite_true hcondOuter (Run.ite_true hcondInner Run.skip),
          by simp, rfl, rfl, rfl, rfl, ?_⟩
        simpa [queueUpdate, hd, hclaimed] using hasg₃
      · rw [decide_eq_false hclaimed] at hcondInner
        have ecvu : (Expr.var "cvu").evalB B σ₃ = some (Q kk) := by
          apply evalB_var
          simp only [σ₃, vars_setArr, σ₂, vars_setVar,
            if_neg (by decide : ¬ ("cvu" = "cvd")), σ₁, if_pos rfl]
          exact hQB
        have ec : (Expr.var "c").evalB B σ₃ = some c := by
          simpa [hc₃] using (evalB_var (B := B) (x := "c") (σ := σ₃)
            (by rw [hc₃]; exact lt_trans hcq hqB))
        have rs := Run.store (a := "asg") ecvu ec (by
          simp only [σ₃, σ₂, arrs_setArr, if_neg (by decide : ¬ ("asg" = "xmem")),
            σ₁, arrs_setVar, hasg, length_arrOf]
          exact hQn)
        refine ⟨σ₃.setArr "asg" (Q kk) c, _,
          Run.ite_true hcondOuter (Run.ite_false hcondInner rs), by simp,
          by simp, by simp [σ₃], by simp [σ₃], by simp [σ₃], ?_⟩
        simp [hasg₃, set_arrOf_eq_upd, queueUpdate, hd, hclaimed]
    · rw [decide_eq_false (by omega)] at hcondOuter
      refine ⟨σ₃, _, Run.ite_false hcondOuter Run.skip, by simp, rfl, rfl, rfl, rfl, ?_⟩
      simpa [queueUpdate, hd] using hasg₃
  obtain ⟨σ₄, K₄, r₄, hK₄, hvars₄, hxmem₄, hq₄, hqd₄, hasg₄⟩ := hmid
  have hxp₄ : σ₄.vars "xp" = xp₀ + kk := by
    rw [hvars₄]
    exact hxp₃
  have hcvk₄ : σ₄.vars "cvk" = kk := by
    rw [hvars₄]
    exact hcvk₃
  have e₅ : (Expr.add (.var "xp") (.lit 1)).evalB B σ₄ = some (xp₀ + kk + 1) := by
    have h := evalB_bin (B := B) (σ := σ₄) (op := .add)
      (evalB_var (x := "xp") (by rw [hxp₄]; omega))
      (evalB_lit (show 1 < B by omega))
      (by simpa only [Bop.apply_add, hxp₄] using (show xp₀ + kk + 1 < B by omega))
    simpa only [Bop.apply_add, hxp₄] using h
  have r₅ := Run.assign (x := "xp") e₅
  let σ₅ := σ₄.setVar "xp" (xp₀ + kk + 1)
  have hcvk₅ : σ₅.vars "cvk" = kk := by simp [σ₅, hcvk₄]
  have hxp₅ : σ₅.vars "xp" = xp₀ + kk + 1 := by simp [σ₅]
  have e₆ : (Expr.add (.var "cvk") (.lit 1)).evalB B σ₅ = some (kk + 1) := by
    have h := evalB_bin (B := B) (σ := σ₅) (op := .add)
      (evalB_var (x := "cvk") (by rw [hcvk₅]; omega))
      (evalB_lit (show 1 < B by omega))
      (by simpa only [Bop.apply_add, hcvk₅] using (show kk + 1 < B by omega))
    simpa only [Bop.apply_add, hcvk₅] using h
  have r₆ := Run.assign (x := "cvk") e₆
  let σ₆ := σ₅.setVar "cvk" (kk + 1)
  have hcvk₆ : σ₆.vars "cvk" = kk + 1 := by simp [σ₆]
  have hxp₆ : σ₆.vars "xp" = xp₀ + kk + 1 := by simp [σ₆, hxp₅]
  have hq₄' : σ₄.arrs "q" = arrOf n Q := hq₄.trans hq₃
  have hqd₄' : σ₄.arrs "qd" = arrOf n QD := hqd₄.trans hqd₃
  have hxmem₄' : σ₄.arrs "xmem" = arrOf na (upd Xm (xp₀ + kk) (Q kk)) :=
    hxmem₄.trans hxmem₃
  refine ⟨σ₆, _, r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆)))), ?_, ?_, by
    simp [σ₆, σ₅, kk]⟩
  · simp only [emitQueueSlot, Expr.size]
    omega
  · refine ⟨upd Xm (xp₀ + kk) (Q kk), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [σ₆, σ₅, vars_setVar, if_neg (by decide : ¬ ("tail" = "cvk")),
        if_neg (by decide : ¬ ("tail" = "xp")), hvars₄, σ₃, vars_setArr,
        σ₂, σ₁, vars_setVar, if_neg (by decide : ¬ ("tail" = "cvd")),
        if_neg (by decide : ¬ ("tail" = "cvu")), htail]
    · simp only [σ₆, σ₅, vars_setVar, if_neg (by decide : ¬ ("qn" = "cvk")),
        if_neg (by decide : ¬ ("qn" = "xp")), hvars₄, σ₃, vars_setArr,
        σ₂, σ₁, vars_setVar, if_neg (by decide : ¬ ("qn" = "cvd")),
        if_neg (by decide : ¬ ("qn" = "cvu")), hqn]
    · simp only [σ₆, σ₅, vars_setVar, if_neg (by decide : ¬ ("c" = "cvk")),
        if_neg (by decide : ¬ ("c" = "xp")), hvars₄, σ₃, vars_setArr,
        σ₂, σ₁, vars_setVar, if_neg (by decide : ¬ ("c" = "cvd")),
        if_neg (by decide : ¬ ("c" = "cvu")), hcvar]
    · simpa [σ₆, σ₅] using hq₄'
    · simpa [σ₆, σ₅] using hqd₄'
    · simpa [σ₆, σ₅] using hxmem₄'
    · have hasg₆ : σ₆.arrs "asg" = arrOf n (queueUpdate
          (queueCell asg₀ q c r kk Q QD) q c r kk Q QD) := by
          simpa [σ₆, σ₅] using hasg₄
      rw [hasg₆,
        queueUpdate_queueCell (asg := asg₀) (q := q) (c := c) (d₀ := r)
          (k := kk) (Q := Q) (QD := QD) hcq, hcvk₆]
    · rw [hcvk₆]
      omega
    · rw [hxp₆, hcvk₆]
      omega
    · intro p hp
      rw [upd_of_ne _ (by omega)]
      exact hkeep p hp
    · intro i hi
      rw [hcvk₆] at hi
      rcases Nat.lt_or_ge i kk with hik | hik
      · rw [upd_of_ne _ (by omega)]
        exact hwrite i (by simpa [kk] using hik)
      · have hieq : i = kk := by omega
        subst i
        rw [upd_self]

/-- The complete emitter costs thirty-four ticks per touched vertex plus
the six-tick loop header. -/
theorem emitQueueCom_spec {B n na tail q c r xp₀ : ℕ} {Q QD Xm₀ asg₀ : ℕ → ℕ}
    (hnB : n < B) (htailB : tail < B) (htailn : tail ≤ n)
    (hqB : q < B) (hcq : c < q) (hrB : r + 1 < B)
    (hxpna : xp₀ + tail ≤ na) (hxpB : xp₀ + tail < B)
    (hQlt : ∀ i < tail, Q i < n) (hQDB : ∀ i < tail, QD i < B)
    (hasgB : ∀ w < n, asg₀ w < B) :
    Spec B
      (fun σ => QueueEmitInv n na tail q c r xp₀ Q QD Xm₀ asg₀ (σ.setVar "cvk" 0))
      (emitQueueCom r)
      (fun _ σ' => QueueEmitInv n na tail q c r xp₀ Q QD Xm₀ asg₀ σ' ∧
        σ'.vars "cvk" = tail)
      (34 * tail + 6) := by
  refine (Spec.forRangeZero "cvk" "tail"
    (QueueEmitInv n na tail q c r xp₀ Q QD Xm₀ asg₀) tail 30 htailB
    (fun _ h => h.choose_spec.2.2.2.2.2.2.2.1)
    (fun _ h => h.choose_spec.1)
    (emitQueueSlot_spec hnB htailB htailn hqB hcq hrB hxpna hxpB hQlt hQDB hasgB)).mono
      (by omega)

/-! ## One queue-emission turn -/

variable {q r c xp : ℕ} {A₀ centre Xoff Xmem asg : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}

/-- The current centre has not yet been deleted from the progressive mask. -/
theorem currentCentre_alive (hcentres : CentresBy n q A₀ π centre)
    (hI : RawCoverInvA G A₀ π centre q r c xp Xoff Xmem asg M) (hc : c < q) :
    M (centre c) ≠ 0 := by
  intro hzero
  rcases (hI.mask (centre c) (hcentres.centre_lt c hc)).mp hzero with hdead | ⟨i, hi, hic⟩
  · exact hcentres.alive c hc hdead
  · have hieq := hcentres.injective (by omega) hc hic
    omega

/-- **The block-BFS seam.**  Copying the returned queue after the old arena
prefix, updating first-catcher assignments from the aligned `qd` values,
and killing the current centre is exactly one `RawCoverInvA` turn.

The segment length is `tail`, not `n` and not `max tail 1`: active centres
are alive, hence the queue contains its source.  The statement exposes only
the entry-by-entry writes an IMP loop naturally proves. -/
theorem RawCoverInvA.stepQueue
    (hcentres : CentresBy n q A₀ π centre)
    (hI : RawCoverInvA G A₀ π centre q r c xp Xoff Xmem asg M) (hc : c < q)
    (htail : tail ≤ n)
    (hQlt : ∀ i, i < tail → Q i < n)
    (hseg : ∀ v, v < n →
      ((∃ i, i < tail ∧ Q i = v) ↔
        (M v ≠ 0 ∧ WD G M (2 * r) (centre c) v)))
    (hQinj : ∀ i, i < tail → ∀ j, j < tail → Q i = Q j → i = j)
    (hQD : ∀ i, i < tail → ∀ k, k ≤ 2 * r →
      (QD i ≤ k ↔ WD G M k (centre c) (Q i)))
    {Xoff' Xmem' asg' M' : ℕ → ℕ}
    (hoff : ∀ k ≤ c, Xoff' k = Xoff k)
    (hoff' : Xoff' (c + 1) = xp + tail)
    (hkeep : ∀ p < xp, Xmem' p = Xmem p)
    (hwrite : ∀ i < tail, Xmem' (xp + i) = Q i)
    (hasg' : ∀ w < n, A₀ w ≠ 0 →
      asg' w = if asg w < q then asg w
        else if ∃ i, i < tail ∧ Q i = w ∧ QD i ≤ r then c else q)
    (hM : ∀ u < n, M' u = if u = centre c then 0 else M u) :
    RawCoverInvA G A₀ π centre q r (c + 1) (xp + tail) Xoff' Xmem' asg' M' := by
  let D : ℕ → ℕ := queueDist (2 * r) tail Q QD
  have hsM : M (centre c) ≠ 0 := currentCentre_alive hcentres hI hc
  have hs : centre c < n := hcentres.centre_lt c hc
  have hD : ∀ (w : Fin n) (k : ℕ), k ≤ 2 * r →
      (D (w : ℕ) ≤ k ↔ WithinDist (masked G M) k ⟨centre c, hs⟩ w) := by
    intro w k hk
    exact (queueDist_le_iff_wd w.isLt hsM hk hseg hQD).trans
      (Lax3Proofs.RamBfs.wd_iff_withinDist hs w.isLt)
  apply RawCoverInvA.step hcentres hI hc hD hoff hoff' hkeep
  · intro w
    constructor
    · rintro ⟨p, hp₁, hp₂, hpw⟩
      obtain ⟨i, rfl⟩ : ∃ i, p = xp + i := ⟨p - xp, by omega⟩
      have hi : i < tail := by omega
      have hQi : Q i = w := by rw [← hpw, hwrite i hi]
      have hqn := hQlt i hi
      have hwd := (hseg (Q i) hqn).mp ⟨i, hi, rfl⟩ |>.2
      exact ⟨hQi ▸ hqn, (queueDist_le_iff_wd (hQi ▸ hqn) hsM le_rfl hseg hQD).mpr
        (by simpa only [hQi] using hwd)⟩
    · rintro ⟨hw, hdw⟩
      have hwd := (queueDist_le_iff_wd hw hsM le_rfl hseg hQD).mp hdw
      have hMw : M w ≠ 0 := by
        by_cases hws : w = centre c
        · simpa only [hws] using hsM
        · exact alive_of_wd hwd (Ne.symm hws)
      obtain ⟨i, hi, hQi⟩ := (hseg w hw).mpr ⟨hMw, hwd⟩
      exact ⟨xp + i, by omega, by omega, by rw [hwrite i hi, hQi]⟩
  · exact Nat.le_add_right xp tail
  · exact Nat.add_le_add_left htail xp
  · intro p p' hp₁ hp₂ hp₁' hp₂' heq
    obtain ⟨i, rfl⟩ : ∃ i, p = xp + i := ⟨p - xp, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, p' = xp + j := ⟨p' - xp, by omega⟩
    have hi : i < tail := by omega
    have hj : j < tail := by omega
    rw [hwrite i hi, hwrite j hj] at heq
    have := hQinj i hi j hj heq
    omega
  · intro w hw halive
    rw [hasg' w hw halive]
    by_cases hset : asg w < q
    · simp only [hset, if_true]
    · simp only [hset, if_false]
      have hiff := queueCatch_iff (d₀ := r) (d := 2 * r) (s := centre c) (w := w)
        hw hsM (by omega) hseg hQD
      by_cases hcatch : ∃ i, i < tail ∧ Q i = w ∧ QD i ≤ r
      · have hdist : D w ≤ r := hiff.mp hcatch
        simp only [hcatch, hdist, if_true]
      · have hdist : ¬ D w ≤ r := fun hd => hcatch (hiff.mpr hd)
        simp only [hcatch, hdist, if_false]
  · exact hM

/-! ## Axiom audit -/

#print axioms queueDist_le_iff_wd
#print axioms emitQueueSlot_spec
#print axioms emitQueueCom_spec
#print axioms RawCoverInvA.stepQueue

end Lax3Proofs.Refine.CoverActiveBlock
