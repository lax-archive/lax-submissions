import Lax3Proofs.Refine.OrderActiveFinal
import Lax3Proofs.Refine.ArenaSeam
import Lax3Proofs.Refine.MemThreadGate
import Lax3Proofs.RamDriverCompose

/-!
# The compact active ordering at the driver interface

The compact engines use `ork` for their carrier-sized rank scratch, while
the driver already reserves the same shape as its fixed `ord` scratch.  This
file first identifies those two calling conventions, then composes the
member entry, the complete augmentation chain, the final elimination, and
the driver's existing re-zeroing tail.
-/

namespace Lax3Proofs.Refine.OrderActiveDriver

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCompose
open Lax3Proofs.Refine.ScatterBlock (MemList renCom renEnv renEnv_arrs
  renEnv_vars renEnv_involutive renCom_run)
open Lax3Proofs.Refine.ArenaSeam (memEntry memEntry_run)
open Lax3Proofs.Refine.ElimCompact (memGraph memRowSum)
open Lax3Proofs.Refine.OrderActiveChain
open Lax3Proofs.Refine.OrderActiveRun
open Lax3Proofs.Refine.OrderActiveFinal
open Lax3Proofs.Refine.OrderActiveTail

/-! ## The resident rank scratch -/

/-- Reuse the driver's fixed `ord` allocation as the compact engine's
`ork` allocation.  No executable copy is needed. -/
def orderScratchSwap : String → String := fun a =>
  if a = "ork" then "ord" else if a = "ord" then "ork" else a

theorem orderScratchSwap_invol (a : String) :
    orderScratchSwap (orderScratchSwap a) = a := by
  by_cases hork : a = "ork"
  · subst a
    simp [orderScratchSwap]
  by_cases hord : a = "ord"
  · subst a
    simp [orderScratchSwap]
  simp [orderScratchSwap, hork, hord]

@[simp] theorem orderScratchSwap_ork : orderScratchSwap "ork" = "ord" := by
  simp [orderScratchSwap]

@[simp] theorem orderScratchSwap_ord : orderScratchSwap "ord" = "ork" := by
  simp [orderScratchSwap]

theorem orderScratchSwap_of_ne {a : String} (hork : a ≠ "ork")
    (hord : a ≠ "ord") : orderScratchSwap a = a := by
  simp [orderScratchSwap, hork, hord]

@[simp] theorem orderScratchSwap_mem : orderScratchSwap "mem" = "mem" := by
  exact orderScratchSwap_of_ne (by decide) (by decide)

@[simp] theorem orderScratchSwap_n : orderScratchSwap "n" = "n" := by
  exact orderScratchSwap_of_ne (by decide) (by decide)

@[simp] theorem orderScratchSwap_mm : orderScratchSwap "mm" = "mm" := by
  exact orderScratchSwap_of_ne (by decide) (by decide)

@[simp] theorem orderScratchSwap_off : orderScratchSwap "off" = "off" := by
  exact orderScratchSwap_of_ne (by decide) (by decide)

@[simp] theorem orderScratchSwap_tgt : orderScratchSwap "tgt" = "tgt" := by
  exact orderScratchSwap_of_ne (by decide) (by decide)

@[simp] theorem orderScratchSwap_alv : orderScratchSwap "alv" = "alv" := by
  exact orderScratchSwap_of_ne (by decide) (by decide)

@[simp] theorem orderScratchSwap_ordName (j : ℕ) :
    orderScratchSwap (ordName j) = ordName j := by
  apply orderScratchSwap_of_ne
  · simp [ordName, String.ext_iff]
  · simp [ordName, String.ext_iff]

@[simp] theorem orderScratchSwap_alvName (j : ℕ) :
    orderScratchSwap (alvName j) = alvName j := by
  apply orderScratchSwap_of_ne
  · simp [alvName, String.ext_iff]
  · simp [alvName, String.ext_iff]

theorem orderScratchSwap_activeZero {a : String} (ha : a ∈ activeZeroNames) :
    orderScratchSwap a = a := by
  simp only [activeZeroNames, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact orderScratchSwap_of_ne (by decide) (by decide)

/-- `LevelMem` and `OrderMem` already contain every physical allocation
used by the active ordering.  The only spelling change is `ork ↔ ord`. -/
theorem activeOrderSized_of_levelMem {B n cap mb ns W : ℕ} {σ : Env}
    (hLM : LevelMem B n cap mb σ) (hOM : OrderMem B n ns W σ) :
    ActiveOrderSized n W (renEnv orderScratchSwap σ) := by
  intro p hp
  simp only [activeOrderLayout, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [renEnv_arrs, orderScratchSwap_mem] using
      hLM.1.get (p := ("mem", n)) (by simp)
  · simpa only [renEnv_arrs, orderScratchSwap_ork] using
      hLM.1.get (p := ("ord", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ioff", n + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("itg", W)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("doff", n + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("dtg", W)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ooff", n + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("otg", W)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ofl", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("gof", n + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("gtg", W)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ffl", n)) (by simp)
  · simpa only [renEnv_arrs, orderScratchSwap_alv] using
      hLM.1.get (p := ("alv", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("deg", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("elm", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("rnk", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("idg", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("bh", n + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("bv", n + W + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("bn", n + W + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ifl", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("noff", n + 1)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("nfl", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ntg", W)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("stf", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("sta", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("std", n)) (by simp)
  · simpa [renEnv_arrs, orderScratchSwap] using
      hOM.2.2.1.get (p := ("ste", n)) (by simp)

/-! ## Active-prefix cleanup -/

/-- Exactly the physical arrays touched by the active-prefix cleanup. -/
def activeZeroLayout (n : ℕ) : List (String × ℕ) :=
  [("elm", n), ("bh", n + 1), ("ooff", n + 1), ("noff", n + 1),
    ("stf", n), ("sta", n), ("std", n), ("ste", n)]

abbrev ActiveZeroSized (n : ℕ) (σ : Env) : Prop := Sized (activeZeroLayout n) σ

theorem activeZeroSized_of_orderMem {B n ns W : ℕ} {σ : Env}
    (h : OrderMem B n ns W σ) : ActiveZeroSized n σ := by
  intro p hp
  simp only [activeZeroLayout, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact h.2.2.1.get (by simp)

/-- Re-zero exactly the scratch prefixes addressed by the compact engines.
The untouched physical tails are supplied by `ActiveZeroTail`. -/
def activeOrderZeroCom : Com :=
  .seq (fillUpto "elm" (.var "mm") (.lit 0))
    (.seq (fillUpto "bh" (.add (.var "mm") (.lit 1)) (.lit 0))
      (.seq (fillUpto "ooff" (.add (.var "mm") (.lit 1)) (.lit 0))
        (.seq (fillUpto "noff" (.add (.var "mm") (.lit 1)) (.lit 0))
          (.seq (fillUpto "stf" (.var "mm") (.lit 0))
            (.seq (fillUpto "sta" (.var "mm") (.lit 0))
              (.seq (fillUpto "std" (.var "mm") (.lit 0))
                (fillUpto "ste" (.var "mm") (.lit 0))))))))

/-- Five vertex-prefix fills and three offset-prefix fills. -/
def activeOrderZeroCost (mm : ℕ) : ℕ := 94 * mm + 93

private theorem zeroPrefixM_spec {B mm Nd : ℕ} (a : String)
    (hmmB : mm < B) (hmmNd : mm ≤ Nd) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf Nd g) ∧ σ.vars "mm" = mm)
      (fillUpto a (.var "mm") (.lit 0))
      (fun σ σ' => (∃ g, σ'.arrs a = arrOf Nd g ∧
          (∀ k < mm, g k = 0) ∧
          (∀ k, mm ≤ k → k < Nd → g k = (σ.arrs a).getD k 0)) ∧
        σ'.vars "i" = mm ∧ σ'.vars "mm" = mm)
      (11 * mm + 6) := by
  refine (Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) mm Nd a
    (.var "mm") (.lit 0) (fun _ => 0) (fun σ => σ.vars "mm" = mm)
    (by omega) hmmB hmmNd ?_ ?_ ?_).mono ?_
  · intro σ σ' h hv _
    exact (hv "mm" (by decide)).trans h
  · intro σ h
    rw [← h]
    exact evalB_var (by rw [h]; omega)
  · intro _ _ _
    exact evalB_lit (by omega)
  · simp only [Expr.size]
    omega

private theorem zeroPrefixM1_spec {B mm Nd : ℕ} (a : String)
    (hmm1B : mm + 1 < B) (hmm1Nd : mm + 1 ≤ Nd) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf Nd g) ∧ σ.vars "mm" = mm)
      (fillUpto a (.add (.var "mm") (.lit 1)) (.lit 0))
      (fun σ σ' => (∃ g, σ'.arrs a = arrOf Nd g ∧
          (∀ k < mm + 1, g k = 0) ∧
          (∀ k, mm + 1 ≤ k → k < Nd → g k = (σ.arrs a).getD k 0)) ∧
        σ'.vars "i" = mm + 1 ∧ σ'.vars "mm" = mm)
      (13 * mm + 21) := by
  refine (Lax3Proofs.RamDriverOrder.fillKeep_spec (B := B) (mm + 1) Nd a
    (.add (.var "mm") (.lit 1)) (.lit 0) (fun _ => 0)
    (fun σ => σ.vars "mm" = mm) (by omega) hmm1B hmm1Nd ?_ ?_ ?_).mono ?_
  · intro σ σ' h hv _
    exact (hv "mm" (by decide)).trans h
  · intro σ h
    exact Lax3Proofs.Refine.CompactPreps.evalB_mmAdd1 h hmm1B
  · intro _ _ _
    exact evalB_lit (by omega)
  · simp only [Expr.size]
    omega

/-- One prefix fill changes none of the inactive cells, including in the
array it writes. -/
private theorem activeZeroTail_fill {B mm N Nd K : ℕ} {a : String}
    {bnd e : Expr} {σ σ' : Env} {g g' : ℕ → ℕ}
    (hr : Run B (fillUpto a bnd e) σ σ' K)
    (hN : activeZeroLen mm a = N) (hNNd : N ≤ Nd)
    (harr : σ.arrs a = arrOf Nd g)
    (harr' : σ'.arrs a = arrOf Nd g')
    (htail : ∀ k, N ≤ k → k < Nd → g' k = (σ.arrs a).getD k 0) :
    ActiveZeroTail mm σ σ' := by
  intro b hb
  by_cases hba : b = a
  · subst b
    rw [hN, harr, harr']
    exact drop_arrOf_congr hNNd fun k hk hkNd => by
      rw [htail k hk hkNd, harr, getD_arrOf g hkNd]
  · rw [hr.frame_arr b (by
      rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]
      simpa using hba)]

/-- A zero live prefix plus a preserved tail that was initially zero is a
zero physical array. -/
private theorem zeroed_of_prefix_tail {N Nd : ℕ} {a : String}
    {σ₀ σ : Env} {g g₀ : ℕ → ℕ}
    (harr : σ.arrs a = arrOf Nd g) (hprefix : ∀ k < N, g k = 0)
    (htail : (σ.arrs a).drop N = (σ₀.arrs a).drop N)
    (harr₀ : σ₀.arrs a = arrOf Nd g₀)
    (hzero₀ : ∀ v ∈ σ₀.arrs a, v = 0) :
    ∀ v ∈ σ.arrs a, v = 0 := by
  rw [harr]
  apply Lax3Proofs.RamDriverCompose.eq_zero_of_mem_arrOf
  intro k hk
  by_cases hkN : k < N
  · exact hprefix k hkN
  · have hNk : N ≤ k := by omega
    have hd := congrArg (fun xs : List ℕ => xs.getD (k - N) 0) htail
    change ((σ.arrs a).drop N).getD (k - N) 0 =
      ((σ₀.arrs a).drop N).getD (k - N) 0 at hd
    rw [Lax3Proofs.RamDriverIO.getD_drop, Lax3Proofs.RamDriverIO.getD_drop,
      Nat.add_sub_of_le hNk, harr, getD_arrOf g hk, harr₀, getD_arrOf g₀ hk] at hd
    exact hd.trans (hzero₀ (g₀ k) (by
      rw [harr₀]
      exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩))

/-- The compact core's tail certificate lets the active-prefix cleanup
recover all eight carrier-wide zero clauses of `OrderMem`, without a
carrier-sized pass. -/
theorem activeOrderZero_spec {B n mm ns W : ℕ} {σ₀ σ : Env}
    (hmm1B : mm + 1 < B) (hmn : mm ≤ n)
    (hOM : OrderMem B n ns W σ₀) (hmm : σ.vars "mm" = mm)
    (hsz : ActiveZeroSized n σ) (htail₀ : ActiveZeroTail mm σ₀ σ) :
    ∃ σ', Run B activeOrderZeroCom σ σ' (activeOrderZeroCost mm) ∧
      σ'.vars "mm" = mm ∧ ActiveZeroSized n σ' ∧
      (∀ v ∈ σ'.arrs "elm", v = 0) ∧ (∀ v ∈ σ'.arrs "bh", v = 0) ∧
      (∀ v ∈ σ'.arrs "ooff", v = 0) ∧ (∀ v ∈ σ'.arrs "noff", v = 0) ∧
      (∀ v ∈ σ'.arrs "stf", v = 0) ∧ (∀ v ∈ σ'.arrs "sta", v = 0) ∧
      (∀ v ∈ σ'.arrs "std", v = 0) ∧ (∀ v ∈ σ'.arrs "ste", v = 0) := by
  obtain ⟨-, -, hsz₀, hzElm₀, hzBh₀, hzOoff₀, hzNoff₀, hzStf₀, hzSta₀,
    hzStd₀, hzSte₀, -, -⟩ := hOM
  have get (τ : Env) (hτ : ActiveZeroSized n τ) (a : String) (N : ℕ)
      (ha : (a, N) ∈ activeZeroLayout n) : ∃ g, τ.arrs a = arrOf N g :=
    hτ.get ha
  obtain ⟨τ₁, r₁, ⟨e₁, hA₁, hZ₁, hT₁⟩, -, hmm₁⟩ :=
    (zeroPrefixM_spec (B := B) (mm := mm) (Nd := n) "elm" (by omega) hmn).run
      ⟨get σ hsz "elm" n (by simp [activeZeroLayout]), hmm⟩
  have hsz₁ := hsz.run r₁
  have ht₁ : ActiveZeroTail mm σ τ₁ :=
    activeZeroTail_fill r₁ (activeZeroLen_elm mm) hmn
      (get σ hsz "elm" n (by simp [activeZeroLayout])).choose_spec hA₁ hT₁
  obtain ⟨τ₂, r₂, ⟨e₂, hA₂, hZ₂, hT₂⟩, -, hmm₂⟩ :=
    (zeroPrefixM1_spec (B := B) (mm := mm) (Nd := n + 1) "bh" hmm1B (by omega)).run
      ⟨get τ₁ hsz₁ "bh" (n + 1) (by simp [activeZeroLayout]), hmm₁⟩
  have hsz₂ := hsz₁.run r₂
  have ht₂ : ActiveZeroTail mm τ₁ τ₂ :=
    activeZeroTail_fill r₂ (activeZeroLen_bh mm) (by omega)
      (get τ₁ hsz₁ "bh" (n + 1) (by simp [activeZeroLayout])).choose_spec hA₂ hT₂
  obtain ⟨τ₃, r₃, ⟨e₃, hA₃, hZ₃, hT₃⟩, -, hmm₃⟩ :=
    (zeroPrefixM1_spec (B := B) (mm := mm) (Nd := n + 1) "ooff" hmm1B (by omega)).run
      ⟨get τ₂ hsz₂ "ooff" (n + 1) (by simp [activeZeroLayout]), hmm₂⟩
  have hsz₃ := hsz₂.run r₃
  have ht₃ : ActiveZeroTail mm τ₂ τ₃ :=
    activeZeroTail_fill r₃ (activeZeroLen_ooff mm) (by omega)
      (get τ₂ hsz₂ "ooff" (n + 1) (by simp [activeZeroLayout])).choose_spec hA₃ hT₃
  obtain ⟨τ₄, r₄, ⟨e₄, hA₄, hZ₄, hT₄⟩, -, hmm₄⟩ :=
    (zeroPrefixM1_spec (B := B) (mm := mm) (Nd := n + 1) "noff" hmm1B (by omega)).run
      ⟨get τ₃ hsz₃ "noff" (n + 1) (by simp [activeZeroLayout]), hmm₃⟩
  have hsz₄ := hsz₃.run r₄
  have ht₄ : ActiveZeroTail mm τ₃ τ₄ :=
    activeZeroTail_fill r₄ (activeZeroLen_noff mm) (by omega)
      (get τ₃ hsz₃ "noff" (n + 1) (by simp [activeZeroLayout])).choose_spec hA₄ hT₄
  obtain ⟨τ₅, r₅, ⟨e₅, hA₅, hZ₅, hT₅⟩, -, hmm₅⟩ :=
    (zeroPrefixM_spec (B := B) (mm := mm) (Nd := n) "stf" (by omega) hmn).run
      ⟨get τ₄ hsz₄ "stf" n (by simp [activeZeroLayout]), hmm₄⟩
  have hsz₅ := hsz₄.run r₅
  have ht₅ : ActiveZeroTail mm τ₄ τ₅ :=
    activeZeroTail_fill r₅ (activeZeroLen_stf mm) hmn
      (get τ₄ hsz₄ "stf" n (by simp [activeZeroLayout])).choose_spec hA₅ hT₅
  obtain ⟨τ₆, r₆, ⟨e₆, hA₆, hZ₆, hT₆⟩, -, hmm₆⟩ :=
    (zeroPrefixM_spec (B := B) (mm := mm) (Nd := n) "sta" (by omega) hmn).run
      ⟨get τ₅ hsz₅ "sta" n (by simp [activeZeroLayout]), hmm₅⟩
  have hsz₆ := hsz₅.run r₆
  have ht₆ : ActiveZeroTail mm τ₅ τ₆ :=
    activeZeroTail_fill r₆ (activeZeroLen_sta mm) hmn
      (get τ₅ hsz₅ "sta" n (by simp [activeZeroLayout])).choose_spec hA₆ hT₆
  obtain ⟨τ₇, r₇, ⟨e₇, hA₇, hZ₇, hT₇⟩, -, hmm₇⟩ :=
    (zeroPrefixM_spec (B := B) (mm := mm) (Nd := n) "std" (by omega) hmn).run
      ⟨get τ₆ hsz₆ "std" n (by simp [activeZeroLayout]), hmm₆⟩
  have hsz₇ := hsz₆.run r₇
  have ht₇ : ActiveZeroTail mm τ₆ τ₇ :=
    activeZeroTail_fill r₇ (activeZeroLen_std mm) hmn
      (get τ₆ hsz₆ "std" n (by simp [activeZeroLayout])).choose_spec hA₇ hT₇
  obtain ⟨τ₈, r₈, ⟨e₈, hA₈, hZ₈, hT₈⟩, -, hmm₈⟩ :=
    (zeroPrefixM_spec (B := B) (mm := mm) (Nd := n) "ste" (by omega) hmn).run
      ⟨get τ₇ hsz₇ "ste" n (by simp [activeZeroLayout]), hmm₇⟩
  have hsz₈ := hsz₇.run r₈
  have ht₈ : ActiveZeroTail mm τ₇ τ₈ :=
    activeZeroTail_fill r₈ (activeZeroLen_ste mm) hmn
      (get τ₇ hsz₇ "ste" n (by simp [activeZeroLayout])).choose_spec hA₈ hT₈
  have ht : ActiveZeroTail mm σ₀ τ₈ :=
    ActiveZeroTail.trans htail₀ (ActiveZeroTail.trans ht₁ (ActiveZeroTail.trans ht₂
      (ActiveZeroTail.trans ht₃ (ActiveZeroTail.trans ht₄ (ActiveZeroTail.trans ht₅
        (ActiveZeroTail.trans ht₆ (ActiveZeroTail.trans ht₇ ht₈)))))))
  have f₂ : ∀ a, a ≠ "bh" → τ₂.arrs a = τ₁.arrs a := fun a ha =>
    r₂.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have f₃ : ∀ a, a ≠ "ooff" → τ₃.arrs a = τ₂.arrs a := fun a ha =>
    r₃.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have f₄ : ∀ a, a ≠ "noff" → τ₄.arrs a = τ₃.arrs a := fun a ha =>
    r₄.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have f₅ : ∀ a, a ≠ "stf" → τ₅.arrs a = τ₄.arrs a := fun a ha =>
    r₅.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have f₆ : ∀ a, a ≠ "sta" → τ₆.arrs a = τ₅.arrs a := fun a ha =>
    r₆.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have f₇ : ∀ a, a ≠ "std" → τ₇.arrs a = τ₆.arrs a := fun a ha =>
    r₇.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have f₈ : ∀ a, a ≠ "ste" → τ₈.arrs a = τ₇.arrs a := fun a ha =>
    r₈.frame_arr a (by rw [Lax3Proofs.RamDriverCompose.warrs_fillUpto]; simpa using ha)
  have g₁ : τ₈.arrs "elm" = arrOf n e₁ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide),
      f₄ _ (by decide), f₃ _ (by decide), f₂ _ (by decide)]
    exact hA₁
  have g₂ : τ₈.arrs "bh" = arrOf (n + 1) e₂ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide),
      f₄ _ (by decide), f₃ _ (by decide)]
    exact hA₂
  have g₃ : τ₈.arrs "ooff" = arrOf (n + 1) e₃ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide),
      f₄ _ (by decide)]
    exact hA₃
  have g₄ : τ₈.arrs "noff" = arrOf (n + 1) e₄ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide), f₅ _ (by decide)]
    exact hA₄
  have g₅ : τ₈.arrs "stf" = arrOf n e₅ := by
    rw [f₈ _ (by decide), f₇ _ (by decide), f₆ _ (by decide)]
    exact hA₅
  have g₆ : τ₈.arrs "sta" = arrOf n e₆ := by
    rw [f₈ _ (by decide), f₇ _ (by decide)]
    exact hA₆
  have g₇ : τ₈.arrs "std" = arrOf n e₇ := by
    rw [f₈ _ (by decide)]
    exact hA₇
  obtain ⟨e₀, he₀⟩ := hsz₀.get (p := ("elm", n)) (by simp)
  obtain ⟨b₀, hb₀⟩ := hsz₀.get (p := ("bh", n + 1)) (by simp)
  obtain ⟨oo₀, hoo₀⟩ := hsz₀.get (p := ("ooff", n + 1)) (by simp)
  obtain ⟨no₀, hno₀⟩ := hsz₀.get (p := ("noff", n + 1)) (by simp)
  obtain ⟨sf₀, hsf₀⟩ := hsz₀.get (p := ("stf", n)) (by simp)
  obtain ⟨sa₀, hsa₀⟩ := hsz₀.get (p := ("sta", n)) (by simp)
  obtain ⟨sd₀, hsd₀⟩ := hsz₀.get (p := ("std", n)) (by simp)
  obtain ⟨se₀, hse₀⟩ := hsz₀.get (p := ("ste", n)) (by simp)
  have rAll : Run B activeOrderZeroCom σ τ₈ (activeOrderZeroCost mm) := by
    exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈))))))).mono (by
      simp only [activeOrderZeroCost]
      omega)
  refine ⟨τ₈, rAll, hmm₈, hsz₈, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zeroed_of_prefix_tail g₁ hZ₁
      (by simpa using ht "elm" (by simp [activeZeroNames])) he₀ hzElm₀
  · exact zeroed_of_prefix_tail g₂ hZ₂
      (by simpa using ht "bh" (by simp [activeZeroNames])) hb₀ hzBh₀
  · exact zeroed_of_prefix_tail g₃ hZ₃
      (by simpa using ht "ooff" (by simp [activeZeroNames])) hoo₀ hzOoff₀
  · exact zeroed_of_prefix_tail g₄ hZ₄
      (by simpa using ht "noff" (by simp [activeZeroNames])) hno₀ hzNoff₀
  · exact zeroed_of_prefix_tail g₅ hZ₅
      (by simpa using ht "stf" (by simp [activeZeroNames])) hsf₀ hzStf₀
  · exact zeroed_of_prefix_tail g₆ hZ₆
      (by simpa using ht "sta" (by simp [activeZeroNames])) hsa₀ hzSta₀
  · exact zeroed_of_prefix_tail g₇ hZ₇
      (by simpa using ht "std" (by simp [activeZeroNames])) hsd₀ hzStd₀
  · exact zeroed_of_prefix_tail hA₈ hZ₈
      (by simpa using ht "ste" (by simp [activeZeroNames])) hse₀ hzSte₀

/-! ## Executable composition -/

def activeOrderCore (j R : ℕ) : Com :=
  renCom orderScratchSwap
    (.seq (compactActiveChainCom j R) (activeFinishCom j))

/-- A uniform core charge: the compact slot counts produced at runtime are
bounded by the raw active row mass and by the chosen live width. -/
def activeOrderCoreCost (mm rs w R : ℕ) : ℕ :=
  compactActiveChainCost mm rs rs w R + activeFinishCost mm w

private theorem compactActiveChainCost_mono_cs {mm rs cs w R : ℕ} (h : cs ≤ rs) :
    compactActiveChainCost mm rs cs w R ≤ compactActiveChainCost mm rs rs w R := by
  simp only [compactActiveChainCost,
    Lax3Proofs.Refine.OrderActiveInit.compactElimFoldInitCost,
    Lax3Proofs.Refine.OrderActiveInit.elimFoldInitCost,
    Lax3Proofs.Refine.OrderActiveElim.elimWorkCost,
    Lax3Proofs.Refine.OrderActiveElim.elimWorkPrepCost,
    Lax3Proofs.RamElim.elimCost,
    Lax3Proofs.Refine.ElimCompact.scatterCost]
  omega

private theorem activeFinishCost_mono {mm m w : ℕ} (h : m ≤ w) :
    activeFinishCost mm m ≤ activeFinishCost mm w := by
  simp only [activeFinishCost, Lax3Proofs.Refine.SymCompact.symCompactCost_eq,
    Lax3Proofs.Refine.OrderActiveElim.elimWorkCost,
    Lax3Proofs.Refine.OrderActiveElim.elimWorkPrepCost,
    Lax3Proofs.RamElim.elimCost,
    Lax3Proofs.Refine.ElimCompact.scatterCost]
  omega

/-- The complete compact core at the driver's resident `ord` allocation.
The theorem deliberately stops before restoring `OrderMem`; that is the
job of `activeOrderZero_spec`, using the tail certificate returned here. -/
theorem activeOrderCore_spec {B n mm ns W w j R d D₁ : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Mem : ℕ → ℕ} {σ : Env}
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M))
    (hBns : n + ns + 1 < B) (hBw : mm + w + 1 < B) (hnB : n < B)
    (hMB : ∀ v < n, M v < B) (hnsW : ns ≤ W) (hwW : w ≤ W)
    (hd : Lax3Proofs.Augmentation.LowDegreeVertices (memGraph G M hml) d)
    (hdens : ∀ (D : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain (memGraph G M hml) D i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity D i D₁)
    (hcap : activeChainWidthE mm (memRowSum mm O Mem) d D₁ R ≤ w)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hmem : σ.arrs "mem" = arrOf n Mem)
    (hoff : σ.arrs "off" = arrOf (n + 1) O)
    (htgt : σ.arrs "tgt" = arrOf W T)
    (halv : σ.arrs (alvName j) = arrOf n M)
    (hord : ∃ g, σ.arrs (ordName j) = arrOf n g)
    (hsz : ActiveOrderSized n W (renEnv orderScratchSwap σ)) :
    ∃ (σ' : Env) (m : ℕ)
        (D : ℕ → Lax3Proofs.Augmentation.Orientation mm) (d₀ k : ℕ)
        (πm : Equiv.Perm (Fin mm)) (centre : ℕ → ℕ),
      Run B (activeOrderCore j R) σ σ'
        (activeOrderCoreCost mm (memRowSum mm O Mem) w R) ∧
      m ≤ w ∧ σ'.arrs (ordName j) = arrOf n centre ∧
      Lax3Proofs.RamCoverActive.CentresBy n mm M
        (Lax3Proofs.Refine.OrderActiveMath.activePerm hml πm) centre ∧
      Lax3Proofs.CoverDegree.AugChainData (memGraph G M hml) D πm R d₀ k ∧
      σ'.vars "n" = n ∧ σ'.vars "mm" = mm ∧
      σ'.arrs "mem" = arrOf n Mem ∧ ActiveZeroTail mm σ σ' := by
  let f := orderScratchSwap
  obtain ⟨τ₁, d₀, cs, r₁, hcsrs, -, hI, hmin, htail₁⟩ :=
    compactActiveChain_spec hcsr hml hBns hBw hnB hMB hnsW hwW hd hdens hcap
      (hn := by simpa only [renEnv_vars] using hn)
      (hmm := by simpa only [renEnv_vars] using hmm)
      (hmem := by simpa only [renEnv_arrs, f, orderScratchSwap_mem] using hmem)
      (hoff := by simpa only [renEnv_arrs, f, orderScratchSwap_off] using hoff)
      (htgt := by simpa only [renEnv_arrs, f, orderScratchSwap_tgt] using htgt)
      (halv := by simpa only [renEnv_arrs, f, orderScratchSwap_alvName] using halv)
      (hsz := hsz) (σ := renEnv f σ)
  have hcapcs : activeChainWidthE mm cs d D₁ R ≤ w := by
    simp only [activeChainWidthE] at hcap ⊢
    omega
  have hord₀ : ∃ g, (renEnv f σ).arrs (ordName j) = arrOf n g := by
    simpa only [renEnv_arrs, f, orderScratchSwap_ordName] using hord
  have hord₁ : ∃ g, τ₁.arrs (ordName j) = arrOf n g :=
    Lax3Proofs.RamDriverCompose.sizedRun r₁ hord₀
  obtain ⟨τ₂, m, D, k, πm, centre, r₂, hmw, hord₂, hcentres, hdata, -, hn₂,
      hmm₂, hmem₂, -, -, htail₂⟩ :=
    activeFinish_spec hml hml.card_le hwW hBw hnB (hmin d hd) hdens hcapcs hmin
      hord₁ hI
  have rInt : Run B (.seq (compactActiveChainCom j R) (activeFinishCom j))
      (renEnv f σ) τ₂ (activeOrderCoreCost mm (memRowSum mm O Mem) w R) :=
    (r₁.seq r₂).mono (Nat.add_le_add
      (compactActiveChainCost_mono_cs hcsrs) (activeFinishCost_mono hmw))
  let σ' := renEnv f τ₂
  have rOut : Run B (activeOrderCore j R) σ σ'
      (activeOrderCoreCost mm (memRowSum mm O Mem) w R) := by
    have hr := renCom_run (f := f) orderScratchSwap_invol rInt
    change Run B (renCom f (.seq (compactActiveChainCom j R) (activeFinishCom j)))
      σ (renEnv f τ₂) (activeOrderCoreCost mm (memRowSum mm O Mem) w R)
    rw [← renEnv_involutive orderScratchSwap_invol σ]
    exact hr
  have htailInt : ActiveZeroTail mm (renEnv f σ) τ₂ :=
    ActiveZeroTail.trans htail₁ htail₂
  have htailOut : ActiveZeroTail mm σ σ' := by
    intro a ha
    simpa only [σ', renEnv_arrs, f, orderScratchSwap_activeZero ha] using htailInt a ha
  refine ⟨σ', m, D, d₀, k, πm, centre, rOut, hmw, ?_, hcentres, hdata,
    ?_, ?_, ?_, htailOut⟩
  · simpa only [σ', renEnv_arrs, f, orderScratchSwap_ordName] using hord₂
  · simpa only [σ', renEnv_vars] using hn₂
  · simpa only [σ', renEnv_vars] using hmm₂
  · simpa only [σ', renEnv_arrs, f, orderScratchSwap_mem] using hmem₂

def activeOrderPhase (j R : ℕ) : Com :=
  .seq (memEntry j) (.seq (activeOrderCore j R) activeOrderZeroCom)

/-! ## Axioms -/

#print axioms activeOrderZero_spec
#print axioms activeOrderCore_spec

end Lax3Proofs.Refine.OrderActiveDriver
