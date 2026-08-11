import Lax3Proofs.Refine.ElimCompactCsr

/-!
# Compacting an active arena at its depth mask

The compact ordering engines use the fixed array name `"alv"`, while a
driver level stores its live mask at `alvName j`.  Copying that mask would
cost on the ambient carrier.  This file instead renames just the compacting
pass, so it reads the depth mask where it already lies.  The compact CSR,
its cost, and the frame are exactly those of the landed compacting theorem.
-/

namespace Lax3Proofs.Refine.OrderActiveCompact

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamDriver (alvName)
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.RamElim (CsrSimple)
open Lax3Proofs.Refine.ScatterBlock (MemList renCom renEnv maskSwap maskSwap_invol
  maskSwap_alv maskSwap_of_ne renEnv_arrs renEnv_vars renEnv_involutive renCom_run)
open Lax3Proofs.Refine.ElimCompact (compactPass memRowSum)
open Lax3Proofs.Refine.ElimCompactCsr (cOff CDone compactPass_run)

variable {n nt mm B : ℕ} {G : SimpleGraph (Fin n)}

/-- The compacting pass, with its mask reads redirected to level `j`'s
already resident active mask. -/
def compactPassAt (j : ℕ) : Com := renCom (maskSwap (alvName j)) compactPass

private theorem swap_fixed (j : ℕ) (a : String)
    (halv : a ≠ "alv") (hdepth : a ≠ alvName j) :
    maskSwap (alvName j) a = a :=
  maskSwap_of_ne halv hdepth

private theorem swap_ne_fixed (j : ℕ) {a q : String} (ha : a ≠ q)
    (hq : maskSwap (alvName j) q = q) : maskSwap (alvName j) a ≠ q := by
  intro h
  apply ha
  have := congrArg (maskSwap (alvName j)) h
  simpa only [maskSwap_invol, hq] using this

/-- The landed compacting theorem at a depth-named mask.  In particular,
the renamed pass has the same arena-sized charge and still writes only
`kix`, `kof`, and `ktg`; both mask arrays are framed automatically. -/
theorem compactPassAt_run (j : ℕ) {O T M Mem : ℕ → ℕ}
    (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) {σ : Env}
    (hmm : σ.vars "mm" = mm) (hmem : σ.arrs "mem" = arrOf n Mem)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs (alvName j) = arrOf n M) (hkix : ∃ g, σ.arrs "kix" = arrOf n g)
    (hkof : ∃ g, σ.arrs "kof" = arrOf (n + 1) g)
    (hktg : ∃ g, σ.arrs "ktg" = arrOf nt g) :
    ∃ (σ' : Env) (Kix KOf KT : ℕ → ℕ),
      Run B (compactPassAt j) σ σ' (40 * mm + 24 * memRowSum mm O Mem + 17) ∧
      (∀ k, k < mm → Kix (Mem k) = k) ∧
      σ'.vars "mm" = mm ∧
      σ'.vars "ks" = cOff O T M Mem Kix mm ∧
      σ'.arrs "kof" = arrOf (n + 1) KOf ∧
      (∀ i ≤ mm, KOf i = cOff O T M Mem Kix i) ∧
      σ'.arrs "ktg" = arrOf nt KT ∧
      CDone O T M Mem Kix KT mm ∧
      (∀ a, a ≠ "kix" → a ≠ "kof" → a ≠ "ktg" → σ'.arrs a = σ.arrs a) := by
  let f := maskSwap (alvName j)
  have hmemFix : f "mem" = "mem" :=
    swap_fixed j "mem" (by decide) (by simp [alvName, String.ext_iff])
  have hoffFix : f "off" = "off" :=
    swap_fixed j "off" (by decide) (by simp [alvName, String.ext_iff])
  have htgtFix : f "tgt" = "tgt" :=
    swap_fixed j "tgt" (by decide) (by simp [alvName, String.ext_iff])
  have hkixFix : f "kix" = "kix" :=
    swap_fixed j "kix" (by decide) (by simp [alvName, String.ext_iff])
  have hkofFix : f "kof" = "kof" :=
    swap_fixed j "kof" (by decide) (by simp [alvName, String.ext_iff])
  have hktgFix : f "ktg" = "ktg" :=
    swap_fixed j "ktg" (by decide) (by simp [alvName, String.ext_iff])
  obtain ⟨τ, Kix, KOf, KT, hrun, hKix, hmm', hks, hkof', hKOf, hktg', hdone, hframe⟩ :=
    compactPass_run (B := B) hcsr hml hB hnB hMB (hmm := by simpa [renEnv_vars] using hmm)
      (hmem := by simpa only [renEnv_arrs, hmemFix] using hmem)
      (hoff := by simpa only [renEnv_arrs, hoffFix] using hoff)
      (htgt := by simpa only [renEnv_arrs, htgtFix] using htgt)
      (halv := by simpa only [renEnv_arrs, maskSwap_alv] using halv)
      (hkix := by simpa only [renEnv_arrs, hkixFix] using hkix)
      (hkof := by simpa only [renEnv_arrs, hkofFix] using hkof)
      (hktg := by simpa only [renEnv_arrs, hktgFix] using hktg)
      (σ := renEnv f σ)
  let σ' := renEnv f τ
  have hrun' : Run B (compactPassAt j) σ σ'
      (40 * mm + 24 * memRowSum mm O Mem + 17) := by
    have h := renCom_run (f := f) (maskSwap_invol (alvName j)) hrun
    change Run B (renCom f compactPass) σ (renEnv f τ)
      (40 * mm + 24 * memRowSum mm O Mem + 17)
    rw [← renEnv_involutive (maskSwap_invol (alvName j)) σ]
    exact h
  refine ⟨σ', Kix, KOf, KT, hrun', hKix, ?_, hks, ?_, hKOf, ?_, hdone, ?_⟩
  · exact hmm'
  · simpa only [σ', renEnv_arrs, hkofFix] using hkof'
  · simpa only [σ', renEnv_arrs, hktgFix] using hktg'
  · intro a ha₁ ha₂ ha₃
    have h₁ : f a ≠ "kix" := swap_ne_fixed j ha₁ hkixFix
    have h₂ : f a ≠ "kof" := swap_ne_fixed j ha₂ hkofFix
    have h₃ : f a ≠ "ktg" := swap_ne_fixed j ha₃ hktgFix
    change (renEnv f τ).arrs a = σ.arrs a
    rw [renEnv_arrs, hframe (f a) h₁ h₂ h₃, renEnv_arrs]
    exact congrArg σ.arrs (maskSwap_invol (alvName j) a)

/-! ## Axioms -/

#print axioms compactPassAt_run

end Lax3Proofs.Refine.OrderActiveCompact
