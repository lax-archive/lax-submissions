import Lax3Proofs.Refine.CoverActiveStreamKill
import Lax3Proofs.Refine.ActiveLevel

/-!
# Depth-owned storage for a streamed active-cover turn

A streamed centre is consumed before the next row is produced, but its child
level still runs the complete recursive driver.  The child therefore reuses
the fixed cover arrays.  This file moves the five pieces of parent state that
must cross that call onto arrays owned by the parent's depth:

* the ordering, progressive mask, resident row, and first-catcher assignment;
* the clean distance array used by the next streamed BFS.

The fifth pair deliberately exchanges `"dist"` with `pdsName j`.  Inside the
same renamed turn, `cacheRoundCom` uses the other side of that exchange for its
temporary retained-parent search.  Thus the two distance computations remain
disjoint without a copy or a carrier walk.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamDepth

open Lax3Proofs.RamDriver
open Lax3Proofs.Refine.ScatterBlock
open Lax13Proofs.Imp
open Lax13Proofs.Reasoning

/-! ## The array permutation -/

/-- Exchange the reusable streamed arrays with their depth-owned storage. -/
def streamDepthSwap (j : ℕ) (a : String) : String :=
  if a = "ord" then ordName j
  else if a = ordName j then "ord"
  else if a = "alv" then cpsName j
  else if a = cpsName j then "alv"
  else if a = "xmem" then xmmName j
  else if a = xmmName j then "xmem"
  else if a = "asg" then asgName j
  else if a = asgName j then "asg"
  else if a = "dist" then pdsName j
  else if a = pdsName j then "dist"
  else a

@[simp] theorem streamDepthSwap_ord (j : ℕ) :
    streamDepthSwap j "ord" = ordName j := by
  simp [streamDepthSwap]

@[simp] theorem streamDepthSwap_ordName (j : ℕ) :
    streamDepthSwap j (ordName j) = "ord" := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_alv (j : ℕ) :
    streamDepthSwap j "alv" = cpsName j := by
  simp [streamDepthSwap, ordName, String.ext_iff]

@[simp] theorem streamDepthSwap_cpsName (j : ℕ) :
    streamDepthSwap j (cpsName j) = "alv" := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_xmem (j : ℕ) :
    streamDepthSwap j "xmem" = xmmName j := by
  simp [streamDepthSwap, ordName, cpsName, String.ext_iff]

@[simp] theorem streamDepthSwap_xmmName (j : ℕ) :
    streamDepthSwap j (xmmName j) = "xmem" := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_asg (j : ℕ) :
    streamDepthSwap j "asg" = asgName j := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, String.ext_iff]

@[simp] theorem streamDepthSwap_asgName (j : ℕ) :
    streamDepthSwap j (asgName j) = "asg" := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_dist (j : ℕ) :
    streamDepthSwap j "dist" = pdsName j := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, String.ext_iff]

@[simp] theorem streamDepthSwap_pdsName (j : ℕ) :
    streamDepthSwap j (pdsName j) = "dist" := by
  simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

/-! Names used by the recursive interface are outside the five exchanges. -/

@[simp] theorem streamDepthSwap_alvName (j d : ℕ) :
    streamDepthSwap j (alvName d) = alvName d := by
  simp [streamDepthSwap, alvName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_gamName (j d : ℕ) :
    streamDepthSwap j (gamName d) = gamName d := by
  simp [streamDepthSwap, gamName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_cluName (j d : ℕ) :
    streamDepthSwap j (cluName d) = cluName d := by
  simp [streamDepthSwap, cluName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_resName (j d : ℕ) :
    streamDepthSwap j (resName d) = resName d := by
  simp [streamDepthSwap, resName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_batName (j d : ℕ) :
    streamDepthSwap j (batName d) = batName d := by
  simp [streamDepthSwap, batName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_memName (j d : ℕ) :
    streamDepthSwap j (memName d) = memName d := by
  simp [streamDepthSwap, memName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_klName (j d : ℕ) :
    streamDepthSwap j (klName d) = klName d := by
  simp [streamDepthSwap, klName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_colName (j d s : ℕ) :
    streamDepthSwap j (colName d s) = colName d s := by
  simp [streamDepthSwap, colName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_tabName (j d i : ℕ) :
    streamDepthSwap j (tabName d i) = tabName d i := by
  simp [streamDepthSwap, tabName, ordName, cpsName, xmmName, asgName, pdsName,
    balAltName, String.ext_iff]

@[simp] theorem streamDepthSwap_parName (j d : ℕ) :
    streamDepthSwap j (parName d) = parName d := by
  simp [streamDepthSwap, parName, balName, ordName, cpsName, xmmName, asgName,
    pdsName, balAltName, String.ext_iff]

theorem streamDepthSwap_of_ne (j : ℕ) (a : String)
    (ho : a ≠ "ord") (hoj : a ≠ ordName j)
    (hl : a ≠ "alv") (hlj : a ≠ cpsName j)
    (hx : a ≠ "xmem") (hxj : a ≠ xmmName j)
    (ha : a ≠ "asg") (haj : a ≠ asgName j)
    (hd : a ≠ "dist") (hdj : a ≠ pdsName j) :
    streamDepthSwap j a = a := by
  simp [streamDepthSwap, ho, hoj, hl, hlj, hx, hxj, ha, haj, hd, hdj]

/-- A depth-storage renaming fixes every array owned by a strictly shallower
level. -/
theorem streamDepthSwap_of_belowArr {j : ℕ} {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    streamDepthSwap j a = a := by
  have hdigit := Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h
  apply streamDepthSwap_of_ne
  · exact fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "ord") (hq ▸ hdigit)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
  · exact fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "alv") (hq ▸ hdigit)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
  · exact fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "xmem") (hq ▸ hdigit)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
  · exact fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "asg") (hq ▸ hdigit)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
  · exact fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "dist") (hq ▸ hdigit)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)

theorem streamDepthSwap_ordName_of_ne {j d : ℕ} (h : d ≠ j) :
    streamDepthSwap j (ordName d) = ordName d := by
  apply streamDepthSwap_of_ne
  · simp [ordName, String.ext_iff]
  · exact fun he => h (Lax3Proofs.RamDriverWrites.ordName_inj he)
  all_goals simp [ordName, cpsName, xmmName, asgName, pdsName, balAltName,
    String.ext_iff]

theorem streamDepthSwap_cpsName_of_ne {j d : ℕ} (h : d ≠ j) :
    streamDepthSwap j (cpsName d) = cpsName d := by
  apply streamDepthSwap_of_ne
  · simp [cpsName, String.ext_iff]
  · simp [cpsName, ordName, String.ext_iff]
  · simp [cpsName, String.ext_iff]
  · exact fun he => h (Lax3Proofs.RamDriverWrites.cpsName_inj he)
  all_goals simp [ordName, cpsName, xmmName, asgName, pdsName, balAltName,
    String.ext_iff]

theorem streamDepthSwap_xmmName_of_ne {j d : ℕ} (h : d ≠ j) :
    streamDepthSwap j (xmmName d) = xmmName d := by
  apply streamDepthSwap_of_ne
  · simp [xmmName, String.ext_iff]
  · simp [xmmName, ordName, String.ext_iff]
  · simp [xmmName, String.ext_iff]
  · simp [xmmName, cpsName, String.ext_iff]
  · exact (Lax3Proofs.RamDriverCompose.xmem_ne_xmmName d).symm
  · exact fun he => h (Lax3Proofs.RamDriverWrites.xmmName_inj he)
  all_goals simp [ordName, cpsName, xmmName, asgName, pdsName, balAltName,
    String.ext_iff]

theorem streamDepthSwap_asgName_of_ne {j d : ℕ} (h : d ≠ j) :
    streamDepthSwap j (asgName d) = asgName d := by
  apply streamDepthSwap_of_ne
  · simp [asgName, String.ext_iff]
  · simp [asgName, ordName, String.ext_iff]
  · simp [asgName, String.ext_iff]
  · simp [asgName, cpsName, String.ext_iff]
  · simp [asgName, String.ext_iff]
  · simp [asgName, xmmName, String.ext_iff]
  · simp [asgName, String.ext_iff]
  · exact fun he => h (Lax3Proofs.RamDriverWrites.asgName_inj he)
  all_goals simp [ordName, cpsName, xmmName, asgName, pdsName, balAltName,
    String.ext_iff]

theorem streamDepthSwap_pdsName_of_ne {j d : ℕ} (h : d ≠ j) :
    streamDepthSwap j (pdsName d) = pdsName d := by
  apply streamDepthSwap_of_ne
  · simp [pdsName, balAltName, String.ext_iff]
  · simp [pdsName, balAltName, ordName, String.ext_iff]
  · simp [pdsName, balAltName, String.ext_iff]
  · simp [pdsName, balAltName, cpsName, String.ext_iff]
  · simp [pdsName, balAltName, String.ext_iff]
  · simp [pdsName, balAltName, xmmName, String.ext_iff]
  · simp [pdsName, balAltName, String.ext_iff]
  · simp [pdsName, balAltName, asgName, String.ext_iff]
  · simp [pdsName, balAltName, String.ext_iff]
  · exact fun he => h (Lax3Proofs.RamDriverWrites.pdsName_inj he)

/-- The five disjoint exchanges are an involution, as required by
`renCom_spec`. -/
theorem streamDepthSwap_invol (j : ℕ) :
    ∀ a, streamDepthSwap j (streamDepthSwap j a) = a := by
  intro a
  by_cases ho : a = "ord"
  · subst a; simp
  by_cases hoj : a = ordName j
  · subst a; simp
  by_cases hl : a = "alv"
  · subst a; simp
  by_cases hlj : a = cpsName j
  · subst a; simp
  by_cases hx : a = "xmem"
  · subst a; simp
  by_cases hxj : a = xmmName j
  · subst a; simp
  by_cases ha : a = "asg"
  · subst a; simp
  by_cases haj : a = asgName j
  · subst a; simp
  by_cases hd : a = "dist"
  · subst a; simp
  by_cases hdj : a = pdsName j
  · subst a; simp
  rw [streamDepthSwap_of_ne j a ho hoj hl hlj hx hxj ha haj hd hdj]
  exact streamDepthSwap_of_ne j a ho hoj hl hlj hx hxj ha haj hd hdj

/-- Run any scratch-level streamed command directly on depth-owned storage. -/
def streamAtDepthCom (j : ℕ) (cmd : Com) : Com :=
  renCom (streamDepthSwap j) cmd

/-! ## Scalar state across the recursive call -/

/-- Save the streamed centre-loop scalars in slots owned by this depth.
`xp` and `tail` agree at the seam, so one slot suffices for both. -/
def streamSaveCom (j : ℕ) : Com :=
  .seq (.assign (cnumName j) (.var "qn"))
    (.seq (.assign (curName j) (.var "c"))
      (.seq (.assign (xpName j) (.var "tail"))
        (.assign (cixName j) (.var "rsbits"))))

/-- Restore the streamed centre-loop scalars after the child has reused the
fixed scalar scratch names. -/
def streamRestoreCom (j : ℕ) : Com :=
  .seq (.assign "qn" (.var (cnumName j)))
    (.seq (.assign "c" (.var (curName j)))
      (.seq (.assign "xp" (.var (xpName j)))
        (.seq (.assign "tail" (.var (xpName j)))
          (.assign "rsbits" (.var (cixName j))))))

def StreamScalarsSaved (j q c tail bits : ℕ) (σ : Env) : Prop :=
  σ.vars (cnumName j) = q ∧ σ.vars (curName j) = c ∧
    σ.vars (xpName j) = tail ∧ σ.vars (cixName j) = bits

/-- The concrete endpoint of `streamSaveCom`.  Naming it lets the recursive
adapter transport the child's semantic precondition across the four scalar
writes without weakening that precondition to an opaque frame relation. -/
def streamSavedEnv (j q c tail bits : ℕ) (σ : Env) : Env :=
  (((σ.setVar (cnumName j) q).setVar (curName j) c).setVar
    (xpName j) tail).setVar (cixName j) bits

/-- Exact execution of the four scalar saves. -/
theorem streamSaveCom_run {B j q c tail bits : ℕ} {σ : Env}
    (hvals : σ.vars "qn" = q ∧ σ.vars "c" = c ∧
      σ.vars "tail" = tail ∧ σ.vars "rsbits" = bits)
    (hqB : q < B) (hcB : c < B) (htailB : tail < B) (hbitsB : bits < B) :
    Run B (streamSaveCom j) σ (streamSavedEnv j q c tail bits σ) 8 := by
  let σ₁ := σ.setVar (cnumName j) q
  let σ₂ := σ₁.setVar (curName j) c
  let σ₃ := σ₂.setVar (xpName j) tail
  have e₁ : (Expr.var "qn").evalB B σ = some q := by
    rw [← hvals.1]
    exact evalB_var (by rw [hvals.1]; exact hqB)
  have e₂ : (Expr.var "c").evalB B σ₁ = some c := by
    have hne : ("c" : String) ≠ cnumName j := by
      simp [cnumName, String.ext_iff]
    have : σ₁.vars "c" = c := by simp [σ₁, hne, hvals.2.1]
    simpa only [this] using (evalB_var (B := B) (σ := σ₁) (x := "c") (this ▸ hcB))
  have e₃ : (Expr.var "tail").evalB B σ₂ = some tail := by
    have hne₁ : ("tail" : String) ≠ curName j := by
      simp [curName, String.ext_iff]
    have hne₂ : ("tail" : String) ≠ cnumName j := by
      simp [cnumName, String.ext_iff]
    have : σ₂.vars "tail" = tail := by
      simp [σ₂, σ₁, hne₁, hne₂, hvals.2.2.1]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₂) (x := "tail") (this ▸ htailB))
  have e₄ : (Expr.var "rsbits").evalB B σ₃ = some bits := by
    have hne₁ : ("rsbits" : String) ≠ xpName j := by
      simp [xpName, String.ext_iff]
    have hne₂ : ("rsbits" : String) ≠ curName j := by
      simp [curName, String.ext_iff]
    have hne₃ : ("rsbits" : String) ≠ cnumName j := by
      simp [cnumName, String.ext_iff]
    have : σ₃.vars "rsbits" = bits := by
      simp [σ₃, σ₂, σ₁, hne₁, hne₂, hne₃, hvals.2.2.2]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₃) (x := "rsbits") (this ▸ hbitsB))
  exact (Run.assign e₁).seq ((Run.assign e₂).seq
    ((Run.assign e₃).seq (Run.assign e₄)))

/-- Four assignments save the five logical loop values at cost eight. -/
theorem streamSaveCom_spec {B j q c tail bits : ℕ}
    (hqB : q < B) (hcB : c < B) (htailB : tail < B) (hbitsB : bits < B) :
    Spec B
      (fun σ => σ.vars "qn" = q ∧ σ.vars "c" = c ∧
        σ.vars "tail" = tail ∧ σ.vars "rsbits" = bits)
      (streamSaveCom j)
      (fun σ σ' => StreamScalarsSaved j q c tail bits σ' ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out)
      8 := by
  intro σ hσ
  let σ₁ := σ.setVar (cnumName j) q
  let σ₂ := σ₁.setVar (curName j) c
  let σ₃ := σ₂.setVar (xpName j) tail
  let σ₄ := σ₃.setVar (cixName j) bits
  have e₁ : (Expr.var "qn").evalB B σ = some q := by
    rw [← hσ.1]
    exact evalB_var (by rw [hσ.1]; exact hqB)
  have e₂ : (Expr.var "c").evalB B σ₁ = some c := by
    have hne : ("c" : String) ≠ cnumName j := by
      simp [cnumName, String.ext_iff]
    have : σ₁.vars "c" = c := by simp [σ₁, hne, hσ.2.1]
    simpa only [this] using (evalB_var (B := B) (σ := σ₁) (x := "c") (this ▸ hcB))
  have e₃ : (Expr.var "tail").evalB B σ₂ = some tail := by
    have hne₁ : ("tail" : String) ≠ curName j := by
      simp [curName, String.ext_iff]
    have hne₂ : ("tail" : String) ≠ cnumName j := by
      simp [cnumName, String.ext_iff]
    have : σ₂.vars "tail" = tail := by
      simp [σ₂, σ₁, hne₁, hne₂, hσ.2.2.1]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₂) (x := "tail") (this ▸ htailB))
  have e₄ : (Expr.var "rsbits").evalB B σ₃ = some bits := by
    have hne₁ : ("rsbits" : String) ≠ xpName j := by
      simp [xpName, String.ext_iff]
    have hne₂ : ("rsbits" : String) ≠ curName j := by
      simp [curName, String.ext_iff]
    have hne₃ : ("rsbits" : String) ≠ cnumName j := by
      simp [cnumName, String.ext_iff]
    have : σ₃.vars "rsbits" = bits := by
      simp [σ₃, σ₂, σ₁, hne₁, hne₂, hne₃, hσ.2.2.2]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₃) (x := "rsbits") (this ▸ hbitsB))
  refine ⟨σ₄, ?_, ?_⟩
  · exact (Run.assign e₁).seq ((Run.assign e₂).seq
      ((Run.assign e₃).seq (Run.assign e₄)))
  · refine ⟨?_, ?_, ?_⟩
    · simp [StreamScalarsSaved, σ₄, σ₃, σ₂, σ₁, cnumName,
        curName, xpName, cixName, String.ext_iff]
    · simp [σ₄, σ₃, σ₂, σ₁]
    · simp [σ₄, σ₃, σ₂, σ₁]

/-- Five assignments restore the fixed streamed scalar interface at cost ten.
The save slots themselves and every array remain unchanged. -/
theorem streamRestoreCom_spec {B j q c tail bits : ℕ}
    (hqB : q < B) (hcB : c < B) (htailB : tail < B) (hbitsB : bits < B) :
    Spec B
      (fun σ => StreamScalarsSaved j q c tail bits σ)
      (streamRestoreCom j)
      (fun σ σ' => σ'.vars "qn" = q ∧ σ'.vars "c" = c ∧
        σ'.vars "xp" = tail ∧ σ'.vars "tail" = tail ∧
        σ'.vars "rsbits" = bits ∧ StreamScalarsSaved j q c tail bits σ' ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out)
      10 := by
  intro σ hσ
  rcases hσ with ⟨hcq, hcu, hxq, hci⟩
  let σ₁ := σ.setVar "qn" q
  let σ₂ := σ₁.setVar "c" c
  let σ₃ := σ₂.setVar "xp" tail
  let σ₄ := σ₃.setVar "tail" tail
  let σ₅ := σ₄.setVar "rsbits" bits
  have e₁ : (Expr.var (cnumName j)).evalB B σ = some q := by
    rw [← hcq]
    exact evalB_var (by rw [hcq]; exact hqB)
  have e₂ : (Expr.var (curName j)).evalB B σ₁ = some c := by
    have hne : curName j ≠ "qn" := by simp [curName, String.ext_iff]
    have : σ₁.vars (curName j) = c := by simp [σ₁, hne, hcu]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₁) (x := curName j) (this ▸ hcB))
  have e₃ : (Expr.var (xpName j)).evalB B σ₂ = some tail := by
    have hne₁ : xpName j ≠ "c" := by simp [xpName, String.ext_iff]
    have hne₂ : xpName j ≠ "qn" := by simp [xpName, String.ext_iff]
    have : σ₂.vars (xpName j) = tail := by simp [σ₂, σ₁, hne₁, hne₂, hxq]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₂) (x := xpName j) (this ▸ htailB))
  have e₄ : (Expr.var (xpName j)).evalB B σ₃ = some tail := by
    have hne₁ : xpName j ≠ "xp" := by simp [xpName, String.ext_iff]
    have hne₂ : xpName j ≠ "c" := by simp [xpName, String.ext_iff]
    have hne₃ : xpName j ≠ "qn" := by simp [xpName, String.ext_iff]
    have : σ₃.vars (xpName j) = tail := by
      simp [σ₃, σ₂, σ₁, hne₁, hne₂, hne₃, hxq]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₃) (x := xpName j) (this ▸ htailB))
  have e₅ : (Expr.var (cixName j)).evalB B σ₄ = some bits := by
    have hne₁ : cixName j ≠ "tail" := by simp [cixName, String.ext_iff]
    have hne₂ : cixName j ≠ "xp" := by simp [cixName, String.ext_iff]
    have hne₃ : cixName j ≠ "c" := by simp [cixName, String.ext_iff]
    have hne₄ : cixName j ≠ "qn" := by simp [cixName, String.ext_iff]
    have : σ₄.vars (cixName j) = bits := by
      simp [σ₄, σ₃, σ₂, σ₁, hne₁, hne₂, hne₃, hne₄, hci]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₄) (x := cixName j) (this ▸ hbitsB))
  have hrun : Run B (streamRestoreCom j) σ σ₅ 10 :=
    (Run.assign e₁).seq ((Run.assign e₂).seq
      ((Run.assign e₃).seq ((Run.assign e₄).seq (Run.assign e₅))))
  have hsaved : StreamScalarsSaved j q c tail bits σ₅ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrun.frame_var _ (by
        simp [streamRestoreCom, Com.wvars, cnumName, String.ext_iff])]
      exact hcq
    · rw [hrun.frame_var _ (by
        simp [streamRestoreCom, Com.wvars, curName, String.ext_iff])]
      exact hcu
    · rw [hrun.frame_var _ (by
        simp [streamRestoreCom, Com.wvars, xpName, String.ext_iff])]
      exact hxq
    · rw [hrun.frame_var _ (by
        simp [streamRestoreCom, Com.wvars, cixName, String.ext_iff])]
      exact hci
  refine ⟨σ₅, hrun, ?_⟩
  refine ⟨by simp [σ₅, σ₄, σ₃, σ₂, σ₁],
    by simp [σ₅, σ₄, σ₃, σ₂], by simp [σ₅, σ₄, σ₃],
    by simp [σ₅, σ₄], by simp [σ₅], hsaved, ?_, ?_⟩
  · simp [σ₅, σ₄, σ₃, σ₂, σ₁]
  · simp [σ₅, σ₄, σ₃, σ₂, σ₁]

/-- The concrete endpoint of the scalar restore. -/
def streamRestoredEnv (q c tail bits : ℕ) (σ : Env) : Env :=
  (((((σ.setVar "qn" q).setVar "c" c).setVar "xp" tail).setVar
    "tail" tail).setVar "rsbits" bits)

/-- Exact execution of the five scalar restores. -/
theorem streamRestoreCom_run {B j q c tail bits : ℕ} {σ : Env}
    (hsaved : StreamScalarsSaved j q c tail bits σ)
    (hqB : q < B) (hcB : c < B) (htailB : tail < B) (hbitsB : bits < B) :
    Run B (streamRestoreCom j) σ (streamRestoredEnv q c tail bits σ) 10 := by
  rcases hsaved with ⟨hcq, hcu, hxq, hci⟩
  let σ₁ := σ.setVar "qn" q
  let σ₂ := σ₁.setVar "c" c
  let σ₃ := σ₂.setVar "xp" tail
  let σ₄ := σ₃.setVar "tail" tail
  have e₁ : (Expr.var (cnumName j)).evalB B σ = some q := by
    rw [← hcq]
    exact evalB_var (by rw [hcq]; exact hqB)
  have e₂ : (Expr.var (curName j)).evalB B σ₁ = some c := by
    have hne : curName j ≠ "qn" := by simp [curName, String.ext_iff]
    have : σ₁.vars (curName j) = c := by simp [σ₁, hne, hcu]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₁) (x := curName j) (this ▸ hcB))
  have e₃ : (Expr.var (xpName j)).evalB B σ₂ = some tail := by
    have hne₁ : xpName j ≠ "c" := by simp [xpName, String.ext_iff]
    have hne₂ : xpName j ≠ "qn" := by simp [xpName, String.ext_iff]
    have : σ₂.vars (xpName j) = tail := by simp [σ₂, σ₁, hne₁, hne₂, hxq]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₂) (x := xpName j) (this ▸ htailB))
  have e₄ : (Expr.var (xpName j)).evalB B σ₃ = some tail := by
    have hne₁ : xpName j ≠ "xp" := by simp [xpName, String.ext_iff]
    have hne₂ : xpName j ≠ "c" := by simp [xpName, String.ext_iff]
    have hne₃ : xpName j ≠ "qn" := by simp [xpName, String.ext_iff]
    have : σ₃.vars (xpName j) = tail := by
      simp [σ₃, σ₂, σ₁, hne₁, hne₂, hne₃, hxq]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₃) (x := xpName j) (this ▸ htailB))
  have e₅ : (Expr.var (cixName j)).evalB B σ₄ = some bits := by
    have hne₁ : cixName j ≠ "tail" := by simp [cixName, String.ext_iff]
    have hne₂ : cixName j ≠ "xp" := by simp [cixName, String.ext_iff]
    have hne₃ : cixName j ≠ "c" := by simp [cixName, String.ext_iff]
    have hne₄ : cixName j ≠ "qn" := by simp [cixName, String.ext_iff]
    have : σ₄.vars (cixName j) = bits := by
      simp [σ₄, σ₃, σ₂, σ₁, hne₁, hne₂, hne₃, hne₄, hci]
    simpa only [this] using
      (evalB_var (B := B) (σ := σ₄) (x := cixName j) (this ▸ hbitsB))
  exact (Run.assign e₁).seq ((Run.assign e₂).seq
    ((Run.assign e₃).seq ((Run.assign e₄).seq (Run.assign e₅))))

/-! ## Concrete recursive frames -/

variable {q_top cap mb ell R j : ℕ} {phi : Lax3.FirstOrder.FO 0}

noncomputable abbrev streamChildDriver : Com :=
  Lax3Proofs.RamDriverMember.driverAtA q_top cap mb ell phi
    (fun d => Lax3Proofs.Refine.OrderActiveDriver.activeOrderPhase d R)
    (fun d => Lax3Proofs.Refine.CoverActiveDriver.activeCoverPhase d cap) (j + 1)

theorem ordName_notMem_child : ordName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).warrs :=
  Lax3Proofs.Refine.ActiveLevel.belowArr_notMem_warrs_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cpsName_notMem_child : cpsName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).warrs :=
  Lax3Proofs.Refine.ActiveLevel.belowArr_notMem_warrs_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem xmmName_notMem_child : xmmName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).warrs :=
  Lax3Proofs.Refine.ActiveLevel.belowArr_notMem_warrs_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem asgName_notMem_child : asgName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).warrs :=
  Lax3Proofs.Refine.ActiveLevel.belowArr_notMem_warrs_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem pdsName_notMem_child : pdsName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).warrs :=
  Lax3Proofs.Refine.ActiveLevel.belowArr_notMem_warrs_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

/-- All five physical arrays retained by a streamed parent survive its
concrete child invocation. -/
theorem streamDepthArrays_notMem_child (a : String)
    (ha : a ∈ [ordName j, cpsName j, xmmName j, asgName j, pdsName j]) :
    a ∉ (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).warrs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  exacts [ordName_notMem_child, cpsName_notMem_child, xmmName_notMem_child,
    asgName_notMem_child, pdsName_notMem_child]

theorem curName_notMem_child : curName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).wvars :=
  Lax3Proofs.Refine.ActiveLevel.belowVar_notMem_wvars_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cnumName_notMem_child : cnumName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).wvars :=
  Lax3Proofs.Refine.ActiveLevel.belowVar_notMem_wvars_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem xpName_notMem_child : xpName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).wvars :=
  Lax3Proofs.Refine.ActiveLevel.belowVar_notMem_wvars_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

theorem cixName_notMem_child : cixName j ∉
    (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).wvars :=
  Lax3Proofs.Refine.ActiveLevel.belowVar_notMem_wvars_activeDriverAt
    ⟨j, Nat.lt_succ_self j, by tauto⟩

/-- The four scalar save slots used around recursion are likewise framed. -/
theorem streamDepthVars_notMem_child (y : String)
    (hy : y ∈ [curName j, cnumName j, xpName j, cixName j]) :
    y ∉ (streamChildDriver (q_top := q_top) (cap := cap) (mb := mb) (ell := ell)
      (R := R) (j := j) (phi := phi)).wvars := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  exacts [curName_notMem_child, cnumName_notMem_child,
    xpName_notMem_child, cixName_notMem_child]

#print axioms streamDepthSwap_invol
#print axioms streamDepthArrays_notMem_child
#print axioms streamDepthVars_notMem_child

end Lax3Proofs.Refine.CoverActiveStreamDepth
