import Lax3Proofs.Refine.OrderVirtualSetRow
import Lax3Proofs.Refine.ScatterBlockProg

/-!
# Renaming private arrays of a virtual row provider

Recursive implicit rows invoke an earlier provider while retaining their own
carrier-sized buffers.  The scalar calling convention (`w`, `vtail`, `c`)
is shared, but every private array must be fresh at each fixed augmentation
depth.  `ScatterBlockProg.renCom` already transports an IMP+ command through
an involutive array renaming.  This file lifts that transport to the exact
`ProvidesSetRows` interface.

The seven elimination arrays are fixed.  A provider's destination and all of
its private scratch arrays may be exchanged with fresh names; the charge and
the represented finite set do not change.
-/

namespace Lax3Proofs.Refine.OrderVirtualRename

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.ScatterBlock
  (renCom renEnv renEnv_arrs renEnv_vars renEnv_involutive renCom_run)

/-- An array renaming that leaves the generic elimination engine resident in
place.  `vrow` is intentionally absent: it is an API destination rather than
a field of `EngineArrays`, and a nested set provider is allowed to move it to
a private buffer. -/
structure FixesEngine (f : String → String) : Prop where
  elm : f "elm" = "elm"
  deg : f "deg" = "deg"
  rank : f "rnk" = "rnk"
  idg : f "idg" = "idg"
  head : f "bh" = "bh"
  val : f "bv" = "bv"
  next : f "bn" = "bn"

/-- Exchange two array names and leave every other name fixed.  Larger
private-workspace renamings are built from disjoint exchanges. -/
def arraySwap (a b : String) : String → String := fun z =>
  if z = a then b else if z = b then a else z

theorem arraySwap_invol (a b z : String) :
    arraySwap a b (arraySwap a b z) = z := by
  by_cases hab : a = b
  · subst b
    by_cases hza : z = a <;> simp [arraySwap, hza]
  by_cases hza : z = a
  · subst z
    simp [arraySwap, hab]
  by_cases hzb : z = b
  · subst z
    simp [arraySwap, hab, Ne.symm hab]
  simp [arraySwap, hza, hzb]

theorem arraySwap_of_ne {a b z : String} (hza : z ≠ a) (hzb : z ≠ b) :
    arraySwap a b z = z := by
  simp [arraySwap, hza, hzb]

/-- A single fresh-name exchange fixes the engine whenever neither endpoint
is one of its seven resident arrays. -/
theorem arraySwap_fixesEngine {a b : String}
    (ha : a ∉ ["elm", "deg", "rnk", "idg", "bh", "bv", "bn"])
    (hb : b ∉ ["elm", "deg", "rnk", "idg", "bh", "bv", "bn"]) :
    FixesEngine (arraySwap a b) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
  rcases ha with ⟨hae, had, har, hai, hah, hav, han⟩
  rcases hb with ⟨hbe, hbd, hbr, hbi, hbh, hbv, hbn⟩
  exact ⟨arraySwap_of_ne (Ne.symm hae) (Ne.symm hbe),
    arraySwap_of_ne (Ne.symm had) (Ne.symm hbd),
    arraySwap_of_ne (Ne.symm har) (Ne.symm hbr),
    arraySwap_of_ne (Ne.symm hai) (Ne.symm hbi),
    arraySwap_of_ne (Ne.symm hah) (Ne.symm hbh),
    arraySwap_of_ne (Ne.symm hav) (Ne.symm hbv),
    arraySwap_of_ne (Ne.symm han) (Ne.symm hbn)⟩

namespace EngineArrays

/-- Pulling an environment through an engine-fixing renaming preserves every
generic elimination array. -/
theorem renEnv {f : String → String} (hf : FixesEngine f)
    {n W : ℕ} {E D R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (h : EngineArrays n W E D R ID BH BV BN sigma) :
    EngineArrays n W E D R ID BH BV BN (renEnv f sigma) := by
  exact ⟨by simpa using h.n_eq,
    by simpa [hf.elm] using h.elm_eq,
    by simpa [hf.deg] using h.deg_eq,
    by simpa [hf.rank] using h.rank_eq,
    by simpa [hf.idg] using h.idg_eq,
    by simpa [hf.head] using h.head_eq,
    by simpa [hf.val] using h.val_eq,
    by simpa [hf.next] using h.next_eq⟩

end EngineArrays

namespace ProviderStable

/-- Array renaming does not touch scalars, hence it transports the provider
calling convention definitionally. -/
theorem renEnv {f : String → String} {sigma tau : Env}
    (h : ProviderStable sigma tau) :
    ProviderStable (renEnv f sigma) (renEnv f tau) := by
  exact ⟨by simpa using h.n_eq, by simpa using h.w_eq,
    by simpa using h.i_eq, by simpa using h.sp_eq,
    by simpa using h.ls_eq, by simpa using h.cnt_eq,
    by simpa using h.mind_eq, by simpa using h.kmax_eq⟩

end ProviderStable

/-- Rename a verified exact-set provider.  The persistent predicate is pulled
back through the same environment renaming, the destination moves to `f dst`,
and everything else in the public contract is unchanged. -/
theorem providesSetRows_ren {B n W : ℕ} {S : Fin n → Finset (Fin n)}
    {P : Env → Prop} {dst : String} {provide : Com} {kappa : ℕ → ℕ}
    {f : String → String}
    (hinvol : ∀ z, f (f z) = z) (hfix : FixesEngine f)
    (hp : ProvidesSetRows B n W S P dst provide kappa) :
    ProvidesSetRows B n W S (fun sigma => P (renEnv f sigma)) (f dst)
      (renCom f provide) kappa := by
  intro w E D R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hP, heng, hw⟩ := hpre
  have hpre' : P (renEnv f sigma) ∧
      EngineArrays n W E D R ID BH BV BN (renEnv f sigma) ∧
      (renEnv f sigma).vars "w" = (w : ℕ) :=
    ⟨hP, EngineArrays.renEnv hfix heng, by simpa using hw⟩
  obtain ⟨tau, hrun, hP', heng', hstable, tail, A, hrow, htail, hA⟩ :=
    (hp w E D R ID BH BV BN).run hpre'
  let tau' := renEnv f tau
  have hrun' : Run B (renCom f provide) sigma tau' (kappa (w : ℕ)) := by
    have hr := renCom_run (f := f) hinvol hrun
    simpa only [tau', renEnv_involutive hinvol] using hr
  have hP'' : P (renEnv f tau') := by
    simpa only [tau', renEnv_involutive hinvol] using hP'
  have heng'' : EngineArrays n W E D R ID BH BV BN tau' :=
    EngineArrays.renEnv hfix heng'
  have hstable' : ProviderStable sigma tau' := by
    have hs := ProviderStable.renEnv (f := f) hstable
    simpa only [tau', renEnv_involutive hinvol] using hs
  have htail' : tau'.vars "vtail" = tail := by
    simpa only [tau', renEnv_vars] using htail
  have hA' : tau'.arrs (f dst) = arrOf n A := by
    simpa only [tau', renEnv_arrs, hinvol dst] using hA
  exact ⟨tau', kappa (w : ℕ), hrun', le_rfl,
    hP'', heng'', hstable', tail, A, hrow, htail', hA'⟩

/-! ## Axiom audit -/

#print axioms EngineArrays.renEnv
#print axioms ProviderStable.renEnv
#print axioms arraySwap_invol
#print axioms arraySwap_fixesEngine
#print axioms providesSetRows_ren

end Lax3Proofs.Refine.OrderVirtualRename
