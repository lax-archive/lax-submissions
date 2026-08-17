import Lax3Proofs.Refine.OrderActiveCompact
import Lax3Proofs.Refine.OrderActiveWidth

/-!
# Compacting an active arena into the order phase's resident workspace

The active ordering phase may not overwrite the level's `off`/`tgt`
arrays, and `OrderMem` deliberately does not allocate the compact helper
names `kix`, `kof`, and `ktg`.  The required storage already exists as
`ffl`, `gof`, and `gtg`.  This file redirects the compacting pass into
that resident workspace, while also reading the level's depth-named mask
in place.  It is a pure array-name transport, so the landed walk and its
exact live-arena charge are unchanged.
-/

namespace Lax3Proofs.Refine.OrderActiveWork

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (Orientation)
open Lax3Proofs.RamDriver (alvName)
open Lax3Proofs.RamDriverCluster (markSet)
open Lax3Proofs.RamElim (CsrSimple InCsr)
open Lax3Proofs.RamAugment (fratSlots)
open Lax3Proofs.Refine.ScatterBlock (MemList renCom renEnv renEnv_arrs renEnv_vars
  renEnv_involutive renCom_run)
open Lax3Proofs.Refine.ElimCompact (compactPass memRowSum cutArrs padArrs tailOf
  cutArrs_arrs cutArrs_vars padArrs_arrs padArrs_vars run_of_run_cutArrs run_length
  getD_padArrs take_arrOf)
open Lax3Proofs.Refine.ElimCompactCsr (cOff cOff_mono cOff_le_memRowSum memRowSum_le
  CDone compactPass_run)
open Lax3Proofs.Refine.AugCompact
open Lax3Proofs.Refine.OrderActiveWidth (augCompactCom_specLive)
open Lax3Proofs.Refine.OrderActiveTail
open Lax3Proofs.Refine.SymCompact

variable {n nt mm B : ℕ} {G : SimpleGraph (Fin n)}

/-- The four disjoint swaps used by the resident compacting pass:
the generic mask and compact output names are exchanged with the arrays
already owned by the current level. -/
def compactWorkSwap (j : ℕ) : String → String := fun z =>
  if z = "alv" then alvName j
  else if z = alvName j then "alv"
  else if z = "kix" then "ffl"
  else if z = "ffl" then "kix"
  else if z = "kof" then "gof"
  else if z = "gof" then "kof"
  else if z = "ktg" then "gtg"
  else if z = "gtg" then "ktg"
  else z

theorem compactWorkSwap_invol (j : ℕ) (z : String) :
    compactWorkSwap j (compactWorkSwap j z) = z := by
  by_cases h0 : z = "alv"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h1 : z = alvName j
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h2 : z = "kix"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h3 : z = "ffl"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h4 : z = "kof"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h5 : z = "gof"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h6 : z = "ktg"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  by_cases h7 : z = "gtg"
  · subst z
    simp [compactWorkSwap, alvName, String.ext_iff]
  simp [compactWorkSwap, h0, h1, h2, h3, h4, h5, h6, h7]

@[simp] theorem compactWorkSwap_alv (j : ℕ) : compactWorkSwap j "alv" = alvName j := by
  simp [compactWorkSwap]

@[simp] theorem compactWorkSwap_kix (j : ℕ) : compactWorkSwap j "kix" = "ffl" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_ffl (j : ℕ) : compactWorkSwap j "ffl" = "kix" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_kof (j : ℕ) : compactWorkSwap j "kof" = "gof" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_gof (j : ℕ) : compactWorkSwap j "gof" = "kof" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_ktg (j : ℕ) : compactWorkSwap j "ktg" = "gtg" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_gtg (j : ℕ) : compactWorkSwap j "gtg" = "ktg" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_mem (j : ℕ) : compactWorkSwap j "mem" = "mem" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_off (j : ℕ) : compactWorkSwap j "off" = "off" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

@[simp] theorem compactWorkSwap_tgt (j : ℕ) : compactWorkSwap j "tgt" = "tgt" := by
  simp [compactWorkSwap, alvName, String.ext_iff]

/-- Compact the current active arena directly into `gof`/`gtg`, using
`ffl` as the transient inverse-index array. -/
def compactPassWorkAt (j : ℕ) : Com := renCom (compactWorkSwap j) compactPass

private theorem swap_ne_output (j : ℕ) {a q q' : String} (ha : a ≠ q')
    (hq : compactWorkSwap j q = q') : compactWorkSwap j a ≠ q := by
  intro h
  apply ha
  have hh := congrArg (compactWorkSwap j) h
  simpa only [compactWorkSwap_invol, hq] using hh

/-- The compact CSR is installed in the resident order workspace.  The
level graph, target allocation, member list, and depth mask are all framed;
the cost still depends only on the active rows traversed. -/
theorem compactPassWorkAt_run (j : ℕ) {O T M Mem : ℕ → ℕ}
    (hcsr : CsrSimple G nt O T) (hml : MemList n mm Mem (markSet n M))
    (hB : mm + nt + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B) {σ : Env}
    (hmm : σ.vars "mm" = mm) (hmem : σ.arrs "mem" = arrOf n Mem)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs (alvName j) = arrOf n M) (hffl : ∃ g, σ.arrs "ffl" = arrOf n g)
    (hgof : ∃ g, σ.arrs "gof" = arrOf (n + 1) g)
    (hgtg : ∃ g, σ.arrs "gtg" = arrOf nt g) :
    ∃ (σ' : Env) (Kix KOf KT : ℕ → ℕ),
      Run B (compactPassWorkAt j) σ σ' (40 * mm + 24 * memRowSum mm O Mem + 17) ∧
      (∀ k, k < mm → Kix (Mem k) = k) ∧
      σ'.vars "mm" = mm ∧
      σ'.vars "ks" = cOff O T M Mem Kix mm ∧
      σ'.arrs "gof" = arrOf (n + 1) KOf ∧
      (∀ i ≤ mm, KOf i = cOff O T M Mem Kix i) ∧
      σ'.arrs "gtg" = arrOf nt KT ∧
      CDone O T M Mem Kix KT mm ∧
      (∀ a, a ≠ "ffl" → a ≠ "gof" → a ≠ "gtg" → σ'.arrs a = σ.arrs a) := by
  let f := compactWorkSwap j
  obtain ⟨τ, Kix, KOf, KT, hrun, hKix, hmm', hks, hkof', hKOf, hktg', hdone, hframe⟩ :=
    compactPass_run (B := B) hcsr hml hB hnB hMB
      (hmm := by simpa only [renEnv_vars] using hmm)
      (hmem := by simpa only [renEnv_arrs, f, compactWorkSwap_mem] using hmem)
      (hoff := by simpa only [renEnv_arrs, f, compactWorkSwap_off] using hoff)
      (htgt := by simpa only [renEnv_arrs, f, compactWorkSwap_tgt] using htgt)
      (halv := by simpa only [renEnv_arrs, f, compactWorkSwap_alv] using halv)
      (hkix := by simpa only [renEnv_arrs, f, compactWorkSwap_kix] using hffl)
      (hkof := by simpa only [renEnv_arrs, f, compactWorkSwap_kof] using hgof)
      (hktg := by simpa only [renEnv_arrs, f, compactWorkSwap_ktg] using hgtg)
      (σ := renEnv f σ)
  let σ' := renEnv f τ
  have hrun' : Run B (compactPassWorkAt j) σ σ'
      (40 * mm + 24 * memRowSum mm O Mem + 17) := by
    have h := renCom_run (f := f) (compactWorkSwap_invol j) hrun
    change Run B (renCom f compactPass) σ (renEnv f τ)
      (40 * mm + 24 * memRowSum mm O Mem + 17)
    rw [← renEnv_involutive (compactWorkSwap_invol j) σ]
    exact h
  refine ⟨σ', Kix, KOf, KT, hrun', hKix, hmm', hks, ?_, hKOf, ?_, hdone, ?_⟩
  · simpa only [σ', renEnv_arrs, f, compactWorkSwap_gof] using hkof'
  · simpa only [σ', renEnv_arrs, f, compactWorkSwap_gtg] using hktg'
  · intro a ha₁ ha₂ ha₃
    have h₁ : f a ≠ "kix" :=
      swap_ne_output j ha₁ (compactWorkSwap_kix j)
    have h₂ : f a ≠ "kof" :=
      swap_ne_output j ha₂ (compactWorkSwap_kof j)
    have h₃ : f a ≠ "ktg" :=
      swap_ne_output j ha₃ (compactWorkSwap_ktg j)
    change (renEnv f τ).arrs a = σ.arrs a
    rw [renEnv_arrs, hframe (f a) h₁ h₂ h₃, renEnv_arrs]
    exact congrArg σ.arrs (compactWorkSwap_invol j a)

/-! ### The widened level target array -/

/-- The compacting pass sees only the occupied target prefix.  Its other
arrays are cut at exactly their physical lengths, so padding the run puts
back only the untouched target tail. -/
def compactWorkLen (j n ns : ℕ) : String → ℕ := fun a =>
  if a = "off" ∨ a = "gof" then n + 1
  else if a = "tgt" ∨ a = "gtg" then ns
  else if a = "mem" ∨ a = "ffl" ∨ a = alvName j then n
  else 0

@[simp] theorem compactWorkLen_off (j n ns : ℕ) :
    compactWorkLen j n ns "off" = n + 1 := by simp [compactWorkLen]

@[simp] theorem compactWorkLen_gof (j n ns : ℕ) :
    compactWorkLen j n ns "gof" = n + 1 := by simp [compactWorkLen]

@[simp] theorem compactWorkLen_tgt (j n ns : ℕ) :
    compactWorkLen j n ns "tgt" = ns := by simp [compactWorkLen]

@[simp] theorem compactWorkLen_gtg (j n ns : ℕ) :
    compactWorkLen j n ns "gtg" = ns := by simp [compactWorkLen]

@[simp] theorem compactWorkLen_mem (j n ns : ℕ) :
    compactWorkLen j n ns "mem" = n := by
  simp [compactWorkLen]

@[simp] theorem compactWorkLen_ffl (j n ns : ℕ) :
    compactWorkLen j n ns "ffl" = n := by
  simp [compactWorkLen]

@[simp] theorem compactWorkLen_alvName (j n ns : ℕ) :
    compactWorkLen j n ns (alvName j) = n := by
  simp [compactWorkLen, alvName, String.ext_iff]

/-- The resident compaction at the level's widened target allocation.
Only the occupied prefix `[0,ns)` is read or written; the physical
`[ns,W)` tail of `gtg` is retained. -/
theorem compactPassWorkAtWide_run (j : ℕ) {ns W : ℕ} {O T M Mem : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hml : MemList n mm Mem (markSet n M))
    (hB : mm + ns + 1 < B) (hnB : n < B) (hMB : ∀ v < n, M v < B)
    (hnsW : ns ≤ W) { σ : Env}
    (hmm : σ.vars "mm" = mm) (hmem : σ.arrs "mem" = arrOf n Mem)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf W T)
    (halv : σ.arrs (alvName j) = arrOf n M) (hffl : ∃ g, σ.arrs "ffl" = arrOf n g)
    (hgof : ∃ g, σ.arrs "gof" = arrOf (n + 1) g)
    (hgtg : ∃ g, σ.arrs "gtg" = arrOf W g) :
    ∃ (σ' : Env) (Kix KOf KT : ℕ → ℕ),
      Run B (compactPassWorkAt j) σ σ' (40 * mm + 24 * memRowSum mm O Mem + 17) ∧
      (∀ k, k < mm → Kix (Mem k) = k) ∧
      σ'.vars "mm" = mm ∧
      σ'.vars "ks" = cOff O T M Mem Kix mm ∧
      σ'.arrs "gof" = arrOf (n + 1) KOf ∧
      (∀ i ≤ mm, KOf i = cOff O T M Mem Kix i) ∧
      σ'.arrs "gtg" = arrOf W KT ∧
      CDone O T M Mem Kix KT mm ∧
      (∀ a, a ≠ "ffl" → a ≠ "gof" → a ≠ "gtg" → σ'.arrs a = σ.arrs a) := by
  classical
  let len := compactWorkLen j n ns
  obtain ⟨τ, Kix, KOf, KT₀, hrun, hKix, hmm', hks, hgof', hKOf, hgtg',
      hdone, hframe⟩ :=
    compactPassWorkAt_run (G := G) (B := B) j hcsr hml hB hnB hMB
      (hmm := by simpa only [cutArrs_vars] using hmm)
      (hmem := by rw [cutArrs_arrs, show len "mem" = n by simp [len], hmem,
        take_arrOf le_rfl])
      (hoff := by rw [cutArrs_arrs, show len "off" = n + 1 by simp [len], hoff,
        take_arrOf le_rfl])
      (htgt := by rw [cutArrs_arrs, show len "tgt" = ns by simp [len], htgt,
        take_arrOf hnsW])
      (halv := by rw [cutArrs_arrs, show len (alvName j) = n by simp [len], halv,
        take_arrOf le_rfl])
      (hffl := by obtain ⟨g, hg⟩ := hffl
                  exact ⟨g, by rw [cutArrs_arrs, show len "ffl" = n by simp [len], hg,
                    take_arrOf le_rfl]⟩)
      (hgof := by obtain ⟨g, hg⟩ := hgof
                  exact ⟨g, by rw [cutArrs_arrs, show len "gof" = n + 1 by simp [len], hg,
                    take_arrOf le_rfl]⟩)
      (hgtg := by obtain ⟨g, hg⟩ := hgtg
                  exact ⟨g, by rw [cutArrs_arrs, show len "gtg" = ns by simp [len], hg,
                    take_arrOf hnsW]⟩)
      (σ := cutArrs σ len)
  let σ' := padArrs τ (tailOf σ len)
  have hrun' : Run B (compactPassWorkAt j) σ σ'
      (40 * mm + 24 * memRowSum mm O Mem + 17) := by
    exact run_of_run_cutArrs len hrun
  have hgofTail : (σ.arrs "gof").drop (len "gof") = [] := by
    obtain ⟨g, hg⟩ := hgof
    rw [show len "gof" = n + 1 by simp [len], hg]
    exact List.drop_eq_nil_of_le (by simp [arrOf])
  have hgofWide : σ'.arrs "gof" = arrOf (n + 1) KOf := by
    change (padArrs τ (tailOf σ len)).arrs "gof" = arrOf (n + 1) KOf
    rw [padArrs_arrs, tailOf, hgofTail, List.append_nil, hgof']
  have hgtgLen : (σ'.arrs "gtg").length = W := by
    rw [run_length hrun' "gtg"]
    obtain ⟨g, hg⟩ := hgtg
    rw [hg, length_arrOf]
  obtain ⟨KT, hKTarr⟩ := Lax3Proofs.RamDriver.exists_arrOf hgtgLen
  have hKT : ∀ z < ns, KT z = KT₀ z := by
    intro z hz
    have hp := getD_padArrs (τ := τ) (tl := tailOf σ len) (a := "gtg")
      (i := z) (by rw [hgtg', length_arrOf]; exact hz)
    have hp' : (σ'.arrs "gtg").getD z 0 = (τ.arrs "gtg").getD z 0 := by
      simpa only [σ'] using hp
    rw [hKTarr, getD_arrOf KT (lt_of_lt_of_le hz hnsW), hgtg',
      getD_arrOf KT₀ hz] at hp'
    exact hp'
  have hcsns : cOff O T M Mem Kix mm ≤ ns :=
    (cOff_le_memRowSum hcsr hml hKix).trans (memRowSum_le hcsr hml)
  have hdone' : CDone O T M Mem Kix KT mm := by
    intro z hz
    obtain ⟨hsound, hcomplete⟩ := hdone z hz
    refine ⟨?_, ?_⟩
    · intro p hp₁ hp₂
      rw [hKT p (lt_of_lt_of_le hp₂
        ((cOff_mono (O := O) (T := T) (M := M) (Mem := Mem) (Kix := Kix)
          (show z + 1 ≤ mm by omega)).trans hcsns))]
      exact hsound p hp₁ hp₂
    · intro v hv
      obtain ⟨p, hp₁, hp₂, hpv⟩ := hcomplete v hv
      refine ⟨p, hp₁, hp₂, ?_⟩
      rw [hKT p (lt_of_lt_of_le hp₂
        ((cOff_mono (O := O) (T := T) (M := M) (Mem := Mem) (Kix := Kix)
          (show z + 1 ≤ mm by omega)).trans hcsns))]
      exact hpv
  refine ⟨σ', Kix, KOf, KT, hrun', hKix, ?_, ?_, hgofWide, hKOf, hKTarr,
    hdone', ?_⟩
  · simpa only [σ', padArrs_vars] using hmm'
  · simpa only [σ', padArrs_vars] using hks
  · intro a ha₁ ha₂ ha₃
    change (padArrs τ (tailOf σ len)).arrs a = σ.arrs a
    rw [padArrs_arrs, hframe a ha₁ ha₂ ha₃, cutArrs_arrs, tailOf,
      List.take_append_drop]

/-! ## The compact engines in the resident graph workspace -/

/-- Exchange the generic engine graph names with the resident compact
CSR.  Every other array name is fixed. -/
def engineWorkSwap : String → String := fun z =>
  if z = "off" then "gof"
  else if z = "gof" then "off"
  else if z = "tgt" then "gtg"
  else if z = "gtg" then "tgt"
  else z

theorem engineWorkSwap_invol (z : String) : engineWorkSwap (engineWorkSwap z) = z := by
  by_cases h0 : z = "off"
  · subst z; simp [engineWorkSwap]
  by_cases h1 : z = "gof"
  · subst z; simp [engineWorkSwap]
  by_cases h2 : z = "tgt"
  · subst z; simp [engineWorkSwap]
  by_cases h3 : z = "gtg"
  · subst z; simp [engineWorkSwap]
  simp [engineWorkSwap, h0, h1, h2, h3]

@[simp] theorem engineWorkSwap_off : engineWorkSwap "off" = "gof" := by
  simp [engineWorkSwap]

@[simp] theorem engineWorkSwap_gof : engineWorkSwap "gof" = "off" := by
  simp [engineWorkSwap]

@[simp] theorem engineWorkSwap_tgt : engineWorkSwap "tgt" = "gtg" := by
  simp [engineWorkSwap]

@[simp] theorem engineWorkSwap_gtg : engineWorkSwap "gtg" = "tgt" := by
  simp [engineWorkSwap]

theorem engineWorkSwap_of_ne {a : String} (h0 : a ≠ "off") (h1 : a ≠ "gof")
    (h2 : a ≠ "tgt") (h3 : a ≠ "gtg") : engineWorkSwap a = a := by
  simp [engineWorkSwap, h0, h1, h2, h3]

@[simp] theorem engineWorkSwap_mem : engineWorkSwap "mem" = "mem" := by
  exact engineWorkSwap_of_ne (by decide) (by decide) (by decide) (by decide)

@[simp] theorem engineWorkSwap_alv : engineWorkSwap "alv" = "alv" := by
  exact engineWorkSwap_of_ne (by decide) (by decide) (by decide) (by decide)

@[simp] theorem engineWorkSwap_ork : engineWorkSwap "ork" = "ork" := by
  exact engineWorkSwap_of_ne (by decide) (by decide) (by decide) (by decide)

@[simp] theorem engineWorkSwap_noff : engineWorkSwap "noff" = "noff" := by
  exact engineWorkSwap_of_ne (by decide) (by decide) (by decide) (by decide)

@[simp] theorem engineWorkSwap_ntg : engineWorkSwap "ntg" = "ntg" := by
  exact engineWorkSwap_of_ne (by decide) (by decide) (by decide) (by decide)

theorem engineWorkSwap_activeZero {a : String} (ha : a ∈ activeZeroNames) :
    engineWorkSwap a = a := by
  simp only [activeZeroNames, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact engineWorkSwap_of_ne (by decide) (by decide) (by decide) (by decide)

/-- The compact augmentation entry, read with its graph in `gof`/`gtg`. -/
def AugWorkEntryC (n mm nt W kd : ℕ) (IO IT : ℕ → ℕ) (σ : Env) : Prop :=
  AugEntryC n mm nt W kd IO IT (renEnv engineWorkSwap σ)

/-- The compact symmetrization entry and answer in the resident workspace. -/
def SymWorkEntryC (n mm nt W kd : ℕ) (IO IT T₀ : ℕ → ℕ) (σ : Env) : Prop :=
  SymEntryC n mm nt W kd IO IT T₀ (renEnv engineWorkSwap σ)

def SymWorkPost (mm nt m : ℕ) (D : Orientation mm) (T₀ : ℕ → ℕ) (σ : Env) : Prop :=
  SymMemPost mm nt m D T₀ (renEnv engineWorkSwap σ)

def augCompactWorkCom : Com := renCom engineWorkSwap augCompactCom

def symCompactWorkCom : Com := renCom engineWorkSwap symCompactCom

/-- One live-width augmentation round in the resident compact graph.
The level's own `off`/`tgt` arrays are explicit frames of the result. -/
theorem augCompactWork_specLive {B n mm nt W w kd d db m : ℕ} {D : Orientation mm}
    {Mem IO IT : ℕ → ℕ} {X : Set (Fin n)} {σ : Env}
    (hml : MemList n mm Mem X) (hin : InCsr D m IO IT) (hd : D.InDegLE d)
    (hmkd : m ≤ kd) (hkdw : kd ≤ w) (hwW : w ≤ W) (hnt : fratSlots D ≤ nt)
    (hdb : 2 * (d * d) + d ≤ db) (hwidth : augWidthE mm kd db ≤ w)
    (hB : mm + w + 1 < B) (hnB : n < B)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ z < kd, IT z < B)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hent : AugWorkEntryC n mm nt W kd IO IT σ) :
    ∃ σ'', Run B augCompactWorkCom σ σ'' (augCompactCost mm kd w + 2) ∧
      AugMemPost mm W Mem D σ'' ∧
      (σ''.arrs "alv").drop mm = (σ.arrs "alv").drop mm ∧
      ActiveZeroTail mm σ σ'' ∧ σ''.vars "n" = n ∧
      σ''.arrs "off" = σ.arrs "off" ∧
      σ''.arrs "tgt" = σ.arrs "tgt" := by
  obtain ⟨τ, hrun, hpost, htail, hzeroTail, hn⟩ :=
    augCompactCom_specLive hml hin hd hmkd hkdw hwW hnt hdb hwidth hB hnB hIOB hITB
      (by simpa only [renEnv_arrs, engineWorkSwap_mem] using hmem) hent
  let σ'' := renEnv engineWorkSwap τ
  have hrun' : Run B augCompactWorkCom σ σ'' (augCompactCost mm kd w + 2) := by
    have h := renCom_run (f := engineWorkSwap) engineWorkSwap_invol hrun
    change Run B (renCom engineWorkSwap augCompactCom) σ (renEnv engineWorkSwap τ)
      (augCompactCost mm kd w + 2)
    rw [← renEnv_involutive engineWorkSwap_invol σ]
    exact h
  refine ⟨σ'', hrun', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [σ'', AugMemPost, renEnv_arrs, renEnv_vars, engineWorkSwap_ork,
      engineWorkSwap_noff, engineWorkSwap_ntg] using hpost
  · simpa only [σ'', renEnv_arrs, engineWorkSwap_alv] using htail
  · intro a ha
    simpa only [σ'', renEnv_arrs, engineWorkSwap_activeZero ha] using hzeroTail a ha
  · simpa only [σ'', renEnv_vars] using hn
  · exact hrun'.frame_arr "off" (by decide)
  · exact hrun'.frame_arr "tgt" (by decide)

/-- Symmetrize the final compact orientation into `gof`/`gtg`, restore
the carrier, and frame the level graph. -/
theorem symCompactWork_spec {B n mm nt W kd m : ℕ} {D : Orientation mm}
    {IO IT T₀ : ℕ → ℕ} {σ : Env} (h1 : SymPreps B n mm nt W kd)
    (hin : InCsr D m IO IT) (hmkd : m ≤ kd) (hkdW : kd ≤ W) (hfit : m + m ≤ nt)
    (hnB : n < B) (hB2 : m + m < B) (hmmB : mm + 1 < B) (hkdB : kd < B)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ z < kd, IT z < B)
    (hent : SymWorkEntryC n mm nt W kd IO IT T₀ σ) :
    ∃ σ'', Run B symCompactWorkCom σ σ'' (symCompactCost mm kd + 2) ∧
      SymWorkPost mm nt m D T₀ σ'' ∧
      (σ''.arrs "gof").drop (mm + 1) = (σ.arrs "gof").drop (mm + 1) ∧
      ActiveZeroTail mm σ σ'' ∧ σ''.vars "n" = n ∧
      σ''.arrs "off" = σ.arrs "off" ∧
      σ''.arrs "tgt" = σ.arrs "tgt" := by
  obtain ⟨τ, hrun, hpost, htail, hzeroTail, hn⟩ :=
    symCompactCom_spec h1 hin hmkd hkdW hfit hnB hB2 hmmB hkdB hIOB hITB hent
  let σ'' := renEnv engineWorkSwap τ
  have hrun' : Run B symCompactWorkCom σ σ'' (symCompactCost mm kd + 2) := by
    have h := renCom_run (f := engineWorkSwap) engineWorkSwap_invol hrun
    change Run B (renCom engineWorkSwap symCompactCom) σ (renEnv engineWorkSwap τ)
      (symCompactCost mm kd + 2)
    rw [← renEnv_involutive engineWorkSwap_invol σ]
    exact h
  refine ⟨σ'', hrun', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SymWorkPost, σ'', renEnv_involutive engineWorkSwap_invol] using hpost
  · simpa only [σ'', renEnv_arrs, engineWorkSwap_gof, SymWorkEntryC] using htail
  · intro a ha
    simpa only [σ'', renEnv_arrs, engineWorkSwap_activeZero ha] using hzeroTail a ha
  · simpa only [σ'', renEnv_vars] using hn
  · exact hrun'.frame_arr "off" (by decide)
  · exact hrun'.frame_arr "tgt" (by decide)

/-! ## Axioms -/

#print axioms compactPassWorkAt_run
#print axioms compactPassWorkAtWide_run
#print axioms augCompactWork_specLive
#print axioms symCompactWork_spec

end Lax3Proofs.Refine.OrderActiveWork
