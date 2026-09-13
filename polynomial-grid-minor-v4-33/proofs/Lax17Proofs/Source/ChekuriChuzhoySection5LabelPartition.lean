import Mathlib.Order.Partition.Finpartition

namespace Lax17Proofs

universe u v w

/-!
# Finite partitions induced by labels

This module packages the partition of a finite type into the nonempty fibers
of a label map.  It is the generic adapter used when the edge groups in
Chekuri--Chuzhoy Section 5 are defined by construction labels.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5LabelPartition


open Finset

variable {E : Type u} {K : Type v}
variable [Fintype E] [DecidableEq E] [DecidableEq K]

/-- The elements carrying a fixed label. -/
def fiber (label : E -> K) (key : K) : Finset E :=
  Finset.univ.filter fun e => label e = key

omit [DecidableEq E] in
@[simp]
theorem mem_fiber {label : E -> K} {key : K} {e : E} :
    e ∈ fiber label key ↔ label e = key := by
  simp [fiber]

/-- Equality of labels as a setoid on the labeled finite type. -/
def labelSetoid (label : E -> K) : Setoid E where
  r e f := label e = label f
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂
  }

instance labelSetoidDecidableRel (label : E -> K) :
    DecidableRel (labelSetoid label).r :=
  fun e f => decEq (label e) (label f)

/-- The partition of `univ` into the nonempty fibers of `label`. -/
def partition (label : E -> K) :
    Finpartition (Finset.univ : Finset E) :=
  Finpartition.ofSetoid (labelSetoid label)

/-- The unique label part containing `e`. -/
def partOf (label : E -> K) (e : E) : Finset E :=
  (partition label).part e

@[simp]
theorem mem_partOf_iff {label : E -> K} {e f : E} :
    f ∈ partOf label e ↔ label e = label f := by
  exact Finpartition.mem_part_ofSetoid_iff_rel

@[simp]
theorem partOf_eq_fiber (label : E -> K) (e : E) :
    partOf label e = fiber label (label e) := by
  ext f
  simp [eq_comm]

@[simp]
theorem partOf_eq_partOf_iff {label : E -> K} {e f : E} :
    partOf label e = partOf label f ↔ label e = label f := by
  constructor
  · intro h
    have he : e ∈ partOf label f := by
      rw [← h]
      simp [partOf]
    exact (mem_partOf_iff.mp he).symm
  · intro h
    rw [partOf_eq_fiber, partOf_eq_fiber, h]

omit [DecidableEq E] in
@[simp]
theorem fiber_nonempty_iff_mem_image (label : E -> K) (key : K) :
    (fiber label key).Nonempty ↔
      key ∈ (Finset.univ : Finset E).image label := by
  constructor
  · rintro ⟨e, he⟩
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, mem_fiber.mp he⟩
  · intro hkey
    rcases Finset.mem_image.mp hkey with ⟨e, _, rfl⟩
    exact ⟨e, by simp⟩

@[simp]
theorem fiber_mem_parts_iff (label : E -> K) (key : K) :
    fiber label key ∈ (partition label).parts ↔
      key ∈ (Finset.univ : Finset E).image label := by
  constructor
  · intro hpart
    exact (fiber_nonempty_iff_mem_image label key).mp
      ((partition label).nonempty_of_mem_parts hpart)
  · intro hkey
    rcases Finset.mem_image.mp hkey with ⟨e, _, he⟩
    have hpart : partOf label e ∈ (partition label).parts := by
      change (partition label).part e ∈ (partition label).parts
      exact (partition label).part_mem.mpr (Finset.mem_univ e)
    simpa [partOf_eq_fiber, he] using hpart

/-- A finset is a part precisely when it is a represented label fiber. -/
theorem mem_parts_iff_exists_fiber {label : E -> K} {U : Finset E} :
    U ∈ (partition label).parts ↔
      ∃ key ∈ (Finset.univ : Finset E).image label,
        U = fiber label key := by
  constructor
  · intro hU
    rcases (partition label).nonempty_of_mem_parts hU with ⟨e, he⟩
    refine ⟨label e, Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩, ?_⟩
    rw [← partOf_eq_fiber label e]
    exact ((partition label).part_eq_iff_mem hU).2 he |>.symm
  · rintro ⟨key, hkey, rfl⟩
    exact (fiber_mem_parts_iff label key).2 hkey

theorem parts_eq_image_fiber (label : E -> K) :
    (partition label).parts =
      ((Finset.univ : Finset E).image label).image (fiber label) := by
  ext U
  simp only [mem_parts_iff_exists_fiber, Finset.mem_image]
  constructor
  · rintro ⟨key, hkey, rfl⟩
    exact ⟨key, hkey, rfl⟩
  · rintro ⟨key, hkey, rfl⟩
    exact ⟨key, hkey, rfl⟩

@[simp]
theorem card_partOf (label : E -> K) (e : E) :
    (partOf label e).card = (fiber label (label e)).card := by
  rw [partOf_eq_fiber]

/-- Uniform bounds on represented label fibers bound every partition part. -/
theorem part_card_le_of_fiber_card_le
    {label : E -> K} {bound : Nat}
    (hbound : ∀ key ∈ (Finset.univ : Finset E).image label,
      (fiber label key).card <= bound)
    {U : Finset E} (hU : U ∈ (partition label).parts) :
    U.card <= bound := by
  rcases mem_parts_iff_exists_fiber.mp hU with ⟨key, hkey, rfl⟩
  exact hbound key hkey

/-- Bounding every partition part is equivalent to bounding every represented
label fiber.  The left side unfolds directly to group-size predicates such as
`TerminalPathSkeleton.GroupSizeAtMost`. -/
theorem all_parts_card_le_iff_fibers_card_le
    (label : E -> K) (bound : Nat) :
    (∀ U ∈ (partition label).parts, U.card <= bound) ↔
      ∀ key ∈ (Finset.univ : Finset E).image label,
        (fiber label key).card <= bound := by
  constructor
  · intro hparts key hkey
    exact hparts (fiber label key) ((fiber_mem_parts_iff label key).2 hkey)
  · intro hfibers U hU
    exact part_card_le_of_fiber_card_le hfibers hU

/-- A selection meeting every label part exactly once is injectively labeled. -/
theorem injOn_label_of_onePerPart
    {label : E -> K} {selected : Finset E}
    (hselected :
      ∀ U ∈ (partition label).parts, (selected ∩ U).card = 1) :
    Set.InjOn label selected := by
  intro e he f hf hef
  have hpart : partOf label e ∈ (partition label).parts := by
    change (partition label).part e ∈ (partition label).parts
    exact (partition label).part_mem.mpr (Finset.mem_univ e)
  have hcard := hselected (partOf label e) hpart
  rcases Finset.card_eq_one.mp hcard with ⟨x, hx⟩
  have hePart : e ∈ partOf label e := by simp [partOf]
  have hfPart : f ∈ partOf label e := mem_partOf_iff.mpr hef
  have heInter : e ∈ selected ∩ partOf label e :=
    Finset.mem_inter.mpr ⟨he, hePart⟩
  have hfInter : f ∈ selected ∩ partOf label e :=
    Finset.mem_inter.mpr ⟨hf, hfPart⟩
  have hex : e = x := by
    apply Finset.mem_singleton.mp
    rw [← hx]
    exact heInter
  have hfx : f = x := by
    apply Finset.mem_singleton.mp
    rw [← hx]
    exact hfInter
  exact hex.trans hfx.symm

/-- Distinct elements selected one-per-part carry distinct labels. -/
theorem label_ne_of_mem_onePerPart
    {label : E -> K} {selected : Finset E}
    (hselected :
      ∀ U ∈ (partition label).parts, (selected ∩ U).card = 1)
    {e f : E} (he : e ∈ selected) (hf : f ∈ selected) (hef : e ≠ f) :
    label e ≠ label f := by
  intro hlabel
  exact hef (injOn_label_of_onePerPart hselected he hf hlabel)

end ChekuriChuzhoySection5LabelPartition
end SimpleGraph

end Lax17Proofs
