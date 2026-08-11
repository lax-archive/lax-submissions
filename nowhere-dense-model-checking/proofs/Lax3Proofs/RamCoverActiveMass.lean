import Lax3Proofs.RamCoverActive
import Lax3Proofs.RamDriver
import Lax3Proofs.Refine.MassWeight

/-!
# Weighted mass of an active-centre cover

An active cover has one block for each live centre, rather than one block
for every carrier position.  This file supplies the weighted double count
in exactly that indexing.  It is the active counterpart of
`Refine.MassWeight.mass_of_alive_compaction_weight`.
-/

namespace Lax3Proofs.RamCoverActiveMass

open Finset
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver
open Lax3Proofs.Refine.MassMath (blockSize clusterAt)
open Lax3Proofs.Refine.MassWeight

variable {n q r m c cnum d : ℕ}
variable {G H : SimpleGraph (Fin n)}
variable {A₀ M Mcur centre Xoff Xmem asg cps : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}

/-- The mathematical postcondition the active ordering phase exports: the
centre list enumerates the live arena in ordering order, and that ordering
has the degree bound consumed by the cover mass argument. -/
structure ActiveOrderP (G : SimpleGraph (Fin n)) (r d : ℕ) (M : ℕ → ℕ)
    (q : ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) : Prop where
  centres : CentresBy n q M π centre
  degree : ∀ v : Fin n, (wreach (masked G M) π (2 * r) v).ncard ≤ d

/-- The active ordering and the level member list enumerate the same live
vertices, so their prefix lengths agree.  Their orders may differ: centres
are sorted by `π`, whereas `MemEnum` is sorted by vertex number. -/
theorem CentresBy.count_eq_memEnum {mm : ℕ} {Mem : ℕ → ℕ}
    (hcentres : CentresBy n q M π centre) (hmem : MemEnum n mm Mem M) :
    q = mm := by
  classical
  let toMem : Fin q → Fin mm := fun k =>
    ⟨(hmem.2.2.2 (centre k) (hcentres.centre_lt k k.isLt)
        (hcentres.alive k k.isLt)).choose,
      (hmem.2.2.2 (centre k) (hcentres.centre_lt k k.isLt)
        (hcentres.alive k k.isLt)).choose_spec.1⟩
  have toMem_val : ∀ k : Fin q, Mem (toMem k) = centre k := by
    intro k
    exact (hmem.2.2.2 (centre k) (hcentres.centre_lt k k.isLt)
      (hcentres.alive k k.isLt)).choose_spec.2
  have toMem_inj : Function.Injective toMem := by
    intro i k hik
    apply Fin.ext
    apply hcentres.injective i.isLt k.isLt
    rw [← toMem_val i, ← toMem_val k, hik]
  have hqmm : q ≤ mm := by
    simpa using Fintype.card_le_of_injective toMem toMem_inj
  let toCentre : Fin mm → Fin q := fun k =>
    ⟨(hcentres.complete (Mem k) (hmem.1 k k.isLt)
        (hmem.2.2.1 k k.isLt)).choose,
      (hcentres.complete (Mem k) (hmem.1 k k.isLt)
        (hmem.2.2.1 k k.isLt)).choose_spec.1⟩
  have toCentre_val : ∀ k : Fin mm, centre (toCentre k) = Mem k := by
    intro k
    exact (hcentres.complete (Mem k) (hmem.1 k k.isLt)
      (hmem.2.2.1 k k.isLt)).choose_spec.2
  have toCentre_inj : Function.Injective toCentre := by
    intro i k hik
    apply Fin.ext
    have hval : Mem i = Mem k := by
      rw [← toCentre_val i, ← toCentre_val k, hik]
    rcases lt_trichotomy (i : ℕ) (k : ℕ) with hlt | heq | hgt
    · have := hmem.2.1 (i : ℕ) (k : ℕ) hlt k.isLt
      omega
    · exact heq
    · have := hmem.2.1 (k : ℕ) (i : ℕ) hgt i.isLt
      omega
  have hmmq : mm ≤ q := by
    simpa using Fintype.card_le_of_injective toCentre toCentre_inj
  omega

theorem ActiveOrderP.count_eq_memEnum {mm : ℕ} {Mem : ℕ → ℕ}
    (horder : ActiveOrderP G r d M q π centre) (hmem : MemEnum n mm Mem M) :
    q = mm :=
  CentresBy.count_eq_memEnum horder.centres hmem

/-! ## A weighted double count with a separate centre type -/

/-- A family indexed by `Fin q`, supported in `S`, whose fibres have
cardinality at most `d`, has total weight at most `d` times the weight of
`S`.  `MassWeight.sum_wsum_le_mul_of_subset` is the `q = n` instance. -/
theorem sum_wsum_le_mul_active (f : Fin n → ℕ) (X : Fin q → Set (Fin n))
    (S : Set (Fin n)) (d : ℕ) (hsub : ∀ u : Fin q, X u ⊆ S)
    (hfib : ∀ w : Fin n, {u : Fin q | w ∈ X u}.ncard ≤ d) :
    ∑ u : Fin q, wsum f (X u) ≤ d * wsum f S := by
  classical
  have hpoint : ∀ v : Fin n,
      ∑ u : Fin q, Set.indicator (X u) f v ≤ d * Set.indicator S f v := by
    intro v
    by_cases hv : v ∈ S
    · have hfib' : (Set.toFinite {u : Fin q | v ∈ X u}).toFinset.card ≤ d := by
        rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
        exact hfib v
      have hres : ∑ u : Fin q, Set.indicator (X u) f v =
          ∑ _u ∈ (Set.toFinite {u : Fin q | v ∈ X u}).toFinset, f v := by
        have h₁ : ∑ u ∈ (Set.toFinite {u : Fin q | v ∈ X u}).toFinset,
              Set.indicator (X u) f v = ∑ u : Fin q, Set.indicator (X u) f v :=
          Finset.sum_subset (Finset.subset_univ _) fun u _ hu => by
            refine Set.indicator_of_notMem (fun hx => hu ?_) f
            exact mem_wsumFinset.mpr hx
        rw [← h₁]
        refine Finset.sum_congr rfl fun u hu => ?_
        have hx : v ∈ X u := by
          have h₂ := mem_wsumFinset.mp hu
          rwa [Set.mem_setOf_eq] at h₂
        exact Set.indicator_of_mem hx f
      rw [hres, Finset.sum_const, smul_eq_mul, Set.indicator_of_mem hv f]
      exact Nat.mul_le_mul_right _ hfib'
    · have hzero : ∀ u : Fin q, Set.indicator (X u) f v = 0 := fun u =>
        Set.indicator_of_notMem (fun hx => hv (hsub u hx)) f
      rw [Finset.sum_congr rfl fun u _ => hzero u]
      simp
  calc
    ∑ u : Fin q, wsum f (X u) =
        ∑ u : Fin q, ∑ v : Fin n, Set.indicator (X u) f v :=
      Finset.sum_congr rfl fun u _ => wsum_eq_sum_indicator f (X u)
    _ = ∑ v : Fin n, ∑ u : Fin q, Set.indicator (X u) f v := Finset.sum_comm
    _ ≤ ∑ v : Fin n, d * Set.indicator S f v :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = d * ∑ v : Fin n, Set.indicator S f v := by rw [Finset.mul_sum]
    _ = d * wsum f S := by rw [← wsum_eq_sum_indicator]

/-! ## Blocks as the mathematical cluster family -/

/-- Every offset in the active prefix lies below the arena pointer. -/
private theorem off_le_arena
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {t : ℕ} (ht : t ≤ q) :
    Xoff t ≤ m := by
  have key : ∀ e t, t + e = q → Xoff t ≤ Xoff q := by
    intro e
    induction e with
    | zero =>
        intro t hte
        rw [show t = q by omega]
    | succ e ih =>
        intro t hte
        exact le_trans (h.mono t (by omega)) (ih (t + 1) (by omega))
  rw [← h.last]
  exact key (q - t) t (by omega)

/-- A block of an active cover has exactly the weight of its cluster. -/
theorem slotWeight_eq_wsum_clusterAtA (f : Fin n → ℕ)
    (h : CoverOutA G M π centre r q m Xoff Xmem asg) {k : ℕ} (hk : k < q) :
    slotWeight n f Xoff Xmem k = wsum f (clusterAt G M π centre r k) := by
  classical
  have hqn := h.count_le
  have hn : 0 < n := by omega
  have hlt : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact h.mem_lt p (lt_of_lt_of_le hp.2 (off_le_arena h (by omega)))
  set g : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hg
  have hgval : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)),
      ((g p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hginj : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)),
      ∀ p' ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), g p = g p' → p = p' := by
    intro p hp p' hp' hpp'
    have hpI := Finset.mem_Ico.mp hp
    have hpI' := Finset.mem_Ico.mp hp'
    have hval : Xmem p = Xmem p' := by
      rw [← hgval p hp, ← hgval p' hp', hpp']
    exact h.block_inj k hk p p' hpI.1 hpI.2 hpI'.1 hpI'.2 hval
  have himg : clusterAt G M π centre r k =
      ↑((Finset.Ico (Xoff k) (Xoff (k + 1))).image g) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp₁, hp₂, hp₃⟩ := (h.block k hk (z : ℕ)).mpr hz
      have hp : p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)) :=
        Finset.mem_Ico.mpr ⟨hp₁, hp₂⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨p, hp, Fin.ext (by rw [hgval p hp, hp₃])⟩)
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
      have hpI := Finset.mem_Ico.mp hp
      show InCluster (masked G M) π r (centre k) ((g p : Fin n) : ℕ)
      rw [hgval p hp]
      exact (h.block k hk (Xmem p)).mp ⟨p, hpI.1, hpI.2, rfl⟩
  rw [himg, wsum_coe_finset, Finset.sum_image hginj]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [natW_val f (hlt p hp)]
  exact congrArg f (Fin.ext (hgval p hp).symm)

/-- The active centres are an injective map into the carrier. -/
private def centreFin (h : CentresBy n q M π centre) (k : Fin q) : Fin n :=
  ⟨centre k, h.centre_lt k k.isLt⟩

private theorem centreFin_injective (h : CentresBy n q M π centre) :
    Function.Injective (centreFin h) := by
  intro i k hik
  apply Fin.ext
  exact h.injective i.isLt k.isLt (congrArg Fin.val hik)

/-- The sum of all active block weights has the cover-degree bound. -/
theorem activeMassW_le (f : Fin n → ℕ)
    (hcentres : CentresBy n q M π centre)
    (hout : CoverOutA G M π centre r q m Xoff Xmem asg)
    (hk : ∀ v : Fin n, (wreach (masked G M) π (2 * r) v).ncard ≤ d) :
    (∑ k ∈ range q, slotWeight n f Xoff Xmem k) ≤
      d * (wsum f {v : Fin n | M (v : ℕ) ≠ 0} + 1) := by
  classical
  let cf : Fin q → Fin n := centreFin hcentres
  have hcf : Function.Injective cf := centreFin_injective hcentres
  let X : Fin q → Set (Fin n) :=
    fun k => clusterAt G M π centre r (k : ℕ)
  let S : Set (Fin n) := {v : Fin n | M (v : ℕ) ≠ 0}
  have hsub : ∀ k : Fin q, X k ⊆ S := by
    intro k z hz
    exact (Lax3Proofs.Refine.MassAlive.inCluster_alive_iff hz).mpr
      (hcentres.alive k k.isLt)
  have hfib : ∀ w : Fin n, {k : Fin q | w ∈ X k}.ncard ≤ d := by
    intro w
    let I : Set (Fin q) := {k : Fin q | w ∈ X k}
    have himg : cf '' I ⊆ wreach (masked G M) π (2 * r) w := by
      rintro _ ⟨k, hkI, rfl⟩
      exact (inCluster_iff (hcentres.centre_lt k k.isLt) w.isLt).mp hkI
    calc
      I.ncard = (cf '' I).ncard := (Set.InjOn.ncard_image hcf.injOn).symm
      _ ≤ (wreach (masked G M) π (2 * r) w).ncard :=
        Set.ncard_le_ncard himg (Set.toFinite _)
      _ ≤ d := hk w
  have hmass : ∑ k : Fin q, wsum f (X k) ≤ d * wsum f S :=
    sum_wsum_le_mul_active f X S d hsub hfib
  calc
    (∑ k ∈ range q, slotWeight n f Xoff Xmem k) =
        ∑ k : Fin q, slotWeight n f Xoff Xmem (k : ℕ) :=
      (Fin.sum_univ_eq_sum_range
        (fun k => slotWeight n f Xoff Xmem k) q).symm
    _ = ∑ k : Fin q, wsum f (X k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact slotWeight_eq_wsum_clusterAtA f hout k.isLt
    _ ≤ d * wsum f S := hmass
    _ ≤ d * (wsum f S + 1) := Nat.mul_le_mul_left _ (by omega)

/-! ## Partial raw covers

The executable loop needs the same degree reading before all centres have
been processed.  A degree bound controls the total prefix, rather than each
individual cluster: one cluster may contain the whole carrier even when the
weak-reach degree is small. -/

private theorem raw_sum_blockSize
    (h : RawCoverInvA G A₀ π centre q r c m Xoff Xmem asg Mcur) :
    ∀ t, t ≤ c → ∑ k ∈ range t, blockSize Xoff k = Xoff t := by
  intro t ht
  induction t with
  | zero => simp [h.zero]
  | succ t ih =>
      rw [sum_range_succ, ih (by omega), blockSize,
        Nat.add_sub_of_le (h.mono t (by omega))]

/-- A processed raw block already has exactly the weight of its mathematical
cluster; sorting is irrelevant to this equality. -/
theorem rawSlotWeight_eq_wsum_clusterAtA (f : Fin n → ℕ)
    (hcentres : CentresBy n q A₀ π centre)
    (h : RawCoverInvA G A₀ π centre q r c m Xoff Xmem asg Mcur)
    {k : ℕ} (hk : k < c) :
    slotWeight n f Xoff Xmem k = wsum f (clusterAt G A₀ π centre r k) := by
  classical
  have hcn : c ≤ n := le_trans h.pos_le hcentres.count_le
  have hn : 0 < n := by omega
  have hoff : Xoff (k + 1) ≤ m := by
    have hm := h.mono' (i := k + 1) (j := c) (by omega) le_rfl
    rwa [h.ptr] at hm
  have hlt : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), Xmem p < n := by
    intro p hp
    rw [Finset.mem_Ico] at hp
    exact h.mem_lt p (lt_of_lt_of_le hp.2 hoff)
  set g : ℕ → Fin n := fun p => ⟨Xmem p % n, Nat.mod_lt _ hn⟩ with hg
  have hgval : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)),
      ((g p : Fin n) : ℕ) = Xmem p :=
    fun p hp => Nat.mod_eq_of_lt (hlt p hp)
  have hginj : ∀ p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)),
      ∀ p' ∈ Finset.Ico (Xoff k) (Xoff (k + 1)), g p = g p' → p = p' := by
    intro p hp p' hp' hpp'
    have hpI := Finset.mem_Ico.mp hp
    have hpI' := Finset.mem_Ico.mp hp'
    have hval : Xmem p = Xmem p' := by
      rw [← hgval p hp, ← hgval p' hp', hpp']
    exact h.block_inj k hk p p' hpI.1 hpI.2 hpI'.1 hpI'.2 hval
  have himg : clusterAt G A₀ π centre r k =
      ↑((Finset.Ico (Xoff k) (Xoff (k + 1))).image g) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp₁, hp₂, hp₃⟩ := (h.block k hk (z : ℕ)).mpr hz
      have hp : p ∈ Finset.Ico (Xoff k) (Xoff (k + 1)) :=
        Finset.mem_Ico.mpr ⟨hp₁, hp₂⟩
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨p, hp, Fin.ext (by rw [hgval p hp, hp₃])⟩)
    · intro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
      have hpI := Finset.mem_Ico.mp hp
      show InCluster (masked G A₀) π r (centre k) ((g p : Fin n) : ℕ)
      rw [hgval p hp]
      exact (h.block k hk (Xmem p)).mp ⟨p, hpI.1, hpI.2, rfl⟩
  rw [himg, wsum_coe_finset, Finset.sum_image hginj]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [natW_val f (hlt p hp)]
  exact congrArg f (Fin.ext (hgval p hp).symm)

/-- Every prefix pointer of the raw active construction is bounded by the
carrier times the weak-reach degree.  No per-cluster cardinality hypothesis
is needed (or generally true). -/
theorem rawPointer_le_degree
    (hcentres : CentresBy n q A₀ π centre)
    (h : RawCoverInvA G A₀ π centre q r c m Xoff Xmem asg Mcur)
    (hk : ∀ v : Fin n, (wreach (masked G A₀) π (2 * r) v).ncard ≤ d) :
    m ≤ n * d := by
  classical
  let cf : Fin c → Fin n := fun k =>
    ⟨centre k, hcentres.centre_lt k (lt_of_lt_of_le k.isLt h.pos_le)⟩
  have hcf : Function.Injective cf := by
    intro i k hik
    apply Fin.ext
    exact hcentres.injective (lt_of_lt_of_le i.isLt h.pos_le)
      (lt_of_lt_of_le k.isLt h.pos_le) (congrArg Fin.val hik)
  let X : Fin c → Set (Fin n) :=
    fun k => clusterAt G A₀ π centre r (k : ℕ)
  have hfib : ∀ w : Fin n, {k : Fin c | w ∈ X k}.ncard ≤ d := by
    intro w
    let I : Set (Fin c) := {k : Fin c | w ∈ X k}
    have himg : cf '' I ⊆ wreach (masked G A₀) π (2 * r) w := by
      rintro _ ⟨k, hkI, rfl⟩
      exact (inCluster_iff
        (hcentres.centre_lt k (lt_of_lt_of_le k.isLt h.pos_le)) w.isLt).mp hkI
    calc
      I.ncard = (cf '' I).ncard := (Set.InjOn.ncard_image hcf.injOn).symm
      _ ≤ (wreach (masked G A₀) π (2 * r) w).ncard :=
        Set.ncard_le_ncard himg (Set.toFinite _)
      _ ≤ d := hk w
  have hmass : ∑ k : Fin c, wsum (fun _ : Fin n => 1) (X k) ≤
      d * wsum (fun _ : Fin n => 1) (Set.univ : Set (Fin n)) :=
    sum_wsum_le_mul_active (fun _ : Fin n => 1) X Set.univ d
      (fun _ => Set.subset_univ _) hfib
  calc
    m = ∑ k ∈ range c, blockSize Xoff k := by
      rw [raw_sum_blockSize h c le_rfl, h.ptr]
    _ = ∑ k : Fin c, blockSize Xoff (k : ℕ) :=
      (Fin.sum_univ_eq_sum_range (fun k => blockSize Xoff k) c).symm
    _ = ∑ k : Fin c, wsum (fun _ : Fin n => 1) (X k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← rawSlotWeight_eq_wsum_clusterAtA (fun _ : Fin n => 1)
        hcentres h k.isLt]
      have hoff : Xoff ((k : ℕ) + 1) ≤ m := by
        have hm := h.mono' (i := (k : ℕ) + 1) (j := c) (by omega) le_rfl
        rwa [h.ptr] at hm
      rw [slotWeight, blockSize]
      symm
      calc
        (∑ p ∈ Finset.Ico (Xoff (k : ℕ)) (Xoff ((k : ℕ) + 1)),
            natW n (fun _ : Fin n => 1) (Xmem p)) =
            ∑ _p ∈ Finset.Ico (Xoff (k : ℕ)) (Xoff ((k : ℕ) + 1)), 1 := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpI := Finset.mem_Ico.mp hp
          rw [natW_val _ (h.mem_lt p (lt_of_lt_of_le hpI.2 hoff))]
        _ = Xoff ((k : ℕ) + 1) - Xoff (k : ℕ) := by simp
    _ ≤ d * wsum (fun _ : Fin n => 1) (Set.univ : Set (Fin n)) := hmass
    _ = n * d := by rw [wsum_univ]; simp [Nat.mul_comm]

/-! ## The compacted turn list -/

/-- A compacted active-position list weighs no more than all active blocks. -/
theorem sum_slotWeight_cps_le_activeMassW (f : Fin n → ℕ)
    (hcomp : Compacted q cnum m M centre Xoff cps) :
    (∑ k ∈ range cnum, slotWeight n f Xoff Xmem (cps k)) ≤
      ∑ k ∈ range q, slotWeight n f Xoff Xmem k := by
  classical
  have hinj : Set.InjOn cps ↑(range cnum) := by
    intro k hk k' hk' he
    exact hcomp.inj (mem_range.mp (Finset.mem_coe.mp hk))
      (mem_range.mp (Finset.mem_coe.mp hk')) he
  rw [← Finset.sum_image (g := cps)
    (f := fun k => slotWeight n f Xoff Xmem k) hinj]
  exact Finset.sum_le_sum_of_subset fun k hk => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact mem_range.mpr (hcomp.lt i (mem_range.mp hi))

/-- Active centres inject into the live arena, so their count is below its
weight. -/
theorem centreCount_le_arenaWeight (H : SimpleGraph (Fin n))
    (hcentres : CentresBy n q M π centre) : q ≤ arenaWeight n H M := by
  classical
  let cf : Fin q → Fin n := centreFin hcentres
  have hcf : Function.Injective cf := centreFin_injective hcentres
  have himg : cf '' (Set.univ : Set (Fin q)) ⊆
      {v : Fin n | M (v : ℕ) ≠ 0} := by
    rintro _ ⟨k, -, rfl⟩
    exact hcentres.alive k k.isLt
  calc
    q = (Set.univ : Set (Fin q)).ncard := by simp
    _ = (cf '' (Set.univ : Set (Fin q))).ncard :=
      (Set.InjOn.ncard_image hcf.injOn).symm
    _ ≤ ({v : Fin n | M (v : ℕ) ≠ 0} : Set (Fin n)).ncard :=
      Set.ncard_le_ncard himg (Set.toFinite _)
    _ ≤ arenaWeight n H M := arenaSize_le_arenaWeight n H M

/-- The exact weighted `hmass` pair consumed by the active level theorem. -/
theorem mass_of_active_compaction_weight (H : SimpleGraph (Fin n))
    (hcentres : CentresBy n q M π centre)
    (hout : CoverOutA G M π centre r q m Xoff Xmem asg)
    (hk : ∀ v : Fin n, (wreach (masked G M) π (2 * r) v).ncard ≤ d)
    (hcomp : Compacted q cnum m M centre Xoff cps) :
    cnum ≤ arenaWeight n H M ∧
      (∑ k ∈ range cnum, blockWeight n H Xoff Xmem (cps k)) ≤
        d * (arenaWeight n H M + 1) := by
  refine ⟨le_trans hcomp.le_carrier (centreCount_le_arenaWeight H hcentres), ?_⟩
  exact le_trans (sum_slotWeight_cps_le_activeMassW (graphW H) hcomp)
    (activeMassW_le (graphW H) hcentres hout hk)

/-- `ActiveOrderP` discharges the active level theorem's opaque `hmass`
slot in one step. -/
theorem mass_of_active_order (H : SimpleGraph (Fin n))
    (horder : ActiveOrderP G r d M q π centre)
    (hout : CoverOutA G M π centre r q m Xoff Xmem asg)
    (hcomp : Compacted q cnum m M centre Xoff cps) :
    cnum ≤ arenaWeight n H M ∧
      (∑ k ∈ range cnum, blockWeight n H Xoff Xmem (cps k)) ≤
        d * (arenaWeight n H M + 1) :=
  mass_of_active_compaction_weight H horder.centres hout horder.degree hcomp

#print axioms rawSlotWeight_eq_wsum_clusterAtA
#print axioms rawPointer_le_degree
#print axioms mass_of_active_order

end Lax3Proofs.RamCoverActiveMass
