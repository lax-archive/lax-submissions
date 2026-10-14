import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Tactic

/-!
Finite trace and VC-dimension bounds for the sampler.  In particular, the
linearity hypothesis only applies to nonempty ground sets.
-/

namespace Lax457868Proofs.SamplerVCDimension

variable {α : Type*} [DecidableEq α]

/-- The distinct restrictions of a finite set family to a finite ground set. -/
def traceFamily (H : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  H.image fun h => S ∩ h

lemma card_powerset_le_of_shatters (H : Finset (Finset α))
    (S : Finset α) (hs : H.Shatters S) :
    2 ^ S.card = (traceFamily H S).card := by
  rw [Finset.shatters_iff] at hs
  simpa [traceFamily, Finset.card_powerset] using congrArg Finset.card hs.symm

/-- A shattered nonempty set realizes every binary pattern, so a linear
shatter bound controls its cardinality. -/
lemma pow_card_le_linear_of_shatters (H : Finset (Finset α)) (c : ℕ)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (traceFamily H S).card ≤ c * S.card)
    {S : Finset α} (hS : S.Nonempty) (hs : H.Shatters S) :
    2 ^ S.card ≤ c * S.card := by
  rw [card_powerset_le_of_shatters H S hs]
  exact hlinear S hS

private lemma two_mul_le_two_pow (m : ℕ) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => norm_num
    | succ m =>
      have hp : 0 < 2 ^ m := pow_pos (by norm_num) _
      have htwo : 2 ≤ 2 ^ (m + 1) := by rw [pow_succ]; omega
      calc
        2 * (m + 1 + 1) = 2 * (m + 1) + 2 := by omega
        _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) := Nat.add_le_add ih htwo
        _ = 2 ^ (m + 1 + 1) := by rw [pow_succ]; omega

/-- The elementary exponential comparison needed for the VC bound.  The
factor two is slightly stronger than the paper's stated factor four. -/
lemma card_le_two_clog_of_pow_le_linear (c n : ℕ)
    (h : 2 ^ n ≤ c * n) : n ≤ 2 * Nat.clog 2 c := by
  let k := Nat.clog 2 c
  have hck : c ≤ 2 ^ k := Nat.le_pow_clog (by norm_num) c
  by_contra hn
  have hnk : 2 * k < n := by omega
  let m := n - k
  have hkm : k + m = n := by dsimp [m]; omega
  have hnm : n < 2 * m := by dsimp [m]; omega
  have hm : 2 * m ≤ 2 ^ m := two_mul_le_two_pow m
  have hc_bound : c * n ≤ 2 ^ k * n := Nat.mul_le_mul_right _ hck
  have hstrict : 2 ^ k * n < 2 ^ k * 2 ^ m := by
    exact Nat.mul_lt_mul_of_pos_left (hnm.trans_le hm) (pow_pos (by norm_num) _)
  have hpow : 2 ^ k * 2 ^ m = 2 ^ n := by rw [← pow_add, hkm]
  omega

/-- Linear growth of nonempty traces bounds the VC dimension. -/
lemma vcDim_le_two_clog (H : Finset (Finset α)) (c : ℕ) (_hc : 2 ≤ c)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (traceFamily H S).card ≤ c * S.card) :
    H.vcDim ≤ 2 * Nat.clog 2 c := by
  unfold Finset.vcDim
  apply Finset.sup_le
  intro S hS
  by_cases hne : S.Nonempty
  · exact card_le_two_clog_of_pow_le_linear c S.card
      (pow_card_le_linear_of_shatters H c hlinear hne
        (Finset.mem_shatterer.mp hS))
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-- The paper's convenient numerical VC bound. -/
lemma vcDim_le_four_clog (H : Finset (Finset α)) (c : ℕ) (hc : 2 ≤ c)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (traceFamily H S).card ≤ c * S.card) :
    H.vcDim ≤ 4 * Nat.clog 2 c := by
  exact (vcDim_le_two_clog H c hc hlinear).trans (by omega)

variable {ι : Type*} [DecidableEq ι]

/-- The neighborhoods of sample positions. Positions are kept distinct even
when the same ground element was drawn more than once. -/
def positionFamily (H : Finset (Finset α)) (P : Finset ι)
    (draw : ι → α) : Finset (Finset ι) :=
  H.image fun h => P.filter (fun i => draw i ∈ h)

lemma shatters_positions_injOn (H : Finset (Finset α))
    (P T : Finset ι) (draw : ι → α) (hTP : T ⊆ P)
    (hs : (positionFamily H P draw).Shatters T) :
    Set.InjOn draw (T : Set ι) := by
  intro i hi j hj hij
  have hi' : i ∈ T := hi
  have hj' : j ∈ T := hj
  obtain ⟨Q, hQ, hTQ⟩ := hs (Finset.singleton_subset_iff.mpr hi')
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hQ
  have hih : draw i ∈ h := by
    have hmem : i ∈ T ∩ P.filter (fun x => draw x ∈ h) := by rw [hTQ]; simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).2).2
  have hjh : draw j ∈ h := by rw [← hij]; exact hih
  have hjmem : j ∈ T ∩ P.filter (fun x => draw x ∈ h) := by
    exact Finset.mem_inter.mpr ⟨hj', Finset.mem_filter.mpr ⟨hTP hj', hjh⟩⟩
  rw [hTQ] at hjmem
  exact (Finset.mem_singleton.mp hjmem).symm

lemma shatters_positions_image (H : Finset (Finset α))
    (P T : Finset ι) (draw : ι → α) (hTP : T ⊆ P)
    (hs : (positionFamily H P draw).Shatters T) :
    H.Shatters (T.image draw) := by
  intro V hV
  let U := T.filter (fun i => draw i ∈ V)
  obtain ⟨Q, hQ, hTQ⟩ := hs (Finset.filter_subset (fun i => draw i ∈ V) T)
  obtain ⟨h, hh, hQeq⟩ := Finset.mem_image.mp hQ
  refine ⟨h, hh, ?_⟩
  have hiff (i : ι) (hi : i ∈ T) : draw i ∈ h ↔ draw i ∈ V := by
    have hmem := congrArg (fun X : Finset ι => i ∈ X) hTQ
    rw [← hQeq] at hmem
    simpa [U, hi, hTP hi] using hmem
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨haT, hih⟩ := Finset.mem_inter.mp ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp haT
    exact (hiff i hi).mp hih
  · intro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hV ha)
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      (hiff i hi).mpr ha⟩

/-- Pulling a finite family back to sample positions preserves its VC bound,
including for repeated draws. -/
lemma positionFamily_vcDim_le (H : Finset (Finset α)) (P : Finset ι)
    (draw : ι → α) : (positionFamily H P draw).vcDim ≤ H.vcDim := by
  unfold Finset.vcDim
  apply Finset.sup_le
  intro T hT
  have hs : (positionFamily H P draw).Shatters T := Finset.mem_shatterer.mp hT
  have hTP : T ⊆ P := by
    intro i hi
    obtain ⟨Q, hQ, hTQ⟩ := hs (Finset.singleton_subset_iff.mpr hi)
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hQ
    have hiQ : i ∈ T ∩ P.filter (fun x => draw x ∈ h) := by rw [hTQ]; simp
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hiQ).2).1
  have hinj := shatters_positions_injOn H P T draw hTP hs
  have himage := shatters_positions_image H P T draw hTP hs
  rw [← Finset.card_image_of_injOn hinj]
  exact himage.card_le_vcDim

lemma positionFamily_vcDim_le_four_clog (H : Finset (Finset α))
    (P : Finset ι) (draw : ι → α) (c : ℕ) (hc : 2 ≤ c)
    (hlinear : ∀ S : Finset α, S.Nonempty →
      (traceFamily H S).card ≤ c * S.card) :
    (positionFamily H P draw).vcDim ≤ 4 * Nat.clog 2 c :=
  (positionFamily_vcDim_le H P draw).trans
    (vcDim_le_four_clog H c hc hlinear)

end Lax457868Proofs.SamplerVCDimension
