import Lax457868Proofs.ClassRepresentativeTrace
import Lax457868Proofs.LocalFlatLaw
import Lax457868Proofs.StoppedPrefixAveraging

/-! Expected source charge for successive variable-width class selectors. -/
namespace Lax457868Proofs.ClassTraceMean
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.StoppingPrefix

lemma firstDecodedWithCount_prefix {α : Type*} (xs ys : List (Option α))
    (hlen : xs.length = ys.length)
    (hpre : xs.take (firstDecodedWithCount xs).2 =
      ys.take (firstDecodedWithCount xs).2) :
    firstDecodedWithCount ys = firstDecodedWithCount xs := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst ys
    rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have htlen : xs.length = ys.length := by simpa using hlen
      cases x with
      | some a =>
        have hy : y = some a := by
          simpa [firstDecodedWithCount] using (congrArg List.head? hpre).symm
        subst y
        simp [firstDecodedWithCount]
      | none =>
        have hc : firstDecodedWithCount (none :: xs) =
            ((firstDecodedWithCount xs).1, (firstDecodedWithCount xs).2 + 1) := by
          simp [firstDecodedWithCount]
        rw [hc] at hpre
        simp only [List.take_succ_cons] at hpre
        have hh := List.cons.inj hpre
        have hy : y = none := hh.1.symm
        subst y
        rw [firstDecodedWithCount, ih ys htlen hh.2]
        rfl

lemma select_prefix (m t : ℕ) (hm : 0 < m) (a b : BitTape m t)
    (hpre : (tapeBits a).take ((selectBitIndexWithCount m hm t a).2 * Nat.clog 2 m) =
      (tapeBits b).take ((selectBitIndexWithCount m hm t a).2 * Nat.clog 2 m)) :
    selectBitIndexWithCount m hm t b = selectBitIndexWithCount m hm t a := by
  have hp : (List.ofFn a).take (selectBitIndexWithCount m hm t a).2 =
      (List.ofFn b).take (selectBitIndexWithCount m hm t a).2 := by
    apply LocalFlatLaw.flatMap_ofFn_injective_of_length (Nat.clog 2 m)
    · simp
    · simpa only [LocalFlatLaw.flatMap_take_blocks, tapeBits] using hpre
  apply firstDecodedWithCount_prefix
  · simp
  · simpa only [List.map_take, selectBitIndexWithCount] using congrArg (List.map (decodeBitIndex m hm)) hp


lemma classTrace_unique (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits bits₂ : List Bool} {v₁ v₂ : List ℕ}
      {u₁ u₂ c₁ c₂ : ℕ} {f₁ f₂ : Bool},
      ClassTrace size t start d r bits v₁ u₁ c₁ f₁ →
      ClassTrace size t start d r bits₂ v₂ u₂ c₂ f₂ →
      bits = bits₂ →
      v₁ = v₂ ∧ u₁ = u₂ ∧ c₁ = c₂ ∧ f₁ = f₂ := by
  intro d r bits bits₂ v₁ v₂ u₁ u₂ c₁ c₂ f₁ f₂ h₁
  induction h₁ generalizing bits₂ v₂ u₂ c₂ f₂ with
  | done d bits =>
    intro h₂ heq
    cases h₂
    simp
  | @failed d r tape tail u hm hsel =>
    intro h₂ heq
    cases h₂ with
    | failed tape' tail' u' hm' hsel' =>
      have hhead : tapeBits tape = tapeBits tape' := by
        have hh := congrArg (List.take (t * Nat.clog 2 (size d))) heq
        simpa [tapeBits_length] using hh
      have ht := tapeBits_injective _ _ hhead
      subst tape'
      have hu : u = u' := congrArg Prod.snd (hsel.symm.trans hsel')
      subst u'
      simp
    | accepted tape' tail' i' u' hm' hsel' hnext =>
      have hhead : tapeBits tape = tapeBits tape' := by
        have hh := congrArg (List.take (t * Nat.clog 2 (size d))) heq
        simpa [tapeBits_length] using hh
      have ht := tapeBits_injective _ _ hhead
      subst tape'
      have hh := congrArg Prod.fst (hsel.symm.trans hsel')
      contradiction
  | @accepted d r tape tail i u values used charge failed hm hsel hnext ih =>
    intro h₂ heq
    cases h₂ with
    | failed tape' tail' u' hm' hsel' =>
      have hhead : tapeBits tape = tapeBits tape' := by
        have hh := congrArg (List.take (t * Nat.clog 2 (size d))) heq
        simpa [tapeBits_length] using hh
      have ht := tapeBits_injective _ _ hhead
      subst tape'
      have hh := congrArg Prod.fst (hsel.symm.trans hsel')
      contradiction
    | accepted tape' tail' i' u' hm' hsel' hnext' =>
      have hhead : tapeBits tape = tapeBits tape' := by
        have hh := congrArg (List.take (t * Nat.clog 2 (size d))) heq
        simpa [tapeBits_length] using hh
      have ht := tapeBits_injective _ _ hhead
      subst tape'
      have htail : tail = tail' := List.append_cancel_left heq
      subst tail'
      have hs := hsel.symm.trans hsel'
      have hi : i = i' := Option.some.inj (congrArg Prod.fst hs)
      have hu : u = u' := congrArg Prod.snd hs
      subst i'
      subst u'
      obtain ⟨hv, hu, hc, hf⟩  := ih hnext' rfl
      simp [hv, hu, hc, hf]

open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open Lax457868Proofs.StoppedPrefixAveraging

noncomputable def charge (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r : ℕ) (bits : List Bool) : ℕ := by
  classical
  exact if h : ∃ c v u f, ClassTrace size t start d r bits v u c f then
    Classical.choose h else 0

lemma charge_eq {size : ℕ → ℕ} {t : ℕ} {start : ℕ → ℕ}
    {d r : ℕ} {bits : List Bool} {v : List ℕ} {u c : ℕ} {f : Bool}
    (h : ClassTrace size t start d r bits v u c f) :
    charge size t start d r bits = c := by
  classical
  have he : ∃ c v u f, ClassTrace size t start d r bits v u c f := ⟨c,v,u,f,h⟩
  simp only [charge, dif_pos he]
  obtain ⟨v', u', f', hh⟩ := Classical.choose_spec he
  exact (classTrace_unique size t start hh h rfl).2.2.1

lemma charge_spec (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r : ℕ) (bits : List Bool)
    (hp : ∀ j, d ≤ j → j < d+r → 0 < size j)
    (hb : bitBudget size t d r ≤ bits.length) :
    ∃ v u f, ClassTrace size t start d r bits v u
      (charge size t start d r bits) f := by
  obtain ⟨v,u,c,f,hh⟩ := trace_exists size t start d r bits hp hb
  exact ⟨v,u,f,by rwa [charge_eq hh]⟩

lemma charge_step_le (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r : ℕ) (a : BitTape (size d) t) (tail : List Bool)
    (hm : 0 < size d)
    (hp : ∀ j, d+1 ≤ j → j < (d+1)+r → 0 < size j)
    (hb : bitBudget size t (d+1) r ≤ tail.length) :
    charge size t start d (r+1) (tapeBits a ++ tail) ≤
      (15 * Nat.clog 2 (size d)+30) * (selectBitIndexWithCount (size d) hm t a).2 +
        12 * Nat.clog 2 (size d)+61 +
        charge size t start (d+1) r
          ((tapeBits a ++ tail).drop ((selectBitIndexWithCount (size d) hm t a).2 *
            Nat.clog 2 (size d))) := by
  generalize hs : selectBitIndexWithCount (size d) hm t a = z
  obtain ⟨o,u⟩ := z
  have hu : u ≤ t := by
    have hh := firstDecodedWithCount_le_length
      ((List.ofFn a).map (decodeBitIndex (size d) hm))
    change (selectBitIndexWithCount (size d) hm t a).2 ≤ _ at hh
    simpa [hs] using hh
  have hdrop : (tapeBits a ++ tail).drop (u*Nat.clog 2 (size d)) =
      (tapeBits a).drop (u*Nat.clog 2 (size d)) ++ tail := by
    rw [List.drop_append]
    have hle := Nat.mul_le_mul_right (Nat.clog 2 (size d)) hu
    simp [tapeBits_length, Nat.sub_eq_zero_of_le hle]
  cases o with
  | none =>
    rw [charge_eq (ClassTrace.failed a tail u hm hs)]
    simp
  | some i =>
    obtain ⟨v,used,f,hh⟩ := charge_spec size t start (d+1) r
      ((tapeBits a).drop (u*Nat.clog 2 (size d)) ++ tail) hp
      (by simp only [List.length_append]; omega)
    rw [charge_eq (ClassTrace.accepted a tail i u hm hs hh), hdrop]

noncomputable def firstTape {N : ℕ} (m t : ℕ)
    (h : t * Nat.clog 2 m ≤ N) (ρ : Tape N) : BitTape m t :=
  (LocalFlatLaw.blockTapeBitsEquiv t (Nat.clog 2 m)).symm ((splitEquiv h ρ).1)

lemma firstTape_split {N : ℕ} (m t : ℕ) (h : t * Nat.clog 2 m ≤ N)
    (ρ : Tape N) : List.ofFn ρ = tapeBits (firstTape m t h ρ) ++
      List.ofFn ((splitEquiv h ρ).2) := by
  have hh := LocalFlatLaw.flatBits_blockTapeBitsEquiv t (Nat.clog 2 m)
    (firstTape m t h ρ)
  have hh' : List.ofFn ((splitEquiv h ρ).1) = tapeBits (firstTape m t h ρ) := by
    simpa only [firstTape, Equiv.apply_symm_apply, flatBits] using hh
  rw [← hh']
  exact boolTape_split h ρ

lemma firstTape_used_le {N : ℕ} (m t : ℕ) (hm : 0 < m)
    (h : t * Nat.clog 2 m ≤ N) (ρ : Tape N) :
    (selectBitIndexWithCount m hm t (firstTape m t h ρ)).2 ≤ t := by
  exact (firstDecodedWithCount_le_length
    ((List.ofFn (firstTape m t h ρ)).map (decodeBitIndex m hm))).trans_eq
      (by simp)

lemma firstTape_causal {N : ℕ} (m t : ℕ) (hm : 0 < m)
    (h : t * Nat.clog 2 m ≤ N) (ρ τ : Tape N)
    (hpre : (List.ofFn ρ).take
        ((selectBitIndexWithCount m hm t (firstTape m t h ρ)).2 * Nat.clog 2 m) =
      (List.ofFn τ).take
        ((selectBitIndexWithCount m hm t (firstTape m t h ρ)).2 * Nat.clog 2 m)) :
    selectBitIndexWithCount m hm t (firstTape m t h τ) =
      selectBitIndexWithCount m hm t (firstTape m t h ρ) := by
  apply select_prefix
  have hle := Nat.mul_le_mul_right (Nat.clog 2 m) (firstTape_used_le m t hm h ρ)
  rw [firstTape_split m t h ρ, firstTape_split m t h τ] at hpre
  simpa only [List.take_append, tapeBits_length, Nat.sub_eq_zero_of_le hle,
    List.take_zero, List.append_nil] using hpre

lemma sum_firstTape_used_le {N : ℕ} (m t : ℕ) (hm : 0 < m)
    (h : t * Nat.clog 2 m ≤ N) :
    (∑ ρ : Tape N, (selectBitIndexWithCount m hm t (firstTape m t h ρ)).2) ≤
      2 * 2 ^ N := by
  classical
  let E := (splitEquiv h).trans
    (Equiv.prodCongr (LocalFlatLaw.blockTapeBitsEquiv t (Nat.clog 2 m)).symm
      (Equiv.refl (Tape (N-t*Nat.clog 2 m))))
  have heq : (∑ ρ : Tape N,
      (selectBitIndexWithCount m hm t (firstTape m t h ρ)).2) =
      ∑ pair : BitTape m t × Tape (N-t*Nat.clog 2 m), bitTapeAttemptsUsed m t pair.1 := by
    apply Fintype.sum_equiv E
    intro ρ
    simp [E, firstTape, selectBitIndexWithCount_eq]
  rw [heq, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hh := Nat.mul_le_mul_left (Fintype.card (Tape (N-t*Nat.clog 2 m)))
    (sum_bitTapeAttemptsUsed_le_two m hm t)
  have hc := Fintype.card_congr E
  simp only [Fintype.card_prod, card_tape] at hc ⊢
  simp only [card_tape] at hh
  change 2^N = Fintype.card (BitTape m t) * 2^(N-t*Nat.clog 2 m) at hc
  nlinarith

def meanBudget (size : ℕ → ℕ) (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => 42 * Nat.clog 2 (size d)+121 + meanBudget size (d+1) r

lemma sum_charge_le (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (r : ℕ) : ∀ d N,
    (∀ j, d ≤ j → j < d+r → 0 < size j) →
    bitBudget size t d r ≤ N →
    (∑ ρ : Tape N, (charge size t start d r (List.ofFn ρ) : ℚ)) ≤
      (meanBudget size d r : ℚ) * 2^N := by
  classical
  induction r with
  | zero =>
    intro d N hp hb
    have hh (ρ : Tape N) := charge_eq (ClassTrace.done (size := size) (t := t)
      (start := start) d (List.ofFn ρ))
    simp [hh, meanBudget]
  | succ r ih =>
    intro d N hp hb
    have hm : 0 < size d := hp d (by omega) (by omega)
    have hhead : t*Nat.clog 2 (size d) ≤ N := by simp only [bitBudget] at hb; omega
    let used (ρ : Tape N) :=
      (selectBitIndexWithCount (size d) hm t (firstTape (size d) t hhead ρ)).2 *
        Nat.clog 2 (size d)
    have hu (ρ : Tape N) : used ρ ≤ t*Nat.clog 2 (size d) :=
      Nat.mul_le_mul_right _ (firstTape_used_le (size d) t hm hhead ρ)
    have huN (ρ : Tape N) : used ρ ≤ N := (hu ρ).trans hhead
    have hc (ρ τ : Tape N) (he : (List.ofFn ρ).take (used ρ) =
        (List.ofFn τ).take (used ρ)) : used τ = used ρ := by
      exact congrArg (fun z => z.2 * Nat.clog 2 (size d))
        (firstTape_causal (size d) t hm hhead ρ τ he)
    let X (ρ : Tape N) : ℚ := charge size t start (d+1) r ((List.ofFn ρ).drop (used ρ))
    have htailmean : (∑ ρ, X ρ) ≤ (meanBudget size (d+1) r : ℚ)*2^N := by
      have hmean := sum_le_of_stopped_prefix used huN hc X
        (fun _ => (meanBudget size (d+1) r : ℚ)) (by intros; rfl) (by
          intro ρ
          have hx (tail : Tape (N-used ρ)) :
              X ((splitEquiv (huN ρ)).symm ((splitEquiv (huN ρ) ρ).1,tail)) =
              charge size t start (d+1) r (List.ofFn tail) := by
            let τ := (splitEquiv (huN ρ)).symm ((splitEquiv (huN ρ) ρ).1,tail)
            have hpre : (List.ofFn ρ).take (used ρ) = (List.ofFn τ).take (used ρ) := by
              rw [prefix_of_split (huN ρ), prefix_of_split (huN ρ)]
              simp [τ]
            have he := hc ρ τ hpre
            dsimp [X]
            change (charge size t start (d+1) r ((List.ofFn τ).drop (used τ)) : ℚ) = _
            rw [he, boolTape_split (huN ρ) τ]
            simp [τ]
          simp_rw [hx]
          apply ih
          · intro j hj hjr
            exact hp j (by omega) (by omega)
          · have hbound := hu ρ
            simp only [bitBudget] at hb
            omega)
      simpa [Finset.sum_const, card_tape, nsmul_eq_mul, mul_comm] using hmean
    have hpoint (ρ : Tape N) : (charge size t start d (r+1) (List.ofFn ρ) : ℚ) ≤
        (15 * Nat.clog 2 (size d)+30 : ℕ) *
          ((selectBitIndexWithCount (size d) hm t (firstTape (size d) t hhead ρ)).2 : ℚ) +
        (12 * Nat.clog 2 (size d)+61 : ℕ) + X ρ := by
      have hh := charge_step_le size t start d r (firstTape (size d) t hhead ρ)
        (List.ofFn ((splitEquiv hhead ρ).2)) hm
        (fun j hj hjr => hp j (by omega) (by omega))
        (by simp only [List.length_ofFn]; simp only [bitBudget] at hb; omega)
      rw [← firstTape_split (size d) t hhead ρ] at hh
      dsimp [X, used]
      have hhQ := (Nat.cast_le (α := ℚ)).mpr hh
      push_cast at hhQ
      push_cast
      linarith
    have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hpoint ρ)
    have hreads : (∑ ρ : Tape N,
        ((selectBitIndexWithCount (size d) hm t (firstTape (size d) t hhead ρ)).2 : ℚ)) ≤
        2 * 2^N := by exact_mod_cast sum_firstTape_used_le (size d) t hm hhead
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, card_tape, nsmul_eq_mul] at hsum
    simp only [meanBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hmulp := mul_le_mul_of_nonneg_left hreads
      (show (0:ℚ) ≤ (15 * Nat.clog 2 (size d)+30 : ℕ) by positivity)
    push_cast at hsum hmulp
    nlinarith

lemma meanBudget_le_class_sizes (size : ℕ → ℕ) (r : ℕ) :
    ∀ d, (∀ j, d ≤ j → j < d+r → 0 < size j) →
    meanBudget size d r ≤ 163 * ∑ j ∈ Finset.range r, size (d+j) := by
  induction r with
  | zero => intro d hp; simp [meanBudget]
  | succ r ih =>
    intro d hp
    have hm := hp d (by omega) (by omega)
    have hlog : Nat.clog 2 (size d) ≤ size d :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := size d)).le
    have ht := ih (d+1) (fun j hj hjr => hp j (by omega) (by omega))
    rw [Finset.sum_range_succ']
    have he : (∑ j ∈ Finset.range r, size (d+(j+1))) =
        ∑ j ∈ Finset.range r, size (d+1+j) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      omega
    rw [he]
    simp only [meanBudget, Nat.add_zero]
    nlinarith

/-- Actual chronological class-selector charges have a linear mean, even
when successive classes have different bit widths and a cap can fail. -/
lemma sum_actual_charge_le (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r N : ℕ)
    (hp : ∀ j, d ≤ j → j < d+r → 0 < size j)
    (hb : bitBudget size t d r ≤ N)
    (cost : Tape N → ℕ)
    (htrace : ∀ ρ, ∃ v u f, ClassTrace size t start d r (List.ofFn ρ) v u (cost ρ) f) :
    (∑ ρ, cost ρ) ≤ (163 * ∑ j ∈ Finset.range r, size (d+j)) * 2^N := by
  have he (ρ : Tape N) : charge size t start d r (List.ofFn ρ) = cost ρ := by
    obtain ⟨v,u,f,hh⟩ := htrace ρ
    exact charge_eq hh
  have hmean := sum_charge_le size t start r d N hp hb
  simp_rw [he] at hmean
  have hnat : (∑ ρ, cost ρ) ≤ meanBudget size d r * 2^N := by
    exact_mod_cast hmean
  exact hnat.trans (Nat.mul_le_mul_right _ (meanBudget_le_class_sizes size r d hp))

end Lax457868Proofs.ClassTraceMean



