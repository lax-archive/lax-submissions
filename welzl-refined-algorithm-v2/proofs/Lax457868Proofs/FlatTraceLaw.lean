import Lax457868Proofs.ClassRepresentativeTrace
import Lax457868Proofs.SequentialDraws
import Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

/-!
Exact finite laws for the actual successive selectors on a single flat tape.
The first accepted prefix, rather than the whole reserved cap, is consumed.
-/

namespace Lax457868Proofs.FlatTraceLaw

open FairBitIndices StoppingPrefix ClassRepresentativeTrace
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

/-- A flat fair-bit tape of exactly `N` bits. -/
abbrev FlatTape (N : ℕ) := Fin N → Bool

/-- The bit list read from a fixed tape. -/
def flatBits {N : ℕ} (tape : FlatTape N) : List Bool := List.ofFn tape

@[simp] lemma flatBits_length {N : ℕ} (tape : FlatTape N) :
    (flatBits tape).length = N := by simp [flatBits]

/-- Flattening fixed-width blocks is injective, including width zero. -/
lemma tapeBits_injective (L t : ℕ) :
    Function.Injective (tapeBits (L := L) (t := t)) := by
  induction t with
  | zero =>
      intro a b hab
      funext i
      exact i.elim0
  | succ t ih =>
      intro a b hab
      have hfirst : List.ofFn (a 0) = List.ofFn (b 0) := by
        have h := congrArg (List.take L) hab
        simpa [tapeBits_succ] using h
      have hrest : tapeBits (fun i => a i.succ) =
          tapeBits (fun i => b i.succ) := by
        have h := congrArg (List.drop L) hab
        simpa [tapeBits_succ] using h
      have hhead : a 0 = b 0 := List.ofFn_inj.mp hfirst
      have htail := ih hrest
      funext i
      cases i using Fin.cases with
      | zero => exact hhead
      | succ j => exact congrFun htail j

/-- A fixed-length list is a fixed flat tape, without changing bit order. -/
noncomputable def flatBitsEquiv (N : ℕ) :
    FlatTape N ≃ {bits : List Bool // bits.length = N} where
  toFun tape := ⟨flatBits tape, flatBits_length tape⟩
  invFun bits := fun i => bits.1[i.val]'(by simpa [bits.2] using i.isLt)
  left_inv tape := by
    funext i
    simp [flatBits]
  right_inv bits := by
    apply Subtype.ext
    simpa [flatBits, bits.2] using (List.ofFn_getElem (xs := bits.1))

/-- A successful flat stream records each actually consumed stopped prefix.
`attempts` is the vector of positive stopping counts. The remaining `bits`
after each prefix are passed unchanged to the next class. -/
inductive FlatClassSuccess (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ℕ → ℕ → List Bool → List ℕ → List ℕ → Prop
  | done (d : ℕ) (bits : List Bool) :
      FlatClassSuccess size t start d 0 bits [] []
  | step {d r v : ℕ} (i : Fin (size d))
      (pre : BitTape (size d) (v + 1)) (rest : List Bool)
      {values attempts : List ℕ}
      (hm : 0 < size d) (hu : v + 1 ≤ t)
      (hstop : stoppedEvent (size d) hm (v + 1) (v + 1) i pre)
      (hnext : FlatClassSuccess size t start (d + 1) r rest values attempts) :
      FlatClassSuccess size t start d (r + 1)
        (tapeBits pre ++ rest) ((start d + i.val) :: values)
        ((v + 1) :: attempts)

/-- A prescribed vector of successful class outputs and stopping counts. -/
inductive ValidPath (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ℕ → ℕ → List ℕ → List ℕ → Prop
  | done (d : ℕ) : ValidPath size t start d 0 [] []
  | step {d r v : ℕ} (i : Fin (size d))
      {values attempts : List ℕ}
      (hm : 0 < size d) (hu : v + 1 ≤ t)
      (hnext : ValidPath size t start (d + 1) r values attempts) :
      ValidPath size t start d (r + 1)
        ((start d + i.val) :: values) ((v + 1) :: attempts)

/-- A choice of one position from each requested positive class. -/
inductive ValidOutput (size : ℕ → ℕ) (start : ℕ → ℕ) :
    ℕ → ℕ → List ℕ → Prop
  | done (d : ℕ) : ValidOutput size start d 0 []
  | step {d r : ℕ} {values : List ℕ} (i : Fin (size d))
      (hnext : ValidOutput size start (d + 1) r values) :
      ValidOutput size start d (r + 1) ((start d + i.val) :: values)

/-- All length-`r` vectors of possible positive stopping counts. -/
def attemptVectors (t : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | r + 1 => (Finset.Icc 1 t).biUnion fun u =>
      (attemptVectors t r).image (List.cons u)

/-- The Cartesian set of positions in the requested class slices. -/
def outputVectors (size start : ℕ → ℕ) (d : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | r + 1 => (Finset.univ : Finset (Fin (size d))).biUnion fun i =>
      (outputVectors size start (d + 1) r).image
        (List.cons (start d + i.val))

/-- Number of ideal joint output vectors for the fixed class sizes. -/
def outputCount (size : ℕ → ℕ) (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => size d * outputCount size (d + 1) r

lemma ValidOutput.mem_outputVectors (size start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values : List ℕ},
      ValidOutput size start d r values →
      values ∈ outputVectors size start d r
  | _, _, _, .done _ => by simp [outputVectors]
  | _, _, _, .step (d := d) (r := r) i hnext => by
      simp only [outputVectors, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, _,
        ValidOutput.mem_outputVectors size start hnext, rfl⟩

lemma outputVectors.validOutput (size start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values : List ℕ},
      values ∈ outputVectors size start d r →
      ValidOutput size start d r values
  | _, 0, values, hmem => by
      simp only [outputVectors, Finset.mem_singleton] at hmem
      subst values
      exact ValidOutput.done _
  | d, r + 1, values, hmem => by
      obtain ⟨i, _, himage⟩ :=
        Finset.mem_biUnion.mp (by simpa only [outputVectors] using hmem)
      obtain ⟨tail, htail, hvalues⟩ := Finset.mem_image.mp himage
      subst values
      exact ValidOutput.step i
        (outputVectors.validOutput size start htail)

lemma card_outputVectors (size start : ℕ → ℕ) (d r : ℕ) :
    (outputVectors size start d r).card = outputCount size d r := by
  induction r generalizing d with
  | zero => simp [outputVectors, outputCount]
  | succ r ih =>
      classical
      simp only [outputVectors, outputCount]
      rw [Finset.card_biUnion]
      · have hinj (i : Fin (size d)) :
            Function.Injective (List.cons (start d + i.val)) := by
          intro a b h
          exact (List.cons.inj h).2
        apply Eq.trans (Finset.sum_congr rfl (by
          intro i hi
          exact Finset.card_image_of_injective _ (hinj i)))
        rw [Finset.sum_const]
        simp [ih]
      · intro i hi j hj hij
        apply Finset.disjoint_left.mpr
        intro values hvi hvj
        obtain ⟨xs, _, hxs⟩ := Finset.mem_image.mp hvi
        obtain ⟨ys, _, hys⟩ := Finset.mem_image.mp hvj
        have hhead : start d + i.val = start d + j.val := by
          exact (List.cons.inj (hxs.trans hys.symm)).1
        exact hij (Fin.ext (Nat.add_left_cancel hhead))

lemma FlatClassSuccess.validPath (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values attempts : List ℕ},
      FlatClassSuccess size t start d r bits values attempts →
      ValidPath size t start d r values attempts
  | _, _, _, _, _, .done d _ => ValidPath.done d
  | _, _, _, _, _, .step i _ _ hm hu _ hnext =>
      ValidPath.step i hm hu (FlatClassSuccess.validPath size t start hnext)

lemma FlatClassSuccess.attempts_mem (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values attempts : List ℕ},
      FlatClassSuccess size t start d r bits values attempts →
      attempts ∈ attemptVectors t r
  | _, _, _, _, _, .done _ _ => by simp [attemptVectors]
  | _, _, _, _, _, .step (v := v) _ _ _ _ hu _ hnext => by
      simp only [attemptVectors, Finset.mem_biUnion, Finset.mem_image]
      refine ⟨v + 1, Finset.mem_Icc.mpr ⟨by omega, hu⟩, _,
        FlatClassSuccess.attempts_mem size t start hnext, rfl⟩

/-- For a valid output, every vector in the finite attempt range gives a
valid path specification. Zero-cap positive-length ranges are empty. -/
lemma ValidOutput.validPath_of_mem (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values : List ℕ},
      ValidOutput size start d r values →
      ∀ attempts, attempts ∈ attemptVectors t r →
        ValidPath size t start d r values attempts
  | _, _, _, .done d, attempts, hmem => by
      simp only [attemptVectors, Finset.mem_singleton] at hmem
      subst attempts
      exact ValidPath.done d
  | _, _, _, .step (d := d) (r := r) i hnext, attempts, hmem => by
      obtain ⟨u, hu, himage⟩ :=
        Finset.mem_biUnion.mp (by simpa only [attemptVectors] using hmem)
      obtain ⟨us, hus, hlist⟩ := Finset.mem_image.mp himage
      have hu' : 0 < u ∧ u ≤ t := by
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hu
        omega
      obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu'.1)
      subst u
      subst attempts
      exact ValidPath.step i (by have := i.isLt; omega) hu'.2
        (ValidOutput.validPath_of_mem size t start hnext us hus)

lemma ValidPath.validOutput (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values attempts : List ℕ},
      ValidPath size t start d r values attempts →
        ValidOutput size start d r values
  | _, _, _, _, .done d => ValidOutput.done d
  | _, _, _, _, .step i _ _ hnext =>
      ValidOutput.step i (ValidPath.validOutput size t start hnext)

/-- The exact integer weight of one specified successful stopped prefix. -/
def stoppedWeight (size : ℕ → ℕ) (d : ℕ) : List ℕ → ℕ
  | [] => 1
  | u :: us => (rejectedBlocks (size d)).card ^ (u - 1) *
      stoppedWeight size (d + 1) us

/-- The bit count consumed by specified stopped prefixes. -/
def consumedBits (size : ℕ → ℕ) (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | u :: us => u * Nat.clog 2 (size d) + consumedBits size (d + 1) us

/-- The source trace's class-selection charge on a prescribed stopping vector. -/
def chargedCost (size : ℕ → ℕ) (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | u :: us =>
      (15 * Nat.clog 2 (size d) + 30) * u +
        12 * Nat.clog 2 (size d) + 61 + chargedCost size (d + 1) us

/-- A stopped first call followed by any property of its untouched suffix. -/
def stoppedFlatEvent (m : ℕ) (hm : 0 < m) (v : ℕ) (i : Fin m)
    (P : List Bool → Prop) (bits : List Bool) : Prop :=
  ∃ pre : BitTape m (v + 1),
    stoppedEvent m hm (v + 1) (v + 1) i pre ∧
      ∃ rest, bits = tapeBits pre ++ rest ∧ P rest

private lemma flatClassSuccess_inv
    (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    {d r : ℕ} {bits : List Bool} {values attempts : List ℕ}
    (hflat : FlatClassSuccess size t start d (r + 1) bits values attempts) :
    ∃ (v : ℕ) (j : Fin (size d)) (pre : BitTape (size d) (v + 1))
      (rest : List Bool) (xs us : List ℕ),
      values = (start d + j.val) :: xs ∧ attempts = (v + 1) :: us ∧
      bits = tapeBits pre ++ rest ∧
      stoppedEvent (size d) (by have := j.isLt; omega) (v + 1) (v + 1) j pre ∧
      FlatClassSuccess size t start (d + 1) r rest xs us := by
  cases hflat with
  | step j pre rest hm hu hp hnext =>
      exact ⟨_, j, pre, rest, _, _, rfl, rfl, rfl, hp, hnext⟩

private lemma flatClassSuccess_step_iff
    (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r v : ℕ) (i : Fin (size d))
    (values attempts : List ℕ) (bits : List Bool)
    (hm : 0 < size d) (hu : v + 1 ≤ t) :
    FlatClassSuccess size t start d (r + 1) bits
      ((start d + i.val) :: values) ((v + 1) :: attempts) ↔
    stoppedFlatEvent (size d) hm v i
      (fun rest => FlatClassSuccess size t start (d + 1) r rest values attempts)
      bits := by
  constructor
  · intro hflat
    obtain ⟨w, j, pre, rest, xs, us, hvalues, hattempts, hbits, hp, hnext⟩ :=
      flatClassSuccess_inv size t start hflat
    have hheads := (List.cons.inj hvalues).1
    have htails := (List.cons.inj hvalues).2
    have huheads := (List.cons.inj hattempts).1
    have hutails := (List.cons.inj hattempts).2
    have hj : j = i := Fin.ext (Nat.add_left_cancel hheads).symm
    have hw : w = v := by omega
    subst j
    subst w
    subst xs
    subst us
    exact ⟨pre, hp, rest, hbits, hnext⟩
  · rintro ⟨pre, hp, rest, heq, hnext⟩
    rw [heq]
    exact FlatClassSuccess.step i pre rest hm hu hp hnext

/-- Splitting after a fixed number of bits determines both pieces. -/
private lemma fixedPrefix_unique {α : Type*} {xs ys as_ bs : List α}
    (hsize : xs.length = as_.length)
    (h : xs ++ ys = as_ ++ bs) : xs = as_ ∧ ys = bs := by
  have hp := congrArg (List.take xs.length) h
  have hs := congrArg (List.drop xs.length) h
  constructor
  · simpa [hsize] using hp
  · simpa [hsize] using hs

/-- An exact-length stopped event is a product of its stopped prefix and
the full remaining suffix event. This product does not reserve rejected or
unread blocks for subsequent selectors. -/
noncomputable def stoppedFlatEventEquiv
    (m : ℕ) (hm : 0 < m) (v N : ℕ) (i : Fin m)
    (P : List Bool → Prop)
    (hN : (v + 1) * Nat.clog 2 m ≤ N) :
    {bits : List Bool // bits.length = N ∧
      stoppedFlatEvent m hm v i P bits} ≃
    {pre : BitTape m (v + 1) //
      stoppedEvent m hm (v + 1) (v + 1) i pre} ×
    {rest : List Bool // rest.length = N - (v + 1) * Nat.clog 2 m ∧ P rest} where
  toFun bits := by
    let pre := Classical.choose bits.2.2
    have hpre := Classical.choose_spec bits.2.2
    let rest := Classical.choose hpre.2
    have hrest := Classical.choose_spec hpre.2
    refine (⟨pre, hpre.1⟩, ⟨rest, ?_, hrest.2⟩)
    have hlen : (v + 1) * Nat.clog 2 m + rest.length = N := by
      calc
        _ = (tapeBits pre ++ rest).length := by simp [tapeBits_length]
        _ = bits.1.length := congrArg List.length hrest.1.symm
        _ = N := bits.2.1
    omega
  invFun pair := by
    refine ⟨tapeBits pair.1.1 ++ pair.2.1, ?_, ?_⟩
    · rw [List.length_append, tapeBits_length]
      have hlen := pair.2.2.1
      omega
    · exact ⟨pair.1.1, pair.1.2, pair.2.1, rfl, pair.2.2.2⟩
  left_inv bits := by
    apply Subtype.ext
    let pre := Classical.choose bits.2.2
    have hpre := Classical.choose_spec bits.2.2
    let rest := Classical.choose hpre.2
    have hrest := Classical.choose_spec hpre.2
    exact hrest.1.symm
  right_inv pair := by
    let h : stoppedFlatEvent m hm v i P
        (tapeBits pair.1.1 ++ pair.2.1) :=
      ⟨pair.1.1, pair.1.2, pair.2.1, rfl, pair.2.2.2⟩
    let pre := Classical.choose h
    have hpre := Classical.choose_spec h
    let rest := Classical.choose hpre.2
    have hrest := Classical.choose_spec hpre.2
    have heq' : tapeBits pre ++ rest =
        tapeBits pair.1.1 ++ pair.2.1 := hrest.1.symm
    have hparts := fixedPrefix_unique (by simp [tapeBits_length]) heq'
    apply Prod.ext
    · apply Subtype.ext
      exact tapeBits_injective _ _ hparts.1
    · apply Subtype.ext
      exact hparts.2

/-- Exact stopped-prefix factor, with the suffix still subject to `P`. -/
lemma card_stoppedFlatEvent (m : ℕ) (hm : 0 < m) (v N : ℕ)
    (i : Fin m) (P : List Bool → Prop)
    (hN : (v + 1) * Nat.clog 2 m ≤ N) :
    Nat.card {bits : List Bool // bits.length = N ∧
      stoppedFlatEvent m hm v i P bits} =
      (rejectedBlocks m).card ^ v *
        Nat.card {rest : List Bool //
          rest.length = N - (v + 1) * Nat.clog 2 m ∧ P rest} := by
  rw [Nat.card_congr (stoppedFlatEventEquiv m hm v N i P hN),
    Nat.card_prod, card_stoppedPrefix]

/-- There are exactly `2^N` flat fair-bit tapes of length `N`. -/
lemma card_flatBits (N : ℕ) :
    Nat.card {bits : List Bool // bits.length = N} = 2 ^ N := by
  rw [← Nat.card_congr (flatBitsEquiv N), Nat.card_eq_fintype_card]
  simp [FlatTape]

/-- Every valid stopping vector consumes no more than its capped budget. -/
lemma ValidPath.consumedBits_le_budget
    (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values attempts : List ℕ},
      ValidPath size t start d r values attempts →
      consumedBits size d attempts ≤ bitBudget size t d r
  | _, _, _, _, .done _ => by simp [consumedBits, bitBudget]
  | _, _, _, _, .step (d := d) (v := v) i hm hu hnext => by
      have htail := ValidPath.consumedBits_le_budget size t start hnext
      have hmul : (v + 1) * Nat.clog 2 (size d) ≤
          t * Nat.clog 2 (size d) := Nat.mul_le_mul_right _ hu
      simp only [consumedBits, bitBudget]
      omega

/-- For a fixed successful output vector and exact stopping counts, the
actual flat-tape fiber has one factor of `rejectedBlocks.card^v` per class
and every unused bit remains free. In particular the cardinality is
independent of the prescribed indices, even with varying class widths. -/
lemma card_flatClassSuccess (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values attempts : List ℕ},
      (hpath : ValidPath size t start d r values attempts) →
      (N : ℕ) → (hbudget : bitBudget size t d r ≤ N) →
      Nat.card {bits : List Bool // bits.length = N ∧
        FlatClassSuccess size t start d r bits values attempts} =
      stoppedWeight size d attempts *
        2 ^ (N - consumedBits size d attempts) := by
  intro d r values attempts hpath N hbudget
  induction hpath generalizing N with
  | done d =>
      let heq : {bits : List Bool // bits.length = N ∧
          FlatClassSuccess size t start d 0 bits [] []} ≃
          {bits : List Bool // bits.length = N} := {
        toFun := fun bits => ⟨bits.1, bits.2.1⟩
        invFun := fun bits => ⟨bits.1, bits.2, FlatClassSuccess.done d bits.1⟩
        left_inv := by intro bits; rfl
        right_inv := by intro bits; rfl
      }
      rw [Nat.card_congr heq, card_flatBits]
      simp [stoppedWeight, consumedBits]
  | @step d r v i values attempts hm hu hnext ih =>
      let L := Nat.clog 2 (size d)
      change t * L + bitBudget size t (d + 1) r ≤ N at hbudget
      have hfirst : (v + 1) * L ≤ N := by
        have hmul : (v + 1) * L ≤ t * L := Nat.mul_le_mul_right L hu
        omega
      have htailBudget : bitBudget size t (d + 1) r ≤
          N - (v + 1) * L := by
        have hmul : (v + 1) * L ≤ t * L := Nat.mul_le_mul_right L hu
        omega
      have hchar (bits : List Bool) :=
        flatClassSuccess_step_iff size t start d r v i values attempts bits hm hu
      have hcard : Nat.card {bits : List Bool // bits.length = N ∧
          FlatClassSuccess size t start d (r + 1) bits
            ((start d + i.val) :: values) ((v + 1) :: attempts)} =
          Nat.card {bits : List Bool // bits.length = N ∧
            stoppedFlatEvent (size d) hm v i
              (fun rest => FlatClassSuccess size t start (d + 1) r rest values attempts) bits} := by
        let e : {bits : List Bool // bits.length = N ∧
            FlatClassSuccess size t start d (r + 1) bits
              ((start d + i.val) :: values) ((v + 1) :: attempts)} ≃
            {bits : List Bool // bits.length = N ∧
              stoppedFlatEvent (size d) hm v i
                (fun rest => FlatClassSuccess size t start (d + 1) r rest values attempts)
                bits} := {
          toFun := fun bits => ⟨bits.1, bits.2.1, (hchar bits.1).mp bits.2.2⟩
          invFun := fun bits => ⟨bits.1, bits.2.1, (hchar bits.1).mpr bits.2.2⟩
          left_inv := by intro bits; apply Subtype.ext; rfl
          right_inv := by intro bits; apply Subtype.ext; rfl
        }
        exact Nat.card_congr e
      rw [hcard, card_stoppedFlatEvent (size d) hm v N i _ hfirst]
      rw [ih (N - (v + 1) * L) htailBudget]
      simp [stoppedWeight, consumedBits, Nat.sub_sub, L,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_assoc]

private lemma tapeBits_append {m u r : ℕ}
    (pre : BitTape m u) (suffix : BitTape m r) :
    tapeBits (Fin.append pre suffix) = tapeBits pre ++ tapeBits suffix := by
  simp [tapeBits, List.ofFn_fin_append, List.flatMap_append]

private lemma tapeBits_cast {m a b : ℕ} (h : a = b)
    (tape : BitTape m a) :
    tapeBits (tape ∘ Fin.cast h.symm) = tapeBits tape := by
  subst b
  rfl

private lemma selector_cast {m a b : ℕ} (hm : 0 < m) (h : a = b)
    (tape : BitTape m a) :
    selectBitIndexWithCount m hm b (tape ∘ Fin.cast h.symm) =
      selectBitIndexWithCount m hm a tape := by
  subst b
  rfl

private lemma splitTapeBits {m t u : ℕ} (hm : 0 < m) (hu : u ≤ t)
    (tape : BitTape m t) :
    ∃ pre : BitTape m u, ∃ suffix : BitTape m (t - u),
      tapeBits tape = tapeBits pre ++ tapeBits suffix ∧
      (tapeBits tape).drop (u * Nat.clog 2 m) = tapeBits suffix ∧
      selectBitIndexWithCount m hm t tape =
        selectBitIndexWithCount m hm (u + (t - u))
          (Fin.append pre suffix) := by
  let h : u + (t - u) = t := Nat.add_sub_of_le hu
  let pair := splitTapeEquiv m u (t - u) (tape ∘ Fin.cast h)
  refine ⟨pair.1, pair.2, ?_, ?_, ?_⟩
  · have heq := (splitTapeEquiv m u (t - u)).left_inv (tape ∘ Fin.cast h)
    calc
      tapeBits tape = tapeBits (tape ∘ Fin.cast h) := by
        simp only [tapeBits, List.ofFn_congr h.symm tape]
        rfl
      _ = tapeBits (Fin.append pair.1 pair.2) := congrArg tapeBits heq.symm
      _ = _ := tapeBits_append pair.1 pair.2
  · have heq := (splitTapeEquiv m u (t - u)).left_inv (tape ∘ Fin.cast h)
    have hbits : tapeBits tape = tapeBits pair.1 ++ tapeBits pair.2 := by
      calc
        tapeBits tape = tapeBits (tape ∘ Fin.cast h) := by
          simp only [tapeBits, List.ofFn_congr h.symm tape]
          rfl
        _ = tapeBits (Fin.append pair.1 pair.2) := congrArg tapeBits heq.symm
        _ = _ := tapeBits_append pair.1 pair.2
    rw [hbits]
    simp [tapeBits_length]
  · have heq := (splitTapeEquiv m u (t - u)).left_inv (tape ∘ Fin.cast h)
    calc
      selectBitIndexWithCount m hm t tape =
          selectBitIndexWithCount m hm (u + (t - u))
            (tape ∘ Fin.cast h) := by
              simp only [selectBitIndexWithCount, List.ofFn_congr h.symm tape,
                Function.comp_apply]
              rfl
      _ = _ := congrArg (selectBitIndexWithCount m hm (u + (t - u))) heq.symm

/-- The first accepted index and stopping attempt are intrinsic to a flat
bitstream, irrespective of the continuation predicate. -/
private lemma stoppedFlatEvent_head_unique_le
    (m : ℕ) (hm : 0 < m) (v w : ℕ) (i j : Fin m)
    (P Q : List Bool → Prop) (bits : List Bool)
    (hle : v + 1 ≤ w + 1)
    (h₁ : stoppedFlatEvent m hm v i P bits)
    (h₂ : stoppedFlatEvent m hm w j Q bits) :
    v = w ∧ i = j := by
  obtain ⟨pre₁, hp₁, rest₁, heq₁, _⟩ := h₁
  obtain ⟨pre₂, hp₂, rest₂, heq₂, _⟩ := h₂
  obtain ⟨short, suffix, hbits, _, hsel₂⟩ :=
    splitTapeBits hm hle pre₂
  have hprefix : tapeBits pre₁ = tapeBits short := by
    have hsame : tapeBits pre₁ ++ rest₁ =
        tapeBits short ++ (tapeBits suffix ++ rest₂) := by
      calc
        tapeBits pre₁ ++ rest₁ = bits := heq₁.symm
        _ = tapeBits pre₂ ++ rest₂ := heq₂
        _ = _ := by rw [hbits, List.append_assoc]
    exact (fixedPrefix_unique (by simp [tapeBits_length]) hsame).1
  have hpre : pre₁ = short := tapeBits_injective _ _ hprefix
  have hp' : stoppedEvent m hm (w + 1) (v + 1) i pre₂ := by
    have he : selectBitIndexWithCount m hm (v + 1 + ((w + 1) - (v + 1)))
        (Fin.append short suffix) = (some i, v + 1) := by
      apply (stoppedEvent_append_iff m hm v ((w + 1) - (v + 1)) i short suffix).mpr
      simpa only [← hpre] using hp₁
    exact hsel₂.trans he
  have heq : (some i, v + 1) = (some j, w + 1) := hp'.symm.trans hp₂
  have hv : v = w := by
    have := congrArg Prod.snd heq
    omega
  have hij : i = j := Option.some.inj (congrArg Prod.fst heq)
  exact ⟨hv, hij⟩

private lemma stoppedFlatEvent_head_unique
    (m : ℕ) (hm : 0 < m) (v w : ℕ) (i j : Fin m)
    (P Q : List Bool → Prop) (bits : List Bool)
    (h₁ : stoppedFlatEvent m hm v i P bits)
    (h₂ : stoppedFlatEvent m hm w j Q bits) :
    v = w ∧ i = j := by
  rcases le_total (v + 1) (w + 1) with hle | hle
  · exact stoppedFlatEvent_head_unique_le m hm v w i j P Q bits hle h₁ h₂
  · obtain ⟨hw, hji⟩ :=
      stoppedFlatEvent_head_unique_le m hm w v j i Q P bits hle h₂ h₁
    exact ⟨hw.symm, hji.symm⟩

/-- On a fixed flat bitstream the output and every successful stopping
count are unique. This is the disjointness behind summing path fibers. -/
lemma flatClassSuccess_deterministic (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool}
      {values₁ attempts₁ values₂ attempts₂ : List ℕ},
      FlatClassSuccess size t start d r bits values₁ attempts₁ →
      FlatClassSuccess size t start d r bits values₂ attempts₂ →
      values₁ = values₂ ∧ attempts₁ = attempts₂
  | _, _, _, _, _, _, _, .done _ _, h₂ => by
      cases h₂
      simp
  | _, _, _, _, _, _, _, .step (d := d) (r := r) (v := v)
      (values := values₁) (attempts := attempts₁)
      i pre₁ rest₁ hm hu hp₁ hnext₁, h₂ => by
      obtain ⟨w, j, pre₂, rest₂, values₂, attempts₂,
        hvalues₂, hattempts₂, hbits₂, hp₂, hnext₂⟩ :=
        flatClassSuccess_inv size t start h₂
      have hhead := stoppedFlatEvent_head_unique (size d) hm v w i j
        (fun bits => FlatClassSuccess size t start (d + 1) r bits values₁ attempts₁)
        (fun bits => FlatClassSuccess size t start (d + 1) r bits values₂ attempts₂)
        (tapeBits pre₁ ++ rest₁)
        ⟨pre₁, hp₁, rest₁, rfl, hnext₁⟩
        ⟨pre₂, hp₂, rest₂, hbits₂, hnext₂⟩
      rcases hhead with ⟨hw, hj⟩
      subst w
      subst j
      have hparts := fixedPrefix_unique (by simp [tapeBits_length]) hbits₂
      have hrest : rest₁ = rest₂ := hparts.2
      subst rest₂
      obtain ⟨hvalues, hattempts⟩ :=
        flatClassSuccess_deterministic size t start hnext₁ hnext₂
      constructor
      · rw [hvalues₂, hvalues]
      · rw [hattempts₂, hattempts]

/-- Every successful actual class trace decomposes into precisely the
accepted prefixes that it consumed, with all unused bits passed onward. -/
lemma classTrace_success_to_flat (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values : List ℕ}
      {used charge : ℕ} {failed : Bool},
      ClassTrace size t start d r bits values used charge failed →
      failed = false →
      ∃ attempts, FlatClassSuccess size t start d r bits values attempts
  | _, _, _, _, _, _, _, .done d bits, _ =>
      ⟨[], FlatClassSuccess.done d bits⟩
  | _, _, _, _, _, _, _, .failed _ _ _ _ _, hfalse => by
      cases hfalse
  | _, _, _, _, _, _, _, .accepted (d := d) (r := r) (values := values)
      tape tail i u hm hsel hnext, hfalse => by
      obtain ⟨attempts, hflatNext⟩ :=
        classTrace_success_to_flat size t start hnext hfalse
      have hu := (stoppedEvent_bounds (size d) hm t u i tape hsel)
      obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu.1)
      subst u
      obtain ⟨pre, suffix, hbits, hdrop, hsel'⟩ :=
        splitTapeBits hm hu.2 tape
      have hp : stoppedEvent (size d) hm (v + 1) (v + 1) i pre := by
        apply (stoppedEvent_append_iff (size d) hm v (t - (v + 1)) i pre suffix).mp
        exact hsel'.symm.trans hsel
      have hnext' : FlatClassSuccess size t start (d + 1) r
          (tapeBits suffix ++ tail) values attempts := by
        simpa only [hdrop] using hflatNext
      refine ⟨(v + 1) :: attempts, ?_⟩
      have hstep := FlatClassSuccess.step i pre
        (tapeBits suffix ++ tail) hm hu.2 hp hnext'
      simpa only [hbits, List.append_assoc] using hstep

/-- A sequence of consumed successful prefixes gives an execution of the
actual capped class trace whenever the remaining flat tape meets its budget.
The unused part of each cap is re-read as the next class's initial bits. -/
lemma flatClassSuccess_to_classTrace (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values attempts : List ℕ},
      FlatClassSuccess size t start d r bits values attempts →
      bitBudget size t d r ≤ bits.length →
      ∃ used charge, ClassTrace size t start d r bits values used charge false ∧
        used = consumedBits size d attempts ∧
        charge = chargedCost size d attempts
  | _, _, _, _, _, .done d bits, _ =>
      ⟨0, 0, ClassTrace.done d bits, rfl, rfl⟩
  | _, _, _, _, _, .step (d := d) (r := r) (v := v) (values := values)
      i pre rest hm hu hstop hnext, hbudget => by
      let L := Nat.clog 2 (size d)
      have hrest : (t - (v + 1)) * L +
          bitBudget size t (d + 1) r ≤ rest.length := by
        have hlen := tapeBits_length pre
        simp only [bitBudget, List.length_append, hlen] at hbudget
        have hmul : t * L = (v + 1) * L + (t - (v + 1)) * L := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hu]
        dsimp [L] at hmul ⊢
        omega
      have hcap : (t - (v + 1)) * L ≤ rest.length := by omega
      obtain ⟨suffix, tail, hsplit⟩ :=
        splitTape L (t - (v + 1)) rest hcap
      let h : v + 1 + (t - (v + 1)) = t := Nat.add_sub_of_le hu
      let full := Fin.append pre suffix
      let tape : BitTape (size d) t := full ∘ Fin.cast h.symm
      have hbits : tapeBits tape = tapeBits pre ++ tapeBits suffix := by
        calc
          tapeBits tape = tapeBits full := tapeBits_cast h full
          _ = _ := tapeBits_append pre suffix
      have hsel : selectBitIndexWithCount (size d) hm t tape =
          (some i, v + 1) := by
        rw [selector_cast hm h full]
        exact (stoppedEvent_append_iff (size d) hm v (t - (v + 1))
          i pre suffix).mpr hstop
      have hnextBits : (tapeBits tape).drop ((v + 1) * L) ++ tail = rest := by
        rw [hbits]
        simp [L, tapeBits_length, hsplit]
      have hnextBudget : bitBudget size t (d + 1) r ≤ rest.length := by
        omega
      obtain ⟨used, charge, hclassNext, hused, hcharge⟩ :=
        flatClassSuccess_to_classTrace size t start hnext hnextBudget
      have hclassNext' : ClassTrace size t start (d + 1) r
          ((tapeBits tape).drop ((v + 1) * L) ++ tail)
          values used charge false := by
        rw [hnextBits]
        exact hclassNext
      have hclass := ClassTrace.accepted tape tail i (v + 1)
        hm hsel hclassNext'
      have hinput : tapeBits tape ++ tail = tapeBits pre ++ rest := by
        rw [hbits, hsplit]
        simp [List.append_assoc]
      refine ⟨(v + 1) * Nat.clog 2 (size d) + used,
        (15 * Nat.clog 2 (size d) + 30) * (v + 1) +
          12 * Nat.clog 2 (size d) + 61 + charge, ?_, ?_, ?_⟩
      · simpa only [hinput] using hclass
      · simp [consumedBits, hused]
      · simp [chargedCost, hcharge]

/-- Success of the concrete class trace is exactly success of the stopped
prefix stream, for every sufficiently long flat tape. -/
lemma classTrace_success_iff_flat (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r : ℕ) (bits : List Bool) (values : List ℕ)
    (hbudget : bitBudget size t d r ≤ bits.length) :
    (∃ used charge, ClassTrace size t start d r bits values used charge false) ↔
      ∃ attempts, FlatClassSuccess size t start d r bits values attempts := by
  constructor
  · rintro ⟨used, charge, htrace⟩
    exact classTrace_success_to_flat size t start htrace rfl
  · rintro ⟨attempts, hflat⟩
    obtain ⟨used, charge, htrace, _, _⟩ :=
      flatClassSuccess_to_classTrace size t start hflat hbudget
    exact ⟨used, charge, htrace⟩

/-- Every successful constant-modulus `DrawTrace` on its one block stream
has the same consumed-prefix interpretation as the varying-class trace. -/
lemma drawTrace_success_to_flat (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ∀ (d : ℕ) {r : ℕ} {blocks : List (Fin (Nat.clog 2 m) → Bool)}
      {values : List (Fin m)} {used : ℕ} {failed : Bool},
      SequentialDraws.DrawTrace m hm t r blocks values used failed →
      failed = false →
      ∃ attempts,
        FlatClassSuccess (fun _ => m) t (fun _ => 0) d r
          (blocks.flatMap List.ofFn) (values.map Fin.val) attempts
  | d, _, _, _, _, _, .done blocks, _ =>
      ⟨[], FlatClassSuccess.done d (blocks.flatMap List.ofFn)⟩
  | _, _, _, _, _, _, .failed _ _ _ _, hfalse => by cases hfalse
  | d, _, _, _, _, _, .accepted (r := r) (values := values)
      tape tail i u hsel hnext, hfalse => by
      obtain ⟨attempts, hflatNext⟩ :=
        drawTrace_success_to_flat m hm t (d + 1) hnext hfalse
      have hu := stoppedEvent_bounds m hm t u i tape hsel
      obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu.1)
      subst u
      obtain ⟨pre, suffix, hbits, hdrop, hsel'⟩ :=
        splitTapeBits hm hu.2 tape
      have hp : stoppedEvent m hm (v + 1) (v + 1) i pre := by
        apply (stoppedEvent_append_iff m hm v (t - (v + 1)) i pre suffix).mp
        exact hsel'.symm.trans hsel
      have hnextBits :
          (((List.ofFn tape).drop (v + 1) ++ tail).flatMap List.ofFn) =
            tapeBits suffix ++ tail.flatMap List.ofFn := by
        simp only [List.flatMap_append]
        rw [← tapeBits_drop, hdrop]
      have hnext' : FlatClassSuccess (fun _ => m) t (fun _ => 0) (d + 1) r
          (tapeBits suffix ++ tail.flatMap List.ofFn)
          (values.map Fin.val) attempts := by
        simpa only [hnextBits] using hflatNext
      have hstep := FlatClassSuccess.step i pre
        (tapeBits suffix ++ tail.flatMap List.ofFn) hm hu.2 hp hnext'
      refine ⟨(v + 1) :: attempts, ?_⟩
      simp only [List.flatMap_append, List.map_cons]
      change FlatClassSuccess (fun _ => m) t (fun _ => 0) d (r + 1)
        (tapeBits tape ++ tail.flatMap List.ofFn)
        (i.val :: values.map Fin.val) ((v + 1) :: attempts)
      rw [hbits]
      simpa only [zero_add, List.append_assoc] using hstep

/-- Fixed-tape event for a prescribed output and stopping vector. -/
noncomputable def pathFiber (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (values attempts : List ℕ) : Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    FlatClassSuccess size t start d r (flatBits tape) values attempts

/-- Fixed-tape event for an actual successful `ClassTrace` output. -/
noncomputable def outputFiber (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (values : List ℕ) : Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ used charge,
      ClassTrace size t start d r (flatBits tape) values used charge false

private lemma card_pathFiber_eq_natCard (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values attempts : List ℕ) :
    (pathFiber size t start d r N values attempts).card =
      Nat.card {bits : List Bool // bits.length = N ∧
        FlatClassSuccess size t start d r bits values attempts} := by
  classical
  let P : List Bool → Prop := fun bits =>
    FlatClassSuccess size t start d r bits values attempts
  let e : {tape : FlatTape N // P (flatBits tape)} ≃
      {bits : List Bool // bits.length = N ∧ P bits} := {
    toFun := fun tape => ⟨flatBits tape.1, flatBits_length tape.1, tape.2⟩
    invFun := fun bits => ⟨(flatBitsEquiv N).symm ⟨bits.1, bits.2.1⟩,
      by
        have heq : flatBits ((flatBitsEquiv N).symm ⟨bits.1, bits.2.1⟩) = bits.1 :=
          congrArg Subtype.val ((flatBitsEquiv N).apply_symm_apply ⟨bits.1, bits.2.1⟩)
        simpa only [heq] using bits.2.2⟩
    left_inv := by
      intro tape
      apply Subtype.ext
      exact (flatBitsEquiv N).left_inv tape.1
    right_inv := by
      intro bits
      apply Subtype.ext
      change flatBits ((flatBitsEquiv N).symm ⟨bits.1, bits.2.1⟩) = bits.1
      exact congrArg Subtype.val ((flatBitsEquiv N).right_inv ⟨bits.1, bits.2.1⟩)
  }
  change (Finset.univ.filter fun tape : FlatTape N => P (flatBits tape)).card = _
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- The concrete successful output fiber is the disjoint union over all
possible vectors of actual stopping attempts. -/
lemma outputFiber_eq_biUnion (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values : List ℕ)
    (hbudget : bitBudget size t d r ≤ N) :
    outputFiber size t start d r N values =
      (attemptVectors t r).biUnion fun attempts =>
        pathFiber size t start d r N values attempts := by
  classical
  ext tape
  simp only [outputFiber, pathFiber, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion]
  rw [classTrace_success_iff_flat size t start d r (flatBits tape) values
    (by simpa using hbudget)]
  constructor
  · rintro ⟨attempts, hflat⟩
    exact ⟨attempts, FlatClassSuccess.attempts_mem size t start hflat, hflat⟩
  · rintro ⟨attempts, _, hflat⟩
    exact ⟨attempts, hflat⟩

/-- Different stopping vectors have disjoint flat-tape fibers. -/
lemma pathFiber_disjoint (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values : List ℕ)
    {a b : List ℕ} (hab : a ≠ b) :
    Disjoint (pathFiber size t start d r N values a)
      (pathFiber size t start d r N values b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro tape ha hb
  simp only [pathFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hab (flatClassSuccess_deterministic size t start ha hb).2

/-- The integer weight of a prescribed path, or zero when its output or
stopping vector is inadmissible. -/
noncomputable def pathWeight (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (values attempts : List ℕ) : ℕ := by
  classical
  exact if ValidPath size t start d r values attempts then
    stoppedWeight size d attempts * 2 ^ (N - consumedBits size d attempts)
  else 0

/-- The common cardinality of every valid joint output fiber for this
fixed class-size vector and flat-tape length. -/
def jointWeight (size : ℕ → ℕ) (t d r N : ℕ) : ℕ :=
  ∑ attempts ∈ attemptVectors t r,
    stoppedWeight size d attempts *
      2 ^ (N - consumedBits size d attempts)

/-- Exact joint output count for the actual varying-width `ClassTrace` on
one uniform flat tape. Each summand retains its exact consumed-bit count;
the last `N-consumedBits` bits are uniformly unrestricted. -/
theorem card_outputFiber_sum (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values : List ℕ)
    (hbudget : bitBudget size t d r ≤ N) :
    (outputFiber size t start d r N values).card =
      ∑ attempts ∈ attemptVectors t r,
        pathWeight size t start d r N values attempts := by
  classical
  rw [outputFiber_eq_biUnion size t start d r N values hbudget]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro attempts hattempts
    by_cases hpath : ValidPath size t start d r values attempts
    · simp only [pathWeight, hpath, ite_true]
      rw [card_pathFiber_eq_natCard]
      exact card_flatClassSuccess size t start hpath N hbudget
    · simp only [pathWeight, hpath, ite_false]
      have hempty : pathFiber size t start d r N values attempts = ∅ := by
        ext tape
        simp only [pathFiber, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hflat
          exact (hpath (FlatClassSuccess.validPath size t start hflat)).elim
        · intro hmem
          simp at hmem
      simp [hempty]
  · intro a ha b hb hab
    exact pathFiber_disjoint size t start d r N values hab

/-- The actual successive class representatives are jointly uniform on
their valid Cartesian output space, with a subprobability weight that
depends on the fixed class sizes. This is an unconditional flat-tape law:
selector failure contributes the missing mass and is never conditioned away. -/
theorem card_outputFiber_valid (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values : List ℕ)
    (hbudget : bitBudget size t d r ≤ N)
    (hvalid : ValidOutput size start d r values) :
    (outputFiber size t start d r N values).card =
      jointWeight size t d r N := by
  rw [card_outputFiber_sum size t start d r N values hbudget]
  unfold jointWeight
  apply Finset.sum_congr rfl
  intro attempts hattempts
  have hpath := ValidOutput.validPath_of_mem size t start hvalid
    attempts hattempts
  simp [pathWeight, hpath]

/-- Every two valid joint outputs have the same exact flat-tape count. -/
theorem card_outputFiber_eq (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (x y : List ℕ)
    (hbudget : bitBudget size t d r ≤ N)
    (hx : ValidOutput size start d r x)
    (hy : ValidOutput size start d r y) :
    (outputFiber size t start d r N x).card =
      (outputFiber size t start d r N y).card := by
  rw [card_outputFiber_valid size t start d r N x hbudget hx,
    card_outputFiber_valid size t start d r N y hbudget hy]

/-- No concrete successful trace can produce an output outside the ideal
Cartesian product of the requested class slices. -/
theorem card_outputFiber_invalid (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values : List ℕ)
    (hbudget : bitBudget size t d r ≤ N)
    (hinvalid : ¬ ValidOutput size start d r values) :
    (outputFiber size t start d r N values).card = 0 := by
  rw [card_outputFiber_sum size t start d r N values hbudget]
  apply Finset.sum_eq_zero
  intro attempts _
  have hpath : ¬ ValidPath size t start d r values attempts := by
    intro hp
    exact hinvalid (ValidPath.validOutput size t start hp)
  simp [pathWeight, hpath]

/-- All flat tapes on which every requested concrete class call succeeds. -/
noncomputable def successFiber (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) : Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ values used charge,
      ClassTrace size t start d r (flatBits tape) values used charge false

/-- The complementary failed tapes, including failure at any class. -/
noncomputable def failureFiber (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) : Finset (FlatTape N) :=
  Finset.univ \ successFiber size t start d r N

private lemma successFiber_eq_biUnion (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (hbudget : bitBudget size t d r ≤ N) :
    successFiber size t start d r N =
      (outputVectors size start d r).biUnion fun values =>
        outputFiber size t start d r N values := by
  classical
  ext tape
  simp only [successFiber, outputFiber, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion]
  constructor
  · rintro ⟨values, used, charge, htrace⟩
    obtain ⟨attempts, hflat⟩ :=
      classTrace_success_to_flat size t start htrace rfl
    have hvalid := ValidPath.validOutput size t start
      (FlatClassSuccess.validPath size t start hflat)
    exact ⟨values, ValidOutput.mem_outputVectors size start hvalid,
      used, charge, htrace⟩
  · rintro ⟨values, _, used, charge, htrace⟩
    exact ⟨values, used, charge, htrace⟩

private lemma outputFiber_disjoint (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (hbudget : bitBudget size t d r ≤ N)
    {x y : List ℕ} (hxy : x ≠ y) :
    Disjoint (outputFiber size t start d r N x)
      (outputFiber size t start d r N y) := by
  classical
  apply Finset.disjoint_left.mpr
  intro tape hx hy
  simp only [outputFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  obtain ⟨_, hflatX⟩ :=
    (classTrace_success_iff_flat size t start d r (flatBits tape) x
      (by simpa using hbudget)).mp hx
  obtain ⟨_, hflatY⟩ :=
    (classTrace_success_iff_flat size t start d r (flatBits tape) y
      (by simpa using hbudget)).mp hy
  exact hxy (flatClassSuccess_deterministic size t start hflatX hflatY).1

/-- The exact total mass of successful flat tapes. It is the number of
ideal output vectors times their common subprobability numerator. -/
theorem card_successFiber (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (hbudget : bitBudget size t d r ≤ N) :
    (successFiber size t start d r N).card =
      outputCount size d r * jointWeight size t d r N := by
  classical
  rw [successFiber_eq_biUnion size t start d r N hbudget,
    Finset.card_biUnion]
  · calc
      (∑ values ∈ outputVectors size start d r,
        (outputFiber size t start d r N values).card) =
        ∑ _values ∈ outputVectors size start d r,
          jointWeight size t d r N := by
            apply Finset.sum_congr rfl
            intro values hvalues
            exact card_outputFiber_valid size t start d r N values hbudget
              (outputVectors.validOutput size start hvalues)
      _ = outputCount size d r * jointWeight size t d r N := by
        simp [card_outputVectors]
  · intro x hx y hy hxy
    exact outputFiber_disjoint size t start d r N hbudget hxy

/-- For each fixed class-size vector, the successful capped selector is a
subprobability kernel dominated pointwise by the ideal uniform product law.
The inequality is in integer cross-multiplied form: the left side is the
number of ideal outputs times the tapes producing any one valid output, and
`2^N` is the number of fair-bit tapes. It applies separately to each initial
sample determining `size`, without conditioning that sample on success. -/
theorem outputFiber_le_ideal_uniform (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ) (values : List ℕ)
    (hbudget : bitBudget size t d r ≤ N)
    (hvalid : ValidOutput size start d r values) :
    outputCount size d r *
      (outputFiber size t start d r N values).card ≤ 2 ^ N := by
  rw [card_outputFiber_valid size t start d r N values hbudget hvalid]
  rw [← card_successFiber size t start d r N hbudget]
  have hsub : successFiber size t start d r N ⊆
      (Finset.univ : Finset (FlatTape N)) := Finset.subset_univ _
  simpa [FlatTape] using Finset.card_le_card hsub

/-- With no attempts allowed, a requested class has no successful output
on any flat tape, regardless of the unused suffix length. -/
theorem card_outputFiber_zero_cap (size start : ℕ → ℕ)
    (d r N : ℕ) (values : List ℕ)
    (hbudget : bitBudget size 0 d (r + 1) ≤ N) :
    (outputFiber size 0 start d (r + 1) N values).card = 0 := by
  rw [card_outputFiber_sum size 0 start d (r + 1) N values hbudget]
  simp [attemptVectors]

/-- Exact selector-failure deficit for this fixed class-size vector.
In particular the success-conditioned initial sample is weighted by the
sample-specific `jointWeight`; it need not be uniform. -/
theorem card_failureFiber (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r N : ℕ)
    (hbudget : bitBudget size t d r ≤ N) :
    (failureFiber size t start d r N).card =
      2 ^ N - outputCount size d r * jointWeight size t d r N := by
  rw [failureFiber, Finset.card_sdiff, Finset.inter_univ,
    card_successFiber size t start d r N hbudget]
  simp [FlatTape]

private lemma one_validPath (t : ℕ) (ht : 0 < t) (start : ℕ → ℕ) :
    ∀ (d r : ℕ), ∃ values attempts,
      ValidPath (fun _ => 1) t start d r values attempts ∧
      stoppedWeight (fun _ => 1) d attempts = 1 ∧
      consumedBits (fun _ => 1) d attempts = 0
  | d, 0 => ⟨[], [], ValidPath.done d, by simp [stoppedWeight],
      by simp [consumedBits]⟩
  | d, r + 1 => by
      obtain ⟨values, attempts, hpath, hweight, hbits⟩ :=
        one_validPath t ht start (d + 1) r
      refine ⟨start d :: values, 1 :: attempts, ?_, ?_, ?_⟩
      · simpa using ValidPath.step (0 : Fin 1) (by decide) ht hpath
      · simp [stoppedWeight, hweight]
      · simp [consumedBits, hbits]

private lemma bitBudget_one (t d r : ℕ) :
    bitBudget (fun _ => 1) t d r = 0 := by
  induction r generalizing d with
  | zero => rfl
  | succ r ih => simp [bitBudget, ih]

/-- A positive cap on size-one classes consumes no bits and cannot fail.
The statement permits any number of further unread bits on the tape. -/
theorem card_failureFiber_one (t : ℕ) (ht : 0 < t)
    (start : ℕ → ℕ) (d r N : ℕ) :
    (failureFiber (fun _ => 1) t start d r N).card = 0 := by
  classical
  obtain ⟨values, attempts, hpath, hweight, hbits⟩ :=
    one_validPath t ht start d r
  have hbudget : bitBudget (fun _ => 1) t d r ≤ N := by
    simp [bitBudget_one]
  have hpathCard :
      (pathFiber (fun _ => 1) t start d r N values attempts).card = 2 ^ N := by
    rw [card_pathFiber_eq_natCard,
      card_flatClassSuccess (fun _ => 1) t start hpath N hbudget]
    simp [hweight, hbits]
  have hsub : pathFiber (fun _ => 1) t start d r N values attempts ⊆
      successFiber (fun _ => 1) t start d r N := by
    intro tape htape
    have hflat : FlatClassSuccess (fun _ => 1) t start d r
        (flatBits tape) values attempts := by
      simpa [pathFiber] using htape
    obtain ⟨used, charge, htrace, _, _⟩ :=
      flatClassSuccess_to_classTrace (fun _ => 1) t start hflat
        (by simpa using hbudget)
    simp only [successFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨values, used, charge, htrace⟩
  have hsuccess : (successFiber (fun _ => 1) t start d r N).card = 2 ^ N := by
    apply le_antisymm
    · have hle := Finset.card_le_card
        (Finset.subset_univ (successFiber (fun _ => 1) t start d r N))
      simpa [FlatTape] using hle
    · simpa [hpathCard] using Finset.card_le_card hsub
  rw [failureFiber, Finset.card_sdiff, Finset.inter_univ, hsuccess]
  simp [FlatTape]

end Lax457868Proofs.FlatTraceLaw
