import Mathlib.Tactic
import Lax457868Proofs.StoppingPrefix

/-!
A finite reference trace for successive classes.  Its input is one flat list
of fair bits.  A successful capped call exposes the unread part of its own
cap to the next class, even when the next class has a different block width.
-/

namespace Lax457868Proofs.ClassRepresentativeTrace

open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam
open Lax457868Proofs.StoppingPrefix

/-- Bits supplied for the worst case of each remaining capped call. -/
def bitBudget (size : ℕ → ℕ) (t d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => t * Nat.clog 2 (size d) + bitBudget size t (d + 1) r

/-- The Boolean form of the source reader's flattened input. -/
def tapeBits {L t : ℕ} (tape : Fin t → Fin L → Bool) : List Bool :=
  (List.ofFn tape).flatMap List.ofFn

lemma tapeBits_length {L t : ℕ} (tape : Fin t → Fin L → Bool) :
    (tapeBits tape).length = t * L := by
  simp [tapeBits, List.length_flatMap, List.sum_ofFn]

lemma tapeBits_words {L t : ℕ} (tape : Fin t → Fin L → Bool) :
    (tapeBits tape).map Bool.toNat = flattenBitBlocks tape := by
  unfold tapeBits flattenBitBlocks
  rw [List.map_flatMap]
  congr 1
  funext a
  simp only [Lax195003.WordRamRandomness.bitTape, List.map_ofFn]
  congr 1
  funext i
  cases h : a i <;> simp [h, Bool.toNat]

lemma tapeBits_succ {L t : ℕ} (tape : Fin (t + 1) → Fin L → Bool) :
    tapeBits tape = List.ofFn (tape 0) ++ tapeBits (fun i => tape i.succ) := by
  simp [tapeBits, List.ofFn_succ]

/-- Split off exactly `t` blocks of width `L` from a flat list.  This is a
proof-side operation and stores no product in a RAM word. -/
lemma splitTape (L t : ℕ) (bits : List Bool) (hlen : t * L ≤ bits.length) :
    ∃ (tape : Fin t → Fin L → Bool) (tail : List Bool),
      bits = tapeBits tape ++ tail := by
  induction t generalizing bits with
  | zero => exact ⟨Fin.elim0, bits, by simp [tapeBits]⟩
  | succ t ih =>
      have hL : L ≤ bits.length := by
        have hs : (t + 1) * L = t * L + L := by ring
        omega
      let first := bits.take L
      have hfirst : first.length = L := by
        simp [first, List.length_take, Nat.min_eq_left hL]
      let head : Fin L → Bool := fun i => first[i.val]'(by simp [hfirst, i.isLt])
      have hhead : List.ofFn head = first := by
        simpa [head, hfirst] using (List.ofFn_getElem (xs := first))
      have htail : t * L ≤ (bits.drop L).length := by
        simp [List.length_drop]
        have hs : (t + 1) * L = t * L + L := by ring
        omega
      obtain ⟨tailTape, tail, hrec⟩ := ih (bits.drop L) htail
      let tape : Fin (t + 1) → Fin L → Bool := Fin.cons head tailTape
      refine ⟨tape, tail, ?_⟩
      calc
        bits = first ++ bits.drop L := (List.take_append_drop L bits).symm
        _ = List.ofFn head ++ tapeBits tailTape ++ tail := by rw [hhead, hrec]; simp [List.append_assoc]
        _ = tapeBits tape ++ tail := by simp [tapeBits_succ, tape]

/-- The number of bits used by a successful call is the number of attempts
actually made times that class's width. -/
private lemma selected_used {m t u : ℕ} (hm : 0 < m)
    (tape : BitTape m t) (i : Fin m)
    (hsel : selectBitIndexWithCount m hm t tape = (some i, u)) : u ≤ t :=
  (stoppedEvent_bounds m hm t u i tape hsel).2

/-- A failed capped call always consumes all `t` attempts. -/
private lemma failed_used {m t u : ℕ} (hm : 0 < m)
    (tape : BitTape m t)
    (hsel : selectBitIndexWithCount m hm t tape = (none, u)) : u = t := by
  have hnone : selectBitIndex m hm t tape = none := by
    have h := congrArg Prod.fst hsel
    simpa [selectBitIndexWithCount_eq m hm t tape] using h
  have hreject := (selectBitIndex_eq_none_iff m hm t tape).mp hnone
  have hcomplete := (selector_complete_rejection_iff m hm t tape).mpr hreject
  exact congrArg Prod.snd (hsel.symm.trans hcomplete)

/-- The actual successive selections. `values` holds each chosen position in
`ord`. `charge` adds `(15*L+30)*u+12*L+61` for every attempted class, where
`u` is its actual attempt count and `L` its own binary width. The constant
`61` covers the size read, log wrapper, lookup, branch, and loop guard. -/
inductive ClassTrace (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ℕ → ℕ → List Bool → List ℕ → ℕ → ℕ → Bool → Prop
  | done (d : ℕ) (bits : List Bool) :
      ClassTrace size t start d 0 bits [] 0 0 false
  | failed {d r : ℕ} (tape : BitTape (size d) t) (tail : List Bool) (u : ℕ)
      (hm : 0 < size d)
      (hsel : selectBitIndexWithCount (size d) hm t tape = (none, u)) :
      ClassTrace size t start d (r + 1)
        (tapeBits tape ++ tail) [] (u * Nat.clog 2 (size d))
        ((15 * Nat.clog 2 (size d) + 30) * u +
          12 * Nat.clog 2 (size d) + 61) true
  | accepted {d r : ℕ} (tape : BitTape (size d) t) (tail : List Bool)
      (i : Fin (size d)) (u : ℕ) {values : List ℕ} {used charge : ℕ}
      {failed : Bool}
      (hm : 0 < size d)
      (hsel : selectBitIndexWithCount (size d) hm t tape = (some i, u))
      (hnext : ClassTrace size t start (d + 1) r
        ((tapeBits tape).drop (u * Nat.clog 2 (size d)) ++ tail)
        values used charge failed) :
      ClassTrace size t start d (r + 1) (tapeBits tape ++ tail)
        ((start d + i.val) :: values)
        (u * Nat.clog 2 (size d) + used)
        ((15 * Nat.clog 2 (size d) + 30) * u +
          12 * Nat.clog 2 (size d) + 61 + charge) failed

/-- Enough actual fair bits construct a trace for all requested classes. -/
lemma trace_exists (size : ℕ → ℕ)
    (t : ℕ) (start : ℕ → ℕ) (d r : ℕ) (bits : List Bool)
    (hpositive : ∀ j, d ≤ j → j < d + r → 0 < size j)
    (hlen : bitBudget size t d r ≤ bits.length) :
    ∃ values used charge failed,
      ClassTrace size t start d r bits values used charge failed := by
  induction r generalizing d bits with
  | zero => exact ⟨[], 0, 0, false, ClassTrace.done d bits⟩
  | succ r ih =>
      have hm : 0 < size d := hpositive d (by omega) (by omega)
      have hfirst : t * Nat.clog 2 (size d) ≤ bits.length := by
        simp only [bitBudget] at hlen
        omega
      obtain ⟨tape, tail, hsplit⟩ :=
        splitTape (Nat.clog 2 (size d)) t bits hfirst
      let choice := selectBitIndexWithCount (size d) hm t tape
      cases hc : choice.1 with
      | none =>
          have hsel : selectBitIndexWithCount (size d) hm t tape =
              (none, choice.2) := by
            cases h : selectBitIndexWithCount (size d) hm t tape with
            | mk a b => simpa [choice, h] using hc
          refine ⟨[], choice.2 * Nat.clog 2 (size d),
            (15 * Nat.clog 2 (size d) + 30) * choice.2 +
              12 * Nat.clog 2 (size d) + 61, true, ?_⟩
          rw [hsplit]
          exact ClassTrace.failed tape tail choice.2 hm hsel
      | some i =>
          have hsel : selectBitIndexWithCount (size d) hm t tape =
              (some i, choice.2) := by
            cases h : selectBitIndexWithCount (size d) hm t tape with
            | mk a b => simpa [choice, h] using hc
          have hu := selected_used hm tape i hsel
          have htail : bitBudget size t (d + 1) r ≤
              ((tapeBits tape).drop (choice.2 * Nat.clog 2 (size d)) ++ tail).length := by
            have hbits : bits.length = t * Nat.clog 2 (size d) + tail.length := by
              rw [hsplit]
              simp [tapeBits_length]
            simp only [bitBudget] at hlen
            simp [tapeBits_length, List.length_drop]
            omega
          obtain ⟨values, used, charge, failed, hnext⟩ :=
            ih (d + 1) ((tapeBits tape).drop
              (choice.2 * Nat.clog 2 (size d)) ++ tail)
              (by
                intro j hjlo hjhi
                exact hpositive j (by omega) (by omega)) htail
          refine ⟨(start d + i.val) :: values,
            choice.2 * Nat.clog 2 (size d) + used,
            (15 * Nat.clog 2 (size d) + 30) * choice.2 +
              12 * Nat.clog 2 (size d) + 61 + charge,
            failed, ?_⟩
          rw [hsplit]
          exact ClassTrace.accepted tape tail i choice.2 hm hsel hnext

/-- The trace stops at the first failure. -/
lemma ClassTrace.length_status (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values : List ℕ}
      {used charge : ℕ} {failed : Bool},
      ClassTrace size t start d r bits values used charge failed →
        values.length ≤ r ∧ (failed = false ↔ values.length = r)
  | _, _, _, _, _, _, _, .done _ _ => by simp
  | _, _, _, _, _, _, _, .failed _ _ _ _ _ => by simp
  | _, _, _, _, _, _, _, .accepted _ _ _ _ _ _ hnext => by
      obtain ⟨hle, hiff⟩ := ClassTrace.length_status size t start hnext
      simp only [List.length_cons]
      constructor
      · omega
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hiff

/-- Every consumed bit belongs to the supplied flat tape. -/
lemma ClassTrace.used_le (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values : List ℕ}
      {used charge : ℕ} {failed : Bool},
      ClassTrace size t start d r bits values used charge failed →
        used ≤ bits.length
  | _, _, _, _, _, _, _, .done _ _ => by simp
  | _, _, _, _, _, _, _, .failed tape tail u hm hsel => by
      have hu : u = t := failed_used hm tape hsel
      simp [hu, tapeBits_length]
  | _, _, _, _, _, _, _, .accepted (d := d) tape tail i u hm hsel hnext => by
      have hnextUsed := ClassTrace.used_le size t start hnext
      have hu : u ≤ t := selected_used hm tape i hsel
      have hmul : u * Nat.clog 2 (size d) ≤
          t * Nat.clog 2 (size d) := Nat.mul_le_mul_right _ hu
      simp only [List.length_append, tapeBits_length] at hnextUsed ⊢
      simp only [List.length_drop, tapeBits_length] at hnextUsed
      omega

/-- With no requested classes, no bit is read or representative chosen. -/
lemma ClassTrace.empty (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    {d : ℕ} {bits : List Bool} {values : List ℕ}
    {used charge : ℕ} {failed : Bool}
    (htrace : ClassTrace size t start d 0 bits values used charge failed) :
    values = [] ∧ used = 0 ∧ charge = 0 ∧ failed = false := by
  cases htrace
  simp

/-- Zero retries fail at the first requested class, without reading a bit. -/
lemma ClassTrace.zero_cap (size : ℕ → ℕ) (start : ℕ → ℕ)
    {d r : ℕ} {bits : List Bool} {values : List ℕ}
    {used charge : ℕ} {failed : Bool}
    (hr : 0 < r)
    (htrace : ClassTrace size 0 start d r bits values used charge failed) :
    values = [] ∧ used = 0 ∧
      charge = 12 * Nat.clog 2 (size d) + 61 ∧ failed = true := by
  cases r with
  | zero => omega
  | succ r =>
      cases htrace with
      | failed tape tail u hm hsel =>
          have hzero := selector_zero (size d) hm tape
          have hu : u = 0 := congrArg Prod.snd (hsel.symm.trans hzero)
          simp [hu]
      | accepted tape tail i u hm hsel hnext =>
          have hzero := selector_zero (size d) hm tape
          rw [hzero] at hsel
          cases hsel

/-- A nonzero cap accepts a singleton class on its first zero-width block. -/
lemma singleton_selector (t : ℕ) (ht : 0 < t) (tape : BitTape 1 t) :
    selectBitIndexWithCount 1 (by decide) t tape =
      (some (0 : Fin 1), 1) := by
  have hdecode : ∀ b : Fin (Nat.clog 2 1) → Bool,
      decodeBitIndex 1 (by decide) b = some (0 : Fin 1) := by
    intro b
    simp [decodeBitIndex, bitBlockValue, Lax195003.WordRamRandomness.bitTape]
  cases t with
  | zero => omega
  | succ t =>
      simp [selectBitIndexWithCount, List.ofFn_succ,
        firstDecodedWithCount, hdecode]

private lemma flatMap_drop_fixed {α β : Type*} (xs : List α)
    (f : α → List β) (L u : ℕ) (hlen : ∀ a, (f a).length = L) :
    (xs.flatMap f).drop (u * L) = (xs.drop u).flatMap f := by
  induction u generalizing xs with
  | zero => simp
  | succ u ih =>
      cases xs with
      | nil => simp
      | cons a xs =>
          have ha := hlen a
          have hdrop : (f a ++ xs.flatMap f).drop (L + u * L) =
              (xs.flatMap f).drop (u * L) := by
            rw [List.drop_append]
            simp [ha]
          simpa [List.flatMap_cons, Nat.succ_mul, ih, Nat.add_comm] using hdrop

lemma tapeBits_drop {L t : ℕ} (tape : Fin t → Fin L → Bool) (u : ℕ) :
    (tapeBits tape).drop (u * L) =
      ((List.ofFn tape).drop u).flatMap List.ofFn := by
  exact flatMap_drop_fixed (List.ofFn tape) List.ofFn L u (by intro a; simp)

lemma tapeWords_drop {L t : ℕ} (tape : Fin t → Fin L → Bool) (u : ℕ) :
    ((tapeBits tape).drop (u * L)).map Bool.toNat =
      flattenBitBlockList ((List.ofFn tape).drop u) := by
  rw [tapeBits_drop]
  let xs := (List.ofFn tape).drop u
  change (xs.flatMap List.ofFn).map Bool.toNat = flattenBitBlockList xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.flatMap_cons, List.map_append, flattenBitBlockList]
      rw [ih]
      congr 1
      simp only [List.map_ofFn, Lax195003.WordRamRandomness.bitTape]
      congr 1
      funext i
      cases h : a i <;> simp [h, Bool.toNat]

end Lax457868Proofs.ClassRepresentativeTrace
