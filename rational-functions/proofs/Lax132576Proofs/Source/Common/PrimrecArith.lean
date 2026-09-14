/-
# Primitive recursion for the arithmetic of `ℤ` and `ℚ`

**This file is general-purpose: nothing in it is about transducers.**  It supplies the part of
Mathlib's `Primrec`/`Computable` API that Mathlib itself does not have, namely the fact that the
integers and the rationals are `Primcodable` and that their arithmetic -- addition, subtraction,
multiplication, comparison, `gcd`, divisibility, and the construction of a rational from a
numerator and a denominator -- is primitive recursive.  It is stated in Mathlib's own style and
namespaces (`Primrec.int_add`, `Primrec.rat_mul`, …), so that it could be contributed there
unchanged.

The two `Primcodable` instances are built so that their underlying `Encodable` structures are the
ones already in Mathlib (`Int.encodable` and `Rat.instEncodable`); no new encoding of `ℤ` or of `ℚ`
is introduced, and therefore no diamond with the existing instances is created.

* `ℤ` is encoded through `Equiv.intEquivNat`: `Int.ofNat n ↦ 2 * n` and `Int.negSucc n ↦ 2 * n + 1`.
  Every natural number is the code of an integer, so the `Primcodable` structure is obtained from
  `Primcodable.ofEquiv`.  All the arithmetic is then reduced to arithmetic on `ℕ` through the pair
  of natural numbers `(z.toNat, (-z).toNat)`, of which one is always `0` and whose difference is
  `z`.
* `ℚ` is encoded through `Rat.instEncodable`, as `Nat.pair (encode q.num) q.den`; here *not* every
  natural number is a code, and the `Primcodable` structure is established by identifying the codes
  (`Primrec.rat_encode_decode`): `n` is a code exactly when `(Nat.unpair n).2` is positive and
  coprime to the absolute value of the integer coded by `(Nat.unpair n).1`.  Rational arithmetic is
  then reduced to integer arithmetic through `Rat.num`, `Rat.den` and `mkRat`.

Along the way `Nat.gcd` is shown to be primitive recursive (`Primrec.nat_gcd`), which Mathlib also
lacks; the proof is the Euclidean recursion, fed to `Primrec.nat_omega_rec`.
-/
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open Encodable

/-! ## The greatest common divisor -/

open Primrec

namespace Lax132576Proofs.Primrec

open Primrec in
private theorem nat_gcd_aux : Primrec₂ (fun (_ : Unit) (p : ℕ × ℕ) => Nat.gcd p.1 p.2) := by
  refine Primrec.nat_omega_rec _ (m := fun _ p => p.1)
    (l := fun _ p => if p.1 = 0 then [] else [(p.2 % p.1, p.1)])
    (g := fun _ q => if q.1.1 = 0 then some q.1.2 else q.2.head?)
    ((fst.comp snd).to₂) ?_ ?_ ?_ ?_
  · exact (Primrec.ite (PrimrecRel.comp Primrec.eq (fst.comp snd) (const 0)) (const [])
      (list_cons.comp (Primrec₂.pair.comp (Primrec.nat_mod.comp (snd.comp snd) (fst.comp snd))
        (fst.comp snd)) (const []))).to₂
  · exact (Primrec.ite (PrimrecRel.comp Primrec.eq (fst.comp (fst.comp snd)) (const 0))
      (option_some.comp (snd.comp (fst.comp snd)))
      (list_head?.comp (snd.comp snd))).to₂
  · intro a b b' hb'
    by_cases h : b.1 = 0
    · simp [h] at hb'
    · simp [h] at hb'
      subst hb'
      exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
  · intro a b
    by_cases h : b.1 = 0
    · simp [h]
    · simp only [h, if_false, List.map_cons, List.map_nil, List.head?_cons]
      exact congrArg some (Nat.gcd_rec b.1 b.2).symm

/-- The greatest common divisor of two natural numbers is primitive recursive. -/
theorem nat_gcd : Primrec₂ Nat.gcd :=
  (nat_gcd_aux.comp (const ()) (Primrec₂.pair.comp fst snd)).to₂

/-- Coprimality of two natural numbers is primitive recursive. -/
theorem nat_coprime : PrimrecRel Nat.Coprime :=
  (PrimrecRel.comp Primrec.eq (nat_gcd.comp fst snd) (const 1)).of_eq fun _ => Iff.rfl

/-- Divisibility of natural numbers is primitive recursive. -/
theorem nat_dvd : PrimrecRel ((· ∣ ·) : ℕ → ℕ → Prop) :=
  (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp snd fst) (const 0)).of_eq fun p => by
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · simp [h]
    · exact (Nat.dvd_iff_mod_eq_zero (m := p.1) (n := p.2)).symm

end Lax132576Proofs.Primrec

/-! ## The integers -/

/-- The integers are `Primcodable`, with the encoding of `Int.encodable`. -/
instance Lax132576Proofs.Int.primcodable : Primcodable ℤ := Primcodable.ofEquiv ℕ Equiv.intEquivNat

open Primrec

namespace Lax132576Proofs.Primrec

theorem int_encode_ofNat (n : ℕ) : encode (Int.ofNat n) = 2 * n := rfl

theorem int_encode_negSucc (n : ℕ) : encode (Int.negSucc n) = 2 * n + 1 := rfl

theorem int_encode_symm (a : ℕ) : encode (Equiv.intEquivNat.symm a) = a :=
  Equiv.apply_symm_apply _ _

theorem int_toNat_eq (z : ℤ) : z.toNat = if encode z % 2 = 0 then encode z / 2 else 0 := by
  cases z with
  | ofNat n =>
      rw [int_encode_ofNat, if_pos (by omega)]
      show n = 2 * n / 2
      omega
  | negSucc n =>
      rw [int_encode_negSucc, if_neg (by omega)]
      rfl

theorem int_negToNat_eq (z : ℤ) :
    (-z).toNat = if encode z % 2 = 0 then 0 else (encode z + 1) / 2 := by
  cases z with
  | ofNat n =>
      rw [int_encode_ofNat, if_pos (by omega)]
      exact Int.toNat_neg_natCast n
  | negSucc n =>
      rw [int_encode_negSucc, if_neg (by omega)]
      have : -(Int.negSucc n) = ((n + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
      rw [this, Int.toNat_natCast]
      omega

/-- The absolute value of an integer, read off its code. -/
theorem int_natAbs_encode (z : ℤ) : z.natAbs = (encode z + 1) / 2 := by
  have h1 := int_toNat_eq z
  have h2 := int_negToNat_eq z
  have h3 : z.natAbs = z.toNat + (-z).toNat := by omega
  rw [h3, h1, h2]
  split <;> omega

theorem int_toNat : Primrec Int.toNat :=
  (Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.encode (const 2)) (const 0))
    (Primrec.nat_div.comp Primrec.encode (const 2)) (const 0)).of_eq
    fun z => (int_toNat_eq z).symm

theorem int_negToNat : Primrec fun z : ℤ => (-z).toNat :=
  (Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.encode (const 2)) (const 0))
    (const 0)
    (Primrec.nat_div.comp (Primrec.succ.comp Primrec.encode) (const 2))).of_eq
    fun z => (int_negToNat_eq z).symm

theorem int_encode_subNat (m k : ℕ) :
    encode ((m : ℤ) - k) = if k ≤ m then 2 * (m - k) else 2 * (k - m) - 1 := by
  rcases le_or_gt k m with h | h
  · rw [if_pos h]
    have : ((m : ℤ) - k) = Int.ofNat (m - k) := by simp [Int.ofNat_sub h]
    rw [this, int_encode_ofNat]
  · rw [if_neg (by omega)]
    have : ((m : ℤ) - k) = Int.negSucc (k - m - 1) := by
      rw [Int.negSucc_eq]
      have : ((k - m - 1 : ℕ) : ℤ) = (k : ℤ) - m - 1 := by omega
      rw [this]; ring
    rw [this, int_encode_negSucc]
    omega

/-- Building the integer `m - k` out of two natural numbers is primitive recursive. -/
theorem int_subNat : Primrec₂ fun m k : ℕ => (m : ℤ) - k := by
  apply Primrec₂.encode_iff.1
  refine (Primrec.ite (PrimrecRel.comp Primrec.nat_le snd fst)
    (Primrec.nat_mul.comp (const 2) (Primrec.nat_sub.comp fst snd))
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp (const 2) (Primrec.nat_sub.comp snd fst))
      (const 1))).to₂.of_eq ?_
  intro m k
  exact (int_encode_subNat m k).symm

/-- The cast `ℕ → ℤ` is primitive recursive. -/
theorem int_natCast : Primrec (fun n : ℕ => (n : ℤ)) :=
  (int_subNat.comp Primrec.id (const 0)).of_eq fun n => by simp

/-- The absolute value of an integer is primitive recursive. -/
theorem int_natAbs : Primrec Int.natAbs :=
  (Primrec.nat_add.comp int_toNat int_negToNat).of_eq fun z => by omega

/-- Addition of integers is primitive recursive. -/
theorem int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) :=
  (int_subNat.comp (Primrec.nat_add.comp (int_toNat.comp fst) (int_toNat.comp snd))
    (Primrec.nat_add.comp (int_negToNat.comp fst) (int_negToNat.comp snd))).to₂.of_eq
    fun z w => by push_cast; omega

/-- Negation of integers is primitive recursive. -/
theorem int_neg : Primrec (fun z : ℤ => -z) :=
  (int_subNat.comp int_negToNat int_toNat).of_eq fun z => by omega

/-- Subtraction of integers is primitive recursive. -/
theorem int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) :=
  (int_subNat.comp (Primrec.nat_add.comp (int_toNat.comp fst) (int_negToNat.comp snd))
    (Primrec.nat_add.comp (int_negToNat.comp fst) (int_toNat.comp snd))).to₂.of_eq
    fun z w => by push_cast; omega

/-- Multiplication of integers is primitive recursive. -/
theorem int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) :=
  (int_subNat.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (int_toNat.comp fst) (int_toNat.comp snd))
        (Primrec.nat_mul.comp (int_negToNat.comp fst) (int_negToNat.comp snd)))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (int_toNat.comp fst) (int_negToNat.comp snd))
        (Primrec.nat_mul.comp (int_negToNat.comp fst) (int_toNat.comp snd)))).to₂.of_eq
    fun z w => by
      have h1 : ((z.toNat : ℤ) - ((-z).toNat : ℤ)) = z := by omega
      have h2 : ((w.toNat : ℤ) - ((-w).toNat : ℤ)) = w := by omega
      push_cast
      nlinarith [h1, h2]

/-- The order of the integers is primitive recursive. -/
theorem int_le : PrimrecRel ((· ≤ ·) : ℤ → ℤ → Prop) :=
  (PrimrecRel.comp Primrec.nat_le
    (Primrec.nat_add.comp (int_toNat.comp fst) (int_negToNat.comp snd))
    (Primrec.nat_add.comp (int_toNat.comp snd) (int_negToNat.comp fst))).of_eq
    fun p => by omega

/-- The strict order of the integers is primitive recursive. -/
theorem int_lt : PrimrecRel ((· < ·) : ℤ → ℤ → Prop) :=
  (PrimrecRel.comp Primrec.nat_lt
    (Primrec.nat_add.comp (int_toNat.comp fst) (int_negToNat.comp snd))
    (Primrec.nat_add.comp (int_toNat.comp snd) (int_negToNat.comp fst))).of_eq
    fun p => by omega

/-- The greatest common divisor of two integers is primitive recursive. -/
theorem int_gcd : Primrec₂ Int.gcd :=
  (nat_gcd.comp (int_natAbs.comp fst) (int_natAbs.comp snd)).to₂

/-- Divisibility of integers is primitive recursive. -/
theorem int_dvd : PrimrecRel ((· ∣ ·) : ℤ → ℤ → Prop) :=
  (PrimrecRel.comp nat_dvd (int_natAbs.comp fst) (int_natAbs.comp snd)).of_eq fun _ =>
    Int.natAbs_dvd_natAbs

end Lax132576Proofs.Primrec

/-! ## The rationals -/

open Primrec

namespace Lax132576Proofs.Primrec

/-- The type through which `Rat.instEncodable` encodes the rationals. -/
private abbrev RatSig := Σ n : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d }

private theorem decode_int_val (a : ℕ) : (decode (α := ℤ) a) = some (Equiv.intEquivNat.symm a) :=
  rfl

private theorem decode_den (z : ℤ) (b : ℕ) :
    (decode (α := { d : ℕ // 0 < d ∧ z.natAbs.Coprime d }) b)
      = if h : 0 < b ∧ z.natAbs.Coprime b then some ⟨b, h⟩ else none := rfl

private theorem decode_ratSig (a b : ℕ) :
    (decode (α := RatSig) (Nat.pair a b))
      = if h : 0 < b ∧ (Equiv.intEquivNat.symm a).natAbs.Coprime b then
          some ⟨Equiv.intEquivNat.symm a, ⟨b, h⟩⟩ else none := by
  simp only [Encodable.decode_sigma_val, Nat.unpair_pair, decode_int_val, decode_den]
  split <;> simp_all [Nat.Coprime]

/-- The decoding of a rational number from a pair of natural numbers. -/
theorem decode_rat (a b : ℕ) :
    (decode (α := ℚ) (Nat.pair a b))
      = if h : 0 < b ∧ (Equiv.intEquivNat.symm a).natAbs.Coprime b then
          some (Rat.mk' (Equiv.intEquivNat.symm a) b (by omega) h.2) else none := by
  simp only [Encodable.decode_ofEquiv, decode_ratSig]
  split
  · rename_i h
    revert h
    rintro ⟨h1, h2⟩
    rfl
  · simp

/-- A rational number is encoded by the pair of the code of its numerator and its denominator. -/
theorem encode_rat (q : ℚ) : encode q = Nat.pair (encode q.num) q.den := rfl

/-- The natural numbers that are codes of rational numbers. -/
theorem rat_encode_decode (n : ℕ) :
    encode (decode (α := ℚ) n) =
      if 0 < (Nat.unpair n).2 ∧ Nat.Coprime (((Nat.unpair n).1 + 1) / 2) (Nat.unpair n).2
      then n + 1 else 0 := by
  have hn : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := Nat.pair_unpair n
  rw [← hn]
  set a := (Nat.unpair n).1
  set b := (Nat.unpair n).2
  rw [Nat.unpair_pair, decode_rat]
  have habs : (Equiv.intEquivNat.symm a).natAbs = (a + 1) / 2 := by
    rw [int_natAbs_encode, int_encode_symm]
  have hcond : (0 < b ∧ (Equiv.intEquivNat.symm a).natAbs.Coprime b)
      ↔ (0 < b ∧ Nat.Coprime ((a + 1) / 2) b) := by rw [habs]
  split
  · rename_i h
    rw [if_pos (hcond.1 h), Encodable.encode_some, encode_rat]
    show (Nat.pair (encode (Equiv.intEquivNat.symm a)) b).succ = Nat.pair a b + 1
    rw [int_encode_symm]
  · rename_i h
    rw [if_neg (fun hc => h (hcond.2 hc))]
    rfl

/-- The rationals are `Primcodable`, with the encoding of `Rat.instEncodable`. -/
instance Lax132576Proofs.Rat.primcodable : Primcodable ℚ where
  __ := (inferInstance : Encodable ℚ)
  prim := by
    have h : Primrec fun n : ℕ =>
        if 0 < (Nat.unpair n).2 ∧ Nat.Coprime (((Nat.unpair n).1 + 1) / 2) (Nat.unpair n).2
        then n + 1 else 0 := by
      refine Primrec.ite (PrimrecPred.and
        (PrimrecRel.comp Primrec.nat_lt (const 0) (snd.comp Primrec.unpair))
        (PrimrecRel.comp nat_coprime
          (Primrec.nat_div.comp (Primrec.succ.comp (fst.comp Primrec.unpair)) (const 2))
          (snd.comp Primrec.unpair))) Primrec.succ (const 0)
    exact Primrec.nat_iff.1 (h.of_eq fun n => (rat_encode_decode n).symm)

/-- The numerator of a rational number is primitive recursive. -/
theorem rat_num : Primrec Rat.num :=
  Primrec.encode_iff.1 <| (fst.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    rw [encode_rat, Nat.unpair_pair]

/-- The denominator of a rational number is primitive recursive. -/
theorem rat_den : Primrec Rat.den :=
  (snd.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    rw [encode_rat, Nat.unpair_pair]

/-- Splitting an exact integer division into two natural divisions. -/
private theorem int_div_split (n : ℤ) (g : ℕ) (h : (g : ℤ) ∣ n) :
    ((n.toNat / g : ℕ) : ℤ) - (((-n).toNat / g : ℕ) : ℤ) = n / (g : ℤ) := by
  rcases Nat.eq_zero_or_pos g with rfl | hgpos
  · have : n = 0 := by simpa using h
    simp [this]
  · obtain ⟨k, rfl⟩ := h
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hgpos.ne')]
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
      have h1 : ((g : ℤ) * (m : ℤ)) = ((g * m : ℕ) : ℤ) := by push_cast; ring
      rw [h1, Int.toNat_natCast, show (-(((g * m : ℕ)) : ℤ)).toNat = 0 from by simp; positivity,
        Nat.mul_div_cancel_left _ hgpos]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
      have h1 : ((g : ℤ) * (-(m : ℤ))) = -((g * m : ℕ) : ℤ) := by push_cast; ring
      rw [h1, show (-((g * m : ℕ) : ℤ)).toNat = 0 from by simp; positivity, neg_neg,
        Int.toNat_natCast, Nat.mul_div_cancel_left _ hgpos]
      simp

/-- Building a rational number out of an integer numerator and a natural denominator is
primitive recursive. -/
theorem rat_mkRat : Primrec₂ (fun (n : ℤ) (d : ℕ) => mkRat n d) := by
  apply Primrec₂.encode_iff.1
  have hg : Primrec fun p : ℤ × ℕ => Nat.gcd p.2 p.1.natAbs :=
    nat_gcd.comp snd (int_natAbs.comp fst)
  have hnum : Primrec fun p : ℤ × ℕ =>
      if p.2 = 0 then (0 : ℤ)
      else ((p.1.toNat / Nat.gcd p.2 p.1.natAbs : ℕ) : ℤ)
        - (((-p.1).toNat / Nat.gcd p.2 p.1.natAbs : ℕ) : ℤ) :=
    Primrec.ite (PrimrecRel.comp Primrec.eq snd (const 0)) (const 0)
      (int_subNat.comp (Primrec.nat_div.comp (int_toNat.comp fst) hg)
        (Primrec.nat_div.comp (int_negToNat.comp fst) hg))
  have hden : Primrec fun p : ℤ × ℕ => if p.2 = 0 then 1 else p.2 / Nat.gcd p.2 p.1.natAbs :=
    Primrec.ite (PrimrecRel.comp Primrec.eq snd (const 0)) (const 1)
      (Primrec.nat_div.comp snd hg)
  refine (Primrec₂.natPair.comp (Primrec.encode.comp hnum) hden).to₂.of_eq fun n d => ?_
  rw [encode_rat, Rat.num_mkRat, Rat.den_mkRat]
  by_cases hd : d = 0
  · simp [hd]
  · simp only [hd, if_false]
    congr 2
    have hdvd : ((Nat.gcd d n.natAbs : ℕ) : ℤ) ∣ n := by
      refine dvd_trans (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right d n.natAbs)) ?_
      exact Int.natAbs_dvd.2 dvd_rfl
    exact int_div_split n (Nat.gcd d n.natAbs) hdvd

/-- Addition of rationals is primitive recursive. -/
theorem rat_add : Primrec₂ ((· + ·) : ℚ → ℚ → ℚ) := by
  have h : Primrec fun p : ℚ × ℚ =>
      mkRat (p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ)) (p.1.den * p.2.den) :=
    rat_mkRat.comp
      (int_add.comp (int_mul.comp (rat_num.comp fst) (int_natCast.comp (rat_den.comp snd)))
        (int_mul.comp (rat_num.comp snd) (int_natCast.comp (rat_den.comp fst))))
      (Primrec.nat_mul.comp (rat_den.comp fst) (rat_den.comp snd))
  refine h.to₂.of_eq fun q r => ?_
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_eq_iff (by positivity)]
  have e1 := Rat.mul_den_eq_num q
  have e2 := Rat.mul_den_eq_num r
  nlinarith [e1, e2]

/-- Multiplication of rationals is primitive recursive. -/
theorem rat_mul : Primrec₂ ((· * ·) : ℚ → ℚ → ℚ) := by
  have h : Primrec fun p : ℚ × ℚ => mkRat (p.1.num * p.2.num) (p.1.den * p.2.den) :=
    rat_mkRat.comp (int_mul.comp (rat_num.comp fst) (rat_num.comp snd))
      (Primrec.nat_mul.comp (rat_den.comp fst) (rat_den.comp snd))
  refine h.to₂.of_eq fun q r => ?_
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_eq_iff (by positivity), ← Rat.mul_den_eq_num q, ← Rat.mul_den_eq_num r]
  ring

/-- Negation of rationals is primitive recursive. -/
theorem rat_neg : Primrec (fun q : ℚ => -q) := by
  have h : Primrec fun q : ℚ => mkRat (-q.num) q.den :=
    rat_mkRat.comp (int_neg.comp rat_num) rat_den
  refine h.of_eq fun q => ?_
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [Rat.mkRat_eq_div]
  push_cast
  rw [div_eq_iff hq]
  have e1 := Rat.mul_den_eq_num q
  linarith [e1]

/-- Subtraction of rationals is primitive recursive. -/
theorem rat_sub : Primrec₂ ((· - ·) : ℚ → ℚ → ℚ) :=
  (rat_add.comp fst (rat_neg.comp snd)).to₂.of_eq fun q r => by ring

/-- The cast `ℤ → ℚ` is primitive recursive. -/
theorem rat_intCast : Primrec (fun z : ℤ => (z : ℚ)) := by
  have h : Primrec fun z : ℤ => mkRat z 1 := rat_mkRat.comp Primrec.id (const 1)
  exact h.of_eq fun z => by rw [Rat.mkRat_eq_div]; simp

/-- The cast `ℕ → ℚ` is primitive recursive. -/
theorem rat_natCast : Primrec (fun n : ℕ => (n : ℚ)) :=
  (rat_intCast.comp int_natCast).of_eq fun n => by push_cast; rfl

/-- The order of the rationals, in terms of numerators and denominators. -/
theorem rat_le_iff (q r : ℚ) : q ≤ r ↔ q.num * (r.den : ℤ) ≤ r.num * (q.den : ℤ) := by
  have hq : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.pos
  have hr : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.pos
  have hc : (0 : ℚ) < (q.den : ℚ) * (r.den : ℚ) := mul_pos hq hr
  have e1 : (q.den : ℚ) * (r.den : ℚ) * q = (q.num : ℚ) * (r.den : ℚ) := by
    rw [show ((q.den : ℚ) * (r.den : ℚ)) * q = (q * (q.den : ℚ)) * (r.den : ℚ) from by ring,
      Rat.mul_den_eq_num]
  have e2 : (q.den : ℚ) * (r.den : ℚ) * r = (r.num : ℚ) * (q.den : ℚ) := by
    rw [show ((q.den : ℚ) * (r.den : ℚ)) * r = (r * (r.den : ℚ)) * (q.den : ℚ) from by ring,
      Rat.mul_den_eq_num]
  rw [← mul_le_mul_iff_right₀ hc, e1, e2]
  exact_mod_cast Iff.rfl

/-- The order of the rationals is primitive recursive. -/
theorem rat_le : PrimrecRel ((· ≤ ·) : ℚ → ℚ → Prop) :=
  (PrimrecRel.comp int_le
      (int_mul.comp (rat_num.comp fst) (int_natCast.comp (rat_den.comp snd)))
      (int_mul.comp (rat_num.comp snd) (int_natCast.comp (rat_den.comp fst)))).of_eq
    fun p => (rat_le_iff p.1 p.2).symm

end Lax132576Proofs.Primrec
