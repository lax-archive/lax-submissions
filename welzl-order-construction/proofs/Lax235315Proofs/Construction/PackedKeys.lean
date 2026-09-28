import Lax235315Proofs.Construction.CollisionDetection
import Lax235315Proofs.Construction.KeySampling
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

/-! Packaging the program's eight radix digits as one finite random key. -/

namespace Lax235315Proofs.Construction.PackedKeys

open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.KeySampling
open Lax235315Proofs.Construction.RadixMath

/-- Lexicographic order on natural-number lists, with the first entry most
significant. The lists used below always have the same length. -/
def LexNat : List ℕ → List ℕ → Prop
  | [], [] => False
  | x :: xs, y :: ys => x < y ∨ x = y ∧ LexNat xs ys
  | _, _ => False

/-- Nonstrict lexicographic order, matching `RadixMath.LexOn`. -/
def LexNatLe : List ℕ → List ℕ → Prop
  | [], [] => True
  | x :: xs, y :: ys => x < y ∨ x = y ∧ LexNatLe xs ys
  | _, _ => False

lemma lexNatLe_and_ne_iff_lexNat : ∀ {xs ys : List ℕ},
    xs.length = ys.length →
      (LexNatLe xs ys ∧ xs ≠ ys ↔ LexNat xs ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen
      have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      simp [LexNatLe, LexNat]
  | cons x xs ih =>
      intro ys hlen
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen.symm
      have hlen' : xs.length = ys.length := by simp_all
      constructor
      · rintro ⟨hlex, hne⟩
        rcases hlex with hxy | ⟨hxy, htail⟩
        · exact Or.inl hxy
        · right
          refine ⟨hxy, (ih hlen').mp ⟨htail, ?_⟩⟩
          intro heq
          exact hne (by rw [hxy, heq])
      · intro hlex
        rcases hlex with hxy | ⟨hxy, htail⟩
        · exact ⟨Or.inl hxy, by
            intro heq
            exact (Nat.ne_of_lt hxy) (List.cons.inj heq).1⟩
        · have hrest := (ih hlen').mpr htail
          exact ⟨Or.inr ⟨hxy, hrest.1⟩, by
            intro heq
            exact hrest.2 (List.cons.inj heq).2⟩

/-- Reading a list backwards as little-endian digits is strictly increasing
for the corresponding most-significant-first lexicographic order. -/
lemma ofDigits_reverse_lt_of_lex {q : ℕ} (hq : 1 < q) :
    ∀ {xs ys : List ℕ}, xs.length = ys.length →
      (∀ d ∈ xs, d < q) → (∀ d ∈ ys, d < q) → LexNat xs ys →
      Nat.ofDigits q xs.reverse < Nat.ofDigits q ys.reverse := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen
      have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      simp [LexNat]
  | cons x xs ih =>
      intro ys hlen hxs hys hlex
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen.symm
      have hlen' : xs.length = ys.length := by simp_all
      have hxs' : ∀ d ∈ xs, d < q := fun d hd => hxs d (by simp [hd])
      have hys' : ∀ d ∈ ys, d < q := fun d hd => hys d (by simp [hd])
      have htailX : Nat.ofDigits q xs.reverse < q ^ xs.length := by
        simpa using Nat.ofDigits_lt_base_pow_length hq (l := xs.reverse)
          (fun d hd => hxs' d (by simpa using hd))
      rw [List.reverse_cons, List.reverse_cons,
        Nat.ofDigits_append, Nat.ofDigits_append]
      simp only [Nat.ofDigits_singleton, List.length_reverse]
      rcases hlex with hxy | ⟨rfl, htail⟩
      · calc
          Nat.ofDigits q xs.reverse + q ^ xs.length * x <
              q ^ xs.length + q ^ xs.length * x :=
            Nat.add_lt_add_right htailX _
          _ = q ^ xs.length * (x + 1) := by ring
          _ ≤ q ^ xs.length * y := Nat.mul_le_mul_left _ hxy
          _ ≤ Nat.ofDigits q ys.reverse + q ^ xs.length * y := by omega
          _ = Nat.ofDigits q ys.reverse + q ^ ys.length * y := by rw [hlen']
      · have hlt := ih hlen' hxs' hys' htail
        simpa [hlen'] using Nat.add_lt_add_right hlt (q ^ xs.length * x)

/-- Conversely, strict order of two bounded equal-length base expansions
comes from lexicographic order of their most-significant-first digits. -/
lemma lex_of_ofDigits_reverse_lt {q : ℕ} (hq : 1 < q) :
    ∀ {xs ys : List ℕ}, xs.length = ys.length →
      (∀ d ∈ xs, d < q) → (∀ d ∈ ys, d < q) →
      Nat.ofDigits q xs.reverse < Nat.ofDigits q ys.reverse → LexNat xs ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys hlen
      have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      simp
  | cons x xs ih =>
      intro ys hlen hxs hys hlt
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen.symm
      have hlen' : xs.length = ys.length := by simp_all
      have hxs' : ∀ d ∈ xs, d < q := fun d hd => hxs d (by simp [hd])
      have hys' : ∀ d ∈ ys, d < q := fun d hd => hys d (by simp [hd])
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · exact Or.inl hxy
      · right
        refine ⟨rfl, ih hlen' hxs' hys' ?_⟩
        have hlt' : Nat.ofDigits q xs.reverse + q ^ xs.length * x <
            Nat.ofDigits q ys.reverse + q ^ xs.length * x := by
          simpa [List.reverse_cons, Nat.ofDigits_append, hlen'] using hlt
        omega
      · exfalso
        have hrevLex : LexNat (y :: ys) (x :: xs) := Or.inl hyx
        have hrev := ofDigits_reverse_lt_of_lex hq hlen.symm hys hxs hrevLex
        exact (Nat.not_lt_of_ge hrev.le) hlt

lemma ofDigits_reverse_lt_iff_lex {q : ℕ} (hq : 1 < q)
    {xs ys : List ℕ} (hlen : xs.length = ys.length)
    (hxs : ∀ d ∈ xs, d < q) (hys : ∀ d ∈ ys, d < q) :
    Nat.ofDigits q xs.reverse < Nat.ofDigits q ys.reverse ↔ LexNat xs ys :=
  ⟨lex_of_ofDigits_reverse_lt hq hlen hxs hys,
    ofDigits_reverse_lt_of_lex hq hlen hxs hys⟩

/-- The eight digits in most-significant-first order. -/
def digitList (digits : Fin 8 → ℕ → ℕ) (v : ℕ) : List ℕ :=
  [digits 0 v, digits 1 v, digits 2 v, digits 3 v,
    digits 4 v, digits 5 v, digits 6 v, digits 7 v]

/-- The base-`q` key represented by the eight program digits. -/
def packedKey (q : ℕ) (digits : Fin 8 → ℕ → ℕ) (v : ℕ) : ℕ :=
  Nat.ofDigits q (digitList digits v).reverse

@[simp] lemma digitList_length (digits : Fin 8 → ℕ → ℕ) (v : ℕ) :
    (digitList digits v).length = 8 := rfl

lemma digitList_bounded {q : ℕ} {digits : Fin 8 → ℕ → ℕ} {v : ℕ}
    (h : ∀ d, digits d v < q) : ∀ a ∈ digitList digits v, a < q := by
  intro a ha
  simp only [digitList, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply h

lemma packedKey_lt_pow {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {v : ℕ} (h : ∀ d, digits d v < q) :
    packedKey q digits v < q ^ 8 := by
  apply Nat.ofDigits_lt_base_pow_length hq
  intro a ha
  exact digitList_bounded h a (by simpa [packedKey] using ha)

lemma lexNatLe_digitList_iff {digits : Fin 8 → ℕ → ℕ} {u v : ℕ} :
    LexNatLe (digitList digits u) (digitList digits v) ↔
      LexOn digits digitOrder u v := by
  simp [digitList, digitOrder, LexNatLe, LexOn]

lemma digitList_eq_iff {digits : Fin 8 → ℕ → ℕ} {u v : ℕ} :
    digitList digits u = digitList digits v ↔ AllDigitsEqual digits u v := by
  constructor
  · intro h d
    fin_cases d <;> simp_all [digitList]
  · intro h
    simp only [digitList]
    rw [h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7]

lemma packedKey_lt_iff_lexOn_and_not_equal {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {u v : ℕ}
    (hu : ∀ d, digits d u < q) (hv : ∀ d, digits d v < q) :
    packedKey q digits u < packedKey q digits v ↔
      LexOn digits digitOrder u v ∧ ¬AllDigitsEqual digits u v := by
  rw [packedKey, packedKey, ofDigits_reverse_lt_iff_lex hq
    (digitList_length digits u |>.trans (digitList_length digits v).symm)
    (digitList_bounded hu) (digitList_bounded hv)]
  rw [← lexNatLe_and_ne_iff_lexNat (by simp), lexNatLe_digitList_iff,
    ]
  constructor
  · rintro ⟨hlex, hne⟩
    exact ⟨hlex, fun heq => hne (digitList_eq_iff.mpr heq)⟩
  · rintro ⟨hlex, hne⟩
    exact ⟨hlex, fun heq => hne (digitList_eq_iff.mp heq)⟩

lemma packedKey_eq_iff {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {u v : ℕ}
    (hu : ∀ d, digits d u < q) (hv : ∀ d, digits d v < q) :
    packedKey q digits u = packedKey q digits v ↔ AllDigitsEqual digits u v := by
  rw [packedKey, packedKey]
  constructor
  · intro h
    apply digitList_eq_iff.mp
    apply List.reverse_injective
    exact Nat.ofDigits_inj_of_len_eq hq
      (by simp) (by simpa using digitList_bounded hu)
      (by simpa using digitList_bounded hv) h
  · intro h
    rw [digitList_eq_iff.mpr h]

lemma mem_digitOrder (d : Fin 8) : d ∈ digitOrder := by
  fin_cases d <;> simp [digitOrder]

/-- On the radix-sorted vertex list, absence of an adjacent collision means
the packed keys are injective on every listed vertex. -/
lemma packedKey_injective_on_of_noAdjacent {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hbound : ∀ v ∈ xs, ∀ d, digits d v < q)
    (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise (LexOn digits digitOrder))
    (hcollision : ¬ HasAdjacentEqualDigits digits xs) :
    Set.InjOn (packedKey q digits) {v | v ∈ xs} := by
  intro u hu v hv heq
  obtain ⟨i, hi, hui⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j, hj, hvj⟩ := List.mem_iff_getElem.mp hv
  by_contra huv
  have hij : i ≠ j := by
    intro hij
    subst j
    exact huv (hui.symm.trans hvj)
  have hall : AllDigitsEqual digits u v :=
    (packedKey_eq_iff hq (hbound u hu) (hbound v hv)).mp heq
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have heqd : ∀ d ∈ digitOrder, digits d xs[i] = digits d xs[j] := by
      intro d hd
      simpa [hui, hvj] using hall d
    obtain ⟨k, hk⟩ := exists_adjacent_equal_of_equal_indices hsorted
      hi hj hij' heqd
    apply hcollision
    refine ⟨k.val + 1, by omega, ?_, ?_⟩
    · have hklt := k.isLt
      omega
    · intro d
      have hk0 : k.val < xs.length := by have := k.isLt; omega
      have hk1 : k.val + 1 < xs.length := by have := k.isLt; omega
      simp only [Nat.add_sub_cancel]
      rw [List.getD_eq_getElem _ _ hk0, List.getD_eq_getElem _ _ hk1]
      exact hk d (mem_digitOrder d)
  · have hall' : AllDigitsEqual digits v u := fun d => (hall d).symm
    have heqd : ∀ d ∈ digitOrder, digits d xs[i] = digits d xs[j] := by
      intro d hd
      simpa [hui, hvj] using hall d
    have heqd' : ∀ d ∈ digitOrder, digits d xs[j] = digits d xs[i] := by
      intro d hd
      simpa [hui, hvj] using hall' d
    obtain ⟨k, hk⟩ := exists_adjacent_equal_of_equal_indices hsorted
      hj hi hji' heqd'
    apply hcollision
    refine ⟨k.val + 1, by omega, ?_, ?_⟩
    · have hklt := k.isLt
      omega
    · intro d
      have hk0 : k.val < xs.length := by have := k.isLt; omega
      have hk1 : k.val + 1 < xs.length := by have := k.isLt; omega
      simp only [Nat.add_sub_cancel]
      rw [List.getD_eq_getElem _ _ hk0, List.getD_eq_getElem _ _ hk1]
      exact hk d (mem_digitOrder d)

/-- Collision-free radix output is strictly increasing in the packed key. -/
lemma pairwise_packedKey_lt_of_noAdjacent {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hbound : ∀ v ∈ xs, ∀ d, digits d v < q)
    (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise (LexOn digits digitOrder))
    (hcollision : ¬ HasAdjacentEqualDigits digits xs) :
    xs.Pairwise (fun u v => packedKey q digits u < packedKey q digits v) := by
  have hinj := packedKey_injective_on_of_noAdjacent hq hbound hnodup
    hsorted hcollision
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hiMem : xs[i] ∈ xs := List.getElem_mem hi
  have hjMem : xs[j] ∈ xs := List.getElem_mem hj
  have hlex : LexOn digits digitOrder xs[i] xs[j] :=
    (List.pairwise_iff_getElem.mp hsorted) i j hi hj hij
  have hverticesNe : xs[i] ≠ xs[j] := by
    intro heq
    have := (hnodup.getElem_inj_iff (hi := hi) (hj := hj)).mp heq
    omega
  have hkeysNe : packedKey q digits xs[i] ≠ packedKey q digits xs[j] := by
    intro heq
    exact hverticesNe (hinj hiMem hjMem heq)
  apply (packedKey_lt_iff_lexOn_and_not_equal hq
    (hbound xs[i] hiMem) (hbound xs[j] hjMem)).mpr
  exact ⟨hlex, fun hall => hkeysNe
    ((packedKey_eq_iff hq (hbound xs[i] hiMem) (hbound xs[j] hjMem)).mpr hall)⟩

/-- In a duplicate-free complete list sorted by an injective finite key,
the number of smaller keys at position `i` is exactly `i`. -/
lemma keyRank_eq_index_of_pairwise
    {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ}
    (f : KeyInjection α M) {xs : List α}
    (hcomplete : ∀ x : α, x ∈ xs) (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise fun x y => f.1 x < f.1 y)
    {i : ℕ} (hi : i < xs.length) :
    keyRank f.1 xs[i] = i := by
  have hset : (Finset.univ.filter fun y => f.1 y < f.1 xs[i]) =
      (xs.take i).toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_take_iff_getElem]
    constructor
    · intro hy
      obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp (hcomplete y)
      have hji : j < i := by
        by_contra hnot
        have hij : i ≤ j := Nat.le_of_not_gt hnot
        rcases hij.eq_or_lt with rfl | hij'
        · rw [← hjy] at hy
          exact (lt_irrefl _ hy).elim
        · have hforward := (List.pairwise_iff_getElem.mp hsorted)
              i j hi hj hij'
          rw [hjy] at hforward
          exact (not_lt_of_ge hforward.le hy).elim
      exact ⟨j, by simp [hji, hj], hjy⟩
    · rintro ⟨j, hj, hjy⟩
      have hji : j < i := by omega
      have hjlen : j < xs.length := hji.trans hi
      have hforward := (List.pairwise_iff_getElem.mp hsorted)
        j i hjlen hi hji
      simpa [hjy] using hforward
  unfold keyRank
  rw [hset, List.toFinset_card_of_nodup hnodup.take]
  simp [hi.le]

/-- Therefore the mathematical bottom-`s` key sample is precisely the first
`s` entries of any complete strictly key-sorted list. -/
lemma keySample_eq_take_of_pairwise
    {α : Type*} [Fintype α] [DecidableEq α] {M s : ℕ}
    (f : KeyInjection α M) {xs : List α}
    (hcomplete : ∀ x : α, x ∈ xs) (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise fun x y => f.1 x < f.1 y)
    (hs : s ≤ xs.length) :
    keySample f s = (xs.take s).toFinset := by
  ext x
  simp only [keySample, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset, List.mem_take_iff_getElem]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp (hcomplete x)
    have hrank := keyRank_eq_index_of_pairwise f hcomplete hnodup hsorted hi
    have hxrank : keyRank f.1 x = i := by simpa [hix] using hrank
    rw [hxrank] at hx
    exact ⟨i, by simp [hx, hi], hix⟩
  · rintro ⟨i, hi, hix⟩
    have his : i < s := by omega
    have hilen : i < xs.length := his.trans_le hs
    have hrank := keyRank_eq_index_of_pairwise f hcomplete hnodup hsorted hilen
    have hxrank : keyRank f.1 x = i := by simpa [hix] using hrank
    simpa [hxrank] using his

/-- The collision-free packed keys, indexed by positions in the radix output,
form the `Fin (q^8)` assignment used by the counting argument. -/
def indexKeyInjection {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hbound : ∀ v ∈ xs, ∀ d, digits d v < q)
    (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise (LexOn digits digitOrder))
    (hcollision : ¬ HasAdjacentEqualDigits digits xs) :
    KeyInjection (Fin xs.length) (q ^ 8) := by
  let f : Fin xs.length → Fin (q ^ 8) := fun i =>
    ⟨packedKey q digits xs[i], packedKey_lt_pow hq
      (hbound xs[i] (List.getElem_mem i.isLt))⟩
  refine ⟨f, ?_⟩
  intro i j hij
  apply Fin.ext
  apply (hnodup.getElem_inj_iff (hi := i.isLt) (hj := j.isLt)).mp
  apply packedKey_injective_on_of_noAdjacent hq hbound hnodup hsorted
    hcollision
  · exact List.getElem_mem i.isLt
  · exact List.getElem_mem j.isLt
  · exact Fin.mk.inj hij

lemma indexKeyRank_eq {q : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hbound : ∀ v ∈ xs, ∀ d, digits d v < q)
    (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise (LexOn digits digitOrder))
    (hcollision : ¬ HasAdjacentEqualDigits digits xs)
    (i : Fin xs.length) :
    keyRank (indexKeyInjection hq hbound hnodup hsorted hcollision).1 i = i.val := by
  let f := indexKeyInjection hq hbound hnodup hsorted hcollision
  have hstrict := pairwise_packedKey_lt_of_noAdjacent hq hbound hnodup
    hsorted hcollision
  have hfilter : (Finset.univ.filter fun j : Fin xs.length => f.1 j < f.1 i) =
      Finset.univ.filter fun j : Fin xs.length => j.val < i.val := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hkey
      by_contra hnot
      have hij : i.val ≤ j.val := Nat.le_of_not_gt hnot
      rcases hij.eq_or_lt with heq | hij'
      · have : i = j := Fin.ext heq
        subst j
        exact (lt_irrefl _ hkey).elim
      · have hrev := (List.pairwise_iff_getElem.mp hstrict)
            i.val j.val i.isLt j.isLt hij'
        exact (not_lt_of_ge hrev.le hkey).elim
    · intro hji
      exact (List.pairwise_iff_getElem.mp hstrict)
        j.val i.val j.isLt i.isLt hji
  unfold keyRank
  change (Finset.univ.filter fun j : Fin xs.length => f.1 j < f.1 i).card = i.val
  rw [hfilter]
  rw [← Fintype.card_coe]
  simpa using Fintype.card_fin_lt_of_le i.isLt.le

lemma indexKeySample_eq_range {q s : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hbound : ∀ v ∈ xs, ∀ d, digits d v < q)
    (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise (LexOn digits digitOrder))
    (hcollision : ¬ HasAdjacentEqualDigits digits xs) :
    keySample (indexKeyInjection hq hbound hnodup hsorted hcollision) s =
      Finset.univ.filter fun i : Fin xs.length => i.val < s := by
  ext i
  simp [keySample, indexKeyRank_eq hq hbound hnodup hsorted hcollision]

def indexVertexEmbedding {xs : List ℕ} (hnodup : xs.Nodup) :
    Fin xs.length ↪ ℕ where
  toFun i := xs[i]
  inj' := by
    intro i j hij
    apply Fin.ext
    exact (hnodup.getElem_inj_iff (hi := i.isLt) (hj := j.isLt)).mp hij

/-- Mapping sampled indices back through the radix output recovers exactly
its first `s` vertices. -/
lemma image_indexKeySample_eq_take {q s : ℕ} (hq : 1 < q)
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hbound : ∀ v ∈ xs, ∀ d, digits d v < q)
    (hnodup : xs.Nodup)
    (hsorted : xs.Pairwise (LexOn digits digitOrder))
    (hcollision : ¬ HasAdjacentEqualDigits digits xs)
    (hs : s ≤ xs.length) :
    (keySample (indexKeyInjection hq hbound hnodup hsorted hcollision) s).map
        (indexVertexEmbedding hnodup) = (xs.take s).toFinset := by
  rw [indexKeySample_eq_range hq hbound hnodup hsorted hcollision]
  ext v
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    indexVertexEmbedding, List.mem_toFinset, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, his, rfl⟩
    exact ⟨i.val, by simp [his, i.isLt], rfl⟩
  · rintro ⟨i, hi, hiv⟩
    have his : i < s := hi.trans_le (Nat.min_le_left _ _)
    have hilen : i < xs.length := hi.trans_le (Nat.min_le_right _ _)
    exact ⟨⟨i, hilen⟩, his, by simpa [indexVertexEmbedding] using hiv⟩

end Lax235315Proofs.Construction.PackedKeys
