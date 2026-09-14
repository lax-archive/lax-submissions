/-
Map duplicate is a first-order transduction.

The transduction has two copies of every non-separator position of the input
(and one copy of every separator position), labelled by the letter of that
position; inside a block, all first copies come before all second copies, and
the blocks keep their order.  This turns the input `w₁ # ⋯ # wₙ` into
`w₁w₁ # ⋯ # wₙwₙ`.

This is one of the ingredients of the easy inclusion of Theorem
`nolabel:thm-fo-transduction-into-primes`. -/
import Lax314295Proofs.Source.PartC.BlockForm
import Lax314295Proofs.Source.PartC.ITransBuild
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace FODup

open RegPair

variable {A₀ : Type}

/-! ## The order in which map duplicate reads the input -/

/-- The elements selected by the transduction: the first copy of every position
and the second copy of every non-separator position. -/
def dupSel (w : List (Option A₀)) (x : Bool × ℕ) : Prop :=
  x.2 < w.length ∧ (x.1 = false ∨ ¬ SepAt w x.2)

/-- The order in which the output of map duplicate reads the (two copies of
the) positions of the input: inside a block all first copies come before all
second copies, and otherwise the order is the order of the input. -/
def dupOrd (w : List (Option A₀)) : Bool × ℕ → Bool × ℕ → Prop
  | (false, p), (false, q) => p ≤ q
  | (true, p), (true, q) => p ≤ q
  | (false, p), (true, q) => SameBlk w p q ∨ p ≤ q
  | (true, p), (false, q) => ¬ SameBlk w p q ∧ p ≤ q

lemma dupOrd_refl (w : List (Option A₀)) (x : Bool × ℕ) : dupOrd w x x := by
  obtain ⟨c, p⟩ := x
  cases c
  · exact le_refl _
  · exact le_refl _

lemma dupOrd_antisymm {w : List (Option A₀)} {x y : Bool × ℕ} (hx : dupSel w x)
    (hy : dupSel w y) (h₁ : dupOrd w x y) (h₂ : dupOrd w y x) : x = y := by
  obtain ⟨c, p⟩ := x
  obtain ⟨c', q⟩ := y
  cases c <;> cases c'
  · have : p = q := le_antisymm h₁ h₂
    rw [this]
  · -- `(false, p)` and `(true, q)`
    have hns : ¬ SameBlk w q p := h₂.1
    have hpq : p ≤ q := by
      rcases h₁ with h | h
      · exact absurd (sameBlk_symm h) hns
      · exact h
    have hpq' : p = q := le_antisymm hpq h₂.2
    subst hpq'
    exact absurd (sameBlk_self_iff.2 ⟨hy.1, by
      rcases hy.2 with h | h
      · exact absurd h (by simp)
      · exact h⟩) hns
  · have hns : ¬ SameBlk w p q := h₁.1
    have hqp : q ≤ p := by
      rcases h₂ with h | h
      · exact absurd (sameBlk_symm h) hns
      · exact h
    have hpq' : p = q := le_antisymm h₁.2 hqp
    subst hpq'
    exact absurd (sameBlk_self_iff.2 ⟨hx.1, by
      rcases hx.2 with h | h
      · exact absurd h (by simp)
      · exact h⟩) hns
  · have : p = q := le_antisymm h₁ h₂
    rw [this]

lemma dupOrd_trans {w : List (Option A₀)} {x y z : Bool × ℕ} (hz : z.2 < w.length)
    (h₁ : dupOrd w x y) (h₂ : dupOrd w y z) : dupOrd w x z := by
  obtain ⟨c, p⟩ := x
  obtain ⟨c', q⟩ := y
  obtain ⟨c'', r⟩ := z
  simp only at hz
  cases c <;> cases c' <;> cases c''
  · exact le_trans (show p ≤ q from h₁) (show q ≤ r from h₂)
  · -- `(false,p) ≤ (false,q) ≤ (true,r)`
    have h₁' : p ≤ q := h₁
    rcases (show SameBlk w q r ∨ q ≤ r from h₂) with hs | hle
    · rcases le_total p r with h | h
      · exact Or.inr h
      · have hqp : SameBlk w q p := sameBlk_of_between hs (by omega) (by omega)
        exact Or.inl (sameBlk_trans (sameBlk_symm hqp) hs)
    · exact Or.inr (by omega)
  · -- `(false,p) ≤ (true,q) ≤ (false,r)`
    have h₂a : ¬ SameBlk w q r := h₂.1
    have h₂b : q ≤ r := h₂.2
    rcases (show SameBlk w p q ∨ p ≤ q from h₁) with hs | hle
    · exact le_of_sameBlk_of_not_sameBlk hs h₂a h₂b
    · exact le_trans hle h₂b
  · -- `(false,p) ≤ (true,q) ≤ (true,r)`
    have h₂' : q ≤ r := h₂
    rcases le_total p r with h | h
    · exact Or.inr h
    · rcases (show SameBlk w p q ∨ p ≤ q from h₁) with hs | hle
      · exact Or.inl (sameBlk_of_between hs (by omega) (by omega))
      · exact Or.inr (by omega)
  · -- `(true,p) ≤ (false,q) ≤ (false,r)`
    have h₁a : ¬ SameBlk w p q := h₁.1
    have h₁b : p ≤ q := h₁.2
    have h₂' : q ≤ r := h₂
    exact ⟨fun hs => h₁a (sameBlk_of_between hs (by omega) (by omega)), by omega⟩
  · -- `(true,p) ≤ (false,q) ≤ (true,r)`
    have h₁a : ¬ SameBlk w p q := h₁.1
    have h₁b : p ≤ q := h₁.2
    rcases (show SameBlk w q r ∨ q ≤ r from h₂) with hs | hle
    · exact le_of_not_sameBlk_of_sameBlk h₁a hs h₁b
    · exact le_trans h₁b hle
  · -- `(true,p) ≤ (true,q) ≤ (false,r)`
    have h₁' : p ≤ q := h₁
    have h₂a : ¬ SameBlk w q r := h₂.1
    have h₂b : q ≤ r := h₂.2
    refine ⟨fun hs => ?_, by omega⟩
    have hxy : SameBlk w p q := sameBlk_of_between hs (by omega) (by omega)
    exact h₂a (sameBlk_trans (sameBlk_symm hxy) hs)
  · exact le_trans (show p ≤ q from h₁) (show q ≤ r from h₂)

lemma dupOrd_total (w : List (Option A₀)) (x y : Bool × ℕ) :
    dupOrd w x y ∨ dupOrd w y x := by
  obtain ⟨c, p⟩ := x
  obtain ⟨c', q⟩ := y
  cases c <;> cases c'
  · exact le_total p q
  · by_cases hs : SameBlk w p q
    · exact Or.inl (Or.inl hs)
    · rcases le_total p q with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨fun h' => hs (sameBlk_symm h'), h⟩
  · by_cases hs : SameBlk w q p
    · exact Or.inr (Or.inl hs)
    · rcases le_total p q with h | h
      · exact Or.inl ⟨fun h' => hs (sameBlk_symm h'), h⟩
      · exact Or.inr (Or.inr h)
  · exact le_total p q

/-! ## The enumeration of the copies in the output order -/

/-- The copies of the positions of `w` can be enumerated in the order in which
map duplicate outputs them, with the labels of the output string. -/
def DupEnum (w : List (Option A₀)) : Prop :=
  ∃ es : List (Bool × ℕ), es.Nodup ∧ (∀ x, x ∈ es ↔ dupSel w x) ∧
    es.Pairwise (dupOrd w) ∧
    List.Forall₂ (fun (x : Bool × ℕ) (a : Option A₀) => w[x.2]? = some a) es
      (mapDuplicate A₀ w)

lemma dupEnum_map_some (b : List A₀) : DupEnum (b.map some) := by
  refine ⟨(List.range b.length).map (fun p => (false, p)) ++
    (List.range b.length).map (fun p => (true, p)), ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨List.nodup_range.map (fun p q h => by simpa using h),
      List.nodup_range.map (fun p q h => by simpa using h), ?_⟩
    intro a ha c hc
    simp only [List.mem_map, List.mem_range] at ha hc
    obtain ⟨p, -, rfl⟩ := ha
    obtain ⟨q, -, rfl⟩ := hc
    simp
  · rintro ⟨c, p⟩
    simp only [List.mem_append, List.mem_map, List.mem_range, dupSel, List.length_map,
      Prod.mk.injEq]
    constructor
    · rintro (⟨q, hq, rfl, rfl⟩ | ⟨q, hq, rfl, rfl⟩)
      · exact ⟨hq, Or.inl rfl⟩
      · exact ⟨hq, Or.inr (not_sepAt_map_some b q)⟩
    · rintro ⟨hp, -⟩
      cases c
      · exact Or.inl ⟨p, hp, rfl, rfl⟩
      · exact Or.inr ⟨p, hp, rfl, rfl⟩
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := b.length))
      intro p q h
      exact le_of_lt h
    · rw [List.pairwise_map]
      refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := b.length))
      intro p q h
      exact le_of_lt h
    · intro a ha c hc
      simp only [List.mem_map, List.mem_range] at ha hc
      obtain ⟨p, hp, rfl⟩ := ha
      obtain ⟨q, hq, rfl⟩ := hc
      exact Or.inl ((sameBlk_map_some_iff b p q).2 ⟨hp, hq⟩)
  · rw [show mapDuplicate A₀ (b.map some) = (b ++ b).map some from
      mapLift_map_some (fun u => u ++ u) b, List.map_append]
    refine forall₂_append ?_ ?_ <;>
      · rw [List.forall₂_map_left_iff, List.forall₂_iff_get]
        refine ⟨by simp, fun k h₁ h₂ => ?_⟩
        simp only [List.length_range] at h₁
        simp only [List.get_eq_getElem, List.getElem_range]
        rw [List.getElem?_eq_getElem (by simpa using h₁)]

lemma dupEnum_cons {b : List A₀} {w' : List (Option A₀)} (h : DupEnum w') :
    DupEnum (b.map some ++ none :: w') := by
  obtain ⟨es, hnd, hmem, hord, hlab⟩ := h
  have hlen : (b.map some ++ none :: w').length = b.length + 1 + w'.length :=
    length_block_decomp b w'
  set w := b.map some ++ none :: w' with hw
  set P1 : List (Bool × ℕ) := (List.range b.length).map (fun p => ((false, p) : Bool × ℕ))
    with hP1
  set P2 : List (Bool × ℕ) := (List.range b.length).map (fun p => ((true, p) : Bool × ℕ))
    with hP2
  set P3 : List (Bool × ℕ) :=
    (false, b.length) :: es.map (fun x => ((x.1, b.length + 1 + x.2) : Bool × ℕ)) with hP3
  have memP1 : ∀ (c : Bool) (p : ℕ), (c, p) ∈ P1 ↔ (c = false ∧ p < b.length) := by
    intro c p
    constructor
    · intro h
      obtain ⟨q, hq, hqx⟩ := List.mem_map.1 h
      injection hqx with h1 h2
      subst h1; subst h2
      exact ⟨rfl, List.mem_range.1 hq⟩
    · rintro ⟨rfl, hp⟩
      exact List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩
  have memP2 : ∀ (c : Bool) (p : ℕ), (c, p) ∈ P2 ↔ (c = true ∧ p < b.length) := by
    intro c p
    constructor
    · intro h
      obtain ⟨q, hq, hqx⟩ := List.mem_map.1 h
      injection hqx with h1 h2
      subst h1; subst h2
      exact ⟨rfl, List.mem_range.1 hq⟩
    · rintro ⟨rfl, hp⟩
      exact List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩
  have memP3 : ∀ (c : Bool) (p : ℕ), (c, p) ∈ P3 ↔
      ((c = false ∧ p = b.length) ∨ ∃ q, (c, q) ∈ es ∧ p = b.length + 1 + q) := by
    intro c p
    constructor
    · intro h
      rcases List.mem_cons.1 h with h' | h'
      · injection h' with h1 h2
        exact Or.inl ⟨h1, h2⟩
      · obtain ⟨⟨c', q⟩, hq, hqx⟩ := List.mem_map.1 h'
        injection hqx with h1 h2
        subst h1; subst h2
        exact Or.inr ⟨q, hq, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨(c, q), hq, rfl⟩)
  refine ⟨P1 ++ P2 ++ P3, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hP1]
      exact List.nodup_range.map (fun p q h => by simpa using h)
    · rw [hP2]
      exact List.nodup_range.map (fun p q h => by simpa using h)
    · rintro ⟨c, p⟩ ha ⟨c', q⟩ hc
      have h1 := (memP1 c p).1 ha
      have h2 := (memP2 c' q).1 hc
      intro hEq
      injection hEq with e1 _
      rw [h1.1, h2.1] at e1
      exact absurd e1 (by simp)
    · rw [hP3, List.nodup_cons]
      constructor
      · intro hmemx
        obtain ⟨⟨c, q⟩, hq, hqx⟩ := List.mem_map.1 hmemx
        injection hqx with _ h2
        omega
      · refine hnd.map ?_
        rintro ⟨c, p⟩ ⟨c', q⟩ hxy
        injection hxy with e1 e2
        simp only [Prod.mk.injEq]
        exact ⟨e1, by omega⟩
    · rintro ⟨c, p⟩ ha ⟨c', q⟩ hc
      rcases List.mem_append.1 ha with h' | h'
      · have h1 := (memP1 c p).1 h'
        rcases (memP3 c' q).1 hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩ <;>
          · intro hEq
            injection hEq with _ e2
            omega
      · have h1 := (memP2 c p).1 h'
        rcases (memP3 c' q).1 hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩ <;>
          · intro hEq
            injection hEq with _ e2
            omega
  · rintro ⟨c, p⟩
    rw [List.mem_append, List.mem_append, memP1, memP2, memP3]
    constructor
    · rintro ((⟨rfl, hp⟩ | ⟨rfl, hp⟩) | ⟨rfl, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact ⟨by rw [hlen]; omega, Or.inl rfl⟩
      · exact ⟨by rw [hlen]; omega, Or.inr (not_sepAt_block_left b w' hp)⟩
      · exact ⟨by rw [hlen]; omega, Or.inl rfl⟩
      · have hsel := (hmem (c, q)).1 hq
        have hq' : q < w'.length := hsel.1
        refine ⟨by rw [hlen]; omega, ?_⟩
        rcases hsel.2 with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (fun hs => h'' ((sepAt_block_right b w' q).1 hs))
    · rintro ⟨hp, hc⟩
      rw [hlen] at hp
      rcases lt_trichotomy p b.length with hlt | heq | hgt
      · cases c
        · exact Or.inl (Or.inl ⟨rfl, hlt⟩)
        · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
      · subst heq
        cases c
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · rcases hc with h'' | h''
          · exact absurd h'' (by simp)
          · exact absurd (sepAt_block_mid b w') h''
      · have hq' : p - (b.length + 1) < w'.length := by omega
        have hsel : dupSel w' (c, p - (b.length + 1)) := by
          refine ⟨hq', ?_⟩
          rcases hc with h'' | h''
          · exact Or.inl h''
          · refine Or.inr (fun hs => h'' ?_)
            have hp2 : p = b.length + 1 + (p - (b.length + 1)) := by omega
            rw [hp2, sepAt_block_right]
            exact hs
        exact Or.inr (Or.inr ⟨p - (b.length + 1), (hmem _).2 hsel, by omega⟩)
  · rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hP1, List.pairwise_map]
      refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := b.length))
      intro p q h
      exact (show p ≤ q from le_of_lt h)
    · rw [hP2, List.pairwise_map]
      refine List.Pairwise.imp ?_ (List.pairwise_lt_range (n := b.length))
      intro p q h
      exact (show p ≤ q from le_of_lt h)
    · rintro ⟨c, p⟩ ha ⟨c', q⟩ hc
      obtain ⟨rfl, hp⟩ := (memP1 c p).1 ha
      obtain ⟨rfl, hq⟩ := (memP2 c' q).1 hc
      exact Or.inl (sameBlk_block_left b w' hp hq)
    · rw [hP3, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · rintro ⟨c, p⟩ ha
        obtain ⟨⟨c', q⟩, hq, hqx⟩ := List.mem_map.1 ha
        injection hqx with e1 e2
        subst e1; subst e2
        cases c'
        · exact (show b.length ≤ b.length + 1 + q by omega)
        · exact Or.inr (show b.length ≤ b.length + 1 + q by omega)
      · rw [List.pairwise_map]
        refine hord.imp_of_mem ?_
        rintro ⟨c, p⟩ ⟨c', q⟩ - - hpq
        cases c <;> cases c'
        · exact (show b.length + 1 + p ≤ b.length + 1 + q from by
            have : p ≤ q := hpq
            omega)
        · rcases (show SameBlk w' p q ∨ p ≤ q from hpq) with hs | hle
          · exact Or.inl ((sameBlk_block_right b w' p q).2 hs)
          · exact Or.inr (show b.length + 1 + p ≤ b.length + 1 + q by omega)
        · refine ⟨fun hs => hpq.1 ((sameBlk_block_right b w' p q).1 hs), ?_⟩
          have hle : p ≤ q := hpq.2
          exact (show b.length + 1 + p ≤ b.length + 1 + q by omega)
        · exact (show b.length + 1 + p ≤ b.length + 1 + q from by
            have : p ≤ q := hpq
            omega)
    · rintro ⟨c, p⟩ ha ⟨c', q⟩ hc
      rcases List.mem_append.1 ha with h' | h'
      · obtain ⟨rfl, hp⟩ := (memP1 c p).1 h'
        rcases (memP3 c' q).1 hc with ⟨rfl, rfl⟩ | ⟨r, -, rfl⟩
        · exact (show p ≤ b.length by omega)
        · cases c'
          · exact (show p ≤ b.length + 1 + r by omega)
          · exact Or.inr (show p ≤ b.length + 1 + r by omega)
      · obtain ⟨rfl, hp⟩ := (memP2 c p).1 h'
        rcases (memP3 c' q).1 hc with ⟨rfl, rfl⟩ | ⟨r, -, rfl⟩
        · exact ⟨not_sameBlk_block_cross b w' hp (le_refl _), show p ≤ b.length by omega⟩
        · cases c'
          · exact ⟨not_sameBlk_block_cross b w' hp (by omega),
              show p ≤ b.length + 1 + r by omega⟩
          · exact (show p ≤ b.length + 1 + r by omega)
  · rw [hw, show mapDuplicate A₀ (b.map some ++ none :: w') =
      (b ++ b).map some ++ none :: mapDuplicate A₀ w' from
      mapLift_map_some_cons_none (fun u => u ++ u) b w', List.map_append]
    rw [hP1, hP2, hP3]
    refine forall₂_append (forall₂_append ?_ ?_) (List.Forall₂.cons ?_ ?_)
    · rw [List.forall₂_map_left_iff, List.forall₂_iff_get]
      refine ⟨by simp, fun k h₁ h₂ => ?_⟩
      simp only [List.length_range] at h₁
      simp only [List.get_eq_getElem, List.getElem_range]
      rw [getElem?_block_left b w' h₁]
      simp
    · rw [List.forall₂_map_left_iff, List.forall₂_iff_get]
      refine ⟨by simp, fun k h₁ h₂ => ?_⟩
      simp only [List.length_range] at h₁
      simp only [List.get_eq_getElem, List.getElem_range]
      rw [getElem?_block_left b w' h₁]
      simp
    · exact getElem?_block_mid b w'
    · rw [List.forall₂_map_left_iff]
      refine hlab.imp ?_
      rintro ⟨c, q⟩ x hq
      exact (getElem?_block_right b w' q).trans hq

lemma dupEnum_blockStr : ∀ bs : List (List A₀), bs ≠ [] → DupEnum (blockStr bs) := by
  intro bs
  induction bs with
  | nil => intro h; exact absurd rfl h
  | cons b bs ih =>
      intro _
      rcases bs with _ | ⟨c, cs⟩
      · rw [blockStr_singleton]
        exact dupEnum_map_some b
      · rw [blockStr_cons b (c :: cs) (by simp)]
        exact dupEnum_cons (ih (by simp))

lemma dupEnum_all (w : List (Option A₀)) : DupEnum w := by
  have h := dupEnum_blockStr (splitSep w) (splitSep_ne_nil w)
  rwa [blockStr_splitSep] at h

/-! ## The transduction -/

/-- The first-order transduction computing map duplicate. -/
def trans (A₀ : Type) : ITrans (Option A₀) (Option A₀) where
  P := Bool
  E := Empty
  finP := inferInstance
  finE := inferInstance
  univP := fun c => match c with
    | false => MSO.tt
    | true => MSO.not (sepF A₀ 0)
  univC := fun j => j.elim
  labP := fun _ b => MSO.lab b 0
  labC := fun j _ => j.elim
  ordPP := fun c c' => match c, c' with
    | false, false => MSO.le 0 1
    | true, true => MSO.le 0 1
    | false, true => MSO.or (sameBlkF A₀ 0 1 2) (MSO.le 0 1)
    | true, false => MSO.and (MSO.not (sameBlkF A₀ 0 1 2)) (MSO.le 0 1)
  ordPC := fun _ j => j.elim
  ordCP := fun j _ => j.elim
  ordCC := fun j _ => j.elim

lemma selected_iff (w : List (Option A₀)) (c : Bool) (p : ℕ) :
    (trans A₀).selected w (Sum.inl (c, p)) ↔ dupSel w (c, p) := by
  cases c
  · show (p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (MSO.tt : MSO (Option A₀))) ↔ _
    simp [dupSel]
  · show (p < w.length ∧ ¬ MSO.Sat w (fun _ => p) (fun _ => ∅) (sepF A₀ 0)) ↔ _
    rw [sat_sepF]
    simp [dupSel]

lemma labRel_iff (w : List (Option A₀)) (c : Bool) (p : ℕ) (b : Option A₀) :
    (trans A₀).labRel w (Sum.inl (c, p)) b ↔ w[p]? = some b := Iff.rfl

lemma ordRel_iff (w : List (Option A₀)) (c c' : Bool) {p q : ℕ} (hp : p < w.length)
    (hq : q < w.length) :
    (trans A₀).ordRel w (Sum.inl (c, p)) (Sum.inl (c', q)) ↔ dupOrd w (c, p) (c', q) := by
  cases c <;> cases c'
  · show MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (MSO.le 0 1) ↔ _
    simp [dupOrd, MSO.Sat]
  · rw [show (trans A₀).ordRel w (Sum.inl (false, p)) (Sum.inl (true, q)) ↔
        (MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (sameBlkF A₀ 0 1 2) ∨
          MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (MSO.le 0 1)) from Iff.rfl]
    rw [sat_sameBlkF w (by omega) (by omega) _ _ (by simpa using hp) (by simpa using hq)]
    simp [dupOrd, MSO.Sat]
  · rw [show (trans A₀).ordRel w (Sum.inl (true, p)) (Sum.inl (false, q)) ↔
        (¬ MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (sameBlkF A₀ 0 1 2) ∧
          MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (MSO.le 0 1)) from Iff.rfl]
    rw [sat_sameBlkF w (by omega) (by omega) _ _ (by simpa using hp) (by simpa using hq)]
    simp [dupOrd, MSO.Sat]
  · show MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (MSO.le 0 1) ↔ _
    simp [dupOrd, MSO.Sat]

lemma proper : (trans A₀).Proper := by
  intro w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨c, p⟩ | j) hx
    · rw [selected_iff] at hx
      refine ⟨w[p]'hx.1, (labRel_iff w c p _).2 (List.getElem?_eq_getElem hx.1), fun b hb => ?_⟩
      have hb' : w[p]? = some b := (labRel_iff w c p b).1 hb
      rw [List.getElem?_eq_getElem hx.1] at hb'
      exact (Option.some_inj.1 hb').symm
    · exact j.elim
  · rintro (⟨c, p⟩ | j) hx
    · rw [selected_iff] at hx
      exact (ordRel_iff w c c hx.1 hx.1).2 (dupOrd_refl w (c, p))
    · exact j.elim
  · rintro (⟨c, p⟩ | j) (⟨c', q⟩ | j') hx hy h₁ h₂
    · rw [selected_iff] at hx hy
      rw [ordRel_iff w c c' hx.1 hy.1] at h₁
      rw [ordRel_iff w c' c hy.1 hx.1] at h₂
      have := dupOrd_antisymm hx hy h₁ h₂
      exact congrArg Sum.inl this
    · exact j'.elim
    · exact j.elim
    · exact j.elim
  · rintro (⟨c, p⟩ | j) (⟨c', q⟩ | j') (⟨c'', r⟩ | j'') hx hy hz h₁ h₂
    · rw [selected_iff] at hx hy hz
      rw [ordRel_iff w c c' hx.1 hy.1] at h₁
      rw [ordRel_iff w c' c'' hy.1 hz.1] at h₂
      exact (ordRel_iff w c c'' hx.1 hz.1).2 (dupOrd_trans hz.1 h₁ h₂)
    · exact j''.elim
    · exact j'.elim
    · exact j'.elim
    · exact j.elim
    · exact j.elim
    · exact j.elim
    · exact j.elim
  · rintro (⟨c, p⟩ | j) (⟨c', q⟩ | j') hx hy
    · rw [selected_iff] at hx hy
      rw [ordRel_iff w c c' hx.1 hy.1, ordRel_iff w c' c hy.1 hx.1]
      exact dupOrd_total w (c, p) (c', q)
    · exact j'.elim
    · exact j.elim
    · exact j.elim

lemma allFO : (trans A₀).AllFO := by
  refine ⟨fun c => ?_, fun j => j.elim, fun _ _ => trivial, fun j _ => j.elim,
    fun c c' => ?_, fun _ j => j.elim, fun j _ => j.elim, fun j _ => j.elim⟩
  · cases c
    · exact trivial
    · exact isFO_sepF (A := A₀) 0
  · cases c <;> cases c'
    · exact trivial
    · exact ⟨isFO_sameBlkF 0 1 2, trivial⟩
    · exact ⟨isFO_sameBlkF 0 1 2, trivial⟩
    · exact trivial

lemma outputs (w : List (Option A₀)) : (trans A₀).Outputs w (mapDuplicate A₀ w) := by
  obtain ⟨es, hnd, hmem, hord, hlab⟩ := dupEnum_all w
  refine (trans A₀).outputs_of_forall₂ (es.map (fun x => Sum.inl x)) ?_ ?_ ?_ ?_
  · exact hnd.map (fun x y h => by simpa using h)
  · rintro (⟨c, p⟩ | j)
    · rw [selected_iff, List.mem_map]
      constructor
      · rintro ⟨y, hy, hyp⟩
        have : y = (c, p) := by simpa using hyp
        subst this
        exact (hmem _).1 hy
      · intro hp
        exact ⟨(c, p), (hmem (c, p)).2 hp, rfl⟩
    · exact j.elim
  · rw [List.pairwise_map]
    refine hord.imp_of_mem ?_
    rintro ⟨c, p⟩ ⟨c', q⟩ hp hq hpq
    exact (ordRel_iff w c c' ((hmem _).1 hp).1 ((hmem _).1 hq).1).2 hpq
  · rw [List.forall₂_map_left_iff]
    refine hlab.imp ?_
    rintro ⟨c, p⟩ x hx
    exact (labRel_iff w c p x).2 hx

end FODup

/-- **Map duplicate is a first-order transduction.** -/
theorem isFOTransduction_mapDuplicate (A₀ : Type) : IsFOTransduction (mapDuplicate A₀) :=
  (FODup.trans A₀).isFOTransduction FODup.proper FODup.allFO FODup.outputs

end Lax314295Proofs.Transducers
