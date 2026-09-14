/-
Map reverse is a first-order transduction.

The transduction has one copy of every position of the input, labelled by the
letter of that position, and orders two positions `p` and `q` by: if `p` and `q`
are non-separator positions of the same block (`Transducers.SameBlk`), then
`q ≤ p`, and otherwise `p ≤ q`.  Reversing the order inside every block turns
the input `w₁ # ⋯ # wₙ` into `reverse w₁ # ⋯ # reverse wₙ`.

This is one of the ingredients of the easy inclusion of Theorem
`nolabel:thm-fo-transduction-into-primes`. -/
import Lax314295Proofs.Source.PartC.BlockForm
import Lax314295Proofs.Source.PartC.ITransBuild
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace FORev

open RegPair

variable {A₀ : Type}

/-! ## The order in which map reverse reads the input -/

/-- The order in which the output of map reverse reads the positions of the
input: inside a block the order of the input is reversed, and elsewhere it is
the order of the input. -/
def revOrd (w : List (Option A₀)) (p q : ℕ) : Prop :=
  (SameBlk w p q ∧ q ≤ p) ∨ (¬ SameBlk w p q ∧ p ≤ q)

lemma revOrd_refl (w : List (Option A₀)) (p : ℕ) : revOrd w p p := by
  by_cases h : SameBlk w p p
  · exact Or.inl ⟨h, le_refl _⟩
  · exact Or.inr ⟨h, le_refl _⟩

lemma revOrd_antisymm {w : List (Option A₀)} {p q : ℕ} (h₁ : revOrd w p q)
    (h₂ : revOrd w q p) : p = q := by
  rcases h₁ with ⟨hs, hle⟩ | ⟨hs, hle⟩ <;> rcases h₂ with ⟨hs', hle'⟩ | ⟨hs', hle'⟩
  · omega
  · exact absurd (sameBlk_symm hs) hs'
  · exact absurd (sameBlk_symm hs') hs
  · omega

lemma revOrd_total (w : List (Option A₀)) (p q : ℕ) : revOrd w p q ∨ revOrd w q p := by
  by_cases h : SameBlk w p q
  · rcases le_total q p with hle | hle
    · exact Or.inl (Or.inl ⟨h, hle⟩)
    · exact Or.inr (Or.inl ⟨sameBlk_symm h, hle⟩)
  · rcases le_total p q with hle | hle
    · exact Or.inl (Or.inr ⟨h, hle⟩)
    · exact Or.inr (Or.inr ⟨fun h' => h (sameBlk_symm h'), hle⟩)

lemma revOrd_trans {w : List (Option A₀)} {x y z : ℕ} (h₁ : revOrd w x y) (h₂ : revOrd w y z) : revOrd w x z := by
  rcases h₁ with ⟨hxy, hyx⟩ | ⟨hxy, hxy'⟩ <;> rcases h₂ with ⟨hyz, hzy⟩ | ⟨hyz, hyz'⟩
  · exact Or.inl ⟨sameBlk_trans hxy hyz, by omega⟩
  · exact Or.inr ⟨not_sameBlk_trans hxy hyz,
      le_of_sameBlk_of_not_sameBlk hxy hyz hyz'⟩
  · exact Or.inr ⟨fun h => hxy (sameBlk_trans h (sameBlk_symm hyz)),
      le_of_not_sameBlk_of_sameBlk hxy hyz hxy'⟩
  · exact Or.inr ⟨fun h => hxy (sameBlk_of_between h (by omega) (by omega)), by omega⟩

/-! ## The enumeration of the positions in the output order -/

/-- The positions of `w` can be enumerated in the order in which map reverse
outputs them, with the labels of the output string. -/
def RevEnum (w : List (Option A₀)) : Prop :=
  ∃ es : List ℕ, es.Nodup ∧ (∀ p, p ∈ es ↔ p < w.length) ∧
    es.Pairwise (revOrd w) ∧
    List.Forall₂ (fun p (x : Option A₀) => w[p]? = some x) es (mapReverse A₀ w)

lemma revEnum_map_some (b : List A₀) : RevEnum (b.map some) := by
  refine ⟨(List.range b.length).reverse, List.nodup_reverse.2 List.nodup_range, ?_, ?_, ?_⟩
  · intro p; simp
  · rw [List.pairwise_reverse, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_range] at hi hj
    simp only [List.getElem_range]
    exact Or.inl ⟨(sameBlk_map_some_iff b j i).2 ⟨hj, hi⟩, le_of_lt hij⟩
  · rw [show mapReverse A₀ (b.map some) = (b.reverse).map some from
      mapLift_map_some List.reverse b]
    rw [List.map_reverse, List.forall₂_reverse_iff, List.forall₂_iff_get]
    refine ⟨by simp, fun k h₁ h₂ => ?_⟩
    simp only [List.length_range] at h₁
    simp only [List.get_eq_getElem, List.getElem_range]
    rw [List.getElem?_eq_getElem (by simpa using h₁)]

lemma revEnum_cons {b : List A₀} {w' : List (Option A₀)} (h : RevEnum w') :
    RevEnum (b.map some ++ none :: w') := by
  obtain ⟨es, hnd, hmem, hord, hlab⟩ := h
  have hlen : (b.map some ++ none :: w').length = b.length + 1 + w'.length :=
    length_block_decomp b w'
  refine ⟨(List.range b.length).reverse ++ b.length :: es.map (fun q => b.length + 1 + q),
    ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨List.nodup_reverse.2 List.nodup_range, ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, hnd.map (fun q q' hqq => by omega)⟩
      simp only [List.mem_map, not_exists]
      intro q hq
      omega
    · intro a ha c hc
      rw [List.mem_reverse, List.mem_range] at ha
      rcases List.mem_cons.1 hc with rfl | hq
      · omega
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hq
        omega
  · intro p
    simp only [List.mem_append, List.mem_reverse, List.mem_range, List.mem_cons, List.mem_map,
      hlen]
    constructor
    · rintro (hp | rfl | ⟨q, hq, rfl⟩)
      · omega
      · omega
      · have := (hmem q).1 hq; omega
    · intro hp
      rcases lt_trichotomy p b.length with hc | hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr ⟨p - (b.length + 1), (hmem _).2 (by omega), by omega⟩)
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_reverse, List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [List.length_range] at hi hj
      simp only [List.getElem_range]
      exact Or.inl ⟨sameBlk_block_left b w' hj hi, le_of_lt hij⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨q, -, rfl⟩ := ha
        exact Or.inr ⟨fun hs => not_sepAt_of_sameBlk_left hs (sepAt_block_mid b w'), by omega⟩
      · rw [List.pairwise_map]
        refine hord.imp_of_mem ?_
        intro p q _ _ hpq
        rcases hpq with ⟨hs, hle⟩ | ⟨hs, hle⟩
        · exact Or.inl ⟨(sameBlk_block_right b w' p q).2 hs, by omega⟩
        · exact Or.inr ⟨fun h' => hs ((sameBlk_block_right b w' p q).1 h'), by omega⟩
    · intro a ha c hc
      simp only [List.mem_reverse, List.mem_range] at ha
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨q, -, rfl⟩
      · exact Or.inr ⟨not_sameBlk_block_cross b w' ha (le_refl _), by omega⟩
      · exact Or.inr ⟨not_sameBlk_block_cross b w' ha (by omega), by omega⟩
  · rw [show mapReverse A₀ (b.map some ++ none :: w') =
      (b.reverse).map some ++ none :: mapReverse A₀ w' from
      mapLift_map_some_cons_none List.reverse b w']
    refine forall₂_append ?_ (List.Forall₂.cons ?_ ?_)
    · rw [List.map_reverse, List.forall₂_reverse_iff, List.forall₂_iff_get]
      refine ⟨by simp, fun k h₁ h₂ => ?_⟩
      simp only [List.length_range] at h₁
      simp only [List.get_eq_getElem, List.getElem_range]
      rw [getElem?_block_left b w' h₁]
      simp
    · exact getElem?_block_mid b w'
    · rw [List.forall₂_map_left_iff]
      refine hlab.imp ?_
      intro q x hq
      rw [getElem?_block_right b w' q]
      exact hq

lemma revEnum_blockStr : ∀ bs : List (List A₀), bs ≠ [] → RevEnum (blockStr bs) := by
  intro bs
  induction bs with
  | nil => intro h; exact absurd rfl h
  | cons b bs ih =>
      intro _
      rcases bs with _ | ⟨c, cs⟩
      · rw [blockStr_singleton]
        exact revEnum_map_some b
      · rw [blockStr_cons b (c :: cs) (by simp)]
        exact revEnum_cons (ih (by simp))

lemma revEnum_all (w : List (Option A₀)) : RevEnum w := by
  have h := revEnum_blockStr (splitSep w) (splitSep_ne_nil w)
  rwa [blockStr_splitSep] at h

/-! ## The transduction -/

/-- The first-order transduction computing map reverse. -/
def trans (A₀ : Type) : ITrans (Option A₀) (Option A₀) where
  P := Unit
  E := Empty
  finP := inferInstance
  finE := inferInstance
  univP := fun _ => MSO.tt
  univC := fun j => j.elim
  labP := fun _ b => MSO.lab b 0
  labC := fun j _ => j.elim
  ordPP := fun _ _ => MSO.or (MSO.and (sameBlkF A₀ 0 1 2) (MSO.le 1 0))
      (MSO.and (MSO.not (sameBlkF A₀ 0 1 2)) (MSO.le 0 1))
  ordPC := fun _ j => j.elim
  ordCP := fun j _ => j.elim
  ordCC := fun j _ => j.elim

lemma selected_iff (w : List (Option A₀)) (p : ℕ) :
    (trans A₀).selected w (Sum.inl ((), p)) ↔ p < w.length := by
  show (p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (MSO.tt : MSO (Option A₀))) ↔ _
  simp

lemma labRel_iff (w : List (Option A₀)) (p : ℕ) (b : Option A₀) :
    (trans A₀).labRel w (Sum.inl ((), p)) b ↔ w[p]? = some b := Iff.rfl

lemma ordRel_iff (w : List (Option A₀)) {p q : ℕ} (hp : p < w.length) (hq : q < w.length) :
    (trans A₀).ordRel w (Sum.inl ((), p)) (Sum.inl ((), q)) ↔ revOrd w p q := by
  have hfo0 : (fun v : ℕ => if v = 0 then p else q) 0 = p := by simp
  have hfo1 : (fun v : ℕ => if v = 0 then p else q) 1 = q := by simp
  rw [show (trans A₀).ordRel w (Sum.inl ((), p)) (Sum.inl ((), q)) ↔
      ((MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (sameBlkF A₀ 0 1 2) ∧
        MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (MSO.le 1 0)) ∨
       (¬ MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (sameBlkF A₀ 0 1 2) ∧
        MSO.Sat w (fun v => if v = 0 then p else q) (fun _ => ∅) (MSO.le 0 1))) from Iff.rfl]
  rw [sat_sameBlkF w (by omega) (by omega) _ _ (by simpa using hp) (by simpa using hq)]
  simp [revOrd, MSO.Sat]

lemma proper : (trans A₀).Proper := by
  intro w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (⟨⟨⟩, p⟩ | j) hx
    · rw [selected_iff] at hx
      refine ⟨w[p], (labRel_iff w p _).2 (List.getElem?_eq_getElem hx), fun b hb => ?_⟩
      have hb' : w[p]? = some b := (labRel_iff w p b).1 hb
      rw [List.getElem?_eq_getElem hx] at hb'
      exact (Option.some_inj.1 hb').symm
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) hx
    · rw [selected_iff] at hx
      exact (ordRel_iff w hx hx).2 (revOrd_refl w p)
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) (⟨⟨⟩, q⟩ | j') hx hy h₁ h₂
    · rw [selected_iff] at hx hy
      rw [ordRel_iff w hx hy] at h₁
      rw [ordRel_iff w hy hx] at h₂
      have : p = q := revOrd_antisymm h₁ h₂
      rw [this]
    · exact j'.elim
    · exact j.elim
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) (⟨⟨⟩, q⟩ | j') (⟨⟨⟩, r⟩ | j'') hx hy hz h₁ h₂
    · rw [selected_iff] at hx hy hz
      rw [ordRel_iff w hx hy] at h₁
      rw [ordRel_iff w hy hz] at h₂
      exact (ordRel_iff w hx hz).2 (revOrd_trans h₁ h₂)
    · exact j''.elim
    · exact j'.elim
    · exact j'.elim
    · exact j.elim
    · exact j.elim
    · exact j.elim
    · exact j.elim
  · rintro (⟨⟨⟩, p⟩ | j) (⟨⟨⟩, q⟩ | j') hx hy
    · rw [selected_iff] at hx hy
      rw [ordRel_iff w hx hy, ordRel_iff w hy hx]
      exact revOrd_total w p q
    · exact j'.elim
    · exact j.elim
    · exact j.elim

lemma allFO : (trans A₀).AllFO :=
  ⟨fun _ => trivial, fun j => j.elim, fun _ _ => trivial, fun j _ => j.elim,
    fun _ _ => ⟨⟨isFO_sameBlkF 0 1 2, trivial⟩, ⟨isFO_sameBlkF 0 1 2, trivial⟩⟩,
    fun _ j => j.elim, fun j _ => j.elim, fun j _ => j.elim⟩

lemma outputs (w : List (Option A₀)) : (trans A₀).Outputs w (mapReverse A₀ w) := by
  obtain ⟨es, hnd, hmem, hord, hlab⟩ := revEnum_all w
  refine (trans A₀).outputs_of_forall₂ (es.map (fun p => Sum.inl ((), p))) ?_ ?_ ?_ ?_
  · exact hnd.map (fun p q h => by simpa using h)
  · rintro (⟨⟨⟩, p⟩ | j)
    · rw [selected_iff, List.mem_map]
      constructor
      · rintro ⟨q, hq, hqp⟩
        have : q = p := by simpa using hqp
        rw [← this]
        exact (hmem q).1 hq
      · intro hp
        exact ⟨p, (hmem p).2 hp, rfl⟩
    · exact j.elim
  · rw [List.pairwise_map]
    refine hord.imp_of_mem ?_
    intro p q hp hq hpq
    exact (ordRel_iff w ((hmem p).1 hp) ((hmem q).1 hq)).2 hpq
  · rw [List.forall₂_map_left_iff]
    exact hlab.imp (fun p x hx => (labRel_iff w p x).2 hx)

end FORev

/-- **Map reverse is a first-order transduction.** -/
theorem isFOTransduction_mapReverse (A₀ : Type) : IsFOTransduction (mapReverse A₀) :=
  (FORev.trans A₀).isFOTransduction FORev.proper FORev.allFO FORev.outputs

end Lax314295Proofs.Transducers
