import Lax185574Proofs.Conversions.Ram.ConsEmit
import Lax185574Proofs.Conversions.Ram.MergeSpec
import Lax185574Proofs.Conversions.Ram.Encode
import Lax185574Proofs.Conversions.MergeConstructionRun

/-!
The steps of one stage of the construction script against the flags the
program computes.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax185574.SequenceEncoding Lax185574Proofs.Conversions.MergeConstruction

variable {n : ℕ}

theorem finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem finRange_flatMap {β : Type*} (g : ℕ → List β) :
    (List.finRange n).flatMap (fun a => g a.val) = (List.range n).flatMap g := by
  rw [← finRange_map_val, List.flatMap_map]

variable (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n)))

/-- The labels of stage `j`. -/
noncomputable def labJ (j : ℕ) : ℕ → ℕ := repN (part ms j)

theorem col_eq_labJ (j : ℕ) (x : Fin n) : col ms j x = labJ ms j x := by
  simp [col, labJ, repN_fin]

/-- The flags of stage `j`. -/
def BadJ (j : ℕ) : ℕ → ℕ → Prop := FlagP n (labJ ms j) fun x y => ¬ gA (rel ms (j + 1)) x y
def UnrJ (j : ℕ) : ℕ → ℕ → Prop := FlagP n (labJ ms j) fun x y => ¬ gA (resolvedAt ms j) x y
def PosJ (j : ℕ) : ℕ → ℕ → Prop :=
  FlagP n (labJ ms j) fun x y => ¬ gA (resolvedAt ms j) x y ∧ gA G x y

theorem rect_adj' (j a b : ℕ) (hab : a ≤ b) (x y : Fin n) :
    (rect ms j a b).Adj x y ↔ x ≠ y ∧ min (labJ ms j x) (labJ ms j y) = a ∧
      max (labJ ms j x) (labJ ms j y) = b := by
  rw [rect_adj, col_eq_labJ, col_eq_labJ]
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> refine ⟨hne, ?_, ?_⟩ <;> omega
  · rintro ⟨hne, h1, h2⟩
    refine ⟨hne, ?_⟩
    omega

theorem flagP_iff_rect {P : ℕ → ℕ → Prop} (j a b : ℕ) (hab : a ≤ b) :
    FlagP n (labJ ms j) P a b ↔ ∃ x y : Fin n, (rect ms j a b).Adj x y ∧ P x y := by
  constructor
  · rintro ⟨x, hx, y, hy, hne, h1, h2, hP⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, (rect_adj' ms j a b hab _ _).mpr
      ⟨fun h => hne (Fin.mk.inj_iff.mp h), h1, h2⟩, hP⟩
  · rintro ⟨x, y, hr, hP⟩
    obtain ⟨hne, h1, h2⟩ := (rect_adj' ms j a b hab _ _).mp hr
    exact ⟨x, x.2, y, y.2, fun h => hne (Fin.ext h), h1, h2, hP⟩

theorem resolves_iff (j : ℕ) (a b : Fin n) :
    Resolves ms j (a, b) ↔ (a : ℕ) ≤ b ∧ labJ ms j a = a ∧ labJ ms j b = b ∧
      ¬ BadJ ms j a b ∧ UnrJ ms j a b := by
  unfold Resolves
  simp only
  constructor
  · rintro ⟨hab, ha, hb, hrel, hres⟩
    refine ⟨hab, by rw [← col_eq_labJ, col, ha], by rw [← col_eq_labJ, col, hb], ?_, ?_⟩
    · rw [BadJ, flagP_iff_rect ms j a b hab]
      rintro ⟨x, y, hr, hn⟩
      exact hn ((gA_fin _ x y).mpr (hrel hr))
    · rw [UnrJ, flagP_iff_rect ms j a b hab]
      by_contra hc
      push Not at hc
      exact hres fun x y hr => (gA_fin _ x y).mp (hc x y hr)
  · rintro ⟨hab, ha, hb, hbad, hunr⟩
    refine ⟨hab, Fin.ext (by rw [← col_eq_labJ] at ha; exact ha),
      Fin.ext (by rw [← col_eq_labJ] at hb; exact hb), fun x y hr => ?_, fun hle => ?_⟩
    · by_contra hn
      exact hbad ((flagP_iff_rect ms j a b hab).mpr ⟨x, y, hr, fun h => hn ((gA_fin _ x y).mp h)⟩)
    · obtain ⟨x, y, hr, hn⟩ := (flagP_iff_rect ms j a b hab).mp hunr
      exact hn ((gA_fin _ x y).mpr (hle hr))

theorem positive_iff (j : ℕ) (a b : Fin n) (hab : (a : ℕ) ≤ b) :
    Positive G ms j (a, b) ↔ PosJ G ms j a b := by
  rw [PosJ, flagP_iff_rect ms j a b hab]
  unfold Positive
  constructor
  · rintro ⟨x, y, hr, hn, hadj⟩
    exact ⟨x, y, hr, fun h => hn ((gA_fin _ x y).mp h), (gA_fin _ x y).mpr hadj⟩
  · rintro ⟨x, y, hr, hn, hadj⟩
    exact ⟨x, y, hr, fun h => hn ((gA_fin _ x y).mpr h), (gA_fin _ x y).mp hadj⟩

theorem filter_map_flatMap {α β γ : Type*} (l : List α) (p : α → Bool) (f : α → β)
    (g : β → List γ) : ((l.filter p).map f).flatMap g =
      l.flatMap fun a => if p a then g (f a) else [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    split <;> simp_all

theorem filter_flatMap' {α β : Type*} (l : List α) (h : α → List β) (p : β → Bool) :
    (l.flatMap h).filter p = l.flatMap fun a => (h a).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_append, ih]

theorem map_flatMap' {α β γ : Type*} (l : List α) (h : α → List β) (f : β → γ) :
    (l.flatMap h).map f = l.flatMap fun a => (h a).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem flatMap_flatMap' {α β γ : Type*} (l : List α) (h : α → List β) (g : β → List γ) :
    (l.flatMap h).flatMap g = l.flatMap fun a => (h a).flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_append, ih]

open Classical in
/-- **The resolves of a stage**, as the program emits them. -/
theorem resTriples_eq (j : ℕ) :
    resTriples n (labJ ms j) (BadJ ms j) (UnrJ ms j) (PosJ G ms j) =
      ((resolvePairs ms j).map (resolveStep G ms j)).flatMap stepCode := by
  unfold resolvePairs
  rw [filter_map_flatMap]
  rw [flatMap_flatMap']
  let g : ℕ → List ℕ := fun a => (List.range n).flatMap fun b =>
    if a ≤ b ∧ labJ ms j a = a ∧ labJ ms j b = b ∧ ¬ BadJ ms j a b ∧ UnrJ ms j a b then
      [2 - ind (PosJ G ms j a b), a, b] else []
  have hg : ∀ a : Fin n, ((List.finRange n).map fun b => (a, b)).flatMap
      (fun p => if decide (Resolves ms j p) = true then stepCode (resolveStep G ms j p) else []) =
      g a := by
    intro a
    rw [List.flatMap_map]
    simp only [g]
    rw [← finRange_flatMap]
    refine List.flatMap_congr fun b _ => ?_
    simp only [decide_eq_true_eq]
    by_cases hR : Resolves ms j (a, b)
    · rw [if_pos hR, if_pos ((resolves_iff ms j a b).mp hR)]
      have hab : (a : ℕ) ≤ b := ((resolves_iff ms j a b).mp hR).1
      unfold resolveStep
      by_cases hP : Positive G ms j (a, b)
      · rw [if_pos hP]
        have := (positive_iff G ms j a b hab).mp hP
        simp [stepCode, ind, this]
      · rw [if_neg hP]
        have : ¬ PosJ G ms j a b := fun h => hP ((positive_iff G ms j a b hab).mpr h)
        simp only [stepCode, ind, if_neg this]
    · rw [if_neg hR, if_neg (fun h => hR ((resolves_iff ms j a b).mpr h))]
  rw [show (List.finRange n).flatMap (fun a => ((List.finRange n).map fun b => (a, b)).flatMap
      (fun p => if decide (Resolves ms j p) = true then stepCode (resolveStep G ms j p) else [])) =
      (List.finRange n).flatMap (fun a => g a.val) from List.flatMap_congr fun a _ => hg a,
    finRange_flatMap]
  rfl

open Classical in
/-- **The merges of a stage**, as the program emits them. -/
theorem mrgTriples_eq (j : ℕ) :
    mrgTriples n (labJ ms j) (labJ ms (j + 1)) =
      ((mergeSources ms j).map (mergeStep ms j)).flatMap stepCode := by
  unfold mergeSources mrgTriples
  rw [filter_map_flatMap, ← finRange_flatMap]
  refine List.flatMap_congr fun v _ => ?_
  simp only [decide_eq_true_eq]
  have h1 : labJ ms j v = v ↔ rep (part ms j) v = v := by
    rw [← col_eq_labJ, col]; exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  have h2 : labJ ms (j + 1) v = v ↔ rep (part ms (j + 1)) v = v := by
    rw [← col_eq_labJ, col]; exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  by_cases hs : IsSource ms j v
  · rw [if_pos hs, if_pos ⟨h1.mpr hs.1, fun h => hs.2 (h2.mp h)⟩]
    simp [mergeStep, stepCode, labJ, repN_fin]
  · rw [if_neg hs, if_neg (fun h => hs ⟨h1.mp h.1, fun h' => h.2 (h2.mpr h')⟩)]

theorem labJ_eq_iff (j : ℕ) (a x : Fin n) : labJ ms j a = labJ ms j x ↔ part ms j a x := by
  rw [← col_eq_labJ, ← col_eq_labJ]; exact col_eq_iff ms j a x

/-- **The resolved pairs after a stage.** -/
theorem resolvedAt_succ_iff (j : ℕ) (x y : Fin n) :
    gA (resolvedAt ms (j + 1)) x y ↔ gA (resolvedAt ms j) x y ∨
      ((x : ℕ) ≠ y ∧ ¬ BadJ ms j (min (labJ ms j x) (labJ ms j y)) (max (labJ ms j x) (labJ ms j y))) := by
  rw [gA_fin, gA_fin, resolvedAt_succ, SimpleGraph.sup_adj, block_adj, BadJ,
    flagP_iff_rect ms j _ _ (min_le_max)]
  refine or_congr_right ⟨fun ⟨hne, h⟩ => ⟨fun he => hne (Fin.ext he), ?_⟩, fun ⟨hne, h⟩ =>
    ⟨fun he => hne (congrArg Fin.val he), ?_⟩⟩
  · rintro ⟨x', y', hr, hn⟩
    obtain ⟨hne', h1, h2⟩ := (rect_adj' ms j _ _ min_le_max x' y').mp hr
    apply hn
    rw [gA_fin]
    rcases le_total (labJ ms j x) (labJ ms j y) with hxy | hxy
    · simp only [min_eq_left hxy, max_eq_right hxy] at h1 h2
      rcases le_total (labJ ms j x') (labJ ms j y') with h' | h'
      · rw [min_eq_left h'] at h1; rw [max_eq_right h'] at h2
        exact h x' y' ((labJ_eq_iff ms j _ _).mp h1) ((labJ_eq_iff ms j _ _).mp h2) hne'
      · rw [min_eq_right h'] at h1; rw [max_eq_left h'] at h2
        exact (h y' x' ((labJ_eq_iff ms j _ _).mp h1) ((labJ_eq_iff ms j _ _).mp h2)
          (Ne.symm hne')).symm
    · simp only [min_eq_right hxy, max_eq_left hxy] at h1 h2
      rcases le_total (labJ ms j x') (labJ ms j y') with h' | h'
      · rw [min_eq_left h'] at h1; rw [max_eq_right h'] at h2
        exact (h y' x' ((labJ_eq_iff ms j _ _).mp h2) ((labJ_eq_iff ms j _ _).mp h1)
          (Ne.symm hne')).symm
      · rw [min_eq_right h'] at h1; rw [max_eq_left h'] at h2
        exact h x' y' ((labJ_eq_iff ms j _ _).mp h2) ((labJ_eq_iff ms j _ _).mp h1) hne'
  · intro a b ha hb hab
    by_contra hn
    refine h ⟨a, b, (rect_adj' ms j _ _ min_le_max a b).mpr ⟨hab, ?_, ?_⟩, fun h' => hn ((gA_fin _ a b).mp h')⟩
    · rw [(labJ_eq_iff ms j a x).mpr ha, (labJ_eq_iff ms j b y).mpr hb]
    · rw [(labJ_eq_iff ms j a x).mpr ha, (labJ_eq_iff ms j b y).mpr hb]

end Lax185574Proofs.Conversions.Ram
