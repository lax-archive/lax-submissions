import Lax185574Proofs.Gaifman.RadiusChange
import Mathlib.Tactic

/-!
Separation of a local formula whose anchors are split as a nonempty tuple
`x̄` and one far-away point `y`.  Locally bound variables are assigned to the
side of the anchor (or constant) whose ball supplied them.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/Separation.lean`.
-/

namespace Lax185574Proofs.Gaifman.Separation

noncomputable section

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.Distance Lax185574Proofs.Gaifman.NormalFormOps
open Lax185574Proofs.Gaifman.NeighborhoodFormula

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The fixed split of `k+1` anchors into the first `k` anchors and the last
anchor. -/
def splitAnchor {k : ℕ} : Fin (k + 1) → Fin k ⊕ Fin 1 :=
  Fin.lastCases (Sum.inr 0) (fun i => Sum.inl i)

/-- Split a local term according to a chosen split of the locally bound
variables. Constants belong to the left side. -/
def splitTerm {σ : Vocabulary} {k B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) :
    LocalTerm σ (k + 1) B → LocalTerm σ k a ⊕ LocalTerm σ 1 b
  | .anchor i =>
      match splitAnchor i with
      | .inl j => .inl (.anchor j)
      | .inr j => .inr (.anchor j)
  | .bound i =>
      match side i with
      | .inl j => .inl (.bound j)
      | .inr j => .inr (.bound j)
  | .const c => .inl (.const c)

/-- Reassemble the source bound environment from its two sides. -/
def combineBound {M : Type*} {B a b : ℕ} (side : Fin B → Fin a ⊕ Fin b)
    (left : Fin a → M) (right : Fin b → M) : Fin B → M :=
  fun i => match side i with
    | .inl j => left j
    | .inr j => right j

/-- Assign the newest bound variable to the left side. -/
def extendLeft {B a b : ℕ} (side : Fin B → Fin a ⊕ Fin b) :
    Fin (B + 1) → Fin (a + 1) ⊕ Fin b :=
  Fin.lastCases (.inl (Fin.last a)) (fun i =>
    match side i with
    | .inl j => .inl j.castSucc
    | .inr j => .inr j)

/-- Assign the newest bound variable to the right side. -/
def extendRight {B a b : ℕ} (side : Fin B → Fin a ⊕ Fin b) :
    Fin (B + 1) → Fin a ⊕ Fin (b + 1) :=
  Fin.lastCases (.inr (Fin.last b)) (fun i =>
    match side i with
    | .inl j => .inl j
    | .inr j => .inr j.castSucc)

theorem combineBound_extendLeft {M : Type*} {B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) (left : Fin a → M)
    (right : Fin b → M) (x : M) :
    combineBound (extendLeft side) (Fin.snoc left x) right =
      Fin.snoc (combineBound side left right) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [combineBound, extendLeft]
  · cases h : side j <;> simp [combineBound, extendLeft, h]

theorem combineBound_extendRight {M : Type*} {B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) (left : Fin a → M)
    (right : Fin b → M) (x : M) :
    combineBound (extendRight side) left (Fin.snoc right x) =
      Fin.snoc (combineBound side left right) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [combineBound, extendRight]
  · cases h : side j <;> simp [combineBound, extendRight, h]

/-- A term classified on the left has the same value in the source and left
environments. -/
theorem eval_splitTerm_left {σ : Vocabulary} {M : Type*} {k B a b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b) (t : LocalTerm σ (k + 1) B)
    (u : LocalTerm σ k a) (h : splitTerm side t = .inl u) :
    t.eval A (Fin.snoc anchors y) (combineBound side left right) =
      u.eval A anchors left := by
  cases t with
  | anchor i =>
      induction i using Fin.lastCases with
      | last => simp [splitTerm, splitAnchor] at h
      | cast i =>
          simp [splitTerm, splitAnchor] at h
          subst u
          simp [LocalTerm.eval]
  | bound i =>
      cases hs : side i with
      | inl j =>
          simp [splitTerm, hs] at h
          subst u
          simp [LocalTerm.eval, combineBound, hs]
      | inr j => simp [splitTerm, hs] at h
  | const c =>
      simp [splitTerm] at h
      subst u
      rfl

/-- A term classified on the right has the same value in the source and right
environments. -/
theorem eval_splitTerm_right {σ : Vocabulary} {M : Type*} {k B a b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b) (t : LocalTerm σ (k + 1) B)
    (u : LocalTerm σ 1 b) (h : splitTerm side t = .inr u) :
    t.eval A (Fin.snoc anchors y) (combineBound side left right) =
      u.eval A (fun _ => y) right := by
  cases t with
  | anchor i =>
      induction i using Fin.lastCases with
      | last =>
          simp [splitTerm, splitAnchor] at h
          subst u
          simp [LocalTerm.eval]
      | cast i => simp [splitTerm, splitAnchor] at h
  | bound i =>
      cases hs : side i with
      | inl j => simp [splitTerm, hs] at h
      | inr j =>
          simp [splitTerm, hs] at h
          subst u
          simp [LocalTerm.eval, combineBound, hs]
  | const c => simp [splitTerm] at h

/-- Values of left-classified terms stay in the left radius-`R` ball. -/
theorem value_left_inBall {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b)
    (hleft : ∀ i j, side i = .inl j → inBallAround A R anchors (left j))
    (t : LocalTerm σ (k + 1) B) (u : LocalTerm σ k a)
    (h : splitTerm side t = .inl u) :
    inBallAround A R anchors
      (t.eval A (Fin.snoc anchors y) (combineBound side left right)) := by
  rw [eval_splitTerm_left A anchors y left right side t u h]
  cases u with
  | anchor i => exact anchor_inBallAround A anchors i
  | bound j =>
      cases t with
      | anchor i =>
          induction i using Fin.lastCases <;> simp [splitTerm, splitAnchor] at h
      | bound i =>
          cases hs : side i with
          | inl j' =>
              simp [splitTerm, hs] at h
              subst j'
              exact hleft i j hs
          | inr j' => simp [splitTerm, hs] at h
      | const c => simp [splitTerm] at h
  | const c => exact constant_inBallAround A anchors c

/-- Values of right-classified terms stay in the radius-`R` ball of `y`. -/
theorem value_right_near {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b)
    (hright : ∀ i j, side i = .inr j → distanceAtMost A R y (right j))
    (t : LocalTerm σ (k + 1) B) (u : LocalTerm σ 1 b)
    (h : splitTerm side t = .inr u) :
    distanceAtMost A R y
      (t.eval A (Fin.snoc anchors y) (combineBound side left right)) := by
  rw [eval_splitTerm_right A anchors y left right side t u h]
  cases u with
  | anchor i =>
      exact distanceAtMost_refl A R y
  | bound j =>
      cases t with
      | anchor i =>
          induction i using Fin.lastCases <;> simp [splitTerm, splitAnchor] at h
      | bound i =>
          cases hs : side i with
          | inl j' => simp [splitTerm, hs] at h
          | inr j' =>
              simp [splitTerm, hs] at h
              subst j'
              exact hright i j hs
      | const c => simp [splitTerm] at h
  | const c =>
      cases t with
      | anchor i =>
          induction i using Fin.lastCases <;> simp [splitTerm, splitAnchor] at h
      | bound i =>
          cases hs : side i <;> simp [splitTerm, hs] at h
      | const c' => simp [splitTerm] at h

/-- A left value and a right value cannot be at distance one when `y` is
outside the radius-`2R+1` left neighborhood. -/
theorem not_distance_one_cross {σ : Vocabulary} {M : Type*} {k R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y left right : M)
    (hy : ¬ inBallAround A (2 * R + 1) anchors y)
    (hl : inBallAround A R anchors left)
    (hr : distanceAtMost A R y right) :
    ¬ distanceAtMost A 1 left right := by
  intro hlr
  apply hy
  have hlefty : distanceAtMost A (1 + R) left y :=
    distanceAtMost_trans A hlr (distanceAtMost_symm A hr)
  have hball := inBallAround_of_distance A anchors hl hlefty
  exact inBallAround_mono A (by omega) anchors hball

/-- Split membership in the source ball into the left ball and the ball of
the last anchor. -/
theorem inBall_snoc_iff {σ : Vocabulary} {M : Type*} {k R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y x : M) :
    inBallAround A R (Fin.snoc anchors y) x ↔
      inBallAround A R anchors x ∨ distanceAtMost A R y x := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨c, hc⟩)
    · induction i using Fin.lastCases with
      | last => exact Or.inr (by simpa using hi)
      | cast i => exact Or.inl (Or.inl ⟨i, by simpa using hi⟩)
    · exact Or.inl (Or.inr ⟨c, hc⟩)
  · rintro ((⟨i, hi⟩ | ⟨c, hc⟩) | hy)
    · exact Or.inl ⟨i.castSucc, by simpa using hi⟩
    · exact Or.inr ⟨c, hc⟩
    · exact Or.inl ⟨Fin.last k, by simpa using hy⟩

/-! ### The separating syntax -/

/-- True formulas used as neutral factors on the two nonempty sides. -/
def trueLeft {σ : Vocabulary} {k R a : ℕ} (i : Fin k) :
    LocalFormula σ k R a := .eq (.anchor i) (.anchor i)

def trueRight {σ : Vocabulary} {R b : ℕ} :
    LocalFormula σ 1 R b := .eq (.anchor 0) (.anchor 0)

@[simp] theorem sat_trueLeft {σ : Vocabulary} {M : Type*} {k R a : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin a → M)
    (i : Fin k) : (trueLeft (σ := σ) (R := R) (a := a) i).Sat A anchors bound := rfl

@[simp] theorem sat_trueRight {σ : Vocabulary} {M : Type*} {R b : ℕ}
    (A : Structure σ M) (y : M) (bound : Fin b → M) :
    (trueRight (σ := σ) (R := R) (b := b)).Sat A (fun _ => y) bound := rfl

/-- Negation of a disjunction of separated pairs, in disjunctive normal
form. -/
def negPairs {σ : Vocabulary} {k R a b : ℕ} (i : Fin k) :
    List (LocalFormula σ k R a × LocalFormula σ 1 R b) →
      List (LocalFormula σ k R a × LocalFormula σ 1 R b)
  | [] => [(trueLeft i, trueRight)]
  | p :: ps =>
      (negPairs i ps).flatMap fun q =>
        [(LocalFormula.conjunction (.not p.1) q.1, q.2),
          (q.1, LocalFormula.conjunction (.not p.2) q.2)]

theorem sat_negPairs {σ : Vocabulary} {M : Type*} {k R a b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M) (i : Fin k)
    (ps : List (LocalFormula σ k R a × LocalFormula σ 1 R b)) :
    (∃ p ∈ negPairs i ps,
      p.1.Sat A anchors left ∧ p.2.Sat A (fun _ => y) right) ↔
      ∀ p ∈ ps, ¬ (p.1.Sat A anchors left ∧
        p.2.Sat A (fun _ => y) right) := by
  induction ps with
  | nil =>
      constructor
      · intro _ p hp
        simp at hp
      · intro _
        exact ⟨(trueLeft i, trueRight), by simp [negPairs],
          sat_trueLeft A anchors left i, sat_trueRight A y right⟩
  | cons p ps ih =>
      constructor
      · rintro ⟨q, hq, hq1, hq2⟩ p' hp'
        simp only [negPairs, List.mem_flatMap, List.mem_cons,
          List.not_mem_nil, or_false] at hq
        obtain ⟨d, hd, hqd⟩ := hq
        have hkey :
            (d.1.Sat A anchors left ∧ d.2.Sat A (fun _ => y) right) ∧
            ¬ (p.1.Sat A anchors left ∧ p.2.Sat A (fun _ => y) right) := by
          rcases hqd with rfl | rfl
          · have hq1' := (LocalFormula.sat_conjunction A anchors left
              (.not p.1) d.1).mp hq1
            exact ⟨⟨hq1'.2, hq2⟩, fun hp => hq1'.1 hp.1⟩
          · have hq2' := (LocalFormula.sat_conjunction A (fun _ => y) right
              (.not p.2) d.2).mp hq2
            exact ⟨⟨hq1, hq2'.2⟩, fun hp => hq2'.1 hp.2⟩
        rcases List.mem_cons.mp hp' with rfl | hp''
        · exact hkey.2
        · exact ih.mp ⟨d, hd, hkey.1⟩ p' hp''
      · intro h
        obtain ⟨d, hd, hd1, hd2⟩ :=
          ih.mpr fun p' hp' => h p' (List.mem_cons.mpr (Or.inr hp'))
        have hp := h p (List.mem_cons.mpr (Or.inl rfl))
        by_cases h1 : p.1.Sat A anchors left
        · refine ⟨(d.1, LocalFormula.conjunction (.not p.2) d.2), ?_,
            hd1, ?_⟩
          · simp only [negPairs, List.mem_flatMap, List.mem_cons]
            exact ⟨d, hd, Or.inr (Or.inl rfl)⟩
          · apply (LocalFormula.sat_conjunction A (fun _ => y) right
              (.not p.2) d.2).mpr
            exact ⟨(fun h2 => hp ⟨h1, h2⟩), hd2⟩
        · refine ⟨(LocalFormula.conjunction (.not p.1) d.1, d.2), ?_,
            ?_, hd2⟩
          · simp only [negPairs, List.mem_flatMap, List.mem_cons]
            exact ⟨d, hd, Or.inl rfl⟩
          · apply (LocalFormula.sat_conjunction A anchors left
              (.not p.1) d.1).mpr
            exact ⟨h1, hd1⟩

/-- Extract left arguments when every argument term is left-classified. -/
noncomputable def leftArgs {σ : Vocabulary} {k B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) {Q : σ.Relation}
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (h : ∀ i, ∃ t, splitTerm side (args i) = .inl t) :
    Fin (σ.arity Q) → LocalTerm σ k a :=
  fun i => Classical.choose (h i)

theorem splitTerm_leftArgs {σ : Vocabulary} {k B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) {Q : σ.Relation}
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (h : ∀ i, ∃ t, splitTerm side (args i) = .inl t) (i : Fin (σ.arity Q)) :
    splitTerm side (args i) = .inl (leftArgs side args h i) :=
  Classical.choose_spec (h i)

/-- Extract right arguments when every argument term is right-classified. -/
noncomputable def rightArgs {σ : Vocabulary} {k B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) {Q : σ.Relation}
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (h : ∀ i, ∃ t, splitTerm side (args i) = .inr t) :
    Fin (σ.arity Q) → LocalTerm σ 1 b :=
  fun i => Classical.choose (h i)

theorem splitTerm_rightArgs {σ : Vocabulary} {k B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) {Q : σ.Relation}
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (h : ∀ i, ∃ t, splitTerm side (args i) = .inr t) (i : Fin (σ.arity Q)) :
    splitTerm side (args i) = .inr (rightArgs side args h i) :=
  Classical.choose_spec (h i)

/-- Wrap the left member of every pair in a local existential. -/
def wrapLeft {σ : Vocabulary} {k R a b : ℕ} :
    List (LocalFormula σ k R (a + 1) × LocalFormula σ 1 R b) →
      List (LocalFormula σ k R a × LocalFormula σ 1 R b) :=
  List.map fun p => (.ex p.1, p.2)

/-- Wrap the right member in an existential explicitly guarded from the one
right anchor (excluding the constants, which belong to the left side). -/
noncomputable def wrapRight {σ : Vocabulary} {k R a b : ℕ} :
    List (LocalFormula σ k R a × LocalFormula σ 1 R (b + 1)) →
      List (LocalFormula σ k R a × LocalFormula σ 1 R b) :=
  List.map fun p => (p.1, .ex (LocalFormula.conjunction
    (nearAnchors R R (.bound (Fin.last b))) p.2))

/-- The finite separated disjunction associated to a local formula. -/
noncomputable def separate {σ : Vocabulary} {k R B a b : ℕ}
    (i0 : Fin k) (side : Fin B → Fin a ⊕ Fin b) :
    LocalFormula σ (k + 1) R B →
      List (LocalFormula σ k R a × LocalFormula σ 1 R b)
  | .rel Q args =>
      if hl : ∀ i, ∃ t, splitTerm side (args i) = .inl t then
        [(.rel Q (leftArgs side args hl), trueRight)]
      else if hr : ∀ i, ∃ t, splitTerm side (args i) = .inr t then
        [(trueLeft i0, .rel Q (rightArgs side args hr))]
      else []
  | .eq left right =>
      match splitTerm side left, splitTerm side right with
      | .inl l, .inl r => [(.eq l r, trueRight)]
      | .inr l, .inr r => [(trueLeft i0, .eq l r)]
      | _, _ => []
  | .not φ => negPairs i0 (separate i0 side φ)
  | .or φ ψ => separate i0 side φ ++ separate i0 side ψ
  | .ex φ =>
      wrapLeft (separate i0 (extendLeft side) φ) ++
        wrapRight (separate i0 (extendRight side) φ)

/-- Separation specialized to a closed local formula: there are no locally
bound variables to assign initially. -/
noncomputable def separateClosed {σ : Vocabulary} {k R : ℕ} (i0 : Fin k)
    (φ : LocalFormula σ (k + 1) R 0) :
    List (LocalFormula σ k R 0 × LocalFormula σ 1 R 0) :=
  separate i0 Fin.elim0 φ

theorem exists_cross_args {σ : Vocabulary} {k B a b : ℕ}
    (side : Fin B → Fin a ⊕ Fin b) {Q : σ.Relation}
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (hnl : ¬ ∀ i, ∃ t, splitTerm side (args i) = .inl t)
    (hnr : ¬ ∀ i, ∃ t, splitTerm side (args i) = .inr t) :
    ∃ i li j rj,
      splitTerm side (args i) = .inl li ∧
      splitTerm side (args j) = .inr rj := by
  push_neg at hnl hnr
  obtain ⟨j, hj⟩ := hnl
  obtain ⟨i, hi⟩ := hnr
  cases his : splitTerm side (args i) with
  | inl li =>
      cases hjs : splitTerm side (args j) with
      | inl lj => exact False.elim (hj lj hjs)
      | inr rj => exact ⟨i, li, j, rj, his, hjs⟩
  | inr ri => exact False.elim (hi ri his)

/-- Semantics of the explicitly right-guarded existential used by
`wrapRight`. -/
theorem sat_rightEx {σ : Vocabulary} {M : Type*} {R b : ℕ}
    (A : Structure σ M) (y : M) (bound : Fin b → M)
    (φ : LocalFormula σ 1 R (b + 1)) :
    (.ex (LocalFormula.conjunction
      (nearAnchors R R (.bound (Fin.last b))) φ) :
        LocalFormula σ 1 R b).Sat A (fun _ => y) bound ↔
      ∃ x, distanceAtMost A R y x ∧
        φ.Sat A (fun _ => y) (Fin.snoc bound x) := by
  simp only [LocalFormula.Sat, LocalFormula.sat_conjunction]
  constructor
  · rintro ⟨x, -, hnear, hφ⟩
    have hn := (sat_nearAnchors A (fun _ : Fin 1 => y)
      (Fin.snoc bound x) (.bound (Fin.last b)) (by omega)).mp hnear
    rcases hn with ⟨i, hi⟩
    exact ⟨x, by simpa [LocalTerm.eval] using hi, hφ⟩
  · rintro ⟨x, hxy, hφ⟩
    have hxBall : inBallAround A R (fun _ : Fin 1 => y) x :=
      Or.inl ⟨0, hxy⟩
    refine ⟨x, hxBall, ?_, hφ⟩
    apply (sat_nearAnchors A (fun _ : Fin 1 => y)
      (Fin.snoc bound x) (.bound (Fin.last b)) (by omega)).mpr
    exact ⟨0, by simpa [LocalTerm.eval] using hxy⟩

theorem sat_rel_left {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b) (Q : σ.Relation)
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (hl : ∀ i, ∃ t, splitTerm side (args i) = .inl t) :
    (LocalFormula.rel Q args : LocalFormula σ (k + 1) R B).Sat A
        (Fin.snoc anchors y) (combineBound side left right) ↔
      (LocalFormula.rel Q (leftArgs side args hl) :
        LocalFormula σ k R a).Sat A anchors left := by
  change A.relation Q _ ↔ A.relation Q _
  have htuple :
      (fun i => (args i).eval A (Fin.snoc anchors y)
        (combineBound side left right)) =
      (fun i => (leftArgs side args hl i).eval A anchors left) := by
    funext i
    exact eval_splitTerm_left A anchors y left right side (args i)
      (leftArgs side args hl i) (splitTerm_leftArgs side args hl i)
  rw [htuple]

theorem sat_rel_right {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b) (Q : σ.Relation)
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (hr : ∀ i, ∃ t, splitTerm side (args i) = .inr t) :
    (LocalFormula.rel Q args : LocalFormula σ (k + 1) R B).Sat A
        (Fin.snoc anchors y) (combineBound side left right) ↔
      (LocalFormula.rel Q (rightArgs side args hr) :
        LocalFormula σ 1 R b).Sat A (fun _ => y) right := by
  change A.relation Q _ ↔ A.relation Q _
  have htuple :
      (fun i => (args i).eval A (Fin.snoc anchors y)
        (combineBound side left right)) =
      (fun i => (rightArgs side args hr i).eval A (fun _ => y) right) := by
    funext i
    exact eval_splitTerm_right A anchors y left right side (args i)
      (rightArgs side args hr i) (splitTerm_rightArgs side args hr i)
  rw [htuple]

theorem not_sat_rel_cross {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (left : Fin a → M) (right : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b) (Q : σ.Relation)
    (args : Fin (σ.arity Q) → LocalTerm σ (k + 1) B)
    (hy : ¬ inBallAround A (2 * R + 1) anchors y)
    (hleft : ∀ i j, side i = .inl j → inBallAround A R anchors (left j))
    (hright : ∀ i j, side i = .inr j → distanceAtMost A R y (right j))
    (hnl : ¬ ∀ i, ∃ t, splitTerm side (args i) = .inl t)
    (hnr : ¬ ∀ i, ∃ t, splitTerm side (args i) = .inr t) :
    ¬ (LocalFormula.rel Q args : LocalFormula σ (k + 1) R B).Sat A
      (Fin.snoc anchors y) (combineBound side left right) := by
  intro hsat
  obtain ⟨i, li, j, rj, hi, hj⟩ := exists_cross_args side args hnl hnr
  have hli := value_left_inBall A anchors y left right side hleft
    (args i) li hi
  have hrj := value_right_near A anchors y left right side hright
    (args j) rj hj
  apply not_distance_one_cross A anchors y _ _ hy hli hrj
  exact relation_tuple_distance_one A hsat i j

theorem not_sat_eq_cross {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (leftEnv : Fin a → M) (rightEnv : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b)
    (hy : ¬ inBallAround A (2 * R + 1) anchors y)
    (hleft : ∀ i j, side i = .inl j → inBallAround A R anchors (leftEnv j))
    (hright : ∀ i j, side i = .inr j → distanceAtMost A R y (rightEnv j))
    (left right : LocalTerm σ (k + 1) B)
    (l : LocalTerm σ k a) (r : LocalTerm σ 1 b)
    (hl : splitTerm side left = .inl l)
    (hr : splitTerm side right = .inr r) :
    ¬ (LocalFormula.eq left right : LocalFormula σ (k + 1) R B).Sat A
      (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) := by
  intro heq
  change left.eval A (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) =
    right.eval A (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) at heq
  have hlBall := value_left_inBall A anchors y leftEnv rightEnv side hleft left l hl
  have hrNear := value_right_near A anchors y leftEnv rightEnv side hright right r hr
  apply not_distance_one_cross A anchors y _ _ hy hlBall hrNear
  exact distanceAtMost_mono A (r := 0) (s := 1) (by omega) heq

theorem sat_eq_left {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (leftEnv : Fin a → M) (rightEnv : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b)
    (left right : LocalTerm σ (k + 1) B)
    (l r : LocalTerm σ k a)
    (hl : splitTerm side left = .inl l)
    (hr : splitTerm side right = .inl r) :
    (LocalFormula.eq left right : LocalFormula σ (k + 1) R B).Sat A
        (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) ↔
      (LocalFormula.eq l r : LocalFormula σ k R a).Sat A anchors leftEnv := by
  change left.eval A (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) =
      right.eval A (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) ↔
    l.eval A anchors leftEnv = r.eval A anchors leftEnv
  rw [eval_splitTerm_left A anchors y leftEnv rightEnv side left l hl,
    eval_splitTerm_left A anchors y leftEnv rightEnv side right r hr]

theorem sat_eq_right {σ : Vocabulary} {M : Type*} {k B a b R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (leftEnv : Fin a → M) (rightEnv : Fin b → M)
    (side : Fin B → Fin a ⊕ Fin b)
    (left right : LocalTerm σ (k + 1) B)
    (l r : LocalTerm σ 1 b)
    (hl : splitTerm side left = .inr l)
    (hr : splitTerm side right = .inr r) :
    (LocalFormula.eq left right : LocalFormula σ (k + 1) R B).Sat A
        (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) ↔
      (LocalFormula.eq l r : LocalFormula σ 1 R b).Sat A
        (fun _ => y) rightEnv := by
  change left.eval A (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) =
      right.eval A (Fin.snoc anchors y) (combineBound side leftEnv rightEnv) ↔
    l.eval A (fun _ => y) rightEnv = r.eval A (fun _ => y) rightEnv
  rw [eval_splitTerm_right A anchors y leftEnv rightEnv side left l hl,
    eval_splitTerm_right A anchors y leftEnv rightEnv side right r hr]

/-- Correctness of the structural separation procedure. -/
theorem sat_separate {σ : Vocabulary} {M : Type*} {k R B : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M)
    (i0 : Fin k) (φ : LocalFormula σ (k + 1) R B) :
    ∀ {a b : ℕ} (side : Fin B → Fin a ⊕ Fin b)
      (left : Fin a → M) (right : Fin b → M),
      (¬ inBallAround A (2 * R + 1) anchors y) →
      (∀ i j, side i = .inl j → inBallAround A R anchors (left j)) →
      (∀ i j, side i = .inr j → distanceAtMost A R y (right j)) →
      (φ.Sat A (Fin.snoc anchors y) (combineBound side left right) ↔
        ∃ p ∈ separate i0 side φ,
          p.1.Sat A anchors left ∧ p.2.Sat A (fun _ => y) right) := by
  induction φ with
  | rel Q args =>
      intro a b side left right hy hleft hright
      by_cases hl : ∀ i, ∃ t, splitTerm side (args i) = .inl t
      · rw [sat_rel_left A anchors y left right side Q args hl]
        simp [separate, hl]
      · by_cases hr : ∀ i, ∃ t, splitTerm side (args i) = .inr t
        · rw [sat_rel_right A anchors y left right side Q args hr]
          simp [separate, hl, hr]
        · have hn := not_sat_rel_cross A anchors y left right side Q args
            hy hleft hright hl hr
          simp [separate, hl, hr, hn]
  | eq sourceLeft sourceRight =>
      intro a b side left right hy hleft hright
      cases hl : splitTerm side sourceLeft with
      | inl l =>
          cases hr : splitTerm side sourceRight with
          | inl r =>
              rw [sat_eq_left A anchors y left right side sourceLeft sourceRight l r hl hr]
              simp [separate, hl, hr]
          | inr r =>
              have hn := not_sat_eq_cross A anchors y left right side hy
                hleft hright sourceLeft sourceRight l r hl hr
              simp [separate, hl, hr, hn]
      | inr l =>
          cases hr : splitTerm side sourceRight with
          | inl r =>
              have hnrev := not_sat_eq_cross A anchors y left right side hy
                hleft hright sourceRight sourceLeft r l hr hl
              have hn : ¬ (LocalFormula.eq sourceLeft sourceRight :
                  LocalFormula σ (k + 1) R _).Sat A (Fin.snoc anchors y)
                    (combineBound side left right) := by
                intro hsat
                exact hnrev hsat.symm
              simp [separate, hl, hr, hn]
          | inr r =>
              rw [sat_eq_right A anchors y left right side sourceLeft sourceRight l r hl hr]
              simp [separate, hl, hr]
  | not ψ ih =>
      intro a b side left right hy hleft hright
      rw [show (LocalFormula.not ψ).Sat A (Fin.snoc anchors y)
          (combineBound side left right) ↔
          ¬ ψ.Sat A (Fin.snoc anchors y) (combineBound side left right) from Iff.rfl]
      rw [ih side left right hy hleft hright]
      rw [show separate i0 side (.not ψ) = negPairs i0 (separate i0 side ψ) from rfl]
      rw [sat_negPairs A anchors y left right i0 (separate i0 side ψ)]
      constructor
      · intro hn p hp hs
        exact hn ⟨p, hp, hs⟩
      · rintro h ⟨p, hp, hs⟩
        exact h p hp hs
  | or ψ χ ihψ ihχ =>
      intro a b side left right hy hleft hright
      rw [show (LocalFormula.or ψ χ).Sat A (Fin.snoc anchors y)
          (combineBound side left right) ↔
          ψ.Sat A (Fin.snoc anchors y) (combineBound side left right) ∨
          χ.Sat A (Fin.snoc anchors y) (combineBound side left right) from Iff.rfl]
      rw [ihψ side left right hy hleft hright,
        ihχ side left right hy hleft hright]
      simp only [separate, List.mem_append]
      constructor
      · rintro (⟨p, hp, hp1, hp2⟩ | ⟨p, hp, hp1, hp2⟩)
        · exact ⟨p, Or.inl hp, hp1, hp2⟩
        · exact ⟨p, Or.inr hp, hp1, hp2⟩
      · rintro ⟨p, hp, hp1, hp2⟩
        rcases hp with hp | hp
        · exact Or.inl ⟨p, hp, hp1, hp2⟩
        · exact Or.inr ⟨p, hp, hp1, hp2⟩
  | ex ψ ih =>
      intro a b side left right hy hleft hright
      -- The local witness belongs either to the left ball (including the
      -- constants) or to the radius-`R` ball of `y`.
      simp only [LocalFormula.Sat, inBall_snoc_iff]
      constructor
      · rintro ⟨x, hxLeft | hxRight, hxψ⟩
        · have hleft' : ∀ i j, extendLeft side i = .inl j →
              inBallAround A R anchors
                ((Fin.snoc left x : Fin (a + 1) → M) j) := by
            intro i j hij
            induction i using Fin.lastCases with
            | last =>
                simp [extendLeft] at hij
                subst j
                simpa using hxLeft
            | cast i =>
                cases hs : side i with
                | inl j' =>
                    simp [extendLeft, hs] at hij
                    subst j
                    simpa using hleft i j' hs
                | inr j' => simp [extendLeft, hs] at hij
          have hright' : ∀ i j, extendLeft side i = .inr j →
              distanceAtMost A R y (right j) := by
            intro i j hij
            induction i using Fin.lastCases with
            | last => simp [extendLeft] at hij
            | cast i =>
                cases hs : side i with
                | inl j' => simp [extendLeft, hs] at hij
                | inr j' =>
                    simp [extendLeft, hs] at hij
                    subst j
                    exact hright i j' hs
          have hbody := (ih (extendLeft side) (Fin.snoc left x) right
            hy hleft' hright').mp ?_
          · obtain ⟨p, hp, hp1, hp2⟩ := hbody
            refine ⟨(.ex p.1, p.2), ?_, ⟨x, hxLeft, hp1⟩, hp2⟩
            simp only [separate, List.mem_append, wrapLeft, List.mem_map]
            exact Or.inl ⟨p, hp, rfl⟩
          · rw [combineBound_extendLeft]
            exact hxψ
        · have hleft' : ∀ i j, extendRight side i = .inl j →
              inBallAround A R anchors (left j) := by
            intro i j hij
            induction i using Fin.lastCases with
            | last => simp [extendRight] at hij
            | cast i =>
                cases hs : side i with
                | inl j' =>
                    simp [extendRight, hs] at hij
                    subst j
                    exact hleft i j' hs
                | inr j' => simp [extendRight, hs] at hij
          have hright' : ∀ i j, extendRight side i = .inr j →
              distanceAtMost A R y
                ((Fin.snoc right x : Fin (b + 1) → M) j) := by
            intro i j hij
            induction i using Fin.lastCases with
            | last =>
                simp [extendRight] at hij
                subst j
                simpa using hxRight
            | cast i =>
                cases hs : side i with
                | inl j' => simp [extendRight, hs] at hij
                | inr j' =>
                    simp [extendRight, hs] at hij
                    subst j
                    simpa using hright i j' hs
          have hbody := (ih (extendRight side) left (Fin.snoc right x)
            hy hleft' hright').mp ?_
          · obtain ⟨p, hp, hp1, hp2⟩ := hbody
            refine ⟨(p.1, .ex (LocalFormula.conjunction
              (nearAnchors R R (.bound (Fin.last b))) p.2)), ?_, hp1, ?_⟩
            · simp only [separate, List.mem_append, wrapRight, List.mem_map]
              exact Or.inr ⟨p, hp, rfl⟩
            · apply (sat_rightEx A y right p.2).mpr
              exact ⟨x, hxRight, hp2⟩
          · rw [combineBound_extendRight]
            exact hxψ
      · rintro ⟨p, hp, hp1, hp2⟩
        simp only [separate, List.mem_append] at hp
        rcases hp with hp | hp
        · simp only [wrapLeft, List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          rcases hp1 with ⟨x, hxLeft, hq1⟩
          refine ⟨x, Or.inl hxLeft, ?_⟩
          rw [← combineBound_extendLeft]
          apply (ih (extendLeft side) (Fin.snoc left x) right hy ?_ ?_).mpr
          · exact ⟨q, hq, hq1, hp2⟩
          · intro i j hij
            induction i using Fin.lastCases with
            | last =>
                simp [extendLeft] at hij
                subst j
                simpa using hxLeft
            | cast i =>
                cases hs : side i with
                | inl j' =>
                    simp [extendLeft, hs] at hij
                    subst j
                    simpa using hleft i j' hs
                | inr j' => simp [extendLeft, hs] at hij
          · intro i j hij
            induction i using Fin.lastCases with
            | last => simp [extendLeft] at hij
            | cast i =>
                cases hs : side i with
                | inl j' => simp [extendLeft, hs] at hij
                | inr j' =>
                    simp [extendLeft, hs] at hij
                    subst j
                    exact hright i j' hs
        · simp only [wrapRight, List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          obtain ⟨x, hxRight, hq2⟩ := (sat_rightEx A y right q.2).mp hp2
          refine ⟨x, Or.inr hxRight, ?_⟩
          rw [← combineBound_extendRight]
          apply (ih (extendRight side) left (Fin.snoc right x) hy ?_ ?_).mpr
          · exact ⟨q, hq, hp1, hq2⟩
          · intro i j hij
            induction i using Fin.lastCases with
            | last => simp [extendRight] at hij
            | cast i =>
                cases hs : side i with
                | inl j' =>
                    simp [extendRight, hs] at hij
                    subst j
                    exact hleft i j' hs
                | inr j' => simp [extendRight, hs] at hij
          · intro i j hij
            induction i using Fin.lastCases with
            | last =>
                simp [extendRight] at hij
                subst j
                simpa using hxRight
            | cast i =>
                cases hs : side i with
                | inl j' => simp [extendRight, hs] at hij
                | inr j' =>
                    simp [extendRight, hs] at hij
                    subst j
                    simpa using hright i j' hs

theorem sat_separateClosed {σ : Vocabulary} {M : Type*} {k R : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (y : M) (i0 : Fin k)
    (φ : LocalFormula σ (k + 1) R 0)
    (hy : ¬ inBallAround A (2 * R + 1) anchors y) :
    φ.Sat A (Fin.snoc anchors y) Fin.elim0 ↔
      ∃ p ∈ separateClosed i0 φ,
        p.1.Sat A anchors Fin.elim0 ∧
          p.2.Sat A (fun _ => y) Fin.elim0 := by
  have h := sat_separate A anchors y i0 φ
    (a := 0) (b := 0) Fin.elim0 Fin.elim0 Fin.elim0 hy
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simpa [separateClosed, combineBound, Subsingleton.elim
    (combineBound (M := M) Fin.elim0 Fin.elim0 Fin.elim0) Fin.elim0] using h

end

end Lax185574Proofs.Gaifman.Separation
