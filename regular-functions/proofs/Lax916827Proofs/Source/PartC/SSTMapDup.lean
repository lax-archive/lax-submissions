/-
Post-composition of a streaming string transducer with the map duplicate
function (a step of the "regular to sst" half of Theorem `theorem:sst-two-way-equivalence` of
*Transducers*, M. Bojańczyk).

The construction is the one for map reverse (`SSTMapRev.lean`), with five
registers instead of three: the first and the last part of the content of a
register are each kept in two copies, since they get duplicated when they are
merged into the middle part.

As in `SSTMapRev.lean` the bookkeeping is organised around a *combination
operation* on tuples, which is associative, compatible with substitution, and
uses each part of each of its two arguments at most once -- the last point being
exactly the copyless restriction.
-/
import Lax916827Proofs.Source.PartC.SSTMapRev
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace MapDupSST

open scoped Classical

variable {W W' Z : Type}

/-! ### Tuples and their combination -/

/-- The five parts of the image of a string: two copies of the first block, the
middle, and two copies of the last block. -/
inductive P5 | fstA | fstB | mid | lstA | lstB
  deriving DecidableEq

instance : Fintype P5 :=
  ⟨{P5.fstA, P5.fstB, P5.mid, P5.lstA, P5.lstB}, fun x => by cases x <;> decide⟩

/-- The image of a string, decomposed. -/
abbrev Quin (W : Type) := Bool × List W × List W × List W × List W × List W

/-- The tuple of the empty string. -/
def unitQuin (W : Type) : Quin W := (false, [], [], [], [], [])

/-- The tuple of a concatenation, in terms of the tuples of the two factors. -/
def comb (σ : List W) : Quin W → Quin W → Quin W
  | (false, a₁, a₂, _, _, _), (false, a₁', a₂', _, _, _) =>
      (false, a₁ ++ a₁', a₂ ++ a₂', [], [], [])
  | (false, a₁, a₂, _, _, _), (true, a₁', a₂', b', c₁', c₂') =>
      (true, a₁ ++ a₁', a₂ ++ a₂', b', c₁', c₂')
  | (true, a₁, a₂, b, c₁, c₂), (false, a₁', a₂', _, _, _) =>
      (true, a₁, a₂, b, c₁ ++ a₁', c₂ ++ a₂')
  | (true, a₁, a₂, b, c₁, c₂), (true, a₁', a₂', b', c₁', c₂') =>
      (true, a₁, a₂, b ++ σ ++ (c₁ ++ a₁') ++ (c₂ ++ a₂') ++ b', c₁', c₂')

/-- The string described by a tuple. -/
def out (σ : List W) : Quin W → List W
  | (false, a₁, a₂, _, _, _) => a₁ ++ a₂
  | (true, a₁, a₂, b, c₁, c₂) => a₁ ++ a₂ ++ b ++ σ ++ c₁ ++ c₂

/-- The component of a tuple. -/
def comp : Quin W → P5 → List W
  | (_, a₁, _, _, _, _), P5.fstA => a₁
  | (_, _, a₂, _, _, _), P5.fstB => a₂
  | (_, _, _, b, _, _), P5.mid => b
  | (_, _, _, _, c₁, _), P5.lstA => c₁
  | (_, _, _, _, _, c₂), P5.lstB => c₂

/-- The tuple of a string, computed letter by letter. -/
def quinOf (σ : List W) (single : Z → Quin W) : List Z → Quin W
  | [] => unitQuin W
  | z :: s => comb σ (single z) (quinOf σ single s)

@[simp] lemma quinOf_nil (σ : List W) (single : Z → Quin W) :
    quinOf σ single ([] : List Z) = unitQuin W := rfl

lemma quinOf_cons (σ : List W) (single : Z → Quin W) (z : Z) (s : List Z) :
    quinOf σ single (z :: s) = comb σ (single z) (quinOf σ single s) := rfl

/-- A tuple is *good* if a string without separators has empty middle and last
parts. -/
def Good (t : Quin W) : Prop :=
  t.1 = false → t.2.2.2.1 = [] ∧ t.2.2.2.2.1 = [] ∧ t.2.2.2.2.2 = []

lemma good_unitQuin : Good (unitQuin W) := fun _ => ⟨rfl, rfl, rfl⟩

lemma good_comb (σ : List W) (v w : Quin W) : Good (comb σ v w) := by
  obtain ⟨b₁, a₁, a₂, c, d, e⟩ := v
  obtain ⟨b₂, a₁', a₂', c', d', e'⟩ := w
  cases b₁ <;> cases b₂ <;> intro h <;> simp_all [comb]

lemma good_quinOf (σ : List W) (single : Z → Quin W) (s : List Z) :
    Good (quinOf σ single s) := by
  cases s with
  | nil => exact good_unitQuin
  | cons z s => exact good_comb _ _ _

lemma comb_unitQuin_left {σ : List W} {t : Quin W} (h : Good t) :
    comb σ (unitQuin W) t = t := by
  obtain ⟨b, a₁, a₂, c, d, e⟩ := t
  cases b with
  | false =>
      obtain ⟨hc, hd, he⟩ := h rfl
      simp_all [comb, unitQuin]
  | true => simp [comb, unitQuin]

lemma comb_assoc (σ : List W) (u v w : Quin W) :
    comb σ (comb σ u v) w = comb σ u (comb σ v w) := by
  obtain ⟨b₁, u₁, u₂, u₃, u₄, u₅⟩ := u
  obtain ⟨b₂, v₁, v₂, v₃, v₄, v₅⟩ := v
  obtain ⟨b₃, w₁, w₂, w₃, w₄, w₅⟩ := w
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp [comb]

lemma quinOf_append (σ : List W) (single : Z → Quin W) (s t : List Z) :
    quinOf σ single (s ++ t) = comb σ (quinOf σ single s) (quinOf σ single t) := by
  induction s with
  | nil => exact (comb_unitQuin_left (good_quinOf σ single t)).symm
  | cons z s ih =>
      rw [List.cons_append, quinOf_cons, ih, quinOf_cons, comb_assoc]

/-! ### Transport along a substitution -/

/-- Applying a map to every component of a tuple. -/
def mapQuin (φ : List W → List W') (t : Quin W) : Quin W' :=
  (t.1, φ t.2.1, φ t.2.2.1, φ t.2.2.2.1, φ t.2.2.2.2.1, φ t.2.2.2.2.2)

lemma mapQuin_comb {φ : List W → List W'} (hφ : ∀ a b, φ (a ++ b) = φ a ++ φ b)
    (hnil : φ [] = []) {σ : List W} {σ' : List W'} (hσ : φ σ = σ') (v w : Quin W) :
    mapQuin φ (comb σ v w) = comb σ' (mapQuin φ v) (mapQuin φ w) := by
  obtain ⟨b₁, u₁, u₂, u₃, u₄, u₅⟩ := v
  obtain ⟨b₂, v₁, v₂, v₃, v₄, v₅⟩ := w
  cases b₁ <;> cases b₂ <;> simp [comb, mapQuin, hφ, hnil, hσ]

lemma mapQuin_out {φ : List W → List W'} (hφ : ∀ a b, φ (a ++ b) = φ a ++ φ b)
    {σ : List W} {σ' : List W'} (hσ : φ σ = σ') (t : Quin W) :
    φ (out σ t) = out σ' (mapQuin φ t) := by
  obtain ⟨b, a₁, a₂, c, d, e⟩ := t
  cases b <;> simp [out, mapQuin, hφ, hσ]

lemma mapQuin_unitQuin {φ : List W → List W'} (hnil : φ [] = []) :
    mapQuin φ (unitQuin W) = unitQuin W' := by simp [mapQuin, unitQuin, hnil]

/-! ### The semantics: the tuple of a string over `A₀ + 1` -/

variable {A₀ X : Type}

/-- The tuple of a single letter. -/
def semSingle : Option A₀ → Quin (Option A₀)
  | none => (true, [], [], [], [], [])
  | some a => (false, [some a], [some a], [], [], [])

/-- The tuple of a string over `A₀ + 1`. -/
def semQuin (v : List (Option A₀)) : Quin (Option A₀) := quinOf [none] semSingle v

lemma semQuin_append (u v : List (Option A₀)) :
    semQuin (u ++ v) = comb [none] (semQuin u) (semQuin v) :=
  quinOf_append _ _ u v

lemma semQuin_map_some (u : List A₀) :
    semQuin (u.map some) = (false, u.map some, u.map some, [], [], []) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      rw [List.map_cons, show (some a :: u.map some) = [some a] ++ u.map some from rfl,
        semQuin_append, ih]
      simp [semQuin, quinOf, semSingle, comb, unitQuin]

lemma semQuin_sep : semQuin ([none] : List (Option A₀)) = (true, [], [], [], [], []) := by
  simp [semQuin, quinOf, semSingle, comb, unitQuin]

/-- Map duplicate on a string without separators. -/
lemma out_semQuin_map_some (u : List A₀) :
    out [none] (semQuin (u.map some)) = mapDuplicate A₀ (u.map some) := by
  rw [semQuin_map_some, mapDuplicate, mapLift_map_some]
  simp [out]

lemma out_semQuin_aux : ∀ (n : ℕ) (v : List (Option A₀)), v.length ≤ n →
    out [none] (semQuin v) = mapDuplicate A₀ v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hv0 : v = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hv)
      subst hv0
      simpa using out_semQuin_map_some ([] : List A₀)
  | succ n ih =>
      intro v hv
      rcases MapRevSST.exists_split v with ⟨u, rfl⟩ | ⟨u, w, rfl, hlt⟩
      · exact out_semQuin_map_some u
      · have hwlen : w.length ≤ n := by simp at hv hlt ⊢; omega
        have hw : out [none] (semQuin w) = mapDuplicate A₀ w := ih w hwlen
        have hrhs : mapDuplicate A₀ (u.map some ++ none :: w)
            = (u ++ u).map some ++ none :: mapDuplicate A₀ w := by
          rw [mapDuplicate, mapLift_map_some_cons_none]
        rw [hrhs, ← hw, semQuin_append, semQuin_map_some,
          show ((none :: w) : List (Option A₀)) = [none] ++ w from rfl, semQuin_append,
          semQuin_sep]
        rcases hsem : semQuin w with ⟨b, a₁, a₂, c, d, e⟩
        cases b <;> simp [comb, out]

/-- **The tuple computes map duplicate.** -/
lemma out_semQuin (v : List (Option A₀)) : out [none] (semQuin v) = mapDuplicate A₀ v :=
  out_semQuin_aux v.length v le_rfl

/-! ### The symbolic tuple -/

/-- The tuple of a single letter of a register update. -/
def symSingle (hs : X → Bool) :
    X ⊕ Option A₀ → Quin ((X × P5) ⊕ Option A₀)
  | Sum.inl y =>
      (hs y, [Sum.inl (y, P5.fstA)], [Sum.inl (y, P5.fstB)], [Sum.inl (y, P5.mid)],
        [Sum.inl (y, P5.lstA)], [Sum.inl (y, P5.lstB)])
  | Sum.inr none => (true, [], [], [], [], [])
  | Sum.inr (some a) => (false, [Sum.inr (some a)], [Sum.inr (some a)], [], [], [])

/-- The tuple of a register update. -/
def symQuin (hs : X → Bool) (s : List (X ⊕ Option A₀)) : Quin ((X × P5) ⊕ Option A₀) :=
  quinOf [Sum.inr none] (symSingle hs) s

lemma symQuin_cons (hs : X → Bool) (z : X ⊕ Option A₀) (s : List (X ⊕ Option A₀)) :
    symQuin hs (z :: s) = comb [Sum.inr none] (symSingle hs z) (symQuin hs s) := rfl

lemma subst_append_hom (η' : X × P5 → List (Option A₀)) (a b : List ((X × P5) ⊕ Option A₀)) :
    SST.subst η' (a ++ b) = SST.subst η' a ++ SST.subst η' b := SST.subst_append _ _ _

/-- **The transfer lemma**: substituting the register contents into the symbolic
tuple gives the tuple of the substituted string. -/
lemma mapQuin_symQuin {η : X → List (Option A₀)} {η' : X × P5 → List (Option A₀)}
    {hs : X → Bool}
    (hinv : ∀ y, mapQuin (SST.subst η') (symSingle hs (Sum.inl y)) = semQuin (η y))
    (s : List (X ⊕ Option A₀)) :
    mapQuin (SST.subst η') (symQuin hs s) = semQuin (SST.subst η s) := by
  induction s with
  | nil => exact mapQuin_unitQuin rfl
  | cons z s ih =>
      rw [symQuin_cons, mapQuin_comb (subst_append_hom η') rfl
        (show SST.subst η' [Sum.inr none] = [none] from rfl), ih]
      cases z with
      | inl y =>
          rw [hinv y, SST.subst_cons_inl, semQuin_append]
      | inr b =>
          have hb : mapQuin (SST.subst η') (symSingle hs (Sum.inr b)) = semQuin [b] := by
            cases b with
            | none => rfl
            | some a => rfl
          rw [hb, SST.subst_cons_inr, show (b :: SST.subst η s) = [b] ++ SST.subst η s from rfl,
            semQuin_append]

/-! ### The copyless restriction -/

section Counting

variable [DecidableEq X]

/-- All the register names occurring in a symbolic tuple. -/
def Lall (t : Quin ((X × P5) ⊕ Option A₀)) : List (X × P5) :=
  regsOf (comp t P5.fstA) ++ regsOf (comp t P5.fstB) ++ regsOf (comp t P5.mid) ++
    regsOf (comp t P5.lstA) ++ regsOf (comp t P5.lstB)

lemma count_Lall_comb (v w : Quin ((X × P5) ⊕ Option A₀)) (r : X × P5) :
    (Lall (comb [Sum.inr none] v w)).count r ≤ (Lall v).count r + (Lall w).count r := by
  obtain ⟨b₁, u₁, u₂, u₃, u₄, u₅⟩ := v
  obtain ⟨b₂, v₁, v₂, v₃, v₄, v₅⟩ := w
  cases b₁ <;> cases b₂ <;>
    simp [comb, Lall, comp, regsOf, List.count_append] <;> omega

lemma count_Lall_symSingle (hs : X → Bool) (z : X ⊕ Option A₀) (r : X × P5) :
    (Lall (symSingle hs z)).count r ≤ (regsOf [z]).count r.1 := by
  cases z with
  | inl y =>
      obtain ⟨y', j⟩ := r
      by_cases hy : y' = y
      · subst hy
        cases j <;> simp [Lall, comp, symSingle, regsOf]
      · cases j <;> simp [Lall, comp, symSingle, regsOf, List.count_cons]
  | inr b =>
      cases b <;> simp [Lall, comp, symSingle, regsOf]

lemma count_Lall_symQuin (hs : X → Bool) (s : List (X ⊕ Option A₀)) (r : X × P5) :
    (Lall (symQuin hs s)).count r ≤ (regsOf s).count r.1 := by
  induction s with
  | nil => simp [Lall, symQuin, unitQuin, comp, regsOf]
  | cons z s ih =>
      rw [symQuin_cons]
      have h1 := count_Lall_comb (symSingle hs z) (symQuin hs s) r
      have h2 := count_Lall_symSingle hs z r
      have h3 : (regsOf (z :: s)).count r.1 = (regsOf [z]).count r.1 + (regsOf s).count r.1 := by
        rw [show (z :: s) = [z] ++ s from rfl, regsOf.append, List.count_append]
      omega

lemma mem_of_mem_comp {hs : X → Bool} {s : List (X ⊕ Option A₀)} {j : P5} {r : X × P5}
    (h : r ∈ regsOf (comp (symQuin hs s) j)) : r.1 ∈ regsOf s := by
  have hle := count_Lall_symQuin hs s r
  have h1 : 1 ≤ (Lall (symQuin hs s)).count r := by
    have : 1 ≤ (regsOf (comp (symQuin hs s) j)).count r := List.count_pos_iff.2 h
    cases j <;>
      · simp only [Lall, List.count_append]
        omega
  exact List.count_pos_iff.1 (by omega)

end Counting

/-! ### The new sst -/

/-- The sst computing `mapDuplicate ∘ T.eval`: its registers are the five parts
of the registers of `T`, and its state remembers, for every register of `T`,
whether its content contains a separator. -/
noncomputable def mdComp {A QT : Type} [Fintype X] (T : SST A (Option A₀) QT X) :
    SST A (Option A₀) (QT × (X → Bool)) (X × P5) where
  init := (T.init, fun _ => false)
  step := fun p a =>
    (((T.step p.1 a).1, fun x => (symQuin p.2 ((T.step p.1 a).2 x)).1),
      fun xj => comp (symQuin p.2 ((T.step p.1 a).2 xj.1)) xj.2)
  step_copyless := by
    classical
    rintro ⟨qT, hs⟩ a
    show Copyless (fun xj : X × P5 => comp (symQuin hs ((T.step qT a).2 xj.1)) xj.2)
    have h := T.step_copyless qT a
    rw [copyless_iff] at h ⊢
    constructor
    · rintro ⟨x, j⟩
      show (regsOf (comp (symQuin hs ((T.step qT a).2 x)) j)).Nodup
      refine List.nodup_iff_count_le_one.2 (fun r => ?_)
      have hle := count_Lall_symQuin hs ((T.step qT a).2 x) r
      have hx : (regsOf ((T.step qT a).2 x)).count r.1 ≤ 1 :=
        List.nodup_iff_count_le_one.1 (h.1 x) r.1
      have hj : (regsOf (comp (symQuin hs ((T.step qT a).2 x)) j)).count r
          ≤ (Lall (symQuin hs ((T.step qT a).2 x))).count r := by
        cases j <;>
          · simp only [Lall, List.count_append]
            omega
      omega
    · rintro ⟨x, j⟩ ⟨x', j'⟩ hne r hr hr'
      simp only at hr hr'
      by_cases hxx : x = x'
      · subst hxx
        have hjj : j ≠ j' := fun hh => hne (by rw [hh])
        have hle := count_Lall_symQuin hs ((T.step qT a).2 x) r
        have hx : (regsOf ((T.step qT a).2 x)).count r.1 ≤ 1 :=
          List.nodup_iff_count_le_one.1 (h.1 x) r.1
        have h1 : 1 ≤ (regsOf (comp (symQuin hs ((T.step qT a).2 x)) j)).count r :=
          List.count_pos_iff.2 hr
        have h2 : 1 ≤ (regsOf (comp (symQuin hs ((T.step qT a).2 x)) j')).count r :=
          List.count_pos_iff.2 hr'
        have hsum : (regsOf (comp (symQuin hs ((T.step qT a).2 x)) j)).count r
            + (regsOf (comp (symQuin hs ((T.step qT a).2 x)) j')).count r
            ≤ (Lall (symQuin hs ((T.step qT a).2 x))).count r := by
          cases j <;> cases j' <;> simp_all only [ne_eq, not_true_eq_false] <;>
            · simp only [Lall, List.count_append]
              omega
        omega
      · exact h.2 x x' hxx r.1 (mem_of_mem_comp hr) (mem_of_mem_comp hr')
  final := fun p => out [Sum.inr none] (symQuin p.2 (T.final p.1))

lemma mapQuin_subst_single (η' : X × P5 → List (Option A₀)) (hs : X → Bool) (x : X) :
    mapQuin (SST.subst η') (symSingle hs (Sum.inl x))
      = (hs x, η' (x, P5.fstA), η' (x, P5.fstB), η' (x, P5.mid), η' (x, P5.lstA),
          η' (x, P5.lstB)) := by
  simp [mapQuin, symSingle, SST.subst]

lemma mapQuin_eq_comp (φ : List ((X × P5) ⊕ Option A₀) → List (Option A₀))
    (t : Quin ((X × P5) ⊕ Option A₀)) :
    mapQuin φ t = (t.1, φ (comp t P5.fstA), φ (comp t P5.fstB), φ (comp t P5.mid),
      φ (comp t P5.lstA), φ (comp t P5.lstB)) := rfl

lemma mdComp_eval {A QT : Type} [Fintype X] (T : SST A (Option A₀) QT X) (w : List A) :
    (mdComp T).eval w = mapDuplicate A₀ (T.eval w) := by
  refine SST.eval_of_sim (T := T) (T' := mdComp T) (p := mapDuplicate A₀)
    (fun c c' => c'.1.1 = c.1 ∧ ∀ x,
      mapQuin (SST.subst c'.2) (symSingle c'.1.2 (Sum.inl x)) = semQuin (c.2 x))
    ⟨rfl, fun x => by rw [mapQuin_subst_single]; rfl⟩ ?_ ?_ w
  · rintro ⟨qT, η⟩ ⟨⟨qT', hs⟩, η'⟩ a ⟨hq, hinv⟩
    cases hq
    refine ⟨rfl, fun x => ?_⟩
    have key := mapQuin_symQuin (η := η) (η' := η') hinv ((T.step qT a).2 x)
    rw [mapQuin_eq_comp] at key
    rw [mapQuin_subst_single]
    exact key
  · rintro ⟨qT, η⟩ ⟨⟨qT', hs⟩, η'⟩ ⟨hq, hinv⟩
    cases hq
    have h := mapQuin_symQuin (η := η) (η' := η') hinv (T.final qT)
    show SST.subst η' (out [Sum.inr none] (symQuin hs (T.final qT)))
      = mapDuplicate A₀ (SST.subst η (T.final qT))
    rw [show SST.subst η' (out [Sum.inr none] (symQuin hs (T.final qT)))
        = out [none] (mapQuin (SST.subst η') (symQuin hs (T.final qT))) from
      mapQuin_out (subst_append_hom η') rfl _, h, out_semQuin]

end MapDupSST

/-- **Post-composition with map duplicate.**  If `f` is computed by an sst, then
so is `map duplicate ∘ f`. -/
theorem isSST_comp_mapDuplicate {A A₀ : Type} {f : List A → List (Option A₀)} (hf : IsSST f) :
    IsSST (fun w => mapDuplicate A₀ (f w)) := by
  obtain ⟨QT, X, hQT, hX, T, rfl⟩ := hf
  haveI := hQT
  exact ⟨QT × (X → Bool), X × MapDupSST.P5, inferInstance, inferInstance,
    MapDupSST.mdComp T, funext fun w => MapDupSST.mdComp_eval T w⟩

end Lax916827Proofs.Transducers
