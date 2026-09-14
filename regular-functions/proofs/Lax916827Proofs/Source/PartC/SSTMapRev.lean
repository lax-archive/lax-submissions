/-
Post-composition of a streaming string transducer with the map reverse function
(a step of the "regular to sst" half of Theorem `theorem:sst-two-way-equivalence` of *Transducers*,
M. Bojańczyk).

Following the book, every register `X` of the sst is replaced by three
registers, corresponding to the three parts of its content

  (part before the first separator) (part between the first and the last
  separator) (part after the last separator),

which store, respectively, the reverse of the first part, the image of the
middle part under map reverse, and the reverse of the last part.  The state of
the new sst remembers which registers contain a separator, which is what is
needed to combine the three parts of a concatenation.

The bookkeeping is organised around the *combination operation* `comb` on
triples: it is associative, it is compatible with substitution, and -- this is
the copyless restriction -- it uses each of the three parts of each of its two
arguments at most once.
-/
import Lax916827Proofs.Source.PartC.RegularDef
import Lax916827Proofs.Source.PartC.ContAux
import Lax916827Proofs.Source.PartC.SSTComp
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace MapRevSST

open scoped Classical

variable {W W' Z : Type}

/-! ### Triples and their combination -/

/-- The three parts of the image of a string: the first block, the middle, and
the last block. -/
inductive P3 | fst | mid | lst
  deriving DecidableEq

instance : Fintype P3 := ⟨{P3.fst, P3.mid, P3.lst}, fun x => by cases x <;> decide⟩

/-- The image of a string, decomposed: the flag says whether the string contains
a separator, and the three components are the images of the first block, of the
middle part (with a leading separator before each of its blocks) and of the last
block. -/
abbrev Tri (W : Type) := Bool × List W × List W × List W

/-- The triple of the empty string. -/
def unitTri (W : Type) : Tri W := (false, [], [], [])

/-- The triple of a concatenation, in terms of the triples of the two factors.
Each part of each argument is used at most once, which is what makes the
resulting register updates copyless. -/
def comb (σ : List W) : Tri W → Tri W → Tri W
  | (false, a₁, _, _), (false, a₂, _, _) => (false, a₂ ++ a₁, [], [])
  | (false, a₁, _, _), (true, a₂, b₂, c₂) => (true, a₂ ++ a₁, b₂, c₂)
  | (true, a₁, b₁, c₁), (false, a₂, _, _) => (true, a₁, b₁, a₂ ++ c₁)
  | (true, a₁, b₁, c₁), (true, a₂, b₂, c₂) => (true, a₁, b₁ ++ σ ++ a₂ ++ c₁ ++ b₂, c₂)

/-- The string described by a triple. -/
def out (σ : List W) : Tri W → List W
  | (false, a, _, _) => a
  | (true, a, b, c) => a ++ b ++ σ ++ c

/-- The component of a triple. -/
def comp : Tri W → P3 → List W
  | (_, a, _, _), P3.fst => a
  | (_, _, b, _), P3.mid => b
  | (_, _, _, c), P3.lst => c

/-- The triple of a string, computed letter by letter. -/
def triOf (σ : List W) (single : Z → Tri W) : List Z → Tri W
  | [] => unitTri W
  | z :: s => comb σ (single z) (triOf σ single s)

@[simp] lemma triOf_nil (σ : List W) (single : Z → Tri W) :
    triOf σ single ([] : List Z) = unitTri W := rfl

lemma triOf_cons (σ : List W) (single : Z → Tri W) (z : Z) (s : List Z) :
    triOf σ single (z :: s) = comb σ (single z) (triOf σ single s) := rfl

/-- A triple is *good* if a string without separators has an empty middle part
and an empty last part. -/
def Good (t : Tri W) : Prop := t.1 = false → t.2.2.1 = [] ∧ t.2.2.2 = []

lemma good_unitTri : Good (unitTri W) := fun _ => ⟨rfl, rfl⟩

lemma good_comb (σ : List W) (v w : Tri W) : Good (comb σ v w) := by
  obtain ⟨b₁, a₁, c₁, d₁⟩ := v
  obtain ⟨b₂, a₂, c₂, d₂⟩ := w
  cases b₁ <;> cases b₂ <;> intro h <;> simp_all [comb]

lemma good_triOf (σ : List W) (single : Z → Tri W) (s : List Z) :
    Good (triOf σ single s) := by
  cases s with
  | nil => exact good_unitTri
  | cons z s => exact good_comb _ _ _

lemma comb_unitTri_left {σ : List W} {t : Tri W} (h : Good t) :
    comb σ (unitTri W) t = t := by
  obtain ⟨b, a, c, d⟩ := t
  cases b with
  | false =>
      obtain ⟨hc, hd⟩ := h rfl
      simp_all [comb, unitTri]
  | true => simp [comb, unitTri]

lemma comb_assoc (σ : List W) (u v w : Tri W) :
    comb σ (comb σ u v) w = comb σ u (comb σ v w) := by
  obtain ⟨b₁, a₁, c₁, d₁⟩ := u
  obtain ⟨b₂, a₂, c₂, d₂⟩ := v
  obtain ⟨b₃, a₃, c₃, d₃⟩ := w
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp [comb]

lemma triOf_append (σ : List W) (single : Z → Tri W) (s t : List Z) :
    triOf σ single (s ++ t) = comb σ (triOf σ single s) (triOf σ single t) := by
  induction s with
  | nil => exact (comb_unitTri_left (good_triOf σ single t)).symm
  | cons z s ih =>
      rw [List.cons_append, triOf_cons, ih, triOf_cons, comb_assoc]

/-! ### Transport along a substitution -/

/-- Applying a map to every component of a triple. -/
def mapTri (φ : List W → List W') (t : Tri W) : Tri W' := (t.1, φ t.2.1, φ t.2.2.1, φ t.2.2.2)

lemma mapTri_comb {φ : List W → List W'} (hφ : ∀ a b, φ (a ++ b) = φ a ++ φ b)
    (hnil : φ [] = []) {σ : List W} {σ' : List W'} (hσ : φ σ = σ') (v w : Tri W) :
    mapTri φ (comb σ v w) = comb σ' (mapTri φ v) (mapTri φ w) := by
  obtain ⟨b₁, a₁, c₁, d₁⟩ := v
  obtain ⟨b₂, a₂, c₂, d₂⟩ := w
  cases b₁ <;> cases b₂ <;>
    simp [comb, mapTri, hφ, hnil, hσ]

lemma mapTri_out {φ : List W → List W'} (hφ : ∀ a b, φ (a ++ b) = φ a ++ φ b)
    {σ : List W} {σ' : List W'} (hσ : φ σ = σ') (t : Tri W) :
    φ (out σ t) = out σ' (mapTri φ t) := by
  obtain ⟨b, a, c, d⟩ := t
  cases b <;> simp [out, mapTri, hφ, hσ]

lemma mapTri_unitTri {φ : List W → List W'} (hnil : φ [] = []) :
    mapTri φ (unitTri W) = unitTri W' := by simp [mapTri, unitTri, hnil]

end MapRevSST

/-! ### The semantics: the triple of a string over `A₀ + 1` -/

namespace MapRevSST

variable {A₀ : Type}

/-- The triple of a single letter. -/
def semSingle : Option A₀ → Tri (Option A₀)
  | none => (true, [], [], [])
  | some a => (false, [some a], [], [])

/-- The triple of a string over `A₀ + 1`. -/
def semTri (v : List (Option A₀)) : Tri (Option A₀) := triOf [none] semSingle v

lemma semTri_append (u v : List (Option A₀)) :
    semTri (u ++ v) = comb [none] (semTri u) (semTri v) :=
  triOf_append _ _ u v

lemma semTri_map_some (u : List A₀) :
    semTri (u.map some) = (false, (u.reverse).map some, [], []) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      rw [List.map_cons, show (some a :: u.map some) = [some a] ++ u.map some from rfl,
        semTri_append, ih]
      simp [semTri, triOf, semSingle, comb, unitTri]

lemma semTri_sep : semTri ([none] : List (Option A₀)) = (true, [], [], []) := by
  simp [semTri, triOf, semSingle, comb, unitTri]

/-- Every string over `A₀ + 1` is either free of separators or splits at its
first separator. -/
lemma exists_split (v : List (Option A₀)) :
    (∃ u : List A₀, v = u.map some) ∨
      ∃ (u : List A₀) (w : List (Option A₀)), v = u.map some ++ none :: w ∧
        w.length < v.length := by
  induction v with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons x v ih =>
      cases x with
      | none => exact Or.inr ⟨[], v, rfl, by simp⟩
      | some a =>
          rcases ih with ⟨u, rfl⟩ | ⟨u, w, rfl, hlt⟩
          · exact Or.inl ⟨a :: u, by simp⟩
          · exact Or.inr ⟨a :: u, w, by simp, by simpa using Nat.lt_succ_of_lt hlt⟩

/-- Map reverse on a string without separators. -/
lemma out_semTri_map_some (u : List A₀) :
    out [none] (semTri (u.map some)) = mapReverse A₀ (u.map some) := by
  rw [semTri_map_some, mapReverse, mapLift_map_some]
  rfl

lemma out_semTri_aux : ∀ (n : ℕ) (v : List (Option A₀)), v.length ≤ n →
    out [none] (semTri v) = mapReverse A₀ v := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hv0 : v = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hv)
      subst hv0
      simpa using out_semTri_map_some ([] : List A₀)
  | succ n ih =>
      intro v hv
      rcases exists_split v with ⟨u, rfl⟩ | ⟨u, w, rfl, hlt⟩
      · exact out_semTri_map_some u
      · have hwlen : w.length ≤ n := by simp at hv hlt ⊢; omega
        have hw : out [none] (semTri w) = mapReverse A₀ w := ih w hwlen
        have hrhs : mapReverse A₀ (u.map some ++ none :: w)
            = (u.reverse).map some ++ none :: mapReverse A₀ w := by
          rw [mapReverse, mapLift_map_some_cons_none]
        rw [hrhs, ← hw, semTri_append, semTri_map_some,
          show ((none :: w) : List (Option A₀)) = [none] ++ w from rfl, semTri_append,
          semTri_sep]
        rcases hsem : semTri w with ⟨b, a, c, d⟩
        cases b <;> simp [comb, out]

/-- **The triple computes map reverse.** -/
lemma out_semTri (v : List (Option A₀)) : out [none] (semTri v) = mapReverse A₀ v :=
  out_semTri_aux v.length v le_rfl

end MapRevSST

/-! ### The symbolic triple -/

namespace MapRevSST

variable {A₀ X : Type}

/-- The triple of a single letter of a register update: a register `y`
contributes its three parts, a letter contributes itself, and the separator
contributes the flag. -/
def symSingle (hs : X → Bool) :
    X ⊕ Option A₀ → Tri ((X × P3) ⊕ Option A₀)
  | Sum.inl y => (hs y, [Sum.inl (y, P3.fst)], [Sum.inl (y, P3.mid)], [Sum.inl (y, P3.lst)])
  | Sum.inr none => (true, [], [], [])
  | Sum.inr (some a) => (false, [Sum.inr (some a)], [], [])

/-- The triple of a register update. -/
def symTri (hs : X → Bool) (s : List (X ⊕ Option A₀)) : Tri ((X × P3) ⊕ Option A₀) :=
  triOf [Sum.inr none] (symSingle hs) s

lemma symTri_cons (hs : X → Bool) (z : X ⊕ Option A₀) (s : List (X ⊕ Option A₀)) :
    symTri hs (z :: s) = comb [Sum.inr none] (symSingle hs z) (symTri hs s) := rfl

lemma subst_append_hom (η' : X × P3 → List (Option A₀)) (a b : List ((X × P3) ⊕ Option A₀)) :
    SST.subst η' (a ++ b) = SST.subst η' a ++ SST.subst η' b := SST.subst_append _ _ _

/-- **The transfer lemma**: substituting the register contents into the symbolic
triple gives the triple of the substituted string. -/
lemma mapTri_symTri {η : X → List (Option A₀)} {η' : X × P3 → List (Option A₀)}
    {hs : X → Bool}
    (hinv : ∀ y, mapTri (SST.subst η') (symSingle hs (Sum.inl y)) = semTri (η y))
    (s : List (X ⊕ Option A₀)) :
    mapTri (SST.subst η') (symTri hs s) = semTri (SST.subst η s) := by
  induction s with
  | nil => exact mapTri_unitTri rfl
  | cons z s ih =>
      rw [symTri_cons, mapTri_comb (subst_append_hom η') rfl
        (show SST.subst η' [Sum.inr none] = [none] from rfl), ih]
      cases z with
      | inl y =>
          rw [hinv y, SST.subst_cons_inl, semTri_append]
      | inr b =>
          have hb : mapTri (SST.subst η') (symSingle hs (Sum.inr b)) = semTri [b] := by
            cases b with
            | none => rfl
            | some a => rfl
          rw [hb, SST.subst_cons_inr, show (b :: SST.subst η s) = [b] ++ SST.subst η s from rfl,
            semTri_append]

/-! ### The copyless restriction -/

section Counting

variable [DecidableEq X]

/-- All the register names occurring in a symbolic triple. -/
def Lall (t : Tri ((X × P3) ⊕ Option A₀)) : List (X × P3) :=
  regsOf (comp t P3.fst) ++ regsOf (comp t P3.mid) ++ regsOf (comp t P3.lst)

lemma count_Lall_comb (v w : Tri ((X × P3) ⊕ Option A₀)) (r : X × P3) :
    (Lall (comb [Sum.inr none] v w)).count r ≤ (Lall v).count r + (Lall w).count r := by
  obtain ⟨b₁, a₁, c₁, d₁⟩ := v
  obtain ⟨b₂, a₂, c₂, d₂⟩ := w
  cases b₁ <;> cases b₂ <;>
    simp [comb, Lall, comp, regsOf, List.count_append] <;> omega

lemma count_Lall_symSingle (hs : X → Bool) (z : X ⊕ Option A₀) (r : X × P3) :
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

lemma count_Lall_symTri (hs : X → Bool) (s : List (X ⊕ Option A₀)) (r : X × P3) :
    (Lall (symTri hs s)).count r ≤ (regsOf s).count r.1 := by
  induction s with
  | nil => simp [Lall, symTri, unitTri, comp, regsOf]
  | cons z s ih =>
      rw [symTri_cons]
      have h1 := count_Lall_comb (symSingle hs z) (symTri hs s) r
      have h2 := count_Lall_symSingle hs z r
      have h3 : (regsOf (z :: s)).count r.1 = (regsOf [z]).count r.1 + (regsOf s).count r.1 := by
        rw [show (z :: s) = [z] ++ s from rfl, regsOf.append, List.count_append]
      omega

lemma mem_of_mem_comp {hs : X → Bool} {s : List (X ⊕ Option A₀)} {j : P3} {r : X × P3}
    (h : r ∈ regsOf (comp (symTri hs s) j)) : r.1 ∈ regsOf s := by
  have hle := count_Lall_symTri hs s r
  have h1 : 1 ≤ (Lall (symTri hs s)).count r := by
    have : 1 ≤ (regsOf (comp (symTri hs s) j)).count r := List.count_pos_iff.2 h
    cases j <;>
      · simp only [Lall, List.count_append]
        omega
  exact List.count_pos_iff.1 (by omega)

end Counting

/-! ### The new sst -/

/-- The sst computing `mapReverse ∘ T.eval`: its registers are the three parts
of the registers of `T`, and its state remembers, for every register of `T`,
whether its content contains a separator. -/
noncomputable def mrComp {A QT : Type} [Fintype X] (T : SST A (Option A₀) QT X) :
    SST A (Option A₀) (QT × (X → Bool)) (X × P3) where
  init := (T.init, fun _ => false)
  step := fun p a =>
    (((T.step p.1 a).1, fun x => (symTri p.2 ((T.step p.1 a).2 x)).1),
      fun xj => comp (symTri p.2 ((T.step p.1 a).2 xj.1)) xj.2)
  step_copyless := by
    classical
    rintro ⟨qT, hs⟩ a
    show Copyless (fun xj : X × P3 => comp (symTri hs ((T.step qT a).2 xj.1)) xj.2)
    have h := T.step_copyless qT a
    rw [copyless_iff] at h ⊢
    constructor
    · rintro ⟨x, j⟩
      show (regsOf (comp (symTri hs ((T.step qT a).2 x)) j)).Nodup
      refine List.nodup_iff_count_le_one.2 (fun r => ?_)
      have hle := count_Lall_symTri hs ((T.step qT a).2 x) r
      have hx : (regsOf ((T.step qT a).2 x)).count r.1 ≤ 1 :=
        List.nodup_iff_count_le_one.1 (h.1 x) r.1
      have hj : (regsOf (comp (symTri hs ((T.step qT a).2 x)) j)).count r
          ≤ (Lall (symTri hs ((T.step qT a).2 x))).count r := by
        cases j <;>
          · simp only [Lall, List.count_append]
            omega
      omega
    · rintro ⟨x, j⟩ ⟨x', j'⟩ hne r hr hr'
      simp only at hr hr'
      by_cases hxx : x = x'
      · subst hxx
        have hjj : j ≠ j' := fun hh => hne (by rw [hh])
        have hle := count_Lall_symTri hs ((T.step qT a).2 x) r
        have hx : (regsOf ((T.step qT a).2 x)).count r.1 ≤ 1 :=
          List.nodup_iff_count_le_one.1 (h.1 x) r.1
        have h1 : 1 ≤ (regsOf (comp (symTri hs ((T.step qT a).2 x)) j)).count r :=
          List.count_pos_iff.2 hr
        have h2 : 1 ≤ (regsOf (comp (symTri hs ((T.step qT a).2 x)) j')).count r :=
          List.count_pos_iff.2 hr'
        have hsum : (regsOf (comp (symTri hs ((T.step qT a).2 x)) j)).count r
            + (regsOf (comp (symTri hs ((T.step qT a).2 x)) j')).count r
            ≤ (Lall (symTri hs ((T.step qT a).2 x))).count r := by
          cases j <;> cases j' <;> simp_all only [ne_eq, not_true_eq_false] <;>
            · simp only [Lall, List.count_append]
              omega
        omega
      · exact h.2 x x' hxx r.1 (mem_of_mem_comp hr) (mem_of_mem_comp hr')
  final := fun p => out [Sum.inr none] (symTri p.2 (T.final p.1))

lemma mapTri_subst_single (η' : X × P3 → List (Option A₀)) (hs : X → Bool) (x : X) :
    mapTri (SST.subst η') (symSingle hs (Sum.inl x))
      = (hs x, η' (x, P3.fst), η' (x, P3.mid), η' (x, P3.lst)) := by
  simp [mapTri, symSingle, SST.subst]

lemma mapTri_eq_comp (φ : List ((X × P3) ⊕ Option A₀) → List (Option A₀))
    (t : Tri ((X × P3) ⊕ Option A₀)) :
    mapTri φ t = (t.1, φ (comp t P3.fst), φ (comp t P3.mid), φ (comp t P3.lst)) := rfl

lemma mrComp_eval {A QT : Type} [Fintype X] (T : SST A (Option A₀) QT X) (w : List A) :
    (mrComp T).eval w = mapReverse A₀ (T.eval w) := by
  refine SST.eval_of_sim (T := T) (T' := mrComp T) (p := mapReverse A₀)
    (fun c c' => c'.1.1 = c.1 ∧ ∀ x,
      mapTri (SST.subst c'.2) (symSingle c'.1.2 (Sum.inl x)) = semTri (c.2 x))
    ⟨rfl, fun x => by rw [mapTri_subst_single]; rfl⟩ ?_ ?_ w
  · rintro ⟨qT, η⟩ ⟨⟨qT', hs⟩, η'⟩ a ⟨hq, hinv⟩
    cases hq
    refine ⟨rfl, fun x => ?_⟩
    have key := mapTri_symTri (η := η) (η' := η') hinv ((T.step qT a).2 x)
    rw [mapTri_eq_comp] at key
    rw [mapTri_subst_single]
    exact key
  · rintro ⟨qT, η⟩ ⟨⟨qT', hs⟩, η'⟩ ⟨hq, hinv⟩
    cases hq
    have h := mapTri_symTri (η := η) (η' := η') hinv (T.final qT)
    show SST.subst η' (out [Sum.inr none] (symTri hs (T.final qT)))
      = mapReverse A₀ (SST.subst η (T.final qT))
    rw [show SST.subst η' (out [Sum.inr none] (symTri hs (T.final qT)))
        = out [none] (mapTri (SST.subst η') (symTri hs (T.final qT))) from
      mapTri_out (subst_append_hom η') rfl _, h, out_semTri]

end MapRevSST

/-- **Post-composition with map reverse.**  If `f` is computed by an sst, then so
is `map reverse ∘ f`. -/
theorem isSST_comp_mapReverse {A A₀ : Type} {f : List A → List (Option A₀)} (hf : IsSST f) :
    IsSST (fun w => mapReverse A₀ (f w)) := by
  obtain ⟨QT, X, hQT, hX, T, rfl⟩ := hf
  haveI := hQT
  exact ⟨QT × (X → Bool), X × MapRevSST.P3, inferInstance, inferInstance,
    MapRevSST.mrComp T, funext fun w => MapRevSST.mrComp_eval T w⟩

end Lax916827Proofs.Transducers
