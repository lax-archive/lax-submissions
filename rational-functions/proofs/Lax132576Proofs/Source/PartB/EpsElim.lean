/-
Elimination of ε-transitions (Lemma `lemma:eliminate-epsilon-transitions`).

Let `M` be an nfa with output in the atomic normal form of
`RequestProject/PartB/Atomize.lean`.  The automaton with extended transitions that
computes the same relation without ε-transitions has the states of `M`, a fresh
initial state `ι` and a fresh final state `φ`, and the transitions

* `ι --ε/L--> φ`, where `L` is the set of outputs of `M` on the empty input;
* `ι --a/L--> q`, where `L` is the set of outputs of the runs of `M` from an
  initial state to `q` that read exactly the letter `a`;
* `q --a/L--> q'`, where `L` is the set of outputs of the runs of `M` from `q`
  to `q'` that read exactly the letter `a`.

Each of these languages is regular by `outputs_isRegular`.  Only productive
states are used, which is what makes the languages finite when every input has
finitely many outputs.
-/
import Lax132576Proofs.Source.PartB.OutLang
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace EpsElim

variable {A B Q : Type} (M : NFAO A B Q)

/-- The states of the automaton with extended transitions: the states of `M`,
a fresh initial state (`Sum.inr false`) and a fresh final state
(`Sum.inr true`). -/
abbrev St (Q : Type) : Type := Q ⊕ Bool

/-- The fresh initial state. -/
def iota (Q : Type) : St Q := Sum.inr false

/-- The fresh final state. -/
def phi (Q : Type) : St Q := Sum.inr true

/-- The transitions of the automaton with extended transitions. -/
def edelta : Set (St Q × List A × Language B × St Q) :=
  {z | z = (iota Q, [], OutLang.outputs M M.init M.final [], phi Q)} ∪
  {z | ∃ (a : A) (q' : Q), Productive M q' ∧
      z = (iota Q, [a], OutLang.outputs M M.init {q'} [a], Sum.inl q')} ∪
  {z | ∃ (a : A) (q q' : Q), Productive M q ∧ Productive M q' ∧
      z = (Sum.inl q, [a], OutLang.outputs M {q} {q'} [a], Sum.inl q')}

lemma edelta_finite [Finite A] [Finite Q] : (edelta M).Finite := by
  refine Set.Finite.union (Set.Finite.union (Set.finite_singleton _) ?_) ?_
  · refine Set.Finite.subset (Set.finite_range
      (fun p : A × Q => (iota Q, [p.1], OutLang.outputs M M.init {p.2} [p.1], Sum.inl p.2))) ?_
    rintro z ⟨a, q', -, rfl⟩
    exact ⟨(a, q'), rfl⟩
  · refine Set.Finite.subset (Set.finite_range
      (fun p : A × Q × Q =>
        (Sum.inl p.2.1, [p.1], OutLang.outputs M {p.2.1} {p.2.2} [p.1], Sum.inl p.2.2))) ?_
    rintro z ⟨a, q, q', -, -, rfl⟩
    exact ⟨(a, q, q'), rfl⟩

/-- The automaton with extended transitions. -/
def eAut [Finite A] [Finite Q] : LabAut A (Language B) (St Q) where
  init := {iota Q}
  final := {s | ∃ p ∈ M.final, s = Sum.inl p} ∪ {phi Q}
  δ := edelta M
  δ_finite := edelta_finite M

/-! ### The transitions, by their source -/

lemma edelta_src_iota {u : List A} {L : Language B} {s : St Q}
    (h : (iota Q, u, L, s) ∈ edelta M) :
    (u = [] ∧ L = OutLang.outputs M M.init M.final [] ∧ s = phi Q) ∨
      (∃ (a : A) (q' : Q), Productive M q' ∧ u = [a] ∧
        L = OutLang.outputs M M.init {q'} [a] ∧ s = Sum.inl q') := by
  rcases h with (h | ⟨a, q', hprod, h⟩) | ⟨a, q, q', hq, hq', h⟩ <;>
    simp only [Set.mem_setOf_eq, Prod.mk.injEq, iota, phi] at h
  · exact Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · exact Or.inr ⟨a, q', hprod, h.2.1, h.2.2.1, h.2.2.2⟩
  · exact absurd h.1 (by simp)

lemma edelta_src_inl {q : Q} {u : List A} {L : Language B} {s : St Q}
    (h : (Sum.inl q, u, L, s) ∈ edelta M) :
    ∃ (a : A) (q' : Q), Productive M q ∧ Productive M q' ∧ u = [a] ∧
      L = OutLang.outputs M {q} {q'} [a] ∧ s = Sum.inl q' := by
  rcases h with (h | ⟨a, q', hprod, h⟩) | ⟨a, q₀, q', hq, hq', h⟩ <;>
    simp only [Set.mem_setOf_eq, Prod.mk.injEq, iota, phi, Sum.inl.injEq] at h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · obtain ⟨rfl, hu, hL, hs⟩ := h
    exact ⟨a, q', hq, hq', hu, hL, hs⟩

lemma edelta_src_phi {u : List A} {L : Language B} {s : St Q}
    (h : (phi Q, u, L, s) ∈ edelta M) : False := by
  rcases h with (h | ⟨a, q', hprod, h⟩) | ⟨a, q, q', hq, hq', h⟩ <;>
    simp only [Set.mem_setOf_eq, Prod.mk.injEq, iota, phi] at h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)

/-! ### The shape of the runs -/

variable [Finite A] [Finite Q]

lemma path_from_phi {ts : List (St Q × List A × Language B × St Q)} {s : St Q}
    (h : (eAut M).Path (phi Q) ts s) : ts = [] ∧ s = phi Q := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons ht _ => exact absurd ht (fun h' => edelta_src_phi M h')

lemma path_letters {s s' : St Q} {ts : List (St Q × List A × Language B × St Q)}
    (h : (eAut M).Path s ts s') (hs : s ≠ iota Q) : ∀ t ∈ ts, t.2.1.length = 1 := by
  induction h with
  | nil => simp
  | @cons s u L s₁ ts s' ht hrest ih =>
      intro t htmem
      match s, hs with
      | Sum.inl q, _ =>
          obtain ⟨a, q', hq, hq', rfl, hL, rfl⟩ := edelta_src_inl M ht
          rcases List.mem_cons.1 htmem with rfl | hmem
          · simp
          · exact ih (by simp [iota]) t hmem
      | Sum.inr true, _ => exact absurd ht (fun h' => edelta_src_phi M h')
      | Sum.inr false, hs => exact absurd rfl hs

/-- A run that starts in a state of `M` ends in a state of `M`. -/
lemma path_target_inl {q : Q} {s : St Q} {ts : List (St Q × List A × Language B × St Q)}
    (h : (eAut M).Path (Sum.inl q) ts s) : ∃ p : Q, s = Sum.inl p := by
  generalize hs₀ : (Sum.inl q : St Q) = s₀ at h
  induction h generalizing q with
  | nil => exact ⟨q, hs₀.symm⟩
  | @cons s u L s₁ ts s' ht hrest ih =>
      subst hs₀
      obtain ⟨a, q', hq, hq', hu, hL, hs⟩ := edelta_src_inl M ht
      exact ih hs.symm

/-- The runs of the automaton with extended transitions are ε-free. -/
lemma eAut_epsilonFree :
    ∀ ts, (eAut M).Accepting ts →
      (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
        (LabAut.inputOf ts = [] → ts.length = 1) := by
  rintro ts ⟨s, hs, s', hs', hpath⟩
  have hs₀ : s = iota Q := hs
  subst hs₀
  cases hpath with
  | nil =>
      exfalso
      rcases hs' with ⟨p, -, hp⟩ | hp
      · exact absurd hp (by simp [iota])
      · exact absurd hp (by simp [iota, phi])
  | @cons _ u L s₁ ts₁ _ ht hrest =>
      rcases edelta_src_iota M ht with ⟨rfl, -, rfl⟩ | ⟨a, q', -, rfl, -, rfl⟩
      · obtain ⟨rfl, -⟩ := path_from_phi M hrest
        exact ⟨by simp, fun _ => rfl⟩
      · refine ⟨fun _ t htmem => ?_, fun hnil => absurd hnil (by simp)⟩
        rcases List.mem_cons.1 htmem with rfl | hmem
        · simp
        · exact path_letters M hrest (by simp [iota]) t hmem

/-! ### Soundness -/

lemma path_sound {s s' : St Q} {ts : List (St Q × List A × Language B × St Q)}
    (h : (eAut M).Path s ts s') :
    ∀ (q p : Q), s = Sum.inl q → s' = Sum.inl p →
      ∀ v ∈ (LabAut.labelsOf ts).prod, M.relFrom q (LabAut.inputOf ts) v p := by
  induction h with
  | nil s =>
      rintro q p rfl hp v hv
      have hqp : q = p := by simpa using hp
      subst hqp
      simp only [LabAut.labelsOf_nil, List.prod_nil, Language.mem_one] at hv
      subst hv
      simpa using M.relFrom_nil q
  | @cons s u L s₁ ts s' ht hrest ih =>
      rintro q p rfl hp v hv
      obtain ⟨a, q', hq, hq', hu, hL, hs⟩ := edelta_src_inl M ht
      subst hu
      subst hL
      simp only [LabAut.labelsOf_cons, List.prod_cons, Language.mem_mul] at hv
      obtain ⟨x, hx, v', hv', rfl⟩ := hv
      obtain ⟨q₁, hq₁, q₂, hq₂, hrel⟩ := hx
      have hq₁' : q₁ = q := hq₁
      have hq₂' : q₂ = q' := hq₂
      subst hq₁'; subst hq₂'
      have hrest' := ih q₂ p hs hp v' hv'
      simpa using M.relFrom_trans hrel hrest'

/-! ### Completeness -/

omit [Finite A] [Finite Q] in
lemma split_first_letter (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    {q p : Q} {w : List A} {v : List B} (h : M.relFrom q w v p) :
    ∀ (a : A) (w' : List A), w = a :: w' →
      ∃ (q₁ : Q) (x₁ v₁ : List B), M.relFrom q [a] x₁ q₁ ∧ M.relFrom q₁ w' v₁ p ∧
        v = x₁ ++ v₁ := by
  refine NFAO.relFrom_induction (M := M)
    (motive := fun q w v => ∀ (a : A) (w' : List A), w = a :: w' →
      ∃ (q₁ : Q) (x₁ v₁ : List B), M.relFrom q [a] x₁ q₁ ∧ M.relFrom q₁ w' v₁ p ∧
        v = x₁ ++ v₁) ?_ ?_ h
  · intro a w' hcontra
    exact absurd hcontra (by simp)
  · intro q₀ q₁ u x w₂ v₂ ht _ ih a w' heq
    have hu : u.length ≤ 1 := (hatom _ ht).1
    match u, hu with
    | [], _ =>
        simp only [List.nil_append] at heq
        obtain ⟨q₂, x₁, v₁, h1, h2, h3⟩ := ih a w' heq
        exact ⟨q₂, x ++ x₁, v₁, by simpa using M.relFrom_step ht h1, h2, by simp [h3]⟩
    | [b], _ =>
        simp only [List.cons_append, List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨q₁, x, v₂, NFAO.relFrom_single ht, ‹M.relFrom q₁ w₂ v₂ p›, rfl⟩

omit [Finite A] [Finite Q] in
lemma reach_of_relFrom {q q' : Q} {w : List A} {v : List B} (hq : LenNF.Reach M q)
    (h : M.relFrom q w v q') : LenNF.Reach M q' := by
  obtain ⟨q₀, h₀, ts₀, hp₀⟩ := hq
  obtain ⟨ts, hts, -, -⟩ := h
  exact ⟨q₀, h₀, ts₀ ++ ts, hp₀.append hts⟩

omit [Finite A] [Finite Q] in
lemma coReach_of_relFrom {q q' : Q} {w : List A} {v : List B} (hq' : LenNF.CoReach M q')
    (h : M.relFrom q w v q') : LenNF.CoReach M q := by
  obtain ⟨p, hp, ts₁, hp₁⟩ := hq'
  obtain ⟨ts, hts, -, -⟩ := h
  exact ⟨p, hp, ts ++ ts₁, hts.append hp₁⟩

/-- Every run of `M` on a nonempty input is matched by a run of the automaton
with extended transitions. -/
lemma path_complete (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    {p : Q} (hpp : Productive M p) :
    ∀ (w : List A) (q : Q) (v : List B), Productive M q → w ≠ [] → M.relFrom q w v p →
      ∃ ts, (eAut M).Path (Sum.inl q) ts (Sum.inl p) ∧ LabAut.inputOf ts = w ∧
        v ∈ (LabAut.labelsOf ts).prod := by
  intro w
  induction w with
  | nil => intro q v _ hne; exact absurd rfl hne
  | cons a w' ih =>
      intro q v hq _ hrel
      by_cases hw' : w' = []
      · subst hw'
        refine ⟨[(Sum.inl q, [a], OutLang.outputs M {q} {p} [a], Sum.inl p)], ?_, rfl, ?_⟩
        · exact LabAut.Path.cons (Or.inr ⟨a, q, p, hq, hpp, rfl⟩) (LabAut.Path.nil _)
        · simp only [LabAut.labelsOf_cons, LabAut.labelsOf_nil, List.prod_cons, List.prod_nil,
            mul_one]
          exact ⟨q, rfl, p, rfl, hrel⟩
      · obtain ⟨q₁, x₁, v₁, h1, h2, rfl⟩ := split_first_letter M hatom hrel a w' rfl
        have hq₁ : Productive M q₁ := by
          rw [LenNF.productive_iff]
          exact ⟨reach_of_relFrom M ((LenNF.productive_iff M q).1 hq).1 h1,
            coReach_of_relFrom M ((LenNF.productive_iff M p).1 hpp).2 h2⟩
        obtain ⟨ts, hpath, hin, hout⟩ := ih q₁ v₁ hq₁ hw' h2
        refine ⟨(Sum.inl q, [a], OutLang.outputs M {q} {q₁} [a], Sum.inl q₁) :: ts, ?_, ?_, ?_⟩
        · exact LabAut.Path.cons (Or.inr ⟨a, q, q₁, hq, hq₁, rfl⟩) hpath
        · simp [hin]
        · simp only [LabAut.labelsOf_cons, List.prod_cons, Language.mem_mul]
          exact ⟨x₁, ⟨q, rfl, q₁, rfl, h1⟩, v₁, hout, rfl⟩

/-! ### The automaton with extended transitions computes the same relation -/

lemma eAut_rel (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) (w : List A)
    (v : List B) :
    M.rel w v ↔ ∃ ts, (eAut M).Accepting ts ∧ LabAut.inputOf ts = w ∧
      v ∈ (LabAut.labelsOf ts).prod := by
  constructor
  · rw [NFAO.rel_iff_relFrom]
    rintro ⟨q₀, h₀, p, hp, hrel⟩
    have hreach₀ : LenNF.Reach M q₀ := ⟨q₀, h₀, [], LabAut.Path.nil q₀⟩
    have hcop : LenNF.CoReach M p := ⟨p, hp, [], LabAut.Path.nil p⟩
    have hprodp : Productive M p := (LenNF.productive_iff M p).2
      ⟨reach_of_relFrom M hreach₀ hrel, hcop⟩
    match w with
    | [] =>
        refine ⟨[(iota Q, [], OutLang.outputs M M.init M.final [], phi Q)],
          ⟨iota Q, rfl, phi Q, Or.inr rfl, LabAut.Path.cons (Or.inl (Or.inl rfl))
            (LabAut.Path.nil _)⟩, rfl, ?_⟩
        simp only [LabAut.labelsOf_cons, LabAut.labelsOf_nil, List.prod_cons, List.prod_nil,
          mul_one]
        exact ⟨q₀, h₀, p, hp, hrel⟩
    | a :: w' =>
        by_cases hw' : w' = []
        · subst hw'
          refine ⟨[(iota Q, [a], OutLang.outputs M M.init {p} [a], Sum.inl p)],
            ⟨iota Q, rfl, Sum.inl p, Or.inl ⟨p, hp, rfl⟩,
              LabAut.Path.cons (Or.inl (Or.inr ⟨a, p, hprodp, rfl⟩)) (LabAut.Path.nil _)⟩,
            rfl, ?_⟩
          simp only [LabAut.labelsOf_cons, LabAut.labelsOf_nil, List.prod_cons, List.prod_nil,
            mul_one]
          exact ⟨q₀, h₀, p, rfl, hrel⟩
        · obtain ⟨q₁, x₁, v₁, h1, h2, rfl⟩ := split_first_letter M hatom hrel a w' rfl
          have hprod₁ : Productive M q₁ := (LenNF.productive_iff M q₁).2
            ⟨reach_of_relFrom M hreach₀ h1, coReach_of_relFrom M hcop h2⟩
          obtain ⟨ts, hpath, hin, hout⟩ := path_complete M hatom hprodp w' q₁ v₁ hprod₁ hw' h2
          refine ⟨(iota Q, [a], OutLang.outputs M M.init {q₁} [a], Sum.inl q₁) :: ts,
            ⟨iota Q, rfl, Sum.inl p, Or.inl ⟨p, hp, rfl⟩,
              LabAut.Path.cons (Or.inl (Or.inr ⟨a, q₁, hprod₁, rfl⟩)) hpath⟩, by simp [hin], ?_⟩
          simp only [LabAut.labelsOf_cons, List.prod_cons, Language.mem_mul]
          exact ⟨x₁, ⟨q₀, h₀, q₁, rfl, h1⟩, v₁, hout, rfl⟩
  · rintro ⟨ts, ⟨s, hs, s', hs', hpath⟩, rfl, hv⟩
    have hs₀ : s = iota Q := hs
    subst hs₀
    cases hpath with
    | nil =>
        exfalso
        rcases hs' with ⟨p, -, hp⟩ | hp
        · exact absurd hp (by simp [iota])
        · exact absurd hp (by simp [iota, phi])
    | @cons _ u L s₁ ts₁ _ ht hrest =>
        rcases edelta_src_iota M ht with ⟨rfl, rfl, rfl⟩ | ⟨a, q', hprod', rfl, rfl, rfl⟩
        · obtain ⟨rfl, -⟩ := path_from_phi M hrest
          simp only [LabAut.labelsOf_cons, LabAut.labelsOf_nil, List.prod_cons, List.prod_nil,
            mul_one] at hv
          obtain ⟨q₀, h₀, p, hp, hrel⟩ := hv
          rw [NFAO.rel_iff_relFrom]
          exact ⟨q₀, h₀, p, hp, by simpa using hrel⟩
        · obtain ⟨p, rfl⟩ := path_target_inl M hrest
          have hpfin : p ∈ M.final := by
            rcases hs' with ⟨p₀, hp₀, hp₀'⟩ | hp₀
            · have : p = p₀ := by simpa using hp₀'
              subst this
              exact hp₀
            · exact absurd hp₀ (by simp [phi])
          simp only [LabAut.labelsOf_cons, List.prod_cons, Language.mem_mul] at hv
          obtain ⟨x, hx, v', hv', rfl⟩ := hv
          obtain ⟨q₀, h₀, q₁, hq₁, hrel⟩ := hx
          have hq₁' : q₁ = q' := hq₁
          subst hq₁'
          have hrest' := path_sound M hrest q₁ p rfl rfl v' hv'
          rw [NFAO.rel_iff_relFrom]
          exact ⟨q₀, h₀, p, hpfin, by simpa using M.relFrom_trans hrel hrest'⟩

/-! ### The case of finitely many outputs -/

omit [Finite A] [Finite Q] in
lemma outputs_finite_aux (hfin : ∀ w, {v | M.rel w v}.Finite)
    {S T : Set Q} {y₁ y₂ : List B} {w₁ w₂ : List A}
    (hpre : ∀ q ∈ S, ∃ q₀ ∈ M.init, M.relFrom q₀ w₁ y₁ q)
    (hpost : ∀ q ∈ T, ∃ p ∈ M.final, M.relFrom q w₂ y₂ p) (w : List A) :
    (OutLang.outputs M S T w).Finite := by
  refine Set.Finite.of_finite_image (f := fun x => y₁ ++ x ++ y₂) ?_ ?_
  · refine Set.Finite.subset (hfin (w₁ ++ w ++ w₂)) ?_
    rintro _ ⟨x, ⟨q, hq, q', hq', hrel⟩, rfl⟩
    obtain ⟨q₀, h₀, hpre'⟩ := hpre q hq
    obtain ⟨p, hp, hpost'⟩ := hpost q' hq'
    rw [Set.mem_setOf_eq, NFAO.rel_iff_relFrom]
    exact ⟨q₀, h₀, p, hp, M.relFrom_trans (M.relFrom_trans hpre' hrel) hpost'⟩
  · intro x _ x' _ h
    simpa using h

omit [Finite A] [Finite Q] in
/-- If every input has finitely many outputs, then the labels of the
transitions are finite languages. -/
lemma edelta_labels_finite (hfin : ∀ w, {v | M.rel w v}.Finite) :
    ∀ t ∈ edelta M, t.2.2.1.Finite := by
  rintro t ((ht | ⟨a, q', hprod', ht⟩) | ⟨a, q, q', hprod, hprod', ht⟩)
  · have ht' : t = (iota Q, [], OutLang.outputs M M.init M.final [], phi Q) := ht
    rw [ht']
    exact outputs_finite_aux M hfin (y₁ := []) (y₂ := []) (w₁ := []) (w₂ := [])
      (fun q hq => ⟨q, hq, M.relFrom_nil q⟩) (fun q hq => ⟨q, hq, M.relFrom_nil q⟩) []
  · obtain ⟨p, hp, ts₂, hpath₂⟩ := ((LenNF.productive_iff M q').1 hprod').2
    rw [ht]
    exact outputs_finite_aux M hfin (y₁ := []) (w₁ := [])
      (y₂ := NFAO.outputOf ts₂) (w₂ := LabAut.inputOf ts₂)
      (fun q hq => ⟨q, hq, M.relFrom_nil q⟩)
      (fun q hq => ⟨p, hp, by rw [show q = q' from hq]; exact ⟨ts₂, hpath₂, rfl, rfl⟩⟩) [a]
  · obtain ⟨q₀, h₀, ts₁, hpath₁⟩ := ((LenNF.productive_iff M q).1 hprod).1
    obtain ⟨p, hp, ts₂, hpath₂⟩ := ((LenNF.productive_iff M q').1 hprod').2
    rw [ht]
    exact outputs_finite_aux M hfin
      (y₁ := NFAO.outputOf ts₁) (w₁ := LabAut.inputOf ts₁)
      (y₂ := NFAO.outputOf ts₂) (w₂ := LabAut.inputOf ts₂)
      (fun r hr => ⟨q₀, h₀, by rw [show r = q from hr]; exact ⟨ts₁, hpath₁, rfl, rfl⟩⟩)
      (fun r hr => ⟨p, hp, by rw [show r = q' from hr]; exact ⟨ts₂, hpath₂, rfl, rfl⟩⟩) [a]

/-- The transitions of the ordinary automaton: a transition of the automaton
with extended transitions together with a string in its label. -/
def ndelta : Set (St Q × List A × List B × St Q) :=
  {z | ∃ L : Language B, (z.1, z.2.1, L, z.2.2.2) ∈ edelta M ∧ z.2.2.1 ∈ L}

lemma ndelta_finite (hfin : ∀ w, {v | M.rel w v}.Finite) : (ndelta M).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion (edelta_finite M)
    (fun t ht => Set.Finite.image (fun x => (t.1, t.2.1, x, t.2.2.2))
      (edelta_labels_finite M hfin t ht))) ?_
  rintro ⟨s, u, x, s'⟩ ⟨L, hL, hx⟩
  exact Set.mem_biUnion hL ⟨x, hx, rfl⟩

/-- The ordinary nfa with output, used when every input has finitely many
outputs. -/
def nAut (hfin : ∀ w, {v | M.rel w v}.Finite) : NFAO A B (St Q) where
  init := {iota Q}
  final := {s | ∃ p ∈ M.final, s = Sum.inl p} ∪ {phi Q}
  δ := ndelta M
  δ_finite := ndelta_finite M hfin

omit [Finite A] [Finite Q] in
lemma ndelta_src_iota {u : List A} {x : List B} {s : St Q}
    (h : (iota Q, u, x, s) ∈ ndelta M) :
    (u = [] ∧ s = phi Q) ∨ (∃ (a : A) (q' : Q), u = [a] ∧ s = Sum.inl q') := by
  obtain ⟨L, hL, -⟩ := h
  rcases edelta_src_iota M hL with ⟨hu, -, hs⟩ | ⟨a, q', -, hu, -, hs⟩
  · exact Or.inl ⟨hu, hs⟩
  · exact Or.inr ⟨a, q', hu, hs⟩

omit [Finite A] [Finite Q] in
lemma ndelta_src_inl {q : Q} {u : List A} {x : List B} {s : St Q}
    (h : (Sum.inl q, u, x, s) ∈ ndelta M) :
    ∃ (a : A) (q' : Q), u = [a] ∧ s = Sum.inl q' := by
  obtain ⟨L, hL, -⟩ := h
  obtain ⟨a, q', -, -, hu, -, hs⟩ := edelta_src_inl M hL
  exact ⟨a, q', hu, hs⟩

omit [Finite A] [Finite Q] in
lemma ndelta_src_phi {u : List A} {x : List B} {s : St Q}
    (h : (phi Q, u, x, s) ∈ ndelta M) : False := by
  obtain ⟨L, hL, -⟩ := h
  exact edelta_src_phi M hL

lemma nPath_from_phi (hfin : ∀ w, {v | M.rel w v}.Finite)
    {ts : List (St Q × List A × List B × St Q)} {s : St Q}
    (h : (nAut M hfin).Path (phi Q) ts s) : ts = [] ∧ s = phi Q := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons ht _ => exact absurd ht (fun h' => ndelta_src_phi M h')

lemma nPath_letters (hfin : ∀ w, {v | M.rel w v}.Finite) {s s' : St Q}
    {ts : List (St Q × List A × List B × St Q)}
    (h : (nAut M hfin).Path s ts s') (hs : s ≠ iota Q) : ∀ t ∈ ts, t.2.1.length = 1 := by
  induction h with
  | nil => simp
  | @cons s u x s₁ ts s' ht hrest ih =>
      intro t htmem
      match s, hs with
      | Sum.inl q, _ =>
          obtain ⟨a, q', rfl, rfl⟩ := ndelta_src_inl M ht
          rcases List.mem_cons.1 htmem with rfl | hmem
          · simp
          · exact ih (by simp [iota]) t hmem
      | Sum.inr true, _ => exact absurd ht (fun h' => ndelta_src_phi M h')
      | Sum.inr false, hs => exact absurd rfl hs

/-- The runs of the ordinary automaton are ε-free as well. -/
lemma nAut_epsilonFree (hfin : ∀ w, {v | M.rel w v}.Finite) :
    ∀ ts, (nAut M hfin).Accepting ts →
      (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
        (LabAut.inputOf ts = [] → ts.length = 1) := by
  rintro ts ⟨s, hs, s', hs', hpath⟩
  have hs₀ : s = iota Q := hs
  subst hs₀
  cases hpath with
  | nil =>
      exfalso
      rcases hs' with ⟨p, -, hp⟩ | hp
      · exact absurd hp (by simp [iota])
      · exact absurd hp (by simp [iota, phi])
  | @cons _ u x s₁ ts₁ _ ht hrest =>
      rcases ndelta_src_iota M ht with ⟨rfl, rfl⟩ | ⟨a, q', rfl, rfl⟩
      · obtain ⟨rfl, -⟩ := nPath_from_phi M hfin hrest
        exact ⟨by simp, fun _ => rfl⟩
      · refine ⟨fun _ t htmem => ?_, fun hnil => absurd hnil (by simp)⟩
        rcases List.mem_cons.1 htmem with rfl | hmem
        · simp
        · exact nPath_letters M hfin hrest (by simp [iota]) t hmem

/-! ### The two automata compute the same relation -/

lemma epath_of_npath (hfin : ∀ w, {v | M.rel w v}.Finite) {s s' : St Q}
    {ts : List (St Q × List A × List B × St Q)} (h : (nAut M hfin).Path s ts s') :
    ∃ ts', (eAut M).Path s ts' s' ∧ LabAut.inputOf ts' = LabAut.inputOf ts ∧
      NFAO.outputOf ts ∈ (LabAut.labelsOf ts').prod := by
  induction h with
  | nil s => exact ⟨[], LabAut.Path.nil s, rfl, by simp [Language.mem_one]⟩
  | @cons s u x s₁ ts s' ht hrest ih =>
      obtain ⟨L, hL, hx⟩ := ht
      obtain ⟨ts', hpath', hin', hout'⟩ := ih
      refine ⟨(s, u, L, s₁) :: ts', LabAut.Path.cons hL hpath', by simp [hin'], ?_⟩
      simp only [LabAut.labelsOf_cons, List.prod_cons, Language.mem_mul, NFAO.outputOf_cons]
      exact ⟨x, hx, NFAO.outputOf ts, hout', rfl⟩

lemma npath_of_epath (hfin : ∀ w, {v | M.rel w v}.Finite) {s s' : St Q}
    {ts : List (St Q × List A × Language B × St Q)} (h : (eAut M).Path s ts s') :
    ∀ v ∈ (LabAut.labelsOf ts).prod, ∃ ts', (nAut M hfin).Path s ts' s' ∧
      LabAut.inputOf ts' = LabAut.inputOf ts ∧ NFAO.outputOf ts' = v := by
  induction h with
  | nil s =>
      intro v hv
      simp only [LabAut.labelsOf_nil, List.prod_nil, Language.mem_one] at hv
      exact ⟨[], LabAut.Path.nil s, rfl, hv.symm⟩
  | @cons s u L s₁ ts s' ht hrest ih =>
      intro v hv
      simp only [LabAut.labelsOf_cons, List.prod_cons, Language.mem_mul] at hv
      obtain ⟨x, hx, v', hv', rfl⟩ := hv
      obtain ⟨ts', hpath', hin', hout'⟩ := ih v' hv'
      exact ⟨(s, u, x, s₁) :: ts', LabAut.Path.cons ⟨L, ht, hx⟩ hpath', by simp [hin'],
        by simp [hout']⟩

lemma nAut_rel (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    (hfin : ∀ w, {v | M.rel w v}.Finite) (w : List A) (v : List B) :
    (nAut M hfin).rel w v ↔ M.rel w v := by
  rw [eAut_rel M hatom w v]
  constructor
  · rintro ⟨ts, ⟨s, hs, s', hs', hpath⟩, hin, hout⟩
    obtain ⟨ts', hpath', hin', hmem⟩ := epath_of_npath M hfin hpath
    exact ⟨ts', ⟨s, hs, s', hs', hpath'⟩, by rw [hin', hin], hout ▸ hmem⟩
  · rintro ⟨ts, ⟨s, hs, s', hs', hpath⟩, hin, hv⟩
    obtain ⟨ts', hpath', hin', hout'⟩ := npath_of_epath M hfin hpath v hv
    exact ⟨ts', ⟨s, hs, s', hs', hpath'⟩, by rw [hin', hin], hout'⟩

end EpsElim

/-- **Lemma `lemma:eliminate-epsilon-transitions` (Elimination of ε-transitions).**  Every rational
relation is computed by an nfa with output and extended transitions in which every accepting run
reads exactly one letter per transition (or consists of a single transition, if the input is empty).
If moreover every input string has finitely many outputs, then extended transitions are not needed.
-/
theorem epsilon_elimination_aux {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    (∃ (Q : Type) (_ : Finite Q) (N : LabAut A (Language B) Q),
        (∀ t ∈ N.δ, Language.IsRegular t.2.2.1) ∧
        (∀ ts, N.Accepting ts →
          (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
            (LabAut.inputOf ts = [] → ts.length = 1)) ∧
        ∀ w v, R w v ↔ ∃ ts, N.Accepting ts ∧ LabAut.inputOf ts = w ∧
          v ∈ (LabAut.labelsOf ts).prod) ∧
      ((∀ w, {v | R w v}.Finite) →
        ∃ (Q : Type) (_ : Finite Q) (N : NFAO A B Q),
          (∀ ts, N.Accepting ts →
            (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
              (LabAut.inputOf ts = [] → ts.length = 1)) ∧
          ∀ w v, R w v ↔ N.rel w v) := by
  obtain ⟨Q, hQ, M, hatom, hrel⟩ := exists_atomic_nfao hR
  have hregular : ∀ t ∈ EpsElim.edelta M, Language.IsRegular t.2.2.1 := by
    rintro t ((ht | ⟨a, q', -, ht⟩) | ⟨a, q, q', -, -, ht⟩)
    · have ht' : t = (EpsElim.iota Q, [], OutLang.outputs M M.init M.final [],
        EpsElim.phi Q) := ht
      rw [ht']
      exact outputs_isRegular M M.init M.final [] hatom
    · rw [ht]
      exact outputs_isRegular M M.init {q'} [a] hatom
    · rw [ht]
      exact outputs_isRegular M {q} {q'} [a] hatom
  refine ⟨⟨EpsElim.St Q, inferInstance, EpsElim.eAut M, hregular, EpsElim.eAut_epsilonFree M,
    fun w v => ((hrel w v).trans (EpsElim.eAut_rel M hatom w v))⟩, ?_⟩
  intro hfinR
  have hfin : ∀ w, {v | M.rel w v}.Finite := by
    intro w
    have : {v | M.rel w v} = {v | R w v} := by
      ext v; exact (hrel w v).symm
    rw [this]
    exact hfinR w
  exact ⟨EpsElim.St Q, inferInstance, EpsElim.nAut M hfin, EpsElim.nAut_epsilonFree M hfin,
    fun w v => (hrel w v).trans (EpsElim.nAut_rel M hatom hfin w v).symm⟩

end Lax132576Proofs.Transducers
