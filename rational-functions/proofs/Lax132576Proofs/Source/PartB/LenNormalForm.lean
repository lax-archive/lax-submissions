/- The normal form of length preserving rational functions (Lemma
`lem:characterisation-length-preserving`).

Let `f` be a length preserving rational function and let `M` be an nfa with
output computing it in which every transition reads at most one letter and
writes at most one letter (the atomic normal form of
`RequestProject/PartB/Atomize.lean`).

Every state `q` of `M` that appears in an accepting run has a *type* `τ q`: the
difference between the length of the output and the length of the input of any
run from an initial state to `q`; it is well defined because `f` is length
preserving.  The states of the new automaton are pairs `(q, s)` where `s` is a
string of length `|τ q|`, which is

* the output produced by `M` but not yet emitted, when `τ q ≥ 0`, and
* the output already emitted but not yet produced by `M` (a guess, verified
  later), when `τ q ≤ 0`.

Every transition of the new automaton emits exactly as many letters as it reads.
-/
import Lax132576Proofs.Source.PartB.Atomize
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## Segments of a string -/

/-- The segment of `X` strictly between the positions `a` and `b`. -/
def seg {B : Type} (X : List B) (a b : ℕ) : List B := (X.take b).drop a

lemma seg_eq {B : Type} (X : List B) (a b : ℕ) : seg X a b = (X.drop a).take (b - a) := by
  simp [seg, List.drop_take]

lemma seg_length {B : Type} (X : List B) (a b : ℕ) (hb : b ≤ X.length) :
    (seg X a b).length = b - a := by
  simp [seg, hb]

lemma seg_concat {B : Type} (X : List B) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    seg X a b ++ seg X b c = seg X a c := by
  rw [seg_eq, seg_eq, seg_eq]
  have hd : X.drop b = (X.drop a).drop (b - a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [hd, ← List.take_add]
  congr 1
  omega

@[simp] lemma seg_self {B : Type} (X : List B) (a : ℕ) : seg X a a = [] := by
  simp [seg_eq]

@[simp] lemma seg_zero {B : Type} (X : List B) (b : ℕ) : seg X 0 b = X.take b := by
  simp [seg]

/-! ## Paths: input and output of a concatenation -/

namespace LabAut

lemma inputOf_append {A L Q : Type} (ts ts' : List (Q × List A × L × Q)) :
    inputOf (ts ++ ts') = inputOf ts ++ inputOf ts' := by
  simp [inputOf]

end LabAut

namespace NFAO

lemma outputOf_append {A B Q : Type} (ts ts' : List (Q × List A × List B × Q)) :
    outputOf (ts ++ ts') = outputOf ts ++ outputOf ts' := by
  simp [outputOf, LabAut.labelsOf]

end NFAO

namespace LenNF

variable {A B Q : Type} (M : NFAO A B Q) (f : List A → List B)

/-- A state is reachable if some path from an initial state ends in it. -/
def Reach (q : Q) : Prop := ∃ q₀ ∈ M.init, ∃ ts, M.Path q₀ ts q

/-- A state is co-reachable if some path from it ends in a final state. -/
def CoReach (q : Q) : Prop := ∃ p ∈ M.final, ∃ ts, M.Path q ts p

lemma productive_iff (q : Q) : Productive M q ↔ Reach M q ∧ CoReach M q := by
  constructor
  · rintro ⟨q₀, h₀, p, hp, ts₁, ts₂, hp₁, hp₂⟩
    exact ⟨⟨q₀, h₀, ts₁, hp₁⟩, ⟨p, hp, ts₂, hp₂⟩⟩
  · rintro ⟨⟨q₀, h₀, ts₁, hp₁⟩, ⟨p, hp, ts₂, hp₂⟩⟩
    exact ⟨q₀, h₀, p, hp, ts₁, ts₂, hp₁, hp₂⟩

variable {M f} (hM : ∀ w v, M.rel w v ↔ v = f w) (hlen : LengthPreserving f)

include hM hlen in
/-- Every accepting run writes as many letters as it reads. -/
lemma balanced {q₀ p : Q} {ts : List (Q × List A × List B × Q)}
    (h₀ : q₀ ∈ M.init) (hp : p ∈ M.final) (hpath : M.Path q₀ ts p) :
    (NFAO.outputOf ts).length = (LabAut.inputOf ts).length := by
  have hrel : M.rel (LabAut.inputOf ts) (NFAO.outputOf ts) :=
    ⟨ts, ⟨q₀, h₀, p, hp, hpath⟩, rfl, rfl⟩
  rw [hM] at hrel
  rw [hrel]
  exact hlen _

include hM hlen in
/-- The type of a productive state. -/
lemma exists_typing {q : Q} (hq : Productive M q) :
    ∃ d : ℤ, ∀ (q₀ : Q) (ts : List (Q × List A × List B × Q)), q₀ ∈ M.init → M.Path q₀ ts q →
      ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + d := by
  obtain ⟨q₀, h₀, p, hp, ts₁, ts₂, hp₁, hp₂⟩ := hq
  refine ⟨((NFAO.outputOf ts₁).length : ℤ) - (LabAut.inputOf ts₁).length, ?_⟩
  intro q₀' ts h₀' hpath
  have e1 : (NFAO.outputOf (ts₁ ++ ts₂)).length = (LabAut.inputOf (ts₁ ++ ts₂)).length :=
    balanced hM hlen h₀ hp (hp₁.append hp₂)
  have e2 : (NFAO.outputOf (ts ++ ts₂)).length = (LabAut.inputOf (ts ++ ts₂)).length :=
    balanced hM hlen h₀' hp (hpath.append hp₂)
  rw [NFAO.outputOf_append, LabAut.inputOf_append] at e1 e2
  simp only [List.length_append] at e1 e2
  omega

open Classical in
/-- The type of a state: the difference between the length of the output and
the length of the input of any run from an initial state to it. -/
noncomputable def tau (q : Q) : ℤ :=
  if h : Productive M q then (exists_typing hM hlen h).choose else 0

lemma tau_spec {q : Q} (hq : Productive M q) {q₀ : Q}
    {ts : List (Q × List A × List B × Q)} (h₀ : q₀ ∈ M.init) (hpath : M.Path q₀ ts q) :
    ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + tau hM hlen q := by
  rw [tau, dif_pos hq]
  exact (exists_typing hM hlen hq).choose_spec q₀ ts h₀ hpath

lemma tau_init {q : Q} (hq : Productive M q) (h₀ : q ∈ M.init) : tau hM hlen q = 0 := by
  have := tau_spec hM hlen hq h₀ (LabAut.Path.nil q)
  simpa using this.symm

lemma tau_final {q : Q} (hq : Productive M q) (hf : q ∈ M.final) : tau hM hlen q = 0 := by
  obtain ⟨q₀, h₀, ts₁, hp₁⟩ := ((productive_iff M q).1 hq).1
  have hbal := balanced hM hlen h₀ hf hp₁
  have := tau_spec hM hlen hq h₀ hp₁
  omega

lemma tau_step {q q' : Q} {u : List A} {x : List B} (hq : Productive M q)
    (hq' : Productive M q') (ht : (q, u, x, q') ∈ M.δ) :
    tau hM hlen q' = tau hM hlen q + x.length - u.length := by
  obtain ⟨q₀, h₀, ts₁, hp₁⟩ := ((productive_iff M q).1 hq).1
  have hpath' : M.Path q₀ (ts₁ ++ [(q, u, x, q')]) q' :=
    hp₁.append (LabAut.Path.cons ht (LabAut.Path.nil q'))
  have e1 := tau_spec hM hlen hq h₀ hp₁
  have e2 := tau_spec hM hlen hq' h₀ hpath'
  rw [NFAO.outputOf_append, LabAut.inputOf_append] at e2
  simp only [List.length_append, NFAO.outputOf_cons, NFAO.outputOf_nil, LabAut.inputOf_cons,
    LabAut.inputOf_nil, List.append_nil] at e2
  push_cast at e2
  omega

/-! ## The balanced automaton -/

/-- The states of the new automaton: a state of `M` together with a string of
length `|τ q|`, the output that is produced but not yet emitted (if `τ q ≥ 0`)
or emitted but not yet produced (if `τ q ≤ 0`). -/
def StSet : Set (Q × List B) := {p | p.2.length = (tau hM hlen p.1).natAbs}

lemma stSet_finite [Finite Q] [Finite B] : (StSet hM hlen).Finite := by
  obtain ⟨N, hN⟩ := (Set.finite_range (fun q : Q => (tau hM hlen q).natAbs)).bddAbove
  refine Set.Finite.subset
    (Set.Finite.prod (Set.finite_univ (α := Q)) (List.finite_length_le B N)) ?_
  rintro ⟨q, s⟩ hs
  refine ⟨trivial, ?_⟩
  simp only [StSet, Set.mem_setOf_eq] at hs
  simp only [Set.mem_setOf_eq, hs]
  exact hN ⟨q, rfl⟩

/-- A state of the new automaton. -/
abbrev St : Type := ↑(StSet hM hlen)

instance [Finite Q] [Finite B] : Finite (St hM hlen) := (stSet_finite hM hlen).to_subtype

/-- The output produced but not yet emitted. -/
noncomputable def pen (σ : St hM hlen) : List B := if 0 ≤ tau hM hlen σ.val.1 then σ.val.2 else []

/-- The output emitted but not yet produced. -/
noncomputable def deb (σ : St hM hlen) : List B := if 0 ≤ tau hM hlen σ.val.1 then [] else σ.val.2

lemma pen_or_deb_nil (σ : St hM hlen) : pen hM hlen σ = [] ∨ deb hM hlen σ = [] := by
  unfold pen deb
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma pen_nil_of_buffer_nil {σ : St hM hlen} (h : σ.val.2 = []) : pen hM hlen σ = [] := by
  unfold pen; split_ifs <;> simp [h]

lemma deb_nil_of_buffer_nil {σ : St hM hlen} (h : σ.val.2 = []) : deb hM hlen σ = [] := by
  unfold deb; split_ifs <;> simp [h]

/-- The transitions of the new automaton: a transition of `M` together with an
emitted string of the same length as the input, subject to the bookkeeping
equation for the buffers. -/
def bdelta : Set (St hM hlen × List A × List B × St hM hlen) :=
  {z | ∃ (σ σ' : St hM hlen) (u : List A) (v x : List B),
    (σ.val.1, u, x, σ'.val.1) ∈ M.δ ∧ v.length = u.length ∧
      deb hM hlen σ ++ v ++ pen hM hlen σ' = pen hM hlen σ ++ x ++ deb hM hlen σ' ∧
      z = (σ, u, v, σ')}

lemma bdelta_finite [Finite A] [Finite B] [Finite Q]
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) :
    (bdelta hM hlen).Finite := by
  refine Set.Finite.subset
    (Set.Finite.prod (Set.finite_univ (α := St hM hlen))
      (Set.Finite.prod (List.finite_length_le A 1)
        (Set.Finite.prod (List.finite_length_le B 1)
          (Set.finite_univ (α := St hM hlen))))) ?_
  rintro ⟨σ, u, v, σ'⟩ ⟨σ₁, σ₁', u₁, v₁, x₁, ht, hv, _, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  exact ⟨trivial, (hatom _ ht).1, by simpa [hv] using (hatom _ ht).1, trivial⟩

/-- The automaton in which every transition emits as many letters as it
reads. -/
def bAut [Finite A] [Finite B] [Finite Q]
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) :
    NFAO A B (St hM hlen) where
  init := {σ | σ.val.1 ∈ M.init ∧ σ.val.2 = []}
  final := {σ | σ.val.1 ∈ M.final ∧ σ.val.2 = []}
  δ := bdelta hM hlen
  δ_finite := bdelta_finite hM hlen hatom

lemma bAut_balanced [Finite A] [Finite B] [Finite Q]
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) :
    ∀ t ∈ (bAut hM hlen hatom).δ, t.2.1.length = t.2.2.1.length := by
  rintro ⟨σ, u, v, σ'⟩ ⟨σ₁, σ₁', u₁, v₁, x₁, ht, hv, _, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  exact hv.symm

/-! ### Soundness -/

/-- Gluing two steps of the bookkeeping equation. -/
lemma glue {D₀ v₁ P₁ P₀ x₁ D₁ v₂ P₂ x₂ D₂ : List B}
    (h₁ : D₀ ++ v₁ ++ P₁ = P₀ ++ x₁ ++ D₁) (h₂ : D₁ ++ v₂ ++ P₂ = P₁ ++ x₂ ++ D₂)
    (hmid : P₁ = [] ∨ D₁ = []) :
    D₀ ++ (v₁ ++ v₂) ++ P₂ = P₀ ++ (x₁ ++ x₂) ++ D₂ := by
  rcases hmid with hP | hD
  · subst hP
    simp only [List.append_nil, List.nil_append] at h₁ h₂
    calc D₀ ++ (v₁ ++ v₂) ++ P₂ = (D₀ ++ v₁) ++ (v₂ ++ P₂) := by simp [List.append_assoc]
      _ = (P₀ ++ x₁ ++ D₁) ++ (v₂ ++ P₂) := by rw [h₁]
      _ = P₀ ++ x₁ ++ (D₁ ++ v₂ ++ P₂) := by simp [List.append_assoc]
      _ = P₀ ++ x₁ ++ (x₂ ++ D₂) := by rw [h₂]
      _ = P₀ ++ (x₁ ++ x₂) ++ D₂ := by simp [List.append_assoc]
  · subst hD
    simp only [List.append_nil, List.nil_append] at h₁ h₂
    calc D₀ ++ (v₁ ++ v₂) ++ P₂ = (D₀ ++ v₁) ++ (v₂ ++ P₂) := by simp [List.append_assoc]
      _ = (D₀ ++ v₁) ++ (P₁ ++ x₂ ++ D₂) := by rw [h₂]
      _ = (D₀ ++ v₁ ++ P₁) ++ (x₂ ++ D₂) := by simp [List.append_assoc]
      _ = (P₀ ++ x₁) ++ (x₂ ++ D₂) := by rw [h₁]
      _ = P₀ ++ (x₁ ++ x₂) ++ D₂ := by simp [List.append_assoc]

lemma bAut_sound [Finite A] [Finite B] [Finite Q]
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    {σ σ' : St hM hlen} {w : List A} {v : List B}
    (h : (bAut hM hlen hatom).relFrom σ w v σ') :
    ∃ x, M.relFrom σ.val.1 w x σ'.val.1 ∧
      deb hM hlen σ ++ v ++ pen hM hlen σ' = pen hM hlen σ ++ x ++ deb hM hlen σ' := by
  refine NFAO.relFrom_induction (M := bAut hM hlen hatom)
    (motive := fun σ w v => ∃ x, M.relFrom σ.val.1 w x σ'.val.1 ∧
      deb hM hlen σ ++ v ++ pen hM hlen σ' = pen hM hlen σ ++ x ++ deb hM hlen σ') ?_ ?_ h
  · refine ⟨[], NFAO.relFrom_nil _ _, ?_⟩
    rcases pen_or_deb_nil hM hlen σ' with hP | hP <;> simp [hP]
  · rintro σ₀ σ₁ u v₁ w₂ v₂ ht _ ⟨x₂, hrel₂, heq₂⟩
    obtain ⟨σa, σb, u', v', x₁, htM, hvlen, heq₁, hz⟩ := ht
    simp only [Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hz
    exact ⟨x₁ ++ x₂, NFAO.relFrom_step htM hrel₂,
      glue heq₁ heq₂ (pen_or_deb_nil hM hlen _)⟩

/-! ### Completeness -/

lemma pen_eq_seg {X : List B} {σ : St hM hlen} {n m : ℕ}
    (htau : tau hM hlen σ.val.1 = (m : ℤ) - (n : ℤ))
    (hs : σ.val.2 = seg X (min n m) (max n m)) :
    pen hM hlen σ = if n ≤ m then seg X n m else [] := by
  unfold pen
  rw [htau]
  by_cases h : n ≤ m
  · rw [if_pos (by omega : (0:ℤ) ≤ (m:ℤ) - n), if_pos h, hs, min_eq_left h, max_eq_right h]
  · rw [if_neg (by omega : ¬ (0:ℤ) ≤ (m:ℤ) - n), if_neg h]

lemma deb_eq_seg {X : List B} {σ : St hM hlen} {n m : ℕ}
    (htau : tau hM hlen σ.val.1 = (m : ℤ) - (n : ℤ))
    (hs : σ.val.2 = seg X (min n m) (max n m)) :
    deb hM hlen σ = if n ≤ m then [] else seg X m n := by
  unfold deb
  rw [htau]
  by_cases h : n ≤ m
  · rw [if_pos (by omega : (0:ℤ) ≤ (m:ℤ) - n), if_pos h]
  · rw [if_neg (by omega : ¬ (0:ℤ) ≤ (m:ℤ) - n), if_neg h, hs,
      min_eq_right (by omega : m ≤ n), max_eq_left (by omega : m ≤ n)]

/-- The bookkeeping equation for the buffers, in terms of the positions in the
total output. -/
lemma buffer_eq {X : List B} {n m n₁ m₁ : ℕ} (hn : n ≤ n₁) (hm : m ≤ m₁) :
    (if n ≤ m then ([] : List B) else seg X m n) ++ seg X n n₁ ++
        (if n₁ ≤ m₁ then seg X n₁ m₁ else [])
      = (if n ≤ m then seg X n m else []) ++ seg X m m₁ ++
        (if n₁ ≤ m₁ then [] else seg X m₁ n₁) := by
  by_cases h1 : n ≤ m <;> by_cases h2 : n₁ ≤ m₁ <;>
    simp only [h1, h2, if_false, if_pos, List.nil_append, List.append_nil]
  · rw [seg_concat X hn h2, seg_concat X h1 hm]
  · rw [seg_concat X h1 hm, seg_concat X (by omega : n ≤ m₁) (by omega : m₁ ≤ n₁)]
  · rw [seg_concat X (by omega : m ≤ n) hn, seg_concat X (by omega : m ≤ n₁) h2]
  · rw [seg_concat X (by omega : m ≤ n) hn, seg_concat X hm (by omega : m₁ ≤ n₁)]

/-- Every run of `M` is matched by a run of the balanced automaton: the `i`-th
letter of the output is emitted while the `i`-th letter of the input is read,
and the buffers are the segments of the output between the two positions. -/
lemma bAut_complete_aux [Finite A] [Finite B] [Finite Q]
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    {q q' : Q} {ts : List (Q × List A × List B × Q)} (hpath : M.Path q ts q') :
    Reach M q → CoReach M q' →
    ∀ (X : List B) (n m : ℕ) (σ σ' : St hM hlen),
      σ.val.1 = q → σ'.val.1 = q' →
      tau hM hlen q = (m : ℤ) - (n : ℤ) →
      NFAO.outputOf ts = seg X m (m + (NFAO.outputOf ts).length) →
      n + (LabAut.inputOf ts).length ≤ X.length →
      m + (NFAO.outputOf ts).length ≤ X.length →
      σ.val.2 = seg X (min n m) (max n m) →
      σ'.val.2 = seg X (min (n + (LabAut.inputOf ts).length) (m + (NFAO.outputOf ts).length))
                       (max (n + (LabAut.inputOf ts).length) (m + (NFAO.outputOf ts).length)) →
      (bAut hM hlen hatom).relFrom σ (LabAut.inputOf ts)
        (seg X n (n + (LabAut.inputOf ts).length)) σ' := by
  induction hpath with
  | nil q₀ =>
      intro _ _ X n m σ σ' h1 h2 _ _ _ _ hs hs'
      simp only [LabAut.inputOf_nil, NFAO.outputOf_nil, List.length_nil, Nat.add_zero] at hs' ⊢
      have hσ : σ = σ' := Subtype.ext (Prod.ext (h1.trans h2.symm) (by rw [hs, hs']))
      subst hσ
      simpa using NFAO.relFrom_nil (bAut hM hlen hatom) σ
  | @cons q u x q₁ rest qend ht hrest ih =>
      intro hreach hco X n m σ σ' hσ1 hσ'1 htau hout hbn hbm hs hs'
      have hin : LabAut.inputOf ((q, u, x, q₁) :: rest) = u ++ LabAut.inputOf rest := rfl
      have houtc : NFAO.outputOf ((q, u, x, q₁) :: rest) = x ++ NFAO.outputOf rest := rfl
      have hlin : (LabAut.inputOf ((q, u, x, q₁) :: rest)).length
          = u.length + (LabAut.inputOf rest).length := by rw [hin, List.length_append]
      have hlout : (NFAO.outputOf ((q, u, x, q₁) :: rest)).length
          = x.length + (NFAO.outputOf rest).length := by rw [houtc, List.length_append]
      rw [hlin] at hbn hs' ⊢
      rw [hlout] at hbm hs'
      set n₁ := n + u.length with hn₁
      set m₁ := m + x.length with hm₁
      have e1 : n + (u.length + (LabAut.inputOf rest).length)
          = n₁ + (LabAut.inputOf rest).length := by omega
      have e2 : m + (x.length + (NFAO.outputOf rest).length)
          = m₁ + (NFAO.outputOf rest).length := by omega
      rw [e1, e2] at hs'
      rw [e1] at hbn ⊢
      rw [e2] at hbm
      obtain ⟨p, hp, ts₂, hpath₂⟩ := hco
      have hcoq : CoReach M q :=
        ⟨p, hp, ((q, u, x, q₁) :: rest) ++ ts₂, (LabAut.Path.cons ht hrest).append hpath₂⟩
      have hq : Productive M q := (productive_iff M q).2 ⟨hreach, hcoq⟩
      have hreach₁ : Reach M q₁ := by
        obtain ⟨q₀, h₀, ts₀, hp₀⟩ := hreach
        exact ⟨q₀, h₀, ts₀ ++ [(q, u, x, q₁)],
          hp₀.append (LabAut.Path.cons ht (LabAut.Path.nil q₁))⟩
      have hcoq₁ : CoReach M q₁ := ⟨p, hp, rest ++ ts₂, hrest.append hpath₂⟩
      have hq₁ : Productive M q₁ := (productive_iff M q₁).2 ⟨hreach₁, hcoq₁⟩
      have htau₁ : tau hM hlen q₁ = (m₁ : ℤ) - (n₁ : ℤ) := by
        rw [tau_step hM hlen hq hq₁ ht, htau, hn₁, hm₁]
        push_cast
        ring
      have hout2 : x ++ NFAO.outputOf rest = seg X m (m₁ + (NFAO.outputOf rest).length) := by
        rw [← e2, ← hlout, ← houtc]
        exact hout
      obtain ⟨hx, hrestout⟩ := List.append_inj
        (hout2.trans (seg_concat X (by omega : m ≤ m₁)
          (by omega : m₁ ≤ m₁ + (NFAO.outputOf rest).length)).symm)
        (by rw [seg_length X m m₁ (by omega)]; omega : x.length = (seg X m m₁).length)
      have hwf : ((q₁, seg X (min n₁ m₁) (max n₁ m₁)) : Q × List B) ∈ StSet hM hlen := by
        show (seg X (min n₁ m₁) (max n₁ m₁)).length = (tau hM hlen q₁).natAbs
        rw [seg_length X _ _ (by omega : max n₁ m₁ ≤ X.length)]
        omega
      set σ₁ : St hM hlen := ⟨(q₁, seg X (min n₁ m₁) (max n₁ m₁)), hwf⟩ with hσ₁
      have hσ₁₁ : σ₁.val.1 = q₁ := rfl
      have hσ₁₂ : σ₁.val.2 = seg X (min n₁ m₁) (max n₁ m₁) := rfl
      have htrans : (σ, u, seg X n n₁, σ₁) ∈ (bAut hM hlen hatom).δ := by
        refine ⟨σ, σ₁, u, seg X n n₁, x, ?_, ?_, ?_, rfl⟩
        · rw [hσ1, hσ₁₁]; exact ht
        · rw [seg_length X n n₁ (by omega)]; omega
        · rw [deb_eq_seg hM hlen (by rw [hσ1]; exact htau) hs,
            pen_eq_seg hM hlen (by rw [hσ1]; exact htau) hs,
            deb_eq_seg hM hlen (X := X) (n := n₁) (m := m₁) (by rw [hσ₁₁]; exact htau₁) hσ₁₂,
            pen_eq_seg hM hlen (X := X) (n := n₁) (m := m₁) (by rw [hσ₁₁]; exact htau₁) hσ₁₂, hx]
          exact buffer_eq (X := X) (by omega) (by omega)
      have hIH := ih hreach₁ ⟨p, hp, ts₂, hpath₂⟩ X n₁ m₁ σ₁ σ' hσ₁₁ hσ'1 htau₁ hrestout hbn hbm
        hσ₁₂ hs'
      have hstep := NFAO.relFrom_step htrans hIH
      rw [seg_concat X (by omega : n ≤ n₁)
        (by omega : n₁ ≤ n₁ + (LabAut.inputOf rest).length)] at hstep
      rw [hin]
      exact hstep

/-! ### The balanced automaton computes the same relation -/

lemma bAut_rel [Finite A] [Finite B] [Finite Q]
    (hatom : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) (w : List A) (v : List B) :
    (bAut hM hlen hatom).rel w v ↔ M.rel w v := by
  constructor
  · rw [NFAO.rel_iff_relFrom, NFAO.rel_iff_relFrom]
    rintro ⟨σ, ⟨hσinit, hσnil⟩, σ', ⟨hσ'fin, hσ'nil⟩, hrel⟩
    obtain ⟨x, hMrel, heq⟩ := bAut_sound hM hlen hatom hrel
    rw [pen_nil_of_buffer_nil hM hlen hσnil, deb_nil_of_buffer_nil hM hlen hσnil,
      pen_nil_of_buffer_nil hM hlen hσ'nil, deb_nil_of_buffer_nil hM hlen hσ'nil] at heq
    simp only [List.nil_append, List.append_nil] at heq
    exact ⟨σ.val.1, hσinit, σ'.val.1, hσ'fin, heq ▸ hMrel⟩
  · intro hrel
    obtain ⟨ts, ⟨q₀, h₀, p, hp, hpath⟩, hinp, houtp⟩ := hrel
    subst hinp
    subst houtp
    have hbal : (NFAO.outputOf ts).length = (LabAut.inputOf ts).length :=
      balanced hM hlen h₀ hp hpath
    have hreach₀ : Reach M q₀ := ⟨q₀, h₀, [], LabAut.Path.nil q₀⟩
    have hco₀ : CoReach M q₀ := ⟨p, hp, ts, hpath⟩
    have hcop : CoReach M p := ⟨p, hp, [], LabAut.Path.nil p⟩
    have hreachp : Reach M p := ⟨q₀, h₀, ts, hpath⟩
    have htau₀ : tau hM hlen q₀ = 0 :=
      tau_init hM hlen ((productive_iff M q₀).2 ⟨hreach₀, hco₀⟩) h₀
    have htaup : tau hM hlen p = 0 :=
      tau_final hM hlen ((productive_iff M p).2 ⟨hreachp, hcop⟩) hp
    have hwf₀ : ((q₀, ([] : List B)) : Q × List B) ∈ StSet hM hlen := by
      show ([] : List B).length = (tau hM hlen q₀).natAbs
      simp [htau₀]
    have hwfp : ((p, ([] : List B)) : Q × List B) ∈ StSet hM hlen := by
      show ([] : List B).length = (tau hM hlen p).natAbs
      simp [htaup]
    have hkey := bAut_complete_aux hM hlen hatom hpath hreach₀ hcop (NFAO.outputOf ts) 0 0
      (⟨(q₀, []), hwf₀⟩ : St hM hlen) (⟨(p, []), hwfp⟩ : St hM hlen) rfl rfl
      (by simp [htau₀])
      (by simp [seg])
      (by omega) (by omega) (by simp)
      (by rw [Nat.zero_add, Nat.zero_add, hbal, min_self, max_self, seg_self])
    have hvv : seg (NFAO.outputOf ts) 0 (0 + (LabAut.inputOf ts).length) = NFAO.outputOf ts := by
      simp [seg, ← hbal]
    rw [hvv] at hkey
    rw [NFAO.rel_iff_relFrom]
    exact ⟨⟨(q₀, []), hwf₀⟩, ⟨h₀, rfl⟩, ⟨(p, []), hwfp⟩, ⟨hp, rfl⟩, hkey⟩

end LenNF

/-- **Lemma `lem:characterisation-length-preserving`.**  If a rational function is
length-preserving, then it is computed by an nfa with output in which the input and output strings
of every transition have the same length. -/
theorem lengthPreserving_rational_normal_form_aux {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hlen : LengthPreserving f) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
      (∀ t ∈ M.δ, t.2.1.length = t.2.2.1.length) ∧ ∀ w v, M.rel w v ↔ v = f w := by
  obtain ⟨Q, hQ, M, hatom, hrel⟩ := exists_atomic_nfao hf
  have hM : ∀ w v, M.rel w v ↔ v = f w := fun w v => (hrel w v).symm
  exact ⟨LenNF.St hM hlen, inferInstance, LenNF.bAut hM hlen hatom,
    LenNF.bAut_balanced hM hlen hatom,
    fun w v => (LenNF.bAut_rel hM hlen hatom w v).trans (hM w v)⟩

end Lax132576Proofs.Transducers
