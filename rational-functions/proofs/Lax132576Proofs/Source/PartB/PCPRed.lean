/- Theorem `thm:undecidable-equivalence-rational-relations` of *Transducers* (M. Bojańczyk): the
equivalence problem for rational relations is undecidable.

Following the book, undecidability is obtained by a reduction from the Post
correspondence problem, whose undecidability is taken as an explicit hypothesis
(it is a classical result that is not proved here).

Given an instance of the Post correspondence problem, that is a finite list of
pairs of strings `(u₀, v₀), …, (u_{n-1}, v_{n-1})`, write `g` and `h` for the
two homomorphisms `i ↦ uᵢ` and `i ↦ vᵢ` from `A* = {0, …, n-1}*` to
`B* = {0, …, m-1}*`, where `m` is larger than every letter occurring in the
instance.  The reduction produces the two relations

* `R₁ = {(w, v) ∈ A* × B* | w = ε or v ≠ g w or v ≠ h w}`,
* `R₂ = A* × B*`,

which are equal exactly when the instance has no solution.  The relation `R₁` is rational because
the complement of a homomorphism is rational (Claim `claim:homomorphism-complement-rational`); the
automaton is written out explicitly here, since the reduction has to be a computable function on
codes. -/
import Lax132576Proofs.Source.PartB.Codes
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace PCP

/-! ## The Post correspondence problem -/

/-- An instance of the Post correspondence problem: a finite list of pairs of
strings over the alphabet `ℕ`. -/
abbrev Instance := List (List ℕ × List ℕ)

/-- A transition of an automaton described by a code. -/
private abbrev Tr := ℕ × List ℕ × List ℕ × ℕ

/-- The parameters of a component: the homomorphism, the size of the output
alphabet and the number of the first state. -/
private abbrev Prm := List (List ℕ) × ℕ × ℕ

/-- The concatenation of the strings `ws` selected by a list of indices; this is
the homomorphic image of the index string. -/
def conc (ws : List (List ℕ)) (idx : List ℕ) : List ℕ :=
  (idx.map (fun i => ws.getD i [])).flatten

@[simp] lemma conc_nil (ws : List (List ℕ)) : conc ws [] = [] := rfl

@[simp] lemma conc_cons (ws : List (List ℕ)) (i : ℕ) (idx : List ℕ) :
    conc ws (i :: idx) = ws.getD i [] ++ conc ws idx := rfl

/-- **The Post correspondence problem.**  An instance is solvable if some
nonempty sequence of indices makes the two concatenations equal. -/
def Solvable (P : Instance) : Prop :=
  ∃ idx : List ℕ, idx ≠ [] ∧ (∀ i ∈ idx, i < P.length) ∧
    conc (P.map Prod.fst) idx = conc (P.map Prod.snd) idx

/-! ## The automata produced by the reduction -/

/-- `Good n w` says that all letters of `w` are smaller than `n`. -/
def Good (n : ℕ) (w : List ℕ) : Prop := ∀ i ∈ w, i < n

lemma Good.nil (n : ℕ) : Good n [] := by simp [Good]

lemma Good.append {n : ℕ} {w v : List ℕ} (hw : Good n w) (hv : Good n v) :
    Good n (w ++ v) := by
  intro i hi
  rcases List.mem_append.1 hi with h | h
  · exact hw i h
  · exact hv i h

/-- The transitions of the component of the automaton that checks that the
output is *not* the image of the input under the homomorphism given by `ws`.
The four states of the component are `s` (the output produced so far is the
image of the input read so far), `s+1` (the output is a proper prefix of the
image and is finished), `s+2` (a mismatching letter has been produced, so both
the remaining input and the remaining output are arbitrary) and `s+3` (the
input is finished and the output is still growing). -/
def compTrans (ws : List (List ℕ)) (m s : ℕ) : List Tr :=
  (List.range ws.length).flatMap (fun i =>
      (s, [i], ws.getD i [], s) :: (s + 1, [i], [], s + 1) :: (s + 2, [i], [], s + 2) ::
        (List.range (ws.getD i []).length).flatMap (fun k =>
          (s, [i], (ws.getD i []).take k, s + 1) ::
            ((List.range m).filter (fun b => !(b == (ws.getD i []).getD k 0))).map
              (fun b => (s, [i], (ws.getD i []).take k ++ [b], s + 2)))) ++
    (List.range m).flatMap (fun b =>
      [(s, [], [b], s + 3), (s + 2, [], [b], s + 2), (s + 3, [], [b], s + 3)])

/-- The eight families of transitions of a component. -/
lemma mem_compTrans {ws : List (List ℕ)} {m s : ℕ} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ compTrans ws m s ↔
      (∃ i < ws.length, t = (s, [i], ws.getD i [], s)) ∨
      (∃ i < ws.length, t = (s + 1, [i], [], s + 1)) ∨
      (∃ i < ws.length, t = (s + 2, [i], [], s + 2)) ∨
      (∃ i < ws.length, ∃ k < (ws.getD i []).length,
        t = (s, [i], (ws.getD i []).take k, s + 1)) ∨
      (∃ i < ws.length, ∃ k < (ws.getD i []).length, ∃ b < m,
        b ≠ (ws.getD i []).getD k 0 ∧ t = (s, [i], (ws.getD i []).take k ++ [b], s + 2)) ∨
      (∃ b < m, t = (s, [], [b], s + 3)) ∨
      (∃ b < m, t = (s + 2, [], [b], s + 2)) ∨
      (∃ b < m, t = (s + 3, [], [b], s + 3)) := by
  simp only [compTrans, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.mem_map, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨b, hb, h⟩)
    · rcases h with h | h | h | ⟨k, hk, h | ⟨b, ⟨hb, hbne⟩, h⟩⟩
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr (Or.inl ⟨i, hi, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨i, hi, h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, k, hk, h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, k, hk, b, hb, hbne, h.symm⟩))))
    · rcases h with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, hb, h⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, hb, h⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, hb, h⟩))))))
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, k, hk, h⟩ |
      ⟨i, hi, k, hk, b, hb, hbne, h⟩ | ⟨b, hb, h⟩ | ⟨b, hb, h⟩ | ⟨b, hb, h⟩)
    · exact Or.inl ⟨i, hi, Or.inl h⟩
    · exact Or.inl ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨i, hi, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨i, hi, Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inl h⟩))⟩
    · exact Or.inl ⟨i, hi, Or.inr (Or.inr (Or.inr ⟨k, hk, Or.inr ⟨b, ⟨hb, hbne⟩, h.symm⟩⟩))⟩
    · exact Or.inr ⟨b, hb, Or.inl h⟩
    · exact Or.inr ⟨b, hb, Or.inr (Or.inl h)⟩
    · exact Or.inr ⟨b, hb, Or.inr (Or.inr h)⟩

/-! ## Elementary lemmas about runs -/

/-- A state with a loop reading one letter of the input and producing no output
reads any string over the input alphabet. -/
lemma loop_in {M : NFAO ℕ ℕ ℕ} {e n : ℕ} (hδ : ∀ i < n, (e, [i], [], e) ∈ M.δ)
    {w : List ℕ} (hw : Good n w) : M.relFrom e w [] e := by
  induction w with
  | nil => exact M.relFrom_nil e
  | cons i w ih =>
      have hi : i < n := hw i (by simp)
      have hstep := NFAO.relFrom_step (hδ i hi) (ih fun j hj => hw j (by simp [hj]))
      simpa using hstep

/-- A state with a loop producing one letter of the output and reading no input
produces any string over the output alphabet. -/
lemma loop_out {M : NFAO ℕ ℕ ℕ} {e m : ℕ} (hδ : ∀ b < m, (e, [], [b], e) ∈ M.δ)
    {v : List ℕ} (hv : Good m v) : M.relFrom e [] v e := by
  induction v with
  | nil => exact M.relFrom_nil e
  | cons b v ih =>
      have hb : b < m := hv b (by simp)
      have hstep := NFAO.relFrom_step (hδ b hb) (ih fun c hc => hv c (by simp [hc]))
      simpa using hstep

/-- A state with both loops relates any pair of strings over the two
alphabets. -/
lemma loop_both {M : NFAO ℕ ℕ ℕ} {e n m : ℕ} (hin : ∀ i < n, (e, [i], [], e) ∈ M.δ)
    (hout : ∀ b < m, (e, [], [b], e) ∈ M.δ) {w v : List ℕ} (hw : Good n w) (hv : Good m v) :
    M.relFrom e w v e := by
  simpa using NFAO.relFrom_trans (loop_in hin hw) (loop_out hout hv)

/-- Every accepted pair of strings is over the two alphabets, provided that this
holds for every transition. -/
lemma good_of_relFrom {M : NFAO ℕ ℕ ℕ} {n m : ℕ}
    (hδ : ∀ t ∈ M.δ, Good n t.2.1 ∧ Good m t.2.2.1) {q p : ℕ} {w v : List ℕ}
    (h : M.relFrom q w v p) : Good n w ∧ Good m v := by
  refine NFAO.relFrom_induction (motive := fun _ w v => Good n w ∧ Good m v)
    ⟨Good.nil n, Good.nil m⟩ ?_ h
  rintro q q' u x w v ht - ⟨hw, hv⟩
  exact ⟨(hδ _ ht).1.append hw, (hδ _ ht).2.append hv⟩

/-- A state from which every transition reads no input and loops reads only the
empty string. -/
lemma eps_state_sound {M : NFAO ℕ ℕ ℕ} {e : ℕ}
    (hδ : ∀ t ∈ M.δ, t.1 = e → t.2.1 = [] ∧ t.2.2.2 = e) {w v : List ℕ} {p : ℕ}
    (h : M.relFrom e w v p) : w = [] := by
  refine NFAO.relFrom_induction (motive := fun q w _ => q = e → w = []) (by simp) ?_ h rfl
  rintro q q' u x w v ht - ih rfl
  obtain ⟨hu, hq'⟩ := hδ _ ht rfl
  have hu' : u = [] := hu
  have hq'' : q' = q := hq'
  simp [hu', ih hq'']

/-! ## Soundness and completeness of a component -/

/-- The invariant satisfied by the states of a component along a path that ends
in a final state: in the state `s` the output is not the image of the input, in
the state `s+1` the output is empty, and in the state `s+3` the input is
empty. -/
def inv (ws : List (List ℕ)) (s q : ℕ) (w v : List ℕ) : Prop :=
  if q = s then v ≠ conc ws w else if q = s + 1 then v = [] else if q = s + 3 then w = [] else True

@[simp] lemma inv_zero (ws : List (List ℕ)) (s : ℕ) (w v : List ℕ) :
    inv ws s s w v ↔ v ≠ conc ws w := by simp [inv]

@[simp] lemma inv_one (ws : List (List ℕ)) (s : ℕ) (w v : List ℕ) :
    inv ws s (s + 1) w v ↔ v = [] := by
  simp [inv]

@[simp] lemma inv_two (ws : List (List ℕ)) (s : ℕ) (w v : List ℕ) : inv ws s (s + 2) w v := by
  simp [inv]

@[simp] lemma inv_three (ws : List (List ℕ)) (s : ℕ) (w v : List ℕ) :
    inv ws s (s + 3) w v ↔ w = [] := by
  simp [inv]

/-- **Soundness of a component.**  If every transition of `M` whose source is
one of the four states of the component is a transition of the component, then
a path from `s` to a state other than `s` witnesses that the output is not the
image of the input. -/
lemma compTrans_sound {M : NFAO ℕ ℕ ℕ} {ws : List (List ℕ)} {m s : ℕ}
    (hsub : ∀ t ∈ M.δ, (t.1 = s ∨ t.1 = s + 1 ∨ t.1 = s + 2 ∨ t.1 = s + 3) →
      t ∈ compTrans ws m s)
    {p : ℕ} (hp : p ≠ s) {w v : List ℕ} (h : M.relFrom s w v p) : v ≠ conc ws w := by
  have key : ∀ {q : ℕ} {w v : List ℕ}, M.relFrom q w v p →
      (q = s ∨ q = s + 1 ∨ q = s + 2 ∨ q = s + 3) → inv ws s q w v := by
    intro q w v hq
    refine NFAO.relFrom_induction
      (motive := fun q w v => (q = s ∨ q = s + 1 ∨ q = s + 2 ∨ q = s + 3) → inv ws s q w v)
      ?_ ?_ hq
    · rintro (rfl | rfl | rfl | rfl)
      · exact absurd rfl hp
      · simp
      · simp
      · simp
    · rintro q q' u x w v ht - ih hq
      rcases mem_compTrans.1 (hsub _ ht hq) with
        ⟨i, hi, he⟩ | ⟨i, hi, he⟩ | ⟨i, hi, he⟩ | ⟨i, hi, k, hk, he⟩ |
        ⟨i, hi, k, hk, b, hb, hbne, he⟩ | ⟨b, hb, he⟩ | ⟨b, hb, he⟩ | ⟨b, hb, he⟩ <;>
        simp only [Prod.mk.injEq] at he <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      · have h1 : v ≠ conc ws w := by simpa using ih (Or.inl rfl)
        simp only [inv_zero, conc_cons, List.singleton_append]
        simpa using h1
      · have h1 : v = [] := by simpa using ih (Or.inr (Or.inl rfl))
        simp [h1]
      · simp
      · have h1 : v = [] := by simpa using ih (Or.inr (Or.inl rfl))
        subst h1
        simp only [inv_zero, conc_cons, List.singleton_append]
        intro hcon
        have hlen := congrArg List.length hcon
        simp only [List.length_append, List.length_take, List.append_nil] at hlen
        omega
      · simp only [inv_zero, conc_cons, List.singleton_append]
        intro hcon
        have hlen : ((ws.getD i []).take k).length = k := by
          simp only [List.length_take]; omega
        have h1 : (((ws.getD i []).take k ++ [b]) ++ v)[k]? = some b := by
          rw [List.append_assoc,
            List.getElem?_append_right (by omega : ((ws.getD i []).take k).length ≤ k), hlen,
            Nat.sub_self]
          simp
        have h2 : ((ws.getD i []) ++ conc ws w)[k]? = some ((ws.getD i [])[k]'hk) := by
          rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
        have hbne' : b ≠ (ws.getD i [])[k]'hk := by
          rwa [List.getD_eq_getElem (ws.getD i []) 0 hk] at hbne
        rw [hcon, h2] at h1
        exact hbne' (Option.some.inj h1).symm
      · have h1 : w = [] := by simpa using ih (Or.inr (Or.inr (Or.inr rfl)))
        simp [h1]
      · simp
      · have h1 : w = [] := by simpa using ih (Or.inr (Or.inr (Or.inr rfl)))
        simp [h1]
  simpa using key h (Or.inl rfl)

/-- If `x` is not a prefix of `y`, then `y` either stops inside `x`, or has a
letter that differs from the corresponding letter of `x`. -/
lemma prefix_cases : ∀ {x y : List ℕ}, ¬ x <+: y →
    ∃ k < x.length, y = x.take k ∨ ∃ b r, y = x.take k ++ b :: r ∧ b ≠ x.getD k 0 := by
  intro x
  induction x with
  | nil => intro y h; exact absurd List.nil_prefix h
  | cons a x ih =>
      intro y h
      match y with
      | [] => exact ⟨0, by simp, Or.inl (by simp)⟩
      | c :: y' =>
          by_cases hc : c = a
          · subst hc
            have h' : ¬ x <+: y' := fun hpre => h (List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
            obtain ⟨k, hk, hcase⟩ := ih h'
            refine ⟨k + 1, by simpa using hk, ?_⟩
            rcases hcase with rfl | ⟨b, r, hy, hbne⟩
            · exact Or.inl (by simp)
            · exact Or.inr ⟨b, r, by simp [hy], by simpa using hbne⟩
          · exact ⟨0, by simp, Or.inr ⟨c, y', by simp, by simpa using hc⟩⟩

/-- **Completeness of a component.**  If all the transitions of the component
are transitions of `M`, then every pair of strings over the two alphabets whose
output is not the image of the input is related by a path from `s` to one of the
three other states of the component. -/
lemma compTrans_complete {M : NFAO ℕ ℕ ℕ} {ws : List (List ℕ)} {m s : ℕ}
    (hsub : ∀ t ∈ compTrans ws m s, t ∈ M.δ) :
    ∀ {w v : List ℕ}, Good ws.length w → Good m v → v ≠ conc ws w →
      ∃ p, (p = s + 1 ∨ p = s + 2 ∨ p = s + 3) ∧ M.relFrom s w v p := by
  have hin1 : ∀ i < ws.length, (s + 1, [i], [], s + 1) ∈ M.δ := fun i hi =>
    hsub _ (mem_compTrans.2 (Or.inr (Or.inl ⟨i, hi, rfl⟩)))
  have hin2 : ∀ i < ws.length, (s + 2, [i], [], s + 2) ∈ M.δ := fun i hi =>
    hsub _ (mem_compTrans.2 (Or.inr (Or.inr (Or.inl ⟨i, hi, rfl⟩))))
  have hout2 : ∀ b < m, (s + 2, [], [b], s + 2) ∈ M.δ := fun b hb =>
    hsub _ (mem_compTrans.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))))))))
  have hout3 : ∀ b < m, (s + 3, [], [b], s + 3) ∈ M.δ := fun b hb =>
    hsub _ (mem_compTrans.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, hb, rfl⟩))))))))
  intro w
  induction w with
  | nil =>
      intro v hw hv hne
      match v with
      | [] => exact absurd (conc_nil ws).symm hne
      | b :: v' =>
          have hb : b < m := hv b (by simp)
          have ht : (s, [], [b], s + 3) ∈ M.δ :=
            hsub _ (mem_compTrans.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩)))))))
          have hrun := NFAO.relFrom_step ht
            (loop_out hout3 (fun c hc => hv c (List.mem_cons_of_mem b hc)))
          exact ⟨s + 3, Or.inr (Or.inr rfl), by simpa using hrun⟩
  | cons i w' ih =>
      intro v hw hv hne
      have hi : i < ws.length := hw i (by simp)
      have hw' : Good ws.length w' := fun j hj => hw j (by simp [hj])
      by_cases hpre : ws.getD i [] <+: v
      · obtain ⟨v', rfl⟩ := hpre
        have hne' : v' ≠ conc ws w' := fun hcon => hne (by simp [hcon])
        have hv' : Good m v' := fun c hc => hv c (by simp [hc])
        obtain ⟨p, hp, hrun⟩ := ih hw' hv' hne'
        have ht : (s, [i], ws.getD i [], s) ∈ M.δ :=
          hsub _ (mem_compTrans.2 (Or.inl ⟨i, hi, rfl⟩))
        exact ⟨p, hp, by simpa using NFAO.relFrom_step ht hrun⟩
      · obtain ⟨k, hk, hcase⟩ := prefix_cases hpre
        rcases hcase with rfl | ⟨b, r, rfl, hbne⟩
        · have ht : (s, [i], (ws.getD i []).take k, s + 1) ∈ M.δ :=
            hsub _ (mem_compTrans.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, k, hk, rfl⟩)))))
          have hrun := NFAO.relFrom_step ht (loop_in hin1 hw')
          exact ⟨s + 1, Or.inl rfl, by simpa using hrun⟩
        · have hb : b < m := hv b (by simp)
          have hr : Good m r := fun c hc => hv c (by simp [hc])
          have ht : (s, [i], (ws.getD i []).take k ++ [b], s + 2) ∈ M.δ :=
            hsub _ (mem_compTrans.2
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, k, hk, b, hb, hbne, rfl⟩))))))
          have hrun := NFAO.relFrom_step ht (loop_both hin2 hout2 hw' hr)
          exact ⟨s + 2, Or.inr (Or.inl rfl), by simpa using hrun⟩

/-- The source of a transition of a component is one of its four states. -/
lemma compTrans_source {ws : List (List ℕ)} {m s : ℕ} {t : ℕ × List ℕ × List ℕ × ℕ}
    (h : t ∈ compTrans ws m s) : t.1 = s ∨ t.1 = s + 1 ∨ t.1 = s + 2 ∨ t.1 = s + 3 := by
  rcases mem_compTrans.1 h with
    ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, k, hk, rfl⟩ |
    ⟨i, hi, k, hk, b, hb, hbne, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp

/-- The transitions of a component read letters of the input alphabet and write
letters of the output alphabet. -/
lemma compTrans_good {ws : List (List ℕ)} {m s : ℕ} (hm : ∀ l ∈ ws, Good m l)
    {t : ℕ × List ℕ × List ℕ × ℕ} (h : t ∈ compTrans ws m s) :
    Good ws.length t.2.1 ∧ Good m t.2.2.1 := by
  have hgetD : ∀ i : ℕ, Good m (ws.getD i []) := by
    intro i
    by_cases hi : i < ws.length
    · rw [List.getD_eq_getElem ws [] hi]
      exact hm _ (List.getElem_mem hi)
    · rw [List.getD_eq_default ws [] (by omega)]
      exact Good.nil m
  have htake : ∀ (i k : ℕ), Good m ((ws.getD i []).take k) := fun i k c hc =>
    hgetD i c (List.mem_of_mem_take hc)
  rcases mem_compTrans.1 h with
    ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, k, hk, rfl⟩ |
    ⟨i, hi, k, hk, b, hb, hbne, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · exact ⟨by simpa [Good] using hi, hgetD i⟩
  · exact ⟨by simpa [Good] using hi, Good.nil m⟩
  · exact ⟨by simpa [Good] using hi, Good.nil m⟩
  · exact ⟨by simpa [Good] using hi, htake i k⟩
  · exact ⟨by simpa [Good] using hi, (htake i k).append (by simpa [Good] using hb)⟩
  · exact ⟨Good.nil _, by simpa [Good] using hb⟩
  · exact ⟨Good.nil _, by simpa [Good] using hb⟩
  · exact ⟨Good.nil _, by simpa [Good] using hb⟩

/-! ## The reduction -/

lemma le_foldr_max : ∀ (l : List ℕ) {b : ℕ}, b ∈ l → b ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro b hb; simp at hb
  | cons a l ih =>
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · simp
      · exact le_trans (ih hb) (by simp)

/-- A bound on the letters occurring in an instance: the output alphabet of the
automata produced by the reduction is `{0, …, bnd P - 1}`. -/
def bnd (P : Instance) : ℕ := (P.flatMap (fun p => p.1 ++ p.2)).foldr max 0 + 1

lemma good_fst (P : Instance) : ∀ l ∈ P.map Prod.fst, Good (bnd P) l := by
  rintro l hl b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
  have : b ∈ P.flatMap (fun p => p.1 ++ p.2) :=
    List.mem_flatMap.2 ⟨p, hp, by simp [hb]⟩
  have := le_foldr_max _ this
  simp only [bnd]
  omega

lemma good_snd (P : Instance) : ∀ l ∈ P.map Prod.snd, Good (bnd P) l := by
  rintro l hl b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
  have : b ∈ P.flatMap (fun p => p.1 ++ p.2) :=
    List.mem_flatMap.2 ⟨p, hp, by simp [hb]⟩
  have := le_foldr_max _ this
  simp only [bnd]
  omega

lemma good_conc {ws : List (List ℕ)} {m : ℕ} (hm : ∀ l ∈ ws, Good m l) (idx : List ℕ) :
    Good m (conc ws idx) := by
  intro b hb
  obtain ⟨l, hl, hbl⟩ := List.mem_flatten.1 hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem ws [] hi] at hbl
    exact hm _ (List.getElem_mem hi) b hbl
  · rw [List.getD_eq_default ws [] (by omega)] at hbl
    simp at hbl

/-- The first automaton produced by the reduction: it accepts a pair of strings
over the two alphabets when the input is empty or the output differs from one of
the two homomorphic images. -/
def code1 (P : Instance) : RelCode :=
  (compTrans (P.map Prod.fst) (bnd P) 0 ++ compTrans (P.map Prod.snd) (bnd P) 4 ++
      (List.range (bnd P)).map (fun b => (8, [], [b], 8)),
    [0, 4, 8], [1, 2, 3, 5, 6, 7, 8])

/-- The second automaton produced by the reduction: it accepts all pairs of
strings over the two alphabets. -/
def code2 (P : Instance) : RelCode :=
  ((List.range P.length).map (fun i => (0, [i], [], 0)) ++
      (List.range (bnd P)).map (fun b => (0, [], [b], 0)),
    [0], [0])

lemma mem_code1_delta {P : Instance} {t : ℕ × List ℕ × List ℕ × ℕ} :
    t ∈ (codeAut (code1 P)).δ ↔
      t ∈ compTrans (P.map Prod.fst) (bnd P) 0 ∨ t ∈ compTrans (P.map Prod.snd) (bnd P) 4 ∨
        ∃ b < bnd P, t = (8, [], [b], 8) := by
  simp only [codeAut, code1, Set.mem_setOf_eq, List.mem_append, List.mem_map, List.mem_range,
    or_assoc]
  constructor
  · rintro (h | h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
  · rintro (h | h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨b, hb, rfl⟩)

/-- The relation computed by the first automaton of the reduction. -/
lemma code1_rel (P : Instance) (w v : List ℕ) :
    codeRel (code1 P) w v ↔ Good P.length w ∧ Good (bnd P) v ∧
      (w = [] ∨ v ≠ conc (P.map Prod.fst) w ∨ v ≠ conc (P.map Prod.snd) w) := by
  have hlen : (P.map Prod.fst).length = P.length := by simp
  have hlen' : (P.map Prod.snd).length = P.length := by simp
  have hδgood : ∀ t ∈ (codeAut (code1 P)).δ, Good P.length t.2.1 ∧ Good (bnd P) t.2.2.1 := by
    intro t ht
    rcases mem_code1_delta.1 ht with h | h | ⟨b, hb, rfl⟩
    · simpa [hlen] using compTrans_good (good_fst P) h
    · simpa [hlen'] using compTrans_good (good_snd P) h
    · exact ⟨Good.nil _, by simpa [Good] using hb⟩
  constructor
  · intro h
    rw [codeRel, NFAO.rel_iff_relFrom] at h
    obtain ⟨q, hq, p, hp, hrel⟩ := h
    refine ⟨(good_of_relFrom hδgood hrel).1, (good_of_relFrom hδgood hrel).2, ?_⟩
    have hq' : q = 0 ∨ q = 4 ∨ q = 8 := by simpa [codeAut, code1] using hq
    have hp' : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by
      simpa [codeAut, code1] using hp
    rcases hq' with rfl | rfl | rfl
    · refine Or.inr (Or.inl (compTrans_sound (m := bnd P) (s := 0) ?_ (by omega) hrel))
      intro t ht hsrc
      rcases mem_code1_delta.1 ht with h | h | ⟨b, hb, rfl⟩
      · exact h
      · exfalso
        rcases compTrans_source h with h' | h' | h' | h' <;>
          rcases hsrc with h0 | h0 | h0 | h0 <;> omega
      · simp at hsrc
    · refine Or.inr (Or.inr (compTrans_sound (m := bnd P) (s := 4) ?_ (by omega) hrel))
      intro t ht hsrc
      rcases mem_code1_delta.1 ht with h | h | ⟨b, hb, rfl⟩
      · exfalso
        rcases compTrans_source h with h' | h' | h' | h' <;>
          rcases hsrc with h0 | h0 | h0 | h0 <;> omega
      · exact h
      · simp at hsrc
    · refine Or.inl (eps_state_sound ?_ hrel)
      intro t ht h8
      rcases mem_code1_delta.1 ht with h | h | ⟨b, hb, rfl⟩
      · exfalso; rcases compTrans_source h with h' | h' | h' | h' <;> omega
      · exfalso; rcases compTrans_source h with h' | h' | h' | h' <;> omega
      · exact ⟨rfl, rfl⟩
  · rintro ⟨hw, hv, hcase⟩
    rw [codeRel, NFAO.rel_iff_relFrom]
    rcases hcase with rfl | hne | hne
    · refine ⟨8, by simp [codeAut, code1], 8, by simp [codeAut, code1], ?_⟩
      exact loop_out (fun b hb => mem_code1_delta.2 (Or.inr (Or.inr ⟨b, hb, rfl⟩))) hv
    · obtain ⟨p, hp, hrel⟩ := compTrans_complete (M := codeAut (code1 P)) (s := 0)
        (fun t ht => mem_code1_delta.2 (Or.inl ht)) (by simpa [hlen] using hw) hv hne
      exact ⟨0, by simp [codeAut, code1], p, by rcases hp with rfl | rfl | rfl <;>
        simp [codeAut, code1], hrel⟩
    · obtain ⟨p, hp, hrel⟩ := compTrans_complete (M := codeAut (code1 P)) (s := 4)
        (fun t ht => mem_code1_delta.2 (Or.inr (Or.inl ht))) (by simpa [hlen'] using hw) hv hne
      exact ⟨4, by simp [codeAut, code1], p, by rcases hp with rfl | rfl | rfl <;>
        simp [codeAut, code1], hrel⟩

/-- The relation computed by the second automaton of the reduction: all pairs of
strings over the two alphabets. -/
lemma code2_rel (P : Instance) (w v : List ℕ) :
    codeRel (code2 P) w v ↔ Good P.length w ∧ Good (bnd P) v := by
  have hmem : ∀ t : ℕ × List ℕ × List ℕ × ℕ, t ∈ (codeAut (code2 P)).δ ↔
      (∃ i < P.length, t = (0, [i], [], 0)) ∨ ∃ b < bnd P, t = (0, [], [b], 0) := by
    intro t
    simp only [codeAut, code2, Set.mem_setOf_eq, List.mem_append, List.mem_map, List.mem_range]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr ⟨b, hb, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr ⟨b, hb, rfl⟩
  constructor
  · intro h
    rw [codeRel, NFAO.rel_iff_relFrom] at h
    obtain ⟨q, hq, p, hp, hrel⟩ := h
    refine good_of_relFrom ?_ hrel
    intro t ht
    rcases (hmem t).1 ht with ⟨i, hi, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ⟨by simpa [Good] using hi, Good.nil _⟩
    · exact ⟨Good.nil _, by simpa [Good] using hb⟩
  · rintro ⟨hw, hv⟩
    rw [codeRel, NFAO.rel_iff_relFrom]
    refine ⟨0, by simp [codeAut, code2], 0, by simp [codeAut, code2], ?_⟩
    exact loop_both (fun i hi => (hmem _).2 (Or.inl ⟨i, hi, rfl⟩))
      (fun b hb => (hmem _).2 (Or.inr ⟨b, hb, rfl⟩)) hw hv

/-- **The reduction is correct.**  The two automata produced by the reduction
compute the same relation exactly when the instance has no solution. -/
lemma code_eq_iff (P : Instance) : codeRel (code1 P) = codeRel (code2 P) ↔ ¬ Solvable P := by
  constructor
  · rintro heq ⟨idx, hne, hidx, hsol⟩
    have h2 : codeRel (code2 P) idx (conc (P.map Prod.fst) idx) :=
      (code2_rel P _ _).2 ⟨hidx, good_conc (good_fst P) idx⟩
    rw [← heq] at h2
    obtain ⟨-, -, hcase⟩ := (code1_rel P _ _).1 h2
    rcases hcase with rfl | h | h
    · exact hne rfl
    · exact h rfl
    · exact h hsol
  · intro hns
    funext w v
    apply propext
    rw [code1_rel, code2_rel]
    constructor
    · rintro ⟨hw, hv, -⟩
      exact ⟨hw, hv⟩
    · rintro ⟨hw, hv⟩
      refine ⟨hw, hv, ?_⟩
      by_cases hw0 : w = []
      · exact Or.inl hw0
      · by_cases h1 : v = conc (P.map Prod.fst) w
        · exact Or.inr (Or.inr fun h2 => hns ⟨w, hw0, hw, h1.symm.trans h2⟩)
        · exact Or.inr (Or.inl h1)

/-! ## Computability of the reduction

The reduction has to be a computable function on codes; this is checked with
Mathlib's `Primrec` combinators.  The only rewriting needed is that a `filter`
followed by a `map` is a `flatMap`, which avoids a predicate depending on the
parameters. -/

lemma filter_map_eq_flatMap (l : List ℕ) (c : ℕ) (f : ℕ → ℕ × List ℕ × List ℕ × ℕ) :
    (l.filter (fun b => !(b == c))).map f = l.flatMap (fun b => if b = c then [] else [f b]) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : a = c <;> simp [h, ih]

lemma compTrans_eq_flatMap (ws : List (List ℕ)) (m s : ℕ) :
    compTrans ws m s =
      (List.range ws.length).flatMap (fun i =>
        (s, [i], ws.getD i [], s) :: (s + 1, [i], [], s + 1) :: (s + 2, [i], [], s + 2) ::
          (List.range (ws.getD i []).length).flatMap (fun k =>
            (s, [i], (ws.getD i []).take k, s + 1) ::
              (List.range m).flatMap (fun b =>
                if b = (ws.getD i []).getD k 0 then ([] : List Tr)
                else [(s, [i], (ws.getD i []).take k ++ [b], s + 2)]))) ++
      (List.range m).flatMap (fun b =>
        [(s, [], [b], s + 3), (s + 2, [], [b], s + 2), (s + 3, [], [b], s + 3)]) := by
  simp only [compTrans, filter_map_eq_flatMap]

/-- Taking a prefix of a string is primitive recursive. -/
lemma primrec_take : Primrec₂ (fun (l : List ℕ) (k : ℕ) => l.take k) := by
  have key : ∀ (l : List ℕ) (k : ℕ), l.take k = (List.range k).flatMap (fun i => l[i]?.toList) := by
    intro l k
    induction k with
    | zero => simp
    | succ k ih => rw [List.range_succ, List.flatMap_append, ← ih, List.take_add_one]; simp
  have h : Primrec fun p : List ℕ × ℕ => (List.range p.2).flatMap (fun i => p.1[i]?.toList) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp Primrec.snd) ?_
    show Primrec fun q : (List ℕ × ℕ) × ℕ => q.1.1[q.2]?.toList
    exact Primrec.optionToList.comp
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  show Primrec fun p : List ℕ × ℕ => p.1.take p.2
  exact h.of_eq (fun p => (key p.1 p.2).symm)

/-- The transitions of a component are a primitive recursive function of the
homomorphism, the size of the output alphabet and the number of the first
state. -/
lemma primrec_compTrans :
    Primrec (fun x : Prm => compTrans x.1 x.2.1 x.2.2) := by
  have hinner : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ =>
      if q.2 = (q.1.1.1.1.getD q.1.1.2 []).getD q.1.2 0 then
        ([] : List Tr)
      else [(q.1.1.1.2.2, [q.1.1.2], (q.1.1.1.1.getD q.1.1.2 []).take q.1.2 ++ [q.2],
        q.1.1.1.2.2 + 2)]) := by
    have hx : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ => q.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hi : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ => q.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hk : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ => q.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hb : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ => q.2) := Primrec.snd
    have hword : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ => q.1.1.1.1.getD q.1.1.2 []) :=
      (Primrec.list_getD ([] : List ℕ)).comp (Primrec.fst.comp hx) hi
    have hs : Primrec (fun q : ((Prm × ℕ) × ℕ) × ℕ => q.1.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp hx)
    refine Primrec.ite (Primrec.eq.comp hb ((Primrec.list_getD (0 : ℕ)).comp hword hk))
      (Primrec.const ([] : List Tr)) ?_
    refine Primrec.list_cons.comp ?_ (Primrec.const ([] : List Tr))
    refine Primrec.pair hs ?_
    refine Primrec.pair (Primrec.list_cons.comp hi (Primrec.const ([] : List ℕ))) ?_
    refine Primrec.pair ?_ (Primrec.nat_add.comp hs (Primrec.const 2))
    exact Primrec.list_append.comp (primrec_take.comp hword hk)
      (Primrec.list_cons.comp hb (Primrec.const ([] : List ℕ)))
  have hbody2 : Primrec (fun p : (Prm × ℕ) × ℕ =>
      (p.1.1.2.2, [p.1.2], (p.1.1.1.getD p.1.2 []).take p.2, p.1.1.2.2 + 1) ::
        (List.range p.1.1.2.1).flatMap (fun b =>
          if b = (p.1.1.1.getD p.1.2 []).getD p.2 0 then
            ([] : List Tr)
          else [(p.1.1.2.2, [p.1.2], (p.1.1.1.getD p.1.2 []).take p.2 ++ [b],
            p.1.1.2.2 + 2)])) := by
    have hx : Primrec (fun p : (Prm × ℕ) × ℕ => p.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hi : Primrec (fun p : (Prm × ℕ) × ℕ => p.1.2) :=
      Primrec.snd.comp Primrec.fst
    have hk : Primrec (fun p : (Prm × ℕ) × ℕ => p.2) := Primrec.snd
    have hword : Primrec (fun p : (Prm × ℕ) × ℕ => p.1.1.1.getD p.1.2 []) :=
      (Primrec.list_getD ([] : List ℕ)).comp (Primrec.fst.comp hx) hi
    have hs : Primrec (fun p : (Prm × ℕ) × ℕ => p.1.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp hx)
    have hm : Primrec (fun p : (Prm × ℕ) × ℕ => p.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp hx)
    refine Primrec.list_cons.comp ?_ (Primrec.list_flatMap (Primrec.list_range.comp hm) hinner)
    refine Primrec.pair hs ?_
    refine Primrec.pair (Primrec.list_cons.comp hi (Primrec.const ([] : List ℕ))) ?_
    exact Primrec.pair (primrec_take.comp hword hk) (Primrec.nat_add.comp hs (Primrec.const 1))
  have hbody1 : Primrec (fun p : (Prm × ℕ) =>
      (p.1.2.2, [p.2], p.1.1.getD p.2 [], p.1.2.2) :: (p.1.2.2 + 1, [p.2], [], p.1.2.2 + 1) ::
        (p.1.2.2 + 2, [p.2], [], p.1.2.2 + 2) ::
        (List.range (p.1.1.getD p.2 []).length).flatMap (fun k =>
          (p.1.2.2, [p.2], (p.1.1.getD p.2 []).take k, p.1.2.2 + 1) ::
            (List.range p.1.2.1).flatMap (fun b =>
              if b = (p.1.1.getD p.2 []).getD k 0 then
                ([] : List Tr)
              else [(p.1.2.2, [p.2], (p.1.1.getD p.2 []).take k ++ [b], p.1.2.2 + 2)]))) := by
    have hx : Primrec (fun p : (Prm × ℕ) => p.1) := Primrec.fst
    have hi : Primrec (fun p : (Prm × ℕ) => p.2) := Primrec.snd
    have hword : Primrec (fun p : (Prm × ℕ) => p.1.1.getD p.2 []) :=
      (Primrec.list_getD ([] : List ℕ)).comp (Primrec.fst.comp hx) hi
    have hs : Primrec (fun p : (Prm × ℕ) => p.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp hx)
    have hsing : Primrec (fun p : (Prm × ℕ) => [p.2]) :=
      Primrec.list_cons.comp hi (Primrec.const ([] : List ℕ))
    refine Primrec.list_cons.comp
      (Primrec.pair hs (Primrec.pair hsing (Primrec.pair hword hs))) ?_
    refine Primrec.list_cons.comp
      (Primrec.pair (Primrec.nat_add.comp hs (Primrec.const 1))
        (Primrec.pair hsing (Primrec.pair (Primrec.const ([] : List ℕ))
          (Primrec.nat_add.comp hs (Primrec.const 1))))) ?_
    refine Primrec.list_cons.comp
      (Primrec.pair (Primrec.nat_add.comp hs (Primrec.const 2))
        (Primrec.pair hsing (Primrec.pair (Primrec.const ([] : List ℕ))
          (Primrec.nat_add.comp hs (Primrec.const 2))))) ?_
    exact Primrec.list_flatMap
      (Primrec.list_range.comp (Primrec.list_length.comp hword)) hbody2
  have hlast : Primrec (fun q : (Prm × ℕ) =>
      [((q.1.2.2, [], [q.2], q.1.2.2 + 3) : ℕ × List ℕ × List ℕ × ℕ),
        (q.1.2.2 + 2, [], [q.2], q.1.2.2 + 2), (q.1.2.2 + 3, [], [q.2], q.1.2.2 + 3)]) := by
    have hs : Primrec (fun q : (Prm × ℕ) => q.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hbl : Primrec (fun q : (Prm × ℕ) => [q.2]) :=
      Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ))
    have h1 : Primrec (fun q : (Prm × ℕ) =>
        ((q.1.2.2, [], [q.2], q.1.2.2 + 3) : ℕ × List ℕ × List ℕ × ℕ)) :=
      Primrec.pair hs (Primrec.pair (Primrec.const ([] : List ℕ))
        (Primrec.pair hbl (Primrec.nat_add.comp hs (Primrec.const 3))))
    have h2 : Primrec (fun q : (Prm × ℕ) =>
        ((q.1.2.2 + 2, [], [q.2], q.1.2.2 + 2) : ℕ × List ℕ × List ℕ × ℕ)) :=
      Primrec.pair (Primrec.nat_add.comp hs (Primrec.const 2))
        (Primrec.pair (Primrec.const ([] : List ℕ))
          (Primrec.pair hbl (Primrec.nat_add.comp hs (Primrec.const 2))))
    have h3 : Primrec (fun q : (Prm × ℕ) =>
        ((q.1.2.2 + 3, [], [q.2], q.1.2.2 + 3) : ℕ × List ℕ × List ℕ × ℕ)) :=
      Primrec.pair (Primrec.nat_add.comp hs (Primrec.const 3))
        (Primrec.pair (Primrec.const ([] : List ℕ))
          (Primrec.pair hbl (Primrec.nat_add.comp hs (Primrec.const 3))))
    exact Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2
      (Primrec.list_cons.comp h3 (Primrec.const ([] : List Tr))))
  refine Primrec.of_eq ?_ (fun x => (compTrans_eq_flatMap x.1 x.2.1 x.2.2).symm)
  exact Primrec.list_append.comp
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) hbody1)
    (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd)) hlast)

/-- The bound on the letters of an instance is primitive recursive. -/
lemma primrec_bnd : Primrec bnd := by
  have hflat : Primrec (fun P : Instance => P.flatMap (fun p => p.1 ++ p.2)) := by
    refine Primrec.list_flatMap Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.1 ++ q.2.2
    exact Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec (fun P : Instance => (P.flatMap (fun p => p.1 ++ p.2)).foldr max 0) := by
    refine (Primrec.list_foldr (h := fun _ q => max q.1 q.2) hflat (Primrec.const 0) ?_).of_eq
      (fun _ => rfl)
    show Primrec fun q : Instance × (ℕ × ℕ) => max q.2.1 q.2.2
    exact Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.succ.comp hfold

/-- **The reduction is computable.** -/
lemma computable_reduction : Computable (fun P : Instance => (code1 P, code2 P)) := by
  have hfst : Primrec (fun P : Instance => P.map Prod.fst) := by
    refine Primrec.list_map Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.1
    exact Primrec.fst.comp Primrec.snd
  have hsnd : Primrec (fun P : Instance => P.map Prod.snd) := by
    refine Primrec.list_map Primrec.id ?_
    show Primrec fun q : Instance × (List ℕ × List ℕ) => q.2.2
    exact Primrec.snd.comp Primrec.snd
  have hc1a : Primrec (fun P : Instance => compTrans (P.map Prod.fst) (bnd P) 0) :=
    primrec_compTrans.comp (Primrec.pair hfst (Primrec.pair primrec_bnd (Primrec.const 0)))
  have hc1b : Primrec (fun P : Instance => compTrans (P.map Prod.snd) (bnd P) 4) :=
    primrec_compTrans.comp (Primrec.pair hsnd (Primrec.pair primrec_bnd (Primrec.const 4)))
  have hc1c : Primrec (fun P : Instance =>
      (List.range (bnd P)).map (fun b => ((8, [], [b], 8) : ℕ × List ℕ × List ℕ × ℕ))) := by
    refine Primrec.list_map (Primrec.list_range.comp primrec_bnd) ?_
    show Primrec fun q : Instance × ℕ => ((8, [], [q.2], 8) : ℕ × List ℕ × List ℕ × ℕ)
    exact Primrec.pair (Primrec.const 8) (Primrec.pair (Primrec.const ([] : List ℕ))
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ)))
        (Primrec.const 8)))
  have hcode1 : Primrec code1 :=
    Primrec.pair (Primrec.list_append.comp (Primrec.list_append.comp hc1a hc1b) hc1c)
      (Primrec.const ([0, 4, 8], [1, 2, 3, 5, 6, 7, 8]))
  have hc2a : Primrec (fun P : Instance =>
      (List.range P.length).map (fun i => ((0, [i], [], 0) : ℕ × List ℕ × List ℕ × ℕ))) := by
    refine Primrec.list_map (Primrec.list_range.comp Primrec.list_length) ?_
    show Primrec fun q : Instance × ℕ => ((0, [q.2], [], 0) : ℕ × List ℕ × List ℕ × ℕ)
    exact Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ)))
        (Primrec.pair (Primrec.const ([] : List ℕ)) (Primrec.const 0)))
  have hc2b : Primrec (fun P : Instance =>
      (List.range (bnd P)).map (fun b => ((0, [], [b], 0) : ℕ × List ℕ × List ℕ × ℕ))) := by
    refine Primrec.list_map (Primrec.list_range.comp primrec_bnd) ?_
    show Primrec fun q : Instance × ℕ => ((0, [], [q.2], 0) : ℕ × List ℕ × List ℕ × ℕ)
    exact Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const ([] : List ℕ))
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : List ℕ)))
        (Primrec.const 0)))
  have hcode2 : Primrec code2 :=
    Primrec.pair (Primrec.list_append.comp hc2a hc2b) (Primrec.const ([0], [0]))
  exact (Primrec.pair hcode1 hcode2).to_comp

/-! ## Theorem `thm:undecidable-equivalence-rational-relations` -/

/-- **Theorem `thm:undecidable-equivalence-rational-relations`.**  Assuming that the Post
correspondence problem is undecidable, the equivalence problem for rational relations is
undecidable. -/
theorem equivalence_undecidable (hPCP : ¬ ComputablePred Solvable) :
    ¬ ComputablePred (fun p : RelCode × RelCode => codeRel p.1 = codeRel p.2) := by
  rintro ⟨hdec, hcomp⟩
  set F : RelCode × RelCode → Bool := fun p => decide (codeRel p.1 = codeRel p.2) with hF
  have hFspec : ∀ p, F p = true ↔ codeRel p.1 = codeRel p.2 := by
    intro p; simp [hF]
  have hD : Computable (fun P : Instance => !F (code1 P, code2 P)) :=
    Primrec.not.to_comp.comp (hcomp.comp computable_reduction)
  refine hPCP ⟨fun P => Classical.propDecidable _, hD.of_eq (fun P => ?_)⟩
  by_cases h : Solvable P
  · have hfalse : F (code1 P, code2 P) = false := by
      by_contra hc
      exact (code_eq_iff P).1 ((hFspec _).1 (by simpa using hc)) h
    simp [h, hfalse]
  · have htrue : F (code1 P, code2 P) = true := (hFspec _).2 ((code_eq_iff P).2 h)
    simp [h, htrue]

end PCP

end Lax132576Proofs.Transducers
