/-
# From string rewriting to the Modified Post Correspondence Problem

This file contains the combinatorial heart of Sipser's proof of Theorem 5.15: the dominos
of parts 1–7 of the construction, in the general setting of a string rewriting system.

Given a rewriting system `S`, a start string `s` and a target string `t`, we build an
MPCP instance whose matches (starting with the first domino) correspond exactly to
derivations `s ⟶* t`.
-/
import Lax251941Proofs.Source.PCP.Rewriting

namespace Lax251941Proofs.PCP

variable {α : Type*}

/-- The MPCP instance associated with a string rewriting system `S`, a start string `s`
and a target string `t`.  The symbol `hash` is the separator `#` between successive
strings of a derivation, and `start` is the marker opening the derivation.

The dominos are, in order:
* `[start / start s #]` – Sipser's part 1;
* `[u / v]` for each rule `u → v` – Sipser's parts 2, 3 and 6;
* `[a / a]` for each letter `a` – Sipser's part 4;
* `[# / #]` and `[# / x #]` – Sipser's part 5;
* `[t # # / #]` – Sipser's part 7. -/
def mpcpOf (S : SRS α) (hash start : α) (s t : List α) : Inst α :=
  ([start], start :: (s ++ [hash]))
    :: (S.rules
        ++ S.alphabet.map (fun a => ([a], [a]))
        ++ [([hash], [hash])]
        ++ S.ext.map (fun x => ([hash], [x, hash]))
        ++ [(t ++ [hash, hash], [hash])])

/-- Well-formedness conditions for the reduction: the two auxiliary symbols `hash` and
`start` are distinct from each other and do not belong to the alphabet, and the start and
target strings are over the alphabet. -/
structure MpcpWF (S : SRS α) (hash start : α) (s t : List α) : Prop where
  wf : S.WF
  hash_not_mem : hash ∉ S.alphabet
  start_not_mem : start ∉ S.alphabet
  hash_ne_start : hash ≠ start
  s_sub : ∀ a ∈ s, a ∈ S.alphabet
  t_sub : ∀ a ∈ t, a ∈ S.alphabet

/-- Splitting off a `hash`-free prefix. -/
lemma prefix_split {hash : α} {u X A Y : List α} (h : u ++ X = A ++ hash :: Y)
    (hu : hash ∉ u) : ∃ A', A = u ++ A' ∧ X = A' ++ hash :: Y := by
  rcases List.append_eq_append_iff.mp h with ⟨a', hA, hX⟩ | ⟨c', hu', hd⟩
  · exact ⟨a', hA, hX⟩
  · cases c' with
    | nil => exact ⟨[], by simpa using hu'.symm, by simpa using hd.symm⟩
    | cons e c'' =>
      exfalso
      have : e = hash := (List.cons.injEq _ _ _ _ ▸ hd).1.symm
      subst this
      exact hu (by simp [hu'])

section Main

variable {S : SRS α} {hash start : α} {s t : List α}

/-- The key invariant of Sipser's construction, in the direction "a match yields a
derivation".

If `m` is a sequence of dominos of the instance whose top string equals
`A ++ [#] ++ B ++ (bottom string of m)` — i.e. the still-unmatched part of the bottom
string is `A # B`, where `A` is the unread rest of the current string of the derivation
and `B` is the part of the next string produced so far, obtained from the already-read
part `δ` of the current string — then the current string `δ ++ A` rewrites to `t`. -/
lemma mpcp_main (h : MpcpWF S hash start s t) :
    ∀ (m : List (Domino α)) (δ A B : List α),
      (∀ d ∈ m, d ∈ mpcpOf S hash start s t) →
      BodyRel S δ B → (∀ a ∈ A, a ∈ S.alphabet) →
      topStr m = (A ++ [hash] ++ B) ++ botStr m →
      Reaches S (δ ++ A) t := by
  intro m
  induction m with
  | nil =>
    intro δ A B _ _ _ heq
    exfalso
    simp only [topStr_nil, botStr_nil, List.append_nil] at heq
    have : hash ∈ ([] : List α) := by
      rw [heq]; simp
    simp at this
  | cons d m ih =>
    intro δ A B hmem hbody hA heq
    have hdmem : d ∈ mpcpOf S hash start s t := hmem d (by simp)
    have hmem' : ∀ e ∈ m, e ∈ mpcpOf S hash start s t := fun e he => hmem e (by simp [he])
    have hBalpha : ∀ a ∈ B, a ∈ S.alphabet := hbody.mem_alphabet h.wf
    simp only [topStr_cons, botStr_cons] at heq
    -- generic treatment of dominos whose top string avoids `hash` and is a prefix of `A`
    have step_rule : ∀ u v : List α, d = (u, v) → hash ∉ u →
        BodyRel S (δ ++ u) (B ++ v) → Reaches S (δ ++ A) t := by
      intro u v hduv hu hbody'
      subst hduv
      simp only at heq
      have heq' : u ++ topStr m = A ++ hash :: (B ++ (v ++ botStr m)) := by
        simpa [List.append_assoc] using heq
      obtain ⟨A', hAeq, hX⟩ := prefix_split heq' hu
      have hA' : ∀ a ∈ A', a ∈ S.alphabet := by
        intro a ha; exact hA a (by simp [hAeq, ha])
      have := ih (δ ++ u) A' (B ++ v) hmem' hbody' hA' (by
        simpa [List.append_assoc] using hX)
      simpa [hAeq, List.append_assoc] using this
    -- `A` must be empty when the domino's top string is `[hash]`
    have hash_case : d.1 = [hash] → A = [] ∧ topStr m = B ++ (d.2 ++ botStr m) := by
      intro hd1
      rw [hd1] at heq
      cases A with
      | nil => refine ⟨rfl, ?_⟩; simpa using heq
      | cons a A' =>
        exfalso
        have : hash = a := by
          have := congrArg (fun l => l.head?) heq
          simpa using this
        exact h.hash_not_mem (this ▸ hA a (by simp))
    simp only [mpcpOf, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false] at hdmem
    rcases hdmem with hd | (((hd | hd) | hd) | hd) | hd
    · -- part 1 domino, used again: impossible, `start` never occurs in `A`
      exfalso
      have hd1 : d.1 = [start] := by rw [hd]
      rw [hd1] at heq
      have heq' : [start] ++ topStr m = A ++ hash :: (B ++ (d.2 ++ botStr m)) := by
        simpa [List.append_assoc] using heq
      obtain ⟨A', hAeq, _⟩ := prefix_split heq' (by simpa using h.hash_ne_start)
      exact h.start_not_mem (hA start (by simp [hAeq]))
    · -- parts 2, 3, 6: a rule of the rewriting system
      obtain ⟨u, v⟩ := d
      exact step_rule u v rfl
        (fun hc => h.hash_not_mem (h.wf.rules_left_sub (u, v) hd hash hc))
        (hbody.rule hd)
    · -- part 4: copying a letter
      obtain ⟨a, ha, hda⟩ := hd
      refine step_rule [a] [a] hda.symm ?_ (hbody.copy ha)
      simp only [List.mem_singleton]
      rintro rfl
      exact h.hash_not_mem ha
    · -- part 5, first domino: the separator is copied, the next string is complete
      obtain ⟨hA0, hm⟩ := hash_case (by rw [hd])
      have hd2 : d.2 = [hash] := by rw [hd]
      rw [hd2] at hm
      have := ih [] B [] hmem' BodyRel.nil hBalpha (by simpa [List.append_assoc] using hm)
      simp only [List.nil_append] at this
      simpa [hA0] using (hbody.reaches.trans this)
    · -- part 5, second domino: a blank is appended to the next string
      obtain ⟨x, hx, hdx⟩ := hd
      obtain ⟨hA0, hm⟩ := hash_case (by rw [← hdx])
      have hd2 : d.2 = [x, hash] := by rw [← hdx]
      rw [hd2] at hm
      have hBx : ∀ a ∈ B ++ [x], a ∈ S.alphabet := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hBalpha a ha
        · simpa [List.mem_singleton.mp ha] using h.wf.ext_sub x hx
      have := ih [] (B ++ [x]) [] hmem' BodyRel.nil hBx (by
        simpa [List.append_assoc] using hm)
      simp only [List.nil_append] at this
      have hstep : Reaches S B (B ++ [x]) := Reaches.single (Step.ext hx)
      simpa [hA0] using (hbody.reaches.trans (hstep.trans this))
    · -- part 7: the final domino, the derivation has reached `t`
      have hd1 : d.1 = t ++ [hash, hash] := by rw [hd]
      have hd2 : d.2 = [hash] := by rw [hd]
      rw [hd1, hd2] at heq
      have heq' : t ++ (hash :: hash :: topStr m) = A ++ hash :: (B ++ (hash :: botStr m)) := by
        simpa [List.append_assoc] using heq
      obtain ⟨A', hAeq, hX⟩ :=
        prefix_split heq' (fun hc => h.hash_not_mem (h.t_sub hash hc))
      have hA' : ∀ a ∈ A', a ∈ S.alphabet := fun a ha => hA a (by simp [hAeq, ha])
      -- `A'` starts with `hash`, hence is empty
      have hA'nil : A' = [] := by
        cases A' with
        | nil => rfl
        | cons a A'' =>
          exfalso
          have : hash = a := by
            have := congrArg (fun l => l.head?) hX
            simpa using this
          exact h.hash_not_mem (this ▸ hA' a (by simp))
      subst hA'nil
      simp only [List.nil_append] at hX
      have hX' : hash :: topStr m = B ++ hash :: botStr m := by
        simpa using hX
      have hBnil : B = [] := by
        cases B with
        | nil => rfl
        | cons b B'' =>
          exfalso
          have : hash = b := by
            have := congrArg (fun l => l.head?) hX'
            simpa using this
          exact h.hash_not_mem (this ▸ hBalpha b (by simp))
      subst hBnil
      have hδ : δ = [] := hbody.eq_nil_of_nil h.wf
      subst hδ
      simp only [List.append_nil] at hAeq
      subst hAeq
      simpa using Reaches.refl S _

/-- A match of the MPCP instance beginning with the first domino yields a derivation. -/
lemma reaches_of_hasMatchFirst (h : MpcpWF S hash start s t)
    (hm : HasMatchFirst (mpcpOf S hash start s t)) : Reaches S s t := by
  obtain ⟨d, rest, hP, m, hmem, heq⟩ := hm
  have hd : d = ([start], start :: (s ++ [hash])) := by
    have h1 : (mpcpOf S hash start s t).head? = some d := by rw [hP]; simp
    have h2 : (mpcpOf S hash start s t).head? = some ([start], start :: (s ++ [hash])) := by
      simp [mpcpOf]
    exact (Option.some.inj (h2.symm.trans h1)).symm
  subst hd
  have hmem' : ∀ e ∈ m, e ∈ mpcpOf S hash start s t := by
    intro e he; exact hP ▸ hmem e he
  simp only [topStr_cons, botStr_cons] at heq
  have heq' : topStr m = (s ++ [hash] ++ []) ++ botStr m := by
    simpa [List.append_assoc] using heq
  simpa using mpcp_main h m [] s [] hmem' BodyRel.nil h.s_sub heq'

section Membership

variable (S hash start s t)

lemma mem_mpcpOf_first : ([start], start :: (s ++ [hash])) ∈ mpcpOf S hash start s t :=
  List.mem_cons_self

lemma mem_mpcpOf_rule {u v : List α} (h : (u, v) ∈ S.rules) :
    (u, v) ∈ mpcpOf S hash start s t :=
  List.mem_cons_of_mem _ <| List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_left _ <| List.mem_append_left _ h

lemma mem_mpcpOf_copy {a : α} (h : a ∈ S.alphabet) :
    ([a], [a]) ∈ mpcpOf S hash start s t :=
  List.mem_cons_of_mem _ <| List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_left _ <| List.mem_append_right _ (List.mem_map_of_mem h)

lemma mem_mpcpOf_hash : ([hash], [hash]) ∈ mpcpOf S hash start s t :=
  List.mem_cons_of_mem _ <| List.mem_append_left _ <| List.mem_append_left _ <|
    List.mem_append_right _ (by simp)

lemma mem_mpcpOf_ext {x : α} (h : x ∈ S.ext) :
    ([hash], [x, hash]) ∈ mpcpOf S hash start s t :=
  List.mem_cons_of_mem _ <| List.mem_append_left _ <| List.mem_append_right _
    (List.mem_map_of_mem h)

lemma mem_mpcpOf_final : (t ++ [hash, hash], [hash]) ∈ mpcpOf S hash start s t :=
  List.mem_cons_of_mem _ <| List.mem_append_right _ (by simp)

end Membership

/-- The dominos `[a / a]` copying a string letter by letter (Sipser's part 4). -/
def copyDominoes (X : List α) : List (Domino α) := X.map (fun a => ([a], [a]))

@[simp] lemma topStr_copyDominoes (X : List α) : topStr (copyDominoes X) = X := by
  induction X with
  | nil => rfl
  | cons a X ih => simpa [copyDominoes, topStr] using congrArg (fun l => a :: l) ih

@[simp] lemma botStr_copyDominoes (X : List α) : botStr (copyDominoes X) = X := by
  induction X with
  | nil => rfl
  | cons a X ih => simpa [copyDominoes, botStr] using congrArg (fun l => a :: l) ih

lemma mem_copyDominoes (X : List α) (hX : ∀ a ∈ X, a ∈ S.alphabet) :
    ∀ d ∈ copyDominoes X, d ∈ mpcpOf S hash start s t := by
  intro d hd
  simp only [copyDominoes, List.mem_map] at hd
  obtain ⟨a, ha, rfl⟩ := hd
  exact mem_mpcpOf_copy S hash start s t (hX a ha)

/-- Every single rewriting step can be simulated by a run of dominos taking the current
string (followed by the separator) on top to the next string (followed by the separator)
at the bottom. -/
lemma exists_dominoes_of_step {C C' : List α}
    (hC : ∀ a ∈ C, a ∈ S.alphabet) (hstep : Step S C C') :
    ∃ ds : List (Domino α), (∀ d ∈ ds, d ∈ mpcpOf S hash start s t) ∧
      topStr ds = C ++ [hash] ∧ botStr ds = C' ++ [hash] := by
  cases hstep with
  | rule hr =>
    cases hr with
    | mk l u v r hrule =>
      refine ⟨copyDominoes l ++ [(u, v)] ++ copyDominoes r ++ [([hash], [hash])], ?_, ?_, ?_⟩
      · intro d hd
        simp only [List.mem_append, List.mem_singleton] at hd
        rcases hd with ((hd | hd) | hd) | hd
        · exact mem_copyDominoes l (fun a ha => hC a (by simp [ha])) d hd
        · subst hd; exact mem_mpcpOf_rule S hash start s t hrule
        · exact mem_copyDominoes r (fun a ha => hC a (by simp [ha])) d hd
        · subst hd; exact mem_mpcpOf_hash S hash start s t
      · simp [List.append_assoc]
      · simp [List.append_assoc]
  | @ext x hx =>
    refine ⟨copyDominoes C ++ [([hash], [x, hash])], ?_, ?_, ?_⟩
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact mem_copyDominoes C hC d hd
      · subst hd; exact mem_mpcpOf_ext S hash start s t hx
    · simp
    · simp [List.append_assoc]

/-- The partial matches of Sipser's construction: after simulating a derivation `s ⟶* C`,
the bottom string exceeds the top string exactly by `C #`. -/
lemma exists_partial_match (h : MpcpWF S hash start s t) {C : List α}
    (hreach : Reaches S s C) :
    ∃ m : List (Domino α), (∀ d ∈ m, d ∈ mpcpOf S hash start s t) ∧
      s ++ [hash] ++ botStr m = topStr m ++ (C ++ [hash]) := by
  induction hreach with
  | refl => exact ⟨[], by simp, by simp⟩
  | @tail C C' hreach hstep ih =>
    obtain ⟨m, hmem, heq⟩ := ih
    have hC : ∀ a ∈ C, a ∈ S.alphabet := Reaches.mem_alphabet h.wf hreach h.s_sub
    obtain ⟨ds, hds, hdtop, hdbot⟩ := exists_dominoes_of_step (S := S) (hash := hash) (start := start) (s := s) (t := t) hC hstep
    refine ⟨m ++ ds, ?_, ?_⟩
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hmem d hd
      · exact hds d hd
    · have e1 : s ++ [hash] ++ botStr (m ++ ds)
          = (s ++ [hash] ++ botStr m) ++ botStr ds := by
        simp
      rw [e1, heq, hdbot, topStr_append, hdtop]

/-- A derivation yields a match of the MPCP instance beginning with the first domino. -/
lemma hasMatchFirst_of_reaches (h : MpcpWF S hash start s t) (hreach : Reaches S s t) :
    HasMatchFirst (mpcpOf S hash start s t) := by
  obtain ⟨m, hmem, heq⟩ := exists_partial_match (S := S) (hash := hash) (start := start) (s := s) (t := t) h hreach
  refine ⟨([start], start :: (s ++ [hash])), _, rfl, m ++ [(t ++ [hash, hash], [hash])], ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hmem e he
    · rw [List.mem_singleton.mp he]; exact mem_mpcpOf_final S hash start s t
  · have e1 : topStr (([start], start :: (s ++ [hash])) :: (m ++ [(t ++ [hash, hash], [hash])]))
        = [start] ++ (topStr m ++ (t ++ [hash, hash])) := by
      simp
    have e2 : botStr (([start], start :: (s ++ [hash])) :: (m ++ [(t ++ [hash, hash], [hash])]))
        = [start] ++ ((s ++ [hash] ++ botStr m) ++ [hash]) := by
      simp [List.append_assoc]
    rw [e1, e2, heq]
    simp

/-- Every letter occurring in the MPCP instance is a letter of the alphabet, or one of the
two auxiliary symbols. -/
lemma mem_symbols_of_mem_mpcpOf (h : MpcpWF S hash start s t) {d : Domino α}
    (hd : d ∈ mpcpOf S hash start s t) :
    (∀ a ∈ d.1, a ∈ S.alphabet ∨ a = hash ∨ a = start) ∧
      (∀ a ∈ d.2, a ∈ S.alphabet ∨ a = hash ∨ a = start) := by
  simp only [mpcpOf, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hd
  rcases hd with hd | (((hd | hd) | hd) | hd) | hd
  · subst hd
    constructor
    · intro a ha; simp only [List.mem_singleton] at ha; exact Or.inr (Or.inr ha)
    · intro a ha
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | ha | ha
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (h.s_sub a ha)
      · exact Or.inr (Or.inl ha)
  · obtain ⟨u, v⟩ := d
    exact ⟨fun a ha => Or.inl (h.wf.rules_left_sub (u, v) hd a ha),
      fun a ha => Or.inl (h.wf.rules_right_sub (u, v) hd a ha)⟩
  · obtain ⟨a, ha, rfl⟩ := hd
    exact ⟨fun b hb => Or.inl (by simpa [List.mem_singleton.mp hb] using ha),
      fun b hb => Or.inl (by simpa [List.mem_singleton.mp hb] using ha)⟩
  · subst hd
    exact ⟨fun a ha => Or.inr (Or.inl (by simpa using ha)),
      fun a ha => Or.inr (Or.inl (by simpa using ha))⟩
  · obtain ⟨x, hx, rfl⟩ := hd
    refine ⟨fun a ha => Or.inr (Or.inl (by simpa using ha)), fun a ha => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Or.inl (h.wf.ext_sub _ hx)
    · exact Or.inr (Or.inl rfl)
  · subst hd
    refine ⟨fun a ha => ?_, fun a ha => Or.inr (Or.inl (by simpa using ha))⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact Or.inl (h.t_sub a ha)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)

/-- All dominos of the MPCP instance carry nonempty strings. -/
lemma ne_nil_of_mem_mpcpOf (h : MpcpWF S hash start s t) {d : Domino α}
    (hd : d ∈ mpcpOf S hash start s t) : d.1 ≠ [] ∧ d.2 ≠ [] := by
  simp only [mpcpOf, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hd
  rcases hd with hd | (((hd | hd) | hd) | hd) | hd
  · subst hd; simp
  · obtain ⟨u, v⟩ := d
    exact ⟨h.wf.rules_left_ne (u, v) hd, h.wf.rules_right_ne (u, v) hd⟩
  · obtain ⟨a, -, rfl⟩ := hd; simp
  · subst hd; simp
  · obtain ⟨x, -, rfl⟩ := hd; simp
  · subst hd; simp

/-- **The reduction from string rewriting to MPCP.**  The MPCP instance `mpcpOf S # ⋆ s t`
has a match beginning with its first domino if and only if `s` rewrites to `t`.  This is
the content of parts 1–7 of Sipser's construction in the proof of Theorem 5.15. -/
theorem hasMatchFirst_mpcpOf_iff (h : MpcpWF S hash start s t) :
    HasMatchFirst (mpcpOf S hash start s t) ↔ Reaches S s t :=
  ⟨reaches_of_hasMatchFirst h, hasMatchFirst_of_reaches h⟩

end Main

end Lax251941Proofs.PCP
