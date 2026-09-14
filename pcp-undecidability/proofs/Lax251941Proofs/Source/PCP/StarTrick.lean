/-
# From MPCP to PCP: Sipser's `⋆` trick

The last part of the proof of Sipser's Theorem 5.15 converts an instance `P'` of the
Modified Post Correspondence Problem (where a match is required to begin with the first
domino) into an instance `P` of the plain Post Correspondence Problem.

Following Sipser we write, for a string `u = u₁ ⋯ uₙ`,
`⋆u = ∗u₁∗u₂ ⋯ ∗uₙ` and `u⋆ = u₁∗u₂∗ ⋯ uₙ∗`, and the instance `P` consists of

* `[⋆t₁ / ⋆b₁⋆]`,
* `[⋆tᵢ / bᵢ⋆]` for every domino `[tᵢ / bᵢ]` of `P'`,
* `[∗◇ / ◇]`.

Because the interleaved `∗`s can be matched only in one way, the only domino that can
begin a match of `P` is the first one, and matches of `P` correspond to matches of `P'`
beginning with the first domino.
-/
import Lax251941Proofs.Source.PCP.Basic

namespace Lax251941Proofs.PCP

variable {α : Type*}

section Star

variable (star : α)

/-- `⋆u = ∗u₁∗u₂ ⋯ ∗uₙ`: insert the symbol `∗` before every letter. -/
def starTop : List α → List α
  | [] => []
  | a :: u => star :: a :: starTop u

/-- `u⋆ = u₁∗u₂∗ ⋯ uₙ∗`: insert the symbol `∗` after every letter. -/
def starBot : List α → List α
  | [] => []
  | a :: u => a :: star :: starBot u

@[simp] lemma starTop_nil : starTop star ([] : List α) = [] := rfl
@[simp] lemma starBot_nil : starBot star ([] : List α) = [] := rfl

@[simp] lemma starTop_cons (a : α) (u : List α) :
    starTop star (a :: u) = star :: a :: starTop star u := rfl

@[simp] lemma starBot_cons (a : α) (u : List α) :
    starBot star (a :: u) = a :: star :: starBot star u := rfl

@[simp] lemma starTop_append (u v : List α) :
    starTop star (u ++ v) = starTop star u ++ starTop star v := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih]

@[simp] lemma starBot_append (u v : List α) :
    starBot star (u ++ v) = starBot star u ++ starBot star v := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih]

/-- `∗u⋆ = ⋆u∗`: the two ways of adding the extra `∗` agree. -/
lemma star_cons_starBot (u : List α) : star :: starBot star u = starTop star u ++ [star] := by
  induction u with
  | nil => simp
  | cons a u ih => simp [← ih]

/-- Splitting a `⋆`-string along a `⋆`-prefix. -/
lemma starTop_split {Z u R : List α} (h : starTop star Z = starTop star u ++ R) :
    ∃ Z', Z = u ++ Z' ∧ R = starTop star Z' := by
  induction u generalizing Z with
  | nil => exact ⟨Z, by simp, by simpa using h.symm⟩
  | cons a u ih =>
    cases Z with
    | nil => simp at h
    | cons z Z₁ =>
      simp only [starTop_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨-, hz, h'⟩ := h
      obtain ⟨Z', hZ', hR⟩ := ih h'
      exact ⟨Z', by simp [hz, hZ'], hR⟩

end Star

section Construction

variable [DecidableEq α] (star diamond : α)

/-- The PCP instance obtained from an MPCP instance by Sipser's `⋆` trick. -/
def pcpOfMpcp (P : Inst α) : Inst α :=
  match P with
  | [] => []
  | d :: rest =>
      (starTop star d.1, star :: starBot star d.2)
        :: ((d :: rest).map fun e => (starTop star e.1, starBot star e.2))
        ++ [([star, diamond], [diamond])]

/-- Deleting all occurrences of the symbol `◇`. -/
def eraseDiamond (l : List α) : List α := l.filter (fun a => a ≠ diamond)

@[simp] lemma eraseDiamond_nil : eraseDiamond diamond ([] : List α) = [] := rfl

@[simp] lemma eraseDiamond_append (u v : List α) :
    eraseDiamond diamond (u ++ v) = eraseDiamond diamond u ++ eraseDiamond diamond v := by
  simp [eraseDiamond, List.filter_append]

lemma eraseDiamond_eq_self {u : List α} (h : diamond ∉ u) :
    eraseDiamond diamond u = u := by
  refine List.filter_eq_self.mpr ?_
  intro a ha
  simp only [ne_eq, decide_eq_true_eq]
  rintro rfl
  exact h ha

@[simp] lemma eraseDiamond_cons_self (u : List α) :
    eraseDiamond diamond (diamond :: u) = eraseDiamond diamond u := by
  simp [eraseDiamond]

/-- The state of the analysis of a match of `pcpOfMpcp`: after an even number of symbols
has been read from the bottom, the rest of the string is `⋆Z`; after an odd number, it is
`⋆Z` with its leading `∗` removed. -/
def phaseStr (star : α) : Bool → List α → List α
  | false, Z => starTop star Z
  | true, [] => []
  | true, a :: Z => a :: starTop star Z

variable (P : Inst α)

/-- `UnderList ms ns` relates a sequence `ms` of dominos of the PCP instance
`pcpOfMpcp star diamond P` with the corresponding sequence `ns` of dominos of the MPCP
instance `P`: the `◇` domino has no counterpart, and the two copies of a domino of `P`
(the first, `⋆`-decorated one and the ordinary one) both correspond to that domino. -/
inductive UnderList (star diamond : α) : Inst α → List (Domino α) → List (Domino α) → Prop
  | nil {P : Inst α} : UnderList star diamond P [] []
  | special {d : Domino α} {rest : Inst α} {ms ns : List (Domino α)} :
      UnderList star diamond (d :: rest) ms ns →
      UnderList star diamond (d :: rest)
        ((starTop star d.1, star :: starBot star d.2) :: ms) (d :: ns)
  | copy {P : Inst α} {e : Domino α} {ms ns : List (Domino α)} : e ∈ P →
      UnderList star diamond P ms ns →
      UnderList star diamond P ((starTop star e.1, starBot star e.2) :: ms) (e :: ns)
  | diamond {P : Inst α} {ms ns : List (Domino α)} :
      UnderList star diamond P ms ns →
      UnderList star diamond P (([star, diamond], [diamond]) :: ms) ns

omit [DecidableEq α] in
/-- Every sequence of dominos of `pcpOfMpcp star diamond P` has an underlying sequence of
dominos of `P`. -/
lemma exists_underList {P : Inst α} {ms : List (Domino α)}
    (hms : ∀ d ∈ ms, d ∈ pcpOfMpcp star diamond P) :
    ∃ ns, UnderList star diamond P ms ns := by
  induction ms with
  | nil => exact ⟨[], UnderList.nil⟩
  | cons d ms ih =>
    obtain ⟨ns, hns⟩ := ih fun e he => hms e (by simp [he])
    have hd := hms d (by simp)
    cases hP : P with
    | nil => rw [hP, pcpOfMpcp] at hd; simp at hd
    | cons d1 rest =>
      rw [hP] at hd hns
      simp only [pcpOfMpcp, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false] at hd
      rcases hd with (hd | hd) | hd
      · exact ⟨d1 :: ns, by rw [hd]; exact UnderList.special hns⟩
      · obtain ⟨e, he, hde⟩ := hd
        exact ⟨e :: ns, by rw [← hde]; exact UnderList.copy (List.mem_cons.mpr he) hns⟩
      · exact ⟨ns, by rw [hd]; exact UnderList.diamond hns⟩

omit [DecidableEq α] in
lemma UnderList.mem_of_mem {P : Inst α} {ms ns : List (Domino α)}
    (h : UnderList star diamond P ms ns) : ∀ e ∈ ns, e ∈ P := by
  induction h with
  | nil => simp
  | special _ ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · exact he ▸ List.mem_cons_self
    · exact ih e he
  | copy hmem _ ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · exact he ▸ hmem
    · exact ih e he
  | diamond _ ih => exact ih

/-- The top string of a sequence of dominos of the PCP instance is `⋆X`, where `X` is the
top string of the underlying sequence with a `◇` inserted for each `◇` domino. -/
lemma UnderList.top {P : Inst α} {ms ns : List (Domino α)}
    (hstar : ∀ d ∈ P, star ∉ d.1) (hdia : ∀ d ∈ P, diamond ∉ d.1)
    (hsd : star ≠ diamond) (h : UnderList star diamond P ms ns) :
    ∃ X, topStr ms = starTop star X ∧ topStr ns = eraseDiamond diamond X ∧ star ∉ X := by
  induction h with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | @special d rest ms ns _ ih =>
    obtain ⟨X, h1, h2, h3⟩ := ih hstar hdia
    refine ⟨d.1 ++ X, by simp [h1], ?_, ?_⟩
    · simp only [topStr_cons, h2, eraseDiamond_append,
        eraseDiamond_eq_self diamond (hdia d List.mem_cons_self)]
    · intro hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hstar d List.mem_cons_self hc
      · exact h3 hc
  | @copy P e ms ns hmem _ ih =>
    obtain ⟨X, h1, h2, h3⟩ := ih hstar hdia
    refine ⟨e.1 ++ X, by simp [h1], ?_, ?_⟩
    · simp only [topStr_cons, h2, eraseDiamond_append,
        eraseDiamond_eq_self diamond (hdia e hmem)]
    · intro hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hstar e hmem hc
      · exact h3 hc
  | @diamond P ms ns _ ih =>
    obtain ⟨X, h1, h2, h3⟩ := ih hstar hdia
    refine ⟨diamond :: X, by simp [h1], by simp [h2], ?_⟩
    intro hc
    rcases List.mem_cons.mp hc with hc | hc
    · exact hsd hc
    · exact h3 hc

/-- The heart of the analysis: reading the bottom strings of a match of the PCP instance
against the string `⋆Z` forces the underlying dominos to reproduce `Z` (with the `◇`s
deleted), and a match can only start with the first, `⋆`-decorated domino. -/
lemma UnderList.bot {P : Inst α} {ms ns : List (Domino α)}
    (hstar : ∀ d ∈ P, star ∉ d.2) (hdia : ∀ d ∈ P, diamond ∉ d.2)
    (hne : ∀ d ∈ P, d.2 ≠ []) (hsd : star ≠ diamond)
    (h : UnderList star diamond P ms ns) :
    ∀ (b : Bool) (Z : List α), star ∉ Z → botStr ms = phaseStr star b Z →
      botStr ns = eraseDiamond diamond Z ∧
        (b = false → ms ≠ [] → ∃ d rest ns', P = d :: rest ∧ ns = d :: ns') := by
  induction h with
  | nil =>
    intro b Z _ hZ
    simp only [botStr_nil] at hZ
    have hZnil : eraseDiamond diamond Z = [] := by
      cases b with
      | false =>
        cases Z with
        | nil => simp
        | cons z Z => simp [phaseStr] at hZ
      | true =>
        cases Z with
        | nil => simp
        | cons z Z => simp [phaseStr] at hZ
    exact ⟨by simp [hZnil], fun _ hc => absurd rfl hc⟩
  | @special d rest ms ns _ ih =>
    intro b Z hZ hbot
    have hd2 : diamond ∉ d.2 := hdia d List.mem_cons_self
    cases b with
    | true =>
      -- impossible: the decorated domino starts with `∗`, the string does not
      exfalso
      cases Z with
      | nil => simp [phaseStr] at hbot
      | cons z Z' =>
        simp only [botStr_cons, phaseStr, List.cons_append, List.cons.injEq] at hbot
        exact hZ (by simp [hbot.1])
    | false =>
      simp only [botStr_cons, phaseStr] at hbot
      have hbot' : starTop star Z = starTop star d.2 ++ (star :: botStr ms) := by
        rw [← hbot]
        simp [star_cons_starBot]
      obtain ⟨Z', hZeq, hR⟩ := starTop_split star hbot'
      cases Z' with
      | nil => simp at hR
      | cons z Z'' =>
        have hms : botStr ms = phaseStr star true (z :: Z'') := by
          simp only [starTop_cons, List.cons.injEq] at hR
          simp [phaseStr, hR.2]
        have hZ' : star ∉ z :: Z'' := fun hc => hZ (by rw [hZeq]; exact List.mem_append_right _ hc)
        obtain ⟨hbotns, -⟩ := ih hstar hdia hne true (z :: Z'') hZ' hms
        refine ⟨?_, fun _ _ => ⟨d, rest, ns, rfl, rfl⟩⟩
        rw [botStr_cons, hbotns, hZeq]
        simp [eraseDiamond_eq_self diamond hd2]
  | @copy P e ms ns hmem _ ih =>
    intro b Z hZ hbot
    have he2 : diamond ∉ e.2 := hdia e hmem
    have hestar : star ∉ e.2 := hstar e hmem
    obtain ⟨a, l, h2⟩ : ∃ a l, e.2 = a :: l := by
      cases h2 : e.2 with
      | nil => exact absurd h2 (hne e hmem)
      | cons a l => exact ⟨a, l, rfl⟩
    have ha : a ≠ star := fun hc => hestar (by rw [h2, hc]; simp)
    cases b with
    | false =>
      exfalso
      cases Z with
      | nil => rw [botStr_cons, h2] at hbot; simp [phaseStr] at hbot
      | cons z Z' =>
        rw [botStr_cons, h2] at hbot
        simp only [starBot_cons, phaseStr, starTop_cons, List.cons_append,
          List.cons.injEq] at hbot
        exact ha hbot.1
    | true =>
      cases Z with
      | nil => exfalso; rw [botStr_cons, h2] at hbot; simp [phaseStr] at hbot
      | cons z Z' =>
        rw [botStr_cons, h2] at hbot
        simp only [starBot_cons, phaseStr, List.cons_append, List.cons.injEq] at hbot
        obtain ⟨haz, hrest⟩ := hbot
        have hrest' : starTop star Z' = starTop star l ++ (star :: botStr ms) := by
          rw [← hrest, ← List.cons_append, star_cons_starBot]
          simp
        obtain ⟨Z₂, hZeq, hR⟩ := starTop_split star hrest'
        cases Z₂ with
        | nil => simp at hR
        | cons z₂ Z₃ =>
          have hms : botStr ms = phaseStr star true (z₂ :: Z₃) := by
            simp only [starTop_cons, List.cons.injEq] at hR
            simp [phaseStr, hR.2]
          have hZ₂ : star ∉ z₂ :: Z₃ := by
            intro hc
            exact hZ (List.mem_cons_of_mem _ (by rw [hZeq]; exact List.mem_append_right _ hc))
          obtain ⟨hbotns, -⟩ := ih hstar hdia hne true (z₂ :: Z₃) hZ₂ hms
          refine ⟨?_, fun hb => absurd hb (by simp)⟩
          have hself : eraseDiamond diamond (a :: l) = a :: l :=
            eraseDiamond_eq_self diamond (by rw [← h2]; exact he2)
          rw [botStr_cons, hbotns, h2, ← haz, hZeq]
          calc (a :: l) ++ eraseDiamond diamond (z₂ :: Z₃)
              = eraseDiamond diamond (a :: l) ++ eraseDiamond diamond (z₂ :: Z₃) := by
                rw [hself]
            _ = eraseDiamond diamond ((a :: l) ++ (z₂ :: Z₃)) := by
                rw [eraseDiamond_append]
            _ = eraseDiamond diamond (a :: (l ++ (z₂ :: Z₃))) := by simp
  | @diamond P ms ns _ ih =>
    intro b Z hZ hbot
    cases b with
    | false =>
      exfalso
      cases Z with
      | nil => simp [phaseStr] at hbot
      | cons z Z' =>
        simp only [phaseStr, starTop_cons, botStr_cons, List.cons_append,
          List.cons.injEq] at hbot
        exact hsd hbot.1.symm
    | true =>
      cases Z with
      | nil => simp [phaseStr] at hbot
      | cons z Z' =>
        simp only [phaseStr, botStr_cons, List.cons_append, List.cons.injEq] at hbot
        obtain ⟨hzd, hms⟩ := hbot
        have hZ' : star ∉ Z' := fun hc => hZ (List.mem_cons_of_mem _ hc)
        obtain ⟨hbotns, -⟩ := ih hstar hdia hne false Z' hZ' (by simpa [phaseStr] using hms)
        refine ⟨?_, fun hb => absurd hb (by simp)⟩
        rw [hbotns, ← hzd]
        simp

/-- Hypotheses on an MPCP instance under which Sipser's `⋆` trick works: the auxiliary
symbols `∗` and `◇` are distinct and occur in no domino, and all strings are nonempty. -/
structure StarWF (star diamond : α) (P : Inst α) : Prop where
  star_ne_diamond : star ≠ diamond
  star_not_top : ∀ d ∈ P, star ∉ d.1
  star_not_bot : ∀ d ∈ P, star ∉ d.2
  diamond_not_top : ∀ d ∈ P, diamond ∉ d.1
  diamond_not_bot : ∀ d ∈ P, diamond ∉ d.2
  top_ne_nil : ∀ d ∈ P, d.1 ≠ []
  bot_ne_nil : ∀ d ∈ P, d.2 ≠ []

variable {star diamond}

/-- A match of the starred PCP instance yields a match of the MPCP instance that begins
with the first domino. -/
lemma hasMatchFirst_of_hasMatch {P : Inst α} (hWF : StarWF star diamond P)
    (h : HasMatch (pcpOfMpcp star diamond P)) : HasMatchFirst P := by
  obtain ⟨ms, hne, hmem, heq⟩ := h
  obtain ⟨ns, hu⟩ := exists_underList star diamond hmem
  obtain ⟨X, hX1, hX2, hX3⟩ :=
    UnderList.top star diamond hWF.star_not_top hWF.diamond_not_top hWF.star_ne_diamond hu
  have hbot : botStr ms = phaseStr star false X := by
    rw [← heq, hX1]; rfl
  obtain ⟨hbotns, hfirst⟩ :=
    UnderList.bot star diamond hWF.star_not_bot hWF.diamond_not_bot hWF.bot_ne_nil
      hWF.star_ne_diamond hu false X hX3 hbot
  obtain ⟨d, rest, ns', hP, hns⟩ := hfirst rfl hne
  refine ⟨d, rest, hP, ns', ?_, ?_⟩
  · intro e he
    exact UnderList.mem_of_mem star diamond hu e (by rw [hns]; exact List.mem_cons_of_mem _ he)
  · rw [← hns, hX2, hbotns]

omit [DecidableEq α] in
/-- A match of the MPCP instance beginning with the first domino yields a match of the
starred PCP instance. -/
lemma hasMatch_of_hasMatchFirst {P : Inst α}
    (h : HasMatchFirst P) : HasMatch (pcpOfMpcp star diamond P) := by
  obtain ⟨d, rest, hP, ns, hmem, heq⟩ := h
  subst hP
  refine ⟨(starTop star d.1, star :: starBot star d.2)
      :: (ns.map fun e => (starTop star e.1, starBot star e.2))
      ++ [([star, diamond], [diamond])], by simp, ?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at he
    rcases he with (he | he) | he
    · exact he ▸ List.mem_cons_self
    · obtain ⟨f, hf, hfe⟩ := he
      refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
      exact hfe ▸ List.mem_map_of_mem (hmem f hf)
    · exact he ▸ List.mem_cons_of_mem _ (List.mem_append_right _ (by simp))
  · -- the top and bottom strings of the starred match both equal `⋆(t₁ ⋯ tₖ)∗◇`
    have htop : ∀ ms : List (Domino α),
        topStr (ms.map fun e => (starTop star e.1, starBot star e.2))
          = starTop star (topStr ms) := by
      intro ms
      induction ms with
      | nil => simp
      | cons a ms ih => simp [ih]
    have hbot : ∀ ms : List (Domino α),
        botStr (ms.map fun e => (starTop star e.1, starBot star e.2))
          = starBot star (botStr ms) := by
      intro ms
      induction ms with
      | nil => simp
      | cons a ms ih => simp [ih]
    have heq' : d.1 ++ topStr ns = d.2 ++ botStr ns := by simpa using heq
    have hL : topStr ((starTop star d.1, star :: starBot star d.2)
          :: (ns.map fun e => (starTop star e.1, starBot star e.2))
          ++ [([star, diamond], [diamond])])
        = starTop star (d.1 ++ topStr ns) ++ [star, diamond] := by
      simp [htop, List.append_assoc]
    have hR : botStr ((starTop star d.1, star :: starBot star d.2)
          :: (ns.map fun e => (starTop star e.1, starBot star e.2))
          ++ [([star, diamond], [diamond])])
        = starTop star (d.2 ++ botStr ns) ++ [star, diamond] := by
      have h1 : botStr ((starTop star d.1, star :: starBot star d.2)
          :: (ns.map fun e => (starTop star e.1, starBot star e.2))
          ++ [([star, diamond], [diamond])])
          = (star :: starBot star (d.2 ++ botStr ns)) ++ [diamond] := by
        simp [hbot, List.append_assoc]
      rw [h1, star_cons_starBot]
      simp
    rw [hL, hR, heq']

/-- **Sipser's `⋆` trick.**  The PCP instance `pcpOfMpcp ∗ ◇ P` has a match if and only if
the MPCP instance `P` has a match beginning with its first domino. -/
theorem hasMatch_pcpOfMpcp_iff {P : Inst α} (hWF : StarWF star diamond P) :
    HasMatch (pcpOfMpcp star diamond P) ↔ HasMatchFirst P :=
  ⟨hasMatchFirst_of_hasMatch hWF, hasMatch_of_hasMatchFirst⟩

end Construction

end Lax251941Proofs.PCP
