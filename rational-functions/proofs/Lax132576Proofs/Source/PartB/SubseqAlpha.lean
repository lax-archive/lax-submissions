/-
The non-branching part of a continuous function with bounded variation
(the first half of the proof of Theorem `thm:subsequential-functions`).

Let `f : A* → B*` be a partial function which is continuous and has bounded
variation.  Continuity makes the domain of `f` regular, so that every string
that can be extended into the domain can be extended by a *short* string
(`exists_short_extension`), and bounded variation is uniform over the extensions
of bounded length (`exists_uniform_bv`).  The data of `f` together with the two
constants obtained this way is bundled in the structure `Subseq.Data`.

For such a datum, `alpha D w` is the longest common prefix of the outputs of the
short extensions of `w`; this is the *non-branching part* of the book.  Its main
property is the delay bound: the output of every short extension of `w` exceeds
`alpha D w` by a bounded number of letters.
-/
import Lax132576Proofs.Source.PartB.SubseqDef
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Subseq

variable {A B : Type}

/-! ## The domain and its prefixes -/

/-- The domain of a partial function. -/
def Dom (f : List A → Option (List B)) : Language A := {w | (f w).isSome}

/-- The strings that can be extended to a string in the domain. -/
def Pre (f : List A → Option (List B)) : Language A := {w | ∃ v, (f (w ++ v)).isSome}

lemma mem_pre_of_mem_dom {f : List A → Option (List B)} {w : List A} (h : w ∈ Dom f) :
    w ∈ Pre f := ⟨[], by simpa using h⟩

lemma mem_pre_of_append {f : List A → Option (List B)} {w v : List A} (h : w ++ v ∈ Pre f) :
    w ∈ Pre f := by
  obtain ⟨u, hu⟩ := h
  exact ⟨v ++ u, by simpa [List.append_assoc] using hu⟩

lemma isRegular_univ (B : Type) : Language.IsRegular (Set.univ : Language B) := by
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), Set.univ⟩, ?_⟩
  ext w
  simp [DFA.accepts, DFA.acceptsFrom]

lemma dom_isRegular [Finite A] [Finite B] {f : List A → Option (List B)}
    (hcont : PartialContinuous f) : (Dom f).IsRegular := by
  have h := hcont (Set.univ : Language B) (isRegular_univ B)
  have heq : {w : List A | ∃ v, f w = some v ∧ v ∈ (Set.univ : Language B)} = Dom f := by
    ext w
    simp only [Set.mem_setOf_eq, Dom, Set.mem_univ, and_true, Option.isSome_iff_exists]
  exact heq ▸ h

/-- In a dfa with finitely many states, an accepted string can be replaced by a
short one. -/
lemma dfa_exists_short_accepted {σ : Type} [Fintype σ] (M : DFA A σ) (q : σ) (v : List A)
    (hv : M.evalFrom q v ∈ M.accept) :
    ∃ v' : List A, v'.length ≤ Fintype.card σ ∧ M.evalFrom q v' ∈ M.accept := by
  induction hn : v.length using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    subst hn
    by_cases hle : v.length ≤ Fintype.card σ
    · exact ⟨v, hle, hv⟩
    · push_neg at hle
      have hcard : Fintype.card σ < Fintype.card (Fin (v.length + 1)) := by
        simpa using Nat.lt_succ_of_lt hle
      obtain ⟨i, j, hij, hst⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (v.length + 1) =>
          M.evalFrom q (v.take i.val)) hcard
      have key : ∀ i j : Fin (v.length + 1), i.val < j.val →
          M.evalFrom q (v.take i.val) = M.evalFrom q (v.take j.val) →
          ∃ v' : List A, v'.length ≤ Fintype.card σ ∧ M.evalFrom q v' ∈ M.accept := by
        intro i j hlt hstij
        have hjle : j.val ≤ v.length := by omega
        have hlen : (v.take i.val ++ v.drop j.val).length < v.length := by
          simp only [List.length_append, List.length_take, List.length_drop]
          omega
        have hacc : M.evalFrom q (v.take i.val ++ v.drop j.val) ∈ M.accept := by
          rw [DFA.evalFrom_of_append, hstij, ← DFA.evalFrom_of_append, List.take_append_drop]
          exact hv
        exact ih _ hlen _ hacc rfl
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact key i j hlt hst
      · exact key j i hlt hst.symm

/-- If a string can be extended into the domain, then it can be extended by a
string of bounded length. -/
lemma exists_short_extension [Finite A] [Finite B] {f : List A → Option (List B)}
    (hcont : PartialContinuous f) :
    ∃ k : ℕ, ∀ w : List A, w ∈ Pre f → ∃ v : List A, v.length ≤ k ∧ (f (w ++ v)).isSome := by
  classical
  obtain ⟨σ, hσ, M, hM⟩ := dom_isRegular hcont
  haveI : Fintype σ := Fintype.ofFinite σ
  refine ⟨Fintype.card σ, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ := hw
  have hmem : M.evalFrom (M.evalFrom M.start w) v ∈ M.accept := by
    rw [← DFA.evalFrom_of_append]
    have : w ++ v ∈ M.accepts := by rw [hM]; exact hv
    exact this
  obtain ⟨v', hlen, hv'⟩ := dfa_exists_short_accepted M (M.evalFrom M.start w) v hmem
  refine ⟨v', hlen, ?_⟩
  have hacc : w ++ v' ∈ M.accepts := by
    show M.evalFrom M.start (w ++ v') ∈ M.accept
    rw [DFA.evalFrom_of_append]
    exact hv'
  rw [hM] at hacc
  exact hacc

/-- Bounded variation is uniform over the extensions of bounded length, because
there are finitely many of them. -/
lemma exists_uniform_bv [Finite A] {f : List A → Option (List B)}
    (hbv : BoundedVariation f) (c : ℕ) :
    ∃ K : ℕ, ∀ (w u₁ u₂ : List A) (x₁ x₂ : List B), u₁.length ≤ c → u₂.length ≤ c →
      f (w ++ u₁) = some x₁ → f (w ++ u₂) = some x₂ → leftDist x₁ x₂ ≤ K := by
  classical
  haveI : Finite {u : List A // u.length ≤ c} := (List.finite_length_le A c).to_subtype
  haveI : Fintype {u : List A // u.length ≤ c} := Fintype.ofFinite _
  choose Kf hKf using fun p : {u : List A // u.length ≤ c} × {u : List A // u.length ≤ c} =>
    hbv p.1.val p.2.val
  refine ⟨Finset.univ.sup Kf, fun w u₁ u₂ x₁ x₂ h₁ h₂ hx₁ hx₂ => ?_⟩
  have hb := hKf (⟨u₁, h₁⟩, ⟨u₂, h₂⟩) w x₁ x₂ hx₁ hx₂
  exact le_trans hb (Finset.le_sup (f := Kf) (Finset.mem_univ _))

/-! ## The data of the construction -/

/-- A continuous partial function with bounded variation, together with the two
constants used in the construction of a subsequential transducer for it: every
string that can be extended into the domain can be extended by a string of
length at most `k`, and the outputs on two extensions of length at most `k + 1`
are at left distance at most `K`. -/
structure Data (A B : Type) where
  /-- The partial function. -/
  f : List A → Option (List B)
  /-- The bound on the length of the extensions into the domain. -/
  k : ℕ
  /-- The bound on the left distance of the outputs of short extensions. -/
  K : ℕ
  /-- Continuity of `f`. -/
  cont : PartialContinuous f
  /-- Every string that can be extended into the domain has a short extension. -/
  short : ∀ w : List A, w ∈ Pre f → ∃ v : List A, v.length ≤ k ∧ (f (w ++ v)).isSome
  /-- Uniform bounded variation on the extensions of length at most `k + 1`. -/
  bv : ∀ (w u₁ u₂ : List A) (x₁ x₂ : List B), u₁.length ≤ k + 1 → u₂.length ≤ k + 1 →
    f (w ++ u₁) = some x₁ → f (w ++ u₂) = some x₂ → leftDist x₁ x₂ ≤ K

/-- Every continuous partial function with bounded variation gives such a
datum. -/
lemma exists_data [Finite A] [Finite B] {f : List A → Option (List B)}
    (hcont : PartialContinuous f) (hbv : BoundedVariation f) :
    ∃ D : Data A B, D.f = f := by
  obtain ⟨k, hk⟩ := exists_short_extension hcont
  obtain ⟨K, hK⟩ := exists_uniform_bv hbv (k + 1)
  exact ⟨⟨f, k, K, hcont, hk, fun w u₁ u₂ x₁ x₂ h₁ h₂ => hK w u₁ u₂ x₁ x₂ h₁ h₂⟩, rfl⟩

variable (D : Data A B)

/-- `w` has an extension of length at most `k + 1` inside the domain. -/
def ShortDef (w : List A) : Prop := ∃ v : List A, v.length ≤ D.k + 1 ∧ (D.f (w ++ v)).isSome

lemma shortDef_iff (w : List A) : ShortDef D w ↔ w ∈ Pre D.f := by
  constructor
  · rintro ⟨v, _, hv⟩; exact ⟨v, hv⟩
  · intro hw
    obtain ⟨v, hv, hvd⟩ := D.short w hw
    exact ⟨v, by omega, hvd⟩

/-! ## The non-branching part -/

open Classical in
/-- A reference output: the output of some short extension of `w`. -/
noncomputable def refOut (w : List A) : List B :=
  if h : ShortDef D w then (D.f (w ++ h.choose)).getD [] else []

lemma refOut_spec {w : List A} (h : ShortDef D w) :
    ∃ v : List A, v.length ≤ D.k + 1 ∧ D.f (w ++ v) = some (refOut D w) := by
  classical
  refine ⟨h.choose, h.choose_spec.1, ?_⟩
  have hs := h.choose_spec.2
  rw [refOut, dif_pos h]
  cases hh : D.f (w ++ h.choose) with
  | none => rw [hh] at hs; simp at hs
  | some x => simp

/-- The length of the longest common prefix of the outputs of the short
extensions of `w`. -/
noncomputable def alphaLen (w : List A) : ℕ :=
  sInf {n : ℕ | ∃ (v : List A) (x : List B), v.length ≤ D.k + 1 ∧ D.f (w ++ v) = some x ∧
    (lcp2 (refOut D w) x).length = n}

/-- The *non-branching part* of `w`: the longest common prefix of the outputs of
the extensions of `w` of length at most `k + 1`. -/
noncomputable def alpha (w : List A) : List B := (refOut D w).take (alphaLen D w)

lemma alpha_eq_nil {w : List A} (h : ¬ ShortDef D w) : alpha D w = [] := by
  have : refOut D w = [] := by rw [refOut, dif_neg h]
  simp [alpha, this]

/-- `alpha D w` is a prefix of the output of every short extension of `w`. -/
lemma alpha_prefix {w v : List A} {x : List B} (hv : v.length ≤ D.k + 1)
    (hx : D.f (w ++ v) = some x) : alpha D w <+: x := by
  have hle : alphaLen D w ≤ (lcp2 (refOut D w) x).length := Nat.sInf_le ⟨v, x, hv, hx, rfl⟩
  have h1 : (refOut D w).take (alphaLen D w) <+:
      (refOut D w).take (lcp2 (refOut D w) x).length := List.take_prefix_take_left hle
  have h2 : (refOut D w).take (lcp2 (refOut D w) x).length = lcp2 (refOut D w) x :=
    (List.prefix_iff_eq_take.1 (lcp2_prefix_left _ _)).symm
  rw [h2] at h1
  exact h1.trans (lcp2_prefix_right _ _)

/-- `alpha D w` is the *longest* common prefix of the outputs of the short
extensions of `w`. -/
lemma alpha_greatest {w : List A} {p : List B} (h : ShortDef D w)
    (hp : ∀ (v : List A) (x : List B), v.length ≤ D.k + 1 → D.f (w ++ v) = some x → p <+: x) :
    p <+: alpha D w := by
  obtain ⟨v₀, hv₀, hf₀⟩ := refOut_spec D h
  have hne : {n : ℕ | ∃ (v : List A) (x : List B), v.length ≤ D.k + 1 ∧ D.f (w ++ v) = some x ∧
      (lcp2 (refOut D w) x).length = n}.Nonempty := ⟨_, v₀, refOut D w, hv₀, hf₀, rfl⟩
  have hmem : ∃ (v : List A) (x : List B), v.length ≤ D.k + 1 ∧ D.f (w ++ v) = some x ∧
      (lcp2 (refOut D w) x).length = alphaLen D w := Nat.sInf_mem hne
  obtain ⟨v, x, hv, hx, hlen⟩ := hmem
  have h1 : p <+: refOut D w := hp v₀ _ hv₀ hf₀
  have h2 : p <+: x := hp v x hv hx
  have h3 : p <+: lcp2 (refOut D w) x := prefix_lcp2 h1 h2
  have h4 : lcp2 (refOut D w) x = alpha D w := by
    rw [alpha, ← hlen]
    exact List.prefix_iff_eq_take.1 (lcp2_prefix_left _ _)
  rwa [h4] at h3

/-- The longest common prefix is achieved by a pair of short extensions: given
one short extension with output `x`, there is another one whose output has
exactly `alpha D w` as longest common prefix with `x`. -/
lemma alpha_achieved {w v : List A} {x : List B} (hv : v.length ≤ D.k + 1)
    (hx : D.f (w ++ v) = some x) :
    ∃ (v' : List A) (x' : List B), v'.length ≤ D.k + 1 ∧ D.f (w ++ v') = some x' ∧
      (lcp2 x x').length = (alpha D w).length := by
  by_contra hcon
  push_neg at hcon
  have hshort : ShortDef D w := ⟨v, hv, by rw [hx]; simp⟩
  have hge : ∀ (v' : List A) (x' : List B), v'.length ≤ D.k + 1 → D.f (w ++ v') = some x' →
      (alpha D w).length + 1 ≤ (lcp2 x x').length := by
    intro v' x' hv' hx'
    have h1 : alpha D w <+: x := alpha_prefix D hv hx
    have h2 : alpha D w <+: x' := alpha_prefix D hv' hx'
    have hle := (prefix_lcp2 h1 h2).length_le
    have hne := hcon v' x' hv' hx'
    omega
  have hxlen : (alpha D w).length + 1 ≤ x.length := by
    have h1 := hge v x hv hx
    have h2 : (lcp2 x x).length ≤ x.length := lcp2_length_le_left x x
    omega
  have hpre : ∀ (v' : List A) (x' : List B), v'.length ≤ D.k + 1 → D.f (w ++ v') = some x' →
      x.take ((alpha D w).length + 1) <+: x' := by
    intro v' x' hv' hx'
    have h := hge v' x' hv' hx'
    have h1 : x.take ((alpha D w).length + 1) <+: x.take (lcp2 x x').length :=
      List.take_prefix_take_left h
    have h2 : x.take (lcp2 x x').length = lcp2 x x' :=
      (List.prefix_iff_eq_take.1 (lcp2_prefix_left _ _)).symm
    rw [h2] at h1
    exact h1.trans (lcp2_prefix_right _ _)
  have hlen := (alpha_greatest D hshort hpre).length_le
  simp only [List.length_take] at hlen
  omega

/-- The bound on the length of the branching part. -/
def M0 : ℕ := 2 * D.K

/-- **The delay bound.**  The output of a short extension of `w` exceeds the
non-branching part `alpha D w` by at most `M0 D` letters. -/
lemma delay_bound {w v : List A} {x : List B} (hv : v.length ≤ D.k + 1)
    (hx : D.f (w ++ v) = some x) : x.length - (alpha D w).length ≤ M0 D := by
  have hshort : ShortDef D w := ⟨v, hv, by rw [hx]; simp⟩
  obtain ⟨v₀, hv₀, hf₀⟩ := refOut_spec D hshort
  have hd : leftDist (refOut D w) x ≤ D.K := D.bv w v₀ v _ x hv₀ hv hf₀ hx
  have hxy : x.length - (refOut D w).length ≤ D.K :=
    length_sub_le_of_leftDist (by rw [leftDist_comm]; exact hd)
  have hpre : ∀ (v' : List A) (x' : List B), v'.length ≤ D.k + 1 → D.f (w ++ v') = some x' →
      (refOut D w).take ((refOut D w).length - D.K) <+: x' := by
    intro v' x' hv' hx'
    exact take_sub_prefix_of_leftDist (D.bv w v₀ v' _ x' hv₀ hv' hf₀ hx')
  have hlen := (alpha_greatest D hshort hpre).length_le
  simp only [List.length_take] at hlen
  simp only [M0]
  omega

end Subseq

end Lax132576Proofs.Transducers
