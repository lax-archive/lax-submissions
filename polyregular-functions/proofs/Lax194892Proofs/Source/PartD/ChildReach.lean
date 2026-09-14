/-
**The children of a configuration, described by reachability.**

`RequestProject/PartD/ChildSem.lean` defines the children of a configuration of a pebble transducer
through the auxiliary relation `Transducers.Pebble.StrictAbove`, a run whose *intermediate*
configurations stay above a given height.  In order to recognise the children by an automaton, they
have to be described instead by the reachability relation `Transducers.Pebble.RestrReaches`, which
`RequestProject/PartD/PebReach.lean` proves regular.  That is what this file does:

* `Transducers.CG.nextChild_iff` -- the successor of a child is reached either by a single step, or
  by pushing a pebble, running above the child and popping the pebble again; and in the second case
  the column does not change.  This is the decomposition that the checking automaton uses.
* `Transducers.CG.childStar_iff_restrReaches` -- a vertex is reached from a child by a chain of
  `NextChild` steps if and only if its configuration is reached from that of the child by a run
  that never pops below the height of the children.
* `Transducers.CG.childStar_iff_mem` -- for the list of children of a configuration, the vertices
  reached from the first child by such a chain are exactly the children.
-/
import Lax194892Proofs.Source.PartD.ChildSem
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace Pebble

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q k} {w : List A}

/-- The source of a restricted run has the required height. -/
lemma restrReaches_heightGe {ℓ : ℕ} {c c' : PebbleCfg Q} (h : M.RestrReaches w ℓ c c') :
    HeightGe ℓ c := by
  cases h with
  | refl q st hq => exact hq
  | step hq _ _ => exact hq

/-- The target of a restricted run has the required height. -/
lemma restrReaches_target_heightGe {ℓ : ℕ} {c c' : PebbleCfg Q} (h : M.RestrReaches w ℓ c c') :
    HeightGe ℓ c' := by
  induction h with
  | refl q st hq => exact hq
  | step _ _ _ ih => exact ih

/-- A restricted run does not touch the pebbles below its floor. -/
lemma restrReaches_take {j : ℕ} {q q' : Q} {st st' : List ℕ}
    (h : M.RestrReaches w (j + 1) (PebbleCfg.conf q st) (PebbleCfg.conf q' st')) :
    st'.take j = st.take j := by
  generalize hc : PebbleCfg.conf q st = c at h
  generalize hc' : PebbleCfg.conf q' st' = c' at h
  induction h generalizing q st with
  | refl q₀ st₀ hq =>
      injection hc with _ e2
      injection hc' with _ f2
      rw [e2, f2]
  | @step q₀ st₀ d d' o hq hs hr ih =>
      injection hc with e1 e2
      subst e1
      subst e2
      cases d with
      | halt => exact absurd (restrReaches_heightGe hr) (by simp)
      | conf q₁ st₁ =>
          have h0 : j < st.length := by omega
          rw [ih rfl hc', stepCfg_take hs h0]

/-- A run above a height is a run above any smaller height. -/
lemma StrictAbove.weaken {h h' : ℕ} (hle : h' ≤ h) {c c' : PebbleCfg Q}
    (hr : M.StrictAbove w h c c') : M.StrictAbove w h' c c' := by
  induction hr with
  | one hs => exact StrictAbove.one hs
  | @cons d d' d'' o hs hh _ ih =>
      refine StrictAbove.cons hs ?_ ih
      cases d' with
      | conf q₁ st₁ => exact le_trans hle hh
      | halt => exact hh

/-- A step can be appended to a run above a height. -/
lemma StrictAbove.append {h : ℕ} {a b c : PebbleCfg Q} {o : List B}
    (hr : M.StrictAbove w h a b) (hb : HeightGe h b) (hs : M.stepCfg w b = some (o, c)) :
    M.StrictAbove w h a c := by
  induction hr with
  | @one d d' o' hs' => exact StrictAbove.cons hs' hb (StrictAbove.one hs)
  | @cons d d' d'' o' hs' hh _ ih => exact StrictAbove.cons hs' hh (ih hb hs)

/-- The last step of a run above a height, when the target falls below it. -/
lemma strictAbove_last {h : ℕ} {c c'' : PebbleCfg Q} (hr : M.StrictAbove w h c c'')
    (hc : HeightGe h c) :
    ∃ (c' : PebbleCfg Q) (o : List B), M.RestrReaches w h c c' ∧
      M.stepCfg w c' = some (o, c'') := by
  induction hr with
  | @one d d' o hs =>
      cases d with
      | halt => exact absurd hc (by simp)
      | conf q st => exact ⟨PebbleCfg.conf q st, o, RestrReaches.refl _ _ hc, hs⟩
  | @cons d d' d'' o hs hh _ ih =>
      obtain ⟨c', o', hrr, hst⟩ := ih hh
      cases d with
      | halt => exact absurd hc (by simp)
      | conf q st => exact ⟨c', o', RestrReaches.step hc hs hrr, hst⟩

/-- A step above the height, followed by a restricted run, is a run above the height. -/
lemma strictAbove_of_step_restrReaches {h : ℕ} {c c' c'' : PebbleCfg Q} {o : List B}
    (hs : M.stepCfg w c = some (o, c')) (hh : HeightGe h c')
    (hr : M.RestrReaches w h c' c'') : M.StrictAbove w h c c'' := by
  induction hr generalizing c o with
  | refl q st hq => exact StrictAbove.one hs
  | @step q₁ st₁ d' d'' o₁ hq₁ hs₁ hr₁ ih =>
      exact StrictAbove.cons hs hh (ih hs₁ (restrReaches_heightGe hr₁))

/-- A run above a height whose endpoints are also above it is a restricted run. -/
lemma restrReaches_of_strictAbove {h : ℕ} {c c' : PebbleCfg Q} (hr : M.StrictAbove w h c c')
    (hc : HeightGe h c) (hc' : HeightGe h c') : M.RestrReaches w h c c' := by
  induction hr with
  | @one d d' o hs =>
      cases d with
      | halt => exact absurd hc (by simp)
      | conf q st =>
          cases d' with
          | halt => exact absurd hc' (by simp)
          | conf q' st' => exact RestrReaches.step hc hs (RestrReaches.refl _ _ hc')
  | @cons d d' d'' o hs hh _ ih =>
      cases d with
      | halt => exact absurd hc (by simp)
      | conf q st => exact RestrReaches.step hc hs (ih hh hc')

/-- Restricted runs compose. -/
lemma restrReaches_trans {h : ℕ} {c c' c'' : PebbleCfg Q} (h₁ : M.RestrReaches w h c c')
    (h₂ : M.RestrReaches w h c' c'') : M.RestrReaches w h c c'' := by
  induction h₁ with
  | refl q st hq => exact h₂
  | step hq hs _ ih => exact RestrReaches.step hq hs (ih h₂)

end Pebble

namespace CG

open Pebble

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q k} {w : List A} {st : List ℕ} {q : Q}

/-- A stack of height `st.length + 1` whose bottom part is `st`. -/
lemma eq_append_of_take {st st₁ : List ℕ} (h : st₁.take st.length = st)
    (hlen : st₁.length = st.length + 1) : ∃ x, st₁ = st ++ [x] := by
  refine ⟨st₁[st.length]'(by omega), ?_⟩
  have h1 : st₁ = st₁.take st.length ++ st₁.drop st.length := (List.take_append_drop _ _).symm
  have h2 : st₁.drop st.length = [st₁[st.length]'(by omega)] := by
    refine List.ext_getElem (by simp; omega) ?_
    intro n hn hn'
    simp only [List.length_drop, hlen] at hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp
  rw [h] at h1
  rw [h2] at h1
  exact h1

@[simp] lemma cfgOf_eq_conf (v : Vtx Q) : cfgOf st v = PebbleCfg.conf v.1 (st ++ [v.2]) := rfl

/-! ## The successor of a child -/

/-- **The successor of a child is reached either by a single step, or by pushing a pebble, running
above the child and popping the pebble again.**  In the second case the column of the child does
not change, because popping a pebble leaves the pebbles below it in place. -/
theorem nextChild_iff {v v' : Vtx Q} :
    NextChild M w st v v' ↔
      (∃ o, M.stepCfg w (cfgOf st v) = some (o, cfgOf st v')) ∨
      (∃ (q₂ q₃ : Q) (r : ℕ) (o₁ o₂ : List B),
        M.stepCfg w (cfgOf st v) = some (o₁, PebbleCfg.conf q₂ (st ++ [v.2] ++ [0])) ∧
        M.RestrReaches w (st.length + 2) (PebbleCfg.conf q₂ (st ++ [v.2] ++ [0]))
          (PebbleCfg.conf q₃ (st ++ [v.2] ++ [r])) ∧
        M.stepCfg w (PebbleCfg.conf q₃ (st ++ [v.2] ++ [r])) = some (o₂, cfgOf st v')) := by
  constructor
  · intro h
    cases h with
    | @one c c' o hs => exact Or.inl ⟨o, hs⟩
    | @cons c d c'' o hs hh hr =>
        right
        -- the first step is a push
        cases d with
        | halt => exact absurd hh (by simp)
        | conf q₂ st₂ =>
            have hlen2 : st.length + 2 ≤ st₂.length := hh
            have hle : st₂.length ≤ (st ++ [v.2]).length + 1 := stepCfg_length_le hs
            simp only [List.length_append, List.length_cons, List.length_nil] at hle
            have hst2 : st₂ = st ++ [v.2] ++ [0] := by
              rcases stepCfg_conf_cases hs with h1 | h1 | h1 | ⟨p, -, hp⟩
              · exfalso
                have := congrArg List.length h1
                simp only [List.length_append, List.length_cons, List.length_nil] at this
                omega
              · exact h1
              · exfalso
                have := congrArg List.length h1
                simp only [List.length_append, List.length_cons, List.length_nil,
                  List.length_dropLast] at this
                omega
              · exfalso
                rcases hp with ⟨h2, -⟩ | h2 <;>
                  · have := congrArg List.length h2
                    simp only [List.length_append, List.length_cons, List.length_nil,
                      List.length_dropLast] at this
                    omega
            subst hst2
            -- the run above the child, and its last step
            obtain ⟨c', o₂, hrr, hst⟩ := strictAbove_last hr hh
            cases c' with
            | halt => exact absurd (restrReaches_target_heightGe hrr) (by simp)
            | conf q₃ st₃ =>
                have hlen3 : st.length + 2 ≤ st₃.length := restrReaches_target_heightGe hrr
                have htake : st₃.take (st.length + 1) = st ++ [v.2] := by
                  have := restrReaches_take (j := st.length + 1) hrr
                  rw [this]
                  rw [List.take_append_of_le_length (by simp)]
                  exact List.take_of_length_le (by simp)
                have hpop : st ++ [v'.2] = st₃.dropLast ∧ st₃.length = st.length + 2 := by
                  rcases stepCfg_conf_cases hst with h1 | h1 | h1 | ⟨p, -, hp⟩
                  · exfalso
                    have := congrArg List.length h1
                    simp only [List.length_append, List.length_cons, List.length_nil] at this
                    omega
                  · exfalso
                    have := congrArg List.length h1
                    simp only [List.length_append, List.length_cons, List.length_nil] at this
                    omega
                  · refine ⟨h1, ?_⟩
                    have := congrArg List.length h1
                    simp only [List.length_append, List.length_cons, List.length_nil,
                      List.length_dropLast] at this
                    omega
                  · exfalso
                    rcases hp with ⟨h2, -⟩ | h2 <;>
                      · have := congrArg List.length h2
                        simp only [List.length_append, List.length_cons, List.length_nil,
                          List.length_dropLast] at this
                        omega
                obtain ⟨hdl, hlen3'⟩ := hpop
                obtain ⟨r, hr3⟩ := eq_append_of_take (st := st ++ [v.2]) (by
                  simpa using htake) (by simp; omega)
                refine ⟨q₂, q₃, r, o, o₂, hs, ?_, ?_⟩
                · rw [← hr3]; exact hrr
                · rw [← hr3]; exact hst
  · rintro (⟨o, hs⟩ | ⟨q₂, q₃, r, o₁, o₂, hs₁, hrr, hs₂⟩)
    · exact StrictAbove.one hs
    · have hh₂ : HeightGe (st.length + 2) (PebbleCfg.conf q₂ (st ++ [v.2] ++ [0])) := by
        simp [HeightGe]
      have hh₃ : HeightGe (st.length + 2) (PebbleCfg.conf q₃ (st ++ [v.2] ++ [r])) := by
        simp [HeightGe]
      exact StrictAbove.append (strictAbove_of_step_restrReaches hs₁ hh₂ hrr) hh₃ hs₂

/-! ## Chains of children -/

/-- **The reflexive transitive closure of the successor relation on children.** -/
inductive ChildStar (M : Pebble A B Q k) (w : List A) (st : List ℕ) : Vtx Q → Vtx Q → Prop
  /-- The empty chain. -/
  | refl (v : Vtx Q) : ChildStar M w st v v
  /-- One successor step, followed by a chain. -/
  | cons {v v' v'' : Vtx Q} : NextChild M w st v v' → ChildStar M w st v' v'' →
      ChildStar M w st v v''

lemma ChildStar.restrReaches {v v' : Vtx Q} (h : ChildStar M w st v v') :
    M.RestrReaches w (st.length + 1) (cfgOf st v) (cfgOf st v') := by
  induction h with
  | refl v => exact RestrReaches.refl _ _ (by simp)
  | cons hn _ ih =>
      refine restrReaches_trans ?_ ih
      refine restrReaches_of_strictAbove (hn.weaken (by omega)) ?_ ?_ <;> simp [HeightGe]

/-- The key step: a restricted run between configurations of the height of the children is a chain
of successor steps.  The second disjunct of the hypothesis is the invariant that carries the
argument through the excursions above that height. -/
lemma childStar_of_restrReaches_aux :
    ∀ {c c'' : PebbleCfg Q}, M.RestrReaches w (st.length + 1) c c'' →
      ∀ (v v' : Vtx Q), c'' = cfgOf st v' →
        (c = cfgOf st v ∨
          (M.StrictAbove w (st.length + 2) (cfgOf st v) c ∧ HeightGe (st.length + 2) c)) →
        ChildStar M w st v v' := by
  intro c c'' h
  induction h with
  | refl q₀ st₀ hq =>
      rintro v v' hc'' (heq | ⟨-, hgt⟩)
      · have hvv : cfgOf st v = cfgOf st v' := by rw [← heq, hc'']
        exact (cfgOf_inj hvv) ▸ ChildStar.refl v
      · rw [cfgOf, PebbleCfg.conf.injEq] at hc''
        obtain ⟨-, hst0⟩ := hc''
        subst hst0
        have hcon : st.length + 2 ≤ (st ++ [v'.2]).length := hgt
        simp at hcon
  | @step q₀ st₀ d d'' o hq hs hr ih =>
      rintro v v' rfl hdisj
      cases d with
      | halt => exact absurd (restrReaches_heightGe hr) (by simp)
      | conf q₁ st₁ =>
          have hgt1 : st.length + 1 ≤ st₁.length := restrReaches_heightGe hr
          rcases hdisj with heq | ⟨hsa, hgt⟩
          · -- the source is the child `v`
            rw [cfgOf, PebbleCfg.conf.injEq] at heq
            obtain ⟨hq0, hst0⟩ := heq
            subst hq0
            subst hst0
            by_cases hcase : st₁.length = st.length + 1
            · have htake : st₁.take st.length = st := by
                rw [stepCfg_take hs (by simp)]
                rw [List.take_append_of_le_length (by simp)]
                exact List.take_of_length_le (by simp)
              obtain ⟨x, hx⟩ := eq_append_of_take htake hcase
              subst hx
              refine ChildStar.cons (v' := (q₁, x)) (StrictAbove.one hs) ?_
              exact ih (q₁, x) v' rfl (Or.inl rfl)
            · refine ih v v' rfl (Or.inr ⟨StrictAbove.one hs, ?_⟩)
              show st.length + 2 ≤ st₁.length
              omega
          · -- the source is inside an excursion above the child `v`
            have hsa' : M.StrictAbove w (st.length + 2) (cfgOf st v)
                (PebbleCfg.conf q₁ st₁) := hsa.append hgt hs
            by_cases hcase : st₁.length = st.length + 1
            · have htake : st₁.take st.length = st := by
                have := strictAbove_take (j := st.length) (hsa'.weaken (by omega))
                  (by simp) q₁ st₁ rfl
                rw [this, List.take_append_of_le_length (by simp)]
                exact List.take_of_length_le (by simp)
              obtain ⟨x, hx⟩ := eq_append_of_take htake hcase
              subst hx
              refine ChildStar.cons (v' := (q₁, x)) hsa' ?_
              exact ih (q₁, x) v' rfl (Or.inl rfl)
            · refine ih v v' rfl (Or.inr ⟨hsa', ?_⟩)
              show st.length + 2 ≤ st₁.length
              omega

/-- **A vertex is reached from a child by a chain of successor steps exactly when its configuration
is reached by a run that never pops below the height of the children.** -/
theorem childStar_iff_restrReaches {v v' : Vtx Q} :
    ChildStar M w st v v' ↔
      M.RestrReaches w (st.length + 1) (cfgOf st v) (cfgOf st v') :=
  ⟨ChildStar.restrReaches, fun h => childStar_of_restrReaches_aux h v v' rfl (Or.inl rfl)⟩

/-! ## The chain from the first child enumerates the children -/

variable {ch : ℕ → Vtx Q} {m : ℕ}

lemma IsChildSeq.childStar (hseq : IsChildSeq M w q st ch m) {t : ℕ} (ht : t ≤ m) :
    ChildStar M w st (ch 0) (ch t) := by
  induction t with
  | zero => exact ChildStar.refl _
  | succ t ih =>
      have htm : t < m := by omega
      have hst := ih (by omega)
      clear ih
      -- append the last step
      have : ∀ {a b : Vtx Q}, ChildStar M w st a b → ∀ {c : Vtx Q}, NextChild M w st b c →
          ChildStar M w st a c := by
        intro a b hab
        induction hab with
        | refl v => intro c hc; exact ChildStar.cons hc (ChildStar.refl _)
        | cons hn _ ihn => intro c hc; exact ChildStar.cons hn (ihn hc)
      exact this hst (hseq.next t htm)

/-- **The vertices reached from the first child are exactly the children.** -/
theorem childStar_iff_mem (hseq : IsChildSeq M w q st ch m) (v : Vtx Q) :
    ChildStar M w st (ch 0) v ↔ ∃ t ≤ m, ch t = v := by
  constructor
  · intro h
    have key : ∀ {a b : Vtx Q}, ChildStar M w st a b → ∀ t ≤ m, a = ch t → ∃ t' ≤ m, ch t' = b := by
      intro a b hab
      induction hab with
      | refl v => intro t ht hv; exact ⟨t, ht, hv.symm⟩
      | @cons a a' b hn _ ih =>
          intro t ht hat
          subst hat
          have htm : t < m := by
            by_contra hcon
            have : t = m := by omega
            subst this
            exact hseq.stop a' hn
          have : a' = ch (t + 1) := (hn.unique (hseq.next t htm))
          exact ih (t + 1) (by omega) this
    exact key h 0 (Nat.zero_le _) rfl
  · rintro ⟨t, ht, rfl⟩
    exact hseq.childStar ht

/-! ## The first child, and the successor of a child, described inside the chain -/

/-- **The first child is reached by a single step**: the run that produces it cannot have an
intermediate configuration, because one step raises the stack by at most one and an intermediate
configuration would have to be two higher than the parent. -/
theorem firstChild_iff_step {v : Vtx Q} :
    FirstChild M w q st v ↔ ∃ o, M.stepCfg w (PebbleCfg.conf q st) = some (o, cfgOf st v) := by
  constructor
  · intro h
    cases h with
    | @one c c' o hs => exact ⟨o, hs⟩
    | @cons c d c'' o hs hh _ =>
        exfalso
        cases d with
        | halt => exact absurd hh (by simp)
        | conf q₁ st₁ =>
            have h1 : st.length + 2 ≤ st₁.length := hh
            have h2 : st₁.length ≤ st.length + 1 := stepCfg_length_le hs
            omega
  · rintro ⟨o, hs⟩
    exact StrictAbove.one hs

/-- The chain of successors joins any two children in order. -/
lemma IsChildSeq.childStar_from (hseq : IsChildSeq M w q st ch m) {s t : ℕ} (hst : s ≤ t)
    (ht : t ≤ m) : ChildStar M w st (ch s) (ch t) := by
  obtain ⟨i, rfl⟩ : ∃ i, t = s + i := ⟨t - s, by omega⟩
  induction i with
  | zero => exact ChildStar.refl _
  | succ i ih =>
      have hprev := ih (by omega) (by omega)
      have hnext : NextChild M w st (ch (s + i)) (ch (s + i + 1)) := hseq.next _ (by omega)
      have key : ∀ {a b : Vtx Q}, ChildStar M w st a b → ∀ {c : Vtx Q}, NextChild M w st b c →
          ChildStar M w st a c := by
        intro a b hab
        induction hab with
        | refl v => intro c hc; exact ChildStar.cons hc (ChildStar.refl _)
        | cons hn _ ihn => intro c hc; exact ChildStar.cons hn (ihn hc)
      exact key hprev hnext

/-- **The vertices reached from a child are exactly the later children.** -/
theorem childStar_from_iff_mem (hseq : IsChildSeq M w q st ch m) {s : ℕ} (hs : s ≤ m)
    (v : Vtx Q) : ChildStar M w st (ch s) v ↔ ∃ t, s ≤ t ∧ t ≤ m ∧ ch t = v := by
  constructor
  · intro h
    have key : ∀ {a b : Vtx Q}, ChildStar M w st a b → ∀ t ≤ m, a = ch t →
        ∃ t', t ≤ t' ∧ t' ≤ m ∧ ch t' = b := by
      intro a b hab
      induction hab with
      | refl v => intro t ht hv; exact ⟨t, le_refl t, ht, hv.symm⟩
      | @cons a a' b hn _ ih =>
          intro t ht hat
          subst hat
          have htm : t < m := by
            by_contra hcon
            have : t = m := by omega
            subst this
            exact hseq.stop a' hn
          have heq : a' = ch (t + 1) := (hn.unique (hseq.next t htm))
          obtain ⟨t', h1, h2, h3⟩ := ih (t + 1) (by omega) heq
          exact ⟨t', by omega, h2, h3⟩
    exact key h s hs rfl
  · rintro ⟨t, h1, h2, rfl⟩
    exact hseq.childStar_from h1 h2

/-- **The successor of a child is the vertex reached from it with no child strictly in between.**
This is the description of `NextChild` that the checking automaton uses: it involves only chains of
successors, that is only the reachability relation `Transducers.Pebble.RestrReaches`. -/
theorem nextChild_iff_no_mid (hseq : IsChildSeq M w q st ch m) {s : ℕ} (hs : s ≤ m) (v : Vtx Q) :
    NextChild M w st (ch s) v ↔
      (ChildStar M w st (ch s) v ∧ ch s ≠ v ∧
        ¬ ∃ u, ChildStar M w st (ch s) u ∧ ChildStar M w st u v ∧ u ≠ ch s ∧ u ≠ v) := by
  have hdist := hseq.distinct
  constructor
  · intro h
    have hsm : s < m := by
      by_contra hc
      have : s = m := by omega
      subst this
      exact hseq.stop v h
    have hv : v = ch (s + 1) := h.unique (hseq.next s hsm)
    subst hv
    refine ⟨ChildStar.cons h (ChildStar.refl _), ?_, ?_⟩
    · intro hc
      have := hdist s (s + 1) (by omega) (by omega) hc
      omega
    · rintro ⟨u, h1, h2, h3, h4⟩
      obtain ⟨p, hp1, hp2, rfl⟩ := (childStar_from_iff_mem hseq hs u).1 h1
      obtain ⟨t, ht1, ht2, ht3⟩ := (childStar_from_iff_mem hseq hp2 (ch (s + 1))).1 h2
      have hts : t = s + 1 := hdist t (s + 1) ht2 (by omega) ht3
      have hple : p = s ∨ p = s + 1 := by omega
      rcases hple with rfl | rfl
      · exact h3 rfl
      · exact h4 rfl
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨t, ht1, ht2, rfl⟩ := (childStar_from_iff_mem hseq hs v).1 h1
    have hts : s ≠ t := by
      intro hc
      exact h2 (by rw [hc])
    have hlt : s < t := by omega
    by_cases hcase : t = s + 1
    · subst hcase
      exact hseq.next s (by omega)
    · exfalso
      refine h3 ⟨ch (s + 1), hseq.childStar_from (by omega) (by omega),
        hseq.childStar_from (by omega) ht2, ?_, ?_⟩
      · intro hc
        have := hdist (s + 1) s (by omega) (by omega) hc
        omega
      · intro hc
        have := hdist (s + 1) t (by omega) ht2 hc
        omega

end CG

end Lax194892Proofs.Transducers
