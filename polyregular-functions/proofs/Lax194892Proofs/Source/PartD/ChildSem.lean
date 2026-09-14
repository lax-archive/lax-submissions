/-
**The children of a configuration of a pebble transducer.**

Section D.2 of *Transducers* (M. Bojańczyk) organises a run of a pebble transducer as a tree: the
*parent* of a configuration whose stack has height `ℓ` is the most recent earlier configuration of
height `ℓ - 1`, and the *children* of a configuration `c` of height `ℓ` are therefore the
configurations of height `ℓ + 1` that occur after `c` and before the run comes back down to the
height `ℓ`.  This file defines the children and proves the three combinatorial facts about them
that the string representation of the child configuration graph needs
(`RequestProject/PartD/ChildPath.lean`):

* consecutive children sit in the same column or in adjacent ones
  (`Transducers.CG.NextChild.column_adjacent`);
* the columns of the children are gaps of the input string (`Transducers.CG.NextChild.le_length`);
* the children are pairwise distinct, as soon as the last one has no successor
  (`Transducers.CG.IsChildSeq.distinct`), because the successor of a child is unique
  (`Transducers.CG.NextChild.unique`) and a repetition would therefore make the list of children
  periodic.

The auxiliary notion is `Transducers.Pebble.StrictAbove M w h c c'`: a run of at least one step from
`c` to `c'` all of whose *intermediate* configurations have stack height at least `h`.  With
`h = ℓ + 2` and with `c`, `c'` of height `ℓ + 1` this says exactly that `c'` is the next
configuration of height at most `ℓ + 1` after `c`, that is, the next child.
-/
import Lax194892Proofs.Source.PartD.ChildPath
import Lax194892Proofs.Source.PartD.PebEnc
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace Pebble

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q k} {w : List A}

/-- The stack of the configuration has height at least `h`; the halting vertex has no height. -/
def HeightGe (h : ℕ) : PebbleCfg Q → Prop
  | PebbleCfg.conf _ st => h ≤ st.length
  | PebbleCfg.halt => False

@[simp] lemma heightGe_conf {h : ℕ} {q : Q} {st : List ℕ} :
    HeightGe h (PebbleCfg.conf q st) ↔ h ≤ st.length := Iff.rfl

@[simp] lemma heightGe_halt {h : ℕ} : ¬ HeightGe h (PebbleCfg.halt : PebbleCfg Q) := id

/-- **A run of at least one step whose intermediate configurations have height at least `h`.** -/
inductive StrictAbove (M : Pebble A B Q k) (w : List A) (h : ℕ) :
    PebbleCfg Q → PebbleCfg Q → Prop
  /-- A single step. -/
  | one {c c' : PebbleCfg Q} {o : List B} : M.stepCfg w c = some (o, c') → StrictAbove M w h c c'
  /-- A step to a configuration of height at least `h`, followed by such a run. -/
  | cons {c c' c'' : PebbleCfg Q} {o : List B} : M.stepCfg w c = some (o, c') → HeightGe h c' →
      StrictAbove M w h c' c'' → StrictAbove M w h c c''

/-- **The target of such a run is unique**, as long as it is below the height `h`: the machine is
deterministic, so the first configuration of height less than `h` after `c` is determined. -/
lemma StrictAbove.unique {h : ℕ} {c c₁ c₂ : PebbleCfg Q} (h₁ : M.StrictAbove w h c c₁)
    (h₂ : M.StrictAbove w h c c₂) (hn₁ : ¬ HeightGe h c₁) (hn₂ : ¬ HeightGe h c₂) : c₁ = c₂ := by
  induction h₁ generalizing c₂ with
  | @one c c' o hs =>
      cases h₂ with
      | one hs' =>
          have := hs.symm.trans hs'
          exact (Prod.ext_iff.1 (Option.some.injEq _ _ ▸ this : _ = _)).2
      | cons hs' hh' _ =>
          exfalso
          have := hs.symm.trans hs'
          have : c' = _ := (Prod.ext_iff.1 (Option.some.injEq _ _ ▸ this : _ = _)).2
          exact hn₁ (this ▸ hh')
  | @cons c c' c'' o hs hh _ ih =>
      cases h₂ with
      | one hs' =>
          exfalso
          have heq := hs.symm.trans hs'
          have : c' = c₂ := (Prod.ext_iff.1 (Option.some.injEq _ _ ▸ heq : _ = _)).2
          exact hn₂ (this ▸ hh)
      | cons hs' _ hr' =>
          have heq := hs.symm.trans hs'
          have hc : c' = _ := (Prod.ext_iff.1 (Option.some.injEq _ _ ▸ heq : _ = _)).2
          exact ih (hc ▸ hr') hn₁ hn₂

/-! ## What one step does to the stack -/

/-- The four ways in which one step changes the stack. -/
lemma stepCfg_conf_cases {q q' : Q} {st st' : List ℕ} {o : List B}
    (h : M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st')) :
    st' = st ∨ st' = st ++ [0] ∨ st' = st.dropLast ∨
      (∃ p, st.getLast? = some p ∧
        ((st' = st.dropLast ++ [p + 1] ∧ p < w.length) ∨ (st' = st.dropLast ++ [p - 1]))) := by
  rw [stepCfg] at h
  split at h
  · -- output a letter
    left
    have h2 := congrArg Prod.snd (Option.some.inj h)
    injection h2 with _ h4
    exact h4.symm
  · -- terminate
    exact absurd (congrArg Prod.snd (Option.some.inj h)) (by simp)
  · -- push
    right; left
    split at h
    · have h2 := congrArg Prod.snd (Option.some.inj h)
      injection h2 with _ h4
      exact h4.symm
    · exact absurd h (by simp)
  · -- pop
    right; right; left
    split at h
    · exact absurd h (by simp)
    · have h2 := congrArg Prod.snd (Option.some.inj h)
      injection h2 with _ h4
      exact h4.symm
  · -- move
    right; right; right
    split at h
    · exact absurd h (by simp)
    · rename_i p hgl
      refine ⟨p, hgl, ?_⟩
      split at h
      · split at h
        · rename_i hp
          refine Or.inl ⟨?_, hp⟩
          have h2 := congrArg Prod.snd (Option.some.inj h)
          injection h2 with _ h4
          exact h4.symm
        · exact absurd h (by simp)
      · split at h
        · refine Or.inr ?_
          have h2 := congrArg Prod.snd (Option.some.inj h)
          injection h2 with _ h4
          exact h4.symm
        · exact absurd h (by simp)

/-- One step does not touch the pebbles below the top one. -/
lemma stepCfg_take {q q' : Q} {st st' : List ℕ} {o : List B} {j : ℕ}
    (h : M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st'))
    (hj : j < st.length) : st'.take j = st.take j := by
  have hdl : st.dropLast.take j = st.take j := by
    rw [List.dropLast_eq_take, List.take_take]
    congr 1
    omega
  rcases stepCfg_conf_cases h with h1 | h1 | h1 | ⟨p, _, hp⟩
  · rw [h1]
  · rw [h1, List.take_append_of_le_length (by omega)]
  · rw [h1, hdl]
  · rcases hp with ⟨h2, -⟩ | h2 <;>
      rw [h2, List.take_append_of_le_length (by rw [List.length_dropLast]; omega), hdl]

/-- A run that stays above the height `j + 1` does not touch the pebbles of index less than `j`. -/
lemma strictAbove_take {j : ℕ} {q₀ : Q} {st₀ : List ℕ} {c' : PebbleCfg Q}
    (h : M.StrictAbove w (j + 1) (PebbleCfg.conf q₀ st₀) c') (h0 : j < st₀.length) :
    ∀ q' st', c' = PebbleCfg.conf q' st' → st'.take j = st₀.take j := by
  generalize hc : PebbleCfg.conf q₀ st₀ = c at h
  induction h generalizing q₀ st₀ with
  | @one c c' o hs =>
      intro q' st' hc'
      subst hc; subst hc'
      exact stepCfg_take hs h0
  | @cons c d c'' o hs hh _ ih =>
      intro q' st' hc'
      subst hc
      cases d with
      | halt => exact absurd hh (by simp)
      | conf q₁ st₁ =>
          have h1 : j < st₁.length := by
            have : j + 1 ≤ st₁.length := hh
            omega
          have := ih (q₀ := q₁) (st₀ := st₁) h1 rfl q' st' hc'
          rw [this, stepCfg_take hs h0]

end Pebble

namespace CG

open Pebble

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q k} {w : List A} {st : List ℕ} {q : Q}

/-- The configuration of the child that the vertex `v` stands for: the pebbles of the parent, with
the moving pebble on top. -/
def cfgOf (st : List ℕ) (v : Vtx Q) : PebbleCfg Q := PebbleCfg.conf v.1 (st ++ [v.2])

@[simp] lemma cfgOf_length (st : List ℕ) (v : Vtx Q) :
    (st ++ [v.2]).length = st.length + 1 := by simp

lemma not_heightGe_cfgOf (st : List ℕ) (v : Vtx Q) :
    ¬ HeightGe (st.length + 2) (cfgOf st v) := by
  simp [cfgOf, HeightGe]

lemma cfgOf_inj {v v' : Vtx Q} (h : cfgOf st v = cfgOf st v') : v = v' := by
  injection h with h1 h2
  have : v.2 = v'.2 := by
    have := congrArg (fun l => l[st.length]?) h2
    simpa using this
  exact Prod.ext h1 this

/-- **`v'` is the child that follows the child `v`**: the run from `v` comes back to the height of
the children only at `v'`. -/
def NextChild (M : Pebble A B Q k) (w : List A) (st : List ℕ) (v v' : Vtx Q) : Prop :=
  M.StrictAbove w (st.length + 2) (cfgOf st v) (cfgOf st v')

/-- **`v` is the first child** of the configuration `(q, st)`. -/
def FirstChild (M : Pebble A B Q k) (w : List A) (q : Q) (st : List ℕ) (v : Vtx Q) : Prop :=
  M.StrictAbove w (st.length + 2) (PebbleCfg.conf q st) (cfgOf st v)

/-- **The successor of a child is unique.** -/
lemma NextChild.unique {v v₁ v₂ : Vtx Q} (h₁ : NextChild M w st v v₁)
    (h₂ : NextChild M w st v v₂) : v₁ = v₂ :=
  cfgOf_inj (Pebble.StrictAbove.unique h₁ h₂ (not_heightGe_cfgOf st v₁)
    (not_heightGe_cfgOf st v₂))

/-- **The first child is unique.** -/
lemma FirstChild.unique {v₁ v₂ : Vtx Q} (h₁ : FirstChild M w q st v₁)
    (h₂ : FirstChild M w q st v₂) : v₁ = v₂ :=
  cfgOf_inj (Pebble.StrictAbove.unique h₁ h₂ (not_heightGe_cfgOf st v₁)
    (not_heightGe_cfgOf st v₂))

/-- One step never raises the stack by more than one. -/
lemma stepCfg_length_le {q q' : Q} {st st' : List ℕ} {o : List B}
    (h : M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st')) :
    st'.length ≤ st.length + 1 := by
  rcases stepCfg_conf_cases h with h1 | h1 | h1 | ⟨p, -, hp⟩
  · rw [h1]; omega
  · rw [h1]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [h1, List.length_dropLast]; omega
  · rcases hp with ⟨h2, -⟩ | h2 <;>
      rw [h2] <;>
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_dropLast] <;>
      omega

/-- **The first child sits in the first gap**: the only way for the machine to make a child is to
push a pebble, and a pushed pebble sits in the first gap. -/
lemma FirstChild.column_zero {v : Vtx Q} (h : FirstChild M w q st v) : v.2 = 0 := by
  cases h with
  | @one c c' o hs =>
      rcases stepCfg_conf_cases hs with h1 | h1 | h1 | ⟨p, hp0, hp⟩
      · exfalso
        have := congrArg List.length h1
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      · have := congrArg (fun l => l[st.length]?) h1
        simpa using this
      · exfalso
        have := congrArg List.length h1
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_dropLast] at this
        omega
      · exfalso
        have hne : st ≠ [] := by
          intro hnil
          rw [hnil] at hp0
          simp at hp0
        have hpos : 0 < st.length := List.length_pos_of_ne_nil hne
        rcases hp with ⟨h2, -⟩ | h2 <;>
          · have := congrArg List.length h2
            simp only [List.length_append, List.length_cons, List.length_nil,
              List.length_dropLast] at this
            omega
  | @cons c d c'' o hs hh _ =>
      exfalso
      cases d with
      | halt => exact hh
      | conf q₁ st₁ =>
          have h1 : st.length + 2 ≤ st₁.length := hh
          have h2 := stepCfg_length_le hs
          omega

/-- **Consecutive children sit in the same column or in adjacent ones.** -/
lemma NextChild.column {v v' : Vtx Q} (h : NextChild M w st v v') :
    v'.2 = v.2 ∨ (v'.2 = v.2 + 1 ∧ v.2 < w.length) ∨ v'.2 = v.2 - 1 := by
  have hdl : (st ++ [v.2]).dropLast = st := by simp
  have hgl : (st ++ [v.2]).getLast? = some v.2 := by simp
  cases h with
  | @one c c' o hs =>
      rcases stepCfg_conf_cases hs with h1 | h1 | h1 | ⟨p, hp0, hp⟩
      · left
        have := congrArg (fun l => l[st.length]?) h1
        simpa using this
      · exfalso
        have := congrArg List.length h1
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      · exfalso
        have := congrArg List.length h1
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_dropLast] at this
        omega
      · rw [hgl] at hp0
        obtain rfl : p = v.2 := by simpa using hp0.symm
        rw [hdl] at hp
        rcases hp with ⟨h2, hlt⟩ | h2
        · right; left
          refine ⟨?_, hlt⟩
          have := congrArg (fun l => l[st.length]?) h2
          simpa using this
        · right; right
          have := congrArg (fun l => l[st.length]?) h2
          simpa using this
  | @cons c d c'' o hs hh hr =>
      left
      cases d with
      | halt => exact absurd hh (by simp)
      | conf q₁ st₁ =>
          have hlen : st.length + 2 ≤ st₁.length := hh
          have h1 : st₁ = (st ++ [v.2]) ++ [0] := by
            rcases stepCfg_conf_cases hs with h1 | h1 | h1 | ⟨p, -, hp⟩
            · exfalso
              rw [h1] at hlen
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen
              omega
            · exact h1
            · exfalso
              rw [h1] at hlen
              simp only [List.length_append, List.length_cons, List.length_nil,
                List.length_dropLast] at hlen
              omega
            · exfalso
              rcases hp with ⟨h2, -⟩ | h2 <;>
                · rw [h2] at hlen
                  simp only [List.length_append, List.length_cons, List.length_nil,
                    List.length_dropLast] at hlen
                  omega
          have h2 := strictAbove_take (j := st.length + 1) hr
            (by rw [h1]; simp) v'.1 (st ++ [v'.2]) rfl
          rw [h1] at h2
          have h3 : (st ++ [v'.2]).take (st.length + 1) = st ++ [v'.2] := by
            refine List.take_of_length_le ?_
            simp
          have h4 : ((st ++ [v.2]) ++ [0]).take (st.length + 1) = st ++ [v.2] := by
            rw [List.take_append_of_le_length (by simp)]
            refine List.take_of_length_le ?_
            simp
          rw [h3, h4] at h2
          have := congrArg (fun l => l[st.length]?) h2
          simpa using this

lemma NextChild.column_adjacent {v v' : Vtx Q} (h : NextChild M w st v v') :
    v'.2 ≤ v.2 + 1 ∧ v.2 ≤ v'.2 + 1 := by
  rcases h.column with h1 | ⟨h1, -⟩ | h1 <;> omega

lemma NextChild.le_length {v v' : Vtx Q} (h : NextChild M w st v v') (hv : v.2 ≤ w.length) :
    v'.2 ≤ w.length := by
  rcases h.column with h1 | ⟨h1, h2⟩ | h1 <;> omega

/-! ## The list of children -/

/-- **`ch 0, …, ch m` is the list of the children** of the configuration `(q, st)`, in order of
execution. -/
structure IsChildSeq (M : Pebble A B Q k) (w : List A) (q : Q) (st : List ℕ)
    (ch : ℕ → Vtx Q) (m : ℕ) : Prop where
  /-- The list starts with the first child. -/
  first : FirstChild M w q st (ch 0)
  /-- Each child is followed by the next one. -/
  next : ∀ t < m, NextChild M w st (ch t) (ch (t + 1))
  /-- The last child has no successor. -/
  stop : ∀ v, ¬ NextChild M w st (ch m) v

variable {ch : ℕ → Vtx Q} {m : ℕ}

lemma IsChildSeq.shift (h : IsChildSeq M w q st ch m) {s t : ℕ} (hlt : s < t)
    (hst : ch s = ch t) : ∀ i, t + i ≤ m → ch (s + i) = ch (t + i) := by
  intro i
  induction i with
  | zero => intro _; simpa using hst
  | succ i ih =>
      intro hi
      have heq := ih (by omega)
      have h1 : s + i < m := by omega
      have h2 : t + i < m := by omega
      have hn := h.next _ h1
      rw [heq] at hn
      have hres := hn.unique (h.next _ h2)
      rw [show s + (i + 1) = s + i + 1 from rfl, show t + (i + 1) = t + i + 1 from rfl, hres]

/-- **The children are pairwise distinct.** -/
lemma IsChildSeq.distinct (h : IsChildSeq M w q st ch m) : Distinct ch m := by
  intro s t hs ht hst
  by_contra hne
  rcases Nat.lt_or_ge s t with hlt | hge
  · have hi := h.shift hlt hst (m - t) (by omega)
    have hm : t + (m - t) = m := by omega
    rw [hm] at hi
    exact h.stop (ch (s + (m - t) + 1)) (by
      rw [← hi]
      exact h.next _ (by omega))
  · have hlt : t < s := by omega
    have hi := h.shift hlt hst.symm (m - s) (by omega)
    have hm : s + (m - s) = m := by omega
    rw [hm] at hi
    exact h.stop (ch (t + (m - s) + 1)) (by
      rw [← hi]
      exact h.next _ (by omega))

/-- The columns of the children are gaps of the input string. -/
lemma IsChildSeq.column_le (h : IsChildSeq M w q st ch m) : ∀ t ≤ m, (ch t).2 ≤ w.length := by
  intro t
  induction t with
  | zero => intro _; rw [h.first.column_zero]; omega
  | succ t ih =>
      intro ht
      exact (h.next t (by omega)).le_length (ih (by omega))

end CG

end Lax194892Proofs.Transducers
