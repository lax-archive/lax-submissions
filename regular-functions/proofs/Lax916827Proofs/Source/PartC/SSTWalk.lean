/-
The two-way transducer that simulates a normalised streaming string transducer,
by a depth-first traversal of its register flow tree (the "sst to regular" half
of Theorem `theorem:sst-two-way-equivalence` of *Transducers*, M. Bojańczyk).

Fix a normalised sst `N` (see `RequestProject/PartC/SSTNorm.lean`) and an input
`w`.  The *frame* at head position `p < |w|` is the register update
`N.upd w[p]`, and the frame at the last position `|w|` is the final output
string `N.final (N.state w)`.  The value of a register `x` after `p + 1` letters
is obtained from the frame at `p` by substituting, for every register `y`
occurring in `N.upd w[p] x`, the value of `y` after `p` letters -- and the
output of `N` is obtained by expanding, in this way, the frame at `|w|`.

The two-way transducer performs that expansion directly:

* in the state `start z` at position `p` it starts expanding the string
  `N.upd w[p] z` left to right, printing the letters it meets;
* when it meets a register `y`, it moves *left* to `p - 1` in the state
  `start y`, to expand the value of `y`;
* when the expansion of a frame owned by `z` at position `p` is finished, it
  moves *right* to `p + 1` in the state `ret z`; there it has to resume the
  expansion at the place where `z` occurs, and the copyless restriction is
  exactly what makes that place a function of `z` and of the letter at `p + 1`:
  `z` occurs at most once in the whole update applied at that position.

The traversal starts by sweeping to the end of the input and expanding the final
output string, whose register occurrences are pairwise distinct because `N` is
normalised; when its expansion is finished, the machine halts.
-/
import Lax916827Proofs.Source.PartC.SSTNorm
import Lax916827Proofs.Source.PartC.TwoWayPrecomp
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace NSSTWalk

/-! ## Strings over registers and letters -/

section Strings

variable {X B : Type}

/-- The letters of a string over `X + B`, forgetting the registers. -/
def lettersOf : List (X ⊕ B) → List B
  | [] => []
  | Sum.inl _ :: s => lettersOf s
  | Sum.inr b :: s => b :: lettersOf s

/-- The decomposition of a string over `X + B` at its first register: the
letters before it, that register, and the rest of the string. -/
def firstReg : List (X ⊕ B) → Option (List B × X × List (X ⊕ B))
  | [] => none
  | Sum.inl z :: s => some ([], z, s)
  | Sum.inr b :: s => (firstReg s).map (fun p => (b :: p.1, p.2))

/-- The suffix of a string over `X + B` after the first occurrence of a given
register. -/
def sufAfter [DecidableEq X] (y : X) : List (X ⊕ B) → Option (List (X ⊕ B))
  | [] => none
  | Sum.inl z :: s => if z = y then some s else sufAfter y s
  | Sum.inr _ :: s => sufAfter y s

lemma subst_eq_lettersOf {η : X → List B} (h : ∀ x, η x = []) (s : List (X ⊕ B)) :
    SST.subst η s = lettersOf s := by
  induction s with
  | nil => rfl
  | cons z s ih => cases z <;> simp [lettersOf, ih, h]

lemma subst_eq_lettersOf_of_firstReg (η : X → List B) :
    ∀ {s : List (X ⊕ B)}, firstReg s = none → SST.subst η s = lettersOf s
  | [], _ => rfl
  | Sum.inl _ :: _, h => by simp [firstReg] at h
  | Sum.inr b :: s, h => by
      have h' : firstReg (X := X) (B := B) s = none := by
        rcases hs : firstReg (X := X) (B := B) s with _ | p
        · rfl
        · rw [firstReg, hs] at h; simp at h
      simp [lettersOf, subst_eq_lettersOf_of_firstReg η h']

lemma eq_of_firstReg :
    ∀ {s : List (X ⊕ B)} {pre : List B} {z : X} {s' : List (X ⊕ B)},
      firstReg s = some (pre, z, s') → s = pre.map Sum.inr ++ Sum.inl z :: s'
  | [], _, _, _, h => by simp [firstReg] at h
  | Sum.inl _ :: _, _, _, _, h => by
      rw [firstReg] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | Sum.inr b :: s, pre, z, s', h => by
      rcases hs : firstReg (X := X) (B := B) s with _ | ⟨pre₀, z₀, s₀⟩
      · rw [firstReg, hs] at h; simp at h
      · rw [firstReg, hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [eq_of_firstReg hs]
        simp

lemma sufAfter_eq_none [DecidableEq X] {y : X} {s : List (X ⊕ B)} (h : y ∉ regsOf s) :
    sufAfter y s = none := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl z =>
          rw [regsOf.cons_inl, List.mem_cons] at h
          simp only [sufAfter, if_neg (fun hz : z = y => h (Or.inl hz.symm))]
          exact ih (fun hy => h (Or.inr hy))
      | inr b =>
          rw [regsOf.cons_inr] at h
          simp only [sufAfter]
          exact ih h

lemma sufAfter_append [DecidableEq X] {y : X} {s' : List (X ⊕ B)} :
    ∀ {t : List (X ⊕ B)}, y ∉ regsOf t → sufAfter y (t ++ Sum.inl y :: s') = some s'
  | [], _ => by simp [sufAfter]
  | Sum.inl z :: t, h => by
      rw [regsOf.cons_inl, List.mem_cons] at h
      rw [List.cons_append, sufAfter, if_neg (fun hz => h (Or.inl hz.symm))]
      exact sufAfter_append (fun hy => h (Or.inr hy))
  | Sum.inr _ :: t, h => by
      rw [regsOf.cons_inr] at h
      rw [List.cons_append, sufAfter]
      exact sufAfter_append h

/-- The register of the update in which a given register occurs, together with
the suffix of that string after the occurrence. -/
noncomputable def findReg [DecidableEq X] [Fintype X] (u : X → List (X ⊕ B)) (y : X) :
    Option (X × List (X ⊕ B)) :=
  Finset.univ.toList.findSome? (fun x => (sufAfter y (u x)).map (fun s => (x, s)))

end Strings

/-! ## A uniqueness lemma for `List.findSome?` -/

lemma findSome?_eq_of_unique {α β : Type} (f : α → Option β) (x : α) :
    ∀ l : List α, x ∈ l → (∀ x' ∈ l, x' ≠ x → f x' = none) → l.findSome? f = f x := by
  intro l
  induction l with
  | nil => intro hx; simp at hx
  | cons a l ih =>
      intro _ huniq
      by_cases hax : a = x
      · subst hax
        rcases hf : f a with _ | b
        · rw [List.findSome?_cons, hf]
          refine List.findSome?_eq_none_iff.2 ?_
          intro x' hx'
          by_cases h' : x' = a
          · rw [h']; exact hf
          · exact huniq x' (List.mem_cons_of_mem _ hx') h'
        · rw [List.findSome?_cons, hf]
      · have hxl : x ∈ l := by
          rcases List.mem_cons.1 ‹x ∈ a :: l› with h | h
          · exact absurd h.symm hax
          · exact h
        rw [List.findSome?_cons, huniq a List.mem_cons_self hax]
        exact ih hxl (fun x' hx' => huniq x' (List.mem_cons_of_mem _ hx'))

/-! ## The states of the traversal -/

/-- The states of the two-way transducer: sweeping to the right end of the
input, starting the expansion of the frame owned by a register, or returning
from the expansion of the value of a register. -/
inductive St (X : Type) : Type
  /-- Sweeping right to the end of the input. -/
  | sweep : St X
  /-- Starting the expansion of the frame owned by the given register. -/
  | start : X → St X
  /-- Returning from the expansion of the value of the given register. -/
  | ret : X → St X

/-- The states of the traversal form a finite set. -/
def stEquiv {X : Type} : St X ≃ Option (X ⊕ X) where
  toFun
    | St.sweep => none
    | St.start x => some (Sum.inl x)
    | St.ret x => some (Sum.inr x)
  invFun
    | none => St.sweep
    | some (Sum.inl x) => St.start x
    | some (Sum.inr x) => St.ret x
  left_inv := by rintro (_ | x | x) <;> rfl
  right_inv := by rintro (_ | (x | x)) <;> rfl

instance {X : Type} [Finite X] : Finite (St X) := Finite.of_equiv _ (stEquiv (X := X)).symm

/-! ## The two-way transducer -/

variable {A B Q X : Type} [Fintype X] [DecidableEq X]

/-- One step of the expansion of the string `s`, whose registers refer to the
values at the current position; `owner` is the register owning the frame that
`s` is a suffix of (`none` for the final output string), and `atLeft` says that
the head is at the left end of the input, where all registers are empty. -/
def act (owner : Option X) (atLeft : Bool) (s : List (X ⊕ B)) :
    List B ⊕ (St X × List B × Bool) :=
  match (if atLeft then none else firstReg s) with
  | none =>
      match owner with
      | none => Sum.inl (lettersOf s)
      | some x => Sum.inr (St.ret x, lettersOf s, true)
  | some (pre, z, _) => Sum.inr (St.start z, pre, false)

/-- The two-way transducer that traverses the register flow tree of a
normalised sst. -/
noncomputable def mach (N : NSST A B Q X) : TwoWay A B (St X) where
  init := St.sweep
  step := fun l S r =>
    match S, r with
    | St.sweep, some _ => Sum.inr (St.sweep, [], true)
    | St.sweep, none => act none l.isNone (N.final (N.stateOf l))
    | St.start x, some a => act (some x) l.isNone (N.upd a x)
    | St.start _, none => Sum.inl []
    | St.ret y, some a =>
        match findReg (N.upd a) y with
        | some p => act (some p.1) l.isNone p.2
        | none => Sum.inl []
    | St.ret y, none =>
        match sufAfter y (N.final (N.stateOf l)) with
        | some s' => act none l.isNone s'
        | none => Sum.inl []

/-! ## Locating the occurrence of a register -/

/-- The copyless restriction: if the register `y` occurs in the update of `x`,
then `findReg` finds that occurrence. -/
lemma findReg_eq (u : X → List (X ⊕ B)) (hu : Copyless u) (x y : X)
    {t s' : List (X ⊕ B)} (hux : u x = t ++ Sum.inl y :: s') :
    findReg u y = some (x, s') := by
  obtain ⟨h1, h2⟩ := (copyless_iff u).1 hu
  have hnodup : (regsOf (u x)).Nodup := h1 x
  rw [hux, regsOf.append, regsOf.cons_inl] at hnodup
  have hyt : y ∉ regsOf t := by
    intro hy
    exact (List.disjoint_of_nodup_append hnodup) hy List.mem_cons_self
  have hx : sufAfter y (u x) = some s' := by rw [hux]; exact sufAfter_append hyt
  have hother : ∀ x' : X, x' ≠ x → sufAfter y (u x') = none := by
    intro x' hne
    refine sufAfter_eq_none (fun hy => h2 x x' (fun h => hne h.symm) y ?_ hy)
    rw [hux, regsOf.append, regsOf.cons_inl]
    exact List.mem_append_right _ List.mem_cons_self
  rw [findReg, findSome?_eq_of_unique _ x _ (by simp) ?_, hx]
  · rfl
  · intro x' _ hne
    rw [hother x' hne]
    rfl

/-! ## Correctness of the traversal -/

/-- **The scan lemma.**  Starting at a position whose letter is `a`, in a state
whose transition starts the expansion of a suffix `s` of the frame `N.upd a x`,
the machine expands `s` and comes back to the next position in the state
`ret x`. -/
lemma scan (N : NSST A B Q X) : ∀ (n m : ℕ) (u : List A) (s : List (X ⊕ B)),
    u.length = n → s.length = m →
    ∀ (a : A) (v : List A) (x : X) (t : List (X ⊕ B)) (S : St X),
    N.upd a x = t ++ s →
    (mach N).step u.getLast? S (some a) = act (some x) u.getLast?.isNone s →
    (mach N).Reaches (Cfg.conf u S (a :: v)) (SST.subst (N.val u) s)
      (Cfg.conf (u ++ [a]) (St.ret x) v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro u s hu hs a v x t S hts hstep
  by_cases hcase : u.getLast?.isNone = true ∨ firstReg s = none
  · have hact : (if u.getLast?.isNone then none
        else firstReg s) = (none : Option (List B × X × List (X ⊕ B))) := by
      rcases hcase with h | h <;> simp [h]
    have hsubst : SST.subst (N.val u) s = lettersOf s := by
      rcases hcase with h | h
      · have hnil : u = [] := List.getLast?_eq_none_iff.1 (Option.isNone_iff_eq_none.1 h)
        subst hnil
        exact subst_eq_lettersOf (fun _ => rfl) s
      · exact subst_eq_lettersOf_of_firstReg _ h
    have hstep' : (mach N).step u.getLast? S ((a :: v).head?)
        = Sum.inr (St.ret x, lettersOf s, true) := by
      rw [List.head?_cons, hstep]
      simp only [act, hact]
    rw [hsubst]
    exact TwoWay.reaches_one (TwoWay.stepCfg_right_cons _ hstep')
  · push_neg at hcase
    obtain ⟨hleft, hfr⟩ := hcase
    obtain ⟨a', ha'⟩ : ∃ a', u.getLast? = some a' := by
      rcases h : u.getLast? with _ | a'
      · exact absurd (by rw [h]; rfl) hleft
      · exact ⟨a', rfl⟩
    have hAtLeft : u.getLast?.isNone = false := by rw [ha']; rfl
    obtain ⟨pre, z, s', hfr'⟩ : ∃ pre z s', firstReg s = some (pre, z, s') := by
      rcases h : firstReg s with _ | ⟨pre, z, s'⟩
      · exact absurd h hfr
      · exact ⟨pre, z, s', rfl⟩
    have hdec : s = pre.map Sum.inr ++ Sum.inl z :: s' := eq_of_firstReg hfr'
    have hune : u ≠ [] := by
      intro h; rw [h] at ha'; simp at ha'
    -- the first step: print the letters before the register, move left
    have hstep1 : (mach N).step u.getLast? S ((a :: v).head?)
        = Sum.inr (St.start z, pre, false) := by
      rw [List.head?_cons, hstep]
      simp only [act, hAtLeft, hfr', if_false, Bool.false_eq_true]
    have hr1 := TwoWay.reaches_one (TwoWay.stepCfg_left_some (mach N) ha' hstep1)
    -- the expansion of the value of `z`, one position to the left
    have hdl : u.dropLast ++ [a'] = u := List.dropLast_append_getLast? a' ha'
    have hlen : u.dropLast.length < n := by
      rw [← hu, List.length_dropLast]
      have : 0 < u.length := List.length_pos_iff.2 hune
      omega
    have hstepd : (mach N).step u.dropLast.getLast? (St.start z) (some a')
        = act (some z) u.dropLast.getLast?.isNone (N.upd a' z) := rfl
    have hr2 := ihn u.dropLast.length hlen (N.upd a' z).length u.dropLast (N.upd a' z)
      rfl rfl a' (a :: v) z [] (St.start z) (by simp) hstepd
    rw [hdl] at hr2
    have hval : SST.subst (N.val u.dropLast) (N.upd a' z) = N.val u z := by
      rw [← NSST.val_concat, hdl]
    rw [hval] at hr2
    -- the return step: locate the occurrence of `z` and resume the expansion
    have hdecu : N.upd a x = (t ++ pre.map Sum.inr) ++ Sum.inl z :: s' := by
      rw [hts, hdec, List.append_assoc]
    have hfind : findReg (N.upd a) z = some (x, s') :=
      findReg_eq (N.upd a) (N.upd_copyless a) x z hdecu
    have hstep3 : (mach N).step u.getLast? (St.ret z) ((a :: v).head?)
        = act (some x) u.getLast?.isNone s' := by
      have hm : (mach N).step u.getLast? (St.ret z) (some a) =
          (match findReg (N.upd a) z with
            | some p => act (some p.1) u.getLast?.isNone p.2
            | none => Sum.inl []) := rfl
      rw [List.head?_cons, hm, hfind]
    have hslt : s'.length < m := by
      rw [← hs, hdec]
      simp
      omega
    have hr3 := ihm s'.length hslt u s' hu rfl a v x
      (t ++ pre.map Sum.inr ++ [Sum.inl z]) (St.ret z)
      (by rw [hdecu]; simp) hstep3
    have hout : SST.subst (N.val u) s = pre ++ (N.val u z ++ SST.subst (N.val u) s') := by
      rw [hdec, SST.subst_append, SST.subst_map_inr, SST.subst_cons_inl]
    rw [hout]
    exact hr1.trans (hr2.trans hr3)

/-- **The top lemma.**  At the right end of the input, in a state whose
transition starts the expansion of a suffix `s` of the final output string, the
machine expands `s` and halts. -/
lemma top (N : NSST A B Q X) : ∀ (m : ℕ) (s : List (X ⊕ B)), s.length = m →
    ∀ (u : List A) (t : List (X ⊕ B)) (S : St X),
    N.final (N.state u) = t ++ s →
    (mach N).step u.getLast? S none = act none u.getLast?.isNone s →
    (mach N).Reaches (Cfg.conf u S []) (SST.subst (N.val u) s) Cfg.halt := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro s hs u t S hts hstep
  by_cases hcase : u.getLast?.isNone = true ∨ firstReg s = none
  · have hact : (if u.getLast?.isNone then none
        else firstReg s) = (none : Option (List B × X × List (X ⊕ B))) := by
      rcases hcase with h | h <;> simp [h]
    have hsubst : SST.subst (N.val u) s = lettersOf s := by
      rcases hcase with h | h
      · have hnil : u = [] := List.getLast?_eq_none_iff.1 (Option.isNone_iff_eq_none.1 h)
        subst hnil
        exact subst_eq_lettersOf (fun _ => rfl) s
      · exact subst_eq_lettersOf_of_firstReg _ h
    have hstep' : (mach N).step u.getLast? S (([] : List A).head?)
        = Sum.inl (lettersOf s) := by
      rw [List.head?_nil, hstep]
      simp only [act, hact]
    rw [hsubst]
    exact TwoWay.reaches_one (TwoWay.stepCfg_halt_eq _ hstep')
  · push_neg at hcase
    obtain ⟨hleft, hfr⟩ := hcase
    obtain ⟨a', ha'⟩ : ∃ a', u.getLast? = some a' := by
      rcases h : u.getLast? with _ | a'
      · exact absurd (by rw [h]; rfl) hleft
      · exact ⟨a', rfl⟩
    have hAtLeft : u.getLast?.isNone = false := by rw [ha']; rfl
    obtain ⟨pre, z, s', hfr'⟩ : ∃ pre z s', firstReg s = some (pre, z, s') := by
      rcases h : firstReg s with _ | ⟨pre, z, s'⟩
      · exact absurd h hfr
      · exact ⟨pre, z, s', rfl⟩
    have hdec : s = pre.map Sum.inr ++ Sum.inl z :: s' := eq_of_firstReg hfr'
    have hune : u ≠ [] := by
      intro h; rw [h] at ha'; simp at ha'
    have hstep1 : (mach N).step u.getLast? S (([] : List A).head?)
        = Sum.inr (St.start z, pre, false) := by
      rw [List.head?_nil, hstep]
      simp only [act, hAtLeft, hfr', if_false, Bool.false_eq_true]
    have hr1 := TwoWay.reaches_one (TwoWay.stepCfg_left_some (mach N) ha' hstep1)
    have hdl : u.dropLast ++ [a'] = u := List.dropLast_append_getLast? a' ha'
    have hstepd : (mach N).step u.dropLast.getLast? (St.start z) (some a')
        = act (some z) u.dropLast.getLast?.isNone (N.upd a' z) := rfl
    have hr2 := scan N u.dropLast.length (N.upd a' z).length u.dropLast (N.upd a' z)
      rfl rfl a' [] z [] (St.start z) (by simp) hstepd
    rw [hdl] at hr2
    have hval : SST.subst (N.val u.dropLast) (N.upd a' z) = N.val u z := by
      rw [← NSST.val_concat, hdl]
    rw [hval] at hr2
    have hsuf : sufAfter z (N.final (N.state u)) = some s' := by
      have hdecf : N.final (N.state u) = (t ++ pre.map Sum.inr) ++ Sum.inl z :: s' := by
        rw [hts, hdec]; simp
      have hz : z ∉ regsOf (t ++ pre.map Sum.inr) := by
        have hnd := N.final_nodup (N.state u)
        rw [hdecf, regsOf.append, regsOf.cons_inl] at hnd
        intro hy
        exact (List.disjoint_of_nodup_append hnd) hy List.mem_cons_self
      rw [hdecf]
      exact sufAfter_append hz
    have hstep3 : (mach N).step u.getLast? (St.ret z) (([] : List A).head?)
        = act none u.getLast?.isNone s' := by
      have hm : (mach N).step u.getLast? (St.ret z) none =
          (match sufAfter z (N.final (N.stateOf u.getLast?)) with
            | some s'' => act none u.getLast?.isNone s''
            | none => Sum.inl []) := rfl
      rw [List.head?_nil, hm]
      rw [show N.stateOf u.getLast? = N.state u from rfl, hsuf]
    have hslt : s'.length < m := by
      rw [← hs, hdec]
      simp
      omega
    have hr3 := ihm s'.length hslt s' rfl u (t ++ pre.map Sum.inr ++ [Sum.inl z]) (St.ret z)
      (by rw [hts, hdec]; simp) hstep3
    have hout : SST.subst (N.val u) s = pre ++ (N.val u z ++ SST.subst (N.val u) s') := by
      rw [hdec, SST.subst_append, SST.subst_map_inr, SST.subst_cons_inl]
    rw [hout]
    exact hr1.trans (hr2.trans hr3)

/-- The initial sweep to the right end of the input. -/
lemma sweep (N : NSST A B Q X) : ∀ (v u : List A),
    (mach N).Reaches (Cfg.conf u St.sweep v) [] (Cfg.conf (u ++ v) St.sweep []) := by
  intro v
  induction v with
  | nil => intro u; simpa using TwoWay.Reaches.refl (Cfg.conf u St.sweep [])
  | cons a v ih =>
      intro u
      have hstep : (mach N).step u.getLast? St.sweep ((a :: v).head?)
          = Sum.inr (St.sweep, [], true) := rfl
      have h1 := TwoWay.reaches_one (TwoWay.stepCfg_right_cons (mach N) hstep)
      have := h1.trans (ih (u ++ [a]))
      simpa using this

/-- The two-way transducer computes the semantics of the normalised sst. -/
theorem mach_computes (N : NSST A B Q X) (w : List A) : (mach N).Computes w (N.eval w) := by
  have h1 := sweep N w []
  rw [List.nil_append] at h1
  have hstep : (mach N).step w.getLast? St.sweep (([] : List A).head?)
      = act none w.getLast?.isNone (N.final (N.state w)) := rfl
  have h2 := top N (N.final (N.state w)).length (N.final (N.state w)) rfl w [] St.sweep
    (by simp) hstep
  have := h1.trans h2
  rw [List.nil_append] at this
  exact this

end NSSTWalk

/-- Every function computed by a normalised sst is computed by a two-way
transducer. -/
theorem isTwoWay_of_nsst {A B Q X : Type} [Fintype X] (N : NSST A B Q X) :
    IsTwoWay N.eval := by
  classical
  exact ⟨NSSTWalk.St X, inferInstance, NSSTWalk.mach N, NSSTWalk.mach_computes N⟩

end Lax916827Proofs.Transducers
