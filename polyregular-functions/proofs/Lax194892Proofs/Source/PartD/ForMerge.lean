/-
Part D: for-transducers -- merging two nests of loops into one.

The single semantic step behind Lemma `lemma:prenex-normal-form`: on an input of length at least
two, the sequential composition of two nests of loops is again a nest of loops.  One extra loop
variable `pi` is used as a two-valued *phase*: its first iteration (`pi` at the first position,
which is the value of the designated variable `zv`) runs the first nest, its last iteration (`pi`
at the last position, the value of `lv`) runs the second nest, and the remaining iterations do
nothing.  Inside a phase the loop variables of the *other* nest are pinned to `zv`, which by
`Transducers.pin_inner` and `Transducers.pin_outer` makes them run their body exactly once.
-/
import Lax194892Proofs.Source.PartD.ForNest

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B : Type}

/-! ## Programs that output at most one letter -/

namespace ForProg

lemma outputsAtMostOne_skip : (ForProg.skip : ForProg A B).OutputsAtMostOne :=
  fun _ _ _ => by simp [ForProg.exec]

lemma outputsAtMostOne_output (c : B) : (ForProg.output c : ForProg A B).OutputsAtMostOne :=
  fun _ _ _ => by simp [ForProg.exec]

lemma outputsAtMostOne_assign (i : ℕ) (v : Bool) :
    (ForProg.assign i v : ForProg A B).OutputsAtMostOne :=
  fun _ _ _ => by simp [ForProg.exec]

lemma outputsAtMostOne_ite (t : ForTest A) (P Q : ForProg A B) (hP : P.OutputsAtMostOne)
    (hQ : Q.OutputsAtMostOne) : (ForProg.ite t P Q).OutputsAtMostOne := by
  intro w pos bv
  simp only [ForProg.exec]
  split
  · exact hP w pos bv
  · exact hQ w pos bv

lemma outputsAtMostOne_renamePos (f : ℕ → ℕ) (P : ForProg A B) (hlf : P.LoopFree)
    (hP : P.OutputsAtMostOne) : (ForProg.renamePos f P).OutputsAtMostOne := by
  intro w pos bv
  rw [exec_renamePos w f P hlf pos bv]
  exact hP w _ bv

end ForProg

/-- The loop list of the merged nest: a fresh phase variable `pi` in front of the concatenation of
the two loop lists. -/
def mergeLoops (pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) : List (Bool × ℕ) := (true, pi) :: (L₁ ++ L₂)

/-- The body of the merged nest. -/
def mergeBody (zv lv pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B) : ForProg A B :=
  ForProg.ite (ForTest.and (ForTest.eqPos pi zv) (pinTest zv L₂)) b₁
    (ForProg.ite (ForTest.and (ForTest.eqPos pi lv) (pinTest zv L₁)) b₂ ForProg.skip)

/-- **Merging two nests of loops.**  With `zv` pointing at a position of the input and `lv` at a
later one, the nest `mergeLoops`/`mergeBody` computes the sequential composition of the two nests
it is built from.  Only the *order* of the two designated positions matters, so the same lemma
serves the prenex form of the book, where `zv` and `lv` hold the first and the last position, and
the *forward* prenex form of Exercise `exer:forward-for-transducer`, where they hold the first and
the second one. -/
lemma exec_merge (w : List A) (zv lv pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B)
    (pos : ℕ → ℕ) (bv : ℕ → Bool)
    (hzv : pos zv < pos lv) (hlv : pos lv < w.length)
    (hpiz : pi ≠ zv) (hpil : pi ≠ lv)
    (hpiL : pi ∉ (L₁ ++ L₂).map Prod.snd)
    (hpib₁ : pi ∉ b₁.posVars) (hpib₂ : pi ∉ b₂.posVars)
    (hzL : zv ∉ (L₁ ++ L₂).map Prod.snd) (hlL : lv ∉ (L₁ ++ L₂).map Prod.snd)
    (hnd₁ : (L₁.map Prod.snd).Nodup) (hnd₂ : (L₂.map Prod.snd).Nodup)
    (hb₁ : ∀ y ∈ L₂.map Prod.snd, y ∉ b₁.posVars)
    (hb₂ : ∀ y ∈ L₁.map Prod.snd, y ∉ L₂.map Prod.snd ∧ y ∉ b₂.posVars) :
    ForProg.exec w (ForProg.nestLoops (mergeLoops pi L₁ L₂)
        (mergeBody zv lv pi L₁ L₂ b₁ b₂)) pos bv
      = ForProg.exec w (ForProg.seq (ForProg.nestLoops L₁ b₁) (ForProg.nestLoops L₂ b₂)) pos bv := by
  set n := w.length with hnw
  set M : List (Bool × ℕ) := L₁ ++ L₂ with hM
  set body : ForProg A B := mergeBody zv lv pi L₁ L₂ b₁ b₂ with hbody
  have hzL₁ : zv ∉ L₁.map Prod.snd := fun h => hzL (by simp [hM, h])
  have hzL₂ : zv ∉ L₂.map Prod.snd := fun h => hzL (by simp [hM, h])
  -- the value of `pi`, `zv`, `lv` is not touched by the tuples of `M`
  have hset : ∀ (t : List ℕ) (p : ℕ) (i : ℕ), i ∉ M.map Prod.snd →
      setTuple M t (Function.update pos pi p) i = Function.update pos pi p i :=
    fun t p i hi => setTuple_of_not_mem M t _ hi
  have hloop : ForProg.exec w (ForProg.nestLoops (mergeLoops pi L₁ L₂) body) pos bv
      = runList (fun s p => ForProg.exec w (ForProg.nestLoops M body)
          (Function.update pos pi p) s) (List.range n) bv := by
    show ForProg.exec w (ForProg.loop true pi (ForProg.nestLoops M body)) pos bv = _
    rw [ForProg.exec]
    simp only [if_true, forLoopRun_eq_runList, hnw]
  -- iterations other than the two designated ones do nothing
  have hdead : ∀ p, p < n → ¬ (p = pos zv ∨ p = pos lv) → ∀ s,
      ForProg.exec w (ForProg.nestLoops M body) (Function.update pos pi p) s = (s, []) := by
    intro p _ hp s
    refine nest_noop w M body _ s (fun t => ?_)
    have hpi : setTuple M t (Function.update pos pi p) pi = p := by
      rw [hset t p pi hpiL, Function.update_self]
    have hz : setTuple M t (Function.update pos pi p) zv = pos zv := by
      rw [hset t p zv hzL, Function.update_of_ne (Ne.symm hpiz)]
    have hl : setTuple M t (Function.update pos pi p) lv = pos lv := by
      rw [hset t p lv hlL, Function.update_of_ne (Ne.symm hpil)]
    simp only [hbody, mergeBody, ForProg.exec]
    rw [if_neg, if_neg]
    · rintro ⟨h1, -⟩
      simp only [ForTest.Holds] at h1
      exact hp (Or.inr (by rw [hpi, hl] at h1; exact h1))
    · rintro ⟨h1, -⟩
      simp only [ForTest.Holds] at h1
      exact hp (Or.inl (by rw [hpi, hz] at h1; exact h1))
  -- the iteration at `pos zv` runs the first nest
  have hfirst : ∀ s, ForProg.exec w (ForProg.nestLoops M body) (Function.update pos pi (pos zv)) s
      = ForProg.exec w (ForProg.nestLoops L₁ b₁) pos s := by
    intro s
    have hpi : Function.update pos pi (pos zv) pi = pos zv := Function.update_self _ _ _
    have hz : Function.update pos pi (pos zv) zv = pos zv :=
      Function.update_of_ne (Ne.symm hpiz) _ _
    have hl : Function.update pos pi (pos zv) lv = pos lv :=
      Function.update_of_ne (Ne.symm hpil) _ _
    have hcongr : ForProg.exec w (ForProg.nestLoops M body) (Function.update pos pi (pos zv)) s
        = ForProg.exec w (ForProg.nestLoops M (ForProg.ite (pinTest zv L₂) b₁ ForProg.skip))
            (Function.update pos pi (pos zv)) s := by
      refine nest_congr w M body _ _ s (fun _ => True) trivial (fun t s' _ => ?_)
        (fun _ _ _ => trivial)
      have hpi' : setTuple M t (Function.update pos pi (pos zv)) pi = pos zv := by
        rw [hset t (pos zv) pi hpiL, hpi]
      have hz' : setTuple M t (Function.update pos pi (pos zv)) zv = pos zv := by
        rw [hset t (pos zv) zv hzL, hz]
      have hl' : setTuple M t (Function.update pos pi (pos zv)) lv = pos lv := by
        rw [hset t (pos zv) lv hlL, hl]
      simp only [hbody, mergeBody, ForProg.exec, ForTest.Holds]
      by_cases hpin : ForTest.Holds w (setTuple M t (Function.update pos pi (pos zv))) s'
          (pinTest zv L₂ : ForTest A)
      · rw [if_pos ⟨by rw [hpi', hz'], hpin⟩, if_pos hpin]
      · rw [if_neg (fun h => hpin h.2), if_neg hpin, if_neg]
        rintro ⟨h1, -⟩
        rw [hpi', hl'] at h1
        omega
    rw [hcongr, hM, nest_pin_inner w zv L₁ L₂ b₁ _ s (by rw [hz]; omega) hzL₁ hzL₂ hnd₂ hb₁]
    refine ForProg.exec_congr_pos w _ _ _ _ (fun i hi => ?_)
    rw [posVars_nestLoops] at hi
    have : i ≠ pi := by
      rintro rfl
      rcases List.mem_append.mp hi with h | h
      · exact hpiL (by simp [hM, h])
      · exact hpib₁ h
    exact Function.update_of_ne this _ _
  -- the iteration at `pos lv` runs the second nest
  have hlast : ∀ s, ForProg.exec w (ForProg.nestLoops M body) (Function.update pos pi (pos lv)) s
      = ForProg.exec w (ForProg.nestLoops L₂ b₂) pos s := by
    intro s
    have hpi : Function.update pos pi (pos lv) pi = pos lv := Function.update_self _ _ _
    have hz : Function.update pos pi (pos lv) zv = pos zv :=
      Function.update_of_ne (Ne.symm hpiz) _ _
    have hl : Function.update pos pi (pos lv) lv = pos lv :=
      Function.update_of_ne (Ne.symm hpil) _ _
    have hcongr : ForProg.exec w (ForProg.nestLoops M body) (Function.update pos pi (pos lv)) s
        = ForProg.exec w (ForProg.nestLoops M (ForProg.ite (pinTest zv L₁) b₂ ForProg.skip))
            (Function.update pos pi (pos lv)) s := by
      refine nest_congr w M body _ _ s (fun _ => True) trivial (fun t s' _ => ?_)
        (fun _ _ _ => trivial)
      have hpi' : setTuple M t (Function.update pos pi (pos lv)) pi = pos lv := by
        rw [hset t (pos lv) pi hpiL, hpi]
      have hz' : setTuple M t (Function.update pos pi (pos lv)) zv = pos zv := by
        rw [hset t (pos lv) zv hzL, hz]
      have hl' : setTuple M t (Function.update pos pi (pos lv)) lv = pos lv := by
        rw [hset t (pos lv) lv hlL, hl]
      simp only [hbody, mergeBody, ForProg.exec, ForTest.Holds]
      rw [if_neg]
      · by_cases hpin : ForTest.Holds w (setTuple M t (Function.update pos pi (pos lv))) s'
            (pinTest zv L₁ : ForTest A)
        · rw [if_pos ⟨by rw [hpi', hl'], hpin⟩, if_pos hpin]
        · rw [if_neg (fun h => hpin h.2), if_neg hpin]
      · rintro ⟨h1, -⟩
        rw [hpi', hz'] at h1
        omega
    rw [hcongr, hM, nest_pin_outer w zv L₁ L₂ b₂ _ s (by rw [hz]; omega) hzL₁ hzL₂ hnd₁ hb₂]
    refine ForProg.exec_congr_pos w _ _ _ _ (fun i hi => ?_)
    rw [posVars_nestLoops] at hi
    have : i ≠ pi := by
      rintro rfl
      rcases List.mem_append.mp hi with h | h
      · exact hpiL (by simp [hM, h])
      · exact hpib₂ h
    exact Function.update_of_ne this _ _
  -- put the three parts together
  have hfilter : (List.range n).filter (fun p => decide (p = pos zv ∨ p = pos lv))
      = [pos zv, pos lv] :=
    filter_range_pair n (pos zv) (pos lv) (by omega) (by omega) _ (fun x _ => by simp)
  rw [hloop, runList_filter _ (fun p => decide (p = pos zv ∨ p = pos lv)) _ _
    (fun p hp hpf s => hdead p (List.mem_range.mp hp) (by simpa using hpf) s), hfilter]
  rw [runList_cons, runList_cons, runList_nil, hfirst, hlast]
  simp [ForProg.exec]

/-! ## The syntax of the merged nest -/

lemma boolVars_pinTest (z : ℕ) (L : List (Bool × ℕ)) :
    (pinTest z L : ForTest A).boolVars = [] := by
  induction L with
  | nil => rfl
  | cons a L ih => obtain ⟨d, y⟩ := a; simp [pinTest_cons, ForTest.boolVars, ih]

lemma posVars_mergeBody (zv lv pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B) :
    (mergeBody zv lv pi L₁ L₂ b₁ b₂).posVars ⊆
      pi :: zv :: lv :: (L₁.map Prod.snd ++ L₂.map Prod.snd ++ b₁.posVars ++ b₂.posVars) := by
  intro i hi
  have key : ∀ L : List (Bool × ℕ), i ∈ (pinTest zv L : ForTest A).posVars →
      i = zv ∨ i ∈ L.map Prod.snd := by
    intro L h
    simpa using posVars_pinTest (A := A) zv L h
  have h₁ := key L₁
  have h₂ := key L₂
  simp only [mergeBody, ForProg.posVars, ForTest.posVars, List.append_assoc, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  simp only [List.mem_cons, List.mem_append]
  tauto

lemma boolVars_mergeBody (zv lv pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B) :
    (mergeBody zv lv pi L₁ L₂ b₁ b₂).boolVars = b₁.boolVars ++ b₂.boolVars := by
  simp [mergeBody, ForProg.boolVars, ForTest.boolVars, boolVars_pinTest]

lemma loopFree_mergeBody (zv lv pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B)
    (h₁ : b₁.LoopFree) (h₂ : b₂.LoopFree) : (mergeBody zv lv pi L₁ L₂ b₁ b₂).LoopFree :=
  ⟨h₁, h₂, trivial⟩

lemma outputsAtMostOne_mergeBody (zv lv pi : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B)
    (h₁ : b₁.OutputsAtMostOne) (h₂ : b₂.OutputsAtMostOne) :
    (mergeBody zv lv pi L₁ L₂ b₁ b₂).OutputsAtMostOne :=
  ForProg.outputsAtMostOne_ite _ _ _ h₁
    (ForProg.outputsAtMostOne_ite _ _ _ h₂ ForProg.outputsAtMostOne_skip)

end Lax194892Proofs.Transducers
