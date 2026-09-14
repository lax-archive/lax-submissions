/-
Part D: for-transducers -- assembling the prenex form, Lemma `lemma:prenex-normal-form`.

`Transducers.trFor` simulates a for-program by a single nest of loops, but only on inputs of
length at least two, and only once two designated position variables hold the first and the last
position of the input.  Here those two variables are bound by two extra outermost loops, whose
*first* iteration -- selected by a Boolean flag that is raised at the end of it -- is the one that
does the work; and the inputs of length at most one, on which the nest does nothing, are dealt
with by the epilogue, which is allowed by Definition `def:prenex-normal-form-for-transducers` and
is exactly what the book uses it for.
-/
import Lax194892Proofs.Source.PartD.ForPrenex

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B : Type}

/-! ## A bound on the variables of a program -/

/-- The largest element of a list of natural numbers. -/
def maxList : List ℕ → ℕ
  | [] => 0
  | a :: l => max a (maxList l)

lemma le_maxList : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ maxList l := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)

/-! ## A program only depends on the Boolean variables it mentions -/

/-- Two runs of a program from states that agree on a set of variables containing all the
variables of the program produce the same output and stay in agreement. -/
lemma exec_congr_bv (w : List A) : ∀ (P : ForProg A B) (pos : ℕ → ℕ) (S : ℕ → Prop),
    (∀ i ∈ P.boolVars, S i) → ∀ bv bv' : ℕ → Bool, (∀ i, S i → bv i = bv' i) →
      (ForProg.exec w P pos bv).2 = (ForProg.exec w P pos bv').2 ∧
        ∀ i, S i → (ForProg.exec w P pos bv).1 i = (ForProg.exec w P pos bv').1 i := by
  intro P
  induction P with
  | skip => intro pos S hS bv bv' h; exact ⟨rfl, fun i hi => h i hi⟩
  | output c => intro pos S hS bv bv' h; exact ⟨rfl, fun i hi => h i hi⟩
  | assign j v =>
      intro pos S hS bv bv' h
      refine ⟨rfl, fun i hi => ?_⟩
      show Function.update bv j v i = Function.update bv' j v i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, h i hi]
  | seq P Q ihP ihQ =>
      intro pos S hS bv bv' h
      have hSP : ∀ i ∈ P.boolVars, S i := fun i hi => hS i (by simp [ForProg.boolVars, hi])
      have hSQ : ∀ i ∈ Q.boolVars, S i := fun i hi => hS i (by simp [ForProg.boolVars, hi])
      obtain ⟨e₁, e₂⟩ := ihP pos S hSP bv bv' h
      obtain ⟨f₁, f₂⟩ := ihQ pos S hSQ _ _ e₂
      exact ⟨by show _ ++ _ = _ ++ _; rw [e₁, f₁], f₂⟩
  | ite t P Q ihP ihQ =>
      intro pos S hS bv bv' h
      have hSP : ∀ i ∈ P.boolVars, S i := fun i hi => hS i (by simp [ForProg.boolVars, hi])
      have hSQ : ∀ i ∈ Q.boolVars, S i := fun i hi => hS i (by simp [ForProg.boolVars, hi])
      have ht : ForTest.Holds w pos bv t ↔ ForTest.Holds w pos bv' t :=
        ForTest.holds_congr w t pos pos bv bv' (fun _ _ => rfl)
          (fun i hi => h i (hS i (by simp [ForProg.boolVars, hi])))
      simp only [ForProg.exec]
      by_cases hT : ForTest.Holds w pos bv t
      · rw [if_pos hT, if_pos (ht.mp hT)]
        exact ihP pos S hSP bv bv' h
      · rw [if_neg hT, if_neg (fun hc => hT (ht.mpr hc))]
        exact ihQ pos S hSQ bv bv' h
  | loop d x P ih =>
      intro pos S hS bv bv' h
      simp only [ForProg.exec, forLoopRun_eq_runList]
      refine runList_sim _ _ (fun s s' => ∀ i, S i → s i = s' i) _ bv bv' h
        (fun s s' p _ hR => ?_)
      exact ih (Function.update pos x p) S hS s s' hR

/-! ## The epilogue: simulating a program on an input of length at most one -/

/-- The epilogue of the prenex form: a loop-free program that runs the loops of `P` once if the
Boolean variable `G` is true, and not at all otherwise.  On an input of length at most one, and
with `G` saying whether the input is nonempty, it computes the same as `P`. -/
def shortSim (G : ℕ) : ForProg A B → ForProg A B
  | ForProg.skip => ForProg.skip
  | ForProg.output c => ForProg.output c
  | ForProg.assign i v => ForProg.assign i v
  | ForProg.seq P Q => ForProg.seq (shortSim G P) (shortSim G Q)
  | ForProg.ite t P Q => ForProg.ite t (shortSim G P) (shortSim G Q)
  | ForProg.loop _ _ P => ForProg.ite (ForTest.boolVar G) (shortSim G P) ForProg.skip

lemma loopFree_shortSim (G : ℕ) : ∀ P : ForProg A B, (shortSim G P).LoopFree := by
  intro P
  induction P with
  | skip => trivial
  | output c => trivial
  | assign i v => trivial
  | seq P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | ite t P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | loop d x P ih => exact ⟨ih, trivial⟩

lemma shortSim_spec (G : ℕ) (w : List A) (hn : w.length ≤ 1) (pos : ℕ → ℕ)
    (hpos : ∀ x, pos x = 0) :
    ∀ (P : ForProg A B), G ∉ P.boolVars → ∀ s : ℕ → Bool, (s G = true ↔ 0 < w.length) →
      ForProg.exec w (shortSim G P) pos s = ForProg.exec w P pos s := by
  intro P
  induction P with
  | skip => intro _ s _; rfl
  | output c => intro _ s _; rfl
  | assign i v => intro _ s _; rfl
  | seq P Q ihP ihQ =>
      intro hG s hs
      have hGP : G ∉ P.boolVars := fun h => hG (by simp [ForProg.boolVars, h])
      have hGQ : G ∉ Q.boolVars := fun h => hG (by simp [ForProg.boolVars, h])
      have h₁ := ihP hGP s hs
      have hGs : (ForProg.exec w P pos s).1 G = s G :=
        ForProg.exec_bv_unchanged w P pos s hGP
      simp only [shortSim, ForProg.exec, h₁]
      rw [ihQ hGQ _ (by rw [hGs]; exact hs)]
  | ite t P Q ihP ihQ =>
      intro hG s hs
      have hGP : G ∉ P.boolVars := fun h => hG (by simp [ForProg.boolVars, h])
      have hGQ : G ∉ Q.boolVars := fun h => hG (by simp [ForProg.boolVars, h])
      simp only [shortSim, ForProg.exec, ihP hGP s hs, ihQ hGQ s hs]
  | loop d x P ih =>
      intro hG s hs
      have hGP : G ∉ P.boolVars := by simpa [ForProg.boolVars] using hG
      have hupd : Function.update pos x 0 = pos := by
        funext y
        by_cases hy : y = x
        · subst hy; simp [hpos]
        · simp [Function.update_of_ne hy]
      rcases Nat.lt_or_ge 0 w.length with hpos' | hzero
      · -- the input has exactly one letter
        have hlen : w.length = 1 := by omega
        have hrange : (if d then List.range w.length else (List.range w.length).reverse) = [0] := by
          cases d <;> simp [hlen]
        simp only [shortSim, ForProg.exec, ForTest.Holds, if_pos (hs.mpr hpos'), ih hGP s hs,
          hrange, forLoopRun, hupd]
        simp
      · -- the input is empty
        have hlen : w.length = 0 := by omega
        have hrange : (if d then List.range w.length else (List.range w.length).reverse) = [] := by
          cases d <;> simp [hlen]
        have hsG : ¬ (s G = true) := by
          intro h
          have := hs.mp h
          omega
        simp only [shortSim, ForProg.exec, ForTest.Holds, if_neg hsG, hrange, forLoopRun]

/-! ## Tuples of an input of length one -/

lemma tuplesOf_one (L : List (Bool × ℕ)) : tuplesOf L 1 = [L.map (fun _ => 0)] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      have hr : loopRange d 1 = [0] := by cases d <;> simp [loopRange]
      rw [tuplesOf_cons, hr, ih]
      simp

lemma setTuple_zero (L : List (Bool × ℕ)) (pos : ℕ → ℕ) (hpos : ∀ x, pos x = 0) :
    setTuple L (L.map (fun _ => 0)) pos = pos := by
  induction L generalizing pos with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      have hupd : Function.update pos x 0 = pos := by
        funext y
        by_cases hy : y = x
        · subst hy; simp [hpos]
        · simp [Function.update_of_ne hy]
      simp only [List.map_cons, setTuple_cons, hupd]
      exact ih pos hpos


/-! ## The body of the single nest of loops -/

/-- The body of the single nest of loops of the prenex form.  The variable `g` is the innermost
of the three extra loops, `dn` is the flag saying that the work is over, and `G` and `H` tell the
epilogue whether the input has exactly one letter, respectively at least two letters.

While `dn` is false, the body runs the translated body `b` at the iterations with `g = zv` -- and
only if the input has at least two letters, that is, if `zv ≠ lv` -- and at the last iteration
`g = lv` it raises the appropriate flag and sets `dn`. -/
def prenexBody (zv lv g dn G H : ℕ) (b : ForProg A B) : ForProg A B :=
  ForProg.ite
    (ForTest.and (ForTest.and (ForTest.not (ForTest.boolVar dn)) (ForTest.eqPos g zv))
      (ForTest.not (ForTest.eqPos zv lv))) b
    (ForProg.ite (ForTest.and (ForTest.eqPos g lv) (ForTest.not (ForTest.boolVar dn)))
      (ForProg.ite (ForTest.eqPos zv lv)
        (ForProg.seq (ForProg.assign G true) (ForProg.assign dn true))
        (ForProg.seq (ForProg.assign H true) (ForProg.assign dn true)))
      ForProg.skip)

lemma loopFree_prenexBody (zv lv g dn G H : ℕ) (b : ForProg A B) (hb : b.LoopFree) :
    (prenexBody zv lv g dn G H b).LoopFree :=
  ⟨hb, ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, trivial⟩⟩

lemma outputsAtMostOne_prenexBody (zv lv g dn G H : ℕ) (b : ForProg A B)
    (hb : b.OutputsAtMostOne) : (prenexBody zv lv g dn G H b).OutputsAtMostOne := by
  intro w pos bv
  simp only [prenexBody, ForProg.exec]
  split
  · exact hb w pos bv
  · split
    · split <;> simp
    · simp

/-- Once the flag `dn` is up, the body does nothing. -/
lemma exec_prenexBody_dead (w : List A) (zv lv g dn G H : ℕ) (b : ForProg A B) (pos : ℕ → ℕ)
    (s : ℕ → Bool) (hs : s dn = true) :
    ForProg.exec w (prenexBody zv lv g dn G H b) pos s = (s, []) := by
  simp [prenexBody, ForProg.exec, ForTest.Holds, hs]

/-- At an iteration where `g` is neither `zv` nor `lv`, the body does nothing. -/
lemma exec_prenexBody_skip (w : List A) (zv lv g dn G H : ℕ) (b : ForProg A B) (pos : ℕ → ℕ)
    (s : ℕ → Bool) (h1 : pos g ≠ pos zv) (h2 : pos g ≠ pos lv) :
    ForProg.exec w (prenexBody zv lv g dn G H b) pos s = (s, []) := by
  simp [prenexBody, ForProg.exec, ForTest.Holds, h1, h2]

/-- Once the flag `dn` is up, a whole nest of loops over the body does nothing. -/
lemma exec_nest_prenexBody_dead (w : List A) (zv lv g dn G H : ℕ) (b : ForProg A B)
    (L : List (Bool × ℕ)) (pos : ℕ → ℕ) (s : ℕ → Bool) (hs : s dn = true) :
    ForProg.exec w (ForProg.nestLoops L (prenexBody zv lv g dn G H b)) pos s = (s, []) :=
  nest_noop w L _ pos s (fun _ => exec_prenexBody_dead w zv lv g dn G H b _ s hs)

/-- Peeling off the outermost loop of a nest. -/
lemma exec_nest_cons (w : List A) (d : Bool) (x : ℕ) (L : List (Bool × ℕ)) (body : ForProg A B)
    (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForProg.exec w (ForProg.nestLoops ((d, x) :: L) body) pos bv
      = runList (fun s p => ForProg.exec w (ForProg.nestLoops L body) (Function.update pos x p) s)
          (loopRange d w.length) bv := by
  rw [ForProg.nestLoops]
  simp only [ForProg.exec, forLoopRun_eq_runList, loopRange]

lemma runList_one {α S C : Type} (step : S → α → S × List C) (a : α) (s : S) :
    runList step [a] s = step s a := by
  rw [runList_cons]
  show ((step s a).1, (step s a).2 ++ []) = step s a
  simp

lemma runList_two {α S C : Type} (step : S → α → S × List C) (a₁ a₂ : α) (s : S) :
    runList step [a₁, a₂] s =
      ((step (step s a₁).1 a₂).1, (step s a₁).2 ++ (step (step s a₁).1 a₂).2) := by
  rw [runList_cons, runList_one]


lemma runList_head_dead {α S C : Type} (step : S → α → S × List C) (a : α) (as : List α) (s : S)
    (hdead : ∀ t ∈ as, step (step s a).1 t = ((step s a).1, [])) :
    runList step (a :: as) s = step s a := by
  rw [runList_cons, runList_noop step as (step s a).1 hdead]
  simp

/-! ## The prenex form of a translated program -/

/-- **The nest of loops of the prenex form computes the program, on inputs of length at least
two.**  This is the heart of the prenex form: on such an input, the three extra loops let the nest
run the translated body once for every tuple, in the right state, and the flag `k' + 3` records
that this has happened, so that the epilogue does nothing. -/
theorem exec_nest_big (P : ForProg A B) (zv lv k₀ : ℕ) (L : List (Bool × ℕ)) (b : ForProg A B)
    (k' : ℕ) (hzv : zv < k₀) (hzl : zv < lv) (hlv : lv < k₀)
    (hPpos : ∀ i ∈ P.posVars, i < zv) (hPbool : ∀ i ∈ P.boolVars, i < zv)
    (htr : trFor zv lv P k₀ = (L, b, k')) (w : List A) (hbig : 2 ≤ w.length) :
    ∃ s : ℕ → Bool, s (k' + 3) = true ∧
      ForProg.exec w (ForProg.nestLoops ((true, zv) :: (false, lv) :: (true, k') :: L)
          (prenexBody zv lv k' (k' + 1) (k' + 2) (k' + 3) b)) (fun _ => 0) (fun _ => false)
        = (s, (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
  classical
  have ok : TrOk zv lv P k₀ L b k' := trFor_ok zv lv P k₀ L b k' htr
  have hk : k₀ ≤ k' := ok.mono
  have hz : zv ∉ P.posVars := fun h => by have := hPpos zv h; omega
  have hl : lv ∉ P.posVars := fun h => by have := hPpos lv h; omega
  have hPpos' : ∀ i ∈ P.posVars, i < k₀ := fun i hi => by have := hPpos i hi; omega
  have hPbool' : ∀ i ∈ P.boolVars, i < k₀ := fun i hi => by have := hPbool i hi; omega
  have hbbool : ∀ i ∈ b.boolVars, i < k' := by
    intro i hi
    rcases ok.boolOk i hi with h | h
    · have := hPbool' i h; omega
    · omega
  have hbdn : (k' + 1) ∉ b.boolVars := fun h => by have := hbbool _ h; omega
  have hbH : (k' + 3) ∉ b.boolVars := fun h => by have := hbbool _ h; omega
  have hGP : (k' + 2) ∉ P.boolVars := fun h => by have := hPbool' _ h; omega
  have hnotL : ∀ i : ℕ, (i < k₀ ∨ k' ≤ i) → i ∉ L.map Prod.snd := by
    intro i hi hmem
    have := ok.loopRange i hmem
    omega
  set body : ForProg A B := prenexBody zv lv k' (k' + 1) (k' + 2) (k' + 3) b with hbodydef
  set FL : List (Bool × ℕ) := (true, zv) :: (false, lv) :: (true, k') :: L with hFLdef
  have hn0 : 0 < w.length := by omega
  set p2 : ℕ → ℕ := Function.update (fun _ : ℕ => 0) lv (w.length - 1) with hp2def
  have hp2z : p2 zv = 0 := by rw [hp2def, Function.update_of_ne (by omega)]
  have hp2l : p2 lv = w.length - 1 := by rw [hp2def, Function.update_self]
  -- the values of the position variables inside the nest
  have hset : ∀ (t : List ℕ) (gg i : ℕ), (i < k₀ ∨ k' ≤ i) →
      setTuple L t (Function.update p2 k' gg) i = Function.update p2 k' gg i :=
    fun t gg i hi => setTuple_of_not_mem L t _ (hnotL i hi)
  have hsz : ∀ (t : List ℕ) (gg : ℕ), setTuple L t (Function.update p2 k' gg) zv = 0 := by
    intro t gg
    rw [hset t gg zv (Or.inl hzv), Function.update_of_ne (by omega), hp2z]
  have hsl : ∀ (t : List ℕ) (gg : ℕ),
      setTuple L t (Function.update p2 k' gg) lv = w.length - 1 := by
    intro t gg
    rw [hset t gg lv (Or.inl hlv), Function.update_of_ne (by omega), hp2l]
  have hsg : ∀ (t : List ℕ) (gg : ℕ), setTuple L t (Function.update p2 k' gg) k' = gg := by
    intro t gg
    rw [hset t gg k' (Or.inr le_rfl), Function.update_self]
  -- at an iteration with `g` neither first nor last, the nest does nothing
  have hbad : ∀ gg : ℕ, gg ≠ 0 → gg ≠ w.length - 1 → ∀ s : ℕ → Bool,
      ForProg.exec w (ForProg.nestLoops L body) (Function.update p2 k' gg) s = (s, []) := by
    intro gg h1 h2 s
    refine nest_noop w L body _ s (fun t => ?_)
    exact exec_prenexBody_skip w zv lv k' (k' + 1) (k' + 2) (k' + 3) b _ s
      (by rw [hsg t gg, hsz t gg]; exact h1) (by rw [hsg t gg, hsl t gg]; exact h2)
  -- the iteration with `g` first: the nest computes what `P` computes
  have hguard : ∀ (t : List ℕ) (s : ℕ → Bool), s (k' + 1) = false →
      ForProg.exec w body (setTuple L t (Function.update p2 k' 0)) s
        = ForProg.exec w b (setTuple L t (Function.update p2 k' 0)) s := by
    intro t s hs
    rw [hbodydef, prenexBody]
    refine exec_ite_pos _ _ _ _ _ _ ⟨⟨?_, ?_⟩, ?_⟩
    · show ¬ (s (k' + 1) = true)
      rw [hs]; simp
    · show setTuple L t (Function.update p2 k' 0) k' = setTuple L t (Function.update p2 k' 0) zv
      rw [hsg t 0, hsz t 0]
    · show ¬ (setTuple L t (Function.update p2 k' 0) zv
        = setTuple L t (Function.update p2 k' 0) lv)
      rw [hsz t 0, hsl t 0]; omega
  have hcongr : ForProg.exec w (ForProg.nestLoops L body) (Function.update p2 k' 0)
        (fun _ => false)
      = ForProg.exec w (ForProg.nestLoops L b) (Function.update p2 k' 0) (fun _ => false) := by
    refine nest_congr w L body b _ (fun _ => false) (fun s => s (k' + 1) = false) rfl hguard ?_
    intro t s hs
    rw [hguard t s hs, ForProg.exec_bv_unchanged w b _ s hbdn]
    exact hs
  have hspec := trFor_spec zv lv k₀ hzv hlv w P hPpos' hPbool' hz hl k₀ L b k' htr le_rfl
    (Function.update p2 k' 0)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hp2z, hp2l]; omega)
    (by rw [Function.update_of_ne (by omega), hp2l]; omega) (fun _ => false) (fun _ => false)
    (fun _ _ => rfl)
  have hposP : ForProg.exec w P (Function.update p2 k' 0) (fun _ => false)
      = ForProg.exec w P (fun _ => 0) (fun _ => false) := by
    refine ForProg.exec_congr_pos w P _ _ _ (fun i hi => ?_)
    have h1 : i < k₀ := hPpos' i hi
    have h2 : i < zv := hPpos i hi
    rw [Function.update_of_ne (by omega), hp2def, Function.update_of_ne (by omega)]
  have hstep0 : ForProg.exec w (ForProg.nestLoops L body) (Function.update p2 k' 0)
        (fun _ => false)
      = ((ForProg.exec w (ForProg.nestLoops L b) (Function.update p2 k' 0) (fun _ => false)).1,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    rw [hcongr]
    refine Prod.ext rfl ?_
    rw [hspec.1, hposP]
  set s₄ : ℕ → Bool :=
    (ForProg.exec w (ForProg.nestLoops L b) (Function.update p2 k' 0) (fun _ => false)).1
    with hs4def
  have hs4dn : s₄ (k' + 1) = false := by
    rw [hs4def]
    exact nest_bv_fix w L b _ _ (k' + 1)
      (fun t s => ForProg.exec_bv_unchanged w b _ s hbdn)
  have hs4H : s₄ (k' + 3) = false := by
    rw [hs4def]
    exact nest_bv_fix w L b _ _ (k' + 3)
      (fun t s => ForProg.exec_bv_unchanged w b _ s hbH)
  -- the iteration with `g` last: the flags are raised
  have hkill : ∀ (t : List ℕ) (s : ℕ → Bool), s (k' + 1) = false →
      ForProg.exec w body (setTuple L t (Function.update p2 k' (w.length - 1))) s
        = (Function.update (Function.update s (k' + 3) true) (k' + 1) true, []) := by
    intro t s hs
    rw [hbodydef, prenexBody]
    rw [exec_ite_neg _ _ _ _ _ _ ?_, exec_ite_pos _ _ _ _ _ _ ?_, exec_ite_neg _ _ _ _ _ _ ?_]
    · show ((ForProg.exec w (ForProg.assign (k' + 1) true) _
        (Function.update s (k' + 3) true)).1, _) = _
      simp [ForProg.exec]
    · show ¬ (setTuple L t (Function.update p2 k' (w.length - 1)) zv
        = setTuple L t (Function.update p2 k' (w.length - 1)) lv)
      rw [hsz t _, hsl t _]; omega
    · exact ⟨by
        show setTuple L t (Function.update p2 k' (w.length - 1)) k'
          = setTuple L t (Function.update p2 k' (w.length - 1)) lv
        rw [hsg t _, hsl t _], by show ¬ (s (k' + 1) = true); rw [hs]; simp⟩
    · rintro ⟨⟨-, h2⟩, -⟩
      have h2' : setTuple L t (Function.update p2 k' (w.length - 1)) k'
          = setTuple L t (Function.update p2 k' (w.length - 1)) zv := h2
      rw [hsg t _, hsz t _] at h2'
      omega
  have hstep1 : ForProg.exec w (ForProg.nestLoops L body)
        (Function.update p2 k' (w.length - 1)) s₄
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true, []) := by
    have hdead : ∀ (t : List ℕ) (s : ℕ → Bool), s (k' + 1) = true →
        ForProg.exec w body (setTuple L t (Function.update p2 k' (w.length - 1))) s
          = (s, []) := by
      intro t s hs
      rw [hbodydef]
      exact exec_prenexBody_dead w zv lv k' (k' + 1) (k' + 2) (k' + 3) b _ s hs
    rw [nest_kill w L body _ s₄ (fun s => s (k' + 1) = true) hn0 hdead
      (by rw [hkill _ s₄ hs4dn]; simp), hkill _ s₄ hs4dn]
  -- the loop on `g`
  have hg : ForProg.exec w (ForProg.nestLoops ((true, k') :: L) body) p2 (fun _ => false)
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    rw [exec_nest_cons, show loopRange true w.length = List.range w.length from rfl,
      runList_filter _ (fun x => decide (x = 0 ∨ x = w.length - 1)) _ _ ?_,
      filter_range_pair w.length 0 (w.length - 1) (by omega) (by omega) _ (by intro x hx; simp),
      runList_two]
    · simp only [hstep0, hstep1]
      simp
    · intro a _ ha s
      simp only [decide_eq_false_iff_not, not_or] at ha
      exact hbad a ha.1 ha.2 s
  -- the loop on `lv`
  have hlvloop : ForProg.exec w (ForProg.nestLoops ((false, lv) :: (true, k') :: L) body)
        (fun _ => 0) (fun _ => false)
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    obtain ⟨l₂, hl₂⟩ := loopRange_eq_cons (n := w.length) false hn0
    have hl₂' : loopRange false w.length = (w.length - 1) :: l₂ := by simpa using hl₂
    rw [exec_nest_cons, hl₂', runList_head_dead _ _ _ _ ?_]
    · rw [← hp2def] at *
      exact hg
    · intro t _
      rw [← hp2def, hg]
      exact exec_nest_prenexBody_dead w zv lv k' (k' + 1) (k' + 2) (k' + 3) b _ _ _ (by simp)
  -- the loop on `zv`
  have hzvloop : ForProg.exec w (ForProg.nestLoops FL body) (fun _ => 0) (fun _ => false)
      = (Function.update (Function.update s₄ (k' + 3) true) (k' + 1) true,
        (ForProg.exec w P (fun _ => 0) (fun _ => false)).2) := by
    obtain ⟨l₁, hl₁⟩ := loopRange_eq_cons (n := w.length) true hn0
    have hl₁' : loopRange true w.length = 0 :: l₁ := by simpa using hl₁
    have hupd0 : Function.update (fun _ : ℕ => 0) zv 0 = (fun _ : ℕ => 0) := by
      funext y
      by_cases hy : y = zv
      · subst hy; simp
      · simp [Function.update_of_ne hy]
    rw [hFLdef, exec_nest_cons, hl₁', runList_head_dead _ _ _ _ ?_]
    · simp only [hupd0]
      exact hlvloop
    · intro t _
      simp only [hupd0, hlvloop]
      exact exec_nest_prenexBody_dead w zv lv k' (k' + 1) (k' + 2) (k' + 3) b _ _ _ (by simp)
  exact ⟨_, by rw [Function.update_of_ne (by omega), Function.update_self], hzvloop⟩

/-- **The prenex form.**  Given the translation `Transducers.trFor` of a program `P` into a single
nest of loops, valid on the inputs of length at least two, one obtains a program in prenex form
equivalent to `P`: three extra loops bind the two designated variables `zv`, `lv` and a variable
`g` that separates the work (done at `g = zv`) from the raising of the flags (done at `g = lv`),
and the epilogue deals with the inputs of length at most one. -/
theorem prenex_of_trFor (P : ForProg A B) (zv lv k₀ : ℕ) (L : List (Bool × ℕ)) (b : ForProg A B)
    (k' : ℕ) (hzv : zv < k₀) (hzl : zv < lv) (hlv : lv < k₀)
    (hPpos : ∀ i ∈ P.posVars, i < zv) (hPbool : ∀ i ∈ P.boolVars, i < zv)
    (htr : trFor zv lv P k₀ = (L, b, k')) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w := by
  classical
  have ok : TrOk zv lv P k₀ L b k' := trFor_ok zv lv P k₀ L b k' htr
  have hk : k₀ ≤ k' := ok.mono
  have hz : zv ∉ P.posVars := fun h => by have := hPpos zv h; omega
  have hl : lv ∉ P.posVars := fun h => by have := hPpos lv h; omega
  have hPpos' : ∀ i ∈ P.posVars, i < k₀ := fun i hi => by have := hPpos i hi; omega
  have hPbool' : ∀ i ∈ P.boolVars, i < k₀ := fun i hi => by have := hPbool i hi; omega
  have hbbool : ∀ i ∈ b.boolVars, i < k' := by
    intro i hi
    rcases ok.boolOk i hi with h | h
    · have := hPbool' i h; omega
    · omega
  have hbdn : (k' + 1) ∉ b.boolVars := fun h => by have := hbbool _ h; omega
  have hbH : (k' + 3) ∉ b.boolVars := fun h => by have := hbbool _ h; omega
  have hGP : (k' + 2) ∉ P.boolVars := fun h => by have := hPbool' _ h; omega
  have hnotL : ∀ i : ℕ, (i < k₀ ∨ k' ≤ i) → i ∉ L.map Prod.snd := by
    intro i hi hmem
    have := ok.loopRange i hmem
    omega
  set body : ForProg A B := prenexBody zv lv k' (k' + 1) (k' + 2) (k' + 3) b with hbodydef
  set FL : List (Bool × ℕ) := (true, zv) :: (false, lv) :: (true, k') :: L with hFLdef
  refine ⟨_, ⟨FL, body, ForProg.ite (ForTest.boolVar (k' + 3)) ForProg.skip (shortSim (k' + 2) P),
      loopFree_prenexBody _ _ _ _ _ _ b ok.loopFree, ⟨trivial, loopFree_shortSim _ P⟩,
      outputsAtMostOne_prenexBody _ _ _ _ _ _ b ok.out1, rfl⟩, ?_⟩
  intro w
  rw [ForProg.eval, exec_seq]
  by_cases hbig : 2 ≤ w.length
  · -- the input has at least two letters
    obtain ⟨s, hsH, hzvloop⟩ :=
      exec_nest_big P zv lv k₀ L b k' hzv hzl hlv hPpos hPbool htr w hbig
    have hsH' : ForTest.Holds w (fun _ => 0) s (ForTest.boolVar (k' + 3)) := hsH
    rw [hFLdef, hbodydef, hzvloop, exec_ite_pos _ _ _ _ _ _ hsH']
    simp [ForProg.exec, ForProg.eval]
  · -- the input has at most one letter
    have hshort : w.length ≤ 1 := by omega
    rcases Nat.lt_or_ge 0 w.length with h1 | h0
    · -- exactly one letter
      have hlen : w.length = 1 := by omega
      have hnest : ForProg.exec w (ForProg.nestLoops FL body) (fun _ => 0) (fun _ => false)
          = ForProg.exec w body (fun _ => 0) (fun _ => false) := by
        rw [exec_nestLoops, hlen, tuplesOf_one, runList_one]
        simp only [setTuple_zero FL _ (fun _ => rfl)]
      have hbody1 : ForProg.exec w body (fun _ => 0) (fun _ => false)
          = (Function.update (Function.update (fun _ : ℕ => false) (k' + 2) true) (k' + 1) true,
            []) := by
        have hg1 : ¬ ForTest.Holds w (fun _ : ℕ => 0) (fun _ : ℕ => false)
            (ForTest.and (ForTest.and (ForTest.not (ForTest.boolVar (k' + 1)))
              (ForTest.eqPos k' zv)) (ForTest.not (ForTest.eqPos zv lv))) := by
          rintro ⟨-, h⟩
          exact h rfl
        have hg2 : ForTest.Holds w (fun _ : ℕ => 0) (fun _ : ℕ => false)
            (ForTest.and (ForTest.eqPos k' lv) (ForTest.not (ForTest.boolVar (k' + 1)))) :=
          ⟨rfl, by simp [ForTest.Holds]⟩
        have hg3 : ForTest.Holds w (fun _ : ℕ => 0) (fun _ : ℕ => false)
            (ForTest.eqPos zv lv) := rfl
        rw [hbodydef, prenexBody, exec_ite_neg _ _ _ _ _ _ hg1, exec_ite_pos _ _ _ _ _ _ hg2,
          exec_ite_pos _ _ _ _ _ _ hg3]
        simp [ForProg.exec]
      rw [hnest, hbody1]
      have hH : ¬ ForTest.Holds w (fun _ => 0)
          (Function.update (Function.update (fun _ : ℕ => false) (k' + 2) true) (k' + 1) true)
          (ForTest.boolVar (k' + 3)) := by
        show ¬ (_ = true)
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        simp
      rw [exec_ite_neg _ _ _ _ _ _ hH]
      rw [shortSim_spec (k' + 2) w hshort _ (fun _ => rfl) P hGP _ ?_]
      · have hbv := exec_congr_bv w P (fun _ => 0) (fun i => i ∈ P.boolVars) (fun i hi => hi)
          (Function.update (Function.update (fun _ : ℕ => false) (k' + 2) true) (k' + 1) true)
          (fun _ => false) ?_
        · rw [hbv.1]
          simp [ForProg.eval]
        · intro i hi
          have := hPbool' i hi
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · rw [Function.update_of_ne (by omega), Function.update_self]
        simp [hlen]
    · -- no letters at all
      have hlen : w.length = 0 := by omega
      have hnest : ForProg.exec w (ForProg.nestLoops FL body) (fun _ => 0) (fun _ => false)
          = ((fun _ => false), []) := by
        rw [hFLdef, exec_nest_cons,
          show loopRange true w.length = [] by simp [loopRange, hlen]]
        rfl
      rw [hnest]
      rw [exec_ite_neg _ _ _ _ _ _ (by show ¬ (_ = true); simp)]
      rw [shortSim_spec (k' + 2) w hshort _ (fun _ => rfl) P hGP _ (by simp [hlen])]
      simp [ForProg.eval]


/-- **Lemma `lemma:prenex-normal-form`.**  Every for-transducer is equivalent to one in prenex
form.  This is the statement proved in `RequestProject/PartD/Statements.lean`; the fresh variables
used by the construction are chosen above every variable of the given program. -/
theorem forTransducer_prenex_aux (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w := by
  classical
  obtain ⟨L, b, k', htr⟩ : ∃ L b k',
      trFor (maxList (P.posVars ++ P.boolVars) + 1) (maxList (P.posVars ++ P.boolVars) + 2) P
        (maxList (P.posVars ++ P.boolVars) + 3) = (L, b, k') := ⟨_, _, _, rfl⟩
  exact prenex_of_trFor P _ _ _ L b k' (by omega) (by omega) (by omega)
    (fun i hi => by
      have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega)
    (fun i hi => by
      have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega) htr


/-- **Every for-program is computed by a single nest of loops on the inputs of length at least
two.**  The body of the nest is loop-free and produces at most one letter per iteration; the
inputs of length at most one, on which the nest produces nothing, are excluded -- on those a nest
of loops cannot produce the fixed output that a program may have.  This is the form of a
for-transducer used in the proof of Lemma `lem:for-closed-under-composition`. -/
theorem for_nest_form (P : ForProg A B) :
    ∃ (L : List (Bool × ℕ)) (p : ForProg A B), p.LoopFree ∧ p.OutputsAtMostOne ∧
      (L.map Prod.snd).Nodup ∧
      ∀ w : List A, 2 ≤ w.length →
        (ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2 = P.eval w := by
  classical
  obtain ⟨L, b, k', htr⟩ : ∃ L b k',
      trFor (maxList (P.posVars ++ P.boolVars) + 1) (maxList (P.posVars ++ P.boolVars) + 2) P
        (maxList (P.posVars ++ P.boolVars) + 3) = (L, b, k') := ⟨_, _, _, rfl⟩
  have hPpos : ∀ i ∈ P.posVars, i < maxList (P.posVars ++ P.boolVars) + 1 := fun i hi => by
    have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega
  have hPbool : ∀ i ∈ P.boolVars, i < maxList (P.posVars ++ P.boolVars) + 1 := fun i hi => by
    have := le_maxList (P.posVars ++ P.boolVars) i (by simp [hi]); omega
  have ok := trFor_ok _ _ P _ L b k' htr
  refine ⟨(true, maxList (P.posVars ++ P.boolVars) + 1) ::
      (false, maxList (P.posVars ++ P.boolVars) + 2) :: (true, k') :: L,
    prenexBody (maxList (P.posVars ++ P.boolVars) + 1) (maxList (P.posVars ++ P.boolVars) + 2)
      k' (k' + 1) (k' + 2) (k' + 3) b,
    loopFree_prenexBody _ _ _ _ _ _ b ok.loopFree,
    outputsAtMostOne_prenexBody _ _ _ _ _ _ b ok.out1, ?_, ?_⟩
  · have hmono := ok.mono
    have hrange := ok.loopRange
    simp only [List.map_cons, List.nodup_cons, List.mem_cons]
    refine ⟨?_, ?_, ?_, ok.nodup⟩
    · rintro (h | h | h)
      · omega
      · omega
      · have := hrange _ h; omega
    · rintro (h | h)
      · omega
      · have := hrange _ h; omega
    · intro h
      have := hrange _ h; omega
  intro w hbig
  obtain ⟨s, -, h⟩ := exec_nest_big P _ _ _ L b k' (by omega) (by omega) (by omega) hPpos hPbool
    htr w hbig
  rw [h]
  rfl

end Lax194892Proofs.Transducers
