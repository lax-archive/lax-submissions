/-
Part D: for-transducers -- manipulating nests of loops.

The tools with which the prenex form of Lemma `lemma:prenex-normal-form` is assembled.  A nest of
loops visits every tuple of positions once, in lexicographic order, so a *pinned* nest -- one whose
body is guarded by the test "all these loop variables are equal to `z`" -- runs its body exactly
once for every tuple of the *other* loop variables, in the same order.  This is what lets two nests
of loops be merged into one, which is the whole content of the prenex normal form.
-/
import Lax194892Proofs.Source.PartD.ForSem

namespace Lax194892Proofs.Transducers

open scoped Classical

/-! ## Generic folds, continued -/

section Generic

variable {α S B : Type}

/-- Two bodies that agree on the states satisfying an invariant give the same fold. -/
lemma runList_congr (step₁ step₂ : S → α → S × List B) (Φ : S → Prop) (as : List α) (s : S)
    (hs : Φ s) (h : ∀ t a, Φ t → step₁ t a = step₂ t a) (hinv : ∀ t a, Φ t → Φ (step₁ t a).1) :
    runList step₁ as s = runList step₂ as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      rw [runList_cons, runList_cons, ← h s a hs, ih (step₁ s a).1 (hinv s a hs)]

/-- A fold over a list all of whose steps but one do nothing. -/
lemma runList_single (step : S → ℕ → S × List B) (l : List ℕ) (v : ℕ) (s : S)
    (hl : l.filter (fun p => decide (p = v)) = [v])
    (h : ∀ t p, p ≠ v → step t p = (t, [])) : runList step l s = step s v := by
  rw [runList_filter step (fun p => decide (p = v)) l s
    (fun a _ ha t => h t a (by simpa using ha)), hl]
  simp [runList_cons]

end Generic

/-! ## Lists of positions -/

lemma filter_range_single (n v : ℕ) (hv : v < n) (p : ℕ → Bool)
    (hp : ∀ x, x < n → (p x = true ↔ x = v)) : (List.range n).filter p = [v] := by
  induction n with
  | zero => omega
  | succ m ih =>
      rw [List.range_succ, List.filter_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | h
      · have h1 : (List.range m).filter p = [v] := ih h (fun x hx => hp x (by omega))
        have hm : p m = false := by
          by_cases hc : p m = true
          · exact absurd ((hp m (by omega)).mp hc) (by omega)
          · simpa using hc
        rw [h1, List.filter_cons_of_neg (by simp [hm]), List.filter_nil, List.append_nil]
      · subst h
        have h1 : (List.range v).filter p = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx hc
          have hxv : x < v := by simpa using hx
          exact absurd ((hp x (by omega)).mp hc) (by omega)
        have hv' : p v = true := (hp v (by omega)).mpr rfl
        rw [h1, List.filter_cons_of_pos hv', List.filter_nil, List.nil_append]

lemma filter_loopRange_single (d : Bool) (n v : ℕ) (hv : v < n) (p : ℕ → Bool)
    (hp : ∀ x, x < n → (p x = true ↔ x = v)) : (loopRange d n).filter p = [v] := by
  cases d
  · rw [loopRange_false, List.filter_reverse, filter_range_single n v hv p hp]
    simp
  · rw [loopRange_true, filter_range_single n v hv p hp]

lemma filter_range_pair (n v₀ v₁ : ℕ) (h01 : v₀ < v₁) (hn : v₁ < n) (p : ℕ → Bool)
    (hp : ∀ x, x < n → (p x = true ↔ (x = v₀ ∨ x = v₁))) :
    (List.range n).filter p = [v₀, v₁] := by
  induction n with
  | zero => omega
  | succ m ih =>
      rw [List.range_succ, List.filter_append]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · have h1 : (List.range m).filter p = [v₀, v₁] := ih h (fun x hx => hp x (by omega))
        have hm : p m = false := by
          by_cases hc : p m = true
          · rcases (hp m (by omega)).mp hc with h' | h' <;> omega
          · simpa using hc
        rw [h1, List.filter_cons_of_neg (by simp [hm]), List.filter_nil, List.append_nil]
      · subst h
        have h1 : (List.range v₁).filter p = [v₀] :=
          filter_range_single v₁ v₀ h01 p (fun x hx =>
            ⟨fun hc => by rcases (hp x (by omega)).mp hc with h' | h' <;> omega,
             fun hc => (hp x (by omega)).mpr (Or.inl hc)⟩)
        have hv' : p v₁ = true := (hp v₁ (by omega)).mpr (Or.inr rfl)
        rw [h1, List.filter_cons_of_pos hv', List.filter_nil]
        rfl

/-- The first tuple visited by a nest of loops. -/
def firstTuple (L : List (Bool × ℕ)) (n : ℕ) : List ℕ :=
  L.map (fun a => if a.1 then 0 else n - 1)

lemma loopRange_eq_cons (d : Bool) {n : ℕ} (hn : 0 < n) :
    ∃ l, loopRange d n = (if d then 0 else n - 1) :: l := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  cases d
  · refine ⟨(List.range m).reverse, ?_⟩
    simp [loopRange, List.range_succ]
  · exact ⟨(List.range m).map Nat.succ, by simp [loopRange, List.range_succ_eq_map]⟩

lemma tuplesOf_eq_cons (L : List (Bool × ℕ)) {n : ℕ} (hn : 0 < n) :
    ∃ rest, tuplesOf L n = firstTuple L n :: rest := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      obtain ⟨l, hl⟩ := loopRange_eq_cons d hn
      obtain ⟨rest, hrest⟩ := ih
      refine ⟨((tuplesOf L n).map (fun t => (if d then 0 else n - 1) :: t)).tail ++
        l.flatMap (fun p => (tuplesOf L n).map (fun t => p :: t)), ?_⟩
      rw [tuplesOf_cons, hl]
      simp only [List.flatMap_cons, hrest, List.map_cons]
      rfl

/-! ## Nests of loops -/

variable {A B : Type}

/-- The position variables of a nest of loops. -/
lemma posVars_nestLoops (L : List (Bool × ℕ)) (body : ForProg A B) :
    (ForProg.nestLoops L body).posVars = L.map Prod.snd ++ body.posVars := by
  induction L with
  | nil => simp [ForProg.nestLoops]
  | cons a L ih => obtain ⟨d, x⟩ := a; simp [ForProg.nestLoops, ForProg.posVars, ih]

/-- The Boolean variables of a nest of loops. -/
lemma boolVars_nestLoops (L : List (Bool × ℕ)) (body : ForProg A B) :
    (ForProg.nestLoops L body).boolVars = body.boolVars := by
  induction L with
  | nil => rfl
  | cons a L ih => obtain ⟨d, x⟩ := a; simp [ForProg.nestLoops, ForProg.boolVars, ih]

/-- A nest whose body never does anything does nothing. -/
lemma nest_noop (w : List A) (L : List (Bool × ℕ)) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (h : ∀ t : List ℕ, ForProg.exec w body (setTuple L t pos) bv = (bv, [])) :
    ForProg.exec w (ForProg.nestLoops L body) pos bv = (bv, []) := by
  rw [exec_nestLoops]
  exact runList_noop _ _ _ (fun t _ => h t)

/-- Two bodies that agree on the states satisfying an invariant give the same nest. -/
lemma nest_congr (w : List A) (L : List (Bool × ℕ)) (body₁ body₂ : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (Φ : (ℕ → Bool) → Prop) (hs : Φ bv)
    (h : ∀ (t : List ℕ) (bv' : ℕ → Bool), Φ bv' →
      ForProg.exec w body₁ (setTuple L t pos) bv' = ForProg.exec w body₂ (setTuple L t pos) bv')
    (hinv : ∀ (t : List ℕ) (bv' : ℕ → Bool), Φ bv' →
      Φ (ForProg.exec w body₁ (setTuple L t pos) bv').1) :
    ForProg.exec w (ForProg.nestLoops L body₁) pos bv
      = ForProg.exec w (ForProg.nestLoops L body₂) pos bv := by
  rw [exec_nestLoops, exec_nestLoops]
  exact runList_congr _ _ Φ _ _ hs (fun t a ht => h a t ht) (fun t a ht => hinv a t ht)

/-- A nest whose body kills itself at the first tuple runs its body once. -/
lemma nest_kill (w : List A) (L : List (Bool × ℕ)) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (Φ : (ℕ → Bool) → Prop) (hn : 0 < w.length)
    (hdead : ∀ (t : List ℕ) (bv' : ℕ → Bool), Φ bv' →
      ForProg.exec w body (setTuple L t pos) bv' = (bv', []))
    (hset : Φ (ForProg.exec w body (setTuple L (firstTuple L w.length) pos) bv).1) :
    ForProg.exec w (ForProg.nestLoops L body) pos bv
      = ForProg.exec w body (setTuple L (firstTuple L w.length) pos) bv := by
  obtain ⟨rest, hrest⟩ := tuplesOf_eq_cons L hn
  rw [exec_nestLoops, hrest, runList_cons,
    runList_noop _ rest _ (fun t _ => hdead t _ hset)]
  simp

/-! ## Pinned nests -/

/-- The test saying that every loop variable of `L` is equal to the position variable `z`. -/
def pinTest {A : Type} (z : ℕ) : List (Bool × ℕ) → ForTest A
  | [] => ForTest.eqPos z z
  | (_, y) :: L => ForTest.and (ForTest.eqPos y z) (pinTest z L)

lemma pinTest_nil (z : ℕ) : (pinTest z ([] : List (Bool × ℕ)) : ForTest A) = ForTest.eqPos z z :=
  rfl

lemma pinTest_cons (z : ℕ) (d : Bool) (y : ℕ) (L : List (Bool × ℕ)) :
    (pinTest z ((d, y) :: L) : ForTest A) = ForTest.and (ForTest.eqPos y z) (pinTest z L) := rfl

lemma holds_pinTest_nil (w : List A) (z : ℕ) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForTest.Holds w pos bv (pinTest z ([] : List (Bool × ℕ)) : ForTest A) := rfl

/-- Pinning the *inner* loops: the body runs once, for the tuple in which every pinned variable
equals `z`. -/
lemma pin_inner (w : List A) (z : ℕ) (L : List (Bool × ℕ)) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (hz : pos z < w.length) (hzL : z ∉ L.map Prod.snd)
    (hnd : (L.map Prod.snd).Nodup) (hbody : ∀ y ∈ L.map Prod.snd, y ∉ body.posVars) :
    ForProg.exec w (ForProg.nestLoops L (ForProg.ite (pinTest z L) body ForProg.skip)) pos bv
      = ForProg.exec w body pos bv := by
  induction L generalizing pos with
  | nil =>
      show ForProg.exec w (ForProg.ite _ body ForProg.skip) pos bv = _
      rw [ForProg.exec]
      simp [holds_pinTest_nil]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      rw [List.map_cons, List.nodup_cons] at hnd
      have hxL : x ∉ L.map Prod.snd := hnd.1
      have hndL : (L.map Prod.snd).Nodup := hnd.2
      rw [List.map_cons, List.mem_cons] at hzL
      push_neg at hzL
      have hzx : z ≠ x := hzL.1
      have hzL' : z ∉ L.map Prod.snd := hzL.2
      -- the value of the pinned variable in a tuple of the inner loops
      have hval : ∀ (t : List ℕ) (p : ℕ),
          setTuple L t (Function.update pos x p) x = p := by
        intro t p
        rw [setTuple_of_not_mem L t _ hxL, Function.update_self]
      have hvalz : ∀ (t : List ℕ) (p : ℕ),
          setTuple L t (Function.update pos x p) z = pos z := by
        intro t p
        rw [setTuple_of_not_mem L t _ hzL', Function.update_of_ne hzx]
      show ForProg.exec w (ForProg.loop d x _) pos bv = _
      rw [ForProg.exec]
      have hd : (if d then List.range w.length else (List.range w.length).reverse)
          = loopRange d w.length := by cases d <;> rfl
      rw [hd, forLoopRun_eq_runList]
      -- all the iterations but the one with `x = pos z` do nothing
      have hfilter : (loopRange d w.length).filter (fun p => decide (p = pos z)) = [pos z] :=
        filter_loopRange_single d w.length (pos z) hz _ (fun x _ => by simp)
      rw [runList_single _ _ (pos z) bv hfilter ?_]
      · -- the remaining iteration
        have hpin : ∀ (t : List ℕ) (bv' : ℕ → Bool),
            ForProg.exec w (ForProg.ite (pinTest z ((d, x) :: L)) body ForProg.skip)
                (setTuple L t (Function.update pos x (pos z))) bv'
              = ForProg.exec w (ForProg.ite (pinTest z L) body ForProg.skip)
                (setTuple L t (Function.update pos x (pos z))) bv' := by
          intro t bv'
          rw [pinTest_cons]
          simp only [ForProg.exec, ForTest.Holds]
          have : setTuple L t (Function.update pos x (pos z)) x
              = setTuple L t (Function.update pos x (pos z)) z := by
            rw [hval t (pos z), hvalz t (pos z)]
          exact if_congr (by simp [this]) rfl rfl
        rw [nest_congr w L _ (ForProg.ite (pinTest z L) body ForProg.skip) _ bv (fun _ => True)
          trivial (fun t bv' _ => hpin t bv') (fun _ _ _ => trivial)]
        rw [ih (Function.update pos x (pos z)) (by rwa [Function.update_of_ne hzx]) hzL' hndL
          (fun y hy => hbody y (by simp [hy]))]
        refine ForProg.exec_congr_pos w body _ _ bv (fun i hi => ?_)
        rw [Function.update_of_ne]
        rintro rfl
        exact hbody i (by simp) hi
      · -- the iterations that do nothing
        intro bv' p hp
        refine nest_noop w L _ _ bv' (fun t => ?_)
        simp only [ForProg.exec, pinTest_cons, ForTest.Holds]
        rw [if_neg]
        rintro ⟨h1, -⟩
        rw [hval t p, hvalz t p] at h1
        exact hp h1

/-- Pinning the *outer* loops: the inner nest runs once, for the tuple in which every pinned
variable equals `z`. -/
lemma pin_outer (w : List A) (z : ℕ) (L₁ L₂ : List (Bool × ℕ)) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (hz : pos z < w.length) (hz1 : z ∉ L₁.map Prod.snd)
    (hz2 : z ∉ L₂.map Prod.snd) (hnd : (L₁.map Prod.snd).Nodup)
    (hdisj : ∀ y ∈ L₁.map Prod.snd, y ∉ L₂.map Prod.snd ∧ y ∉ body.posVars) :
    ForProg.exec w (ForProg.nestLoops L₁ (ForProg.nestLoops L₂
        (ForProg.ite (pinTest z L₁) body ForProg.skip))) pos bv
      = ForProg.exec w (ForProg.nestLoops L₂ body) pos bv := by
  induction L₁ generalizing pos with
  | nil =>
      show ForProg.exec w (ForProg.nestLoops L₂ (ForProg.ite _ body ForProg.skip)) pos bv = _
      refine nest_congr w L₂ _ body pos bv (fun _ => True) trivial (fun t bv' _ => ?_)
        (fun _ _ _ => trivial)
      simp [ForProg.exec, holds_pinTest_nil]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      rw [List.map_cons, List.nodup_cons] at hnd
      have hxL : x ∉ L.map Prod.snd := hnd.1
      have hndL : (L.map Prod.snd).Nodup := hnd.2
      rw [List.map_cons, List.mem_cons] at hz1
      push_neg at hz1
      have hzx : z ≠ x := hz1.1
      have hzL' : z ∉ L.map Prod.snd := hz1.2
      have hx2 : x ∉ L₂.map Prod.snd := (hdisj x (by simp)).1
      have hxbody : x ∉ body.posVars := (hdisj x (by simp)).2
      have hval : ∀ (t : List ℕ) (p : ℕ),
          setTuple (L ++ L₂) t (Function.update pos x p) x = p := by
        intro t p
        rw [setTuple_of_not_mem (L ++ L₂) t _ (by simp [hxL, hx2]), Function.update_self]
      have hvalz : ∀ (t : List ℕ) (p : ℕ),
          setTuple (L ++ L₂) t (Function.update pos x p) z = pos z := by
        intro t p
        rw [setTuple_of_not_mem (L ++ L₂) t _ (by simp [hzL', hz2]), Function.update_of_ne hzx]
      show ForProg.exec w (ForProg.loop d x _) pos bv = _
      rw [ForProg.exec]
      have hd : (if d then List.range w.length else (List.range w.length).reverse)
          = loopRange d w.length := by cases d <;> rfl
      rw [hd, forLoopRun_eq_runList]
      have hfilter : (loopRange d w.length).filter (fun p => decide (p = pos z)) = [pos z] :=
        filter_loopRange_single d w.length (pos z) hz _ (fun x _ => by simp)
      rw [runList_single _ _ (pos z) bv hfilter ?_]
      · have hpin : ∀ (t : List ℕ) (bv' : ℕ → Bool),
            ForProg.exec w (ForProg.ite (pinTest z ((d, x) :: L)) body ForProg.skip)
                (setTuple (L ++ L₂) t (Function.update pos x (pos z))) bv'
              = ForProg.exec w (ForProg.ite (pinTest z L) body ForProg.skip)
                (setTuple (L ++ L₂) t (Function.update pos x (pos z))) bv' := by
          intro t bv'
          rw [pinTest_cons]
          simp only [ForProg.exec, ForTest.Holds]
          have : setTuple (L ++ L₂) t (Function.update pos x (pos z)) x
              = setTuple (L ++ L₂) t (Function.update pos x (pos z)) z := by
            rw [hval t (pos z), hvalz t (pos z)]
          exact if_congr (by simp [this]) rfl rfl
        rw [← nestLoops_append]
        rw [nest_congr w (L ++ L₂) _ (ForProg.ite (pinTest z L) body ForProg.skip) _ bv
          (fun _ => True) trivial (fun t bv' _ => hpin t bv') (fun _ _ _ => trivial)]
        rw [nestLoops_append]
        rw [ih (Function.update pos x (pos z)) (by rwa [Function.update_of_ne hzx]) hzL' hndL
          (fun y hy => hdisj y (by simp [hy]))]
        refine ForProg.exec_congr_pos w _ _ _ bv (fun i hi => ?_)
        rw [posVars_nestLoops] at hi
        rw [Function.update_of_ne]
        rintro rfl
        rcases List.mem_append.mp hi with h | h
        · exact hx2 h
        · exact hxbody h
      · intro bv' p hp
        rw [← nestLoops_append]
        refine nest_noop w (L ++ L₂) _ _ bv' (fun t => ?_)
        simp only [ForProg.exec, pinTest_cons, ForTest.Holds]
        rw [if_neg]
        rintro ⟨h1, -⟩
        rw [hval t p, hvalz t p] at h1
        exact hp h1

/-- Pinning the inner loops of a nest that has already been split in two. -/
lemma nest_pin_inner (w : List A) (z : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ : ForProg A B)
    (pos : ℕ → ℕ) (bv : ℕ → Bool) (hz : pos z < w.length) (hz1 : z ∉ L₁.map Prod.snd)
    (hz2 : z ∉ L₂.map Prod.snd) (hnd2 : (L₂.map Prod.snd).Nodup)
    (hdisj : ∀ y ∈ L₂.map Prod.snd, y ∉ b₁.posVars) :
    ForProg.exec w (ForProg.nestLoops (L₁ ++ L₂)
        (ForProg.ite (pinTest z L₂) b₁ ForProg.skip)) pos bv
      = ForProg.exec w (ForProg.nestLoops L₁ b₁) pos bv := by
  rw [nestLoops_append]
  refine nest_congr w L₁ _ b₁ pos bv (fun _ => True) trivial (fun t bv' _ => ?_)
    (fun _ _ _ => trivial)
  exact pin_inner w z L₂ b₁ _ bv' (by rwa [setTuple_of_not_mem L₁ t pos hz1]) hz2 hnd2 hdisj

/-- Pinning the outer loops of a nest that has already been split in two. -/
lemma nest_pin_outer (w : List A) (z : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₂ : ForProg A B)
    (pos : ℕ → ℕ) (bv : ℕ → Bool) (hz : pos z < w.length) (hz1 : z ∉ L₁.map Prod.snd)
    (hz2 : z ∉ L₂.map Prod.snd) (hnd1 : (L₁.map Prod.snd).Nodup)
    (hdisj : ∀ y ∈ L₁.map Prod.snd, y ∉ L₂.map Prod.snd ∧ y ∉ b₂.posVars) :
    ForProg.exec w (ForProg.nestLoops (L₁ ++ L₂)
        (ForProg.ite (pinTest z L₁) b₂ ForProg.skip)) pos bv
      = ForProg.exec w (ForProg.nestLoops L₂ b₂) pos bv := by
  rw [nestLoops_append]
  exact pin_outer w z L₁ L₂ b₂ pos bv hz hz1 hz2 hnd1 hdisj

/-- The position variables of a pinning test. -/
lemma posVars_pinTest (z : ℕ) (L : List (Bool × ℕ)) :
    (pinTest z L : ForTest A).posVars ⊆ z :: L.map Prod.snd := by
  induction L with
  | nil => intro i hi; simpa [pinTest_nil, ForTest.posVars] using hi
  | cons a L ih =>
      obtain ⟨d, y⟩ := a
      intro i hi
      rw [pinTest_cons] at hi
      simp only [ForTest.posVars, List.mem_append, List.mem_cons] at hi ⊢
      rcases hi with hi | hi
      · simp only [List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact Or.inr (by simp)
        · exact Or.inl rfl
      · have := ih hi
        simp only [List.mem_cons] at this
        rcases this with rfl | h
        · exact Or.inl rfl
        · exact Or.inr (by simp [h])

/-- A pinning test holds exactly when all the pinned variables have the value of `z`. -/
lemma holds_pinTest (w : List A) (z : ℕ) (L : List (Bool × ℕ)) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ForTest.Holds w pos bv (pinTest z L : ForTest A) ↔ ∀ y ∈ L.map Prod.snd, pos y = pos z := by
  induction L with
  | nil => simp [pinTest_nil, ForTest.Holds]
  | cons a L ih =>
      obtain ⟨d, y⟩ := a
      rw [pinTest_cons]
      simp only [ForTest.Holds, ih, List.map_cons, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩ u hu
        rcases hu with rfl | hu
        · exact h1
        · exact h2 u hu
      · intro h
        exact ⟨h y (Or.inl rfl), fun u hu => h u (Or.inr hu)⟩

end Lax194892Proofs.Transducers
