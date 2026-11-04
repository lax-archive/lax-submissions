import Lax185574Proofs.Chain.Ram.TpSpec
import Lax185574Proofs.Chain.Damping

/-!
The quantities of the predamping procedure on numbers.

For the partition selector `B ↦ tpRel G B r`, a set `Bs` and its
labelling `L = lbl n (tpN G Bs r)`, the number of parts crossed by `w`,
the number of parts meeting `Δ[w,s]` and the number of representatives
between `w` and `s` are expressed as counts over the numbers below `n`
(`crossCnt_eq`, `ham_eq`, `betw_eq`). A part is counted by its least
vertex, which is a label `c` with `L c = c`, and a representative is a
vertex of least position in its part.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ}

/-! ### First elements of `Fin n` -/

/-- The first element of `Fin n` with a property, through `find?`. -/
theorem map_find?_finRange (p : Fin n → Prop) [DecidablePred p] :
    ((List.finRange n).find? fun w => decide (p w)).map Fin.val =
      open Classical in
      if ∃ v < n, ∃ h : v < n, p ⟨v, h⟩ then some (leastBelow (fun v => ∃ h : v < n, p ⟨v, h⟩) n n)
        else none := by
  classical
  set p' : ℕ → Prop := fun v => ∃ h : v < n, p ⟨v, h⟩
  cases hf : (List.finRange n).find? (fun w => decide (p w)) with
  | none =>
    rw [List.find?_eq_none] at hf
    have : ¬ ∃ v < n, p' v := by
      rintro ⟨v, hv, h, hp⟩
      exact hf ⟨v, h⟩ (List.mem_finRange _) (by simpa using hp)
    simp only [p'] at this
    rw [if_neg this]; rfl
  | some w =>
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨hpw, i, hi, hwi, hbefore⟩ := hf
    have hex : ∃ v < n, p' v := ⟨w, w.2, w.2, by simpa using hpw⟩
    simp only [p'] at hex
    rw [if_pos hex]
    simp only [Option.map_some, Option.some.injEq]
    obtain ⟨h1, h2, h3⟩ := leastBelow_spec (d := n) hex
    have hiw : i = w := by
      rw [List.getElem_finRange] at hwi; rw [← hwi]; rfl
    refine le_antisymm ?_ (leastBelow_le_of w.2 ⟨w.2, by simpa using hpw⟩)
    by_contra hc
    push Not at hc
    obtain ⟨hlt, hp⟩ := h2
    have := hbefore (leastBelow (fun v => ∃ h : v < n, p ⟨v, h⟩) n n) (by omega)
    rw [List.getElem_finRange] at this
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this (by simpa using hp)

/-! ### Counting parts by least vertices -/

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (o : VOrder (Fin n)) (r : ℕ)

/-- The partition selector of the chain. -/
def tpP (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) : Finset (Fin n) → Fin n → Fin n → Bool :=
  fun B => tpRel G B r

theorem tpP_selector : IsSelector G (tpP G r) := isSelector_tp r

variable {G o r}

/-- Representatives with a property of their part, counted by least
vertices. -/
theorem card_reps_filter_eq (Bs : Finset (Fin n)) (ψ : Fin n → Prop) [DecidablePred ψ]
    (hψ : ∀ x y, tpRel G Bs r x y = true → (ψ x ↔ ψ y)) :
    ((reps (tpP G r) o Bs).filter ψ).card =
      open Classical in
      ((range n).filter fun c => lbl n (tpN G Bs r) c = c ∧ ∃ h : c < n, ψ ⟨c, h⟩).card := by
  classical
  have hP := tpP_selector G r
  have hE := tpN_isEqv (G := G) (B := Bs) r
  have hrel : ∀ (x : Fin n) (c : ℕ) (hc : c < n), lbl n (tpN G Bs r) c = c →
      (tpRel G Bs r x ⟨c, hc⟩ = true ↔ lbl n (tpN G Bs r) x = c) := by
    intro x c hc hLc
    rw [← tpN_fin (k := r), ← lbl_eq_iff hE x.2 hc, hLc]
  refine card_bij (fun x _ => lbl n (tpN G Bs r) x) (fun x hx => ?_) (fun x hx x' hx' h => ?_)
    (fun c hc => ?_)
  · obtain ⟨-, hψx⟩ := mem_filter.1 hx
    have hLx := lbl_lt hE x.2
    have hLL : lbl n (tpN G Bs r) (lbl n (tpN G Bs r) x) = lbl n (tpN G Bs r) x := by
      rw [lbl_eq_iff hE hLx x.2]; exact (lbl_spec hE x.2).2.1
    refine mem_filter.2 ⟨mem_range.2 hLx, hLL, hLx, ?_⟩
    exact (hψ _ _ ((hrel x _ hLx hLL).2 rfl)).1 hψx
  · have h1 := (mem_filter.1 hx).1
    have h2 := (mem_filter.1 hx').1
    refine rep_unique hP h1 h2 ?_
    change tpRel G Bs r x x' = true
    rw [← tpN_fin (k := r), ← lbl_eq_iff hE x.2 x'.2]; exact h
  · obtain ⟨hcn, hLc, hc', hψc⟩ := mem_filter.1 hc
    obtain ⟨x, hx, hxc⟩ := exists_rep hP Bs ⟨c, hc'⟩
    have hxc' : lbl n (tpN G Bs r) x = c := by
      have := (lbl_eq_iff hE x.2 hc').2 ((tpN_fin (k := r) x ⟨c, hc'⟩).2 hxc)
      rw [this, hLc]
    refine ⟨x, mem_filter.2 ⟨hx, ?_⟩, hxc'⟩
    exact (hψ _ _ ((hrel x c hc' hLc).2 hxc')).2 hψc

/-! ### The three quantities -/

open Classical in
/-- The number of parts crossed by `w`, on numbers. -/
noncomputable def crossN (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (w : ℕ) : ℕ :=
  ((range n).filter fun c => L c = c ∧ L w ≠ c ∧ cntN G L w c ≠ 0 ∧
    cntN G L w c ≠ szN n L c).card

/-- `y ∈ Δ[w,s]`, on numbers. -/
def sdN (G : SimpleGraph (Fin n)) (w s y : ℕ) : Prop :=
  w ≠ s ∧ (y = w ∨ y = s ∨ ¬ (gA G w y ↔ gA G s y))

open Classical in
/-- The number of parts meeting `Δ[w,s]`, on numbers. -/
noncomputable def hamN (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (w s : ℕ) : ℕ :=
  ((range n).filter fun c => L c = c ∧ ∃ y < n, sdN G w s y ∧ L y = c).card

/-- `z` has the least position in its part. -/
def isRepN (n : ℕ) (pf L : ℕ → ℕ) (z : ℕ) : Prop := ∀ y < n, L y = L z → pf z ≤ pf y

open Classical in
/-- The number of representatives strictly between `w` and `s`. -/
noncomputable def betwN (n : ℕ) (pf L : ℕ → ℕ) (w s : ℕ) : ℕ :=
  ((range n).filter fun z => isRepN n pf L z ∧
    ((pf w < pf z ∧ pf z < pf s) ∨ (pf s < pf z ∧ pf z < pf w))).card

/-- The positions of an ordering, on numbers. -/
def posN (o : VOrder (Fin n)) (z : ℕ) : ℕ := if h : z < n then o.pos ⟨z, h⟩ else 0

theorem posN_fin (z : Fin n) : posN o z = o.pos z := by simp [posN, z.2]

theorem crossCnt_eq (Bs : Finset (Fin n)) (w : Fin n) :
    crossCnt G (tpP G r) o Bs w = crossN G (lbl n (tpN G Bs r)) w := by
  classical
  unfold crossCnt crossN
  rw [card_reps_filter_eq Bs _ fun x y hxy => by
    rw [(cls_eq_iff ((tpP_selector G r).equiv Bs)).2 hxy]]
  congr 1
  refine filter_congr fun c hc => ?_
  have hcn := mem_range.1 hc
  have hE := tpN_isEqv (G := G) (B := Bs) r
  refine and_congr_right fun hLc => ?_
  have hmem : w ∈ cls (tpP G r Bs) ⟨c, hcn⟩ ↔ (lbl n (tpN G Bs r)) w = c := by
    rw [mem_cls]
    change tpRel G Bs r ⟨c, hcn⟩ w = true ↔ _
    rw [← tpN_fin (k := r), ← lbl_eq_iff hE hcn w.2, hLc, eq_comm]
  have hcomp := complete_iff (G := G) (B := Bs) (k := r) w.2 hcn
  have hanti := anticomplete_iff (G := G) (B := Bs) (k := r) w.2 hcn
  simp only [Fin.eta] at hcomp hanti
  refine (exists_prop_of_true hcn).trans ?_
  change Crosses G w (cls (tpRel G Bs r) ⟨c, hcn⟩) ↔ _
  unfold Crosses
  change ¬ w ∈ cls (tpP G r Bs) ⟨c, hcn⟩ ∧ _ ↔ _
  rw [hmem, hcomp, hanti, hLc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h3, fun h => h2 ?_⟩
    rw [h]; unfold ind; rw [if_neg h1]; simp
  · rintro ⟨h1, h3, h4⟩
    refine ⟨h1, fun h => h4 ?_, h3⟩
    rw [h]; unfold ind; rw [if_neg h1]; simp

theorem ham_eq (Bs : Finset (Fin n)) (w s : Fin n) :
    ham G (tpP G r) o Bs w s = hamN G (lbl n (tpN G Bs r)) w s := by
  classical
  unfold ham hamN
  have := card_reps_filter_eq (G := G) (o := o) (r := r) Bs
    (fun x => ∃ y ∈ sdiff G w s, tpP G r Bs x y = true) fun x x' hxx' => by
      have hq := (tpP_selector G r).equiv Bs
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, hq.trans _ _ _ (hq.symm _ _ hxx') h⟩,
        fun ⟨y, hy, h⟩ => ⟨y, hy, hq.trans _ _ _ hxx' h⟩⟩
  convert this using 2
  · ext x; simp only [mem_filter]
  refine Finset.ext fun c => ?_
  simp only [mem_filter]
  refine and_congr_right fun hc => ?_
  have hcn := mem_range.1 hc
  have hE := tpN_isEqv (G := G) (B := Bs) r
  refine and_congr_right fun hLc => ?_
  symm
  constructor
  · rintro ⟨_, y, hy, hyc⟩
    refine ⟨y, y.2, ?_, ?_⟩
    · rw [mem_sdiff] at hy
      refine ⟨fun h => hy.1 (Fin.ext h), ?_⟩
      rcases hy.2 with h | h | h
      · left; rw [h]
      · right; left; rw [h]
      · right; right; rwa [gA_iff w.2 y.2, gA_iff s.2 y.2]
    · change tpRel G Bs r ⟨c, hcn⟩ y = true at hyc
      rw [← tpN_fin (k := r), ← lbl_eq_iff hE hcn y.2, hLc] at hyc
      exact hyc.symm
  · rintro ⟨y, hy, hsd, hyc⟩
    refine ⟨hcn, ⟨y, hy⟩, ?_, ?_⟩
    · rw [mem_sdiff]
      refine ⟨fun h => hsd.1 (congrArg Fin.val h), ?_⟩
      rcases hsd.2 with h | h | h
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; rwa [gA_iff w.2 hy, gA_iff s.2 hy] at h
    · change tpRel G Bs r ⟨c, hcn⟩ ⟨y, hy⟩ = true
      rw [← tpN_fin (k := r), ← lbl_eq_iff hE hcn hy, hLc, hyc]

theorem isRep_iff (Bs : Finset (Fin n)) (z : Fin n) :
    z ∈ reps (tpP G r) o Bs ↔ isRepN n (posN o) (lbl n (tpN G Bs r)) z := by
  have hE := tpN_isEqv (G := G) (B := Bs) r
  unfold reps isRepN
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h y hy hyz
    have := h ⟨y, hy⟩ (by
      change tpRel G Bs r z ⟨y, hy⟩ = true
      rw [← tpN_fin (k := r), ← lbl_eq_iff hE z.2 hy]; exact hyz.symm)
    simpa [posN, z.2, hy] using this
  · intro h y hy
    have := h y y.2 (by
      change tpRel G Bs r z y = true at hy
      rw [← tpN_fin (k := r), ← lbl_eq_iff hE z.2 y.2] at hy; exact hy.symm)
    simpa [posN, z.2, y.2] using this

theorem betw_eq (Bs : Finset (Fin n)) (w s : Fin n) :
    betw (tpP G r) o Bs w s = betwN n (posN o) (lbl n (tpN G Bs r)) w s := by
  classical
  unfold betw betwN
  refine card_bij (fun x _ => (x : ℕ)) (fun x hx => ?_) (fun x _ x' _ h => Fin.ext h)
    (fun z hz => ?_)
  · obtain ⟨hrep, hb⟩ := mem_filter.1 hx
    refine mem_filter.2 ⟨mem_range.2 x.2, (isRep_iff Bs x).1 hrep, ?_⟩
    simp only [posN_fin]; exact hb
  · obtain ⟨hzn, hrep, hb⟩ := mem_filter.1 hz
    have hzn' := mem_range.1 hzn
    refine ⟨⟨z, hzn'⟩, mem_filter.2 ⟨(isRep_iff Bs ⟨z, hzn'⟩).2 hrep, ?_⟩, rfl⟩
    have e1 := posN_fin (o := o) ⟨z, hzn'⟩
    have e2 := posN_fin (o := o) w
    have e3 := posN_fin (o := o) s
    simp only at e1
    rw [← e1, ← e2, ← e3]; exact hb

end Lax185574Proofs.Chain.Ram
