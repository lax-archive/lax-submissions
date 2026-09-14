/-
# Compiling partial recursive functions to counter machine programs

Mathlib's `Nat.Partrec'` presents the partial recursive functions of several arguments as
the closure of the constants, the successor and the projections under composition,
primitive recursion and minimisation.  This file compiles such a description into a
counter machine program.

The calling convention is: the `n` arguments sit in the registers `0, …, n-1`, the value
is delivered in the register `n`, the arguments are left untouched, and every scratch
register below the bound `b` is zero on entry and on exit.  Because the convention is so
rigid, the transformation effected by a program computing `f` is exactly
`Function.update s n y`, which makes the constructions compose without any bookkeeping.
-/
import Lax251941Proofs.Source.Sim.Macro
import Lax251941Proofs.Source.Sim.Simulate
import Mathlib.Computability.Halting

namespace Lax251941Proofs.PCP
namespace Sim

open List (Vector)

/-- The contents of the first `n` registers, as a vector. -/
def vargs (n : ℕ) (s : Regs) : List.Vector ℕ n := List.Vector.ofFn (fun i : Fin n => s i)

@[simp] lemma vargs_get (n : ℕ) (s : Regs) (i : Fin n) : (vargs n s).get i = s i := by
  simp [vargs]

lemma vargs_congr {n : ℕ} {s t : Regs} (h : ∀ i, i < n → s i = t i) : vargs n s = vargs n t := by
  simp only [vargs]
  congr 1
  funext i
  exact h i i.isLt

/-- `Computes n b f P`: the program `P` computes the `n`-ary partial function `f`, using
the registers below `b` as workspace. -/
def Computes (n b : ℕ) (f : List.Vector ℕ n →. ℕ) (P : Prog) : Prop :=
  n < b ∧
  ∀ s : Regs, (∀ i, n ≤ i → i < b → s i = 0) →
    (∀ y ∈ f (vargs n s), Runs P s (Function.update s n y)) ∧
    (¬ (f (vargs n s)).Dom → ¬ CHalts P s)

lemma Computes.lt {n b : ℕ} {f : List.Vector ℕ n →. ℕ} {P : Prog} (h : Computes n b f P) :
    n < b := h.1

lemma Computes.mono {n b b' : ℕ} {f : List.Vector ℕ n →. ℕ} {P : Prog} (h : Computes n b f P)
    (hb : b ≤ b') : Computes n b' f P :=
  ⟨lt_of_lt_of_le h.1 hb, fun s hs => h.2 s (fun i h1 h2 => hs i h1 (by omega))⟩

lemma Computes.congr {n b : ℕ} {f f' : List.Vector ℕ n →. ℕ} {P : Prog} (h : Computes n b f P)
    (he : ∀ v, f v = f' v) : Computes n b f' P :=
  ⟨h.1, fun s hs => by rw [← he]; exact h.2 s hs⟩

lemma mOfFn_some : ∀ {k : ℕ} (h : Fin k → ℕ),
    (List.Vector.mOfFn fun i => (Part.some (h i) : Part ℕ)) = Part.some (List.Vector.ofFn h)
  | 0, h => by
    rw [show List.Vector.ofFn h = List.Vector.nil from List.Vector.eq_nil _]
    rfl
  | (k + 1), h => by
    rw [List.Vector.mOfFn, mOfFn_some (fun i => h i.succ)]
    simp [List.Vector.ofFn]

/-! ## Total functions -/

lemma mem_lift {α : Type*} {f : α → ℕ} {v : α} {y : ℕ}
    (h : y ∈ ((f : α → ℕ) : α →. ℕ) v) : y = f v := by
  simpa [PFun.coe_val] using h

lemma mem_lift_self {α : Type*} (f : α → ℕ) (v : α) : f v ∈ ((f : α → ℕ) : α →. ℕ) v := by
  simp [PFun.coe_val]

lemma dom_lift {α : Type*} (f : α → ℕ) (v : α) : (((f : α → ℕ) : α →. ℕ) v).Dom := by
  simp [PFun.coe_val]

/-- For a total function only the halting clause of `Computes` has content. -/
lemma computes_of_total {n b : ℕ} {f : List.Vector ℕ n → ℕ} {P : Prog} (hb : n < b)
    (h : ∀ s : Regs, (∀ i, n ≤ i → i < b → s i = 0) →
      Runs P s (Function.update s n (f (vargs n s)))) :
    Computes n b ((f : List.Vector ℕ n → ℕ) : _ →. ℕ) P := by
  refine ⟨hb, fun s hs => ⟨fun y hy => ?_, fun hd => absurd (dom_lift f _) hd⟩⟩
  rw [mem_lift hy]
  exact h s hs

/-! ## The base cases -/

lemma computes_zero : Computes 0 1 ((fun _ => 0 : List.Vector ℕ 0 → ℕ) : _ →. ℕ) [] := by
  refine computes_of_total (by omega) (fun s hs => ?_)
  have : Function.update s 0 0 = s := by
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · simp [hs 0 (by omega) (by omega)]
    · simp [Function.update_of_ne hi]
  simpa [this] using runs_nil s

lemma vargs_one_head (s : Regs) : (vargs 1 s).head = s 0 := by
  rw [← List.Vector.get_zero, vargs_get]
  rfl

lemma computes_succ :
    Computes 1 3 ((fun v : List.Vector ℕ 1 => v.head + 1 : List.Vector ℕ 1 → ℕ) : _ →. ℕ)
      (pseq (pcopy 0 1 2) [Instr.inc 1]) := by
  refine computes_of_total (by omega) (fun s hs => ?_)
  have h2 : s 2 = 0 := hs 2 (by omega) (by omega)
  have hrun := runs_pseq (impl_pcopy (show (0:ℕ) ≠ 1 by omega) (show (0:ℕ) ≠ 2 by omega)
      (show (1:ℕ) ≠ 2 by omega) s)
    (impl_inc 1 (fun i => if i = 1 then s 0 else if i = 2 then 0 else s i))
  refine Eq.mpr ?_ hrun
  congr 1
  funext i
  simp only [vargs_one_head, Function.update_apply]
  rcases eq_or_ne i 1 with rfl | hi
  · simp
  · rcases eq_or_ne i 2 with rfl | hi2
    · simp [hi, h2]
    · simp [hi, hi2]

lemma computes_get {n : ℕ} (i : Fin n) :
    Computes n (n + 2) ((fun v : List.Vector ℕ n => v.get i : List.Vector ℕ n → ℕ) : _ →. ℕ)
      (pcopy i n (n + 1)) := by
  have hi : (i : ℕ) < n := i.isLt
  refine computes_of_total (by omega) (fun s hs => ?_)
  have h2 : s (n + 1) = 0 := hs (n + 1) (by omega) (by omega)
  have hrun := impl_pcopy (src := (i : ℕ)) (dst := n) (tmp := n + 1)
    (by omega) (by omega) (by omega) s
  refine Eq.mpr ?_ hrun
  congr 1
  funext j
  simp only [vargs_get, Function.update_apply]
  rcases eq_or_ne j n with rfl | hj
  · simp
  · rcases eq_or_ne j (n + 1) with rfl | hj2
    · simp [h2]
    · simp [hj, hj2]

/-! ## Composition -/

lemma mem_mOfFn : ∀ {k : ℕ} {p : Fin k → Part ℕ} {v : List.Vector ℕ k},
    v ∈ List.Vector.mOfFn p → ∀ i, v.get i ∈ p i
  | 0, _, _, _, i => i.elim0
  | (k + 1), p, v, h, i => by
    rw [List.Vector.mOfFn] at h
    simp only [Part.bind_eq_bind, Part.mem_bind_iff] at h
    obtain ⟨a, ha, w, hw, h⟩ := h
    have hv : v = a ::ᵥ w := by simpa using h
    subst hv
    refine Fin.cases ?_ ?_ i
    · simpa using ha
    · intro j
      simpa using mem_mOfFn hw j

lemma mOfFn_mem : ∀ {k : ℕ} {p : Fin k → Part ℕ} {Y : Fin k → ℕ},
    (∀ i, Y i ∈ p i) → List.Vector.ofFn Y ∈ List.Vector.mOfFn p
  | 0, p, Y, _ => by
    rw [List.Vector.mOfFn, show List.Vector.ofFn Y = List.Vector.nil from List.Vector.eq_nil _]
    simp
  | (k + 1), p, Y, h => by
    rw [List.Vector.mOfFn]
    simp only [Part.bind_eq_bind, Part.mem_bind_iff]
    refine ⟨Y 0, h 0, List.Vector.ofFn (fun i => Y i.succ), mOfFn_mem (fun i => h i.succ), ?_⟩
    rw [List.Vector.ofFn]
    simp

lemma computes_comp {m k : ℕ} {f : List.Vector ℕ k →. ℕ} {g : Fin k → List.Vector ℕ m →. ℕ}
    {bF : ℕ} {F : Prog} (hF : Computes k bF f F)
    {bG : Fin k → ℕ} {G : Fin k → Prog} (hG : ∀ i, Computes m (bG i) (g i) (G i)) :
    ∃ b P, Computes m b (fun v => (List.Vector.mOfFn fun i => g i v) >>= f) P := by
  classical
  obtain ⟨W, hWF, hWG, hWm, hWk⟩ :
      ∃ W, bF ≤ W ∧ (∀ i, bG i ≤ W) ∧ m + 1 ≤ W ∧ k + 1 ≤ W :=
    ⟨max (max bF (m + 1)) (max (k + 1) (Finset.univ.sup bG)),
      le_trans (le_max_left _ _) (le_max_left _ _),
      fun i => le_trans (le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _))
        (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_left _ _),
      le_trans (le_max_left _ _) (le_max_right _ _)⟩
  refine ⟨W + k + 1 + m,
    pseq (pstages (fun j => if h : j < k then pseq (G ⟨j, h⟩) (pmove m (W + j)) else []) k)
      (pseq (pmoveBlock 0 (W + k + 1) m) (pseq (pmoveBlock W 0 k)
        (pseq F (pseq (pmove k W) (pseq (pclearRange 0 k)
          (pseq (pmoveBlock (W + k + 1) 0 m) (pmove W m))))))),
    by omega, fun s hs => ?_⟩
  set Q : ℕ → Prog := fun j => if h : j < k then pseq (G ⟨j, h⟩) (pmove m (W + j)) else []
    with hQdef
  set uu : (ℕ → ℕ) → ℕ → Regs :=
    fun Y j i => if W ≤ i ∧ i < W + j then Y (i - W) else s i with huudef
  have huu_out : ∀ (Y : ℕ → ℕ) (j i : ℕ), (i < W ∨ W + j ≤ i) → uu Y j i = s i := by
    intro Y j i hi
    rw [huudef]
    simp only
    rw [if_neg (by omega)]
  have huu_in : ∀ (Y : ℕ → ℕ) (j i : ℕ), W ≤ i → i < W + j → uu Y j i = Y (i - W) := by
    intro Y j i h1 h2
    rw [huudef]
    simp only
    rw [if_pos ⟨h1, h2⟩]
  have huu_va : ∀ (Y : ℕ → ℕ) (j : ℕ), vargs m (uu Y j) = vargs m s :=
    fun Y j => vargs_congr (fun i hi => huu_out Y j i (Or.inl (by omega)))
  have huu_pre : ∀ (Y : ℕ → ℕ) (j : ℕ) (i : Fin k) (x : ℕ), m ≤ x → x < bG i → uu Y j x = 0 := by
    intro Y j i x h1 h2
    have hxW : x < W := lt_of_lt_of_le h2 (hWG i)
    rw [huu_out Y j x (Or.inl hxW)]
    exact hs x h1 (by omega)
  -- the value of the `t`-th inner function, when it is defined
  set Yc : ℕ → ℕ := fun t => if h : t < k then
      (if hd : (g ⟨t, h⟩ (vargs m s)).Dom then (g ⟨t, h⟩ (vargs m s)).get hd else 0) else 0
    with hYcdef
  have hYc_mem : ∀ (t : ℕ) (ht : t < k), (g ⟨t, ht⟩ (vargs m s)).Dom →
      Yc t ∈ g ⟨t, ht⟩ (vargs m s) := by
    intro t ht hd
    rw [hYcdef]
    simp only [dif_pos ht, dif_pos hd]
    exact Part.get_mem hd
  -- running the stages
  have stages_run : ∀ (j : ℕ), j ≤ k →
      (∀ (t : ℕ) (ht : t < k), t < j → (g ⟨t, ht⟩ (vargs m s)).Dom) →
      Runs (pstages Q j) s (uu Yc j) := by
    intro j
    induction j with
    | zero =>
      intro _ _
      have he : uu Yc 0 = s := by
        funext i
        exact huu_out Yc 0 i (by omega)
      rw [he]
      exact runs_nil s
    | succ j ih =>
      intro hj hY
      have hjk : j < k := by omega
      have hrun1 := ih (by omega) (fun t ht htj => hY t ht (by omega))
      obtain ⟨hGrun, -⟩ := (hG ⟨j, hjk⟩).2 (uu Yc j) (huu_pre Yc j ⟨j, hjk⟩)
      have hGrun' := hGrun (Yc j) (by
        rw [huu_va Yc j]
        exact hYc_mem j hjk (hY j hjk (by omega)))
      have hmv := impl_pmove (src := m) (dst := W + j) (show m ≠ W + j by omega)
        (Function.update (uu Yc j) m (Yc j))
      have hstage := runs_pseq hGrun' hmv
      have hQj : Q j = pseq (G ⟨j, hjk⟩) (pmove m (W + j)) := by
        rw [hQdef]
        exact dif_pos hjk
      show Runs (pseq (pstages Q j) (Q j)) s (uu Yc (j + 1))
      rw [hQj]
      refine runs_pseq hrun1 ?_
      refine Eq.mpr ?_ hstage
      congr 1
      funext i
      by_cases him : i = m
      · rw [him, huu_out Yc (j + 1) m (by omega)]
        simp only
        exact hs m le_rfl (by omega)
      · by_cases hiw : i = W + j
        · rw [hiw, huu_in Yc (j + 1) (W + j) (by omega) (by omega)]
          simp only [if_neg (show W + j ≠ m by omega), Function.update_self]
          congr 1
          omega
        · simp only [if_neg him, if_neg hiw, Function.update_of_ne him]
          rw [huudef]
          simp only
          by_cases hin : W ≤ i ∧ i < W + j
          · rw [if_pos hin, if_pos ⟨hin.1, by omega⟩]
          · rw [if_neg hin, if_neg (by omega)]
  -- the whole prefix
  have prefix_run : (∀ (t : ℕ) (ht : t < k), (g ⟨t, ht⟩ (vargs m s)).Dom) →
      ∃ u1 u2 u3 : Regs, Runs (pstages Q k) s u1 ∧ Runs (pmoveBlock 0 (W + k + 1) m) u1 u2 ∧
        Runs (pmoveBlock W 0 k) u2 u3 ∧
        (∀ t, t < k → u3 t = Yc t) ∧
        (∀ i, k ≤ i → i < W + k + 1 → u3 i = 0) ∧
        (∀ j, j < m → u3 (W + k + 1 + j) = s j) ∧
        (∀ i, W + k + 1 + m ≤ i → u3 i = s i) := by
    intro hdom
    have hr1 := stages_run k le_rfl (fun t ht _ => hdom t ht)
    obtain ⟨u2, hr2, hb1, hb2, hb3⟩ :=
      acts_pmoveBlock (src := 0) (dst := W + k + 1) (m := m) (Or.inl (by omega)) (uu Yc k)
    obtain ⟨u3, hr3, hc1, hc2, hc3⟩ :=
      acts_pmoveBlock (src := W) (dst := 0) (m := k) (Or.inr (by omega)) u2
    refine ⟨uu Yc k, u2, u3, hr1, hr2, hr3, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have h1 := hc1 t ht
      rw [Nat.zero_add] at h1
      rw [h1, hb3 (W + t) (fun j hj => by omega), huu_in Yc k (W + t) (by omega) (by omega)]
      congr 1
      omega
    · intro i h1 h2
      by_cases hin : W ≤ i ∧ i < W + k
      · obtain ⟨t, rfl⟩ : ∃ t, i = W + t := ⟨i - W, by omega⟩
        exact hc2 t (by omega)
      · rw [hc3 i (fun j hj => by omega)]
        by_cases hlt : i < m
        · simpa using hb2 i hlt
        · rw [hb3 i (fun j hj => by omega), huu_out Yc k i (by omega)]
          exact hs i (by omega) (by omega)
    · intro j hj
      rw [hc3 (W + k + 1 + j) (fun t ht => by omega)]
      have h1 := hb1 j hj
      rw [Nat.zero_add] at h1
      rw [h1, huu_out Yc k j (Or.inl (by omega))]
    · intro i hi
      rw [hc3 i (fun t ht => by omega), hb3 i (fun t ht => by omega),
        huu_out Yc k i (Or.inr (by omega))]
  refine ⟨?_, ?_⟩
  · -- the convergent case
    intro z hz
    obtain ⟨w, hw, hzf⟩ := Part.mem_bind_iff.mp hz
    have hdom : ∀ (t : ℕ) (ht : t < k), (g ⟨t, ht⟩ (vargs m s)).Dom :=
      fun t ht => Part.dom_iff_mem.mpr ⟨_, mem_mOfFn hw ⟨t, ht⟩⟩
    obtain ⟨u1, u2, u3, hr1, hr2, hr3, ha, hb, hc, hd⟩ := prefix_run hdom
    have hYcw : ∀ i : Fin k, Yc (i : ℕ) = w.get i := by
      intro i
      have h1 := hYc_mem (i : ℕ) i.isLt (hdom (i : ℕ) i.isLt)
      have h2 := mem_mOfFn hw i
      simp only [Fin.eta] at h1
      exact Part.mem_unique h1 h2
    have hvk : vargs k u3 = w := by
      rw [vargs, show (fun i : Fin k => u3 (i : ℕ)) = fun i => w.get i from
        funext (fun i => by rw [ha i i.isLt, hYcw i])]
      exact List.Vector.ofFn_get w
    obtain ⟨hFrun, -⟩ := hF.2 u3 (fun i h1 h2 => hb i h1 (by omega))
    have hr4 := hFrun z (by rw [hvk]; exact hzf)
    have hr5 := impl_pmove (src := k) (dst := W) (show k ≠ W by omega)
      (Function.update u3 k z)
    obtain ⟨u6, hr6, hd1, hd2⟩ := acts_pclearRange 0 k
      (fun i => if i = k then 0 else if i = W then (Function.update u3 k z) k
        else (Function.update u3 k z) i)
    obtain ⟨u7, hr7, he1, he2, he3⟩ :=
      acts_pmoveBlock (src := W + k + 1) (dst := 0) (m := m) (Or.inr (by omega)) u6
    have hr8 := impl_pmove (src := W) (dst := m) (show W ≠ m by omega) u7
    refine Eq.mpr ?_ (runs_pseq hr1 (runs_pseq hr2 (runs_pseq hr3 (runs_pseq hr4
      (runs_pseq hr5 (runs_pseq hr6 (runs_pseq hr7 hr8)))))))
    congr 1
    have hu7W : u7 W = z := by
      rw [he3 W (fun j hj => by omega), hd2 W (Or.inr (by omega))]
      simp [show W ≠ k by omega]
    funext i
    by_cases hiW : i = W
    · rw [hiW]
      simp only [Function.update_of_ne (show W ≠ m by omega)]
      exact hs W (by omega) (by omega)
    · by_cases him : i = m
      · rw [him]
        simp only [if_neg (show m ≠ W by omega), Function.update_self]
        exact hu7W.symm
      · simp only [if_neg hiW, if_neg him, Function.update_of_ne him]
        by_cases hlt : i < m
        · have h1 := he1 i hlt
          rw [Nat.zero_add] at h1
          rw [h1, hd2 (W + k + 1 + i) (Or.inr (by omega))]
          simp only [if_neg (show W + k + 1 + i ≠ k by omega),
            if_neg (show W + k + 1 + i ≠ W by omega),
            Function.update_of_ne (show W + k + 1 + i ≠ k by omega)]
          exact (hc i hlt).symm
        · by_cases hge : W + k + 1 + m ≤ i
          · rw [he3 i (fun j hj => by omega), hd2 i (Or.inr (by omega))]
            simp only [if_neg (show i ≠ k by omega), if_neg hiW,
              Function.update_of_ne (show i ≠ k by omega)]
            exact (hd i hge).symm
          · by_cases hblk : W + k + 1 ≤ i
            · obtain ⟨j, rfl⟩ : ∃ j, i = W + k + 1 + j := ⟨i - (W + k + 1), by omega⟩
              rw [he2 j (by omega)]
              exact hs _ (by omega) (by omega)
            · rw [he3 i (fun j hj => by omega)]
              by_cases hik : i < k
              · rw [hd1 i (by omega) (by omega)]
                exact hs i (by omega) (by omega)
              · rw [hd2 i (Or.inr (by omega))]
                by_cases hik2 : i = k
                · rw [hik2]
                  simp only
                  exact hs k (by omega) (by omega)
                · simp only [if_neg hik2, if_neg hiW, Function.update_of_ne hik2]
                  rw [hb i (by omega) (by omega)]
                  exact hs i (by omega) (by omega)
  · -- the divergent case
    intro hnd
    by_cases hdom : ∀ (t : ℕ) (ht : t < k), (g ⟨t, ht⟩ (vargs m s)).Dom
    · obtain ⟨u1, u2, u3, hr1, hr2, hr3, ha, hb, hc, hd⟩ := prefix_run hdom
      have hvk : vargs k u3 = List.Vector.ofFn (fun i : Fin k => Yc (i : ℕ)) := by
        rw [vargs]
        congr 1
        funext i
        exact ha i i.isLt
      have hfnd : ¬ (f (vargs k u3)).Dom := by
        intro hdf
        refine hnd (Part.dom_iff_mem.mpr ?_)
        obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hdf
        refine ⟨z, ?_⟩
        show z ∈ (List.Vector.mOfFn fun i => g i (vargs m s)) >>= f
        refine Part.mem_bind_iff.mpr ⟨vargs k u3, ?_, hz⟩
        rw [hvk]
        exact mOfFn_mem (fun i => by
          have h1 := hYc_mem (i : ℕ) i.isLt (hdom (i : ℕ) i.isLt)
          simpa using h1)
      exact not_halts_pseq_right hr1 (not_halts_pseq_right hr2 (not_halts_pseq_right hr3
        (not_halts_pseq_left ((hF.2 u3 (fun i h1 h2 => hb i h1 (by omega))).2 hfnd))))
    · -- some inner function diverges
      have key : ∀ j, j ≤ k →
          (∀ (t : ℕ) (ht : t < k), t < j → (g ⟨t, ht⟩ (vargs m s)).Dom)
          ∨ ¬ CHalts (pstages Q j) s := by
        intro j
        induction j with
        | zero => intro _; exact Or.inl (fun t ht h => absurd h (by omega))
        | succ j ih =>
          intro hj
          have hjk : j < k := by omega
          rcases ih (by omega) with hall | hnh
          · by_cases hjd : (g ⟨j, hjk⟩ (vargs m s)).Dom
            · refine Or.inl (fun t ht htj => ?_)
              rcases Nat.lt_or_ge t j with h | h
              · exact hall t ht h
              · have htj' : t = j := by omega
                subst htj'
                exact hjd
            · refine Or.inr ?_
              show ¬ CHalts (pseq (pstages Q j) (Q j)) s
              refine not_halts_pseq_right (stages_run j (by omega) hall) ?_
              rw [show Q j = pseq (G ⟨j, hjk⟩) (pmove m (W + j)) from by
                rw [hQdef]; exact dif_pos hjk]
              refine not_halts_pseq_left ?_
              refine ((hG ⟨j, hjk⟩).2 (uu Yc j) (huu_pre Yc j ⟨j, hjk⟩)).2 ?_
              rw [huu_va Yc j]
              exact hjd
          · refine Or.inr ?_
            show ¬ CHalts (pseq (pstages Q j) (Q j)) s
            exact not_halts_pseq_left hnh
      rcases key k le_rfl with hall | hnh
      · exact absurd (fun t ht => hall t ht ht) hdom
      · exact not_halts_pseq_left hnh

/-! ## Primitive recursion -/

lemma vargs_cons {n : ℕ} (t : Regs) : vargs (n + 1) t = t 0 ::ᵥ vargs n (fun i => t (i + 1)) :=
  rfl

lemma vargs_head {n : ℕ} (t : Regs) : (vargs (n + 1) t).head = t 0 := by
  rw [vargs_cons]
  rfl

lemma vargs_tail {n : ℕ} (t : Regs) : (vargs (n + 1) t).tail = vargs n (fun i => t (i + 1)) := by
  rw [vargs_cons]
  rfl

lemma computes_prec {n : ℕ} {f : List.Vector ℕ n → ℕ} {g : List.Vector ℕ (n + 2) → ℕ}
    {bF bG : ℕ} {F G : Prog} (hF : Computes n bF ((f : List.Vector ℕ n → ℕ) : _ →. ℕ) F)
    (hG : Computes (n + 2) bG ((g : List.Vector ℕ (n + 2) → ℕ) : _ →. ℕ) G) :
    ∃ b P, Computes (n + 1) b
      ((fun v : List.Vector ℕ (n + 1) =>
        v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail) : List.Vector ℕ (n+1) → ℕ)
          : _ →. ℕ) P := by
  classical
  obtain ⟨W, hWF, hWG, hWn⟩ : ∃ W, bF ≤ W ∧ bG ≤ W ∧ n + 3 ≤ W :=
    ⟨max (max bF bG) (n + 3), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  refine ⟨W + n + 5,
    pseq (pmoveBlock 0 W (n + 1))
      (pseq (pcopyBlock (W + 1) 0 (W + n + 4) n)
        (pseq F
          (pseq (pmove n (W + n + 2))
            (pseq (pclearRange 0 n)
              (pseq (pcopy W (W + n + 1) (W + n + 4))
                (pseq (loopDec (W + n + 1)
                    (pseq (pcopy (W + n + 3) 0 (W + n + 4))
                      (pseq (pcopy (W + n + 2) 1 (W + n + 4))
                        (pseq (pcopyBlock (W + 1) 2 (W + n + 4) n)
                          (pseq G
                            (pseq (pmove (n + 2) (W + n + 2))
                              (pseq [Instr.inc (W + n + 3)] (pclearRange 0 W))))))))
                  (pseq (pclear (W + n + 3))
                    (pseq (pmoveBlock W 0 (n + 1)) (pmove (W + n + 2) (n + 1)))))))))),
    computes_of_total (by omega) (fun s hs => ?_)⟩
  set tv : List.Vector ℕ n := vargs n (fun i => s (i + 1)) with htv
  set rk : ℕ → ℕ := fun j => Nat.rec (f tv) (fun y IH => g (y ::ᵥ IH ::ᵥ tv)) j with hrk
  have hrksucc : ∀ y, rk (y + 1) = g (y ::ᵥ rk y ::ᵥ tv) := fun _ => rfl
  have hval : ((fun v : List.Vector ℕ (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) (vargs (n + 1) s)) = rk (s 0) := by
    simp only []
    rw [vargs_head, vargs_tail, hrk, htv]
  -- step 1: save the arguments
  obtain ⟨t1, hr1, ha1, ha2, ha3⟩ :=
    acts_pmoveBlock (src := 0) (dst := W) (m := n + 1) (Or.inl (by omega)) s
  have ht1lo : ∀ i, i < W → t1 i = 0 := by
    intro i hi
    by_cases h : i < n + 1
    · have := ha2 i h
      rwa [Nat.zero_add] at this
    · rw [ha3 i (fun j hj => by omega)]
      exact hs i (by omega) (by omega)
  have ht1arg : ∀ j, j < n + 1 → t1 (W + j) = s j := by
    intro j hj
    have := ha1 j hj
    rwa [Nat.zero_add] at this
  have ht1hi : ∀ i, W + n + 1 ≤ i → t1 i = s i := fun i hi => ha3 i (fun j hj => by omega)
  have ht1head : t1 W = s 0 := by
    have := ht1arg 0 (by omega)
    rwa [Nat.add_zero] at this
  -- step 2: copy the tail into the argument positions of `f`
  obtain ⟨t2, hr2, hb1, hb2, hb3⟩ :=
    acts_pcopyBlock (src := W + 1) (dst := 0) (tmp := W + n + 4) (m := n) (Or.inr (by omega))
      (fun j hj => by omega) (fun j hj => by omega) t1
  have ht2lo : ∀ j, j < n → t2 j = s (j + 1) := by
    intro j hj
    have := hb1 j hj
    rw [Nat.zero_add] at this
    rw [this, show W + 1 + j = W + (j + 1) from by omega, ht1arg (j + 1) (by omega)]
  have ht2out : ∀ i, i ≠ W + n + 4 → n ≤ i → t2 i = t1 i :=
    fun i h1 h2 => hb3 i h1 (fun j hj => by omega)
  have ht2mid : ∀ i, n ≤ i → i < W → t2 i = 0 := by
    intro i h1 h2
    rw [ht2out i (by omega) h1]
    exact ht1lo i h2
  have ht2va : vargs n t2 = tv := by
    rw [htv]
    exact vargs_congr (fun i hi => by rw [ht2lo i hi])
  -- step 3: the base value
  obtain ⟨hFrun, -⟩ := hF.2 t2 (fun i h1 h2 => ht2mid i h1 (by omega))
  have hr3 := hFrun (f tv) (by rw [ht2va]; exact mem_lift_self f tv)
  -- step 4: store it in the accumulator
  have hr4 := impl_pmove (src := n) (dst := W + n + 2) (show n ≠ W + n + 2 by omega)
    (Function.update t2 n (f tv))
  -- step 5: clear the argument positions
  obtain ⟨t5, hr5, hc1, hc2⟩ := acts_pclearRange 0 n
    (fun i => if i = n then 0 else if i = W + n + 2 then (Function.update t2 n (f tv)) n
      else (Function.update t2 n (f tv)) i)
  have ht5lo : ∀ i, i < W → t5 i = 0 := by
    intro i hi
    by_cases h : i < n
    · exact hc1 i (by omega) (by omega)
    · rw [hc2 i (Or.inr (by omega))]
      beta_reduce
      by_cases h2 : i = n
      · rw [h2, if_pos rfl]
      · rw [if_neg h2, if_neg (show i ≠ W + n + 2 by omega),
          Function.update_of_ne h2]
        exact ht2mid i (by omega) hi
  have ht5other : ∀ i, W ≤ i → i ≠ W + n + 2 → i ≠ W + n + 4 → t5 i = t1 i := by
    intro i h1 h2 h3
    rw [hc2 i (Or.inr (by omega))]
    beta_reduce
    rw [if_neg (show i ≠ n by omega), if_neg h2,
      Function.update_of_ne (show i ≠ n by omega)]
    exact ht2out i h3 (by omega)
  have ht5acc : t5 (W + n + 2) = f tv := by
    rw [hc2 _ (Or.inr (by omega))]
    beta_reduce
    rw [if_neg (show W + n + 2 ≠ n by omega), if_pos rfl, Function.update_self]
  -- step 6: load the counter
  have hr6 := impl_pcopy (src := W) (dst := W + n + 1) (tmp := W + n + 4)
    (by omega) (by omega) (by omega) t5
  set t6 : Regs := fun i => if i = W + n + 1 then t5 W else if i = W + n + 4 then 0 else t5 i
    with ht6def
  -- the loop invariant
  set I : Regs → Prop := fun t => ∃ j, j + t (W + n + 1) = s 0 ∧ t (W + n + 3) = j ∧
      t (W + n + 2) = rk j ∧ t W = s 0 ∧ (∀ q, q < n → t (W + 1 + q) = s (q + 1)) ∧
      (∀ i, i < W → t i = 0) ∧ t (W + n + 4) = 0 ∧ (∀ i, W + n + 5 ≤ i → t i = s i) with hIdef
  have hI6 : I t6 := by
    refine ⟨0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht6def]
      beta_reduce
      rw [if_pos rfl, ht5other W (by omega) (by omega) (by omega), ht1head, Nat.zero_add]
    · rw [ht6def]
      beta_reduce
      rw [if_neg (show W + n + 3 ≠ W + n + 1 by omega),
        if_neg (show W + n + 3 ≠ W + n + 4 by omega),
        ht5other _ (by omega) (by omega) (by omega), ht1hi _ (by omega)]
      exact hs _ (by omega) (by omega)
    · rw [ht6def]
      beta_reduce
      rw [if_neg (show W + n + 2 ≠ W + n + 1 by omega),
        if_neg (show W + n + 2 ≠ W + n + 4 by omega)]
      exact ht5acc
    · rw [ht6def]
      beta_reduce
      rw [if_neg (show W ≠ W + n + 1 by omega), if_neg (show W ≠ W + n + 4 by omega),
        ht5other W (by omega) (by omega) (by omega), ht1head]
    · intro q hq
      rw [ht6def]
      beta_reduce
      rw [if_neg (show W + 1 + q ≠ W + n + 1 by omega),
        if_neg (show W + 1 + q ≠ W + n + 4 by omega),
        ht5other _ (by omega) (by omega) (by omega),
        show W + 1 + q = W + (q + 1) from by omega, ht1arg (q + 1) (by omega)]
    · intro i hi
      rw [ht6def]
      beta_reduce
      rw [if_neg (show i ≠ W + n + 1 by omega), if_neg (show i ≠ W + n + 4 by omega)]
      exact ht5lo i hi
    · rw [ht6def]
      beta_reduce
      rw [if_neg (show W + n + 4 ≠ W + n + 1 by omega), if_pos rfl]
    · intro i hi
      rw [ht6def]
      beta_reduce
      rw [if_neg (show i ≠ W + n + 1 by omega), if_neg (show i ≠ W + n + 4 by omega),
        ht5other i (by omega) (by omega) (by omega), ht1hi i (by omega)]
  -- one turn of the loop
  have hstep : ∀ t, I t → t (W + n + 1) ≠ 0 →
      ∃ t', Runs (pseq (pcopy (W + n + 3) 0 (W + n + 4))
        (pseq (pcopy (W + n + 2) 1 (W + n + 4))
          (pseq (pcopyBlock (W + 1) 2 (W + n + 4) n)
            (pseq G (pseq (pmove (n + 2) (W + n + 2))
              (pseq [Instr.inc (W + n + 3)] (pclearRange 0 W)))))))
        (Function.update t (W + n + 1) (t (W + n + 1) - 1)) t' ∧ I t' ∧
        t' (W + n + 1) < t (W + n + 1) := by
    intro t hIt hne
    obtain ⟨j, hj, hY, hA, hX, htail, hlo, hT, hhi⟩ := hIt
    set u : Regs := Function.update t (W + n + 1) (t (W + n + 1) - 1) with hudef
    have huC : u (W + n + 1) = t (W + n + 1) - 1 := by rw [hudef, Function.update_self]
    have huo : ∀ i, i ≠ W + n + 1 → u i = t i := fun i hi => Function.update_of_ne hi _ _
    -- b1
    have hv1 := impl_pcopy (src := W + n + 3) (dst := 0) (tmp := W + n + 4)
      (by omega) (by omega) (by omega) u
    set v1 : Regs := fun i => if i = 0 then u (W + n + 3) else if i = W + n + 4 then 0 else u i
      with hv1def
    -- b2
    have hv2 := impl_pcopy (src := W + n + 2) (dst := 1) (tmp := W + n + 4)
      (by omega) (by omega) (by omega) v1
    set v2 : Regs := fun i => if i = 1 then v1 (W + n + 2) else if i = W + n + 4 then 0 else v1 i
      with hv2def
    -- b3
    obtain ⟨v3, hv3, hd1, hd2, hd3⟩ :=
      acts_pcopyBlock (src := W + 1) (dst := 2) (tmp := W + n + 4) (m := n) (Or.inr (by omega))
        (fun q hq => by omega) (fun q hq => by omega) v2
    have hv30 : v3 0 = j := by
      rw [hd3 0 (by omega) (fun q hq => by omega), hv2def]
      simp only [if_neg (show (0 : ℕ) ≠ 1 by omega), if_neg (show (0 : ℕ) ≠ W + n + 4 by omega),
        hv1def, if_pos rfl]
      rw [huo _ (by omega), hY]
    have hv31 : v3 1 = rk j := by
      rw [hd3 1 (by omega) (fun q hq => by omega), hv2def]
      beta_reduce
      rw [if_pos rfl, hv1def]
      beta_reduce
      rw [if_neg (show W + n + 2 ≠ 0 by omega),
        if_neg (show W + n + 2 ≠ W + n + 4 by omega), huo _ (by omega), hA]
    have hv3tail : ∀ q, q < n → v3 (2 + q) = s (q + 1) := by
      intro q hq
      rw [hd1 q hq, hv2def]
      simp only [if_neg (show W + 1 + q ≠ 1 by omega),
        if_neg (show W + 1 + q ≠ W + n + 4 by omega), hv1def,
        if_neg (show W + 1 + q ≠ 0 by omega)]
      rw [huo _ (by omega)]
      exact htail q hq
    have hv3out : ∀ i, i ≠ W + n + 4 → n + 2 ≤ i → v3 i = u i := by
      intro i h1 h2
      rw [hd3 i h1 (fun q hq => by omega), hv2def]
      simp only [if_neg (show i ≠ 1 by omega), hv1def,
        if_neg (show i ≠ 0 by omega), if_neg h1]
    have hv3mid : ∀ i, n + 2 ≤ i → i < W → v3 i = 0 := by
      intro i h1 h2
      rw [hv3out i (by omega) h1, huo i (by omega)]
      exact hlo i h2
    have hv3va : vargs (n + 2) v3 = j ::ᵥ rk j ::ᵥ tv := by
      rw [vargs_cons, hv30]
      congr 1
      rw [vargs_cons, Nat.zero_add, hv31]
      congr 1
      rw [htv]
      exact vargs_congr (fun q hq => by
        show v3 (q + 1 + 1) = s (q + 1)
        rw [show q + 1 + 1 = 2 + q from by omega]
        exact hv3tail q hq)
    obtain ⟨hGrun, -⟩ := hG.2 v3 (fun i h1 h2 => hv3mid i h1 (by omega))
    have hv4 := hGrun (g (j ::ᵥ rk j ::ᵥ tv)) (by rw [hv3va]; exact mem_lift_self g _)
    -- b5
    have hv5 := impl_pmove (src := n + 2) (dst := W + n + 2) (show n + 2 ≠ W + n + 2 by omega)
      (Function.update v3 (n + 2) (g (j ::ᵥ rk j ::ᵥ tv)))
    set v5 : Regs := fun i => if i = n + 2 then 0 else
      if i = W + n + 2 then (Function.update v3 (n + 2) (g (j ::ᵥ rk j ::ᵥ tv))) (n + 2)
      else (Function.update v3 (n + 2) (g (j ::ᵥ rk j ::ᵥ tv))) i with hv5def
    have hv5acc : v5 (W + n + 2) = rk (j + 1) := by
      rw [hv5def]
      beta_reduce
      rw [if_neg (show W + n + 2 ≠ n + 2 by omega), if_pos rfl, Function.update_self]
    have hv5out : ∀ i, i ≠ n + 2 → i ≠ W + n + 2 → v5 i = v3 i := by
      intro i h1 h2
      rw [hv5def]
      simp only [if_neg h1, if_neg h2, Function.update_of_ne h1]
    -- b6
    have hv6 := impl_inc (W + n + 3) v5
    set v6 : Regs := Function.update v5 (W + n + 3) (v5 (W + n + 3) + 1) with hv6def
    have hv5Y : v5 (W + n + 3) = j := by
      rw [hv5out _ (by omega) (by omega), hv3out _ (by omega) (by omega), huo _ (by omega), hY]
    -- b7
    obtain ⟨v7, hv7, he1, he2⟩ := acts_pclearRange 0 W v6
    have hv7lo : ∀ i, i < W → v7 i = 0 := fun i hi => he1 i (by omega) (by omega)
    have hv7hi : ∀ i, W ≤ i → v7 i = v6 i := fun i hi => he2 i (Or.inr (by omega))
    have hv6out : ∀ i, i ≠ W + n + 3 → v6 i = v5 i :=
      fun i hi => by rw [hv6def]; exact Function.update_of_ne hi _ _
    refine ⟨v7, runs_pseq hv1 (runs_pseq hv2 (runs_pseq hv3 (runs_pseq hv4
      (runs_pseq hv5 (runs_pseq hv6 hv7))))), ⟨j + 1, ?_, ?_, ?_, ?_, ?_, hv7lo, ?_, ?_⟩, ?_⟩
    · rw [hv7hi _ (by omega), hv6out _ (by omega), hv5out _ (by omega) (by omega),
        hv3out _ (by omega) (by omega), huC]
      omega
    · rw [hv7hi _ (by omega), hv6def, Function.update_self, hv5Y]
    · rw [hv7hi _ (by omega), hv6out _ (by omega), hv5acc]
    · rw [hv7hi _ (by omega), hv6out _ (by omega), hv5out _ (by omega) (by omega),
        hv3out _ (by omega) (by omega), huo _ (by omega), hX]
    · intro q hq
      rw [hv7hi _ (by omega), hv6out _ (by omega), hv5out _ (by omega) (by omega),
        hv3out _ (by omega) (by omega), huo _ (by omega)]
      exact htail q hq
    · rw [hv7hi _ (by omega), hv6out _ (by omega), hv5out _ (by omega) (by omega)]
      exact hd2
    · intro i hi
      rw [hv7hi _ (by omega), hv6out _ (by omega), hv5out _ (by omega) (by omega),
        hv3out _ (by omega) (by omega), huo _ (by omega)]
      exact hhi i hi
    · rw [hv7hi _ (by omega), hv6out _ (by omega), hv5out _ (by omega) (by omega),
        hv3out _ (by omega) (by omega), huC]
      omega
  obtain ⟨t7, hr7, hI7, hz7⟩ := runs_loopDec_of_measure (mu := fun t => t (W + n + 1)) hstep t6 hI6
  obtain ⟨jf, hjf, hY7, hA7, hX7, htail7, hlo7, hT7, hhi7⟩ := hI7
  have hjfx : jf = s 0 := by omega
  -- step 8: clear the index register
  have hr8 := impl_clear (W + n + 3) t7
  set t8 : Regs := Function.update t7 (W + n + 3) 0 with ht8def
  have ht8out : ∀ i, i ≠ W + n + 3 → t8 i = t7 i :=
    fun i hi => by rw [ht8def]; exact Function.update_of_ne hi _ _
  -- step 9: restore the arguments
  obtain ⟨t9, hr9, hf1, hf2, hf3⟩ :=
    acts_pmoveBlock (src := W) (dst := 0) (m := n + 1) (Or.inr (by omega)) t8
  -- step 10: deliver the value
  have hr10 := impl_pmove (src := W + n + 2) (dst := n + 1) (show W + n + 2 ≠ n + 1 by omega) t9
  refine Eq.mpr ?_ (runs_pseq hr1 (runs_pseq hr2 (runs_pseq hr3 (runs_pseq hr4 (runs_pseq hr5
    (runs_pseq hr6 (runs_pseq hr7 (runs_pseq hr8 (runs_pseq hr9 hr10)))))))))
  congr 1
  have ht9acc : t9 (W + n + 2) = rk (s 0) := by
    rw [hf3 _ (fun q hq => by omega), ht8out _ (by omega), hA7, hjfx]
  funext i
  by_cases hiA : i = W + n + 2
  · rw [hiA]
    simp only
    rw [Function.update_of_ne (show W + n + 2 ≠ n + 1 by omega)]
    exact hs _ (by omega) (by omega)
  · by_cases hio : i = n + 1
    · rw [hio]
      beta_reduce
      rw [Function.update_self, if_neg (show n + 1 ≠ W + n + 2 by omega), if_pos rfl]
      exact hval.trans ht9acc.symm
    · simp only [if_neg hiA, if_neg hio, Function.update_of_ne hio]
      by_cases hlt : i < n + 1
      · have h1 := hf1 i hlt
        rw [Nat.zero_add] at h1
        rw [h1, ht8out _ (by omega)]
        match i, hlt with
        | 0, _ => rw [Nat.add_zero]; exact hX7.symm
        | (q + 1), hq =>
          rw [show W + (q + 1) = W + 1 + q from by omega]
          exact (htail7 q (by omega)).symm
      · by_cases hblk : W ≤ i ∧ i < W + (n + 1)
        · obtain ⟨q, rfl⟩ : ∃ q, i = W + q := ⟨i - W, by omega⟩
          rw [hf2 q (by omega)]
          exact hs _ (by omega) (by omega)
        · rw [hf3 i (fun q hq => by omega)]
          by_cases hiY : i = W + n + 3
          · rw [hiY, ht8def, Function.update_self]
            exact hs _ (by omega) (by omega)
          · rw [ht8out i hiY]
            by_cases hge : W + n + 5 ≤ i
            · exact (hhi7 i hge).symm
            · by_cases hiW : i < W
              · rw [hlo7 i hiW]
                exact hs i (by omega) (by omega)
              · -- `i` is the counter or the scratch register
                by_cases hiC : i = W + n + 1
                · rw [hiC]
                  rw [show t7 (W + n + 1) = 0 from hz7]
                  exact hs _ (by omega) (by omega)
                · have hiT : i = W + n + 4 := by omega
                  rw [hiT, hT7]
                  exact hs _ (by omega) (by omega)

end Sim
end Lax251941Proofs.PCP
