import Lax185574Proofs.RamParCode

/-!
The parallel combinator: the representation of the two threads, and
facts about runs of the threads.

The active thread is represented by `Rel` as in `RamSimRun`. The
inactive thread is represented by `Rel` in the memory where its saved
cells (base, cursor, buffer start, output count) replace the loaded
ones (`Other`). `Rel.congr` says that `Rel` depends only on the cells a
simulation reads, so both representations survive the steps of the
other thread.
-/

namespace Lax185574Proofs.RamPar

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim

variable {w K : ℕ}

/-! ### Layout arithmetic -/

/-- The global conditions. -/
structure Glob (w K : ℕ) (x : List ℕ) : Prop where
  k8 : 8 ≤ K
  kw : K < w
  xl : x.length < 2 ^ w

/-- The base of the region of thread `b`. -/
theorem geo_base (w K : ℕ) (b : Bool) : (geo w K b).base = 2 ^ (w - 2) * (b.toNat + 1) := rfl

theorem lay {x : List ℕ} (G : Glob w K x) :
    64 ≤ 2 ^ (w - 2) ∧ 2 ^ (w - K) ≤ 2 ^ (w - 2) ∧ 2 ^ w = 4 * 2 ^ (w - 2) := by
  have k8 := G.k8
  have kw := G.kw
  refine ⟨?_, Nat.pow_le_pow_right (by norm_num) (by omega), ?_⟩
  · calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (w - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ w = 2 ^ ((w - 2) + 2) := by congr 1; omega
      _ = 4 * 2 ^ (w - 2) := by rw [pow_add]; ring

/-- The two regions: `[P, P + V)` and `[2 P, 2 P + V)`. -/
theorem base_facts {x : List ℕ} (G : Glob w K x) (b : Bool) :
    64 ≤ (geo w K b).base ∧ (geo w K b).base + 2 ^ (w - K) ≤ 2 ^ w ∧
    ((geo w K b).base + 2 ^ (w - K) ≤ (geo w K (!b)).base ∨
      (geo w K (!b)).base + 2 ^ (w - K) ≤ (geo w K b).base) := by
  obtain ⟨h1, h2, h3⟩ := lay G
  cases b <;> simp only [geo_base, Bool.not_false, Bool.not_true, Bool.toNat_false,
    Bool.toNat_true] <;> omega

/-! ### What a simulation reads -/

/-- The cells a simulation reads. -/
def Sup (g : Geo) (a : ℕ) : Prop :=
  a < 9 ∨ a = 16 ∨ a = 17 ∨ (g.base ≤ a ∧ a < g.base + 2 ^ g.v) ∨ (g.ob ≤ a ∧ a < g.ob + g.cap)

/-- `Rel` depends only on the cells it reads. -/
theorem Rel.congr {g : Geo} {ovf ovf' : ℕ} {x' : List ℕ} {s S S' : State}
    (R : Rel w g [.input] 16 (.buffer ovf) x' [] s S) (hm : WordMem w S'.mem)
    (hi : S'.input = S.input) (ho : S'.out = S.out)
    (hs : ∀ a, Sup g a → S'.mem a = S.mem a) :
    Rel w g [.input] 16 (.buffer ovf') x' [] s S' := by
  have E := R.env
  have hlow : ∀ a, a < 9 → S'.mem a = S.mem a := fun a ha => hs a (Or.inl ha)
  have h16 : S'.mem 16 = S.mem 16 := hs 16 (Or.inr (Or.inl rfl))
  have h17 : S'.mem (16 + 1) = S.mem (16 + 1) := hs 17 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := R.out
  obtain ⟨segs, hT, hx⟩ := R.table
  refine
    { env := ⟨hm, by rw [hlow 0 (by omega)]; exact E.zero, by rw [hlow 1 (by omega)]; exact E.one,
        by rw [hlow 2 (by omega)]; exact E.mask, by rw [hlow 3 (by omega)]; exact E.baseCell,
        E.room, E.low, E.hv⟩
      cword := R.cword
      mem := fun a ha => by
        rw [hs _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))]; exact R.mem a ha
      input := R.input
      cur := by rw [hlow 4 (by omega)]; exact R.cur
      inp := by rw [hlow 4 (by omega)]; exact R.inp
      tot := by rw [hlow 5 (by omega)]; exact R.tot
      table := ⟨segs, ?_, hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ⟨ho.trans h1, by rw [hlow 6 (by omega)]; exact h2, by rw [hlow 7 (by omega)]; exact h3,
        by rw [hlow 8 (by omega)]; exact h4, h5, h6, h7, h8, fun j hj => by
          have hj' : j < s.out.length := hj
          rw [hs _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))]; exact h9 j hj'⟩ }
  cases segs with
  | nil => exact (show False from hT).elim
  | cons seg rest =>
      cases rest with
      | cons _ _ =>
          obtain ⟨-, -, -, h⟩ := hT
          exact (show False from h).elim
      | nil =>
          obtain ⟨n1, n2, hseg, -⟩ := hT
          obtain ⟨e1, e2, e3⟩ := hseg
          refine ⟨n1, n2, ?_, trivial⟩
          show seg = (S'.input.drop (S'.mem (16 + 1))).take (S'.mem 16) ∧
            (0 < S'.mem 16 → S'.mem (16 + 1) + S'.mem 16 ≤ S'.input.length) ∧
            S'.input.length < 2 ^ w
          rw [h16, h17, hi]
          exact ⟨e1, e2, e3⟩

/-! ### The inactive thread -/

/-- The memory with the saved cells of thread `b` in place of the
loaded ones. -/
def swp (b : Bool) (m : ℕ → ℕ) (a : ℕ) : ℕ :=
  if a = 3 then m (sv b) else if a = 4 then m (sv b + 1) else if a = 6 then m (sv b + 2)
  else if a = 7 then m (sv b + 3) else m a

/-- The state with the saved cells of thread `b` loaded. -/
def swpS (b : Bool) (S : State) : State := { S with mem := swp b S.mem }

/-- Thread `b` is represented, with buffer overflow going to `ovf`. -/
abbrev TRel (w K : ℕ) (x : List ℕ) (b : Bool) (ovf : ℕ) (s S : State) : Prop :=
  Rel w (geo w K b) [.input] 16 (.buffer ovf) x [] s S

/-- The inactive thread `b` is represented through its saved cells. -/
def Other (w K : ℕ) (x : List ℕ) (b : Bool) (s S : State) : Prop :=
  TRel w K x b 0 s (swpS b S)

/-- The cells the representation of an inactive thread reads. -/
def OSup (w K : ℕ) (b : Bool) (a : ℕ) : Prop :=
  (a < 9 ∧ a ≠ 3 ∧ a ≠ 4 ∧ a ≠ 6 ∧ a ≠ 7) ∨ a = 16 ∨ a = 17 ∨
    ((geo w K b).base ≤ a ∧ a < (geo w K b).base + 2 ^ (w - K)) ∨ (ob b ≤ a ∧ a < ob b + 2) ∨
    (sv b ≤ a ∧ a < sv b + 4)

theorem Other.frame {x : List ℕ} {b : Bool} {s S S' : State} (h : Other w K x b s S)
    (hm : WordMem w S'.mem) (hi : S'.input = S.input) (ho : S'.out = S.out)
    (hs : ∀ a, OSup w K b a → S'.mem a = S.mem a) : Other w K x b s S' := by
  have hsv := sv_ge b
  refine Rel.congr h (fun a => ?_) hi ho (fun a ha => ?_)
  · simp only [swpS, swp]; split_ifs <;> exact hm _
  · simp only [Sup] at ha
    simp only [swpS, swp]
    split_ifs with h3 h4 h6 h7
    all_goals exact hs _ (by simp only [OSup]; simp only [geo] at ha ⊢; omega)

/-- The cells an inactive thread reads are not written by the steps of
the active thread. -/
theorem osup_not_W {x : List ℕ} (G : Glob w K x) {b : Bool} {a : ℕ} (h : OSup w K b a) :
    ¬ (geo w K (!b)).W a := by
  have hB := base_facts G b
  have hB' := base_facts G (!b)
  have hsv := sv_ge b
  have hob := ob_ge b
  have hob' := ob_ge (!b)
  have hne : ob b ≠ ob (!b) := by cases b <;> simp [ob]
  simp only [Bool.not_not] at hB'
  simp only [OSup] at h
  simp only [Geo.W]
  show ¬ (a = 4 ∨ a = 7 ∨ (9 ≤ a ∧ a ≤ 14) ∨
    ((geo w K (!b)).base ≤ a ∧ a < (geo w K (!b)).base + 2 ^ (w - K)) ∨
    (ob (!b) ≤ a ∧ a < ob (!b) + 2))
  have hob2 : ob b + 4 ≤ ob (!b) ∨ ob (!b) + 4 ≤ ob b := by cases b <;> simp [ob]
  omega

/-! ### Runs of the threads -/

/-- Thread `P` never halts with an output `1 :: y`, `y` of length at
most one. -/
def Never (v : ℕ) (P : Program) (x : List ℕ) : Prop :=
  ∀ y t, y.length ≤ 1 → ¬ RunsTo v P x (1 :: y) t

theorem never_of_long {v k : ℕ} {P : Program} {x : List ℕ} {s : State}
    (h : run v P k (initState x) = some s) (hl : 2 < s.out.length) : Never v P x := by
  intro y t hy ⟨k', s', h1, h2, h3, _⟩
  rcases Nat.lt_or_ge k' k with hk | hk
  · have : run v P k (initState x) = none := by
      rw [show k = k' + ((k - k' - 1) + 1) by omega, run_add, h1]
      exact run_succ_of_terminal h2 _
    rw [h] at this; cases this
  · have h1' : run v P (k + (k' - k)) (initState x) = some s' := by
      rw [show k + (k' - k) = k' by omega]; exact h1
    rw [run_add, h, Option.bind_some] at h1'
    have hp := (run_out_prefix h1').length_le
    rw [h3, List.length_cons] at hp
    omega

theorem never_of_terminal {v k : ℕ} {P : Program} {x : List ℕ} {s : State}
    (h : run v P k (initState x) = some s) (hs : step v P s = none)
    (hb : ∀ y, y.length ≤ 1 → s.out ≠ 1 :: y) : Never v P x := by
  intro y t hy hR
  have := (runsTo_unique hR ⟨k, s, h, hs, rfl, rfl⟩).1
  exact hb y hy this.symm

theorem never_empty {v : ℕ} {P : Program} {x : List ℕ} (hP : P.length = 0) : Never v P x := by
  refine never_of_terminal (k := 0) (s := initState x) rfl
    (step_none_of_length_le (by simp [initState, hP])) ?_
  intro y _ h
  simp [initState] at h

/-- A live thread has made fewer steps than any accepting run takes. -/
theorem alive_lt {v c t : ℕ} {p : Program} {x' y : List ℕ} {s : State}
    (hrun : run v p c (initState x') = some s) (hpc : s.pc < p.length ∨ s.pc = 0)
    (hR : RunsTo v p x' (1 :: y) t) : c < t := by
  obtain ⟨k, sT, hk, hsT, hout, ht⟩ := hR
  by_contra hct
  rcases Nat.lt_or_ge k c with hkc | hkc
  · have : run v p c (initState x') = none := by
      rw [show c = k + ((c - k - 1) + 1) by omega, run_add, hk]
      exact run_succ_of_terminal hsT _
    rw [hrun] at this; cases this
  · have htc : terminalCost p sT = 0 := by omega
    have hck : c = k := by omega
    subst hck
    rw [hrun] at hk
    cases hk
    rw [terminalCost_eq] at htc
    split_ifs at htc with h
    rcases hpc with h1 | h1
    · omega
    · have hp : p.length = 0 := by omega
      have h0 : step v p (initState x') = none := step_none_of_length_le (by simp [initState, hp])
      cases c with
      | zero =>
          simp only [run_zero, Option.some.injEq] at hrun
          rw [← hrun] at hout; simp [initState] at hout
      | succ c =>
          rw [run_succ, h0] at hrun; cases hrun

theorem run_snoc {v k : ℕ} {P : Program} {s₀ s s' : State} (h : run v P k s₀ = some s)
    (h' : step v P s = some s') : run v P (k + 1) s₀ = some s' := by
  rw [run_add, h, Option.bind_some, run_succ, h']
  rfl

end Lax185574Proofs.RamPar
