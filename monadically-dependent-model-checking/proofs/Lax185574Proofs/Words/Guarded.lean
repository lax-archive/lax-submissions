import Lax185574Proofs.Words.Computes

/-!
`Computes` for programs whose values may outgrow the input.

`computes_of_run` asks that every value of the run is bounded by a
polynomial of fixed degree in the input. Some algorithms of this
submission write outputs whose size is polynomial in parameters beyond
the input, with a degree that is not fixed before them. At a word length
where such a value does not fit, the machine would compute modulo `2^w`
and could halt with a wrong output, which the first clause of
`Computes` forbids.

The guarded program avoids this. It first computes `W = 2^(w-r) - 1`
for a constant `r` of the layout, by `not` and a division, and stores it
in the scalar `W`. Then it runs the compiled IMP+ command, which is
expected to keep every value at most `W` and to set the scalar `ovf` to
a nonzero value when it would have to go beyond. At the end, the program
halts if `ovf` is zero and loops forever otherwise. So a halting run has
an output computed without overflow. Once the time bound fits into a
word, the command is expected to finish without setting `ovf`.
-/

namespace Lax185574Proofs.Words

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning Lax808846Proofs.Machine
open Lax185574.WordEncoding Lax185574.Computing

/-- The number of bits the guarded program reserves for the layout. -/
def guardBits (L : Layout) : ℕ := L.temps + 2 + L.scalars.length + L.arrays.length

/-- The guarded program: compute `W`, run the command, then halt if
`ovf` is zero and loop forever otherwise. -/
def guardedProgram (L : Layout) (c : Com) : Program :=
  [.not (L.varAddr "W") (L.varAddr "W"), .set 0 (2 ^ guardBits L),
    .div (L.varAddr "W") (L.varAddr "W") 0] ++ compile L c 3 ++
  [.jzero (L.varAddr "ovf") (3 + size L c + 2), .jump (3 + size L c + 1), .halt]

/-- A state at a jump to itself never halts. -/
theorem not_runsTo_of_loop {w : ℕ} {p : Program} {x : List ℕ} {k₀ : ℕ} {sL : State}
    (hL : run w p k₀ (initState x) = some sL) (hj : p[sL.pc]? = some (.jump sL.pc))
    {y : List ℕ} {t : ℕ} : ¬ RunsTo w p x y t := by
  rintro ⟨k, s, hk, hs, -, -⟩
  have hstay : ∀ n, run w p n sL = some sL := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [run_succ, step_eq, hj]
      show ((Instr.jump sL.pc).effect w sL).bind (run w p n) = _
      rw [effect_jump]
      exact ih
  have h1 : run w p (k₀ + (k + 1)) (initState x) = some sL := by
    rw [run_add, hL]; exact hstay _
  have h2 : run w p (k + (k₀ + 1)) (initState x) = none := by
    rw [run_add, hk]; exact run_succ_of_terminal hs _
  rw [show k₀ + (k + 1) = k + (k₀ + 1) by omega] at h1
  rw [h1] at h2
  exact absurd h2 (by simp)

theorem two_pow_sub_one_div {w r : ℕ} (h : r ≤ w) : (2 ^ w - 1) / 2 ^ r = 2 ^ (w - r) - 1 := by
  have hw : 2 ^ w = 2 ^ r * 2 ^ (w - r) := by rw [← pow_add]; congr 1; omega
  have hr : 0 < 2 ^ r := by positivity
  have hq : 0 < 2 ^ (w - r) := by positivity
  rw [hw]
  generalize 2 ^ r = A at hr ⊢
  generalize 2 ^ (w - r) = Q at hq ⊢
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm, Nat.mul_sub_one]; omega
  · have : 0 < A * Q := Nat.mul_pos hr hq
    rw [Nat.sub_add_cancel hq, Nat.mul_comm Q A]; omega

/-- The memory after the three instructions computing `W`. -/
def preludeMem (L : Layout) (w : ℕ) : ℕ → ℕ :=
  setCell w (setCell w (setCell w (fun _ => 0) (L.varAddr "W") (2 ^ w - 1)) 0
    (2 ^ guardBits L)) (L.varAddr "W") (2 ^ (w - guardBits L) - 1)

/-- The state after the three instructions computing `W`. -/
def preludeState (L : Layout) (w : ℕ) (x : List ℕ) : State :=
  { initState x with pc := 3, mem := preludeMem L w }

theorem prelude_run {L : Layout} {c : Com} {w : ℕ} (x : List ℕ) (hr : guardBits L < w)
    (hwa : L.varAddr "W" < 2 ^ w) :
    run w (guardedProgram L c) 3 (initState x) = some (preludeState L w x) := by
  have hR : 2 ^ guardBits L < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) hr
  have h0 : (0 : ℕ) < 2 ^ w := by positivity
  have hne : (0 : ℕ) ≠ L.varAddr "W" := by
    have := temps_le_varAddr L "W"; omega
  rw [show (3 : ℕ) = 1 + (1 + 1) from rfl, run_add, run_one (ins := .not (L.varAddr "W")
    (L.varAddr "W")) (by simp [guardedProgram, initState]), effect_not hwa]
  simp only [Option.bind_some]
  rw [run_add, run_one (ins := .set 0 (2 ^ guardBits L)) (by simp [guardedProgram, initState]),
    effect_set]
  simp only [Option.bind_some]
  rw [run_one (ins := .div (L.varAddr "W") (L.varAddr "W") 0) (by simp [guardedProgram, initState]),
    effect_div hwa h0]
  simp only [initState, preludeState, preludeMem]
  congr 2
  rw [setCell_of_ne _ _ h0 (Ne.symm hne), setCell_self _ hwa (by omega), setCell_self _ h0 hR,
    Nat.sub_zero, two_pow_sub_one_div (by omega)]

theorem represents_prelude {L : Layout} {w : ℕ} (ext : String → ℕ) (x : List ℕ)
    (hW : "W" ∈ L.scalars) (hwa : L.varAddr "W" < 2 ^ w) (hWw : 2 ^ (w - guardBits L) - 1 < 2 ^ w) :
    Represents L ((initEnv ext x).setVar "W" (2 ^ (w - guardBits L) - 1)) (preludeState L w x) where
  vars y hy := by
    have h0 : (0 : ℕ) < 2 ^ w := by positivity
    have hne0 : L.varAddr y ≠ 0 := by have := temps_le_varAddr L y; omega
    simp only [preludeState, preludeMem, vars_setVar]
    by_cases hyW : y = "W"
    · subst hyW; simp only [if_true]; exact setCell_self _ hwa hWw
    · have hne : L.varAddr y ≠ L.varAddr "W" := fun h => hyW (varAddr_inj L hy hW h)
      rw [if_neg hyW, setCell_of_ne _ _ hwa hne, setCell_of_ne _ _ h0 hne0,
        setCell_of_ne _ _ hwa hne]
      rfl
  arrs a ha i hi := by
    have h0 : (0 : ℕ) < 2 ^ w := by positivity
    have hne0 : L.arrAddr a i ≠ 0 := by have := temps_le_arrAddr L a i; omega
    have hne : L.arrAddr a i ≠ L.varAddr "W" := fun h => varAddr_ne_arrAddr L hW i h.symm
    simp only [preludeState, preludeMem, arrs_setVar]
    rw [setCell_of_ne _ _ hwa hne, setCell_of_ne _ _ h0 hne0, setCell_of_ne _ _ hwa hne]
    show (0 : ℕ) = (List.replicate (ext a) 0).getD i 0
    simp only [initEnv, arrs_setVar, List.length_replicate] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl
  inp := rfl
  out := rfl

theorem guarded_getElem_post {L : Layout} {c : Com} (j : ℕ) :
    (guardedProgram L c)[3 + size L c + j]? =
      [Instr.jzero (L.varAddr "ovf") (3 + size L c + 2), .jump (3 + size L c + 1), .halt][j]? := by
  rw [guardedProgram, List.getElem?_append_right (by simp; omega)]
  congr 1
  simp only [List.length_append, List.length_cons, List.length_nil, compile_length]
  omega

theorem guarded_fits (L : Layout) (c : Com) :
    Fits (guardedProgram L c) 3 (compile L c 3) := by
  intro i hi
  rw [guardedProgram, List.append_assoc, List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]

/-- **Guarded programs compute.** Suppose that for every `W` above
`c₀ · (|x| + M + 1)^e`, the command, started with `W` in the scalar
`W`, runs with every value at most `W`, produces the word of `b` unless
it sets `ovf`, and, once the time bound fits into `2^r · (W + 1)`, does
not set `ovf` and stays within the time bound. Then the guarded program
computes `b` from `a`. -/
theorem computes_of_guarded {α : Type*} {β : Type*} [WordEncoding α] [WordEncoding β]
    {L : Layout} {cmd : Com} (hok : Com.Ok L cmd) (hW : "W" ∈ L.scalars)
    (hO : "ovf" ∈ L.scalars) {e c₀ : ℕ} (he : 1 ≤ e) (hc₀ : 1 ≤ c₀)
    {a : α} {b : β} {T : ℕ → ℕ} (hx : toWord a ≠ [])
    (hrun : ∀ W : ℕ, c₀ * ((toWord a).length + maxEntry (toWord a) + 1) ^ e ≤ W + 1 →
      ∃ (ext : String → ℕ) (σ' : Env) (k : ℕ),
        Run (W + 1) cmd ((initEnv ext (toWord a)).setVar "W" W) σ' k ∧
        (σ'.vars "ovf" = 0 → σ'.out = toWord b) ∧
        (T (wordLength a) ≤ 2 ^ guardBits L * (W + 1) →
          σ'.vars "ovf" = 0 ∧ L.const * k + 5 ≤ T (wordLength a))) :
    Computes (guardedProgram L cmd) e (2 ^ (guardBits L + 1) * c₀) a b T := by
  set x := toWord a with hxdef
  set r := guardBits L with hr
  set M := maxEntry x
  set X := (x.length + M + 1) ^ e with hX
  intro w hadm
  have hcX : 2 ^ (r + 1) * c₀ * X ≤ 2 ^ w := hadm M (maxEntry_mem hx)
  have hlen : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hXge : x.length + M + 1 ≤ X := by
    calc x.length + M + 1 = (x.length + M + 1) ^ 1 := (pow_one _).symm
      _ ≤ X := Nat.pow_le_pow_right (by omega) he
  -- the word length leaves room for `r` bits
  have hrw : r + 2 ≤ w := by
    have : 2 ^ (r + 2) ≤ 2 ^ w := by
      calc 2 ^ (r + 2) = 2 ^ (r + 1) * 1 * 2 := by ring
        _ ≤ 2 ^ (r + 1) * c₀ * X := by gcongr; omega
        _ ≤ 2 ^ w := hcX
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hsplit : 2 ^ w = 2 ^ r * 2 ^ (w - r) := by rw [← pow_add]; congr 1; omega
  set W := 2 ^ (w - r) - 1 with hWdef
  have hW1 : W + 1 = 2 ^ (w - r) := by
    have : 0 < 2 ^ (w - r) := by positivity
    omega
  have hc₀X : c₀ * X ≤ W + 1 := by
    rw [hW1]
    have h2 : 2 ^ (r + 1) = 2 ^ r * 2 := by ring
    rw [hsplit, h2] at hcX
    have hpos : 0 < 2 ^ r := by positivity
    have : 2 ^ r * (2 * (c₀ * X)) ≤ 2 ^ r * 2 ^ (w - r) := by
      calc 2 ^ r * (2 * (c₀ * X)) = 2 ^ r * 2 * c₀ * X := by ring
        _ ≤ _ := hcX
    have := Nat.le_of_mul_le_mul_left this hpos
    omega
  obtain ⟨ext, σ', k, ⟨k', hk', hbs⟩, hout, htime⟩ := hrun W hc₀X
  -- the layout fits
  have hPQ : L.temps + 2 + L.scalars.length + L.arrays.length ≤ 2 ^ r := by
    have := Nat.lt_two_pow_self (n := r); simp only [hr, guardBits] at this ⊢; omega
  have hfit : L.FitsWords (W + 1) w := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hW1]; exact Nat.one_lt_two_pow (by omega)
    · rw [hW1, hsplit]; exact Nat.le_mul_of_pos_left _ (by positivity)
    · simp only [Layout.span]
      rw [hW1, hsplit]
      have hq : 1 ≤ 2 ^ (w - r) := Nat.one_le_two_pow
      generalize 2 ^ (w - r) = Q at hq ⊢
      nlinarith
  have hwa : L.varAddr "W" < 2 ^ w := L.varAddr_lt_two_pow hfit hW
  have hoa : L.varAddr "ovf" < 2 ^ w := L.varAddr_lt_two_pow hfit hO
  have hWw : W < 2 ^ w := by have := hfit.bound; omega
  have hpre := prelude_run (c := cmd) x (by omega) hwa
  have hrep := represents_prelude ext x hW hwa hWw
  have hinpB : ((initEnv ext x).setVar "W" W).InpBounded (W + 1) := by
    intro v hv
    have := le_maxEntry (x := x) hv
    have : X ≤ c₀ * X := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨t, s', ht, hrun', hpc', hrep'⟩ :=
    compile_correct hfit hbs hok hinpB 3 (preludeState L w x) rfl hrep (guarded_fits L cmd)
  have hjz : (guardedProgram L cmd)[s'.pc]? =
      some (.jzero (L.varAddr "ovf") (3 + size L cmd + 2)) := by
    rw [hpc', show 3 + size L cmd = 3 + size L cmd + 0 from rfl, guarded_getElem_post]; rfl
  have hmem : s'.mem (L.varAddr "ovf") = σ'.vars "ovf" := hrep'.vars "ovf" hO
  have hreach : run w (guardedProgram L cmd) (3 + t) (initState x) = some s' :=
    run_trans hpre hrun'
  by_cases hov : σ'.vars "ovf" = 0
  · -- the program halts with the output of the command
    set s'' : State := { s' with pc := 3 + size L cmd + 2 } with hs''
    have hstep : run w (guardedProgram L cmd) 1 s' = some s'' := by
      rw [run_one hjz, effect_jzero hoa, hmem, if_pos hov]
    have hhalt : (guardedProgram L cmd)[s''.pc]? = some .halt := by
      rw [hs'', guarded_getElem_post]; rfl
    have hRuns : RunsTo w (guardedProgram L cmd) x (toWord b) (3 + t + 1 + 1) := by
      refine ⟨3 + t + 1, s'', run_trans hreach hstep, ?_, ?_, ?_⟩
      · rw [step_eq, hhalt]; rfl
      · rw [hs'']; show s'.out = _; rw [hrep'.out, hout hov]
      · rw [terminalCost_of_getElem? hhalt]
    refine ⟨fun y t' h => (runsTo_unique h hRuns).1, fun hT y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine ⟨3 + t + 1 + 1, ?_, hRuns⟩
    show 3 + t + 1 + 1 ≤ T (wordLength a)
    have hT' : T (wordLength a) ≤ 2 ^ r * (W + 1) := by rw [hW1, ← hsplit]; exact hT
    have h1 := (htime hT').2
    have h2 : L.const * k' ≤ L.const * k := Nat.mul_le_mul_left _ hk'
    omega
  · -- the program loops forever
    set s'' : State := { s' with pc := 3 + size L cmd + 1 } with hs''
    have hstep : run w (guardedProgram L cmd) 1 s' = some s'' := by
      rw [run_one hjz, effect_jzero hoa, hmem, if_neg hov]
      simp [hs'', hpc']
    have hloop : (guardedProgram L cmd)[s''.pc]? = some (.jump s''.pc) := by
      rw [hs'', guarded_getElem_post]; rfl
    refine ⟨fun y t' h => absurd h (not_runsTo_of_loop (run_trans hreach hstep) hloop),
      fun hT => ?_⟩
    have hT' : T (wordLength a) ≤ 2 ^ r * (W + 1) := by rw [hW1, ← hsplit]; exact hT
    exact absurd (htime hT').1 hov

end Lax185574Proofs.Words
