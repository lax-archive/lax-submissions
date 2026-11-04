import Lax185574Proofs.Conversions.Ram.ConsStage

/-!
The program of cl:from-merge-to-construction: read the graph and the
merge sequence, run the stages into the buffer, then write the colors
of the initial partial graph, the number of steps and the steps.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574Proofs.Conversions.MergeConstruction

/-- Read the first stage: its partition into `cur`, and its relation,
which no stage needs. -/
def readFirst : Com :=
  .ite (.lt (.lit 0) (.var "m"))
    (.seq (readPartition "cur") (.seq (.read "c") (readRows "rel" "c"))) .skip

/-- Write the colors `0, …, n - 1`, the number of steps and the steps. -/
def writeScript : Com :=
  .seq (.write (.var "n")) (.seq (forUp "v" (.var "n") (.write (.var "v")))
    (.seq (.write (.div (.var "p") (.lit 3))) writeBuf))

/-- The whole program. -/
def consProg : Com :=
  .seq (.read "n") (.seq (readRows "adj" "n") (.seq (.read "m") (.seq readFirst
    (.seq (forUp "j" (.var "m") stageM) writeScript))))

/-- The scalars and arrays of `consProg`. -/
def consLayout : Lax808846Proofs.Compile.Layout :=
  ⟨["n", "m", "j", "c", "p", "s1", "s2", "s3", "x", "y", "a", "b", "lo", "hi", "v", "i", "r", "d",
    "k", "x1", "pc", "fl", "e", "f"],
    ["adj", "cur", "nxt", "rel", "res", "bad", "unr", "pos", "buf"], 8⟩

theorem consProg_ok : Lax808846Proofs.Compile.Com.Ok consLayout consProg := by
  simp [consProg, readFirst, writeScript, writeBuf, readRows, readRow, readElem, forUp,
    readPartition, readPart, readPartElem, stageM, loadNext, flagPhase, matFill, rowFill, rm, eqE,
    flagScan, flagStep, lohi, cBad, cUnr, cPos, cRes, emitResolves, resBody, pushVars, pairSet,
    pairSetStep, emitMerges, mrgBody, copyCur, consLayout, Lax808846Proofs.Compile.Com.Ok,
    Lax808846Proofs.Compile.Cond.Ok, Lax808846Proofs.Compile.condExpr,
    Lax808846Proofs.Compile.Expr.Ok]

variable {n : ℕ} (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n)))

theorem length_stepCode (s : Step) : (stepCode s).length = 3 := by cases s <;> rfl

theorem length_flatMap_stepCode (l : List Step) : (l.flatMap stepCode).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons s l ih => simp [List.flatMap_cons, length_stepCode, ih]; ring

theorem codes_lt (j : ℕ) : ∀ v ∈ codesBefore G ms j, v < n + 3 := by
  classical
  induction j with
  | zero => simp [codesBefore]
  | succ j ih =>
    intro v hv
    rw [codesBefore_succ] at hv
    simp only [List.mem_append] at hv
    rcases hv with hv | hv | hv
    · exact ih v hv
    · simp only [resTriples, List.mem_flatMap, List.mem_range] at hv
      obtain ⟨a, ha, b, hb, hv⟩ := hv
      split at hv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simp at hv
    · simp only [mrgTriples, List.mem_flatMap, List.mem_range] at hv
      obtain ⟨u, hu, hv⟩ := hv
      split at hv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        have := labJ_lt ms (j + 1) hu
        rcases hv with rfl | rfl | rfl <;> omega
      · simp at hv

/-- **The word of the script**, as the program writes it. -/
theorem toWord_script : toWord (script G ms) =
    (n :: List.range n) ++ ((codesBefore G ms ms.length).length / 3 :: codesBefore G ms ms.length) := by
  have hc : toWord (fun v : Fin n => (v : ℕ)) = n :: List.range n := by
    change (List.ofFn fun v : Fin n => (v : ℕ)).length ::
      ((List.ofFn fun v : Fin n => (v : ℕ)).map toWord).flatten = _
    rw [ofFn_eq_range_map n (fun v => v)]
    simp only [List.length_map, List.length_range, List.map_map]
    congr 1
    have : ∀ l : List ℕ, (l.map (toWord ∘ fun v => v)).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl
    exact this _
  have hs : toWord (script G ms).steps = (script G ms).steps.length ::
      ((script G ms).steps.flatMap stepCode) := by
    change (script G ms).steps.length :: ((script G ms).steps.map toWord).flatten = _
    rfl
  change toWord (script G ms).colors ++ toWord (script G ms).steps = _
  rw [hs]
  have hsteps : (script G ms).steps.flatMap stepCode = codesBefore G ms ms.length := rfl
  rw [hsteps, show (script G ms).colors = fun v : Fin n => (v : ℕ) from rfl, hc]
  congr 2
  rw [← hsteps, length_flatMap_stepCode]
  omega

variable {G ms} in
theorem ConsBase.setVar {cap j : ℕ} {τ : Env} (h : ConsBase G ms cap j τ) (x : String)
    (hx : x ∉ ["n", "m", "p"]) (v : ℕ) : ConsBase G ms cap j (τ.setVar x v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  exact ⟨by simp [Ne.symm hx.1, h.hn], by simp [Ne.symm hx.2.1, h.hm], h.hadj.of_eq (by simp),
    h.hres.of_eq (by simp), h.hcur.of_eq (by simp),
    h.hbuf.of_eq (by simp [Ne.symm hx.2.2]) (by simp), by simpa using h.hnxt,
    by simpa using h.hrel, by simpa using h.hbad, by simpa using h.hunr, by simpa using h.hpos,
    by simpa using h.hinp⟩

/-- The capacity of the buffer. -/
def consCap (n m : ℕ) : ℕ := 3 * m * (n * n + n)

/-- The array lengths of `consProg`. -/
def consExt (n m : ℕ) : String → ℕ := fun a =>
  if a = "adj" ∨ a = "rel" ∨ a = "res" ∨ a = "bad" ∨ a = "unr" ∨ a = "pos" then n * n
  else if a = "cur" ∨ a = "nxt" then n
  else if a = "buf" then consCap n m else 0

theorem labJ_zero_nil (hms : ms = []) {v : ℕ} (hv : v < n) : labJ ms 0 v = 0 := by
  subst hms; exact labJ_last [] hv

theorem toWord_ms :
    toWord ms = ms.length :: (ms.map fun p => toWord p.1 ++ toWord p.2).flatten := rfl

/-- **The run of the program.** -/
theorem consProg_run :
    ∃ σ', Run (valBound 8 3 (toWord (G, ms))) consProg
      (initEnv (consExt n ms.length) (toWord (G, ms))) σ'
      (2000 * (ms.length + 1) * (n + 1) ^ 2) ∧ σ'.out = toWord (script G ms) := by
  classical
  set m := ms.length with hm
  set x := toWord (G, ms) with hx
  have hx' : x = toWord G ++ toWord ms := rfl
  set B := valBound 8 3 x with hB
  set cap := consCap n m with hcap
  have hxG : toWord G = n :: ((nbhds G).map toWord).flatten := toWord_graph_nbhds G
  have hxS := toWord_ms ms
  have hnM : n ≤ maxEntry x := le_maxEntry (by rw [hx', hxG]; simp)
  have hmx : m + 2 ≤ x.length := by
    rw [hx', List.length_append, hxG, hxS]
    have : m ≤ ((ms.map fun p => toWord p.1 ++ toWord p.2).flatten).length := by
      rw [hm]
      have key : ∀ l : List (Setoid (Fin n) × SimpleGraph (Fin n)),
          l.length ≤ ((l.map fun p => toWord p.1 ++ toWord p.2).flatten).length := by
        intro l
        induction l with
        | nil => simp
        | cons q l ih =>
          simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
          have : 1 ≤ (toWord q.1).length := by rw [toWord_setoid_words]; simp
          omega
      exact key ms
    simp only [List.length_cons]
    omega
  set X := m + n + 2
  have hBX : X * X * X * 8 ≤ B := by
    simp only [hB, valBound]
    have : X ≤ x.length + maxEntry x + 1 := by omega
    have h3 : X ^ 3 ≤ (x.length + maxEntry x + 1) ^ 3 := Nat.pow_le_pow_left this 3
    nlinarith
  have hcapB : n * n + cap + m + 2 * n + 3 < B := by
    simp only [hcap, consCap]
    have h1 : (m + 1) * (n + 1) * (n + 1) ≤ X * X * X :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    nlinarith
  have hB2 : n * n + n + 1 < B := by omega
  have hnn : n ≤ n * n := Nat.le_mul_self n
  -- reading the graph
  set σ0 := initEnv (consExt n m) x with hσ0
  set σ1 : Env := { σ0.setVar "n" n with inp := ((nbhds G).map toWord).flatten ++ toWord ms }
    with hσ1
  have hr1 : Run B (.read "n") σ0 σ1 1 := Run.read (by simp [hσ0, initEnv, hx', hxG])
  obtain ⟨σ2, hr2, hinp2, hlen2, hadj2⟩ := readRows_run (B := B) (arr := "adj") (cnt := "n")
    (L := nbhds G) (σ := σ1) (rest := toWord ms) (by decide) (by decide) (by simp [hσ1])
    (by simp [hσ1, length_nbhds]) (by simp [hσ1])
    (by simp [hσ1, hσ0, initEnv, consExt, length_nbhds]) (by rw [length_nbhds]; omega)
    (by rw [length_nbhds]; omega)
  have hn2 : σ2.vars "n" = n := by rw [hr2.frame_var "n" (by decide)]; simp [hσ1]
  -- the number of stages
  set σ3 : Env := { σ2.setVar "m" m with inp := (ms.map fun p => toWord p.1 ++ toWord p.2).flatten }
    with hσ3
  have hr3 : Run B (.read "m") σ2 σ3 1 := Run.read (by rw [hinp2, hxS])
  have hσ2a : ∀ a, a ≠ "adj" → σ2.arrs a = σ0.arrs a := fun a ha => by
    rw [hr2.frame_arr a (by simp [readRows, readRow, readElem, forUp, Com.warrs]; exact ha)]
    simp [hσ1]
  -- the first stage
  have hfirst : ∃ σ4 K4, Run B readFirst σ3 σ4 K4 ∧ K4 ≤ 50 * (n + 1) * (n + 1) ∧
      Vec σ4 "cur" n (labJ ms 0) ∧
      σ4.inp = ((ms.drop 1).map fun p => toWord p.1 ++ toWord p.2).flatten ∧
      (∀ y, y ∈ ["n", "m", "p"] → σ4.vars y = σ3.vars y) ∧
      (∀ a, a ∈ ["adj", "res", "buf", "nxt", "bad", "unr", "pos"] → σ4.arrs a = σ3.arrs a) ∧
      (∀ a, (σ4.arrs a).length = (σ3.arrs a).length) ∧ σ4.out = σ3.out := by
    have hc : (Cond.lt (.lit 0) (.var "m")).evalB B σ3 = some (decide (0 < m)) := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by simp [hσ3]; omega))]
      simp [hσ3]
    by_cases hm0 : 0 < m
    · have hms : 0 < ms.length := by omega
      have hinp : σ3.inp = toWord ms[0].1 ++ (toWord ms[0].2 ++
          ((ms.drop 1).map fun p => toWord p.1 ++ toWord p.2).flatten) := by
        have key : ∀ (l : List (Setoid (Fin n) × SimpleGraph (Fin n))) (h : 0 < l.length),
            (l.map fun p => toWord p.1 ++ toWord p.2).flatten = toWord l[0].1 ++ (toWord l[0].2 ++
              ((l.drop 1).map fun p => toWord p.1 ++ toWord p.2).flatten) := by
          intro l h
          cases l with
          | nil => simp at h
          | cons a l => simp
        simp only [hσ3]
        exact key ms hms
      obtain ⟨τ1, hr1', hinp1, hv1⟩ := readPartition_run (B := B) (dst := "cur") ms[0].1 hinp
        (by simp [hσ3, hσ2a "cur" (by decide), hσ0, initEnv, consExt]) (by omega)
      set R := ms[0].2
      have hinp1' : τ1.inp = n :: (((nbhds R).map toWord).flatten ++
          ((ms.drop 1).map fun p => toWord p.1 ++ toWord p.2).flatten) := by
        rw [hinp1, toWord_graph_nbhds]; rfl
      set τ2 : Env := { τ1.setVar "c" n with inp := ((nbhds R).map toWord).flatten ++
          ((ms.drop 1).map fun p => toWord p.1 ++ toWord p.2).flatten } with hτ2
      have hr2' : Run B (.read "c") τ1 τ2 1 := Run.read hinp1'
      have hfr1 : ∀ y, y ∈ ["n", "m", "p"] → τ1.vars y = σ3.vars y := by
        intro y hy
        refine hr1'.frame_var y ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl <;>
          simp [readPartition, readPart, readPartElem, forUp, Com.wvars]
      have hfa1 : ∀ a, a ≠ "cur" → τ1.arrs a = σ3.arrs a := fun a ha =>
        hr1'.frame_arr a (by simp [readPartition, readPart, readPartElem, forUp, Com.warrs]; exact ha)
      obtain ⟨τ3, hr3', hinp3, -, -⟩ := readRows_run (B := B) (arr := "rel") (cnt := "c")
        (L := nbhds R) (σ := τ2)
        (rest := ((ms.drop 1).map fun p => toWord p.1 ++ toWord p.2).flatten) (by decide) (by decide)
        (by simp [hτ2]) (by simp [hτ2, length_nbhds])
        (by simp [hτ2, hfr1 "n" (by decide), hσ3, hn2])
        (by simp [hτ2, hfa1 "rel" (by decide), hσ3, hσ2a "rel" (by decide), hσ0, initEnv,
          consExt, length_nbhds])
        (by rw [length_nbhds]; omega) (by rw [length_nbhds]; omega)
      refine ⟨τ3, _, Run.ite_true (by rw [hc]; simp [hm0]) (Run.seq hr1' (Run.seq hr2' hr3')),
        by simp only [Cond.size, size_lit, size_var, length_nbhds]; nlinarith, ?_, hinp3,
        fun y hy => ?_, fun a ha => ?_, fun a => ?_, ?_⟩
      · rw [labJ_of_lt ms hms]
        exact hv1.of_eq (by rw [hr3'.frame_arr "cur" (by decide)]; simp [hτ2])
      · rw [hr3'.frame_var y (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl <;> decide)]
        simp only [hτ2]
        rw [vars_setVar, if_neg (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl | rfl <;> decide), hfr1 y hy]
      · rw [hr3'.frame_arr a (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
        simp only [hτ2, arrs_setVar]
        exact hfa1 a (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      · rw [run_length_arrs hr3']
        simp only [hτ2, arrs_setVar]
        rw [run_length_arrs hr1']
      · rw [hr3'.out_eq (by decide)]
        simp only [hτ2, out_setVar]
        rw [hr1'.out_eq (by simp [readPartition, readPart, readPartElem, forUp, Com.NoWrite])]
    · have hms : ms = [] := List.eq_nil_of_length_eq_zero (by omega)
      refine ⟨σ3, _, Run.ite_false (by rw [hc]; simp [hm0]) Run.skip, by simp; nlinarith,
        ⟨by simp [hσ3, hσ2a "cur" (by decide), hσ0, initEnv, consExt], fun v hv => ?_⟩,
        by simp [hσ3, hms], fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩
      rw [labJ_zero_nil ms hms hv]
      simp [hσ3, hσ2a "cur" (by decide), hσ0, initEnv, consExt, hv]
  obtain ⟨σ4, K4, hr4, hK4, hcur4, hinp4, hv4, ha4, hl4, ho4⟩ := hfirst
  -- the state before the stages
  have hb4 : ConsBase G ms cap 0 σ4 := by
    refine ⟨by rw [hv4 "n" (by decide)]; simp [hσ3, hn2], by rw [hv4 "m" (by decide)]; simp [hσ3, hm],
      ⟨?_, fun u hu z hz => ?_⟩, ⟨?_, fun u hu z hz => ?_⟩, hcur4, ⟨?_, ?_, fun i h => ?_⟩,
      ?_, ?_, ?_, ?_, ?_, by simpa using hinp4⟩
    · rw [ha4 "adj" (by decide)]; simp only [hσ3, arrs_setVar]; rw [hlen2, length_nbhds]
    · rw [ha4 "adj" (by decide)]; simp only [hσ3, arrs_setVar]
      rw [hadj2 u (by rw [length_nbhds]; exact hu) z hz]
      exact congrArg some (ite_eq_ind (mem_nbhds (by rw [length_nbhds]; exact hu)))
    · rw [ha4 "res" (by decide)]; simp [hσ3, hσ2a "res" (by decide), hσ0, initEnv, consExt]
    · rw [ha4 "res" (by decide)]
      simp only [hσ3, arrs_setVar, hσ2a "res" (by decide), hσ0, initEnv]
      rw [List.getElem?_replicate_of_lt (by simp [consExt]; exact rowMajor_lt hu hz)]
      congr 1
      symm
      simp [ind, resolvedAt_zero, gA]
    · rw [ha4 "buf" (by decide)]; simp [hσ3, hσ2a "buf" (by decide), hσ0, initEnv, consExt, hcap]
    · rw [hv4 "p" (by decide)]; simp [hσ3, hr2.frame_var "p" (by decide), hσ1, hσ0, initEnv,
        codesBefore]
    · simp [codesBefore] at h
    · rw [hl4]; simp [hσ3, hσ2a "nxt" (by decide), hσ0, initEnv, consExt]
    · rw [hl4]; simp [hσ3, hσ2a "rel" (by decide), hσ0, initEnv, consExt]
    · rw [hl4]; simp [hσ3, hσ2a "bad" (by decide), hσ0, initEnv, consExt]
    · rw [hl4]; simp [hσ3, hσ2a "unr" (by decide), hσ0, initEnv, consExt]
    · rw [hl4]; simp [hσ3, hσ2a "pos" (by decide), hσ0, initEnv, consExt]
  have hout4 : σ4.out = [] := by
    rw [ho4]; simp only [hσ3, out_setVar]; rw [hr2.out_eq (by decide)]; simp [hσ1, hσ0, initEnv]
  -- the stages
  obtain ⟨σ5, hr5, hb5, -⟩ :=
    forUp_run (B := B) (i := "j") (e := .var "m") (body := stageM) (N := m)
      (K := 1000 * (n + 1) * (n + 1)) (fun k ρ => ConsBase G ms cap k ρ) (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.hm]; omega), hI.hm])
      (σ := σ4) (hb4.setVar "j" (by decide) 0)
      (by
        rintro k hk ρ hρ hjk
        obtain ⟨ρ', hr', hb', hj'⟩ := stageM_run G ms hρ hk hjk (by simp [hcap, consCap, hm]) hcapB
        exact ⟨ρ', hr', hj', hb'.setVar "j" (by decide) _⟩)
  have hout5 : σ5.out = [] := by rw [hr5.out_eq (by decide), hout4]
  -- the output
  set codes := codesBefore G ms m with hcodes
  have hlc := length_codesBefore G ms m
  have hcc : codes.length ≤ cap := by simp only [hcap, consCap]; exact hlc
  set σ6 : Env := { σ5 with out := σ5.out ++ [n] } with hσ6
  have hw6 : Run B (.write (.var "n")) σ5 σ6 2 :=
    (Run.write (by rw [evalB_var (by rw [hb5.hn]; omega), hb5.hn])).mono (by simp)
  obtain ⟨σ7, hr7, ⟨hn7, hp7, ho7⟩, -⟩ :=
    forUp_run (B := B) (i := "v") (e := .var "n") (body := .write (.var "v")) (N := n) (K := 2)
      (fun k ρ => ρ.vars "n" = n ∧ ρ.vars "p" = codes.length ∧ ρ.out = [n] ++ List.range k)
      (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1]; omega), hI.1])
      (σ := σ6) ⟨by simp [hσ6, hb5.hn], by simp [hσ6, hb5.hbuf.hp, hcodes], by simp [hσ6, hout5]⟩
      (by
        rintro k hk ρ ⟨hn, hp, ho⟩ hvk
        refine ⟨_, (Run.write (by rw [evalB_var (by omega), hvk])).mono (by simp), by simp [hvk],
          by simp [hn], by simp [hp], by simp [ho, List.range_succ]⟩)
  set σ8 : Env := { σ7 with out := σ7.out ++ [codes.length / 3] } with hσ8
  have hw8 : Run B (.write (.div (.var "p") (.lit 3))) σ7 σ8 4 := by
    refine (Run.write ?_).mono (by simp)
    rw [evalB_bin (evalB_var (by rw [hp7]; omega)) (evalB_lit (by omega)) (by
      simp only [Bop.apply_div, hp7]; omega)]
    simp [hp7]
  have hbuf8 : BufAt cap codes σ8 := (hb5.hbuf.of_eq (by
    rw [hr7.frame_var "p" (by decide)]) (by
    rw [hr7.frame_arr "buf" (by decide)])).of_eq (by simp [hσ8]) (by simp [hσ8])
  obtain ⟨σ9, hr9, ho9⟩ := writeBuf_run (B := B) hbuf8 (by omega) (fun v hv => by
    have := codes_lt G ms m v hv; omega)
  refine ⟨σ9, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5
    (Run.seq hw6 (Run.seq hr7 (Run.seq hw8 hr9)))))))).mono ?_, ?_⟩
  · simp only [size_var, length_nbhds, hcap, consCap]
    have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    ring_nf
    nlinarith [Nat.zero_le (m * n), Nat.zero_le (m * n * n), Nat.zero_le (n * n)]
  · rw [ho9, hσ8, ho7, toWord_script]
    simp [hcodes, hm]

end Lax185574Proofs.Conversions.Ram
