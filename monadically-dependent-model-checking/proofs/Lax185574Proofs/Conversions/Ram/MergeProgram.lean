import Lax185574Proofs.Conversions.Ram.MergeStage
import Lax185574Proofs.Words.FinsetRead
import Lax185574Proofs.Words.ComputesLe

/-!
The program of lem:better-mw: read the graph and the chain, then write
the stages of the merge sequence `mergeSeq` one after the other.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.Partitions Lax185574.PairRelation
open Lax185574Proofs.Conversions.BetterMerge

/-- The whole program. -/
def mergeProg : Com :=
  .seq (.read "n") (.seq (readRows "adj" "n") (.seq (.read "m") (.seq (readRows "inS" "m")
    (.seq (.write (.var "m")) (forUp "s" (.var "m") stageC)))))

/-- The scalars and arrays of `mergeProg`. -/
def mergeLayout : Lax808846Proofs.Compile.Layout :=
  ⟨["n", "m", "s", "t", "u", "v", "ok", "z", "w", "d", "a", "b", "j", "k", "r", "x1", "x"],
    ["adj", "inS", "lab", "qlab", "E", "Lm", "Dp", "Dm", "Rm", "R1", "R3", "R5"], 8⟩

theorem mergeProg_ok : Lax808846Proofs.Compile.Com.Ok mergeLayout mergeProg := by
  simp [mergeProg, readRows, readRow, readElem, forUp, stageC, classify, classifyStep, eqA, zstepA,
    eqQ, zstepQ, rm, matFill, rowFill, eExpr, adjE, eqE, bfs, bfsU, fillR1, lstepC, rstepC, resetLm,
    lbody, rbody, lmIdx, copyD, writeParts, writePart, countRow, emitRow, partTest, rExpr,
    writeGraph, rmTest, mergeLayout, Lax808846Proofs.Compile.Com.Ok,
    Lax808846Proofs.Compile.Cond.Ok, Lax808846Proofs.Compile.condExpr,
    Lax808846Proofs.Compile.Expr.Ok]

/-- The array lengths of `mergeProg`. -/
def mergeExt (n m : ℕ) : String → ℕ := fun a =>
  if a = "adj" ∨ a = "E" ∨ a = "Lm" ∨ a = "Dp" ∨ a = "Dm" ∨ a = "Rm" then n * n
  else if a = "inS" then m * n
  else if a = "lab" ∨ a = "qlab" ∨ a = "R1" ∨ a = "R3" ∨ a = "R5" then n else 0

variable {n : ℕ}

/-- The neighborhoods of a graph, as the list its word is made of. -/
noncomputable def nbhds (G : SimpleGraph (Fin n)) : List (Finset (Fin n)) :=
  open Classical in List.ofFn fun v : Fin n => Finset.univ.filter (G.Adj v)

theorem toWord_graph_nbhds (G : SimpleGraph (Fin n)) :
    toWord G = n :: ((nbhds G).map toWord).flatten := by
  classical
  change toWord (List.ofFn fun v : Fin n => Finset.univ.filter (G.Adj v)) = _
  change (List.ofFn _).length :: ((List.ofFn _).map toWord).flatten = _
  simp only [List.length_ofFn, nbhds]

theorem length_nbhds (G : SimpleGraph (Fin n)) : (nbhds G).length = n := by simp [nbhds]

theorem mem_nbhds {G : SimpleGraph (Fin n)} {t u : ℕ} (ht : t < (nbhds G).length) :
    u ∈ sortedVals (nbhds G)[t] ↔ gA G t u := by
  classical
  have htn : t < n := by rw [length_nbhds] at ht; exact ht
  rw [mem_sortedVals]
  simp only [nbhds, List.getElem_ofFn, gA]
  constructor
  · rintro ⟨h, hm⟩; exact ⟨htn, h, by simpa using hm⟩
  · rintro ⟨h1, h2, ha⟩; exact ⟨h2, by simpa using ha⟩

theorem toWord_list_finset (S : List (Finset (Fin n))) :
    toWord S = S.length :: (S.map toWord).flatten := rfl

/-- The output, stage by stage. -/
theorem toWord_mergeSeq (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) :
    toWord (mergeSeq n G S) = S.length :: (List.range S.length).flatMap fun s =>
      toWord (Q G S (S.length - 1 - s)) ++ toWord (R G S (S.length - 1 - s)) := by
  have h : (mergeSeq n G S).map toWord = (List.range S.length).map fun s =>
      toWord (Q G S (S.length - 1 - s)) ++ toWord (R G S (S.length - 1 - s)) := by
    refine List.ext_getElem (by simp [mergeSeq]) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, mergeSeq, List.getElem_reverse]
    have hi : i < S.length := by simpa [mergeSeq] using h1
    have : S.getD (S.length - 1 - i) ∅ = S[S.length - 1 - i] := by
      rw [List.getD_eq_getElem]
    simp only [Q, R, P, this, stage]
    rfl
  change (mergeSeq n G S).length :: ((mergeSeq n G S).map toWord).flatten = _
  rw [h, length_mergeSeq, List.flatMap]

theorem length_le_flatten (S : List (Finset (Fin n))) :
    S.length ≤ ((S.map toWord).flatten).length := by
  induction S with
  | nil => simp
  | cons A S ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have : 1 ≤ (toWord A).length := by rw [toWord_finset_fin]; simp
    omega

theorem ite_eq_ind {p q : Prop} [Decidable p] (h : p ↔ q) : (if p then 1 else 0) = ind q := by
  unfold ind; by_cases hp : p <;> simp [hp, h.mp, ← h]

/-- **The run of the program.** -/
theorem mergeProg_run (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) :
    ∃ σ', Run (valBound 4 2 (toWord (G, S))) mergeProg
      (initEnv (mergeExt n S.length) (toWord (G, S))) σ'
      (3000 * (S.length + 1) * (n + 1) ^ 3) ∧ σ'.out = toWord (mergeSeq n G S) := by
  classical
  set m := S.length with hm
  set x := toWord (G, S) with hx
  have hx' : x = toWord G ++ toWord S := rfl
  set B := valBound 4 2 x with hB
  have hxG : toWord G = n :: ((nbhds G).map toWord).flatten := toWord_graph_nbhds G
  have hxS : toWord S = m :: (S.map toWord).flatten := toWord_list_finset S
  have hnM : n ≤ maxEntry x := le_maxEntry (by rw [hx', hxG]; simp)
  have hmx : m + 2 ≤ x.length := by
    rw [hx', List.length_append, hxG, hxS]
    have := length_le_flatten S
    simp only [List.length_cons]
    omega
  have hBX : (m + n + 2) * (m + n + 2) * 4 ≤ B := by
    simp only [hB, valBound]
    have : m + n + 2 ≤ x.length + maxEntry x + 1 := by omega
    nlinarith
  have hB1 : m * n + n * n + 2 * n + 3 < B := by nlinarith
  have hB2 : m + 1 < B := by nlinarith
  -- reading the graph
  set σ0 := initEnv (mergeExt n m) x with hσ0
  set σ1 : Env := { σ0.setVar "n" n with inp := ((nbhds G).map toWord).flatten ++ toWord S }
    with hσ1
  have hr1 : Run B (.read "n") σ0 σ1 1 := Run.read (by simp [hσ0, initEnv, hx', hxG])
  obtain ⟨σ2, hr2, hinp2, hlen2, hadj2⟩ := readRows_run (B := B) (arr := "adj") (cnt := "n")
    (L := nbhds G) (σ := σ1) (rest := toWord S) (by decide) (by decide) (by simp [hσ1])
    (by simp [hσ1, length_nbhds]) (by simp [hσ1])
    (by simp [hσ1, hσ0, initEnv, mergeExt, length_nbhds]) (by rw [length_nbhds]; nlinarith)
    (by rw [length_nbhds]; omega)
  -- reading the chain
  set σ3 : Env := { σ2.setVar "m" m with inp := (S.map toWord).flatten } with hσ3
  have hr3 : Run B (.read "m") σ2 σ3 1 := Run.read (by rw [hinp2, hxS])
  have hn2 : σ2.vars "n" = n := by rw [hr2.frame_var "n" (by decide)]; simp [hσ1]
  obtain ⟨σ4, hr4, hinp4, hlen4, hinS4⟩ := readRows_run (B := B) (arr := "inS") (cnt := "m")
    (L := S) (σ := σ3) (rest := []) (by decide) (by decide) (by simp [hσ3])
    (by simp [hσ3, hm]) (by simp [hσ3, hn2])
    (by
      simp only [hσ3, arrs_setVar]
      rw [hr2.frame_arr "inS" (by decide)]
      simp [hσ1, hσ0, initEnv, mergeExt, hm])
    (by nlinarith) (by omega)
  -- the count of the stages
  set σ5 : Env := { σ4 with out := σ4.out ++ [m] } with hσ5
  have hm4 : σ4.vars "m" = m := by rw [hr4.frame_var "m" (by decide)]; simp [hσ3]
  have hn4 : σ4.vars "n" = n := by rw [hr4.frame_var "n" (by decide)]; simp [hσ3, hn2]
  have hr5 : Run B (.write (.var "m")) σ4 σ5 2 :=
    (Run.write (by rw [evalB_var (by rw [hm4]; omega), hm4])).mono (by simp)
  have hout4 : σ4.out = [] := by
    rw [hr4.out_eq (by decide)]
    simp only [hσ3, out_setVar]
    rw [hr2.out_eq (by decide)]
    simp [hσ1, hσ0, initEnv]
  -- the arrays not read into
  have harr : ∀ a, a ≠ "adj" → a ≠ "inS" → σ5.arrs a = σ0.arrs a := by
    intro a h1 h2
    simp only [hσ5]
    rw [hr4.frame_arr a (by simp [readRows, readRow, readElem, forUp, Com.warrs]; exact h2)]
    simp only [hσ3, arrs_setVar]
    rw [hr2.frame_arr a (by simp [readRows, readRow, readElem, forUp, Com.warrs]; exact h1)]
    simp [hσ1]
  have hlen0 : ∀ a, (σ0.arrs a).length = mergeExt n m a := by simp [hσ0, initEnv]
  have hb5 : Base n m G S σ5 := by
    refine ⟨by simp [hσ5, hn4], by simp [hσ5, hm4], ⟨?_, fun u hu z hz => ?_⟩,
      fun t ht z hz => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hσ5]
      rw [hr4.frame_arr "adj" (by decide)]
      simp only [hσ3, arrs_setVar]
      rw [hlen2, length_nbhds]
    · simp only [hσ5]
      rw [hr4.frame_arr "adj" (by decide)]
      simp only [hσ3, arrs_setVar]
      rw [hadj2 u (by rw [length_nbhds]; exact hu) z hz]
      exact congrArg some (ite_eq_ind (mem_nbhds (by rw [length_nbhds]; exact hu)))
    · simp only [hσ5]
      rw [hinS4 t ht z hz, List.getD_eq_getElem _ _ ht]
      exact congrArg some (ite_eq_ind Iff.rfl)
    all_goals (rw [harr _ (by decide) (by decide), hlen0]; simp [mergeExt])
  -- the stages
  let I : ℕ → Env → Prop := fun k ρ => Base n m G S ρ ∧
    ρ.out = m :: (List.range k).flatMap fun s =>
      toWord (Q G S (m - 1 - s)) ++ toWord (R G S (m - 1 - s))
  obtain ⟨σ6, hr6, ⟨-, ho6⟩, -⟩ :=
    forUp_run (B := B) (i := "s") (e := .var "m") (body := stageC) (N := m)
      (K := 2000 * (n + 1) ^ 3) I (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hm]; omega), hI.1.hm])
      (σ := σ5) ⟨hb5.setVar "s" (by decide) (by decide) 0, by simp [hσ5, hout4]⟩
      (by
        rintro k hk ρ ⟨hbρ, hoρ⟩ hsk
        obtain ⟨ρ', hr', hb', hs', ho'⟩ := stage_run hbρ hsk hk hB1 (by omega)
        refine ⟨ρ', hr', hs', ⟨hb'.setVar "s" (by decide) (by decide) _, ?_⟩⟩
        simp only [out_setVar, ho', hoρ, List.range_succ, List.flatMap_append]
        simp)
  refine ⟨σ6, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5 hr6))))).mono ?_,
    by rw [ho6, toWord_mergeSeq]⟩
  simp only [size_var, length_nbhds]
  ring_nf
  nlinarith [Nat.zero_le n, Nat.zero_le (n * n), Nat.zero_le (n * n * n), Nat.zero_le m,
    Nat.zero_le (m * n), Nat.zero_le (m * n * n), Nat.zero_le (m * n * n * n)]

end Lax185574Proofs.Conversions.Ram
