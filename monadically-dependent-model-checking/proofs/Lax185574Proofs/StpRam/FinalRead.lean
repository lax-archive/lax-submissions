import Lax185574Proofs.StpRam.ReadCsr
import Lax185574Proofs.StpRam.FinalCompute
import Lax185574Proofs.Lib.DistMatrix

/-!
The reading part of the final round of lem:compute-stp.

The input of the final round, after the tag `2` and the length `ℓ` of
the state, is the word of the partial graph, `k, q` and the word of the
distance matrix, then the state: `0, n, k, q, j, gl`, the word of the
list `F` of the family trees and the word of the list `A` of the shifted
trees. `finalRead` skips the colors, reads the edges and the non-edges
into compressed-row form, reads `k` and `q`, reads the distance matrix
into the array `dd` (`readDm`), skips the state header and the word of
`F`, and reads `A` with `readWords`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.PartialGraphs

/-! ### The resolved neighbors -/

/-- The resolved neighbors of `w`, edges first. -/
noncomputable def adjOf {n : ℕ} (G : PartialGraph (Fin n)) (w : Fin n) : List (Fin n) :=
  (nbrL G.edge w ++ nbrL G.nonEdge w).filterMap fun z => if h : z < n then some ⟨z, h⟩ else none

theorem mem_adjOf {n : ℕ} (G : PartialGraph (Fin n)) (w v : Fin n) :
    v ∈ adjOf G w ↔ InRow (offL G.edge) (tgtL G.edge) w v ∨ InRow (offL G.nonEdge) (tgtL G.nonEdge) w v := by
  rw [inRow_iff _ w.isLt, inRow_iff _ w.isLt]
  simp only [adjOf, List.mem_filterMap, List.mem_append]
  constructor
  · rintro ⟨z, hz, hzv⟩
    split_ifs at hzv with h
    · simp only [Option.some.injEq] at hzv; subst hzv; exact hz
  · intro h
    exact ⟨v.val, h, by simp⟩

theorem mem_adjOf_resolved {n : ℕ} (G : PartialGraph (Fin n)) (w v : Fin n) :
    v ∈ adjOf G w ↔ G.resolved.Adj w v := by
  rw [mem_adjOf, inRow_iff _ w.isLt, inRow_iff _ w.isLt, mem_nbrL w.isLt, mem_nbrL w.isLt]
  simp only [PartialGraph.resolved, SimpleGraph.sup_adj, v.isLt, exists_true_left]

theorem adj2_lt {n : ℕ} (G : PartialGraph (Fin n)) (w v : ℕ) (hw : w < n)
    (h : Adj2 (offL G.edge) (tgtL G.edge) (offL G.nonEdge) (tgtL G.nonEdge) w v) : v < n := by
  rcases h with h | h
  · rw [inRow_iff _ hw] at h; exact lt_of_mem_nbrL h
  · rw [inRow_iff _ hw] at h; exact lt_of_mem_nbrL h

theorem flatten_map_toWord_nat : ∀ l : List ℕ, (l.map toWord).flatten = l
  | [] => rfl
  | c :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_map_toWord_nat l]; rfl

theorem toWord_colors {n : ℕ} (c : Fin n → ℕ) : toWord c = n :: List.ofFn c := by
  change (List.ofFn c).length :: ((List.ofFn c).map toWord).flatten = _
  rw [List.length_ofFn, flatten_map_toWord_nat]

theorem toWord_pg {n : ℕ} (G : PartialGraph (Fin n)) :
    toWord G = (n :: List.ofFn G.color) ++ toWord G.edge ++ toWord G.nonEdge := by
  change toWord G.color ++ (toWord G.edge ++ toWord G.nonEdge) = _
  rw [toWord_colors]; simp

/-! ### Skipping -/

/-- Skip as many entries as the scalar `c` says. -/
def skipLoop (c : String) : Com := forUp "ci2" (.var c) (.read "cx")

theorem skipLoop_run {B : ℕ} {c : String} (hc : c ≠ "ci2") (hc' : c ≠ "cx") {σ : Env} {l rest : List ℕ}
    (hinp : σ.inp = l ++ rest) (hcv : σ.vars c = l.length) (hlB : l.length < B) :
    ∃ σ', Run B (skipLoop c) σ σ' (9 * l.length + 6) ∧ σ'.inp = rest ∧
      (∀ x, x ≠ "ci2" → x ≠ "cx" → σ'.vars x = σ.vars x) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out := by
  obtain ⟨σ', hr, ⟨hin', hv', ha', ho'⟩, -⟩ := forUp_run (B := B) (i := "ci2") (e := .var c)
    (body := .read "cx") (N := l.length) (K := 1)
    (fun j τ => τ.inp = l.drop j ++ rest ∧ (∀ x, x ≠ "ci2" → x ≠ "cx" → τ.vars x = σ.vars x) ∧
      τ.arrs = σ.arrs ∧ τ.out = σ.out) (σ := σ) hlB
    (fun j _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨by rw [hI.2.1 c hc hc', hcv], by rw [hI.2.1 c hc hc', hcv]; exact hlB⟩)
    ⟨by simp [hinp], fun x h1 _ => by simp [h1], by simp, by simp⟩
    (by
      rintro j hj τ ⟨hin, hv, ha, ho⟩ hci
      have hd : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
      refine ⟨{ τ.setVar "cx" l[j] with inp := l.drop (j + 1) ++ rest }, Run.read (by rw [hin, hd]; rfl),
        by simp [hci], by simp, fun x h1 h2 => by simp [h1, h2, hv x h1 h2], by simp [ha], by simp [ho]⟩)
  exact ⟨σ', hr.mono (by simp; omega), by simpa using hin', hv', ha', ho'⟩

/-- Skip the frames of a list of words. -/
def skipFrames : Com := forUp "fi" (.var "fc") (.seq (.read "fl") (skipLoop "fl"))

theorem skipFrames_run {B L : ℕ} {σ : Env} {F : List (List ℕ)} {rest : List ℕ}
    (hinp : σ.inp = frames F ++ rest) (hfc : σ.vars "fc" = F.length) (hFB : F.length < B)
    (hL : ∀ u ∈ F, u.length ≤ L) (hLB : L < B) :
    ∃ σ', Run B skipFrames σ σ' (F.length * (9 * L + 18) + 6) ∧ σ'.inp = rest ∧
      (∀ x, x ∉ ["fi", "fl", "ci2", "cx"] → σ'.vars x = σ.vars x) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out := by
  obtain ⟨σ', hr, ⟨hin', hv', ha', ho'⟩, -⟩ := forUp_run (B := B) (i := "fi") (e := .var "fc")
    (body := .seq (.read "fl") (skipLoop "fl")) (N := F.length) (K := 9 * L + 10)
    (fun j τ => τ.inp = frames (F.drop j) ++ rest ∧
      (∀ x, x ∉ ["fi", "fl", "ci2", "cx"] → τ.vars x = σ.vars x) ∧ τ.arrs = σ.arrs ∧ τ.out = σ.out)
    (σ := σ) hFB
    (fun j _ τ hI _ => by
      simp only [evalB_var_iff]
      exact ⟨by rw [hI.2.1 "fc" (by decide), hfc], by rw [hI.2.1 "fc" (by decide), hfc]; exact hFB⟩)
    ⟨by simp [hinp], fun x hx => by simp at hx; simp [hx.1], by simp, by simp⟩
    (by
      rintro j hj τ ⟨hin, hv, ha, ho⟩ hfi
      have hd : F.drop j = F[j] :: F.drop (j + 1) := List.drop_eq_getElem_cons hj
      have hlj : F[j].length ≤ L := hL _ (List.getElem_mem hj)
      set τ1 : Env := { τ.setVar "fl" F[j].length with inp := F[j] ++ (frames (F.drop (j + 1)) ++ rest) }
        with hτ1
      have r1 : Run B (.read "fl") τ τ1 1 := Run.read (by
        simp only [hin, hd, frames, List.map_cons, List.flatten_cons, List.cons_append, List.append_assoc])
      obtain ⟨τ2, r2, hin2, hv2, ha2, ho2⟩ := skipLoop_run (B := B) (c := "fl") (by decide) (by decide)
        (σ := τ1) (l := F[j]) (rest := frames (F.drop (j + 1)) ++ rest) rfl (by simp [hτ1]) (by omega)
      refine ⟨τ2, (Run.seq r1 r2).mono (by omega), ?_, by simpa using hin2, fun x hx => ?_,
        by simp [ha2, hτ1, ha], by simp [ho2, hτ1, ho]⟩
      · rw [hv2 "fi" (by decide) (by decide)]; simp [hτ1, hfi]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [vars_setVar, if_neg hx.1]
        rw [hv2 x hx.2.2.1 hx.2.2.2]
        simp [hτ1, hx.2.1, hv x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2])])
  refine ⟨σ', hr.mono ?_, by simpa [frames] using hin', fun x hx => ?_, ha', ho'⟩
  · simp only [Expr.size]; nlinarith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [hv' x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2])]

/-! ### Reading the input of the final round -/

/-- Read the window: skip the colors, read the edges and the non-edges,
and read `k` and `q`. -/
def readWin : Com :=
  .seq (.read "cn") (.seq (skipLoop "cn") (.seq (readCsr "eo" "et") (.seq (readCsr "no" "nt")
    (.seq (.read "kk") (.read "qq")))))

/-- The cost bound of `readWin`. -/
def winCost (n : ℕ) : ℕ := 2 * (n * (17 * n + 18) + 12) + 9 * n + 9

set_option maxHeartbeats 1000000 in
/-- **Reading the window.** -/
theorem readWin_run {B n k q : ℕ} (G : PartialGraph (Fin n)) {rest : List ℕ} {σ : Env}
    (hinp : σ.inp = (toWord G ++ [k, q]) ++ rest)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = offL G.nonEdge n)
    (hnB : n + 1 < B) (hEB : offL G.edge n + 1 < B) (hNB : offL G.nonEdge n + 1 < B) :
    ∃ σ', Run B readWin σ σ' (winCost n) ∧
      Csr "eo" "et" n (offL G.edge n) n (offL G.edge) (tgtL G.edge) σ' ∧
      Csr "no" "nt" n (offL G.nonEdge n) n (offL G.nonEdge) (tgtL G.nonEdge) σ' ∧
      σ'.vars "cn" = n ∧ σ'.vars "kk" = k ∧ σ'.vars "qq" = q ∧ σ'.inp = rest ∧ σ'.out = σ.out ∧
      (∀ x, x ∉ ["eo", "et", "no", "nt"] → σ'.arrs x = σ.arrs x) ∧
      (∀ x, x ∉ readWin.wvars → σ'.vars x = σ.vars x) := by
  rw [toWord_pg] at hinp
  -- the colors
  set σ3 : Env := { σ.setVar "cn" n with inp := List.ofFn G.color ++ (toWord G.edge ++
    (toWord G.nonEdge ++ ([k, q] ++ rest))) } with hσ3
  have r3 : Run B (.read "cn") σ σ3 1 := Run.read (by rw [hinp]; simp)
  obtain ⟨σ4, r4, hin4, hv4, ha4, ho4⟩ := skipLoop_run (B := B) (c := "cn") (by decide) (by decide)
    (σ := σ3) (l := List.ofFn G.color) rfl (by simp [hσ3]) (by simp; omega)
  -- the edges and the non-edges
  obtain ⟨σ5, r5, hc5, hin5, -⟩ := readCsr_run (B := B) G.edge (o := "eo") (t := "et") (by decide)
    (σ := σ4) hin4 (by rw [ha4]; simp [hσ3, heo]) (by rw [ha4]; simp [hσ3, het])
    hnB hEB
  have hf5 : ∀ x, x ∉ (readCsr "eo" "et").warrs → σ5.arrs x = σ4.arrs x := fun x h => r5.frame_arr x h
  obtain ⟨σ6, r6, hc6, hin6, hcn6⟩ := readCsr_run (B := B) G.nonEdge (o := "no") (t := "nt") (by decide)
    (σ := σ5) hin5 (by rw [hf5 _ (by decide), ha4]; simp [hσ3, hno])
    (by rw [hf5 _ (by decide), ha4]; simp [hσ3, hnt]) hnB hNB
  have hf6 : ∀ x, x ∉ (readCsr "no" "nt").warrs → σ6.arrs x = σ5.arrs x := fun x h => r6.frame_arr x h
  -- the rank
  set σ7 : Env := { σ6.setVar "kk" k with inp := q :: rest } with hσ7
  have r7 : Run B (.read "kk") σ6 σ7 1 := Run.read (by rw [hin6]; simp)
  set σ8 : Env := { σ7.setVar "qq" q with inp := rest } with hσ8
  have r8 : Run B (.read "qq") σ7 σ8 1 := Run.read rfl
  have hrun : Run B readWin σ σ8 (winCost n) := by
    unfold readWin
    refine (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))).mono ?_
    simp only [winCost, List.length_ofFn]
    omega
  refine ⟨σ8, hrun, ?_, ?_, ?_, by simp [hσ8, hσ7], by simp [hσ8], rfl, hrun.out_eq (by decide),
    fun x hx => hrun.frame_arr x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp [readWin, readCsr, vtxRd, slotRd, skipLoop, forUp, Com.warrs]; tauto),
    fun x hx => hrun.frame_var x hx⟩
  · refine hc5.of_eq ?_ ?_
    · simp only [hσ8, hσ7, arrs_setVar]; rw [hf6 _ (by decide)]
    · simp only [hσ8, hσ7, arrs_setVar]; rw [hf6 _ (by decide)]
  · refine hc6.of_eq ?_ ?_
    · simp [hσ8, hσ7]
    · simp [hσ8, hσ7]
  · simp only [hσ8, hσ7, vars_setVar]; simp [hcn6]

/-! ### Reading the distance matrix -/

theorem dm_pos {n i : ℕ} (h : i < n * n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp at h
  · exact h0

/-- The entries of an `n × n` matrix, as an array of length `n · n` with
the entry `(u, v)` at `u · n + v`. -/
def dmArr (n : ℕ) (f : Fin n → Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n * n then
    f ⟨i / n, Nat.div_lt_of_lt_mul h⟩ ⟨i % n, Nat.mod_lt _ (dm_pos h)⟩
  else 0

theorem dm_idx_lt {n : ℕ} (u v : Fin n) : u.val * n + v.val < n * n := by
  have : u.val * n + n ≤ n * n := by
    have := Nat.mul_le_mul_right n (show u.val + 1 ≤ n by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  omega

theorem dmArr_apply {n : ℕ} (f : Fin n → Fin n → ℕ) (u v : Fin n) :
    dmArr n f (u.val * n + v.val) = f u v := by
  have hn : 0 < n := Fin.pos u
  unfold dmArr
  rw [dif_pos (dm_idx_lt u v)]
  have h1 : (u.val * n + v.val) / n = u.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt v.isLt, Nat.zero_add]
  have h2 : (u.val * n + v.val) % n = v.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt v.isLt]
  congr 1
  · exact Fin.ext h1
  · exact Fin.ext h2

theorem dm_eq_arrOf_getD (l : List ℕ) : l = arrOf l.length (fun i => l.getD i 0) := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < l.length
  · rw [getElem?_arrOf _ hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- Read an entry of the matrix into `dd`. -/
def rdEnt : Com :=
  .seq (.read "cx") (.store "dd" (.add (.mul (.var "du") (.var "cn")) (.var "dv")) (.var "cx"))

/-- Read a row of the matrix: its length, then its entries. -/
def rdRow : Com := .seq (.read "cx") (forUp "dv" (.var "cn") rdEnt)

/-- Read the word of an `n × n` matrix into the array `dd`, with `n` in
`cn`. -/
def readDm : Com := .seq (.read "cx") (forUp "du" (.var "cn") rdRow)

/-- The cost bound of `readDm`. -/
def dmCost (n : ℕ) : ℕ := 16 * (n * n) + 16 * n + 8

/-- The rows of the word of a matrix. -/
def dmRows (n : ℕ) (f : Fin n → Fin n → ℕ) : List (List ℕ) :=
  List.ofFn fun u : Fin n => n :: List.ofFn (f u)

set_option maxHeartbeats 2000000 in
/-- **Reading the matrix.** -/
theorem readDm_run {B n : ℕ} (f : Fin n → Fin n → ℕ) {rest : List ℕ} {σ : Env}
    (hinp : σ.inp = Lax185574Proofs.DistMatrix.matWord n f ++ rest) (hcn : σ.vars "cn" = n)
    (hdd : (σ.arrs "dd").length = n * n) (hnnB : n * n < B) (hfB : ∀ u v, f u v < B) :
    ∃ σ', Run B readDm σ σ' (dmCost n) ∧ σ'.inp = rest ∧ σ'.arrs "dd" = arrOf (n * n) (dmArr n f) ∧
      (∀ x, x ∉ ["cx", "du", "dv"] → σ'.vars x = σ.vars x) ∧
      (∀ x, x ≠ "dd" → σ'.arrs x = σ.arrs x) ∧ σ'.out = σ.out := by
  have hnB : n < B := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · omega
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left n h0) hnnB
  set d0 := σ.arrs "dd" with hd0
  set rows := dmRows n f with hrows
  have hlr : rows.length = n := by simp [hrows, dmRows]
  have hmw : Lax185574Proofs.DistMatrix.matWord n f = n :: rows.flatten := rfl
  set σ0 : Env := { σ.setVar "cx" n with inp := rows.flatten ++ rest } with hσ0
  have r0 : Run B (.read "cx") σ σ0 1 := Run.read (by rw [hinp, hmw]; rfl)
  let F : ℕ → ℕ → ℕ := fun m i => if i < m then dmArr n f i else d0.getD i 0
  have hF0 : arrOf (n * n) (F 0) = d0 := by
    rw [dm_eq_arrOf_getD d0, hdd]
    exact arrOf_congr fun i _ => by simp [F]
  let I : ℕ → Env → Prop := fun u τ => τ.inp = (rows.drop u).flatten ++ rest ∧ τ.vars "cn" = n ∧
    τ.arrs "dd" = arrOf (n * n) (F (u * n)) ∧ (∀ x, x ∉ ["cx", "du", "dv"] → τ.vars x = σ.vars x) ∧
    (∀ x, x ≠ "dd" → τ.arrs x = σ.arrs x) ∧ τ.out = σ.out
  obtain ⟨σ', hr', ⟨hin', -, hdd', hv', ha', ho'⟩, -⟩ := forUp_run (B := B) (i := "du") (e := .var "cn")
    (body := rdRow) (N := n) (K := 16 * n + 7) I (σ := σ0) hnB
    (fun u _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by rw [hI.2.1]; omega⟩)
    ⟨by simp [hσ0], by simp [hσ0, hcn], by simp [hσ0, hF0, hd0],
      fun x hx => by simp at hx; simp [hσ0, hx.1, hx.2.1],
      fun x _ => by simp [hσ0], by simp [hσ0]⟩
    (by
      rintro u hu τ ⟨hinτ, hcnτ, hddτ, hvτ, haτ, hoτ⟩ hdu
      have hdr : rows.drop u = (n :: List.ofFn (f ⟨u, hu⟩)) :: rows.drop (u + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
        simp [hrows, dmRows]
      set row := List.ofFn (f ⟨u, hu⟩) with hrow
      set τ1 : Env := { τ.setVar "cx" n with inp := row ++ ((rows.drop (u + 1)).flatten ++ rest) }
        with hτ1
      have r1 : Run B (.read "cx") τ τ1 1 := Run.read (by rw [hinτ, hdr]; simp)
      let J : ℕ → Env → Prop := fun v ρ => ρ.inp = row.drop v ++ ((rows.drop (u + 1)).flatten ++ rest) ∧
        ρ.vars "cn" = n ∧ ρ.vars "du" = u ∧ ρ.arrs "dd" = arrOf (n * n) (F (u * n + v)) ∧
        (∀ x, x ∉ ["cx", "du", "dv"] → ρ.vars x = σ.vars x) ∧
        (∀ x, x ≠ "dd" → ρ.arrs x = σ.arrs x) ∧ ρ.out = σ.out
      obtain ⟨τ2, hr2, ⟨hin2, hcn2, hdu2, hdd2, hv2, ha2, ho2⟩, -⟩ := forUp_run (B := B) (i := "dv")
        (e := .var "cn") (body := rdEnt) (N := n) (K := 8) J (σ := τ1) hnB
        (fun v _ ρ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by rw [hI.2.1]; omega⟩)
        ⟨by simp [hτ1], by simp [hτ1, hcnτ], by simp [hτ1, hdu], by simp [hτ1, hddτ],
          fun x hx => by simp at hx; simp [hτ1, hx.1, hx.2.2, hvτ x (by simp [hx.1, hx.2.1, hx.2.2])],
          fun x hx => by simp [hτ1, haτ x hx], by simp [hτ1, hoτ]⟩
        (by
          rintro v hv ρ ⟨hinρ, hcnρ, hduρ, hddρ, hvρ, haρ, hoρ⟩ hdv
          have hrl : row.length = n := by simp [hrow]
          have hdrow : row.drop v = f ⟨u, hu⟩ ⟨v, hv⟩ :: row.drop (v + 1) := by
            rw [List.drop_eq_getElem_cons (by omega)]
            simp [hrow]
          set e := f ⟨u, hu⟩ ⟨v, hv⟩ with he
          set ρ1 : Env := { ρ.setVar "cx" e with inp := row.drop (v + 1) ++
            ((rows.drop (u + 1)).flatten ++ rest) } with hρ1
          have rr : Run B (.read "cx") ρ ρ1 1 := Run.read (by rw [hinρ, hdrow]; simp)
          have hidx : u * n + v < n * n := dm_idx_lt ⟨u, hu⟩ ⟨v, hv⟩
          have hix : (Expr.add (.mul (.var "du") (.var "cn")) (.var "dv")).evalB B ρ1 = some (u * n + v) := by
            simp only [evalB_bin_iff, evalB_var_iff]
            exact ⟨u * n, v, ⟨u, n, ⟨by simp [hρ1, hduρ], by simp [hρ1, hduρ]; omega⟩,
              ⟨by simp [hρ1, hcnρ], by simp [hρ1, hcnρ]; omega⟩, by simp, by
                have : u * n ≤ u * n + v := by omega
                omega⟩, ⟨by simp [hρ1, hdv], by simp [hρ1, hdv]; omega⟩, by simp, by omega⟩
          have rs : Run B (.store "dd" (.add (.mul (.var "du") (.var "cn")) (.var "dv")) (.var "cx"))
              ρ1 (ρ1.setArr "dd" (u * n + v) e) 7 :=
            (Run.store hix (by simp only [evalB_var_iff]; exact ⟨by simp [hρ1], by simp [hρ1, he, hfB]⟩)
              (by simp [hρ1, hddρ]; omega)).mono (by simp [Expr.size])
          refine ⟨ρ1.setArr "dd" (u * n + v) e, (Run.seq rr rs).mono (by omega), by simp [hρ1, hdv],
            by simp [hρ1], by simp [hρ1, hcnρ], by simp [hρ1, hduρ], ?_,
            ?_, fun x hx => by simp [hρ1, hx, haρ x hx], by simp [hρ1, hoρ]⟩
          swap
          · intro x hx
            rw [← hvρ x hx]
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
            simp [hρ1, hx.1, hx.2.2]
          simp only [arrs_setVar, arrs_setArr, if_true, hρ1, hddρ, set_arrOf]
          refine arrOf_congr fun i _ => ?_
          by_cases hi : i = u * n + v
          · subst hi
            simp only [if_true, F, show u * n + v < u * n + (v + 1) by omega, if_true]
            rw [he, ← dmArr_apply f ⟨u, hu⟩ ⟨v, hv⟩]
          · simp only [hi, if_false, F]
            have : (i < u * n + v) ↔ (i < u * n + (v + 1)) := by omega
            simp only [this])
      refine ⟨τ2, (Run.seq r1 hr2).mono (by simp [Expr.size]; omega), ?_⟩
      have hdv2 : τ2.vars "du" = u := hdu2
      refine ⟨hdv2, ?_, by simp [hcn2], by simp [hdd2, Nat.add_mul, Nat.one_mul], fun x hx => ?_,
        fun x hx => by simp [ha2 x hx], by simp [ho2]⟩
      · simp [hin2, List.drop_eq_nil_of_le (show row.length ≤ n by simp [hrow])]
      · simp at hx; simp [hx.2.1, hv2 x (by simp [hx.1, hx.2.1, hx.2.2])])
  refine ⟨σ', (Run.seq r0 hr').mono ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · simp only [dmCost, Expr.size]; nlinarith
  · rw [hin', List.drop_eq_nil_of_le (by omega)]; simp
  · rw [hdd']; exact arrOf_congr fun i hi => by simp [F, hi]
  · exact hv' x hx
  · exact ha' x hx
  · exact ho'

/-- Read the window: the graph, `k`, `q` and the distance matrix. -/
def readWinD : Com := .seq readWin readDm

set_option maxHeartbeats 1000000 in
/-- **Reading the window with the matrix.** -/
theorem readWinD_run {B n k q : ℕ} (G : PartialGraph (Fin n)) (f : Fin n → Fin n → ℕ)
    {rest : List ℕ} {σ : Env}
    (hinp : σ.inp = (toWord G ++ [k, q]) ++ Lax185574Proofs.DistMatrix.matWord n f ++ rest)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = offL G.nonEdge n)
    (hdd : (σ.arrs "dd").length = n * n)
    (hnB : n + 1 < B) (hEB : offL G.edge n + 1 < B) (hNB : offL G.nonEdge n + 1 < B)
    (hnnB : n * n < B) (hfB : ∀ u v, f u v < B) :
    ∃ σ', Run B readWinD σ σ' (winCost n + dmCost n) ∧
      Csr "eo" "et" n (offL G.edge n) n (offL G.edge) (tgtL G.edge) σ' ∧
      Csr "no" "nt" n (offL G.nonEdge n) n (offL G.nonEdge) (tgtL G.nonEdge) σ' ∧
      σ'.vars "cn" = n ∧ σ'.vars "kk" = k ∧ σ'.vars "qq" = q ∧ σ'.inp = rest ∧ σ'.out = σ.out ∧
      σ'.arrs "dd" = arrOf (n * n) (dmArr n f) ∧
      (∀ x, x ∉ ["eo", "et", "no", "nt", "dd"] → σ'.arrs x = σ.arrs x) ∧
      (∀ x, x ∉ readWinD.wvars → σ'.vars x = σ.vars x) := by
  obtain ⟨σ1, r1, hc1, hc2, hcn1, hk1, hq1, hin1, ho1, ha1, -⟩ := readWin_run (B := B) (k := k) (q := q)
    G (rest := Lax185574Proofs.DistMatrix.matWord n f ++ rest) (by rw [hinp]; simp) heo het hno hnt
    hnB hEB hNB
  obtain ⟨σ2, r2, hin2, hdd2, hv2, ha2, ho2⟩ := readDm_run (B := B) f (σ := σ1) hin1 hcn1
    (by rw [ha1 _ (by decide), hdd]) hnnB hfB
  have hrun : Run B readWinD σ σ2 (winCost n + dmCost n) := Run.seq r1 r2
  refine ⟨σ2, hrun, hc1.of_eq (ha2 _ (by decide)) (ha2 _ (by decide)),
    hc2.of_eq (ha2 _ (by decide)) (ha2 _ (by decide)), by rw [hv2 _ (by decide), hcn1],
    by rw [hv2 _ (by decide), hk1], by rw [hv2 _ (by decide), hq1], hin2, by rw [ho2, ho1], hdd2,
    fun x hx => ?_, fun x hx => hrun.frame_var x hx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  rw [ha2 x hx.2.2.2.2, ha1 x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1])]

/-- Read the input of the final round after the tag and the length of
the state. -/
def finalRead : Com :=
  .seq readWinD (.seq (.assign "hc" (.lit 6))
    (.seq (skipLoop "hc") (.seq (.read "fc") (.seq skipFrames (.seq readWords
      (.assign "n" (.var "cn")))))))

/-- The cost bound of `finalRead`. -/
def readCost (n L nF xl : ℕ) : ℕ :=
  2 * (n * (17 * n + 18) + 12) + 9 * n + 100 + nF * (9 * L + 18) + 21 * xl + 9 + dmCost n

set_option maxHeartbeats 1000000 in
/-- **Reading the final round's input.** -/
theorem finalRead_run {B n k q : ℕ} (G : PartialGraph (Fin n)) (f : Fin n → Fin n → ℕ)
    {hd rest : List ℕ}
    {Fs As : List (List ℕ)} (hhd : hd.length = 6) {L : ℕ} (hFL : ∀ u ∈ Fs, u.length ≤ L)
    {σ : Env}
    (hinp : σ.inp = (toWord G ++ [k, q]) ++ Lax185574Proofs.DistMatrix.matWord n f ++ hd ++
      toWord Fs ++ toWord As ++ rest)
    (hdd : (σ.arrs "dd").length = n * n) (hnnB : n * n < B) (hfB : ∀ u v, f u v < B)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = offL G.nonEdge n)
    (ha : total As ≤ (σ.arrs "a").length) (hst : As.length ≤ (σ.arrs "st").length)
    (hln : As.length ≤ (σ.arrs "ln").length)
    (hnB : n + 1 < B) (hEB : offL G.edge n + 1 < B) (hNB : offL G.nonEdge n + 1 < B)
    (hFB : Fs.length < B) (hLB : L < B) (hAB : (toWord As).length < B) (hAv : ∀ v ∈ toWord As, v < B)
    (h6 : 6 < B) :
    ∃ σ', Run B finalRead σ σ' (readCost n L Fs.length (toWord As).length) ∧
      GraphAt n (offL G.edge n) (offL G.nonEdge n) (offL G.edge) (tgtL G.edge) (offL G.nonEdge)
        (tgtL G.nonEdge) σ' ∧ WordsAt As σ' ∧ σ'.vars "kk" = k ∧ σ'.vars "qq" = q ∧
      σ'.vars "m" = As.length ∧ σ'.out = σ.out ∧ σ'.arrs "dd" = arrOf (n * n) (dmArr n f) ∧
      (∀ x, x ∉ ["eo", "et", "no", "nt", "a", "st", "ln", "dd"] → σ'.arrs x = σ.arrs x) := by
  obtain ⟨σ8, r8, hc5, hc6, hcn8, hk8, hq8, hin8, ho8, hdd8, ha8, -⟩ := readWinD_run (B := B) (k := k)
    (q := q) G f (rest := hd ++ (toWord Fs ++ (toWord As ++ rest))) (by rw [hinp]; simp) heo het hno
    hnt hdd hnB hEB hNB hnnB hfB
  -- the state header and the family
  set σ9 := σ8.setVar "hc" 6 with hσ9
  have r9 : Run B (.assign "hc" (.lit 6)) σ8 σ9 2 := (Run.assign (by simp; omega)).mono (by simp)
  obtain ⟨σ10, r10, hin10, hv10, ha10, ho10⟩ := skipLoop_run (B := B) (c := "hc") (by decide) (by decide)
    (σ := σ9) (l := hd) (rest := toWord Fs ++ (toWord As ++ rest)) (by simp [hσ9, hin8])
    (by simp [hσ9, hhd]) (by omega)
  rw [toWord_words Fs] at hin10
  set σ11 : Env := { σ10.setVar "fc" Fs.length with inp := frames Fs ++ (toWord As ++ rest) } with hσ11
  have r11 : Run B (.read "fc") σ10 σ11 1 := Run.read (by rw [hin10]; simp)
  obtain ⟨σ12, r12, hin12, hv12, ha12, ho12⟩ := skipFrames_run (B := B) (L := L) (σ := σ11) rfl
    (by simp [hσ11]) hFB hFL hLB
  -- the shifted trees
  have hw12a : σ12.arrs = σ8.arrs := by rw [ha12]; simp [hσ11, ha10, hσ9]
  have ha8' : ∀ x, x ∉ ["eo", "et", "no", "nt", "dd"] → σ12.arrs x = σ.arrs x := fun x hx => by
    rw [hw12a, ha8 x hx]
  obtain ⟨σ13, r13, hm13, hin13, hw13⟩ := readWords_wordsAt (B := B) (ws := As) (σ := σ12) hin12
    (by rw [ha8' _ (by decide)]; exact ha) (by rw [ha8' _ (by decide)]; exact hst)
    (by rw [ha8' _ (by decide)]; exact hln) hAB hAv
  -- the frames from `σ8` to `σ13`
  have hv813 : ∀ x, x ∉ ["hc", "ci2", "cx", "fc", "fi", "fl", "m", "i", "p", "n", "j", "v"] →
      σ13.vars x = σ8.vars x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [r13.frame_var x (by simp [readWords, readWord, readEntries, readEntry, Com.wvars]; tauto),
      hv12 x (by simp; tauto)]
    simp only [hσ11, vars_setVar, if_neg hx.2.2.2.1]
    rw [hv10 x hx.2.1 hx.2.2.1]
    simp [hσ9, hx.1]
  have ha813 : ∀ x, x ∉ ["a", "st", "ln"] → σ13.arrs x = σ8.arrs x := by
    intro x hx
    rw [r13.frame_arr x (by simp [readWords, readWord, readEntries, readEntry, Com.warrs] at hx ⊢; tauto),
      hw12a]
  have hcn13 : σ13.vars "cn" = n := by rw [hv813 "cn" (by decide), hcn8]
  set σ14 := σ13.setVar "n" n with hσ14
  have r14 : Run B (.assign "n" (.var "cn")) σ13 σ14 2 :=
    (Run.assign (by simp only [evalB_var_iff]; exact ⟨hcn13.symm, by rw [hcn13]; omega⟩)).mono (by simp)
  have hrun : Run B finalRead σ σ14 (readCost n L Fs.length (toWord As).length) := by
    unfold finalRead
    have hR := Run.seq r9 (Run.seq r10 (Run.seq r11 (Run.seq r12 (Run.seq r13 r14))))
    refine (Run.seq r8 hR).mono ?_
    simp only [readCost, winCost]
    omega
  refine ⟨σ14, hrun, ⟨?_, ?_, by simp [hσ14]⟩, hw13.of_arrs (by simp [hσ14]) (by simp [hσ14])
      (by simp [hσ14]), ?_, ?_, by simp [hσ14, hm13], hrun.out_eq (by decide),
      by simp only [hσ14, arrs_setVar]; rw [ha813 _ (by decide), hdd8],
      fun x hx => hrun.frame_arr x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp [finalRead, readWinD, readDm, rdRow, rdEnt, readWin, readCsr, vtxRd, slotRd, skipLoop,
          skipFrames, forUp, readWords, readWord, readEntries, readEntry, Com.warrs]; tauto)⟩
  · refine hc5.of_eq ?_ ?_
    · simp only [hσ14, arrs_setVar]; rw [ha813 _ (by decide)]
    · simp only [hσ14, arrs_setVar]; rw [ha813 _ (by decide)]
  · refine hc6.of_eq ?_ ?_
    · simp only [hσ14, arrs_setVar]; rw [ha813 _ (by decide)]
    · simp only [hσ14, arrs_setVar]; rw [ha813 _ (by decide)]
  · simp only [hσ14, vars_setVar, show ("kk" : String) = "n" ↔ False by decide, if_false]
    rw [hv813 "kk" (by decide), hk8]
  · simp only [hσ14, vars_setVar, show ("qq" : String) = "n" ↔ False by decide, if_false]
    rw [hv813 "qq" (by decide), hq8]

end Lax185574Proofs.StpRam
