import Lax185574Proofs.Words.TreeMap
import Lax185574Proofs.Words.JobWord

/-!
One-pass transformations of type trees into jobs (`Words/JobWord.lean`).
The program `jobProg readArgs subCmd grdCmd` reads a type tree and the
arguments with `readTree` and `readArgs`, lists the nodes (`bfs`), and writes for
every node, from the last to the first, two jobs: the atom candidates of
the node (flag `0`), and the extension candidates (flag `1`), where the
child of an extension is given by the indices of its jobs. Nothing is
sorted. The last item is the header and the indices of the jobs of the
root.

The indices of the jobs of every node are first put into the buffer
(`fillRefs`), so that the command `exList` of `Words/TreeExts.lean`
forms the items of the extension jobs unchanged. `jobProg_run` states
that the program writes the word of `rawJobs` and `rawFinal`, within a
polynomial cost and with values polynomial in the input.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- The indices of the jobs of node `c`: its atoms, and below height `q`
its extensions. Node `c` is processed as the `(N - 1 - c)`-th node. -/
def refsOf (q N : ℕ) (DA : List ℕ) (c : ℕ) : List ℕ :=
  if DA.getD c 0 < q then [2 * (N - 1 - c), 2 * (N - 1 - c) + 1] else [2 * (N - 1 - c)]

/-- The two jobs of node `c` of the list `PA, DA, FA` of the nodes. -/
def nodeJobs (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ) (q N : ℕ)
    (PA DA FA : List ℕ) (c : ℕ) : List Job :=
  [(0, atomCands sub (DA.getD c 0) X (PA.getD c 0)),
    (1, if DA.getD c 0 < q then
        exCands gsub (DA.getD c 0) X (listEnd X (PA.getD c 0))
          (fun i => refsOf q N DA (FA.getD c 0 + i)) (xg X (listEnd X (PA.getD c 0)))
      else [])]

/-- The jobs of all nodes, from the last node to the first. -/
def rawJobs (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ) (q N : ℕ)
    (PA DA FA : List ℕ) : List Job :=
  (List.range N).reverse.flatMap (nodeJobs sub gsub X q N PA DA FA)

/-- The last item: the header, and the jobs of the root. -/
def rawFinal (k q olv N : ℕ) : List ℕ × List ℕ :=
  ([k, q, olv], if 0 < q then [2 * (N - 1), 2 * (N - 1) + 1] else [2 * (N - 1)])

/-! ### Counting loops -/

/-- The counting loop: set `i` to `0`, then run `body` and increment `i` while `i < e`. -/
def forUpJ (i : String) (e : Expr) (body : Com) : Com :=
  .seq (.assign i (.lit 0))
    (.while (.lt (.var i) e) (.seq body (.assign i (.add (.var i) (.lit 1)))))

/-- The counting loop rule. `I k` holds after `k` rounds, the bound `e`
evaluates to `N` throughout, and each round costs at most `K`. -/
theorem forUpJ_run {B : ℕ} {i : String} {e : Expr} {body : Com} {N K : ℕ}
    (I : ℕ → Env → Prop) {σ : Env} (hN : N < B)
    (he : ∀ k ≤ N, ∀ τ, I k τ → τ.vars i = k → e.evalB B τ = some N)
    (h0 : I 0 (σ.setVar i 0))
    (hstep : ∀ k < N, ∀ τ, I k τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' K ∧ τ'.vars i = k ∧ I (k + 1) (τ'.setVar i (k + 1))) :
    ∃ σ', Run B (forUpJ i e body) σ σ' (N * (K + e.size + 7) + e.size + 5) ∧
      I N σ' ∧ σ'.vars i = N := by
  let J : Env → Prop := fun τ => ∃ k ≤ N, τ.vars i = k ∧ I k τ
  obtain ⟨σ', hrun, ⟨k, hk, hik, hI⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var i) e)
      (c := .seq body (.assign i (.add (.var i) (.lit 1)))) J (fun τ => N - τ.vars i)
      (K + 4)
      (fun τ ⟨k, hk, hik, hI⟩ => ⟨_, evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)⟩)
      (by
        rintro τ ⟨k, hk, hik, hI⟩ hc
        have hkN : k < N := by
          rw [evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)] at hc
          simp only [Option.some.injEq, decide_eq_true_eq] at hc
          omega
        obtain ⟨τ', hr, hi', hI'⟩ := hstep k hkN τ hI hik
        refine ⟨τ'.setVar i (k + 1), (Run.seq hr (Run.assign ?_)).mono (by simp),
          ⟨k + 1, hkN, by simp, hI'⟩, by simp; omega⟩
        simp [hi']; omega)
      (show J (σ.setVar i 0) from ⟨0, Nat.zero_le _, by simp, h0⟩)
  have hkN : k = N := by
    rw [evalB_condLt (evalB_var (by omega)) (he k hk σ' hI hik)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hkN] at hI hik
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hI, hik⟩
  simp only [Cond.size, Expr.size]
  have : N - (σ.setVar i 0).vars i = N := by simp
  rw [this]
  nlinarith

/-! ### Writing a list of words -/

/-- Write the list of the `m` words held in the arrays `a`, `st`, `ln`:
the number of words, then their frames. -/
def writeAll : Com := .seq (.write (.var "m")) (forUpJ "ow" (.var "m") writeWord)

theorem writeAll_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) (hm : σ.vars "m" = ws.length) :
    ∃ σ', Run B writeAll σ σ' ((13 * total ws + 30) * (ws.length + 1)) ∧
      σ'.out = σ.out ++ toWord ws := by
  have hlen := hb.len
  set σ1 : Env := { σ with out := σ.out ++ [ws.length] } with hσ1
  let I : ℕ → Env → Prop := fun k τ =>
    τ.out = σ.out ++ ws.length :: frames (ws.take k) ∧ τ.vars "m" = ws.length ∧ τ.arrs = σ.arrs
  obtain ⟨σ', hr, ⟨hout, -, -⟩, -⟩ := forUpJ_run (B := B) (i := "ow") (e := .var "m")
    (body := writeWord) (N := ws.length) (K := 13 * total ws + 14) I (σ := σ1) (by omega)
    (fun k _ τ hI _ => by rw [← hI.2.1]; exact evalB_var (by rw [hI.2.1]; omega))
    ⟨by simp [hσ1, frames], by simp [hσ1, hm], by simp [hσ1]⟩
    (by
      rintro k hk τ ⟨hout, hmτ, harr⟩ hik
      have hwτ : WordsAt ws τ := hw.of_arrs (by rw [harr]) (by rw [harr]) (by rw [harr])
      obtain ⟨τ', hr', hout'⟩ := writeWord_run hwτ hb hik hk
      have hwk : ws[k].length ≤ total ws := by
        have := length_wd_le ws k; rwa [wd_eq hk] at this
      refine ⟨τ', hr'.mono (by omega), by rw [hr'.frame_var "ow" (by decide), hik], ?_, ?_, ?_⟩
      · simp only [out_setVar, hout', hout, frames_take_succ'' hk]; simp
      · simp only [vars_setVar, show ("m" : String) = "ow" ↔ False by decide, if_false]
        rw [hr'.frame_var "m" (by decide), hmτ]
      · simp only [arrs_setVar]; funext b
        rw [hr'.frame_arr b (by simp [writeWord, writeEntry, Com.warrs]), harr])
  rw [List.take_length] at hout
  refine ⟨σ', ?_, by rw [hout, toWord_words]⟩
  unfold writeAll
  refine (Run.seq (Run.write (v := ws.length) (by simp [hm]; omega)) hr).mono ?_
  simp only [Expr.size]
  nlinarith

/-! ### The indices of the jobs of the nodes in the buffer -/

/-- The index of the first job of node `fi`, halved: `nn - 1 - fi`. -/
def fillIdx : Expr := .sub (.sub (.var "nn") (.lit 1)) (.var "fi")

/-- Put the indices of the jobs of node `fi` into the buffer, at `2 fi`. -/
def fillBody : Com :=
  .seq (.store "bs" (.var "fi") (.add (.var "fi") (.var "fi")))
    (.seq (.store "b" (.add (.var "fi") (.var "fi")) (.add fillIdx fillIdx))
      (.seq (.store "b" (.add (.add (.var "fi") (.var "fi")) (.lit 1))
          (.add (.add fillIdx fillIdx) (.lit 1)))
        (.ite (.lt (.get "dep" (.var "fi")) (.var "hq")) (.store "bl" (.var "fi") (.lit 2))
          (.store "bl" (.var "fi") (.lit 1)))))

/-- Put the indices of the jobs of all nodes into the buffer. -/
def fillRefs : Com := forUpJ "fi" (.var "nn") fillBody

theorem length_refsOf (q N : ℕ) (DA : List ℕ) (c : ℕ) :
    (refsOf q N DA c).length = if DA.getD c 0 < q then 2 else 1 := by
  unfold refsOf; split_ifs <;> rfl

theorem length_refsOf_le (q N : ℕ) (DA : List ℕ) (c : ℕ) : (refsOf q N DA c).length ≤ 2 := by
  rw [length_refsOf]; split_ifs <;> omega

theorem refsOf_lt {q N : ℕ} {DA : List ℕ} {c : ℕ} : ∀ r ∈ refsOf q N DA c, r < 2 * N + 2 := by
  intro r hr; unfold refsOf at hr; split_ifs at hr <;> simp at hr <;> omega

/-- The indices of the jobs of the nodes `c < k` are in the buffer. -/
def RefsIn (q N : ℕ) (DA : List ℕ) (k : ℕ) (τ : Env) : Prop :=
  ∀ c < k, (τ.arrs "bs").getD c 0 = 2 * c ∧ (τ.arrs "bl").getD c 0 = (refsOf q N DA c).length ∧
    (τ.arrs "b")[2 * c]? = some (2 * (N - 1 - c)) ∧ (τ.arrs "b")[2 * c + 1]? = some (2 * (N - 1 - c) + 1)

theorem bufWord_refsOf {q N : ℕ} {DA : List ℕ} {c : ℕ} {τ : Env}
    (h0 : (τ.arrs "b")[2 * c]? = some (2 * (N - 1 - c)))
    (h1 : (τ.arrs "b")[2 * c + 1]? = some (2 * (N - 1 - c) + 1)) :
    BufWord (refsOf q N DA c) (2 * c) τ := by
  intro j hj
  have hj2 := length_refsOf_le q N DA c
  unfold refsOf at hj ⊢
  split_ifs at hj ⊢ with h
  · simp at hj
    interval_cases j
    · simpa using h0
    · simpa using h1
  · simp at hj
    subst hj; simpa using h0

@[simp] theorem size_fillIdx : fillIdx.size = 5 := rfl

theorem evalB_fillIdx {B N k : ℕ} {τ : Env} (hn : τ.vars "nn" = N) (hf : τ.vars "fi" = k)
    (hN : N < B) (hk : k < B) (h1 : 1 < B) : fillIdx.evalB B τ = some (N - 1 - k) := by
  unfold fillIdx
  simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hn, hf]
  exact ⟨N - 1, k, ⟨N, 1, ⟨rfl, hN⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ⟨rfl, hk⟩, rfl, by omega⟩

theorem fillRefs_spec (B q N Lb Lbb : ℕ) (DA : List ℕ) (hNb : N ≤ Lb) (hNbb : 2 * N ≤ Lbb)
    (hDA : ∀ c < N, DA.getD c 0 ≤ q) (hDAl : N ≤ DA.length) (hB : 2 * N + 2 < B) (hqB : q < B) :
    Spec B (fun τ => τ.vars "nn" = N ∧ τ.vars "hq" = q ∧ τ.arrs "dep" = DA ∧
        (τ.arrs "bs").length = Lb ∧ (τ.arrs "bl").length = Lb ∧ (τ.arrs "b").length = Lbb)
      fillRefs (fun _ τ' => RefsIn q N DA N τ') (N * 60 + 6) := by
  rintro σ ⟨hnn, hhq, hdep, hbs, hbl, hb⟩
  let I : ℕ → Env → Prop := fun k τ => τ.vars "nn" = N ∧ τ.vars "hq" = q ∧ τ.arrs "dep" = DA ∧
    (τ.arrs "bs").length = Lb ∧ (τ.arrs "bl").length = Lb ∧ (τ.arrs "b").length = Lbb ∧
    RefsIn q N DA k τ
  obtain ⟨σ', hr, ⟨-, -, -, -, -, -, hR⟩, -⟩ := forUpJ_run (B := B) (i := "fi") (e := .var "nn")
    (body := fillBody) (N := N) (K := 52) I (σ := σ) (by omega)
    (fun k _ τ hI _ => by rw [← hI.1]; exact evalB_var (by rw [hI.1]; omega))
    ⟨by simp [hnn], by simp [hhq], by simp [hdep], by simp [hbs], by simp [hbl], by simp [hb],
      fun c hc => by omega⟩
    (by
      rintro k hk τ ⟨hn, hq, hd, hl1, hl2, hl3, hR⟩ hik
      have hdk : DA.getD k 0 ≤ q := hDA k hk
      set τa := τ.setArr "bs" k (2 * k) with hτa
      set τb := τa.setArr "b" (2 * k) (2 * (N - 1 - k)) with hτb
      set τc := τb.setArr "b" (2 * k + 1) (2 * (N - 1 - k) + 1) with hτc
      have hfi : ∀ ρ : Env, ρ.vars = τ.vars → ρ.vars "fi" = k := fun ρ h => by rw [h, hik]
      have hix := evalB_fillIdx (B := B) hn hik (by omega) (by omega) (by omega)
      have r1 : Run B (.store "bs" (.var "fi") (.add (.var "fi") (.var "fi"))) τ τa 5 := by
        refine (Run.store (idx := k) (v := 2 * k) ?_ ?_ ?_).mono (by simp)
        · simp [hik]; omega
        · simp only [evalB_bin_iff, evalB_var_iff, hik]
          exact ⟨k, k, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp; omega, by omega⟩
        · omega
      have hixa : fillIdx.evalB B τa = some (N - 1 - k) := evalB_fillIdx (by simp [hτa, hn])
        (by simp [hτa, hik]) (by omega) (by omega) (by omega)
      have r2 : Run B (.store "b" (.add (.var "fi") (.var "fi")) (.add fillIdx fillIdx)) τa τb
          15 := by
        refine (Run.store (idx := 2 * k) (v := 2 * (N - 1 - k)) ?_ ?_ ?_).mono (by simp)
        · simp only [evalB_bin_iff, evalB_var_iff, hτa, vars_setArr, hik]
          exact ⟨k, k, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp; omega, by omega⟩
        · rw [show 2 * (N - 1 - k) = Bop.add.apply (N - 1 - k) (N - 1 - k) by simp; omega]
          exact evalB_bin hixa hixa (by simp; omega)
        · simp [hτa]; omega
      have hixb : fillIdx.evalB B τb = some (N - 1 - k) := evalB_fillIdx (by simp [hτb, hτa, hn])
        (by simp [hτb, hτa, hik]) (by omega) (by omega) (by omega)
      have r3 : Run B (.store "b" (.add (.add (.var "fi") (.var "fi")) (.lit 1))
          (.add (.add fillIdx fillIdx) (.lit 1))) τb τc 19 := by
        refine (Run.store (idx := 2 * k + 1) (v := 2 * (N - 1 - k) + 1) ?_ ?_ ?_).mono (by simp)
        · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hτb, hτa, vars_setArr, hik]
          exact ⟨2 * k, 1, ⟨k, k, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp; omega, by omega⟩,
            ⟨rfl, by omega⟩, by simp, by omega⟩
        · rw [show 2 * (N - 1 - k) + 1 = Bop.add.apply (Bop.add.apply (N - 1 - k) (N - 1 - k)) 1 by
            simp; omega]
          exact evalB_bin (evalB_bin hixb hixb (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)
        · simp [hτb, hτa]; omega
      have hvc : τc.vars = τ.vars := by simp [hτc, hτb, hτa]
      have hdc : τc.arrs "dep" = DA := by simp [hτc, hτb, hτa, hd]
      have hdep_ev : (Expr.get "dep" (.var "fi")).evalB B τc = some (DA.getD k 0) := by
        simp only [evalB_get_iff, evalB_var_iff, hvc, hik, hdc]
        refine ⟨k, ⟨rfl, by omega⟩, ?_, by omega⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hlen : (refsOf q N DA k).length = if DA.getD k 0 < q then 2 else 1 := length_refsOf q N DA k
      set v := (refsOf q N DA k).length with hv
      have r4 : Run B (.ite (.lt (.get "dep" (.var "fi")) (.var "hq")) (.store "bl" (.var "fi") (.lit 2))
          (.store "bl" (.var "fi") (.lit 1))) τc (τc.setArr "bl" k v) 8 := by
        by_cases hlt : DA.getD k 0 < q
        · rw [if_pos hlt] at hlen
          rw [hlen]
          refine (Run.ite_true ?_ (Run.store (idx := k) (v := 2) ?_ ?_ ?_)).mono (by simp)
          · simp only [evalB_condLt_iff]
            exact ⟨DA.getD k 0, q, hdep_ev, by simp [hvc, hq]; omega, (decide_eq_true hlt).symm⟩
          · simp [hvc, hik]; omega
          · simp; omega
          · simp [hτc, hτb, hτa]; omega
        · rw [if_neg hlt] at hlen
          rw [hlen]
          refine (Run.ite_false ?_ (Run.store (idx := k) (v := 1) ?_ ?_ ?_)).mono (by simp)
          · simp only [evalB_condLt_iff]
            exact ⟨DA.getD k 0, q, hdep_ev, by simp [hvc, hq]; omega, (decide_eq_false hlt).symm⟩
          · simp [hvc, hik]; omega
          · simp; omega
          · simp [hτc, hτb, hτa]; omega
      refine ⟨τc.setArr "bl" k v, ?_, by simp [hvc, hik], ?_⟩
      · unfold fillBody
        refine (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono ?_
        simp
      · refine ⟨by simp [hτc, hτb, hτa, hn], by simp [hτc, hτb, hτa, hq], by simp [hτc, hτb, hτa, hd],
          by simp [hτc, hτb, hτa, hl1], by simp [hτc, hτb, hτa, hl2], by simp [hτc, hτb, hτa, hl3], ?_⟩
        intro c hc
        have hbs' : ((τc.setArr "bl" k v).setVar "fi" (k + 1)).arrs "bs" = (τ.arrs "bs").set k (2 * k) := by
          simp [hτc, hτb, hτa]
        have hbl' : ((τc.setArr "bl" k v).setVar "fi" (k + 1)).arrs "bl" = (τ.arrs "bl").set k v := by
          simp [hτc, hτb, hτa]
        have hb' : ((τc.setArr "bl" k v).setVar "fi" (k + 1)).arrs "b" =
            ((τ.arrs "b").set (2 * k) (2 * (N - 1 - k))).set (2 * k + 1) (2 * (N - 1 - k) + 1) := by
          simp [hτc, hτb, hτa]
        rw [hbs', hbl', hb', getD_set_of_lt (by omega), getD_set_of_lt (by omega)]
        by_cases hck : c = k
        · subst hck
          rw [if_pos rfl, if_pos rfl]
          refine ⟨rfl, rfl, ?_, ?_⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
          · rw [List.getElem?_set_self (by simp; omega)]
        · obtain ⟨h1, h2, h3, h4⟩ := hR c (by omega)
          simp only [if_neg hck]
          refine ⟨h1, h2, ?_, ?_⟩
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h3]
          · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), h4])
  exact ⟨σ', hr.mono (by simp), hR⟩

theorem RefsIn.of_arrs {q N : ℕ} {DA : List ℕ} {k : ℕ} {τ τ' : Env} (h : RefsIn q N DA k τ)
    (h1 : τ'.arrs "bs" = τ.arrs "bs") (h2 : τ'.arrs "bl" = τ.arrs "bl") (h3 : τ'.arrs "b" = τ.arrs "b") :
    RefsIn q N DA k τ' := by
  intro c hc; rw [h1, h2, h3]; exact h c hc

/-! ### The jobs of one node -/

/-- Write the two jobs of node `u`: its atom candidates with flag `0`,
and with flag `1` its extension candidates, whose children are given by
the indices of their jobs. -/
def jobNode (subCmd grdCmd : Com) : Com :=
  .seq (.assign "y" (.get "pos" (.var "u"))) (.seq (.assign "dd" (.get "dep" (.var "u")))
    (.seq (atList subCmd) (.seq (.write (.lit 0)) (.seq writeAll
      (.ite (.lt (.var "dd") (.var "hq"))
        (.seq (exList grdCmd) (.seq (.write (.lit 1)) writeAll))
        (.seq (.write (.lit 1)) (.write (.lit 0))))))))

/-- The word of the two jobs of node `c`. -/
def nodeOut (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ) (q N : ℕ)
    (PA DA FA : List ℕ) (c : ℕ) : List ℕ :=
  ((nodeJobs sub gsub X q N PA DA FA c).map toWord).flatten

/-- The cost bound of `writeAll` for at most `n` words of total length at most `n`. -/
def writeAllCost (n : ℕ) : ℕ := (13 * n + 30) * (n + 1)

/-- The cost bound of the jobs of one node. -/
def jobNodeCost (Ks Kg n : ℕ) : ℕ :=
  ((Ks + 34) * n + 64) * n + 30 + ((Kg + 18 * n + 84) * n + 40) + 2 * writeAllCost n + 20

theorem toWord_rawJob (f : ℕ) (ws : List (List ℕ)) : toWord ((f, ws) : Job) = f :: toWord ws := rfl

theorem two_le_toWord_succ {h ℓ : ℕ} (t : Node (h + 1) ℓ) : 2 ≤ (toWord t).length := by
  rw [toWord_node_succ, List.length_append, toWord_words, toWord_words]; simp; omega

theorem writeAll_noWrite_arrs : writeAll.warrs = [] := by
  simp [writeAll, forUpJ, writeWord, writeEntry, Com.warrs]

theorem atList_noWrite {subCmd : Com} (hFs : HookFrame subCmd) : (atList subCmd).NoWrite := by
  simp [atList, atFrame, atEntries, atEntry, Com.NoWrite, hFs.2.2.2]

theorem exList_noWrite {grdCmd : Com} (hFg : HookFrame grdCmd) : (exList grdCmd).NoWrite := by
  simp [exList, exFrame, exCopies, exCopy, Com.NoWrite, hFg.2.2.2]

theorem jobNode_spec (subCmd grdCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ)
    (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop) (B Ks Kg : ℕ)
    (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd) (hS : SubOK subCmd sub Dat B Ks)
    (hG : GrdOK grdCmd gsub Dat B Kg) (hD : DatOK Dat)
    (X : List ℕ) (q N : ℕ) (PA DA FA : List ℕ) (Alen Slen : ℕ)
    (hnodes : NodesOK X q N PA DA) (hscan : ScannedOK X q N N PA DA FA)
    (hN : N ≤ X.length + 1) (hPAl : N ≤ PA.length) (hDAl : N ≤ DA.length) (hFAl : N ≤ FA.length)
    (hX : ∀ v ∈ X, v < B) (hXB : 2 * X.length + 6 < B) (hqB : q + 1 < B)
    (hsub : ∀ dd ≤ q, ∀ tg k v r, v ∈ X → sub tg k dd v = some r → r < B)
    (hgsub : ∀ dd ≤ q, ∀ i r, i ∈ X → gsub dd i = some r → r < B)
    (hA : X.length ≤ Alen) (hSl : X.length < Slen) (v : ℕ) (hv : v < N) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "hq" = q ∧ τ.vars "u" = v ∧
        τ.arrs "pos" = PA ∧ τ.arrs "dep" = DA ∧ τ.arrs "fc" = FA ∧ Dat τ ∧ RefsIn q N DA N τ ∧
        N ≤ (τ.arrs "bs").length ∧ N ≤ (τ.arrs "bl").length ∧ (τ.arrs "a").length = Alen ∧
        (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen)
      (jobNode subCmd grdCmd)
      (fun τ τ' => τ'.out = τ.out ++ nodeOut sub gsub X q N PA DA FA v)
      (jobNodeCost Ks Kg X.length) := by
  rintro τ ⟨hxa, hhq, hu, hpa, hda, hfa, hdat, hR, hbsl, hbll, hal, hstl, hlnl⟩
  obtain ⟨hdq, hNd⟩ := hnodes v hv
  obtain ⟨p, hp⟩ : ∃ p, PA.getD v 0 = p := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, DA.getD v 0 = d := ⟨_, rfl⟩
  rw [hp, hd] at hNd
  rw [hd] at hdq
  obtain ⟨ws0, r0, hws0⟩ := hNd.atomList
  have hLF : ListFacts X p := listFacts_of hws0
  obtain ⟨-, hpe, hen, hnx⟩ := hNd.atoms
  obtain ⟨ℓt, t, rt, hxt⟩ := hNd
  have htl : (toWord t).length ≤ X.length := by
    have := le_of_drop_eq hxt (toWord_node_ne_nil t); omega
  have hpB : p < B := by omega
  have hdB : d < B := by omega
  have hev1 : (Expr.get "pos" (.var "u")).evalB B τ = some p := by
    simp only [evalB_get_iff, evalB_var_iff, hu, hpa]
    refine ⟨v, ⟨rfl, by omega⟩, ?_, hpB⟩
    rw [← hp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  set τ1 := τ.setVar "y" p with hτ1
  have hev2 : (Expr.get "dep" (.var "u")).evalB B τ1 = some d := by
    simp only [evalB_get_iff, evalB_var_iff, hτ1, vars_setVar, arrs_setVar, hu, hda]
    refine ⟨v, ⟨by simp, by simp; omega⟩, ?_, hdB⟩
    rw [← hd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  set τ2 := τ1.setVar "dd" d with hτ2
  -- the atom candidates
  obtain ⟨τ3, hr3, hx3, hy3, hdd3, hdat3, hm3, hw3, hal3, hst3, hln3⟩ :=
    atList_spec subCmd sub Dat B Ks hFs hS hD X p d Alen Slen hLF hX (by omega) hdB hA hSl τ2
      ⟨by simp [hτ2, hτ1, hxa], by simp [hτ2, hτ1], by simp [hτ2, hτ1],
        hD τ τ2 (by simp [hτ2, hτ1]) (by simp [hτ2, hτ1]) (by simp [hτ2, hτ1])
          (by simp [hτ2, hτ1]) (by simp [hτ2, hτ1]) hdat,
        by simp [hτ2, hτ1, hal], by simp [hτ2, hτ1, hstl], by simp [hτ2, hτ1, hlnl]⟩
  have hwv := fun y => atList_var hFs (y := y)
  have hwa' := fun b => atList_arr hFs (b := b)
  set ws1 := atomCands sub d X p with hws1
  have hc1 := atCands_le sub d X p (xg X p)
  rw [atCands_full, ← hws1] at hc1
  have hle0 : (toWord ws0).length ≤ X.length := by
    have := le_of_drop_eq hws0 (by rw [toWord_words]; simp); omega
  have ht1 := toWord_atomCands_le hws0 sub d
  rw [← hws1] at ht1
  have hlw1 := length_toWord_words ws1
  have hb1 : WordsBound B ws1 := by
    refine ⟨by omega, fun u hu w hw => ?_, by omega⟩
    rw [hws1, atomCands] at hu
    obtain ⟨u0, hu0, hu0u⟩ := List.mem_filterMap.mp hu
    simp only [listWords, List.mem_map, List.mem_range] at hu0
    obtain ⟨j, -, rfl⟩ := hu0
    exact atomMap_lt (hsub d hdq) (fun v hv => mem_frWord hv) hu0u w hw
  have hws1l : ws1.length ≤ X.length := by omega
  have hws1t : total ws1 ≤ X.length := by omega
  -- writing the atom job
  set τ4 : Env := { τ3 with out := τ3.out ++ [0] } with hτ4
  obtain ⟨τ5, hr5, hout5⟩ := writeAll_run (B := B) (ws := ws1) (σ := τ4) (hw3.of_arrs rfl rfl rfl) hb1 hm3
  have hW1 : (13 * total ws1 + 30) * (ws1.length + 1) ≤ writeAllCost X.length :=
    Nat.mul_le_mul (by omega) (by omega)
  have hout3 : τ3.out = τ.out := by rw [hr3.out_eq (atList_noWrite hFs)]; simp [hτ2, hτ1]
  have ha5 : ∀ b, τ5.arrs b = τ3.arrs b := fun b => hr5.frame_arr b (by rw [writeAll_noWrite_arrs]; simp)
  have hca : ∀ b, b ∉ ["a", "st", "ln"] → τ5.arrs b = τ.arrs b := by
    intro b hb; rw [ha5 b, hr3.frame_arr b (hwa' b hb)]; simp [hτ2, hτ1]
  have hcv : ∀ y, y ∈ ["u", "hq", "g1", "g2", "g3", "g4"] → τ5.vars y = τ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [hr5.frame_var _ (by decide)]
      show τ3.vars _ = _
      rw [hr3.frame_var _ (hwv _ (by decide) (by decide))]
      simp [hτ2, hτ1]
  have hx5 : τ5.arrs "x" = X := by rw [hca "x" (by decide), hxa]
  have hfa5 : τ5.arrs "fc" = FA := by rw [hca "fc" (by decide), hfa]
  have hu5 : τ5.vars "u" = v := by rw [hcv "u" (by simp), hu]
  have hq5 : τ5.vars "hq" = q := by rw [hcv "hq" (by simp), hhq]
  have hdd5 : τ5.vars "dd" = d := by rw [hr5.frame_var _ (by decide)]; exact hdd3
  have hy5 : τ5.vars "y" = listEnd X p := by rw [hr5.frame_var _ (by decide)]; exact hy3
  have hdat5 : Dat τ5 := hD τ τ5 (hcv "g1" (by simp)) (hcv "g2" (by simp)) (hcv "g3" (by simp))
    (hcv "g4" (by simp)) (hca "gt" (by decide)) hdat
  have hR5 : RefsIn q N DA N τ5 :=
    hR.of_arrs (hca "bs" (by decide)) (hca "bl" (by decide)) (hca "b" (by decide))
  have hout5' : τ5.out = τ.out ++ (0 :: toWord ws1) := by
    rw [hout5, hτ4]; simp [hout3]
  have hpre : Run B (.seq (.assign "y" (.get "pos" (.var "u"))) (.seq (.assign "dd" (.get "dep" (.var "u")))
      (.seq (atList subCmd) (.seq (.write (.lit 0)) writeAll)))) τ τ5
      (4 + 4 + (((Ks + 34) * X.length + 64) * X.length + 30) + 2 + writeAllCost X.length) := by
    refine (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2) (Run.seq hr3
      (Run.seq (Run.write (v := 0) (by simp; omega)) hr5)))).mono ?_
    simp only [Expr.size]; omega
  have hjob1 : nodeOut sub gsub X q N PA DA FA v = (0 :: toWord ws1) ++
      toWord ((1, if d < q then exCands gsub d X (listEnd X p)
          (fun i => refsOf q N DA (FA.getD v 0 + i)) (xg X (listEnd X p)) else []) : Job) := by
    simp only [nodeOut, nodeJobs, hp, hd, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, toWord_rawJob, hws1]
  by_cases hdq' : d < q
  · -- an inner node: the extension job
    obtain ⟨h', hh'⟩ : ∃ h', q - d = h' + 1 := ⟨q - d - 1, by omega⟩
    have hN' : NodeAt X p (h' + 1) := by rw [← hh']; exact ⟨ℓt, t, rt, hxt⟩
    obtain ⟨hch, -, hend'⟩ := hN'.exts
    obtain ⟨ℓ2, t2, r2, hxt2⟩ := hN'
    obtain ⟨-, hext⟩ := nodeSplit hxt2
    obtain ⟨e, he⟩ : ∃ e, listEnd X p = e := ⟨_, rfl⟩
    rw [he] at hext hch hend'
    have hLFe : ListFacts X e := listFacts_of hext
    have hcnt := hLFe.frPos_le (xg X e) le_rfl
    have hendE := hLFe.end_le
    obtain ⟨hvFC, hFCN, hsc⟩ := hscan v hv
    obtain ⟨FC, hFC⟩ : ∃ FC, FA.getD v 0 = FC := ⟨_, rfl⟩
    rw [hFC] at hvFC hFCN hsc
    rw [hd, hp, he] at hsc
    have hsc' := hsc hdq'
    set T : ℕ → List ℕ := fun i => refsOf q N DA (FC + i) with hT
    have hTlen : ∀ i < xg X e, (T i).length + 1 ≤ xg X (frPos X e i) := by
      intro i hi
      obtain ⟨⟨ℓ3, μ, r3, hμ⟩, hne, -⟩ := hch i hi
      have h2 := nodeEnd_eq hμ
      have h3 : frPos X e (i + 1) = frPos X e i + 1 + xg X (frPos X e i) := skipFr_succ' _ _ _
      obtain ⟨-, -, hdep⟩ := hsc' i hi
      have hTl : (T i).length = if d + 1 < q then 2 else 1 := by
        simp only [hT, length_refsOf, hdep]
      have hμl : (if d + 1 < q then 2 else 1) ≤ (toWord μ).length := by
        split_ifs with hlt'
        · obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := ⟨h' - 1, by omega⟩
          exact two_le_toWord_succ μ
        · have := List.length_pos_iff.mpr (toWord_node_ne_nil μ); omega
      omega
    have hTB : ∀ i < xg X e, ∀ w ∈ T i, w < B := by
      intro i _ w hw
      have := refsOf_lt w hw; omega
    have hFCc : FC + xg X e ≤ N := by
      rcases Nat.eq_zero_or_pos (xg X e) with h0 | h0
      · omega
      · have := (hsc' (xg X e - 1) (by omega)).1; omega
    have hbs5 : N ≤ (τ5.arrs "bs").length := by rw [hca "bs" (by decide)]; exact hbsl
    have hbl5 : N ≤ (τ5.arrs "bl").length := by rw [hca "bl" (by decide)]; exact hbll
    have hcb : ChildBuf X e FC T B τ5 := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ⟨by omega, by omega⟩, fun i hi => ?_⟩
      · obtain ⟨hlt, -, -⟩ := hsc' i hi; exact (hR5 (FC + i) hlt).2.1
      · obtain ⟨hlt, -, -⟩ := hsc' i hi
        obtain ⟨h1, -, h3, h4⟩ := hR5 (FC + i) hlt
        rw [h1]; exact bufWord_refsOf h3 h4
      · obtain ⟨hlt, -, -⟩ := hsc' i hi
        rw [(hR5 (FC + i) hlt).1]; have := length_refsOf_le q N DA (FC + i); simp only [hT]; omega
    have hfr1 : ∀ i < xg X e, 1 ≤ xg X (frPos X e i) := fun i hi => (hch i hi).2.2
    obtain ⟨τ6, hr6, hx6, hy6, hdd6, hdat6, hm6, hw6, hcb6, hal6, hst6, hln6⟩ :=
      exList_spec grdCmd gsub Dat B Kg hFg hG hD X e d FC T Alen Slen hLFe hfr1 hTlen hTB hX (by omega)
        hdB (by omega) hA hSl τ5 ⟨hx5, by rw [hy5, he], hdd5, hdat5,
          by rw [hfa5, hu5]; omega, by rw [hu5]; omega, by rw [hfa5, hu5, hFC], hcb,
          by rw [ha5]; exact hal3, by rw [ha5]; exact hst3, by rw [ha5]; exact hln3⟩
    set ws2 := exCands gsub d X e T (xg X e) with hws2
    have hc2 := exCands_le gsub d X e T hTlen (xg X e) le_rfl
    rw [← hws2] at hc2
    have hb2 : WordsBound B ws2 := by
      refine ⟨by omega, fun u hu w hw => ?_, by omega⟩
      rw [hws2, exCands] at hu
      obtain ⟨i, hi, hiu⟩ := List.mem_filterMap.mp hu
      rw [List.mem_range] at hi
      simp only [Option.map_eq_some_iff] at hiu
      obtain ⟨g, hg, rfl⟩ := hiu
      rcases List.mem_cons.mp hw with rfl | hw
      · have h1 := hfr1 i hi
        have h2 := (hLFe.frPos_le (i + 1) (by omega)).2
        have h3 : frPos X e (i + 1) = frPos X e i + 1 + xg X (frPos X e i) := skipFr_succ' _ _ _
        exact hgsub d (by omega) _ _ (xg_mem (by omega)) hg
      · exact hTB i hi w hw
    have hfe2 : frPos X e (xg X e) = listEnd X e := rfl
    have hws2l : ws2.length ≤ X.length := by omega
    have hws2t : total ws2 ≤ X.length := by omega
    set τ7 : Env := { τ6 with out := τ6.out ++ [1] } with hτ7
    obtain ⟨τ8, hr8, hout8⟩ := writeAll_run (B := B) (ws := ws2) (σ := τ7) (hw6.of_arrs rfl rfl rfl) hb2 hm6
    have hW2 : (13 * total ws2 + 30) * (ws2.length + 1) ≤ writeAllCost X.length :=
      Nat.mul_le_mul (by omega) (by omega)
    have hout6 : τ6.out = τ5.out := by rw [hr6.out_eq (exList_noWrite hFg)]
    refine ⟨τ8, ?_, ?_⟩
    · unfold jobNode
      refine (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2) (Run.seq hr3
        (Run.seq (Run.write (v := 0) (by simp; omega)) (Run.seq hr5 (Run.ite_true ?_
          (Run.seq hr6 (Run.seq (Run.write (v := 1) (by simp; omega)) hr8)))))))).mono ?_
      · simp only [evalB_condLt_iff, evalB_var_iff, hdd5, hq5]
        exact ⟨d, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hdq']⟩
      · simp only [Cond.size, Expr.size, jobNodeCost]; omega
    · show τ8.out = τ.out ++ nodeOut sub gsub X q N PA DA FA v
      rw [hjob1, if_pos hdq', hout8, hτ7, hout6, hout5', toWord_rawJob, he, hFC]
      simp [hws2, hT]
  · -- a leaf: no extensions
    set τ6 : Env := { τ5 with out := τ5.out ++ [1] } with hτ6
    set τ7 : Env := { τ6 with out := τ6.out ++ [0] } with hτ7
    refine ⟨τ7, ?_, ?_⟩
    · unfold jobNode
      refine (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2) (Run.seq hr3
        (Run.seq (Run.write (v := 0) (by simp; omega)) (Run.seq hr5 (Run.ite_false ?_
          (Run.seq (Run.write (v := 1) (by simp; omega)) (Run.write (v := 0) (by simp; omega))))))))).mono ?_
      · simp only [evalB_condLt_iff, evalB_var_iff, hdd5, hq5]
        exact ⟨d, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hdq']⟩
      · simp only [Cond.size, Expr.size, jobNodeCost]; omega
    · show τ7.out = τ.out ++ nodeOut sub gsub X q N PA DA FA v
      rw [hjob1, if_neg hdq', hτ7, hτ6, hout5', toWord_rawJob]
      simp [toWord_words, frames]

/-! ### The jobs of all nodes, from the last to the first -/

/-- Write the jobs of all listed nodes, from the last to the first. -/
def jobLoop (subCmd grdCmd : Com) : Com :=
  .seq (.assign "u" (.var "nn")) (.while (.lt (.lit 0) (.var "u"))
    (.seq (.assign "u" (.sub (.var "u") (.lit 1))) (jobNode subCmd grdCmd)))

/-- The scalars that the jobs of a node may write. -/
def jobVars : List String :=
  ["y", "dd", "e1", "e2", "m", "ap", "lf", "tg", "dr", "kk", "ev", "cc", "gi", "cs", "cl", "ck",
    "pa", "la", "k", "ow"]

theorem jobNode_var {subCmd grdCmd : Com} (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd)
    {y : String} (h1 : y ∉ hookVars) (h2 : y ∉ jobVars) : y ∉ (jobNode subCmd grdCmd).wvars := by
  have ha := atList_var hFs h1 (y := y) (by intro h; apply h2; simp [jobVars] at h ⊢; tauto)
  have he := exList_var hFg h1 (y := y) (by intro h; apply h2; simp [jobVars] at h ⊢; tauto)
  have hw : y ∉ writeAll.wvars := by
    intro h; apply h2; simp [writeAll, forUpJ, writeWord, writeEntry, Com.wvars, jobVars] at h ⊢; tauto
  have hs : y ∉ ["y", "dd"] := by intro h; apply h2; simp [jobVars] at h ⊢; tauto
  simp only [jobNode, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.nil_append, List.append_nil, not_or] at hs ⊢
  simp_all

theorem jobNode_arr {subCmd grdCmd : Com} (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd)
    {b : String} (h1 : b ∉ ["a", "st", "ln"]) : b ∉ (jobNode subCmd grdCmd).warrs := by
  have ha := atList_arr hFs h1
  have he := exList_arr hFg h1
  simp only [jobNode, Com.warrs, writeAll_noWrite_arrs, List.mem_append, List.nil_append,
    List.append_nil, not_or]
  exact ⟨ha, he⟩

theorem jobLoop_var {subCmd grdCmd : Com} (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd)
    {y : String} (h1 : y ∉ hookVars) (h2 : y ∉ jobVars) (hu : y ≠ "u") :
    y ∉ (jobLoop subCmd grdCmd).wvars := by
  have := jobNode_var hFs hFg h1 h2
  simp only [jobLoop, Com.wvars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨hu, hu, this⟩

theorem jobLoop_arr {subCmd grdCmd : Com} (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd)
    {b : String} (h1 : b ∉ ["a", "st", "ln"]) : b ∉ (jobLoop subCmd grdCmd).warrs := by
  have := jobNode_arr hFs hFg h1
  simp only [jobLoop, Com.warrs, List.nil_append]
  exact this

/-- The words of the jobs of the nodes `u, …, N - 1`, from the last to the first. -/
def jobsFrom (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ) (q N : ℕ)
    (PA DA FA : List ℕ) (u : ℕ) : List ℕ :=
  ((List.range' u (N - u)).reverse.map (nodeOut sub gsub X q N PA DA FA)).flatten

theorem jobsFrom_pred (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ)
    (q N : ℕ) (PA DA FA : List ℕ) {v : ℕ} (hv : v < N) :
    jobsFrom sub gsub X q N PA DA FA v =
      jobsFrom sub gsub X q N PA DA FA (v + 1) ++ nodeOut sub gsub X q N PA DA FA v := by
  have hm : N - v = (N - (v + 1)) + 1 := by omega
  simp only [jobsFrom, hm, List.range'_succ, List.reverse_cons, List.map_append, List.flatten_append,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The invariant of `jobLoop`: the jobs of the nodes from `u` on are written. -/
def JLInv (Dat : Env → Prop) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ)
    (X : List ℕ) (q N : ℕ) (PA DA FA : List ℕ) (Alen Slen : ℕ) (O : List ℕ) (τ : Env) : Prop :=
  τ.arrs "x" = X ∧ τ.vars "hq" = q ∧ τ.vars "nn" = N ∧ τ.vars "u" ≤ N ∧ τ.arrs "pos" = PA ∧
    τ.arrs "dep" = DA ∧ τ.arrs "fc" = FA ∧ Dat τ ∧ RefsIn q N DA N τ ∧
    N ≤ (τ.arrs "bs").length ∧ N ≤ (τ.arrs "bl").length ∧ (τ.arrs "a").length = Alen ∧
    (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen ∧
    τ.out = O ++ jobsFrom sub gsub X q N PA DA FA (τ.vars "u")

theorem jobLoop_spec (subCmd grdCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ)
    (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop) (B Ks Kg : ℕ)
    (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd) (hS : SubOK subCmd sub Dat B Ks)
    (hG : GrdOK grdCmd gsub Dat B Kg) (hD : DatOK Dat)
    (X : List ℕ) (q N : ℕ) (PA DA FA : List ℕ) (Alen Slen : ℕ)
    (hnodes : NodesOK X q N PA DA) (hscan : ScannedOK X q N N PA DA FA)
    (hN : N ≤ X.length + 1) (hPAl : N ≤ PA.length) (hDAl : N ≤ DA.length) (hFAl : N ≤ FA.length)
    (hX : ∀ v ∈ X, v < B) (hXB : 2 * X.length + 6 < B) (hqB : q + 1 < B)
    (hsub : ∀ dd ≤ q, ∀ tg k v r, v ∈ X → sub tg k dd v = some r → r < B)
    (hgsub : ∀ dd ≤ q, ∀ i r, i ∈ X → gsub dd i = some r → r < B)
    (hA : X.length ≤ Alen) (hSl : X.length < Slen) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "hq" = q ∧ τ.vars "nn" = N ∧ τ.arrs "pos" = PA ∧
        τ.arrs "dep" = DA ∧ τ.arrs "fc" = FA ∧ Dat τ ∧ RefsIn q N DA N τ ∧
        N ≤ (τ.arrs "bs").length ∧ N ≤ (τ.arrs "bl").length ∧ (τ.arrs "a").length = Alen ∧
        (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen)
      (jobLoop subCmd grdCmd)
      (fun τ τ' => τ'.out = τ.out ++ jobsFrom sub gsub X q N PA DA FA 0)
      ((jobNodeCost Ks Kg X.length + 12) * (X.length + 1) + 10) := by
  rintro τ ⟨hxa, hhq, hnn, hpa, hda, hfa, hdat, hR, hbsl, hbll, hal, hstl, hlnl⟩
  have hNB : N < B := by omega
  set τ0 := τ.setVar "u" N with hτ0
  have hI0 : JLInv Dat sub gsub X q N PA DA FA Alen Slen τ.out τ0 := by
    refine ⟨by simp [hτ0, hxa], by simp [hτ0, hhq], by simp [hτ0, hnn], by simp [hτ0], by simp [hτ0, hpa],
      by simp [hτ0, hda], by simp [hτ0, hfa],
      hD τ τ0 (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) hdat,
      hR.of_arrs (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]),
      by simp [hτ0, hbsl], by simp [hτ0, hbll], by simp [hτ0, hal], by simp [hτ0, hstl],
      by simp [hτ0, hlnl], by simp [hτ0, jobsFrom]⟩
  have hbody : Spec B (fun ρ => JLInv Dat sub gsub X q N PA DA FA Alen Slen τ.out ρ ∧
      (Cond.lt (.lit 0) (.var "u")).evalB B ρ = some true)
      (.seq (.assign "u" (.sub (.var "u") (.lit 1))) (jobNode subCmd grdCmd))
      (fun ρ ρ' => JLInv Dat sub gsub X q N PA DA FA Alen Slen τ.out ρ' ∧ ρ'.vars "u" < ρ.vars "u")
      (jobNodeCost Ks Kg X.length + 4) := by
    rintro ρ ⟨⟨hx, hq, hn, hule, hp, hd, hf, hdt, hRρ, h1, h2, h3, h4, h5, hout⟩, hc⟩
    have hpos : 0 < ρ.vars "u" := by
      simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at hc
      obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, h⟩ := hc
      simpa using h.symm
    obtain ⟨v, hv⟩ : ∃ v, ρ.vars "u" = v + 1 := ⟨ρ.vars "u" - 1, by omega⟩
    set ρ1 := ρ.setVar "u" v with hρ1
    obtain ⟨ρ2, hr2, hout2⟩ := jobNode_spec subCmd grdCmd sub gsub Dat B Ks Kg hFs hFg hS hG hD X q N
      PA DA FA Alen Slen hnodes hscan hN hPAl hDAl hFAl hX hXB hqB hsub hgsub hA hSl v (by omega) ρ1
        ⟨by simp [hρ1, hx], by simp [hρ1, hq], by simp [hρ1], by simp [hρ1, hp],
          by simp [hρ1, hd], by simp [hρ1, hf],
          hD ρ ρ1 (by simp [hρ1]) (by simp [hρ1]) (by simp [hρ1]) (by simp [hρ1]) (by simp [hρ1]) hdt,
          hRρ.of_arrs (by simp [hρ1]) (by simp [hρ1]) (by simp [hρ1]),
          by simp [hρ1, h1], by simp [hρ1, h2], by simp [hρ1, h3], by simp [hρ1, h4], by simp [hρ1, h5]⟩
    have hv2 : ∀ y, y ∉ hookVars → y ∉ jobVars → y ≠ "u" → ρ2.vars y = ρ.vars y := by
      intro y hy1 hy2 hy3
      rw [hr2.frame_var y (jobNode_var hFs hFg hy1 hy2)]
      simp [hρ1, hy3]
    have ha2 : ∀ b, b ∉ ["a", "st", "ln"] → ρ2.arrs b = ρ.arrs b := by
      intro b hb; rw [hr2.frame_arr b (jobNode_arr hFs hFg hb)]; simp [hρ1]
    have hu2 : ρ2.vars "u" = v := by
      rw [hr2.frame_var "u" (jobNode_var hFs hFg (by decide) (by decide))]
      simp [hρ1]
    refine ⟨ρ2, (Run.seq (Run.assign (v := v) ?_) hr2).mono (by simp; omega), ⟨?_, ?_, ?_, by omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨v + 1, 1, ⟨hv.symm, by omega⟩, ⟨rfl, by omega⟩, by simp, by omega⟩
    · rw [ha2 "x" (by decide), hx]
    · rw [hv2 "hq" (by decide) (by decide) (by decide), hq]
    · rw [hv2 "nn" (by decide) (by decide) (by decide), hn]
    · rw [ha2 "pos" (by decide), hp]
    · rw [ha2 "dep" (by decide), hd]
    · rw [ha2 "fc" (by decide), hf]
    · exact hD ρ ρ2 (hv2 "g1" (by decide) (by decide) (by decide)) (hv2 "g2" (by decide) (by decide) (by decide))
        (hv2 "g3" (by decide) (by decide) (by decide)) (hv2 "g4" (by decide) (by decide) (by decide)) (ha2 "gt" (by decide)) hdt
    · exact hRρ.of_arrs (ha2 "bs" (by decide)) (ha2 "bl" (by decide)) (ha2 "b" (by decide))
    · rw [ha2 "bs" (by decide)]; exact h1
    · rw [ha2 "bl" (by decide)]; exact h2
    · rw [Run.length_arrs hr2]; simp [hρ1, h3]
    · rw [Run.length_arrs hr2]; simp [hρ1, h4]
    · rw [Run.length_arrs hr2]; simp [hρ1, h5]
    · rw [hout2, hu2, jobsFrom_pred sub gsub X q N PA DA FA (show v < N by omega), ← hv]
      simp [hρ1, hout]
  have hK : ∀ ρ, ρ = τ0 → (1 + (Cond.lt (.lit 0) (.var "u")).size + (jobNodeCost Ks Kg X.length + 4)) *
      ρ.vars "u" + 1 + (Cond.lt (.lit 0) (.var "u")).size ≤
      (jobNodeCost Ks Kg X.length + 8) * (X.length + 1) + 4 := by
    intro ρ h; subst h
    simp only [hτ0, vars_setVar, if_true, Cond.size, Expr.size]
    have h2 : 1 + (1 + 1 + 1) + (jobNodeCost Ks Kg X.length + 4) = jobNodeCost Ks Kg X.length + 8 := by ring
    rw [h2]
    have := Nat.mul_le_mul_left (jobNodeCost Ks Kg X.length + 8) hN
    omega
  obtain ⟨τ', hr, hI', hfalse⟩ := (Spec.while_count (B := B) (P := fun ρ => ρ = τ0)
    (b := .lt (.lit 0) (.var "u"))
    (c := .seq (.assign "u" (.sub (.var "u") (.lit 1))) (jobNode subCmd grdCmd))
    (K := (jobNodeCost Ks Kg X.length + 8) * (X.length + 1) + 4)
    (JLInv Dat sub gsub X q N PA DA FA Alen Slen τ.out) (fun ρ => ρ.vars "u") (jobNodeCost Ks Kg X.length + 4)
    (fun ρ hI => ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (by have := hI.2.2.2.1; omega))⟩)
    hbody (fun ρ h => h ▸ hI0) hK).run rfl
  have hu' : τ'.vars "u" = 0 := by
    simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at hfalse
    obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, h⟩ := hfalse
    simp at h; omega
  refine ⟨τ', ?_, ?_⟩
  · unfold jobLoop
    refine (Run.seq (Run.assign (v := N) (by simp [hnn]; omega)) hr).mono ?_
    simp only [Expr.size]
    have : (jobNodeCost Ks Kg X.length + 8) * (X.length + 1) ≤
        (jobNodeCost Ks Kg X.length + 12) * (X.length + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · show τ'.out = _
    rw [hI'.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hu']

/-! ### The program -/

/-- Twice the index of the first job of the root, `2 (nn - 1)`. -/
def rootIdx : Expr := .add (.sub (.var "nn") (.lit 1)) (.sub (.var "nn") (.lit 1))

@[simp] theorem size_rootIdx : rootIdx.size = 7 := rfl

theorem evalB_rootIdx {B N : ℕ} {τ : Env} (hn : τ.vars "nn" = N) (hB : 2 * N + 2 < B) :
    rootIdx.evalB B τ = some (2 * (N - 1)) := by
  unfold rootIdx
  simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hn]
  exact ⟨N - 1, N - 1, ⟨N, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
    ⟨N, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, by simp; omega, by omega⟩

/-- Write the indices of the jobs of the root. -/
def rootRefs : Com :=
  .ite (.lt (.lit 0) (.var "hq"))
    (.seq (.write (.lit 2)) (.seq (.write rootIdx) (.write (.add rootIdx (.lit 1)))))
    (.seq (.write (.lit 1)) (.write rootIdx))

/-- The jobs of a transformation of a type tree: read the tree and the
arguments, list the nodes, put the indices of their jobs into the buffer,
write the number of jobs and the jobs of all nodes, and then the header
and the indices of the jobs of the root. -/
def jobProg (readArgs subCmd grdCmd : Com) : Com :=
  .seq readTree (.seq readArgs (.seq bfs (.seq fillRefs
    (.seq (.write (.add (.var "nn") (.var "nn"))) (.seq (jobLoop subCmd grdCmd)
      (.seq (.write (.lit 3)) (.seq (.write (.var "hk")) (.seq (.write (.var "hq"))
        (.seq (.write (.var "ol")) rootRefs)))))))))

/-- The array lengths of `jobProg` on an input of length `n`, where `G`
is the length of `gt`. -/
def jobExt (n G : ℕ) : String → ℕ := fun a =>
  if a = "x" ∨ a = "a" then n + 1
  else if a = "pos" ∨ a = "dep" ∨ a = "fc" ∨ a = "bs" ∨ a = "bl" ∨ a = "st" ∨ a = "ln" then n + 2
  else if a = "b" then 2 * n + 4
  else if a = "gt" then G
  else 0

/-- The cost bound of `jobProg` on an input of length `n`. -/
def jobCost (Ks Kg Ka n : ℕ) : ℕ :=
  (48 * n + 40) + Ka + ((60 * (n + 1) + 84) * (n + 2) + 30) + ((n + 2) * 60 + 6) + 4 +
    ((jobNodeCost Ks Kg (n + 1) + 12) * (n + 2) + 10) + 40

theorem jobCost_le (Ks Kg Ka n : ℕ) :
    jobCost Ks Kg Ka n ≤ (Ks + Kg + Ka + 1000) * 1000 * (n + 1) ^ 4 := by
  simp only [jobCost, jobNodeCost, writeAllCost]
  nlinarith [Nat.zero_le n, Nat.zero_le (n * n), Nat.zero_le (n * n * n), Nat.zero_le (n * n * n * n),
    Nat.zero_le (Ks * n), Nat.zero_le (Ks * n * n), Nat.zero_le (Ks * n * n * n),
    Nat.zero_le (Ks * n * n * n * n), Nat.zero_le (Kg * n), Nat.zero_le (Kg * n * n),
    Nat.zero_le (Kg * n * n * n), Nat.zero_le (Kg * n * n * n * n), Nat.zero_le (Ka * n),
    Nat.zero_le (Ka * n * n), Nat.zero_le (Ka * n * n * n), Nat.zero_le (Ka * n * n * n * n),
    Nat.zero_le Ks, Nat.zero_le Kg, Nat.zero_le Ka]

theorem toWord_rawJobs (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (gsub : ℕ → ℕ → Option ℕ) (X : List ℕ)
    (q N : ℕ) (PA DA FA : List ℕ) :
    toWord (rawJobs sub gsub X q N PA DA FA) = (2 * N) :: jobsFrom sub gsub X q N PA DA FA 0 := by
  change (rawJobs sub gsub X q N PA DA FA).length ::
    ((rawJobs sub gsub X q N PA DA FA).map toWord).flatten = _
  congr 1
  · simp [rawJobs, nodeJobs, List.length_flatMap]; ring
  · simp only [rawJobs, jobsFrom, List.flatMap, List.map_flatten, List.range_eq_range', Nat.sub_zero]
    rw [List.flatten_flatten, List.map_map, List.map_map]
    rfl

theorem toWord_rawFinal (k q olv N : ℕ) : toWord (rawFinal k q olv N) = [3, k, q, olv] ++
    (if 0 < q then [2, 2 * (N - 1), 2 * (N - 1) + 1] else [1, 2 * (N - 1)]) := by
  change toWord ([k, q, olv] : List ℕ) ++
    toWord (if 0 < q then [2 * (N - 1), 2 * (N - 1) + 1] else [2 * (N - 1)]) = _
  rw [toWord_listNat, toWord_listNat]
  split_ifs <;> rfl

theorem fillRefs_noWrite : fillRefs.NoWrite := by
  simp [fillRefs, forUpJ, fillBody, Com.NoWrite]

set_option maxHeartbeats 1000000 in
/-- **The jobs of a transformation of a type tree.** -/
theorem jobProg_run (readArgs subCmd grdCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ)
    (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop) (B Ks Kg Ka : ℕ)
    (hFs : HookFrame subCmd) (hFg : HookFrame grdCmd) (hFa : ArgFrame readArgs)
    (hS : SubOK subCmd sub Dat B Ks) (hG : GrdOK grdCmd gsub Dat B Kg) (hD : DatOK Dat)
    (k q ℓ : ℕ) (t : Node q ℓ) (argW : List ℕ) (G olv : ℕ)
    (hA : Spec B (fun τ => τ.inp = argW ∧ τ.vars "hl" = ℓ ∧ τ.arrs "gt" = List.replicate G 0)
      readArgs (fun _ τ' => Dat τ' ∧ τ'.vars "ol" = olv) Ka)
    (hx : ∀ v ∈ [k, q, ℓ] ++ toWord t ++ argW, v < B)
    (hB : (([k, q, ℓ] ++ toWord t ++ argW).length + 2) * (([k, q, ℓ] ++ toWord t ++ argW).length + 2) < B)
    (hsub : ∀ dd ≤ q, ∀ tg kk v r, (v ∈ toWord t ∨ v = 0) → sub tg kk dd v = some r → r < B)
    (hgsub : ∀ dd ≤ q, ∀ i r, (i ∈ toWord t ∨ i = 0) → gsub dd i = some r → r < B) (holB : olv < B)
    (hq1B : q + 1 < B) :
    ∃ (σ' : Env) (N : ℕ) (PA DA FA : List ℕ),
      Run B (jobProg readArgs subCmd grdCmd)
        (initEnv (jobExt ([k, q, ℓ] ++ toWord t ++ argW).length G) ([k, q, ℓ] ++ toWord t ++ argW)) σ'
        (jobCost Ks Kg Ka ([k, q, ℓ] ++ toWord t ++ argW).length) ∧
      NodesOK (toWord t ++ List.replicate (([k, q, ℓ] ++ toWord t ++ argW).length + 1 - (toWord t).length) 0)
        q N PA DA ∧
      ScannedOK (toWord t ++ List.replicate (([k, q, ℓ] ++ toWord t ++ argW).length + 1 - (toWord t).length) 0)
        q N N PA DA FA ∧
      PA.getD 0 0 = 0 ∧ DA.getD 0 0 = 0 ∧ 1 ≤ N ∧ N ≤ (toWord t).length + 1 ∧
      σ'.out = toWord (rawJobs sub gsub
        (toWord t ++ List.replicate (([k, q, ℓ] ++ toWord t ++ argW).length + 1 - (toWord t).length) 0)
        q N PA DA FA, rawFinal k q olv N) := by
  set x := [k, q, ℓ] ++ toWord t ++ argW with hxdef
  obtain ⟨n, hn⟩ : ∃ n, x.length = n := ⟨_, rfl⟩
  rw [hn] at hB ⊢
  have hnt : (toWord t).length + 3 ≤ n := by rw [← hn]; simp [hxdef]
  have htn : 1 ≤ (toWord t).length := List.length_pos_iff.mpr (toWord_node_ne_nil t)
  have hB1 : 2 * n + 8 < B := by nlinarith
  set ext := jobExt n G with hext
  set O := List.replicate (n + 1) 0 with hO
  obtain ⟨X, hX⟩ : ∃ X, toWord t ++ List.replicate (n + 1 - (toWord t).length) 0 = X := ⟨_, rfl⟩
  rw [hX]
  have hXO : X = toWord t ++ O.drop (toWord t).length := by rw [← hX]; simp [hO, List.drop_replicate]
  have hXl : X.length = n + 1 := by rw [← hX]; simp; omega
  have hXv : ∀ v ∈ X, v < B := by
    intro v hv
    rw [← hX] at hv
    rcases List.mem_append.mp hv with h | h
    · exact hx v (by simp [hxdef, h])
    · rw [List.eq_of_mem_replicate h]; omega
  have htv : ∀ v ∈ toWord t, v < B := fun v h => hx v (by simp [hxdef, h])
  have hqB : q < B := hx q (by simp [hxdef])
  have hkB : k < B := hx k (by simp [hxdef])
  have hXmem : ∀ v ∈ X, v ∈ toWord t ∨ v = 0 := by
    intro v hv
    rw [← hX] at hv
    rcases List.mem_append.mp hv with h | h
    · exact Or.inl h
    · exact Or.inr (List.eq_of_mem_replicate h)
  have hsub' : ∀ dd ≤ q, ∀ tg kk v r, v ∈ X → sub tg kk dd v = some r → r < B :=
    fun dd h tg kk v r hv => hsub dd h tg kk v r (hXmem v hv)
  have hgsub' : ∀ dd ≤ q, ∀ i r, i ∈ X → gsub dd i = some r → r < B :=
    fun dd h i r hi => hgsub dd h i r (hXmem i hi)
  have hroot : NodeAt X 0 q := ⟨ℓ, t, List.replicate (n + 1 - (toWord t).length) 0, by simp [← hX]⟩
  have hL0 : nodeEnd X 0 q = (toWord t).length := by
    rw [nodeEnd_eq (t := t) (r := List.replicate (n + 1 - (toWord t).length) 0) (by simp [← hX])]; simp
  -- reading
  set σ0 := initEnv ext x with hσ0
  obtain ⟨σ1, hr1, hk1, hq1, hl1, hx1, hinp1⟩ := readTree_spec B k q ℓ t argW O (by simp [hO]; omega)
    (by omega) htv hqB σ0 ⟨by simp [hσ0, initEnv, hxdef], by simp [hσ0, initEnv, hext, jobExt, hO]⟩
  rw [← hXO] at hx1
  have hv1 : ∀ y, y ∉ readTree.wvars → σ1.vars y = σ0.vars y := fun y h => hr1.frame_var y h
  have ha1 : ∀ b, b ∉ readTree.warrs → σ1.arrs b = σ0.arrs b := fun b h => hr1.frame_arr b h
  obtain ⟨σ2, hr2, hdat2, hol2⟩ := hA σ1 ⟨hinp1, hl1, by rw [ha1 "gt" (by decide)]; simp [hσ0, initEnv, hext, jobExt]⟩
  have hv2 : ∀ y, y ∉ ["g1", "g2", "g3", "g4", "ol", "r1", "r2", "r3"] → σ2.vars y = σ1.vars y :=
    fun y h => hr2.frame_var y (fun hm => h (hFa.1 y hm))
  have ha2 : ∀ b, b ≠ "gt" → σ2.arrs b = σ1.arrs b := fun b h => hr2.frame_arr b (fun hm => h (hFa.2.1 b hm))
  have hinit : ∀ b, b ≠ "x" → b ≠ "gt" → σ2.arrs b = List.replicate (ext b) 0 := by
    intro b h1 h2
    rw [ha2 b h2, ha1 b (by simp [readTree, cpList, cpFrame, cpEntries, cpEntry, Com.warrs]; exact h1)]
    rfl
  -- listing the nodes
  have hextP : ∀ b, b = "pos" ∨ b = "dep" ∨ b = "fc" ∨ b = "bs" ∨ b = "bl" ∨ b = "st" ∨ b = "ln" →
      ext b = n + 2 := by
    intro b hb; simp only [hext, jobExt]; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  obtain ⟨σ3, hr3, hI3, hun3⟩ := bfs_spec B X q (n + 2) (by omega) hXv (by omega) hroot (by omega) σ2
    ⟨by rw [ha2 "x" (by decide), hx1], by rw [hv2 "hq" (by decide), hq1],
      by rw [hinit "pos" (by decide) (by decide), List.length_replicate, hextP "pos" (by simp)],
      by rw [hinit "dep" (by decide) (by decide), List.length_replicate, hextP "dep" (by simp)],
      by rw [hinit "fc" (by decide) (by decide), List.length_replicate, hextP "fc" (by simp)]⟩
  obtain ⟨hx3, hq3, -, hn13, hsum3, hpl3, hdl3, hfl3, hnodes3, hscan3, hr03, hd03⟩ := hI3
  have hv3 : ∀ y, y ∉ bfs.wvars → σ3.vars y = σ2.vars y := fun y h => hr3.frame_var y h
  have ha3 : ∀ b, b ∉ bfs.warrs → σ3.arrs b = σ2.arrs b := fun b h => hr3.frame_arr b h
  set N := σ3.vars "nn" with hN
  set PA := σ3.arrs "pos" with hPA
  set DA := σ3.arrs "dep" with hDA
  set FA := σ3.arrs "fc" with hFA
  rw [hun3] at hscan3
  have hNt : N ≤ (toWord t).length + 1 := by rw [hL0] at hsum3; omega
  have hNX : N ≤ X.length + 1 := by omega
  have hdat3 : Dat σ3 := hD σ2 σ3 (hv3 "g1" (by decide)) (hv3 "g2" (by decide)) (hv3 "g3" (by decide))
    (hv3 "g4" (by decide)) (ha3 "gt" (by decide)) hdat2
  have hlen3 : ∀ b, b ∉ bfs.warrs → b ≠ "x" → b ≠ "gt" → σ3.arrs b = List.replicate (ext b) 0 :=
    fun b h1 h2 h3 => by rw [ha3 b h1, hinit b h2 h3]
  -- the indices of the jobs
  obtain ⟨σ4, hr4, hR4⟩ := fillRefs_spec B q N (n + 2) (2 * n + 4) DA (by omega) (by omega)
    (fun c hc => (hnodes3 c hc).1) (by omega) (by omega) hqB σ3
    ⟨rfl, hq3, rfl, by rw [hlen3 "bs" (by decide) (by decide) (by decide)]; simp [hext, jobExt],
      by rw [hlen3 "bl" (by decide) (by decide) (by decide)]; simp [hext, jobExt],
      by rw [hlen3 "b" (by decide) (by decide) (by decide)]; simp [hext, jobExt]⟩
  have hv4 : ∀ y, y ∉ fillRefs.wvars → σ4.vars y = σ3.vars y := fun y h => hr4.frame_var y h
  have ha4 : ∀ b, b ∉ fillRefs.warrs → σ4.arrs b = σ3.arrs b := fun b h => hr4.frame_arr b h
  have hl4 : ∀ b, (σ4.arrs b).length = (σ3.arrs b).length := Run.length_arrs hr4
  set σ5 : Env := { σ4 with out := σ4.out ++ [2 * N] } with hσ5
  have hdat5 : Dat σ5 := hD σ3 σ5 (hv4 "g1" (by decide)) (hv4 "g2" (by decide)) (hv4 "g3" (by decide))
    (hv4 "g4" (by decide)) (ha4 "gt" (by decide)) hdat3
  -- the jobs
  obtain ⟨σ6, hr6, hout6⟩ := jobLoop_spec subCmd grdCmd sub gsub Dat B Ks Kg hFs hFg hS hG hD X q N
    PA DA FA (n + 1) (n + 2) hnodes3 hscan3 hNX (by omega) (by omega) (by omega) hXv (by omega)
    (by omega) hsub' hgsub' (by omega) (by omega) σ5
    ⟨by show σ4.arrs "x" = X; rw [ha4 "x" (by decide)]; exact hx3,
      by show σ4.vars "hq" = q; rw [hv4 "hq" (by decide)]; exact hq3,
      hv4 "nn" (by decide), ha4 "pos" (by decide), ha4 "dep" (by decide), ha4 "fc" (by decide), hdat5,
      hR4,
      by show N ≤ (σ4.arrs "bs").length
         rw [hl4, hlen3 "bs" (by decide) (by decide) (by decide)]; simp [hext, jobExt]; omega,
      by show N ≤ (σ4.arrs "bl").length
         rw [hl4, hlen3 "bl" (by decide) (by decide) (by decide)]; simp [hext, jobExt]; omega,
      by show (σ4.arrs "a").length = n + 1
         rw [hl4, hlen3 "a" (by decide) (by decide) (by decide)]; simp [hext, jobExt],
      by show (σ4.arrs "st").length = n + 2
         rw [hl4, hlen3 "st" (by decide) (by decide) (by decide)]; simp [hext, jobExt],
      by show (σ4.arrs "ln").length = n + 2
         rw [hl4, hlen3 "ln" (by decide) (by decide) (by decide)]; simp [hext, jobExt]⟩
  have hjv : ∀ y, y ∉ hookVars → y ∉ jobVars → y ≠ "u" → σ6.vars y = σ4.vars y :=
    fun y h1 h2 h3 => hr6.frame_var y (jobLoop_var hFs hFg h1 h2 h3)
  have hk6 : σ6.vars "hk" = k := by
    rw [hjv "hk" (by decide) (by decide) (by decide), hv4 "hk" (by decide), hv3 "hk" (by decide),
      hv2 "hk" (by decide), hk1]
  have hq6 : σ6.vars "hq" = q := by
    rw [hjv "hq" (by decide) (by decide) (by decide), hv4 "hq" (by decide), hq3]
  have hol6 : σ6.vars "ol" = olv := by
    rw [hjv "ol" (by decide) (by decide) (by decide), hv4 "ol" (by decide), hv3 "ol" (by decide), hol2]
  have hnn6 : σ6.vars "nn" = N := by
    rw [hjv "nn" (by decide) (by decide) (by decide), hv4 "nn" (by decide)]
  have hout4 : σ4.out = [] := by
    rw [hr4.out_eq fillRefs_noWrite, hr3.out_eq bfs_noWrite, hr2.out_eq hFa.2.2,
      hr1.out_eq readTree_noWrite]
    rfl
  -- the last item
  set σ7 : Env := { σ6 with out := σ6.out ++ [3] } with hσ7
  set σ8 : Env := { σ7 with out := σ7.out ++ [k] } with hσ8
  set σ9 : Env := { σ8 with out := σ8.out ++ [q] } with hσ9
  set σ10 : Env := { σ9 with out := σ9.out ++ [olv] } with hσ10
  have hnn10 : σ10.vars "nn" = N := hnn6
  have hq10 : σ10.vars "hq" = q := hq6
  have hN2 : 2 * N + 2 < B := by omega
  obtain ⟨σ', hrr, hout'⟩ : ∃ σ', Run B rootRefs σ10 σ' 24 ∧ σ'.out = σ10.out ++
      (if 0 < q then [2, 2 * (N - 1), 2 * (N - 1) + 1] else [1, 2 * (N - 1)]) := by
    have hri := evalB_rootIdx hnn10 hN2
    by_cases hq0 : 0 < q
    · refine ⟨_, (Run.ite_true ?_ (Run.seq (Run.write (v := 2) (by simp; omega))
        (Run.seq (Run.write hri) (Run.write (v := 2 * (N - 1) + 1) ?_)))).mono (by simp), ?_⟩
      · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq10]
        exact ⟨0, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hq0]⟩
      · rw [show 2 * (N - 1) + 1 = Bop.add.apply (2 * (N - 1)) 1 by simp]
        refine evalB_bin ?_ (evalB_lit (by omega)) (by simp; omega)
        exact evalB_rootIdx hnn10 hN2
      · simp [if_pos hq0]
    · refine ⟨_, (Run.ite_false ?_ (Run.seq (Run.write (v := 1) (by simp; omega))
        (Run.write hri))).mono (by simp), ?_⟩
      · simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff, hq10]
        exact ⟨0, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hq0]⟩
      · simp [if_neg hq0]
  refine ⟨σ', N, PA, DA, FA, ?_, hnodes3, hscan3, hr03, hd03, hn13, hNt, ?_⟩
  · unfold jobProg
    refine (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq (Run.write (v := 2 * N) ?_)
      (Run.seq hr6 (Run.seq (Run.write (v := 3) ?_) (Run.seq (Run.write (v := k) ?_)
        (Run.seq (Run.write (v := q) ?_) (Run.seq (Run.write (v := olv) ?_) hrr)))))))))).mono ?_
    · simp only [evalB_bin_iff, evalB_var_iff, hv4 "nn" (by decide)]
      exact ⟨N, N, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp; omega, by omega⟩
    · simp; omega
    · simp [hk6]; omega
    · simp [hq6]; omega
    · simp [hol6]; exact holB
    · have h60 : N * 60 ≤ (n + 2) * 60 := Nat.mul_le_mul_right _ (by omega)
      simp only [jobCost, Expr.size, hXl, show n + 1 + 1 = n + 2 from rfl]
      omega
  · rw [hout', hσ10, hσ9, hσ8, hσ7, hout6, hσ5, hout4]
    change _ = toWord (rawJobs sub gsub X q N PA DA FA) ++ toWord (rawFinal k q olv N)
    rw [toWord_rawJobs, toWord_rawFinal]
    simp

end Lax185574Proofs.Words
