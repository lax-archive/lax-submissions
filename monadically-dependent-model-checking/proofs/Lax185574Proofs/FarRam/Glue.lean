import Lax185574Proofs.FarRam.Call


/-!
The glue program of lem:to-ftree.

Round `0` reads the tree and the scatter type. Round `j` reads the tree,
the state `0, j, |S|` and the words of the scatter type followed by the
answers to the first `j` queries. While `j` is below the number of
extensions, the round asks for the restriction of the child of
extension `j` to its last position. Otherwise it computes the far tree.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.ShiftRam

def locate : Com :=
  .seq (.assign "y" (.lit 0)) (.seq skipList (.seq (.assign "ye" (.var "y")) (.seq skipList
    (.seq (.assign "n0" (.add (.var "y") (.lit 3))) (.assign "nR" (.get "x" (.var "ye")))))))

def tailPre : Com :=
  .seq readWords (.seq (.assign "nw" (.var "m"))
    (.seq (.ite (.eq (.var "tg") (.lit 0)) (.assign "ns" (.var "nw")) .skip) locate))

def tailCmd : Com := .seq tailPre (.ite (.lt (.var "jr") (.var "nR")) emitCall finalCmd)

def readHdr : Com := .seq (.read "z0") (.seq (.read "jr") (.read "ns"))


/-- The facts at the start of the tail of a round. -/
structure TailIn (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t : Node (q + 1) ℓ) (k : ℕ) (W : List (List ℕ))
    (nS j : ℕ) (rin : List ℕ) (σ : Env) : Prop where
  inp : σ.inp = toWord W ++ rin
  xa : σ.arrs "x" = X
  hk : σ.vars "hk" = k
  hq : σ.vars "hq" = q + 1
  hl : σ.vars "hl" = ℓ
  jr : σ.vars "jr" = j
  ns0 : σ.vars "tg" = 0 → W.length = nS
  ns1 : σ.vars "tg" ≠ 0 → σ.vars "ns" = nS
  tgB : σ.vars "tg" < B
  la : total W ≤ (σ.arrs "a").length
  lst : W.length ≤ (σ.arrs "st").length
  lln : W.length ≤ (σ.arrs "ln").length
  lf : (σ.arrs "f").length = 4
  lbt : ℓ ≤ (σ.arrs "bt").length
  lmt : (Node.exts t).words.length * ℓ ≤ (σ.arrs "mt").length
  lfar : (Node.exts t).words.length ≤ (σ.arrs "far").length
  leqa : (Node.exts t).words.length ≤ (σ.arrs "eqa").length
  lsel : nS ≤ (σ.arrs "sel").length

theorem listEnd_listEnd {q ℓ : ℕ} {X : List ℕ} {t : Node (q + 1) ℓ} {rest : List ℕ}
    (hx : X.drop 0 = toWord t ++ rest) : listEnd X (listEnd X 0) = (toWord t).length := by
  obtain ⟨h1, h2⟩ := nodeSplit hx
  have e1 := (listAt h1).2.2.2.1
  have e2 := (listAt h2).2.2.2.1
  rw [e2, e1, toWord_node_succ, List.length_append]; omega

def preCost (W : List (List ℕ)) (X : List ℕ) : ℕ := 21 * (toWord W).length + 60 * X.length + 100

theorem tailPre_run (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t : Node (q + 1) ℓ) (rest : List ℕ)
    (hx : X.drop 0 = toWord t ++ rest) (k : ℕ) (W : List (List ℕ)) (nS j : ℕ) (rin : List ℕ)
    (σ : Env) (h : TailIn B X t k W nS j rin σ) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B)
    (hWB : (toWord W).length < B) (hWv : ∀ v ∈ toWord W, v < B) :
    ∃ σ', Run B tailPre σ σ' (preCost W X) ∧ WordsAt W σ' ∧ σ'.vars "nw" = W.length ∧
      σ'.vars "ns" = nS ∧ σ'.vars "ye" = listEnd X 0 ∧ σ'.vars "n0" = (toWord t).length + 3 ∧
      σ'.vars "nR" = (Node.exts t).words.length ∧ σ'.arrs "x" = X ∧ σ'.vars "hk" = k ∧
      σ'.vars "hq" = q + 1 ∧ σ'.vars "hl" = ℓ ∧ σ'.vars "jr" = j ∧ σ'.out = σ.out ∧
      (∀ a, (σ'.arrs a).length = (σ.arrs a).length) := by
  obtain ⟨σ1, r1, hm1, hinp1, hw1⟩ := readWords_wordsAt h.inp h.la h.lst h.lln hWB hWv
  have hfv1 : ∀ z, z ∉ readWords.wvars → σ1.vars z = σ.vars z := fun z hz => r1.frame_var z hz
  have hfa1 : ∀ a, a ∉ readWords.warrs → σ1.arrs a = σ.arrs a := fun a ha => r1.frame_arr a ha
  have hlen1 := run_length_arrs r1
  have hWl : W.length < B := by have := length_toWord_words W; omega
  set σ2 := σ1.setVar "nw" W.length
  have r2 : Run B (.assign "nw" (.var "m")) σ1 σ2 2 :=
    (Run.assign (by simp only [evalB_var_iff]; exact ⟨hm1.symm, by omega⟩)).mono (by simp)
  have htg2 : σ2.vars "tg" = σ.vars "tg" := by simp [σ2, hfv1 "tg" (by decide)]
  -- the number of entries of the scatter type
  obtain ⟨σ3, r3, hns3⟩ : ∃ σ3, Run B (.ite (.eq (.var "tg") (.lit 0)) (.assign "ns" (.var "nw")) .skip)
      σ2 σ3 6 ∧ σ3.vars "ns" = nS ∧ σ3.arrs = σ2.arrs ∧ σ3.out = σ2.out ∧
      ∀ z, z ≠ "ns" → σ3.vars z = σ2.vars z := by
    by_cases h0 : σ.vars "tg" = 0
    · refine ⟨σ2.setVar "ns" W.length, (Run.ite_true ?_ (Run.assign ?_)).mono (by simp), ?_, by simp,
        by simp, fun z hz => by simp [hz]⟩
      · rw [eq_true_iff' (by rw [htg2]; exact h.tgB) (by omega), htg2, h0]; rfl
      · simp only [evalB_var_iff]; exact ⟨by simp [σ2], by simp [σ2]; omega⟩
      · simp [h.ns0 h0]
    · refine ⟨σ2, (Run.ite_false ?_ Run.skip).mono (by simp), ?_, rfl, rfl, fun _ _ => rfl⟩
      · rw [eq_true_iff' (by rw [htg2]; exact h.tgB) (by omega), htg2]; simp [h0]
      · simp [σ2, hfv1 "ns" (by decide), h.ns1 h0]
  obtain ⟨hns3, ha3, ho3, hfv3⟩ := hns3
  -- locating the extensions
  have hx3 : σ3.arrs "x" = X := by rw [ha3]; simp [σ2, hfa1 "x" (by decide), h.xa]
  obtain ⟨hA, h2⟩ := nodeSplit hx
  have hL0 := listFacts_of hA
  have hLe := listFacts_of h2
  set e := listEnd X 0
  have heX : e < X.length := by have := hLe.frPos_le 0 (Nat.zero_le _); have := hLe.end_le; omega
  have hR0 : xg X e = (Node.exts t).words.length := (listAt h2).1
  obtain ⟨σ4, r4, hy4⟩ := skipList_spec B X 0 hL0 (by omega) hX (σ3.setVar "y" 0) ⟨by simp [hx3], by simp⟩
  have hx4 : σ4.arrs "x" = X := by rw [r4.frame_arr "x" (by decide)]; simp [hx3]
  set σ5 := σ4.setVar "ye" e
  have r5 : Run B (.assign "ye" (.var "y")) σ4 σ5 2 :=
    (Run.assign (by simp only [evalB_var_iff]; exact ⟨hy4.symm, by omega⟩)).mono (by simp)
  obtain ⟨σ6, r6, hy6⟩ := skipList_spec B X e hLe (by omega) hX σ5 ⟨by simp [σ5, hx4], by simp [σ5, hy4, e]⟩
  rw [listEnd_listEnd hx] at hy6
  have htl : (toWord t).length ≤ X.length := by
    have := congrArg List.length hx; simp at this; omega
  set σ7 := σ6.setVar "n0" ((toWord t).length + 3)
  have r7 : Run B (.assign "n0" (.add (.var "y") (.lit 3))) σ6 σ7 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨_, 3, ⟨hy6.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  have hx6 : σ6.arrs "x" = X := by rw [r6.frame_arr "x" (by decide)]; simp [σ5, hx4]
  have hye6 : σ6.vars "ye" = e := by rw [r6.frame_var "ye" (by decide)]; simp [σ5]
  set σ8 := σ7.setVar "nR" (Node.exts t).words.length
  have r8 : Run B (.assign "nR" (.get "x" (.var "ye"))) σ7 σ8 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    refine ⟨e, ⟨by simp [σ7, hye6], by simp [σ7, hye6]; omega⟩, ?_, by rw [← hR0]; exact xg_lt hX (by omega)⟩
    simp only [σ7, arrs_setVar, hx6]
    rw [List.getElem?_eq_getElem heX, ← xg_of_lt heX, hR0]
  -- the frames of the steps
  have hv48 : ∀ z, z ∉ ["y", "e1", "e2", "ye", "n0", "nR"] → σ8.vars z = σ3.vars z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp only [σ8, σ7, vars_setVar, if_neg hz.2.2.2.2.2, if_neg hz.2.2.2.2.1]
    rw [r6.frame_var z (by simp [skipList, skipBody, Com.wvars, hz.1, hz.2.1, hz.2.2.1])]
    simp only [σ5, vars_setVar, if_neg hz.2.2.2.1]
    rw [r4.frame_var z (by simp [skipList, skipBody, Com.wvars, hz.1, hz.2.1, hz.2.2.1])]
    simp [hz.1]
  have ha8 : σ8.arrs = σ3.arrs := by
    funext a
    simp only [σ8, σ7, arrs_setVar]
    rw [r6.frame_arr a (by simp [skipList, skipBody, Com.warrs])]
    simp only [σ5, arrs_setVar]
    rw [r4.frame_arr a (by simp [skipList, skipBody, Com.warrs])]
    simp
  have ho8 : σ8.out = σ3.out := by
    simp only [σ8, σ7, out_setVar]
    rw [r6.out_eq (by decide)]; simp only [σ5, out_setVar]; rw [r4.out_eq (by decide)]; simp
  have hv13 : ∀ z, z ∉ ["m", "i", "p", "n", "j", "v", "nw", "ns"] → σ3.vars z = σ.vars z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hfv3 z hz.2.2.2.2.2.2.2]; simp only [σ2, vars_setVar, if_neg hz.2.2.2.2.2.2.1]
    exact hfv1 z (by simp [readWords, readWord, readEntries, readEntry, Com.wvars]; tauto)
  refine ⟨σ8, ?_, ?_, ?_, ?_, by simp [σ8, σ7, hye6], by simp [σ8, σ7], by simp [σ8], by rw [ha8, hx3], ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · unfold tailPre locate
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8)))))))).mono ?_
    simp only [preCost, Expr.size]; omega
  · exact hw1.of_arrs (by rw [ha8, ha3]; simp [σ2]) (by rw [ha8, ha3]; simp [σ2]) (by rw [ha8, ha3]; simp [σ2])
  · rw [hv48 "nw" (by decide), hfv3 "nw" (by decide)]; simp [σ2]
  · rw [hv48 "ns" (by decide), hns3]
  · rw [hv48 "hk" (by decide), hv13 "hk" (by decide), h.hk]
  · rw [hv48 "hq" (by decide), hv13 "hq" (by decide), h.hq]
  · rw [hv48 "hl" (by decide), hv13 "hl" (by decide), h.hl]
  · rw [hv48 "jr" (by decide), hv13 "jr" (by decide), h.jr]
  · rw [ho8, ho3]; simp [σ2, r1.out_eq (by decide)]
  · intro a; rw [ha8, ha3]; simp [σ2, hlen1 a]

theorem evalB_lt_vars {B : ℕ} {σ : Env} {x y : String} {a b : ℕ} (hx : σ.vars x = a) (hy : σ.vars y = b)
    (ha : a < B) (hb : b < B) : (Cond.lt (.var x) (.var y)).evalB B σ = some (decide (a < b)) := by
  rw [evalB_condLt (evalB_var (by rw [hx]; exact ha)) (evalB_var (by rw [hy]; exact hb)), hx, hy]

/-- **The tail of a call round.** -/
theorem tail_call (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t : Node (q + 1) ℓ) (rest : List ℕ)
    (hx : X.drop 0 = toWord t ++ rest) (k : ℕ) (W : List (List ℕ)) (nS j : ℕ) (rin : List ℕ)
    (σ : Env) (h : TailIn B X t k W nS j rin σ) (hj : j < (Node.exts t).words.length)
    (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hb : WordsBound B W)
    (hWB : (toWord W).length + 4 < B) (hWv : ∀ v ∈ toWord W, v < B)
    (hvB : X.length + nS + k + q + ℓ + 6 < B) :
    ∃ σ', Run B tailCmd σ σ' (preCost W X + callCost W X j + 10) ∧ ∃ a ∈ Node.exts t,
      toWord a = (Node.exts t).words[j] ∧
      σ'.out = σ.out ++ ([1, 4 + W.length + total W, (toWord t).length + 3, 0, j + 1, nS, W.length + 1] ++
        frames W ++ [k + 1, q, ℓ + 1] ++ toWord a.2 ++ [1, ℓ]) := by
  obtain ⟨σ1, r1, hw1, hnw1, hns1, hye1, hn01, hnR1, hx1, hk1, hq1, hl1, hjr1, ho1, -⟩ :=
    tailPre_run B X t rest hx k W nS j rin σ h hX hXB (by omega) hWv
  have htl : (toWord t).length ≤ X.length := by
    have := congrArg List.length hx; simp at this; omega
  have hRX : (Node.exts t).words.length ≤ X.length := by
    obtain ⟨-, h2⟩ := nodeSplit hx
    have hLe := listFacts_of h2
    have hR0 := (listAt h2).1
    have hf1 := (hLe.frPos_le _ le_rfl).1
    have hf2 := (hLe.frPos_le _ le_rfl).2
    have hel := hLe.end_le
    omega
  have hWl := length_toWord_words W
  obtain ⟨σ2, r2, a, ha, haw, ho2⟩ := emitCall_run B X t rest hx k W nS ((toWord t).length + 3) j σ1 hw1 hb
    hnw1 hx1 hye1 hjr1 hj hn01 hns1 hk1 hq1 hl1 hX (by omega) (by omega) (by omega)
  refine ⟨σ2, ?_, a, ha, haw, by rw [ho2, ho1]⟩
  unfold tailCmd
  exact (Run.seq r1 (Run.ite_true (by rw [evalB_lt_vars hjr1 hnR1 (by omega) (by omega), decide_eq_true hj])
    r2)).mono (by simp only [Cond.size, Expr.size]; omega)

/-- **The tail of the last round.** -/
theorem tail_final (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t : Node (q + 1) ℓ) (rest : List ℕ)
    (hx : X.drop 0 = toWord t ++ rest) (k : ℕ) (W : List (List ℕ)) (nS : ℕ) (rin : List ℕ)
    (σ : Env) (h : TailIn B X t k W nS (Node.exts t).words.length rin σ)
    (hWl : W.length = nS + (Node.exts t).words.length)
    (h3 : ∀ j < nS, 3 ≤ (wd W j).length) (hb : WordsBound B W) (hX : ∀ v ∈ X, v < B)
    (hXB : X.length + 5 < B) (hWB : (toWord W).length + 4 < B) (hWv : ∀ v ∈ toWord W, v < B) (h9 : 9 < B)
    (hRB : 4 * (9 ^ (ℓ - 1) * Lax3.DistFO.rhoMinus (k + 1) q) + 2 * Lax3.DistFO.rhoMinus (k + 1) q + 2 < B)
    (hEB : (k + (q + 1) + 1) * q + 1 < B) (hkB : k + q + 3 < B)
    (hNB : (Node.exts t).words.length * ℓ + ℓ + nS + (Node.exts t).words.length + 2 < B) :
    ∃ σ', Run B tailCmd σ σ' (preCost W X + finalCost X W k q ℓ nS (Node.exts t).words.length + 10) ∧
      σ'.out = σ.out ++ 0 :: toWord (farList X (W.drop nS) k q ℓ (W.take nS)) := by
  obtain ⟨σ1, r1, hw1, hnw1, hns1, hye1, hn01, hnR1, hx1, hk1, hq1, hl1, hjr1, ho1, hlen1⟩ :=
    tailPre_run B X t rest hx k W nS _ rin σ h hX hXB (by omega) hWv
  obtain ⟨σ2, r2, ho2⟩ := finalCmd_run B X t rest hx k W nS σ1 ⟨hx1, by rw [hlen1]; exact h.lf, hl1⟩ hk1 hq1
    hw1 hns1 hWl (by rw [hlen1]; exact h.lbt) (by rw [hlen1]; exact h.lmt) (by rw [hlen1]; exact h.lfar)
    (by rw [hlen1]; exact h.leqa) (by rw [hlen1]; exact h.lsel) h3 hb hX hXB h9 hRB hEB hkB hNB
  refine ⟨σ2, ?_, by rw [ho2, ho1]⟩
  unfold tailCmd
  exact (Run.seq r1 (Run.ite_false (by rw [evalB_lt_vars hjr1 hnR1 (by omega) (by omega)]; simp) r2)).mono
    (by simp only [Cond.size, Expr.size]; omega)

def headCmd : Com :=
  .seq (.read "tg") (.seq (.read "sl") (.seq readTree
    (.ite (.eq (.var "tg") (.lit 0)) (.assign "jr" (.lit 0)) readHdr)))

/-- The glue program: the head, then the tail. -/
def glue : Com := .seq headCmd tailCmd

/-- The array lengths a round needs. -/
structure ExtOK {q ℓ : ℕ} (t : Node (q + 1) ℓ) (W : List (List ℕ)) (nS : ℕ) (ext : String → ℕ) : Prop where
  x : (toWord t).length ≤ ext "x"
  a : total W ≤ ext "a"
  st : W.length ≤ ext "st"
  ln : W.length ≤ ext "ln"
  f : ext "f" = 4
  bt : ℓ ≤ ext "bt"
  mt : (Node.exts t).words.length * ℓ ≤ ext "mt"
  far : (Node.exts t).words.length ≤ ext "far"
  eqa : (Node.exts t).words.length ≤ ext "eqa"
  sel : nS ≤ ext "sel"

theorem head_run (B : ℕ) (ext : String → ℕ) (tg sl k q ℓ : ℕ) (t : Node (q + 1) ℓ) (hdr : List ℕ)
    (W : List (List ℕ)) (nS j : ℕ) (rin : List ℕ) (he : ExtOK t W nS ext)
    (hcase : (tg = 0 ∧ hdr = [] ∧ j = 0 ∧ nS = W.length) ∨ (tg = 1 ∧ hdr = [0, j, nS]))
    (hv : ∀ v ∈ toWord t, v < B) (htB : (toWord t).length < B) (hsB : sl < B) (hkB : k + q + ℓ + 2 < B)
    (hjB : j + nS < B) :
    ∃ σ', Run B headCmd (initEnv ext ([tg, sl, k, q + 1, ℓ] ++ toWord t ++ hdr ++ toWord W ++ rin)) σ'
      (48 * (toWord t).length + 60) ∧
      TailIn B (toWord t ++ (List.replicate (ext "x") 0).drop (toWord t).length) t k W nS j rin σ' ∧
      σ'.out = [] := by
  set u := [tg, sl, k, q + 1, ℓ] ++ toWord t ++ hdr ++ toWord W ++ rin
  set σ0 := initEnv ext u
  have htg : tg < B := by rcases hcase with h | h <;> omega
  set σ1 : Env := { σ0.setVar "tg" tg with inp := sl :: ([k, q + 1, ℓ] ++ toWord t ++ (hdr ++ toWord W ++ rin)) }
  set σ2 : Env := { σ1.setVar "sl" sl with inp := [k, q + 1, ℓ] ++ toWord t ++ (hdr ++ toWord W ++ rin) }
  have r1 : Run B (.read "tg") σ0 σ1 1 := Run.read (by simp [σ0, u, initEnv])
  have r2 : Run B (.read "sl") σ1 σ2 1 := Run.read rfl
  obtain ⟨σ3, r3, hk3, hq3, hl3, hx3, hinp3⟩ := (readTree_spec B k (q + 1) ℓ t (hdr ++ toWord W ++ rin)
    (List.replicate (ext "x") 0) (by simpa using he.x) htB hv (by omega)) σ2
    ⟨rfl, by simp [σ2, σ1, σ0, initEnv]⟩
  have hfv3 : ∀ z, z ∉ readTree.wvars → σ3.vars z = σ2.vars z := fun z hz => r3.frame_var z hz
  have hfa3 : ∀ a, a ∉ readTree.warrs → σ3.arrs a = σ2.arrs a := fun a ha => r3.frame_arr a ha
  have hlen3 := run_length_arrs r3
  have htg3 : σ3.vars "tg" = tg := by rw [hfv3 "tg" (by decide)]; simp [σ2, σ1]
  have hc : (Cond.eq (.var "tg") (.lit 0)).evalB B σ3 = some (decide (tg = 0)) := by
    rw [eq_true_iff' (by rw [htg3]; exact htg) (by omega), htg3]
  have harr : ∀ a, (σ3.arrs a).length = ext a := fun a => by
    rw [hlen3]; simp [σ2, σ1, σ0, initEnv]
  rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨σ3.setVar "jr" 0, ?_, ?_, ?_⟩
    · unfold headCmd
      exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_true (by rw [hc]; rfl)
        (Run.assign (evalB_lit (by omega))))))).mono (by simp only [Cond.size, Expr.size]; omega)
    · refine ⟨by simpa using hinp3, by simpa using hx3, by simpa using hk3, by simpa using hq3,
        by simpa using hl3, by simp, fun _ => rfl, fun h => absurd (by simpa using htg3) h,
        by simp [htg3]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [arrs_setVar, harr]
      exacts [he.a, he.st, he.ln, he.f, he.bt, he.mt, he.far, he.eqa, he.sel]
    · simp only [out_setVar]; rw [r3.out_eq readTree_noWrite]; simp [σ2, σ1, σ0, initEnv]
  · set σ4 : Env := { σ3.setVar "z0" 0 with inp := j :: nS :: (toWord W ++ rin) }
    set σ5 : Env := { σ4.setVar "jr" j with inp := nS :: (toWord W ++ rin) }
    set σ6 : Env := { σ5.setVar "ns" nS with inp := toWord W ++ rin }
    refine ⟨σ6, ?_, ?_, ?_⟩
    · unfold headCmd readHdr
      exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.ite_false (by rw [hc]; rfl)
        (Run.seq (Run.read (by rw [hinp3]; rfl)) (Run.seq (Run.read rfl) (Run.read rfl))))))).mono
          (by simp only [Cond.size, Expr.size]; omega)
    · refine ⟨rfl, by simp [σ6, σ5, σ4, hx3], by simp [σ6, σ5, σ4, hk3], by simp [σ6, σ5, σ4, hq3],
        by simp [σ6, σ5, σ4, hl3], by simp [σ6, σ5], fun h => by simp [σ6, σ5, σ4, htg3] at h,
        fun _ => by simp [σ6], by simp [σ6, σ5, σ4, htg3]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp only [σ6, σ5, σ4, arrs_setVar, harr]
      exacts [he.a, he.st, he.ln, he.f, he.bt, he.mt, he.far, he.eqa, he.sel]
    · simp only [σ6, σ5, σ4, out_setVar]; rw [r3.out_eq readTree_noWrite]; simp [σ2, σ1, σ0, initEnv]

end Lax185574Proofs.FarRam
