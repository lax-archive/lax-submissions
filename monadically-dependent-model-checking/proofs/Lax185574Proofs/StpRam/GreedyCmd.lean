import Lax185574Proofs.StpRam.GreedyPure
import Lax185574Proofs.Words.Select

/-!
The greedy scan of lem:compute-stp in IMP+.

The tree words are the words `A` in the arrays `a`, `st`, `ln`. For the
level `gi`, the radius `gr`, the index `gu` of the tree word `ν` in `A`
and the cap `cap`, `greedyCmd` scans the vertices `gv = 0, …, n − 1`.
While fewer than `cap` vertices are chosen, it compares the word of the
tree of level `gi` of `gv` with `ν`, and chooses `gv` if the words are
equal and `gv` is not blocked. Choosing scans the row of `gv` in
the distance matrix `dd` (`rowMark`) and adds the vertices within
distance `gr` of `gv` to the blocked vertices in `bl`. The number of
chosen vertices ends in `gc`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram

theorem cmpCode_eq_one {u v : List ℕ} : cmpCode u v = 1 ↔ u = v := by
  unfold cmpCode
  split_ifs with h1 h2
  · simp only [zero_ne_one, false_iff]; rintro rfl; exact lt_irrefl _ h1
  · simp [h2]
  · simp [h2]

/-! ### Marking a row of the distance matrix -/

/-- The step of `rowMark`: block `b` if the entry `(bu, b)` is positive
and at most `br + 1`. -/
def rmBody : Com :=
  .seq (.assign "be" (.get "dd" (.add (.mul (.var "bu") (.var "n")) (.var "b"))))
    (.ite (.lt (.lit 0) (.var "be"))
      (.ite (.lt (.var "br") (.sub (.var "be") (.lit 1))) .skip (.store "bl" (.var "b") (.lit 1)))
      .skip)

/-- Add the vertices within distance `br` of `bu` to the blocked
vertices, by a scan of row `bu` of the matrix in `dd`. -/
def rowMark : Com := forUp "b" (.var "n") rmBody

/-- The cost bound of `rowMark`. -/
def rmCost (n : ℕ) : ℕ := 32 * n + 6

set_option maxHeartbeats 1000000 in
/-- **Marking a row.** -/
theorem rowMark_run {B n u r : ℕ} {g h : ℕ → ℕ} {Q : ℕ → Prop} {σ : Env} (hn : σ.vars "n" = n)
    (hu : σ.vars "bu" = u) (hr : σ.vars "br" = r) (huN : u < n) (hnnB : n * n < B) (hrB : r < B)
    (hdd : σ.arrs "dd" = arrOf (n * n) g) (hgB : ∀ i < n * n, g i < B)
    (hbl : σ.arrs "bl" = arrOf n h) (hh : IndOn n h Q) :
    ∃ σ' h', Run B rowMark σ σ' (rmCost n) ∧ σ'.arrs "bl" = arrOf n h' ∧
      IndOn n h' (fun v => Q v ∨ DT g n u v r) ∧
      (∀ x, x ∉ ["b", "be"] → σ'.vars x = σ.vars x) ∧ (∀ x, x ≠ "bl" → σ'.arrs x = σ.arrs x) ∧
      σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  have hnB : n < B := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · omega
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left n h0) hnnB
  let I : ℕ → Env → Prop := fun k τ => τ.vars "n" = n ∧ τ.vars "bu" = u ∧ τ.vars "br" = r ∧
    τ.arrs "dd" = arrOf (n * n) g ∧
    τ.arrs "bl" = arrOf n (fun v => if v < k ∧ 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1 then 1
      else h v) ∧
    (∀ x, x ∉ ["b", "be"] → τ.vars x = σ.vars x) ∧ (∀ x, x ≠ "bl" → τ.arrs x = σ.arrs x) ∧
    τ.out = σ.out ∧ τ.inp = σ.inp
  obtain ⟨σ', hrun, ⟨-, -, -, -, hbl', hv', ha', ho', hi'⟩, -⟩ := forUp_run (B := B) (i := "b")
    (e := .var "n") (body := rmBody) (N := n) (K := 24) I (σ := σ) hnB
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.symm, by rw [hI.1]; omega⟩)
    ⟨by simp [hn], by simp [hu], by simp [hr], by simp [hdd], by simp [hbl],
      fun x hx => by simp at hx; simp [hx.1], fun x _ => by simp, by simp, by simp⟩
    (by
      rintro k hk τ ⟨hnτ, huτ, hrτ, hddτ, hblτ, hvτ, haτ, hoτ, hiτ⟩ hb
      have hidx : u * n + k < n * n := by
        have : u * n + n ≤ n * n := by
          have := Nat.mul_le_mul_right n (show u + 1 ≤ n by omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        omega
      set e := g (u * n + k) with he
      have heB : e < B := hgB _ hidx
      have hix : (Expr.add (.mul (.var "bu") (.var "n")) (.var "b")).evalB B τ = some (u * n + k) := by
        simp only [evalB_bin_iff, evalB_var_iff]
        exact ⟨u * n, k, ⟨u, n, ⟨huτ.symm, by omega⟩, ⟨hnτ.symm, by omega⟩, by simp, by
          have : u * n ≤ u * n + k := by omega
          omega⟩, ⟨hb.symm, by omega⟩, by simp, by omega⟩
      have hget : (Expr.get "dd" (.add (.mul (.var "bu") (.var "n")) (.var "b"))).evalB B τ = some e :=
        evalB_get hix (by rw [hddτ, getElem?_arrOf _ hidx]) heB
      set τ1 := τ.setVar "be" e with hτ1
      have r1 : Run B (.assign "be" (.get "dd" (.add (.mul (.var "bu") (.var "n")) (.var "b")))) τ τ1 7 :=
        (Run.assign hget).mono (by simp [Expr.size])
      have hbe1 : τ1.vars "be" = e := by simp [hτ1]
      have hc1 : (Cond.lt (.lit 0) (.var "be")).evalB B τ1 = some (decide (0 < e)) :=
        evalB_condLt (evalB_lit (by omega)) (by rw [← hbe1]; exact evalB_var (by rw [hbe1]; exact heB))
      have hbr1 : τ1.vars "br" = r := by simp [hτ1, hrτ]
      have hc2 : (Cond.lt (.var "br") (.sub (.var "be") (.lit 1))).evalB B τ1 =
          some (decide (r < e - 1)) := by
        refine evalB_condLt (by rw [← hbr1]; exact evalB_var (by rw [hbr1]; exact hrB)) ?_
        have := evalB_bin (op := .sub) (B := B) (σ := τ1) (e := .var "be") (f := .lit 1)
          (m := e) (n := 1) (by rw [← hbe1]; exact evalB_var (by rw [hbe1]; exact heB))
          (evalB_lit (by omega)) (by simp; omega)
        simpa using this
      have hbk : τ1.vars "b" = k := by simp [hτ1, hb]
      have hfun : ∀ (c : Prop) [Decidable c], (c ↔ (0 < e ∧ e ≤ r + 1)) →
          arrOf n (fun v => if v < k + 1 ∧ 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1 then 1 else h v) =
            arrOf n (fun v => if v = k then (if c then 1 else h k) else
              if v < k ∧ 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1 then 1 else h v) := by
        intro c _ hc
        congr 1; funext v
        by_cases hv : v = k
        · subst hv; simp only [if_true, he] at hc ⊢
          by_cases hc' : c
          · rw [if_pos hc', if_pos ⟨by omega, hc.1 hc'⟩]
          · rw [if_neg hc', if_neg (fun h' => hc' (hc.2 h'.2))]
        · have : (v < k + 1 ∧ 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1) ↔
              (v < k ∧ 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1) := by omega
          simp only [hv, if_false, this]
      have hrest : ∀ τ' : Env, τ'.vars "n" = n → τ'.vars "bu" = u → τ'.vars "br" = r →
          τ'.arrs "dd" = arrOf (n * n) g → τ'.vars "b" = k →
          (∀ x, x ∉ ["b", "be"] → τ'.vars x = σ.vars x) → (∀ x, x ≠ "bl" → τ'.arrs x = σ.arrs x) →
          τ'.out = σ.out → τ'.inp = σ.inp → (c : Prop) → [Decidable c] → (c ↔ (0 < e ∧ e ≤ r + 1)) →
          τ'.arrs "bl" = arrOf n (fun v => if v = k then (if c then 1 else h k) else
              if v < k ∧ 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1 then 1 else h v) →
          τ'.vars "b" = k ∧ I (k + 1) (τ'.setVar "b" (k + 1)) := by
        intro τ' h1 h2 h3 h4 h5 h6 h7 h8 h9 c _ hc h10
        refine ⟨h5, by simp [h1], by simp [h2], by simp [h3], by simp [h4], ?_, fun x hx => ?_,
          fun x hx => by simp [h7 x hx], by simp [h8], by simp [h9]⟩
        · simp only [arrs_setVar, h10, hfun c hc]
        · simp at hx; simp [hx.1, h6 x (by simp [hx.1, hx.2])]
      have hτ1v : ∀ x, x ∉ ["b", "be"] → τ1.vars x = σ.vars x := fun x hx => by
        simp at hx; simp [hτ1, hx.2, hvτ x (by simp [hx.1, hx.2])]
      by_cases hpos : 0 < e
      · by_cases hfar : r < e - 1
        · refine ⟨τ1, (Run.seq r1 (Run.ite_true (by rw [hc1]; simp [hpos])
            (Run.ite_true (by rw [hc2]; simp [hfar]) Run.skip))).mono (by simp [Cond.size, Expr.size]),
            hrest τ1 (by simp [hτ1, hnτ]) (by simp [hτ1, huτ]) hbr1 (by simp [hτ1, hddτ]) hbk hτ1v
              (fun x hx => by simp [hτ1, haτ x hx]) (by simp [hτ1, hoτ]) (by simp [hτ1, hiτ]) False
              ⟨False.elim, fun h' => by omega⟩ ?_⟩
          simp only [hτ1, arrs_setVar, hblτ, if_false]
          congr 1; funext v
          by_cases hv : v = k
          · subst hv; simp
          · simp [hv]
        · have hst : Run B (.store "bl" (.var "b") (.lit 1)) τ1 (τ1.setArr "bl" k 1) 3 := by
            refine (Run.store (by rw [← hbk]; exact evalB_var (by rw [hbk]; omega)) (evalB_lit (by omega))
              (by simp [hτ1, hblτ]; omega)).mono (by simp [Expr.size])
          refine ⟨τ1.setArr "bl" k 1, (Run.seq r1 (Run.ite_true (by rw [hc1]; simp [hpos])
            (Run.ite_false (by rw [hc2]; simp [hfar]) hst))).mono (by simp [Cond.size, Expr.size]),
            hrest _ (by simp [hτ1, hnτ]) (by simp [hτ1, huτ]) (by simp [hbr1]) (by simp [hτ1, hddτ])
              (by simp [hbk]) (fun x hx => by simp [hτ1v x hx])
              (fun x hx => by simp [hτ1, hx, haτ x hx]) (by simp [hτ1, hoτ])
              (by simp [hτ1, hiτ]) True ⟨fun _ => ⟨hpos, by omega⟩, fun _ => trivial⟩ ?_⟩
          simp only [arrs_setArr, if_true, hτ1, arrs_setVar, hblτ, set_arrOf]
      · refine ⟨τ1, (Run.seq r1 (Run.ite_false (by rw [hc1]; simp [hpos]) Run.skip)).mono
          (by simp [Cond.size, Expr.size]),
          hrest τ1 (by simp [hτ1, hnτ]) (by simp [hτ1, huτ]) hbr1 (by simp [hτ1, hddτ]) hbk hτ1v
            (fun x hx => by simp [hτ1, haτ x hx]) (by simp [hτ1, hoτ]) (by simp [hτ1, hiτ]) False
            ⟨False.elim, fun h' => by omega⟩ ?_⟩
        simp only [hτ1, arrs_setVar, hblτ, if_false]
        congr 1; funext v
        by_cases hv : v = k
        · subst hv; simp
        · simp [hv])
  refine ⟨σ', _, hrun.mono (by simp [rmCost, Expr.size]; omega), hbl', fun v hv => ?_, hv', ha', ho', hi'⟩
  have h2 := hh v hv
  unfold DT
  beta_reduce
  by_cases hc : 0 < g (u * n + v) ∧ g (u * n + v) ≤ r + 1
  · rw [if_pos ⟨hv, hc⟩]
    exact ⟨⟨fun _ => Or.inr hc, fun _ => rfl⟩, le_rfl⟩
  · rw [if_neg (fun h' => hc h'.2)]
    exact ⟨by rw [h2.1]; exact ⟨Or.inl, fun h => h.elim id (fun h' => absurd h' hc)⟩, h2.2⟩

/-! ### The scan -/

def chooseCmd : Com := .seq (.assign "gc" (.add (.var "gc") (.lit 1))) (.seq (.assign "bu" (.var "gv"))
  (.seq (.assign "br" (.var "gr")) rowMark))

def ciExpr : Expr := .add (.mul (.sub (.var "gi") (.lit 1)) (.var "n")) (.var "gv")

def testCmd : Com :=
  .seq (.assign "ci" ciExpr) (.seq (.assign "cj" (.var "gu")) (.seq cmpWords
    (.ite (.eq (.var "c") (.lit 1)) (.ite (.eq (.get "bl" (.var "gv")) (.lit 0)) chooseCmd .skip) .skip)))

def gbody : Com :=
  .seq (.ite (.lt (.var "gc") (.var "cap")) testCmd .skip) (.assign "gv" (.add (.var "gv") (.lit 1)))

def greedyCmd : Com := .seq (rowFill "bl" (.var "b") (.lit 0)) (.seq (.assign "gc" (.lit 0))
  (.seq (.assign "gv" (.lit 0)) (.while (.lt (.var "gv") (.var "n")) gbody)))

/-- The state of the scan before vertex `j`. -/
def GInv (A : List (List ℕ)) (n nsE nsN : ℕ) (oE tE oN tN : ℕ → ℕ) (g : ℕ → ℕ) (i r ui c : ℕ)
    (S : ℕ → List ℕ) (τ : Env) : Prop :=
  GraphAt n nsE nsN oE tE oN tN τ ∧ WordsAt A τ ∧ τ.vars "gi" = i ∧ τ.vars "gr" = r ∧
    τ.vars "gu" = ui ∧ τ.vars "cap" = c ∧ τ.vars "gv" ≤ n ∧
    τ.vars "gc" = (S (τ.vars "gv")).length ∧ τ.arrs "dd" = arrOf (n * n) g ∧
    (τ.arrs "dn").length = n ∧ ∃ h, τ.arrs "bl" = arrOf n h ∧
      IndOn n h (fun v => ∃ s ∈ S (τ.vars "gv"), DT g n s v r)

/-- The cost bound of `greedyCmd`. -/
def greedyCost (n L c : ℕ) : ℕ :=
  (36 * L + 130) * n + (rmCost n + 16 * n + 20) * c + 11 * n + 20

set_option maxHeartbeats 1000000 in
/-- **The greedy scan.** -/
theorem greedyCmd_run {B n nsE nsN i r ui c L : ℕ} {oE tE oN tN : ℕ → ℕ} {g : ℕ → ℕ}
    {A : List (List ℕ)}
    {σ : Env} (hG : GraphAt n nsE nsN oE tE oN tN σ) (hw : WordsAt A σ) (hb : WordsBound B A)
    (hnB : n + 2 < B) (hnnB : n * n < B) (hgB : ∀ j < n * n, g j < B) (hrB : r < B) (hcB : c + 1 < B)
    (hi1 : 1 ≤ i) (hiA : (i - 1) * n + n ≤ A.length) (huA : ui < A.length) (hL : ∀ u ∈ A, u.length ≤ L)
    (hgi : σ.vars "gi" = i) (hgr : σ.vars "gr" = r) (hgu : σ.vars "gu" = ui) (hcap : σ.vars "cap" = c)
    (hdd : σ.arrs "dd" = arrOf (n * n) g) (hdn : (σ.arrs "dn").length = n)
    (hbl : (σ.arrs "bl").length = n) :
    ∃ σ', Run B greedyCmd σ σ' (greedyCost n L c) ∧
      σ'.vars "gc" = (greedyN (fun v => lw A n i v = wd A ui)
        (fun s v => DT g n s v r) c n).length ∧
      GraphAt n nsE nsN oE tE oN tN σ' ∧ WordsAt A σ' := by
  set S : ℕ → List ℕ := greedyN (fun v => lw A n i v = wd A ui)
    (fun s v => DT g n s v r) c with hS
  have hlenA := hb.len
  have hAB : A.length < B := by omega
  -- clearing the blocked vertices
  obtain ⟨σ1, hr1, ⟨hG1, hw1, hgi1, hgr1, hgu1, hcap1, hdd1, hdn1⟩, hl1, hg1⟩ := rowFill_run (B := B)
    (n := n) (base := 0) (K := 3) (arr := "bl") (ie := .var "b") (e := .lit 0)
    (fun τ => GraphAt n nsE nsN oE tE oN tN τ ∧ WordsAt A τ ∧ τ.vars "gi" = i ∧ τ.vars "gr" = r ∧
      τ.vars "gu" = ui ∧ τ.vars "cap" = c ∧ τ.arrs "dd" = arrOf (n * n) g ∧ (τ.arrs "dn").length = n)
    (fun _ => 0) (by omega) (fun τ h => h.1.2.2)
    (fun τ x h => ⟨h.1.setVar (by decide) _, h.2.1.of_arrs (by simp) (by simp) (by simp),
      by simp [h.2.2.1], by simp [h.2.2.2.1], by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1],
      by simp [h.2.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.2]⟩)
    (fun τ j x h => ⟨h.1.setArr (by decide) (by decide) (by decide) (by decide) _ _,
      h.2.1.of_arrs (by simp) (by simp) (by simp), by simp [h.2.2.1], by simp [h.2.2.2.1],
      by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2.1], by simp [h.2.2.2.2.2.2.1],
      by simp [h.2.2.2.2.2.2.2]⟩)
    (fun τ k h hb hk => by simp only [evalB_var_iff]; exact ⟨by simp [hb], by omega⟩)
    (fun τ k h hb hk => by simp; omega) (by simp) ⟨hG, hw, hgi, hgr, hgu, hcap, hdd, hdn⟩ (by omega)
  have hbl1 := arrOf_of_fill (f := fun _ => 0) hbl hl1 hg1
  set σ2 := (σ1.setVar "gc" 0).setVar "gv" 0 with hσ2
  have hI2 : GInv A n nsE nsN oE tE oN tN g i r ui c S σ2 := by
    refine ⟨(hG1.setVar (by decide) _).setVar (by decide) _, hw1.of_arrs (by simp [hσ2])
      (by simp [hσ2]) (by simp [hσ2]), by simp [hσ2, hgi1], by simp [hσ2, hgr1], by simp [hσ2, hgu1],
      by simp [hσ2, hcap1], by simp [hσ2], by simp [hσ2, hS, greedyN], by simp [hσ2, hdd1],
      by simp [hσ2, hdn1], fun _ => 0, by simp [hσ2, hbl1], fun v hv => ?_⟩
    simp [hσ2, hS, greedyN]
  set Kv := 36 * L + 130 with hKv
  set Kb := rmCost n + 16 * n + 20 with hKb
  let Φ : Env → ℕ := fun τ => Kv * (n - τ.vars "gv") + Kb * (c - τ.vars "gc")
  obtain ⟨σ', K, hrun, hI', hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "gv") (.var "n")) (c := gbody)
      (GInv A n nsE nsN oE tE oN tN g i r ui c S) Φ
      (fun τ hI => evalB_condLt_vars (by have := hI.2.2.2.2.2.2.1; omega)
        (by rw [hI.1.2.2]; omega))
      (by
        rintro τ ⟨hGτ, hwτ, hgiτ, hgrτ, hguτ, hcapτ, hgvτ, hgcτ, hddτ, hdnτ, h, hblτ, hhτ⟩ hcond
        set j := τ.vars "gv" with hj
        have hjn : j < n := by have := lt_of_condLt_true hcond; rwa [hGτ.2.2] at this
        have hSc : (S j).length ≤ c := length_greedyN_le _ _ _ _
        have hSj := greedyN_succ (fun v => lw A n i v = wd A ui)
          (fun s v => DT g n s v r) c j
        rw [← hS] at hSj
        -- the result of the branch, before the increment of `gv`
        obtain ⟨τ2, K2, hr2, hI2, hc2⟩ : ∃ τ2 K2,
            Run B (.ite (.lt (.var "gc") (.var "cap")) testCmd .skip) τ τ2 K2 ∧
            (GraphAt n nsE nsN oE tE oN tN τ2 ∧ WordsAt A τ2 ∧ τ2.vars "gi" = i ∧ τ2.vars "gr" = r ∧
              τ2.vars "gu" = ui ∧ τ2.vars "cap" = c ∧ τ2.vars "gv" = j ∧
              τ2.vars "gc" = (S (j + 1)).length ∧ τ2.arrs "dd" = arrOf (n * n) g ∧
              (τ2.arrs "dn").length = n ∧ ∃ h, τ2.arrs "bl" = arrOf n h ∧
                IndOn n h (fun v => ∃ s ∈ S (j + 1), DT g n s v r)) ∧
            K2 + Kb * (c - (S (j + 1)).length) ≤ Kv - 8 + Kb * (c - (S j).length) := by
          have hgcB : τ.vars "gc" < B := by omega
          rcases Nat.lt_or_ge (S j).length c with hlt | hge
          swap
          · -- the cap is reached
            have hSe : S (j + 1) = S j := by
              rw [hSj]; unfold gstepN; rw [if_neg (by omega)]
            refine ⟨τ, _, Run.ite_false (by
                rw [evalB_condLt (evalB_var hgcB) (evalB_var (by omega))]; simp [hgcτ, hcapτ]; omega)
              Run.skip, ⟨hGτ, hwτ, hgiτ, hgrτ, hguτ, hcapτ, rfl, by rw [hgcτ, hSe], hddτ, hdnτ, h,
                hblτ, by rw [hSe]; exact hhτ⟩, ?_⟩
            rw [hSe]; simp only [size_condLt, Expr.size]; omega
          -- the comparison
          have hci : (i - 1) * n + j < A.length := by omega
          have hile : i - 1 ≤ (i - 1) * n := Nat.le_mul_of_pos_right _ (by omega)
          set τa := (τ.setVar "ci" ((i - 1) * n + j)).setVar "cj" ui with hτa
          have hra1 : Run B (.assign "ci" ciExpr) τ (τ.setVar "ci" ((i - 1) * n + j)) 8 := by
            refine (Run.assign ?_).mono (by simp [ciExpr])
            simp only [ciExpr, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
            refine ⟨(i - 1) * n, j, ⟨i - 1, n, ⟨i, 1, ⟨hgiτ.symm, by omega⟩, ⟨rfl, by omega⟩,
              by simp [Bop.apply], by omega⟩, ⟨hGτ.2.2.symm, by rw [hGτ.2.2]; omega⟩, by simp [Bop.apply], ?_⟩,
              ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
            have : (i - 1) * n ≤ (i - 1) * n + j := by omega
            omega
          have hra2 : Run B (.assign "cj" (.var "gu")) (τ.setVar "ci" ((i - 1) * n + j)) τa 2 := by
            refine (Run.assign ?_).mono (by simp)
            simp only [evalB_var_iff]; exact ⟨by simp [hguτ], by simp [hguτ]; omega⟩
          have hwa : WordsAt A τa := hwτ.of_arrs (by simp [hτa]) (by simp [hτa]) (by simp [hτa])
          obtain ⟨τb, hrb, hcb⟩ := cmpWords_run hwa hb (i := (i - 1) * n + j) (j := ui)
            (by simp [hτa]) (by simp [hτa]) hci huA
          have hlenL : A[(i - 1) * n + j].length ≤ L := hL _ (List.getElem_mem _)
          have hfb : ∀ x, x ∉ cmpWords.wvars → τb.vars x = τa.vars x := fun x hx => hrb.frame_var x hx
          have hab : ∀ x, x ∉ cmpWords.warrs → τb.arrs x = τa.arrs x := fun x hx => hrb.frame_arr x hx
          have hwb : WordsAt A τb := hwa.of_arrs (hab "a" (by decide)) (hab "st" (by decide))
            (hab "ln" (by decide))
          have hGb : GraphAt n nsE nsN oE tE oN tN τb := by
            refine GraphAt.of_arrs (τ := τa) ((hGτ.setVar (by decide) _).setVar (by decide) _)
              (hfb "n" (by decide)) (hab _ (by decide)) (hab _ (by decide)) (hab _ (by decide))
              (hab _ (by decide))
          have hgvb : τb.vars "gv" = j := by
            rw [hfb "gv" (by decide)]
            simp only [hτa, vars_setVar, show ("gv" : String) = "cj" ↔ False by decide,
              show ("gv" : String) = "ci" ↔ False by decide, if_false]
            exact hj.symm
          have hgcb : τb.vars "gc" = (S j).length := by
            rw [hfb "gc" (by decide)]
            simp only [hτa, vars_setVar, show ("gc" : String) = "cj" ↔ False by decide,
              show ("gc" : String) = "ci" ↔ False by decide, if_false]
            exact hgcτ
          have hblb : τb.arrs "bl" = arrOf n h := by rw [hab "bl" (by decide)]; simp [hτa, hblτ]
          have hddb : τb.arrs "dd" = arrOf (n * n) g := by rw [hab "dd" (by decide)]; simp [hτa, hddτ]
          have hdnb : (τb.arrs "dn").length = n := by rw [hab "dn" (by decide)]; simp [hτa, hdnτ]
          have hvb : ∀ x ∈ ["gi", "gr", "gu", "cap"], τb.vars x = τ.vars x := by
            intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> (rw [hfb _ (by decide)]; simp [hτa])
          have hcb' : τb.vars "c" < B := by
            rw [hcb]; have := cmpCode_le_two A[(i - 1) * n + j] A[ui]; have := hb.three; omega
          have hwd : wd A ((i - 1) * n + j) = lw A n i j := rfl
          have hcode : cmpCode A[(i - 1) * n + j] A[ui] = 1 ↔ lw A n i j = wd A ui := by
            rw [cmpCode_eq_one, ← hwd, wd_eq hci, wd_eq huA]
          have hcmpB : (36 * A[(i - 1) * n + j].length + 56) ≤ 36 * L + 56 := by omega
          have hcondc := eq_true_iff' (B := B) (σ := τb) (x := "c") (n := 1) hcb' (by omega)
          have hbase : Run B (.ite (.lt (.var "gc") (.var "cap")) testCmd .skip) τ τb
              (1 + 3 + (10 + (36 * L + 56) + 0)) → True := fun _ => trivial
          clear hbase
          by_cases heq : lw A n i j = wd A ui
          swap
          · -- not the tree word
            have hSe : S (j + 1) = S j := by
              rw [hSj]; unfold gstepN; rw [if_neg (fun h' => heq h'.2.1)]
            refine ⟨τb, _, Run.ite_true (by
                rw [evalB_condLt (evalB_var hgcB) (evalB_var (by omega))]; simp [hgcτ, hcapτ]; omega)
              (by
                unfold testCmd
                refine (Run.seq hra1 (Run.seq hra2 (Run.seq hrb (Run.ite_false (by
                  rw [hcondc]; simp [hcb, hcode, heq]) Run.skip))))),
              ⟨hGb, hwb, by rw [hvb "gi" (by simp), hgiτ], by rw [hvb "gr" (by simp), hgrτ],
                by rw [hvb "gu" (by simp), hguτ], by rw [hvb "cap" (by simp), hcapτ], hgvb,
                by rw [hgcb, hSe], hddb, hdnb, h, hblb, by rw [hSe]; exact hhτ⟩, ?_⟩
            rw [hSe]; simp only [size_condLt, size_condEq, Expr.size]; omega
          -- the tree word: is the vertex blocked?
          have hhj := hhτ j hjn
          have hblc : (Cond.eq (.get "bl" (.var "gv")) (.lit 0)).evalB B τb = some (h j == 0) := by
            rw [evalB_condEq_iff]
            refine ⟨h j, 0, ?_, by simp; omega, rfl⟩
            simp only [evalB_get_iff, evalB_var_iff]
            exact ⟨j, ⟨hgvb.symm, by omega⟩, by rw [hblb, getElem?_arrOf _ hjn], by have := hhj.2; omega⟩
          by_cases hfree : h j = 0
          swap
          · -- blocked
            have hblk : ∃ s ∈ S j, DT g n s j r := hhj.1.mp (by have := hhj.2; omega)
            have hSe : S (j + 1) = S j := by
              rw [hSj]; unfold gstepN
              rw [if_neg (fun h' => by obtain ⟨s, hs, hs'⟩ := hblk; exact h'.2.2 s hs hs')]
            refine ⟨τb, _, Run.ite_true (by
                rw [evalB_condLt (evalB_var hgcB) (evalB_var (by omega))]; simp [hgcτ, hcapτ]; omega)
              (by
                unfold testCmd
                refine (Run.seq hra1 (Run.seq hra2 (Run.seq hrb (Run.ite_true (by
                  rw [hcondc]; simp [hcb, hcode, heq]) (Run.ite_false (by rw [hblc]; simp [hfree])
                    Run.skip)))))),
              ⟨hGb, hwb, by rw [hvb "gi" (by simp), hgiτ], by rw [hvb "gr" (by simp), hgrτ],
                by rw [hvb "gu" (by simp), hguτ], by rw [hvb "cap" (by simp), hcapτ], hgvb,
                by rw [hgcb, hSe], hddb, hdnb, h, hblb, by rw [hSe]; exact hhτ⟩, ?_⟩
            rw [hSe]; simp only [size_condLt, size_condEq, Expr.size]; omega
          -- free: choose it
          have hnot : ¬ ∃ s ∈ S j, DT g n s j r := fun h' =>
            by have := hhj.1.mpr h'; omega
          have hSe : S (j + 1) = S j ++ [j] := by
            rw [hSj]; unfold gstepN
            rw [if_pos ⟨hlt, heq, fun s hs hs' => hnot ⟨s, hs, hs'⟩⟩]
          set τc := ((τb.setVar "gc" ((S j).length + 1)).setVar "bu" j).setVar "br" r with hτc
          have hrc1 : Run B (.assign "gc" (.add (.var "gc") (.lit 1))) τb
              (τb.setVar "gc" ((S j).length + 1)) 4 := by
            refine (Run.assign ?_).mono (by simp)
            simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
            exact ⟨(S j).length, 1, ⟨hgcb.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply],
              by omega⟩
          have hrc2 : Run B (.assign "bu" (.var "gv")) (τb.setVar "gc" ((S j).length + 1))
              ((τb.setVar "gc" ((S j).length + 1)).setVar "bu" j) 2 := by
            refine (Run.assign ?_).mono (by simp)
            simp only [evalB_var_iff]; exact ⟨by simp [hgvb], by simp [hgvb]; omega⟩
          have hrc3 : Run B (.assign "br" (.var "gr")) ((τb.setVar "gc" ((S j).length + 1)).setVar "bu" j)
              τc 2 := by
            refine (Run.assign ?_).mono (by simp)
            simp only [evalB_var_iff]
            exact ⟨by simp [hvb "gr" (by simp), hgrτ], by simp [hvb "gr" (by simp), hgrτ]; omega⟩
          have hGc : GraphAt n nsE nsN oE tE oN tN τc :=
            ((hGb.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
          obtain ⟨τe, h', hre, hble, hhe, hfe, hae, -, -⟩ := rowMark_run (B := B) (n := n) (u := j) (r := r)
            (σ := τc) hGc.2.2 (by simp [hτc])
            (by simp [hτc, hvb "gr" (by simp), hgrτ]) hjn hnnB hrB (by simp [hτc, hddb]) hgB
            (by simp [hτc, hblb]) hhτ
          have hvc : ∀ x, x ∉ ["b", "be"] → τe.vars x = τc.vars x := hfe
          have hac : ∀ x, x ≠ "bl" → τe.arrs x = τc.arrs x := hae
          refine ⟨τe, _, Run.ite_true (by
                rw [evalB_condLt (evalB_var hgcB) (evalB_var (by omega))]; simp [hgcτ, hcapτ]; omega)
              (by
                unfold testCmd
                refine (Run.seq hra1 (Run.seq hra2 (Run.seq hrb (Run.ite_true (by
                  rw [hcondc]; simp [hcb, hcode, heq]) (Run.ite_true (by rw [hblc]; simp [hfree])
                    (by unfold chooseCmd; exact Run.seq hrc1 (Run.seq hrc2 (Run.seq hrc3 hre))))))))),
              ⟨GraphAt.of_arrs hGc (hvc "n" (by decide)) (hac _ (by decide)) (hac _ (by decide))
                (hac _ (by decide)) (hac _ (by decide)),
               hwb.of_arrs (by rw [hac "a" (by decide)]; simp [hτc])
                (by rw [hac "st" (by decide)]; simp [hτc])
                (by rw [hac "ln" (by decide)]; simp [hτc]),
               by rw [hvc "gi" (by decide)]; simp [hτc, hvb "gi" (by simp), hgiτ],
               by rw [hvc "gr" (by decide)]; simp [hτc, hvb "gr" (by simp), hgrτ],
               by rw [hvc "gu" (by decide)]; simp [hτc, hvb "gu" (by simp), hguτ],
               by rw [hvc "cap" (by decide)]; simp [hτc, hvb "cap" (by simp), hcapτ],
               by rw [hvc "gv" (by decide)]; simp [hτc, hgvb],
               by rw [hvc "gc" (by decide)]; simp [hτc, hSe],
               by rw [hac "dd" (by decide)]; simp [hτc, hddb],
               by rw [hac "dn" (by decide)]; simp [hτc, hdnb],
               h', hble, fun v hv => ⟨?_, (hhe v hv).2⟩⟩, ?_⟩
          · rw [(hhe v hv).1, hSe]
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro (⟨s, hs, h1⟩ | h1)
              · exact ⟨s, Or.inl hs, h1⟩
              · exact ⟨j, Or.inr rfl, h1⟩
            · rintro ⟨s, hs | rfl, h1⟩
              · exact Or.inl ⟨s, hs, h1⟩
              · exact Or.inr h1
          · rw [hSe, List.length_append, List.length_singleton]
            have e1 : Kb * (c - (S j).length) = Kb * (c - ((S j).length + 1)) + Kb := by
              rw [show c - (S j).length = (c - ((S j).length + 1)) + 1 by omega]; ring
            simp only [size_condLt, size_condEq, Expr.size]
            rw [e1]
            have : 36 * A[(i - 1) * n + j].length ≤ 36 * L := by omega
            have hKb' : Kb = rmCost n + 16 * n + 20 := hKb
            have hKv' : Kv = 36 * L + 130 := hKv
            omega
        obtain ⟨hG2, hw2, hgi2, hgr2, hgu2, hcap2, hgv2, hgc2, hdm2, hdn2, h2, hbl2, hh2⟩ := hI2
        refine ⟨τ2.setVar "gv" (j + 1), _, Run.seq hr2 (Run.assign (v := j + 1) ?_),
          ⟨hG2.setVar (by decide) _, hw2.of_arrs (by simp) (by simp) (by simp), by simp [hgi2],
            by simp [hgr2], by simp [hgu2], by simp [hcap2], by simp; omega, by simp [hgc2],
            by simp [hdm2], by simp [hdn2], h2, by simp [hbl2], by simpa using hh2⟩, ?_⟩
        · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
          exact ⟨j, 1, ⟨hgv2.symm, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
        · simp only [Φ, vars_setVar, if_true, show ("gc" : String) = "gv" ↔ False by decide, if_false,
            Expr.size, size_condLt]
          rw [hgc2, hgcτ]
          have e2 : Kv * (n - j) = Kv * (n - (j + 1)) + Kv := by
            rw [show n - j = (n - (j + 1)) + 1 by omega]; ring
          rw [e2]
          have hKv' : Kv = 36 * L + 130 := hKv
          omega)
      hI2
  obtain ⟨hG', hw', -, -, -, -, hgv', hgc', -⟩ := hI'
  have hgvn : σ'.vars "gv" = n := by
    have := le_of_condLt_false hfalse; rw [hG'.2.2] at this; omega
  refine ⟨σ', (Run.seq hr1 (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq
    (Run.assign (v := 0) (by simp; omega)) hrun))).mono ?_, by rw [hgc', hgvn], hG', hw'⟩
  simp only [Φ, hσ2, vars_setVar, if_true, Nat.sub_zero, size_condLt, Expr.size,
    show ("gc" : String) = "gv" ↔ False by decide, if_false] at hK ⊢
  simp only [greedyCost, ← hKv, ← hKb]
  omega

end Lax185574Proofs.StpRam
