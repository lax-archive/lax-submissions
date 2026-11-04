import Lax185574Proofs.MC.Glue.Out

/-!
The schedule of the glue program of thm:mc: the head `hd j` that round
`j` writes, as a function of the call `j`.

Round `j` issues call `j` and writes its fields into the state (`ckOf`
the kind, `ctOf` the step, `cvOf` the vertex, `cPOf`, `cQOf` the colors
and `csOf` the sign), with the words of the partial graph (`gwOf`), of
the family of trees (`fwOf`) and of the localized sentence. The word of
the partial graph is followed by the word of its matrix of distances.
The tag is `2` when the next round must read the next step from its
window, that is when call `j` is a call of a step and a step follows, and
`1` otherwise.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionModelChecking

variable {n : ℕ}

/-- The kind of a call: `0` merge, `1` resolve, `2` evaluation, `3` the
merge `merge_{P,P}` with the fixed query. -/
def ckOf : PCall n → ℕ
  | .merge _ P Q => if P = Q then 3 else 0
  | .resolve .. => 1
  | .eval _ => 2

/-- The step of a call, `m` for the evaluation. -/
def ctOf (m : ℕ) : PCall n → ℕ
  | .merge t .. => t
  | .resolve t .. => t
  | .eval _ => m

/-- The vertex scalar of a call, always `0`: the evaluation works on
vertex `0`. -/
def cvOf (_ : PCall n) : ℕ := 0

/-- The colors of a call. -/
def cPOf : PCall n → ℕ
  | .merge _ P _ => P
  | .resolve _ _ P _ => P
  | .eval _ => 0

def cQOf : PCall n → ℕ
  | .merge _ _ Q => Q
  | .resolve _ _ _ Q => Q
  | .eval _ => 0

/-- The sign of a resolve call. -/
def csOf : PCall n → ℕ
  | .resolve _ sg _ _ => if sg then 1 else 0
  | _ => 0

/-- The call is the call of a step. -/
def lastOf : PCall n → Prop
  | .merge .. => True
  | .resolve .. => True
  | .eval _ => False

instance (c : PCall n) : Decidable (lastOf c) := by
  cases c <;> simp only [lastOf] <;> infer_instance

/-- The tag of the head of a call. -/
def tagOf (m : ℕ) (c : PCall n) : ℕ := if lastOf c ∧ ctOf m c + 1 < m then 2 else 1

/-- The window length that the tag asks for. -/
def kOf (m : ℕ) (c : PCall n) : ℕ := if tagOf m c = 2 then 3 else 0

/-- The window start: the next step. -/
def s0Of (off m : ℕ) (c : PCall n) : ℕ := if tagOf m c = 2 then off + 3 * (ctOf m c + 1) else 0

open Lax185574.DistanceMatrix in
/-- The word of the partial graph of a call, with its matrix of distances. -/
noncomputable def gwOf (s : List (PartialGraph (Fin n))) (m : ℕ) (c : PCall n) : List ℕ :=
  toWord (sAt s (ctOf m c)) ++ toWord (distMatrix (sAt s (ctOf m c)))

/-- The word of the family of trees of a call. -/
noncomputable def fwOf (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) : List ℕ :=
  toWord (family (sAt s (ctOf m c)) 1 q)

/-- The scalars of the state of a call. -/
def scOf (off m q : ℕ) (c : PCall n) : List ℕ :=
  [s0Of off m c, n, m, off, q, ckOf c, ctOf m c, cvOf c, cPOf c, cQOf c, csOf c]

/-- The head written by the round of a call. -/
noncomputable def hdOf (s : List (PartialGraph (Fin n))) (q off m : ℕ) (lw : List ℕ)
    (c : PCall n) : List ℕ :=
  hdW (tagOf m c) (kOf m c) (stW (scOf off m q c) (gwOf s m c) (fwOf s q m c) lw)

/-- The heads along the calls `cs`. -/
noncomputable def hdSeq (s : List (PartialGraph (Fin n))) (q off m : ℕ) (lw : List ℕ)
    (cs : List (PCall n)) (j : ℕ) : List ℕ :=
  match cs[j]? with
  | some c => hdOf s q off m lw c
  | none => [1, 0, 0]

theorem tagOf_pos (m : ℕ) (c : PCall n) : tagOf m c ≠ 0 := by
  unfold tagOf; split_ifs <;> omega

theorem hdOf_shape (s : List (PartialGraph (Fin n))) (q off m : ℕ) (lw : List ℕ) (c : PCall n) :
    hdOf s q off m lw c ≠ [] ∧ (hdOf s q off m lw c).head? ≠ some 0 ∧
      (hdOf s q off m lw c).getD 1 0 + 3 = (hdOf s q off m lw c).length := by
  refine ⟨by simp [hdOf, hdW], by simp [hdOf, hdW, tagOf_pos], by simp [hdOf, hdW]⟩

theorem hdSeq_shape (s : List (PartialGraph (Fin n))) (q off m : ℕ) (lw : List ℕ)
    (cs : List (PCall n)) (j : ℕ) (hj : j < cs.length) :
    hdSeq s q off m lw cs j ≠ [] ∧ (hdSeq s q off m lw cs j).head? ≠ some 0 ∧
      (hdSeq s q off m lw cs j).getD 1 0 + 3 = (hdSeq s q off m lw cs j).length := by
  unfold hdSeq
  rw [List.getElem?_eq_getElem hj]
  exact hdOf_shape _ _ _ _ _ _

/-! ### The query of a call -/

/-- The word of the jobs of a merge step. -/
theorem toWord_mjobs (G : PartialGraph (Fin n)) (q P Q : ℕ) :
    toWord (mjobs G q P Q) = jbW (List.ofFn fun v : Fin n => tree G 1 q ![v]) P Q := by
  rw [toWord_words]
  simp only [mjobs, jbW, jbF, frames, List.length_ofFn, List.map_ofFn]
  congr 2
  congr 1
  funext v
  have e : toWord (tree G 1 q ![v], P, Q) = toWord (tree G 1 q ![v]) ++ [P, Q] := rfl
  simp only [Function.comp_apply, e, List.length_append, List.length_cons, List.length_nil]

/-- The word of a family of trees is a count and the words of the trees. -/
theorem toWord_family (G : PartialGraph (Fin n)) (q : ℕ) :
    toWord (family G 1 q) = n :: ((List.ofFn fun a : Fin n => tree G 1 q ![a]).map toWord).flatten := by
  show (List.ofFn _).length :: ((List.ofFn (family G 1 q)).map toWord).flatten = _
  rw [List.length_ofFn]; rfl

/-- The query written for a call is the query of the call, once the
word `tr` is the word of the jobs for a merge and the word of the tree
for the evaluation. -/
theorem qW_callQ (s : List (PartialGraph (Fin n))) (q m : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (c : PCall n) (tr : List ℕ)
    (htr : ∀ t P Q, c = .merge t P Q → P ≠ Q → tr = toWord (mjobs (sAt s t) q P Q))
    (hev : ∀ a, c = .eval a → tr = toWord (tree (sAt s (s.length - 1)) 1 q ![a])) :
    qW (ckOf c) (cPOf c) (cQOf c) (csOf c) (gwOf s m c) (fwOf s q m c) tr
      (Lax185574.DistanceLogic.DistFO.code (loc q φ)) = callQ s q φ c := by
  cases c with
  | merge t P Q =>
    by_cases hPQ : P = Q
    · simp [qW, ckOf, hPQ, callQ, callQM, callQR, callQE]
    · rw [htr t P Q rfl hPQ]
      simp [qW, realQ, ckOf, hPQ, callQ, callQM, callQR, callQE]
  | resolve t sg P Q =>
    simp [qW, realQ, ckOf, callQ, callQM, callQR, callQE, cPOf, cQOf, csOf, gwOf, fwOf, ctOf,
      List.append_assoc]
    simp only [Lax185574Proofs.Legacy.toWord_prod, Lax185574Proofs.Legacy.toWord_nat,
      Lax185574Proofs.Legacy.toWord_bool]
    rfl
  | eval a =>
    rw [hev a rfl]
    simp [qW, realQ, ckOf, callQ, callQM, callQR, callQE]
    simp only [Lax185574Proofs.Legacy.toWord_prod, Lax185574Proofs.Legacy.toWord_distFO]

/-- The word that the query of a call uses: the jobs of a merge step, or
the tree of the evaluation. -/
noncomputable def trOf (s : List (PartialGraph (Fin n))) (q : ℕ) : PCall n → List ℕ
  | .merge t P Q => jbW (List.ofFn fun v : Fin n => tree (sAt s t) 1 q ![v]) P Q
  | .resolve .. => []
  | .eval a => toWord (tree (sAt s (s.length - 1)) 1 q ![a])

theorem qW_trOf (s : List (PartialGraph (Fin n))) (q m : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (c : PCall n) :
    qW (ckOf c) (cPOf c) (cQOf c) (csOf c) (gwOf s m c) (fwOf s q m c) (trOf s q c)
      (Lax185574.DistanceLogic.DistFO.code (loc q φ)) = callQ s q φ c :=
  qW_callQ s q m φ c _ (fun t P Q h _ => by subst h; simp [trOf, toWord_mjobs])
    (fun a h => by subst h; rfl)

theorem fwOf_eq (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) :
    fwOf s q m c = (List.ofFn fun v : Fin n => tree (sAt s (ctOf m c)) 1 q ![v]).length ::
      ((List.ofFn fun v : Fin n => tree (sAt s (ctOf m c)) 1 q ![v]).map toWord).flatten := by
  rw [fwOf, toWord_family, List.length_ofFn]

theorem gn_of_fwOf {s : List (PartialGraph (Fin n))} {q m : ℕ} {c : PCall n} {ts : List TypeTree}
    (h : fwOf s q m c = ts.length :: (ts.map toWord).flatten) : ts.length = n := by
  have := congrArg List.head? h
  rw [fwOf, toWord_family] at this
  simpa using this.symm

theorem trOK_of (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) (a N : ℕ)
    (hev : ckOf c = 2 → a + N ≤ (fwOf s q m c).length ∧ trOf s q c = seg (fwOf s q m c) a N) :
    TrOK (ckOf c) (cPOf c) (cQOf c) a N (fwOf s q m c) (trOf s q c) := by
  refine ⟨fun h0 => ?_, hev⟩
  cases c with
  | merge t P Q => exact ⟨_, fwOf_eq s q m _, rfl⟩
  | resolve => simp [ckOf] at h0
  | eval => simp [ckOf] at h0

theorem trOf_bounds (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) {a N W : ℕ}
    (hev : ckOf c = 2 → a + N ≤ (fwOf s q m c).length ∧ trOf s q c = seg (fwOf s q m c) a N)
    (hv : ∀ v ∈ fwOf s q m c, v ≤ W) (hP : cPOf c ≤ W) (hQ : cQOf c ≤ W)
    (hl : (fwOf s q m c).length + 2 ≤ W) :
    (trOf s q c).length ≤ 4 * (fwOf s q m c).length ∧ ∀ v ∈ trOf s q c, v ≤ W := by
  cases c with
  | merge t P Q =>
    have hfw : fwOf s q m (.merge t P Q) = (List.ofFn fun v : Fin n => tree (sAt s t) 1 q ![v]).length ::
        ((List.ofFn fun v : Fin n => tree (sAt s t) 1 q ![v]).map toWord).flatten := fwOf_eq s q m _
    obtain ⟨h1, h2⟩ := length_jbW P Q hfw
    exact ⟨by simp only [trOf]; omega, mem_jbW hfw hv hP hQ hl⟩
  | resolve => simp [trOf]
  | eval b =>
    obtain ⟨-, he⟩ := hev rfl
    rw [he]
    exact ⟨by simp [seg]; omega, fun v hv' => hv v (mem_seg hv')⟩

/-! ### The first call -/

/-- The first call of a step. -/
def firstCall (hn : 0 < n) : Step → PCall n
  | .merge P Q => .merge 0 P Q
  | .resolvePos P Q => .resolve 0 true P Q
  | .resolveNeg P Q => .resolve 0 false P Q

theorem pcalls_zero_nil (hn : 0 < n) : (pcalls n [])[0]? = some (.eval ⟨0, hn⟩) := by
  simp [pcalls, callsFrom, hn]

theorem pcalls_zero_cons (hn : 0 < n) (st : Step) (r : List Step) :
    (pcalls n (st :: r))[0]? = some (firstCall hn st) := by
  cases st <;> simp [pcalls, callsFrom, stepCalls, firstCall]

theorem iL_block_length (q c : ℕ) : ([1, q, 1] ++ initWord 1 q 1 c).length = iL q + 3 := by
  simp [length_initWord]

theorem seg_fw0 {q : ℕ} {c : ℕ → ℕ} (hn : 0 < n) :
    seg (fw0 n q c) 1 (iL q + 3) = [1, q, 1] ++ initWord 1 q 1 (c 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [fw0, List.range_succ_eq_map, List.flatMap_cons]
  simp only [seg, List.drop_succ_cons, List.drop_zero]
  rw [List.take_append_of_le_length (by rw [iL_block_length]), List.take_of_length_le
    (by rw [iL_block_length])]

theorem tl_fw0 (q : ℕ) (c : ℕ → ℕ) (hn : 0 < n) : ((fw0 n q c).length - 1) / n = iL q + 3 := by
  rw [length_fw0, show 1 + n * (iL q + 3) - 1 = n * (iL q + 3) by omega,
    Nat.mul_div_cancel_left _ hn]

theorem length_run {n : ℕ} (σ : Script n) : σ.run.length = σ.steps.length + 1 := by
  simp [Script.run]

/-! ### Setting the tag -/

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- `z := 1` if the condition holds. -/
def setIf (b : Cond) (z : String) : Com := .ite b (.assign z (.lit 1)) .skip

theorem setIf_run {B : ℕ} {b : Cond} {z : String} {τ : Env} {p : Bool} (hb : b.evalB B τ = some p)
    (hB : 1 < B) : ∃ τ', Run B (setIf b z) τ τ' (3 + b.size) ∧
      τ'.vars z = (if p then 1 else τ.vars z) ∧ OFr τ τ' [z] := by
  cases p
  · exact ⟨τ, (Run.ite_false hb Run.skip).mono (by omega), by simp, (OFr.refl τ).mono (by simp)⟩
  · exact ⟨τ.setVar z 1, (Run.ite_true hb (Run.assign (evalB_lit hB))).mono (by simp [Expr.size]; omega),
      by simp, OFr.setVar τ z 1⟩

/-- `lst` is `1` exactly when the call is the call of a step. -/
def lastChk : Com :=
  .ite (.eq (.var "ck") (.lit 2)) (.assign "lst" (.lit 0)) (.assign "lst" (.lit 1))

def tag2 : Com :=
  .seq (.assign "otg" (.lit 2)) (.seq (.assign "okk" (.lit 3))
    (.assign "s0" (.add (.var "off") (.mul (.lit 3) (.add (.var "ct") (.lit 1))))))

def tag1 : Com :=
  .seq (.assign "otg" (.lit 1)) (.seq (.assign "okk" (.lit 0)) (.assign "s0" (.lit 0)))

/-- Tag, window length and window start of the head. -/
def tagSet : Com :=
  .seq lastChk (.ite (.eq (.var "lst") (.lit 1))
    (.ite (.lt (.add (.var "ct") (.lit 1)) (.var "sm")) tag2 tag1) tag1)

theorem lastChk_run {W ck : ℕ} {τ : Env} (hck : τ.vars "ck" = ck) (hW : 4 ≤ W) (hckW : ck ≤ W) :
    ∃ τ', Run (W + 1) lastChk τ τ' 40 ∧ τ'.vars "lst" = (if ck = 2 then 0 else 1) ∧
      OFr τ τ' ["lst"] := by
  have hc := condEq_lit (B := W + 1) (d := 2) hck (by omega) (by omega)
  by_cases h2 : ck = 2
  · refine ⟨τ.setVar "lst" 0, ?_, by simp [h2], OFr.setVar τ "lst" 0⟩
    unfold lastChk
    exact (Run.ite_true (by rw [hc, decide_eq_true h2]) (Run.assign (evalB_lit (by omega)))).mono
      (by simp [Cond.size, Expr.size])
  · refine ⟨τ.setVar "lst" 1, ?_, by simp [h2], OFr.setVar τ "lst" 1⟩
    unfold lastChk
    exact (Run.ite_false (by rw [hc, decide_eq_false h2]) (Run.assign (evalB_lit (by omega)))).mono
      (by simp [Cond.size, Expr.size])

theorem last_iff (c : PCall n) : ckOf c ≠ 2 ↔ lastOf c := by
  cases c with
  | merge t P Q => by_cases h : P = Q <;> simp [ckOf, lastOf, h]
  | resolve t sg P Q => simp [ckOf, lastOf]
  | eval a => simp [ckOf, lastOf]

theorem tagSet_run {W m o : ℕ} {τ : Env} (c : PCall n) (hck : τ.vars "ck" = ckOf c)
    (hct : τ.vars "ct" = ctOf m c)
    (hsm : τ.vars "sm" = m) (hoff : τ.vars "off" = o) (hW : 4 ≤ W) (hckW : ckOf c ≤ W)
    (hmW : m ≤ W) (hb : o + 3 * (ctOf m c + 1) ≤ W) :
    ∃ τ', Run (W + 1) tagSet τ τ' 70 ∧ τ'.vars "otg" = tagOf m c ∧ τ'.vars "okk" = kOf m c ∧
      τ'.vars "s0" = s0Of o m c ∧ OFr τ τ' ["lst", "otg", "okk", "s0"] := by
  obtain ⟨τ₁, r₁, h₁, f₁⟩ := lastChk_run hck hW hckW
  have h₁' : τ₁.vars "lst" = if lastOf c then 1 else 0 := by
    rw [h₁]; by_cases hl : lastOf c
    · rw [if_pos hl, if_neg ((last_iff c).2 hl)]
    · rw [if_neg hl, if_pos (by by_contra h; exact hl ((last_iff c).1 h))]
  have v₁ : ∀ y ∈ ["ct", "sm", "off"], τ₁.vars y = τ.vars y := fun y hy => f₁.vars y (by
    simp at hy; rcases hy with rfl | rfl | rfl <;> decide)
  have hct₁ : τ₁.vars "ct" = ctOf m c := by rw [v₁ _ (by simp), hct]
  have hc1 := condEq_lit (B := W + 1) (τ := τ₁) (x := "lst") (d := 1) h₁' (by split_ifs <;> omega)
    (by omega)
  have hlt := evalB_condLt (B := W + 1) (σ := τ₁) (e := .add (.var "ct") (.lit 1)) (f := .var "sm")
    (ev_add (ev_var hct₁ (by omega)) (evalB_lit (by omega)) (by omega))
    (ev_var (by rw [v₁ _ (by simp), hsm]) (by omega))
  have t1 : ∃ τ', Run (W + 1) tag1 τ₁ τ' 10 ∧ τ'.vars "otg" = 1 ∧ τ'.vars "okk" = 0 ∧
      τ'.vars "s0" = 0 ∧ OFr τ₁ τ' ["otg", "okk", "s0"] :=
    ⟨_, (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.assign (evalB_lit (by omega))))).mono (by simp [Expr.size]), by simp, by simp, by simp,
      (((OFr.setVar _ _ _).trans (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).mono (by simp)⟩
  have t2 : ∃ τ', Run (W + 1) tag2 τ₁ τ' 20 ∧ τ'.vars "otg" = 2 ∧ τ'.vars "okk" = 3 ∧
      τ'.vars "s0" = o + 3 * (ctOf m c + 1) ∧ OFr τ₁ τ' ["otg", "okk", "s0"] := by
    refine ⟨_, (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.assign (ev_add (ev_var (v := o) (by simp [v₁ _ (by simp : "off" ∈ _), hoff]) (by omega))
        (evalB_bin (evalB_lit (by omega)) (ev_add (ev_var (v := ctOf m c) (by simp [hct₁]) (by omega))
          (evalB_lit (by omega)) (by omega)) (by show 3 * (ctOf m c + 1) < W + 1; omega)) (by show o + 3 * (ctOf m c + 1) < W + 1; omega))))).mono
      (by simp [Expr.size]), by simp, by simp, by simp,
      (((OFr.setVar _ _ _).trans (OFr.setVar _ _ _)).trans (OFr.setVar _ _ _)).mono (by simp)⟩
  obtain ⟨τ₂, r₂, g₂, k₂, s₂, f₂⟩ := t1
  obtain ⟨τ₃, r₃, g₃, k₃, s₃, f₃⟩ := t2
  by_cases hl : lastOf c
  · by_cases hm : ctOf m c + 1 < m
    · have ht : tagOf m c = 2 := by simp [tagOf, hl, hm]
      refine ⟨τ₃, ?_, by rw [g₃, ht], by rw [k₃, kOf, ht]; rfl, by rw [s₃, s0Of, ht]; rfl,
        (f₁.trans f₃).mono (by simp)⟩
      unfold tagSet
      refine (Run.seq r₁ (Run.ite_true (by rw [hc1, if_pos hl]; rfl) (Run.ite_true
        (by rw [hlt, decide_eq_true hm]) r₃))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    · have ht : tagOf m c = 1 := by simp [tagOf, hl, hm]
      refine ⟨τ₂, ?_, by rw [g₂, ht], by rw [k₂, kOf, ht]; rfl, by rw [s₂, s0Of, ht]; rfl,
        (f₁.trans f₂).mono (by simp)⟩
      unfold tagSet
      refine (Run.seq r₁ (Run.ite_true (by rw [hc1, if_pos hl]; rfl) (Run.ite_false
        (by rw [hlt, decide_eq_false hm]) r₂))).mono ?_
      simp only [Cond.size, Expr.size]; omega
  · have ht : tagOf m c = 1 := by simp [tagOf, hl]
    refine ⟨τ₂, ?_, by rw [g₂, ht], by rw [k₂, kOf, ht]; rfl, by rw [s₂, s0Of, ht]; rfl,
      (f₁.trans f₂).mono (by simp)⟩
    unfold tagSet
    refine (Run.seq r₁ (Run.ite_false (by rw [hc1, if_neg hl]; rfl) r₂)).mono ?_
    simp only [Cond.size, Expr.size]; omega

end Lax185574Proofs.MC.Glue
