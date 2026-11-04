import Lax185574Proofs.MC.Brute.Machine
import Lax808846Proofs.Tactic

/-!
One step of the evaluation machine in IMP+.

The configuration lives in scalars and arrays: `bfm` the mode, `bfp` the
position, `bfb` the value, `bfs` the height of the stack and `bfd` the
number of bound variables. The stack is in the arrays `bfk` (kind),
`bfa` (position) and `bfw` (value), bottom first, and the assignment in
`bfg`, which is zero beyond the bound variables. The code is in `bfc`,
the ends of the left conjuncts in `bfe` and the adjacency matrix in
`bfA`, row by row. `bfStep` performs one step of `step`, and
`bfStep_sim` shows that it does so on every small configuration.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The kind of a frame. -/
def frKind : Fr → ℕ
  | .neg => 1
  | .andL _ => 2
  | .andR => 3
  | .ex _ _ => 4

/-- The position of a frame. -/
def frArg : Fr → ℕ
  | .andL r => r
  | .ex pc _ => pc
  | _ => 0

/-- The value of a frame. -/
def frVal : Fr → ℕ
  | .ex _ v => v
  | _ => 0

/-- The array `arr` holds `g` of the frames of `s`, bottom first. -/
def StkAt (arr : List ℕ) (g : Fr → ℕ) (s : List Fr) : Prop :=
  ∀ i (h : i < s.length), arr.getD i 0 = g (s.reverse[i]'(by simpa using h))

/-- The array `arr` holds the assignment `a`, and zeros beyond it. -/
def AsgAt (arr : List ℕ) (a : List ℕ) : Prop := ∀ i, arr.getD i 0 = a.getD i 0

theorem StkAt.push {arr : List ℕ} {g : Fr → ℕ} {s : List Fr} (h : StkAt arr g s) (f : Fr)
    (hl : s.length < arr.length) : StkAt (arr.set s.length (g f)) g (f :: s) := by
  intro i hi
  simp only [List.length_cons] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases he : s.length = i
  · subst he
    simp [hl]
  · rw [if_neg he, ← List.getD_eq_getElem?_getD, h i (by omega)]
    simp only [List.reverse_cons]
    rw [List.getElem_append_left]

theorem StkAt.push' {arr : List ℕ} {g : Fr → ℕ} {s : List Fr} {i v : ℕ} (h : StkAt arr g s) (f : Fr)
    (hi : i = s.length) (hl : s.length < arr.length) (hv : v = g f) :
    StkAt (arr.set i v) g (f :: s) := by
  subst hi hv; exact h.push f hl

theorem StkAt.reset' {arr : List ℕ} {g : Fr → ℕ} {f : Fr} {s : List Fr} {i v : ℕ}
    (h : StkAt arr g (f :: s)) (f' : Fr) (hi : i = s.length) (hl : s.length < arr.length)
    (hv : v = g f') : StkAt (arr.set i v) g (f' :: s) := by
  subst hi hv
  intro j hj
  simp only [List.length_cons] at hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases he : s.length = j
  · subst he; simp [hl]
  · rw [if_neg he, ← List.getD_eq_getElem?_getD, h j (by simp; omega)]
    simp only [List.reverse_cons]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]

theorem StkAt.pop {arr : List ℕ} {g : Fr → ℕ} {f : Fr} {s : List Fr} (h : StkAt arr g (f :: s)) :
    StkAt arr g s := by
  intro i hi
  rw [h i (by simp; omega)]
  simp only [List.reverse_cons]
  rw [List.getElem_append_left]

theorem StkAt.top {arr : List ℕ} {g : Fr → ℕ} {f : Fr} {s : List Fr} (h : StkAt arr g (f :: s)) :
    arr.getD s.length 0 = g f := by
  rw [h s.length (by simp)]
  simp

theorem StkAt.retop {arr : List ℕ} {g : Fr → ℕ} {f f' : Fr} {s : List Fr}
    (h : StkAt arr g (f :: s)) (hg : g f' = g f) : StkAt arr g (f' :: s) := by
  intro i hi
  simp only [List.length_cons] at hi
  by_cases he : i = s.length
  · subst he; rw [h.top]; simp [hg]
  · rw [h.pop i (by omega)]
    simp only [List.reverse_cons]
    rw [List.getElem_append_left]

theorem StkAt.reset {arr : List ℕ} {g : Fr → ℕ} {f : Fr} {s : List Fr} (h : StkAt arr g (f :: s))
    (f' : Fr) (hl : s.length < arr.length) : StkAt (arr.set s.length (g f')) g (f' :: s) :=
  h.pop.push f' hl

theorem getD_dropLast_snoc (b : List ℕ) (x j : ℕ) :
    (b ++ [x]).getD j 0 = if j = b.length then x else b.getD j 0 := by
  rcases lt_trichotomy j b.length with h | rfl | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem AsgAt.set {arr a a' : List ℕ} {i v : ℕ} (h : AsgAt arr a) (hi : i < arr.length)
    (ha : ∀ j, a'.getD j 0 = if j = i then v else a.getD j 0) : AsgAt (arr.set i v) a' := by
  intro j
  rw [ha j, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases he : i = j
  · subst he; simp [hi]
  · rw [if_neg he, if_neg (Ne.symm he), ← List.getD_eq_getElem?_getD, h j]

theorem AsgAt.snoc0 {arr a : List ℕ} (h : AsgAt arr a) (hi : a.length < arr.length) :
    AsgAt (arr.set a.length 0) (a ++ [0]) :=
  h.set hi fun j => getD_dropLast_snoc a 0 j

theorem AsgAt.snoc0' {arr a : List ℕ} {i : ℕ} (h : AsgAt arr a) (he : i = a.length)
    (hi : a.length < arr.length) : AsgAt (arr.set i 0) (a ++ [0]) := by
  subst he; exact h.snoc0 hi

theorem getD_length {a : List ℕ} : a.getD a.length 0 = 0 := by simp

theorem dropLast_cases (a : List ℕ) : a = [] ∨ ∃ b x, a = b ++ [x] := by
  rcases List.eq_nil_or_concat a with h | ⟨b, x, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, x, by simpa using h⟩

theorem AsgAt.drop {arr a : List ℕ} (h : AsgAt arr a) (hi : a.length - 1 < arr.length) :
    AsgAt (arr.set (a.length - 1) 0) a.dropLast := by
  refine h.set hi fun j => ?_
  rcases dropLast_cases a with rfl | ⟨b, x, rfl⟩
  · simp
  · rw [List.dropLast_concat, getD_dropLast_snoc]
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    split_ifs with h1
    · subst h1; simp
    · rfl

theorem AsgAt.repl {arr a : List ℕ} (h : AsgAt arr a) (v : ℕ) (hi : a.length - 1 < arr.length) :
    AsgAt (arr.set (a.length - 1) v) (a.dropLast ++ [v]) := by
  refine h.set hi fun j => ?_
  rcases dropLast_cases a with rfl | ⟨b, x, rfl⟩
  · simp only [List.dropLast_nil, List.nil_append, List.length_nil, Nat.zero_sub]
    rcases j with _ | j <;> simp
  · rw [List.dropLast_concat, getD_dropLast_snoc, getD_dropLast_snoc]
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    split_ifs <;> rfl

theorem AsgAt.drop' {arr a : List ℕ} {i : ℕ} (h : AsgAt arr a) (hi : i = a.length - 1)
    (hl : a.length - 1 < arr.length) : AsgAt (arr.set i 0) a.dropLast := by
  subst hi; exact h.drop hl

theorem AsgAt.repl' {arr a : List ℕ} {i x : ℕ} (h : AsgAt arr a) (v : ℕ) (hi : i = a.length - 1)
    (hl : a.length - 1 < arr.length) (hv : x = v) : AsgAt (arr.set i x) (a.dropLast ++ [v]) := by
  subst hi hv; exact h.repl _ hl

/-- Collapse the environment chains of a symbolic run. -/
macro "bsimp" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, arrs_setArr, vars_setArr,
  length_arrs_setArr, List.length_set, ↓reduceIte, String.reduceEq])

/-- Close an infeasible path of a symbolic run. -/
macro "bsimpa" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, arrs_setArr, vars_setArr,
  length_arrs_setArr, List.length_set, ↓reduceIte, String.reduceEq] at *)

/-- Close an infeasible path of a symbolic run. -/
macro "bdead" : tactic => `(tactic| (exfalso; simp only [vars_setVar, arrs_setVar, arrs_setArr,
  vars_setArr, ↓reduceIte, String.reduceEq] at *; omega))

/-- The data arrays: the code, the ends and the adjacency matrix. -/
structure BData (B : ℕ) (τ : Env) : Prop where
  lc : (τ.arrs "bfc").length = B
  le : (τ.arrs "bfe").length = B
  lA : (τ.arrs "bfA").length = B
  vc : ∀ i, (τ.arrs "bfc").getD i 0 < B
  ve : ∀ i, (τ.arrs "bfe").getD i 0 < B
  vA : ∀ i, (τ.arrs "bfA").getD i 0 ≤ 1

/-- The configuration `c` is represented in `τ`. -/
structure BRep (B n : ℕ) (c : Cfg) (τ : Env) : Prop where
  hn : τ.vars "bfn" = n
  hm : τ.vars "bfm" = if c.ev then 1 else 0
  hp : τ.vars "bfp" = c.pos
  hb : τ.vars "bfb" = if c.val then 1 else 0
  hs : τ.vars "bfs" = c.stk.length
  hd : τ.vars "bfd" = c.asg.length
  lk : (τ.arrs "bfk").length = B
  la : (τ.arrs "bfa").length = B
  lw : (τ.arrs "bfw").length = B
  lg : (τ.arrs "bfg").length = B
  kind : StkAt (τ.arrs "bfk") frKind c.stk
  arg : StkAt (τ.arrs "bfa") frArg c.stk
  val : StkAt (τ.arrs "bfw") frVal c.stk
  asg : AsgAt (τ.arrs "bfg") c.asg

/-- The machine's view of the arrays. -/
def feOf (τ : Env) : ℕ → ℕ := fun j => (τ.arrs "bfe").getD j 0

/-- The adjacency test read from the matrix. -/
def adjOf (τ : Env) (n : ℕ) : ℕ → ℕ → Bool := fun u v => (τ.arrs "bfA").getD (u * n + v) 0 == 1

/-- The code. -/
def cdOf (τ : Env) : List ℕ := τ.arrs "bfc"

/-- Push a frame. -/
def pushF (k : ℕ) (a v : Expr) : Com :=
  .seq (.store "bfk" (.var "bfs") (.lit k)) (.seq (.store "bfa" (.var "bfs") a)
    (.seq (.store "bfw" (.var "bfs") v) (.assign "bfs" (.add (.var "bfs") (.lit 1)))))

/-- The evaluation steps. -/
def evalStep : Com :=
  .seq (.assign "bfo" (.get "bfc" (.var "bfp")))
  (.ite (.eq (.var "bfo") (.lit 0))
    (.seq (.assign "bfb" (.get "bfA" (.add (.mul (.get "bfg" (.get "bfc" (.add (.var "bfp") (.lit 1))))
      (.var "bfn")) (.get "bfg" (.get "bfc" (.add (.var "bfp") (.lit 2))))))) (.assign "bfm" (.lit 0)))
  (.ite (.eq (.var "bfo") (.lit 1))
    (.seq (.ite (.eq (.get "bfg" (.get "bfc" (.add (.var "bfp") (.lit 1))))
        (.get "bfg" (.get "bfc" (.add (.var "bfp") (.lit 2)))))
      (.assign "bfb" (.lit 1)) (.assign "bfb" (.lit 0))) (.assign "bfm" (.lit 0)))
  (.ite (.eq (.var "bfo") (.lit 2))
    (.seq (pushF 1 (.lit 0) (.lit 0)) (.assign "bfp" (.add (.var "bfp") (.lit 1))))
  (.ite (.eq (.var "bfo") (.lit 3))
    (.seq (pushF 2 (.get "bfe" (.add (.var "bfp") (.lit 1))) (.lit 0))
      (.assign "bfp" (.add (.var "bfp") (.lit 1))))
  (.ite (.eq (.var "bfn") (.lit 0))
    (.seq (.assign "bfb" (.lit 0)) (.assign "bfm" (.lit 0)))
    (.seq (pushF 4 (.add (.var "bfp") (.lit 1)) (.lit 0))
      (.seq (.store "bfg" (.var "bfd") (.lit 0))
        (.seq (.assign "bfd" (.add (.var "bfd") (.lit 1))) (.assign "bfp" (.add (.var "bfp") (.lit 1)))))))))))

/-- Return from a quantifier frame. -/
def retEx : Com :=
  .seq (.assign "bfv" (.get "bfw" (.var "bft"))) (.seq (.assign "bfd" (.sub (.var "bfd") (.lit 1)))
    (.ite (.eq (.var "bfb") (.lit 1))
      (.seq (.assign "bfs" (.var "bft")) (.store "bfg" (.var "bfd") (.lit 0)))
      (.ite (.lt (.add (.var "bfv") (.lit 1)) (.var "bfn"))
        (.seq (.store "bfw" (.var "bft") (.add (.var "bfv") (.lit 1)))
          (.seq (.store "bfg" (.var "bfd") (.add (.var "bfv") (.lit 1)))
            (.seq (.assign "bfd" (.add (.var "bfd") (.lit 1)))
              (.seq (.assign "bfm" (.lit 1)) (.assign "bfp" (.get "bfa" (.var "bft")))))))
        (.seq (.assign "bfs" (.var "bft")) (.store "bfg" (.var "bfd") (.lit 0))))))

/-- The return steps. -/
def retStep : Com :=
  .seq (.assign "bft" (.sub (.var "bfs") (.lit 1))) (.seq (.assign "bfo" (.get "bfk" (.var "bft")))
  (.ite (.eq (.var "bfo") (.lit 1))
    (.seq (.assign "bfb" (.sub (.lit 1) (.var "bfb"))) (.assign "bfs" (.var "bft")))
  (.ite (.eq (.var "bfo") (.lit 2))
    (.ite (.eq (.var "bfb") (.lit 1))
      (.seq (.store "bfk" (.var "bft") (.lit 3))
        (.seq (.assign "bfm" (.lit 1)) (.seq (.assign "bfp" (.get "bfa" (.var "bft")))
          (.store "bfa" (.var "bft") (.lit 0)))))
      (.assign "bfs" (.var "bft")))
  (.ite (.eq (.var "bfo") (.lit 3))
    (.assign "bfs" (.var "bft"))
    retEx))))

/-- One step. -/
def bfStep : Com := .ite (.eq (.var "bfm") (.lit 1)) evalStep retStep

theorem asg_getD_lt {n : ℕ} {a : List ℕ} (haN : ∀ x ∈ a, x < n) (i : ℕ) :
    a.getD i 0 < n ∨ a.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : a[i]? with
  | none => simp
  | some x => exact Or.inl (by simpa using haN x (List.mem_of_getElem? h))

theorem idx_lt {n B u v : ℕ} (hnB : n * n < B) (hu : u < n ∨ u = 0) (hv : v < n ∨ v = 0) :
    u * n + v < B := by
  rcases hu with hu | rfl
  · rcases hv with hv | rfl
    · have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hu
      nlinarith
    · have : u * n < n * n := Nat.mul_lt_mul_of_pos_right hu (by omega)
      omega
  · rcases hv with hv | rfl
    · simp; nlinarith
    · simp; omega

set_option hygiene false in
/-- Close the fields of the representation that a step does not change. -/
macro "bfin" : tactic => `(tactic| first
  | assumption
  | rfl
  | (simp; done)
  | omega
  | (simp only [List.length_cons, List.length_append, List.length_singleton]; omega)
  | exact hr.hn
  | (simpa using hr.hm)
  | (simpa using hr.hb)
  | exact hr.hp
  | exact hr.hb
  | exact hr.hs
  | exact hr.hd
  | exact hr.lk
  | exact hr.la
  | exact hr.lw
  | exact hr.lg
  | exact hr.kind
  | exact hr.arg
  | exact hr.val
  | exact hr.asg
  | skip)

/-- Finish a symbolic run: close the infeasible paths and the bounds,
split the representation into its fields and close the unchanged ones. -/
macro "bwalk" : tactic => `(tactic| (
  all_goals first | bdead | (bsimpa; omega) | skip
  all_goals (try refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals (try bsimp)
  all_goals bfin))

/-- The facts every case of the simulation starts from. -/
structure Pre (B n L : ℕ) (c : Cfg) (τ : Env) : Prop where
  rep : BRep B n c τ
  dat : BData B τ
  small : Small L n c
  hLB : L + 3 < B
  hnB : n * n < B

theorem ev_adj {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨true, p, b, s, a⟩ τ) (hop : (τ.arrs "bfc").getD p 0 = 0) :
    ∃ τ', Run B evalStep τ τ' 100 ∧ BRep B n ⟨false, p,
      adjOf τ n (a.getD ((τ.arrs "bfc").getD (p + 1) 0) 0) (a.getD ((τ.arrs "bfc").getD (p + 2) 0) 0),
      s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only at hpL hsL haL haN hfr
  have hn := hr.hn
  have hp : τ.vars "bfp" = p := hr.hp
  have hlc := hD.lc
  have hlA := hD.lA
  have hlg := hr.lg
  rw [← hp] at hop
  have hc1 := hD.vc (τ.vars "bfp" + 1)
  have hc2 := hD.vc (τ.vars "bfp" + 2)
  have hg1 := hr.asg ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0)
  have hg2 := hr.asg ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0)
  simp only at hg1 hg2
  have hidx : (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) 0 * τ.vars "bfn" +
      (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0) 0 < B := by
    rw [hg1, hg2, hn]; exact idx_lt hnB (asg_getD_lt haN _) (asg_getD_lt haN _)
  have hAv := hD.vA ((τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) 0 *
    τ.vars "bfn" + (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0) 0)
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hmul : (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) 0 * τ.vars "bfn" < B := by
    omega
  have hv1 : (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) 0 < B := by
    rw [hg1]; rcases asg_getD_lt haN ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) with h | h
    · nlinarith
    · omega
  have hv2 : (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0) 0 < B := by
    rw [hg2]; rcases asg_getD_lt haN ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0) with h | h
    · nlinarith
    · omega
  unfold evalStep pushF
  run_vcg
  bwalk
  simp only [adjOf]
  rw [← hp, ← hg1, ← hg2, ← hn]
  have key : ∀ x : ℕ, x ≤ 1 → x = if (x == 1) = true then 1 else 0 := by
    intro x hx; interval_cases x <;> rfl
  exact key _ hAv

theorem ev_eq {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨true, p, b, s, a⟩ τ) (hop : (τ.arrs "bfc").getD p 0 = 1) :
    ∃ τ', Run B evalStep τ τ' 100 ∧ BRep B n ⟨false, p,
      a.getD ((τ.arrs "bfc").getD (p + 1) 0) 0 == a.getD ((τ.arrs "bfc").getD (p + 2) 0) 0,
      s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only at hpL hsL haL haN hfr
  have hn := hr.hn
  have hp : τ.vars "bfp" = p := hr.hp
  have hlc := hD.lc
  have hlg := hr.lg
  rw [← hp] at hop
  have hc1 := hD.vc (τ.vars "bfp" + 1)
  have hc2 := hD.vc (τ.vars "bfp" + 2)
  have hg1 := hr.asg ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0)
  have hg2 := hr.asg ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0)
  simp only at hg1 hg2
  have hv1 : (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) 0 < B := by
    rw [hg1]; rcases asg_getD_lt haN ((τ.arrs "bfc").getD (τ.vars "bfp" + 1) 0) with h | h
    · nlinarith
    · omega
  have hv2 : (τ.arrs "bfg").getD ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0) 0 < B := by
    rw [hg2]; rcases asg_getD_lt haN ((τ.arrs "bfc").getD (τ.vars "bfp" + 2) 0) with h | h
    · nlinarith
    · omega
  unfold evalStep pushF
  run_vcg
  bwalk
  all_goals rename_i hc
  all_goals bsimpa
  all_goals rw [← hp, ← hg1, ← hg2]
  · simp only [hc, beq_self_eq_true, ↓reduceIte]
  · simp only [beq_iff_eq, hc, ↓reduceIte]

theorem ev_not {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨true, p, b, s, a⟩ τ) (hop : (τ.arrs "bfc").getD p 0 = 2) :
    ∃ τ', Run B evalStep τ τ' 100 ∧ BRep B n ⟨true, p + 1, b, .neg :: s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only at hpL hsL haL haN hfr
  have hp : τ.vars "bfp" = p := hr.hp
  have hss : τ.vars "bfs" = s.length := hr.hs
  have hlc := hD.lc
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  rw [← hp] at hop
  unfold evalStep pushF
  run_vcg
  bwalk
  · exact StkAt.push' hr.kind .neg hss (by simp [hlk]; omega) rfl
  · exact StkAt.push' hr.arg .neg hss (by simp [hla]; omega) rfl
  · exact StkAt.push' hr.val .neg hss (by simp [hlw]; omega) rfl

theorem ev_and {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨true, p, b, s, a⟩ τ) (hop : (τ.arrs "bfc").getD p 0 = 3) :
    ∃ τ', Run B evalStep τ τ' 100 ∧
      BRep B n ⟨true, p + 1, b, .andL (feOf τ (p + 1)) :: s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only at hpL hsL haL haN hfr
  have hp : τ.vars "bfp" = p := hr.hp
  have hss : τ.vars "bfs" = s.length := hr.hs
  have hlc := hD.lc
  have hle := hD.le
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  rw [← hp] at hop
  have he1 := hD.ve (τ.vars "bfp" + 1)
  unfold evalStep pushF
  run_vcg
  bwalk
  · exact StkAt.push' hr.kind (.andL _) hss (by simp [hlk]; omega) rfl
  · exact StkAt.push' hr.arg (.andL (feOf τ (p + 1))) hss (by simp [hla]; omega) (by rw [hp]; rfl)
  · exact StkAt.push' hr.val (.andL _) hss (by simp [hlw]; omega) rfl

theorem ev_ex0 {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨true, p, b, s, a⟩ τ) (h0 : (τ.arrs "bfc").getD p 0 ≠ 0)
    (h1 : (τ.arrs "bfc").getD p 0 ≠ 1) (h2 : (τ.arrs "bfc").getD p 0 ≠ 2)
    (h3 : (τ.arrs "bfc").getD p 0 ≠ 3) (hn0 : n = 0) :
    ∃ τ', Run B evalStep τ τ' 100 ∧ BRep B n ⟨false, p, false, s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only at hpL hsL haL haN hfr
  have hp : τ.vars "bfp" = p := hr.hp
  have hn : τ.vars "bfn" = n := hr.hn
  have hlc := hD.lc
  have hc0 := hD.vc (τ.vars "bfp")
  rw [← hp] at h0 h1 h2 h3
  unfold evalStep pushF
  run_vcg
  bwalk

theorem ev_ex {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨true, p, b, s, a⟩ τ) (h0 : (τ.arrs "bfc").getD p 0 ≠ 0)
    (h1 : (τ.arrs "bfc").getD p 0 ≠ 1) (h2 : (τ.arrs "bfc").getD p 0 ≠ 2)
    (h3 : (τ.arrs "bfc").getD p 0 ≠ 3) (hn0 : n ≠ 0) :
    ∃ τ', Run B evalStep τ τ' 100 ∧ BRep B n ⟨true, p + 1, b, .ex (p + 1) 0 :: s, a ++ [0]⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only at hpL hsL haL haN hfr
  have hp : τ.vars "bfp" = p := hr.hp
  have hn : τ.vars "bfn" = n := hr.hn
  have hss : τ.vars "bfs" = s.length := hr.hs
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlc := hD.lc
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hc0 := hD.vc (τ.vars "bfp")
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  rw [← hp] at h0 h1 h2 h3
  unfold evalStep pushF
  run_vcg
  bwalk
  · simp; omega
  · exact StkAt.push' hr.kind (.ex _ _) hss (by simp [hlk]; omega) rfl
  · exact StkAt.push' hr.arg (.ex (p + 1) 0) hss (by simp [hla]; omega) (by rw [hp]; rfl)
  · exact StkAt.push' hr.val (.ex _ 0) hss (by simp [hlw]; omega) rfl
  · exact AsgAt.snoc0' hr.asg hd (by simp [hlg]; omega)

theorem ret_neg {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, b, .neg :: s, a⟩ τ) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨false, p, !b, s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if b then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.neg) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.neg) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.neg) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.neg) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · rw [hb]; cases b <;> rfl
  · exact hr.kind.pop
  · exact hr.arg.pop
  · exact hr.val.pop

theorem ret_andT {B n L p : ℕ} {r : ℕ} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, true, .andL r :: s, a⟩ τ) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨true, r, true, .andR :: s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if true then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.andL r) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.andL r) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.andL r) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.andL r) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · exact hr.kind.reset' .andR (by omega) (by simp [hlk]; omega) rfl
  · exact hr.arg.reset' .andR (by omega) (by simp [hla]; omega) rfl
  · exact hr.val.retop rfl

theorem ret_andF {B n L p : ℕ} {r : ℕ} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, false, .andL r :: s, a⟩ τ) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨false, p, false, s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if false then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.andL r) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.andL r) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.andL r) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.andL r) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · exact hr.kind.pop
  · exact hr.arg.pop
  · exact hr.val.pop

theorem ret_andR {B n L p : ℕ} {b : Bool} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, b, .andR :: s, a⟩ τ) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨false, p, b, s, a⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if b then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.andR) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.andR) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.andR) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.andR) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · exact hr.kind.pop
  · exact hr.arg.pop
  · exact hr.val.pop

theorem ret_exT {B n L p : ℕ} {pc v : ℕ} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, true, .ex pc v :: s, a⟩ τ) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨false, p, true, s, a.dropLast⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if true then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.ex pc v) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · simp; omega
  · exact hr.kind.pop
  · exact hr.arg.pop
  · exact hr.val.pop
  · exact hr.asg.drop' (by dsimp only; omega) (by simp [hlg]; omega)

theorem ret_exN {B n L p : ℕ} {pc v : ℕ} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, false, .ex pc v :: s, a⟩ τ) (hv : v + 1 < n) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨true, pc, false, .ex pc (v + 1) :: s, a.dropLast ++ [v + 1]⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if false then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.ex pc v) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · simp; omega
  · exact hr.kind.retop rfl
  · exact hr.arg.retop rfl
  · exact hr.val.reset' (.ex pc (v + 1)) (by omega) (by simp [hlw]; omega) (by rw [hw]; rfl)
  · exact hr.asg.repl' (v + 1) (by dsimp only; omega) (by simp [hlg]; omega) (by rw [hw])

theorem ret_exE {B n L p : ℕ} {pc v : ℕ} {s : List Fr} {a : List ℕ} {τ : Env}
    (h : Pre B n L ⟨false, p, false, .ex pc v :: s, a⟩ τ) (hv : ¬ v + 1 < n) :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n ⟨false, p, false, s, a.dropLast⟩ τ' := by
  obtain ⟨hr, hD, ⟨hpL, hsL, haL, haN, hfr⟩, hLB, hnB⟩ := h
  simp only [List.length_cons] at hpL hsL haL haN hfr
  have hn : τ.vars "bfn" = n := hr.hn
  have hnb : τ.vars "bfn" < B := by rw [hn]; nlinarith
  have hp : τ.vars "bfp" = p := hr.hp
  have hb : τ.vars "bfb" = if false then 1 else 0 := hr.hb
  try simp only [Bool.false_eq_true, eq_self_iff_true, if_true, if_false] at hb
  have hss : τ.vars "bfs" = s.length + 1 := by have := hr.hs; simpa using this
  have hd : τ.vars "bfd" = a.length := hr.hd
  have hlk := hr.lk
  have hla := hr.la
  have hlw := hr.lw
  have hlg := hr.lg
  have hk : (τ.arrs "bfk").getD (τ.vars "bfs" - 1) 0 = frKind (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.kind.top
  have ha : (τ.arrs "bfa").getD (τ.vars "bfs" - 1) 0 = frArg (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.arg.top
  have hw : (τ.arrs "bfw").getD (τ.vars "bfs" - 1) 0 = frVal (.ex pc v) := by
    rw [hss, Nat.add_sub_cancel]; exact hr.val.top
  have hbB : τ.vars "bfb" < B := by rw [hb]; (try split) <;> omega
  have hfr0 := hfr (.ex pc v) (by simp)
  simp only [frKind, frArg, frVal, FrOK] at hk ha hw hfr0
  unfold retStep retEx
  run_vcg
  bwalk
  · simp; omega
  · exact hr.kind.pop
  · exact hr.arg.pop
  · exact hr.val.pop
  · exact hr.asg.drop' (by dsimp only; omega) (by simp [hlg]; omega)

theorem evalStep_sim {B n L : ℕ} {c c' : Cfg} {τ : Env} (h : Pre B n L c τ) (hev : c.ev = true)
    (hst : step n (adjOf τ n) (cdOf τ) (feOf τ) c = some c') :
    ∃ τ', Run B evalStep τ τ' 100 ∧ BRep B n c' τ' := by
  obtain ⟨ev, p, b, s, a⟩ := c
  simp only at hev; subst hev
  have hpn := h.rep.hn
  simp only [step, if_true, cdOf] at hst
  split at hst
  · rename_i _ hop
    injection hst with hst; subst hst; exact ev_adj h hop
  · rename_i _ hop
    injection hst with hst; subst hst; exact ev_eq h hop
  · rename_i _ hop
    injection hst with hst; subst hst; exact ev_not h hop
  · rename_i _ hop
    injection hst with hst; subst hst; exact ev_and h hop
  · rename_i _ h0 h1 h2 h3
    by_cases hn0 : n = 0
    · simp only [hn0, if_true] at hst
      injection hst with hst; subst hst; exact ev_ex0 h h0 h1 h2 h3 hn0
    · simp only [hn0, if_false] at hst
      injection hst with hst; subst hst; exact ev_ex h h0 h1 h2 h3 hn0

theorem retStep_sim {B n L : ℕ} {c c' : Cfg} {τ : Env} (h : Pre B n L c τ) (hev : c.ev = false)
    (hst : step n (adjOf τ n) (cdOf τ) (feOf τ) c = some c') :
    ∃ τ', Run B retStep τ τ' 100 ∧ BRep B n c' τ' := by
  obtain ⟨ev, p, b, s, a⟩ := c
  simp only at hev; subst hev
  cases s with
  | nil => simp [step] at hst
  | cons f s =>
    cases f with
    | neg =>
      simp only [step, Bool.false_eq_true, if_false, Option.some.injEq] at hst
      subst hst; exact ret_neg h
    | andL r =>
      cases b
      · simp only [step, Bool.false_eq_true, if_false, Option.some.injEq] at hst
        subst hst; exact ret_andF h
      · simp only [step, Bool.false_eq_true, if_false, if_true, Option.some.injEq] at hst
        subst hst; exact ret_andT h
    | andR =>
      simp only [step, Bool.false_eq_true, if_false, Option.some.injEq] at hst
      subst hst; exact ret_andR h
    | ex pc v =>
      cases b
      · by_cases hv : v + 1 < n
        · simp only [step, Bool.false_eq_true, if_false, hv, if_true, Option.some.injEq] at hst
          subst hst; exact ret_exN h hv
        · simp only [step, Bool.false_eq_true, if_false, hv, Option.some.injEq] at hst
          subst hst; exact ret_exE h hv
      · simp only [step, Bool.false_eq_true, if_false, if_true, Option.some.injEq] at hst
        subst hst; exact ret_exT h

/-- **One step of the machine.** On a small configuration with a
successor, `bfStep` moves the representation to the successor. -/
theorem bfStep_sim {B n L : ℕ} {c c' : Cfg} {τ : Env} (h : Pre B n L c τ)
    (hst : step n (adjOf τ n) (cdOf τ) (feOf τ) c = some c') :
    ∃ τ', Run B bfStep τ τ' 104 ∧ BRep B n c' τ' := by
  have hm := h.rep.hm
  have hmB : τ.vars "bfm" < B := by have := h.hLB; split at hm <;> omega
  have h1B : 1 < B := by have := h.hLB; omega
  cases hev : c.ev
  · obtain ⟨τ', hr, hb⟩ := retStep_sim h hev hst
    rw [hev] at hm
    refine ⟨τ', Run.ite_false ?_ hr, hb⟩
    rw [evalB_condEq (evalB_var hmB) (evalB_lit h1B)]
    simp [hm]
  · obtain ⟨τ', hr, hb⟩ := evalStep_sim h hev hst
    rw [hev] at hm
    refine ⟨τ', Run.ite_true ?_ hr, hb⟩
    rw [evalB_condEq (evalB_var hmB) (evalB_lit h1B)]
    simp [hm]

end Lax185574Proofs.MC.Brute
