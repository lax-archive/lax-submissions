import Lax185574Proofs.MC.Glue.RP
import Lax185574Proofs.MC.Asm.Defs


/-!
Reading the input of the glue program of thm:mc, and the layout of the
input word `x = g ++ toWord σ ++ toWord φ`.

`readInto ar` reads `n` entries from the input tape into the array `ar`.
The layout lemmas give the positions of the colors, of the number of
steps, of the steps and of the code of the sentence in `x`, from the
header of the graph block.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax271696.GraphEncoding

/-! ### Reading entries into an array -/

/-- Read one entry into `ar` at `p`, and advance `p` and `j`. -/
def readOne (ar : String) : Com :=
  .seq (.read "v") (.seq (.store ar (.var "p") (.var "v"))
    (.seq (.assign "p" (.add (.var "p") (.lit 1))) (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Read `n` entries into `ar` from position `p` on, counting with `j`. -/
def readInto (ar : String) : Com := .while (.lt (.var "j") (.var "n")) (readOne ar)

/-- `j` entries of `u` have been read after the prefix `pre` of `ar`, whose
old contents are `orig`. -/
def IntoInv (ar : String) (pre orig u rest : List ℕ) (τ : Env) : Prop :=
  ∃ j ≤ u.length, τ.vars "j" = j ∧ τ.vars "n" = u.length ∧ τ.vars "p" = pre.length + j ∧
    τ.inp = u.drop j ++ rest ∧ τ.arrs ar = (pre ++ u.take j) ++ orig.drop (pre.length + j)

theorem readInto_run {B : ℕ} {ar : String} {pre orig u rest : List ℕ} {σ : Env}
    (hfit : pre.length + u.length ≤ orig.length) (hB : pre.length + u.length < B)
    (hu : ∀ v ∈ u, v < B) (hσ : IntoInv ar pre orig u rest σ) :
    ∃ σ', Run B (readInto ar) σ σ' (16 * u.length + 4) ∧
      σ'.vars "p" = pre.length + u.length ∧ σ'.vars "j" = u.length ∧ σ'.inp = rest ∧
      σ'.arrs ar = (pre ++ u) ++ orig.drop (pre.length + u.length) := by
  have hstep : ∀ τ, IntoInv ar pre orig u rest τ →
      (Cond.lt (.var "j") (.var "n")).evalB B τ = some true →
      ∃ τ', Run B (readOne ar) τ τ' 12 ∧ IntoInv ar pre orig u rest τ' ∧
        u.length - τ'.vars "j" < u.length - τ.vars "j" := by
    rintro τ ⟨j, hjle, hj, hn, hp, hinp, ha⟩ hc
    have hjlt : j < u.length := by
      rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by omega)), hj, hn] at hc
      simpa using hc
    have hinp' : τ.inp = u[j] :: (u.drop (j + 1) ++ rest) := by
      rw [hinp, List.drop_eq_getElem_cons hjlt]; rfl
    have huj : u[j] < B := hu _ (List.getElem_mem _)
    have hlen : (pre ++ u.take j).length = pre.length + j := by simp; omega
    have hr : Run B (readOne ar) τ
        (((({ τ.setVar "v" u[j] with inp := u.drop (j + 1) ++ rest }).setArr ar (pre.length + j)
          u[j]).setVar "p" (pre.length + j + 1)).setVar "j" (j + 1)) 12 := by
      unfold readOne
      refine (Run.seq (Run.read hinp') (Run.seq (Run.store ?_ ?_ ?_)
        (Run.seq (Run.assign ?_) (Run.assign ?_)))).mono (by simp)
      · simp [hp]; omega
      · simp; exact huj
      · simp [ha]; omega
      · simp [hp]; omega
      · simp [hj]; omega
    refine ⟨_, hr, ⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp [hn]
    · simp; omega
    · simp
    · simp only [arrs_setVar, arrs_setArr, if_true, ha]
      rw [← hlen, set_prefix (by simp; omega), hlen, List.take_add_one,
        List.getElem?_eq_getElem hjlt]
      simp [Nat.add_assoc]
    · simp [hj]; omega
  obtain ⟨σ', hrun, ⟨j, hjle, hj', hn, hp, hinp, ha⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "j") (.var "n")) (c := readOne ar)
      (IntoInv ar pre orig u rest) (fun τ => u.length - τ.vars "j") 12
      (fun τ ⟨j, hjle, hj, hn, _⟩ => evalB_condLt_vars (by rw [hj]; omega) (by rw [hn]; omega))
      hstep hσ
  have hju : j = u.length := by
    rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by omega)), hj', hn] at hfalse
    simp at hfalse; omega
  subst hju
  obtain ⟨j0, -, hj0, -, -, -, -⟩ := hσ
  refine ⟨σ', hrun.mono ?_, hp, hj', by simpa using hinp, ?_⟩
  · simp only [Cond.size, Expr.size]; omega
  · rw [ha, List.take_length]

/-! ### The layout of the input word -/

theorem flatten_map_single (l : List ℕ) : (l.map fun c => [c]).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem toWord_colors {n : ℕ} (c : Fin n → ℕ) : toWord c = n :: List.ofFn c := by
  show (List.ofFn c).length :: ((List.ofFn c).map (fun a => [a])).flatten = _
  rw [flatten_map_single, List.length_ofFn]

theorem toWord_steps (st : List Step) :
    toWord st = st.length :: (st.map stepCode).flatten := rfl

theorem toWord_script {n : ℕ} (σ : Script n) :
    toWord σ = (n :: List.ofFn σ.colors) ++ (σ.steps.length :: (σ.steps.map stepCode).flatten) := by
  show toWord σ.colors ++ toWord σ.steps = _
  rw [toWord_colors, toWord_steps]

theorem length_flatten_stepCode (st : List Step) : ((st.map stepCode).flatten).length = 3 * st.length := by
  induction st with
  | nil => simp
  | cons s st ih => cases s <;> simp [stepCode, ih] <;> omega

/-- The input word behind the graph block. -/
theorem input_drop {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) :
    (g ++ toWord σ ++ c).drop g.length = n :: (List.ofFn σ.colors ++ (σ.steps.length ::
      ((σ.steps.map stepCode).flatten ++ c))) := by
  rw [List.append_assoc, List.drop_left, toWord_script]; simp

theorem getElem?_input {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) (k : ℕ) :
    (g ++ toWord σ ++ c)[g.length + k]? = (n :: (List.ofFn σ.colors ++ (σ.steps.length ::
      ((σ.steps.map stepCode).flatten ++ c))))[k]? := by
  rw [← input_drop g σ c, List.getElem?_drop]

theorem input_n {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) :
    (g ++ toWord σ ++ c)[g.length]? = some n := by
  have := getElem?_input g σ c 0; simpa using this

theorem input_color {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) (i : Fin n) :
    (g ++ toWord σ ++ c)[g.length + 1 + i]? = some (σ.colors i) := by
  rw [Nat.add_assoc, getElem?_input, Nat.add_comm, List.getElem?_cons_succ,
    List.getElem?_append_left (by simp)]
  simp

theorem input_count {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) :
    (g ++ toWord σ ++ c)[g.length + 1 + n]? = some σ.steps.length := by
  rw [Nat.add_assoc, getElem?_input, Nat.add_comm, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp

theorem input_steps {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) :
    (g ++ toWord σ ++ c).drop (g.length + n + 2) = (σ.steps.map stepCode).flatten ++ c := by
  rw [show g.length + n + 2 = g.length + (n + 2) by omega, ← List.drop_drop, input_drop]
  rw [List.drop_succ_cons, show n + 1 = (List.ofFn σ.colors).length + 1 by simp,
    ← List.drop_drop, List.drop_left]
  rfl

theorem drop_flatten_stepCode (st : List Step) (c : List ℕ) :
    ((st.map stepCode).flatten ++ c).drop (3 * st.length) = c := by
  rw [show 3 * st.length = ((st.map stepCode).flatten).length from (length_flatten_stepCode st).symm,
    List.drop_left]

theorem input_formula {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) :
    (g ++ toWord σ ++ c).drop (g.length + n + 2 + 3 * σ.steps.length) = c := by
  rw [← List.drop_drop, input_steps, drop_flatten_stepCode]

theorem drop_step (st : List Step) (c : List ℕ) {t : ℕ} (ht : t < st.length) :
    ((st.map stepCode).flatten ++ c).drop (3 * t) =
      stepCode st[t] ++ (((st.drop (t + 1)).map stepCode).flatten ++ c) := by
  induction st generalizing t with
  | nil => simp at ht
  | cons s st ih =>
      cases t with
      | zero => simp
      | succ t =>
          have h3 : (stepCode s).length = 3 := by cases s <;> rfl
          simp only [List.map_cons, List.flatten_cons, List.append_assoc]
          rw [show 3 * (t + 1) = (stepCode s).length + 3 * t by omega, ← List.drop_drop,
            List.drop_left]
          simpa using ih (by simpa using ht)

/-- The window of step `t` is its code. -/
theorem input_window {n : ℕ} (g : List ℕ) (σ : Script n) (c : List ℕ) {t : ℕ}
    (ht : t < σ.steps.length) :
    ((g ++ toWord σ ++ c).drop (g.length + n + 2 + 3 * t)).take 3 = stepCode σ.steps[t] := by
  rw [← List.drop_drop, input_steps, drop_step _ _ ht]
  have h3 : (stepCode σ.steps[t]).length = 3 := by cases σ.steps[t] <;> rfl
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- The graph block from its header. -/
theorem graph_length {g : List ℕ} {n : ℕ} {Gr : SimpleGraph (Fin n)} (h : EncodesGraph g n Gr) :
    g.length = 3 + g.getD 0 0 + 2 * g.getD 1 0 := by
  have := h.length_eq; have := h.vertexCount_eq
  simp only [vertexCount, edgeCount] at *; omega


/-! ### The header of round 0 -/

/-- Positions in the input read into `U`: `gn = n`, `gE` the edge count,
`gL = |g|`, `sm = m`, `off` the start of the steps, `fp` the code of the
sentence. -/
def hdr0 : Com :=
  .seq (.assign "gn" (.get "U" (.lit 0))) (.seq (.assign "gE" (.get "U" (.lit 1)))
  (.seq (.assign "gL" (.add (.add (.lit 3) (.var "gn")) (.add (.var "gE") (.var "gE"))))
  (.seq (.assign "sm" (.get "U" (.add (.add (.var "gL") (.lit 1)) (.var "gn"))))
  (.seq (.assign "off" (.add (.add (.var "gL") (.var "gn")) (.lit 2)))
  (.assign "fp" (.add (.var "off") (.add (.var "sm") (.add (.var "sm") (.var "sm")))))))))

theorem hdr0_run {B n : ℕ} {Gr : SimpleGraph (Fin n)} {g c r : List ℕ} {sc : Script n} {σ : Env}
    (hg : EncodesGraph g n Gr) (hU : σ.arrs "U" = (g ++ toWord sc ++ c) ++ r)
    (hB : (g ++ toWord sc ++ c).length + 1 < B) :
    Run B hdr0 σ ((((((σ.setVar "gn" n).setVar "gE" (g.getD 1 0)).setVar "gL" g.length).setVar
      "sm" sc.steps.length).setVar "off" (g.length + n + 2)).setVar "fp"
        (g.length + n + 2 + 3 * sc.steps.length)) 60 := by
  set x := g ++ toWord sc ++ c with hx
  have hgl := graph_length hg
  have hn0 : g.getD 0 0 = n := hg.vertexCount_eq
  have hlen' : x.length = g.length + n + 2 + 3 * sc.steps.length + c.length := by
    simp only [hx, List.length_append, toWord_script, List.length_cons, List.length_ofFn,
      length_flatten_stepCode]; omega
  have hlen : g.length + n + 2 + 3 * sc.steps.length ≤ x.length := by omega
  have hxlen : g.length + n + 2 ≤ x.length := by omega
  have h0 : (σ.arrs "U")[0]? = some n := by
    rw [hU, List.getElem?_append_left (by omega), hx, List.append_assoc,
      List.getElem?_append_left (by omega), ← hn0, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]; rfl
  have h1 : (σ.arrs "U")[1]? = some (g.getD 1 0) := by
    rw [hU, List.getElem?_append_left (by omega), hx, List.append_assoc,
      List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]; rfl
  have hm : (σ.arrs "U")[g.length + 1 + n]? = some sc.steps.length := by
    rw [hU, List.getElem?_append_left (by omega)]; exact input_count g sc c
  unfold hdr0
  have hE : g.getD 1 0 ≤ g.length := by omega
  refine (Run.seq (Run.assign (evalB_get (evalB_lit (by omega)) h0 (by omega)))
    (Run.seq (Run.assign (evalB_get (evalB_lit (by omega)) (by simpa using h1) (by omega)))
    (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_)
      (Run.assign ?_)))))).mono (by simp)
  · rw [show g.length = 3 + n + (g.getD 1 0 + g.getD 1 0) by omega]
    exact ev_add (ev_add (evalB_lit (by omega)) (ev_var (v := n) (by simp)
      (by omega)) (by omega)) (ev_add (ev_var (v := g.getD 1 0) (by simp) (by omega))
      (ev_var (v := g.getD 1 0) (by simp) (by omega)) (by omega)) (by omega)
  · exact evalB_get (ev_add (ev_add (ev_var (v := g.length) (by simp) (by omega))
      (evalB_lit (by omega)) (by omega)) (ev_var (v := n) (by simp) (by omega)) (by omega))
      (by simpa using hm) (by omega)
  · exact ev_add (ev_add (ev_var (v := g.length) (by simp) (by omega))
      (ev_var (v := n) (by simp) (by omega)) (by omega)) (evalB_lit (by omega)) (by omega)
  · rw [show g.length + n + 2 + 3 * sc.steps.length = g.length + n + 2 +
      (sc.steps.length + (sc.steps.length + sc.steps.length)) by omega]
    exact ev_add (ev_var (v := g.length + n + 2) (by simp) (by omega))
      (ev_add (ev_var (v := sc.steps.length) (by simp) (by omega))
      (ev_add (ev_var (v := sc.steps.length) (by simp) (by omega))
        (ev_var (v := sc.steps.length) (by simp) (by omega)) (by omega)) (by omega)) (by omega)

end Lax185574Proofs.MC.Glue
