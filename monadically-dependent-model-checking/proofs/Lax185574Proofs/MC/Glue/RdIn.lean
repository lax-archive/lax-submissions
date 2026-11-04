import Lax185574Proofs.MC.Glue.Trans

/-!
Reading the input of a round of the glue program of thm:mc after the
first.

After the tag `tg`, the input is `ℓ :: win ++ st ++ |b| :: b`: the state
length, the window (three entries if the tag is `2`, none otherwise),
the state and the answer of the callee. `rdIn` reads `ℓ` into `sl`, the
window into `w0 w1 w2`, and the state and the answer one after the
other into the array `x`, with `|b|` in `bl`. `ldSc` loads the eleven
scalars of the state and the lengths of its three words (`gl fl ll`),
and sets the positions of the words in `x` (`gA fA lA`) and of the
answer (`bA`). `cpLo` copies the localized sentence into `lo`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-! ### Reading -/

/-- Read the window if the tag is `2`. -/
def rdWin : Com :=
  .ite (.eq (.var "tg") (.lit 2)) (.seq (.read "w0") (.seq (.read "w1") (.read "w2"))) .skip

/-- Read the input after the tag. -/
def rdIn : Com :=
  .seq (.read "sl") (.seq rdWin
  (.seq (.assign "p" (.lit 0)) (.seq (.assign "j" (.lit 0)) (.seq (.assign "n" (.var "sl"))
  (.seq (readInto "x") (.seq (.read "bl") (.seq (.assign "j" (.lit 0))
  (.seq (.assign "n" (.var "bl")) (readInto "x")))))))))

theorem read_run {B : ℕ} {τ : Env} {x : String} {v : ℕ} {rest : List ℕ} (h : τ.inp = v :: rest) :
    ∃ τ', Run B (.read x) τ τ' 1 ∧ (∀ y, τ'.vars y = if y = x then v else τ.vars y) ∧
      τ'.arrs = τ.arrs ∧ τ'.inp = rest ∧ τ'.out = τ.out :=
  ⟨_, Run.read h, fun _ => rfl, rfl, rfl, rfl⟩

theorem rdWin_run {B : ℕ} {τ : Env} {win rest : List ℕ} (htg : τ.vars "tg" < B) (h2 : 2 < B)
    (hwin : win.length = if τ.vars "tg" = 2 then 3 else 0) (hinp : τ.inp = win ++ rest) :
    ∃ τ', Run B rdWin τ τ' 10 ∧ τ'.inp = rest ∧
      (τ.vars "tg" = 2 → τ'.vars "w0" = win.getD 0 0 ∧ τ'.vars "w1" = win.getD 1 0 ∧
        τ'.vars "w2" = win.getD 2 0) := by
  have hc := condEq_lit (B := B) (x := "tg") (d := 2) rfl htg h2
  by_cases ht : τ.vars "tg" = 2
  · rw [if_pos ht] at hwin
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, win = [a, b, c] := by
      match win, hwin with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    refine ⟨_, (Run.ite_true (by rw [hc, decide_eq_true ht]) (Run.seq (Run.read (v := a)
      (rest := b :: c :: rest) (by rw [hinp]; rfl)) (Run.seq (Run.read (v := b) (rest := c :: rest) rfl)
      (Run.read (v := c) (rest := rest) rfl)))).mono (by simp [Cond.size, Expr.size]), rfl,
      fun _ => ⟨by simp, by simp, by simp⟩⟩
  · rw [if_neg ht] at hwin
    rw [List.length_eq_zero_iff] at hwin; subst hwin
    exact ⟨τ, (Run.ite_false (by rw [hc, decide_eq_false ht]) Run.skip).mono
      (by simp [Cond.size, Expr.size]), by simpa using hinp, fun h => absurd h ht⟩

theorem rdIn_run {B : ℕ} {τ : Env} {win st b rest : List ℕ}
    (htg : τ.vars "tg" < B) (h2 : 2 < B)
    (hwin : win.length = if τ.vars "tg" = 2 then 3 else 0)
    (hinp : τ.inp = st.length :: win ++ st ++ b.length :: b ++ rest)
    (hcap : st.length + b.length ≤ (τ.arrs "x").length) (hB : st.length + b.length < B)
    (hv : ∀ v ∈ st ++ b, v < B) :
    ∃ τ', Run B rdIn τ τ' (16 * (st.length + b.length) + 60) ∧
      τ'.vars "sl" = st.length ∧ τ'.vars "bl" = b.length ∧
      τ'.arrs "x" = (st ++ b) ++ (τ.arrs "x").drop (st.length + b.length) ∧ τ'.inp = rest ∧
      (τ.vars "tg" = 2 → τ'.vars "w0" = win.getD 0 0 ∧ τ'.vars "w1" = win.getD 1 0 ∧
        τ'.vars "w2" = win.getD 2 0) := by
  obtain ⟨τ₁, r₁, hv₁, ha₁, hi₁, -⟩ := read_run (B := B) (x := "sl") (τ := τ) (v := st.length)
    (rest := win ++ st ++ b.length :: b ++ rest) (by rw [hinp]; simp)
  have htg₁ : τ₁.vars "tg" = τ.vars "tg" := by rw [hv₁]; simp
  obtain ⟨τ₂, r₂, hi₂, hw₂⟩ := rdWin_run (τ := τ₁) (win := win) (rest := st ++ b.length :: b ++ rest)
    (by rw [htg₁]; exact htg) h2 (by rw [htg₁]; exact hwin) (by rw [hi₁]; simp)
  have hsl₂ : τ₂.vars "sl" = st.length := by
    rw [r₂.frame_var "sl" (by decide), hv₁]; simp
  have hx₂ : τ₂.arrs "x" = τ.arrs "x" := by rw [r₂.frame_arr "x" (by decide), ha₁]
  set τ₃ := ((τ₂.setVar "p" 0).setVar "j" 0).setVar "n" st.length with hτ₃
  have hst : ∀ v ∈ st, v < B := fun v h => hv v (by simp [h])
  have hbv : ∀ v ∈ b, v < B := fun v h => hv v (by simp [h])
  obtain ⟨τ₄, r₄, hp₄, hj₄, hi₄, hx₄⟩ := readInto_run (B := B) (ar := "x") (pre := [])
    (orig := τ.arrs "x") (u := st) (rest := b.length :: b ++ rest) (σ := τ₃) (by simp; omega)
    (by simp; omega) hst ⟨0, by simp, by simp [hτ₃], by simp [hτ₃], by simp [hτ₃], by
      simp [hτ₃, hi₂], by simp [hτ₃, hx₂]⟩
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hp₄ hx₄
  obtain ⟨τ₅, r₅, hv₅, ha₅, hi₅, -⟩ := read_run (B := B) (x := "bl") (τ := τ₄) (v := b.length) (rest := b ++ rest)
    (by rw [hi₄]; simp)
  set τ₆ := (τ₅.setVar "j" 0).setVar "n" b.length with hτ₆
  obtain ⟨τ₇, r₇, -, -, hi₇, hx₇⟩ := readInto_run (B := B) (ar := "x") (pre := st)
    (orig := τ.arrs "x") (u := b) (rest := rest) (σ := τ₆) (by omega) (by omega) hbv
    ⟨0, by simp, by simp [hτ₆], by simp [hτ₆], by simp [hτ₆, hv₅, hp₄], by simp [hτ₆, hi₅],
      by simp [hτ₆, ha₅, hx₄]⟩
  refine ⟨τ₇, ?_, ?_, ?_, hx₇, hi₇, fun h => ?_⟩
  · unfold rdIn
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq (Run.assign (evalB_lit (by omega)))
      (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (ev_var (v := st.length) (by
        simp [hsl₂]) (by omega))) (Run.seq r₄ (Run.seq r₅ (Run.seq (Run.assign
        (evalB_lit (by omega))) (Run.seq (Run.assign (ev_var (v := b.length) (by simp [hv₅]) (by omega)))
        r₇))))))))).mono ?_
    simp only [Expr.size]; omega
  · rw [r₇.frame_var "sl" (by decide)]
    simp only [hτ₆, vars_setVar, hv₅]
    simp only [show ("sl" = "n") = False by decide, show ("sl" = "j") = False by decide,
      show ("sl" = "bl") = False by decide, if_false]
    rw [r₄.frame_var "sl" (by decide)]; simp [hτ₃, hsl₂]
  · rw [r₇.frame_var "bl" (by decide)]; simp [hτ₆, hv₅]
  · obtain ⟨h0, h1, h2⟩ := hw₂ (by rw [htg₁]; exact h)
    have e : ∀ y ∈ ["w0", "w1", "w2"], τ₇.vars y = τ₂.vars y := by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [r₇.frame_var y (by rcases hy with rfl | rfl | rfl <;> decide)]
      simp only [hτ₆, vars_setVar, hv₅]
      rw [if_neg (by rcases hy with rfl | rfl | rfl <;> decide),
        if_neg (by rcases hy with rfl | rfl | rfl <;> decide),
        if_neg (by rcases hy with rfl | rfl | rfl <;> decide),
        r₄.frame_var y (by rcases hy with rfl | rfl | rfl <;> decide)]
      simp only [hτ₃, vars_setVar]
      rw [if_neg (by rcases hy with rfl | rfl | rfl <;> decide),
        if_neg (by rcases hy with rfl | rfl | rfl <;> decide),
        if_neg (by rcases hy with rfl | rfl | rfl <;> decide)]
    exact ⟨by rw [e _ (by simp), h0], by rw [e _ (by simp), h1], by rw [e _ (by simp), h2]⟩

/-! ### Loading scalars -/

/-- Load `x[k], x[k+1], …` into the scalars `ys`. -/
def ldL : List String → ℕ → Com
  | [], _ => .skip
  | y :: ys, k => .seq (.assign y (.get "x" (.lit k))) (ldL ys (k + 1))

theorem ldL_run {B : ℕ} : ∀ (ys : List String) (k : ℕ) (vals : List ℕ) (τ : Env),
    ys.Nodup → ys.length = vals.length → (∀ i (h : i < vals.length), (τ.arrs "x")[k + i]? = some vals[i]) →
    (∀ v ∈ vals, v < B) → k + ys.length < B →
    ∃ τ', Run B (ldL ys k) τ τ' (4 * ys.length + 1) ∧ ys.map τ'.vars = vals ∧
      (∀ z, z ∉ ys → τ'.vars z = τ.vars z) ∧ τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out
  | [], k, vals, τ, _, hl, _, _, _ => by
    have : vals = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst this
    exact ⟨τ, Run.skip.mono (by simp), rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | y :: ys, k, vals, τ, hnd, hl, hx, hvB, hB => by
    obtain ⟨v, vs, rfl⟩ : ∃ v vs, vals = v :: vs := by
      cases vals with
      | nil => simp at hl
      | cons v vs => exact ⟨v, vs, rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hv0 := hx 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hv0
    have r₁ : Run B (.assign y (.get "x" (.lit k))) τ (τ.setVar y v) 3 :=
      (Run.assign (evalB_get (evalB_lit (by simp at hB; omega)) hv0 (hvB v (by simp)))).mono
        (by simp [Expr.size])
    obtain ⟨τ', r', hm, hfr, ha, hi, ho⟩ := ldL_run ys (k + 1) vs (τ.setVar y v) (List.nodup_cons.1 hnd).2
      hl (fun i h => by
        have := hx (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      (fun u hu => hvB u (by simp [hu])) (by simp at hB; omega)
    refine ⟨τ', (Run.seq r₁ r').mono (by simp; omega), ?_, fun z hz => ?_, by rw [ha]; rfl,
      by rw [hi]; rfl, by rw [ho]; rfl⟩
    · simp only [List.map_cons, hm, List.cons.injEq, and_true]
      rw [hfr y (List.nodup_cons.1 hnd).1]; simp
    · simp only [List.mem_cons, not_or] at hz
      rw [hfr z hz.2]; simp [hz.1]

/-- The names loaded from the state. -/
def ldNames : List String := scN ++ ["gl", "fl", "ll"]

/-- Load the scalars of the state and set the positions. -/
def ldSc : Com :=
  .seq (ldL ldNames 0) (.seq (.assign "gA" (.lit 14)) (.seq (.assign "fA" (.add (.lit 14) (.var "gl")))
    (.seq (.assign "lA" (.add (.var "fA") (.var "fl"))) (.assign "bA" (.var "sl")))))

theorem ldSc_run {B : ℕ} {τ : Env} {sc gw fw lw R : List ℕ} (hsc : sc.length = 11)
    (hx : τ.arrs "x" = stW sc gw fw lw ++ R) (hv : ∀ v ∈ stW sc gw fw lw, v < B)
    (hB : 14 + gw.length + fw.length + lw.length < B) (hsl : τ.vars "sl" < B) :
    ∃ τ', Run B ldSc τ τ' 90 ∧ scN.map τ'.vars = sc ∧ τ'.vars "gl" = gw.length ∧
      τ'.vars "fl" = fw.length ∧ τ'.vars "ll" = lw.length ∧ τ'.vars "gA" = 14 ∧
      τ'.vars "fA" = 14 + gw.length ∧ τ'.vars "lA" = 14 + gw.length + fw.length ∧
      τ'.vars "bA" = τ.vars "sl" ∧
      (∀ z, z ∉ ldNames ++ ["gA", "fA", "lA", "bA"] → τ'.vars z = τ.vars z) ∧
      τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  have hst : stW sc gw fw lw = (sc ++ [gw.length, fw.length, lw.length]) ++ (gw ++ fw ++ lw) := by
    simp [stW, List.append_assoc]
  obtain ⟨τ₁, r₁, hm, hfr, ha, hi, ho⟩ := ldL_run (B := B) ldNames 0 (sc ++ [gw.length, fw.length, lw.length])
    τ (by decide) (by simp [ldNames, scN, hsc])
    (fun i h => by
      rw [hx, hst, List.append_assoc, List.getElem?_append_left (by simpa using h), Nat.zero_add,
        List.getElem?_eq_getElem h])
    (fun v h => hv v (by rw [hst]; exact List.mem_append_left _ h)) (by simp [ldNames, scN]; omega)
  have hm' := hm
  simp only [ldNames, List.map_append, List.map_cons, List.map_nil] at hm'
  have hscL : (scN.map τ₁.vars).length = sc.length := by simp [scN, hsc]
  obtain ⟨h1, h2⟩ := List.append_inj hm' hscL
  simp only [List.cons.injEq, and_true] at h2
  obtain ⟨hg, hf, hl⟩ := h2
  have hsl₁ : τ₁.vars "sl" = τ.vars "sl" := hfr "sl" (by decide)
  refine ⟨((((τ₁.setVar "gA" 14).setVar "fA" (14 + gw.length)).setVar "lA"
    (14 + gw.length + fw.length)).setVar "bA" (τ.vars "sl")), ?_, ?_, by simp [hg], by simp [hf],
    by simp [hl], by simp, by simp, by simp, by simp, fun z hz => ?_, by simp [ha], by simp [hi],
    by simp [ho]⟩
  · unfold ldSc
    refine (Run.seq r₁ (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign
      (ev_add (evalB_lit (by omega)) (ev_var (by simp [hg]) (by omega)) (by omega)))
      (Run.seq (Run.assign (ev_add (ev_var (by simp) (by omega)) (ev_var (by simp [hf])
        (by omega)) (by omega))) (Run.assign (ev_var (by simp [hsl₁]) hsl)))))).mono ?_
    simp [ldNames, scN, Expr.size]
  · rw [← h1]
    apply List.map_congr_left
    intro z hz
    simp only [scN, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [vars_setVar]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [List.mem_append, not_or, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [vars_setVar, if_neg hz.2.1, if_neg hz.2.2.1, if_neg hz.2.2.2.1, if_neg hz.2.2.2.2]
    exact hfr z hz.1

end Lax185574Proofs.MC.Glue
