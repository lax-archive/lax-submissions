import Lax185574Proofs.MC.Glue.Round0
import Lax185574Proofs.Words.TreeWord

/-!
Walking over words in an array, for the rounds of the glue program of
thm:mc.

The scalar `y` is a position in an array `ar`. `skipL ar` moves `y` over
the word of a list of words (a count, then frames `len :: w`), `skipT ar`
over the word of a type tree (the header `k, q, ℓ`, then one list of
atoms and, if `q ≥ 1`, one list of extensions) and `locT ar` over the
first `cv` trees of a sequence of tree words. All of them cost a
constant per entry passed. `walk_run` is the loop over consecutive words
that they share, and `forUp_pot` a counting loop whose rounds cost a
constant per unit of a length that depends on the round.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionModelChecking
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-! ### Words in a row -/

theorem flatten_take_succ (us : List (List ℕ)) {k : ℕ} (hk : k < us.length) :
    (us.take (k + 1)).flatten = (us.take k).flatten ++ us.getD k [] := by
  rw [List.take_succ_eq_append_getElem hk, List.getD_eq_getElem _ _ hk, List.flatten_append,
    List.flatten_singleton]

theorem flatten_take_mono (us : List (List ℕ)) : Monotone fun k => (us.take k).flatten.length := by
  refine monotone_nat_of_le_succ fun k => ?_
  by_cases hk : k < us.length
  · show _ ≤ _
    rw [flatten_take_succ us hk]; simp
  · show _ ≤ _
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem drop_flatten_take {X : List ℕ} {p : ℕ} {us : List (List ℕ)} {r : List ℕ}
    (hX : X.drop p = us.flatten ++ r) {k : ℕ} (hk : k < us.length) :
    X.drop (p + (us.take k).flatten.length) = us.getD k [] ++ ((us.drop (k + 1)).flatten ++ r) := by
  have e : us.flatten = (us.take k).flatten ++ (us.getD k [] ++ (us.drop (k + 1)).flatten) := by
    conv_lhs => rw [← List.take_append_drop k us]
    rw [List.flatten_append, List.drop_eq_getElem_cons hk, List.flatten_cons,
      List.getD_eq_getElem _ _ hk]
  rw [← List.drop_drop, hX, e, List.append_assoc]; simp

theorem flatten_take_add_le (us : List (List ℕ)) {k : ℕ} (hk : k < us.length) :
    (us.take k).flatten.length + (us.getD k []).length ≤ us.flatten.length := by
  have h := flatten_take_mono us (show k + 1 ≤ us.length by omega)
  dsimp only at h
  rw [flatten_take_succ us hk, List.take_length, List.length_append] at h
  exact h

theorem length_le_flatten_words (us : List (List (List ℕ))) :
    us.length ≤ (us.map toWord).flatten.length := by
  induction us with
  | nil => simp
  | cons u us ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, toWord_words]
    omega

/-- **A walk over consecutive words.** The body moves `y` over word `k`
at a cost of at most `c` per entry and `c`, so the loop moves `y` over the
first `N` words. -/
theorem walk_run {B c N : ℕ} {ar i m : String} {body : Com} {X : List ℕ} {p : ℕ}
    {us : List (List ℕ)} {r : List ℕ} {τ : Env}
    (hiw : i ∉ body.wvars) (hmw : m ∉ body.wvars) (hiy : i ≠ "y") (him : i ≠ m)
    (hwa : ar ∉ body.warrs)
    (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hmN : τ.vars m = N) (hN : N ≤ us.length)
    (hXd : X.drop p = us.flatten ++ r) (hB : p + us.flatten.length + N < B)
    (hbody : ∀ k < N, ∀ ρ : Env, ρ.arrs ar = X → ρ.vars "y" = p + (us.take k).flatten.length →
      ρ.vars i = k → ρ.vars m = N →
      ∃ ρ', Run B body ρ ρ' (c * (us.getD k []).length + c) ∧
        ρ'.vars "y" = ρ.vars "y" + (us.getD k []).length) :
    ∃ τ', Run B (forUp i (.var m) body) τ τ' ((c + 8) * ((us.take N).flatten.length + N) + 8) ∧
      τ'.vars "y" = p + (us.take N).flatten.length ∧ τ'.vars i = N := by
  set F : ℕ → ℕ := fun k => (us.take k).flatten.length with hF
  have hFm := flatten_take_mono us
  have hFN : F N ≤ us.flatten.length := by
    have := hFm (show N ≤ us.length from hN)
    simp only [hF, List.take_length] at this ⊢; exact this
  let I : Env → Prop := fun ρ => ρ.arrs ar = X ∧ ρ.vars m = N ∧ ρ.vars i ≤ N ∧
    ρ.vars "y" = p + F (ρ.vars i)
  let Φ : Env → ℕ := fun ρ => c * (F N - F (ρ.vars i)) + (c + 8) * (N - ρ.vars i)
  have hdef : ∀ ρ, I ρ → ∃ v, (Cond.lt (.var i) (.var m)).evalB B ρ = some v := fun ρ hI =>
    evalB_condLt_vars (by have := hI.2.2.1; omega) (by rw [hI.2.1]; omega)
  have hstep : ∀ ρ, I ρ → (Cond.lt (.var i) (.var m)).evalB B ρ = some true →
      ∃ ρ' K, Run B (.seq body (.assign i (.add (.var i) (.lit 1)))) ρ ρ' K ∧ I ρ' ∧
        1 + (Cond.lt (.var i) (.var m)).size + K + Φ ρ' ≤ Φ ρ := by
    intro ρ ⟨hXa, hm, hle, hyy⟩ hc
    have hlt : ρ.vars i < N := by
      have := lt_of_condLt_true hc; rw [hm] at this; exact this
    obtain ⟨ρ₁, r₁, hy₁⟩ := hbody (ρ.vars i) hlt ρ hXa hyy rfl hm
    have hi₁ : ρ₁.vars i = ρ.vars i := r₁.frame_var i hiw
    have hm₁ : ρ₁.vars m = N := by rw [r₁.frame_var m hmw, hm]
    have hX₁ : ρ₁.arrs ar = X := by rw [r₁.frame_arr ar hwa, hXa]
    have hs := flatten_take_succ us (k := ρ.vars i) (by omega)
    have hFs : F (ρ.vars i + 1) = F (ρ.vars i) + (us.getD (ρ.vars i) []).length := by
      simp only [hF]; rw [hs]; simp
    have hF1 : F (ρ.vars i + 1) ≤ F N := hFm (show ρ.vars i + 1 ≤ N by omega)
    refine ⟨ρ₁.setVar i (ρ.vars i + 1), _, Run.seq r₁ (Run.assign (v := ρ.vars i + 1) ?_),
      ⟨by simpa using hX₁, by simp [Ne.symm him, hm₁], by simp; omega, ?_⟩, ?_⟩
    · exact ev_add (ev_var hi₁ (by omega)) (evalB_lit (by omega)) (by omega)
    · have : (ρ₁.setVar i (ρ.vars i + 1)).vars "y" = ρ₁.vars "y" := by simp [Ne.symm hiy]
      have h2 : (ρ₁.setVar i (ρ.vars i + 1)).vars i = ρ.vars i + 1 := by simp
      rw [this, h2, hy₁, hyy, hFs]; omega
    · simp only [Φ, vars_setVar, if_pos rfl, ↓reduceIte, Cond.size, Expr.size]
      generalize hu : (us.getD (ρ.vars i) []).length = u at hFs
      generalize ρ.vars i = k at hFs hF1 hlt
      have e1 : F N - F k = (F N - F (k + 1)) + u := by omega
      have e2 : N - k = (N - (k + 1)) + 1 := by omega
      rw [e1, e2, Nat.mul_add, Nat.mul_add]
      omega
  have hI0 : I (τ.setVar i 0) := ⟨by simpa using hX, by simp [Ne.symm him, hmN], by simp,
    by simp [Ne.symm hiy, hy, hF]⟩
  obtain ⟨σ', K, hr, ⟨-, hm', hle', hy'⟩, hfalse, hK⟩ := Run.while_potential I Φ hdef hstep hI0
  have hiN : σ'.vars i = N := by
    have := le_of_condLt_false hfalse; rw [hm'] at this; omega
  refine ⟨σ', ?_, by rw [hy', hiN], hiN⟩
  unfold forUp
  refine (Run.seq (Run.assign (evalB_lit (by omega))) hr).mono ?_
  simp only [Φ, vars_setVar, if_pos rfl, ↓reduceIte, Cond.size, Expr.size] at hK ⊢
  have hF0 : F 0 = 0 := by simp [hF]
  rw [hF0, Nat.sub_zero, Nat.sub_zero] at hK
  have hK' : K ≤ c * F N + (c + 8) * N + 4 := by omega
  have : c * F N ≤ (c + 8) * F N := Nat.mul_le_mul_right _ (by omega)
  show 1 + 1 + K ≤ (c + 8) * (F N + N) + 8
  rw [Nat.mul_add]; omega

/-! ### A list of words -/

/-- Move `y` over the list of words at `y` in `ar`. -/
def skipL (ar : String) : Com :=
  .seq (.assign "e1" (.get ar (.var "y"))) (.seq (.assign "y" (.add (.var "y") (.lit 1)))
    (.seq (.assign "e2" (.lit 0)) (.while (.lt (.var "e2") (.var "e1"))
      (.seq (.assign "y" (.add (.add (.var "y") (.get ar (.var "y"))) (.lit 1)))
        (.assign "e2" (.add (.var "e2") (.lit 1)))))))

theorem getElem?_of_drop {X : List ℕ} {p a : ℕ} {r : List ℕ} (h : X.drop p = a :: r) :
    X[p]? = some a := by
  have h2 := congrArg (fun l => l[0]?) h
  simpa [List.getElem?_drop] using h2

theorem length_le_frames (ws : List (List ℕ)) : ws.length ≤ (frames ws).length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have : frames (w :: ws) = (w.length :: w) ++ frames ws := rfl
    rw [this]; simp; omega

theorem skipL_run {B : ℕ} {ar : String} {X : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hx : X.drop p = toWord ws ++ r)
    (hB : p + (toWord ws).length < B) :
    ∃ τ', Run B (skipL ar) τ τ' (20 * (toWord ws).length + 20) ∧
      τ'.vars "y" = p + (toWord ws).length := by
  obtain ⟨h0, hpos, hfr, hend, -⟩ := listAt hx
  have hlen : (toWord ws).length = 1 + (frames ws).length := by rw [toWord_words]; simp; omega
  have hwl : ws.length ≤ (frames ws).length := length_le_frames ws
  have hFP : ∀ j ≤ ws.length, frPos X p j ≤ p + (toWord ws).length := fun j hj => by
    have := (frPos_le_listEnd hx (j := j) (by rw [h0]; exact hj)).2.1; rw [hend] at this; exact this
  let I : Env → Prop := fun ρ => ρ.arrs ar = X ∧ ρ.vars "e1" = ws.length ∧
    ρ.vars "e2" ≤ ws.length ∧ ρ.vars "y" = frPos X p (ρ.vars "e2")
  have hdef : ∀ ρ, I ρ → ∃ v, (Cond.lt (.var "e2") (.var "e1")).evalB B ρ = some v := fun ρ hI =>
    evalB_condLt_vars (by have := hI.2.2.1; have := hFP 0 (by omega); have := hpos 0 (by omega); omega)
      (by rw [hI.2.1]; have := hFP 0 (by omega); have := hpos 0 (by omega); omega)
  have hstep : ∀ ρ, I ρ → (Cond.lt (.var "e2") (.var "e1")).evalB B ρ = some true →
      ∃ ρ', Run B (.seq (.assign "y" (.add (.add (.var "y") (.get ar (.var "y"))) (.lit 1)))
        (.assign "e2" (.add (.var "e2") (.lit 1)))) ρ ρ' 12 ∧ I ρ' ∧
        ws.length - ρ'.vars "e2" < ws.length - ρ.vars "e2" := by
    intro ρ ⟨hXa, he1, hle, hyy⟩ hc
    have hlt : ρ.vars "e2" < ws.length := by
      have := lt_of_condLt_true hc; rw [he1] at this; exact this
    obtain ⟨hx1, -, -⟩ := hfr _ hlt
    have hs : frPos X p (ρ.vars "e2" + 1) = frPos X p (ρ.vars "e2") + 1 +
        xg X (frPos X p (ρ.vars "e2")) := skipFr_succ' _ _ _
    have hF1 := hFP (ρ.vars "e2" + 1) (by omega)
    obtain ⟨-, hd⟩ := hpos _ hlt.le
    rw [frames_drop hlt] at hd
    have hget : X[frPos X p (ρ.vars "e2")]? = some ws[ρ.vars "e2"].length := getElem?_of_drop
      (by rw [hd]; rfl)
    rw [hx1] at hs
    refine ⟨(ρ.setVar "y" (frPos X p (ρ.vars "e2") + ws[ρ.vars "e2"].length + 1)).setVar "e2"
      (ρ.vars "e2" + 1), (Run.seq (Run.assign ?_) (Run.assign ?_)).mono (by simp [Expr.size]),
      ⟨by simpa using hXa, by simp [he1], by simp; omega, ?_⟩, by simp; omega⟩
    · exact ev_add (ev_add (ev_var hyy (by omega)) (evalB_get (ev_var hyy (by omega))
        (by rw [hXa]; exact hget) (by omega)) (by omega)) (evalB_lit (by omega)) (by omega)
    · exact ev_add (ev_var (by simp) (by omega)) (evalB_lit (by omega)) (by omega)
    · simp only [vars_setVar, if_pos rfl]; simp; omega
  have hp0 := hpos 0 (by omega)
  simp only [List.take_zero, frames, List.map_nil, List.flatten_nil, List.length_nil] at hp0
  have hget0 : X[p]? = some ws.length := getElem?_of_drop (by rw [hx, toWord_words]; rfl)
  set τ₁ := ((τ.setVar "e1" ws.length).setVar "y" (p + 1)).setVar "e2" 0 with hτ₁
  have hI1 : I τ₁ := ⟨by simp [hτ₁, hX], by simp [hτ₁], by simp [hτ₁], by simp [hτ₁, hp0.1]⟩
  obtain ⟨σ', hr, ⟨-, -, hle', hy'⟩, hfalse⟩ := Run.while_count I
    (fun ρ => ws.length - ρ.vars "e2") 12 hdef hstep hI1
  have he2 : σ'.vars "e2" = ws.length := by
    have := le_of_condLt_false hfalse
    have h1 : σ'.vars "e1" = τ₁.vars "e1" := hr.frame_var "e1" (by simp [Com.wvars])
    rw [h1, hI1.2.1] at this; omega
  refine ⟨σ', ?_, ?_⟩
  · unfold skipL
    refine (Run.seq (Run.assign (evalB_get (ev_var hy (by omega)) (by rw [hX]; exact hget0)
      (by omega))) (Run.seq (Run.assign (ev_add (ev_var (by simp [hy]) (by omega))
      (evalB_lit (by omega)) (by omega))) (Run.seq (Run.assign (evalB_lit (by omega))) hr))).mono ?_
    simp only [Expr.size, Cond.size]
    have : ws.length - τ₁.vars "e2" = ws.length := by simp [hτ₁]
    rw [this]; omega
  · rw [hy', he2]
    have := (hpos ws.length le_rfl).1
    rw [List.take_length] at this
    rw [this, hlen]; omega

/-! ### A type tree -/

/-- Move `y` over the word of the type tree at `y` in `ar`. -/
def skipT (ar : String) : Com :=
  .seq (.assign "e3" (.get ar (.add (.var "y") (.lit 1))))
    (.seq (.assign "y" (.add (.var "y") (.lit 3)))
      (.seq (skipL ar) (.ite (.eq (.var "e3") (.lit 0)) .skip (skipL ar))))

theorem toWord_typeTree_split (t : TypeTree) : toWord t = [t.k, t.q, t.ℓ] ++ toWord t.root := rfl

theorem skipT_run' {B : ℕ} {ar : String} {X : List ℕ} {p : ℕ} {t : TypeTree} {r : List ℕ}
    {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hx : X.drop p = toWord t ++ r)
    (hB : p + (toWord t).length < B) (hXv : ∀ v ∈ toWord t, v < B) :
    ∃ τ', Run B (skipT ar) τ τ' (40 * (toWord t).length + 60) ∧
      τ'.vars "y" = p + (toWord t).length := by
  obtain ⟨k, q, ℓ, root⟩ := t
  have hqB : q < B := hXv q (by simp [toWord_typeTree_split])
  rw [toWord_typeTree_split] at hx hB ⊢
  simp only [List.cons_append, List.nil_append, List.length_cons] at hB ⊢
  have hq : X[p + 1]? = some q := by
    have := congrArg (fun l => l[1]?) hx
    simpa [List.getElem?_drop] using this
  have hr : X.drop (p + 3) = toWord root ++ r := by
    rw [← List.drop_drop, hx]; rfl
  set τ₁ := (τ.setVar "e3" q).setVar "y" (p + 3) with hτ₁
  have ra : Run B (.assign "e3" (.get ar (.add (.var "y") (.lit 1)))) τ (τ.setVar "e3" q) 5 :=
    (Run.assign (evalB_get (ev_add (ev_var hy (by omega)) (evalB_lit (by omega))
      (by omega)) (by rw [hX]; exact hq) hqB)).mono (by simp [Expr.size])
  have rb : Run B (.assign "y" (.add (.var "y") (.lit 3))) (τ.setVar "e3" q) τ₁ 4 :=
    (Run.assign (ev_add (ev_var (by simp [hy]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have hX₁ : τ₁.arrs ar = X := by simp [hτ₁, hX]
  have hy₁ : τ₁.vars "y" = p + 3 := by simp [hτ₁]
  cases q with
  | zero =>
    rw [toWord_node_zero] at hr hB ⊢
    obtain ⟨τ₂, r₂, hy₂⟩ := skipL_run (B := B) hX₁ hy₁ hr (by omega)
    have he3 : τ₂.vars "e3" = 0 := by rw [r₂.frame_var "e3" (by simp [skipL, Com.wvars])]; simp [hτ₁]
    refine ⟨τ₂, ?_, by rw [hy₂]; omega⟩
    unfold skipT
    refine (Run.seq ra (Run.seq rb (Run.seq r₂ (Run.ite_true
      (by rw [condEq_lit he3 (by omega) (by omega)]; rfl) Run.skip)))).mono ?_
    simp only [Cond.size, Expr.size]; omega
  | succ h =>
    obtain ⟨h1, -⟩ := nodeSplit hr
    rw [toWord_node_succ] at hB ⊢
    simp only [List.length_append] at hB ⊢
    obtain ⟨τ₂, r₂, hy₂⟩ := skipL_run (B := B) hX₁ hy₁ h1 (by omega)
    have h2 : X.drop (p + 3 + (toWord (TreeAlgo.Node.atoms root).words).length) =
        toWord (TreeAlgo.Node.exts root).words ++ r := by
      rw [← List.drop_drop, h1]; simp
    have hX₂ : τ₂.arrs ar = X := by rw [r₂.frame_arr ar (by simp [skipL, Com.warrs]), hX₁]
    obtain ⟨τ₃, r₃, hy₃⟩ := skipL_run (B := B) hX₂ hy₂ h2 (by omega)
    have he3 : τ₂.vars "e3" = h + 1 := by rw [r₂.frame_var "e3" (by simp [skipL, Com.wvars])]; simp [hτ₁]
    refine ⟨τ₃, ?_, by rw [hy₃]; omega⟩
    unfold skipT
    refine (Run.seq ra (Run.seq rb (Run.seq r₂ (Run.ite_false
      (by rw [condEq_lit he3 (by omega) (by omega), decide_eq_false (by omega)]) r₃)))).mono ?_
    simp only [Cond.size, Expr.size]; omega

theorem skipT_run {B : ℕ} {ar : String} {X : List ℕ} {p : ℕ} {t : TypeTree} {r : List ℕ}
    {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hx : X.drop p = toWord t ++ r)
    (hB : p + (toWord t).length < B) (hXv : ∀ v ∈ X, v < B) :
    ∃ τ', Run B (skipT ar) τ τ' (40 * (toWord t).length + 60) ∧
      τ'.vars "y" = p + (toWord t).length :=
  skipT_run' hX hy hx hB fun v hv => hXv v (List.mem_of_mem_drop (by rw [hx]; simp [hv]))

/-! ### Trees in a row -/

/-- Move `y` over `cv` tree words. -/
def locT (ar : String) : Com := forUp "e4" (.var "cv") (skipT ar)

theorem locT_run {B i : ℕ} {ar : String} {X : List ℕ} {p : ℕ} {ts : List TypeTree} {r : List ℕ}
    {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hcv : τ.vars "cv" = i)
    (hi : i ≤ ts.length) (hx : X.drop p = (ts.map toWord).flatten ++ r)
    (hB : p + (ts.map toWord).flatten.length + i < B) (hXv : ∀ v ∈ X, v < B) :
    ∃ τ', Run B (locT ar) τ τ' (108 * (((ts.map toWord).take i).flatten.length + i) + 8) ∧
      τ'.vars "y" = p + (((ts.map toWord).take i).flatten.length) ∧ τ'.vars "e4" = i := by
  have hl : (ts.map toWord).length = ts.length := List.length_map _
  refine walk_run (c := 100) (by simp [skipT, skipL, Com.wvars]) (by simp [skipT, skipL, Com.wvars])
    (by decide) (by decide) (by simp [skipT, skipL, Com.warrs]) hX hy hcv (by omega) hx hB ?_
  intro k hk ρ hXρ hyρ _ _
  have hd := drop_flatten_take hx (k := k) (by omega)
  have hg : (ts.map toWord).getD k [] = toWord ts[k] := by
    rw [List.getD_eq_getElem _ _ (by omega)]; simp
  have hle := flatten_take_add_le (ts.map toWord) (k := k) (by omega)
  rw [hg] at hd hle ⊢
  obtain ⟨ρ', r', hy'⟩ := skipT_run (B := B) (t := ts[k]) hXρ hyρ hd (by omega) hXv
  exact ⟨ρ', r'.mono (by omega), by rw [hy', hyρ]⟩

/-! ### Counting loops with a potential -/

/-- **A counting loop with a potential.** Round `k` costs at most
`c (len k) + c`, so the loop costs a constant per unit of the sum of the
lengths and per round. -/
theorem forUp_pot {B : ℕ} {i : String} {e : Expr} {body : Com} {N c : ℕ} (len : ℕ → ℕ)
    (I : ℕ → Env → Prop) {σ : Env} (hN : N < B)
    (he : ∀ k ≤ N, ∀ τ, I k τ → τ.vars i = k → e.evalB B τ = some N)
    (h0 : I 0 (σ.setVar i 0))
    (hstep : ∀ k < N, ∀ τ, I k τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' (c * len k + c) ∧ τ'.vars i = k ∧ I (k + 1) (τ'.setVar i (k + 1))) :
    ∃ σ', Run B (forUp i e body) σ σ'
        ((c + e.size + 7) * ((∑ k ∈ Finset.range N, len k) + N) + e.size + 5) ∧
      I N σ' ∧ σ'.vars i = N := by
  set S : ℕ → ℕ := fun k => ∑ j ∈ Finset.range k, len j with hSd
  have hS : ∀ k, S (k + 1) = S k + len k := fun k => Finset.sum_range_succ _ _
  have hSm : Monotone S := monotone_nat_of_le_succ fun k => by rw [hS]; omega
  set C := c + e.size + 7 with hC
  let J : Env → Prop := fun τ => ∃ k ≤ N, τ.vars i = k ∧ I k τ
  let Φ : Env → ℕ := fun τ => C * ((S N - S (τ.vars i)) + (N - τ.vars i))
  obtain ⟨σ', K, hrun, ⟨k, hk, hik, hI⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var i) e)
      (c := .seq body (.assign i (.add (.var i) (.lit 1)))) J Φ
      (fun τ ⟨k, hk, hik, hI⟩ => ⟨_, evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)⟩)
      (by
        rintro τ ⟨k, hk, hik, hI⟩ hc
        have hkN : k < N := by
          rw [evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)] at hc
          simp only [Option.some.injEq, decide_eq_true_eq] at hc
          omega
        obtain ⟨τ', hr, hi', hI'⟩ := hstep k hkN τ hI hik
        refine ⟨τ'.setVar i (k + 1), _, (Run.seq hr (Run.assign (v := k + 1) ?_)),
          ⟨k + 1, hkN, by simp, hI'⟩, ?_⟩
        · simp [hi']; omega
        · simp only [Φ, vars_setVar, ↓reduceIte, hik, Cond.size, Expr.size]
          have h1 := hS k
          have h2 : S (k + 1) ≤ S N := hSm (show k + 1 ≤ N by omega)
          have e1 : S N - S k = (S N - S (k + 1)) + len k := by omega
          have e2 : N - k = (N - (k + 1)) + 1 := by omega
          rw [e1, e2]
          have : C * (S N - S (k + 1) + len k + (N - (k + 1) + 1)) =
              C * (S N - S (k + 1) + (N - (k + 1))) + C * len k + C := by ring
          rw [this]
          have h3 : c * len k ≤ C * len k := Nat.mul_le_mul_right _ (by omega)
          omega)
      (show J (σ.setVar i 0) from ⟨0, Nat.zero_le _, by simp, h0⟩)
  have hkN : k = N := by
    rw [evalB_condLt (evalB_var (by omega)) (he k hk σ' hI hik)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hkN] at hI hik
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hI, hik⟩
  simp only [Φ, vars_setVar, ↓reduceIte, Cond.size, Expr.size] at hK ⊢
  have hS0 : S 0 = 0 := by simp [hSd]
  rw [hS0, Nat.sub_zero, Nat.sub_zero] at hK
  have : C * (S N + N) = C * (∑ k ∈ Finset.range N, len k + N) := rfl
  omega

end Lax185574Proofs.MC.Glue
