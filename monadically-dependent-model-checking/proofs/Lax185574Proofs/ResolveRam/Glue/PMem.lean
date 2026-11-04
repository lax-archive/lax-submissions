import Lax185574Proofs.ResolveRam.Glue.FilterCp

/-!
Looking up a short word in a list of words held in an array.

The list of words `ws` is stored as its word `|ws|` followed by the frames
of the words, from position `p` of the array `A`. The target is a word `t`
of length three or four, given by the scalars `mL` (its length) and
`m0`, …, `m3` (its entries). `memScan A` sets `mb` to `1` if `t` is one of
the words and to `0` otherwise (`memScan_run`). It reads no input, writes
no array and no output, and writes only the scalars `mV`. The atoms of a
node are such a list, so this is the test `inW` of the atom words.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- The last comparison of a frame: a target of length three matches,
one of length four needs its entry `3`. -/
def memLast (A : String) : Com :=
  .ite (.eq (.var "tmL") (.lit 3)) (.assign "tmb" (.lit 1))
    (.ite (.eq (.get A (.add (.var "tmf") (.lit 4))) (.var "tm3")) (.assign "tmb" (.lit 1)) .skip)

/-- Compare the frame at `mf` with the target. -/
def memMatch (A : String) : Com :=
  .ite (.eq (.get A (.var "tmf")) (.var "tmL"))
    (.ite (.eq (.get A (.add (.var "tmf") (.lit 1))) (.var "tm0"))
      (.ite (.eq (.get A (.add (.var "tmf") (.lit 2))) (.var "tm1"))
        (.ite (.eq (.get A (.add (.var "tmf") (.lit 3))) (.var "tm2")) (memLast A) .skip) .skip) .skip)
    .skip

/-- Test one frame and move to the next. -/
def memBody (A : String) : Com :=
  .seq (memMatch A) (.assign "tmf" (.add (.add (.var "tmf") (.get A (.var "tmf"))) (.lit 1)))

/-- Look up the target in the list of words at `mp` of `A`. -/
def memScan (A : String) : Com :=
  .seq (.assign "tmb" (.lit 0)) (.seq (.assign "tmf" (.add (.var "tmp") (.lit 1)))
    (.seq (.assign "tmn" (.get A (.var "tmp"))) (forUp "tmj" (.var "tmn") (memBody A))))

/-- The scalars that `memScan` writes. -/
def mV : List String := ["tmb", "tmf", "tmn", "tmj"]

theorem memScan_wvars (A : String) : ∀ y ∈ (memScan A).wvars, y ∈ mV := by
  intro y hy
  simp [memScan, memBody, memMatch, memLast, forUp, Com.wvars] at hy
  simp [mV]; tauto

theorem memScan_warrs (A : String) : (memScan A).warrs = [] := by
  simp [memScan, memBody, memMatch, memLast, forUp, Com.warrs]

theorem memScan_reads (A : String) : ¬ (memScan A).reads := by
  simp [memScan, memBody, memMatch, memLast, forUp, Com.reads]

theorem memScan_noWrite (A : String) : (memScan A).NoWrite := by
  simp [memScan, memBody, memMatch, memLast, forUp, Com.NoWrite]

/-- A run of a command that writes no array, reads nothing and writes
nothing keeps the arrays and the tapes, and the scalars outside its
written names. -/
theorem run_frame {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (ha : c.warrs = []) (hr : ¬ c.reads) (hw : c.NoWrite) :
    σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp :=
  ⟨funext fun a => h.frame_arr a (by rw [ha]; simp), h.out_eq hw, h.frame_inp hr⟩

/-- The target word given by the scalars. -/
def TargetAt (t : List ℕ) (τ : Env) : Prop :=
  (t.length = 3 ∨ t.length = 4) ∧ τ.vars "tmL" = t.length ∧ τ.vars "tm0" = t.getD 0 0 ∧
    τ.vars "tm1" = t.getD 1 0 ∧ τ.vars "tm2" = t.getD 2 0 ∧ (t.length = 4 → τ.vars "tm3" = t.getD 3 0)

theorem TargetAt.congr {t : List ℕ} {τ τ' : Env} (h : TargetAt t τ)
    (hv : ∀ y ∈ ["tmL", "tm0", "tm1", "tm2", "tm3"], τ'.vars y = τ.vars y) : TargetAt t τ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_, fun h => ?_⟩
  · rw [hv "tmL" (by simp), h2]
  · rw [hv "tm0" (by simp), h3]
  · rw [hv "tm1" (by simp), h4]
  · rw [hv "tm2" (by simp), h5]
  · rw [hv "tm3" (by simp), h6 h]

/-- Two words of length three or four agree if their lengths and entries do. -/
theorem eq_of_getD {w t : List ℕ} (ht : t.length = 3 ∨ t.length = 4) (hl : w.length = t.length)
    (h0 : w.getD 0 0 = t.getD 0 0) (h1 : w.getD 1 0 = t.getD 1 0) (h2 : w.getD 2 0 = t.getD 2 0)
    (h3 : t.length = 4 → w.getD 3 0 = t.getD 3 0) : w = t := by
  apply List.ext_getElem hl
  intro i hi hi'
  have e : ∀ j (hj : j < w.length) (hj' : j < t.length), w.getD j 0 = t.getD j 0 → w[j] = t[j] :=
    fun j hj hj' h => by
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h; exact h
  rcases ht with ht | ht
  · have : i < 3 := by omega
    interval_cases i
    · exact e 0 hi hi' h0
    · exact e 1 hi hi' h1
    · exact e 2 hi hi' h2
  · have : i < 4 := by omega
    interval_cases i
    · exact e 0 hi hi' h0
    · exact e 1 hi hi' h1
    · exact e 2 hi hi' h2
    · exact e 3 hi hi' (h3 ht)

theorem getElem?_of_drop {X : List ℕ} {f : ℕ} {u : List ℕ} (h : X.drop f = u) {i : ℕ}
    (hi : i < u.length) : X[f + i]? = some u[i] := by
  rw [← List.getElem?_drop, h, List.getElem?_eq_getElem hi]

theorem bqT {a b : ℕ} (h : a = b) : some (a == b) = some true := by simp [h]

theorem bqF {a b : ℕ} (h : ¬ a = b) : some (a == b) = some false := by simp [h]

/-- **One frame.** -/
theorem memBody_run {B : ℕ} {A : String} {X : List ℕ} {f : ℕ} {w r t : List ℕ} {τ : Env}
    (hX : τ.arrs A = X) (hdr : X.drop f = w.length :: (w ++ r)) (hf : τ.vars "tmf" = f)
    (ht : TargetAt t τ) (htB : ∀ v ∈ t, v < B) (hB : 5 < B) (hfB : f + 1 + w.length < B)
    (hv : ∀ v ∈ w.length :: w, v < B) :
    ∃ τ', Run B (memBody A) τ τ' 60 ∧ τ'.vars "tmf" = f + 1 + w.length ∧
      τ'.vars "tmb" = (if w = t then 1 else τ.vars "tmb") ∧
      (∀ y, y ≠ "tmf" → y ≠ "tmb" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs := by
  obtain ⟨htl, hL, h0, h1, h2, h3⟩ := ht
  have gX : ∀ i (hi : i < (w.length :: (w ++ r)).length), X[f + i]? =
      some (w.length :: (w ++ r))[i] := fun i hi => getElem?_of_drop hdr hi
  have hmem : ∀ i (hi : i < (w.length :: (w ++ r)).length), i < w.length + 1 →
      (w.length :: (w ++ r))[i] < B := by
    intro i hi hi2
    rcases i with _ | k
    · simpa using hv _ (List.mem_cons_self ..)
    · simp only [List.getElem_cons_succ]
      rw [List.getElem_append_left (by omega)]
      exact hv _ (List.mem_cons_of_mem _ (List.getElem_mem _))
  have g0 : ∀ τ' : Env, τ'.vars "tmf" = f → τ'.arrs A = X →
      (Expr.get A (.var "tmf")).evalB B τ' = some w.length := fun τ' hf' hX' =>
    evalB_get (ev_var hf' (by omega)) (by rw [hX']; simpa using gX 0 (by simp))
      (by simpa using hmem 0 (by simp) (by omega))
  have gk : ∀ k j, j = k + 1 → ∀ (hk : k < w.length),
      (Expr.get A (.add (.var "tmf") (.lit j))).evalB B τ = some w[k] := fun k j hj hk => by
    subst hj
    have hk' : k + 1 < (w.length :: (w ++ r)).length := by simp; omega
    have e1 := gX (k + 1) hk'
    have e2 := hmem (k + 1) hk' (by omega)
    simp only [List.getElem_cons_succ, List.getElem_append_left hk] at e1 e2
    exact evalB_get (ev_add (ev_var hf (by omega)) (evalB_lit (by omega)) (by omega))
      (by rw [hX]; exact e1) e2
  have tB : ∀ j, t.getD j 0 < B := fun j => by
    rw [List.getD_eq_getElem?_getD]
    cases h : t[j]? with
    | none => simp; omega
    | some v => simpa using htB v (List.mem_of_getElem? h)
  have eM : ∀ τ' : Env, τ'.vars "tmf" = f → τ'.arrs A = X →
      (Expr.add (.add (.var "tmf") (.get A (.var "tmf"))) (.lit 1)).evalB B τ' =
        some (f + w.length + 1) := fun τ' hf' hX' => by
    have a1 : (Expr.var "tmf").evalB B τ' = some f := ev_var hf' (by omega)
    have a2 : (Expr.add (.var "tmf") (.get A (.var "tmf"))).evalB B τ' = some (f + w.length) :=
      ev_add a1 (g0 τ' hf' hX') (by omega)
    exact ev_add a2 (evalB_lit (by omega)) (by omega)
  have rmv : Run B (.assign "tmf" (.add (.add (.var "tmf") (.get A (.var "tmf"))) (.lit 1))) τ
      (τ.setVar "tmf" (f + w.length + 1)) 7 :=
    (Run.assign (eM τ hf hX)).mono (by simp [Expr.size])
  have rmv1 : Run B (.assign "tmf" (.add (.add (.var "tmf") (.get A (.var "tmf"))) (.lit 1)))
      (τ.setVar "tmb" 1) ((τ.setVar "tmb" 1).setVar "tmf" (f + w.length + 1)) 7 :=
    (Run.assign (eM _ (by simp [hf]) (by simp [hX]))).mono (by simp [Expr.size])
  have cE : ∀ (e : Expr) (x : String) (a b : ℕ), e.evalB B τ = some a → τ.vars x = b → b < B →
      (Cond.eq e (.var x)).evalB B τ = some (a == b) := fun e x a b he hx hb =>
    evalB_condEq he (ev_var hx hb)
  -- no match: skip, then move
  have miss : w ≠ t → ∀ K, Run B (memMatch A) τ τ K →
      ∃ τ', Run B (memBody A) τ τ' (K + 7) ∧ τ'.vars "tmf" = f + 1 + w.length ∧
        τ'.vars "tmb" = (if w = t then 1 else τ.vars "tmb") ∧
        (∀ y, y ≠ "tmf" → y ≠ "tmb" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs := fun hne K hr =>
    ⟨_, Run.seq hr rmv, by simp; omega, by simp [hne], fun y hy _ => by simp [hy], by simp⟩
  have hit : w = t → Run B (memMatch A) τ (τ.setVar "tmb" 1) 50 →
      ∃ τ', Run B (memBody A) τ τ' 60 ∧ τ'.vars "tmf" = f + 1 + w.length ∧
        τ'.vars "tmb" = (if w = t then 1 else τ.vars "tmb") ∧
        (∀ y, y ≠ "tmf" → y ≠ "tmb" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs := fun he hr =>
    ⟨_, (Run.seq hr rmv1).mono (by omega), by simp; omega, by simp [he], fun y hy hy' => by simp [hy, hy'],
      by simp⟩
  have c0 := cE _ "tmL" _ _ (g0 τ hf hX) hL (by omega)
  by_cases e0 : w.length = t.length
  · have hw3 : 3 ≤ w.length := by omega
    have c1 := cE _ "tm0" _ _ (gk 0 1 rfl (by omega)) h0 (tB 0)
    have c2 := cE _ "tm1" _ _ (gk 1 2 rfl (by omega)) h1 (tB 1)
    have c3 := cE _ "tm2" _ _ (gk 2 3 rfl (by omega)) h2 (tB 2)
    have w0 : w.getD 0 0 = w[0] := List.getD_eq_getElem _ _ (by omega)
    have w1 : w.getD 1 0 = w[1] := List.getD_eq_getElem _ _ (by omega)
    have w2 : w.getD 2 0 = w[2] := List.getD_eq_getElem _ _ (by omega)
    by_cases e1 : w[0] = t.getD 0 0
    · by_cases e2 : w[1] = t.getD 1 0
      · by_cases e3 : w[2] = t.getD 2 0
        · have hpre : ∀ K, Run B (memLast A) τ (τ.setVar "tmb" 1) K →
              Run B (memMatch A) τ (τ.setVar "tmb" 1) (K + 4 * 8) := fun K hr => by
            unfold memMatch
            refine (Run.ite_true (by rw [c0]; exact bqT e0) (Run.ite_true (by rw [c1]; exact bqT e1)
              (Run.ite_true (by rw [c2]; exact bqT e2) (Run.ite_true (by rw [c3]; exact bqT e3) hr)))).mono ?_
            simp [Cond.size, Expr.size]; omega
          have cL := evalB_condEq (B := B) (σ := τ) (ev_var hL (by omega)) (evalB_lit (n := 3) (by omega))
          by_cases e4 : t.length = 3
          · have he : w = t := eq_of_getD htl e0 (by rw [w0, e1]) (by rw [w1, e2]) (by rw [w2, e3])
              (fun h => absurd h (by omega))
            refine hit he ((hpre 10 ?_).mono (by omega))
            unfold memLast
            exact (Run.ite_true (by rw [cL]; exact bqT e4) (Run.assign (evalB_lit (by omega)))).mono
              (by simp [Cond.size, Expr.size])
          · have e4' : t.length = 4 := by omega
            have c4 := cE _ "tm3" _ _ (gk 3 4 rfl (by omega)) (h3 e4') (tB 3)
            have w3 : w.getD 3 0 = w[3]'(by omega) := List.getD_eq_getElem _ _ (by omega)
            by_cases e5 : w[3]'(by omega) = t.getD 3 0
            · have he : w = t := eq_of_getD htl e0 (by rw [w0, e1]) (by rw [w1, e2]) (by rw [w2, e3])
                (fun _ => by rw [w3, e5])
              refine hit he ((hpre 18 ?_).mono (by omega))
              unfold memLast
              refine (Run.ite_false (by rw [cL]; exact bqF e4) (Run.ite_true (by rw [c4]; exact bqT e5)
                (Run.assign (evalB_lit (by omega))))).mono ?_
              simp [Cond.size, Expr.size]
            · have hne : w ≠ t := fun h => e5 (by rw [← w3, h])
              obtain ⟨τ', r', h'⟩ := miss hne 50 (by
                unfold memMatch memLast
                refine (Run.ite_true (by rw [c0]; exact bqT e0) (Run.ite_true (by rw [c1]; exact bqT e1)
                  (Run.ite_true (by rw [c2]; exact bqT e2) (Run.ite_true (by rw [c3]; exact bqT e3)
                    (Run.ite_false (by rw [cL]; exact bqF e4) (Run.ite_false (by rw [c4]; exact bqF e5)
                      Run.skip)))))).mono ?_
                simp [Cond.size, Expr.size])
              exact ⟨τ', r'.mono (by omega), h'⟩
        · have hne : w ≠ t := fun h => e3 (by rw [← w2, h])
          obtain ⟨τ', r', h'⟩ := miss hne 50 (by
            unfold memMatch
            refine (Run.ite_true (by rw [c0]; exact bqT e0) (Run.ite_true (by rw [c1]; exact bqT e1)
              (Run.ite_true (by rw [c2]; exact bqT e2) (Run.ite_false (by rw [c3]; exact bqF e3)
                Run.skip)))).mono ?_
            simp [Cond.size, Expr.size])
          exact ⟨τ', r'.mono (by omega), h'⟩
      · have hne : w ≠ t := fun h => e2 (by rw [← w1, h])
        obtain ⟨τ', r', h'⟩ := miss hne 50 (by
          unfold memMatch
          refine (Run.ite_true (by rw [c0]; exact bqT e0) (Run.ite_true (by rw [c1]; exact bqT e1)
            (Run.ite_false (by rw [c2]; exact bqF e2) Run.skip))).mono ?_
          simp [Cond.size, Expr.size])
        exact ⟨τ', r'.mono (by omega), h'⟩
    · have hne : w ≠ t := fun h => e1 (by rw [← w0, h])
      obtain ⟨τ', r', h'⟩ := miss hne 50 (by
        unfold memMatch
        refine (Run.ite_true (by rw [c0]; exact bqT e0) (Run.ite_false (by rw [c1]; exact bqF e1)
          Run.skip)).mono ?_
        simp [Cond.size, Expr.size])
      exact ⟨τ', r'.mono (by omega), h'⟩
  · have hne : w ≠ t := fun h => e0 (by rw [h])
    obtain ⟨τ', r', h'⟩ := miss hne 50 (by
      unfold memMatch
      refine (Run.ite_false (by rw [c0]; exact bqF e0) Run.skip).mono ?_
      simp [Cond.size, Expr.size])
    exact ⟨τ', r'.mono (by omega), h'⟩

theorem take_succ_mem {ws : List (List ℕ)} {k : ℕ} (hk : k < ws.length) (t : List ℕ) :
    (t ∈ ws.take (k + 1)) = (t ∈ ws.take k ∨ ws[k] = t) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton, eq_iff_iff]
  exact or_congr_right eq_comm

theorem frames_split (ws : List (List ℕ)) (k : ℕ) :
    frames ws = frames (ws.take k) ++ frames (ws.drop k) := by
  rw [← frames_append, List.take_append_drop]

theorem frames_take_le (ws : List (List ℕ)) (k : ℕ) :
    (frames (ws.take k)).length ≤ (frames ws).length := by
  rw [frames_split ws k, List.length_append]; omega

theorem frame_mem {ws : List (List ℕ)} {k : ℕ} (hk : k < ws.length) :
    ∀ v ∈ ws[k].length :: ws[k], v ∈ toWord ws := by
  intro v hv
  rw [toWord_words, frames_split ws k, frames_drop hk]
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  rcases List.mem_cons.1 hv with h | h
  · rw [h]; exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

/-- **Looking up a word.** -/
theorem memScan_run {B : ℕ} {A : String} {X : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r t : List ℕ}
    {σ : Env} (hX : σ.arrs A = X) (hdr : X.drop p = toWord ws ++ r) (hp : σ.vars "tmp" = p)
    (ht : TargetAt t σ) (htB : ∀ v ∈ t, v < B) (hB : 5 < B) (hpB : p + (toWord ws).length + 2 < B)
    (hv : ∀ v ∈ toWord ws, v < B) :
    ∃ σ', Run B (memScan A) σ σ' (70 * ws.length + 30) ∧
      σ'.vars "tmb" = (if t ∈ ws then 1 else 0) ∧ (∀ y, y ∉ mV → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  obtain ⟨h0, hpos, -, -, -⟩ := listAt hdr
  have hwl : ws.length < (toWord ws).length := by
    rw [toWord_words, List.length_cons, length_frames]; omega
  have g0 : X[p]? = some ws.length := by
    have := getElem?_of_drop hdr (i := 0) (by simp; omega)
    simpa [toWord_words] using this
  set σ1 := ((σ.setVar "tmb" 0).setVar "tmf" (p + 1)).setVar "tmn" ws.length
  have r1a : Run B (.assign "tmb" (.lit 0)) σ (σ.setVar "tmb" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have r1b : Run B (.assign "tmf" (.add (.var "tmp") (.lit 1))) (σ.setVar "tmb" 0)
      ((σ.setVar "tmb" 0).setVar "tmf" (p + 1)) 4 :=
    (Run.assign (ev_add (ev_var (v := p) (by simp [hp]) (by omega)) (evalB_lit (by omega))
      (by omega))).mono (by simp [Expr.size])
  have r1c : Run B (.assign "tmn" (.get A (.var "tmp"))) ((σ.setVar "tmb" 0).setVar "tmf" (p + 1)) σ1 3 :=
    (Run.assign (evalB_get (ev_var (v := p) (by simp [hp]) (by omega)) (by simp [hX, g0])
      (by omega))).mono
      (by simp [Expr.size])
  let I : ℕ → Env → Prop := fun k τ => τ.arrs A = X ∧ τ.vars "tmf" = p + 1 + (frames (ws.take k)).length ∧
    τ.vars "tmb" = (if t ∈ ws.take k then 1 else 0) ∧ τ.vars "tmn" = ws.length ∧
    (∀ y, y ∉ mV → τ.vars y = σ.vars y)
  have hσ1 : ∀ y, y ∉ mV → σ1.vars y = σ.vars y := fun y hy => by
    simp only [mV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [σ1, hy.1, hy.2.1, hy.2.2.1]
  have tgt : ∀ τ : Env, (∀ y, y ∉ mV → τ.vars y = σ.vars y) → TargetAt t τ := fun τ hτ =>
    ht.congr fun y hy => hτ y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨σ2, r2, ⟨a2, -, b2, -, v2⟩, -⟩ := forUp_run (B := B) (i := "tmj") (e := .var "tmn")
    (body := memBody A) (N := ws.length) (K := 60) I (σ := σ1) (by omega)
    (fun k _ τ hI _ => ev_var hI.2.2.2.1 (by omega))
    ⟨by simp [σ1, hX], by simp [σ1, frames], by simp [σ1], by simp [σ1],
      fun y hy => by
        have : y ≠ "tmj" := by rintro rfl; simp [mV] at hy
        simp [this, hσ1 y hy]⟩
    (by
      rintro k hk τ ⟨aτ, fτ, bτ, nτ, vτ⟩ hj
      obtain ⟨-, hd⟩ := hpos k hk.le
      obtain ⟨hf1, -⟩ := hpos k hk.le
      rw [frames_drop hk] at hd
      rw [← hf1] at fτ
      have hfl := frames_take_le ws (k + 1)
      rw [length_frames_take_succ hk] at hfl
      have htw : (toWord ws).length = (frames ws).length + 1 := by rw [toWord_words]; simp
      obtain ⟨τ', r', f', b', v', a'⟩ := memBody_run (B := B) (w := ws[k])
        (r := frames (ws.drop (k + 1)) ++ r) aτ (by rw [hd]; simp) fτ (tgt τ vτ) htB hB
        (by rw [hf1]; omega) (fun v hv' => hv v (frame_mem hk v hv'))
      refine ⟨τ', r', by rw [v' "tmj" (by decide) (by decide), hj], by simp [a', aτ], ?_, ?_, ?_, fun y hy => ?_⟩
      · simp only [vars_setVar, show ("tmf" : String) ≠ "tmj" by decide, if_false]
        rw [f', hf1, length_frames_take_succ hk]; omega
      · simp only [vars_setVar, show ("tmb" : String) ≠ "tmj" by decide, if_false]
        rw [b', bτ]
        have := take_succ_mem hk t
        by_cases e : ws[k] = t <;> by_cases e2 : t ∈ ws.take k <;> simp_all
      · simp only [vars_setVar, show ("tmn" : String) ≠ "tmj" by decide, if_false]
        rw [v' "tmn" (by decide) (by decide), nτ]
      · have : y ≠ "tmj" := by intro h; subst h; simp [mV] at hy
        simp only [vars_setVar, this, if_false]
        rw [v' y (by intro h; subst h; simp [mV] at hy) (by intro h; subst h; simp [mV] at hy), vτ y hy])
  have hrun : Run B (memScan A) σ σ2 (70 * ws.length + 30) := by
    unfold memScan
    exact (Run.seq r1a (Run.seq r1b (Run.seq r1c r2))).mono (by simp only [Expr.size]; omega)
  obtain ⟨fa, fo, fi⟩ := run_frame hrun (memScan_warrs A) (memScan_reads A) (memScan_noWrite A)
  exact ⟨σ2, hrun, by rw [b2, List.take_length], v2, fa, fo, fi⟩

end Lax185574Proofs.ResolveRam.Glue
