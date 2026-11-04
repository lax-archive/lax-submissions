import Lax185574Proofs.MC.Glue.Link
import Lax185574Proofs.Words.TreeWord

/-!
Walking over partial graphs, and copying, for the rounds of the glue
program of thm:mc after the first.

`skipPG ar` moves `y` over the word of a partial graph on `gn` vertices
(the colors, then two graphs, each a list of `gn` finite sets), at a
constant cost per entry passed. `cpTo` appends a segment of one array to
a filled array and `recol` recolors the colors of the word of a partial
graph in place.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionModelChecking
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-! ### Lists of lists of words in a row -/

/-- Move `y` over `gn` words of lists of words. -/
def skipLs (ar : String) : Com := forUp "e5" (.var "gn") (skipL ar)

theorem skipLs_run {B : ℕ} {ar : String} {X : List ℕ} {p : ℕ} {us : List (List (List ℕ))}
    {r : List ℕ} {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p)
    (hgn : τ.vars "gn" = us.length) (hx : X.drop p = (us.map toWord).flatten ++ r)
    (hB : p + (us.map toWord).flatten.length + us.length < B) :
    ∃ τ', Run B (skipLs ar) τ τ' (28 * ((us.map toWord).flatten.length + us.length) + 8) ∧
      τ'.vars "y" = p + (us.map toWord).flatten.length := by
  have hl : (us.map toWord).length = us.length := List.length_map _
  obtain ⟨τ', r', hy', -⟩ := walk_run (c := 20) (N := us.length) (us := us.map toWord)
    (ar := ar) (i := "e5") (m := "gn") (body := skipL ar)
    (by simp [skipL, Com.wvars]) (by simp [skipL, Com.wvars])
    (by decide) (by decide) (by simp [skipL, Com.warrs]) hX hy hgn (by omega) hx hB (by
      intro k hk ρ hXρ hyρ _ _
      have hd := drop_flatten_take hx (k := k) (by omega)
      have hg : (us.map toWord).getD k [] = toWord us[k] := by
        rw [List.getD_eq_getElem _ _ (by omega)]; simp
      have hle := flatten_take_add_le (us.map toWord) (k := k) (by omega)
      rw [hg] at hd hle ⊢
      obtain ⟨ρ', r', hy'⟩ := skipL_run (B := B) (ws := us[k]) hXρ hyρ hd (by omega)
      exact ⟨ρ', r'.mono (by omega), by rw [hy', hyρ]⟩)
  rw [List.take_of_length_le (by omega)] at r' hy'
  exact ⟨τ', r', hy'⟩

/-! ### A partial graph -/

open Classical in
/-- The word of a graph on `Fin n`: the neighborhoods, each a list of words. -/
theorem toWord_graph_lists {n : ℕ} (H : SimpleGraph (Fin n)) :
    toWord H = n :: ((List.ofFn fun v : Fin n => (Finset.univ.filter (H.Adj v)).words).map
      toWord).flatten := by
  show (List.ofFn fun v : Fin n => Finset.univ.filter (H.Adj v)).length ::
    ((List.ofFn fun v : Fin n => Finset.univ.filter (H.Adj v)).map toWord).flatten = _
  rw [List.length_ofFn, List.map_ofFn, List.map_ofFn]
  rfl

theorem toWord_pg {n : ℕ} (G : PartialGraph (Fin n)) :
    toWord G = (n :: List.ofFn G.color) ++ (toWord G.edge ++ toWord G.nonEdge) := by
  show toWord G.color ++ (toWord G.edge ++ toWord G.nonEdge) = _
  rw [Lax185574Proofs.MC.Glue.toWord_colors]

/-- Move `y` over the word of a graph on `gn` vertices. -/
def skipG (ar : String) : Com := .seq (.assign "y" (.add (.var "y") (.lit 1))) (skipLs ar)

/-- Move `y` over the word of a partial graph on `gn` vertices. -/
def skipPG (ar : String) : Com :=
  .seq (.assign "y" (.add (.add (.var "y") (.lit 1)) (.var "gn"))) (.seq (skipG ar) (skipG ar))

theorem skipG_run {B n : ℕ} {ar : String} {X : List ℕ} {p : ℕ} (H : SimpleGraph (Fin n))
    {r : List ℕ} {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hgn : τ.vars "gn" = n)
    (hx : X.drop p = toWord H ++ r) (hB : p + 2 * (toWord H).length < B) :
    ∃ τ', Run B (skipG ar) τ τ' (60 * (toWord H).length + 20) ∧
      τ'.vars "y" = p + (toWord H).length := by
  classical
  set us := List.ofFn fun v : Fin n => (Finset.univ.filter (H.Adj v)).words with hus
  have hw := toWord_graph_lists H
  rw [← hus] at hw
  have hul : us.length = n := by simp [hus]
  rw [hw] at hx hB ⊢
  simp only [List.length_cons] at hB ⊢
  have hx' : X.drop (p + 1) = (us.map toWord).flatten ++ r := by
    rw [← List.drop_drop, hx]; rfl
  obtain ⟨τ', r', hy'⟩ := skipLs_run (B := B) (us := us) (p := p + 1) (τ := τ.setVar "y" (p + 1)) (by simpa using hX)
    (by simp [hy]) (by simp [hgn, hul]) hx' (by have := length_le_flatten_words us; omega)
  refine ⟨τ', ?_, by rw [hy']; omega⟩
  unfold skipG
  refine (Run.seq (Run.assign (ev_add (ev_var hy (by omega)) (evalB_lit (by omega)) (by omega)))
    r').mono ?_
  simp only [Expr.size]
  have := length_le_flatten_words us
  omega

theorem skipPG_run {B n : ℕ} {ar : String} {X : List ℕ} {p : ℕ} (G : PartialGraph (Fin n))
    {r : List ℕ} {τ : Env} (hX : τ.arrs ar = X) (hy : τ.vars "y" = p) (hgn : τ.vars "gn" = n)
    (hx : X.drop p = toWord G ++ r) (hB : p + 2 * (toWord G).length < B) :
    ∃ τ', Run B (skipPG ar) τ τ' (60 * (toWord G).length + 50) ∧
      τ'.vars "y" = p + (toWord G).length := by
  rw [toWord_pg] at hx hB ⊢
  simp only [List.length_append, List.length_cons, List.length_ofFn] at hB ⊢
  have h1 : X.drop (p + 1 + n) = toWord G.edge ++ (toWord G.nonEdge ++ r) := by
    have := drop_add_of_drop (u := n :: List.ofFn G.color) (by rw [hx, List.append_assoc])
    rw [show p + 1 + n = p + (n :: List.ofFn G.color).length by simp; omega]; rw [List.append_assoc] at this; exact this
  have hX₁ : (τ.setVar "y" (p + 1 + n)).arrs ar = X := by simpa using hX
  obtain ⟨τ₂, r₂, hy₂⟩ := skipG_run (B := B) G.edge hX₁ (by simp) (by simp [hgn]) h1 (by omega)
  have h2 : X.drop (p + 1 + n + (toWord G.edge).length) = toWord G.nonEdge ++ r :=
    drop_add_of_drop h1
  have hX₂ : τ₂.arrs ar = X := by rw [r₂.frame_arr ar (by simp [skipG, skipLs, skipL, forUp, Com.warrs]), hX₁]
  have hgn₂ : τ₂.vars "gn" = n := by
    rw [r₂.frame_var "gn" (by simp [skipG, skipLs, skipL, forUp, Com.wvars])]; simp [hgn]
  obtain ⟨τ₃, r₃, hy₃⟩ := skipG_run (B := B) G.nonEdge hX₂ hy₂ hgn₂ h2 (by omega)
  refine ⟨τ₃, ?_, by rw [hy₃]; omega⟩
  unfold skipPG
  refine (Run.seq (Run.assign (ev_add (ev_add (ev_var hy (by omega)) (evalB_lit (by omega))
    (by omega)) (ev_var hgn (by omega)) (by omega))) (Run.seq r₂ r₃)).mono ?_
  simp only [Expr.size]; omega

/-! ### Copies -/

/-- Append the `l` cells of `src` from position `s` to the filled array `dst`. -/
def cpTo (dst pv src s l : String) : Com :=
  forUp "ci" (.var l) (push1 dst pv (.get src (.add (.var s) (.var "ci"))))

theorem cpTo_run {B : ℕ} {dst pv src s l : String} {σ : Env} {pre : List ℕ} {a N : ℕ}
    (hsrc : src ≠ dst) (hs : σ.vars s = a) (hl : σ.vars l = N) (hpv : pv ≠ "ci")
    (hs1 : s ≠ pv) (hs2 : s ≠ "ci") (hl1 : l ≠ pv) (hl2 : l ≠ "ci")
    (hF : Filled dst pv pre σ) (hA : a + N ≤ (σ.arrs src).length)
    (hcap : pre.length + N ≤ (σ.arrs dst).length) (hB : a + N < B) (hB' : pre.length + N < B)
    (hv : ∀ v ∈ seg (σ.arrs src) a N, v < B) :
    ∃ σ', Run B (cpTo dst pv src s l) σ σ' (N * 20 + 6) ∧
      Filled dst pv (pre ++ seg (σ.arrs src) a N) σ' := by
  set A := σ.arrs src with hAdef
  let P : Env → Prop := fun τ => τ.vars s = a ∧ τ.vars l = N ∧ τ.arrs src = A ∧
    (τ.arrs dst).length = (σ.arrs dst).length
  obtain ⟨σ', r, -, -, F⟩ := forUp_push1 (B := B) (N := N) (cap := (σ.arrs dst).length)
    (i := "ci") (a := dst) (pv := pv) (e := .get src (.add (.var s) (.var "ci")))
    (bnd := .var l) (Ne.symm hpv) (fun k => A.getD (a + k) 0) P
    (fun τ v hP => ⟨by simp [hs2, hP.1], by simp [hl2, hP.2.1], by simp [hP.2.2.1],
      by simp [hP.2.2.2]⟩)
    (fun τ τ' hP hv' ha hlen => ⟨by rw [hv' s hs1, hP.1], by rw [hv' l hl1, hP.2.1],
      by rw [ha src hsrc, hP.2.2.1], by rw [hlen, hP.2.2.2]⟩)
    (fun τ hP => hP.2.2.2) (by omega) ⟨hs, hl, rfl, rfl⟩ hF
    (fun τ hP => ev_var hP.2.1 (by omega))
    (fun k hk τ hP hik => by
      have hk' : a + k < A.length := by omega
      have hmem : A.getD (a + k) 0 ∈ seg A a N := by
        rw [← flatMap_getD_eq_seg A a N hA]
        exact List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, by simp⟩
      exact evalB_get (ev_add (ev_var hP.1 (by omega)) (ev_var hik (by omega)) (by omega))
        (by rw [hP.2.2.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; simp)
        (hv _ hmem))
    hcap hB'
  refine ⟨σ', r.mono (by simp [Expr.size]; omega), ?_⟩
  rwa [flatMap_getD_eq_seg A a N hA] at F

/-- A color after the recoloring of a merge, if `ρ = 1`. -/
def recol (ρ P Q c : ℕ) : ℕ := if ρ = 1 ∧ c = Q then P else c

/-- Append the `gn` cells of `x` from `cA` to `GW`, recolored if `rc = 1`. -/
def cpCol : Com :=
  forUp "ci" (.var "gn") (.ite (.eq (.var "rc") (.lit 1))
    (.ite (.eq (.get "x" (.add (.var "cA") (.var "ci"))) (.var "cQ")) (push1 "GW" "pg" (.var "cP"))
      (push1 "GW" "pg" (.get "x" (.add (.var "cA") (.var "ci")))))
    (push1 "GW" "pg" (.get "x" (.add (.var "cA") (.var "ci")))))

theorem cpCol_run {B : ℕ} {σ : Env} {pre X : List ℕ} {a N ρ P Q : ℕ}
    (hX : σ.arrs "x" = X) (ha : σ.vars "cA" = a) (hN : σ.vars "gn" = N) (hρ : σ.vars "rc" = ρ)
    (hP : σ.vars "cP" = P) (hQ : σ.vars "cQ" = Q) (hρB : ρ < B) (hPB : P < B) (hQB : Q < B)
    (hF : Filled "GW" "pg" pre σ) (hA : a + N ≤ X.length)
    (hcap : pre.length + N ≤ (σ.arrs "GW").length) (hB : a + N < B) (hB' : pre.length + N < B)
    (hv : ∀ v ∈ X, v < B) :
    ∃ σ', Run B cpCol σ σ' (N * 40 + 6) ∧
      Filled "GW" "pg" (pre ++ (seg X a N).map (recol ρ P Q)) σ' := by
  let Pr : Env → Prop := fun τ => τ.arrs "x" = X ∧ τ.vars "cA" = a ∧ τ.vars "gn" = N ∧
    τ.vars "rc" = ρ ∧ τ.vars "cP" = P ∧ τ.vars "cQ" = Q ∧
    (τ.arrs "GW").length = (σ.arrs "GW").length
  have hfr : ∀ τ τ', Pr τ → (∀ y, y ≠ "pg" → τ'.vars y = τ.vars y) →
      (∀ b, b ≠ "GW" → τ'.arrs b = τ.arrs b) → (τ'.arrs "GW").length = (τ.arrs "GW").length →
      Pr τ' := fun τ τ' h hv' ha' hl' =>
    ⟨by rw [ha' "x" (by decide), h.1], by rw [hv' _ (by decide), h.2.1],
      by rw [hv' _ (by decide), h.2.2.1], by rw [hv' _ (by decide), h.2.2.2.1],
      by rw [hv' _ (by decide), h.2.2.2.2.1], by rw [hv' _ (by decide), h.2.2.2.2.2.1],
      by rw [hl', h.2.2.2.2.2.2]⟩
  obtain ⟨σ', r, -, -, F⟩ := forUp_append (B := B) (N := N) (K := 30) (i := "ci") (a := "GW")
    (pv := "pg") (e := .var "gn") (body := .ite (.eq (.var "rc") (.lit 1))
      (.ite (.eq (.get "x" (.add (.var "cA") (.var "ci"))) (.var "cQ")) (push1 "GW" "pg" (.var "cP"))
        (push1 "GW" "pg" (.get "x" (.add (.var "cA") (.var "ci")))))
      (push1 "GW" "pg" (.get "x" (.add (.var "cA") (.var "ci")))))
    (by decide) (fun k => [recol ρ P Q (X.getD (a + k) 0)]) Pr
    (fun τ v h => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
        by simpa using h5, by simpa using h6, by simpa using h7⟩) (by omega)
    ⟨hX, ha, hN, hρ, hP, hQ, rfl⟩ hF (fun τ h => ev_var h.2.2.1 (by omega))
    (fun k hk τ h hik hFk => by
      have hk' : a + k < X.length := by omega
      have hxv : X.getD (a + k) 0 < B := hv _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; simp)
      have hget : (Expr.get "x" (.add (.var "cA") (.var "ci"))).evalB B τ = some (X.getD (a + k) 0) :=
        evalB_get (ev_add (ev_var h.2.1 (by omega)) (ev_var hik (by omega)) (by omega))
          (by rw [h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; simp) hxv
      have hlen : (pre ++ (List.range k).flatMap fun k => [recol ρ P Q (X.getD (a + k) 0)]).length =
          pre.length + k := by
        rw [List.length_append, length_flatMap_single]
      have hcap' : (pre ++ (List.range k).flatMap fun k => [recol ρ P Q (X.getD (a + k) 0)]).length <
          (τ.arrs "GW").length := by rw [hlen, h.2.2.2.2.2.2]; omega
      have hpush : ∀ (e : Expr) (v : ℕ), e.evalB B τ = some v → v = recol ρ P Q (X.getD (a + k) 0) →
          e.size ≤ 4 → ∃ τ', Run B (push1 "GW" "pg" e) τ τ' 10 ∧ τ'.vars "ci" = k ∧ Pr τ' ∧
            Filled "GW" "pg" (pre ++ (List.range (k + 1)).flatMap fun k =>
              [recol ρ P Q (X.getD (a + k) 0)]) τ' := by
        intro e v he hve hs
        obtain ⟨τ', r', F', fv, fa, fl, -, -⟩ := push1_run hFk he hcap' (by rw [hlen]; omega)
        refine ⟨τ', r'.mono (by omega), by rw [fv _ (by decide), hik], hfr τ τ' h fv fa fl, ?_⟩
        rw [flatMap_range_succ', ← List.append_assoc, ← hve]; exact F'
      have hc1 := condEq_lit (B := B) h.2.2.2.1 hρB (show 1 < B by omega)
      by_cases h1 : ρ = 1
      · have hc2 := evalB_condEq (B := B) hget (ev_var h.2.2.2.2.2.1 hQB)
        by_cases h2 : X.getD (a + k) 0 = Q
        · obtain ⟨τ', r', h'⟩ := hpush (.var "cP") P (ev_var h.2.2.2.2.1 hPB)
            (by rw [recol, if_pos ⟨h1, h2⟩]) (by simp [Expr.size])
          exact ⟨τ', (Run.ite_true (by rw [hc1, decide_eq_true h1]) (Run.ite_true
            (by rw [hc2, h2, beq_self_eq_true]) r')).mono (by simp [Cond.size, Expr.size]), h'⟩
        · obtain ⟨τ', r', h'⟩ := hpush _ _ hget (by rw [recol, if_neg (fun h => h2 h.2)])
            (by simp [Expr.size])
          exact ⟨τ', (Run.ite_true (by rw [hc1, decide_eq_true h1]) (Run.ite_false
            (by rw [hc2, beq_eq_false_iff_ne.2 h2]) r')).mono (by simp [Cond.size, Expr.size]), h'⟩
      · obtain ⟨τ', r', h'⟩ := hpush _ _ hget (by rw [recol, if_neg (fun h => h1 h.1)])
          (by simp [Expr.size])
        exact ⟨τ', (Run.ite_false (by rw [hc1, decide_eq_false h1]) r').mono
          (by simp [Cond.size, Expr.size]), h'⟩)
  refine ⟨σ', r.mono (by simp [Expr.size]; omega), ?_⟩
  have e : ((List.range N).flatMap fun k => [recol ρ P Q (X.getD (a + k) 0)]) =
      (seg X a N).map (recol ρ P Q) := by
    have : ((List.range N).flatMap fun k => [recol ρ P Q (X.getD (a + k) 0)]) =
        ((List.range N).flatMap fun k => [X.getD (a + k) 0]).map (recol ρ P Q) := by
      simp [List.map_flatMap]
    rw [this, flatMap_getD_eq_seg X a N hA]
  rwa [e] at F

end Lax185574Proofs.MC.Glue
