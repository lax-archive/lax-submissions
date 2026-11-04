import Lax185574Proofs.MC.Glue.Parse0
import Lax185574Proofs.MC.InitWord
import Lax185574Proofs.Lib.DistMatrix

/-!
Round 0 of the glue program of thm:mc: reading the input, and the
initial words of the partial graph and of the family of type trees.

After the tag, the input of round 0 is `|x| :: x ++ [0]`, and `read0`
reads `x` into the array `U`. From the header of the graph block
(`hdr0`), `gwInit` writes the word of the initial partial graph of the
script into `GW`: the number `n` of vertices and the colors, then two
graphs without edges. `fwInit` writes the word of the family of the
type trees of rank `(1, q)` of the vertices into `FW`. Since the initial
partial graph has no resolved pairs, the tree of a vertex of color `c`
is `[1, q, 1] ++ initWord 1 q 1 c`, which `buildInit` writes into `ta`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees

/-! ### The initial words -/

/-- The word of the initial partial graph with colors `c`. -/
def gw0 (n : ℕ) (c : ℕ → ℕ) : List ℕ :=
  (n :: (List.range n).flatMap fun k => [c k]) ++ (n :: (List.range n).flatMap fun _ => [0]) ++
    (n :: (List.range n).flatMap fun _ => [0])

/-- The word of the matrix of distances of a partial graph on `n`
vertices without edges: `1` on the diagonal (distance `0`), `0`
elsewhere (distance `∞`). -/
def dm0 (n : ℕ) : List ℕ :=
  n :: (List.range n).flatMap fun u => n :: (List.range n).flatMap fun v => [if u = v then 1 else 0]

/-- The word of the initial partial graph with colors `c` and of its
matrix of distances. -/
def gd0 (n : ℕ) (c : ℕ → ℕ) : List ℕ := gw0 n c ++ dm0 n

/-- The word of the family of the initial trees of rank `(1, q)`. -/
def fw0 (n q : ℕ) (c : ℕ → ℕ) : List ℕ :=
  n :: (List.range n).flatMap fun k => [1, q, 1] ++ initWord 1 q 1 (c k)

theorem flatten_ofFn_eq {n : ℕ} (f : Fin n → List ℕ) (g : ℕ → List ℕ)
    (h : ∀ k (hk : k < n), f ⟨k, hk⟩ = g k) : (List.ofFn f).flatten = (List.range n).flatMap g := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append, flatMap_range_succ',
        ih (fun i => f i.castSucc) (fun k hk => h k (by omega))]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      exact congrArg _ (h n (by omega))

theorem ofFn_eq_flatMap {n : ℕ} (f : Fin n → ℕ) (g : ℕ → ℕ) (h : ∀ k (hk : k < n), f ⟨k, hk⟩ = g k) :
    List.ofFn f = (List.range n).flatMap fun k => [g k] := by
  rw [← flatten_ofFn_eq (fun i => [f i]) (fun k => [g k]) (fun k hk => by rw [h])]
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.singleton_append]
    exact congrArg _ (ih _)

theorem sAt_run_zero {n : ℕ} (σ : Script n) : sAt σ.run 0 = unresolved σ.colors := by
  simp [sAt, Script.run]

theorem toWord_bot (n : ℕ) :
    toWord (⊥ : SimpleGraph (Fin n)) = n :: (List.range n).flatMap fun _ => [0] := by
  show (List.ofFn _).length :: ((List.ofFn _).map toWord).flatten = _
  rw [List.length_ofFn, List.map_ofFn]
  congr 1
  apply flatten_ofFn_eq
  intro k hk
  have he : ∀ S : Finset (Fin n), S = ∅ → toWord S = [0] := by
    rintro S rfl
    have hw : Finset.words (∅ : Finset (Fin n)) = [] := by simp [Finset.words]
    show toWord (Finset.words (∅ : Finset (Fin n))) = _
    rw [hw]; rfl
  exact he _ (by ext; simp)

/-- The word of the initial partial graph of a script. -/
theorem toWord_sAt_zero {n : ℕ} (σ : Script n) (c : ℕ → ℕ)
    (hc : ∀ k (hk : k < n), σ.colors ⟨k, hk⟩ = c k) : toWord (sAt σ.run 0) = gw0 n c := by
  rw [sAt_run_zero]
  show toWord σ.colors ++ (toWord (⊥ : SimpleGraph (Fin n)) ++ toWord (⊥ : SimpleGraph (Fin n))) = _
  rw [toWord_colors, toWord_bot, gw0, List.append_assoc]
  congr 2
  rw [← flatten_ofFn_eq (n := n) (fun i => [σ.colors i]) (fun k => [c k])
    (fun k hk => by rw [hc k hk])]
  rw [← flatten_map_single (List.ofFn σ.colors), List.map_ofFn]
  rfl

open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix in
/-- The word of the matrix of distances of the initial partial graph. -/
theorem toWord_dist_zero {n : ℕ} (σ : Script n) : toWord (distMatrix (sAt σ.run 0)) = dm0 n := by
  rw [toWord_distMatrix, matWord, dm0, sAt_run_zero]
  congr 1
  apply flatten_ofFn_eq
  intro u hu
  congr 1
  apply ofFn_eq_flatMap
  intro v hv
  rw [dcode_distMatrix_of_bot _ rfl rfl]
  simp [Fin.ext_iff]

open Lax185574.DistanceMatrix in
theorem toWord_gd_zero {n : ℕ} (σ : Script n) (c : ℕ → ℕ)
    (hc : ∀ k (hk : k < n), σ.colors ⟨k, hk⟩ = c k) :
    toWord (sAt σ.run 0) ++ toWord (distMatrix (sAt σ.run 0)) = gd0 n c := by
  rw [toWord_sAt_zero σ c hc, toWord_dist_zero, gd0]

/-- The word of the initial family of trees of a script. -/
theorem toWord_family_zero {n : ℕ} (σ : Script n) (q : ℕ) (c : ℕ → ℕ)
    (hc : ∀ k (hk : k < n), σ.colors ⟨k, hk⟩ = c k) :
    toWord (family (sAt σ.run 0) 1 q) = fw0 n q c := by
  show (List.ofFn _).length :: ((List.ofFn (family (sAt σ.run 0) 1 q)).map toWord).flatten = _
  rw [List.length_ofFn, List.map_ofFn, fw0]
  congr 1
  apply flatten_ofFn_eq
  intro k hk
  simp only [Function.comp, family, sAt_run_zero]
  rw [toWord_tree_unresolved _ rfl rfl]
  simp [unresolved, hc k hk]


/-- The colors of the script as read from the input word. -/
def inCol (x : List ℕ) (gl : ℕ) (k : ℕ) : ℕ := x.getD (gl + 1 + k) 0

theorem inCol_spec {n : ℕ} (g : List ℕ) (σ : Script n) (r : List ℕ) {k : ℕ} (hk : k < n) :
    (g ++ toWord σ ++ r)[g.length + 1 + k]? = some (inCol (g ++ toWord σ ++ r) g.length k) ∧
      σ.colors ⟨k, hk⟩ = inCol (g ++ toWord σ ++ r) g.length k := by
  have h := input_color g σ r ⟨k, hk⟩
  simp only [inCol, List.getD_eq_getElem?_getD, h]
  exact ⟨rfl, rfl⟩

/-- The initial words of a script, with the colors read from the input. -/
theorem init_words {n : ℕ} (g : List ℕ) (σ : Script n) (r : List ℕ) (q : ℕ) :
    toWord (sAt σ.run 0) = gw0 n (inCol (g ++ toWord σ ++ r) g.length) ∧
      toWord (family (sAt σ.run 0) 1 q) = fw0 n q (inCol (g ++ toWord σ ++ r) g.length) :=
  ⟨toWord_sAt_zero σ _ fun _ hk => (inCol_spec g σ r hk).2,
    toWord_family_zero σ q _ fun _ hk => (inCol_spec g σ r hk).2⟩

/-! ### Reading the input of round 0 -/

/-- Read the length `|x|` into `n` and then `x` into `U`. -/
def read0 : Com :=
  .seq (.read "n") (.seq (.assign "j" (.lit 0)) (.seq (.assign "p" (.lit 0)) (readInto "U")))

theorem read0_run {B : ℕ} {x rest : List ℕ} {σ : Env} (hinp : σ.inp = x.length :: (x ++ rest))
    (hU : x.length ≤ (σ.arrs "U").length) (hB : x.length < B) (hx : ∀ v ∈ x, v < B) :
    ∃ σ', Run B read0 σ σ' (16 * x.length + 12) ∧ σ'.inp = rest ∧ σ'.vars "n" = x.length ∧
      σ'.arrs "U" = x ++ (σ.arrs "U").drop x.length := by
  set τ := (({ σ.setVar "n" x.length with inp := x ++ rest } : Env).setVar "j" 0).setVar "p" 0
    with hτ
  have hI : IntoInv "U" [] (σ.arrs "U") x rest τ :=
    ⟨0, by omega, by simp [hτ], by simp [hτ], by simp [hτ], by simp [hτ], by simp [hτ]⟩
  obtain ⟨σ', r, -, -, hinp', hU'⟩ := readInto_run (B := B) (by simpa using hU) (by simpa using hB)
    hx hI
  have hn : σ'.vars "n" = x.length := by
    rw [r.frame_var "n" (by decide)]; simp [hτ]
  refine ⟨σ', ?_, hinp', hn, by simpa using hU'⟩
  unfold read0
  exact (Run.seq (Run.read hinp) (Run.seq (Run.assign (evalB_lit (by omega)))
    (Run.seq (Run.assign (evalB_lit (by omega))) r))).mono (by simp; omega)

/-! ### Loops that append one value per round -/

theorem length_flatMap_single (f : ℕ → ℕ) (N : ℕ) :
    ((List.range N).flatMap fun k => [f k]).length = N := by
  rw [length_flatMap_const (m := 1) (fun _ => rfl)]; ring

/-- A counting loop whose round `k` appends the value `f k`. -/
theorem forUp_push1 {B N cap : ℕ} {i a pv : String} {e bnd : Expr} (hi : i ≠ pv) (f : ℕ → ℕ)
    (P : Env → Prop) (hPi : ∀ τ v, P τ → P (τ.setVar i v))
    (hPp : ∀ τ τ', P τ → (∀ y, y ≠ pv → τ'.vars y = τ.vars y) → (∀ b, b ≠ a → τ'.arrs b = τ.arrs b) →
      (τ'.arrs a).length = (τ.arrs a).length → P τ')
    (hPc : ∀ τ, P τ → (τ.arrs a).length = cap)
    {σ : Env} {l : List ℕ} (hN : N < B) (hP : P σ) (hσ : Filled a pv l σ)
    (he : ∀ τ, P τ → bnd.evalB B τ = some N)
    (hv : ∀ k < N, ∀ τ, P τ → τ.vars i = k → e.evalB B τ = some (f k))
    (hcap : l.length + N ≤ cap) (hB : l.length + N < B) :
    ∃ σ', Run B (forUp i bnd (push1 a pv e)) σ σ' (N * (6 + e.size + bnd.size + 7) + bnd.size + 5) ∧
      P σ' ∧ σ'.vars i = N ∧ Filled a pv (l ++ (List.range N).flatMap fun k => [f k]) σ' := by
  refine forUp_append hi (fun k => [f k]) P hPi hN hP hσ he ?_
  intro k hk τ hP hik hF
  have hlen : (l ++ (List.range k).flatMap fun k => [f k]).length = l.length + k := by
    rw [List.length_append, length_flatMap_single]
  obtain ⟨τ', r, F', fv, fa, fl, -, -⟩ := push1_run hF (hv k hk τ hP hik)
    (by rw [hlen, hPc τ hP]; omega) (by rw [hlen]; omega)
  refine ⟨τ', r, by rw [fv i hi, hik], hPp τ τ' hP fv fa fl, ?_⟩
  rw [flatMap_range_succ', ← List.append_assoc]; exact F'

/-! ### The word of the initial partial graph -/

/-- Append the colors `U[gL + 1 + i]` for `i < gn`, or `gn` zeros. -/
def gwCols : Com :=
  forUp "gi" (.var "gn") (push1 "GW" "pg" (.get "U" (.add (.add (.var "gL") (.lit 1)) (.var "gi"))))
def gwZeros : Com := forUp "gi" (.var "gn") (push1 "GW" "pg" (.lit 0))

/-- Row `e5` of the matrix of distances without edges: `gn`, then `1` at
`e5` and `0` elsewhere. -/
def dmRow : Com :=
  .seq (push1 "GW" "pg" (.var "gn")) (forUp "gi" (.var "gn")
    (push1 "GW" "pg" (.sub (.lit 1) (.add (.sub (.var "e5") (.var "gi")) (.sub (.var "gi") (.var "e5"))))))

/-- The matrix of distances without edges. -/
def dmInit : Com := .seq (push1 "GW" "pg" (.var "gn")) (forUp "e5" (.var "gn") dmRow)

/-- The word of the initial partial graph into `GW`, with `gn = n` and
the colors in `U` behind `gL = |g|`. -/
def gwInit : Com :=
  .seq (.assign "pg" (.lit 0)) (.seq (push1 "GW" "pg" (.var "gn")) (.seq gwCols
  (.seq (push1 "GW" "pg" (.var "gn")) (.seq gwZeros
  (.seq (push1 "GW" "pg" (.var "gn")) (.seq gwZeros dmInit))))))

theorem length_gw0 (n : ℕ) (c : ℕ → ℕ) : (gw0 n c).length = 3 * n + 3 := by
  simp only [gw0, List.length_append, List.length_cons, length_flatMap_single]; omega

theorem length_dm0 (n : ℕ) : (dm0 n).length = 1 + n * (n + 1) := by
  simp only [dm0, List.length_cons]
  rw [length_flatMap_const (m := n + 1) (fun u => by simp [length_flatMap_single])]; ring

theorem length_gd0 (n : ℕ) (c : ℕ → ℕ) : (gd0 n c).length = 3 * n + 3 + (1 + n * (n + 1)) := by
  rw [gd0, List.length_append, length_gw0, length_dm0]

theorem dmRow_run {B n u cap : ℕ} {l : List ℕ} {τ : Env} (hgn : τ.vars "gn" = n)
    (he5 : τ.vars "e5" = u) (hF : Filled "GW" "pg" l τ) (hcap : (τ.arrs "GW").length = cap)
    (hu : u < n) (hc : l.length + n + 1 ≤ cap) (hB : l.length + n + 1 < B) :
    ∃ τ', Run B dmRow τ τ' (30 * n + 30) ∧
      Filled "GW" "pg" (l ++ (n :: (List.range n).flatMap fun v => [if u = v then 1 else 0])) τ' ∧
      (∀ y, y ≠ "pg" → y ≠ "gi" → τ'.vars y = τ.vars y) ∧
      (∀ b, b ≠ "GW" → τ'.arrs b = τ.arrs b) ∧ (τ'.arrs "GW").length = cap := by
  obtain ⟨τ₁, r₁, F₁, fv₁, fa₁, fl₁, -, -⟩ := push1_run (B := B) hF (ev_var hgn (by omega))
    (by rw [hcap]; omega) (by omega)
  let P : Env → Prop := fun τ' => (∀ y, y ≠ "pg" → y ≠ "gi" → τ'.vars y = τ.vars y) ∧
    (∀ b, b ≠ "GW" → τ'.arrs b = τ.arrs b) ∧ (τ'.arrs "GW").length = cap
  have P₁ : P τ₁ := ⟨fun y hy _ => fv₁ y hy, fa₁, by rw [fl₁, hcap]⟩
  have hl₁ : (l ++ [n]).length = l.length + 1 := by simp
  obtain ⟨τ₂, r₂, P₂, -, F₂⟩ := forUp_push1 (B := B) (N := n) (cap := cap) (i := "gi")
    (a := "GW") (pv := "pg")
    (e := .sub (.lit 1) (.add (.sub (.var "e5") (.var "gi")) (.sub (.var "gi") (.var "e5"))))
    (bnd := .var "gn") (by decide) (fun v => if u = v then 1 else 0) P
    (fun τ' v h => ⟨fun y hy hy' => by simp [hy']; exact h.1 y hy hy', h.2.1, by simpa using h.2.2⟩)
    (fun τ' τ'' h fv fa fl => ⟨fun y hy hy' => by rw [fv y hy]; exact h.1 y hy hy',
      fun b hb => by rw [fa b hb]; exact h.2.1 b hb, by rw [fl]; exact h.2.2⟩)
    (fun τ' h => h.2.2) (by omega) P₁ F₁ (fun τ' h => ev_var (by rw [h.1 _ (by decide) (by decide), hgn]) (by omega))
    (fun k hk τ' h hik => by
      have h5 : τ'.vars "e5" = u := by rw [h.1 _ (by decide) (by decide), he5]
      have hval : (if u = k then 1 else 0) = 1 - ((u - k) + (k - u)) := by split_ifs <;> omega
      show _ = some (if u = k then 1 else 0)
      rw [hval]
      exact ev_sub (evalB_lit (by omega)) (ev_add (ev_sub (ev_var h5 (by omega))
        (ev_var hik (by omega)) (by omega)) (ev_sub (ev_var hik (by omega))
        (ev_var h5 (by omega)) (by omega)) (by omega)) (by omega))
    (by rw [hl₁]; omega) (by rw [hl₁]; omega)
  refine ⟨τ₂, ?_, ?_, P₂.1, P₂.2.1, P₂.2.2⟩
  · unfold dmRow
    refine (Run.seq r₁ r₂).mono ?_
    simp only [Expr.size]; omega
  · have e : l ++ (n :: (List.range n).flatMap fun v => [if u = v then 1 else 0]) =
        l ++ [n] ++ (List.range n).flatMap fun v => [if u = v then 1 else 0] := by
      simp only [List.append_assoc, List.singleton_append]
    rw [e]; exact F₂

theorem gwInit_run {B n gl : ℕ} {c : ℕ → ℕ} {σ : Env} (hn : σ.vars "gn" = n)
    (hgl : σ.vars "gL" = gl) (hU : ∀ k < n, (σ.arrs "U")[gl + 1 + k]? = some (c k))
    (hc : ∀ k < n, c k < B) (hcap : 3 * n + 3 + (1 + n * (n + 1)) ≤ (σ.arrs "GW").length)
    (hB : 3 * n + 3 + (1 + n * (n + 1)) < B) (hgB : gl + 1 + n < B) :
    ∃ σ', Run B gwInit σ σ' (50 * n + 50 + 50 * (n + 1) ^ 2) ∧ Filled "GW" "pg" (gd0 n c) σ' := by
  set cap := (σ.arrs "GW").length
  let P : Env → Prop := fun τ => τ.vars "gn" = n ∧ τ.vars "gL" = gl ∧ τ.arrs "U" = σ.arrs "U" ∧
    (τ.arrs "GW").length = cap
  have hPi : ∀ τ v, P τ → P (τ.setVar "gi" v) := fun τ v h => by
    obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4]⟩
  have hPi5 : ∀ τ v, P τ → P (τ.setVar "e5" v) := fun τ v h => by
    obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4]⟩
  have hPp : ∀ τ τ', P τ → (∀ y, y ≠ "pg" → τ'.vars y = τ.vars y) →
      (∀ b, b ≠ "GW" → τ'.arrs b = τ.arrs b) → (τ'.arrs "GW").length = (τ.arrs "GW").length →
      P τ' := fun τ τ' h fv fa fl => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨by rw [fv _ (by decide), h1], by rw [fv _ (by decide), h2], by
      rw [fa _ (by decide), h3], by rw [fl, h4]⟩
  have hPc : ∀ τ, P τ → (τ.arrs "GW").length = cap := fun τ h => h.2.2.2
  have hgn : ∀ τ, P τ → (Expr.var "gn").evalB B τ = some n := fun τ h => ev_var h.1 (by omega)
  -- the first entry
  set σ₀ := σ.setVar "pg" 0 with hσ₀
  have P₀ : P σ₀ := ⟨by simp [hσ₀, hn], by simp [hσ₀, hgl], by simp [hσ₀], by
    simp only [hσ₀, arrs_setVar]; rfl⟩
  obtain ⟨σ₁, r₁, F₁, fv₁, fa₁, fl₁, -, -⟩ := push1_run (Filled.empty "GW" "pg" σ) (hgn σ₀ P₀)
    (by simp; omega) (by simp; omega)
  have P₁ := hPp _ _ P₀ fv₁ fa₁ fl₁
  -- the colors
  obtain ⟨σ₂, r₂, P₂, -, F₂⟩ := forUp_push1 (B := B) (N := n) (cap := cap) (i := "gi") (a := "GW")
    (pv := "pg") (e := .get "U" (.add (.add (.var "gL") (.lit 1)) (.var "gi"))) (bnd := .var "gn")
    (by decide) c P hPi hPp hPc (by omega) P₁ F₁ hgn
    (fun k hk τ h hik => evalB_get (ev_add (ev_add (ev_var h.2.1 (by omega)) (evalB_lit (by omega))
      (by omega)) (ev_var hik (by omega)) (by omega)) (by rw [h.2.2.1]; exact hU k hk) (hc k hk))
    (by simp; omega) (by simp; omega)
  -- the two graphs without edges
  have hl₂ : ([] ++ [n] ++ (List.range n).flatMap fun k => [c k]).length = n + 1 := by
    simp
  obtain ⟨σ₃, r₃, F₃, fv₃, fa₃, fl₃, -, -⟩ := push1_run F₂ (hgn σ₂ P₂)
    (by rw [hl₂, hPc σ₂ P₂]; omega) (by rw [hl₂]; omega)
  have P₃ := hPp _ _ P₂ fv₃ fa₃ fl₃
  obtain ⟨σ₄, r₄, P₄, -, F₄⟩ := forUp_push1 (B := B) (N := n) (cap := cap) (i := "gi") (a := "GW")
    (pv := "pg") (e := .lit 0) (bnd := .var "gn") (by decide) (fun _ => 0) P hPi hPp hPc
    (by omega) P₃ F₃ hgn (fun k hk τ h hik => evalB_lit (by omega))
    (by simp; omega) (by simp; omega)
  have hl₄ : ([] ++ [n] ++ ((List.range n).flatMap fun k => [c k]) ++ [n] ++
      (List.range n).flatMap fun _ => [0]).length = 2 * n + 2 := by
    simp; omega
  obtain ⟨σ₅, r₅, F₅, fv₅, fa₅, fl₅, -, -⟩ := push1_run F₄ (hgn σ₄ P₄)
    (by rw [hl₄, hPc σ₄ P₄]; omega) (by rw [hl₄]; omega)
  have P₅ := hPp _ _ P₄ fv₅ fa₅ fl₅
  obtain ⟨σ₆, r₆, P₆, -, F₆⟩ := forUp_push1 (B := B) (N := n) (cap := cap) (i := "gi") (a := "GW")
    (pv := "pg") (e := .lit 0) (bnd := .var "gn") (by decide) (fun _ => 0) P hPi hPp hPc
    (by omega) P₅ F₅ hgn (fun k hk τ h hik => evalB_lit (by omega))
    (by simp; omega) (by simp; omega)
  have hl₆ : ([] ++ [n] ++ ((List.range n).flatMap fun k => [c k]) ++ [n] ++
      ((List.range n).flatMap fun _ => [0]) ++ [n] ++ (List.range n).flatMap fun _ => [0]).length =
      3 * n + 3 := by simp; omega
  -- the matrix of distances
  obtain ⟨σ₇, r₇, F₇, fv₇, fa₇, fl₇, -, -⟩ := push1_run F₆ (hgn σ₆ P₆)
    (by rw [hl₆, hPc σ₆ P₆]; omega) (by rw [hl₆]; omega)
  have P₇ := hPp _ _ P₆ fv₇ fa₇ fl₇
  obtain ⟨L₇, hL₇⟩ : ∃ L, L = [] ++ [n] ++ ((List.range n).flatMap fun k => [c k]) ++ [n] ++
      ((List.range n).flatMap fun _ => [0]) ++ [n] ++ ((List.range n).flatMap fun _ => [0]) ++ [n] :=
    ⟨_, rfl⟩
  rw [← hL₇] at F₇
  have hL₇l : L₇.length = 3 * n + 4 := by
    rw [hL₇, List.length_append, hl₆, List.length_singleton]
  obtain ⟨f, hf⟩ : ∃ f : ℕ → List ℕ,
      f = fun u => n :: (List.range n).flatMap fun v => [if u = v then 1 else 0] := ⟨_, rfl⟩
  have hfl : ∀ u, (f u).length = n + 1 := fun u => by
    rw [hf]; simp only [List.length_cons, length_flatMap_single]
  have hrange : ∀ k, ((List.range k).flatMap f).length = k * (n + 1) :=
    fun k => length_flatMap_const hfl k
  obtain ⟨σ₈, r₈, -, -, F₈⟩ := forUp_append (B := B) (i := "e5") (e := .var "gn") (body := dmRow)
    (N := n) (K := 30 * n + 30) (a := "GW") (pv := "pg") (by decide) f P hPi5 (by omega) P₇ F₇ hgn
    (by
      intro u hu τ hP hiu hF
      have hlen : (L₇ ++ (List.range u).flatMap f).length = 3 * n + 4 + u * (n + 1) := by
        rw [List.length_append, hL₇l, hrange]
      have hun : u * (n + 1) + (n + 1) ≤ n * (n + 1) := by
        have := Nat.mul_le_mul_right (n + 1) (show u + 1 ≤ n by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      obtain ⟨τ₂, r₂, F₂, fv₂, fa₂, fl₂⟩ := dmRow_run (B := B) hP.1 hiu hF (hPc τ hP) hu
        (by rw [hlen]; omega) (by rw [hlen]; omega)
      refine ⟨τ₂, r₂, by rw [fv₂ _ (by decide) (by decide), hiu], ?_, ?_⟩
      · exact ⟨by rw [fv₂ _ (by decide) (by decide), hP.1], by rw [fv₂ _ (by decide) (by decide), hP.2.1],
          by rw [fa₂ _ (by decide), hP.2.2.1], fl₂⟩
      · have e : f u = n :: (List.range n).flatMap fun v => [if u = v then 1 else 0] := by rw [hf]
        rw [flatMap_range_succ', ← List.append_assoc, e]; exact F₂)
  have c₈ : n * (30 * n + 30 + (Expr.var "gn").size + 7) + (Expr.var "gn").size + 5 ≤
      38 * (n + 1) ^ 2 + 6 := by
    simp only [Expr.size]; nlinarith
  have r₈' := r₈.mono c₈
  refine ⟨σ₈, ?_, ?_⟩
  · unfold gwInit gwCols gwZeros dmInit
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₁ (Run.seq r₂ (Run.seq r₃
      (Run.seq r₄ (Run.seq r₅ (Run.seq r₆ (Run.seq r₇ r₈')))))))).mono ?_
    clear c₈ r₈' r₈
    simp only [Expr.size]
    have hS : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    generalize (n + 1) ^ 2 = S at hS ⊢
    omega
  · have e : gd0 n c = L₇ ++ (List.range n).flatMap f := by
      rw [hL₇, hf, gd0, gw0, dm0]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [e]; exact F₈

/-! ### The word of the initial family of trees -/

/-- The length of the initial tree of rank `(1, q)` without its header. -/
def iL (q : ℕ) : ℕ := lvlLen (1 + q) q 1 q

theorem length_initWord (q c : ℕ) : (initWord 1 q 1 c).length = iL q := by
  rw [← lvlWord_top, length_lvlWord]; rfl

theorem initWord_entry {q c v : ℕ} (hv : v ∈ initWord 1 q 1 c) : v ≤ iL q + c + 5 := by
  rw [← lvlWord_top] at hv
  exact lvlWord_entries (1 + q) q 1 c le_rfl q le_rfl v hv

/-- The cost of one initial tree. -/
def initCost (q : ℕ) : ℕ :=
  (q + 1) * (lvlCost (iL q) + 100 * (iL q + 1) + 60) + 8 + 16 * iL q

/-- The tree of vertex `gi`: its header `[1, q, 1]`, then the word that
`buildInit` writes into `ta`, copied. -/
def fwTree : Com :=
  .seq (pushL "FW" "pf" [.lit 1, .var "rk", .lit 1])
  (.seq (.assign "iwc" (.get "U" (.add (.add (.var "gL") (.lit 1)) (.var "gi"))))
  (.seq buildInit (forUp "gc" (.var "iwn") (push1 "FW" "pf" (.get "ta" (.var "gc"))))))

/-- The word of the initial family of trees into `FW`, with `rk = q`. -/
def fwInit : Com :=
  .seq (.assign "pf" (.lit 0)) (.seq (push1 "FW" "pf" (.var "gn"))
  (.seq (.assign "iwK" (.add (.var "rk") (.lit 1))) (.seq (.assign "iwq" (.var "rk"))
  (.seq (.assign "iwl" (.lit 1)) (forUp "gi" (.var "gn") fwTree)))))

theorem length_fw0 (n q : ℕ) (c : ℕ → ℕ) : (fw0 n q c).length = 1 + n * (iL q + 3) := by
  simp only [fw0, List.length_cons]
  rw [length_flatMap_const (m := iL q + 3) (fun k => by
    simp only [List.length_append, List.length_cons, List.length_nil, length_initWord]; omega)]; omega

/-- The context of the loop over the vertices. -/
structure FWCtx (n gl q cap capF : ℕ) (U : List ℕ) (τ : Env) : Prop where
  gn : τ.vars "gn" = n
  gL : τ.vars "gL" = gl
  rk : τ.vars "rk" = q
  iwK : τ.vars "iwK" = 1 + q
  iwq : τ.vars "iwq" = q
  iwl : τ.vars "iwl" = 1
  U : τ.arrs "U" = U
  FW : (τ.arrs "FW").length = capF
  ta : (τ.arrs "ta").length = cap
  tb : (τ.arrs "tb").length = cap

theorem FWCtx.frame {n gl q cap capF : ℕ} {U : List ℕ} {τ τ' : Env} (h : FWCtx n gl q cap capF U τ)
    (hv : ∀ y ∈ ["gn", "gL", "rk", "iwK", "iwq", "iwl"], τ'.vars y = τ.vars y)
    (hU : τ'.arrs "U" = τ.arrs "U") (hF : (τ'.arrs "FW").length = (τ.arrs "FW").length)
    (ha : (τ'.arrs "ta").length = (τ.arrs "ta").length)
    (hb : (τ'.arrs "tb").length = (τ.arrs "tb").length) : FWCtx n gl q cap capF U τ' :=
  ⟨by rw [hv _ (by simp), h.gn], by rw [hv _ (by simp), h.gL], by rw [hv _ (by simp), h.rk],
    by rw [hv _ (by simp), h.iwK], by rw [hv _ (by simp), h.iwq], by rw [hv _ (by simp), h.iwl],
    by rw [hU, h.U], by rw [hF, h.FW], by rw [ha, h.ta], by rw [hb, h.tb]⟩

theorem fwTree_run {B n gl q cap capF k : ℕ} {U : List ℕ} {c : ℕ → ℕ} {l : List ℕ} {τ : Env}
    (hC : FWCtx n gl q cap capF U τ) (hk : τ.vars "gi" = k) (hkn : k < n)
    (hU : U[gl + 1 + k]? = some (c k)) (hcB : 4 * iL q + c k + 20 < B)
    (hcap : iL q ≤ cap) (hF : Filled "FW" "pf" l τ) (hl : l.length + iL q + 3 ≤ capF)
    (hlB : l.length + iL q + 3 < B) (hgB : gl + 1 + n < B) (hqB : q < B) :
    ∃ τ', Run B fwTree τ τ' (initCost q + 38) ∧ FWCtx n gl q cap capF U τ' ∧
      τ'.vars "gi" = k ∧ Filled "FW" "pf" (l ++ ([1, q, 1] ++ initWord 1 q 1 (c k))) τ' := by
  -- the header
  obtain ⟨τ₁, r₁, F₁, fv₁, fa₁, fl₁, -, -⟩ := pushL_run (B := B) (es := [.lit 1, .var "rk", .lit 1])
    (vs := [1, q, 1]) hF (fun τ' hv _ => by
      refine List.Forall₂.cons (evalB_lit (by omega)) (List.Forall₂.cons
        (ev_var (by rw [hv _ (by decide), hC.rk]) hqB) (List.Forall₂.cons (evalB_lit (by omega))
        List.Forall₂.nil)))
    (by simp; rw [hC.FW]; omega) (by simp; omega)
  have C₁ : FWCtx n gl q cap capF U τ₁ := hC.frame (fun y hy => fv₁ y (by
    simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) (fa₁ _ (by decide))
    fl₁ (by rw [fa₁ _ (by decide)]) (by rw [fa₁ _ (by decide)])
  have hk₁ : τ₁.vars "gi" = k := by rw [fv₁ _ (by decide), hk]
  -- the color
  have hcol : (Expr.get "U" (.add (.add (.var "gL") (.lit 1)) (.var "gi"))).evalB B τ₁ =
      some (c k) := evalB_get (ev_add (ev_add (ev_var C₁.gL (by omega)) (evalB_lit (by omega))
        (by omega)) (ev_var hk₁ (by omega)) (by omega)) (by rw [C₁.U]; exact hU) (by omega)
  set τ₂ := τ₁.setVar "iwc" (c k) with hτ₂
  have r₂ : Run B (.assign "iwc" (.get "U" (.add (.add (.var "gL") (.lit 1)) (.var "gi")))) τ₁ τ₂ 7 :=
    (Run.assign hcol).mono (by simp)
  have hB₂ : BCtx (1 + q) q 1 (c k) cap τ₂ :=
    ⟨by simp [hτ₂, C₁.iwK], by simp [hτ₂, C₁.iwq], by simp [hτ₂, C₁.iwl], by simp [hτ₂],
      by simp [hτ₂, C₁.ta], by simp [hτ₂, C₁.tb]⟩
  -- the tree
  obtain ⟨τ₃, r₃, B₃, F₃⟩ := buildInit_initWord (B := B) (k := 1) hB₂ le_rfl hcap hcB
  have fv₃ : ∀ y ∈ ["gn", "gL", "rk", "iwK", "iwq", "iwl", "gi", "pf"], τ₃.vars y = τ₂.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact r₃.frame_var _ (by decide)
  have C₃ : FWCtx n gl q cap capF U τ₃ := by
    have C₂ : FWCtx n gl q cap capF U τ₂ := C₁.frame (fun y hy => by
      simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hτ₂]) (by simp [hτ₂])
      (by simp [hτ₂]) (by simp [hτ₂]) (by simp [hτ₂])
    exact C₂.frame (fun y hy => fv₃ y (by simp at hy ⊢; tauto))
      (r₃.frame_arr _ (by decide)) (by rw [r₃.frame_arr _ (by decide)])
      (by rw [B₃.lta, C₂.ta]) (by rw [B₃.ltb, C₂.tb])
  have F₃' : Filled "FW" "pf" (l ++ [1, q, 1]) τ₃ :=
    (F₁.setVar (by decide) _).congr (fv₃ "pf" (by simp)) (r₃.frame_arr _ (by decide))
  -- the copy
  set w := initWord 1 q 1 (c k) with hw
  have hwl : w.length = iL q := length_initWord q (c k)
  let P : Env → Prop := fun ρ => ρ.vars "iwn" = iL q ∧ ρ.arrs "ta" = τ₃.arrs "ta" ∧
    (ρ.arrs "FW").length = capF
  obtain ⟨τ₄, r₄, -, -, F₄⟩ := forUp_push1 (B := B) (N := iL q) (cap := capF) (i := "gc") (a := "FW")
    (pv := "pf") (e := .get "ta" (.var "gc")) (bnd := .var "iwn") (by decide) (fun j => w.getD j 0) P
    (fun ρ v h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩)
    (fun ρ ρ' h fv fa fl => ⟨by rw [fv _ (by decide), h.1], by rw [fa _ (by decide), h.2.1],
      by rw [fl, h.2.2]⟩) (fun ρ h => h.2.2) (by omega)
    ⟨by rw [F₃.pos, hwl], rfl, C₃.FW⟩ F₃' (fun ρ h => ev_var h.1 (by omega))
    (fun j hj ρ h hj' => by
      have hjw : j < w.length := by omega
      have hent := initWord_entry (List.getElem_mem hjw)
      refine evalB_get (ev_var hj' (by omega)) ?_ (by rw [List.getD_eq_getElem _ _ hjw]; omega)
      rw [h.2.1, F₃.get j hjw, List.getD_eq_getElem _ _ hjw])
    (by simp; omega) (by simp; omega)
  have fv₄ : ∀ y, y ≠ "gc" → y ≠ "pf" → τ₄.vars y = τ₃.vars y := fun y h1 h2 =>
    r₄.frame_var y (by simp [forUp, push1, Com.wvars, h1, h2])
  refine ⟨τ₄, ?_, C₃.frame (fun y hy => fv₄ y (by simp at hy; rcases hy with rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide) (by simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
      (r₄.frame_arr _ (by decide)) (run_length_arrs r₄ _) (by rw [r₄.frame_arr _ (by decide)])
      (by rw [r₄.frame_arr _ (by decide)]), ?_, ?_⟩
  · unfold fwTree
    refine (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ r₄))).mono ?_
    simp only [initCost, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Expr.size]
    unfold iL
    generalize (q + 1) * (lvlCost (lvlLen (1 + q) q 1 q) + 100 * (lvlLen (1 + q) q 1 q + 1) + 60) = T
    omega
  · rw [fv₄ _ (by decide) (by decide), fv₃ _ (by simp)]; simp [hτ₂, hk₁]
  · have := flatMap_getD w
    rw [hwl] at this
    rw [this] at F₄
    simpa using F₄

theorem fwInit_run {B n gl q cap capF : ℕ} {c : ℕ → ℕ} {σ : Env} (hn : σ.vars "gn" = n)
    (hgl : σ.vars "gL" = gl) (hq : σ.vars "rk" = q)
    (hU : ∀ k < n, (σ.arrs "U")[gl + 1 + k]? = some (c k)) (hc : ∀ k < n, 4 * iL q + c k + 20 < B)
    (hta : (σ.arrs "ta").length = cap) (htb : (σ.arrs "tb").length = cap) (hcap : iL q ≤ cap)
    (hF : (σ.arrs "FW").length = capF) (hl : 1 + n * (iL q + 3) ≤ capF)
    (hlB : 1 + n * (iL q + 3) < B) (hgB : gl + 1 + n < B) (hqB : q + 1 < B) :
    ∃ σ', Run B fwInit σ σ' (n * (initCost q + 46) + 30) ∧ Filled "FW" "pf" (fw0 n q c) σ' := by
  set σ₀ := σ.setVar "pf" 0 with hσ₀
  obtain ⟨σ₁, r₁, F₁, fv₁, fa₁, fl₁, -, -⟩ := push1_run (B := B) (Filled.empty "FW" "pf" σ)
    (e := .var "gn") (v := n) (ev_var (by simp [hn]) (by omega)) (by simp; omega) (by simp; omega)
  have hq₁ : σ₁.vars "rk" = q := by rw [fv₁ _ (by decide)]; simp [hq]
  set σ₄ := ((σ₁.setVar "iwK" (q + 1)).setVar "iwq" q).setVar "iwl" 1 with hσ₄
  have C₄ : FWCtx n gl q cap capF (σ.arrs "U") σ₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hσ₄, fv₁ _ (by decide : "gn" ≠ "pf"), fv₁ _ (by decide : "gL" ≠ "pf"),
        fv₁ _ (by decide : "rk" ≠ "pf"), fa₁ _ (by decide : "U" ≠ "FW"), fa₁ _ (by decide : "ta" ≠ "FW"),
        fa₁ _ (by decide : "tb" ≠ "FW"), fl₁, hn, hgl, hq, hta, htb, hF]
    omega
  have F₄ : Filled "FW" "pf" ([] ++ [n]) σ₄ :=
    ((F₁.setVar (y := "iwK") (by decide) (q + 1)).setVar (y := "iwq") (by decide) q).setVar
      (y := "iwl") (by decide) 1
  obtain ⟨σ', r₃, -, -, F'⟩ := forUp_append (B := B) (i := "gi") (e := .var "gn") (body := fwTree)
    (N := n) (K := initCost q + 38) (a := "FW") (pv := "pf") (by decide)
    (fun k => [1, q, 1] ++ initWord 1 q 1 (c k)) (FWCtx n gl q cap capF (σ.arrs "U"))
    (fun τ v h => h.frame (fun y hy => by
      simp at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp) (by simp)
      (by simp) (by simp)) (by omega) C₄ F₄ (fun τ h => ev_var h.gn (by omega))
    (fun k hk τ h hik hF => by
      have hlen : ([] ++ [n] ++ (List.range k).flatMap fun k => [1, q, 1] ++ initWord 1 q 1 (c k)).length =
          1 + k * (iL q + 3) := by
        rw [List.length_append, length_flatMap_const (m := iL q + 3) (fun j => by
          simp only [List.length_append, List.length_cons, List.length_nil, length_initWord]; omega)]
        simp
      have hkk : (k + 1) * (iL q + 3) ≤ n * (iL q + 3) := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨τ', r, C', hk', F'⟩ := fwTree_run (B := B) h hik hk (hU k hk) (hc k hk) hcap hF
        (by rw [hlen]; nlinarith) (by rw [hlen]; nlinarith) hgB (by omega)
      refine ⟨τ', r, hk', C', ?_⟩
      rw [flatMap_range_succ', ← List.append_assoc]; exact F')
  refine ⟨σ', ?_, by simpa [fw0] using F'⟩
  unfold fwInit
  refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₁
    (Run.seq (Run.assign (ev_add (ev_var hq₁ (by omega)) (evalB_lit (by omega)) (by omega)))
    (Run.seq (Run.assign (ev_var (by simp [hq₁]) (by omega)))
    (Run.seq (Run.assign (evalB_lit (by omega))) r₃))))).mono ?_
  simp only [Expr.size]
  nlinarith

end Lax185574Proofs.MC.Glue
