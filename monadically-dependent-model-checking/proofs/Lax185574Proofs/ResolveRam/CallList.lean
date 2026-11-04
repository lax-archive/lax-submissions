import Lax185574Proofs.ResolveRam.FarFilter
import Lax185574Proofs.ResolveRam.AtomList

/-!
The calls of the program of lem:resolve-lift, in the order of the
program.

The data of the resolve are fixed as `dataOf` (the colors that occur,
the distances between color classes in `G`, and `σ = stp_{k₀,q₀}`). The
levels are those of the script with the expansion `exR`, built from the
answers `shOf`, `faOf`, `coOf` of the callees, with the far tree filtered
by the test `passF` (`faP`). The calls are, if `G` has
a vertex:

* one call of lem:compute-stp on the input,
* top down, for every item of level `d < q₀`: the rank shift of its
  tree, the far tree of its tree from `stpCut (k+1) σ`, and one
  composition of the shifted tree with every member of the far tree that
  passes the test `passF`,
* bottom up, for every item of level `d ≤ q₀`: the canonical form of
  the words of its new atoms, and if `d < q₀`, the canonical form of the
  words of its children with their guards.

`callInst` shows that every call is an instance of the statement of its
callee: the trees are trees of tuples of `G` at the right ranks, and the
far vertices of the compositions are far.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### The canonical form of a list of words -/

/-- A word that is its own encoding. -/
structure RawW where
  /-- The word. -/
  w : List ℕ

instance : WordEncoding RawW := ⟨RawW.w⟩

/-- The canonical form of a list of words: the sorted list of the
distinct words. -/
def canonW (ws : List (List ℕ)) : List ℕ := toWord (ws.toFinset.sort (· ≤ ·))

theorem toWord_finset_list {α : Type*} [WordEncoding α] [DecidableEq α] (l : List α) :
    toWord l.toFinset = canonW (l.map toWord) := by
  show toWord (Finset.words l.toFinset) = _
  unfold Finset.words canonW
  congr 2
  ext w
  simp

theorem toWord_finsetOf_list {α : Type*} [WordEncoding α] (l : List α) :
    toWord (finsetOf {x | x ∈ l}) = canonW (l.map toWord) := by
  classical
  rw [finsetOf_list, toWord_finset_list]

/-- The canonical form of the words `ws` is the answer of the canonical
form on the list of the raw words. -/
theorem canonW_raw (ws : List (List ℕ)) :
    toWord (finsetOf {x | x ∈ ws.map RawW.mk}) = canonW ws ∧
      (ws.map RawW.mk).map toWord = ws := by
  have h : (ws.map RawW.mk).map toWord = ws := by
    rw [List.map_map]
    exact List.map_id' ws |>.symm ▸ (by rfl)
  exact ⟨by rw [toWord_finsetOf_list, h], h⟩

/-! ### The data and the script -/

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

open Classical in
/-- Whether some vertex of color `X` is within distance `r` of some
vertex of color `Y` in `G`. -/
noncomputable def cdSem (X Y r : ℕ) : Bool :=
  decide (∃ x y, G.color x = X ∧ G.color y = Y ∧ WithinDist G.resolved r x y)

/-- The data of the resolve. -/
noncomputable def dataOf : ResolveData := ⟨P, Q, s, colsCore G.color, cdSem G, stp G k₀ q₀⟩

theorem dataOf_spec : (dataOf G P Q s k₀ q₀).Spec G k₀ q₀ := by
  refine ⟨fun Y => ?_, fun X Y r => ?_, rfl⟩
  · simp [dataOf, colsCore, Occurs]
  · simp [dataOf, cdSem]

/-- The colors that occur, sorted. -/
noncomputable def colsL : List ℕ := (colsCore G.color).sort (· ≤ ·)

theorem mem_colsL (Y : ℕ) : Y ∈ colsL G ↔ Y ∈ (dataOf G P Q s k₀ q₀).cols := by
  simp [colsL, dataOf]

/-- The expansion of the program. -/
noncomputable def exR : TypeTree → List (ℕ × TypeTree) :=
  exG (dataOf G P Q s k₀ q₀) (shOf G) (faP G (dataOf G P Q s k₀ q₀)) (coOf G)

/-- Level `d`. -/
noncomputable def lvR (d : ℕ) : List Item := levels (exR G P Q s k₀ q₀) (famItems G k₀ q₀) d

/-- The outputs of level `d`, when `m` levels lie below it. -/
noncomputable def outR (m d : ℕ) : List TypeTree :=
  outsAt (dataOf G P Q s k₀ q₀) (exR G P Q s k₀ q₀) (famItems G k₀ q₀) m d

theorem expandOK_exR :
    ExpandOK G (dataOf G P Q s k₀ q₀) (farMapOf G) (exR G P Q s k₀ q₀) k₀ q₀ :=
  expandOK_faP _ (dataOf_spec G P Q s k₀ q₀)

theorem lvR_good (hk₀ : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    GoodAt G k₀ q₀ d x := by
  refine levels_good _ (farMapOf G) (dataOf_spec G P Q s k₀ q₀) (farSpec_farMapOf G)
    (expandOK_exR G P Q s k₀ q₀) ?_ d hd x hx
  intro x hx
  simp only [famItems, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  exact ⟨1, ![b], by simp [family], le_rfl, hk₀⟩

/-! ### The calls -/

/-- A call: the scatter type, the rank shift or the far tree of a tree,
the composition of two trees, or the canonical form of a list of
words. -/
inductive RCall
  | stp
  | shift (τ : TypeTree)
  | ftree (τ : TypeTree)
  | compose (σ ν : TypeTree)
  | canon (ws : List (List ℕ))

/-- The words of the new atoms of a tree. -/
noncomputable def atomQ (τ : TypeTree) : List (List ℕ) :=
  (atomL (dataOf G P Q s k₀ q₀) τ.k τ.q (colsL G) τ.root).map toWord

/-- The words of the children of item `i` of level `d`, with their
guards. -/
noncomputable def kidQ (d i : ℕ) : TypeTree → List (List ℕ)
  | ⟨_, q + 1, ℓ, _⟩ =>
    (kidL q ℓ (kidsOf (lvR G P Q s k₀ q₀ (d + 1)) (outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1)) i)).map
      toWord
  | ⟨_, 0, _, _⟩ => []

/-- The calls of an item on the way down. -/
noncomputable def downCalls (x : Item) : List RCall :=
  [.shift x.2, .ftree x.2] ++
    (faP G (dataOf G P Q s k₀ q₀) x.2).map (RCall.compose (shOf G x.2))

/-- The calls of item `i` of level `d` on the way up. -/
noncomputable def upCalls (d : ℕ) (y : Item × ℕ) : List RCall :=
  .canon (atomQ G P Q s k₀ q₀ y.1.2) ::
    if d < q₀ then [.canon (kidQ G P Q s k₀ q₀ d y.2 y.1.2)] else []

/-- The calls on the way down. -/
noncomputable def downAll : List RCall :=
  (List.range q₀).flatMap fun d => (lvR G P Q s k₀ q₀ d).flatMap (downCalls G P Q s k₀ q₀)

/-- The calls on the way up. -/
noncomputable def upAll : List RCall :=
  (List.range (q₀ + 1)).reverse.flatMap fun d => (lvR G P Q s k₀ q₀ d).zipIdx.flatMap
    (upCalls G P Q s k₀ q₀ d)

/-- **The calls of the program.** -/
noncomputable def rcalls : List RCall :=
  if n = 0 then [] else RCall.stp :: (downAll G P Q s k₀ q₀ ++ upAll G P Q s k₀ q₀)

/-- A call is an instance of the statement of its callee. -/
def CallInst : RCall → Prop
  | .stp => 1 ≤ n
  | .shift τ => ∃ d < q₀, ∃ (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ ∧ ℓ ≤ k₀ + d ∧
      τ = tree G (k₀ + d) (q₀ - d - 1 + 1) u
  | .ftree τ => ∃ d < q₀, ∃ (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ ∧ ℓ ≤ k₀ + d ∧
      τ = tree G (k₀ + d) (q₀ - d - 1 + 1) u
  | .compose σ ν => ∃ d < q₀, ∃ (ℓ : ℕ) (u : Fin ℓ → Fin n) (b : Fin n), 1 ≤ ℓ ∧ ℓ ≤ k₀ + d ∧
      (∀ i, ¬ WithinDist G.resolved (rhoMinus (k₀ + d + 1) (q₀ - d - 1)) (u i) b) ∧
      σ = tree G (k₀ + d + 1) (q₀ - d - 1) u ∧ ν = tree G (k₀ + d + 1) (q₀ - d - 1) ![b]
  | .canon _ => True

theorem callInst_down (hk₀ : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    ∀ c ∈ downCalls G P Q s k₀ q₀ x, CallInst G k₀ q₀ c := by
  obtain ⟨ℓ, u, hu, h1, hk⟩ := lvR_good G P Q s k₀ q₀ hk₀ hd.le hx
  have hq : q₀ - d = q₀ - d - 1 + 1 := by omega
  rw [hq] at hu
  intro c hc
  simp only [downCalls, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at hc
  rcases hc with (rfl | rfl) | ⟨ν, hν, rfl⟩
  · exact ⟨d, hd, ℓ, u, h1, hk, hu⟩
  · exact ⟨d, hd, ℓ, u, h1, hk, hu⟩
  · have hfa := (ansOK_of G k₀ q₀).fa (k₀ + d) (q₀ - d - 1) ℓ u h1 hk (by omega) (by omega) ν
    rw [← hu] at hfa
    obtain ⟨b, hb, rfl⟩ := (mem_ftree (G := G) (k₀ + d) (q₀ - d - 1) u ν).1 (hfa.1 (List.mem_filter.1 hν).1)
    refine ⟨d, hd, ℓ, u, b, h1, hk, hb, ?_, rfl⟩
    rw [hu, shOf_tree G u h1 hk]

/-- **Every call is an instance of its callee.** -/
theorem callInst (hk₀ : 1 ≤ k₀) (c : RCall) (hc : c ∈ rcalls G P Q s k₀ q₀) : CallInst G k₀ q₀ c := by
  unfold rcalls at hc
  split_ifs at hc with hn
  · simp at hc
  rcases List.mem_cons.1 hc with rfl | hc
  · show 1 ≤ n; omega
  rcases List.mem_append.1 hc with hc | hc
  · simp only [downAll, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨d, hd, x, hx, hc⟩ := hc
    exact callInst_down G P Q s k₀ q₀ hk₀ hd hx c hc
  · simp only [upAll, List.mem_flatMap, List.mem_reverse, List.mem_range] at hc
    obtain ⟨d, -, y, -, hc⟩ := hc
    simp only [upCalls] at hc
    split_ifs at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; trivial

end Lax185574Proofs.ResolveRam
