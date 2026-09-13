import Lax10Proofs.Contract

/-!
# Local coloring lemmas

These lemmas are the coloring infrastructure used by the separator induction in
Theorem 3.
-/

namespace Lax10Proofs

universe u

variable {V : Type u}

/-- The fresh color left unused by $embedOldColor$. -/
def freshColor {m : Nat} (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩

/-- Embed the old palette $Fin (m - 1)$ into $Fin m$, leaving color $0$ fresh. -/
def embedOldColor {m : Nat} (hm : 0 < m) (i : Fin (m - 1)) : Fin m :=
  ⟨i.val + 1, by
    have hle : i.val + 1 ≤ m - 1 := Nat.succ_le_of_lt i.isLt
    exact lt_of_le_of_lt hle (Nat.sub_lt hm (by decide : 0 < 1))⟩

@[simp]
theorem embedOldColor_ne_fresh {m : Nat} (hm : 0 < m) (i : Fin (m - 1)) :
    embedOldColor hm i ≠ freshColor hm := by
  intro h
  have hval := congrArg Fin.val h
  simp [embedOldColor, freshColor] at hval

theorem embedOldColor_injective {m : Nat} (hm : 0 < m) :
    Function.Injective (embedOldColor (m := m) hm) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp [embedOldColor] at hval
  exact hval

namespace KColoring

/-- A coloring of a graph on a subsingleton vertex type. -/
def ofSubsingleton {m : Nat} (G : SimpleGraph V) [Subsingleton V] (hm : 0 < m) :
    KColoring m G where
  color _ := ⟨0, hm⟩
  valid := by
    intro x y hxy hcolor
    have hxy_eq : x = y := Subsingleton.elim x y
    subst y
    exact G.irrefl hxy

/-- Transfer a coloring of the top subgraph back to the ambient graph. -/
def ofTopCoe {m : Nat} {G : SimpleGraph V}
    (c : KColoring m (⊤ : G.Subgraph).coe) :
    KColoring m G where
  color x := c.color ⟨x, by simp [SimpleGraph.Subgraph.verts_top]⟩
  valid := by
    intro x y hxy
    exact c.valid
      (show (⊤ : G.Subgraph).coe.Adj
          ⟨x, by simp [SimpleGraph.Subgraph.verts_top]⟩
        ⟨y, by simp [SimpleGraph.Subgraph.verts_top]⟩ from by
        simpa [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.top_adj] using hxy)

/-- Pull a coloring back along a graph homomorphism. -/
def pullback {W : Type*} {m : Nat} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (c : KColoring m H) :
    KColoring m G where
  color x := c.color (f x)
  valid := by
    intro x y hxy
    exact c.valid (f.map_rel hxy)

/--
Starting from an $(m - 1)$-coloring, recolor an independent set with a fresh
color and shift all old colors away from that fresh color.
-/
noncomputable def recolorIndependent {m : Nat} {G : SimpleGraph V} [DecidableEq V]
    (hm : 0 < m) (c : KColoring (m - 1) G) (s : Finset V)
    (hindep : ∀ ⦃x y : V⦄, x ∈ s → y ∈ s → ¬ G.Adj x y) :
    KColoring m G where
  color x := if x ∈ s then freshColor hm else embedOldColor hm (c.color x)
  valid := by
    classical
    intro x y hxy hsame
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · exact hindep hx hy hxy
      · have hsame' : freshColor hm = embedOldColor hm (c.color y) := by
          simpa only [if_pos hx, if_neg hy] using hsame
        exact embedOldColor_ne_fresh hm (c.color y) hsame'.symm
    · by_cases hy : y ∈ s
      · have hsame' : embedOldColor hm (c.color x) = freshColor hm := by
          simpa only [if_neg hx, if_pos hy] using hsame
        exact embedOldColor_ne_fresh hm (c.color x) hsame'
      · have hsame' : embedOldColor hm (c.color x) = embedOldColor hm (c.color y) := by
          simpa only [if_neg hx, if_neg hy] using hsame
        exact c.valid hxy (embedOldColor_injective hm hsame')

/-- Reinterpret a coloring through an equality of graphs. -/
def castGraph {m : Nat} {G H : SimpleGraph V} (h : G = H) (c : KColoring m G) :
    KColoring m H where
  color := c.color
  valid := by
    intro x y hxy
    exact c.valid (h ▸ hxy)

/--
Glue two colorings across a separated cover.  The cover is expressed by vertex
sets $A$ and $B$; there are no edges from $A \ B$ to $B \ A$, and the two
side-colorings agree on the overlap.
-/
noncomputable def glueSeparated {m : Nat} {G : SimpleGraph V} (A B : Set V)
    (hcover : A ∪ B = Set.univ)
    (hsep : ∀ ⦃x y : V⦄, x ∈ A → x ∉ B → y ∈ B → y ∉ A → ¬ G.Adj x y)
    (cA : KColoring m (G.induce A)) (cB : KColoring m (G.induce B))
    (hagree : ∀ ⦃x : V⦄, (hxA : x ∈ A) → (hxB : x ∈ B) →
      cA.color ⟨x, hxA⟩ = cB.color ⟨x, hxB⟩) :
    KColoring m G where
  color x := by
    classical
    exact
      if hxA : x ∈ A then cA.color ⟨x, hxA⟩
      else
        cB.color ⟨x, by
          have hxAB : x ∈ A ∪ B := by
            simp [hcover]
          exact hxAB.resolve_left hxA⟩
  valid := by
    classical
    intro x y hxy hsame
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · exact cA.valid
          (show (G.induce A).Adj ⟨x, hxA⟩ ⟨y, hyA⟩ from hxy)
          (by simpa only [dif_pos hxA, dif_pos hyA] using hsame)
      · have hyB : y ∈ B := by
          have hyAB : y ∈ A ∪ B := by
            simp [hcover]
          exact hyAB.resolve_left hyA
        by_cases hxB : x ∈ B
        · have hx_eq : cA.color ⟨x, hxA⟩ = cB.color ⟨x, hxB⟩ := hagree hxA hxB
          have hsameA : cA.color ⟨x, hxA⟩ = cB.color ⟨y, hyB⟩ := by
            simpa only [dif_pos hxA, dif_neg hyA] using hsame
          have hsameB : cB.color ⟨x, hxB⟩ = cB.color ⟨y, hyB⟩ := by
            exact hx_eq.symm.trans hsameA
          exact cB.valid
            (show (G.induce B).Adj ⟨x, hxB⟩ ⟨y, hyB⟩ from hxy)
            hsameB
        · exact (hsep hxA hxB hyB hyA hxy).elim
    · have hxB : x ∈ B := by
        have hxAB : x ∈ A ∪ B := by
          simp [hcover]
        exact hxAB.resolve_left hxA
      by_cases hyA : y ∈ A
      · by_cases hyB : y ∈ B
        · have hy_eq : cA.color ⟨y, hyA⟩ = cB.color ⟨y, hyB⟩ := hagree hyA hyB
          have hsameA : cB.color ⟨x, hxB⟩ = cA.color ⟨y, hyA⟩ := by
            simpa only [dif_neg hxA, dif_pos hyA] using hsame
          have hsameB : cB.color ⟨x, hxB⟩ = cB.color ⟨y, hyB⟩ := by
            exact hsameA.trans hy_eq
          exact cB.valid
            (show (G.induce B).Adj ⟨x, hxB⟩ ⟨y, hyB⟩ from hxy)
            hsameB
        · exact (hsep hyA hyB hxB hxA hxy.symm).elim
      · have hyB : y ∈ B := by
          have hyAB : y ∈ A ∪ B := by
            simp [hcover]
          exact hyAB.resolve_left hyA
        exact cB.valid
          (show (G.induce B).Adj ⟨x, hxB⟩ ⟨y, hyB⟩ from hxy)
          (by simpa only [dif_neg hxA, dif_neg hyA] using hsame)

end KColoring

end Lax10Proofs
