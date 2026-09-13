import Lax17Proofs.Source.Exponent7.CleanBridgeBatch

namespace Lax17Proofs

/-!
# Prescribed-matching dichotomy

The clean bridge-batch theorem produces linearly many simultaneous row-to-row
bridges but chooses their matching. The short-wide path-of-sets argument
requires the alternating prescribed matchings

`(0,1), (2,3), ...` and `(1,2), (3,4), ...`.

`CleanMatchingDichotomyStatement reserve` states this requirement. Results
that use it take its proof as an explicit hypothesis.
-/

namespace SimpleGraph
namespace Exponent7

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {S T : Finset V}

/-- A finite matching on a finite vertex type.  The edge type retains
occurrences, while `endpoint_disjoint` says that distinct occurrences have
four distinct endpoints. -/
structure RowMatching (ι : Type v) [Fintype ι] [DecidableEq ι] where
  EdgeIndex : Type
  [edgeFintype : Fintype EdgeIndex]
  [edgeDecidableEq : DecidableEq EdgeIndex]
  left : EdgeIndex → ι
  right : EdgeIndex → ι
  left_ne_right : ∀ e, left e ≠ right e
  endpoint_disjoint :
    Pairwise fun e f =>
      Disjoint ({left e, right e} : Finset ι)
        ({left f, right f} : Finset ι)

namespace RowMatching

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

instance (M : RowMatching ι) : Fintype M.EdgeIndex :=
  M.edgeFintype

instance (M : RowMatching ι) : DecidableEq M.EdgeIndex :=
  M.edgeDecidableEq

/-- Number of matching edges. -/
def card (M : RowMatching ι) : ℕ :=
  Fintype.card M.EdgeIndex

/-- Every matching edge has both endpoints in the endpoint set. -/
noncomputable def endpointSet (M : RowMatching ι) : Finset ι :=
  Finset.univ.biUnion fun e : M.EdgeIndex => {M.left e, M.right e}

theorem left_mem_endpointSet (M : RowMatching ι) (e : M.EdgeIndex) :
    M.left e ∈ M.endpointSet := by
  classical
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by simp⟩

theorem right_mem_endpointSet (M : RowMatching ι) (e : M.EdgeIndex) :
    M.right e ∈ M.endpointSet := by
  classical
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, by simp⟩

end RowMatching

/-- A realization of a prescribed matching by simultaneous clean bridges
between selected paths of `R`.

The selected paths are indexed by `ι` and embedded injectively in `R.Index`.
Every bridge stays in `C`, its internal vertices avoid every selected row, and
the bridge paths are pairwise node-disjoint. -/
structure CleanMatchingRealization
    (R : PathPacking G S T)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (row : ι ↪ R.Index) (M : RowMatching ι) (C : Finset V) where
  path : M.EdgeIndex → GraphPath G
  source_mem :
    ∀ e, (path e).source ∈ (R.path (row (M.left e))).vertexSet
  target_mem :
    ∀ e, (path e).target ∈ (R.path (row (M.right e))).vertexSet
  staysIn :
    ∀ e, (path e).vertexSet ⊆ C
  internallyDisjoint_selectedRows :
    ∀ e,
      (path e).InternallyDisjointFromSet
        (selectedRowVertexSet R
          ((Finset.univ : Finset ι).image row))
  node_disjoint :
    Pairwise fun e f => GraphPath.NodeDisjoint (path e) (path f)

namespace CleanMatchingRealization

variable
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {R : PathPacking G S T} {row : ι ↪ R.Index}
    {M : RowMatching ι} {C : Finset V}

/-- Forget the prescribed names and view a realization as a clean bridge
batch.  This is useful for consumers which only need simultaneous
disjointness. -/
noncomputable def toCleanBridgeBatch
    (B : CleanMatchingRealization R row M C) :
    CleanBridgeBatch R ((Finset.univ : Finset ι).image row) := by
  classical
  let used : Finset R.Index := M.endpointSet.image row
  refine
    { BridgeIndex := M.EdgeIndex
      usedRows := used
      usedRows_subset := ?_
      left := fun e => row (M.left e)
      right := fun e => row (M.right e)
      left_mem := ?_
      right_mem := ?_
      left_ne_right := ?_
      row_pairs_disjoint := ?_
      path := B.path
      source_mem := B.source_mem
      target_mem := B.target_mem
      internallyDisjoint_usedRows := ?_
      node_disjoint := B.node_disjoint }
  · intro r hr
    rcases Finset.mem_image.mp hr with ⟨x, _hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · intro e
    exact Finset.mem_image.mpr
      ⟨M.left e, M.left_mem_endpointSet e, rfl⟩
  · intro e
    exact Finset.mem_image.mpr
      ⟨M.right e, M.right_mem_endpointSet e, rfl⟩
  · intro e h
    exact M.left_ne_right e (row.injective h)
  · intro e f hef
    rw [Finset.disjoint_left]
    intro r hre hrf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hre hrf
    have hbad := Finset.disjoint_left.mp (M.endpoint_disjoint hef)
    rcases hre with hre | hre <;> rcases hrf with hrf | hrf
    · exact (hbad (a := M.left e) (by simp)) (by
        have h := row.injective (hre.symm.trans hrf)
        simpa [h] using
          (show M.left f ∈ ({M.left f, M.right f} : Finset ι) by simp))
    · exact (hbad (a := M.left e) (by simp)) (by
        have h := row.injective (hre.symm.trans hrf)
        simpa [h] using
          (show M.right f ∈ ({M.left f, M.right f} : Finset ι) by simp))
    · exact (hbad (a := M.right e) (by simp)) (by
        have h := row.injective (hre.symm.trans hrf)
        simpa [h] using
          (show M.left f ∈ ({M.left f, M.right f} : Finset ι) by simp))
    · exact (hbad (a := M.right e) (by simp)) (by
        have h := row.injective (hre.symm.trans hrf)
        simpa [h] using
          (show M.right f ∈ ({M.left f, M.right f} : Finset ι) by simp))
  · intro e
    intro v hvPath hv
    apply B.internallyDisjoint_selectedRows e hvPath
    rcases (mem_selectedRowVertexSet R used).1 hv with
      ⟨r, hr, hvr⟩
    apply (mem_selectedRowVertexSet R
      ((Finset.univ : Finset ι).image row)).2
    exact ⟨r, by
      rcases Finset.mem_image.mp hr with ⟨x, _hx, rfl⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, hvr⟩

end CleanMatchingRealization

/-! ## The two canonical alternating matchings -/

/-- Matching `(0,1), (2,3), ...` on `Fin g`. -/
def oddRowMatching (g : ℕ) : RowMatching (Fin g) where
  EdgeIndex := Fin (g / 2)
  left := fun e => ⟨2 * e.1, by
    have hdiv := Nat.mul_div_le g 2
    omega⟩
  right := fun e => ⟨2 * e.1 + 1, by
    have hdiv := Nat.mul_div_le g 2
    omega⟩
  left_ne_right := by
    intro e h
    have h' : 2 * e.1 = 2 * e.1 + 1 := congrArg Fin.val h
    omega
  endpoint_disjoint := by
    intro e f hef
    rw [Finset.disjoint_left]
    intro x hxe hxf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe hxf
    rcases hxe with hxe | hxe <;> rcases hxf with hxf | hxf
    · have hval :
          2 * e.1 = 2 * f.1 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      apply hef
      apply Fin.ext
      omega
    · have hval :
          2 * e.1 = 2 * f.1 + 1 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      omega
    · have hval :
          2 * e.1 + 1 = 2 * f.1 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      omega
    · have hval :
          2 * e.1 + 1 = 2 * f.1 + 1 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      apply hef
      apply Fin.ext
      omega

@[simp] theorem oddRowMatching_card (g : ℕ) :
    (oddRowMatching g).card = g / 2 := by
  change Fintype.card (Fin (g / 2)) = g / 2
  exact Fintype.card_fin (g / 2)

/-- Matching `(1,2), (3,4), ...` on `Fin g`. -/
def evenRowMatching (g : ℕ) : RowMatching (Fin g) where
  EdgeIndex := Fin ((g - 1) / 2)
  left := fun e => ⟨2 * e.1 + 1, by
    have hdiv := Nat.mul_div_le (g - 1) 2
    omega⟩
  right := fun e => ⟨2 * e.1 + 2, by
    have hdiv := Nat.mul_div_le (g - 1) 2
    omega⟩
  left_ne_right := by
    intro e h
    have h' : 2 * e.1 + 1 = 2 * e.1 + 2 :=
      congrArg Fin.val h
    omega
  endpoint_disjoint := by
    intro e f hef
    rw [Finset.disjoint_left]
    intro x hxe hxf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe hxf
    rcases hxe with hxe | hxe <;> rcases hxf with hxf | hxf
    · have hval :
          2 * e.1 + 1 = 2 * f.1 + 1 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      apply hef
      apply Fin.ext
      omega
    · have hval :
          2 * e.1 + 1 = 2 * f.1 + 2 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      omega
    · have hval :
          2 * e.1 + 2 = 2 * f.1 + 1 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      omega
    · have hval :
          2 * e.1 + 2 = 2 * f.1 + 2 :=
        congrArg Fin.val (hxe.symm.trans hxf)
      apply hef
      apply Fin.ext
      omega

@[simp] theorem evenRowMatching_card (g : ℕ) :
    (evenRowMatching g).card = (g - 1) / 2 := by
  change Fintype.card (Fin ((g - 1) / 2)) = (g - 1) / 2
  exact Fintype.card_fin ((g - 1) / 2)

theorem evenRowMatching_card_le_half (g : ℕ) :
    (evenRowMatching g).card ≤ g / 2 := by
  simp
  omega

/-! ## Prescribed-matching hypothesis -/

/-- Prescribed-matching dichotomy for batching Appendix C.1 bridges.

The reserve constant is explicit, and the selected `g` rows may be any
injectively indexed subfamily of a larger cluster linkage. -/
def CleanMatchingDichotomyStatement (reserve : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (g : ℕ)
    {S T : Finset V} (R : PathPacking G S T)
    (C : Finset V) (row : Fin g ↪ R.Index)
    (M : RowMatching (Fin g)),
      2 ≤ g →
      reserve * g ^ 2 ≤ R.card →
      R.StaysIn C →
      NodeWellLinkedIn G C R.sourceSet →
      M.card ≤ g / 2 →
      ContainsGridMinor G g ∨
        Nonempty (CleanMatchingRealization R row M C)

/-- Specialize a prescribed-matching dichotomy to the odd matching. -/
theorem cleanOddMatching_or_grid
    {reserve : ℕ} (hD : CleanMatchingDichotomyStatement.{u} reserve)
    (G : _root_.SimpleGraph V) (g : ℕ)
    (R : PathPacking G S T) (C : Finset V)
    (row : Fin g ↪ R.Index)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ R.card)
    (hstay : R.StaysIn C)
    (hwell : NodeWellLinkedIn G C R.sourceSet) :
    ContainsGridMinor G g ∨
      Nonempty (CleanMatchingRealization R row (oddRowMatching g) C) :=
  hD (V := V) G g R C row (oddRowMatching g) hg hwidth hstay hwell
    (by simp)

/-- Specialize a prescribed-matching dichotomy to the even matching. -/
theorem cleanEvenMatching_or_grid
    {reserve : ℕ} (hD : CleanMatchingDichotomyStatement.{u} reserve)
    (G : _root_.SimpleGraph V) (g : ℕ)
    (R : PathPacking G S T) (C : Finset V)
    (row : Fin g ↪ R.Index)
    (hg : 2 ≤ g)
    (hwidth : reserve * g ^ 2 ≤ R.card)
    (hstay : R.StaysIn C)
    (hwell : NodeWellLinkedIn G C R.sourceSet) :
    ContainsGridMinor G g ∨
      Nonempty (CleanMatchingRealization R row (evenRowMatching g) C) :=
  hD (V := V) G g R C row (evenRowMatching g) hg hwidth hstay hwell
    (evenRowMatching_card_le_half g)

end Exponent7
end SimpleGraph

end Lax17Proofs
