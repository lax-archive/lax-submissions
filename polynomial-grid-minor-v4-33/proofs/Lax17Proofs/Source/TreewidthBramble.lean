import Lax17Proofs.Source.Treewidth
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Lax17Proofs

universe u v w

/-!
# Finite brambles and treewidth

This file develops the finite bramble interface used by the treewidth side of
the project.  A bramble is represented by a `Finset (Finset V)`.  Its members
are nonempty connected vertex sets and every two members touch, meaning that
they intersect or an edge has one endpoint in each member.

The singleton bramble associated to a clique gives an axiom-free source of
brambles with a sharp hitting-set lower bound.  In particular this proves the
treewidth--bramble lower bound for every graph whose treewidth is bounded by a
clique certificate, and for complete graphs (including the empty graph under
the repository's natural-number treewidth convention).
-/

namespace SimpleGraph

namespace TreewidthBramble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two finite vertex sets touch if they meet or some graph edge joins them. -/
def Touches (G : _root_.SimpleGraph V) (A B : Finset V) : Prop :=
  (A ∩ B).Nonempty ∨
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

namespace Touches

variable {G : _root_.SimpleGraph V} {A B C D : Finset V}

theorem refl (hA : A.Nonempty) : Touches G A A := by
  exact Or.inl (by simpa using hA)

theorem symm (h : Touches G A B) : Touches G B A := by
  rcases h with h | ⟨a, ha, b, hb, hab⟩
  · exact Or.inl (by simpa [Finset.inter_comm] using h)
  · exact Or.inr ⟨b, hb, a, ha, G.symm hab⟩

theorem mono (h : Touches G A B) (hAC : A ⊆ C) (hBD : B ⊆ D) :
    Touches G C D := by
  rcases h with h | ⟨a, ha, b, hb, hab⟩
  · obtain ⟨v, hv⟩ := h
    have ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
    exact Or.inl ⟨v, Finset.mem_inter.mpr ⟨hAC hvA, hBD hvB⟩⟩
  · exact Or.inr ⟨a, hAC ha, b, hBD hb, hab⟩

end Touches

/-- A finite set of vertices is a connected bramble piece. -/
def IsConnectedSet (G : _root_.SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (G.induce (A : Set V)).Connected

/-- A finite bramble, represented in the same form as the well-linked
development: a finite family of nonempty connected vertex finsets, pairwise
touching.  Quantifying also over equal members is equivalent to the customary
distinct-pair formulation because every member is nonempty. -/
def IsBramble (G : _root_.SimpleGraph V) (B : Finset (Finset V)) : Prop :=
  (∀ A ∈ B, IsConnectedSet G A) ∧
    ∀ A ∈ B, ∀ C ∈ B, Touches G A C

/-- `X` is a transversal (hitting set) of the finite family `B`. -/
def Hits (X : Finset V) (B : Finset (Finset V)) : Prop :=
  ∀ A ∈ B, (X ∩ A).Nonempty

/-- A bramble has order at least `k` if every hitting set has at least `k`
vertices.  This avoids choosing a minimum and is the form needed downstream. -/
def HasOrderAtLeast (G : _root_.SimpleGraph V) (B : Finset (Finset V))
    (k : ℕ) : Prop :=
  IsBramble G B ∧ ∀ X : Finset V, Hits X B → k ≤ X.card

/-- The graph has some finite bramble of order at least `k`. -/
def HasBrambleOrderAtLeast (G : _root_.SimpleGraph V) (k : ℕ) : Prop :=
  ∃ B : Finset (Finset V), HasOrderAtLeast G B k

namespace IsBramble

variable {G : _root_.SimpleGraph V} {B C : Finset (Finset V)}

theorem mono (hB : IsBramble G B) (hCB : C ⊆ B) : IsBramble G C := by
  constructor
  · intro A hA
    exact hB.1 A (hCB hA)
  · intro A hA D hD
    exact hB.2 A (hCB hA) D (hCB hD)

theorem member_nonempty (hB : IsBramble G B) {A : Finset V} (hA : A ∈ B) :
    A.Nonempty :=
  (hB.1 A hA).1

/-- The whole vertex set hits every bramble. -/
theorem hits_univ (hB : IsBramble G B) : Hits (Finset.univ : Finset V) B := by
  intro A hA
  simpa using hB.member_nonempty hA

end IsBramble

namespace HasOrderAtLeast

variable {G : _root_.SimpleGraph V} {B : Finset (Finset V)} {k l : ℕ}

theorem antitone (h : HasOrderAtLeast G B k) (hlk : l ≤ k) :
    HasOrderAtLeast G B l := by
  exact ⟨h.1, fun X hX => hlk.trans (h.2 X hX)⟩

theorem le_card_univ (h : HasOrderAtLeast G B k) : k ≤ Fintype.card V := by
  simpa using h.2 Finset.univ h.1.hits_univ

end HasOrderAtLeast

section TreeDecomposition

variable {G : _root_.SimpleGraph V} (D : TreeDecomposition G)

/-- Decomposition nodes whose bags meet a vertex set.  Sets are used here
rather than finsets because this is exactly the vertex set of an induced
subgraph of the decomposition tree. -/
def meetingNodes (A : Finset V) : Set D.Node :=
  {i | (D.bag i ∩ A).Nonempty}

theorem mem_meetingNodes_iff {A : Finset V} {i : D.Node} :
    i ∈ meetingNodes D A ↔ ∃ v ∈ D.bag i, v ∈ A := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  · rintro ⟨v, hvi, hvA⟩
    exact ⟨v, Finset.mem_inter.mpr ⟨hvi, hvA⟩⟩

/-- A walk contained in `A` lifts to reachability between any bags containing
its endpoints, while staying among bags that meet `A`. -/
theorem reachable_meetingNodes_of_walk {A : Finset V} {u v : V}
    (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ A)
    {i j : D.Node} (hui : u ∈ D.bag i) (hvj : v ∈ D.bag j) :
    (D.tree.induce (meetingNodes D A)).Reachable
      ⟨i, mem_meetingNodes_iff D |>.2 ⟨u, hui, hp u p.start_mem_support⟩⟩
      ⟨j, mem_meetingNodes_iff D |>.2 ⟨v, hvj, hp v p.end_mem_support⟩⟩ := by
  induction p generalizing i with
  | @nil x =>
      have hsub : {n : D.Node | x ∈ D.bag n} ⊆ meetingNodes D A := by
        intro n hn
        exact mem_meetingNodes_iff D |>.2
          ⟨x, hn, hp x (by simp)⟩
      have hreach := D.bag_indices_connected x ⟨i, hui⟩ ⟨j, hvj⟩
      simpa using hreach.map (D.tree.induceHomOfLE hsub).toHom
  | @cons u w v huw q ih =>
      obtain ⟨e, hue, hwe⟩ := D.edge_mem_bag huw
      have huA : u ∈ A := hp u (by simp)
      have hwA : w ∈ A := hp w (by simp)
      have hsub : {n : D.Node | u ∈ D.bag n} ⊆ meetingNodes D A := by
        intro n hn
        exact mem_meetingNodes_iff D |>.2 ⟨u, hn, huA⟩
      have hfirst0 := D.bag_indices_connected u ⟨i, hui⟩ ⟨e, hue⟩
      have hfirst := hfirst0.map (D.tree.induceHomOfLE hsub).toHom
      have hq : ∀ x ∈ q.support, x ∈ A := by
        intro x hx
        exact hp x (by simp [hx])
      have hsecond := ih hq hwe hvj
      simpa using hfirst.trans hsecond

/-- The bags meeting a nonempty connected vertex set induce a connected
subgraph of the decomposition tree. -/
theorem meetingNodes_connected {A : Finset V} (hA : IsConnectedSet G A) :
    (D.tree.induce (meetingNodes D A)).Connected := by
  rcases hA.1 with ⟨a, haA⟩
  rcases D.vertex_mem_bag a with ⟨root, haroot⟩
  have hroot : root ∈ meetingNodes D A :=
    mem_meetingNodes_iff D |>.2 ⟨a, haroot, haA⟩
  rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨root, hroot⟩, ?_⟩
  rintro ⟨j, hj⟩
  rcases (mem_meetingNodes_iff D).1 hj with ⟨v, hvj, hvA⟩
  obtain ⟨q⟩ := hA.2 ⟨a, haA⟩ ⟨v, hvA⟩
  let inc : G.induce (A : Set V) →g G :=
    ⟨Subtype.val, by
      intro x y hxy
      exact hxy⟩
  let p : G.Walk a v := q.map inc
  have hp : ∀ x ∈ p.support, x ∈ A := by
    intro x hx
    simp only [p, _root_.SimpleGraph.Walk.support_map, List.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  simpa [p] using reachable_meetingNodes_of_walk D p hp haroot hvj

/-- Touching vertex sets give intersecting subtrees of decomposition nodes. -/
theorem meetingNodes_inter_nonempty {A C : Finset V} (h : Touches G A C) :
    (meetingNodes D A ∩ meetingNodes D C).Nonempty := by
  rcases h with hAC | ⟨a, ha, c, hc, hac⟩
  · obtain ⟨v, hv⟩ := hAC
    have ⟨hvA, hvC⟩ := Finset.mem_inter.mp hv
    rcases D.vertex_mem_bag v with ⟨i, hvi⟩
    exact ⟨i, mem_meetingNodes_iff D |>.2 ⟨v, hvi, hvA⟩,
      mem_meetingNodes_iff D |>.2 ⟨v, hvi, hvC⟩⟩
  · rcases D.edge_mem_bag hac with ⟨i, hai, hci⟩
    exact ⟨i, mem_meetingNodes_iff D |>.2 ⟨a, hai, ha⟩,
      mem_meetingNodes_iff D |>.2 ⟨c, hci, hc⟩⟩

end TreeDecomposition

/-- The precise finite-tree Helly property needed by the easy half of bramble
duality.  It is stated independently so the graph-theoretic reduction below
does not depend on a particular proof of subtree Helly. -/
def FiniteSubtreeHelly (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∀ {N : Type} [Fintype N] [DecidableEq N]
    (T : _root_.SimpleGraph N) (S : I → Set N),
    T.IsTree →
    (∀ i, (T.induce (S i)).Connected) →
    (∀ i j, (S i ∩ S j).Nonempty) →
    ∃ n : N, ∀ i, n ∈ S i

/-- Assuming finite subtree Helly, one bag of every tree decomposition hits
every member of a bramble.  All graph-specific work is discharged by
`meetingNodes_connected` and `meetingNodes_inter_nonempty`. -/
theorem exists_bag_hits_bramble_of_finiteSubtreeHelly
    {G : _root_.SimpleGraph V} (D : TreeDecomposition G)
    {B : Finset (Finset V)} (hB : IsBramble G B)
    (hHelly : FiniteSubtreeHelly {A : Finset V // A ∈ B}) :
    ∃ i : D.Node, Hits (D.bag i) B := by
  classical
  letI : Fintype D.Node := D.nodeFintype
  letI : DecidableEq D.Node := D.nodeDecidableEq
  let I := {A : Finset V // A ∈ B}
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  have hcommon := @hHelly D.Node inferInstance inferInstance
    D.tree (fun A : I => meetingNodes D A.1) D.isTree
    (fun (A : I) => meetingNodes_connected D (hB.1 A.1 A.2))
    (fun (A C : I) =>
      meetingNodes_inter_nonempty D (hB.2 A.1 A.2 C.1 C.2))
  obtain ⟨i, hi⟩ := hcommon
  refine ⟨i, ?_⟩
  intro A hA
  exact hi ⟨A, hA⟩

/-- Every bag has size at most one more than the decomposition width. -/
theorem bag_card_le_width_add_one
    {G : _root_.SimpleGraph V} (D : TreeDecomposition G) (i : D.Node) :
    (D.bag i).card ≤ D.width + 1 := by
  classical
  letI : Fintype D.Node := D.nodeFintype
  letI : DecidableEq D.Node := D.nodeDecidableEq
  have hi : (D.bag i).card ≤
      Finset.univ.sup (fun j : D.Node => (D.bag j).card) := by
    exact Finset.le_sup (f := fun j : D.Node => (D.bag j).card) (by simp)
  dsimp [TreeDecomposition.width]
  omega

/-- Easy duality direction: under finite subtree Helly, the order of any
bramble is at most one more than the width of every tree decomposition. -/
theorem bramble_order_le_decomposition_width_add_one_of_finiteSubtreeHelly
    {G : _root_.SimpleGraph V} (D : TreeDecomposition G)
    {B : Finset (Finset V)} {k : ℕ} (hB : HasOrderAtLeast G B k)
    (hHelly : FiniteSubtreeHelly {A : Finset V // A ∈ B}) :
    k ≤ D.width + 1 := by
  obtain ⟨i, hi⟩ :=
    exists_bag_hits_bramble_of_finiteSubtreeHelly D hB.1 hHelly
  exact (hB.2 (D.bag i) hi).trans (bag_card_le_width_add_one D i)

/-- Easy treewidth--bramble duality direction: no finite bramble has order
greater than `treewidth G + 1`. -/
theorem bramble_order_le_treewidth_add_one_of_finiteSubtreeHelly
    {G : _root_.SimpleGraph V} {B : Finset (Finset V)} {k : ℕ}
    (hB : HasOrderAtLeast G B k)
    (hHelly : FiniteSubtreeHelly {A : Finset V // A ∈ B}) :
    k ≤ treewidth G + 1 := by
  rcases hasTreewidthAtMost_treewidth G with ⟨D, hD⟩
  have hk :=
    bramble_order_le_decomposition_width_add_one_of_finiteSubtreeHelly
      D hB hHelly
  omega

/-- The family of singleton vertex sets indexed by `K`. -/
def singletonFamily (K : Finset V) : Finset (Finset V) :=
  K.image fun v => {v}

@[simp] theorem mem_singletonFamily {K A : Finset V} :
    A ∈ singletonFamily K ↔ ∃ v ∈ K, A = {v} := by
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨v, hv, hvA⟩
    exact ⟨v, hv, hvA.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

@[simp] theorem singletonFamily_card (K : Finset V) :
    (singletonFamily K).card = K.card := by
  classical
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  simpa using hab

theorem isConnectedSet_singleton (G : _root_.SimpleGraph V) (v : V) :
    IsConnectedSet G {v} := by
  constructor
  · simp
  · letI : Nonempty (↥((({v} : Finset V) : Set V))) := ⟨⟨v, by simp⟩⟩
    letI : Subsingleton (↥((({v} : Finset V) : Set V))) := by
      constructor
      intro a b
      apply Subtype.ext
      have ha : a.1 = v := by simpa using a.2
      have hb : b.1 = v := by simpa using b.2
      exact ha.trans hb.symm
    exact _root_.SimpleGraph.Connected.of_subsingleton

/-- Singleton sets indexed by a clique form a bramble. -/
theorem isBramble_singletonFamily {G : _root_.SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) :
    IsBramble G (singletonFamily K) := by
  constructor
  · intro A hA
    rcases mem_singletonFamily.mp hA with ⟨v, _hv, rfl⟩
    exact isConnectedSet_singleton G v
  · intro A hA C hC
    rcases mem_singletonFamily.mp hA with ⟨a, ha, rfl⟩
    rcases mem_singletonFamily.mp hC with ⟨c, hc, rfl⟩
    by_cases hac : a = c
    · subst c
      exact Touches.refl (by simp)
    · exact Or.inr ⟨a, by simp, c, by simp, hK ha hc hac⟩

/-- A set hitting all singleton members indexed by `K` contains `K`. -/
theorem subset_of_hits_singletonFamily {K X : Finset V}
    (hX : Hits X (singletonFamily K)) : K ⊆ X := by
  intro v hv
  have hmem : ({v} : Finset V) ∈ singletonFamily K := by
    exact mem_singletonFamily.mpr ⟨v, hv, rfl⟩
  obtain ⟨w, hw⟩ := hX {v} hmem
  have ⟨hwX, hwv⟩ := Finset.mem_inter.mp hw
  have : w = v := by simpa using hwv
  simpa [this] using hwX

/-- The singleton bramble of a clique has order at least the clique size. -/
theorem singletonFamily_hasOrderAtLeast {G : _root_.SimpleGraph V}
    {K : Finset V} (hK : G.IsClique (K : Set V)) :
    HasOrderAtLeast G (singletonFamily K) K.card := by
  constructor
  · exact isBramble_singletonFamily hK
  · intro X hX
    exact Finset.card_le_card (subset_of_hits_singletonFamily hX)

/-- A clique whose size bounds the treewidth supplies the convention-compatible
lower-duality witness `treewidth G ≤ |X|` for every hitting set `X`. -/
theorem exists_bramble_hitting_card_ge_treewidth_of_clique
    {G : _root_.SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) (htw : treewidth G ≤ K.card) :
    ∃ B : Finset (Finset V),
      IsBramble G B ∧ ∀ X : Finset V, Hits X B → treewidth G ≤ X.card := by
  refine ⟨singletonFamily K, isBramble_singletonFamily hK, ?_⟩
  intro X hX
  exact htw.trans ((singletonFamily_hasOrderAtLeast hK).2 X hX)

/-- With the usual nonempty-graph offset, a clique of size at least
`treewidth G + 1` gives a bramble of that order. -/
theorem exists_bramble_order_treewidth_add_one_of_clique
    {G : _root_.SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) (htw : treewidth G + 1 ≤ K.card) :
    HasBrambleOrderAtLeast G (treewidth G + 1) := by
  refine ⟨singletonFamily K, ?_⟩
  exact (singletonFamily_hasOrderAtLeast hK).antitone htw

/-- Every complete finite graph has a finite bramble for which every hitting
set has cardinality at least its treewidth.  This statement also handles the
empty graph, where both sides are zero under the repository convention. -/
theorem exists_bramble_hitting_card_ge_treewidth_completeGraph :
    ∃ B : Finset (Finset V),
      IsBramble (_root_.SimpleGraph.completeGraph V) B ∧
        ∀ X : Finset V,
          Hits X B → treewidth (_root_.SimpleGraph.completeGraph V) ≤ X.card := by
  apply exists_bramble_hitting_card_ge_treewidth_of_clique
      (K := (Finset.univ : Finset V))
  · intro a _ha b _hb hab
    simpa using hab
  · exact
      (treewidth_le_card_sub_one (_root_.SimpleGraph.completeGraph V)).trans
        (Nat.sub_le _ _)

/-- If the finite vertex type is nonempty, the singleton bramble of all
vertices in the complete graph has the standard order `treewidth + 1`. -/
theorem exists_bramble_order_treewidth_add_one_completeGraph [Nonempty V] :
    HasBrambleOrderAtLeast (_root_.SimpleGraph.completeGraph V)
      (treewidth (_root_.SimpleGraph.completeGraph V) + 1) := by
  apply exists_bramble_order_treewidth_add_one_of_clique
      (K := (Finset.univ : Finset V))
  · intro a _ha b _hb hab
    simpa using hab
  · have hcard : 0 < Fintype.card V := Fintype.card_pos
    have htw :=
      treewidth_le_card_sub_one (_root_.SimpleGraph.completeGraph V)
    have hgoal :
        treewidth (_root_.SimpleGraph.completeGraph V) + 1 ≤ Fintype.card V := by
      omega
    simpa using hgoal

/-- The exact finite lower-duality target, with the convention-compatible
bound that remains meaningful for the empty graph. -/
def LowerDuality (G : _root_.SimpleGraph V) : Prop :=
  HasBrambleOrderAtLeast G (treewidth G)

theorem lowerDuality_of_clique {G : _root_.SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) (htw : treewidth G ≤ K.card) :
    LowerDuality G := by
  exact ⟨singletonFamily K, (singletonFamily_hasOrderAtLeast hK).antitone htw⟩

theorem lowerDuality_completeGraph :
    LowerDuality (_root_.SimpleGraph.completeGraph V) := by
  apply lowerDuality_of_clique (K := (Finset.univ : Finset V))
  · intro a _ha b _hb hab
    simpa using hab
  · exact
      (treewidth_le_card_sub_one (_root_.SimpleGraph.completeGraph V)).trans
        (Nat.sub_le _ _)

end TreewidthBramble

end SimpleGraph

end Lax17Proofs
