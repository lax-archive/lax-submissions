import Lax3Proofs.DriverArena
import Lax3Proofs.ArenaTransport
import Lax3Proofs.Compaction
import Lax3Proofs.SemLocal
import Lax3Proofs.ReachedS
import Lax3Proofs.UqwInstantiation

/-!
# Correctness of the abstract driver (E9, deliverable 3)

Two independent statements, matching the two things §5 owes:

## 1. The tables are correct — §5's chain, per node, composed

`tables_correct`: for every schedule formula `γ ∈ ℱ_j` and every vertex
`v` of a depth-`j` arena, the table entry `tables S ord j A v γ.fml`
holds iff `A ⊨ γ(v)` — satisfaction at the node's own arena and colors.
`mc_correct` then closes the root: `MC S ord G col ↔ G ⊨ φ`.

The per-node step is `sat_child_iff`, which is §5's "why line 28 is
correct" chain with the compaction moved to the front (every step is an
equivalence, so the composition order is free; fusing line 16's
`restrict` with step 3′'s compaction lets every remaining rewrite run on
the child carrier, where each is one landed lemma):

```
 A ⊨ β(v)
   ⟺ SatWithin X_u A β(v)      SemLocal.sat_iff_satWithin_of_ball_subset'
                                + ball_R(v) ⊆ X_u  [ball_subset_cluster_ctr]
   ⟺ B₀ᶜ ⊨ β(v′)              Compaction.sat_compact_iff_satWithin
                                (restrict + renumber, fused; any bijection)
   ⟺ B₀ᶜ ⊨ rel(β)(v′)         Relativize.sat_rel at X = univ — after
                                compaction the cluster is everything, so
                                the marker color is `univ`
   ⟺ B ⊨ iso(rel β)(v′)       Isolate.sat_iso — profiles measured in
                                B₀ᶜ, isolation after (hazard 1); the
                                child's colors satisfy hpd/hpu
                                definitionally (slotColoring)
   ⟺ eval(dec β, sub[v′], sc)  LocalityFun.localityBC_eval at B, then
                                BCAlgebra.eval_congr + the induction
                                hypothesis at ℱ_{j+1} (tables_correct)
```

Note what this does **not** need: the splitter-game record. The chain is
sound at every node the driver builds, whatever the history; the record
buys termination-in-budget, which is the second statement.

## 2. The recursion fits the budget — the `ReachedS` invariant

`Inv` is §5 line 8's precondition, abstractly: the arena's channel
`hist` is the trace of a genuine play `rounds` of the cluster-restricted
splitter game **at the root carrier** (E6: the record is never
re-typed), with one recorded round per level as long as the arena has
edges. `inv_root` starts it, `inv_child` carries it through one descent
(`ReachedS.reachedS_descend` + the restrict∘isolate identity
`map_childArena_eq`), and `eq_bot_of_inv_depth` is the payoff — §5 line
10's leaf test is exhaustive: **at depth `ℓ` the arena is edgeless**
(`ReachedS.reachedS_length_lt` at the UQW budget), so the structural
fuel of `tablesAux` never runs out on an arena with edges, and the leaf
really is `BotTables`' regime.

The width hypothesis `1 + j·(2R+1) ≤ width` of `inv_child` is §3's
`m = ℓ·(2R+1)` at depth `j ≤ ℓ−1` (hazard 2: the batch always fits the
pad, by `genSet_ncard_le`); the descent supplies `reachedS_descend`'s
`hwalk` from `pathSet_subset_genSet` — the recorded supports ARE the
batch, which is D6's channel consumed abstractly.

An isolated centre is the one descent that records no round: its cluster
is a single vertex, the child is edgeless (`childArena_G_eq_bot_of_
isolated`), and `Inv`'s record clause is vacuous there — which is
exactly why the clause is guarded by `A.G ≠ ⊥`.
-/

namespace Lax3Proofs.Driver

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.UniformQuasiWideness Lax12.ColoringNumbers
open Lax3Proofs.LocalityFun Lax3Proofs.WalkDistance

variable {L n₀ : ℕ}

/-! ### Small bridges -/

/-- Isolating nothing is the identity. -/
theorem deleteVerts_empty {V : Type*} (G : SimpleGraph V) :
    deleteVerts G (∅ : Set V) = G := by
  ext a b
  rw [Lax3Proofs.SplitterBasics.deleteVerts_adj]
  simp

/-! ### The per-node chain (§5, "why line 28 is correct") -/

/-- **The per-node semantic step.** For a local `(1, q−1)`-ranked `β`
and a vertex `v` of the cluster of `u` whose `R`-ball the cluster
contains, satisfaction of `β` at `v` in the node equals satisfaction of
the rewritten `stepFml β` at `v`'s child name in the child arena of `u`.
The chain is the module docstring's; each step is one landed lemma. -/
theorem sat_child_iff (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (hq : 1 ≤ S.q)
    {β : DistFO Λ 1} (hloc : IsLocal β) (hrank : DRank 1 (S.q - 1) β)
    {v : Fin A.N} (hv : v ∈ cluster S A π u)
    (hball : ball A.G S.R v ⊆ cluster S A π u) :
    Sat A.G A.col (fun _ => v) β ↔
      Sat (childArena S A π u).G (childArena S A π u).col
        (fun _ => (childEquiv S A π u).symm ⟨v, hv⟩) (stepFml S β) := by
  set e := childEquiv S A π u with he
  set vc := e.symm ⟨v, hv⟩ with hvc
  -- (i) semantic locality into the cluster
  have h1 : Sat A.G A.col (fun _ => v) β ↔
      SatWithin (cluster S A π u) A.G A.col (fun _ => v) β :=
    SemLocal.sat_iff_satWithin_of_ball_subset' A.G A.col hloc hrank _
      (fun _ => (ball_mono_radius A.G v S.rhoMinus_one_le_R).trans hball)
  -- (ii) compaction: restrict + renumber, fused
  have henv : (fun i : Fin 1 => ((e ((fun _ : Fin 1 => vc) i) : Fin A.N))) =
      fun _ : Fin 1 => v := by
    funext i
    show ((e (e.symm ⟨v, hv⟩) : Fin A.N)) = v
    rw [Equiv.apply_symm_apply]
  have h2 : Sat (preG S A π u) (childCol0 S A π u) (fun _ => vc) β ↔
      SatWithin (cluster S A π u) A.G A.col (fun _ => v) β := by
    have h := Compaction.sat_compact_iff_satWithin (A := A.G) (B := preG S A π u)
      (colA := A.col) (colB := childCol0 S A π u) e
      (fun a b => Iff.rfl) (fun c a => Iff.rfl) β (fun _ => vc)
    rwa [henv] at h
  -- (iii) relativization, at the trivial marker `univ`
  have hold : ∀ c : Fin Λ,
      childColR S A π u (Fin.castSucc c) = childCol0 S A π u c ∩ Set.univ := by
    intro c
    rw [childColR, relColoring_castSucc, Set.inter_univ]
  have hmk : childColR S A π u (Fin.last Λ) = Set.univ := relColoring_last _ _
  have h3 : Sat (preG S A π u) (childColR S A π u) (fun _ => vc)
        (Relativize.rel Fin.castSucc (Fin.last Λ) β) ↔
      Sat (preG S A π u) (childCol0 S A π u) (fun _ => vc) β := by
    have h := Relativize.sat_rel (A := preG S A π u) hold hmk β (fun _ => vc)
    rw [Set.compl_univ, deleteVerts_empty] at h
    exact h.trans (SyntaxLemmas.sat_iff_satWithin_univ _ _ _ _).symm
  -- (iv) isolation: profiles measured in `preG`, before isolating
  have h4 : Sat (preG S A π u) (childColR S A π u) (fun _ => vc)
        (Relativize.rel Fin.castSucc (Fin.last Λ) β) ↔
      Sat (deleteVerts (preG S A π u) (Set.range (batchFn S A π u)))
        (childCol S A π u) (fun _ => vc)
        (Lax3Proofs.Isolate.iso isoOld isoPd isoPu
          (Relativize.rel Fin.castSucc (Fin.last Λ) β)) :=
    Lax3Proofs.Isolate.sat_iso
      (fun c => slotColoring_old ..)
      (fun j a => slotColoring_pd ..)
      (fun c b => slotColoring_pu ..)
      S.one_le_R _
      (S.radiiLe_R_of_drank hq (Relativize.drank_rel _ _ hrank))
      (fun _ => vc)
  exact h1.trans (h2.symm.trans (h3.symm.trans h4))

/-! ### The tables are correct -/

/-- **The tables are correct, at every fuel.** For every schedule
formula and every vertex, the table entry equals satisfaction at the
node's own arena. Induction on the fuel; the base returns `BotTables`
through its spec, the step is `sat_child_iff` + `localityBC_eval` +
`BCAlgebra.eval_congr` at the child, with the induction hypothesis
supplying every atom through the schedule's membership lemmas. -/
theorem tablesAux_correct (S : Setup L) (ord : CoverSpec.OrderingRoutine) :
    ∀ (fuel j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N) (γ : Fml S j),
      γ ∈ F S j →
      (tablesAux (n₀ := n₀) S ord fuel j A v γ.fml ↔
        Sat A.G A.col (fun _ => v) γ.fml) := by
  intro fuel
  induction fuel with
  | zero => intro j A v γ hγ; exact Iff.rfl
  | succ fuel ih =>
    intro j A v γ hγ
    rw [tablesAux]
    by_cases hbot : A.G = ⊥
    · rw [if_pos hbot]
    · rw [if_neg hbot]
      have hdec : IsLocal γ.fml ∧ DRank 1 (S.q - 1) γ.fml := ⟨γ.isLocal, γ.drank⟩
      simp only [dif_pos hdec]
      set π := (ord A.N A.G).order with hπ
      set u := centre S A π v with hu
      set B := childArena S A π u with hB
      set vc : Fin B.N :=
        (childEquiv S A π u).symm ⟨v, mem_cluster_centre S A π v⟩ with hvc
      have hq := one_le_q_of_mem_F S γ hγ
      -- the chain, at `u := centre v`
      have hchain := sat_child_iff S A π u hq γ.isLocal γ.drank
        (mem_cluster_centre S A π v)
        (Lax3Proofs.CoverCentres.ball_subset_cluster_ctr A.G π S.R v)
      -- the locality decomposition, evaluated at the child
      have heval := localityBC_eval S.choice (stepFml S γ.fml)
        (drank_stepFml S γ.drank) B.N B.G B.col (fun _ => vc)
      -- the two atom valuations agree, by the induction hypothesis
      have hatoms : ∀ a ∈ (dec S (⟨γ.fml, γ.isLocal, γ.drank⟩ : Fml S j)).atoms,
          ((Sum.elim (fun ψ => tablesAux (n₀ := n₀) S ord fuel (j + 1) B vc ψ)
            (fun σ => σ.t ≤ S.choice.size B.G σ.r
              {a | tablesAux (n₀ := n₀) S ord fuel (j + 1) B a σ.β})) a ↔
          (Sum.elim (Sat B.G B.col (fun _ => vc))
            (ScatterSentence.Sat S.choice B.G B.col)) a) := by
        rintro (ψ | σ) ha
        · -- a local atom is a schedule formula one level down
          obtain ⟨γ', hγ', hfml⟩ := exists_mem_F_succ_of_localAtom S hγ
            (mem_localAtoms.mpr ha)
          simp only [Sum.elim_inl]
          rw [← hfml]
          exact ih (j + 1) B vc γ' hγ'
        · -- a scatter atom's β is a schedule formula one level down
          obtain ⟨γ', hγ', hfml⟩ := exists_mem_F_succ_of_scatterAtom S hγ
            (mem_scatterAtoms.mpr ha)
          simp only [Sum.elim_inr]
          have hset : {a | tablesAux (n₀ := n₀) S ord fuel (j + 1) B a σ.β} =
              {a | Sat B.G B.col (fun _ => a) σ.β} := by
            ext a
            simp only [Set.mem_setOf_eq]
            rw [← hfml]
            exact ih (j + 1) B a γ' hγ'
          rw [hset]
          exact (Lax3Proofs.ScatterFml.scatterSentence_sat_iff S.choice B.G B.col σ.r σ.t σ.β).symm
      calc (dec S (⟨γ.fml, γ.isLocal, γ.drank⟩ : Fml S j)).eval _
          ↔ (dec S (⟨γ.fml, γ.isLocal, γ.drank⟩ : Fml S j)).eval
              (Sum.elim (Sat B.G B.col (fun _ => vc))
                (ScatterSentence.Sat S.choice B.G B.col)) :=
            Lax3Proofs.BCAlgebra.eval_congr _ hatoms
        _ ↔ Sat B.G B.col (fun _ => vc) (stepFml S γ.fml) := heval.symm
        _ ↔ Sat A.G A.col (fun _ => v) γ.fml := hchain.symm

/-- **§5's `Tables` is correct**: at every depth, on every arena, the
table entry at a schedule formula is satisfaction at the node. -/
theorem tables_correct (S : Setup L) (ord : CoverSpec.OrderingRoutine) (j : ℕ)
    (A : Arena (S.pal j) n₀) (v : Fin A.N) (γ : Fml S j) (hγ : γ ∈ F S j) :
    tables (n₀ := n₀) S ord j A v γ.fml ↔ Sat A.G A.col (fun _ => v) γ.fml :=
  tablesAux_correct S ord (S.depth - j) j A v γ hγ

/-- **§5's `MC` is correct**: the abstract driver decides `φ`. The local
sentence atoms of `top` are constants (L1, `sat_localConst`), the scatter
atoms are the root table's greedy counts (`tables_correct` at `ℱ_0`),
and the assembly is `localityBC_eval` at the root. -/
theorem mc_correct (S : Setup L) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L) :
    MC S ord G col ↔ Sat G col Fin.elim0 S.φ := by
  rw [MC]
  have heval := localityBC_eval S.choice S.φ S.hφ n G col Fin.elim0
  rw [show (Sat G col Fin.elim0 S.φ ↔ _) from heval]
  refine Lax3Proofs.BCAlgebra.eval_congr _ ?_
  rintro (ψ | σ) ha
  · simp only [Sum.elim_inl]
    exact (sat_localConst G col Fin.elim0
      (localityBC_atoms_local S.choice S.φ S.hφ ψ ha).1).symm
  · simp only [Sum.elim_inr]
    obtain ⟨γ, hγ, hfml⟩ := exists_mem_F_zero_of_scatterAtom S
      (mem_scatterAtoms.mpr ha)
    have hset : {v : Fin n | tables S ord 0 (rootArena G col) v σ.β} =
        {a : Fin n | Sat G col (fun _ => a) σ.β} := by
      ext a
      simp only [Set.mem_setOf_eq]
      rw [← hfml]
      exact tables_correct S ord 0 (rootArena G col) a γ hγ
    rw [hset]
    exact (Lax3Proofs.ScatterFml.scatterSentence_sat_iff S.choice G col σ.r σ.t σ.β).symm

/-! ### The `ReachedS` invariant: the recursion fits the budget -/

/-- **§5 line 8's precondition, abstractly** (E6: the record lives at
the ROOT carrier and is never re-typed). The channel has exactly one
entry per level; and — as long as the node still has an edge — the
channel is the trace of a genuine play of the cluster-restricted game
whose reached arena is this node's arena, mapped to the root. -/
def Inv (S : Setup L) {Λ : ℕ} (G₀ : SimpleGraph (Fin n₀)) (j : ℕ)
    (A : Arena Λ n₀) : Prop :=
  A.hist.length = j ∧
  (A.G = ⊥ ∨
    ∃ rounds : List (ReachedS.RoundS n₀),
      (∀ e ∈ rounds, (e.vtx, e.arena) ∈ A.hist) ∧
      rounds.length = j ∧
      ReachedS.ReachedS (2 * S.R) G₀ rounds (SimpleGraph.map (⇑A.up) A.G))

/-- The root arena satisfies the invariant with the empty record. -/
theorem inv_root (S : Setup L) {n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) : Inv S G 0 (rootArena G col) := by
  refine ⟨rfl, Or.inr ⟨[], by simp, rfl, ?_⟩⟩
  have h : SimpleGraph.map (⇑(rootArena G col).up) (rootArena G col).G = G := by
    have hid : ⇑(Function.Embedding.refl (Fin n)) = id := rfl
    show SimpleGraph.map (⇑(Function.Embedding.refl (Fin n))) G = G
    rw [hid, SimpleGraph.map_id]
  rw [h]
  exact ReachedS.ReachedS.nil

/-- **§5 line 10's leaf test is exhaustive** — the payoff of the
invariant: at depth `ℓ = N(2s+2)` (the UQW round budget at game radius
`2R`) an arena satisfying the invariant is edgeless. A record of length
`ℓ` would contradict `ReachedS.reachedS_length_lt`. -/
theorem eq_bot_of_inv_depth (S : Setup L) {Λ : ℕ} {G₀ : SimpleGraph (Fin n₀)}
    {A : Arena Λ n₀} {N : ℕ → ℕ} {s : ℕ}
    (hQ : Lax3Proofs.UqwInstantiation.SplitterMargin G₀ N s S.R)
    (hd : S.depth = N (2 * s + 2))
    (h : Inv S G₀ S.depth A) : A.G = ⊥ := by
  obtain ⟨-, hbot | ⟨rounds, -, hlen, hR⟩⟩ := h
  · exact hbot
  · have hlt := ReachedS.reachedS_length_lt hQ hR
    omega

/-! #### One descent preserves the invariant -/

/-- An isolated centre has a one-vertex cluster. -/
theorem cluster_eq_singleton_of_isolated (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {u : Fin A.N} (hu : ∀ z, ¬ A.G.Adj u z) :
    cluster S A π u = {u} := by
  refine Set.eq_of_subset_of_subset (fun w hw => ?_)
    (fun w hw => hw ▸ self_mem_cluster S A π u)
  obtain ⟨p, hlen, -⟩ := Lax3Proofs.ClusterPaths.exists_walk_support_subset_fiber hw
  rcases Nat.eq_zero_or_pos p.length with h0 | h0
  · simp only [Set.mem_singleton_iff]
    cases p with
    | nil => rfl
    | cons h q => simp at h0
  · obtain ⟨z, hz⟩ := Lax3Proofs.SplitterWin.exists_adj_of_length_ne_zero
      p.reverse (by rw [SimpleGraph.Walk.length_reverse]; omega)
    exact absurd hz (hu z)

/-- The child of an isolated centre is edgeless: its carrier is a single
vertex. -/
theorem childArena_G_eq_bot_of_isolated (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {u : Fin A.N} (hu : ∀ z, ¬ A.G.Adj u z) :
    (childArena S A π u).G = ⊥ := by
  have hone : (childArena S A π u).N = 1 := by
    rw [childArena_N, childN, cluster_eq_singleton_of_isolated S A π hu]
    exact Set.ncard_singleton u
  ext a b
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hadj
  have hab : a = b := by
    apply Fin.ext
    have ha := a.2
    have hb := b.2
    omega
  rw [hab] at hadj
  exact SimpleGraph.irrefl _ hadj

/-- The batch always fits the pad (hazard 2): the batch on the child
carrier injects into `genSet`, whose size `genSet_ncard_le` bounds by
`1 + j·(2R+1)`. -/
theorem batchSet_ncard_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    (batchSet S A π u).ncard ≤ 1 + A.hist.length * (2 * S.R + 1) := by
  have hinj : Set.InjOn (fun a => A.up ((childEquiv S A π u) a : Fin A.N))
      (batchSet S A π u) := by
    intro a _ b _ hab
    have h1 := A.up.injective hab
    have h2 := Subtype.ext h1
    exact (childEquiv S A π u).injective h2
  have hmap : ∀ a ∈ batchSet S A π u,
      A.up ((childEquiv S A π u) a : Fin A.N) ∈ batchRoot S A u := fun a ha => ha
  calc (batchSet S A π u).ncard ≤ (batchRoot S A u).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmap hinj (Set.toFinite _)
    _ ≤ 1 + A.hist.length * (2 * S.R + 1) :=
        Lax3Proofs.SplitterWin.genSet_ncard_le (2 * S.R) A.hist (A.up u)

/-- **The restrict∘isolate identity** (§5 line 8's re-expression): the
arena `reachedS_descend` reaches — restrict the mapped node arena to the
mapped cluster, then isolate the mapped batch — IS the child arena,
mapped to the root. -/
theorem map_childArena_eq (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    deleteVerts
        (deleteVerts (SimpleGraph.map (⇑A.up) A.G)
          ((⇑A.up '' cluster S A π u)ᶜ))
        ((fun a => A.up ((childEquiv S A π u) a : Fin A.N)) ''
          Set.range (batchFn S A π u)) =
      SimpleGraph.map (⇑(childArena S A π u).up) (childArena S A π u).G := by
  have hcoe : ∀ a : Fin (childArena S A π u).N,
      (childArena S A π u).up a = A.up ((childEquiv S A π u) a : Fin A.N) :=
    fun _ => rfl
  ext x y
  rw [Lax3Proofs.SplitterBasics.deleteVerts_adj,
    Lax3Proofs.SplitterBasics.deleteVerts_adj]
  constructor
  · rintro ⟨⟨hadj, hx, hy⟩, hxW, hyW⟩
    rw [Set.notMem_compl_iff] at hx hy
    obtain ⟨x', hx', hxe⟩ := hx
    obtain ⟨y', hy', hye⟩ := hy
    obtain ⟨a', b', hab, hax, hby⟩ := (SimpleGraph.map_adj _ _ _ _).mp hadj
    have hax' : a' = x' := A.up.injective (hax.trans hxe.symm)
    have hby' : b' = y' := A.up.injective (hby.trans hye.symm)
    subst hax'
    subst hby'
    have hea : ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨a', hx'⟩) : Fin A.N)
        = a' := by rw [Equiv.apply_symm_apply]
    have heb : ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨b', hy'⟩) : Fin A.N)
        = b' := by rw [Equiv.apply_symm_apply]
    refine (SimpleGraph.map_adj _ _ _ _).mpr
      ⟨(childEquiv S A π u).symm ⟨a', hx'⟩, (childEquiv S A π u).symm ⟨b', hy'⟩,
        ?_, ?_, ?_⟩
    · rw [childArena_G, Lax3Proofs.SplitterBasics.deleteVerts_adj]
      refine ⟨?_, ?_, ?_⟩
      · show A.G.Adj
          ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨a', hx'⟩) : Fin A.N)
          ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨b', hy'⟩) : Fin A.N)
        rw [hea, heb]
        exact hab
      · intro haw
        refine hxW ⟨(childEquiv S A π u).symm ⟨a', hx'⟩, haw, ?_⟩
        show A.up
          ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨a', hx'⟩) : Fin A.N) = x
        rw [hea]
        exact hxe
      · intro hbw
        refine hyW ⟨(childEquiv S A π u).symm ⟨b', hy'⟩, hbw, ?_⟩
        show A.up
          ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨b', hy'⟩) : Fin A.N) = y
        rw [heb]
        exact hye
    · rw [hcoe, hea]
      exact hxe
    · rw [hcoe, heb]
      exact hye
  · intro h
    obtain ⟨a, b, hab, hax, hby⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
    rw [hcoe] at hax hby
    rw [childArena_G, Lax3Proofs.SplitterBasics.deleteVerts_adj] at hab
    obtain ⟨hab, haw, hbw⟩ := hab
    have hadj : A.G.Adj ((childEquiv S A π u) a : Fin A.N)
        ((childEquiv S A π u) b : Fin A.N) := hab
    refine ⟨⟨(SimpleGraph.map_adj _ _ _ _).mpr ⟨_, _, hadj, hax, hby⟩, ?_, ?_⟩, ?_, ?_⟩
    · rw [Set.notMem_compl_iff]
      exact ⟨_, ((childEquiv S A π u) a).2, hax⟩
    · rw [Set.notMem_compl_iff]
      exact ⟨_, ((childEquiv S A π u) b).2, hby⟩
    · rintro ⟨a₂, ha₂, hax₂⟩
      have h1 : A.up ((childEquiv S A π u) a₂ : Fin A.N) =
          A.up ((childEquiv S A π u) a : Fin A.N) := hax₂.trans hax.symm
      have h2 := (childEquiv S A π u).injective (Subtype.ext (A.up.injective h1))
      exact haw (h2 ▸ ha₂)
    · rintro ⟨b₂, hb₂, hby₂⟩
      have h1 : A.up ((childEquiv S A π u) b₂ : Fin A.N) =
          A.up ((childEquiv S A π u) b : Fin A.N) := hby₂.trans hby.symm
      have h2 := (childEquiv S A π u).injective (Subtype.ext (A.up.injective h1))
      exact hbw (h2 ▸ hb₂)

/-- **One descent preserves the invariant.** At a node with an edge, the
child of any centre satisfies the invariant one level down. The width
hypothesis is §3's `m = ℓ(2R+1)` at this depth: it makes the pad exact
(`range_pad`), so the isolated set is exactly the batch. An isolated
centre yields an edgeless child (record clause vacuous); a centre with
an edge extends the record by `reachedS_descend`, with `hwalk` supplied
by `pathSet_subset_genSet` and the reached arena re-expressed by
`map_childArena_eq`. -/
theorem inv_child (S : Setup L) {Λ : ℕ} {G₀ : SimpleGraph (Fin n₀)} {j : ℕ}
    {A : Arena Λ n₀} (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    (hInv : Inv S G₀ j A) (hbot : A.G ≠ ⊥)
    (hwidth : 1 + j * (2 * S.R + 1) ≤ S.width) :
    Inv S G₀ (j + 1) (childArena S A π u) := by
  obtain ⟨hlen, hrec⟩ := hInv
  have hlen' : (childArena S A π u).hist.length = j + 1 := by
    rw [childArena_hist, List.length_cons, hlen]
  refine ⟨hlen', ?_⟩
  obtain ⟨rounds, hmem, hrlen, hR⟩ := hrec.resolve_left hbot
  by_cases hu : ∃ z, A.G.Adj u z
  · -- the centre has an edge: extend the record by one descent
    refine Or.inr ?_
    -- the batch fits, so the pad is exact
    have hfits : (batchSet S A π u).ncard ≤ S.width :=
      (batchSet_ncard_le S A π u).trans (by rw [hlen]; exact hwidth)
    have hpad : Set.range (batchFn S A π u) = batchSet S A π u :=
      range_pad (centreChild_mem_batchSet S A π u) hfits
    -- names
    set e := childEquiv S A π u with hedef
    set Ximg : Set (Fin n₀) := ⇑A.up '' cluster S A π u with hXdef
    set W : Set (Fin n₀) :=
      (fun a => A.up ((e a : Fin A.N))) '' Set.range (batchFn S A π u) with hWdef
    -- the descent's five hypotheses
    have hv : ∃ z, (SimpleGraph.map (⇑A.up) A.G).Adj (A.up u) z := by
      obtain ⟨z, hz⟩ := hu
      exact ⟨A.up z, (SimpleGraph.map_adj _ _ _ _).mpr ⟨u, z, hz, rfl, rfl⟩⟩
    have hXball : Ximg ⊆ ball (SimpleGraph.map (⇑A.up) A.G) (2 * S.R) (A.up u) := by
      rintro x ⟨x', hx', rfl⟩
      obtain ⟨p, hlen_p, -⟩ :=
        Lax3Proofs.ClusterPaths.exists_walk_support_subset_fiber hx'
      rw [mem_ball]
      exact Lax3Proofs.ArenaTransport.withinDist_map A.up
        (withinDist_symm ⟨p, hlen_p⟩)
    have hWX : W ⊆ Ximg := by
      rintro x ⟨a, ha, rfl⟩
      exact ⟨(e a : Fin A.N), (e a).2, rfl⟩
    have hself : A.up u ∈ W := by
      refine ⟨centreChild S A π u, ?_, ?_⟩
      · rw [hpad]
        exact centreChild_mem_batchSet S A π u
      · show A.up ((e (centreChild S A π u) : Fin A.N)) = A.up u
        rw [centreChild, ← hedef, Equiv.apply_symm_apply]
    have hwalk : ∀ er ∈ rounds,
        WithinDist er.arena (2 * S.R) er.vtx (A.up u) →
        ∃ p : er.arena.Walk er.vtx (A.up u), p.length ≤ 2 * S.R ∧
          {z | z ∈ p.support} ∩ Ximg ⊆ W := by
      intro er her hwd
      obtain ⟨p, hplen, hpset⟩ := Lax3Proofs.SplitterWin.pathSet_spec hwd
      refine ⟨p, hplen, ?_⟩
      rw [← hpset]
      rintro z ⟨hzp, x', hx', rfl⟩
      -- `z` is a recorded support vertex inside the cluster: it is in the batch
      have hzgen : A.up x' ∈ batchRoot S A u :=
        Lax3Proofs.SplitterWin.pathSet_subset_genSet
          (e := (er.vtx, er.arena)) (hmem er her) _ hzp
      refine ⟨e.symm ⟨x', hx'⟩, ?_, ?_⟩
      · rw [hpad]
        show A.up ((e (e.symm ⟨x', hx'⟩) : Fin A.N)) ∈ batchRoot S A u
        rw [Equiv.apply_symm_apply]
        exact hzgen
      · show A.up ((e (e.symm ⟨x', hx'⟩) : Fin A.N)) = A.up x'
        rw [Equiv.apply_symm_apply]
    obtain ⟨Sgen, hstep⟩ := ReachedS.reachedS_descend hR hv hXball hWX hself hwalk
    refine ⟨⟨A.up u, SimpleGraph.map (⇑A.up) A.G, Ximg, Sgen⟩ :: rounds, ?_, ?_, ?_⟩
    · intro er her
      rw [childArena_hist]
      rcases List.mem_cons.mp her with rfl | her'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hmem er her')
    · rw [List.length_cons, hrlen]
    · rw [← map_childArena_eq S A π u]
      exact hstep
  · -- isolated centre: the child is edgeless
    exact Or.inl (childArena_G_eq_bot_of_isolated S A π
      (fun z hz => hu ⟨z, hz⟩))

end Lax3Proofs.Driver
