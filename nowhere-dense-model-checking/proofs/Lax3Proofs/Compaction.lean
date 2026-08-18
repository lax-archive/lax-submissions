import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.WalkDistance
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
The **compaction lemma**: satisfaction of distance logic transports
between the recursion's *renumbered* child arena and the *kept* arena,
along any bijection of the child's carrier with the cluster.

The recursion of the evaluator computes tables for the child structure
on its own carrier `Fin N`, where `N` is the size of the cluster
`X : Set (Fin n)`; the semantic chain it must feed lives on the kept
carrier `Fin n`, where everything outside the cluster has been
*isolated, not removed*. The two sides never agree as plain
satisfaction: on the kept carrier an unrestricted quantifier still
ranges over the isolated dead vertices, so a formula counting them
separates the arenas. The true statement is one definition down —
satisfaction on the compact side matches satisfaction *relativized to
the cluster* on the kept side, `SatWithin X`, whose quantifiers range
over `X`, whose atoms carry membership in `X`, and whose distances are
measured along walks staying in `X`.

`sat_compact_iff_satWithin` is that transport, against the kept arena
itself; `satWithin_deleteVerts_compl` is the bridge to the arena the
design actually holds, with the cluster's complement isolated —
relativization to `X` cannot see the isolation, since a walk staying in
`X` never uses a deleted edge; and
`sat_compact_iff_satWithin_deleteVerts_compl` is their composite, the
form the semantic chain consumes.

# Any bijection serves

The transport asks nothing of the bijection beyond matching the
adjacencies and the color classes through it — no monotonicity, no
order-preservation. `DistFO` has no order-sensitive constructor:
every case of the induction moves a vertex, a walk, or a witness
through the bijection pointwise, and the two binder cases move a
`Fin.snoc` environment through it by `Fin.comp_snoc`, exactly as the
edgeless transport `Lax3Proofs.BotEval.sat_congr_bot_of_bij` does.

# The walk transport

The distance atoms exchange walks of the compact arena for walks of the
kept arena supported inside the cluster. `exists_walk_push` maps a
compact walk edge by edge through the bijection — every vertex of the
image is a member of the cluster by construction; `exists_walk_pull`
pulls a kept walk supported in the cluster back vertex by vertex, its
support hypothesis supplying the membership each pullback needs. Both
preserve the length exactly, so the `≤ d` of a binary atom and the
`< r` of a unary one read off the same pair. The `deleteVerts` bridge
needs no bijection at all: its walks move by `Walk.transfer`, which
keeps both length and support, the edge conditions being
`deleteVerts_le` in one direction and, in the other, the support
hypothesis applied to the two endpoints of each edge.
-/

namespace Lax3Proofs.Compaction

open Lax3.ColoredGraphs Lax3.DistFO
open Lax12.UniformQuasiWideness
open Lax3Proofs.SyntaxLemmas Lax3Proofs.WalkDistance

variable {L n N : ℕ} {X : Set (Fin n)} {A : SimpleGraph (Fin n)} {B : SimpleGraph (Fin N)}
  {colA : Coloring n L} {colB : Coloring N L}

/-! ### Walks through the bijection

A walk of the compact arena and a walk of the kept arena supported in
the cluster are the same data, read through the bijection edge by edge.
Both directions keep the length on the nose.
-/

section Walks

variable (e : Fin N ≃ ↥X)
  (hAdj : ∀ a b : Fin N, B.Adj a b ↔ A.Adj (e a : Fin n) (e b))

/-- A walk of the compact arena maps to a walk of the kept arena of the
same length, supported inside the cluster: every edge crosses by the
adjacency hypothesis, and every vertex of the image lies in `X` because
it is a value of the bijection. -/
private theorem exists_walk_push {a b : Fin N} (p : B.Walk a b) :
    ∃ q : A.Walk (e a : Fin n) (e b : Fin n),
      q.length = p.length ∧ ∀ z ∈ q.support, z ∈ X := by
  induction p with
  | nil =>
    refine ⟨.nil, rfl, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ (e _).2
  | @cons a c b hac p ih =>
    obtain ⟨q, hq, hqs⟩ := ih
    refine ⟨.cons ((hAdj a c).mp hac) q, by simp [hq], ?_⟩
    intro z hz
    rcases List.mem_cons.mp (by simpa using hz) with rfl | hz
    · exact (e a).2
    · exact hqs z hz

/-- Conversely, a walk of the kept arena supported inside the cluster
pulls back to a walk of the compact arena of the same length. The
endpoints are carried as equations so that the induction can move its
first endpoint; the support hypothesis supplies the cluster membership
each pullback vertex needs. -/
private theorem exists_walk_pull {x y : Fin n} (q : A.Walk x y) {a b : Fin N}
    (hax : (e a : Fin n) = x) (hby : (e b : Fin n) = y)
    (hq : ∀ z ∈ q.support, z ∈ X) :
    ∃ p : B.Walk a b, p.length = q.length := by
  induction q generalizing a with
  | nil =>
    obtain rfl : a = b := e.injective (Subtype.ext (hax.trans hby.symm))
    exact ⟨.nil, rfl⟩
  | @cons x c y hxc q ih =>
    have hc : c ∈ X := hq c (by simp)
    obtain ⟨p, hp⟩ := ih (a := e.symm ⟨c, hc⟩) (by simp)
      (fun z hz => hq z (by simp [hz]))
    refine ⟨.cons ((hAdj a (e.symm ⟨c, hc⟩)).mpr ?_) p, by simp [hp]⟩
    rw [hax]
    simpa using hxc

/-- A distance bound of the compact arena is a distance bound inside the
cluster of the kept arena, through the bijection. -/
private theorem withinDist_compact_iff (d : ℕ) (a b : Fin N) :
    WithinDist B d a b ↔ WithinDistIn X A d (e a : Fin n) (e b : Fin n) := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq, hqs⟩ := exists_walk_push e hAdj p
    exact ⟨q, by rw [hq]; exact hp, hqs⟩
  · rintro ⟨q, hq, hqs⟩
    obtain ⟨p, hp⟩ := exists_walk_pull e hAdj q rfl rfl hqs
    exact ⟨p, by rw [hp]; exact hq⟩

end Walks

/-- Moving a `Fin.snoc` environment through the bijection: the compact
environment extended by a witness reads, on the kept side, as the kept
environment extended by the image of the witness. -/
private theorem snoc_env (e : Fin N ≃ ↥X) {k : ℕ} (m : Fin k → Fin N) (v : Fin N) :
    (fun i => (e (Fin.snoc m v i) : Fin n)) =
      Fin.snoc (fun i => (e (m i) : Fin n)) (e v : Fin n) :=
  Fin.comp_snoc (fun a => (e a : Fin n)) m v

/-- **The compaction transport.** For a cluster `X`, *any* bijection
`e : Fin N ≃ X` of the compact carrier with the cluster, a compact arena
whose adjacency is the kept arena's read through `e`, and colorings
matched through `e`, satisfaction on the compact side is satisfaction
relativized to the cluster on the kept side, at the environment read
through `e`. No order or monotonicity of `e` enters: no constructor of
`DistFO` is order-sensitive. -/
theorem sat_compact_iff_satWithin (e : Fin N ≃ ↥X)
    (hAdj : ∀ a b : Fin N, B.Adj a b ↔ A.Adj (e a : Fin n) (e b))
    (hcol : ∀ (c : Fin L) (v : Fin N), v ∈ colB c ↔ (e v : Fin n) ∈ colA c)
    {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin N) :
    Sat B colB m φ ↔ SatWithin X A colA (fun i => (e (m i) : Fin n)) φ := by
  induction φ with
  | adj i j =>
    rw [sat_adj, satWithin_adj]
    exact ⟨fun h => ⟨(hAdj _ _).mp h, (e (m i)).2, (e (m j)).2⟩,
      fun h => (hAdj _ _).mpr h.1⟩
  | eq i j =>
    rw [sat_eq, satWithin_eq]
    exact ⟨fun h => by rw [h], fun h => e.injective (Subtype.ext h)⟩
  | color c i =>
    rw [sat_color, satWithin_color]
    exact ⟨fun h => ⟨(hcol c (m i)).mp h, (e (m i)).2⟩, fun h => (hcol c (m i)).mpr h.1⟩
  | distLe r i j =>
    rw [sat_distLe, satWithin_distLe]
    exact withinDist_compact_iff e hAdj r (m i) (m j)
  | distColorLt r c i =>
    rw [sat_distColorLt, satWithin_distColorLt]
    constructor
    · rintro ⟨y, hy, w, hw⟩
      obtain ⟨q, hq, hqs⟩ := exists_walk_push e hAdj w
      exact ⟨(e y : Fin n), (hcol c y).mp hy, (e y).2, q, by rw [hq]; exact hw, hqs⟩
    · rintro ⟨y, hy, hyX, w, hw, hws⟩
      obtain ⟨p, hp⟩ := exists_walk_pull e hAdj w (b := e.symm ⟨y, hyX⟩) rfl (by simp) hws
      exact ⟨e.symm ⟨y, hyX⟩, (hcol c _).mpr (by simpa using hy), p, by rw [hp]; exact hw⟩
  | not φ ih => rw [sat_not, satWithin_not, ih m]
  | and φ ψ ihφ ihψ => rw [sat_and, satWithin_and, ihφ m, ihψ m]
  | exU φ ih =>
    rw [sat_exU, satWithin_exU]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨(e v : Fin n), (e v).2, ?_⟩
      have h := (ih (Fin.snoc m v)).mp hv
      rwa [snoc_env e] at h
    · rintro ⟨w, hwX, hsat⟩
      refine ⟨e.symm ⟨w, hwX⟩, (ih _).mpr ?_⟩
      rw [snoc_env e]
      simpa using hsat
  | exL r g φ ih =>
    rw [sat_exL, satWithin_exL]
    constructor
    · rintro ⟨v, ⟨i, hi, hd⟩, hsat⟩
      refine ⟨(e v : Fin n), (e v).2,
        ⟨i, hi, (withinDist_compact_iff e hAdj r (m i) v).mp hd⟩, ?_⟩
      have h := (ih (Fin.snoc m v)).mp hsat
      rwa [snoc_env e] at h
    · rintro ⟨w, hwX, ⟨i, hi, hd⟩, hsat⟩
      refine ⟨e.symm ⟨w, hwX⟩, ⟨i, hi, ?_⟩, (ih _).mpr ?_⟩
      · rw [withinDist_compact_iff e hAdj]
        simpa using hd
      · rw [snoc_env e]
        simpa using hsat

/-! ### The `deleteVerts` corner

The kept-side arena the design holds is `deleteVerts A Xᶜ` — the
cluster's complement isolated, the carrier kept. Relativization to `X`
cannot tell the two apart: inside the cluster no adjacency changes, and
a walk staying in `X` never uses a deleted edge.
-/

section DeleteVertsBridge

variable {u v : Fin n}

/-- A walk of the kept arena supported inside the cluster survives the
isolation of the cluster's complement, with its length and support
unchanged: both endpoints of each of its edges lie in `X`. -/
private theorem walk_to_deleteVerts_compl (p : A.Walk u v)
    (hp : ∀ z ∈ p.support, z ∈ X) :
    ∃ q : (deleteVerts A Xᶜ).Walk u v, q.length = p.length ∧ q.support = p.support := by
  have hedges : ∀ ed ∈ p.edges, ed ∈ (deleteVerts A Xᶜ).edgeSet := by
    intro ed
    refine Sym2.ind (fun x y hed => ?_) ed
    exact SimpleGraph.mem_edgeSet.mpr ⟨p.adj_of_mem_edges hed,
      Set.notMem_compl_iff.mpr (hp x (p.fst_mem_support_of_mem_edges hed)),
      Set.notMem_compl_iff.mpr (hp y (p.snd_mem_support_of_mem_edges hed))⟩
  exact ⟨p.transfer _ hedges, p.length_transfer hedges, p.support_transfer hedges⟩

/-- Conversely, a walk of the isolated arena is a walk of the kept arena
with its length and support unchanged: isolation only removes edges. -/
private theorem walk_of_deleteVerts_compl (p : (deleteVerts A Xᶜ).Walk u v) :
    ∃ q : A.Walk u v, q.length = p.length ∧ q.support = p.support := by
  have hedges : ∀ ed ∈ p.edges, ed ∈ A.edgeSet := fun ed hed =>
    SimpleGraph.edgeSet_mono (deleteVerts_le A Xᶜ) (p.edges_subset_edgeSet hed)
  exact ⟨p.transfer _ hedges, p.length_transfer hedges, p.support_transfer hedges⟩

/-- Distances inside the cluster are blind to the isolation of its
complement. -/
private theorem withinDistIn_deleteVerts_compl_iff (d : ℕ) (u v : Fin n) :
    WithinDistIn X (deleteVerts A Xᶜ) d u v ↔ WithinDistIn X A d u v := by
  constructor
  · rintro ⟨p, hp, hps⟩
    obtain ⟨q, hq, hqs⟩ := walk_of_deleteVerts_compl p
    exact ⟨q, by rw [hq]; exact hp, by rw [hqs]; exact hps⟩
  · rintro ⟨p, hp, hps⟩
    obtain ⟨q, hq, hqs⟩ := walk_to_deleteVerts_compl p hps
    exact ⟨q, by rw [hq]; exact hp, by rw [hqs]; exact hps⟩

end DeleteVertsBridge

/-- **Relativization to the cluster is blind to the isolation of its
complement.** Inside `X`, isolating `Xᶜ` changes no adjacency and no
walk, so satisfaction relativized to `X` agrees between the kept arena
and the design's isolated arena `deleteVerts A Xᶜ`. -/
theorem satWithin_deleteVerts_compl (A : SimpleGraph (Fin n)) (colA : Coloring n L)
    {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin n) :
    SatWithin X (deleteVerts A Xᶜ) colA m φ ↔ SatWithin X A colA m φ := by
  induction φ with
  | adj i j =>
    rw [satWithin_adj, satWithin_adj]
    exact ⟨fun ⟨h, hi, hj⟩ => ⟨h.1, hi, hj⟩,
      fun ⟨h, hi, hj⟩ =>
        ⟨⟨h, Set.notMem_compl_iff.mpr hi, Set.notMem_compl_iff.mpr hj⟩, hi, hj⟩⟩
  | eq i j => exact Iff.rfl
  | color c i => exact Iff.rfl
  | distLe r i j =>
    rw [satWithin_distLe, satWithin_distLe]
    exact withinDistIn_deleteVerts_compl_iff r (m i) (m j)
  | distColorLt r c i =>
    rw [satWithin_distColorLt, satWithin_distColorLt]
    constructor
    · rintro ⟨y, hy, hyX, w, hw, hws⟩
      obtain ⟨q, hq, hqs⟩ := walk_of_deleteVerts_compl w
      exact ⟨y, hy, hyX, q, by rw [hq]; exact hw, by rw [hqs]; exact hws⟩
    · rintro ⟨y, hy, hyX, w, hw, hws⟩
      obtain ⟨q, hq, hqs⟩ := walk_to_deleteVerts_compl w hws
      exact ⟨y, hy, hyX, q, by rw [hq]; exact hw, by rw [hqs]; exact hws⟩
  | not φ ih => rw [satWithin_not, satWithin_not, ih m]
  | and φ ψ ihφ ihψ => rw [satWithin_and, satWithin_and, ihφ m, ihψ m]
  | exU φ ih =>
    rw [satWithin_exU, satWithin_exU]
    exact exists_congr fun w => and_congr_right fun _ => ih _
  | exL r g φ ih =>
    rw [satWithin_exL, satWithin_exL]
    refine exists_congr fun w => and_congr_right fun _ => and_congr ?_ (ih _)
    exact exists_congr fun i => and_congr_right fun _ =>
      withinDistIn_deleteVerts_compl_iff r (m i) w

/-- **The compaction transport, against the isolated kept arena.** The
composite the semantic chain consumes: satisfaction on the compact
carrier is satisfaction relativized to the cluster over the arena with
the cluster's complement isolated. -/
theorem sat_compact_iff_satWithin_deleteVerts_compl (e : Fin N ≃ ↥X)
    (hAdj : ∀ a b : Fin N, B.Adj a b ↔ A.Adj (e a : Fin n) (e b))
    (hcol : ∀ (c : Fin L) (v : Fin N), v ∈ colB c ↔ (e v : Fin n) ∈ colA c)
    {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin N) :
    Sat B colB m φ ↔ SatWithin X (deleteVerts A Xᶜ) colA (fun i => (e (m i) : Fin n)) φ :=
  (sat_compact_iff_satWithin e hAdj hcol φ m).trans
    (satWithin_deleteVerts_compl A colA φ _).symm

end Lax3Proofs.Compaction
