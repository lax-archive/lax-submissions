import Lax185574.TypeTrees
import Lax185574Proofs.WalkDistance
import Lax185574Proofs.Legacy

/-!
Type trees and the satisfaction of distance formulas are invariant under
renaming the vertices of a partial graph along a bijection. This lets
statements about partial graphs on `Fin n` be applied to partial graphs
on any finite vertex type.
-/

namespace Lax185574Proofs.TypeTreeTransport

open Lax185574.PartialGraphs Lax185574.GaifmanGraph
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.WordEncoding Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

variable {V W : Type*}

/-- The partial graph `G` with its vertices renamed along `e`. -/
def transport (G : PartialGraph V) (e : V ≃ W) : PartialGraph W where
  edge := G.edge.comap e.symm
  nonEdge := G.nonEdge.comap e.symm
  disjoint := by
    have h := G.disjoint
    rw [disjoint_iff] at h ⊢
    ext u v
    simp only [SimpleGraph.inf_adj, SimpleGraph.comap_adj, SimpleGraph.bot_adj, iff_false,
      not_and]
    intro h1 h2
    have := congrArg (fun H : SimpleGraph V => H.Adj (e.symm u) (e.symm v)) h
    simp only [SimpleGraph.inf_adj, SimpleGraph.bot_adj, eq_iff_iff, iff_false, not_and] at this
    exact this h1 h2
  color := G.color ∘ e.symm

theorem resolved_transport (G : PartialGraph V) (e : V ≃ W) :
    (transport G e).resolved = G.resolved.comap e.symm := by
  ext u v
  simp [PartialGraph.resolved, transport]

theorem withinDist_transport (G : PartialGraph V) (e : V ≃ W) (d : ℕ) (u v : V) :
    WithinDist (transport G e).resolved d (e u) (e v) ↔ WithinDist G.resolved d u v := by
  rw [resolved_transport]
  have h := withinDist_iso (d := d) (u := e u) (v := e v) (SimpleGraph.Iso.comap e.symm G.resolved)
  simpa using h.symm

theorem withinDistLt_transport (G : PartialGraph V) (e : V ≃ W) (d : ℕ) (u v : V) :
    WithinDistLt (transport G e).resolved d (e u) (e v) ↔ WithinDistLt G.resolved d u v := by
  cases d with
  | zero => simp [WithinDistLt]
  | succ d =>
    have h := withinDist_transport G e d u v
    simp only [WithinDist] at h
    simp only [WithinDistLt, Nat.lt_succ_iff]
    exact h

theorem sat_transport (G : PartialGraph V) (e : V ≃ W) :
    ∀ {ℓ : ℕ} (m : Fin ℓ → V) (φ : DistFO ℓ), Sat (transport G e) (e ∘ m) φ ↔ Sat G m φ
  | _, m, .eq i j => by simp [Sat]
  | _, m, .edge i j => by simp [Sat, transport]
  | _, m, .nonEdge i j => by simp [Sat, transport]
  | _, m, .color Y i => by simp [Sat, transport]
  | _, m, .distLe r i j => by simp only [Sat, Function.comp_apply, withinDist_transport]
  | _, m, .distColorLt r Y i => by
    simp only [Sat, Function.comp_apply]
    constructor
    · rintro ⟨v, hv, hd⟩
      refine ⟨e.symm v, by simpa [transport] using hv, ?_⟩
      rw [← withinDistLt_transport G e]
      simpa using hd
    · rintro ⟨v, hv, hd⟩
      refine ⟨e v, by simpa [transport] using hv, ?_⟩
      rwa [withinDistLt_transport G e]
  | _, m, .not φ => by simp only [Sat, sat_transport G e m φ]
  | _, m, .and φ ψ => by simp only [Sat, sat_transport G e m φ, sat_transport G e m ψ]
  | _, m, .exLocal i s φ => by
    simp only [Sat]
    constructor
    · rintro ⟨v, hv, hφ⟩
      refine ⟨e.symm v, ?_, ?_⟩
      · rw [← withinDist_transport G e]
        simpa using hv
      · rw [← sat_transport G e (Fin.snoc m (e.symm v)) φ, Fin.comp_snoc]
        simpa using hφ
    · rintro ⟨v, hv, hφ⟩
      refine ⟨e v, ?_, ?_⟩
      · rw [Function.comp_apply, withinDist_transport]
        exact hv
      · rw [← Fin.comp_snoc, sat_transport G e]
        exact hφ

theorem atp_transport (G : PartialGraph V) (e : V ≃ W) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) :
    atp (transport G e) k q (e ∘ a) = atp G k q a := by
  ext φ
  simp only [atp, Set.mem_ofPred_eq, sat_transport]

theorem node_transport (G : PartialGraph V) (e : V ≃ W) :
    ∀ (q k : ℕ) {ℓ : ℕ} (a : Fin ℓ → V), node (transport G e) k q (e ∘ a) = node G k q a
  | 0, k, _, a => by
    show finsetOf _ = finsetOf _
    rw [atp_transport]
  | q + 1, k, ℓ, a => by
    simp only [node, atp_transport]
    congr 2
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, b, hb, rfl⟩
      refine ⟨i, e.symm b, ?_, ?_⟩
      · rw [← withinDist_transport G e]
        simpa using hb
      · rw [← node_transport G e q (k + 1) (Fin.snoc a (e.symm b)), Fin.comp_snoc]
        simp
    · rintro ⟨i, b, hb, rfl⟩
      refine ⟨i, e b, ?_, ?_⟩
      · rw [Function.comp_apply, withinDist_transport]
        exact hb
      · rw [← Fin.comp_snoc, node_transport G e q (k + 1)]

theorem tree_transport (G : PartialGraph V) (e : V ≃ W) (k q : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) :
    tree (transport G e) k q (e ∘ a) = tree G k q a := by
  simp only [tree, node_transport]

end Lax185574Proofs.TypeTreeTransport
