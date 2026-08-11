import Lax3Proofs.RamCover

/-!
# Member-scoped ordering and cover contracts

The carrier-wide `RamCover.OrdersBy` and `RamCover.CoverOut` contracts
describe the root instance exactly, but force every nested ordering and
cover pass to initialise dead positions.  This file gives their active-list
counterparts without changing the landed contracts.

There are two lists. `Mem` enumerates the active vertices. `Pos` enumerates,
in increasing order, the positions those vertices occupy in `π`.  The cover
arena is indexed by the `Pos` list rather than by every carrier position;
assignments therefore name an index below `mm`.  The identity-list theorems
at the end show that this is an exact generalisation of the landed surface.
-/

namespace Lax3Proofs.RamCover

open Lax3.ColoredGraphs
open Lax3Proofs.RamBfs (masked)

/-- `ord` inverts `π` at the positions occupied by the first `mm`
members of `Mem`. -/
def OrdersByM {n : ℕ} (mm : ℕ) (Mem : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (ord : ℕ → ℕ) : Prop :=
  ∀ k, k < mm → ∀ hk : Mem k < n,
    ord ((π ⟨Mem k, hk⟩ : Fin n) : ℕ) = Mem k

namespace OrdersByM

variable {n mm : ℕ} {Mem ord : ℕ → ℕ} {π : Equiv.Perm (Fin n)}

/-- The member's rank is sent back to the member. -/
theorem ord_rk (h : OrdersByM mm Mem π ord) {k : ℕ} (hk : k < mm)
    (hmem : Mem k < n) : ord (rk n π (Mem k)) = Mem k := by
  rw [rk_of_lt hmem]
  exact h k hk hmem

/-- The carrier-wide contract restricts to every member list. -/
theorem of_ordersBy (h : OrdersBy n π ord) : OrdersByM mm Mem π ord :=
  fun _ _ hmem => h ⟨_, hmem⟩

end OrdersByM

/-- A member-scoped neighborhood-cover output.  `Pos` lists, in increasing
ordering position, exactly the ranks of the active vertices in `Mem`.
Blocks and assignments are indexed by this list, so their live range is
`mm`, not the carrier size `n`. -/
structure CoverOutM {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (mm : ℕ) (Mem Pos : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord : ℕ → ℕ)
    (r m : ℕ) (Xoff Xmem asg : ℕ → ℕ) : Prop where
  /-- The active list fits in the carrier. -/
  count_le : mm ≤ n
  /-- Every listed member is a vertex. -/
  member_lt : ∀ k < mm, Mem k < n
  /-- Every listed ordering position is a carrier position. -/
  pos_lt : ∀ k < mm, Pos k < n
  /-- Positions are processed in increasing ordering rank. -/
  pos_mono : ∀ k k' : ℕ, k < k' → k' < mm → Pos k < Pos k'
  /-- Every listed position is the rank of a listed member. -/
  pos_sound : ∀ k < mm, ∃ q < mm, Pos k = rk n π (Mem q)
  /-- Every listed member's rank occurs in the position list. -/
  pos_covers : ∀ q < mm, ∃ k < mm, Pos k = rk n π (Mem q)
  /-- The arena starts at zero. -/
  zero : Xoff 0 = 0
  /-- The arena ends after the last active position. -/
  last : Xoff mm = m
  /-- Blocks are laid out in position-list order. -/
  mono : ∀ k < mm, Xoff k ≤ Xoff (k + 1)
  /-- Everything stored in a block is a vertex. -/
  mem_lt : ∀ p < m, Xmem p < n
  /-- Block `k` is the cluster of the centre at active position `Pos k`. -/
  block : ∀ k < mm, ∀ w,
    (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem p = w) ↔
      InCluster (masked G A₀) π r (ord (Pos k)) w
  /-- No active block names a vertex twice. -/
  block_inj : ∀ k < mm, ∀ p q, Xoff k ≤ p → p < Xoff (k + 1) →
    Xoff k ≤ q → q < Xoff (k + 1) → Xmem p = Xmem q → p = q
  /-- Each active block lists its vertices in increasing order. -/
  block_mono : ∀ k < mm, ∀ p q, Xoff k ≤ p → p < q →
    q < Xoff (k + 1) → Xmem p < Xmem q
  /-- Every listed member is assigned an active block index. -/
  asg_lt : ∀ k < mm, asg (Mem k) < mm
  /-- The assigned active block contains the listed member's whole ball. -/
  asg_cover : ∀ (k : ℕ) (hk : k < mm),
    ball (masked G A₀) r ⟨Mem k, member_lt k hk⟩ ⊆
      {z : Fin n |
        InCluster (masked G A₀) π r (ord (Pos (asg (Mem k)))) (z : ℕ)}

namespace CoverOutM

variable {n mm r m : ℕ} {G : SimpleGraph (Fin n)} {A₀ Mem Pos ord Xoff Xmem asg : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)}

/-- A listed position names a listed vertex when the member ordering
contract holds. -/
theorem ord_pos (h : CoverOutM G A₀ mm Mem Pos π ord r m Xoff Xmem asg)
    (hord : OrdersByM mm Mem π ord) {k : ℕ} (hk : k < mm) :
    ∃ q < mm, ord (Pos k) = Mem q := by
  obtain ⟨q, hq, hpos⟩ := h.pos_sound k hk
  refine ⟨q, hq, ?_⟩
  rw [hpos, hord.ord_rk hq (h.member_lt q hq)]

/-- Consequently every active centre is a vertex. -/
theorem ord_pos_lt (h : CoverOutM G A₀ mm Mem Pos π ord r m Xoff Xmem asg)
    (hord : OrdersByM mm Mem π ord) {k : ℕ} (hk : k < mm) : ord (Pos k) < n := by
  obtain ⟨q, hq, heq⟩ := h.ord_pos hord hk
  rw [heq]
  exact h.member_lt q hq

end CoverOutM

/-- On the identity member list, the member ordering contract is exactly
the landed carrier-wide contract. -/
theorem ordersByM_identity_iff {n : ℕ} {π : Equiv.Perm (Fin n)} {ord : ℕ → ℕ} :
    OrdersByM n (fun k => k) π ord ↔ OrdersBy n π ord := by
  constructor
  · intro h v
    simpa using h (v : ℕ) v.isLt v.isLt
  · exact OrdersByM.of_ordersBy

/-- The identity vertex and position lists recover `CoverOut` exactly.
This is the compatibility shim used by the existing carrier-wide root. -/
theorem coverOutM_identity_iff {n r m : ℕ} {G : SimpleGraph (Fin n)}
    {A₀ ord Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} :
    CoverOutM G A₀ n (fun k => k) (fun k => k) π ord r m Xoff Xmem asg ↔
      CoverOut G A₀ π ord r m Xoff Xmem asg := by
  constructor
  · intro h
    refine ⟨h.zero, h.last, h.mono, h.mem_lt, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc w
      simpa using h.block c hc w
    · intro c hc p q hp hp' hq hq' heq
      exact h.block_inj c hc p q hp hp' hq hq' heq
    · intro c hc p q hp hpq hq
      exact h.block_mono c hc p q hp hpq hq
    · intro w hw
      simpa using h.asg_lt w hw
    · intro w hw
      simpa using h.asg_cover w hw
  · intro h
    refine
      { count_le := le_rfl
        member_lt := fun _ hk => hk
        pos_lt := fun _ hk => hk
        pos_mono := fun _ _ hkk _ => hkk
        pos_sound := ?_
        pos_covers := ?_
        zero := h.zero
        last := h.last
        mono := h.mono
        mem_lt := h.mem_lt
        block := ?_
        block_inj := h.block_inj
        block_mono := h.block_mono
        asg_lt := ?_
        asg_cover := ?_ }
    · intro k hk
      let q : Fin n := π.symm ⟨k, hk⟩
      refine ⟨(q : ℕ), q.isLt, ?_⟩
      rw [rk_fin]
      exact congrArg Fin.val (π.apply_symm_apply ⟨k, hk⟩).symm
    · intro q hq
      refine ⟨rk n π q, rk_lt hq, rfl⟩
    · intro k hk w
      simpa using h.block k hk w
    · intro k hk
      simpa using h.asg_lt k hk
    · intro k hk
      simpa using h.asg_cover k hk

end Lax3Proofs.RamCover
