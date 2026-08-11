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

/-- The output of an active cover construction before its block arenas are
put in increasing order.  Breadth-first search naturally emits every
cluster once, but in discovery order.  Every semantic cover clause is
already available at that point; only the representation clause consumed
by the recursive member thread is absent.

Keeping this intermediate surface separate prevents the cover search from
silently assuming a sorting property that its queue does not provide. -/
structure RawCoverOutA {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (r q m : ℕ)
    (Xoff Xmem asg : ℕ → ℕ) : Prop where
  count_le : q ≤ n
  zero : Xoff 0 = 0
  last : Xoff q = m
  mono : ∀ k < q, Xoff k ≤ Xoff (k + 1)
  centre_lt : ∀ k < q, centre k < n
  mem_lt : ∀ p < m, Xmem p < n
  block : ∀ k < q, ∀ w,
    (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem p = w) ↔
      InCluster (masked G A₀) π r (centre k) w
  block_inj : ∀ k < q, ∀ p p', Xoff k ≤ p → p < Xoff (k + 1) →
    Xoff k ≤ p' → p' < Xoff (k + 1) → Xmem p = Xmem p' → p = p'
  asg_lt : ∀ v < n, A₀ v ≠ 0 → asg v < q
  asg_cover : ∀ (v : ℕ) (hv : v < n), A₀ v ≠ 0 →
    ball (masked G A₀) r ⟨v, hv⟩ ⊆
      {z : Fin n | InCluster (masked G A₀) π r (centre (asg v)) (z : ℕ)}

/-- The consumer-facing active cover.  It forgets how the active centres
were enumerated and records only the centre function the block-indexed
driver reads.  Assignments are required exactly on the live vertices of
`A₀`; no dead carrier cell has to be initialised. -/
structure CoverOutA {n : ℕ} (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (r q m : ℕ)
    (Xoff Xmem asg : ℕ → ℕ) : Prop where
  /-- The active centre count fits in the carrier allocation. -/
  count_le : q ≤ n
  /-- The arena starts at zero. -/
  zero : Xoff 0 = 0
  /-- The arena ends after the last active centre. -/
  last : Xoff q = m
  /-- Blocks are laid out in active-centre order. -/
  mono : ∀ k < q, Xoff k ≤ Xoff (k + 1)
  /-- Every active centre is a vertex. -/
  centre_lt : ∀ k < q, centre k < n
  /-- Everything stored in a block is a vertex. -/
  mem_lt : ∀ p < m, Xmem p < n
  /-- Block `k` is the cluster of active centre `centre k`. -/
  block : ∀ k < q, ∀ w,
    (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem p = w) ↔
      InCluster (masked G A₀) π r (centre k) w
  /-- No active block names a vertex twice. -/
  block_inj : ∀ k < q, ∀ p p', Xoff k ≤ p → p < Xoff (k + 1) →
    Xoff k ≤ p' → p' < Xoff (k + 1) → Xmem p = Xmem p' → p = p'
  /-- Each active block lists its vertices in increasing order. -/
  block_mono : ∀ k < q, ∀ p p', Xoff k ≤ p → p < p' →
    p' < Xoff (k + 1) → Xmem p < Xmem p'
  /-- Every live vertex is assigned an active block index. -/
  asg_lt : ∀ v < n, A₀ v ≠ 0 → asg v < q
  /-- The assigned active block contains the live vertex's whole ball. -/
  asg_cover : ∀ (v : ℕ) (hv : v < n), A₀ v ≠ 0 →
    ball (masked G A₀) r ⟨v, hv⟩ ⊆
      {z : Fin n | InCluster (masked G A₀) π r (centre (asg v)) (z : ℕ)}

namespace RawCoverOutA

variable {n r q m : ℕ} {G : SimpleGraph (Fin n)} {A₀ centre Xoff Xmem Xmem' asg : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)}

/-- The exact contract of the final block sorter.  It may rearrange each
half-open block, but must preserve its membership and return a strictly
increasing vertex sequence.  Those two facts turn the raw BFS output into
the consumer-facing active cover; injectivity of the sorted blocks follows
from strict increase and need not be assumed from the sorter. -/
theorem sorted (h : RawCoverOutA G A₀ π centre r q m Xoff Xmem asg)
    (hmem : ∀ p < m, Xmem' p < n)
    (hblock : ∀ k < q, ∀ w,
      (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem' p = w) ↔
        (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem p = w))
    (hmono : ∀ k < q, ∀ p p', Xoff k ≤ p → p < p' →
      p' < Xoff (k + 1) → Xmem' p < Xmem' p') :
    CoverOutA G A₀ π centre r q m Xoff Xmem' asg := by
  refine
    { count_le := h.count_le
      zero := h.zero
      last := h.last
      mono := h.mono
      centre_lt := h.centre_lt
      mem_lt := hmem
      block := ?_
      block_inj := ?_
      block_mono := hmono
      asg_lt := h.asg_lt
      asg_cover := h.asg_cover }
  · intro k hk w
    rw [hblock k hk w, h.block k hk w]
  · intro k hk p p' hp hp_end hp' hp'_end heq
    by_cases hpp : p < p'
    · have hlt := hmono k hk p p' hp hpp hp'_end
      omega
    · by_cases hpp' : p' < p
      · have hlt := hmono k hk p' p hp' hpp' hp_end
        omega
      · omega

/-- A sorted active cover can always be viewed at the raw boundary. -/
theorem of_sorted (h : CoverOutA G A₀ π centre r q m Xoff Xmem asg) :
    RawCoverOutA G A₀ π centre r q m Xoff Xmem asg :=
  { count_le := h.count_le
    zero := h.zero
    last := h.last
    mono := h.mono
    centre_lt := h.centre_lt
    mem_lt := h.mem_lt
    block := h.block
    block_inj := h.block_inj
    asg_lt := h.asg_lt
    asg_cover := h.asg_cover }

end RawCoverOutA

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

/-- Forget the two enumerations and expose the active block interface.
The only additional input is the member list's completeness for the live
mask; `RamDriver.MemEnum` supplies it at every driver level. -/
theorem toActive (h : CoverOutM G A₀ mm Mem Pos π ord r m Xoff Xmem asg)
    (hord : OrdersByM mm Mem π ord)
    (hcomplete : ∀ v < n, A₀ v ≠ 0 → ∃ k < mm, Mem k = v) :
    CoverOutA G A₀ π (fun k => ord (Pos k)) r mm m Xoff Xmem asg := by
  refine
    { count_le := h.count_le
      zero := h.zero
      last := h.last
      mono := h.mono
      centre_lt := fun k hk => h.ord_pos_lt hord hk
      mem_lt := h.mem_lt
      block := h.block
      block_inj := h.block_inj
      block_mono := h.block_mono
      asg_lt := ?_
      asg_cover := ?_ }
  · intro v hv halive
    obtain ⟨k, hk, hkv⟩ := hcomplete v hv halive
    rw [← hkv]
    exact h.asg_lt k hk
  · intro v hv halive
    obtain ⟨k, hk, hkv⟩ := hcomplete v hv halive
    subst v
    simpa using h.asg_cover k hk

end CoverOutM

namespace CoverOut

variable {n r m : ℕ} {G : SimpleGraph (Fin n)} {A₀ ord Xoff Xmem asg : ℕ → ℕ}
  {π : Equiv.Perm (Fin n)}

/-- The landed carrier-wide output, restricted to the live vertices on
the assignment axis, is an active cover with `n` centres. -/
theorem toActive (h : CoverOut G A₀ π ord r m Xoff Xmem asg)
    (hord : OrdersBy n π ord) :
    CoverOutA G A₀ π ord r n m Xoff Xmem asg :=
  { count_le := le_rfl
    zero := h.zero
    last := h.last
    mono := h.mono
    centre_lt := fun _ hk => hord.lt hk
    mem_lt := h.mem_lt
    block := h.block
    block_inj := h.block_inj
    block_mono := h.block_mono
    asg_lt := fun v hv _ => h.asg_lt v hv
    asg_cover := fun v hv _ => h.asg_cover v hv }

end CoverOut

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
