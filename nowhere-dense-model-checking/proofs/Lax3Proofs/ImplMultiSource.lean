import Lax3Proofs.ImplProfiles

/-!
# Multi-source BFS via a virtual source (F3b, §6.3) — consumer-side

F3 (`ProgFrame`) found that `ImplProfiles`' colour half — one
single-source BFS per class *member* — exceeds §6.3's charge envelope
`O((m+L)·‖B₀‖·(R+1))` by a factor `‖B₀‖`: §6.3 budgets **one** BFS per
colour class. The tower has no multi-source BFS (frozen, another
submission), so the fix is entirely consumer-side: run the tower's
single-source BFS on the **augmented graph** `vsrc H X` — `H` embedded
by `Fin.castSucc` on `Fin (n+1)`, plus the virtual source `Fin.last n`
adjacent to exactly the `castSucc`-image of the class `X` — from the
source `Fin.last n` at cap `R+1`.

## §1 `vsrc` and the distance bridge

The load-bearing lemma is `vsrc_withinDist_succ_iff`, both directions:

    WithinDist (vsrc H X) (b+1) (Fin.last n) z.castSucc
      ↔ ∃ y ∈ X, WithinDist H b y z

— a walk from the virtual source spends its first edge into `X`
(`vsrc_exists_first_edge`) and then lives in the embedded `H`; a
revisit of the source only wastes edges (`vsrc_walk_pull_or_shortcut`
peels it to a strictly shorter walk from the source, and the induction
restarts). The `+1` shift is exactly the class-distance/virtual-source-
distance conversion; the degenerate radius is pinned separately:
distance `0` from the source reaches only itself
(`vsrc_withinDist_zero_iff`), and the source is reached by nothing at
distance `0` (`vsrc_not_withinDist_zero_of`). The embedded-walk
transport is reproved privately here (`ArenaTransport`'s
`exists_walk_push/pull` are `private`; `Compaction`/`ImplCover` each
did the same) — `castSucc` is injective, and the virtual source carries
**no** edges beyond the class image (`vsrc_adj_last_iff`), the two dead
ends E6's `(f '' s)ᶜ` hazard warns about.

## §2 The profiles route, restored

`colorTable_of_ballTable` consumes one `BallTable (vsrc H X)
(Fin.last n) (R+1) D` — verbatim the postcondition of
`ImplBfs.bfsAlg_computes_ball_B0` at `vsrc H X` from `Fin.last n`, cap
`R+1` (`bfsAlg_computes_colorTable` is that instantiation, spelled
out): the colour row at threshold `b ≤ R`, in `Driver.childCol`'s own
orientation `{z | ∃ y ∈ X, WithinDist H b z y}`, is the thresholded
array row `{z | D z.castSucc ≤ b + 1}`. Everything is measured in
`H = preG`, **before isolation**, and the rows are cumulative (`≤ b`)
— E12d's hazards carry over unchanged.

`recordProfilesMS` is `ImplProfiles.recordProfiles` with the colour
half rerouted: the seam `ProfileTablesMS` holds `mb` batch tables as
before plus **`L` virtual-source tables** — one per class, not one per
member — and `recordProfilesMS_eq_childCol` is the same statement as
`ImplProfiles.recordProfiles_eq_childCol` with the MS seam.

**The marker class is free** (E12d: `relPal`'s last colour is `univ`,
`relColoring_last`). Its `pu` semantics `∃ y ∈ univ, WithinDist H b z y`
holds at every `z` via `y := z` (`marker_pu_row`), and
`markerTable_ballTable` exhibits a closed-form `BallTable` for
`vsrc H univ` — source at distance `0`, everything else at distance `1`
— so the marker's seam entry costs **no BFS at all**; a machine spends
`L - 1` calls and the charge below, counting `L`, only over-approximates.

## §3 The charge (§6.3's `O((m+L)·‖B₀‖·(R+1))`, restored)

One virtual-source call is `callCostV H X R`: the four `chargeB0`
currencies of the BFS at `vsrc H X`, radius `R+1` — exactly their
`chargeB0_total` sum (`callCostV_eq_chargeB0_add_rows`) — plus the
`R+1` cumulative rows of carrier width `n` read back. The augmented
arena is honestly bigger and honestly bounded: `‖vsrc H X‖ =
(n+1) + (M + |X|) ≤ 2‖H‖ + 1` (`gsize_vsrc_le`, via the degree sum),
so the uniform per-class budget `callCostMS` dominates every class's
call (`callCostV_le_callCostMS`) and the batch call too
(`callCost_le_callCostMS`).

`profilesChargeMS H mb L R = mb·callCost + L·callCostMS` is the
`(mb + L)`-call account, and **`profilesChargeMS_le`** closes the leaf:

    profilesChargeMS H mb L R ≤ (mb + L) · 6(R+1)(‖B₀‖+1)

— §6.3's `O((m+L)·‖B₀‖·(R+1))` **without** the `L·N₀` factor that
`ImplProfiles.profilesCharge_le_iterated` carries (`(mb + Λ·n)` there).
§6.3's own caveat is unchanged: `L` is the node's palette, constant in
`n` but tower-sized in the depth if the `pu` family survives (O3).
-/

namespace Lax3Proofs.Impl

open Lax62Proofs.Refine
open Lax3.ColoredGraphs
open Lax3Proofs.WalkDistance
open Lax3Proofs.Driver

variable {n : ℕ}

/-! ### §1 The virtual-source graph -/

/-- **The augmented graph** (§6.3's multi-source device, consumer-side):
`H` embedded on `Fin (n+1)` by `Fin.castSucc`, plus the virtual source
`Fin.last n`, adjacent to exactly `{y.castSucc | y ∈ X}`. -/
def vsrc (H : SimpleGraph (Fin n)) (X : Set (Fin n)) : SimpleGraph (Fin (n + 1)) where
  Adj a b :=
    (∃ u v : Fin n, H.Adj u v ∧ a = u.castSucc ∧ b = v.castSucc)
    ∨ (∃ y ∈ X, a = Fin.last n ∧ b = y.castSucc)
    ∨ (∃ y ∈ X, a = y.castSucc ∧ b = Fin.last n)
  symm := by
    rintro a b (⟨u, v, huv, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · exact Or.inl ⟨v, u, huv.symm, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨y, hy, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨y, hy, rfl, rfl⟩)
  loopless := by
    constructor
    rintro a (⟨u, v, huv, rfl, h⟩ | ⟨y, hy, rfl, h⟩ | ⟨y, hy, rfl, h⟩)
    · obtain rfl : u = v := Fin.castSucc_inj.mp h
      exact H.irrefl huv
    · exact (Fin.castSucc_lt_last y).ne' h
    · exact (Fin.castSucc_lt_last y).ne h

/-- The BFS needs the adjacency decidable; it is, from `H`'s and the
class's. -/
instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (X : Set (Fin n))
    [DecidablePred (· ∈ X)] : DecidableRel (vsrc H X).Adj := fun a b =>
  inferInstanceAs (Decidable
    ((∃ u v : Fin n, H.Adj u v ∧ a = u.castSucc ∧ b = v.castSucc)
      ∨ (∃ y ∈ X, a = Fin.last n ∧ b = y.castSucc)
      ∨ (∃ y ∈ X, a = y.castSucc ∧ b = Fin.last n)))

section Vsrc

variable {H : SimpleGraph (Fin n)} {X : Set (Fin n)}

theorem vsrc_adj {a b : Fin (n + 1)} :
    (vsrc H X).Adj a b ↔
      (∃ u v : Fin n, H.Adj u v ∧ a = u.castSucc ∧ b = v.castSucc)
      ∨ (∃ y ∈ X, a = Fin.last n ∧ b = y.castSucc)
      ∨ (∃ y ∈ X, a = y.castSucc ∧ b = Fin.last n) := Iff.rfl

/-- Inside the embedding, `vsrc` is exactly `H`. -/
@[simp] theorem vsrc_adj_castSucc {u v : Fin n} :
    (vsrc H X).Adj u.castSucc v.castSucc ↔ H.Adj u v := by
  rw [vsrc_adj]
  constructor
  · rintro (⟨u', v', h, hu, hv⟩ | ⟨y, hy, hu, -⟩ | ⟨y, hy, -, hv⟩)
    · obtain rfl : u = u' := Fin.castSucc_inj.mp hu
      obtain rfl : v = v' := Fin.castSucc_inj.mp hv
      exact h
    · exact absurd hu (Fin.castSucc_lt_last u).ne
    · exact absurd hv (Fin.castSucc_lt_last v).ne
  · exact fun h => Or.inl ⟨u, v, h, rfl, rfl⟩

/-- **The virtual source carries no other edges**: its neighbours are
exactly the class image. (E6's hazard: a stray edge here would poison
every distance.) -/
theorem vsrc_adj_last_iff {c : Fin (n + 1)} :
    (vsrc H X).Adj (Fin.last n) c ↔ ∃ y ∈ X, c = y.castSucc := by
  rw [vsrc_adj]
  constructor
  · rintro (⟨u, v, h, hu, -⟩ | ⟨y, hy, -, rfl⟩ | ⟨y, hy, hu, -⟩)
    · exact absurd hu (Fin.castSucc_lt_last u).ne'
    · exact ⟨y, hy, rfl⟩
    · exact absurd hu (Fin.castSucc_lt_last y).ne'
  · rintro ⟨y, hy, rfl⟩
    exact Or.inr (Or.inl ⟨y, hy, rfl, rfl⟩)

/-- An edge leaving an embedded vertex either stays embedded (an
`H`-edge) or enters the virtual source (so the vertex is in `X`). -/
theorem vsrc_adj_castSucc_iff {y : Fin n} {c : Fin (n + 1)} :
    (vsrc H X).Adj y.castSucc c ↔
      (∃ v : Fin n, H.Adj y v ∧ c = v.castSucc) ∨ (y ∈ X ∧ c = Fin.last n) := by
  rw [vsrc_adj]
  constructor
  · rintro (⟨u', v', h, hu, rfl⟩ | ⟨y', hy', hu, -⟩ | ⟨y', hy', hu, rfl⟩)
    · obtain rfl : y = u' := Fin.castSucc_inj.mp hu
      exact Or.inl ⟨v', h, rfl⟩
    · exact absurd hu (Fin.castSucc_lt_last y).ne
    · obtain rfl : y = y' := Fin.castSucc_inj.mp hu
      exact Or.inr ⟨hy', rfl⟩
  · rintro (⟨v, hv, rfl⟩ | ⟨hy, rfl⟩)
    · exact Or.inl ⟨y, v, hv, rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨y, hy, rfl, rfl⟩)

/-! ### The embedded-walk transport and the distance bridge -/

/-- An `H`-walk embeds into `vsrc` at the same length (`castSucc` edge
by edge). -/
private theorem vsrc_walk_push {y z : Fin n} {b : ℕ} (h : WithinDist H b y z) :
    WithinDist (vsrc H X) b y.castSucc z.castSucc := by
  obtain ⟨p, hp⟩ := h
  suffices h : ∃ q : (vsrc H X).Walk y.castSucc z.castSucc, q.length = p.length by
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by omega⟩
  clear hp
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | cons hadj p ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨.cons (vsrc_adj_castSucc.mpr hadj) q, by simp [hq]⟩

/-- A `vsrc`-walk between embedded endpoints either pulls back to `H`
whole (no shorter), or meets the virtual source — and then its suffix
is a strictly shorter walk from the source: revisiting the source only
wastes edges. -/
private theorem vsrc_walk_pull_or_shortcut {a b : Fin (n + 1)}
    (q : (vsrc H X).Walk a b) :
    ∀ {y z : Fin n}, a = y.castSucc → b = z.castSucc →
      (∃ p : H.Walk y z, p.length ≤ q.length) ∨
        ∃ r : (vsrc H X).Walk (Fin.last n) z.castSucc, r.length < q.length := by
  induction q with
  | nil =>
    rintro y z rfl hb
    obtain rfl : y = z := Fin.castSucc_inj.mp hb
    exact Or.inl ⟨.nil, by simp⟩
  | @cons a c b hadj q ih =>
    rintro y z rfl rfl
    rcases vsrc_adj_castSucc_iff.mp hadj with ⟨v, hyv, rfl⟩ | ⟨-, rfl⟩
    · rcases ih rfl rfl with ⟨p, hp⟩ | ⟨r, hr⟩
      · refine Or.inl ⟨.cons hyv p, ?_⟩
        rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]
        omega
      · refine Or.inr ⟨r, ?_⟩
        rw [SimpleGraph.Walk.length_cons]
        omega
    · refine Or.inr ⟨q, ?_⟩
      rw [SimpleGraph.Walk.length_cons]
      omega

/-- A walk from the virtual source to an embedded vertex spends its
first edge into the class image. -/
private theorem vsrc_exists_first_edge {a b : Fin (n + 1)}
    (w : (vsrc H X).Walk a b) {z : Fin n} (ha : a = Fin.last n)
    (hb : b = z.castSucc) :
    ∃ y ∈ X, ∃ q : (vsrc H X).Walk y.castSucc z.castSucc,
      q.length + 1 ≤ w.length := by
  cases w with
  | nil =>
    subst ha
    exact absurd hb.symm (Fin.castSucc_lt_last z).ne
  | cons hadj q =>
    subst ha hb
    obtain ⟨y, hy, rfl⟩ := vsrc_adj_last_iff.mp hadj
    exact ⟨y, hy, q, by rw [SimpleGraph.Walk.length_cons]⟩

/-- The forward half of the bridge: a `vsrc`-distance bound from the
source yields a class member within `H`-distance one less. The
recursion restarts on the strictly shorter walk whenever the tail
revisits the source. -/
private theorem vsrc_exists_of_withinDist_last {z : Fin n} (d : ℕ)
    (h : WithinDist (vsrc H X) d (Fin.last n) z.castSucc) :
    ∃ y ∈ X, WithinDist H (d - 1) y z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨y, hyX, q, hq⟩ := vsrc_exists_first_edge w rfl rfl
  rcases vsrc_walk_pull_or_shortcut q rfl rfl with ⟨p, hp⟩ | ⟨r, hr⟩
  · exact ⟨y, hyX, p, by omega⟩
  · obtain ⟨y', hy', hyz⟩ := vsrc_exists_of_withinDist_last (d - 2) ⟨r, by omega⟩
    exact ⟨y', hy', withinDist_mono_radius (by omega) hyz⟩
termination_by d
decreasing_by omega

/-- **The distance bridge** (the load-bearing lemma, both directions):
`vsrc`-distance `b+1` from the virtual source to an embedded vertex is
`H`-distance `b` from the class. The `+1` is the shift every profile
row rides on. -/
theorem vsrc_withinDist_succ_iff (H : SimpleGraph (Fin n)) (X : Set (Fin n))
    (b : ℕ) (z : Fin n) :
    WithinDist (vsrc H X) (b + 1) (Fin.last n) z.castSucc ↔
      ∃ y ∈ X, WithinDist H b y z := by
  constructor
  · intro h
    simpa using vsrc_exists_of_withinDist_last (b + 1) h
  · rintro ⟨y, hyX, h⟩
    have hedge : (vsrc H X).Adj (Fin.last n) y.castSucc :=
      vsrc_adj_last_iff.mpr ⟨y, hyX, rfl⟩
    exact withinDist_mono_radius (by omega)
      (withinDist_trans (withinDist_of_adj hedge) (vsrc_walk_push h))

/-- Degenerate boundary, outward: at distance `0` the virtual source
reaches only itself — in particular no embedded vertex, whatever `X`. -/
theorem vsrc_withinDist_zero_iff (H : SimpleGraph (Fin n)) (X : Set (Fin n))
    (v : Fin (n + 1)) :
    WithinDist (vsrc H X) 0 (Fin.last n) v ↔ v = Fin.last n := by
  constructor
  · rintro ⟨w, hw⟩
    exact (SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hw)).symm
  · rintro rfl
    exact withinDist_refl _ _ _

/-- Degenerate boundary, inward: the virtual source is reached by no
embedded vertex at distance `0`. -/
theorem vsrc_not_withinDist_zero_of (H : SimpleGraph (Fin n)) (X : Set (Fin n))
    (z : Fin n) : ¬ WithinDist (vsrc H X) 0 z.castSucc (Fin.last n) := fun h =>
  (Fin.castSucc_lt_last z).ne
    (((vsrc_withinDist_zero_iff H X _).mp (withinDist_symm h)))

/-! ### §2 The colour rows off one virtual-source table -/

/-- **The colour row, one BFS per class** (the E12d route restored):
under a `BallTable` of the virtual-source BFS at cap `R+1`, the colour
row at threshold `b ≤ R` — in `childCol`'s `pu` orientation, cumulative
— is the thresholded array row at `b+1`. -/
theorem colorTable_of_ballTable {H : SimpleGraph (Fin n)} {X : Set (Fin n)}
    {R : ℕ} {D : Fin (n + 1) → ℕ}
    (hD : BallTable (vsrc H X) (Fin.last n) (R + 1) D) {b : ℕ} (hb : b ≤ R) :
    {z | ∃ y ∈ X, WithinDist H b z y} = {z | D z.castSucc ≤ b + 1} := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, h⟩
    exact (hD z.castSucc (b + 1) (by omega)).mpr (mem_ball.mpr
      ((vsrc_withinDist_succ_iff H X b z).mpr ⟨y, hy, withinDist_symm h⟩))
  · intro h
    obtain ⟨y, hy, h'⟩ := (vsrc_withinDist_succ_iff H X b z).mp
      (mem_ball.mp ((hD z.castSucc (b + 1) (by omega)).mp h))
    exact ⟨y, hy, withinDist_symm h'⟩

/-- The seam instantiation, spelled out: the tower's BFS
(`bfsAlg_computes_ball_B0`) at `vsrc H X` from the virtual source, cap
`R+1`, refines the spec whose postcondition is exactly the `BallTable`
that `colorTable_of_ballTable` and `ProfileTablesMS` consume — one call
per colour class. -/
theorem bfsAlg_computes_colorTable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (X : Set (Fin n)) [DecidablePred (· ∈ X)] (R : ℕ) :
    Bfs.bfsAlg (vsrc H X) (fun _ => true) (Fin.last n) (R + 1) ≤
      NRest.spec (fun D => BallTable (vsrc H X) (Fin.last n) (R + 1) D)
        (fun _ => liftACost (chargeB0 (vsrc H X) (R + 1))) :=
  bfsAlg_computes_ball_B0 (vsrc H X) (Fin.last n) (R + 1)

/-! ### The marker class is free -/

/-- **The marker row is everything, at every radius** (E12d's finding,
here a zero-cost fact): `∃ y ∈ univ, WithinDist H b z y` holds via
`y := z`. -/
theorem marker_pu_row (H : SimpleGraph (Fin n)) (b : ℕ) :
    {z | ∃ y ∈ (Set.univ : Set (Fin n)), WithinDist H b z y} = Set.univ :=
  Set.eq_univ_of_forall fun z => ⟨z, Set.mem_univ z, withinDist_refl H b z⟩

/-- The closed-form distance array of the marker class: the source at
`0`, everything else at `1`. -/
def markerTable (n : ℕ) : Fin (n + 1) → ℕ :=
  fun v => if v = Fin.last n then 0 else 1

/-- **No BFS on the marker class**: `markerTable` is a valid `BallTable`
of `vsrc H univ` at every cap, for free — the marker's entry in the
seam costs nothing (`relPal`'s last colour is `univ`,
`relColoring_last`). -/
theorem markerTable_ballTable (H : SimpleGraph (Fin n)) (d : ℕ) :
    BallTable (vsrc H Set.univ) (Fin.last n) d (markerTable n) := by
  intro v k _
  induction v using Fin.lastCases with
  | last =>
    simpa [markerTable] using mem_ball_self (vsrc H Set.univ) k (Fin.last n)
  | cast z =>
    have hne : z.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last z).ne
    cases k with
    | zero =>
      simp only [markerTable, if_neg hne]
      constructor
      · omega
      · intro h
        exact absurd ((vsrc_withinDist_zero_iff H Set.univ _).mp h) hne
    | succ k =>
      simp only [markerTable, if_neg hne]
      constructor
      · exact fun _ => (vsrc_withinDist_succ_iff H Set.univ k z).mpr
          ⟨z, Set.mem_univ z, withinDist_refl H k z⟩
      · omega

end Vsrc

/-! ### §2a `recordProfilesMS` and the identity to `Driver.childCol` -/

variable {Λ mb : ℕ}

/-- **The multi-source seam** to the tower (E11, one hypothesis wide):
`mb` batch tables exactly as in `ImplProfiles.ProfileTables`, plus **one
virtual-source table per colour class** — the postcondition of
`bfsAlg_computes_ball_B0` at `vsrc H (f c)` from `Fin.last n`, cap
`R+1` (`bfsAlg_computes_colorTable`). `m + L` calls, not
`m + Σ_c |f c|`; the marker class's entry is `markerTable n` for free
(`markerTable_ballTable`). -/
def ProfileTablesMS (H : SimpleGraph (Fin n)) (w : Fin mb → Fin n)
    (f : Fin Λ → Set (Fin n)) (R : ℕ) (Dp : Fin mb → Fin n → ℕ)
    (Dc : Fin Λ → Fin (n + 1) → ℕ) : Prop :=
  (∀ j, BallTable H (w j) R (Dp j)) ∧
    ∀ c, BallTable (vsrc H (f c)) (Fin.last n) (R + 1) (Dc c)

/-- **`recordProfilesMS`** (§6.3, the multi-source route): the slot
coloring populated from `mb + L` arrays — old colours at their old
slots, the cumulative batch rows `{z | Dp j z ≤ a}` at the `pd` slots,
and at the `pu` slots the virtual-source rows `{z | Dc c z.castSucc ≤
b + 1}` — the `+1` is the bridge's shift. Its meaning is
`recordProfilesMS_eq_childCol`. -/
def recordProfilesMS (R : ℕ) (f : Fin Λ → Set (Fin n))
    (Dp : Fin mb → Fin n → ℕ) (Dc : Fin Λ → Fin (n + 1) → ℕ) :
    Coloring n (isoPal Λ mb R) :=
  slotColoring f (fun j a => {z | Dp j z ≤ (a : ℕ)})
    (fun c b => {z | Dc c z.castSucc ≤ (b : ℕ) + 1})

section Slots

variable {R : ℕ} (f : Fin Λ → Set (Fin n)) (Dp : Fin mb → Fin n → ℕ)
  (Dc : Fin Λ → Fin (n + 1) → ℕ)

@[simp] theorem recordProfilesMS_old (c : Fin Λ) :
    recordProfilesMS R f Dp Dc (isoOld c) = f c :=
  slotColoring_old ..

@[simp] theorem recordProfilesMS_pd (j : Fin mb) (a : Fin (R + 1)) :
    recordProfilesMS R f Dp Dc (isoPd j a) = {z | Dp j z ≤ (a : ℕ)} :=
  slotColoring_pd ..

@[simp] theorem recordProfilesMS_pu (c : Fin Λ) (b : Fin (R + 1)) :
    recordProfilesMS R f Dp Dc (isoPu c b) = {z | Dc c z.castSucc ≤ (b : ℕ) + 1} :=
  slotColoring_pu ..

variable {f Dp Dc} {H : SimpleGraph (Fin n)} {w : Fin mb → Fin n}

/-- Under the seam, the `pd` slot `(j, a)` is the cumulative distance-
`≤ a` set of the `j`-th padded batch vertex, in `H` — before isolation.
(Verbatim `ImplProfiles.recordProfiles_pd_eq`: the batch half is
unchanged.) -/
theorem recordProfilesMS_pd_eq (h : ProfileTablesMS H w f R Dp Dc)
    (j : Fin mb) (a : Fin (R + 1)) :
    recordProfilesMS R f Dp Dc (isoPd j a)
      = {z | WithinDist H (a : ℕ) z (w j)} := by
  rw [recordProfilesMS_pd, batchRow_eq (h.1 j)]

/-- Under the seam, the `pu` slot `(c, b)` is the cumulative distance-
`≤ b` set of the colour class `f c`, in `H` — before isolation. One
virtual-source BFS, not `|f c|` single-source ones. -/
theorem recordProfilesMS_pu_eq (h : ProfileTablesMS H w f R Dp Dc)
    (c : Fin Λ) (b : Fin (R + 1)) :
    recordProfilesMS R f Dp Dc (isoPu c b)
      = {z | ∃ y ∈ f c, WithinDist H (b : ℕ) z y} := by
  rw [recordProfilesMS_pu,
    ← colorTable_of_ballTable (h.2 c) (Nat.lt_succ_iff.mp b.isLt)]

/-- The marker slot under the seam: a class that is everything rows
everything, at every threshold — no BFS was needed to know it. -/
theorem recordProfilesMS_pu_marker (h : ProfileTablesMS H w f R Dp Dc)
    {c : Fin Λ} (hc : f c = Set.univ) (b : Fin (R + 1)) :
    recordProfilesMS R f Dp Dc (isoPu c b) = Set.univ := by
  rw [recordProfilesMS_pu_eq h, hc, marker_pu_row]

end Slots

variable {L n₀ : ℕ}

/-- **The identity to the driver** — the same statement as
`ImplProfiles.recordProfiles_eq_childCol` with the MS seam: at the
child of centre `u` — graph `preG` (before isolation), batch `batchFn`
(padded), classes `childColR` (the node's colours with the marker) —
`recordProfilesMS` **equals `Driver.childCol S A π u`**: same
`Fin (S.R + 1)` indexing, same cumulative `≤ a` sense, same `preG`.
F3c substitutes this where the frame program holds the child's
colours. -/
theorem recordProfilesMS_eq_childCol (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {Dp : Fin S.width → Fin (childN S A π u) → ℕ}
    {Dc : Fin (relPal Λ) → Fin (childN S A π u + 1) → ℕ}
    (h : ProfileTablesMS (preG S A π u) (batchFn S A π u) (childColR S A π u)
      S.R Dp Dc) :
    recordProfilesMS S.R (childColR S A π u) Dp Dc = childCol S A π u := by
  have hg : (fun j (a : Fin (S.R + 1)) => {z | Dp j z ≤ (a : ℕ)})
      = fun j (a : Fin (S.R + 1)) =>
          {z | WithinDist (preG S A π u) (a : ℕ) z (batchFn S A π u j)} :=
    funext fun j => funext fun a => batchRow_eq (h.1 j) a
  have hh : (fun c (b : Fin (S.R + 1)) => {z | Dc c z.castSucc ≤ (b : ℕ) + 1})
      = fun c (b : Fin (S.R + 1)) => {z | ∃ y ∈ childColR S A π u c,
          WithinDist (preG S A π u) (b : ℕ) z y} :=
    funext fun c => funext fun b =>
      (colorTable_of_ballTable (h.2 c) (Nat.lt_succ_iff.mp b.isLt)).symm
  unfold recordProfilesMS childCol
  rw [hg, hh]

/-! ### §3 The charge -/

section Charge

variable (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- An embedded vertex keeps its `H`-neighbours (embedded) and gains at
most the virtual source. -/
theorem degree_vsrc_castSucc_le (X : Set (Fin n)) [DecidablePred (· ∈ X)]
    (u : Fin n) : (vsrc H X).degree u.castSucc ≤ H.degree u + 1 := by
  have hsub : (vsrc H X).neighborFinset u.castSucc ⊆
      (H.neighborFinset u).image Fin.castSucc ∪ {Fin.last n} := by
    intro c hc
    rw [SimpleGraph.mem_neighborFinset] at hc
    rcases vsrc_adj_castSucc_iff.mp hc with ⟨v, hv, rfl⟩ | ⟨-, rfl⟩
    · refine Finset.mem_union_left _ (Finset.mem_image_of_mem _ ?_)
      rw [SimpleGraph.mem_neighborFinset]
      exact hv
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  calc (vsrc H X).degree u.castSucc
      ≤ ((H.neighborFinset u).image Fin.castSucc ∪ {Fin.last n}).card :=
        Finset.card_le_card hsub
    _ ≤ ((H.neighborFinset u).image Fin.castSucc).card
          + ({Fin.last n} : Finset (Fin (n + 1))).card :=
        Finset.card_union_le _ _
    _ ≤ H.degree u + 1 := by
        have h := Finset.card_image_le
          (s := H.neighborFinset u) (f := Fin.castSucc)
        rw [Finset.card_singleton]
        exact Nat.add_le_add_right h 1

/-- The virtual source has at most `n` neighbours (it is not its own). -/
theorem degree_vsrc_last_le (X : Set (Fin n)) [DecidablePred (· ∈ X)] :
    (vsrc H X).degree (Fin.last n) ≤ n := by
  have h := SimpleGraph.degree_lt_card_verts (G := vsrc H X) (Fin.last n)
  rw [Fintype.card_fin] at h
  omega

/-- The augmented graph has at most `M + |X| ≤ M + n` edges: the
embedded edges plus the star at the source, by the degree sum. -/
theorem card_edgeFinset_vsrc_le (X : Set (Fin n)) [DecidablePred (· ∈ X)] :
    (vsrc H X).edgeFinset.card ≤ H.edgeFinset.card + n := by
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (vsrc H X)
  have hH := SimpleGraph.sum_degrees_eq_twice_card_edges H
  have hb : ∑ a : Fin (n + 1), (vsrc H X).degree a
      ≤ (∑ u : Fin n, (H.degree u + 1)) + n := by
    rw [Fin.sum_univ_castSucc]
    exact Nat.add_le_add
      (Finset.sum_le_sum fun u _ => degree_vsrc_castSucc_le H X u)
      (degree_vsrc_last_le H X)
  rw [Finset.sum_add_distrib, hH, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hb
  omega

/-- **The honest size bound**: `‖vsrc H X‖ = (n+1) + (M+|X|) ≤ 2‖H‖+1`
— the augmented arena is at most twice `B₀` plus the source itself. -/
theorem gsize_vsrc_le (X : Set (Fin n)) [DecidablePred (· ∈ X)] :
    gsize (vsrc H X) ≤ 2 * gsize H + 1 := by
  have h := card_edgeFinset_vsrc_le H X
  unfold gsize
  omega

/-- One virtual-source call, exact: the four `chargeB0` currencies of
the BFS at `vsrc H X`, radius `R+1` (their total: `chargeB0_total`),
plus the `R+1` cumulative rows of carrier width `n` read back at the
thresholds `b+1`, `b ≤ R`. -/
def callCostV (X : Set (Fin n)) [DecidablePred (· ∈ X)] (R : ℕ) : ℕ :=
  (2 * gsize (vsrc H X) + (R + 1) + 2) + (R + 1) * n

/-- The BFS part of `callCostV` is exactly the `chargeB0` account of
one `bfsAlg_computes_colorTable` call — `chargeB0`-shaped plus row
writes, nothing else. -/
theorem callCostV_eq_chargeB0_add_rows (X : Set (Fin n))
    [DecidablePred (· ∈ X)] (R : ℕ) :
    callCostV H X R = ((chargeB0 (vsrc H X) (R + 1)).toFun "bfs.init"
      + (chargeB0 (vsrc H X) (R + 1)).toFun "if"
      + (chargeB0 (vsrc H X) (R + 1)).toFun "bfs.level"
      + (chargeB0 (vsrc H X) (R + 1)).toFun "bfs.expand") + (R + 1) * n := by
  unfold callCostV
  rw [chargeB0_total]

/-- The uniform per-class budget: `callCostV` with the class-dependent
`‖vsrc H X‖` replaced by its bound `2‖H‖+1` — what one colour class is
charged regardless of its size. -/
def callCostMS (R : ℕ) : ℕ :=
  (2 * (2 * gsize H + 1) + (R + 1) + 2) + (R + 1) * n

/-- Every class's actual call fits the uniform budget. -/
theorem callCostV_le_callCostMS (X : Set (Fin n)) [DecidablePred (· ∈ X)]
    (R : ℕ) : callCostV H X R ≤ callCostMS H R := by
  have h := gsize_vsrc_le H X
  unfold callCostV callCostMS
  omega

/-- A batch call (single-source, on `H` itself, cap `R`) also fits the
uniform budget. -/
theorem callCost_le_callCostMS (R : ℕ) : callCost H R ≤ callCostMS H R := by
  unfold callCost callCostMS
  omega

/-- The `Λ` uniform budgets cover the `Λ` actual class calls, whatever
the classes are: the exact colour-half account `Σ_c callCostV` fits the
`L·callCostMS` half of `profilesChargeMS`. -/
theorem sum_callCostV_le (f : Fin Λ → Set (Fin n))
    [∀ c, DecidablePred (· ∈ f c)] (R : ℕ) :
    ∑ c, callCostV H (f c) R ≤ Λ * callCostMS H R := by
  calc ∑ c, callCostV H (f c) R
      ≤ ∑ _c : Fin Λ, callCostMS H R :=
        Finset.sum_le_sum fun c _ => callCostV_le_callCostMS H (f c) R
    _ = Λ * callCostMS H R := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The multi-source charge of the profiles routine**: `mb` batch
calls at `callCost` plus **`L` virtual-source calls** at the uniform
budget — `(mb + L)` calls, §6.3's count. (The marker class costs `0`
by `markerTable_ballTable`; charging it a full call only
over-approximates.) -/
def profilesChargeMS (mb L R : ℕ) : ℕ :=
  mb * callCost H R + L * callCostMS H R

/-- One virtual-source call is `O(‖B₀‖·(R+1))`: at most
`6(R+1)(‖H‖+1)`. -/
theorem callCostMS_le (R : ℕ) : callCostMS H R ≤ 6 * (R + 1) * (gsize H + 1) := by
  have hn : n ≤ gsize H := Nat.le_add_right n _
  have h2 : (R + 1) * n ≤ (R + 1) * gsize H := Nat.mul_le_mul_left _ hn
  unfold callCostMS
  nlinarith [h2]

/-- **The §6.3 bound, restored** — the leaf's point: the whole routine
is at most `(mb + L) · 6(R+1)(‖B₀‖+1)`, which is
`O((m + L)·‖B₀‖·(R+1))` **without** the extra `L·N₀` factor of the
iterated route (`ImplProfiles.profilesCharge_le_iterated`'s
`(mb + Λ·n)`). §6.3's caveat stands: `L` is the node's palette,
constant in `n` but tower-sized in the depth if the `pu` family
survives (O3). -/
theorem profilesChargeMS_le (mb L R : ℕ) :
    profilesChargeMS H mb L R ≤ (mb + L) * (6 * (R + 1) * (gsize H + 1)) := by
  calc profilesChargeMS H mb L R
      ≤ mb * callCostMS H R + L * callCostMS H R :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left mb (callCost_le_callCostMS H R)) _
    _ = (mb + L) * callCostMS H R := (Nat.add_mul mb L _).symm
    _ ≤ (mb + L) * (6 * (R + 1) * (gsize H + 1)) :=
        Nat.mul_le_mul_left _ (callCostMS_le H R)

end Charge

end Lax3Proofs.Impl
