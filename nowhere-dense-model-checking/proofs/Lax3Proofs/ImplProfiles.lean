import Lax3Proofs.DriverArena
import Lax3Proofs.ImplBfs

/-!
# `recordProfiles` (E12d, §6.3, §4 row 5) — the profile rows off the BFS tables

§5 line 20: `B₀ := recordProfiles(B₀, W)` — the cumulative capped
distance rows for the `m` padded batch vertices and the colour classes,
measured in **`B₀` = `preG`, BEFORE isolation** (the campaign's hazard 1:
measured after isolation every distance `≥ 1` row is `∅` and the
`Isolate.sat_iso` rewrite would be unsound, not lossy —
`DriverArena.lean:53-57`). The identity target is
`Driver.childCol`'s two slot families, verbatim.

## §1 The program and its seam

The tower has exactly one BFS, single-source
(`ImplBfs.bfsAlg_computes_ball_B0`), and its postcondition is
`BallTable H s d D : ∀ v, ∀ k ≤ d, (D v ≤ k ↔ v ∈ ball H k s)` —
one distance array `D` answering every radius `k ≤ d` at once. That
array read at the thresholds `a = 0, …, R` IS the cumulative row family
(`≤ a`, never `= a`): no per-radius recomputation, one call per source.
The machine therefore runs

* **the batch half** — one BFS at radius `R` from each of the `m` padded
  batch vertices `w j` (`j : Fin mb`, duplicates included: the batch is
  padded to the schedule's width, and *a padded repeat costs another
  BFS call here* — `profilesCharge` counts `mb` calls flat; a machine
  could copy the repeated row instead, which only lowers the charge);
* **the colour half** — the tower has **no multi-source BFS**, so per
  the E12 split note the honest route is *iterated single-source calls
  over the class members*: one BFS from each `y ∈ f c`, the colour row
  at threshold `b` being the union `{z | ∃ y ∈ f c, Dc c y z ≤ b}` of
  the member rows. (The virtual-source alternative — one call per
  colour on a graph with an added vertex adjacent to the class — needs
  a walk-surgery bridge that does not stay within ~80 consumer-side
  lines; the cost difference is recorded at the charge, §3.)

Everything below consumes the tower through the one-hypothesis seam
`ProfileTables` (a conjunction of `BallTable`s — E11's seam, crossed
exactly as `ImplBfs` §2 crossed it), and the distance arrays are the
outputs `bfsAlg_computes_ball_B0`'s spec guarantees, verbatim.

## §2 The identity to the driver

`recordProfiles f Dp Dc` is the `slotColoring` whose old slots are `f`,
whose `pd` slots are the batch rows and whose `pu` slots are the colour
rows. Under `ProfileTables`:

* `recordProfiles_pd_eq` : the `(j, a)` slot is
  `{z | WithinDist H (a : ℕ) z (w j)}` — cumulative, in `H` = `preG`;
* `recordProfiles_pu_eq` : the `(c, b)` slot is
  `{z | ∃ y ∈ f c, WithinDist H (b : ℕ) z y}`;
* **`recordProfiles_eq_childCol`** : at
  `H := preG S A π u`, `w := batchFn S A π u`, `f := childColR S A π u`,
  the whole coloring **equals `Driver.childCol S A π u`** — same
  `Fin (S.R + 1)` indexing, same cumulative sense, same `preG`. E13
  plugs this equality where the driver holds the child's colours.

## §3 The charge (§6.3: `O((m + L)·‖B₀‖·(R+1))`)

One call is `callCost H R = (2‖B₀‖ + R + 2) + (R + 1)·n`: the four
BFS currencies of `chargeB0` — exactly their `chargeB0_total` sum
(`callCost_eq_chargeB0_add_rows`) — plus the `R + 1` cumulative rows of
carrier width the call populates. The whole routine is
`profilesCharge = (mb + Σ_c |f c|) · callCost`, bounded by
`(mb + Σ_c |f c|) · 3(R+1)(‖B₀‖ + 1)` (`profilesCharge_le`).

**The honest gap to §6.3, stated rather than hidden.** §6.3 charges
`(m + L)` BFS calls because it assumes a *multi-source* BFS per colour
class. The iterated route makes `Σ_c |f c| ≤ L·n` colour calls instead
of `L` (`classSum_le`, `profilesCharge_le_iterated`): the colour term is
`O(L·‖B₀‖²·(R+1))`, a factor `‖B₀‖` above §6.3's `O(L·‖B₀‖·(R+1))`.
The batch term matches §6.3 exactly. And §6.3's own caveat carries
over verbatim: **`L` here is the palette `relPal Λ` of the node, which
is constant in `n` but grows in the depth `j` — as a tower of height
`ℓ` if the `pu` family survives (O3)** — so the charge is
`O(L_ℓ·‖B₀‖²·(R+1))` with `L_ℓ` tower-sized, not "a constant".
-/

namespace Lax3Proofs.Impl

open Lax3.ColoredGraphs
open Lax3Proofs.WalkDistance
open Lax3Proofs.Driver

variable {n : ℕ}

/-! ### §1 The rows read off one distance array -/

section Rows

variable {H : SimpleGraph (Fin n)} {R : ℕ}

/-- The `BallTable` postcondition read at one threshold, in the driver's
orientation (`z` to the source): the distance-array test `D z ≤ a` is
`WithinDist H a z s`, for every `a ≤ R`. -/
theorem ballTable_le_iff {s : Fin n} {D : Fin n → ℕ} (hD : BallTable H s R D)
    {z : Fin n} {a : ℕ} (ha : a ≤ R) : D z ≤ a ↔ WithinDist H a z s :=
  ⟨fun h => withinDist_symm ((hD z a ha).mp h),
   fun h => (hD z a ha).mpr (withinDist_symm h)⟩

/-- **The batch row** (cumulative, `≤ a`): the distance array of one BFS
from `s`, thresholded at `a ≤ R`, is the set within distance `a` of
`s` — `childCol`'s `pd` family shape. -/
theorem batchRow_eq {s : Fin n} {D : Fin n → ℕ} (hD : BallTable H s R D)
    (a : Fin (R + 1)) :
    {z | D z ≤ (a : ℕ)} = {z | WithinDist H (a : ℕ) z s} :=
  Set.ext fun _ => ballTable_le_iff hD (Nat.lt_succ_iff.mp a.isLt)

/-- **The colour row** (cumulative, `≤ b`): the union over the class
members of their thresholded rows is the set within distance `b` of the
class — `childCol`'s `pu` family shape. One BFS per member (the iterated
route; module docstring §1). -/
theorem colorRow_eq {X : Set (Fin n)} {Dc : Fin n → Fin n → ℕ}
    (hDc : ∀ y ∈ X, BallTable H y R (Dc y)) (b : Fin (R + 1)) :
    {z | ∃ y ∈ X, Dc y z ≤ (b : ℕ)} = {z | ∃ y ∈ X, WithinDist H (b : ℕ) z y} :=
  Set.ext fun _ => exists_congr fun y => and_congr_right fun hy =>
    ballTable_le_iff (hDc y hy) (Nat.lt_succ_iff.mp b.isLt)

end Rows

/-! ### §2 `recordProfiles` and the identity to `Driver.childCol` -/

variable {Λ mb : ℕ}

/-- The one-hypothesis seam to the tower (E11): every distance array is
a `BallTable` of its BFS — `Dp j` of the call at the `j`-th padded batch
vertex, `Dc c y` of the call at the class member `y ∈ f c` (entries of
`Dc` at non-members are never read and carry no constraint). These are
verbatim the postconditions `bfsAlg_computes_ball_B0` guarantees for the
`mb + Σ_c |f c|` single-source calls at radius `R` on `H`. -/
def ProfileTables (H : SimpleGraph (Fin n)) (w : Fin mb → Fin n)
    (f : Fin Λ → Set (Fin n)) (R : ℕ) (Dp : Fin mb → Fin n → ℕ)
    (Dc : Fin Λ → Fin n → Fin n → ℕ) : Prop :=
  (∀ j, BallTable H (w j) R (Dp j)) ∧ ∀ c, ∀ y ∈ f c, BallTable H y R (Dc c y)

/-- **`recordProfiles`** (§6.3, §4 row 5): the slot coloring populated
by the BFS rows — old colours at their old slots, the cumulative batch
rows `{z | Dp j z ≤ a}` at the `pd` slots, the cumulative colour rows
`{z | ∃ y ∈ f c, Dc c y z ≤ b}` at the `pu` slots. A function of the
distance arrays alone; its meaning is `recordProfiles_eq_childCol`. -/
def recordProfiles (R : ℕ) (f : Fin Λ → Set (Fin n))
    (Dp : Fin mb → Fin n → ℕ) (Dc : Fin Λ → Fin n → Fin n → ℕ) :
    Coloring n (isoPal Λ mb R) :=
  slotColoring f (fun j a => {z | Dp j z ≤ (a : ℕ)})
    (fun c b => {z | ∃ y ∈ f c, Dc c y z ≤ (b : ℕ)})

section Slots

variable {R : ℕ} (f : Fin Λ → Set (Fin n)) (Dp : Fin mb → Fin n → ℕ)
  (Dc : Fin Λ → Fin n → Fin n → ℕ)

@[simp] theorem recordProfiles_old (c : Fin Λ) :
    recordProfiles R f Dp Dc (isoOld c) = f c :=
  slotColoring_old ..

@[simp] theorem recordProfiles_pd (j : Fin mb) (a : Fin (R + 1)) :
    recordProfiles R f Dp Dc (isoPd j a) = {z | Dp j z ≤ (a : ℕ)} :=
  slotColoring_pd ..

@[simp] theorem recordProfiles_pu (c : Fin Λ) (b : Fin (R + 1)) :
    recordProfiles R f Dp Dc (isoPu c b) = {z | ∃ y ∈ f c, Dc c y z ≤ (b : ℕ)} :=
  slotColoring_pu ..

variable {f Dp Dc} {H : SimpleGraph (Fin n)} {w : Fin mb → Fin n}

/-- Under the seam, the `pd` slot `(j, a)` is the cumulative distance-
`≤ a` set of the `j`-th padded batch vertex, in `H` — before
isolation. -/
theorem recordProfiles_pd_eq (h : ProfileTables H w f R Dp Dc)
    (j : Fin mb) (a : Fin (R + 1)) :
    recordProfiles R f Dp Dc (isoPd j a) = {z | WithinDist H (a : ℕ) z (w j)} := by
  rw [recordProfiles_pd, batchRow_eq (h.1 j)]

/-- Under the seam, the `pu` slot `(c, b)` is the cumulative distance-
`≤ b` set of the colour class `f c`, in `H` — before isolation. -/
theorem recordProfiles_pu_eq (h : ProfileTables H w f R Dp Dc)
    (c : Fin Λ) (b : Fin (R + 1)) :
    recordProfiles R f Dp Dc (isoPu c b) = {z | ∃ y ∈ f c, WithinDist H (b : ℕ) z y} := by
  rw [recordProfiles_pu, colorRow_eq (h.2 c) b]

end Slots

variable {L n₀ : ℕ}

/-- **The identity to the driver** (the E12d deliverable): at the child
of centre `u` — graph `preG` (before isolation), batch `batchFn`
(padded), classes `childColR` (the node's colours with the marker) —
`recordProfiles` **equals `Driver.childCol S A π u`**: same
`Fin (S.R + 1)` indexing, same cumulative `≤ a` sense, same `preG`.
E13 substitutes this where the driver holds the child's colours. -/
theorem recordProfiles_eq_childCol (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N)
    {Dp : Fin S.width → Fin (childN S A π u) → ℕ}
    {Dc : Fin (relPal Λ) → Fin (childN S A π u) → Fin (childN S A π u) → ℕ}
    (h : ProfileTables (preG S A π u) (batchFn S A π u) (childColR S A π u)
      S.R Dp Dc) :
    recordProfiles S.R (childColR S A π u) Dp Dc = childCol S A π u := by
  have hg : (fun j (a : Fin (S.R + 1)) => {z | Dp j z ≤ (a : ℕ)})
      = fun j (a : Fin (S.R + 1)) =>
          {z | WithinDist (preG S A π u) (a : ℕ) z (batchFn S A π u j)} :=
    funext fun j => funext fun a => batchRow_eq (h.1 j) a
  have hh : (fun c (b : Fin (S.R + 1)) =>
        {z | ∃ y ∈ childColR S A π u c, Dc c y z ≤ (b : ℕ)})
      = fun c (b : Fin (S.R + 1)) => {z | ∃ y ∈ childColR S A π u c,
          WithinDist (preG S A π u) (b : ℕ) z y} :=
    funext fun c => funext fun b => colorRow_eq (h.2 c) b
  unfold recordProfiles childCol
  rw [hg, hh]

/-! ### §3 The charge -/

/-- One call of the routine: the four BFS currencies of `chargeB0`
(their total is `2‖H‖ + R + 2`, `chargeB0_total`) plus the `R + 1`
cumulative rows of carrier width `n` the call populates. -/
def callCost (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (R : ℕ) : ℕ :=
  (2 * gsize H + R + 2) + (R + 1) * n

/-- The BFS part of `callCost` is exactly the `chargeB0` account of one
`bfsAlg_computes_ball_B0` call — the charge is `chargeB0`-shaped plus
row writes, nothing else. -/
theorem callCost_eq_chargeB0_add_rows (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (R : ℕ) :
    callCost H R = ((chargeB0 H R).toFun "bfs.init" + (chargeB0 H R).toFun "if"
      + (chargeB0 H R).toFun "bfs.level" + (chargeB0 H R).toFun "bfs.expand")
      + (R + 1) * n := by
  unfold callCost
  rw [chargeB0_total]

/-- The number of colour-half calls of the iterated route: one BFS per
class member, summed over the classes. (§6.3's multi-source count would
be `Λ`; the gap is the module docstring's §3 note.) -/
noncomputable def classSum (f : Fin Λ → Set (Fin n)) : ℕ := ∑ c, (f c).ncard

/-- **The closed-form charge of `recordProfiles`**: `mb` batch calls
(padded — a repeat costs another call) plus `Σ_c |f c|` colour calls,
each at `callCost`. -/
noncomputable def profilesCharge (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (mb : ℕ) (f : Fin Λ → Set (Fin n)) (R : ℕ) : ℕ :=
  (mb + classSum f) * callCost H R

/-- One call is `O(‖B₀‖·(R+1))`: precisely at most `3(R+1)(‖H‖+1)`. -/
theorem callCost_le (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (R : ℕ) :
    callCost H R ≤ 3 * (R + 1) * (gsize H + 1) := by
  have hn : n ≤ gsize H := Nat.le_add_right n _
  have h2 : (R + 1) * n ≤ (R + 1) * gsize H := Nat.mul_le_mul_left _ hn
  unfold callCost
  nlinarith [h2]

/-- **The §6.3-shaped bound at the honest call count**: the whole
routine is at most `(mb + Σ_c |f c|) · 3(R+1)(‖B₀‖+1)` — the batch term
is §6.3's `O(m·‖B₀‖·(R+1))` verbatim. -/
theorem profilesCharge_le (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (mb : ℕ) (f : Fin Λ → Set (Fin n)) (R : ℕ) :
    profilesCharge H mb f R ≤ (mb + classSum f) * (3 * (R + 1) * (gsize H + 1)) :=
  Nat.mul_le_mul_left _ (callCost_le H R)

/-- A class has at most `n` members, so the colour half makes at most
`Λ·n` calls. -/
theorem classSum_le (f : Fin Λ → Set (Fin n)) : classSum f ≤ Λ * n := by
  unfold classSum
  calc ∑ c, (f c).ncard ≤ ∑ _c : Fin Λ, n :=
        Finset.sum_le_sum fun c _ => by
          simpa using Set.ncard_le_ncard (Set.subset_univ (f c)) Set.finite_univ
    _ = Λ * n := by simp [mul_comm]

/-- **The iterated route's total, with the gap to §6.3 in the open**:
`O((mb + Λ·n)·‖B₀‖·(R+1))`. Against §6.3's `O((m + L)·‖B₀‖·(R+1))` the
colour term carries an extra factor `n ≤ ‖B₀‖` — the price of having no
multi-source BFS in the tower (module docstring §3). `Λ` here is the
node's palette (`relPal Λ` at the child of depth `j`): constant in `n`
but tower-sized in `j` if the `pu` family survives — §6.3's own caveat,
not a constant to hide. -/
theorem profilesCharge_le_iterated (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (mb : ℕ) (f : Fin Λ → Set (Fin n)) (R : ℕ) :
    profilesCharge H mb f R ≤ (mb + Λ * n) * (3 * (R + 1) * (gsize H + 1)) :=
  le_trans (profilesCharge_le H mb f R)
    (Nat.mul_le_mul_right _ (Nat.add_le_add_left (classSum_le f) mb))

end Lax3Proofs.Impl
