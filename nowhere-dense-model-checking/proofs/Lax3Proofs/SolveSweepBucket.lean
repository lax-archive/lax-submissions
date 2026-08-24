import Lax3Proofs.SolveSweepMdPeel

/-!
# F6c13 — the peel at a linear budget: the amortization, and why the
pinned tie-break blocks the program

Wave 23 (`SolveSweepMdPeel`) discharges `CovMdPeelIn`
(`SolveSweepOrder.lean:451-480`) verbatim, at

```
Kmp = fun _ A => 86 * A.N * A.N + 43 * A.N + 14
```

because each round finds its minimum by a **full carrier scan**. §7 of
the algorithm charges the whole cover routine at `a·N^{1+2δ}`, so the
`N²` breaks the headline at the root. This leaf was to replace the
scan by the textbook **bucket-queue degeneracy ordering** and land the
same residual at `O(N + m)`, `m` the augmented graph's slot count.

**It does not.** `CovMdPeelIn` is not discharged here, at any budget:
the selection the residual demands is not one a bucket queue can
deliver, and the reason is in `minDegVert`, not in the data structure.
What is delivered is everything else.

## What this file contains

* **§1–§3 the amortization, proved.** The whole cost argument behind
  `O(N + m)` — that the peel's deletes sum to the slot count, that the
  slot count is what `DelAdjSt`'s offset region measures, and that a
  peel loop whose round costs `a + b·d` (in the round's *current*
  degree `d`) and whose cursor falls by at most one per round runs
  inside `(a+e)·N + b·m + e·N + O(1)` — is discharged here, abstractly
  and reusably. `peelLoop_linear` and `peelLoop_linear_cursor` are
  `Spec`s over an arbitrary round body: whoever writes the `O(1)`-per-
  round selection gets the linear budget by instantiating them. Nothing
  in this half depends on how the minimum is found. (Both carry a
  factor two of slack on the `b·m` term: peeling `v` releases `2·b·d`
  of potential and the round is charged `b·d`, so the exact sum of the
  deletes is `b·m/2`.)

* **§4 what the selection owes.** `eq_minDegVert_of_bucket` — the
  bucket-queue shape of the round's correctness obligation — and
  `minDeg_le_minDeg_erase_succ`, the fact that licenses the cursor
  hypothesis of `peelLoop_linear_cursor`.

* **§5 the tie-break is free upstream, proved.** The full six-clause
  `AugChainData` at an *arbitrary* attaining selection
  (`selOrderingRoutine_data`), with the landed routine recovered on the
  nose at the pinned one (`selOrderingRoutine_mdSel`). This is the
  licence for the fix below.

## The finding, stated once here

`CovMdPeelIn` demands `RankArr (ra j) (mdPerm (mdChain A.G R).toGraph)`
— the rank array *at the pinned permutation*. `mdPerm` is built from
`mdRank = mdRankAux F Finset.univ`, whose every round takes

```
minDegVert F S hS = (S.filter (deg = min deg)).min'
```

— the minimum-degree vertex **of least index**. So a round must return
the least index of the current minimum-degree bucket, not an arbitrary
member of it. That is exactly the clause the textbook `O(N+m)` bucket
queue does not provide: Matula–Beck is linear *because* its pop is
arbitrary, and every constant-time bucket discipline that returns the
least index has a quadratic family.

* **Buckets as unsorted lists, scanned for their least member.** A
  perfect matching on `N` vertices puts all `N` vertices in bucket `1`;
  the cursor alternates `1, 0, 1, 0, …` and each return to bucket `1`
  rescans `Θ(N)` live members. `Θ(N²)` at `m = N/2`.

* **One index cursor per degree level, reset when a vertex drops below
  it.** Take a hub `h` adjacent to `u_1 … u_K` (indices `1 … K`), each
  `u_i` also carrying a private pendant `t_i` (index `K+i`). Popping
  `t_i` drops `u_i` to degree `1`, resetting the level-1 cursor to `i`;
  `u_i` is popped, and the cursor must then walk from `i` back past
  `u_{i+1} … u_K` (all still of degree `2`) to reach `t_{i+1}`. `Θ(K²)`
  at `N = 2K+1`, `m = 2K`.

* **Buckets as index-sorted lists.** Removals preserve sortedness, so
  the two families above are linear here; but an insertion must find
  its rank. Give `w_1 < … < w_s` degree `4` and hang a pendant trigger
  on each, ordered so the triggers are popped in increasing index: each
  `w_j` is then inserted at the *tail* of the growing sorted bucket `3`
  while the cursor sits at `1`, at cost `j`. `Θ(s²)`.

The obstruction is not a missing trick, and it is not only about
`min'`. `CovMdPeelIn`'s postcondition names `mdPerm F`, a function of
the *graph*, so the pass's output may not depend on anything else in
the state — and in particular not on the order the adjacency rows
happen to store neighbours in, which `DelAdjSt` deliberately leaves
free (it asks only that each live prefix list `u`'s current
neighbours, in no stated order). A bucket queue's `O(1)` pop returns
whatever its lists were built from, i.e. a function of that row order:
it cannot meet *any* postcondition of the form `RankArr ra (π F)`
unless the row order is first made canonical. Once it is, the pop must
be an extremum of the current bucket in a fixed total order on
`Fin N` — an integer priority-queue extract-min over `[0, N)`
interleaved with `Θ(N + m)` decrease-keys, which is exactly the
sortedness the three families above price.

Three ways out, none of them inside this leaf's ownership:

1. **Re-pin the tie-break to the machine's own order.** §5 proves this
   is free: `minDegVert`'s `min'` is not needed for anything upstream —
   `selRankAux_props` reruns `mdRankAux_props` (injectivity, values
   `< |S|`, the back-degree bound at *every* valid `k`) using only
   `MinDegSel.card_le`, i.e. that the choice attains the minimum
   degree, and `selOrderingRoutine_data` lands the six clauses at any
   such choice. What remains is to sort the adjacency rows by index
   once (counting sort, `O(N+m)`), which makes the bucket order a
   function of `G`, and to define the selection as that canonical run's
   pop. Both the new `mdRank` and a `CovSelPeelIn` stated at it live in
   `SolveSweepOrder`, which this leaf does not own.
2. **Accept a `log` factor.** A binary heap keyed on `deg·N + index`
   gives `O((N+m)·log N)` at the pinned tie-break with no upstream
   change at all, `Kmp` written using `Nat.log 2 A.N`. Still under
   `a·N^{1+2δ}` for `δ > 0`.
3. **Re-charge the landed `peelCom`.** Wave 23 pays `54·N` per round
   for a delete that costs `54·d`; `peelLoop_linear` turns that into
   `54·m` once, giving `32·N² + 54·m + O(N)` (the deletes' exact sum
   is `27·m`) — a real improvement on sparse arenas, but still
   quadratic in the scan, so it is *not* landed here.

Nothing in §1–§3 is conditional on which way out is taken: the deletes
are `O(m)` and the cursor is `O(N)` in all three.

## Where the amortization lives

`livePot F S = ∑ u ∈ S, |nbrsIn F S u|` — twice the number of live
edges. `livePot_erase` is the whole argument: peeling `v` out of `S`
drops the potential by exactly `2·|nbrsIn F S v|`, so a round charged
`b·d` is paid for out of the potential's own fall.
`sum_dg_eq_livePot` says the potential is literally the sum of the
machine's degree array at a peel state, and `offF_eq_slotCount` says
its initial value is the offset region's own width `offF N`.
`peelLoop_linear_cursor` adds the second half: a cursor that falls by
at most one per round has total rise `≤ 2N`, which `minDeg_le_minDeg_erase_succ`
justifies at the abstract peel.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax12.UniformQuasiWideness (deleteVerts)
open Lax3Proofs.CoverRoutine (minDegVert minDegVert_mem card_nbrsIn_minDegVert)
open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)

/-! ## §1 The live-degree potential

The peel's cost is carried by one number: the total degree of the live
set. It falls by exactly twice the peeled vertex's current degree, and
it starts at the slot count. -/

/-- **The live-degree potential**: the total degree of `F` inside `S`,
i.e. twice the number of edges of `F` with both ends in `S`. -/
noncomputable def livePot {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N)) : ℕ :=
  ∑ u ∈ S, (nbrsIn F S u).card

/-- Erasing `v` from the live set erases it from every live
neighbourhood. -/
theorem nbrsIn_erase {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v u : Fin N) : nbrsIn F (S.erase v) u = (nbrsIn F S u).erase v := by
  classical
  ext z
  simp only [mem_nbrsIn, Finset.mem_erase]
  tauto

/-- **A live degree loses one exactly at the neighbours of the peeled
vertex.** The indicator is written as membership in `v`'s own live
neighbourhood — the same `Finset`, read from the other side — so that
it is decidable without a classical instance and so that summing it
over the survivors is `v`'s live degree (`sum_mem_indicator`). -/
theorem card_nbrsIn_erase {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    {v u : Fin N} (hv : v ∈ S) (hu : u ∈ S) :
    (nbrsIn F S u).card
      = (nbrsIn F (S.erase v) u).card + (if u ∈ nbrsIn F S v then 1 else 0) := by
  classical
  rw [nbrsIn_erase]
  by_cases h : u ∈ nbrsIn F S v
  · have hadj : F.Adj u v := (mem_nbrsIn.mp h).2
    have hmem : v ∈ nbrsIn F S u := mem_nbrsIn.mpr ⟨hv, hadj.symm⟩
    have hpos : 0 < (nbrsIn F S u).card := Finset.card_pos.mpr ⟨v, hmem⟩
    rw [Finset.card_erase_of_mem hmem, if_pos h]
    omega
  · have hmem : v ∉ nbrsIn F S u := by
      intro hc
      exact h (mem_nbrsIn.mpr ⟨hu, (mem_nbrsIn.mp hc).2.symm⟩)
    rw [Finset.erase_eq_of_notMem hmem, if_neg h]
    omega

/-- A live neighbourhood of `v` avoids `v`. -/
theorem nbrsIn_subset_erase {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v : Fin N) : nbrsIn F S v ⊆ S.erase v := by
  intro u hu
  obtain ⟨huS, hadj⟩ := mem_nbrsIn.mp hu
  refine Finset.mem_erase.mpr ⟨?_, huS⟩
  rintro rfl
  exact F.irrefl hadj

/-- The peeled vertex's own live degree, counted from the other side:
the number of surviving vertices that lose an edge. -/
theorem sum_mem_indicator {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (v : Fin N) :
    ∑ u ∈ S.erase v, (if u ∈ nbrsIn F S v then 1 else 0) = (nbrsIn F S v).card := by
  classical
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (nbrsIn_subset_erase F S v),
    Finset.sum_const, smul_eq_mul, mul_one]

/-- **The amortization, in one line.** Peeling `v` drops the live-degree
potential by exactly twice `v`'s *current* degree — `v`'s own row and
the one cell each surviving neighbour loses. A round charged `b·d` in
the current degree is therefore paid for out of the potential's own
fall, with `b·d` to spare. -/
theorem livePot_erase {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    {v : Fin N} (hv : v ∈ S) :
    livePot F S = 2 * (nbrsIn F S v).card + livePot F (S.erase v) := by
  classical
  have h1 : livePot F S
      = (nbrsIn F S v).card + ∑ u ∈ S.erase v, (nbrsIn F S u).card :=
    (Finset.add_sum_erase S (fun u => (nbrsIn F S u).card) hv).symm
  have h2 : ∑ u ∈ S.erase v, (nbrsIn F S u).card
      = ∑ u ∈ S.erase v,
          ((nbrsIn F (S.erase v) u).card + (if u ∈ nbrsIn F S v then 1 else 0)) :=
    Finset.sum_congr rfl fun u hu =>
      card_nbrsIn_erase F S hv (Finset.mem_of_mem_erase hu)
  rw [h1, h2, Finset.sum_add_distrib, sum_mem_indicator F S v]
  show (nbrsIn F S v).card + (livePot F (S.erase v) + (nbrsIn F S v).card)
    = 2 * (nbrsIn F S v).card + livePot F (S.erase v)
  omega

/-! ## §2 The slot count -/

/-- **The slot count** of a graph: the width of the adjacency region
`DelAdjSt` lays out for it — one cell per ordered adjacent pair, i.e.
twice the edge count. This is the `m` of `O(N + m)`. -/
noncomputable def slotCount {N : ℕ} (F : SimpleGraph (Fin N)) : ℕ :=
  ∑ v : Fin N, (F.neighborSet v).ncard

/-- On the full carrier the live degree is the degree. -/
theorem card_nbrsIn_univ {N : ℕ} (F : SimpleGraph (Fin N)) (v : Fin N) :
    (nbrsIn F Finset.univ v).card = (F.neighborSet v).ncard := by
  classical
  have hset : (↑(nbrsIn F Finset.univ v) : Set (Fin N)) = F.neighborSet v := by
    ext z
    simp only [Finset.mem_coe, mem_nbrsIn, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborSet]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [← Set.ncard_coe_finset, hset]

/-- The potential starts at the slot count. -/
theorem livePot_univ {N : ℕ} (F : SimpleGraph (Fin N)) :
    livePot F Finset.univ = slotCount F :=
  Finset.sum_congr rfl fun v _ => card_nbrsIn_univ F v

/-- **The region's own width is the slot count.** `AdjFrame`'s two
offset clauses — `offF 0 = 0` and one row per vertex — say exactly that
`offF N` is `∑ v, deg v`. So a budget stated in `slotCount` is a budget
stated in the region's allocation, with no further hypothesis. -/
theorem offF_eq_slotCount {N : ℕ} {G : SimpleGraph (Fin N)} {offF : ℕ → ℕ}
    (h0 : offF 0 = 0)
    (hstep : ∀ v : Fin N, offF ((v : ℕ) + 1) = offF (v : ℕ) + (G.neighborSet v).ncard) :
    offF N = slotCount G := by
  classical
  have key : ∀ i, i ≤ N → offF i =
      ∑ j ∈ Finset.range i, (if h : j < N then (G.neighborSet ⟨j, h⟩).ncard else 0) := by
    intro i
    induction i with
    | zero => intro _; simpa using h0
    | succ k ih =>
        intro hk
        have hkN : k < N := hk
        have hs := hstep ⟨k, hkN⟩
        simp only at hs
        rw [Finset.sum_range_succ, ← ih (by omega), hs, dif_pos hkN]
  have hslot : slotCount G =
      ∑ j ∈ Finset.range N, (if h : j < N then (G.neighborSet ⟨j, h⟩).ncard else 0) := by
    rw [slotCount,
      ← Fin.sum_univ_eq_sum_range
        (fun j => if h : j < N then (G.neighborSet ⟨j, h⟩).ncard else 0) N]
    exact Finset.sum_congr rfl fun v _ => by simp
  rw [key N le_rfl, hslot]

/-- **The potential is the machine's degree array.** At a peel state —
the region at the isolation of the complement of the live set `S` — the
sum of `dg` over the whole carrier is exactly `livePot F S`: live
vertices contribute their live degree (`ncard_neighborSet_deleteVerts_compl`)
and peeled ones contribute `0` (`ncard_neighborSet_deleteVerts_eq_zero`).
So a program can read its own potential off the region. -/
theorem sum_dg_eq_livePot {aj dg mt : String} {N : ℕ} {offF : ℕ → ℕ}
    {F : SimpleGraph (Fin N)} {S : Finset (Fin N)} {σ : Env}
    (h : AdjCore aj dg mt offF (deleteVerts F ((↑S : Set (Fin N))ᶜ)) σ) :
    ∑ u : Fin N, (σ.arrs dg).getD (u : ℕ) 0 = livePot F S := by
  classical
  have hval : ∀ u : Fin N, u ∈ S → (σ.arrs dg).getD (u : ℕ) 0 = (nbrsIn F S u).card := by
    intro u hu
    rw [h.1 u, ncard_neighborSet_deleteVerts_compl F S hu]
  have hzero : ∀ u : Fin N, u ∈ (Finset.univ : Finset (Fin N)) → u ∉ S →
      (σ.arrs dg).getD (u : ℕ) 0 = 0 := by
    intro u _ hu
    rw [h.1 u, ncard_neighborSet_deleteVerts_eq_zero (by simpa using hu)]
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero, livePot]
  exact Finset.sum_congr rfl fun u hu => hval u hu

/-! ## §3 A peel loop at a linear budget

Two `Spec` rules over an arbitrary round body. Neither says anything
about how the round finds its vertex; both say what the loop costs once
it does. The potential is `Spec.while_potential`'s, and the whole
content is §1's `livePot_erase`. -/

/-- **The peel loop at `a·N + b·m`.** A loop whose every turn peels one
vertex `v` out of the live set at a cost affine in `v`'s *current*
degree runs inside `a·N + b·(slot count) + O(1)` — no `N²` anywhere,
however large the individual rounds are.

`Sof` is the live set as a function of the state; the caller supplies
it together with the invariant that pins it (wave 23's `PeelInv` pins
it by the sentinel pattern in the rank region). -/
theorem peelLoop_linear {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (Sof : Env → Finset (Fin N)) (a b : ℕ)
    (hdef : ∀ σ, I σ → ∃ v, bc.evalB B σ = some v)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ), v ∈ Sof σ ∧ Run B body σ σ' K ∧ I σ' ∧
        Sof σ' = (Sof σ).erase v ∧
        1 + bc.size + K ≤ a + b * (nbrsIn F (Sof σ) v).card) :
    Spec B (fun σ => I σ ∧ Sof σ = Finset.univ) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      (a * N + b * slotCount F + 1 + bc.size) := by
  classical
  refine Spec.while_potential I
    (fun σ => a * (Sof σ).card + b * livePot F (Sof σ)) hdef ?_ (fun _ h => h.1) ?_
  · intro σ hI hv
    obtain ⟨v, σ', K, hvS, hrun, hI', hSof, hcost⟩ := hstep σ hI hv
    refine ⟨σ', K, hrun, hI', ?_⟩
    show 1 + bc.size + K + (a * (Sof σ').card + b * livePot F (Sof σ'))
      ≤ a * (Sof σ).card + b * livePot F (Sof σ)
    obtain ⟨c, hc⟩ : ∃ c, (Sof σ).card = c + 1 := by
      have := Finset.card_pos.mpr (⟨v, hvS⟩ : (Sof σ).Nonempty)
      exact ⟨(Sof σ).card - 1, by omega⟩
    have hcard : (Sof σ').card = c := by
      rw [hSof, Finset.card_erase_of_mem hvS, hc]
      omega
    have hpot : livePot F (Sof σ)
        = 2 * (nbrsIn F (Sof σ) v).card + livePot F (Sof σ') := by
      rw [hSof]; exact livePot_erase F (Sof σ) hvS
    have hdist : b * livePot F (Sof σ)
        = 2 * (b * (nbrsIn F (Sof σ) v).card) + b * livePot F (Sof σ') := by
      rw [hpot]; ring
    have hac : a * (c + 1) = a * c + a := by ring
    rw [hcard, hc, hdist, hac]
    omega
  · rintro σ ⟨-, huniv⟩
    show a * (Sof σ).card + b * livePot F (Sof σ) + 1 + bc.size
      ≤ a * N + b * slotCount F + 1 + bc.size
    have hcard : (Sof σ).card = N := by
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    have hpot : livePot F (Sof σ) = slotCount F := by rw [huniv, livePot_univ]
    rw [hcard, hpot]

/-- **The peel loop with a cursor.** The bucket-queue refinement of
`peelLoop_linear`: the round may in addition pay `e` per step of a
cursor `cur` that it drives upward, provided the cursor falls by at
most one per round. The cursor's total rise is then `≤ 2N`, and it is
charged in the potential's `e·(N - cur)` term — which is where the
"rising cursor never revisits a bucket more than the total degree
allows" of the standard algorithm actually lives.

`minDeg_le_minDeg_erase_succ` below is the abstract fact that licenses
the `cur σ ≤ cur σ' + 1` hypothesis for a cursor tracking the live
minimum degree. -/
theorem peelLoop_linear_cursor {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (Sof : Env → Finset (Fin N))
    (cur : Env → ℕ) (a b e : ℕ)
    (hcurN : ∀ σ, I σ → cur σ ≤ N)
    (hdef : ∀ σ, I σ → ∃ v, bc.evalB B σ = some v)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ), v ∈ Sof σ ∧ Run B body σ σ' K ∧ I σ' ∧
        Sof σ' = (Sof σ).erase v ∧ cur σ ≤ cur σ' + 1 ∧
        1 + bc.size + K ≤ a + b * (nbrsIn F (Sof σ) v).card
          + e * (cur σ' + 1 - cur σ)) :
    Spec B (fun σ => I σ ∧ Sof σ = Finset.univ) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      ((a + e) * N + b * slotCount F + e * N + 1 + bc.size) := by
  classical
  refine Spec.while_potential I
    (fun σ => (a + e) * (Sof σ).card + b * livePot F (Sof σ) + e * (N - cur σ))
    hdef ?_ (fun _ h => h.1) ?_
  · intro σ hI hv
    obtain ⟨v, σ', K, hvS, hrun, hI', hSof, hcurdrop, hcost⟩ := hstep σ hI hv
    refine ⟨σ', K, hrun, hI', ?_⟩
    show 1 + bc.size + K
        + ((a + e) * (Sof σ').card + b * livePot F (Sof σ') + e * (N - cur σ'))
      ≤ (a + e) * (Sof σ).card + b * livePot F (Sof σ) + e * (N - cur σ)
    obtain ⟨c, hc⟩ : ∃ c, (Sof σ).card = c + 1 := by
      have := Finset.card_pos.mpr (⟨v, hvS⟩ : (Sof σ).Nonempty)
      exact ⟨(Sof σ).card - 1, by omega⟩
    have hcard : (Sof σ').card = c := by
      rw [hSof, Finset.card_erase_of_mem hvS, hc]
      omega
    have hpot : livePot F (Sof σ)
        = 2 * (nbrsIn F (Sof σ) v).card + livePot F (Sof σ') := by
      rw [hSof]; exact livePot_erase F (Sof σ) hvS
    have hdist : b * livePot F (Sof σ)
        = 2 * (b * (nbrsIn F (Sof σ) v).card) + b * livePot F (Sof σ') := by
      rw [hpot]; ring
    have hac : (a + e) * (c + 1) = (a + e) * c + (a + e) := by ring
    -- the cursor's own inequality: a fall of one costs `e`, a rise pays for itself
    have hkey : e * (cur σ' + 1 - cur σ) + e * (N - cur σ')
        ≤ e + e * (N - cur σ) := by
      have hx := hcurN σ hI
      have hy := hcurN σ' hI'
      have h1 : (cur σ' + 1 - cur σ) + (N - cur σ') ≤ 1 + (N - cur σ) := by omega
      calc e * (cur σ' + 1 - cur σ) + e * (N - cur σ')
          = e * ((cur σ' + 1 - cur σ) + (N - cur σ')) := by ring
        _ ≤ e * (1 + (N - cur σ)) := Nat.mul_le_mul_left e h1
        _ = e + e * (N - cur σ) := by ring
    rw [hcard, hc, hdist, hac]
    omega
  · rintro σ ⟨hI, huniv⟩
    show (a + e) * (Sof σ).card + b * livePot F (Sof σ) + e * (N - cur σ) + 1 + bc.size
      ≤ (a + e) * N + b * slotCount F + e * N + 1 + bc.size
    have hcard : (Sof σ).card = N := by
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    have hcur : e * (N - cur σ) ≤ e * N := Nat.mul_le_mul_left e (Nat.sub_le _ _)
    have hpot : livePot F (Sof σ) = slotCount F := by rw [huniv, livePot_univ]
    rw [hcard, hpot]
    omega

/-! ## §4 What the selection owes, and what it costs

The two clauses a round must meet, isolated. `eq_minDegVert_of_bucket`
is the bucket-queue shape of wave 23's `eq_minDegVert`: it is the
proof obligation an `O(1)` pop would have to discharge, and — see the
module docstring — the reason no constant-time pop does.
`minDeg_le_minDeg_erase_succ` is the cursor's own licence. -/

/-- **The live minimum degree** — the bucket the cursor stands at. -/
noncomputable def minDeg {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) : ℕ := S.inf' hS fun v => (nbrsIn F S v).card

theorem minDeg_le {N : ℕ} (F : SimpleGraph (Fin N)) {S : Finset (Fin N)}
    (hS : S.Nonempty) {u : Fin N} (hu : u ∈ S) :
    minDeg F S hS ≤ (nbrsIn F S u).card := Finset.inf'_le _ hu

theorem minDeg_minDegVert {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) : (nbrsIn F S (minDegVert F S hS)).card = minDeg F S hS :=
  card_nbrsIn_minDegVert F S hS

/-- **The cursor falls by at most one per round.** Peeling any vertex
out of `S` lowers every surviving live degree by at most one, so the
live minimum degree of `S.erase v` is at least `minDeg F S hS - 1`.
This is what bounds a bucket cursor's total *rise* by `2N` — without
it a cursor reset to `0` each round is an `O(N)` round and the peel is
quadratic again. -/
theorem minDeg_le_minDeg_erase_succ {N : ℕ} (F : SimpleGraph (Fin N))
    {S : Finset (Fin N)} (hS : S.Nonempty) {v : Fin N} (hv : v ∈ S)
    (hS' : (S.erase v).Nonempty) :
    minDeg F S hS ≤ minDeg F (S.erase v) hS' + 1 := by
  classical
  obtain ⟨u, huE, hueq⟩ :=
    Finset.exists_mem_eq_inf' hS' fun w => (nbrsIn F (S.erase v) w).card
  have huS : u ∈ S := Finset.mem_of_mem_erase huE
  have hstep : (nbrsIn F S u).card
      = (nbrsIn F (S.erase v) u).card + (if u ∈ nbrsIn F S v then 1 else 0) :=
    card_nbrsIn_erase F S hv huS
  have hle : minDeg F S hS ≤ (nbrsIn F S u).card := minDeg_le F hS huS
  have hind : (if u ∈ nbrsIn F S v then 1 else 0) ≤ 1 := by
    split <;> omega
  have heq : minDeg F (S.erase v) hS' = (nbrsIn F (S.erase v) u).card := hueq
  omega

/-- **What an `O(1)` bucket pop would owe.** A live vertex sitting in
the cursor's bucket `c`, with every live vertex of degree at least `c`
and every live vertex of degree exactly `c` of no smaller index, *is*
`minDegVert` — the pinned `Finset.min'`. The third hypothesis is the
one a bucket queue does not get for free: it is the least *index* of
the bucket, not an arbitrary member of it. -/
theorem eq_minDegVert_of_bucket {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (hS : S.Nonempty) {c : ℕ} {v : Fin N} (hvS : v ∈ S)
    (hvc : (nbrsIn F S v).card = c)
    (hlow : ∀ u ∈ S, c ≤ (nbrsIn F S u).card)
    (hidx : ∀ u ∈ S, (nbrsIn F S u).card = c → (v : ℕ) ≤ (u : ℕ)) :
    v = minDegVert F S hS := by
  refine eq_minDegVert F S hS hvS ?_
  intro x hx
  rcases Nat.lt_or_ge (nbrsIn F S v).card (nbrsIn F S x).card with h | h
  · exact Or.inl h
  · have hxc : (nbrsIn F S x).card = c := le_antisymm (by omega) (hlow x hx)
    exact Or.inr ⟨by omega, hidx x hx hxc⟩

end Lax3Proofs.Prog

/-! ## §5 The tie-break is free upstream

Route 1 of the module docstring, discharged. `minDegVert`'s `min'` is
one *attaining* selection among many; this section reruns
`SolveSweepOrder`'s §1–§2 at an arbitrary one and lands the same
six-clause `AugChainData`, with no hypothesis on the carrier or the
graph. So re-pinning the peel's choice to something a machine can
produce in `O(1)` per round costs the ordering routine **nothing** —
which is what makes the linear peel a change to the *selection*, not
to the mathematics around it.

`selOrderingRoutine_mdSel` closes the loop: at the pinned choice the
generalised routine is the landed `mdOrderingRoutine`, on the nose. -/

namespace Lax3Proofs.CoverRoutine

open scoped SimpleGraph
open Lax12.GraphClasses
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.CoverDegree

variable {n : ℕ}

/-- **A selection rule for the greedy peel**: for every graph and every
nonempty live set, a vertex of the set attaining the minimum inside
degree. `minDegVert` is one (`mdSel`); so is the pop of any bucket
queue whose bucket order is itself a function of the graph. Nothing
below asks for more than these two clauses. -/
structure MinDegSel (n : ℕ) where
  /-- The chosen vertex. -/
  pick : (F : SimpleGraph (Fin n)) → (S : Finset (Fin n)) → S.Nonempty → Fin n
  /-- It is live. -/
  mem : ∀ F S hS, pick F S hS ∈ S
  /-- It attains the minimum live degree. -/
  attains : ∀ F S hS,
    (nbrsIn F S (pick F S hS)).card = S.inf' hS fun v => (nbrsIn F S v).card

/-- **The landed pinned choice, as a selection rule.** -/
noncomputable def mdSel (n : ℕ) : MinDegSel n where
  pick := fun F S hS => minDegVert F S hS
  mem := fun F S hS => minDegVert_mem F S hS
  attains := fun F S hS => card_nbrsIn_minDegVert F S hS

/-- An attaining choice is beaten up by every low-degree witness — the
only consequence of `attains` the peel invariants use. -/
theorem MinDegSel.card_le (sel : MinDegSel n) {F : SimpleGraph (Fin n)} {k : ℕ}
    (hk : LowDegreeVertices F k) (S : Finset (Fin n)) (hS : S.Nonempty) :
    (nbrsIn F S (sel.pick F S hS)).card ≤ k := by
  classical
  obtain ⟨u, huS, hu⟩ := hk S hS
  calc (nbrsIn F S (sel.pick F S hS)).card
      = S.inf' hS (fun v => (nbrsIn F S v).card) := sel.attains F S hS
    _ ≤ (nbrsIn F S u).card := Finset.inf'_le _ huS
    _ ≤ k := hu

/-- `mdRankAux` at an arbitrary attaining selection. -/
noncomputable def selRankAux (sel : MinDegSel n) (F : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Fin n → ℕ :=
  if hS : S.Nonempty then
    fun x =>
      if x = sel.pick F S hS then S.card - 1
      else selRankAux sel F (S.erase (sel.pick F S hS)) x
  else fun _ => 0
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem (sel.mem F S hS)

theorem selRankAux_of_nonempty (sel : MinDegSel n) (F : SimpleGraph (Fin n))
    {S : Finset (Fin n)} (hS : S.Nonempty) (x : Fin n) :
    selRankAux sel F S x =
      if x = sel.pick F S hS then S.card - 1
      else selRankAux sel F (S.erase (sel.pick F S hS)) x := by
  rw [selRankAux, dif_pos hS]

theorem selRankAux_of_empty (sel : MinDegSel n) (F : SimpleGraph (Fin n))
    (x : Fin n) : selRankAux sel F ∅ x = 0 := by
  rw [selRankAux, dif_neg (by simp)]

/-- **The three peel invariants at an arbitrary attaining selection** —
`mdRankAux_props` rerun with the tie-break freed. Only `MinDegSel.card_le`
is used of the choice, so the `min'` in `minDegVert` plays no part. -/
theorem selRankAux_props (sel : MinDegSel n) (F : SimpleGraph (Fin n)) {k : ℕ}
    (hk : LowDegreeVertices F k) :
    ∀ (m : ℕ) (S : Finset (Fin n)), S.card ≤ m →
      Set.InjOn (selRankAux sel F S) ↑S ∧
      (∀ v ∈ S, selRankAux sel F S v < S.card) ∧
      (∀ v ∈ S, ((nbrsIn F S v).filter
        (fun u => selRankAux sel F S u < selRankAux sel F S v)).card ≤ k) := by
  classical
  intro m
  induction m with
  | zero =>
      intro S hScard
      have : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hScard)
      subst this
      exact ⟨by simp, by simp, by simp⟩
  | succ m ih =>
      intro S hScard
      rcases S.eq_empty_or_nonempty with rfl | hS
      · exact ⟨by simp, by simp, by simp⟩
      have hv₀S : sel.pick F S hS ∈ S := sel.mem F S hS
      set v₀ := sel.pick F S hS with hv₀
      have hv₀deg : (nbrsIn F S v₀).card ≤ k := sel.card_le hk S hS
      have hcard : (S.erase v₀).card = S.card - 1 := Finset.card_erase_of_mem hv₀S
      have hcpos : 0 < S.card := Finset.card_pos.2 hS
      have heq : ∀ x, selRankAux sel F S x =
          if x = v₀ then S.card - 1 else selRankAux sel F (S.erase v₀) x :=
        fun x => selRankAux_of_nonempty sel F hS x
      obtain ⟨hinj', hlt', hdeg'⟩ := ih (S.erase v₀) (by omega)
      refine ⟨?_, ?_, ?_⟩
      · intro x hx y hy hxy
        rw [heq x, heq y] at hxy
        by_cases hx0 : x = v₀ <;> by_cases hy0 : y = v₀
        · rw [hx0, hy0]
        · exfalso
          have hyl := hlt' y (Finset.mem_erase.2 ⟨hy0, hy⟩)
          rw [if_pos hx0, if_neg hy0] at hxy
          rw [hcard] at hyl
          omega
        · exfalso
          have hxl := hlt' x (Finset.mem_erase.2 ⟨hx0, hx⟩)
          rw [if_neg hx0, if_pos hy0] at hxy
          rw [hcard] at hxl
          omega
        · rw [if_neg hx0, if_neg hy0] at hxy
          exact hinj' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hx0, hx⟩))
            (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hy0, hy⟩)) hxy
      · intro v hv
        rw [heq v]
        by_cases hv0 : v = v₀
        · rw [if_pos hv0]; omega
        · rw [if_neg hv0]
          have hvl := hlt' v (Finset.mem_erase.2 ⟨hv0, hv⟩)
          rw [hcard] at hvl
          omega
      · intro v hv
        by_cases hv0 : v = v₀
        · subst hv0
          exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hv₀deg
        · have hvE : v ∈ S.erase v₀ := Finset.mem_erase.2 ⟨hv0, hv⟩
          have hvlt := hlt' v hvE
          refine le_trans (Finset.card_le_card ?_) (hdeg' v hvE)
          intro u hu
          obtain ⟨huN, hulr⟩ := Finset.mem_filter.1 hu
          obtain ⟨huS, huadj⟩ := mem_nbrsIn.1 huN
          rw [heq u, heq v, if_neg hv0] at hulr
          have hu0 : u ≠ v₀ := by
            intro hc
            rw [if_pos hc] at hulr
            rw [hcard] at hvlt
            omega
          rw [if_neg hu0] at hulr
          exact Finset.mem_filter.2
            ⟨mem_nbrsIn.2 ⟨Finset.mem_erase.2 ⟨hu0, huS⟩, huadj⟩, hulr⟩

/-- The greedy elimination ranking at an arbitrary attaining selection. -/
noncomputable def selRank (sel : MinDegSel n) (F : SimpleGraph (Fin n)) : Fin n → ℕ :=
  selRankAux sel F Finset.univ

theorem selRank_injective (sel : MinDegSel n) (F : SimpleGraph (Fin n)) :
    Function.Injective (selRank sel F) := by
  have h := (selRankAux_props sel F (lowDegreeVertices_card F) n Finset.univ (by simp)).1
  intro x y hxy
  exact h (by simp) (by simp) hxy

theorem selRank_lt (sel : MinDegSel n) (F : SimpleGraph (Fin n)) (v : Fin n) :
    selRank sel F v < n := by
  have h := (selRankAux_props sel F (lowDegreeVertices_card F) n Finset.univ (by simp)).2.1
  simpa using h v (Finset.mem_univ v)

/-- **Every attaining selection attains every valid bound** — the
sInf-minimality clause, at the freed tie-break. -/
theorem selRank_backDegLE (sel : MinDegSel n) {F : SimpleGraph (Fin n)} {k : ℕ}
    (hk : LowDegreeVertices F k) : BackDegLE F (selRank sel F) k := by
  classical
  have h := (selRankAux_props sel F hk n Finset.univ (by simp)).2.2
  intro v
  refine le_trans (le_of_eq ?_) (h v (Finset.mem_univ v))
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_nbrsIn, Finset.mem_univ, true_and]
  rfl

/-- The permutation, direct as at the pinned choice. -/
noncomputable def selPerm (sel : MinDegSel n) (F : SimpleGraph (Fin n)) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun v => (⟨selRank sel F v, selRank_lt sel F v⟩ : Fin n))
    (Finite.injective_iff_bijective.mp fun _u _v h =>
      selRank_injective sel F (congrArg Fin.val h))

@[simp] theorem selPerm_val (sel : MinDegSel n) (F : SimpleGraph (Fin n)) (v : Fin n) :
    ((selPerm sel F v : Fin n) : ℕ) = selRank sel F v := rfl

theorem selPerm_backDegLE (sel : MinDegSel n) (F : SimpleGraph (Fin n)) :
    BackDegLE F (fun v => ((selPerm sel F v : Fin n) : ℕ)) (elimBound F) :=
  selRank_backDegLE sel (lowDegreeVertices_elimBound F)

theorem inDegLE_baseOr_selPerm (sel : MinDegSel n) (G : SimpleGraph (Fin n)) :
    (baseOr G (selPerm sel G)).InDegLE (elimBound G) := by
  intro v
  refine le_trans (le_of_eq ?_) (selPerm_backDegLE sel G v)
  rw [← Set.ncard_coe_finset]
  congr 1
  ext u
  simp only [Finset.mem_coe, mem_baseOr, Set.mem_setOf_eq, Fin.lt_def]

theorem greedyFratRound_greedyStep_sel (sel : MinDegSel n) {D : Orientation n} :
    GreedyFratRound D (greedyStep (selRank sel (fratGraph D)) D) := by
  intro k hk
  refine ⟨selRank sel (fratGraph D), selRank_backDegLE sel hk, ?_⟩
  intro _u _v hu hold _htr hadj
  rcases mem_greedyStep.1 hu with h | ⟨-, -, hc⟩
  · exact absurd h hold
  · rcases hc with hlt | hno
    · exact hlt
    · exact absurd (Or.inr (fratGraph_adj.1 hadj).2.symm) hno

/-- The deterministic chain at an arbitrary attaining selection. -/
noncomputable def selChain (sel : MinDegSel n) (G : SimpleGraph (Fin n)) :
    ℕ → Orientation n
  | 0 => baseOr G (selPerm sel G)
  | i + 1 => greedyStep (selRank sel (fratGraph (selChain sel G i))) (selChain sel G i)

theorem isAugChain_selChain (sel : MinDegSel n) (G : SimpleGraph (Fin n)) (R : ℕ) :
    IsAugChain G (selChain sel G) R :=
  ⟨baseOr_orients G (selPerm sel G), fun i _ =>
    augStep_greedyStep (selRank_injective sel (fratGraph (selChain sel G i)))⟩

theorem greedyFratRound_selChain (sel : MinDegSel n) (G : SimpleGraph (Fin n)) (i : ℕ) :
    GreedyFratRound (selChain sel G i) (selChain sel G (i + 1)) :=
  greedyFratRound_greedyStep_sel sel

/-- **The ordering routine at an arbitrary attaining selection.** -/
noncomputable def selOrderingRoutine (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) :
    CoverSpec.OrderingRoutine :=
  fun m G =>
    { chain := selChain (sel m) G
      order := selPerm (sel m) (selChain (sel m) G R).toGraph
      inDeg := elimBound G
      backDeg := elimBound (selChain (sel m) G R).toGraph
      steps := 0 }

/-- **The tie-break is free.** The full six-clause `AugChainData`, on
every carrier and every graph, for *every* attaining selection — the
mirror of `mdOrderingRoutine_data` with the choice unpinned. A peel
that pops the minimum-degree bucket in whatever order its data
structure offers therefore still produces a valid ordering routine,
provided the order it offers is a function of the graph. -/
theorem selOrderingRoutine_data (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) :
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      AugChainData G ((selOrderingRoutine sel R) m G).chain
        ((selOrderingRoutine sel R) m G).order R
        ((selOrderingRoutine sel R) m G).inDeg
        ((selOrderingRoutine sel R) m G).backDeg :=
  fun m G =>
    ⟨isAugChain_selChain (sel m) G R,
     fun i _ => greedyFratRound_selChain (sel m) G i,
     inDegLE_baseOr_selPerm (sel m) G,
     fun _k' hk' => elimBound_le hk',
     selPerm_backDegLE (sel m) (selChain (sel m) G R).toGraph,
     fun _k' hk' => elimBound_le hk'⟩

theorem isCoverOrdering_selOrderingRoutine (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (R : ℕ) (δ f : ℝ)
    (htime : ∀ (n' : ℕ) (Gn : SimpleGraph (Fin n')), C n' Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ((selOrderingRoutine sel R) m G).steps ≤ f * (m : ℝ) ^ (1 + 2 * δ)) :
    CoverSpec.IsCoverOrdering C R δ f (selOrderingRoutine sel R) :=
  ⟨fun _n _Gn _hGn m G _hsub => selOrderingRoutine_data sel R m G, htime⟩

/-! ### Conservativity: at the pinned choice, nothing has changed -/

theorem selRankAux_mdSel (F : SimpleGraph (Fin n)) :
    ∀ (m : ℕ) (S : Finset (Fin n)), S.card ≤ m →
      selRankAux (mdSel n) F S = mdRankAux F S := by
  intro m
  induction m with
  | zero =>
      intro S hS
      have : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
      subst this
      funext x
      rw [selRankAux_of_empty, mdRankAux, dif_neg (by simp)]
  | succ m ih =>
      intro S hcard
      rcases S.eq_empty_or_nonempty with rfl | hS
      · funext x
        rw [selRankAux_of_empty, mdRankAux, dif_neg (by simp)]
      · have hmem : (mdSel n).pick F S hS = minDegVert F S hS := rfl
        have hlt : (S.erase (minDegVert F S hS)).card ≤ m := by
          have := Finset.card_erase_of_mem (minDegVert_mem F S hS)
          have hpos : 0 < S.card := Finset.card_pos.2 hS
          omega
        funext x
        rw [selRankAux_of_nonempty (mdSel n) F hS x, mdRankAux_of_nonempty F hS x,
          hmem, ih _ hlt]

theorem selRank_mdSel (F : SimpleGraph (Fin n)) :
    selRank (mdSel n) F = mdRank F :=
  selRankAux_mdSel F n Finset.univ (by simp)

theorem selPerm_mdSel (F : SimpleGraph (Fin n)) :
    selPerm (mdSel n) F = mdPerm F := by
  apply Equiv.ext
  intro v
  apply Fin.ext
  show selRank (mdSel n) F v = mdRank F v
  rw [selRank_mdSel]

theorem selChain_mdSel (G : SimpleGraph (Fin n)) :
    ∀ i, selChain (mdSel n) G i = mdChain G i := by
  intro i
  induction i with
  | zero => rw [selChain, mdChain, selPerm_mdSel]
  | succ i ih => rw [selChain, mdChain, ih, selRank_mdSel]

/-- **At the pinned choice the generalised routine is the landed one.**
So §5 loses nothing: `mdOrderingRoutine` is the instance
`selOrderingRoutine (fun m => mdSel m)`, and any other attaining
selection is available at exactly the same cost. -/
theorem selOrderingRoutine_mdSel (R : ℕ) :
    selOrderingRoutine (fun m => mdSel m) R = mdOrderingRoutine R := by
  funext m G
  have hchain : selChain (mdSel m) G = mdChain G := funext (selChain_mdSel G)
  rw [selOrderingRoutine, mdOrderingRoutine]
  simp only [hchain, selPerm_mdSel]

end Lax3Proofs.CoverRoutine
