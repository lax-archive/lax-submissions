import Lax3Proofs.SolveSegRead

/-!
# F6c11a (part 2) — the readback pass: the row-atom bridge

`SolveSegRead` named **`ReadRows`** — the machine pass that runs the
per-atom scatters on the isolated child and writes the centre-`u` rows
of the level table at `RowEval`'s bits — and landed the compiled-row
evaluation `bcExprA_evalB_rowEval`: the row expression delivers
`RowEval`'s bit *given* that every atom's read expression delivers its
bit of the row assignment (`rowAsn`). This file discharges the **bridge
from the machine regions to those per-atom bits** — the `hav` premises,
at the addresses the machine actually reads:

* **`rowAsn_local_bit`**: the bit of a local atom `Sum.inl ψ` at a
  centre-`u` vertex `v` *is* the child's table cell at
  `(vc, i)` — `vc` the child name of `v`, `i` any position of `ψ` in
  `levelFml S (j+1)` (`localAtom_mem_levelFml` puts every local atom in
  the family) — verbatim a `getD` read off `BlockPost`'s `TableBitsW`
  region. The dependent rewrite to the child of `u` is
  `rowAsn_of_centre`.
* **`rowAsn_scatter_bit`**: the bit of a scatter atom `Sum.inr σa` *is*
  the guard bit of the guarded greedy count on the isolated child's
  graph over the atom's `β`-column — what `scatterCom_specW` leaves in
  the count cell — through `le_greedyScatter_iff`, under the choice
  seam `S.choice = greedyChoice` (`rfl` at the headline setup,
  `headlineSetup_choice`). The `Nat.decLe`-vs-classical instance gap is
  crossed by `if_congr`, per the campaign hazard.
* **`tableBitsW_column`**: the scatter atom's batch set
  `{z | unrollAux k (j+1) Bc z σa.β}` is readable column-wise off the
  same `TableBitsW` region (`scatterAtom_beta_mem_levelFml` places
  `σa.β` in the family) — the bits a per-atom column copy moves into
  the scatter stage's `FinBitsW` input.

With these, the `ReadRowsAll` discharger owes only programs and frames:
per schedule row and scatter atom, a column copy (`tableBitsW_column`
gives the copied bits) and one `scatterCom_specW` call (`FinBitsW` in,
count out — batches padded exactly, the `t = 0` guard a cost clause);
then the store loop over `{v | centre v = u}` (the centre array of
`CLInv`'s `CtrArr` identifies them) evaluating the compiled row, whose
value is pinned by `bcExprA_evalB_rowEval` + this file's two bit
bridges; the untouched clauses ride the stages' frame data.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The column read -/

open Classical in
/-- **A column of the windowed table region, read bit by bit**: at any
position `i` of the formula `β` in the family, cell `(z, i)` holds the
membership bit of `z` in `β`'s row set. This is the source of the
scatter stage's `FinBitsW` input: `scatterAtom_beta_mem_levelFml`
places every scatter atom's `β` in the child's family, and the column
copy moves exactly these bits. -/
theorem tableBitsW_column {a : String} {N Λ : ℕ} {Fl : List (DistFO Λ 1)}
    {T : Fin N → DistFO Λ 1 → Prop} {σ : Env} (hT : TableBitsW a Fl T σ)
    {i : ℕ} (hi : i < Fl.length) {β : DistFO Λ 1} (hiβ : Fl[i] = β)
    (z : Fin N) :
    (σ.arrs a).getD ((z : ℕ) * Fl.length + i) 0
      = if z ∈ {y : Fin N | T y β} then 1 else 0 := by
  subst hiβ
  rw [hT.2 z i hi]
  exact if_congr Iff.rfl rfl rfl

/-! ## §2 The two per-atom bits, at the machine's reads -/

open Classical in
/-- **The local atom's bit is a table read**: at a centre-`u` vertex
`v`, the row assignment's bit of a local atom `ψ` is exactly the
child-table cell at `v`'s child name and any position of `ψ` in the
level-`(j+1)` family — verbatim a `getD` read off `BlockPost`'s
`TableBitsW` region (`localAtom_mem_levelFml` supplies membership; a
position is compile-time data of the row's decomposition). -/
theorem rowAsn_local_bit (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {k j : ℕ} {A : Arena (S.pal j) n₀} {v u : Fin A.N}
    (hv : centre S A ((ord A.N A.G).order) v = u)
    {a : String} {σ : Env}
    (hT : TableBitsW a (levelFml S (j + 1))
      (Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order) u)) σ)
    {ψ : DistFO (S.pal (j + 1)) 1} {i : ℕ}
    (hi : i < (levelFml S (j + 1)).length)
    (hiψ : (levelFml S (j + 1))[i] = ψ) :
    (σ.arrs a).getD
        ((((childEquiv S A ((ord A.N A.G).order) u).symm
            ⟨v, hv ▸ mem_cluster_centre S A ((ord A.N A.G).order) v⟩ : Fin
              (childN S A ((ord A.N A.G).order) u)) : ℕ)
          * (levelFml S (j + 1)).length + i) 0
      = if rowAsn S ord k j A v (Sum.inl ψ) then 1 else 0 := by
  rw [rowAsn_of_centre hv]
  subst hiψ
  exact hT.2 _ i hi

open Classical in
/-- **The scatter atom's bit is the guarded count's guard bit**: at a
centre-`u` vertex `v`, the row assignment's bit of a scatter atom `σa`
is `1` iff the guarded greedy count on the **isolated** child graph
over `σa.β`'s row set reaches `σa.t` — exactly the value
`scatterCom_specW` leaves in the count cell, thresholded. The choice
seam `S.choice = greedyChoice` is `rfl` at the headline setup
(`headlineSetup_choice`); `le_greedyScatter_iff` closes the guard, and
`if_congr` crosses the decidability-instance gap. -/
theorem rowAsn_scatter_bit (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {k j : ℕ} {A : Arena (S.pal j) n₀} {v u : Fin A.N}
    (hv : centre S A ((ord A.N A.G).order) v = u)
    (hchoice : S.choice = greedyChoice)
    (σa : ScatterSentence (S.pal (j + 1))) :
    (if σa.t ≤ Impl.greedyScatter
        (childArena S A ((ord A.N A.G).order) u).G σa.r
        {z | Unroll.unrollAux S ord k (j + 1)
          (childArena S A ((ord A.N A.G).order) u) z σa.β} σa.t
      then 1 else 0)
      = if rowAsn S ord k j A v (Sum.inr σa) then 1 else 0 := by
  rw [rowAsn_of_centre hv]
  refine if_congr ?_ rfl rfl
  show σa.t ≤ Impl.greedyScatter
      (childArena S A ((ord A.N A.G).order) u).G σa.r
      {z | Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order) u) z σa.β} σa.t
    ↔ σa.t ≤ S.choice.size
      (childArena S A ((ord A.N A.G).order) u).G σa.r
      {z | Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order) u) z σa.β}
  rw [hchoice]
  exact Impl.le_greedyScatter_iff _ _ _ _

/-- **The choice seam, at the headline setup**: the campaign's scatter
choice is the guarded greedy one, definitionally — what F7 passes for
`rowAsn_scatter_bit`'s `hchoice`. -/
theorem headlineSetup_choice (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) :
    (Headline.headlineSetup C hC φ).choice = greedyChoice := rfl

end Lax3Proofs.Prog
