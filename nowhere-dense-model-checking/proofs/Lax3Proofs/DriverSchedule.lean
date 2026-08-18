import Lax3Proofs.LocalityFun
import Mathlib.Logic.Equiv.Fin.Basic
import Lax3Proofs.ScatterFml
import Lax3Proofs.Isolate
import Lax3Proofs.Relativize

/-!
# The formula schedule of the abstract driver (E9, deliverable 1)

`algorithm-v2.md` §5 lines 0: the compile-time data of the algorithm —
the families `ℱ_0 … ℱ_ℓ` of one-variable local formulas, the
decompositions `dec_j`, and the top-level combination `top` — as
functions of the depth, depending only on `(φ, ε, C)`-derived data (D5).

## The construction

The input is a `Setup`: the sentence `φ` with its rank witness
`DRank 0 q φ`, a scatter choice, the round budget `depth` (§3's `ℓ`)
and the batch width `width` (§3's `m`). Everything below is a function
of that data alone; no graph is ever consulted.

* `top` is the chosen locality decomposition of `φ` itself
  (`LocalityFun.localityBC`), a boolean combination of local *sentences*
  — constants, by L1, evaluated by `localConst` — and scatter sentences
  over `ℱ_0`.
* `ℱ_0` (`F S 0`) is the list of `β`-formulas of `top`'s scatter atoms.
  Each is one-variable, local, and of distance rank `(1, q−1)`: a
  scatter atom of rank `(0, q)` has its `β` natively at `(i, q−i)`, and
  `ScatterFml.drank_succ_pred_of_drank` trades it to `(1, q−1)`
  (`drank_beta_root`).
* Below the root, each `β ∈ ℱ_j` is piped through the **fixed** rewrite
  `stepFml` — relativization to a marker color (`Relativize.rel`)
  followed by the isolation rewrite (`Isolate.iso`) at batch width
  `width` and profile cap `R` — and then decomposed by `localityBC`
  again. `dec S β` is that decomposition; `ℱ_{j+1}` collects, over all
  `β ∈ ℱ_j`, the local atoms of `dec S β` together with the `β`-formulas
  of its scatter atoms (`next`, `F S (j+1)`).

## The palette tower

`rel` adds one marker color and `iso` adds the two profile-slot families,
so the palette grows deterministically with the depth: `Setup.pal` is the
tower, `relPal`/`isoPal` the two steps. The slot layout of an `iso` step
is fixed by the equivalence `isoEnc` (old colors ⊕ batch-distance
profiles ⊕ color-distance profiles); `slotColoring` builds a coloring
from the three families so that the slot equations `sat_iso` consumes
hold definitionally (`slotColoring_old/_pd/_pu`).

## The rank invariant (L0)

Every member of every `F S j` is local and of distance rank `(1, q−1)`
(`rank_invariant` — carried by the subtype-like structure `Fml`, so it is
true by construction and the work is in the three trades):
`localityBC`'s local atoms keep the rank; a scatter atom's `β` is traded
back to `(1, q−1)` by `drank_succ_pred_of_drank` composed with
`SyntaxLemmas.DRank.antidiagonal` (`drank_beta_node`); and `rel`, `iso`
preserve rank exactly (`Relativize.drank_rel`, `Isolate.drank_iso`), so
`stepFml` does (`drank_stepFml`). The schedule never runs out: it is
defined at every depth `j`, not only up to `q` (the plan's L0 corrects
Rev 1 exactly here).

All radii stay below the cap `R = ρ⁻(0, q)`: `rhoMinus_one_le_R` and
`rhoPlus_two_le_R` bound the two horizons of rank `(1, q−1)` by `R`, and
`radiiLe_R_of_drank` packages them for `Isolate.sat_iso`. The `q = 0`
edge case is handled by emptiness: no scatter sentence has rank `(k, 0)`
(`one_le_q_of_mem_F`), so at `q = 0` every `F S j` is empty and no lemma
below ever needs `ρ⁺(2, q−2) ≤ R` there.

## L1: local sentences are constants

`localConst` evaluates a local sentence from its syntax alone —
zero-variable atoms are impossible (`Fin 0` is empty), a local quantifier
over an empty context has no vertex to be local to and is false — and
`sat_localConst` proves it agrees with `Sat` in every colored graph.
This is what lets the driver's top level treat `top`'s formula atoms as
compile-time constants.

Everything here is `noncomputable` through `Classical.choose` inside
`localityBC`; what the construction buys is a *function* of the setup,
not decidability (D5).
-/

namespace Lax3Proofs.Driver

open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax3Proofs.LocalityFun Lax3Proofs.ScatterFml Lax3Proofs.SyntaxLemmas

/-! ### The palette tower -/

/-- The palette after a relativization step: one marker color is
appended at the last slot. -/
def relPal (Λ : ℕ) : ℕ := Λ + 1

/-- The palette after an isolation step at batch width `mb` and profile
cap `cap`: the old colors, the batch-distance profile slots
(`mb · (cap+1)` of them) and the color-distance profile slots
(`Λ · (cap+1)`). -/
def isoPal (Λ mb cap : ℕ) : ℕ := Λ + (mb * (cap + 1) + Λ * (cap + 1))

/-- The slot layout of an isolation step: old colors, batch-distance
profiles, color-distance profiles. -/
def isoEnc (Λ mb cap : ℕ) :
    (Fin Λ ⊕ (Fin mb × Fin (cap + 1) ⊕ Fin Λ × Fin (cap + 1))) ≃ Fin (isoPal Λ mb cap) :=
  ((Equiv.refl (Fin Λ)).sumCongr (finProdFinEquiv.sumCongr finProdFinEquiv)).trans
    (((Equiv.refl (Fin Λ)).sumCongr finSumFinEquiv).trans finSumFinEquiv)

variable {Λ mb cap : ℕ}

/-- Where an old color lives in the isolation palette. -/
def isoOld (c : Fin Λ) : Fin (isoPal Λ mb cap) := isoEnc Λ mb cap (Sum.inl c)

/-- Where the batch-distance profile slot `(j, a)` lives: "within
distance `a` of the `j`-th batch vertex". -/
def isoPd (j : Fin mb) (a : Fin (cap + 1)) : Fin (isoPal Λ mb cap) :=
  isoEnc Λ mb cap (Sum.inr (Sum.inl (j, a)))

/-- Where the color-distance profile slot `(c, b)` lives: "within
distance `b` of the color class `c`". -/
def isoPu (c : Fin Λ) (b : Fin (cap + 1)) : Fin (isoPal Λ mb cap) :=
  isoEnc Λ mb cap (Sum.inr (Sum.inr (c, b)))

/-- A coloring of the isolation palette, from the three slot families. -/
def slotColoring {n : ℕ} (f : Fin Λ → Set (Fin n))
    (g : Fin mb → Fin (cap + 1) → Set (Fin n))
    (h : Fin Λ → Fin (cap + 1) → Set (Fin n)) : Coloring n (isoPal Λ mb cap) :=
  fun c' => match (isoEnc Λ mb cap).symm c' with
    | Sum.inl c => f c
    | Sum.inr (Sum.inl p) => g p.1 p.2
    | Sum.inr (Sum.inr p) => h p.1 p.2

@[simp] theorem slotColoring_old {n : ℕ} (f : Fin Λ → Set (Fin n))
    (g : Fin mb → Fin (cap + 1) → Set (Fin n))
    (h : Fin Λ → Fin (cap + 1) → Set (Fin n)) (c : Fin Λ) :
    slotColoring f g h (isoOld c) = f c := by
  simp [slotColoring, isoOld]

@[simp] theorem slotColoring_pd {n : ℕ} (f : Fin Λ → Set (Fin n))
    (g : Fin mb → Fin (cap + 1) → Set (Fin n))
    (h : Fin Λ → Fin (cap + 1) → Set (Fin n)) (j : Fin mb) (a : Fin (cap + 1)) :
    slotColoring f g h (isoPd j a) = g j a := by
  simp [slotColoring, isoPd]

@[simp] theorem slotColoring_pu {n : ℕ} (f : Fin Λ → Set (Fin n))
    (g : Fin mb → Fin (cap + 1) → Set (Fin n))
    (h : Fin Λ → Fin (cap + 1) → Set (Fin n)) (c : Fin Λ) (b : Fin (cap + 1)) :
    slotColoring f g h (isoPu c b) = h c b := by
  simp [slotColoring, isoPu]

/-- A coloring of the relativization palette: the old colors at their
old slots, the marker set at the appended last slot. -/
def relColoring {n : ℕ} (f : Fin Λ → Set (Fin n)) (mkSet : Set (Fin n)) :
    Coloring n (relPal Λ) :=
  Fin.lastCases mkSet f

@[simp] theorem relColoring_castSucc {n : ℕ} (f : Fin Λ → Set (Fin n))
    (mkSet : Set (Fin n)) (c : Fin Λ) :
    relColoring f mkSet c.castSucc = f c :=
  Fin.lastCases_castSucc ..

@[simp] theorem relColoring_last {n : ℕ} (f : Fin Λ → Set (Fin n))
    (mkSet : Set (Fin n)) :
    relColoring f mkSet (Fin.last Λ) = mkSet :=
  Fin.lastCases_last ..

/-! ### The setup -/

variable {L : ℕ}

/-- The compile-time data of the algorithm: the sentence with its rank
witness, the scatter choice, and §3's round budget `ℓ` (`depth`) and
batch width `m` (`width`). All schedule and driver constructions are
functions of a `Setup` alone (D5); how `depth` and `width` are obtained
from `(C, ε)` — `UqwInstantiation.exists_roundBudget` and
`m = ℓ·(2R+1)` — is the caller's business and enters only the
hypotheses of the invariant theorems. -/
structure Setup (L : ℕ) where
  /-- The quantifier-rank budget of the sentence. -/
  q : ℕ
  /-- The sentence being model-checked. -/
  φ : DistFO L 0
  /-- The rank witness: `φ` has distance rank `(0, q)`. -/
  hφ : DRank 0 q φ
  /-- The scatter choice fixing every scatter value (the algorithm runs
  the greedy choice; every statement holds for every choice). -/
  choice : ScatterChoice
  /-- §3's `ℓ`: the recursion depth / round budget. -/
  depth : ℕ
  /-- §3's `m`: the batch width the isolation palette is sized by. -/
  width : ℕ

/-- §3's radius cap `R = ρ⁻(0, q)`, which is also the profile cap of
every isolation step. The game radius is `2 * R`. -/
def Setup.R (S : Setup L) : ℕ := rhoMinus 0 S.q

/-- The palette at depth `j`: the input palette at the root, one
`rel`-then-`iso` step per level. -/
def Setup.pal (S : Setup L) : ℕ → ℕ
  | 0 => L
  | j + 1 => isoPal (relPal (S.pal j)) S.width S.R

@[simp] theorem Setup.pal_zero (S : Setup L) : S.pal 0 = L := rfl

theorem Setup.pal_succ (S : Setup L) (j : ℕ) :
    S.pal (j + 1) = isoPal (relPal (S.pal j)) S.width S.R := rfl

/-! ### The radius cap -/

theorem Setup.one_le_R (S : Setup L) : 1 ≤ S.R :=
  Nat.one_le_pow _ _ (by norm_num)

/-- ρ⁻ at rank `(1, q−1)` — the distance-atom horizon of every schedule
formula — stays below the cap `R = ρ⁻(0, q)`. -/
theorem Setup.rhoMinus_one_le_R (S : Setup L) : rhoMinus 1 (S.q - 1) ≤ S.R := by
  unfold Setup.R rhoMinus
  refine Nat.pow_le_pow_right (by norm_num) ?_
  generalize S.q = qq
  rcases qq with _ | s
  · simp
  · simp only [Nat.add_sub_cancel]
    exact Nat.mul_le_mul (by omega) (by omega)

/-- ρ⁺ at rank `(2, q−2)` — the guard horizon of every schedule
formula — stays below the cap, as soon as the schedule is nonempty
(`1 ≤ q`). -/
theorem Setup.rhoPlus_two_le_R (S : Setup L) (hq : 1 ≤ S.q) :
    rhoPlus 2 (S.q - 1 - 1) ≤ S.R := by
  unfold Setup.R rhoMinus rhoPlus
  refine Nat.pow_le_pow_right (by norm_num) ?_
  revert hq
  generalize S.q = qq
  intro hq
  rcases qq with _ | s
  · omega
  · rcases s with _ | t
    · norm_num
    · have h1 : t + 1 + 1 - 1 - 1 = t := by omega
      rw [h1]
      exact Nat.mul_le_mul (by omega) (by omega)

/-- The cap packaging `Isolate.sat_iso` needs: every radius of a
`(1, q−1)`-ranked formula is at most `R`. -/
theorem Setup.radiiLe_R_of_drank (S : Setup L) (hq : 1 ≤ S.q) {Λ' k : ℕ}
    {ψ : DistFO Λ' k} (h : DRank 1 (S.q - 1) ψ) :
    Lax3Proofs.Isolate.RadiiLe S.R ψ :=
  Lax3Proofs.Isolate.radiiLe_of_drank h S.rhoMinus_one_le_R (S.rhoPlus_two_le_R hq)

/-! ### The rank trades -/

/-- The `β`-formula of a scatter atom of the root decomposition — rank
`(0, q)` — has rank `(1, q−1)`. At `q = 0` no scatter sentence has the
rank at all. -/
theorem drank_beta_root {Λ' q : ℕ} {σ : ScatterSentence Λ'} (h : σ.DRank 0 q) :
    DRank 1 (q - 1) σ.β := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [scatterSentence_drank_iff] at h
    obtain ⟨-, i, h1, h2, -⟩ := h
    omega
  · exact drank_succ_pred_of_drank h hq

/-- **The rank trade below the root** (L0). The `β`-formula of a scatter
atom of rank `(1, p)` has rank `(1, p)` again: `drank_succ_pred_of_drank`
takes it to `(2, p−1)` and `DRank.antidiagonal` climbs back. At `p = 0`
no scatter sentence has the rank at all. -/
theorem drank_beta_node {Λ' p : ℕ} {σ : ScatterSentence Λ'} (h : σ.DRank 1 p) :
    DRank 1 p σ.β := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [scatterSentence_drank_iff] at h
    obtain ⟨-, i, h1, h2, -⟩ := h
    omega
  · have h2 : DRank 2 (p - 1) σ.β := drank_succ_pred_of_drank h hp
    have h3 := DRank.antidiagonal (k' := 1) h2
    rwa [Nat.sub_add_cancel hp] at h3

/-! ### The fixed per-level rewrite -/

/-- **The per-level rewrite, fixed once**: relativization to the marker
color appended at the last slot, then the isolation rewrite at batch
width `width` and profile cap `R`, with the slot layout of `isoEnc`.
This is the syntactic half of §5 lines 16–23; the driver's child arena
carries the matching colors. -/
def stepFml (S : Setup L) {Λ' : ℕ} (β : DistFO Λ' 1) :
    DistFO (isoPal (relPal Λ') S.width S.R) 1 :=
  Lax3Proofs.Isolate.iso isoOld isoPd isoPu
    (Lax3Proofs.Relativize.rel Fin.castSucc (Fin.last Λ') β)

/-- `rel` and `iso` preserve distance rank exactly, so the per-level
rewrite does. -/
theorem drank_stepFml (S : Setup L) {Λ' : ℕ} {β : DistFO Λ' 1}
    (h : DRank 1 (S.q - 1) β) : DRank 1 (S.q - 1) (stepFml S β) :=
  Lax3Proofs.Isolate.drank_iso (Lax3Proofs.Relativize.drank_rel _ _ h)

/-! ### The schedule -/

/-- A schedule formula at depth `j`: one-variable over the depth-`j`
palette, local, of distance rank `(1, q−1)`. The two `Prop` fields are
the rank invariant, carried by construction. -/
structure Fml (S : Setup L) (j : ℕ) where
  /-- The formula. -/
  fml : DistFO (S.pal j) 1
  /-- It is local. -/
  isLocal : IsLocal fml
  /-- It has distance rank `(1, q−1)`. -/
  drank : DRank 1 (S.q - 1) fml

/-- **The decomposition `dec_j`** (§5 line 0): the chosen locality
decomposition of the per-level rewrite of `β` — a boolean combination
of local one-variable formulas and scatter sentences over the next
palette, all of rank `(1, q−1)`. It depends on `j` only through the
palette. -/
noncomputable def dec (S : Setup L) {j : ℕ} (β : Fml S j) :
    BC (DistFO (S.pal (j + 1)) 1 ⊕ ScatterSentence (S.pal (j + 1))) :=
  localityBC S.choice (stepFml S β.fml) (drank_stepFml S β.drank)

/-- The schedule formulas one member contributes to the next level: the
local atoms of its decomposition, and the `β`-formulas of the
decomposition's scatter atoms, each with its rank invariant. -/
noncomputable def next (S : Setup L) {j : ℕ} (β : Fml S j) : List (Fml S (j + 1)) :=
  ((localAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).attach.map
      fun ψ => ⟨ψ.1,
        (localAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) ψ.1 ψ.2).1,
        (localAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) ψ.1 ψ.2).2⟩) ++
    ((scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)).attach.map
      fun σ => ⟨σ.1.β,
        isLocal_beta_of_drank
          (scatterAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) σ.1 σ.2),
        drank_beta_node
          (scatterAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) σ.1 σ.2)⟩)

/-- **The top-level decomposition** (§5 line 0): the chosen locality
decomposition of `φ` itself. Its formula atoms are local sentences —
constants, by L1 — and its scatter atoms range over `ℱ_0`. -/
noncomputable def top (S : Setup L) : BC (DistFO L 0 ⊕ ScatterSentence L) :=
  localityBC S.choice S.φ S.hφ

/-- **The schedule `ℱ_j`** (§5 line 0), as a function of the depth: at
the root, the `β`-formulas of `top`'s scatter atoms; below, everything
the previous level's decompositions mention. Defined at *every* depth —
the schedule never runs out (L0 against Rev 1). -/
noncomputable def F (S : Setup L) : (j : ℕ) → List (Fml S j)
  | 0 => (scatterAtoms S.choice S.φ S.hφ).attach.map
      fun σ => ⟨σ.1.β,
        isLocal_beta_of_drank (scatterAtoms_spec S.choice S.φ S.hφ σ.1 σ.2),
        drank_beta_root (scatterAtoms_spec S.choice S.φ S.hφ σ.1 σ.2)⟩
  | j + 1 => (F S j).flatMap (next S)

/-! ### The rank invariant, and membership -/

/-- **The rank invariant (L0), proved.** Every schedule formula at every
depth is local and of distance rank `(1, q−1)`. -/
theorem rank_invariant (S : Setup L) (j : ℕ) :
    ∀ γ ∈ F S j, IsLocal γ.fml ∧ DRank 1 (S.q - 1) γ.fml :=
  fun γ _ => ⟨γ.isLocal, γ.drank⟩

/-- The `β`-formula of a scatter atom of `top` is a root schedule
formula. -/
theorem exists_mem_F_zero_of_scatterAtom (S : Setup L) {σ : ScatterSentence L}
    (hσ : σ ∈ scatterAtoms S.choice S.φ S.hφ) :
    ∃ γ ∈ F S 0, γ.fml = σ.β := by
  refine ⟨⟨σ.β, isLocal_beta_of_drank (scatterAtoms_spec S.choice S.φ S.hφ σ hσ),
    drank_beta_root (scatterAtoms_spec S.choice S.φ S.hφ σ hσ)⟩, ?_, rfl⟩
  rw [F]
  exact List.mem_map.mpr ⟨⟨σ, hσ⟩, List.mem_attach _ _, rfl⟩

/-- A local atom of `dec S β` is a schedule formula one level down. -/
theorem exists_mem_F_succ_of_localAtom (S : Setup L) {j : ℕ} {β : Fml S j}
    (hβ : β ∈ F S j) {ψ : DistFO (S.pal (j + 1)) 1}
    (hψ : ψ ∈ localAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)) :
    ∃ γ ∈ F S (j + 1), γ.fml = ψ := by
  refine ⟨⟨ψ,
    (localAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) ψ hψ).1,
    (localAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) ψ hψ).2⟩, ?_, rfl⟩
  rw [F]
  exact List.mem_flatMap.mpr ⟨β, hβ, List.mem_append_left _
    (List.mem_map.mpr ⟨⟨ψ, hψ⟩, List.mem_attach _ _, rfl⟩)⟩

/-- The `β`-formula of a scatter atom of `dec S β` is a schedule formula
one level down. -/
theorem exists_mem_F_succ_of_scatterAtom (S : Setup L) {j : ℕ} {β : Fml S j}
    (hβ : β ∈ F S j) {σ : ScatterSentence (S.pal (j + 1))}
    (hσ : σ ∈ scatterAtoms S.choice (stepFml S β.fml) (drank_stepFml S β.drank)) :
    ∃ γ ∈ F S (j + 1), γ.fml = σ.β := by
  refine ⟨⟨σ.β,
    isLocal_beta_of_drank
      (scatterAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) σ hσ),
    drank_beta_node
      (scatterAtoms_spec S.choice (stepFml S β.fml) (drank_stepFml S β.drank) σ hσ)⟩, ?_, rfl⟩
  rw [F]
  exact List.mem_flatMap.mpr ⟨β, hβ, List.mem_append_right _
    (List.mem_map.mpr ⟨⟨σ, hσ⟩, List.mem_attach _ _, rfl⟩)⟩

/-- A nonempty schedule forces `1 ≤ q`: no scatter sentence has rank
`(k, 0)`, so at `q = 0` the root level is empty and emptiness
propagates. This is what lets every consumer of the guard-horizon bound
`rhoPlus_two_le_R` obtain its `1 ≤ q` from membership alone. -/
theorem one_le_q_of_mem_F (S : Setup L) :
    ∀ {j : ℕ} (γ : Fml S j), γ ∈ F S j → 1 ≤ S.q := by
  intro j
  induction j with
  | zero =>
    intro γ hγ
    rw [F] at hγ
    obtain ⟨σ, -, rfl⟩ := List.mem_map.mp hγ
    have h := scatterAtoms_spec S.choice S.φ S.hφ σ.1 σ.2
    rw [scatterSentence_drank_iff] at h
    obtain ⟨-, i, h1, h2, -⟩ := h
    omega
  | succ j ih =>
    intro γ hγ
    rw [F] at hγ
    obtain ⟨β, hβ, -⟩ := List.mem_flatMap.mp hγ
    exact ih β hβ

/-! ### L1: local sentences are constants -/

/-- **L1.** The truth value of a local sentence, read off its syntax:
with no variables in scope there are no atoms (`Fin 0` is empty), and a
local quantifier over the empty context ranges over the vertices within
`r` of nothing, hence is false. The `exU` clause is dead code — a local
formula has none — and is set to `False`. -/
def localConst {Λ' : ℕ} : DistFO Λ' 0 → Prop
  | .adj i _ => i.elim0
  | .eq i _ => i.elim0
  | .color _ i => i.elim0
  | .distLe _ i _ => i.elim0
  | .distColorLt _ _ i => i.elim0
  | .not ψ => ¬ localConst ψ
  | .and ψ χ => localConst ψ ∧ localConst χ
  | .exU _ => False
  | .exL _ _ _ => False

/-- **L1, proved against `Sat`.** A local sentence has the same truth
value in every colored graph, and that value is `localConst`. The only
recursive cases are `not` and `and`, which stay at arity zero; a guard
set over `Fin 0` can name no variable, so the `exL` case is false on
both sides. -/
theorem sat_localConst {Λ' n : ℕ} (G : SimpleGraph (Fin n)) (col : Coloring n Λ')
    (m : Fin 0 → Fin n) : ∀ {ψ : DistFO Λ' 0}, IsLocal ψ →
    (Sat G col m ψ ↔ localConst ψ)
  | .adj i _, _ => i.elim0
  | .eq i _, _ => i.elim0
  | .color _ i, _ => i.elim0
  | .distLe _ i _, _ => i.elim0
  | .distColorLt _ _ i, _ => i.elim0
  | .not ψ, h => by
    rw [sat_not, localConst]
    exact not_congr (sat_localConst G col m h)
  | .and ψ χ, h => by
    rw [sat_and, localConst]
    exact and_congr (sat_localConst G col m h.1) (sat_localConst G col m h.2)
  | .exU ψ, h => h.elim
  | .exL r g ψ, _ => by
    rw [sat_exL]
    simp only [localConst, iff_false, not_exists]
    rintro v ⟨⟨i, -, -⟩, -⟩
    exact i.elim0

end Lax3Proofs.Driver
