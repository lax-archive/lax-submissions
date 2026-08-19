import Lax3Proofs.SolveFrameBridge

/-!
# F6c8 (part 2) — the root load, discharged down to the CSR pass

`SolveFrameBridge.RootLoadSpec` — residual 3a of `solveSpec_closed` —
asks for the step from `MatIn` (the materialized root) to the level-0
`BlockPre` at the root arena. This file discharges everything about
that step except one named pass, and records a **scope finding**:

**The finding.** The chain's `GraphCsr` demands duplicate-free rows at
slot count `Σ_v deg v` (`GraphCsr.ns_eq_sum_degree` is what every
budget statement rides). But `Lax11.GraphEncoding.EncodesGraph` — the
endorsed axiom's input format, verbatim — *does not forbid repeated
neighbours within a block*, and `mcD` adds only the word-size side
condition. So the root load is **not** a plain CSR copy (the
`SolveChain` module docstring's sketch understates it): on an
adversarial admissible encoding the pass must *deduplicate* each block
while copying — a mark-array compaction, `O(n + m)`, real program
content. That pass is the one named residual here, **`RootCsrLoadAll`**:
from `MatIn`, produce in the level-0 CSR pair a valid prefix holding
the deduplicated graph (`CsrPrefix`) with the slot count in the level's
`nS` cell, touching nothing but the pair, the cell, and its declared
scratch.

Everything else of `RootLoadSpec` is proved here, unconditionally:

* **`rootGlueCom`** — the rest of the load as a concrete program: the
  carrier cell (`sv.n := n`) and the identity renaming written into the
  level-0 `up` region (the root's `up` is `Function.Embedding.refl` —
  one counted scan, `matCom`'s own shape). `rootGlueCom_spec` proves
  it, with its frame and length preservation.
* **`rootLoadSpec_of_csrLoad`** — the headline: `RootLoadSpec` holds of
  `csrCom ; rootGlueCom`, verbatim, from `RootCsrLoadAll` plus
  hypotheses only of the F7-suppliable kinds: the `ext` length
  conventions at the level-0 names, the empty root channel
  (`htabF 0 (rootArena …) = fun _ _ => []` — `rootArena.hist = []`),
  the degenerate root palette (`pal 0 = 0`, the axiom's uncoloured
  input), the word bound `n < mcB`, name-freshness of the pass's
  scratch, and the level-0 scratch descriptor from `MatIn`'s lengths
  (`Scr` is length-only). The color region is empty (`n·0` cells), the
  channel region is the all-zeros allocation (`MatIn`'s fresh arrays
  are *already* the empty-channel encoding), the table allocation
  survives untouched, and the windowed contract (`ArenaStW`) is
  assembled from the pass's prefix through the `winA` congruences.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §1 The deduplicated CSR prefix, and the named residual -/

/-- **A deduplicated CSR prefix**: the two named allocations hold, as
valid prefixes (`N + 1` offsets, `ns` slots), a duplicate-free CSR of
`G` — `GraphCsr` of the truncation at exactly those windows. This is
the windowed form the level-0 `ArenaStW` consumes; the allocations may
be longer (the target region is allocated at the raw `2m`, the
deduplicated slot count `ns ≤ 2m` is data). -/
def CsrPrefix (o t : String) {N : ℕ} (G : SimpleGraph (Fin N)) (ns : ℕ)
    (σ : Env) : Prop :=
  N + 1 ≤ (σ.arrs o).length ∧ ns ≤ (σ.arrs t).length ∧
    GraphCsr o t G ns
      (winA (fun b => if b = o then some (N + 1)
        else if b = t then some ns else none) σ)

/-- **The named residual: the deduplicating CSR pass**, per admissible
input. From `MatIn`, the pass leaves in the level-0 CSR pair a
deduplicated CSR prefix of `G` with its slot count in the level-0 `nS`
cell; it writes nothing else but its declared scratch (`da` an array,
`rlS` a scalar pool) and reallocates nothing. **This is not a plain
copy** (module docstring): `EncodesGraph` admits repeated neighbours
within a block, `GraphCsr` forbids them and pins `ns = Σ deg` — the
pass owes a mark-array deduplication, `O(n + m)`. -/
def RootCsrLoadAll {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ)
    (ext : List ℕ → String → ℕ) (da : String) (rlS : List String)
    (csrCom : Com) (Kcsr : List ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    Spec (mcB q x) (MatIn (ext x) x) csrCom
      (fun σ σ' =>
        CsrPrefix (arenaNames 0).off (arenaNames 0).tgt G
          (σ'.vars (arenaNames 0).nS) σ' ∧
        (∀ b, b ≠ (arenaNames 0).off → b ≠ (arenaNames 0).tgt → b ≠ da →
          σ'.arrs b = σ.arrs b) ∧
        (∀ y, y ≠ (arenaNames 0).nS → y ∉ rlS → σ'.vars y = σ.vars y) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (Kcsr x)

/-! ## §2 The rest of the load, as a program -/

/-- **The load's glue**: the carrier cell from the header, then the
identity renaming into the level-0 `up` region — `matCom`'s own counted
scan, at the level-0 name. -/
def rootGlueCom : Com :=
  .seq (.assign (arenaNames 0).nN (.var "n"))
    (.seq (.assign "rl.k" (.lit 0))
      (.while (.lt (.var "rl.k") (.var "n"))
        (.seq (.store (arenaNames 0).up (.var "rl.k") (.var "rl.k"))
          (.assign "rl.k" (.add (.var "rl.k") (.lit 1))))))

/-- The level-0 names, reduced to their literals (for `simp`). -/
private theorem nN0_eq : (arenaNames 0).nN = "sv.n" := rfl
private theorem up0_eq : (arenaNames 0).up = "sa.u" := rfl

/-- The scan's invariant: the counter within range and the `up` prefix
below it already the identity. -/
private def rlUpInv (n : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "rl.k" ≤ n ∧
    σ.arrs (arenaNames 0).up
      = List.range (σ.vars "rl.k")
        ++ List.replicate (n - σ.vars "rl.k") 0

/-- Writing the next identity entry extends the range prefix by one. -/
private theorem rl_range_set (nn k : ℕ) (hk : k < nn) :
    (List.range k ++ List.replicate (nn - k) (0 : ℕ)).set k k
      = List.range (k + 1) ++ List.replicate (nn - (k + 1)) 0 := by
  have hrep : List.replicate (nn - k) (0 : ℕ)
      = 0 :: List.replicate (nn - (k + 1)) 0 := by
    rw [show nn - k = nn - (k + 1) + 1 by omega, List.replicate_succ]
  rw [List.set_append_right _ _ (by simp), hrep]
  simp only [List.length_range, Nat.sub_self, List.set_cons_zero,
    List.range_succ, List.append_assoc, List.cons_append, List.nil_append]

/-- One turn of the scan: store the identity entry, advance the
counter. -/
private theorem rlBody_spec (B n : ℕ) (hnB : n < B) :
    Spec B (fun σ => rlUpInv n σ ∧ σ.vars "rl.k" < n)
      (.seq (.store (arenaNames 0).up (.var "rl.k") (.var "rl.k"))
        (.assign "rl.k" (.add (.var "rl.k") (.lit 1))))
      (fun σ σ' => rlUpInv n σ' ∧ σ'.vars "rl.k" = σ.vars "rl.k" + 1) 7 := by
  refine ((Spec.seq
    (Spec.store (a := (arenaNames 0).up) (i := .var "rl.k") (e := .var "rl.k")
      (idx := fun σ => σ.vars "rl.k") (f := fun σ => σ.vars "rl.k")
      (fun σ hσ => evalB_var (lt_trans hσ.2 hnB))
      (fun σ hσ => evalB_var (lt_trans hσ.2 hnB))
      (fun σ hσ => ?_))
    (Spec.assign (P := fun σ' => σ'.vars "rl.k" < n) (x := "rl.k")
      (e := .add (.var "rl.k") (.lit 1)) (f := fun σ' => σ'.vars "rl.k" + 1)
      (fun σ' hσ' => ?_))
    ?_ ?_).mono (by norm_num [Expr.size]))
  · -- the store stays in the array
    obtain ⟨⟨-, hk, hup⟩, hlt⟩ := hσ
    rw [hup]
    simp only [List.length_append, List.length_range, List.length_replicate]
    omega
  · -- the increment evaluates below the bound
    have hk : σ'.vars "rl.k" < B := lt_trans hσ' hnB
    have hres : σ'.vars "rl.k" + 1 < B := by omega
    have hev := evalB_bin (op := .add) (e := Expr.var "rl.k") (f := Expr.lit 1)
      (evalB_var hk) (evalB_lit (by omega)) (by simpa using hres)
    simpa using hev
  · -- the store lands in the increment's precondition
    rintro σ σ' ⟨-, hlt⟩ rfl
    simpa using hlt
  · -- the two updates re-establish the invariant
    rintro σ σ' σ'' ⟨⟨hn, hk, hup⟩, hlt⟩ rfl rfl
    refine ⟨⟨by simp [hn], by simp; omega, ?_⟩, by simp⟩
    have harr : (((σ.setArr (arenaNames 0).up (σ.vars "rl.k")
        (σ.vars "rl.k")).setVar "rl.k"
        ((σ.setArr (arenaNames 0).up (σ.vars "rl.k")
          (σ.vars "rl.k")).vars "rl.k" + 1)).arrs) (arenaNames 0).up
        = (σ.arrs (arenaNames 0).up).set (σ.vars "rl.k") (σ.vars "rl.k") := by
      simp
    rw [harr, hup, rl_range_set n (σ.vars "rl.k") hlt]
    simp

/-- **The glue's `Spec`**: from the header cell and a fresh `n`-cell
`up` allocation, the glue leaves the identity renaming in the level-0
`up` region and the carrier in the level-0 cell — with its exact frame
(it writes one array and two scalars) and length preservation. Cost
`11·n + 8`. -/
theorem rootGlueCom_spec (B n : ℕ) (hnB : n < B) :
    Spec B (fun σ => σ.vars "n" = n ∧
        σ.arrs (arenaNames 0).up = List.replicate n 0)
      rootGlueCom
      (fun σ σ' => σ'.arrs (arenaNames 0).up = List.range n ∧
        σ'.vars (arenaNames 0).nN = n ∧
        (∀ y, y ≠ (arenaNames 0).nN → y ≠ "rl.k" → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ (arenaNames 0).up → σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (11 * n + 8) := by
  -- the carrier assignment
  have hassign : Spec B (fun σ => σ.vars "n" = n ∧
      σ.arrs (arenaNames 0).up = List.replicate n 0)
      (.assign (arenaNames 0).nN (.var "n"))
      (fun σ σ' => σ' = σ.setVar (arenaNames 0).nN n) 2 := by
    refine (Spec.assign (f := fun _ => n) ?_).mono (by norm_num [Expr.size])
    intro σ hσ
    rw [← hσ.1]
    exact evalB_var (by rw [hσ.1]; exact hnB)
  -- the scan, with its frame
  have hloop := (Spec.forRangeZero (B := B) "rl.k" "n" (rlUpInv n) n 7 hnB
    (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (rlBody_spec B n hnB)).frame
  -- the composition, at the named relation
  have hseq := Spec.seq
    (R := fun σ σ'' => σ''.arrs (arenaNames 0).up = List.range n ∧
      σ''.vars (arenaNames 0).nN = n ∧
      (∀ y, y ≠ (arenaNames 0).nN → y ≠ "rl.k" → σ''.vars y = σ.vars y) ∧
      (∀ b, b ≠ (arenaNames 0).up → σ''.arrs b = σ.arrs b))
    hassign hloop
    (fun σ σ' hσ hq => by
      -- the assignment lands in the zeroed-counter invariant
      subst hq
      refine ⟨by simp [nN0_eq, hσ.1], by simp, ?_⟩
      simp [nN0_eq, hσ.2])
    (fun σ σ' σ'' hσ hq hq' => by
      -- assemble: the array's final value, the carrier cell, the frames
      subst hq
      obtain ⟨⟨⟨-, -, hup⟩, hk⟩, hfv, hfa, -, -⟩ := hq'
      have hwv : ∀ y, y ≠ "rl.k" →
          y ∉ (Com.wvars (.seq (.assign "rl.k" (.lit 0))
            (.while (.lt (.var "rl.k") (.var "n"))
              (.seq (.store (arenaNames 0).up (.var "rl.k") (.var "rl.k"))
                (.assign "rl.k" (.add (.var "rl.k") (.lit 1))))))) := by
        intro y hy hmem
        simp only [Com.wvars, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, false_or, or_self] at hmem
        exact hy hmem
      have hwa : ∀ b, b ≠ (arenaNames 0).up →
          b ∉ (Com.warrs (.seq (.assign "rl.k" (.lit 0))
            (.while (.lt (.var "rl.k") (.var "n"))
              (.seq (.store (arenaNames 0).up (.var "rl.k") (.var "rl.k"))
                (.assign "rl.k" (.add (.var "rl.k") (.lit 1))))))) := by
        intro b hb hmem
        simp only [Com.warrs, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, false_or] at hmem
        exact hb hmem
      refine ⟨by rw [hup, hk]; simp, ?_, ?_, ?_⟩
      · -- the carrier cell survives the scan
        rw [hfv _ (hwv _ (by decide))]
        simp [nN0_eq]
      · -- the scalar frame of the whole glue
        intro y hy1 hy2
        rw [hfv _ (hwv _ hy2)]
        simp [nN0_eq, show y ≠ "sv.n" from nN0_eq ▸ hy1]
      · -- the array frame of the whole glue
        intro b hb
        rw [hfa _ (hwa _ hb)]
        simp)
  -- lengths are preserved by any run
  have hfinal := specArrsLength hseq
  refine (hfinal.post ?_).mono (by omega)
  rintro σ σ'' - ⟨⟨h1, h2, h3, h4⟩, h5⟩
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## §3 The headline: `RootLoadSpec` from the CSR pass -/

/-- Reading any position of an all-zeros allocation. -/
private theorem getD_replicate_zero {m i : ℕ} :
    (List.replicate m (0 : ℕ)).getD i 0 = 0 := by
  rcases Nat.lt_or_ge i m with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

open Classical in
/-- **Residual 3a of `solveSpec_closed`, discharged down to the CSR
pass**: `RootLoadSpec` holds — verbatim — of `csrCom ; rootGlueCom`,
from the named residual `RootCsrLoadAll` and hypotheses only of the
F7-suppliable kinds (module docstring): the word bound, the `ext`
length conventions at the level-0 names, the empty root channel and
palette, the pass's scratch freshness, and the level-0 scratch
descriptor off `MatIn`'s lengths. -/
theorem rootLoadSpec_of_csrLoad (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ)
    (ext : List ℕ → String → ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Scr : ℕ → Env → Prop)
    (da : String) (rlS : List String) (csrCom : Com) (Kcsr : List ℕ → ℕ)
    -- the word bound at the carrier
    (hnB : ∀ x ∈ mcD n G c w, n < mcB q x)
    -- the root palette is the axiom's uncoloured input
    (hpal0 : (Headline.headlineSetup C hC φ).pal 0 = 0)
    -- the root channel is empty (rootArena.hist = [])
    (hhtab0 : ∀ (v : Fin (rootArena G (Impl.trivialColoring n)).N)
      (p : Fin (ℓp 0)),
      htabF 0 (rootArena G (Impl.trivialColoring n)) v p = [])
    -- the ext conventions at the level-0 names
    (hextUp0 : ∀ x ∈ mcD n G c w, ext x ((arenaNames 0).up) = n)
    (hextHist : ∀ x ∈ mcD n G c w,
      n * ℓp 0 * (hbf 0 + 1) ≤ ext x ((arenaNames 0).hist))
    (hextTab : ∀ x ∈ mcD n G c w,
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length
        ≤ ext x ((arenaNames 0).tab))
    -- the pass's scratch stays off the level-0 regions and the header
    (hda : da ∉ levelArrays 0)
    (hrlS_n : "n" ∉ rlS)
    -- the level-0 scratch descriptor, off `MatIn`'s lengths
    (hScr0 : ∀ x ∈ mcD n G c w, ∀ σ σ', MatIn (ext x) x σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr 0 σ')
    -- the named residual
    (hcsr : RootCsrLoadAll G c w q ext da rlS csrCom Kcsr) :
    RootLoadSpec C hC φ G c w q ext ℓp htabF hbf Scr
      (.seq csrCom rootGlueCom)
      (fun x => Kcsr x + (11 * n + 8)) := by
  intro x hx
  have henc := hx.1
  have hvc : vertexCount x = n := henc.vertexCount_eq
  -- scratch-name freshness, spelled out
  have hda' : ∀ b ∈ levelArrays 0, b ≠ da := fun b hb h => hda (h ▸ hb)
  have hup_da : (arenaNames 0).up ≠ da := hda' _ (by decide)
  have hcol_da : (arenaNames 0).col ≠ da := hda' _ (by decide)
  have hhist_da : (arenaNames 0).hist ≠ da := hda' _ (by decide)
  have htab_da : (arenaNames 0).tab ≠ da := hda' _ (by decide)
  refine Spec.seq (hcsr x hx) (rootGlueCom_spec (mcB q x) n (hnB x hx)) ?_ ?_
  · -- the pass's output lands in the glue's precondition
    rintro σ σ' hMat ⟨-, hfa, hfv, -⟩
    constructor
    · rw [hfv "n" (by decide) hrlS_n, hMat.root.n_eq, hvc]
    · rw [hfa _ (by decide) (by decide) hup_da,
        hMat.arrs _ (by decide), hextUp0 x hx]
  · -- assemble the level-0 `BlockPre`
    rintro σ σ' σ'' hMat ⟨⟨hoffL, htgtL, hgcsr⟩, hfa1, hfv1, hlen1⟩
      ⟨hup'', hnN'', hfv2, hfa2, hlen2⟩
    -- the untouched cells and regions, at the final state
    have hns : σ''.vars (arenaNames 0).nS = σ'.vars (arenaNames 0).nS :=
      hfv2 _ (by decide) (by decide)
    have harr_off : σ''.arrs (arenaNames 0).off = σ'.arrs (arenaNames 0).off :=
      hfa2 _ (by decide)
    have harr_tgt : σ''.arrs (arenaNames 0).tgt = σ'.arrs (arenaNames 0).tgt :=
      hfa2 _ (by decide)
    have hcol'' : σ''.arrs (arenaNames 0).col
        = List.replicate (ext x ((arenaNames 0).col)) 0 := by
      rw [hfa2 _ (by decide), hfa1 _ (by decide) (by decide) hcol_da,
        hMat.arrs _ (by decide)]
    have hhist'' : σ''.arrs (arenaNames 0).hist
        = List.replicate (ext x ((arenaNames 0).hist)) 0 := by
      rw [hfa2 _ (by decide), hfa1 _ (by decide) (by decide) hhist_da,
        hMat.arrs _ (by decide)]
    have htab'' : σ''.arrs (arenaNames 0).tab
        = List.replicate (ext x ((arenaNames 0).tab)) 0 := by
      rw [hfa2 _ (by decide), hfa1 _ (by decide) (by decide) htab_da,
        hMat.arrs _ (by decide)]
    -- the CSR prefix, transported to the final state
    set pw : String → Option ℕ := fun b =>
      if b = (arenaNames 0).off then some (n + 1)
      else if b = (arenaNames 0).tgt then some (σ'.vars (arenaNames 0).nS)
      else none with hpw_def
    have hpw_off : pw (arenaNames 0).off = some (n + 1) := if_pos rfl
    have hpw_tgt : pw (arenaNames 0).tgt
        = some (σ'.vars (arenaNames 0).nS) := by
      show (if (arenaNames 0).tgt = (arenaNames 0).off then _ else _) = _
      rw [if_neg (by decide), if_pos rfl]
    have hgcsr'' : GraphCsr (arenaNames 0).off (arenaNames 0).tgt G
        (σ'.vars (arenaNames 0).nS) (winA pw σ'') :=
      graphCsr_of_eq hgcsr (arrs_winA_eq_of_arrs_eq harr_off)
        (arrs_winA_eq_of_arrs_eq harr_tgt)
    -- the windowed contract's window family, at the final slot count
    set aws := arenaWs (arenaNames 0) ((Headline.headlineSetup C hC φ).pal 0)
      (ℓp 0) (hbf 0) n (σ''.vars (arenaNames 0).nS) with haws_def
    have haws_off : aws (arenaNames 0).off = some (n + 1) := arenaWs_off
    have haws_tgt : aws (arenaNames 0).tgt
        = some (σ''.vars (arenaNames 0).nS) := arenaWs_tgt (by decide)
    have haws_col : aws (arenaNames 0).col
        = some (n * (Headline.headlineSetup C hC φ).pal 0) :=
      arenaWs_col (by decide) (by decide)
    have haws_up : aws (arenaNames 0).up = some n :=
      arenaWs_up (by decide) (by decide) (by decide)
    have haws_hist : aws (arenaNames 0).hist
        = some (n * ℓp 0 * (hbf 0 + 1)) :=
      arenaWs_hist (by decide) (by decide) (by decide) (by decide)
    -- the allocation fits the windows
    have hFits : FitsW aws σ'' := by
      intro b m hbm
      rcases arenaWs_some_elim hbm with rfl | rfl | rfl | rfl | rfl
      · rw [haws_off] at hbm
        cases hbm
        rw [harr_off]
        exact hoffL
      · rw [haws_tgt] at hbm
        cases hbm
        rw [hns, harr_tgt]
        exact htgtL
      · rw [haws_col] at hbm
        cases hbm
        rw [hpal0]
        simp
      · rw [haws_up] at hbm
        cases hbm
        rw [hup'', List.length_range]
      · rw [haws_hist] at hbm
        cases hbm
        rw [hhist'', List.length_replicate]
        exact hextHist x hx
    -- the exact contract of the truncation
    have hst : ArenaSt (arenaNames 0) (hbf 0)
        (Impl.ofArena (rootArena G (Impl.trivialColoring n))
          (htabF 0 (rootArena G (Impl.trivialColoring n))))
        (winA aws σ'') := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- the carrier cell (the truncation does not touch scalars)
        show σ''.vars (arenaNames 0).nN = n
        exact hnN''
      · -- the CSR: the pass's prefix, read through the arena windows
        show GraphCsr (arenaNames 0).off (arenaNames 0).tgt G
          (σ''.vars (arenaNames 0).nS) (winA aws σ'')
        rw [hns]
        refine graphCsr_of_eq hgcsr'' ?_ ?_
        · exact arrs_winA_congr (haws_off.trans hpw_off.symm) σ''
        · refine arrs_winA_congr ?_ σ''
          rw [haws_tgt, hpw_tgt, hns]
      · -- the color rows: the palette is empty
        refine ⟨?_, ?_⟩
        · rw [arrs_winA_some haws_col σ'']
          simp [hpal0]
        · intro v cc
          exact absurd cc.isLt (by omega)
      · -- the renaming: the identity, written by the glue
        refine ⟨?_, ?_⟩
        · rw [arrs_winA_some haws_up σ'', hup'',
            List.take_of_length_le (by rw [List.length_range])]
          exact List.length_range
        · intro v
          rw [arrs_winA_some haws_up σ'', hup'',
            List.take_of_length_le (by rw [List.length_range]),
            List.getD_eq_getElem _ _
              (by simp only [List.length_range]; exact v.isLt),
            List.getElem_range]
          rfl
      · -- the channel: the all-zeros allocation IS the empty channel
        have hhw : (winA aws σ'').arrs (arenaNames 0).hist
            = List.replicate (n * ℓp 0 * (hbf 0 + 1)) 0 := by
          rw [arrs_winA_some haws_hist σ'', hhist'', List.take_replicate,
            Nat.min_eq_left (hextHist x hx)]
        -- (the length closes definitionally: the arena's carrier is `n`)
        refine ⟨by rw [hhw, List.length_replicate]; rfl, ?_⟩
        intro v p
        have h0 : (Impl.ofArena (rootArena G (Impl.trivialColoring n))
            (htabF 0 (rootArena G (Impl.trivialColoring n)))).hist v p
            = [] := hhtab0 v p
        refine ⟨by rw [h0]; simp, ?_, ?_⟩
        · rw [hhw, h0, getD_replicate_zero]
          simp
        · intro i hi
          rw [h0] at hi
          exact absurd hi (by simp)
    refine ⟨⟨?_, hst⟩, ?_, ?_⟩
    · -- the fit, at the contract's own window family
      exact hFits
    · -- the table allocation survives untouched
      show n * (levelFml (Headline.headlineSetup C hC φ) 0).length
        ≤ (σ''.arrs ((arenaNames 0).tab)).length
      rw [htab'', List.length_replicate]
      exact hextTab x hx
    · -- the level-0 scratch descriptor, off `MatIn`'s lengths
      exact hScr0 x hx σ σ'' hMat (fun b => (hlen2 b).trans (hlen1 b))

end Lax3Proofs.Prog
