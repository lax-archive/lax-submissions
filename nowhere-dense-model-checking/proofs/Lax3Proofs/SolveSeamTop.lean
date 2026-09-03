import Lax3Proofs.SolveFrameBridge

/-!
# F6c9 — the top scatter seam, discharged

`SolveFrameBridge.TopScatterAll` — residual 3b of `solveSpec_closed`,
at the statement this wave fixed: the precondition now carries, next
to the root block's postcondition, the **length-only scratch
descriptor** `Scr` of the stage (IMP+ cannot allocate, so the scatter
machinery's named `≥ N` regions must be advertised as lengths and
threaded from before the chain — `TopScatterSpec`'s docstring). This
file discharges the residual with a **real scatter program**:

* **`topAtomCom`** — one atom's stage: load the four input cells from
  the level-0 arena cells and the atom's compile-time constants
  (`topGlueCom`); extract the atom's β-column of the root table region
  into the bit region `pa` (`topColCom` — `pa[v] := tab[v·|ℱ₀| + bi]`,
  the column index `bi` a compile-time constant of the schedule); run
  the landed guarded greedy scatter (`scatterCom`, consumed through
  the windowed lift `scatterCom_specW` — the `t = 0` guard is inside
  it, a cost clause); store the guard bit `t ≤ gs.c` into slot `i` of
  the per-atom slot region `tsb` (`topBitCom`).
* **`topAtomsCom`** — the stage: one `topAtomCom` per scatter atom of
  `top`, slots indexed by list position. `topAtomsCom_spec` is the
  loop-free induction over the compile-time atom list: each slot ends
  up holding its atom's guard bit over the table the region holds,
  and earlier slots survive later atoms (distinct positions of one
  region).
* **`topScatterAll_of`** — the headline: `TopScatterAll` holds,
  verbatim, of `topAtomsCom` at the canonical level-0 names, the read
  family `av σa := tsb[memIdx atoms σa]`, and the summed budget
  `topScatK`, from F7-suppliable hypotheses only: the word bounds
  (the carrier, its square, the level-0 table row `n·|ℱ₀|`, the
  schedule constants `σa.r + 2`, `σa.t`, `|atoms|`), the scratch
  descriptor's four length clauses (`hscrT` — exactly what the fixed
  `Scr` pre-clause exists to supply), and the four scratch names'
  freshness against the level-0 family. The table the counts are
  taken over is the chain's own (`BlockPost`'s `unrollAux S.depth 0`),
  which **is** `unrolledTables 0` definitionally — no degenerate
  escape: the program never mentions the answer; `av` reads cells the
  scatter runs wrote.

The column index of an atom is `memIdx (levelFml S 0) σa.β` — a
choice-based first index (no `BEq` on formulas needed);
`beta_mem_levelFml_zero` supplies membership. Duplicated atoms are
harmless: a later occurrence rewrites its own slot with the same bit,
and `av` reads the first occurrence's slot.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun

/-! ## §0 Helpers: a choice-based list index, `getD` over `set`, a
transport -/

open Classical in
/-- The index of a member of a list, by choice — no `BEq` on the
element type is asked for (the atom and formula types carry none). -/
noncomputable def memIdx {α : Type*} (l : List α) (a : α) : ℕ :=
  if h : a ∈ l then (List.mem_iff_getElem.mp h).choose else 0

theorem memIdx_lt {α : Type*} {l : List α} {a : α} (h : a ∈ l) :
    memIdx l a < l.length := by
  rw [memIdx, dif_pos h]
  exact (List.mem_iff_getElem.mp h).choose_spec.choose

theorem getElem_memIdx {α : Type*} {l : List α} {a : α} (h : a ∈ l) :
    l[memIdx l a]'(memIdx_lt h) = a := by
  simp only [memIdx, dif_pos h]
  exact (List.mem_iff_getElem.mp h).choose_spec.choose_spec

/-- Reading the written cell of a `set`. -/
theorem getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

/-- Reading any other cell of a `set`. -/
theorem getD_set_ne {l : List ℕ} {i k v : ℕ} (h : k ≠ i) :
    (l.set i v).getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h),
    ← List.getD_eq_getElem?_getD]

/-- `TableBitsW` reads one array; it transports along agreement. -/
theorem tableBitsW_of_eq {a : String} {N Λ : ℕ} {Fl : List (DistFO Λ 1)}
    {T : Fin N → DistFO Λ 1 → Prop} {σ σ' : Env}
    (h : TableBitsW a Fl T σ) (ha : σ'.arrs a = σ.arrs a) :
    TableBitsW a Fl T σ' :=
  ⟨by rw [ha]; exact h.1, fun v i hi => by rw [ha]; exact h.2 v i hi⟩

/-! ## §1 The programs -/

/-- Load the scatter stage's four input cells for one atom: the
carrier and slot count from the level's cells, the radius and demand
as the atom's compile-time constants. -/
def topGlueCom (nm : ArenaNames) (r t : ℕ) : Com :=
  .seq (.assign "gs.n" (.var nm.nN))
    (.seq (.assign "gs.m" (.var nm.nS))
      (.seq (.assign "gs.r" (.lit r)) (.assign "gs.t" (.lit t))))

/-- Extract one β-column of the table region into the bit region:
`pa[v] := tab[v·F + bi]` for `v < gs.n` — the batch the scatter
counts over. -/
def topColCom (tab pa : String) (F bi : ℕ) : Com :=
  .seq (.assign "gs.i" (.lit 0))
    (.while (.lt (.var "gs.i") (.var "gs.n"))
      (Fill.put pa "gs.i"
        (.get tab (.add (.mul (.var "gs.i") (.lit F)) (.lit bi)))))

/-- Store the guard bit of the count: `tsb[i] := (t ≤ gs.c)`. -/
def topBitCom (tsb : String) (i t : ℕ) : Com :=
  .ite (.lt (.var "gs.c") (.lit t))
    (.store tsb (.lit i) (.lit 0))
    (.store tsb (.lit i) (.lit 1))

/-- **One atom's scatter stage**: glue, column extraction, the landed
guarded greedy scatter, the bit store. -/
def topAtomCom (nm : ArenaNames) (pa ma da tsb : String)
    (F i bi r t : ℕ) : Com :=
  .seq (topGlueCom nm r t)
    (.seq (topColCom nm.tab pa F bi)
      (.seq (scatterCom nm.off nm.tgt pa ma da) (topBitCom tsb i t)))

/-- **The whole stage**: one `topAtomCom` per atom, slots by list
position; `bIdx` names each atom's column of the table region. -/
def topAtomsCom (nm : ArenaNames) (pa ma da tsb : String) (F : ℕ)
    {Λc : ℕ} (bIdx : ScatterSentence Λc → ℕ) :
    List (ScatterSentence Λc) → ℕ → Com
  | [], _ => .skip
  | σa :: rest, i =>
    .seq (topAtomCom nm pa ma da tsb F i (bIdx σa) σa.r σa.t)
      (topAtomsCom nm pa ma da tsb F bIdx rest (i + 1))

/-- One atom's budget: the glue (8), the column loop (`16·N + 6`),
the landed `scatterK`, the bit store (7). -/
noncomputable def topAtomK (N ns r t : ℕ) : ℕ :=
  8 + (16 * N + 6) + scatterK N ns r t + 7

/-- The stage's budget: one `topAtomK` per atom, plus the final
skip. -/
noncomputable def topScatK {Λc : ℕ} (N ns : ℕ) :
    List (ScatterSentence Λc) → ℕ
  | [] => 1
  | σa :: rest => topAtomK N ns σa.r σa.t + topScatK N ns rest

/-! ## §2 The stage's state descriptor -/

open Classical in
/-- **The state the stage runs in**: the level's windowed arena, the
windowed table region at the family `Fl` and table `T`, and the four
scratch allocations the fixed `TopScatterSpec` pre-clause exists to
supply — the column region, the scatter's mark and distance regions
(each at least the carrier), and the per-atom slot region (at least
`M` cells). -/
def TopScatSt {Λc n₀ ℓp : ℕ} (nm : ArenaNames) (hb : ℕ)
    (A : Impl.MArena Λc n₀ ℓp) (Fl : List (DistFO Λc 1))
    (T : Fin A.N → DistFO Λc 1 → Prop) (pa ma da tsb : String) (M : ℕ)
    (σ : Env) : Prop :=
  ArenaStW nm hb A σ ∧ TableBitsW nm.tab Fl T σ ∧
    A.N ≤ (σ.arrs pa).length ∧ A.N ≤ (σ.arrs ma).length ∧
    A.N ≤ (σ.arrs da).length ∧ M ≤ (σ.arrs tsb).length

section Stage

variable {B n₀ Λc ℓp hb : ℕ} {A : Impl.MArena Λc n₀ ℓp}
  {nm : ArenaNames} {pa ma da tsb : String}

/-! ## §3 The glue -/

/-- **The glue's `Spec`**: four cell loads, the exact final state. -/
theorem topGlueCom_spec (r t : ℕ) (hNB : A.N < B) (hNNB : A.N * A.N < B)
    (hrB : r < B) (htB : t < B) (hnS : nm.nS ∉ gsScalars) :
    Spec B (fun σ => ArenaStW nm hb A σ) (topGlueCom nm r t)
      (fun σ σ' => σ' = (((σ.setVar "gs.n" A.N).setVar "gs.m"
        (σ.vars nm.nS)).setVar "gs.r" r).setVar "gs.t" t) 8 := by
  intro σ hσ
  have hnSn : nm.nS ≠ "gs.n" := fun h => hnS (by rw [h]; decide)
  have h1 : (Expr.var nm.nN).evalB B σ = some A.N := by
    have hn := hσ.n_eq
    rw [← hn]
    exact evalB_var (by rw [hn]; exact hNB)
  have hnsB : σ.vars nm.nS < B := by
    have := hσ.ns_le_sq
    omega
  have h2 : (Expr.var nm.nS).evalB B (σ.setVar "gs.n" A.N)
      = some (σ.vars nm.nS) := by
    have hv : (σ.setVar "gs.n" A.N).vars nm.nS = σ.vars nm.nS := by
      simp [hnSn]
    rw [← hv]
    exact evalB_var (by rw [hv]; exact hnsB)
  refine ⟨_, ?_, rfl⟩
  exact (Run.seq (Run.assign h1)
    (Run.seq (Run.assign h2)
      (Run.seq (Run.assign (evalB_lit hrB))
        (Run.assign (evalB_lit htB))))).mono (by norm_num)

/-! ## §4 The column extraction -/

open Classical in
/-- The column loop's invariant: the table region, the bound cell,
the bit allocation, and the prefix below the counter already holding
the column of `β`. -/
def ColInv (nm : ArenaNames) {Λc n₀ ℓp : ℕ} (A : Impl.MArena Λc n₀ ℓp)
    (Fl : List (DistFO Λc 1)) (T : Fin A.N → DistFO Λc 1 → Prop)
    (pa : String) (β : DistFO Λc 1) (σ : Env) : Prop :=
  TableBitsW nm.tab Fl T σ ∧ σ.vars "gs.n" = A.N ∧
    A.N ≤ (σ.arrs pa).length ∧ σ.vars "gs.i" ≤ A.N ∧
    ∀ k, k < σ.vars "gs.i" → ∀ hk : k < A.N,
      (σ.arrs pa).getD k 0 = if T ⟨k, hk⟩ β then 1 else 0

open Classical in
/-- One turn of the column loop: read the table bit, store it, bump
the counter. -/
theorem topColBody_spec {Fl : List (DistFO Λc 1)}
    {T : Fin A.N → DistFO Λc 1 → Prop} (bi : ℕ) (β : DistFO Λc 1)
    (hbi : bi < Fl.length) (hβ : Fl[bi] = β)
    (hNB : A.N < B) (hNFB : A.N * Fl.length < B) (h1B : 1 < B)
    (htab_pa : nm.tab ≠ pa) :
    Spec B (fun σ => ColInv nm A Fl T pa β σ ∧ σ.vars "gs.i" < A.N)
      (Fill.put pa "gs.i"
        (.get nm.tab (.add (.mul (.var "gs.i") (.lit Fl.length)) (.lit bi))))
      (fun σ σ' => ColInv nm A Fl T pa β σ' ∧
        σ'.vars "gs.i" = σ.vars "gs.i" + 1) 12 := by
  rintro σ ⟨⟨hTab, hgn, hpaL, hile, hpref⟩, hlt⟩
  have hidx : σ.vars "gs.i" * Fl.length + bi < A.N * Fl.length :=
    tableIdx_lt (⟨σ.vars "gs.i", hlt⟩ : Fin A.N) hbi
  have hiB : σ.vars "gs.i" < B := lt_trans hlt hNB
  -- the index expression evaluates
  have hmul : (Expr.mul (.var "gs.i") (.lit Fl.length)).evalB B σ
      = some (σ.vars "gs.i" * Fl.length) := by
    rw [Expr.mul_def]
    have hFB : Fl.length < B := by
      have h : 1 * Fl.length ≤ A.N * Fl.length :=
        Nat.mul_le_mul_right Fl.length (by omega)
      rw [one_mul] at h
      omega
    have h := evalB_bin (op := .mul) (evalB_var hiB)
      (evalB_lit (n := Fl.length) hFB) (by rw [Bop.apply_mul]; omega)
    rwa [Bop.apply_mul] at h
  have hadd : (Expr.add (.mul (.var "gs.i") (.lit Fl.length))
      (.lit bi)).evalB B σ = some (σ.vars "gs.i" * Fl.length + bi) := by
    rw [Expr.add_def]
    have h := evalB_bin (op := .add) hmul (evalB_lit (n := bi) (by omega))
      (by rw [Bop.apply_add]; omega)
    rwa [Bop.apply_add] at h
  -- the read hits the table region and delivers the bit
  have hlen : σ.vars "gs.i" * Fl.length + bi < (σ.arrs nm.tab).length :=
    lt_of_lt_of_le hidx hTab.1
  have hbit : (σ.arrs nm.tab).getD (σ.vars "gs.i" * Fl.length + bi) 0
      = if T ⟨σ.vars "gs.i", hlt⟩ β then 1 else 0 := by
    have h := hTab.2 ⟨σ.vars "gs.i", hlt⟩ bi hbi
    simp only [hβ] at h
    exact h
  have hev : (Expr.get nm.tab (.add (.mul (.var "gs.i") (.lit Fl.length))
      (.lit bi))).evalB B σ
      = some (if T ⟨σ.vars "gs.i", hlt⟩ β then 1 else 0) := by
    refine evalB_get hadd ?_ (by split <;> omega)
    rw [List.getElem?_eq_getElem hlen]
    refine congrArg some ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
      Option.getD_some] at hbit
    exact hbit
  -- the increment evaluates on the stored state
  have hinc : (Expr.add (.var "gs.i") (.lit 1)).evalB B
      (σ.setArr pa (σ.vars "gs.i") (if T ⟨σ.vars "gs.i", hlt⟩ β then 1 else 0))
      = some (σ.vars "gs.i" + 1) := by
    rw [Expr.add_def]
    have h := evalB_bin (op := .add)
      (evalB_var (x := "gs.i")
        (σ := σ.setArr pa (σ.vars "gs.i")
          (if T ⟨σ.vars "gs.i", hlt⟩ β then 1 else 0))
        (by simpa using hiB))
      (evalB_lit (show 1 < B from h1B))
      (by rw [Bop.apply_add]; simp; omega)
    rw [Bop.apply_add] at h
    simpa using h
  refine ⟨_, (Run.seq
      (Run.store (evalB_var hiB) hev (lt_of_lt_of_le hlt hpaL))
      (Run.assign hinc)).mono (by simp), ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by simp⟩⟩
  · exact tableBitsW_of_eq hTab (by simp [htab_pa])
  · simpa using hgn
  · simpa using hpaL
  · rw [vars_setVar, if_pos rfl]
    omega
  · -- the prefix, one cell longer
    intro k hk hkN
    have hk' : k < σ.vars "gs.i" + 1 := by
      rw [vars_setVar, if_pos rfl] at hk
      exact hk
    rw [arrs_setVar, arrs_setArr, if_pos rfl]
    by_cases hki : k = σ.vars "gs.i"
    · subst hki
      rw [getD_set_self (lt_of_lt_of_le hlt hpaL)]
    · rw [getD_set_ne hki]
      exact hpref k (by omega) hkN

open Classical in
/-- **The column extraction's `Spec`**: from the table region, the
carrier in `gs.n` and a bit allocation of at least the carrier, the
loop leaves the table intact and the bit region holding the β-column's
indicator — `FinBitsW` at the column's set, the shape the scatter lift
consumes. -/
theorem topColCom_spec {Fl : List (DistFO Λc 1)}
    {T : Fin A.N → DistFO Λc 1 → Prop} (bi : ℕ) (β : DistFO Λc 1)
    (hbi : bi < Fl.length) (hβ : Fl[bi] = β)
    (hNB : A.N < B) (hNFB : A.N * Fl.length < B) (h1B : 1 < B)
    (htab_pa : nm.tab ≠ pa) :
    Spec B (fun σ => TableBitsW nm.tab Fl T σ ∧ σ.vars "gs.n" = A.N ∧
        A.N ≤ (σ.arrs pa).length)
      (topColCom nm.tab pa Fl.length bi)
      (fun _ σ' => TableBitsW nm.tab Fl T σ' ∧ σ'.vars "gs.n" = A.N ∧
        FinBitsW pa {v : Fin A.N | T v β} σ')
      (16 * A.N + 6) := by
  have hloop := Spec.forRangeZero (B := B) "gs.i" "gs.n"
    (ColInv nm A Fl T pa β) A.N 12 hNB
    (fun σ hσ => hσ.2.2.2.1) (fun σ hσ => hσ.2.1)
    (topColBody_spec bi β hbi hβ hNB hNFB h1B htab_pa)
  refine ((hloop.pre ?_).post ?_).mono (by omega)
  · rintro σ ⟨hTab, hgn, hpaL⟩
    refine ⟨tableBitsW_of_eq hTab rfl, by simp [hgn], hpaL, by simp, ?_⟩
    intro k hk
    simp at hk
  · rintro σ σ' - ⟨⟨hTab, hgn, hpaL, -, hpref⟩, hiN⟩
    refine ⟨hTab, hgn, hpaL, fun v => ?_⟩
    have h := hpref (v : ℕ) (by rw [hiN]; exact v.2) v.2
    simpa [Set.mem_setOf_eq] using h

/-! ## §5 The bit store -/

open Classical in
/-- **The bit store's `Spec`**: the guard bit of the count into slot
`i` — one comparison, one store. -/
theorem topBitCom_spec (i t cnt : ℕ) (htB : t < B) (hcnt : cnt < B)
    (hiB : i < B) (h1B : 1 < B) :
    Spec B (fun σ => σ.vars "gs.c" = cnt ∧ i < (σ.arrs tsb).length)
      (topBitCom tsb i t)
      (fun σ σ' => σ' = σ.setArr tsb i (if t ≤ cnt then 1 else 0)) 7 := by
  rintro σ ⟨hc, hi⟩
  have h0B : 0 < B := by omega
  have hgc : (Cond.lt (.var "gs.c") (.lit t)).evalB B σ
      = some (decide (cnt < t)) := by
    rw [← hc]
    exact evalB_condLt (evalB_var (by rw [hc]; exact hcnt)) (evalB_lit htB)
  by_cases hlt : cnt < t
  · refine ⟨_, (Run.ite_true (by rw [hgc]; simp [hlt])
      (Run.store (evalB_lit hiB) (evalB_lit h0B) hi)).mono (by simp), ?_⟩
    rw [if_neg (by omega)]
  · refine ⟨_, (Run.ite_false (by rw [hgc]; simp [hlt])
      (Run.store (evalB_lit hiB) (evalB_lit h1B) hi)).mono (by simp), ?_⟩
    rw [if_pos (by omega)]

/-! ## §6 One atom, assembled -/

open Classical in
/-- **One atom's `Spec`**: from the stage's state, `topAtomCom` leaves
the state intact and slot `i` holding the atom's guard bit over the
table `T` — every other slot untouched, every length preserved. The
scatter runs the landed machinery (`scatterCom_specW`); the `t = 0`
guard is inside it. -/
theorem topAtomCom_spec {Fl : List (DistFO Λc 1)}
    {T : Fin A.N → DistFO Λc 1 → Prop} (M i bi : ℕ) (β : DistFO Λc 1)
    (r t : ℕ) (hbi : bi < Fl.length) (hβ : Fl[bi] = β) (hiM : i < M)
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hNFB : A.N * Fl.length < B)
    (hrB : r + 2 < B) (htB : t < B) (hiB : i < B) (h1B : 1 < B)
    (hot : nm.tgt ≠ nm.off)
    (hda5 : da ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hma5 : ma ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hpa5 : pa ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hda_ma : da ≠ ma) (hda_pa : da ≠ pa) (hma_pa : ma ≠ pa)
    (hnN : nm.nN ∉ gsScalars) (hnS : nm.nS ∉ gsScalars)
    (htab_pa : nm.tab ≠ pa) (htab_ma : nm.tab ≠ ma) (htab_da : nm.tab ≠ da)
    (htsb_pa : tsb ≠ pa) (htsb_ma : tsb ≠ ma) (htsb_da : tsb ≠ da)
    (htsb_tab : tsb ≠ nm.tab)
    (htsb5 : tsb ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String)) :
    Spec B (TopScatSt nm hb A Fl T pa ma da tsb M)
      (topAtomCom nm pa ma da tsb Fl.length i bi r t)
      (fun σ σ' => TopScatSt nm hb A Fl T pa ma da tsb M σ' ∧
        (σ'.arrs tsb).getD i 0
          = (if t ≤ Lax3Proofs.Impl.greedyScatter A.G r
              {v : Fin A.N | T v β} t then 1 else 0) ∧
        (∀ k, k ≠ i → (σ'.arrs tsb).getD k 0 = (σ.arrs tsb).getD k 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (topAtomK A.N (∑ v : Fin A.N, A.G.degree v) r t) := by
  -- the name disequalities, spelled out
  have hpa5C := hpa5
  have hma5C := hma5
  have hda5C := hda5
  have htsb5C := htsb5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hpa5C hma5C hda5C htsb5C
  obtain ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h⟩ := hpa5C
  obtain ⟨hma_o, hma_t, hma_c, hma_u, hma_h⟩ := hma5C
  obtain ⟨hda_o, hda_t, hda_c, hda_u, hda_h⟩ := hda5C
  obtain ⟨htsb_o, htsb_t, htsb_c, htsb_u, htsb_h⟩ := htsb5C
  have hnN4 : nm.nN ≠ "gs.n" ∧ nm.nN ≠ "gs.m" ∧ nm.nN ≠ "gs.r" ∧
      nm.nN ≠ "gs.t" ∧ nm.nN ≠ "gs.i" := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun h => hnN (by rw [h]; decide)
  have hnS4 : nm.nS ≠ "gs.n" ∧ nm.nS ≠ "gs.m" ∧ nm.nS ≠ "gs.r" ∧
      nm.nS ≠ "gs.t" ∧ nm.nS ≠ "gs.i" := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fun h => hnS (by rw [h]; decide)
  intro σ hσ
  obtain ⟨hAW, hTab, hpaL, hmaL, hdaL, htsbL⟩ := hσ
  -- §A the glue
  obtain ⟨σ1, hr1, hq1⟩ :=
    topGlueCom_spec (hb := hb) r t hNB hNNB (by omega) htB hnS σ hAW
  subst hq1
  have hAW1 : ArenaStW nm hb A ((((σ.setVar "gs.n" A.N).setVar "gs.m"
      (σ.vars nm.nS)).setVar "gs.r" r).setVar "gs.t" t) := by
    refine arenaStW_of_eq hAW ?_ ?_ rfl rfl rfl rfl rfl
    · simp [hnN4.1, hnN4.2.1, hnN4.2.2.1, hnN4.2.2.2.1]
    · simp [hnS4.1, hnS4.2.1, hnS4.2.2.1, hnS4.2.2.2.1]
  -- §B the column extraction
  obtain ⟨σ2, hr2, ⟨⟨hTab2, hgn2, hPa2⟩, hfv2, hfa2, -, -⟩, hlen2⟩ :=
    (specArrsLength ((topColCom_spec (T := T) bi β hbi hβ hNB hNFB h1B
        htab_pa).frame))
      ((((σ.setVar "gs.n" A.N).setVar "gs.m"
        (σ.vars nm.nS)).setVar "gs.r" r).setVar "gs.t" t)
      ⟨tableBitsW_of_eq hTab rfl, by simp, hpaL⟩
  have hwv2 : ∀ y, y ≠ "gs.i" → σ2.vars y
      = ((((σ.setVar "gs.n" A.N).setVar "gs.m"
        (σ.vars nm.nS)).setVar "gs.r" r).setVar "gs.t" t).vars y := by
    intro y hy
    exact hfv2 y (by simp [topColCom, Com.wvars, Fill.put, hy])
  have hwa2 : ∀ b, b ≠ pa → σ2.arrs b = σ.arrs b := by
    intro b hb'
    exact hfa2 b (by simp [topColCom, Com.warrs, Fill.put, hb'])
  have hAW2 : ArenaStW nm hb A σ2 :=
    arenaStW_of_eq hAW1 (hwv2 _ hnN4.2.2.2.2) (hwv2 _ hnS4.2.2.2.2)
      (hwa2 _ (Ne.symm hpa_o)) (hwa2 _ (Ne.symm hpa_t))
      (hwa2 _ (Ne.symm hpa_c)) (hwa2 _ (Ne.symm hpa_u))
      (hwa2 _ (Ne.symm hpa_h))
  have hgm2 : σ2.vars "gs.m" = σ2.vars nm.nS := by
    rw [hwv2 "gs.m" (by decide), hwv2 nm.nS hnS4.2.2.2.2]
    simp [hnS4.1, hnS4.2.1, hnS4.2.2.1, hnS4.2.2.2.1]
  have hgr2 : σ2.vars "gs.r" = r := by
    rw [hwv2 "gs.r" (by decide)]
    simp
  have hgt2 : σ2.vars "gs.t" = t := by
    rw [hwv2 "gs.t" (by decide)]
    simp
  have hmaL2 : A.N ≤ (σ2.arrs ma).length := by
    rw [hwa2 ma hma_pa]
    exact hmaL
  have hdaL2 : A.N ≤ (σ2.arrs da).length := by
    rw [hwa2 da hda_pa]
    exact hdaL
  -- §C the landed scatter, through the windowed lift
  obtain ⟨σ3, hr3, ⟨hAW3, hnS3, hcnt3, hPa3, hlen3⟩, hfv3, hfa3, -, -⟩ :=
    ((scatterCom_specW (A := A) (X := {v : Fin A.N | T v β}) (hb := hb)
        hNB hNNB hrB htB hot hda5 hma5 hpa5 hda_ma hda_pa hma_pa
        hnN hnS).frame) σ2
      ⟨hAW2, hgn2, hgm2, hgr2, hgt2, hPa2, hmaL2, hdaL2⟩
  have hwa3 : ∀ b, b ≠ ma → b ≠ da → σ3.arrs b = σ2.arrs b := by
    intro b h1 h2
    refine hfa3 b ?_
    rw [warrs_scatterCom]
    simp [h1, h2]
  have hTab3 : TableBitsW nm.tab Fl T σ3 :=
    tableBitsW_of_eq hTab2 (hwa3 _ htab_ma htab_da)
  have htsb3 : σ3.arrs tsb = σ.arrs tsb := by
    rw [hwa3 tsb htsb_ma htsb_da, hwa2 tsb htsb_pa]
  have htsbL3 : i < (σ3.arrs tsb).length := by
    rw [htsb3]
    omega
  -- §D the bit store
  have hcntB : Lax3Proofs.Impl.greedyScatter A.G r {v : Fin A.N | T v β} t
      < B := by
    have hmin := Lax3Proofs.Impl.greedyScatter_eq_min A.G r
      {v : Fin A.N | T v β} t
    have hle : Lax3Proofs.Impl.greedyScatter A.G r {v : Fin A.N | T v β} t
        ≤ t := by rw [hmin]; exact min_le_left _ _
    omega
  obtain ⟨σ4, hr4, hq4⟩ := topBitCom_spec (tsb := tsb) i t
    (Lax3Proofs.Impl.greedyScatter A.G r {v : Fin A.N | T v β} t)
    htB hcntB hiB h1B σ3 ⟨hcnt3, htsbL3⟩
  subst hq4
  -- assemble
  have hlen4 : ∀ b, ((σ3.setArr tsb i
      (if t ≤ Lax3Proofs.Impl.greedyScatter A.G r {v : Fin A.N | T v β} t
        then 1 else 0)).arrs b).length = (σ.arrs b).length := by
    intro b
    calc ((σ3.setArr tsb i _).arrs b).length = (σ3.arrs b).length :=
        length_arrs_setArr σ3 tsb i _ b
      _ = (σ2.arrs b).length := hlen3 b
      _ = (σ.arrs b).length := hlen2 b
  refine ⟨_, (hr1.seq (hr2.seq (hr3.seq hr4))).mono
    (by unfold topAtomK; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, hlen4⟩
  · -- the windowed arena, intact
    exact arenaStW_of_eq hAW3 rfl rfl
      (by simp [Ne.symm htsb_o]) (by simp [Ne.symm htsb_t])
      (by simp [Ne.symm htsb_c]) (by simp [Ne.symm htsb_u])
      (by simp [Ne.symm htsb_h])
  · -- the table region, intact
    exact tableBitsW_of_eq hTab3 (by simp [Ne.symm htsb_tab])
  · rw [hlen4]
    exact hpaL
  · rw [hlen4]
    exact hmaL
  · rw [hlen4]
    exact hdaL
  · rw [hlen4]
    exact htsbL
  · -- slot `i` holds the guard bit
    rw [arrs_setArr, if_pos rfl]
    exact getD_set_self htsbL3
  · -- every other slot untouched
    intro k hk
    rw [arrs_setArr, if_pos rfl, getD_set_ne hk, htsb3]

/-! ## §7 The atom list, by induction -/

open Classical in
/-- **The stage's `Spec`**, by induction over the compile-time atom
list: from the stage's state, `topAtomsCom` leaves the state intact,
slot `i + k` holding atom `k`'s guard bit, every slot below `i`
untouched, every length preserved. -/
theorem topAtomsCom_spec {Fl : List (DistFO Λc 1)}
    {T : Fin A.N → DistFO Λc 1 → Prop} (M : ℕ)
    (bIdx : ScatterSentence Λc → ℕ)
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hNFB : A.N * Fl.length < B)
    (hMB : M < B) (h1B : 1 < B)
    (hot : nm.tgt ≠ nm.off)
    (hda5 : da ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hma5 : ma ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hpa5 : pa ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hda_ma : da ≠ ma) (hda_pa : da ≠ pa) (hma_pa : ma ≠ pa)
    (hnN : nm.nN ∉ gsScalars) (hnS : nm.nS ∉ gsScalars)
    (htab_pa : nm.tab ≠ pa) (htab_ma : nm.tab ≠ ma) (htab_da : nm.tab ≠ da)
    (htsb_pa : tsb ≠ pa) (htsb_ma : tsb ≠ ma) (htsb_da : tsb ≠ da)
    (htsb_tab : tsb ≠ nm.tab)
    (htsb5 : tsb ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (l : List (ScatterSentence Λc)) :
    ∀ i : ℕ, i + l.length ≤ M →
    (∀ σa ∈ l, (∃ h : bIdx σa < Fl.length, Fl[bIdx σa]'h = σa.β) ∧
      σa.r + 2 < B ∧ σa.t < B) →
    Spec B (TopScatSt nm hb A Fl T pa ma da tsb M)
      (topAtomsCom nm pa ma da tsb Fl.length bIdx l i)
      (fun σ σ' => TopScatSt nm hb A Fl T pa ma da tsb M σ' ∧
        (∀ k, (hk : k < l.length) → (σ'.arrs tsb).getD (i + k) 0
          = (if l[k].t ≤ Lax3Proofs.Impl.greedyScatter A.G l[k].r
              {v : Fin A.N | T v l[k].β} l[k].t then 1 else 0)) ∧
        (∀ k, k < i → (σ'.arrs tsb).getD k 0 = (σ.arrs tsb).getD k 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (topScatK A.N (∑ v : Fin A.N, A.G.degree v) l) := by
  induction l with
  | nil =>
    intro i hiM hl
    refine Spec.skip.post ?_
    rintro σ σ' hσ rfl
    exact ⟨hσ, fun k hk => absurd hk (Nat.not_lt_zero k),
      fun k _ => rfl, fun b => rfl⟩
  | cons σa rest ih =>
    intro i hiM hl
    simp only [List.length_cons] at hiM
    obtain ⟨⟨hbi, hβ⟩, hrB, htB⟩ := hl σa (List.mem_cons_self ..)
    have hatom := topAtomCom_spec (T := T) (hb := hb) M i (bIdx σa) σa.β
      σa.r σa.t hbi hβ (by omega) hNB hNNB hNFB hrB htB (by omega) h1B hot
      hda5 hma5 hpa5 hda_ma hda_pa hma_pa hnN hnS htab_pa htab_ma htab_da
      htsb_pa htsb_ma htsb_da htsb_tab htsb5
    have hrest := ih (i + 1) (by omega)
      (fun τa hτa => hl τa (List.mem_cons_of_mem _ hτa))
    refine Spec.seq hatom hrest (fun σ σ' _ h => h.1) ?_
    rintro σ σ' σ'' - ⟨-, hbit', hoth', hlen'⟩ ⟨hSt'', hcells'', hlow'', hlen''⟩
    refine ⟨hSt'', ?_, ?_, fun b => (hlen'' b).trans (hlen' b)⟩
    · intro k hk
      cases k with
      | zero =>
        have h1 : (σ''.arrs tsb).getD i 0 = (σ'.arrs tsb).getD i 0 :=
          hlow'' i (by omega)
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [h1, hbit']
        rfl
      | succ k =>
        have hk' : k < rest.length := by
          simp only [List.length_cons] at hk
          omega
        have h2 := hcells'' k hk'
        rw [show i + (k + 1) = i + 1 + k by omega]
        simpa only [List.getElem_cons_succ] using h2
    · intro k hk
      rw [hlow'' k (by omega), hoth' k (by omega)]

end Stage

/-! ## §8 The headline: `TopScatterAll`, discharged -/

open Classical in
/-- **Residual 3b of `solveSpec_closed`, discharged** — at the
statement this wave fixed: `TopScatterAll` holds, verbatim, of the
real scatter stage `topAtomsCom` at the canonical level-0 names, the
read family `av σa := tsb[memIdx atoms σa]` and the summed budget
`topScatK`, from F7-suppliable hypotheses only (module docstring):
the word bounds, the top scratch descriptor's four length clauses
(`hscrT` — what the fixed `Scr` pre-clause exists to supply), and
the scratch names' freshness against the level-0 family. -/
theorem topScatterAll_of (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ) (Scr : Env → Prop) (pa ma da tsb : String)
    (hq : 1 ≤ q)
    -- the top scratch descriptor's four length clauses
    (hscrT : ∀ σ, Scr σ → n ≤ (σ.arrs pa).length ∧
      n ≤ (σ.arrs ma).length ∧ n ≤ (σ.arrs da).length ∧
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ).length
        ≤ (σ.arrs tsb).length)
    -- the word bounds, per admissible input
    (hB : ∀ x ∈ mcD n G c w, n < mcB q x ∧ n * n < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ) 0).length < mcB q x ∧
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ).length < mcB q x)
    (hatomB : ∀ x ∈ mcD n G c w,
      ∀ σa ∈ scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ,
      σa.r + 2 < mcB q x ∧ σa.t < mcB q x)
    -- the scratch names, fresh against the level-0 family
    (hpa : pa ∉ levelArrays 0) (hma : ma ∉ levelArrays 0)
    (hda : da ∉ levelArrays 0) (htsb : tsb ∉ levelArrays 0)
    (hda_ma : da ≠ ma) (hda_pa : da ≠ pa) (hma_pa : ma ≠ pa)
    (htsb_pa : tsb ≠ pa) (htsb_ma : tsb ≠ ma) (htsb_da : tsb ≠ da) :
    TopScatterAll C hC φ ord G c w q ℓp htabF hbf Scr
      (topAtomsCom (arenaNames 0) pa ma da tsb
        (levelFml (Headline.headlineSetup C hC φ) 0).length
        (fun σa => memIdx (levelFml (Headline.headlineSetup C hC φ) 0) σa.β)
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ) 0)
      (fun σa => .get tsb (.lit (memIdx
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ) σa)))
      (topScatK n (∑ v : Fin n, G.degree v)
        (scatterAtoms (Headline.headlineSetup C hC φ).choice
          (Headline.headlineSetup C hC φ).φ
          (Headline.headlineSetup C hC φ).hφ)) := by
  -- the scratch names' freshness, spelled out
  simp only [levelArrays, List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hpa hma hda htsb
  obtain ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h, hpa_b⟩ := hpa
  obtain ⟨hma_o, hma_t, hma_c, hma_u, hma_h, hma_b⟩ := hma
  obtain ⟨hda_o, hda_t, hda_c, hda_u, hda_h, hda_b⟩ := hda
  obtain ⟨htsb_o, htsb_t, htsb_c, htsb_u, htsb_h, htsb_b⟩ := htsb
  have hpa5 : pa ∉ ([(arenaNames 0).off, (arenaNames 0).tgt,
      (arenaNames 0).col, (arenaNames 0).up, (arenaNames 0).hist] :
      List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h⟩
  have hma5 : ma ∉ ([(arenaNames 0).off, (arenaNames 0).tgt,
      (arenaNames 0).col, (arenaNames 0).up, (arenaNames 0).hist] :
      List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hma_o, hma_t, hma_c, hma_u, hma_h⟩
  have hda5 : da ∉ ([(arenaNames 0).off, (arenaNames 0).tgt,
      (arenaNames 0).col, (arenaNames 0).up, (arenaNames 0).hist] :
      List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hda_o, hda_t, hda_c, hda_u, hda_h⟩
  have htsb5 : tsb ∉ ([(arenaNames 0).off, (arenaNames 0).tgt,
      (arenaNames 0).col, (arenaNames 0).up, (arenaNames 0).hist] :
      List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨htsb_o, htsb_t, htsb_c, htsb_u, htsb_h⟩
  intro x hx
  obtain ⟨hnB, hnnB, hnFB, hMB⟩ := hB x hx
  have h1B : 1 < mcB q x := one_lt_mcB (three_le_length hx.1) hq
  refine ⟨fun σ =>
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ).length ≤ (σ.arrs tsb).length ∧
      ∀ k, (hk : k < (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ).length) →
        (σ.arrs tsb).getD k 0 = scatterBit G
          (Unroll.unrolledTables (Headline.headlineSetup C hC φ) ord 0
            (rootArena G (Impl.trivialColoring n)))
          ((scatterAtoms (Headline.headlineSetup C hC φ).choice
            (Headline.headlineSetup C hC φ).φ
            (Headline.headlineSetup C hC φ).hφ)[k]), ?_, ?_⟩
  · -- the stage's spec, from the fixed precondition
    have hstage := topAtomsCom_spec
      (A := Impl.ofArena (rootArena G (Impl.trivialColoring n))
        (htabF 0 (rootArena G (Impl.trivialColoring n))))
      (nm := arenaNames 0) (hb := hbf 0)
      (Fl := levelFml (Headline.headlineSetup C hC φ) 0)
      (T := Unroll.unrollAux (Headline.headlineSetup C hC φ) ord
        (Headline.headlineSetup C hC φ).depth 0
        (rootArena G (Impl.trivialColoring n)))
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ).length
      (fun σa => memIdx (levelFml (Headline.headlineSetup C hC φ) 0) σa.β)
      hnB hnnB hnFB hMB h1B (by decide) hda5 hma5 hpa5 hda_ma hda_pa hma_pa
      (by decide) (by decide) (Ne.symm hpa_b) (Ne.symm hma_b)
      (Ne.symm hda_b) htsb_pa htsb_ma htsb_da htsb_b htsb5
      (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ) 0 (by omega)
      (fun σa hmem => ⟨
        ⟨memIdx_lt (beta_mem_levelFml_zero _ hmem),
          getElem_memIdx (beta_mem_levelFml_zero _ hmem)⟩,
        hatomB x hx σa hmem⟩)
    refine (hstage.pre ?_).post ?_
    · rintro σ ⟨⟨hAW, hTab⟩, hScr⟩
      obtain ⟨h1, h2, h3, h4⟩ := hscrT σ hScr
      exact ⟨hAW, hTab, h1, h2, h3, h4⟩
    · rintro σ σ' - ⟨hSt', hcells, -, -⟩
      refine ⟨hSt'.2.2.2.2.2, ?_⟩
      intro k hk
      have h := hcells k hk
      rw [Nat.zero_add] at h
      exact h
  · -- the reads deliver the guard bits
    intro σ hQ σa hmem
    obtain ⟨hL, hcell⟩ := hQ
    have hk := memIdx_lt hmem
    have hlt' : memIdx (scatterAtoms (Headline.headlineSetup C hC φ).choice
        (Headline.headlineSetup C hC φ).φ
        (Headline.headlineSetup C hC φ).hφ) σa < (σ.arrs tsb).length := by
      omega
    have hval := hcell (memIdx (scatterAtoms
      (Headline.headlineSetup C hC φ).choice
      (Headline.headlineSetup C hC φ).φ
      (Headline.headlineSetup C hC φ).hφ) σa) hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt',
      Option.getD_some] at hval
    refine evalB_get (evalB_lit (by omega)) ?_ ?_
    · rw [List.getElem?_eq_getElem hlt', hval]
      simp only [getElem_memIdx hmem]
    · rw [scatterBit]
      split <;> omega
