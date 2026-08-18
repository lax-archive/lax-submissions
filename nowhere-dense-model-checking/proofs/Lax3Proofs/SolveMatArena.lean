import Mathlib.Data.List.GetD
import Lax3Proofs.ProgCodegenLayout
import Lax3Proofs.ImplRestrict

/-!
# F6b (part 1) — the root arena, materialized from the parsed word

The solve stages start where `ProgCodegenParse` stops: `CsrIn` — the
CSR word laid out in the frame. The driver's first object is the root
arena (`Driver.rootArena` over the parsed graph, `ImplFrontEnd`
§3), and this file is the machine's side of that step: what the root
`MArena` *is* in cells, the one piece of it the parse did not already
materialize, and the state predicate the driver blocks compose after.

## What the root arena is, in cells

`Impl.MArena`'s five fields, at the root (`rootMArena` below —
`ofArena (rootArena (parseGraph x) (trivialColoring _)) (fun _ _ => [])`):

* **carrier** `N = vertexCount x` — the header cell `"n"`;
* **graph** — the CSR arrays `"off"`/`"tgt"` themselves. The identity
  chain is landed: the zone reads are `offset`/`target`
  (`csrOffsets_getD`/`csrTargets_getD`, off `csr_decomp`), block
  membership over them is `blockMem` (`RootCsr.blockMem_iff`), and on
  an encoding that IS `G.Adj` (`blockMem_iff_adj`/`parseGraphAt_eq`),
  the graph of `Driver.rootArena` (`parse_rootArena`). No copy is made:
  copying `"off"`/`"tgt"` into arena-owned arrays would freeze an
  encoding for no consumer (F6/D-a) and pay `Θ(|x|)` for cells the
  frame already holds. `RootCsr.adj_iff` is the reading.
* **colors** — the axiom's palette is `L = 0`: no rows exist
  (`trivialColoring`, every `Fin 0`-indexed family is empty data);
* **renaming `up`** — the identity (`rootArena`'s
  `Function.Embedding.refl`). This is the one field the parse did not
  materialize: `matCom` writes the identity array into `"up"`
  (`RootCsr.up_getD` is the reading), so the blocks' channel
  maintenance starts from a real array rather than a convention —
  the child arenas' `up` are *computed* arrays, and the root's cell
  layout should not be a special case.
* **channel `hist`** — empty at the root (`rootArena`'s `hist = []`,
  no ancestor rounds): represented by *no cells*; the blocks' own
  channel arrays are still `ext`-declared zero under `MatIn.arrs`.

## The program and the descriptor

`matCom` is one counted scan (`Spec.forRangeZero`): `k := 0; while
k < n { up[k] := k; k := k+1 }`, cost `11·n + 6 ≤ matK x = 11·|x| + 6`
— the `O(|x|)` shape. `matCom_spec` takes the state from `CsrIn ext x`
to `MatIn ext x`:

* `RootCsr x σ` — **the cells the root arena pins**: `"n"`, `"m"`,
  `"off"`, `"tgt"`, `"up"`. This is the stability surface: the driver
  blocks may write anything else and the arena reading survives
  (`RootCsr.stable`, agreement form; `spec_rootCsr_frame`, the
  `Spec.frame` form — the block discharges the five non-membership
  side conditions by `decide` on its own syntax).
* the rest of `MatIn` — the parse's spent counters, every unnamed
  scalar still zero, every other array as `ext` declared, both tapes
  done — the fresh-scratch state block 0 of the driver starts from.

`ext` owes one new length, `hextUp : ext "up" = vertexCount x`, the
same convention as the parse's `hextOff`/`hextTgt` (F6/D-d: the solve
stages size their own arrays). The names `matCom` touches are
`matScalars`/`matArrays`; `matCom_ok` compiles it under `mcLayout`
whenever the extension lists carry `"k"` and `"up"`.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Codegen
open Lax13Proofs.Compile
open Lax11.GraphEncoding

variable {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}

/-! ## §1 Reading the zones back: the pinned arrays are the accessors -/

/-- The offset zone, read anywhere: entry `i` of `csrOffsets x` IS
`offset x i` — `csr_decomp`'s slice, at the cell. -/
theorem csrOffsets_getD (henc : EncodesGraph x n G) {i : ℕ}
    (hi : i ≤ vertexCount x) :
    (csrOffsets x).getD i 0 = offset x i := by
  have hlen := csrOffsets_length henc
  have hx := csr_decomp henc
  calc (csrOffsets x).getD i 0
      = (csrOffsets x ++ csrTargets x).getD i 0 :=
        (List.getD_append _ _ _ _ (by omega)).symm
    _ = ([vertexCount x, edgeCount x] ++ (csrOffsets x ++ csrTargets x)).getD
          (2 + i) 0 := by
        rw [List.getD_append_right [vertexCount x, edgeCount x]
          (csrOffsets x ++ csrTargets x) 0 (2 + i) (by simp)]
        congr 1
        simp
    _ = x.getD (2 + i) 0 := by rw [← hx]
    _ = offset x i := rfl

/-- The target zone, read anywhere: entry `j` of `csrTargets x` IS
`target x j` (out of range both sides read the default). -/
theorem csrTargets_getD (henc : EncodesGraph x n G) (j : ℕ) :
    (csrTargets x).getD j 0 = target x j := by
  have hoff := csrOffsets_length henc
  have htgt := csrTargets_length henc
  have hvc := henc.vertexCount_eq
  have hx := csr_decomp henc
  calc (csrTargets x).getD j 0
      = (csrOffsets x ++ csrTargets x).getD (vertexCount x + 1 + j) 0 := by
        rw [List.getD_append_right (csrOffsets x) (csrTargets x) 0
          (vertexCount x + 1 + j) (by omega)]
        congr 1
        omega
    _ = ([vertexCount x, edgeCount x] ++ (csrOffsets x ++ csrTargets x)).getD
          (2 + (vertexCount x + 1 + j)) 0 := by
        rw [List.getD_append_right [vertexCount x, edgeCount x]
          (csrOffsets x ++ csrTargets x) 0 (2 + (vertexCount x + 1 + j))
          (by simp)]
        congr 1
        simp
    _ = x.getD (3 + vertexCount x + j) 0 := by
        rw [← hx]
        congr 1
        omega
    _ = target x j := rfl

/-! ## §2 The root machine arena, and the cells that hold it -/

/-- **The root machine arena**: `Driver.rootArena` over the parsed
graph at the axiom's empty palette, with the empty channel — the
`MArena` whose machine representation `MatIn` pins. Its `up` is the
identity and its `hist` rows are all `[]`, by `rootArena`'s
definition. -/
noncomputable def rootMArena (x : List ℕ) (ℓp : ℕ) :
    Impl.MArena 0 (vertexCount x) ℓp :=
  Impl.ofArena
    (Driver.rootArena (Impl.parseGraph x) (Impl.trivialColoring (vertexCount x)))
    (fun _ _ => [])

/-- On an encoding (at the encoded carrier) the parse is exact, so the
root machine arena is the driver's root over `G` itself — the machine
record of `parse_rootArena`. A consumer at carrier `n` first rewrites
`n := vertexCount x` through `henc.vertexCount_eq`, exactly as
`parse_encodesGraph` does. -/
theorem rootMArena_eq {G : SimpleGraph (Fin (vertexCount x))}
    (henc : EncodesGraph x (vertexCount x) G) (ℓp : ℕ) :
    rootMArena x ℓp
      = Impl.ofArena
          (Driver.rootArena G (Impl.trivialColoring (vertexCount x)))
          (fun _ _ => []) := by
  unfold rootMArena
  rw [Impl.parseGraph, Impl.parseGraphAt_eq henc]

/-- **The cells the root arena pins** — the stability surface of the
whole solve stage: as long as a block leaves `"n"`, `"m"` and the three
arrays alone, the arena reading below (`adj_iff`, `up_getD`) survives
every scratch write the block makes. -/
structure RootCsr (x : List ℕ) (σ : Env) : Prop where
  /-- The carrier: the declared vertex count, in its header cell. -/
  n_eq : σ.vars "n" = vertexCount x
  /-- The declared edge count — the target zone's extent. -/
  m_eq : σ.vars "m" = edgeCount x
  /-- The offset zone, materialized by the parse. -/
  off_eq : σ.arrs "off" = csrOffsets x
  /-- The target zone, materialized by the parse. -/
  tgt_eq : σ.arrs "tgt" = csrTargets x
  /-- The root renaming: the identity array, materialized by `matCom`. -/
  up_eq : σ.arrs "up" = List.range (vertexCount x)

/-- **Stability, agreement form**: the reading depends on exactly five
cells. -/
theorem RootCsr.stable {σ σ' : Env} (h : RootCsr x σ)
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m")
    (hoff : σ'.arrs "off" = σ.arrs "off") (htgt : σ'.arrs "tgt" = σ.arrs "tgt")
    (hup : σ'.arrs "up" = σ.arrs "up") : RootCsr x σ' :=
  ⟨hn.trans h.n_eq, hm.trans h.m_eq, hoff.trans h.off_eq,
    htgt.trans h.tgt_eq, hup.trans h.up_eq⟩

/-- **Stability, `Spec` form**: any command that cannot assign `"n"` or
`"m"` and cannot store into the three arrays carries `RootCsr` across
its whole run — the five side conditions are `decide` on the block's
own syntax. This is how a driver block keeps the arena readable while
writing its scratch. -/
theorem spec_rootCsr_frame {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop}
    {c : Com} (h : Spec B P c Q K)
    (hn : "n" ∉ c.wvars) (hm : "m" ∉ c.wvars)
    (hoff : "off" ∉ c.warrs) (htgt : "tgt" ∉ c.warrs) (hup : "up" ∉ c.warrs) :
    Spec B (fun σ => P σ ∧ RootCsr x σ) c
      (fun σ σ' => Q σ σ' ∧ RootCsr x σ') K := by
  refine ((h.pre (fun σ hσ => hσ.1)).frame.post ?_)
  rintro σ σ' ⟨-, hroot⟩ ⟨hq, hfv, hfa, -, -⟩
  exact ⟨hq, hroot.stable (hfv _ hn) (hfv _ hm) (hfa _ hoff) (hfa _ htgt)
    (hfa _ hup)⟩

/-! ### The reading: the pinned cells are the root arena -/

/-- The root renaming, read off the pinned cell: the identity. -/
theorem RootCsr.up_getD {σ : Env} (h : RootCsr x σ) {i : ℕ}
    (hi : i < vertexCount x) : (σ.arrs "up").getD i 0 = i := by
  rw [h.up_eq, getD_eq_getElem (by simpa using hi), List.getElem_range]

/-- **Block membership is decided by the pinned cells**: the machine's
scan of `u`'s block — offsets read from `"off"`, targets from `"tgt"` —
decides exactly `Impl.blockMem x u v`, the raw relation the word
stores. -/
theorem RootCsr.blockMem_iff {σ : Env} (h : RootCsr x σ)
    (henc : EncodesGraph x n G) {u : ℕ} (hu : u < n) (v : ℕ) :
    Impl.blockMem x u v ↔
      ∃ jj, (σ.arrs "off").getD u 0 ≤ jj ∧
        jj < (σ.arrs "off").getD (u + 1) 0 ∧
        (σ.arrs "tgt").getD jj 0 = v := by
  have hvc := henc.vertexCount_eq
  rw [h.off_eq, h.tgt_eq, Impl.blockMem_iff,
    csrOffsets_getD henc (show u ≤ vertexCount x by omega),
    csrOffsets_getD henc (show u + 1 ≤ vertexCount x by omega)]
  constructor
  · rintro ⟨jj, h1, h2, h3⟩
    exact ⟨jj, h1, h2, by rw [csrTargets_getD henc jj]; exact h3⟩
  · rintro ⟨jj, h1, h2, h3⟩
    exact ⟨jj, h1, h2, by rw [← csrTargets_getD henc jj]; exact h3⟩

/-- **The pinned cells decide the root arena's adjacency** — the
identity chain, closed at the machine: on an encoding of `G`,
adjacency in `G` (the graph of `Driver.rootArena G col`, and of
`rootMArena` through `parseGraphAt_eq`) is one block scan of the
pinned `"off"`/`"tgt"` cells. The scan of `u`'s own block suffices —
no symmetrization pass: `adj_iff` makes the stored relation already
symmetric on encodings. -/
theorem RootCsr.adj_iff {σ : Env} (h : RootCsr x σ)
    (henc : EncodesGraph x n G) (u v : Fin n) :
    G.Adj u v ↔
      ∃ jj, (σ.arrs "off").getD (u : ℕ) 0 ≤ jj ∧
        jj < (σ.arrs "off").getD ((u : ℕ) + 1) 0 ∧
        (σ.arrs "tgt").getD jj 0 = (v : ℕ) := by
  rw [← Impl.blockMem_iff_adj henc u v]
  exact h.blockMem_iff henc u.isLt (v : ℕ)

/-! ## §3 The program -/

/-- The one scalar `matCom` touches: the scan counter. -/
def matScalars : List String := parseScalars ++ ["k"]

/-- The arrays the materialized state owns: the parse's two zones and
the root renaming. -/
def matArrays : List String := ["off", "tgt", "up"]

/-- **The materialization**: the identity renaming into `"up"` — the
one field of the root `MArena` the parse did not already leave in the
frame. One counted scan; the CSR arrays are deliberately *not* copied
(module docstring). -/
def matCom : Com :=
  .seq (.assign "k" (.lit 0))
    (.while (.lt (.var "k") (.var "n"))
      (.seq (.store "up" (.var "k") (.var "k"))
        (.assign "k" (.add (.var "k") (.lit 1)))))

/-- `matCom` compiles under the skeleton layout as soon as the
extension lists carry its names. -/
theorem matCom_ok {eS eA : List String} (hk : "k" ∈ eS) (hup : "up" ∈ eA) :
    Com.Ok (mcLayout eS eA) matCom := by
  simp [matCom, mcLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok, hk, hup]

/-- `matCom` never writes the output tape. -/
theorem matCom_noWrite : matCom.NoWrite := by
  simp [matCom, Com.NoWrite]

/-- `matCom`'s budget, in the word's own measure: `11·|x| + 6` — the
scan is `11·n + 6` and `n ≤ |x|`. -/
def matK (x : List ℕ) : ℕ := 11 * x.length + 6

/-! ## §4 The marshal descriptor -/

/-- **What the materialization leaves — the state the driver blocks
compose after** (the F6c seam): the root arena's pinned cells
(`RootCsr`), the parse's counters and the scan counter at their final
values, every unnamed cell still zero, every array outside
`matArrays` still as `ext` declared (the blocks' fresh scratch), both
tapes done. -/
structure MatIn (ext : String → ℕ) (x : List ℕ) (σ : Env) : Prop where
  /-- The root arena's cells — the part that must survive the blocks. -/
  root : RootCsr x σ
  /-- The parse's offset-scan length cell, untouched. -/
  np1_eq : σ.vars "np1" = vertexCount x + 1
  /-- The parse's target-scan length cell, untouched. -/
  mm_eq : σ.vars "mm" = 2 * edgeCount x
  /-- The parse's offset counter, untouched. -/
  i_eq : σ.vars "i" = vertexCount x + 1
  /-- The parse's target counter, untouched. -/
  j_eq : σ.vars "j" = 2 * edgeCount x
  /-- The materialization's scan counter, spent. -/
  k_eq : σ.vars "k" = vertexCount x
  /-- Every cell neither the parse nor the materialization names is
  still zero — `"verdict"` in particular. -/
  zero : ∀ y, y ∉ matScalars → σ.vars y = 0
  /-- Every array the state does not own is what `ext` declared: the
  blocks' scratch is fresh. -/
  arrs : ∀ b, b ∉ matArrays → σ.arrs b = List.replicate (ext b) 0
  /-- The input tape is spent. -/
  inp : σ.inp = []
  /-- Nothing has been written. -/
  out : σ.out = []

/-! ## §5 The specification -/

/-- The scan's invariant: the counter within range and the `"up"`
prefix below it already the identity. -/
private def upInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = vertexCount x ∧ σ.vars "k" ≤ vertexCount x ∧
    σ.arrs "up" = List.range (σ.vars "k")
      ++ List.replicate (vertexCount x - σ.vars "k") 0

/-- Writing the next identity entry extends the range prefix by one. -/
private theorem range_set (nn k : ℕ) (hk : k < nn) :
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
private theorem matBody_spec (B : ℕ) (x : List ℕ) (hnB : vertexCount x < B) :
    Spec B (fun σ => upInv x σ ∧ σ.vars "k" < vertexCount x)
      (.seq (.store "up" (.var "k") (.var "k"))
        (.assign "k" (.add (.var "k") (.lit 1))))
      (fun σ σ' => upInv x σ' ∧ σ'.vars "k" = σ.vars "k" + 1) 7 := by
  refine ((Spec.seq
    (Spec.store (a := "up") (i := .var "k") (e := .var "k")
      (idx := fun σ => σ.vars "k") (f := fun σ => σ.vars "k")
      (fun σ hσ => evalB_var (lt_trans hσ.2 hnB))
      (fun σ hσ => evalB_var (lt_trans hσ.2 hnB))
      (fun σ hσ => ?_))
    (Spec.assign (P := fun σ' => σ'.vars "k" < vertexCount x) (x := "k")
      (e := .add (.var "k") (.lit 1)) (f := fun σ' => σ'.vars "k" + 1)
      (fun σ' hσ' => ?_))
    ?_ ?_).mono (by norm_num [Expr.size]))
  · -- the store stays in the array
    obtain ⟨⟨-, hk, hup⟩, hlt⟩ := hσ
    rw [hup]
    simp only [List.length_append, List.length_range, List.length_replicate]
    omega
  · -- the increment evaluates below the bound
    have hk : σ'.vars "k" < B := lt_trans hσ' hnB
    have hres : σ'.vars "k" + 1 < B := by omega
    have hev := evalB_bin (op := .add) (e := Expr.var "k") (f := Expr.lit 1)
      (evalB_var hk) (evalB_lit (by omega)) (by simpa using hres)
    simpa using hev
  · -- the store lands in the increment's precondition
    rintro σ σ' ⟨-, hlt⟩ rfl
    simpa using hlt
  · -- the two updates re-establish the invariant
    rintro σ σ' σ'' ⟨⟨hn, hk, hup⟩, hlt⟩ rfl rfl
    refine ⟨⟨by simp [hn], by simp; omega, ?_⟩, by simp⟩
    have harr : (((σ.setArr "up" (σ.vars "k") (σ.vars "k")).setVar "k"
        ((σ.setArr "up" (σ.vars "k") (σ.vars "k")).vars "k" + 1)).arrs) "up"
        = (σ.arrs "up").set (σ.vars "k") (σ.vars "k") := by simp
    rw [harr, hup, range_set (vertexCount x) (σ.vars "k") hlt]
    simp

/-- **The materialization's `Spec`** (bookend 1 of the solve stage):
from the parse's descriptor on an encoding, `matCom` establishes
`MatIn` — the root arena's machine representation, ready for the
driver blocks — at cost `matK x = 11·|x| + 6`. `ext` owes the one new
array length `hextUp`, the parse's own convention. -/
theorem matCom_spec (B : ℕ) (ext : String → ℕ)
    (henc : EncodesGraph x n G) (hB : x.length + 1 < B)
    (hextUp : ext "up" = vertexCount x) :
    Spec B (CsrIn ext x) matCom (fun _ σ' => MatIn ext x σ') (matK x) := by
  have hl := henc.length_eq
  have hvc := henc.vertexCount_eq
  have hnB : vertexCount x < B := by omega
  have hloop := Spec.forRangeZero (B := B) "k" "n" (upInv x) (vertexCount x) 7 hnB
    (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (matBody_spec B x hnB)
  refine ((hloop.frame.pre ?_).post ?_).mono ?_
  · -- `CsrIn` gives the zeroed-counter invariant
    intro σ hσ
    refine ⟨by simpa using hσ.n_eq, by simp, ?_⟩
    simp only [vars_setVar, arrs_setVar]
    rw [hσ.arrs "up" (by decide) (by decide), hextUp]
    simp
  · -- the loop's exit state is the descriptor
    rintro σ σ' hσ ⟨⟨⟨hn, -, hup⟩, hk⟩, hfv, hfa, hfi, hfo⟩
    have hframe : ∀ y : String, y ≠ "k" → σ'.vars y = σ.vars y := by
      intro y hy
      exact hfv y (by simp [Com.wvars, hy])
    have haframe : ∀ b : String, b ≠ "up" → σ'.arrs b = σ.arrs b := by
      intro b hb
      exact hfa b (by simp [Com.warrs, hb])
    refine ⟨⟨hn, (hframe "m" (by decide)).trans hσ.m_eq,
        (haframe "off" (by decide)).trans hσ.off_eq,
        (haframe "tgt" (by decide)).trans hσ.tgt_eq, ?_⟩,
      (hframe "np1" (by decide)).trans hσ.np1_eq,
      (hframe "mm" (by decide)).trans hσ.mm_eq,
      (hframe "i" (by decide)).trans hσ.i_eq,
      (hframe "j" (by decide)).trans hσ.j_eq,
      hk, ?_, ?_, ?_, ?_⟩
    · -- the finished prefix is the whole identity array
      rw [hup, hk]
      simp
    · -- unnamed cells are still zero
      intro y hy
      have hyk : y ≠ "k" := fun h =>
        hy (h ▸ by simp [matScalars, parseScalars])
      rw [hframe y hyk]
      exact hσ.zero y fun hmem =>
        hy (by simp only [matScalars, List.mem_append]; exact Or.inl hmem)
    · -- unowned arrays are still as declared
      intro b hb
      have hboff : b ≠ "off" := fun h => hb (h ▸ by simp [matArrays])
      have hbtgt : b ≠ "tgt" := fun h => hb (h ▸ by simp [matArrays])
      have hbup : b ≠ "up" := fun h => hb (h ▸ by simp [matArrays])
      rw [haframe b hbup]
      exact hσ.arrs b hboff hbtgt
    · -- the input tape stays spent
      rw [hfi (by simp [Com.reads]), hσ.inp]
    · -- nothing written
      rw [hfo matCom_noWrite, hσ.out]
  · -- the budget: `11·n + 6 ≤ 11·|x| + 6`
    show (7 + 4) * vertexCount x + 6 ≤ matK x
    rw [matK]
    omega

end Lax3Proofs.Prog
