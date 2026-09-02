import Lax62Proofs.Refine.Codegen.Harness
import Lax3Proofs.ImplFrontEnd

/-!
# F6a — the CSR front end as an IMP+ program

The endorsed axiom hands the machine one word
`x = [n, m] ++ offsets ++ targets` (`Lax11.GraphEncoding.EncodesGraph`);
F2 (`ImplFrontEnd`) defined what parsing it *means* (`parseGraphAt`,
`parse_encodesGraph`) and what it may *cost* (`chargeParse`, exactly
`x.length` on an encoding). This file is the machine's side of that
seam: the parse as a concrete IMP+ command, priced, with a
`Reasoning.Spec` from `initEnv` into a marshal descriptor (`CsrIn`)
that the solve stages consume — the discharge of the front-end stage
of `ProgCodegen.lean`'s skeleton.

## The program

`parseCom` is harness material and nothing else
(`word-ram/proofs/Lax62Proofs/Refine/Codegen/Harness.lean`): read the
two header cells (`readScalars`), materialize the two counted scans'
lengths (`n+1` offsets, `2m` targets) into cells by one assignment
each, and run `readArr` twice. The arrays are pre-sized by `ext` —
the harness convention: `initEnv` gives `"off"` length `n+1` and
`"tgt"` length `2m`, and the correspondence is a hypothesis
(`hextOff`/`hextTgt`) exactly as in `readScalarsThenArr_spec`.

## The descriptor

`CsrIn ext x σ` says what the parse leaves: the header in `"n"`/`"m"`,
the offset zone in `"off"`, the target zone in `"tgt"`, the two length
cells and the two counters at their final values, every unnamed cell
still zero, every other array as `ext` declared, both tapes spent.
The zones are `csrOffsets x`/`csrTargets x` — sublists of the word —
so the bridge to F2's accessors is definitional: `offset x i` and
`target x j` are `x.getD` at the very positions these sublists carve
out, and a consumer indexes them through `csr_decomp` and the length
lemmas below. (The graph-level bridge is then F2's own
`blockMem`/`parseGraphAt_eq`: on an encoding the arrays determine
`G.Adj` exactly.)

## The price

`parseCom_spec` charges `12 · x.length`. Exact accounting:
`3 + 4 + (12(n+1)+6) + 4 + (12·2m+6) = 12·x.length − 1` on an encoding
(`x.length = 3 + n + 2m`), rounded up by one for the statement. Against
F2's abstract account this is `12` machine-side units per cell of the
word — `chargeParse`'s total is exactly `x.length` on an encoding
(`chargeParse_total_eq_length`), and `parse_budget_eq_chargeParse`
pins the ratio. The harness constant `12` is `readArr`'s per-entry
price (one `read` + `Fill.put`); F7's accounting absorbs it into the
layout constant's slack, linearly in `|x|`.

## Entries are small — the fact the value bound rides on

`entry_le_length`: **every entry of an encoding is at most the word's
length** — header numbers, offsets (monotone up to `2m`), targets
(vertices `< n`). This proves `GraphEncoding.lean`'s design note ("each
of those is smaller than the length of the word itself") and is what
lets `ProgCodegenLayout` spend the axiom's squared side condition as
the `hinp`/`FitsWords` pair.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax62Proofs.Codegen
open Lax11.GraphEncoding

/-! ## §1 The word, split into its three zones -/

/-- The offset zone of a CSR word: the `n+1` entries after the two
header cells. -/
def csrOffsets (x : List ℕ) : List ℕ := (x.drop 2).take (vertexCount x + 1)

/-- The target zone of a CSR word: everything after the offsets. -/
def csrTargets (x : List ℕ) : List ℕ := x.drop (3 + vertexCount x)

variable {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}

/-- An encoding is at least the header and the trailing offset long. -/
theorem three_le_length (h : EncodesGraph x n G) : 3 ≤ x.length := by
  rw [h.length_eq]; omega

theorem csrOffsets_length (h : EncodesGraph x n G) :
    (csrOffsets x).length = vertexCount x + 1 := by
  have hl := h.length_eq
  have hv := h.vertexCount_eq
  simp only [csrOffsets, List.length_take, List.length_drop]
  omega

theorem csrTargets_length (h : EncodesGraph x n G) :
    (csrTargets x).length = 2 * edgeCount x := by
  have hl := h.length_eq
  have hv := h.vertexCount_eq
  simp only [csrTargets, List.length_drop]
  omega

/-- **The word is its header, its offsets and its targets**, in that
order — the decomposition the tape reads follow. -/
theorem csr_decomp (h : EncodesGraph x n G) :
    x = [vertexCount x, edgeCount x] ++ (csrOffsets x ++ csrTargets x) := by
  have hl := h.length_eq
  have hv := h.vertexCount_eq
  have h0 : (0 : ℕ) < x.length := by omega
  have h1 : (1 : ℕ) < x.length := by omega
  have hzones : csrOffsets x ++ csrTargets x = x.drop 2 := by
    have hdd : x.drop (3 + vertexCount x) = (x.drop 2).drop (vertexCount x + 1) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [csrOffsets, csrTargets, hdd, List.take_append_drop]
  have hd0 : x.drop 0 = x[0] :: x.drop 1 := List.drop_eq_getElem_cons h0
  have hd1 : x.drop 1 = x[1] :: x.drop 2 := List.drop_eq_getElem_cons h1
  have hx0 : x[0] = vertexCount x := (getD_eq_getElem h0).symm
  have hx1 : x[1] = edgeCount x := (getD_eq_getElem h1).symm
  calc x = x.drop 0 := (List.drop_zero (l := x)).symm
    _ = x[0] :: x[1] :: x.drop 2 := by rw [hd0, hd1]
    _ = [vertexCount x, edgeCount x] ++ (csrOffsets x ++ csrTargets x) := by
        rw [hx0, hx1, hzones]
        rfl

/-- The offsets never pass the end of the target array. -/
theorem offset_le_last_of_le (h : EncodesGraph x n G) :
    ∀ i, i ≤ n → offset x i ≤ 2 * edgeCount x := by
  have key : ∀ d i, i + d = n → offset x i ≤ offset x n := by
    intro d
    induction d with
    | zero =>
        intro i hi
        rw [show i = n by omega]
    | succ d ih =>
        intro i hi
        have h1 : offset x i ≤ offset x (i + 1) := h.offset_mono i (by omega)
        have h2 : offset x (i + 1) ≤ offset x n := ih (i + 1) (by omega)
        omega
  intro i hi
  rw [← h.offset_last]
  exact key (n - i) i (by omega)

/-- **Every entry of an encoding is at most the word's length**: each
entry is a header number (`n`, `m`), an offset (`≤ 2m`), or a vertex
(`< n`), and each of those is at most `3 + n + 2m = x.length`. This is
the fact the axiom's word-size side condition is spent against in
`ProgCodegenLayout`. -/
theorem entry_le_length (h : EncodesGraph x n G) : ∀ v ∈ x, v ≤ x.length := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  have hl := h.length_eq
  have hvc := h.vertexCount_eq
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · -- the header
    interval_cases i
    · rw [← getD_eq_getElem hi]
      show vertexCount x ≤ x.length
      omega
    · rw [← getD_eq_getElem hi]
      show edgeCount x ≤ x.length
      omega
  · rcases Nat.lt_or_ge i (3 + n) with hi3 | hi3
    · -- the offset zone
      have hoi : x.getD i 0 = offset x (i - 2) := by
        rw [offset]
        congr 1
        omega
      rw [← getD_eq_getElem hi, hoi]
      have := offset_le_last_of_le h (i - 2) (by omega)
      omega
    · -- the target zone
      have hj : i - (3 + n) < 2 * edgeCount x := by omega
      have hti : x.getD i 0 = target x (i - (3 + n)) := by
        rw [target, hvc]
        congr 1
        omega
      rw [← getD_eq_getElem hi, hti]
      have := h.target_lt _ hj
      omega

theorem mem_csrOffsets_le (h : EncodesGraph x n G) :
    ∀ v ∈ csrOffsets x, v ≤ x.length := fun v hv =>
  entry_le_length h v (List.drop_subset _ _ (List.take_subset _ _ hv))

theorem mem_csrTargets_le (h : EncodesGraph x n G) :
    ∀ v ∈ csrTargets x, v ≤ x.length := fun v hv =>
  entry_le_length h v (List.drop_subset _ _ hv)

/-! ## §2 The program -/

/-- The scalar cells the parse writes or spends: the two header cells,
the two materialized lengths, the two scan counters and the two scan
temporaries. (`"verdict"` is deliberately not here: the parse leaves it
zero, and the descriptor's zero clause says so.) -/
def parseScalars : List String := ["n", "m", "np1", "mm", "i", "t", "j", "u"]

/-- **The front end, as IMP+**: read the header, materialize the two
scan lengths, scan the offset zone into `"off"`, scan the target zone
into `"tgt"`. Harness material and nothing else. -/
def parseCom : Com :=
  .seq (readScalars ["n", "m"])
    (.seq (.assign "np1" (.add (.var "n") (.lit 1)))
      (.seq (readArr "off" "i" "np1" "t")
        (.seq (.assign "mm" (.add (.var "m") (.var "m")))
          (readArr "tgt" "j" "mm" "u"))))

/-! ## §3 The marshal descriptor -/

/-- **What the parse leaves behind** — the precondition the solve
stages' specification is written against (`ProgCodegen.SolveSpec`).
The header is in its two cells, the two zones are materialized in
their arrays, the length cells and the counters stand at their final
values, every unnamed cell is still zero (the two temporaries `"t"`,
`"u"` are spent and excluded), every other array is what `ext`
declared, and both tapes are done. -/
structure CsrIn (ext : String → ℕ) (x : List ℕ) (σ : Env) : Prop where
  /-- The declared vertex count, in its header cell. -/
  n_eq : σ.vars "n" = vertexCount x
  /-- The declared edge count, in its header cell. -/
  m_eq : σ.vars "m" = edgeCount x
  /-- The offset zone, materialized. -/
  off_eq : σ.arrs "off" = csrOffsets x
  /-- The target zone, materialized. -/
  tgt_eq : σ.arrs "tgt" = csrTargets x
  /-- The offset scan's length cell. -/
  np1_eq : σ.vars "np1" = vertexCount x + 1
  /-- The target scan's length cell. -/
  mm_eq : σ.vars "mm" = 2 * edgeCount x
  /-- The offset scan's counter, at the end. -/
  i_eq : σ.vars "i" = vertexCount x + 1
  /-- The target scan's counter, at the end. -/
  j_eq : σ.vars "j" = 2 * edgeCount x
  /-- Every cell the parse does not name is still zero. -/
  zero : ∀ y, y ∉ parseScalars → σ.vars y = 0
  /-- Every other array is what `ext` declared. -/
  arrs : ∀ b, b ≠ "off" → b ≠ "tgt" → σ.arrs b = List.replicate (ext b) 0
  /-- The input tape is spent. -/
  inp : σ.inp = []
  /-- Nothing has been written. -/
  out : σ.out = []

/-! ## §4 The specification -/

/-- **The front end's `Spec`** (stage 1 of the skeleton, discharged):
from `initEnv ext x` on an encoding of `G`, `parseCom` establishes the
descriptor at a cost of `12 · x.length`. The bound `B` is asked for
`x.length + 1 < B` — every value the parse stores (entries, lengths,
counters) is at most `x.length + 1` (`entry_le_length`), which the
layout file's `mcB` satisfies with room. -/
theorem parseCom_spec (B : ℕ) (ext : String → ℕ)
    (henc : EncodesGraph x n G) (hB : x.length + 1 < B)
    (hextOff : ext "off" = vertexCount x + 1)
    (hextTgt : ext "tgt" = 2 * edgeCount x) :
    Spec B (fun σ => σ = initEnv ext x) parseCom
      (fun _ σ' => CsrIn ext x σ') (12 * x.length) := by
  have hl := henc.length_eq
  have hvc := henc.vertexCount_eq
  have h3 : 3 ≤ x.length := three_le_length henc
  have h1B : 1 < B := by omega
  have hvcB : vertexCount x < B := by omega
  have hvc1B : vertexCount x + 1 < B := by omega
  have hecB : edgeCount x < B := by omega
  have h2ecB : 2 * edgeCount x < B := by omega
  have hoffs_len : (csrOffsets x).length = vertexCount x + 1 := csrOffsets_length henc
  have htgts_len : (csrTargets x).length = 2 * edgeCount x := csrTargets_length henc
  have hoffs_B : ∀ v ∈ csrOffsets x, v < B := fun v hv =>
    lt_of_le_of_lt (mem_csrOffsets_le henc v hv) (by omega)
  have htgts_B : ∀ v ∈ csrTargets x, v < B := fun v hv =>
    lt_of_le_of_lt (mem_csrTargets_le henc v hv) (by omega)
  -- Phase 1: the header.
  have h1 : Spec B (fun σ => σ = initEnv ext x) (readScalars ["n", "m"])
      (fun _ σ' => σ'.vars "n" = vertexCount x ∧ σ'.vars "m" = edgeCount x ∧
        (∀ y, y ∉ (["n", "m"] : List String) → σ'.vars y = 0) ∧
        (∀ b, σ'.arrs b = List.replicate (ext b) 0) ∧
        σ'.inp = csrOffsets x ++ csrTargets x ∧ σ'.out = []) 3 := by
    refine (((readScalars_initEnv_rest_spec B ext ["n", "m"]
        [vertexCount x, edgeCount x] (csrOffsets x ++ csrTargets x)
        (by simp) rfl).pre ?_).post ?_).mono (by simp)
    · intro σ hσ
      rw [hσ]
      exact congrArg (initEnv ext) (csr_decomp henc)
    · rintro σ σ' - ⟨hzip, hzero, harr, hinp, hout⟩
      exact ⟨by simpa using hzip ("n", vertexCount x) (by simp),
        by simpa using hzip ("m", edgeCount x) (by simp), hzero, harr, hinp, hout⟩
  -- Phase 2: the offset scan's length cell.
  have h2 : Spec B
      (fun σ => σ.vars "n" = vertexCount x ∧ σ.vars "m" = edgeCount x ∧
        (∀ y, y ∉ (["n", "m"] : List String) → σ.vars y = 0) ∧
        (∀ b, σ.arrs b = List.replicate (ext b) 0) ∧
        σ.inp = csrOffsets x ++ csrTargets x ∧ σ.out = [])
      (.assign "np1" (.add (.var "n") (.lit 1)))
      (fun _ σ' => σ'.vars "n" = vertexCount x ∧ σ'.vars "m" = edgeCount x ∧
        σ'.vars "np1" = vertexCount x + 1 ∧
        (∀ y, y ∉ (["n", "m", "np1"] : List String) → σ'.vars y = 0) ∧
        (∀ b, σ'.arrs b = List.replicate (ext b) 0) ∧
        σ'.inp = csrOffsets x ++ csrTargets x ∧ σ'.out = []) 4 := by
    refine ((Spec.assign (f := fun _ => vertexCount x + 1)
        (x := "np1") (e := .add (.var "n") (.lit 1)) ?_).post ?_).mono
        (by norm_num [Expr.size])
    · rintro σ ⟨hn, -, -, -, -, -⟩
      have hev := evalB_bin (op := .add) (e := Expr.var "n") (f := Expr.lit 1)
        (evalB_var (by rw [hn]; exact hvcB)) (evalB_lit h1B)
        (by rw [hn]; simpa using hvc1B)
      rw [hn] at hev
      simpa using hev
    · rintro σ σ' ⟨hn, hm, hzero, harr, hinp, hout⟩ rfl
      refine ⟨by simp [hn], by simp [hm], by simp, fun y hy => ?_,
        fun b => by simpa using harr b, by simpa using hinp, by simpa using hout⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨hy1, hy2, hy3⟩ := hy
      rw [vars_setVar, if_neg hy3]
      exact hzero y (by simp [hy1, hy2])
  -- Phase 3: the offset zone.
  have h3s : Spec B
      (fun σ => σ.vars "n" = vertexCount x ∧ σ.vars "m" = edgeCount x ∧
        σ.vars "np1" = vertexCount x + 1 ∧
        (∀ y, y ∉ (["n", "m", "np1"] : List String) → σ.vars y = 0) ∧
        (∀ b, σ.arrs b = List.replicate (ext b) 0) ∧
        σ.inp = csrOffsets x ++ csrTargets x ∧ σ.out = [])
      (readArr "off" "i" "np1" "t")
      (fun _ σ' => σ'.vars "n" = vertexCount x ∧ σ'.vars "m" = edgeCount x ∧
        σ'.vars "np1" = vertexCount x + 1 ∧ σ'.vars "i" = vertexCount x + 1 ∧
        σ'.arrs "off" = csrOffsets x ∧
        (∀ y, y ∉ (["n", "m", "np1", "i", "t"] : List String) → σ'.vars y = 0) ∧
        (∀ b, b ≠ "off" → σ'.arrs b = List.replicate (ext b) 0) ∧
        σ'.inp = csrTargets x ∧ σ'.out = [])
      (12 * (vertexCount x + 1) + 6) := by
    refine ((((readArr_spec B "off" "i" "np1" "t" (csrOffsets x) (csrTargets x)
        (by decide) (by decide) (by decide) (by rw [hoffs_len]; exact hvc1B)
        hoffs_B).frame).pre ?_).post ?_).mono (le_of_eq (by rw [hoffs_len]))
    · rintro σ ⟨hn, hm, hnp1, hzero, harr, hinp, hout⟩
      refine ⟨?_, ?_, hinp⟩
      · rw [harr "off", hextOff, hoffs_len]
        simp
      · rw [hnp1, hoffs_len]
    · rintro σ σ' ⟨hn, hm, hnp1, hzero, harr, hinp, hout⟩
        ⟨⟨hoff, hinp', hi⟩, hfv, hfa, -, hfo⟩
      refine ⟨by rw [hfv "n" (by simp)]; exact hn,
        by rw [hfv "m" (by simp)]; exact hm,
        by rw [hfv "np1" (by simp)]; exact hnp1,
        by rw [hi, hoffs_len],
        hoff, fun y hy => ?_,
        fun b hb => by rw [hfa b (by simp [hb])]; exact harr b,
        hinp',
        by rw [hfo (by simp)]; exact hout⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
      rw [hfv y (by simp [hy4, hy5])]
      exact hzero y (by simp [hy1, hy2, hy3])
  -- Phase 4: the target scan's length cell.
  have h4 : Spec B
      (fun σ => σ.vars "n" = vertexCount x ∧ σ.vars "m" = edgeCount x ∧
        σ.vars "np1" = vertexCount x + 1 ∧ σ.vars "i" = vertexCount x + 1 ∧
        σ.arrs "off" = csrOffsets x ∧
        (∀ y, y ∉ (["n", "m", "np1", "i", "t"] : List String) → σ.vars y = 0) ∧
        (∀ b, b ≠ "off" → σ.arrs b = List.replicate (ext b) 0) ∧
        σ.inp = csrTargets x ∧ σ.out = [])
      (.assign "mm" (.add (.var "m") (.var "m")))
      (fun _ σ' => σ'.vars "n" = vertexCount x ∧ σ'.vars "m" = edgeCount x ∧
        σ'.vars "np1" = vertexCount x + 1 ∧ σ'.vars "i" = vertexCount x + 1 ∧
        σ'.vars "mm" = 2 * edgeCount x ∧ σ'.arrs "off" = csrOffsets x ∧
        (∀ y, y ∉ (["n", "m", "np1", "mm", "i", "t"] : List String) → σ'.vars y = 0) ∧
        (∀ b, b ≠ "off" → σ'.arrs b = List.replicate (ext b) 0) ∧
        σ'.inp = csrTargets x ∧ σ'.out = []) 4 := by
    refine ((Spec.assign (f := fun _ => edgeCount x + edgeCount x)
        (x := "mm") (e := .add (.var "m") (.var "m")) ?_).post ?_).mono
        (by norm_num [Expr.size])
    · rintro σ ⟨-, hm, -, -, -, -, -, -, -⟩
      have hev := evalB_bin (op := .add) (e := Expr.var "m") (f := Expr.var "m")
        (evalB_var (by rw [hm]; exact hecB)) (evalB_var (by rw [hm]; exact hecB))
        (by rw [hm]; simpa using by omega)
      rw [hm] at hev
      simpa using hev
    · rintro σ σ' ⟨hn, hm, hnp1, hi, hoff, hzero, harr, hinp, hout⟩ rfl
      refine ⟨by simp [hn], by simp [hm], by simp [hnp1], by simp [hi],
        by simp [two_mul], by simpa using hoff, fun y hy => ?_,
        fun b hb => by simpa using harr b hb, by simpa using hinp,
        by simpa using hout⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
      rw [vars_setVar, if_neg hy4]
      exact hzero y (by simp [hy1, hy2, hy3, hy5, hy6])
  -- Phase 5: the target zone.
  have h5 : Spec B
      (fun σ => σ.vars "n" = vertexCount x ∧ σ.vars "m" = edgeCount x ∧
        σ.vars "np1" = vertexCount x + 1 ∧ σ.vars "i" = vertexCount x + 1 ∧
        σ.vars "mm" = 2 * edgeCount x ∧ σ.arrs "off" = csrOffsets x ∧
        (∀ y, y ∉ (["n", "m", "np1", "mm", "i", "t"] : List String) → σ.vars y = 0) ∧
        (∀ b, b ≠ "off" → σ.arrs b = List.replicate (ext b) 0) ∧
        σ.inp = csrTargets x ∧ σ.out = [])
      (readArr "tgt" "j" "mm" "u")
      (fun _ σ' => CsrIn ext x σ') (12 * (2 * edgeCount x) + 6) := by
    refine ((((readArr_spec B "tgt" "j" "mm" "u" (csrTargets x) []
        (by decide) (by decide) (by decide) (by rw [htgts_len]; exact h2ecB)
        htgts_B).frame).pre ?_).post ?_).mono (le_of_eq (by rw [htgts_len]))
    · rintro σ ⟨hn, hm, hnp1, hi, hmm, hoff, hzero, harr, hinp, hout⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [harr "tgt" (by decide), hextTgt, htgts_len]
        simp
      · rw [hmm, htgts_len]
      · rw [hinp, List.append_nil]
    · rintro σ σ' ⟨hn, hm, hnp1, hi, hmm, hoff, hzero, harr, hinp, hout⟩
        ⟨⟨htgt, hinp', hj⟩, hfv, hfa, -, hfo⟩
      refine ⟨by rw [hfv "n" (by simp)]; exact hn,
        by rw [hfv "m" (by simp)]; exact hm,
        by rw [hfa "off" (by simp)]; exact hoff,
        htgt,
        by rw [hfv "np1" (by simp)]; exact hnp1,
        by rw [hfv "mm" (by simp)]; exact hmm,
        by rw [hfv "i" (by simp)]; exact hi,
        by rw [hj, htgts_len],
        fun y hy => ?_,
        fun b hb1 hb2 => by rw [hfa b (by simp [hb2])]; exact harr b hb1,
        hinp',
        by rw [hfo (by simp)]; exact hout⟩
      simp only [parseScalars, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hy
      obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8⟩ := hy
      rw [hfv y (by simp [hy7, hy8])]
      exact hzero y (by simp [hy1, hy2, hy3, hy4, hy5, hy6])
  -- The chain.
  refine (Spec.seq h1 (Spec.seq h2 (Spec.seq h3s (Spec.seq h4 h5
        (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
      (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
    (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq))
    (fun _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq)).mono (by omega)

/-- The machine budget against F2's abstract account: `12 · x.length`
is twelve machine-side units per cell of `chargeParse`'s total, which
on an encoding is exactly `x.length`. -/
theorem parse_budget_eq_chargeParse (henc : EncodesGraph x n G) :
    12 * x.length = 12 * ((Impl.chargeParse x).toFun "parse.header"
      + (Impl.chargeParse x).toFun "parse.offsets"
      + (Impl.chargeParse x).toFun "parse.targets") := by
  rw [Impl.chargeParse_total_eq_length henc]

end Lax3Proofs.Prog
