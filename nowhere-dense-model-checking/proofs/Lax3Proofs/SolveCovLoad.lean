import Lax3Proofs.SolveGlueLoad

/-!
# F6c10b (residual 2) — the deduplicating CSR pass, discharged

`SolveGlueLoad` §1 names one residual, **`RootCsrLoadAll`**: from
`MatIn` (the materialized root), leave in the level-0 CSR pair a valid
deduplicated prefix (`CsrPrefix`) of `G` with the slot count in the
level-0 `nS` cell, touching nothing but the pair, the cell and the
declared scratch. This file discharges it with a concrete program and
budget.

## The two scope checks (asked by the task packet, answered here)

* **Self-loops**: `EncodesGraph.adj_iff` is an *iff* — a block entry
  `v ∈ block(v)` would force `G.Adj v v`, contradicting a
  `SimpleGraph`'s irreflexivity. Admissible encodings carry **no
  self-loops**; the pass owes no loop-dropping.
* **Symmetry**: for the same reason, `w ∈ block(u) ↔ G.Adj u w ↔
  G.Adj w u ↔ u ∈ block(w)` — both directions of every edge are
  **automatically present** (the encoding's own docstring says so:
  "that is automatic, since adjacency in a simple graph is
  symmetric"). No symmetrization pass is owed. The pass owes exactly
  the within-block deduplication and nothing more.

## The program

One owner-advancing pass (`Lib.Csr.ownerScan_spec`'s shape) over the
root target zone, with a **row-stamped mark array**: `cl.d[w] = u + 1`
records that `w` was already emitted in row `u`, so no re-zeroing
between rows is ever paid — stamps of earlier rows are `≤ u`, fresh
rows test against a value no cell holds. Per slot: read the target;
if unmarked, stamp it, append it to the level-0 target prefix, advance
the write pointer. At each row boundary the write pointer is recorded
as the next level-0 offset. A tail scan closes the offsets of trailing
empty rows, and the slot count lands in the level-0 `nS` cell.

`O(n + m)`, exactly: `csrLoadK x = 70·|x| + 20`, one turn per slot
plus one per row (`pay_le`'s amortization), never `n·m`.

## The abstract output

Row `v` of the output is `dedF` (first-occurrence deduplication, a
`foldl`) of the input block; offsets are the prefix sums. `GraphCsr`'s
three demands are read off `dedF`: `Nodup` rows, membership unchanged
(hence `adj_iff` transports), and the pinned slot count `Σ deg`.

The headline `rootCsrLoadAll_csrLoadCom` concludes the residual
**verbatim**, from hypotheses only of the F7-suppliable kinds: `1 ≤ q`
(the word-bound constant is positive — `mcB` then dominates `|x|`),
and the three `ext` length conventions at the pass's regions
(`n + 1` offset cells, `2m` target cells, `n` mark cells).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax11.GraphEncoding

/-! ## §1 First-occurrence deduplication -/

/-- One step of the deduplicating fold: append `a` unless seen. -/
def dstep (acc : List ℕ) (a : ℕ) : List ℕ := if a ∈ acc then acc else acc ++ [a]

/-- **First-occurrence deduplication**: the list of first occurrences,
in order — exactly what the mark-array pass emits. -/
def dedF (l : List ℕ) : List ℕ := l.foldl dstep []

private theorem foldl_dstep_mem (l : List ℕ) :
    ∀ (acc : List ℕ) (b : ℕ), b ∈ l.foldl dstep acc ↔ b ∈ acc ∨ b ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro acc b
      rw [List.foldl_cons, ih]
      by_cases h : a ∈ acc
      · simp only [dstep, if_pos h, List.mem_cons]
        constructor
        · rintro (hb | hb)
          · exact Or.inl hb
          · exact Or.inr (Or.inr hb)
        · rintro (hb | rfl | hb)
          · exact Or.inl hb
          · exact Or.inl h
          · exact Or.inr hb
      · simp only [dstep, if_neg h, List.mem_append, List.mem_cons]
        tauto

private theorem foldl_dstep_nodup (l : List ℕ) :
    ∀ acc : List ℕ, acc.Nodup → (l.foldl dstep acc).Nodup := by
  induction l with
  | nil => intro acc h; simpa using h
  | cons a l ih =>
      intro acc h
      rw [List.foldl_cons]
      refine ih _ ?_
      by_cases ha : a ∈ acc
      · simpa [dstep, if_pos ha] using h
      · rw [dstep, if_neg ha, List.nodup_append]
        refine ⟨h, List.nodup_singleton a, ?_⟩
        intro y hy z hz
        rw [List.mem_singleton] at hz
        subst hz
        exact fun heq => ha (heq ▸ hy)

private theorem foldl_dstep_length (l : List ℕ) :
    ∀ acc : List ℕ, (l.foldl dstep acc).length ≤ acc.length + l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro acc
      rw [List.foldl_cons]
      refine le_trans (ih _) ?_
      by_cases ha : a ∈ acc
      · rw [dstep, if_pos ha]
        simp only [List.length_cons]
        omega
      · rw [dstep, if_neg ha]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

theorem mem_dedF {l : List ℕ} {b : ℕ} : b ∈ dedF l ↔ b ∈ l := by
  rw [dedF, foldl_dstep_mem]
  simp

theorem nodup_dedF (l : List ℕ) : (dedF l).Nodup :=
  foldl_dstep_nodup l [] (by simp)

theorem length_dedF_le (l : List ℕ) : (dedF l).length ≤ l.length := by
  have := foldl_dstep_length l []
  simpa [dedF] using this

@[simp] theorem dedF_nil : dedF [] = [] := rfl

/-- The snoc step of the fold — the exact case split the mark test
makes. -/
theorem dedF_snoc (l : List ℕ) (a : ℕ) :
    dedF (l ++ [a]) = if a ∈ dedF l then dedF l else dedF l ++ [a] := by
  rw [dedF, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem dedF_snoc_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) :
    dedF (l ++ [a]) = dedF l := by
  rw [dedF_snoc, if_pos (mem_dedF.mpr h)]

theorem dedF_snoc_not_mem {l : List ℕ} {a : ℕ} (h : a ∉ l) :
    dedF (l ++ [a]) = dedF l ++ [a] := by
  rw [dedF_snoc, if_neg (fun hc => h (mem_dedF.mp hc))]

/-! ## §2 List plumbing -/

private theorem arrOf_succ (k : ℕ) (f : ℕ → ℕ) :
    arrOf (k + 1) f = arrOf k f ++ [f k] := by
  simp [arrOf, List.range_succ]

private theorem mem_arrOf {w k : ℕ} {f : ℕ → ℕ} :
    w ∈ arrOf k f ↔ ∃ i, i < k ∧ f i = w := by
  simp [arrOf]

/-- Extending a written prefix by one cell: the store at the prefix's
length lands the next entry, the zero pool shrinks by one. -/
private theorem replicate_cons {k : ℕ} (hk : 1 ≤ k) :
    List.replicate k (0 : ℕ) = 0 :: List.replicate (k - 1) 0 := by
  conv_lhs => rw [show k = (k - 1) + 1 by omega]
  rw [List.replicate_succ]

private theorem set_append_replicate {l : List ℕ} {k v : ℕ} (hk : 1 ≤ k) :
    (l ++ List.replicate k (0 : ℕ)).set l.length v
      = (l ++ [v]) ++ List.replicate (k - 1) 0 := by
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, replicate_cons hk,
    List.set_cons_zero]
  simp

private theorem replicate_set_zero {k v : ℕ} (hk : 1 ≤ k) :
    (List.replicate k (0 : ℕ)).set 0 v = [v] ++ List.replicate (k - 1) 0 := by
  rw [replicate_cons hk, List.set_cons_zero]
  rfl

private theorem getElem?_of_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

private theorem getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  rw [getD_eq_getElem (by simpa using h), List.getElem_set]
  simp

private theorem getD_set_ne {l : List ℕ} {i k v : ℕ} (h : i ≠ k) :
    (l.set i v).getD k 0 = l.getD k 0 := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · rw [getD_eq_getElem (by simpa using hk), getD_eq_getElem hk,
      List.getElem_set, if_neg h]
  · rw [List.getD_eq_default _ _ (by simpa using hk),
      List.getD_eq_default _ _ (by simpa using hk)]

/-! ## §3 The abstract output: deduplicated rows and their offsets -/

variable {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}

/-- The processed part of row `u`, up to slot `j`. -/
def clSlice (x : List ℕ) (u j : ℕ) : List ℕ :=
  arrOf (j - offset x u) (fun k => target x (offset x u + k))

/-- The deduplicated output row of `v`: `dedF` of the whole block. -/
def clRow (x : List ℕ) (v : ℕ) : List ℕ := clSlice x v (offset x (v + 1))

/-- The output rows of the first `u` vertices, concatenated. -/
def clPref (x : List ℕ) (u : ℕ) : List ℕ :=
  (List.range u).flatMap (fun v => dedF (clRow x v))

/-- What the pass has emitted at owner `u`, pointer `j`: the finished
rows, then the deduplication of the current row's processed part. -/
def clEmit (x : List ℕ) (u j : ℕ) : List ℕ :=
  clPref x u ++ dedF (clSlice x u j)

/-- The output offsets: prefix sums of the deduplicated row lengths,
clamped at the carrier. -/
def clOff (x : List ℕ) (n : ℕ) (v : ℕ) : ℕ := (clPref x (min v n)).length

@[simp] theorem clPref_zero : clPref x 0 = [] := by simp [clPref]

theorem clPref_succ (u : ℕ) :
    clPref x (u + 1) = clPref x u ++ dedF (clRow x u) := by
  simp [clPref, List.range_succ]

theorem clPref_prefix {a b : ℕ} (hab : a ≤ b) :
    ∃ t, clPref x b = clPref x a ++ t := by
  induction b with
  | zero =>
      obtain rfl : a = 0 := by omega
      exact ⟨[], by simp⟩
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · obtain ⟨t, ht⟩ := ih (by omega)
        exact ⟨t ++ dedF (clRow x b), by rw [clPref_succ, ht, List.append_assoc]⟩
      · obtain rfl : a = b + 1 := by omega
        exact ⟨[], by simp⟩

theorem clSlice_zero_width {u j : ℕ} (h : j ≤ offset x u) : clSlice x u j = [] := by
  simp [clSlice, show j - offset x u = 0 by omega, arrOf]

@[simp] theorem clEmit_diag (u : ℕ) : clEmit x u (offset x u) = clPref x u := by
  rw [clEmit, clSlice_zero_width le_rfl]
  simp

theorem clEmit_row_end (u : ℕ) :
    clEmit x u (offset x (u + 1)) = clPref x (u + 1) := by
  rw [clEmit, clPref_succ]
  rfl

/-- The slice grows by one target per slot. -/
theorem clSlice_snoc {u j : ℕ} (hlo : offset x u ≤ j) :
    clSlice x u (j + 1) = clSlice x u j ++ [target x j] := by
  rw [clSlice, show j + 1 - offset x u = (j - offset x u) + 1 by omega, arrOf_succ,
    show offset x u + (j - offset x u) = j by omega]
  rfl

theorem mem_clSlice {u j w : ℕ} (hlo : offset x u ≤ j) :
    w ∈ clSlice x u j ↔ ∃ p, offset x u ≤ p ∧ p < j ∧ target x p = w := by
  rw [clSlice, mem_arrOf]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨offset x u + i, by omega, by omega, rfl⟩
  · rintro ⟨p, h1, h2, rfl⟩
    exact ⟨p - offset x u, by omega, by rw [show offset x u + (p - offset x u) = p by omega]⟩

/-! ### The offsets, as an encoding is read -/

section Encoding

variable (henc : EncodesGraph x n G)

include henc in
/-- The offsets do not decrease, over any distance. -/
theorem offset_mono_le {i k : ℕ} (hik : i ≤ k) (hk : k ≤ n) :
    offset x i ≤ offset x k := by
  induction k with
  | zero =>
      obtain rfl : i = 0 := by omega
      exact le_rfl
  | succ k ih =>
      rcases Nat.lt_or_ge i (k + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (henc.offset_mono k (by omega))
      · obtain rfl : i = k + 1 := by omega
        exact le_rfl

include henc in
theorem offset_le_ns {i : ℕ} (hi : i ≤ n) : offset x i ≤ 2 * edgeCount x := by
  have h := offset_mono_le henc hi le_rfl
  have hlast := henc.offset_last
  omega

include henc in
theorem offset_zero' : offset x 0 = 0 := henc.offset_zero

include henc in
/-- The emitted prefix never outgrows the offsets: `|clPref u| ≤ off u`. -/
theorem clPref_length_le {u : ℕ} (hu : u ≤ n) :
    (clPref x u).length ≤ offset x u := by
  induction u with
  | zero => simp [henc.offset_zero]
  | succ u ih =>
      rw [clPref_succ, List.length_append]
      have h1 := ih (by omega)
      have h2 : (dedF (clRow x u)).length ≤ offset x (u + 1) - offset x u := by
        refine le_trans (length_dedF_le _) ?_
        simp [clRow, clSlice]
      have h3 : offset x u ≤ offset x (u + 1) :=
        offset_mono_le henc (by omega) hu
      omega

include henc in
/-- The emitted list never outgrows the slot pointer: `|clEmit u j| ≤ j`. -/
theorem clEmit_length_le {u j : ℕ} (hu : u ≤ n) (hlo : offset x u ≤ j) :
    (clEmit x u j).length ≤ j := by
  rw [clEmit, List.length_append]
  have h1 := clPref_length_le henc hu
  have h2 : (dedF (clSlice x u j)).length ≤ j - offset x u := by
    refine le_trans (length_dedF_le _) ?_
    simp [clSlice]
  omega

theorem clOff_zero : clOff x n 0 = 0 := by simp [clOff]

theorem clOff_eq_length {v : ℕ} (hv : v ≤ n) :
    clOff x n v = (clPref x v).length := by
  rw [clOff, Nat.min_eq_left hv]

theorem clOff_succ {v : ℕ} (hv : v < n) :
    clOff x n (v + 1) = clOff x n v + (dedF (clRow x v)).length := by
  rw [clOff_eq_length (by omega), clOff_eq_length (by omega), clPref_succ,
    List.length_append]

theorem clOff_mono {i k : ℕ} (hik : i ≤ k) : clOff x n i ≤ clOff x n k := by
  obtain ⟨t, ht⟩ := clPref_prefix (x := x) (a := min i n) (b := min k n)
    (min_le_min hik (le_refl n))
  rw [clOff, clOff, ht, List.length_append]
  omega

include henc in
theorem clOff_le_ns {v : ℕ} : clOff x n v ≤ 2 * edgeCount x :=
  le_trans (clPref_length_le henc (Nat.min_le_right v n))
    (offset_le_ns henc (Nat.min_le_right v n))

omit henc in
/-- Indexing the final emitted list inside row `v` reads that row. -/
theorem clPref_getD {v t : ℕ} (hv : v < n) (ht : t < (dedF (clRow x v)).length) :
    (clPref x n).getD (clOff x n v + t) 0 = (dedF (clRow x v)).getD t 0 := by
  obtain ⟨rest, hrest⟩ := clPref_prefix (x := x) (show v + 1 ≤ n by omega)
  rw [hrest, clPref_succ, clOff_eq_length (by omega), List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega),
    Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by omega)]

include henc in
/-- Membership of a deduplicated row is adjacency — the whole chain,
`dedF` → block scan → `adj_iff`. -/
theorem mem_dedF_clRow_iff_adj (v : Fin n) (w : ℕ) :
    w ∈ dedF (clRow x v) ↔ ∃ hw : w < n, G.Adj v ⟨w, hw⟩ := by
  rw [mem_dedF, clRow, mem_clSlice (offset_mono_le henc (Nat.le_succ _) v.isLt)]
  constructor
  · rintro ⟨p, h1, h2, rfl⟩
    have hmem : Impl.blockMem x (v : ℕ) (target x p) :=
      (Impl.blockMem_iff x (v : ℕ) (target x p)).mpr ⟨p, h1, h2, rfl⟩
    have hlt : target x p < n :=
      henc.target_lt p (lt_of_lt_of_le h2 (offset_le_ns henc v.isLt))
    have := (Impl.blockMem_iff_adj henc v ⟨target x p, hlt⟩).mp hmem
    exact ⟨hlt, this⟩
  · rintro ⟨hw, hadj⟩
    have := (Impl.blockMem_iff_adj henc v ⟨w, hw⟩).mpr hadj
    rw [Impl.blockMem_iff] at this
    exact this

end Encoding

/-! ## §4 The program -/

/-- The pass's scalar pool: the owner, the slot pointer, the write
pointer, the target cell. -/
def clScalars : List String := ["cl.u", "cl.j", "cl.p", "cl.w"]

/-- One turn: inside the owner's row, test the mark and emit or skip;
at the row's end, advance the owner and record the boundary offset. -/
def clTurn : Com :=
  .ite (.lt (.var "cl.j") (.get "off" (.add (.var "cl.u") (.lit 1))))
    (.seq (.assign "cl.w" (.get "tgt" (.var "cl.j")))
      (.seq
        (.ite (.eq (.get "cl.d" (.var "cl.w")) (.add (.var "cl.u") (.lit 1)))
          .skip
          (.seq (.store "cl.d" (.var "cl.w") (.add (.var "cl.u") (.lit 1)))
            (.seq (.store "sa.t" (.var "cl.p") (.var "cl.w"))
              (.assign "cl.p" (.add (.var "cl.p") (.lit 1))))))
        (.assign "cl.j" (.add (.var "cl.j") (.lit 1)))))
    (.seq (.assign "cl.u" (.add (.var "cl.u") (.lit 1)))
      (.store "sa.o" (.var "cl.u") (.var "cl.p")))

/-- The boundary writer of the tail scan: the owner branch of the
turn, on its own — trailing empty rows still owe their offsets. -/
def clTail : Com :=
  .seq (.assign "cl.u" (.add (.var "cl.u") (.lit 1)))
    (.store "sa.o" (.var "cl.u") (.var "cl.p"))

/-- The initialization: the three pointers, and the anchored offset
`off[0] = 0`. -/
def clInit : Com :=
  .seq (.assign "cl.u" (.lit 0))
    (.seq (.assign "cl.p" (.lit 0))
      (.seq (.store "sa.o" (.lit 0) (.lit 0))
        (.assign "cl.j" (.lit 0))))

/-- **The deduplicating CSR pass**: initialize, one owner-advancing
pass over the root target zone, the tail boundaries, the slot count. -/
def csrLoadCom : Com :=
  .seq clInit
    (.seq (Csr.scan "cl.j" "mm" clTurn)
      (.seq (.while (.lt (.var "cl.u") (.var "n")) clTail)
        (.assign "sv.m" (.var "cl.p"))))

/-- The pass's budget: one turn per slot, one per row, `O(|x|)`. -/
def csrLoadK (x : List ℕ) : ℕ := 70 * x.length + 20

/-- The level-0 names, reduced to their literals. -/
private theorem off0_eq : (arenaNames 0).off = "sa.o" := rfl
private theorem tgt0_eq : (arenaNames 0).tgt = "sa.t" := rfl
private theorem nS0_eq : (arenaNames 0).nS = "sv.m" := rfl

/-! ## §5 The scan invariant -/

/-- The carried state of the owner-advancing pass: the input CSR
pinned, the two pointers in the owner discipline, the write pointer at
the emitted length, the two output regions as written prefixes over
their zero pools, and the row-stamped mark array — entries at most the
current stamp, the current stamp exactly on the processed part of the
current row. -/
structure LInv (x : List ℕ) (n extO extT extD : ℕ) (σ : Env) : Prop where
  hn : σ.vars "n" = n
  hmm : σ.vars "mm" = 2 * edgeCount x
  hoffI : σ.arrs "off" = csrOffsets x
  htgtI : σ.arrs "tgt" = csrTargets x
  hu : σ.vars "cl.u" ≤ n
  hjns : σ.vars "cl.j" ≤ 2 * edgeCount x
  hlo : offset x (σ.vars "cl.u") ≤ σ.vars "cl.j"
  hhi : σ.vars "cl.u" < n → σ.vars "cl.j" ≤ offset x (σ.vars "cl.u" + 1)
  hp : σ.vars "cl.p" = (clEmit x (σ.vars "cl.u") (σ.vars "cl.j")).length
  hoffO : σ.arrs "sa.o"
    = arrOf (σ.vars "cl.u" + 1) (clOff x n)
      ++ List.replicate (extO - (σ.vars "cl.u" + 1)) 0
  htgtO : σ.arrs "sa.t"
    = clEmit x (σ.vars "cl.u") (σ.vars "cl.j")
      ++ List.replicate (extT - (clEmit x (σ.vars "cl.u") (σ.vars "cl.j")).length) 0
  hdaL : (σ.arrs "cl.d").length = extD
  hdaB : ∀ w, w < n → (σ.arrs "cl.d").getD w 0 ≤ σ.vars "cl.u" + 1
  hdaC : ∀ w, w < n →
    ((σ.arrs "cl.d").getD w 0 = σ.vars "cl.u" + 1
      ↔ w ∈ clSlice x (σ.vars "cl.u") (σ.vars "cl.j"))

/-- The tail scan's invariant: the offsets written to the owner, the
write pointer at the final count, everything past the owner already
flat. -/
structure TInv (x : List ℕ) (n extO : ℕ) (σ : Env) : Prop where
  hn : σ.vars "n" = n
  hu : σ.vars "cl.u" ≤ n
  hp : σ.vars "cl.p" = clOff x n n
  hconst : ∀ v, σ.vars "cl.u" < v → v ≤ n → clOff x n v = clOff x n n
  hoffO : σ.arrs "sa.o"
    = arrOf (σ.vars "cl.u" + 1) (clOff x n)
      ++ List.replicate (extO - (σ.vars "cl.u" + 1)) 0

section Pass

variable {B extO extT extD : ℕ}
variable (henc : EncodesGraph x n G)
variable (hxB : x.length + 1 < B)
variable (hextO : n + 1 ≤ extO) (hextT : 2 * edgeCount x ≤ extT)
variable (hextD : n ≤ extD)

/-- `|x| = 3 + n + 2m`: both figures sit strictly inside the word. -/
private theorem figures_lt (henc : EncodesGraph x n G) (hxB : x.length + 1 < B) :
    n + 1 < B ∧ 2 * edgeCount x < B := by
  have hlen := henc.length_eq
  omega

/-- The increment expression, once. -/
private theorem evalB_incr {B : ℕ} {y : String} {σ : Env}
    (hy : σ.vars y + 1 < B) :
    (Expr.add (.var y) (.lit 1)).evalB B σ = some (σ.vars y + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var y) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hy)
  simpa using h

include henc hxB hextO hextT hextD in
/-- **One turn of the pass**, in `ownerScan_spec`'s step form: it
either consumes one slot (emitting or skipping its target) or advances
the owner (recording one boundary offset), keeps the invariant, and
costs `34` per slot, `15` per row. -/
private theorem clTurn_step :
    ∀ σ, LInv x n extO extT extD σ → σ.vars "cl.j" < 2 * edgeCount x →
      ∃ σ' K', Run B clTurn σ σ' K' ∧ LInv x n extO extT extD σ' ∧
        σ.vars "cl.j" ≤ σ'.vars "cl.j" ∧ σ.vars "cl.u" ≤ σ'.vars "cl.u" ∧
        (σ.vars "cl.j" < σ'.vars "cl.j" ∨ σ.vars "cl.u" < σ'.vars "cl.u") ∧
        K' ≤ 34 * (σ'.vars "cl.j" - σ.vars "cl.j")
          + 15 * (σ'.vars "cl.u" - σ.vars "cl.u") := by
  obtain ⟨hnB, hnsB⟩ := figures_lt henc hxB
  intro σ hI hjns
  obtain ⟨hn, hmm, hoffI, htgtI, hu, hjle, hlo, hhi, hp, hoffO, htgtO,
    hdaL, hdaB, hdaC⟩ := hI
  set u := σ.vars "cl.u" with hu_def
  set j := σ.vars "cl.j" with hj_def
  set p := σ.vars "cl.p" with hp_def
  -- the owner is a real row: `off u ≤ j < 2m = off n`
  have hlast : offset x n = 2 * edgeCount x := henc.offset_last
  have huN : u < n := by
    rcases Nat.lt_or_ge u n with h | h
    · exact h
    · exfalso
      obtain rfl : u = n := by omega
      omega
  have hoffLen : (csrOffsets x).length = n + 1 := by
    have := csrOffsets_length henc
    rwa [henc.vertexCount_eq] at this
  have htgtLen : (csrTargets x).length = 2 * edgeCount x := csrTargets_length henc
  have hoff_getD : ∀ i, i ≤ n → (σ.arrs "off")[i]? = some (offset x i) := by
    intro i hi
    rw [hoffI, getElem?_of_getD (by omega)]
    have := csrOffsets_getD henc (i := i) (by rw [henc.vertexCount_eq]; omega)
    rw [this]
  have hoffB : ∀ i, i ≤ n → offset x i < B :=
    fun i hi => lt_of_le_of_lt (offset_le_ns henc hi) hnsB
  -- the guard
  have huval : (Expr.add (.var "cl.u") (.lit 1)).evalB B σ = some (u + 1) := by
    have h := evalB_incr (B := B) (y := "cl.u") (σ := σ)
      (show σ.vars "cl.u" + 1 < B by rw [← hu_def]; omega)
    rwa [← hu_def] at h
  have hoffval : (Expr.get "off" (.add (.var "cl.u") (.lit 1))).evalB B σ
      = some (offset x (u + 1)) :=
    evalB_get huval (hoff_getD (u + 1) (by omega)) (hoffB (u + 1) (by omega))
  have hcond := evalB_condLt (evalB_var (x := "cl.j") (σ := σ) (by omega)) hoffval
  rw [← hj_def] at hcond
  by_cases hslot : j < offset x (u + 1)
  · -- a slot of the owner's row
    have hcondT : (Cond.lt (.var "cl.j")
        (.get "off" (.add (.var "cl.u") (.lit 1)))).evalB B σ = some true := by
      rw [hcond]
      congr 1
      simpa using hslot
    set w := target x j with hw_def
    have hwN : w < n := henc.target_lt j hjns
    have hread : Run B (.assign "cl.w" (.get "tgt" (.var "cl.j")))
        σ (σ.setVar "cl.w" w) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono
        (by simp)
      rw [htgtI, getElem?_of_getD (by omega)]
      rw [csrTargets_getD henc j]
    set σ₁ := σ.setVar "cl.w" w with hσ₁
    have h1u : σ₁.vars "cl.u" = u := by rw [hσ₁]; simp [hu_def]
    have h1j : σ₁.vars "cl.j" = j := by rw [hσ₁]; simp [hj_def]
    have h1p : σ₁.vars "cl.p" = p := by rw [hσ₁]; simp [hp_def]
    have h1w : σ₁.vars "cl.w" = w := by rw [hσ₁]; simp
    have h1da : σ₁.arrs "cl.d" = σ.arrs "cl.d" := by rw [hσ₁]; simp
    set dw := (σ.arrs "cl.d").getD w 0 with hdw_def
    have hdwB : dw ≤ u + 1 := hdaB w hwN
    -- the mark test
    have hwval : (Expr.var "cl.w").evalB B σ₁ = some w := by
      rw [← h1w]
      exact evalB_var (by rw [h1w]; omega)
    have hdval : (Expr.get "cl.d" (.var "cl.w")).evalB B σ₁ = some dw := by
      refine evalB_get hwval ?_ (by omega)
      rw [h1da, getElem?_of_getD (show w < (σ.arrs "cl.d").length by omega),
        ← hdw_def]
    have hstamp : (Expr.add (.var "cl.u") (.lit 1)).evalB B σ₁ = some (u + 1) := by
      have h := evalB_incr (B := B) (y := "cl.u") (σ := σ₁)
        (show σ₁.vars "cl.u" + 1 < B by rw [h1u]; omega)
      rwa [h1u] at h
    have hmarkEv : (Cond.eq (.get "cl.d" (.var "cl.w"))
        (.add (.var "cl.u") (.lit 1))).evalB B σ₁ = some (dw == u + 1) :=
      evalB_condEq hdval hstamp
    have hslice_snoc : clSlice x u (j + 1) = clSlice x u j ++ [w] :=
      clSlice_snoc hlo
    by_cases hmark : dw = u + 1
    · -- already emitted this row: skip
      have hmarkT : (Cond.eq (.get "cl.d" (.var "cl.w"))
          (.add (.var "cl.u") (.lit 1))).evalB B σ₁ = some true := by
        rw [hmarkEv]
        congr 1
        simpa using hmark
      have hwin : w ∈ clSlice x u j := (hdaC w hwN).mp hmark
      set σ' := σ₁.setVar "cl.j" (j + 1) with hσ'
      have hinc : Run B (.assign "cl.j" (.add (.var "cl.j") (.lit 1))) σ₁ σ' 4 := by
        have hev := evalB_incr (B := B) (y := "cl.j") (σ := σ₁)
          (show σ₁.vars "cl.j" + 1 < B by rw [h1j]; omega)
        rw [h1j] at hev
        exact (Run.assign hev).mono (by simp)
      have hrun : Run B clTurn σ σ' 34 := by
        have hIte : Run B (.ite (.eq (.get "cl.d" (.var "cl.w"))
            (.add (.var "cl.u") (.lit 1))) .skip
            (.seq (.store "cl.d" (.var "cl.w") (.add (.var "cl.u") (.lit 1)))
              (.seq (.store "sa.t" (.var "cl.p") (.var "cl.w"))
                (.assign "cl.p" (.add (.var "cl.p") (.lit 1)))))) σ₁ σ₁ 8 :=
          (Run.ite_true hmarkT Run.skip).mono (by simp)
        exact (Run.ite_true hcondT (hread.seq (hIte.seq hinc))).mono (by simp)
      have h'u : σ'.vars "cl.u" = u := by rw [hσ']; simpa using h1u
      have h'j : σ'.vars "cl.j" = j + 1 := by rw [hσ']; simp
      have h'p : σ'.vars "cl.p" = p := by rw [hσ']; simpa using h1p
      have h'vars : ∀ y, y ≠ "cl.j" → y ≠ "cl.w" → σ'.vars y = σ.vars y := by
        intro y hy1 hy2
        rw [hσ', hσ₁]
        simp [hy1, hy2]
      have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
        intro b
        rw [hσ', hσ₁]
        simp
      have hemit' : clEmit x u (j + 1) = clEmit x u j := by
        rw [clEmit, clEmit, hslice_snoc, dedF_snoc_mem hwin]
      refine ⟨σ', 34, hrun,
        ⟨by rw [h'vars _ (by decide) (by decide)]; exact hn,
          by rw [h'vars _ (by decide) (by decide)]; exact hmm,
          by rw [h'arrs]; exact hoffI,
          by rw [h'arrs]; exact htgtI,
          by rw [h'u]; exact hu,
          by rw [h'j]; omega,
          by rw [h'u, h'j]; omega,
          by rw [h'u, h'j]; intro h; omega,
          by rw [h'p, h'u, h'j, hemit']; exact hp,
          by rw [h'arrs, h'u]; exact hoffO,
          by rw [h'arrs, h'u, h'j, hemit']; exact htgtO,
          by rw [h'arrs]; exact hdaL,
          by rw [h'arrs, h'u]; exact hdaB,
          ?_⟩,
        by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
        by rw [h'j, h'u]; omega⟩
      intro w' hw'
      rw [h'arrs, h'u, h'j, hslice_snoc]
      rw [List.mem_append, List.mem_singleton]
      constructor
      · intro h
        exact Or.inl ((hdaC w' hw').mp h)
      · rintro (h | rfl)
        · exact (hdaC w' hw').mpr h
        · exact hmark
    · -- first occurrence in this row: stamp, emit, advance
      have hmarkF : (Cond.eq (.get "cl.d" (.var "cl.w"))
          (.add (.var "cl.u") (.lit 1))).evalB B σ₁ = some false := by
        rw [hmarkEv]
        congr 1
        simpa using hmark
      have hwout : w ∉ clSlice x u j := fun hc => hmark ((hdaC w hwN).mpr hc)
      have hpj : p ≤ j := by
        rw [hp]
        exact clEmit_length_le henc (by omega) hlo
      -- the three writes
      have hst1 : Run B (.store "cl.d" (.var "cl.w") (.add (.var "cl.u") (.lit 1)))
          σ₁ (σ₁.setArr "cl.d" w (u + 1)) 5 := by
        have hwev : (Expr.var "cl.w").evalB B σ₁ = some w := by
          rw [← h1w]
          exact evalB_var (by rw [h1w]; omega)
        refine (Run.store hwev hstamp ?_).mono (by simp)
        rw [h1da, hdaL]
        omega
      set σ₂ := σ₁.setArr "cl.d" w (u + 1) with hσ₂
      have h2p : σ₂.vars "cl.p" = p := by rw [hσ₂]; simpa using h1p
      have h2w : σ₂.vars "cl.w" = w := by rw [hσ₂]; simpa using h1w
      have h2tgtO : σ₂.arrs "sa.t" = σ.arrs "sa.t" := by rw [hσ₂, hσ₁]; simp
      have hst2 : Run B (.store "sa.t" (.var "cl.p") (.var "cl.w"))
          σ₂ (σ₂.setArr "sa.t" p w) 3 := by
        have hpev : (Expr.var "cl.p").evalB B σ₂ = some p := by
          rw [← h2p]
          exact evalB_var (by rw [h2p]; omega)
        have hwev : (Expr.var "cl.w").evalB B σ₂ = some w := by
          rw [← h2w]
          exact evalB_var (by rw [h2w]; omega)
        refine (Run.store hpev hwev ?_).mono (by simp)
        rw [h2tgtO, htgtO]
        simp only [List.length_append, List.length_replicate]
        have hlen := clEmit_length_le henc (le_of_lt huN) hlo
        rw [← hp]
        omega
      set σ₃ := σ₂.setArr "sa.t" p w with hσ₃
      have h3p : σ₃.vars "cl.p" = p := by rw [hσ₃]; simpa using h2p
      have hst3 : Run B (.assign "cl.p" (.add (.var "cl.p") (.lit 1)))
          σ₃ (σ₃.setVar "cl.p" (p + 1)) 4 := by
        have hev := evalB_incr (B := B) (y := "cl.p") (σ := σ₃)
          (show σ₃.vars "cl.p" + 1 < B by rw [h3p]; omega)
        rw [h3p] at hev
        exact (Run.assign hev).mono (by simp)
      set σ₄ := (σ₃.setVar "cl.p" (p + 1)) with hσ₄
      have h4j : σ₄.vars "cl.j" = j := by rw [hσ₄, hσ₃, hσ₂]; simpa using h1j
      have hinc : Run B (.assign "cl.j" (.add (.var "cl.j") (.lit 1)))
          σ₄ (σ₄.setVar "cl.j" (j + 1)) 4 := by
        have hev := evalB_incr (B := B) (y := "cl.j") (σ := σ₄)
          (show σ₄.vars "cl.j" + 1 < B by rw [h4j]; omega)
        rw [h4j] at hev
        exact (Run.assign hev).mono (by simp)
      set σ' := σ₄.setVar "cl.j" (j + 1) with hσ'
      have hrun : Run B clTurn σ σ' 34 := by
        have hIte : Run B (.ite (.eq (.get "cl.d" (.var "cl.w"))
            (.add (.var "cl.u") (.lit 1))) .skip
            (.seq (.store "cl.d" (.var "cl.w") (.add (.var "cl.u") (.lit 1)))
              (.seq (.store "sa.t" (.var "cl.p") (.var "cl.w"))
                (.assign "cl.p" (.add (.var "cl.p") (.lit 1)))))) σ₁ σ₄ 19 :=
          (Run.ite_false hmarkF (hst1.seq (hst2.seq hst3))).mono (by simp)
        exact (Run.ite_true hcondT (hread.seq (hIte.seq hinc))).mono (by simp)
      -- the final projections
      have h'u : σ'.vars "cl.u" = u := by
        rw [hσ', hσ₄, hσ₃, hσ₂, hσ₁]
        simp [hu_def]
      have h'j : σ'.vars "cl.j" = j + 1 := by rw [hσ']; simp
      have h'p : σ'.vars "cl.p" = p + 1 := by rw [hσ', hσ₄]; simp
      have h'vars : ∀ y, y ≠ "cl.j" → y ≠ "cl.w" → y ≠ "cl.p" →
          σ'.vars y = σ.vars y := by
        intro y hy1 hy2 hy3
        rw [hσ', hσ₄, hσ₃, hσ₂, hσ₁]
        simp [hy1, hy2, hy3]
      have h'arrs : ∀ b, b ≠ "cl.d" → b ≠ "sa.t" → σ'.arrs b = σ.arrs b := by
        intro b hb1 hb2
        rw [hσ', hσ₄, hσ₃, hσ₂, hσ₁]
        simp [hb1, hb2]
      have h'da : σ'.arrs "cl.d" = (σ.arrs "cl.d").set w (u + 1) := by
        rw [hσ', hσ₄, hσ₃, hσ₂, hσ₁]
        simp
      have h'tgt : σ'.arrs "sa.t" = (σ.arrs "sa.t").set p w := by
        rw [hσ', hσ₄, hσ₃, hσ₂, hσ₁]
        simp
      have hemit' : clEmit x u (j + 1) = clEmit x u j ++ [w] := by
        rw [clEmit, clEmit, hslice_snoc, dedF_snoc_not_mem hwout,
          List.append_assoc]
      refine ⟨σ', 34, hrun,
        ⟨by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hn,
          by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hmm,
          by rw [h'arrs _ (by decide) (by decide)]; exact hoffI,
          by rw [h'arrs _ (by decide) (by decide)]; exact htgtI,
          by rw [h'u]; exact hu,
          by rw [h'j]; omega,
          by rw [h'u, h'j]; omega,
          by rw [h'u, h'j]; intro h; omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩,
        by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
        by rw [h'j, h'u]; omega⟩
      · -- the write pointer
        rw [h'p, h'u, h'j, hemit', List.length_append, hp]
        simp
      · -- the offsets, untouched
        rw [h'arrs _ (by decide) (by decide), h'u]
        exact hoffO
      · -- the target prefix, one longer
        rw [h'tgt, h'u, h'j, hemit', htgtO]
        have hone : 1 ≤ extT - (clEmit x u j).length := by
          have hle := clEmit_length_le henc (le_of_lt huN) hlo
          omega
        have hset := set_append_replicate (l := clEmit x u j)
          (k := extT - (clEmit x u j).length) (v := w) hone
        rw [hp, hset, List.length_append, List.length_singleton,
          show extT - (clEmit x u j).length - 1
            = extT - ((clEmit x u j).length + 1) by omega]
      · -- the mark length
        rw [h'da, List.length_set]
        exact hdaL
      · -- the mark bound
        intro w' hw'
        rw [h'da, h'u]
        by_cases hww : w = w'
        · subst hww
          rw [getD_set_self (by omega)]
        · rw [getD_set_ne hww]
          exact hdaB w' hw'
      · -- the mark reading
        intro w' hw'
        rw [h'da, h'u, h'j, hslice_snoc, List.mem_append, List.mem_singleton]
        by_cases hww : w = w'
        · subst hww
          rw [getD_set_self (by omega)]
          simp
        · rw [getD_set_ne hww]
          constructor
          · intro h
            exact Or.inl ((hdaC w' hw').mp h)
          · rintro (h | rfl)
            · exact (hdaC w' hw').mpr h
            · exact absurd rfl hww
  · -- the row's end: advance the owner, record the boundary
    have hcondF : (Cond.lt (.var "cl.j")
        (.get "off" (.add (.var "cl.u") (.lit 1)))).evalB B σ = some false := by
      rw [hcond]
      congr 1
      simpa using hslot
    have hjeq : j = offset x (u + 1) := by
      have := hhi huN
      omega
    have hass : Run B (.assign "cl.u" (.add (.var "cl.u") (.lit 1)))
        σ (σ.setVar "cl.u" (u + 1)) 4 := by
      have hev := evalB_incr (B := B) (y := "cl.u") (σ := σ)
        (show σ.vars "cl.u" + 1 < B by rw [← hu_def]; omega)
      rw [← hu_def] at hev
      exact (Run.assign hev).mono (by simp)
    set σ₁ := σ.setVar "cl.u" (u + 1) with hσ₁
    have h1u : σ₁.vars "cl.u" = u + 1 := by rw [hσ₁]; simp
    have h1p : σ₁.vars "cl.p" = p := by rw [hσ₁]; simp [hp_def]
    have hpB : p < B := by
      have := clEmit_length_le henc (le_of_lt huN) hlo
      rw [hp]
      omega
    have hst : Run B (.store "sa.o" (.var "cl.u") (.var "cl.p"))
        σ₁ (σ₁.setArr "sa.o" (u + 1) p) 3 := by
      have huev : (Expr.var "cl.u").evalB B σ₁ = some (u + 1) := by
        rw [← h1u]
        exact evalB_var (by rw [h1u]; omega)
      have hpev : (Expr.var "cl.p").evalB B σ₁ = some p := by
        rw [← h1p]
        exact evalB_var (by rw [h1p]; exact hpB)
      refine (Run.store huev hpev ?_).mono (by simp)
      have : σ₁.arrs "sa.o" = σ.arrs "sa.o" := by rw [hσ₁]; simp
      rw [this, hoffO]
      simp only [List.length_append, length_arrOf, List.length_replicate]
      omega
    set σ' := σ₁.setArr "sa.o" (u + 1) p with hσ'
    have hrun : Run B clTurn σ σ' 14 :=
      (Run.ite_false hcondF (hass.seq hst)).mono (by simp)
    have h'u : σ'.vars "cl.u" = u + 1 := by rw [hσ']; simpa using h1u
    have h'j : σ'.vars "cl.j" = j := by rw [hσ', hσ₁]; simp [hj_def]
    have h'p : σ'.vars "cl.p" = p := by rw [hσ', hσ₁]; simp [hp_def]
    have h'vars : ∀ y, y ≠ "cl.u" → σ'.vars y = σ.vars y := by
      intro y hy
      rw [hσ', hσ₁]
      simp [hy]
    have h'arrs : ∀ b, b ≠ "sa.o" → σ'.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ', hσ₁]
      simp [hb]
    have h'off : σ'.arrs "sa.o" = (σ.arrs "sa.o").set (u + 1) p := by
      rw [hσ', hσ₁]
      simp
    -- the emitted list survives the boundary
    have hemit_eq : clEmit x (u + 1) j = clEmit x u j := by
      rw [hjeq, clEmit_diag, clEmit_row_end]
    have hnext : u + 1 < n → offset x (u + 1) ≤ offset x (u + 1 + 1) :=
      fun h => offset_mono_le henc (by omega) (by omega)
    refine ⟨σ', 14, hrun,
      ⟨by rw [h'vars _ (by decide)]; exact hn,
        by rw [h'vars _ (by decide)]; exact hmm,
        by rw [h'arrs _ (by decide)]; exact hoffI,
        by rw [h'arrs _ (by decide)]; exact htgtI,
        by rw [h'u]; omega,
        by rw [h'j]; omega,
        by rw [h'u, h'j, hjeq],
        ?_, ?_, ?_, ?_,
        by rw [h'arrs _ (by decide)]; exact hdaL,
        ?_, ?_⟩,
      by rw [h'j], by rw [h'u]; omega, by rw [h'u]; omega,
      by rw [h'j, h'u]; omega⟩
    · -- the new row-window
      rw [h'u, h'j]
      intro h
      have := hnext h
      omega
    · -- the write pointer, unchanged over the boundary
      rw [h'p, h'u, h'j, hemit_eq]
      exact hp
    · -- the offsets, one longer
      rw [h'off, h'u, hoffO]
      have hone : 1 ≤ extO - (u + 1) := by omega
      have hval : clOff x n (u + 1) = p := by
        rw [clOff_eq_length (show u + 1 ≤ n by omega), hp, hjeq, clEmit_row_end]
      have hset := set_append_replicate (l := arrOf (u + 1) (clOff x n))
        (k := extO - (u + 1)) (v := p) hone
      rw [length_arrOf] at hset
      have hR : arrOf (u + 1 + 1) (clOff x n)
          = arrOf (u + 1) (clOff x n) ++ [p] := by
        rw [arrOf_succ, hval]
      rw [hset, hR, show extO - (u + 1) - 1 = extO - (u + 1 + 1) by omega]
    · -- the target prefix over the boundary
      rw [h'arrs _ (by decide), h'u, h'j, hemit_eq]
      exact htgtO
    · -- the mark bound, weakened by one stamp
      intro w' hw'
      rw [h'arrs _ (by decide), h'u]
      have := hdaB w' hw'
      omega
    · -- the fresh stamp is unheld
      intro w' hw'
      rw [h'arrs _ (by decide), h'u, h'j, hjeq,
        clSlice_zero_width (le_refl (offset x (u + 1)))]
      have := hdaB w' hw'
      constructor
      · intro h
        omega
      · intro h
        exact absurd h (List.not_mem_nil)

include henc hxB hextO hextT hextD in
/-- **The whole owner-advancing pass**: from the invariant, the scan
runs the slot pointer to the end of the target zone. -/
private theorem clScan_spec :
    Spec B (LInv x n extO extT extD) (Csr.scan "cl.j" "mm" clTurn)
      (fun _ σ' => LInv x n extO extT extD σ' ∧
        σ'.vars "cl.j" = 2 * edgeCount x)
      (38 * (2 * edgeCount x) + 19 * n + 4) := by
  obtain ⟨hnB, hnsB⟩ := figures_lt henc hxB
  refine Csr.ownerScan_spec B _ n (2 * edgeCount x) 34 15 "cl.j" "mm" "cl.u" clTurn
    (LInv x n extO extT extD) hnsB
    (fun σ hI => ⟨hI.hmm, hI.hjns, hI.hu⟩)
    (clTurn_step henc hxB hextO hextT hextD) (fun σ h => h) ?_
  intro σ hI
  have h1 : 2 * edgeCount x - σ.vars "cl.j" ≤ 2 * edgeCount x := Nat.sub_le _ _
  have h2 : n - σ.vars "cl.u" ≤ n := Nat.sub_le _ _
  have h3 : (34 + 4) * (2 * edgeCount x - σ.vars "cl.j")
      ≤ 38 * (2 * edgeCount x) := Nat.mul_le_mul_left _ h1
  have h4 : (15 + 4) * (n - σ.vars "cl.u") ≤ 19 * n := Nat.mul_le_mul_left _ h2
  omega

include henc hxB hextO in
/-- One boundary of the tail scan. -/
private theorem clTail_body :
    Spec B (fun σ => TInv x n extO σ ∧ σ.vars "cl.u" < n) clTail
      (fun σ σ' => TInv x n extO σ' ∧ σ'.vars "cl.u" = σ.vars "cl.u" + 1) 7 := by
  obtain ⟨hnB, hnsB⟩ := figures_lt henc hxB
  intro σ hσ
  obtain ⟨⟨hn, hu, hp, hconst, hoffO⟩, hlt⟩ := hσ
  set u := σ.vars "cl.u" with hu_def
  set p := σ.vars "cl.p" with hp_def
  have hpns : p ≤ 2 * edgeCount x := by
    rw [hp]
    exact clOff_le_ns henc
  have hass : Run B (.assign "cl.u" (.add (.var "cl.u") (.lit 1)))
      σ (σ.setVar "cl.u" (u + 1)) 4 := by
    have hev := evalB_incr (B := B) (y := "cl.u") (σ := σ)
      (show σ.vars "cl.u" + 1 < B by rw [← hu_def]; omega)
    rw [← hu_def] at hev
    exact (Run.assign hev).mono (by simp)
  set σ₁ := σ.setVar "cl.u" (u + 1) with hσ₁
  have h1u : σ₁.vars "cl.u" = u + 1 := by rw [hσ₁]; simp
  have h1p : σ₁.vars "cl.p" = p := by rw [hσ₁]; simp [hp_def]
  have hst : Run B (.store "sa.o" (.var "cl.u") (.var "cl.p"))
      σ₁ (σ₁.setArr "sa.o" (u + 1) p) 3 := by
    have huev : (Expr.var "cl.u").evalB B σ₁ = some (u + 1) := by
      rw [← h1u]
      exact evalB_var (by rw [h1u]; omega)
    have hpev : (Expr.var "cl.p").evalB B σ₁ = some p := by
      rw [← h1p]
      exact evalB_var (by rw [h1p]; omega)
    refine (Run.store huev hpev ?_).mono (by simp)
    have harr : σ₁.arrs "sa.o" = σ.arrs "sa.o" := by rw [hσ₁]; simp
    rw [harr, hoffO]
    simp only [List.length_append, length_arrOf, List.length_replicate]
    omega
  set σ' := σ₁.setArr "sa.o" (u + 1) p with hσ'
  have h'u : σ'.vars "cl.u" = u + 1 := by rw [hσ']; simpa using h1u
  have h'p : σ'.vars "cl.p" = p := by rw [hσ']; simpa using h1p
  have h'vars : ∀ y, y ≠ "cl.u" → σ'.vars y = σ.vars y := by
    intro y hy
    rw [hσ', hσ₁]
    simp [hy]
  have h'off : σ'.arrs "sa.o" = (σ.arrs "sa.o").set (u + 1) p := by
    rw [hσ', hσ₁]
    simp
  refine ⟨σ', (hass.seq hst).mono (by omega), ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [h'u]⟩
  · rw [h'vars _ (by decide)]
    exact hn
  · rw [h'u]
    omega
  · rw [h'p]
    exact hp
  · intro v hv1 hv2
    rw [h'u] at hv1
    exact hconst v (by omega) hv2
  · rw [h'off, h'u, hoffO]
    have hone : 1 ≤ extO - (u + 1) := by omega
    have hval : clOff x n (u + 1) = p := by
      rw [hconst (u + 1) (by omega) (by omega), hp]
    have hset := set_append_replicate (l := arrOf (u + 1) (clOff x n))
      (k := extO - (u + 1)) (v := p) hone
    rw [length_arrOf] at hset
    have hR : arrOf (u + 1 + 1) (clOff x n)
        = arrOf (u + 1) (clOff x n) ++ [p] := by
      rw [arrOf_succ, hval]
    rw [hset, hR, show extO - (u + 1) - 1 = extO - (u + 1 + 1) by omega]

include henc hxB hextO in
/-- **The tail scan**: the trailing empty rows' boundaries. -/
private theorem clTailLoop_spec :
    Spec B (TInv x n extO) (.while (.lt (.var "cl.u") (.var "n")) clTail)
      (fun _ σ' => TInv x n extO σ' ∧ σ'.vars "cl.u" = n) (11 * n + 4) := by
  obtain ⟨hnB, hnsB⟩ := figures_lt henc hxB
  refine Spec.forRange "cl.u" "n" (TInv x n extO) n 7 (11 * n + 4)
    (fun σ h => by have := h.hu; omega)
    (fun σ h => by rw [h.hn]; omega)
    (fun σ h => h.hn) (fun σ h => h.hu)
    (clTail_body henc hxB hextO) (fun σ h => h) ?_
  intro σ h
  have h1 : n - σ.vars "cl.u" ≤ n := Nat.sub_le _ _
  have h2 : (7 + 4) * (n - σ.vars "cl.u") ≤ 11 * n := Nat.mul_le_mul_left _ h1
  omega

include henc in
/-- **The scan's exit state is the tail's entry state**: at `j = 2m`
the current row is complete and every later row is empty, so the
emitted list is the whole output and the offsets are flat past the
owner. -/
private theorem clEmit_at_end {u : ℕ} (hu : u ≤ n)
    (_hlo : offset x u ≤ 2 * edgeCount x)
    (hhi : u < n → 2 * edgeCount x ≤ offset x (u + 1)) :
    clEmit x u (2 * edgeCount x) = clPref x n ∧
    ∀ v, u < v → v ≤ n → clOff x n v = clOff x n n := by
  have hlast : offset x n = 2 * edgeCount x := henc.offset_last
  rcases Nat.lt_or_ge u n with huN | huN
  · have hup1 : offset x (u + 1) = 2 * edgeCount x := by
      have h1 := offset_le_ns henc (show u + 1 ≤ n by omega)
      have h2 := hhi huN
      omega
    have hflat : ∀ v, u + 1 ≤ v → v ≤ n → clPref x v = clPref x (u + 1) := by
      intro v
      induction v with
      | zero => intro h1 h2; omega
      | succ v ih =>
          intro h1 h2
          rcases Nat.lt_or_ge (u + 1) (v + 1) with hlt | hge
          · have hv1 : offset x v = 2 * edgeCount x := by
              have ha := offset_mono_le henc (show u + 1 ≤ v by omega) (by omega)
              have hb := offset_le_ns henc (show v ≤ n by omega)
              omega
            have hv2 : offset x (v + 1) ≤ offset x v := by
              have hb := offset_le_ns henc h2
              omega
            rw [clPref_succ, ih (by omega) (by omega),
              show clRow x v = ([] : List ℕ) from clSlice_zero_width hv2]
            simp
          · have hveq : v = u := by omega
            rw [hveq]
    constructor
    · rw [show 2 * edgeCount x = offset x (u + 1) from hup1.symm,
        clEmit_row_end, hflat n (by omega) le_rfl]
    · intro v hv1 hv2
      rw [clOff_eq_length hv2, clOff_eq_length le_rfl,
        hflat v (by omega) hv2, hflat n (by omega) le_rfl]
  · have hun : u = n := by omega
    constructor
    · rw [hun, clEmit, show clSlice x n (2 * edgeCount x) = ([] : List ℕ)
        from clSlice_zero_width (le_of_eq hlast.symm)]
      simp
    · intro v hv1 hv2
      omega

/-! ## §6 The initialization, and the invariant's establishment -/

private theorem getD_replicate {m i : ℕ} :
    (List.replicate m (0 : ℕ)).getD i 0 = 0 := by
  rcases Nat.lt_or_ge i m with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

include hxB in
private theorem clInit_spec :
    Spec B (fun σ => 1 ≤ (σ.arrs "sa.o").length) clInit
      (fun σ σ' => σ' = (((σ.setVar "cl.u" 0).setVar "cl.p" 0).setArr
        "sa.o" 0 0).setVar "cl.j" 0) 9 := by
  intro σ hσ
  have h0B : (0 : ℕ) < B := by omega
  have ha1 : Run B (.assign "cl.u" (.lit 0)) σ (σ.setVar "cl.u" 0) 2 :=
    (Run.assign (evalB_lit h0B)).mono (by simp)
  have ha2 : Run B (.assign "cl.p" (.lit 0)) (σ.setVar "cl.u" 0)
      ((σ.setVar "cl.u" 0).setVar "cl.p" 0) 2 :=
    (Run.assign (evalB_lit h0B)).mono (by simp)
  have ha3 : Run B (.store "sa.o" (.lit 0) (.lit 0))
      ((σ.setVar "cl.u" 0).setVar "cl.p" 0)
      (((σ.setVar "cl.u" 0).setVar "cl.p" 0).setArr "sa.o" 0 0) 3 := by
    refine (Run.store (evalB_lit h0B) (evalB_lit h0B) ?_).mono (by simp)
    simpa using hσ
  have ha4 : Run B (.assign "cl.j" (.lit 0))
      (((σ.setVar "cl.u" 0).setVar "cl.p" 0).setArr "sa.o" 0 0)
      ((((σ.setVar "cl.u" 0).setVar "cl.p" 0).setArr "sa.o" 0 0).setVar
        "cl.j" 0) 2 :=
    (Run.assign (evalB_lit h0B)).mono (by simp)
  exact ⟨_, (ha1.seq (ha2.seq (ha3.seq ha4))).mono (by omega), rfl⟩

set_option maxHeartbeats 1000000 in
include henc hextO in
/-- The invariant holds after the initialization. -/
private theorem lInv_init {σ : Env}
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = 2 * edgeCount x)
    (hoffI : σ.arrs "off" = csrOffsets x) (htgtI : σ.arrs "tgt" = csrTargets x)
    (hO : σ.arrs "sa.o" = List.replicate extO 0)
    (hT : σ.arrs "sa.t" = List.replicate extT 0)
    (hD : σ.arrs "cl.d" = List.replicate extD 0) :
    LInv x n extO extT extD
      ((((σ.setVar "cl.u" 0).setVar "cl.p" 0).setArr "sa.o" 0 0).setVar
        "cl.j" 0) := by
  set σ' := (((σ.setVar "cl.u" 0).setVar "cl.p" 0).setArr "sa.o" 0 0).setVar
    "cl.j" 0 with hσ'
  have h'u : σ'.vars "cl.u" = 0 := by rw [hσ']; simp
  have h'j : σ'.vars "cl.j" = 0 := by rw [hσ']; simp
  have h'p : σ'.vars "cl.p" = 0 := by rw [hσ']; simp
  have h'arrs : ∀ b, b ≠ "sa.o" → σ'.arrs b = σ.arrs b := by
    intro b hb
    rw [hσ']
    simp [hb]
  have h'off : σ'.arrs "sa.o" = (σ.arrs "sa.o").set 0 0 := by
    rw [hσ']
    simp
  have hslice0 : clSlice x 0 0 = ([] : List ℕ) :=
    clSlice_zero_width (by omega)
  have hemit0 : clEmit x 0 0 = ([] : List ℕ) := by
    rw [clEmit, hslice0]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ']; simp [hn]
  · rw [hσ']; simp [hmm]
  · rw [h'arrs _ (by decide)]; exact hoffI
  · rw [h'arrs _ (by decide)]; exact htgtI
  · rw [h'u]; omega
  · rw [h'j]; omega
  · rw [h'u, h'j, henc.offset_zero]
  · rw [h'u, h'j]
    intro h
    omega
  · rw [h'p, h'u, h'j, hemit0]
    rfl
  · rw [h'off, h'u, hO, replicate_set_zero (by omega)]
    have : arrOf (0 + 1) (clOff x n) = [0] := by
      rw [show (0 : ℕ) + 1 = 1 from rfl]
      simp [arrOf, clOff_zero]
    rw [this]
  · rw [h'arrs _ (by decide), h'u, h'j, hemit0, hT]
    simp
  · rw [h'arrs _ (by decide), hD]
    simp
  · intro w hw
    rw [h'arrs _ (by decide), hD, getD_replicate, h'u]
    omega
  · intro w hw
    rw [h'arrs _ (by decide), hD, getD_replicate, h'u, h'j, hslice0]
    constructor
    · intro h
      omega
    · intro h
      exact absurd h (List.not_mem_nil)

include henc in
/-- **The scan's exit state is the tail's entry state.** -/
private theorem tInv_of_scan_end {σ : Env} (hI : LInv x n extO extT extD σ)
    (hj : σ.vars "cl.j" = 2 * edgeCount x) :
    TInv x n extO σ ∧
      σ.arrs "sa.t"
        = clPref x n ++ List.replicate (extT - (clPref x n).length) 0 := by
  have hlo := hI.hlo
  rw [hj] at hlo
  have hhi : σ.vars "cl.u" < n →
      2 * edgeCount x ≤ offset x (σ.vars "cl.u" + 1) := by
    intro h
    have := hI.hhi h
    omega
  obtain ⟨hemit, hconst⟩ := clEmit_at_end henc hI.hu hlo hhi
  refine ⟨⟨hI.hn, hI.hu, ?_, hconst, hI.hoffO⟩, ?_⟩
  · rw [hI.hp, hj, hemit, clOff_eq_length le_rfl]
  · have h := hI.htgtO
    rw [hj, hemit] at h
    exact h

end Pass

/-! ## §7 The output read back: the prefix is a deduplicated CSR -/

private theorem take_append_exact {l t : List ℕ} {m : ℕ} (h : l.length = m) :
    (l ++ t).take m = l := by
  subst h
  simp

section Final

variable (henc : EncodesGraph x n G)

include henc in
/-- Every entry of the final emitted list is a vertex. -/
private theorem clPref_entry_lt {p : ℕ} (hp : p < (clPref x n).length) :
    (clPref x n).getD p 0 < n := by
  have hmem : (clPref x n).getD p 0 ∈ clPref x n := by
    rw [getD_eq_getElem hp]
    exact List.getElem_mem hp
  rw [clPref, List.mem_flatMap] at hmem
  obtain ⟨v, hv, hw⟩ := hmem
  rw [List.mem_range] at hv
  obtain ⟨hlt, -⟩ := (mem_dedF_clRow_iff_adj henc ⟨v, hv⟩ _).mp hw
  exact hlt

omit henc in
/-- Row `v` of the output CSR is the deduplicated block of `v`. -/
private theorem clRow_read (v : Fin n) :
    Csr.row (clOff x n) (fun p => (clPref x n).getD p 0) (v : ℕ)
      = dedF (clRow x (v : ℕ)) := by
  have hlen : Csr.rowLen (clOff x n) (v : ℕ)
      = (dedF (clRow x (v : ℕ))).length := by
    rw [Csr.rowLen, clOff_succ v.isLt]
    omega
  rw [Csr.row, hlen]
  refine List.ext_getElem (by simp) ?_
  intro k h1 h2
  have h1' : k < (dedF (clRow x (v : ℕ))).length := by simpa using h1
  have hget : (arrOf (dedF (clRow x (v : ℕ))).length
      fun k => (clPref x n).getD (clOff x n (v : ℕ) + k) 0)[k]'h1
      = (clPref x n).getD (clOff x n (v : ℕ) + k) 0 := by
    simp [arrOf]
  rw [hget, clPref_getD v.isLt h1', getD_eq_getElem h2]

include henc in
/-- **The final state's level-0 pair is the deduplicated CSR prefix**:
`CsrPrefix` read off the two written regions. -/
private theorem csrPrefix_final {extO extT : ℕ} {σ' : Env}
    (hoffF : σ'.arrs "sa.o"
      = arrOf (n + 1) (clOff x n) ++ List.replicate (extO - (n + 1)) 0)
    (htgtF : σ'.arrs "sa.t"
      = clPref x n ++ List.replicate (extT - (clPref x n).length) 0)
    (hO : n + 1 ≤ extO) (hT : 2 * edgeCount x ≤ extT) :
    CsrPrefix "sa.o" "sa.t" G (clOff x n n) σ' := by
  have hnsEq : clOff x n n = (clPref x n).length := clOff_eq_length le_rfl
  have hplen : (clPref x n).length ≤ 2 * edgeCount x :=
    le_trans (clPref_length_le henc le_rfl) (offset_le_ns henc le_rfl)
  have hoffLen : (σ'.arrs "sa.o").length = extO := by
    rw [hoffF]
    simp only [List.length_append, length_arrOf, List.length_replicate]
    omega
  have htgtLen : (σ'.arrs "sa.t").length = extT := by
    rw [htgtF]
    simp only [List.length_append, List.length_replicate]
    omega
  refine ⟨by omega, by rw [htgtLen]; omega, ?_⟩
  -- the windowed reads
  have hpwo : (fun b => if b = "sa.o" then some (n + 1)
      else if b = "sa.t" then some (clOff x n n) else none) "sa.o"
      = some (n + 1) := by simp
  have hpwt : (fun b => if b = "sa.o" then some (n + 1)
      else if b = "sa.t" then some (clOff x n n) else none) "sa.t"
      = some (clOff x n n) := by simp
  have hwoff : (winA (fun b => if b = "sa.o" then some (n + 1)
      else if b = "sa.t" then some (clOff x n n) else none) σ').arrs "sa.o"
      = arrOf (n + 1) (clOff x n) := by
    rw [arrs_winA_some hpwo σ', hoffF, take_append_exact (by simp)]
  have hwtgt : (winA (fun b => if b = "sa.o" then some (n + 1)
      else if b = "sa.t" then some (clOff x n n) else none) σ').arrs "sa.t"
      = clPref x n := by
    rw [arrs_winA_some hpwt σ', htgtF, hnsEq, take_append_exact rfl]
  refine ⟨clOff x n, fun p => (clPref x n).getD p 0,
    ⟨hwoff, ?_, fun i _ => clOff_mono (Nat.le_succ i), rfl, ?_⟩,
    clOff_zero, ?_, ?_⟩
  · -- the target window is the emitted list
    rw [hwtgt, hnsEq]
    exact (arrOf_getD (clPref x n)).symm
  · -- every slot holds a vertex
    intro p hp
    rw [hnsEq] at hp
    exact clPref_entry_lt henc hp
  · -- rows are duplicate-free
    intro v
    rw [clRow_read v]
    exact nodup_dedF _
  · -- row membership is adjacency
    intro v w'
    rw [clRow_read v]
    exact mem_dedF_clRow_iff_adj henc v w'

end Final

/-! ## §8 The write discipline, off the syntax -/

private theorem not_mem_warrs_csrLoadCom {b : String} (h1 : b ≠ "sa.o")
    (h2 : b ≠ "sa.t") (h3 : b ≠ "cl.d") : b ∉ csrLoadCom.warrs := by
  intro hmem
  simp only [csrLoadCom, clInit, clTurn, clTail, Csr.scan, Com.warrs,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    false_or] at hmem
  tauto

private theorem not_mem_wvars_csrLoadCom {y : String} (h0 : y ≠ "sv.m")
    (h1 : y ≠ "cl.u") (h2 : y ≠ "cl.j") (h3 : y ≠ "cl.p") (h4 : y ≠ "cl.w") :
    y ∉ csrLoadCom.wvars := by
  intro hmem
  simp only [csrLoadCom, clInit, clTurn, clTail, Csr.scan, Com.wvars,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    false_or] at hmem
  tauto

/-! ## §9 The headline -/

set_option maxHeartbeats 1000000 in
open Classical in
/-- **F6c10b residual 2, discharged verbatim**: the deduplicating CSR
pass — the concrete program `csrLoadCom` at budget `csrLoadK` — leaves
in the level-0 CSR pair a deduplicated prefix of `G` with its slot
count in the level-0 `nS` cell, from hypotheses only of the
F7-suppliable kinds: `1 ≤ q` and the three `ext` length conventions
(the level-0 offset region at `n + 1` cells, the target region at the
raw `2m`, the mark scratch at `n`). -/
theorem rootCsrLoadAll_csrLoadCom (c w q : ℕ) (ext : List ℕ → String → ℕ)
    (hq : 1 ≤ q)
    (hextO : ∀ x ∈ mcD n G c w, n + 1 ≤ ext x "sa.o")
    (hextT : ∀ x ∈ mcD n G c w, 2 * edgeCount x ≤ ext x "sa.t")
    (hextD : ∀ x ∈ mcD n G c w, n ≤ ext x "cl.d") :
    RootCsrLoadAll G c w q ext "cl.d" clScalars csrLoadCom csrLoadK := by
  intro x hx
  have henc : EncodesGraph x n G := hx.1
  have h3 : 3 ≤ x.length := three_le_length henc
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB h3 hq
  have hlen := henc.length_eq
  have hO := hextO x hx
  have hT := hextT x hx
  have hD := hextD x hx
  obtain ⟨hnB, hnsB⟩ := figures_lt henc hxB
  -- the four phases
  have hInit := clInit_spec (B := mcB q x) (x := x) hxB
  have hScan := clScan_spec henc hxB hO hT hD
  have hTail := (clTailLoop_spec henc hxB hO).frame
  have hFin : Spec (mcB q x) (fun σ => σ.vars "cl.p" < mcB q x)
      (.assign "sv.m" (.var "cl.p"))
      (fun σ σ' => σ' = σ.setVar "sv.m" (σ.vars "cl.p")) 2 := by
    refine (Spec.assign (f := fun σ => σ.vars "cl.p") ?_).mono (by simp)
    intro σ hσ
    exact evalB_var hσ
  -- tail ; fin, from the scan's exit state
  have hTF : Spec (mcB q x)
      (fun σ => TInv x n (ext x "sa.o") σ ∧
        σ.arrs "sa.t" = clPref x n
          ++ List.replicate (ext x "sa.t" - (clPref x n).length) 0)
      (.seq (.while (.lt (.var "cl.u") (.var "n")) clTail)
        (.assign "sv.m" (.var "cl.p")))
      (fun _ σ' => σ'.vars "sv.m" = clOff x n n ∧
        σ'.arrs "sa.o" = arrOf (n + 1) (clOff x n)
          ++ List.replicate (ext x "sa.o" - (n + 1)) 0 ∧
        σ'.arrs "sa.t" = clPref x n
          ++ List.replicate (ext x "sa.t" - (clPref x n).length) 0)
      (11 * n + 4 + 2) := by
    refine Spec.seq (hTail.pre (fun σ hσ => hσ.1)) hFin ?_ ?_
    · -- the tail's exit lands in the final assignment's word bound
      rintro σ σ' - ⟨⟨hT', -⟩, -, -, -, -⟩
      rw [hT'.hp]
      have := clOff_le_ns (x := x) (n := n) henc (v := n)
      omega
    · -- assemble the final state
      rintro σ σ' σ'' ⟨hTin, hsat⟩ ⟨⟨hT', hu'⟩, -, hfa, -, -⟩ rfl
      have hsat' : σ'.arrs "sa.t" = clPref x n
          ++ List.replicate (ext x "sa.t" - (clPref x n).length) 0 := by
        rw [hfa "sa.t" (by simp [clTail, Com.warrs]), hsat]
      refine ⟨by simp [hT'.hp], ?_, ?_⟩
      · have h := hT'.hoffO
        rw [hu'] at h
        simpa using h
      · simpa using hsat'
  -- scan ; (tail ; fin)
  have hSTF : Spec (mcB q x) (LInv x n (ext x "sa.o") (ext x "sa.t") (ext x "cl.d"))
      (.seq (Csr.scan "cl.j" "mm" clTurn)
        (.seq (.while (.lt (.var "cl.u") (.var "n")) clTail)
          (.assign "sv.m" (.var "cl.p"))))
      (fun _ σ' => σ'.vars "sv.m" = clOff x n n ∧
        σ'.arrs "sa.o" = arrOf (n + 1) (clOff x n)
          ++ List.replicate (ext x "sa.o" - (n + 1)) 0 ∧
        σ'.arrs "sa.t" = clPref x n
          ++ List.replicate (ext x "sa.t" - (clPref x n).length) 0)
      (38 * (2 * edgeCount x) + 19 * n + 4 + (11 * n + 4 + 2)) :=
    Spec.seq hScan hTF
      (fun σ σ' _ hq' => tInv_of_scan_end henc hq'.1 hq'.2)
      (fun _ _ _ _ _ hq' => hq')
  -- init ; the rest
  have hMain : Spec (mcB q x) (MatIn (ext x) x) csrLoadCom
      (fun _ σ' => σ'.vars "sv.m" = clOff x n n ∧
        σ'.arrs "sa.o" = arrOf (n + 1) (clOff x n)
          ++ List.replicate (ext x "sa.o" - (n + 1)) 0 ∧
        σ'.arrs "sa.t" = clPref x n
          ++ List.replicate (ext x "sa.t" - (clPref x n).length) 0)
      (csrLoadK x) := by
    refine (Spec.seq (hInit.pre ?_) hSTF ?_ (fun _ _ _ _ _ hq' => hq')).mono ?_
    · -- the fresh region is long enough for the anchored store
      intro σ hM
      rw [hM.arrs "sa.o" (by decide), List.length_replicate]
      omega
    · -- the initialized state satisfies the invariant
      rintro σ σ' hM rfl
      have hn' : σ.vars "n" = n := by
        rw [hM.root.n_eq, henc.vertexCount_eq]
      exact lInv_init henc hO hn' hM.mm_eq hM.root.off_eq hM.root.tgt_eq
        (hM.arrs "sa.o" (by decide)) (hM.arrs "sa.t" (by decide))
        (hM.arrs "cl.d" (by decide))
    · -- the budget
      rw [csrLoadK]
      omega
  -- the frame and the lengths, and the postcondition's shape
  have hFramed := specArrsLength hMain.frame
  refine hFramed.post ?_
  rintro σ σ' hM ⟨⟨⟨hns, hoffF, htgtF⟩, hfv, hfa, -, -⟩, hlenA⟩
  have hnsv : σ'.vars (arenaNames 0).nS = clOff x n n := by
    rw [nS0_eq]
    exact hns
  refine ⟨?_, ?_, ?_, hlenA⟩
  · -- the deduplicated prefix
    rw [off0_eq, tgt0_eq, hnsv]
    exact csrPrefix_final henc hoffF htgtF hO hT
  · -- the array frame
    intro b hb1 hb2 hb3
    rw [off0_eq] at hb1
    rw [tgt0_eq] at hb2
    exact hfa b (not_mem_warrs_csrLoadCom hb1 hb2 hb3)
  · -- the scalar frame
    intro y hy1 hy2
    rw [nS0_eq] at hy1
    simp only [clScalars, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hy2
    exact hfv y (not_mem_wvars_csrLoadCom hy1 hy2.1 hy2.2.1 hy2.2.2.1
      hy2.2.2.2)

end Lax3Proofs.Prog
