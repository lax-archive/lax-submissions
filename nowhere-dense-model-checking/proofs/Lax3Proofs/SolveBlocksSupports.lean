import Lax3Proofs.SolveBfs

/-!
# F6c/4 — the supports stage (`bfsSupports`/`descend`) as IMP+

`SolveBfs` left the exact truncated distance table of one source in a
region (`bfsCom_spec`: `Impl.BallTable` at the contents, every entry
`≤ d + 1`). This file is the stage that consumes it: **`supportsCom`
materializes `Impl.descend`'s walk lists into the `HistArr` column of
the current round** — per reached vertex the counted gradient walk
`v → parent v → … → source`, per unreached vertex the empty list, all
other columns untouched. The stored list is `descend G D v`
*verbatim*, which is what makes the landed `descend_spec` (`ImplBfs`:
`∃ w : H.Walk v s, w.length = D v ∧ w.support = descend H D v`) apply
to the stored data, and `bfsSupports` is recovered cell for cell
(`descendCol_eq_bfsSupports`).

## The least parent, and how least-ness is enforced

`Impl.descend` is deterministic *at the least parent*: each step moves
to `(parents H D v).min'` — the minimum, in vertex order, over **all**
strictly-closer neighbours. An arbitrary-parent walk would be a
correct walk but not `descend`'s list. The machine's first pass
(`parentCom`) therefore computes the least parent of every vertex
in place: the parent region is reset to the sentinel `N`, and one
owner-advancing pass over the whole CSR slot array keeps the running
minimum of the scanned prefix of each row *in the owner's own parent
cell* — a slot whose target is strictly closer (`D w < D u`) is
compared against the cell and stored only if smaller. Rows are
unsorted, so this running minimum is the whole argument: at the row's
end the cell holds the minimum over the full row, which
`row_min_eq_leastParent` identifies with `(parents G D u).min'`
(sentinel `N` exactly when the parent set is empty). Rows past the
scan's final owner are empty (the slot pointer drains the whole
target zone), so their sentinel is also correct.

The second pass (`histCom`) walks every reached vertex down the
gradient: write `v`, then `≤ d` parent-cell hops, each one appended to
the `HistArr` slot of `(v, e)`, then the count. Under `BallTable` the
hop target is `descend`'s own next vertex (`leastParent_step`), so the
written prefix is a prefix of `descend G D v` at every step, and the
loop exits exactly at the source (`D x = 0`, where the parent set is
empty and `descend` closes with `[x]`).

## The contract

`supportsCom_spec`: from the CSR, the input cells
(`sp.n/m/r/l/h/p` = `N/ns/d/ℓp/hb/e`), a length-`N` parent scratch
region (dirty is fine — the routine resets it), the distance region at
`D` (the composition seam: precondition verbatim `bfsCom_spec`'s
postcondition, `BallTable` + the `≤ d + 1` bound as hypotheses), and
the `HistArr` at `hist`, the routine leaves

* the distance region untouched (restated, so the next stage composes),
* the parent region at `leastParent G D` (deliverable 1),
* `HistArr` at `fun v p => if p = e then descendCol G D d v else hist v p`
  (deliverables 2–3): column `e` holds `descend G D v` at reached
  vertices and `[]` (length cell `0` — `HistArr` pins nothing else of
  an empty slot) at unreached ones, every other column exactly as it
  was.

Stored values (deliverable 4): parent cells `≤ N` (`leastParent_le`),
length cells `≤ d + 1` (`descendCol_length_le`; `d + 1 ≤ hb` is the
slot-capacity hypothesis), list cells `< N` (they are `Fin N` names by
the `HistArr` type) — all below `mcB` at schedule constants (head
file's stored-value paragraph).

## The budget

`supportsK N ns d = parentK N ns + histK N d`:

* `parentK N ns = 26·N + 32·ns + 14` — the parent pass: the reset
  (`11·N`), one owner-advancing pass over the whole slot array (`28` a
  slot, `11` a row) — `supportsCharge`'s row-scan term
  `Σ_v (deg v + 1)` at machine constants, priced over the whole CSR
  (`O(N + 2M)`).
* `histK N d = (19·d + 44)·N + 6` — the walks: per vertex a constant
  plus `19` per gradient hop; the machine prices the abstract
  `Σ_reached (D v + 1)` term at its schedule-constant ceiling
  `D v + 1 ≤ d + 1` per vertex, which is where a closed `Spec` budget
  must land (the true per-run cost is the smaller sum, the closed
  envelope cannot see the reached set).

Envelope `supportsK_le : supportsK N ns d ≤ 35·(d+2)·(N+ns+1)` —
`supportsCharge_le`'s `(d + 2) · ballNorm` shape with `ballNorm`
closed to `‖CSR‖` at the schedule constant, F7's reconciliation form.

The scratch cells are the fixed list `spScalars` (prefix `"sp."`), the
five arrays are name parameters; `wvars_supportsCom_subset` /
`warrs_supportsCom` / `noWrite_supportsCom` / `not_reads_supportsCom`
are the frame data (only `pa` and `ha` are written — the CSR, the
distance region and every other region are frame).
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax62Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3Proofs.Impl (parents descend bfsSupports BallTable parents_nonempty
  length_descend)

/-! ## §1 The abstract layer: the least parent and the stored column -/

section Abstract

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- **The least parent, as stored**: the minimum strictly-closer
neighbour — `Impl.descend`'s own step — or the sentinel `N` when there
is none (the source, and every unreached vertex of an empty parent
set). -/
def leastParent (D : Fin N → ℕ) (v : Fin N) : ℕ :=
  if h : (parents G D v).Nonempty then ((parents G D v).min' h : ℕ) else N

/-- **The stored column**: `Impl.descend`'s list at reached vertices,
the empty list beyond the horizon. -/
def descendCol (D : Fin N → ℕ) (d : ℕ) (v : Fin N) : List (Fin N) :=
  if D v ≤ d then descend G D v else []

variable {G}

/-- The column is `Impl.bfsSupports`, cell for cell (`none` reads back
as the empty list — the encoding `HistArr` stores). -/
theorem descendCol_eq_bfsSupports (D : Fin N → ℕ) (d : ℕ) (v : Fin N) :
    descendCol G D d v = (bfsSupports G D d v).getD [] := by
  rw [descendCol, Lax3Proofs.Impl.bfsSupports]
  by_cases h : D v ≤ d <;> simp [h]

theorem descendCol_of_reached {D : Fin N → ℕ} {d : ℕ} {v : Fin N}
    (h : D v ≤ d) : descendCol G D d v = descend G D v := if_pos h

theorem descendCol_of_far {D : Fin N → ℕ} {d : ℕ} {v : Fin N}
    (h : ¬ D v ≤ d) : descendCol G D d v = [] := if_neg h

/-- Membership of the parent set, unfolded. -/
theorem mem_parents_iff {D : Fin N → ℕ} {v u : Fin N} :
    u ∈ parents G D v ↔ G.Adj u v ∧ D u < D v := by
  simp [Lax3Proofs.Impl.parents]

/-- Parent values fit the sentinel bound (`mcB` routing: `≤ N`). -/
theorem leastParent_le (D : Fin N → ℕ) (v : Fin N) :
    leastParent G D v ≤ N := by
  rw [leastParent]
  split
  · exact Nat.le_of_lt (Fin.is_lt _)
  · exact le_rfl

/-- One step of `descend`, at a nonempty parent set. -/
theorem descend_eq_cons {D : Fin N → ℕ} {v : Fin N}
    (h : (parents G D v).Nonempty) :
    descend G D v = v :: descend G D ((parents G D v).min' h) := by
  rw [Lax3Proofs.Impl.descend, dif_pos h]

/-- The last step of `descend`: no strictly-closer neighbour. -/
theorem descend_eq_singleton {D : Fin N → ℕ} {v : Fin N}
    (h : ¬ (parents G D v).Nonempty) : descend G D v = [v] := by
  rw [Lax3Proofs.Impl.descend, dif_neg h]

/-- Every `descend` list starts with its own vertex. -/
theorem descend_cons (D : Fin N → ℕ) (v : Fin N) :
    ∃ tl, descend G D v = v :: tl := by
  by_cases h : (parents G D v).Nonempty
  · exact ⟨_, descend_eq_cons h⟩
  · exact ⟨[], descend_eq_singleton h⟩

/-- At the source the parent set is empty and the walk closes. -/
theorem descend_eq_singleton_of_zero {D : Fin N → ℕ} {v : Fin N}
    (h : D v = 0) : descend G D v = [v] := by
  refine descend_eq_singleton ?_
  rintro ⟨u, hu⟩
  rw [mem_parents_iff] at hu
  omega

/-- **The machine's hop is `descend`'s step**: at a reached vertex of
positive distance the least parent exists, is strictly closer, and is
exactly the vertex `descend` recurses into. -/
theorem leastParent_step {s : Fin N} {d : ℕ} {D : Fin N → ℕ}
    (hD : BallTable G s d D) {v : Fin N} (hvd : D v ≤ d) (hv : 0 < D v) :
    ∃ u : Fin N, leastParent G D v = (u : ℕ) ∧ D u < D v ∧
      descend G D v = v :: descend G D u := by
  have hne := parents_nonempty hD hvd hv
  refine ⟨(parents G D v).min' hne, ?_, ?_, descend_eq_cons hne⟩
  · rw [leastParent, dif_pos hne]
  · exact (mem_parents_iff.mp ((parents G D v).min'_mem hne)).2

/-- Length cells fit the schedule bound (`mcB` routing: `≤ d + 1`). -/
theorem descendCol_length_le {s : Fin N} {d : ℕ} {D : Fin N → ℕ}
    (hD : BallTable G s d D) (v : Fin N) :
    (descendCol G D d v).length ≤ d + 1 := by
  rw [descendCol]
  split
  · rw [length_descend hD ‹_›]
    omega
  · simp

end Abstract

/-! ## §2 Machine tables and slot addresses -/

/-- A `Fin N`-indexed table as the machine array function: the value
below the carrier, a default beyond it (`arrOf` never reads there, but
the function must be total). -/
def supTab {N : ℕ} (f : Fin N → ℕ) (z : ℕ) (q : ℕ) : ℕ :=
  if h : q < N then f ⟨q, h⟩ else z

@[simp] theorem supTab_coe {N : ℕ} (f : Fin N → ℕ) (z : ℕ) (v : Fin N) :
    supTab f z (v : ℕ) = f v := dif_pos v.2

theorem supTab_of_lt {N : ℕ} (f : Fin N → ℕ) (z : ℕ) {q : ℕ} (h : q < N) :
    supTab f z q = f ⟨q, h⟩ := dif_pos h

/-- The combined slot index stays below the slot count. -/
theorem slotIdx_lt {N ℓp v p : ℕ} (hv : v < N) (hp : p < ℓp) :
    v * ℓp + p < N * ℓp := by
  have h1 : v * ℓp + p < (v + 1) * ℓp := by
    have : (v + 1) * ℓp = v * ℓp + ℓp := by ring
    omega
  have h2 : (v + 1) * ℓp ≤ N * ℓp := Nat.mul_le_mul_right ℓp (by omega)
  omega

/-- The combined slot index recovers vertex and round. -/
theorem slotIdx_inj {ℓp v p v' p' : ℕ} (hp : p < ℓp) (hp' : p' < ℓp)
    (h : v * ℓp + p = v' * ℓp + p') : v = v' ∧ p = p' := by
  have hmono : ∀ a b oa ob : ℕ, oa < ℓp → a < b → a * ℓp + oa < b * ℓp + ob := by
    intro a b oa ob hoa hab
    have h1 : a * ℓp + oa < (a + 1) * ℓp := by
      have : (a + 1) * ℓp = a * ℓp + ℓp := by ring
      omega
    have h2 : (a + 1) * ℓp ≤ b * ℓp := Nat.mul_le_mul_right ℓp (by omega)
    omega
  have hvv : v = v' := by
    rcases lt_trichotomy v v' with hlt | heq | hgt
    · have := hmono v v' p p' hp hlt
      omega
    · exact heq
    · have := hmono v' v p' p hp' hgt
      omega
  subst hvv
  exact ⟨rfl, by omega⟩

/-- Every cell of a slot lies inside the region. -/
theorem slotAddr_lt {N ℓp hb v p o : ℕ} (hv : v < N) (hp : p < ℓp)
    (ho : o ≤ hb) :
    (v * ℓp + p) * (hb + 1) + o < N * ℓp * (hb + 1) := by
  have hs : v * ℓp + p + 1 ≤ N * ℓp := slotIdx_lt hv hp
  have h1 : (v * ℓp + p) * (hb + 1) + o < (v * ℓp + p + 1) * (hb + 1) := by
    have : (v * ℓp + p + 1) * (hb + 1) = (v * ℓp + p) * (hb + 1) + (hb + 1) := by
      ring
    omega
  have h2 : (v * ℓp + p + 1) * (hb + 1) ≤ N * ℓp * (hb + 1) :=
    Nat.mul_le_mul_right _ hs
  omega

/-- Cells of distinct slots are separated: a foreign slot's cell lies
entirely below or entirely above this slot's window. -/
theorem slotAddr_outside {hb s s' o : ℕ} (hss : s' ≠ s) (ho : o ≤ hb) :
    s' * (hb + 1) + o < s * (hb + 1) ∨
      s * (hb + 1) + hb < s' * (hb + 1) + o := by
  have key : ∀ a b oa : ℕ, oa ≤ hb → a < b →
      a * (hb + 1) + oa < b * (hb + 1) := by
    intro a b oa hoa hab
    have h1 : a * (hb + 1) + oa < (a + 1) * (hb + 1) := by
      have : (a + 1) * (hb + 1) = a * (hb + 1) + (hb + 1) := by ring
      omega
    have h2 : (a + 1) * (hb + 1) ≤ b * (hb + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  rcases Nat.lt_or_ge s' s with h | h
  · exact Or.inl (key s' s o ho h)
  · right
    have hlt : s < s' := by omega
    have := key s s' hb le_rfl hlt
    omega

/-- **One slot of the channel region, as a function fact**: the length
cell holds the list's length (`≤ hb`), the next cells its names —
`HistArr`'s per-slot content, stated on the abstract array function so
stores update it pointwise. -/
def SlotEnc {N : ℕ} (ℓp hb : ℕ) (F : ℕ → ℕ) (v : Fin N) (p : Fin ℓp)
    (l : List (Fin N)) : Prop :=
  l.length ≤ hb ∧
  F (((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1)) = l.length ∧
  ∀ i : ℕ, ∀ hi : i < l.length,
    F (((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) + 1 + i) = ((l[i] : Fin N) : ℕ)

/-- A slot fact transports along agreement on the slot's window. -/
theorem SlotEnc.of_agree {N ℓp hb : ℕ} {F F' : ℕ → ℕ} {v : Fin N}
    {p : Fin ℓp} {l : List (Fin N)} (h : SlotEnc ℓp hb F v p l)
    (hagree : ∀ o, o ≤ hb →
      F' (((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) + o)
        = F (((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) + o)) :
    SlotEnc ℓp hb F' v p l := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, fun i hi => ?_⟩
  · have := hagree 0 (Nat.zero_le hb)
    rw [Nat.add_zero] at this
    rw [this, h2]
  · have := hagree (1 + i) (by omega)
    rw [← Nat.add_assoc] at this
    rw [this]
    exact h3 i hi

/-- Reading the slot facts off a `HistArr` region held as a function. -/
theorem slotEnc_of_histArr {N ℓp hb : ℕ} {a : String}
    {hist : Fin N → Fin ℓp → List (Fin N)} {σ : Env} {F : ℕ → ℕ}
    (hH : HistArr a ℓp hb hist σ)
    (hF : σ.arrs a = arrOf (N * ℓp * (hb + 1)) F) :
    ∀ (v : Fin N) (p : Fin ℓp), SlotEnc ℓp hb F v p (hist v p) := by
  intro v p
  obtain ⟨hlen, hslots⟩ := hH
  obtain ⟨hble, hcell, hcells⟩ := hslots v p
  have hbase : ((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) < N * ℓp * (hb + 1) := by
    have := slotAddr_lt (o := 0) v.2 p.2 (Nat.zero_le hb)
    omega
  refine ⟨hble, ?_, fun i hi => ?_⟩
  · rw [← hcell, hF, getD_arrOf _ hbase]
  · have haddr : ((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) + (1 + i)
        < N * ℓp * (hb + 1) :=
      slotAddr_lt v.2 p.2 (by omega)
    rw [← Nat.add_assoc] at haddr
    rw [← hcells i hi, hF, getD_arrOf _ haddr]

/-- Reassembling a `HistArr` region from the slot facts. -/
theorem histArr_of_slotEnc {N ℓp hb : ℕ} {a : String}
    {hist : Fin N → Fin ℓp → List (Fin N)} {σ : Env} {F : ℕ → ℕ}
    (hF : σ.arrs a = arrOf (N * ℓp * (hb + 1)) F)
    (h : ∀ (v : Fin N) (p : Fin ℓp), SlotEnc ℓp hb F v p (hist v p)) :
    HistArr a ℓp hb hist σ := by
  refine ⟨by rw [hF, length_arrOf], fun v p => ?_⟩
  obtain ⟨hble, hcell, hcells⟩ := h v p
  have hbase : ((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) < N * ℓp * (hb + 1) := by
    have := slotAddr_lt (o := 0) v.2 p.2 (Nat.zero_le hb)
    omega
  refine ⟨hble, ?_, fun i hi => ?_⟩
  · rw [hF, getD_arrOf _ hbase]
    exact hcell
  · have haddr : ((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) + (1 + i)
        < N * ℓp * (hb + 1) :=
      slotAddr_lt v.2 p.2 (by omega)
    rw [← Nat.add_assoc] at haddr
    rw [hF, getD_arrOf _ haddr]
    exact hcells i hi

/-- A `HistArr` fact only reads the region's contents. -/
theorem histArr_congr_arrs {N ℓp hb : ℕ} {a : String}
    {hist : Fin N → Fin ℓp → List (Fin N)} {σ σ' : Env}
    (h : HistArr a ℓp hb hist σ) (heq : σ'.arrs a = σ.arrs a) :
    HistArr a ℓp hb hist σ' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [heq]; exact h1, fun v p => ?_⟩
  obtain ⟨hble, hcell, hcells⟩ := h2 v p
  exact ⟨hble, by rw [heq]; exact hcell, fun i hi => by rw [heq]; exact hcells i hi⟩

/-! ## §3 The programs -/

/-- The routine's scratch cells (fixed names; the arrays are
parameters): the six inputs `N`/`ns`/`d`/`ℓp`/`hb`/`e`, the owner, the
slot pointer, the slot value, the vertex cursor, the walk cursor, the
name counter, the slot base / reset index. -/
def spScalars : List String :=
  ["sp.n", "sp.m", "sp.r", "sp.l", "sp.h", "sp.p",
    "sp.u", "sp.j", "sp.w", "sp.v", "sp.x", "sp.k", "sp.i"]

/-- Reset the parent region to the sentinel `N`: the region may be
dirty on entry, the routine cleans the scratch it uses. -/
def spReset (pa : String) : Com :=
  .seq (.assign "sp.i" (.lit 0))
    (.while (.lt (.var "sp.i") (.var "sp.n"))
      (.seq (.store pa (.var "sp.i") (.var "sp.n"))
        (.assign "sp.i" (.add (.var "sp.i") (.lit 1)))))

/-- One turn of the parent pass: inside the owner's row, take the slot
and, if its target is strictly closer than the owner **and smaller
than the owner's parent cell**, store it — the running minimum lives
in the cell itself, which is the whole least-ness mechanism; at the
row's end, move the owner on. -/
def spTurn (oa ta da pa : String) : Com :=
  .ite (.lt (.var "sp.j") (.get oa (.add (.var "sp.u") (.lit 1))))
    (.seq (Csr.slot ta "sp.j" "sp.w")
      (.seq
        (.ite (.lt (.get da (.var "sp.w")) (.get da (.var "sp.u")))
          (.ite (.lt (.var "sp.w") (.get pa (.var "sp.u")))
            (.store pa (.var "sp.u") (.var "sp.w"))
            .skip)
          .skip)
        (.assign "sp.j" (.add (.var "sp.j") (.lit 1)))))
    (.assign "sp.u" (.add (.var "sp.u") (.lit 1)))

/-- **The least-parent pass**: reset the parent region to the
sentinel, then one owner-advancing pass over the whole slot array
keeping each row's running minimum in the owner's cell. -/
def parentCom (oa ta da pa : String) : Com :=
  .seq (spReset pa)
    (.seq (.assign "sp.u" (.lit 0))
      (.seq (.assign "sp.j" (.lit 0))
        (Csr.scan "sp.j" "sp.m" (spTurn oa ta da pa))))

/-- One vertex of the walk pass: compute the slot base
`(v·ℓp + e)·(hb + 1)`; if the vertex is reached, write it and walk the
parent cells to the source, appending each name and finally the count;
otherwise write the empty list's count `0`; advance. -/
def histWalkBody (da pa ha : String) : Com :=
  .seq (.assign "sp.i"
      (.mul (.add (.mul (.var "sp.v") (.var "sp.l")) (.var "sp.p"))
        (.add (.var "sp.h") (.lit 1))))
    (.seq
      (.ite (.lt (.get da (.var "sp.v")) (.add (.var "sp.r") (.lit 1)))
        (.seq (.assign "sp.x" (.var "sp.v"))
          (.seq (.assign "sp.k" (.lit 0))
            (.seq (.store ha (.add (.var "sp.i") (.lit 1)) (.var "sp.x"))
              (.seq
                (.while (.lt (.lit 0) (.get da (.var "sp.x")))
                  (.seq (.assign "sp.x" (.get pa (.var "sp.x")))
                    (.seq (.assign "sp.k" (.add (.var "sp.k") (.lit 1)))
                      (.store ha
                        (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k"))
                        (.var "sp.x")))))
                (.store ha (.var "sp.i") (.add (.var "sp.k") (.lit 1)))))))
        (.store ha (.var "sp.i") (.lit 0)))
      (.assign "sp.v" (.add (.var "sp.v") (.lit 1))))

/-- **The walk pass**: one scan over the vertices, each reached vertex
materializing its gradient walk into its `HistArr` slot of the current
round. -/
def histCom (da pa ha : String) : Com :=
  .seq (.assign "sp.v" (.lit 0))
    (.while (.lt (.var "sp.v") (.var "sp.n")) (histWalkBody da pa ha))

/-- **The supports stage**: the least-parent pass, then the walks. -/
def supportsCom (oa ta da pa ha : String) : Com :=
  .seq (parentCom oa ta da pa) (histCom da pa ha)

/-! The frame data, computed once — consumers apply
`(supportsCom_spec …).frame` and read the untouched state off these. -/

theorem wvars_parentCom (oa ta da pa : String) :
    (parentCom oa ta da pa).wvars =
      ["sp.i", "sp.i", "sp.u", "sp.j", "sp.w", "sp.j", "sp.u"] := rfl

theorem warrs_parentCom (oa ta da pa : String) :
    (parentCom oa ta da pa).warrs = [pa, pa] := rfl

theorem wvars_histCom (da pa ha : String) :
    (histCom da pa ha).wvars =
      ["sp.v", "sp.i", "sp.x", "sp.k", "sp.x", "sp.k", "sp.v"] := rfl

theorem warrs_histCom (da pa ha : String) :
    (histCom da pa ha).warrs = [ha, ha, ha, ha] := rfl

theorem wvars_supportsCom (oa ta da pa ha : String) :
    (supportsCom oa ta da pa ha).wvars =
      ["sp.i", "sp.i", "sp.u", "sp.j", "sp.w", "sp.j", "sp.u",
        "sp.v", "sp.i", "sp.x", "sp.k", "sp.x", "sp.k", "sp.v"] := rfl

/-- Every cell the routine writes is scratch. -/
theorem wvars_supportsCom_subset (oa ta da pa ha : String) :
    ∀ y ∈ (supportsCom oa ta da pa ha).wvars, y ∈ spScalars := by
  rw [wvars_supportsCom]
  decide

/-- Only the parent region and the channel region are written. -/
theorem warrs_supportsCom (oa ta da pa ha : String) :
    (supportsCom oa ta da pa ha).warrs = [pa, pa, ha, ha, ha, ha] := rfl

theorem noWrite_supportsCom (oa ta da pa ha : String) :
    (supportsCom oa ta da pa ha).NoWrite := by
  simp [supportsCom, parentCom, spReset, spTurn, histCom, histWalkBody,
    Csr.scan, Csr.slot, Com.NoWrite]

theorem not_reads_supportsCom (oa ta da pa ha : String) :
    ¬ (supportsCom oa ta da pa ha).reads := by
  simp [supportsCom, parentCom, spReset, spTurn, histCom, histWalkBody,
    Csr.scan, Csr.slot, Com.reads]

/-! ## §4 The budget -/

/-- The parent pass: the reset (`11·N`), one owner-advancing pass
(`28` a slot, `11` a row) — the `O(N + 2M)` term. -/
def parentK (N ns : ℕ) : ℕ := 26 * N + 32 * ns + 14

/-- One vertex of the walk pass: the address arithmetic, the reached
test, `19` per gradient hop (`≤ d` hops), the two writes, the
advance. -/
def histKb (d : ℕ) : ℕ := 19 * d + 40

/-- The walk pass: `Σ_reached (D v + 1)` priced at the schedule
ceiling `d + 1` per vertex. -/
def histK (N d : ℕ) : ℕ := (histKb d + 4) * N + 6

/-- **The routine's budget**: the parent pass plus the walks —
`supportsCharge`'s two terms at machine constants. -/
def supportsK (N ns d : ℕ) : ℕ := parentK N ns + histK N d

/-- The envelope, F7's reconciliation form: `supportsCharge_le`'s
`(d + 2) · ballNorm` shape with the touched measure closed to the
whole CSR at a schedule constant. -/
theorem supportsK_le (N ns d : ℕ) :
    supportsK N ns d ≤ 35 * (d + 2) * (N + ns + 1) := by
  have key : supportsK N ns d = (19 * d + 70) * N + 32 * ns + 20 := by
    simp only [supportsK, parentK, histK, histKb]
    ring
  have expand : 35 * (d + 2) * (N + ns + 1)
      = (35 * d + 70) * N + (35 * d + 70) * ns + (35 * d + 70) := by
    ring
  have hN : (19 * d + 70) * N ≤ (35 * d + 70) * N :=
    Nat.mul_le_mul_right N (by omega)
  have hns : 32 * ns ≤ (35 * d + 70) * ns :=
    Nat.mul_le_mul_right ns (by omega)
  omega

/-! ## §5 The reset -/

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

/-- The reset's specification: the parent region becomes the constant
sentinel array. -/
theorem spReset_spec (B N : ℕ) (pa : String) (hNB : N < B) :
    Spec B
      (fun σ => (σ.arrs pa).length = N ∧ σ.vars "sp.n" = N)
      (spReset pa)
      (fun _ σ' => σ'.arrs pa = arrOf N fun _ => N)
      (11 * N + 6) := by
  classical
  set I : Env → Prop := fun σ =>
    σ.vars "sp.n" = N ∧ σ.vars "sp.i" ≤ N ∧
      ∃ f, σ.arrs pa = arrOf N f ∧ ∀ p < σ.vars "sp.i", f p = N with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "sp.i" < N)
      (.seq (.store pa (.var "sp.i") (.var "sp.n"))
        (.assign "sp.i" (.add (.var "sp.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "sp.i" = σ.vars "sp.i" + 1) 7 := by
    intro σ hσ
    obtain ⟨⟨hn, hiN, f, hf, hpre⟩, hlt⟩ := hσ
    have hiB : σ.vars "sp.i" < B := by omega
    have hidx : σ.vars "sp.i" < (σ.arrs pa).length := by
      rw [hf, length_arrOf]; omega
    have hval : (Expr.var "sp.n").evalB B σ = some N := by
      rw [← hn]
      exact evalB_var (by rw [hn]; omega)
    have hstore : Run B (.store pa (.var "sp.i") (.var "sp.n"))
        σ (σ.setArr pa (σ.vars "sp.i") N) 3 :=
      (Run.store (evalB_var hiB) hval hidx).mono (by simp)
    set σ₁ := σ.setArr pa (σ.vars "sp.i") N with hσ₁
    have hassign : Run B (.assign "sp.i" (.add (.var "sp.i") (.lit 1)))
        σ₁ (σ₁.setVar "sp.i" (σ.vars "sp.i" + 1)) 4 := by
      have hev : (Expr.add (.var "sp.i") (.lit 1)).evalB B σ₁
          = some (σ.vars "sp.i" + 1) := by
        have h := evalB_incr (B := B) (x := "sp.i") (σ := σ₁)
          (by rw [hσ₁, vars_setArr]; omega)
        rw [hσ₁] at h ⊢
        simpa using h
      exact (Run.assign hev).mono (by simp)
    refine ⟨_, (hstore.seq hassign).mono (by omega),
      ⟨by simp [hσ₁, hn], by simp [hσ₁]; omega, ?_⟩,
      by simp [hσ₁]⟩
    refine ⟨fun p => if p = σ.vars "sp.i" then N else f p, ?_, ?_⟩
    · simp [hσ₁, hf, set_arrOf]
    · intro p hp
      simp [hσ₁] at hp
      show (if p = σ.vars "sp.i" then N else f p) = N
      by_cases hpe : p = σ.vars "sp.i"
      · rw [if_pos hpe]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hmain := Spec.forRangeZero (B := B) "sp.i" "sp.n" I N 7 hNB
    (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) hbody
  refine ((hmain.pre ?_).post ?_).mono (by omega)
  · rintro σ ⟨hlen, hn⟩
    refine ⟨by simp [hn], by simp, ?_⟩
    refine ⟨fun p => (σ.arrs pa).getD p 0, ?_, by simp⟩
    simp only [arrs_setVar]
    rw [← hlen]
    exact (arrOf_getD (σ.arrs pa)).symm
  · rintro σ σ' hσ ⟨⟨-, -, f, hf, hall⟩, hiN⟩
    rw [hf]
    exact arrOf_congr fun p hp => hall p (by omega)

/-! ## §6 The parent pass -/

section Supports

variable {B N ns d ℓp hb : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {oa ta da pa ha : String} {off tgt : ℕ → ℕ} {D : Fin N → ℕ}

/-- **The row-end identification**: a cell that bounds every
strictly-closer target of the full row from below and is itself such a
target (or the untouched sentinel) is exactly `leastParent`. This is
where least-ness is proved, off the row's unsorted reality. -/
theorem row_min_eq_leastParent
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    {u b : ℕ} (hu : u < N)
    (h1 : ∀ q, off u ≤ q → q < off (u + 1) →
      supTab D 0 (tgt q) < supTab D 0 u → b ≤ tgt q)
    (h2 : b = N ∨ ∃ q, off u ≤ q ∧ q < off (u + 1) ∧ tgt q = b ∧ b < N ∧
      supTab D 0 b < supTab D 0 u) :
    b = leastParent G D ⟨u, hu⟩ := by
  have key : ∀ w : Fin N, w ∈ parents G D ⟨u, hu⟩ ↔
      ∃ q, off u ≤ q ∧ q < off (u + 1) ∧ tgt q = (w : ℕ) ∧
        supTab D 0 (w : ℕ) < supTab D 0 u := by
    intro w
    rw [mem_parents_iff]
    constructor
    · rintro ⟨hAdj, hlt⟩
      have hrow : (w : ℕ) ∈ Csr.row off tgt u := by
        have := (hadj ⟨u, hu⟩ (w : ℕ)).mpr ⟨w.2, by simpa using hAdj.symm⟩
        simpa using this
      obtain ⟨q, hq1, hq2, hq3⟩ := mem_row_iff.mp hrow
      refine ⟨q, hq1, hq2, hq3, ?_⟩
      rw [supTab_coe, supTab_of_lt D 0 hu]
      exact hlt
    · rintro ⟨q, hq1, hq2, hq3, hlt⟩
      have hrow : (w : ℕ) ∈ Csr.row off tgt u :=
        mem_row_iff.mpr ⟨q, hq1, hq2, hq3⟩
      obtain ⟨hw, hAdj⟩ := (hadj ⟨u, hu⟩ (w : ℕ)).mp (by simpa using hrow)
      rw [supTab_coe, supTab_of_lt D 0 hu] at hlt
      exact ⟨by simpa using hAdj.symm, hlt⟩
  by_cases hne : (parents G D ⟨u, hu⟩).Nonempty
  · set m := (parents G D ⟨u, hu⟩).min' hne with hm
    obtain ⟨qm, hqm1, hqm2, hqm3, hqm4⟩ :=
      (key m).mp ((parents G D ⟨u, hu⟩).min'_mem hne)
    have hbm : b ≤ (m : ℕ) := by
      have := h1 qm hqm1 hqm2 (by rw [hqm3]; exact hqm4)
      omega
    have hbN : b < N := lt_of_le_of_lt hbm m.2
    rcases h2 with hb2 | ⟨q, hq1, hq2, hq3, -, hq5⟩
    · omega
    · have hmem : (⟨b, hbN⟩ : Fin N) ∈ parents G D ⟨u, hu⟩ :=
        (key ⟨b, hbN⟩).mpr ⟨q, hq1, hq2, hq3, hq5⟩
      have hmb : m ≤ ⟨b, hbN⟩ := Finset.min'_le _ _ hmem
      have : (m : ℕ) ≤ b := hmb
      rw [leastParent, dif_pos hne, ← hm]
      omega
  · rw [leastParent, dif_neg hne]
    rcases h2 with hb2 | ⟨q, hq1, hq2, hq3, hbN, hq5⟩
    · exact hb2
    · exact absurd ⟨_, (key ⟨b, hbN⟩).mpr ⟨q, hq1, hq2, hq3, hq5⟩⟩ hne

/-- An empty row has no parents: the sentinel is already correct. -/
theorem leastParent_of_empty_row
    (hadj : ∀ (v : Fin N) (w : ℕ),
      w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
    {u : ℕ} (hu : u < N) (hrow : off (u + 1) ≤ off u) :
    leastParent G D ⟨u, hu⟩ = N := by
  rw [leastParent, dif_neg]
  rintro ⟨w, hw⟩
  rw [mem_parents_iff] at hw
  have hrw : (w : ℕ) ∈ Csr.row off tgt u := by
    have := (hadj ⟨u, hu⟩ (w : ℕ)).mpr ⟨w.2, by simpa using hw.1.symm⟩
    simpa using this
  obtain ⟨q, hq1, hq2, -⟩ := mem_row_iff.mp hrw
  omega

/-- The invariant of the parent pass: the CSR, the cells, the owner
discipline (the slot pointer never overtakes the owner's row end),
the untouched distance region, and the parent region — finalized
below the owner, sentinel above it, the running row minimum in the
owner's own cell. -/
def ParentInv (oa ta da pa : String) (ns : ℕ) (off tgt : ℕ → ℕ)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (D : Fin N → ℕ)
    (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧
    σ.vars "sp.m" = ns ∧
    σ.vars "sp.u" ≤ N ∧ σ.vars "sp.j" ≤ ns ∧
    off (σ.vars "sp.u") ≤ σ.vars "sp.j" ∧
    (σ.vars "sp.u" < N → σ.vars "sp.j" ≤ off (σ.vars "sp.u" + 1)) ∧
    σ.arrs da = arrOf N (supTab D 0) ∧
    ∃ P : ℕ → ℕ,
      σ.arrs pa = arrOf N P ∧
      (∀ q, q < N → P q ≤ N) ∧
      (σ.vars "sp.u" < N →
        (∀ q, off (σ.vars "sp.u") ≤ q → q < σ.vars "sp.j" →
          supTab D 0 (tgt q) < supTab D 0 (σ.vars "sp.u") →
            P (σ.vars "sp.u") ≤ tgt q) ∧
        (P (σ.vars "sp.u") = N ∨
          ∃ q, off (σ.vars "sp.u") ≤ q ∧ q < σ.vars "sp.j" ∧
            tgt q = P (σ.vars "sp.u") ∧ P (σ.vars "sp.u") < N ∧
            supTab D 0 (P (σ.vars "sp.u")) < supTab D 0 (σ.vars "sp.u"))) ∧
      (∀ w : Fin N, (w : ℕ) < σ.vars "sp.u" → P (w : ℕ) = leastParent G D w) ∧
      (∀ q, σ.vars "sp.u" < q → q < N → P q = N)

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoff0 : off 0 = 0)
  (hNB : N < B) (hnsB : ns < B)
  (hDB : ∀ v : Fin N, D v < B)
  (hpa_oa : pa ≠ oa) (hpa_ta : pa ≠ ta) (hpa_da : pa ≠ da)

include hadj hNB hnsB hDB hpa_oa hpa_ta hpa_da in
/-- **One turn of the parent pass**, in `ownerScan_spec`'s step form:
it either takes a slot (keeping the running row minimum in the owner's
cell) or moves the owner on, keeps the invariant, and costs `28` per
slot moved, `11` per row moved. -/
theorem spTurn_step :
    ∀ σ, ParentInv oa ta da pa ns off tgt G D σ → σ.vars "sp.j" < ns →
      ∃ σ' K', Run B (spTurn oa ta da pa) σ σ' K' ∧
        ParentInv oa ta da pa ns off tgt G D σ' ∧
        σ.vars "sp.j" ≤ σ'.vars "sp.j" ∧ σ.vars "sp.u" ≤ σ'.vars "sp.u" ∧
        (σ.vars "sp.j" < σ'.vars "sp.j" ∨ σ.vars "sp.u" < σ'.vars "sp.u") ∧
        K' ≤ 28 * (σ'.vars "sp.j" - σ.vars "sp.j")
          + 11 * (σ'.vars "sp.u" - σ.vars "sp.u") := by
  rintro σ ⟨hc, hm, hu, hj, hlo, hhi, hda, P, hpa, hPle, hrun, hdone, hvir⟩ hjns
  have huN : σ.vars "sp.u" < N := hc.owner_lt hu hlo hjns
  set u := σ.vars "sp.u" with hu_def
  set j := σ.vars "sp.j" with hj_def
  have hDN : ∀ q, q < N → supTab D 0 q < B := by
    intro q hq
    rw [supTab_of_lt D 0 hq]
    exact hDB _
  -- the turn's test: `j < off (u+1)`
  have hoffval : (Expr.get oa (.add (.var "sp.u") (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    refine evalB_get (k := u + 1) (evalB_incr (by omega)) ?_
      (hc.off_lt hnsB (by omega))
    rw [hc.offArr, getElem?_arrOf off (by omega)]
  have hcond := evalB_condLt (evalB_var (x := "sp.j") (σ := σ) (by omega)) hoffval
  by_cases hslot : j < off (u + 1)
  · -- inside the row: take the slot
    have hcondT : (Cond.lt (.var "sp.j")
        (.get oa (.add (.var "sp.u") (.lit 1)))).evalB B σ = some true := by
      rw [hcond]
      congr 1
      simpa using hslot
    set w := tgt j with hw_def
    have hwN : w < N := hc.target hjns
    -- slot read
    have hread : Run B (Csr.slot ta "sp.j" "sp.w") σ (σ.setVar "sp.w" w) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono
        (by simp)
      rw [hc.tgtArr, getElem?_arrOf tgt hjns]
    set σ₁ := σ.setVar "sp.w" w with hσ₁
    have h1u : σ₁.vars "sp.u" = u := by rw [hσ₁]; simp [hu_def]
    have h1w : σ₁.vars "sp.w" = w := by rw [hσ₁]; simp
    have h1j : σ₁.vars "sp.j" = j := by rw [hσ₁]; simp [hj_def]
    have h1da : σ₁.arrs da = arrOf N (supTab D 0) := by rw [hσ₁]; simpa using hda
    have h1pa : σ₁.arrs pa = arrOf N P := by rw [hσ₁]; simpa using hpa
    -- the candidate test: `D w < D u`
    have hcandEv : (Cond.lt (.get da (.var "sp.w")) (.get da (.var "sp.u"))).evalB
        B σ₁ = some (decide (supTab D 0 w < supTab D 0 u)) := by
      refine evalB_condLt
        (evalB_get (evalB_var (by rw [h1w]; omega)) ?_ (hDN w hwN))
        (evalB_get (evalB_var (by rw [h1u]; omega)) ?_ (hDN u huN))
      · rw [h1da, h1w, getElem?_arrOf _ hwN]
      · rw [h1da, h1u, getElem?_arrOf _ huN]
    by_cases hcand : supTab D 0 w < supTab D 0 u
    · have hcandT : (Cond.lt (.get da (.var "sp.w"))
          (.get da (.var "sp.u"))).evalB B σ₁ = some true := by
        rw [hcandEv]
        congr 1
        simpa using hcand
      -- the improvement test: `w < pa[u]`
      have himpEv : (Cond.lt (.var "sp.w") (.get pa (.var "sp.u"))).evalB B σ₁
          = some (decide (w < P u)) := by
        refine evalB_condLt (by rw [← h1w]; exact evalB_var (by rw [h1w]; omega))
          (evalB_get (evalB_var (by rw [h1u]; omega)) ?_ (by have := hPle u huN; omega))
        rw [h1pa, h1u, getElem?_arrOf _ huN]
      by_cases himp : w < P u
      · -- improve: store the new running minimum
        have himpT : (Cond.lt (.var "sp.w") (.get pa (.var "sp.u"))).evalB B σ₁
            = some true := by
          rw [himpEv]
          congr 1
          simpa using himp
        have hst : Run B (.store pa (.var "sp.u") (.var "sp.w"))
            σ₁ (σ₁.setArr pa u w) 3 := by
          have huev : (Expr.var "sp.u").evalB B σ₁ = some u := by
            rw [← h1u]
            exact evalB_var (by rw [h1u]; omega)
          have hwev : (Expr.var "sp.w").evalB B σ₁ = some w := by
            rw [← h1w]
            exact evalB_var (by rw [h1w]; omega)
          refine (Run.store huev hwev ?_).mono (by simp)
          rw [h1pa, length_arrOf]
          exact huN
        set σ₂ := σ₁.setArr pa u w with hσ₂
        have hinc : Run B (.assign "sp.j" (.add (.var "sp.j") (.lit 1)))
            σ₂ (σ₂.setVar "sp.j" (j + 1)) 4 := by
          have h2j : σ₂.vars "sp.j" = j := by rw [hσ₂]; simpa using h1j
          have hev := evalB_incr (B := B) (x := "sp.j") (σ := σ₂)
            (by rw [h2j]; omega)
          rw [h2j] at hev
          exact (Run.assign hev).mono (by simp)
        set σ' := σ₂.setVar "sp.j" (j + 1) with hσ'
        have hrun' : Run B (spTurn oa ta da pa) σ σ' 28 := by
          have hInner : Run B (.ite (.lt (.var "sp.w") (.get pa (.var "sp.u")))
              (.store pa (.var "sp.u") (.var "sp.w")) .skip) σ₁ σ₂ 8 :=
            (Run.ite_true himpT hst).mono (by simp)
          have hOuter : Run B (.ite (.lt (.get da (.var "sp.w"))
              (.get da (.var "sp.u")))
              (.ite (.lt (.var "sp.w") (.get pa (.var "sp.u")))
                (.store pa (.var "sp.u") (.var "sp.w")) .skip)
              .skip) σ₁ σ₂ 14 :=
            (Run.ite_true hcandT hInner).mono (by simp)
          have hSeq : Run B (.seq (Csr.slot ta "sp.j" "sp.w")
              (.seq (.ite (.lt (.get da (.var "sp.w")) (.get da (.var "sp.u")))
                (.ite (.lt (.var "sp.w") (.get pa (.var "sp.u")))
                  (.store pa (.var "sp.u") (.var "sp.w")) .skip)
                .skip)
                (.assign "sp.j" (.add (.var "sp.j") (.lit 1))))) σ σ' 21 :=
            (hread.seq (hOuter.seq hinc)).mono (by simp)
          exact (Run.ite_true hcondT hSeq).mono (by simp)
        have h'j : σ'.vars "sp.j" = j + 1 := by rw [hσ']; simp
        have h'u : σ'.vars "sp.u" = u := by rw [hσ', hσ₂, hσ₁]; simp [hu_def]
        have h'vars : ∀ y, y ≠ "sp.j" → y ≠ "sp.w" → σ'.vars y = σ.vars y := by
          intro y hy1 hy2
          rw [hσ', hσ₂, hσ₁]
          simp [hy1, hy2]
        have h'pa : σ'.arrs pa = (arrOf N P).set u w := by
          rw [hσ', hσ₂, hσ₁]
          simp [hpa]
        have h'other : ∀ b, b ≠ pa → σ'.arrs b = σ.arrs b := by
          intro b hb
          rw [hσ', hσ₂, hσ₁]
          simp [hb]
        set P' : ℕ → ℕ := fun q => if q = u then w else P q with hP'_def
        have hP'u : P' u = w := by
          show (if u = u then w else P u) = w
          rw [if_pos rfl]
        have hP'ne : ∀ q, q ≠ u → P' q = P q := by
          intro q hq
          show (if q = u then w else P q) = P q
          rw [if_neg hq]
        refine ⟨σ', 28, hrun',
          ⟨hc.of_eq (h'other oa (Ne.symm hpa_oa)) (h'other ta (Ne.symm hpa_ta)),
            by rw [h'vars _ (by decide) (by decide)]; exact hm,
            by rw [h'u]; exact hu,
            by rw [h'j]; omega,
            by rw [h'u, h'j]; omega,
            by rw [h'u, h'j]; intro h; omega,
            by rw [h'other da (Ne.symm hpa_da)]; exact hda,
            P', ?_, ?_, ?_, ?_, ?_⟩,
          by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
          by rw [h'j, h'u]; omega⟩
        · rw [h'pa, set_arrOf, hP'_def]
        · intro q hq
          by_cases hqu : q = u
          · rw [hqu, hP'u]; omega
          · rw [hP'ne q hqu]
            exact hPle q hq
        · rw [h'u, h'j]
          intro _
          obtain ⟨hr1, -⟩ := hrun huN
          constructor
          · intro q hq1 hq2 hq3
            rw [hP'u]
            rcases Nat.lt_or_ge q j with hqj | hqj
            · exact le_trans (le_of_lt himp) (hr1 q hq1 hqj hq3)
            · have : q = j := by omega
              subst this
              omega
          · right
            exact ⟨j, hlo, by omega, by rw [hP'u],
              by rw [hP'u]; omega, by rw [hP'u]; exact hcand⟩
        · intro x hx
          rw [h'u] at hx
          rw [hP'ne _ (by omega)]
          exact hdone x hx
        · intro q hq1 hq2
          rw [h'u] at hq1
          rw [hP'ne _ (by omega)]
          exact hvir q hq1 hq2
      · -- no improvement: the cell already holds something at most `w`
        have himpF : (Cond.lt (.var "sp.w") (.get pa (.var "sp.u"))).evalB B σ₁
            = some false := by
          rw [himpEv]
          congr 1
          simpa using himp
        set σ' := σ₁.setVar "sp.j" (j + 1) with hσ'
        have hinc : Run B (.assign "sp.j" (.add (.var "sp.j") (.lit 1)))
            σ₁ σ' 4 := by
          have hev := evalB_incr (B := B) (x := "sp.j") (σ := σ₁)
            (by rw [h1j]; omega)
          rw [h1j] at hev
          exact (Run.assign hev).mono (by simp)
        have hrun' : Run B (spTurn oa ta da pa) σ σ' 28 := by
          have hOuter : Run B (.ite (.lt (.get da (.var "sp.w"))
              (.get da (.var "sp.u")))
              (.ite (.lt (.var "sp.w") (.get pa (.var "sp.u")))
                (.store pa (.var "sp.u") (.var "sp.w")) .skip)
              .skip) σ₁ σ₁ 14 :=
            (Run.ite_true hcandT (Run.ite_false himpF Run.skip)).mono (by simp)
          have hSeq := (hread.seq (hOuter.seq hinc)).mono
            (show 3 + (14 + 4) ≤ 21 by omega)
          exact (Run.ite_true hcondT hSeq).mono (by simp)
        have h'j : σ'.vars "sp.j" = j + 1 := by rw [hσ']; simp
        have h'u : σ'.vars "sp.u" = u := by rw [hσ', hσ₁]; simp [hu_def]
        have h'vars : ∀ y, y ≠ "sp.j" → y ≠ "sp.w" → σ'.vars y = σ.vars y := by
          intro y hy1 hy2
          rw [hσ', hσ₁]
          simp [hy1, hy2]
        have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
          intro b
          rw [hσ', hσ₁]
          simp
        refine ⟨σ', 28, hrun',
          ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
            by rw [h'vars _ (by decide) (by decide)]; exact hm,
            by rw [h'u]; exact hu,
            by rw [h'j]; omega,
            by rw [h'u, h'j]; omega,
            by rw [h'u, h'j]; intro h; omega,
            by rw [h'arrs]; exact hda,
            P, by rw [h'arrs]; exact hpa, hPle, ?_, ?_, ?_⟩,
          by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
          by rw [h'j, h'u]; omega⟩
        · rw [h'u, h'j]
          intro _
          obtain ⟨hr1, hr2⟩ := hrun huN
          constructor
          · intro q hq1 hq2 hq3
            rcases Nat.lt_or_ge q j with hqj | hqj
            · exact hr1 q hq1 hqj hq3
            · have : q = j := by omega
              subst this
              rw [← hw_def]
              omega
          · rcases hr2 with h | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
            · exact Or.inl h
            · exact Or.inr ⟨q, hq1, by omega, hq3, hq4, hq5⟩
        · intro x hx
          rw [h'u] at hx
          exact hdone x hx
        · intro q hq1 hq2
          rw [h'u] at hq1
          exact hvir q hq1 hq2
    · -- not a candidate: skip the slot
      have hcandF : (Cond.lt (.get da (.var "sp.w"))
          (.get da (.var "sp.u"))).evalB B σ₁ = some false := by
        rw [hcandEv]
        congr 1
        simpa using hcand
      set σ' := σ₁.setVar "sp.j" (j + 1) with hσ'
      have hinc : Run B (.assign "sp.j" (.add (.var "sp.j") (.lit 1)))
          σ₁ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "sp.j") (σ := σ₁)
          (by rw [h1j]; omega)
        rw [h1j] at hev
        exact (Run.assign hev).mono (by simp)
      have hrun' : Run B (spTurn oa ta da pa) σ σ' 28 := by
        have hOuter : Run B (.ite (.lt (.get da (.var "sp.w"))
            (.get da (.var "sp.u")))
            (.ite (.lt (.var "sp.w") (.get pa (.var "sp.u")))
              (.store pa (.var "sp.u") (.var "sp.w")) .skip)
            .skip) σ₁ σ₁ 14 :=
          (Run.ite_false hcandF Run.skip).mono (by simp)
        have hSeq := (hread.seq (hOuter.seq hinc)).mono
          (show 3 + (14 + 4) ≤ 21 by omega)
        exact (Run.ite_true hcondT hSeq).mono (by simp)
      have h'j : σ'.vars "sp.j" = j + 1 := by rw [hσ']; simp
      have h'u : σ'.vars "sp.u" = u := by rw [hσ', hσ₁]; simp [hu_def]
      have h'vars : ∀ y, y ≠ "sp.j" → y ≠ "sp.w" → σ'.vars y = σ.vars y := by
        intro y hy1 hy2
        rw [hσ', hσ₁]
        simp [hy1, hy2]
      have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
        intro b
        rw [hσ', hσ₁]
        simp
      refine ⟨σ', 28, hrun',
        ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
          by rw [h'vars _ (by decide) (by decide)]; exact hm,
          by rw [h'u]; exact hu,
          by rw [h'j]; omega,
          by rw [h'u, h'j]; omega,
          by rw [h'u, h'j]; intro h; omega,
          by rw [h'arrs]; exact hda,
          P, by rw [h'arrs]; exact hpa, hPle, ?_, ?_, ?_⟩,
        by rw [h'j]; omega, by rw [h'u], by rw [h'j]; omega,
        by rw [h'j, h'u]; omega⟩
      · rw [h'u, h'j]
        intro _
        obtain ⟨hr1, hr2⟩ := hrun huN
        constructor
        · intro q hq1 hq2 hq3
          rcases Nat.lt_or_ge q j with hqj | hqj
          · exact hr1 q hq1 hqj hq3
          · have : q = j := by omega
            subst this
            rw [← hw_def] at hq3
            omega
        · rcases hr2 with h | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
          · exact Or.inl h
          · exact Or.inr ⟨q, hq1, by omega, hq3, hq4, hq5⟩
      · intro x hx
        rw [h'u] at hx
        exact hdone x hx
      · intro q hq1 hq2
        rw [h'u] at hq1
        exact hvir q hq1 hq2
  · -- at the row's end: the cell holds the row minimum — finalize
    have hcondF : (Cond.lt (.var "sp.j")
        (.get oa (.add (.var "sp.u") (.lit 1)))).evalB B σ = some false := by
      rw [hcond]
      congr 1
      simpa using hslot
    have hjeq : j = off (u + 1) := by
      have := hhi huN
      omega
    set σ' := σ.setVar "sp.u" (u + 1) with hσ'
    have hrun' : Run B (spTurn oa ta da pa) σ σ' 11 := by
      have hass : Run B (.assign "sp.u" (.add (.var "sp.u") (.lit 1))) σ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "sp.u") (σ := σ) (by omega)
        exact (Run.assign hev).mono (by simp)
      exact (Run.ite_false hcondF hass).mono (by simp)
    have h'u : σ'.vars "sp.u" = u + 1 := by rw [hσ']; simp
    have h'vars : ∀ y, y ≠ "sp.u" → σ'.vars y = σ.vars y := by
      intro y hy
      rw [hσ']
      simp [hy]
    have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := fun b => by rw [hσ']; simp
    have hufin : P u = leastParent G D ⟨u, huN⟩ := by
      obtain ⟨hr1, hr2⟩ := hrun huN
      refine row_min_eq_leastParent hadj huN ?_ ?_
      · intro q hq1 hq2 hq3
        exact hr1 q hq1 (by omega) hq3
      · rcases hr2 with h | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, hq1, by omega, hq3, hq4, hq5⟩
    refine ⟨σ', 11, hrun',
      ⟨hc.of_eq (h'arrs oa) (h'arrs ta),
        by rw [h'vars "sp.m" (by decide)]; exact hm,
        by rw [h'u]; omega,
        by rw [h'vars "sp.j" (by decide)]; omega,
        by rw [h'u, h'vars "sp.j" (by decide)]; omega,
        ?_,
        by rw [h'arrs]; exact hda,
        P, by rw [h'arrs]; exact hpa, hPle, ?_, ?_, ?_⟩,
      by rw [h'vars "sp.j" (by decide)], by rw [h'u]; omega,
      by rw [h'u]; omega,
      by rw [h'u, h'vars "sp.j" (by decide)]; omega⟩
    · rw [h'u, h'vars "sp.j" (by decide)]
      intro h
      have := hc.off_le_succ h
      omega
    · rw [h'u, h'vars "sp.j" (by decide)]
      intro hu1N
      constructor
      · intro q hq1 hq2 hq3
        omega
      · left
        exact hvir (u + 1) (by omega) hu1N
    · intro x hx
      rw [h'u] at hx
      rcases Nat.lt_or_ge (x : ℕ) u with hxu | hxu
      · exact hdone x hxu
      · have hxeq : (x : ℕ) = u := by omega
        have hxv : x = ⟨u, huN⟩ := Fin.ext hxeq
        rw [hxv]
        simpa using hufin
    · intro q hq1 hq2
      rw [h'u] at hq1
      exact hvir q (by omega) hq2

include hadj hoff0 hNB hnsB hDB hpa_oa hpa_ta hpa_da in
/-- **The least-parent pass, discharged**: from the CSR, the two input
cells and a length-`N` parent region (dirty is fine — the pass resets
it), `parentCom` leaves `leastParent G D` in the parent region and the
distance region untouched. Cost `parentK N ns`. -/
theorem parentCom_spec :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧
        σ.vars "sp.n" = N ∧ σ.vars "sp.m" = ns ∧
        (σ.arrs pa).length = N ∧
        (σ.arrs da).length = N ∧
        (∀ v : Fin N, (σ.arrs da).getD (v : ℕ) 0 = D v))
      (parentCom oa ta da pa)
      (fun _ σ' => Csr oa ta N ns N off tgt σ' ∧
        σ'.arrs da = arrOf N (supTab D 0) ∧
        σ'.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N))
      (parentK N ns) := by
  intro σ hσ
  obtain ⟨hc, hn, hm, hplen, hdlen, hdget⟩ := hσ
  have hdarr : σ.arrs da = arrOf N (supTab D 0) := by
    have h0 : σ.arrs da = arrOf N fun q => (σ.arrs da).getD q 0 := by
      conv_lhs => rw [← arrOf_getD (σ.arrs da)]
      rw [hdlen]
    rw [h0]
    refine arrOf_congr fun q hq => ?_
    rw [supTab_of_lt D 0 hq, ← hdget ⟨q, hq⟩]
  -- 1. the reset
  obtain ⟨σ₁, hr1, hpost1⟩ := ((spReset_spec B N pa hNB).frame).run ⟨hplen, hn⟩
  obtain ⟨hp1, hfv1, hfa1, -, -⟩ := hpost1
  have h1vars : ∀ y, y ≠ "sp.i" → σ₁.vars y = σ.vars y := fun y hy =>
    hfv1 y (by show y ∉ (spReset pa).wvars; show y ∉ ["sp.i", "sp.i"]; simp [hy])
  have h1arrs : ∀ b, b ≠ pa → σ₁.arrs b = σ.arrs b := fun b hb =>
    hfa1 b (by show b ∉ (spReset pa).warrs; show b ∉ [pa]; simp [hb])
  -- 2. the two pointer resets
  set σa := σ₁.setVar "sp.u" 0 with hσa
  set σb := σa.setVar "sp.j" 0 with hσb
  have hra : Run B (.assign "sp.u" (.lit 0)) σ₁ σa 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hrb : Run B (.assign "sp.j" (.lit 0)) σa σb 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hbvars : ∀ y, y ≠ "sp.u" → y ≠ "sp.j" → σb.vars y = σ₁.vars y := by
    intro y hy1 hy2
    rw [hσb, hσa]
    simp [hy1, hy2]
  have hbarrs : ∀ b, σb.arrs b = σ₁.arrs b := by
    intro b
    rw [hσb, hσa]
    simp
  have hbu : σb.vars "sp.u" = 0 := by rw [hσb, hσa]; simp
  have hbj : σb.vars "sp.j" = 0 := by rw [hσb]; simp
  -- 3. the pass
  have hIb : ParentInv oa ta da pa ns off tgt G D σb := by
    refine ⟨(hc.of_eq (h1arrs oa (Ne.symm hpa_oa))
        (h1arrs ta (Ne.symm hpa_ta))).of_eq (hbarrs oa) (hbarrs ta),
      by rw [hbvars _ (by decide) (by decide), h1vars _ (by decide)]; exact hm,
      by rw [hbu]; omega,
      by rw [hbj]; omega,
      by rw [hbu, hbj]; omega,
      by rw [hbu, hbj]; intro h; omega,
      by rw [hbarrs, h1arrs da (Ne.symm hpa_da)]; exact hdarr,
      fun _ => N, by rw [hbarrs]; exact hp1, fun q _ => le_rfl, ?_, ?_, ?_⟩
    · rw [hbu, hbj]
      intro _
      exact ⟨fun q hq1 hq2 hq3 => absurd hq2 (by omega), Or.inl rfl⟩
    · intro x hx
      rw [hbu] at hx
      simp at hx
    · intro q hq1 hq2
      rfl
  have hpass := Csr.ownerScan_spec (B := B) (32 * ns + 15 * N + 4) N ns 28 11
    "sp.j" "sp.m" "sp.u" (spTurn oa ta da pa)
    (P := fun τ => τ = σb)
    (I := ParentInv oa ta da pa ns off tgt G D)
    hnsB
    (fun τ hI => ⟨hI.2.1, hI.2.2.2.1, hI.2.2.1⟩)
    (spTurn_step hadj hNB hnsB hDB hpa_oa hpa_ta hpa_da)
    (fun τ hτ => hτ ▸ hIb)
    (fun τ hτ => by
      subst hτ
      have h1 : (28 + 4) * (ns - σb.vars "sp.j") ≤ 32 * ns :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : (11 + 4) * (N - σb.vars "sp.u") ≤ 15 * N :=
        Nat.mul_le_mul_left _ (by omega)
      omega)
  obtain ⟨σc, hrc, hIc, hjc⟩ := hpass.run rfl
  obtain ⟨hcc, hmc, huc, hjc', hloc, hhic, hdac, P, hpac, hPlec, hrunc, hdonec,
    hvirc⟩ := hIc
  -- 4. the final table
  have hfin : ∀ v : Fin N, P (v : ℕ) = leastParent G D v := by
    intro v
    rcases lt_trichotomy (v : ℕ) (σc.vars "sp.u") with hlt | heq | hgt
    · exact hdonec v hlt
    · have huN : σc.vars "sp.u" < N := by
        have := v.2
        omega
      have hrowdone : σc.vars "sp.j" = off (σc.vars "sp.u" + 1) := by
        have h1 := hhic huN
        have h2 := hcc.le_ns (show σc.vars "sp.u" + 1 ≤ N by omega)
        omega
      obtain ⟨hr1, hr2⟩ := hrunc huN
      have hval : P (σc.vars "sp.u") = leastParent G D ⟨σc.vars "sp.u", huN⟩ := by
        refine row_min_eq_leastParent hadj huN ?_ ?_
        · intro q hq1 hq2 hq3
          exact hr1 q hq1 (by omega) hq3
        · rcases hr2 with h | ⟨q, hq1, hq2, hq3, hq4, hq5⟩
          · exact Or.inl h
          · exact Or.inr ⟨q, hq1, by omega, hq3, hq4, hq5⟩
      have hveq : v = ⟨σc.vars "sp.u", huN⟩ := Fin.ext heq
      rw [hveq]
      simpa using hval
    · have hvir' := hvirc (v : ℕ) hgt v.2
      -- the trailing rows are empty
      have huN : σc.vars "sp.u" < N := by
        have := v.2
        omega
      have hend : off (σc.vars "sp.u" + 1) = ns := by
        have h1 := hhic huN
        have h2 := hcc.le_ns (show σc.vars "sp.u" + 1 ≤ N by omega)
        omega
      have hemp : off ((v : ℕ) + 1) ≤ off (v : ℕ) := by
        have h1 : off (σc.vars "sp.u" + 1) ≤ off (v : ℕ) :=
          hcc.mono (by omega) (by have := v.2; omega)
        have h2 : off ((v : ℕ) + 1) ≤ ns := hcc.le_ns (by have := v.2; omega)
        omega
      have hlp : leastParent G D v = N := by
        have := leastParent_of_empty_row (G := G) (D := D) hadj v.2 hemp
        simpa using this
      rw [hvir', hlp]
  refine ⟨σc, ?_, hcc, hdac, ?_⟩
  · have h := hr1.seq (hra.seq (hrb.seq hrc))
    refine h.mono ?_
    simp only [parentK]
    omega
  · rw [hpac]
    refine arrOf_congr fun q hq => ?_
    rw [supTab_of_lt _ _ hq, ← hfin ⟨q, hq⟩]

end Supports

/-! ## §7 The walk pass -/

section Walks

variable {B N ns d ℓp hb : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {da pa ha : String} {D : Fin N → ℕ}

/-- The invariant of the walk pass at cursor `sp.v`: the input cells,
the two read-only tables, and the channel region as a function whose
column-`e` slots are finished below the cursor and whose other columns
are exactly the inherited ones. -/
def HistInv (da pa ha : String) (d : ℕ) {ℓp : ℕ} (hb : ℕ) (e : Fin ℓp)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (D : Fin N → ℕ)
    (hist : Fin N → Fin ℓp → List (Fin N)) (σ : Env) : Prop :=
  σ.vars "sp.n" = N ∧ σ.vars "sp.r" = d ∧ σ.vars "sp.l" = ℓp ∧
  σ.vars "sp.h" = hb ∧ σ.vars "sp.p" = (e : ℕ) ∧
  σ.vars "sp.v" ≤ N ∧
  σ.arrs da = arrOf N (supTab D 0) ∧
  σ.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) ∧
  ∃ F : ℕ → ℕ,
    σ.arrs ha = arrOf (N * ℓp * (hb + 1)) F ∧
    (∀ v : Fin N, (v : ℕ) < σ.vars "sp.v" →
      SlotEnc ℓp hb F v e (descendCol G D d v)) ∧
    (∀ (v : Fin N) (p : Fin ℓp), p ≠ e →
      SlotEnc ℓp hb F v p (hist v p))

variable {s : Fin N} {e : Fin ℓp} {hist : Fin N → Fin ℓp → List (Fin N)}

variable
  (hD : BallTable G s d D)
  (hNB : N < B) (hdB : d + 2 < B)
  (hlB : ℓp < B) (hhB : hb + 1 < B) (hLB : N * ℓp * (hb + 1) < B)
  (hDB : ∀ v : Fin N, D v < B)
  (hdhb : d + 1 ≤ hb)
  (hha_da : ha ≠ da) (hha_pa : ha ≠ pa)

include hD hNB hdB hlB hhB hLB hDB hdhb hha_da hha_pa in
/-- **One vertex of the walk pass**: the slot base, the reached test,
the counted gradient walk (or the empty-list cell), the advance. -/
theorem histBody_step :
    Spec B
      (fun σ => HistInv da pa ha d hb e G D hist σ ∧ σ.vars "sp.v" < N)
      (histWalkBody da pa ha)
      (fun σ σ' => HistInv da pa ha d hb e G D hist σ' ∧
        σ'.vars "sp.v" = σ.vars "sp.v" + 1)
      (histKb d) := by
  rintro σ ⟨⟨hn, hr, hl, hh, hp, hvle, hda, hpa, F0, hha, hnew, hold⟩, hvN⟩
  set c := σ.vars "sp.v" with hc_def
  set vf : Fin N := ⟨c, hvN⟩ with hvf_def
  set L := N * ℓp * (hb + 1) with hL_def
  set b0 := (c * ℓp + (e : ℕ)) * (hb + 1) with hb0_def
  have hep : (e : ℕ) < ℓp := e.2
  have hcl : c * ℓp + (e : ℕ) < N * ℓp := slotIdx_lt hvN hep
  have hNlL : N * ℓp ≤ L := Nat.le_mul_of_pos_right (N * ℓp) (by omega)
  have hb0o : ∀ o, o ≤ hb → b0 + o < L := fun o ho => slotAddr_lt hvN hep ho
  have hb0L : b0 < L := by
    have := hb0o 0 (Nat.zero_le hb)
    omega
  have hclB : c * ℓp < B := by omega
  have hceB : c * ℓp + (e : ℕ) < B := by omega
  have hb0B : b0 < B := by omega
  -- 1. the slot base
  have hbase : (Expr.mul (.add (.mul (.var "sp.v") (.var "sp.l")) (.var "sp.p"))
      (.add (.var "sp.h") (.lit 1))).evalB B σ = some b0 := by
    have hev_v : (Expr.var "sp.v").evalB B σ = some c := by
      rw [hc_def]
      exact evalB_var (by omega)
    have hev_l : (Expr.var "sp.l").evalB B σ = some ℓp := by
      rw [← hl]
      exact evalB_var (by rw [hl]; omega)
    have hev_p : (Expr.var "sp.p").evalB B σ = some (e : ℕ) := by
      rw [← hp]
      exact evalB_var (by rw [hp]; omega)
    have hev_h : (Expr.var "sp.h").evalB B σ = some hb := by
      rw [← hh]
      exact evalB_var (by rw [hh]; omega)
    have h1 : (Expr.mul (.var "sp.v") (.var "sp.l")).evalB B σ = some (c * ℓp) := by
      have := evalB_bin (B := B) (op := .mul) (σ := σ) hev_v hev_l
        (by simpa using hclB)
      simpa using this
    have h2 : (Expr.add (.mul (.var "sp.v") (.var "sp.l")) (.var "sp.p")).evalB B σ
        = some (c * ℓp + (e : ℕ)) := by
      have := evalB_bin (B := B) (op := .add) (σ := σ) h1 hev_p
        (by simpa using hceB)
      simpa using this
    have h3 : (Expr.add (.var "sp.h") (.lit 1)).evalB B σ = some (hb + 1) := by
      have := evalB_bin (B := B) (op := .add) (σ := σ) hev_h
        (evalB_lit (n := 1) (by omega)) (by simpa using hhB)
      simpa using this
    have hfin := evalB_bin (B := B) (op := .mul) (σ := σ) h2 h3
      (by simp only [Bop.apply_mul]; rw [← hb0_def]; exact hb0B)
    rw [hfin]
    simp only [Bop.apply_mul]
    rw [← hb0_def]
  have hri : Run B (.assign "sp.i"
      (.mul (.add (.mul (.var "sp.v") (.var "sp.l")) (.var "sp.p"))
        (.add (.var "sp.h") (.lit 1)))) σ (σ.setVar "sp.i" b0) 10 :=
    (Run.assign hbase).mono (by simp)
  set σ₁ := σ.setVar "sp.i" b0 with hσ₁
  have h1vars : ∀ y, y ≠ "sp.i" → σ₁.vars y = σ.vars y := by
    intro y hy
    rw [hσ₁]
    simp [hy]
  have h1i : σ₁.vars "sp.i" = b0 := by rw [hσ₁]; simp
  have h1v : σ₁.vars "sp.v" = c := by rw [h1vars _ (by decide)]
  have h1da : σ₁.arrs da = arrOf N (supTab D 0) := by rw [hσ₁]; simpa using hda
  have h1pa : σ₁.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) := by
    rw [hσ₁]
    simpa using hpa
  have h1ha : σ₁.arrs ha = arrOf L F0 := by rw [hσ₁]; simpa using hha
  -- 2. the reached test
  have hreachEv : (Cond.lt (.get da (.var "sp.v"))
      (.add (.var "sp.r") (.lit 1))).evalB B σ₁
      = some (decide (D vf < d + 1)) := by
    have hget : (Expr.get da (.var "sp.v")).evalB B σ₁ = some (D vf) := by
      refine evalB_get (evalB_var (by rw [h1v]; omega)) ?_ (hDB vf)
      rw [h1da, h1v, getElem?_arrOf _ hvN, supTab_of_lt D 0 hvN]
    have hr1 : (Expr.add (.var "sp.r") (.lit 1)).evalB B σ₁ = some (d + 1) := by
      have hev_r : (Expr.var "sp.r").evalB B σ₁ = some d := by
        have h := h1vars "sp.r" (by decide)
        rw [← hr, ← h]
        exact evalB_var (by rw [h, hr]; omega)
      have := evalB_bin (B := B) (op := .add) (σ := σ₁) hev_r
        (evalB_lit (n := 1) (by omega)) (by simp only [Bop.apply_add]; omega)
      simpa using this
    exact evalB_condLt hget hr1
  by_cases hreach : D vf ≤ d
  · -- the reached branch: materialize the walk
    have hreachT : (Cond.lt (.get da (.var "sp.v"))
        (.add (.var "sp.r") (.lit 1))).evalB B σ₁ = some true := by
      rw [hreachEv]
      congr 1
      simpa using show D vf < d + 1 by omega
    -- x := v ; k := 0 ; ha[i+1] := x
    have hrx : Run B (.assign "sp.x" (.var "sp.v")) σ₁ (σ₁.setVar "sp.x" c) 2 := by
      have hev : (Expr.var "sp.v").evalB B σ₁ = some c := by
        rw [← h1v]
        exact evalB_var (by rw [h1v]; omega)
      exact (Run.assign hev).mono (by simp)
    set σ₂ := σ₁.setVar "sp.x" c with hσ₂
    have hrk : Run B (.assign "sp.k" (.lit 0)) σ₂ (σ₂.setVar "sp.k" 0) 2 :=
      (Run.assign (evalB_lit (by omega))).mono (by simp)
    set σ₃ := σ₂.setVar "sp.k" 0 with hσ₃
    have h3i : σ₃.vars "sp.i" = b0 := by rw [hσ₃, hσ₂]; simpa using h1i
    have h3x : σ₃.vars "sp.x" = c := by rw [hσ₃, hσ₂]; simp
    have h3ha : σ₃.arrs ha = arrOf L F0 := by rw [hσ₃, hσ₂]; simpa using h1ha
    have hrst : Run B (.store ha (.add (.var "sp.i") (.lit 1)) (.var "sp.x"))
        σ₃ (σ₃.setArr ha (b0 + 1) c) 5 := by
      have hidx : (Expr.add (.var "sp.i") (.lit 1)).evalB B σ₃ = some (b0 + 1) := by
        have h := evalB_incr (B := B) (x := "sp.i") (σ := σ₃)
          (by rw [h3i]; have := hb0o 1 (by omega); omega)
        rwa [h3i] at h
      have hval : (Expr.var "sp.x").evalB B σ₃ = some c := by
        rw [← h3x]
        exact evalB_var (by rw [h3x]; omega)
      refine (Run.store hidx hval ?_).mono (by simp)
      rw [h3ha, length_arrOf]
      have := hb0o 1 (by omega)
      omega
    set σ₄ := σ₃.setArr ha (b0 + 1) c with hσ₄
    set F₄ : ℕ → ℕ := fun q => if q = b0 + 1 then c else F0 q with hF₄_def
    have h4ha : σ₄.arrs ha = arrOf L F₄ := by
      rw [hσ₄, arrs_setArr, if_pos rfl, h3ha, set_arrOf, hF₄_def]
    -- the walk loop
    obtain ⟨tl0, htl0⟩ := descend_cons (G := G) D vf
    set Iw : Env → Prop := fun τ =>
      τ.vars "sp.i" = b0 ∧
      τ.arrs da = arrOf N (supTab D 0) ∧
      τ.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) ∧
      ∃ (x : Fin N) (k : ℕ) (F : ℕ → ℕ),
        τ.vars "sp.x" = (x : ℕ) ∧ τ.vars "sp.k" = k ∧
        τ.arrs ha = arrOf L F ∧
        D x ≤ d ∧ D x + k ≤ D vf ∧
        (∃ pre : List (Fin N),
          descend G D vf = pre ++ descend G D x ∧ pre.length = k) ∧
        (∀ t : ℕ, t ≤ k → ∃ hlt : t < (descend G D vf).length,
          F (b0 + 1 + t) = ((descend G D vf)[t] : ℕ)) ∧
        (∀ q, q < b0 ∨ b0 + hb < q → F q = F0 q) with hIw_def
    have h4da : σ₄.arrs da = arrOf N (supTab D 0) := by
      rw [hσ₄, arrs_setArr, if_neg (Ne.symm hha_da), hσ₃, hσ₂]
      simpa using h1da
    have h4pa : σ₄.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) := by
      rw [hσ₄, arrs_setArr, if_neg (Ne.symm hha_pa), hσ₃, hσ₂]
      simpa using h1pa
    have hIw4 : Iw σ₄ := by
      refine ⟨by rw [hσ₄]; simpa using h3i, h4da, h4pa,
        vf, 0, F₄,
        by rw [hσ₄, hvf_def]; simpa using h3x,
        by rw [hσ₄, hσ₃]; simp,
        h4ha, hreach, by omega,
        ⟨[], by simp, rfl⟩, ?_, ?_⟩
      · intro t ht
        have ht0 : t = 0 := by omega
        subst ht0
        refine ⟨by rw [htl0]; simp, ?_⟩
        show (if b0 + 1 + 0 = b0 + 1 then c else F0 (b0 + 1 + 0)) = _
        rw [if_pos (by omega), List.getElem_of_eq htl0]
        simp [hvf_def]
      · intro q hq
        show (if q = b0 + 1 then c else F0 q) = F0 q
        rw [if_neg (by omega)]
    have hloop := Run.while_count (B := B)
      (b := .lt (.lit 0) (.get da (.var "sp.x")))
      (c := .seq (.assign "sp.x" (.get pa (.var "sp.x")))
        (.seq (.assign "sp.k" (.add (.var "sp.k") (.lit 1)))
          (.store ha (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k"))
            (.var "sp.x"))))
      Iw (fun τ => supTab D 0 (τ.vars "sp.x")) 14
      (fun τ hI => by
        obtain ⟨-, hda', -, x, k, F, hx, -, -, hxd, -, -, -, -⟩ := hI
        refine ⟨_, evalB_condLt (evalB_lit (show 0 < B by omega))
          (evalB_get (evalB_var (by rw [hx]; have := x.2; omega)) ?_ (hDB x))⟩
        rw [hda', hx, getElem?_arrOf _ x.2, supTab_coe])
      (fun τ hI hcondT => by
        obtain ⟨hi', hda', hpa', x, k, F, hx, hk, hFa, hxd, hxk, ⟨pre, hsplit,
          hplen⟩, hcells, hout⟩ := hI
        -- the guard: `0 < D x`
        have hpos : 0 < D x := by
          have hev : (Cond.lt (.lit 0) (.get da (.var "sp.x"))).evalB B τ
              = some (decide (0 < D x)) := by
            refine evalB_condLt (evalB_lit (by omega))
              (evalB_get (evalB_var (by rw [hx]; have := x.2; omega)) ?_ (hDB x))
            rw [hda', hx, getElem?_arrOf _ x.2, supTab_coe]
          rw [hev] at hcondT
          simpa using hcondT
        obtain ⟨u, hu_eq, hu_lt, hu_step⟩ := leastParent_step hD hxd hpos
        -- x := pa[x]
        have hrx' : Run B (.assign "sp.x" (.get pa (.var "sp.x"))) τ
            (τ.setVar "sp.x" (u : ℕ)) 3 := by
          have hev : (Expr.get pa (.var "sp.x")).evalB B τ = some (u : ℕ) := by
            refine evalB_get (evalB_var (by rw [hx]; have := x.2; omega)) ?_
              (by have := u.2; omega)
            rw [hpa', hx, getElem?_arrOf _ x.2, supTab_coe, hu_eq]
          exact (Run.assign hev).mono (by simp)
        set τ₁ := τ.setVar "sp.x" (u : ℕ) with hτ₁
        have hkB : k + 1 < B := by
          have : k + 1 ≤ D vf := by omega
          have := hreach
          omega
        have hrk' : Run B (.assign "sp.k" (.add (.var "sp.k") (.lit 1))) τ₁
            (τ₁.setVar "sp.k" (k + 1)) 4 := by
          have h1k : τ₁.vars "sp.k" = k := by rw [hτ₁]; simpa using hk
          have hev := evalB_incr (B := B) (x := "sp.k") (σ := τ₁)
            (by rw [h1k]; omega)
          rw [h1k] at hev
          exact (Run.assign hev).mono (by simp)
        set τ₂ := τ₁.setVar "sp.k" (k + 1) with hτ₂
        have hoff_le : k + 2 ≤ hb := by
          have : k + 1 ≤ D vf := by omega
          omega
        have hrst' : Run B (.store ha
            (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k")) (.var "sp.x")) τ₂
            (τ₂.setArr ha (b0 + 1 + (k + 1)) (u : ℕ)) 7 := by
          have h2i : τ₂.vars "sp.i" = b0 := by rw [hτ₂, hτ₁]; simpa using hi'
          have h2k : τ₂.vars "sp.k" = k + 1 := by rw [hτ₂]; simp
          have h2x : τ₂.vars "sp.x" = (u : ℕ) := by rw [hτ₂, hτ₁]; simp
          have hidx1 : (Expr.add (.var "sp.i") (.lit 1)).evalB B τ₂
              = some (b0 + 1) := by
            have h := evalB_incr (B := B) (x := "sp.i") (σ := τ₂)
              (by rw [h2i]; have := hb0o 1 (by omega); omega)
            rwa [h2i] at h
          have hidx : (Expr.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k")).evalB
              B τ₂ = some (b0 + 1 + (k + 1)) := by
            have hkev : (Expr.var "sp.k").evalB B τ₂ = some (k + 1) := by
              rw [← h2k]
              exact evalB_var (by rw [h2k]; omega)
            have := evalB_bin (B := B) (op := .add) (σ := τ₂) hidx1 hkev
              (by simp; have := hb0o (1 + (k + 1)) (by omega); omega)
            simpa using this
          have hval : (Expr.var "sp.x").evalB B τ₂ = some (u : ℕ) := by
            rw [← h2x]
            exact evalB_var (by rw [h2x]; have := u.2; omega)
          refine (Run.store hidx hval ?_).mono (by simp)
          rw [hτ₂, hτ₁]
          simp only [arrs_setVar]
          rw [hFa, length_arrOf]
          have := hb0o (1 + (k + 1)) (by omega)
          omega
        set τ₃ := τ₂.setArr ha (b0 + 1 + (k + 1)) (u : ℕ) with hτ₃
        set F' : ℕ → ℕ := fun q => if q = b0 + 1 + (k + 1) then (u : ℕ) else F q
          with hF'_def
        have hrun : Run B _ τ τ₃ 14 := (hrx'.seq (hrk'.seq hrst')).mono (by omega)
        -- the split, one hop later
        have hsplit' : descend G D vf = (pre ++ [x]) ++ descend G D u := by
          rw [hsplit, hu_step]
          simp
        have hplen' : (pre ++ [x]).length = k + 1 := by simp [hplen]
        obtain ⟨tlu, htlu⟩ := descend_cons (G := G) D u
        have hlen_u : k + 1 < (descend G D vf).length := by
          rw [hsplit', htlu]
          simp only [List.length_append, List.length_cons]
          omega
        have h3da : τ₃.arrs da = arrOf N (supTab D 0) := by
          rw [hτ₃, arrs_setArr, if_neg (Ne.symm hha_da), hτ₂, hτ₁]
          simpa using hda'
        have h3pa : τ₃.arrs pa
            = arrOf N (supTab (fun v => leastParent G D v) N) := by
          rw [hτ₃, arrs_setArr, if_neg (Ne.symm hha_pa), hτ₂, hτ₁]
          simpa using hpa'
        refine ⟨τ₃, hrun, ⟨by rw [hτ₃, hτ₂, hτ₁]; simpa using hi',
          h3da, h3pa,
          u, k + 1, F',
          by rw [hτ₃, hτ₂, hτ₁]; simp,
          by rw [hτ₃, hτ₂]; simp,
          ?_, by omega, by omega,
          ⟨pre ++ [x], hsplit', hplen'⟩, ?_, ?_⟩, ?_⟩
        · rw [hτ₃, arrs_setArr, if_pos rfl, hτ₂, hτ₁]
          simp only [arrs_setVar]
          rw [hFa, set_arrOf, hF'_def]
        · intro t ht
          rcases Nat.lt_or_ge t (k + 1) with htk | htk
          · obtain ⟨hlt, hcell⟩ := hcells t (by omega)
            refine ⟨hlt, ?_⟩
            show (if b0 + 1 + t = b0 + 1 + (k + 1) then (u : ℕ)
              else F (b0 + 1 + t)) = _
            rw [if_neg (by omega)]
            exact hcell
          · have hteq : t = k + 1 := by omega
            subst hteq
            refine ⟨hlen_u, ?_⟩
            show (if b0 + 1 + (k + 1) = b0 + 1 + (k + 1) then (u : ℕ)
              else F (b0 + 1 + (k + 1))) = _
            rw [if_pos rfl]
            have hgoal : (descend G D vf)[k + 1]'hlen_u = u := by
              have hidx : (pre ++ [x]).length ≤ k + 1 := by omega
              rw [List.getElem_of_eq hsplit' hlen_u,
                List.getElem_append_right hidx]
              simp [hplen', htlu]
            rw [hgoal]
        · intro q hq
          show (if q = b0 + 1 + (k + 1) then (u : ℕ) else F q) = F0 q
          rw [if_neg (by omega)]
          exact hout q hq
        · -- the variant drops
          have h3x : τ₃.vars "sp.x" = (u : ℕ) := by rw [hτ₃, hτ₂, hτ₁]; simp
          show supTab D 0 (τ₃.vars "sp.x") < supTab D 0 (τ.vars "sp.x")
          rw [h3x, hx, supTab_coe, supTab_coe]
          exact hu_lt)
      hIw4
    obtain ⟨τf, hrw, hIwf, hcondF⟩ := hloop
    obtain ⟨hfi, hfda, hfpa, xf, kf, Ff, hfx, hfk, hfha, hfxd, hfxk,
      ⟨pref, hfsplit, hfplen⟩, hfcells, hfout⟩ := hIwf
    -- the loop's exit: at the source
    have hxf0 : D xf = 0 := by
      have hev : (Cond.lt (.lit 0) (.get da (.var "sp.x"))).evalB B τf
          = some (decide (0 < D xf)) := by
        refine evalB_condLt (evalB_lit (by omega))
          (evalB_get (evalB_var (by rw [hfx]; have := xf.2; omega)) ?_ (hDB xf))
        rw [hfda, hfx, getElem?_arrOf _ xf.2, supTab_coe]
      rw [hev] at hcondF
      simp at hcondF
      omega
    have hfin_list : descend G D vf = pref ++ [xf] := by
      rw [hfsplit, descend_eq_singleton_of_zero hxf0]
    have hfin_len : (descend G D vf).length = kf + 1 := by
      rw [hfin_list]
      simp [hfplen]
    -- the length cell
    have hkfB : kf + 1 < B := by
      have : kf ≤ D vf := by omega
      omega
    have hrfin : Run B (.store ha (.var "sp.i") (.add (.var "sp.k") (.lit 1)))
        τf (τf.setArr ha b0 (kf + 1)) 5 := by
      have hiev : (Expr.var "sp.i").evalB B τf = some b0 := by
        rw [← hfi]
        exact evalB_var (by rw [hfi]; omega)
      have hkev : (Expr.add (.var "sp.k") (.lit 1)).evalB B τf
          = some (kf + 1) := by
        have h := evalB_incr (B := B) (x := "sp.k") (σ := τf)
          (by rw [hfk]; omega)
        rwa [hfk] at h
      refine (Run.store hiev hkev ?_).mono (by simp)
      rw [hfha, length_arrOf]
      omega
    set τg := τf.setArr ha b0 (kf + 1) with hτg
    set Fg : ℕ → ℕ := fun q => if q = b0 then kf + 1 else Ff q with hFg_def
    have hgha : τg.arrs ha = arrOf L Fg := by
      rw [hτg, arrs_setArr, if_pos rfl, hfha, set_arrOf, hFg_def]
    -- the walk loop's cost: `19` per hop off the entry distance
    have hV4 : supTab D 0 (σ₄.vars "sp.x") = D vf := by
      have : σ₄.vars "sp.x" = c := by rw [hσ₄]; simpa using h3x
      rw [this, hvf_def, supTab_of_lt D 0 hvN]
    have hwcost : Run B (.while (.lt (.lit 0) (.get da (.var "sp.x")))
        (.seq (.assign "sp.x" (.get pa (.var "sp.x")))
          (.seq (.assign "sp.k" (.add (.var "sp.k") (.lit 1)))
            (.store ha (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k"))
              (.var "sp.x"))))) σ₄ τf (19 * d + 5) := by
      refine hrw.mono ?_
      have hle : supTab D 0 (σ₄.vars "sp.x") ≤ d := by rw [hV4]; exact hreach
      simp only [size_condLt, size_lit, size_get, size_var]
      omega
    -- assemble the branch
    have hbranch : Run B (.seq (.assign "sp.x" (.var "sp.v"))
        (.seq (.assign "sp.k" (.lit 0))
          (.seq (.store ha (.add (.var "sp.i") (.lit 1)) (.var "sp.x"))
            (.seq (.while (.lt (.lit 0) (.get da (.var "sp.x")))
                (.seq (.assign "sp.x" (.get pa (.var "sp.x")))
                  (.seq (.assign "sp.k" (.add (.var "sp.k") (.lit 1)))
                    (.store ha
                      (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k"))
                      (.var "sp.x")))))
              (.store ha (.var "sp.i") (.add (.var "sp.k") (.lit 1))))))) σ₁ τg
        (19 * d + 19) := by
      have h := hrx.seq (hrk.seq (hrst.seq (hwcost.seq hrfin)))
      exact h.mono (by omega)
    have hite : Run B (.ite (.lt (.get da (.var "sp.v"))
        (.add (.var "sp.r") (.lit 1)))
        (.seq (.assign "sp.x" (.var "sp.v"))
          (.seq (.assign "sp.k" (.lit 0))
            (.seq (.store ha (.add (.var "sp.i") (.lit 1)) (.var "sp.x"))
              (.seq (.while (.lt (.lit 0) (.get da (.var "sp.x")))
                  (.seq (.assign "sp.x" (.get pa (.var "sp.x")))
                    (.seq (.assign "sp.k" (.add (.var "sp.k") (.lit 1)))
                      (.store ha
                        (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k"))
                        (.var "sp.x")))))
                (.store ha (.var "sp.i") (.add (.var "sp.k") (.lit 1)))))))
        (.store ha (.var "sp.i") (.lit 0))) σ₁ τg (19 * d + 26) :=
      (Run.ite_true hreachT hbranch).mono
        (by simp only [size_condLt, size_get, size_var, size_add, size_lit]; omega)
    -- v++
    have hgv : τg.vars "sp.v" = c := by
      rw [hτg]
      simp only [vars_setArr]
      have := hrw.frame_var "sp.v" (by simp [Com.wvars])
      rw [this, hσ₄, hσ₃, hσ₂]
      simpa using h1v
    have hrv : Run B (.assign "sp.v" (.add (.var "sp.v") (.lit 1)))
        τg (τg.setVar "sp.v" (c + 1)) 4 := by
      have hev := evalB_incr (B := B) (x := "sp.v") (σ := τg)
        (by rw [hgv]; omega)
      rw [hgv] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := τg.setVar "sp.v" (c + 1) with hσ'
    have hbody : Run B (histWalkBody da pa ha) σ σ' (histKb d) := by
      have h := hri.seq (hite.seq hrv)
      refine h.mono ?_
      simp only [histKb]
      omega
    -- the invariant, one vertex later
    have hgvars : ∀ y, y ∉ ["sp.i", "sp.x", "sp.k", "sp.v"] →
        σ'.vars y = σ.vars y := by
      intro y hy
      have hy1 : y ≠ "sp.i" := by rintro rfl; exact hy (by decide)
      have hy2 : y ≠ "sp.x" := by rintro rfl; exact hy (by decide)
      have hy3 : y ≠ "sp.k" := by rintro rfl; exact hy (by decide)
      have hy4 : y ≠ "sp.v" := by rintro rfl; exact hy (by decide)
      rw [hσ']
      simp only [vars_setVar, if_neg hy4]
      rw [hτg]
      simp only [vars_setArr]
      have := hrw.frame_var y (by
        show y ∉ Com.wvars _
        simp [Com.wvars, hy2, hy3])
      rw [this, hσ₄, hσ₃, hσ₂, hσ₁]
      simp [hy1, hy2, hy3]
    have hvfc : (vf : ℕ) = c := by rw [hvf_def]
    have hgda : σ'.arrs da = arrOf N (supTab D 0) := by
      rw [hσ']
      simp only [arrs_setVar]
      rw [hτg, arrs_setArr, if_neg (Ne.symm hha_da)]
      exact hfda
    have hgpa : σ'.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) := by
      rw [hσ']
      simp only [arrs_setVar]
      rw [hτg, arrs_setArr, if_neg (Ne.symm hha_pa)]
      exact hfpa
    have hgout : ∀ q, q < b0 ∨ b0 + hb < q → Fg q = F0 q := by
      intro q hq
      show (if q = b0 then kf + 1 else Ff q) = F0 q
      rw [if_neg (by omega)]
      exact hfout q hq
    -- the new slot
    have hslot_new : SlotEnc ℓp hb Fg vf e (descendCol G D d vf) := by
      rw [descendCol_of_reached hreach]
      refine ⟨by rw [hfin_len]; omega, ?_, ?_⟩
      · show (if ((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1) = b0 then kf + 1
          else Ff (((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1))) = _
        rw [if_pos (by rw [hvfc, ← hb0_def]), hfin_len]
      · intro i hi
        rw [hfin_len] at hi
        obtain ⟨hlt, hcell⟩ := hfcells i (by omega)
        show (if ((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1) + 1 + i = b0 then kf + 1
          else Ff (((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1) + 1 + i)) = _
        rw [if_neg (by rw [hvfc, ← hb0_def]; omega)]
        have haddr : ((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1) + 1 + i
            = b0 + 1 + i := by
          rw [hvfc, ← hb0_def]
        rw [haddr]
        exact hcell
    refine ⟨σ', hbody, ⟨?_, ?_, ?_, ?_, ?_, ?_, hgda, hgpa, Fg, ?_, ?_, ?_⟩, ?_⟩
    · rw [hgvars _ (by decide)]; exact hn
    · rw [hgvars _ (by decide)]; exact hr
    · rw [hgvars _ (by decide)]; exact hl
    · rw [hgvars _ (by decide)]; exact hh
    · rw [hgvars _ (by decide)]; exact hp
    · rw [hσ']; simp; omega
    · rw [hσ']
      simp only [arrs_setVar]
      exact hgha
    · -- the finished slots, cursor advanced
      intro v' hv'
      rw [hσ'] at hv'
      simp at hv'
      rcases Nat.lt_or_ge (v' : ℕ) c with hlt | hge
      · -- an earlier slot: untouched
        refine (hnew v' hlt).of_agree ?_
        intro o ho
        refine hgout _ ?_
        have hne : (v' : ℕ) * ℓp + (e : ℕ) ≠ c * ℓp + (e : ℕ) := by
          intro hcon
          have := (slotIdx_inj hep hep hcon).1
          omega
        have := slotAddr_outside (s := c * ℓp + (e : ℕ))
          (s' := (v' : ℕ) * ℓp + (e : ℕ)) (o := o) hne ho
        rw [← hb0_def] at this
        omega
      · -- this vertex's slot
        have : v' = vf := Fin.ext (by omega)
        rw [this]
        exact hslot_new
    · -- the other columns: untouched
      intro v' p' hp'
      refine (hold v' p' hp').of_agree ?_
      intro o ho
      refine hgout _ ?_
      have hne : (v' : ℕ) * ℓp + (p' : ℕ) ≠ c * ℓp + (e : ℕ) := by
        intro hcon
        exact hp' (Fin.ext (by
          have := (slotIdx_inj p'.2 hep hcon).2
          exact this))
      have := slotAddr_outside (s := c * ℓp + (e : ℕ))
        (s' := (v' : ℕ) * ℓp + (p' : ℕ)) (o := o) hne ho
      rw [← hb0_def] at this
      omega
    · rw [hσ']; simp [hc_def]
  · -- the unreached branch: the empty list's cell
    have hreachF : (Cond.lt (.get da (.var "sp.v"))
        (.add (.var "sp.r") (.lit 1))).evalB B σ₁ = some false := by
      rw [hreachEv]
      congr 1
      simpa using show ¬ D vf < d + 1 by omega
    have hrst : Run B (.store ha (.var "sp.i") (.lit 0)) σ₁
        (σ₁.setArr ha b0 0) 3 := by
      have hiev : (Expr.var "sp.i").evalB B σ₁ = some b0 := by
        rw [← h1i]
        exact evalB_var (by rw [h1i]; omega)
      refine (Run.store hiev (evalB_lit (by omega)) ?_).mono (by simp)
      rw [h1ha, length_arrOf]
      omega
    set σ₄ := σ₁.setArr ha b0 0 with hσ₄
    set F₄ : ℕ → ℕ := fun q => if q = b0 then 0 else F0 q with hF₄_def
    have hvfc : (vf : ℕ) = c := by rw [hvf_def]
    have h4ha : σ₄.arrs ha = arrOf L F₄ := by
      rw [hσ₄, arrs_setArr, if_pos rfl, h1ha, set_arrOf, hF₄_def]
    have hite : Run B (.ite (.lt (.get da (.var "sp.v"))
        (.add (.var "sp.r") (.lit 1)))
        (.seq (.assign "sp.x" (.var "sp.v"))
          (.seq (.assign "sp.k" (.lit 0))
            (.seq (.store ha (.add (.var "sp.i") (.lit 1)) (.var "sp.x"))
              (.seq (.while (.lt (.lit 0) (.get da (.var "sp.x")))
                  (.seq (.assign "sp.x" (.get pa (.var "sp.x")))
                    (.seq (.assign "sp.k" (.add (.var "sp.k") (.lit 1)))
                      (.store ha
                        (.add (.add (.var "sp.i") (.lit 1)) (.var "sp.k"))
                        (.var "sp.x")))))
                (.store ha (.var "sp.i") (.add (.var "sp.k") (.lit 1)))))))
        (.store ha (.var "sp.i") (.lit 0))) σ₁ σ₄ (19 * d + 26) :=
      (Run.ite_false hreachF hrst).mono
        (by simp only [size_condLt, size_get, size_var, size_add, size_lit]; omega)
    have h4v : σ₄.vars "sp.v" = c := by rw [hσ₄]; simpa using h1v
    have hrv : Run B (.assign "sp.v" (.add (.var "sp.v") (.lit 1)))
        σ₄ (σ₄.setVar "sp.v" (c + 1)) 4 := by
      have hev := evalB_incr (B := B) (x := "sp.v") (σ := σ₄)
        (by rw [h4v]; omega)
      rw [h4v] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σ₄.setVar "sp.v" (c + 1) with hσ'
    have hbody : Run B (histWalkBody da pa ha) σ σ' (histKb d) := by
      have h := hri.seq (hite.seq hrv)
      refine h.mono ?_
      simp only [histKb]
      omega
    have hgvars : ∀ y, y ≠ "sp.i" → y ≠ "sp.v" → σ'.vars y = σ.vars y := by
      intro y hy1 hy2
      rw [hσ', hσ₄, hσ₁]
      simp [hy1, hy2]
    have hgout : ∀ q, q < b0 ∨ b0 + hb < q → F₄ q = F0 q := by
      intro q hq
      show (if q = b0 then 0 else F0 q) = F0 q
      rw [if_neg (by omega)]
    have hslot_new : SlotEnc ℓp hb F₄ vf e (descendCol G D d vf) := by
      rw [descendCol_of_far hreach]
      refine ⟨by simp, ?_, ?_⟩
      · show (if ((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1) = b0 then 0
          else F0 (((vf : ℕ) * ℓp + (e : ℕ)) * (hb + 1))) = _
        rw [if_pos (by rw [hvfc, ← hb0_def])]
        simp
      · intro i hi
        simp at hi
    refine ⟨σ', hbody, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F₄, ?_, ?_, ?_⟩, ?_⟩
    · rw [hgvars _ (by decide) (by decide)]; exact hn
    · rw [hgvars _ (by decide) (by decide)]; exact hr
    · rw [hgvars _ (by decide) (by decide)]; exact hl
    · rw [hgvars _ (by decide) (by decide)]; exact hh
    · rw [hgvars _ (by decide) (by decide)]; exact hp
    · rw [hσ']; simp; omega
    · rw [hσ']
      simp only [arrs_setVar]
      rw [hσ₄, arrs_setArr, if_neg (Ne.symm hha_da)]
      exact h1da
    · rw [hσ']
      simp only [arrs_setVar]
      rw [hσ₄, arrs_setArr, if_neg (Ne.symm hha_pa)]
      exact h1pa
    · rw [hσ']
      simp only [arrs_setVar]
      exact h4ha
    · intro v' hv'
      rw [hσ'] at hv'
      simp at hv'
      rcases Nat.lt_or_ge (v' : ℕ) c with hlt | hge
      · refine (hnew v' hlt).of_agree ?_
        intro o ho
        refine hgout _ ?_
        have hne : (v' : ℕ) * ℓp + (e : ℕ) ≠ c * ℓp + (e : ℕ) := by
          intro hcon
          have := (slotIdx_inj hep hep hcon).1
          omega
        have := slotAddr_outside (s := c * ℓp + (e : ℕ))
          (s' := (v' : ℕ) * ℓp + (e : ℕ)) (o := o) hne ho
        rw [← hb0_def] at this
        omega
      · have : v' = vf := Fin.ext (by omega)
        rw [this]
        exact hslot_new
    · intro v' p' hp'
      refine (hold v' p' hp').of_agree ?_
      intro o ho
      refine hgout _ ?_
      have hne : (v' : ℕ) * ℓp + (p' : ℕ) ≠ c * ℓp + (e : ℕ) := by
        intro hcon
        exact hp' (Fin.ext (slotIdx_inj p'.2 hep hcon).2)
      have := slotAddr_outside (s := c * ℓp + (e : ℕ))
        (s' := (v' : ℕ) * ℓp + (p' : ℕ)) (o := o) hne ho
      rw [← hb0_def] at this
      omega
    · rw [hσ']; simp [hc_def]

include hD hNB hdB hlB hhB hLB hDB hdhb hha_da hha_pa in
/-- **The walk pass, discharged**: from the input cells, the distance
and parent tables, and the inherited channel, `histCom` finishes
column `e` — `descendCol` at every vertex — and leaves every other
column exactly as it was. Cost `histK N d`. -/
theorem histCom_spec :
    Spec B
      (fun σ => σ.vars "sp.n" = N ∧ σ.vars "sp.r" = d ∧ σ.vars "sp.l" = ℓp ∧
        σ.vars "sp.h" = hb ∧ σ.vars "sp.p" = (e : ℕ) ∧
        σ.arrs da = arrOf N (supTab D 0) ∧
        σ.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) ∧
        HistArr ha ℓp hb hist σ)
      (histCom da pa ha)
      (fun _ σ' =>
        σ'.arrs da = arrOf N (supTab D 0) ∧
        σ'.arrs pa = arrOf N (supTab (fun v => leastParent G D v) N) ∧
        HistArr ha ℓp hb
          (fun v p => if p = e then descendCol G D d v else hist v p) σ')
      (histK N d) := by
  have hmain := Spec.forRangeZero (B := B) "sp.v" "sp.n"
    (HistInv da pa ha d hb e G D hist) N (histKb d) hNB
    (fun σ hσ => hσ.2.2.2.2.2.1)
    (fun σ hσ => hσ.1)
    (histBody_step hD hNB hdB hlB hhB hLB hDB hdhb hha_da hha_pa)
  refine ((hmain.pre ?_).post ?_).mono (by simp [histK])
  · rintro σ ⟨hn, hr, hl, hh, hp, hda, hpa, hH⟩
    have hlen : (σ.arrs ha).length = N * ℓp * (hb + 1) := hH.1
    set F0 : ℕ → ℕ := fun q => (σ.arrs ha).getD q 0 with hF0
    have hF0a : σ.arrs ha = arrOf (N * ℓp * (hb + 1)) F0 := by
      conv_lhs => rw [← arrOf_getD (σ.arrs ha)]
      rw [hlen]
    refine ⟨by simpa using hn, by simpa using hr, by simpa using hl,
      by simpa using hh, by simpa using hp, by simp,
      by simpa using hda, by simpa using hpa, F0, by simpa using hF0a,
      ?_, ?_⟩
    · intro v hv
      simp at hv
    · intro v p hp'
      exact slotEnc_of_histArr hH hF0a v p
  · rintro σ σ' hσ ⟨⟨-, -, -, -, -, -, hda', hpa', F, hha', hnew, hold⟩, hvN⟩
    refine ⟨hda', hpa', ?_⟩
    refine histArr_of_slotEnc hha' ?_
    intro v p
    by_cases hpe : p = e
    · rw [if_pos hpe, hpe]
      exact hnew v (by rw [hvN]; exact v.2)
    · rw [if_neg hpe]
      exact hold v p hpe

end Walks

/-! ## §8 The headline -/

section Headline

variable {B N ns d ℓp hb : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {oa ta da pa ha : String} {off tgt : ℕ → ℕ} {D : Fin N → ℕ}
  {s : Fin N} {e : Fin ℓp}

variable
  (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩)
  (hoff0 : off 0 = 0)
  (hD : BallTable G s d D)
  (hDd : ∀ v : Fin N, D v ≤ d + 1)
  (hdhb : d + 1 ≤ hb)
  (hNB : N < B) (hnsB : ns < B) (hdB : d + 2 < B)
  (hlB : ℓp < B) (hhB : hb + 1 < B) (hLB : N * ℓp * (hb + 1) < B)
  (hpa_oa : pa ≠ oa) (hpa_ta : pa ≠ ta) (hpa_da : pa ≠ da)
  (hha_oa : ha ≠ oa) (hha_ta : ha ≠ ta) (hha_da : ha ≠ da) (hha_pa : ha ≠ pa)

include hadj hoff0 hD hDd hdhb hNB hnsB hdB hlB hhB hLB hpa_oa hpa_ta hpa_da
  hha_oa hha_ta hha_da hha_pa in
/-- **The supports stage, discharged** (F6c/4): from the CSR, the six
input cells, a length-`N` parent scratch region, the distance region
holding the `BallTable` `D` (the seam: precondition verbatim
`bfsCom_spec`'s postcondition), and the channel at `hist`, the routine
leaves the distance region untouched, the least parents in the parent
region, and **the `HistArr` column of round `e` holding
`Impl.descend`'s lists at every reached vertex** (the empty list
beyond the horizon), every other column exactly as inherited. Cost
`supportsK N ns d`. Everything else is frame
(`wvars_supportsCom_subset`/`warrs_supportsCom`). -/
theorem supportsCom_spec (hist : Fin N → Fin ℓp → List (Fin N)) :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧
        σ.vars "sp.n" = N ∧ σ.vars "sp.m" = ns ∧ σ.vars "sp.r" = d ∧
        σ.vars "sp.l" = ℓp ∧ σ.vars "sp.h" = hb ∧ σ.vars "sp.p" = (e : ℕ) ∧
        (σ.arrs pa).length = N ∧
        (σ.arrs da).length = N ∧
        (∀ v : Fin N, (σ.arrs da).getD (v : ℕ) 0 = D v) ∧
        HistArr ha ℓp hb hist σ)
      (supportsCom oa ta da pa ha)
      (fun _ σ' => Csr oa ta N ns N off tgt σ' ∧
        (σ'.arrs da).length = N ∧
        (∀ v : Fin N, (σ'.arrs da).getD (v : ℕ) 0 = D v) ∧
        (σ'.arrs pa).length = N ∧
        (∀ v : Fin N, (σ'.arrs pa).getD (v : ℕ) 0 = leastParent G D v) ∧
        HistArr ha ℓp hb
          (fun v p => if p = e then descendCol G D d v else hist v p) σ')
      (supportsK N ns d) := by
  have hDB : ∀ v : Fin N, D v < B := fun v => by
    have := hDd v
    omega
  intro σ hσ
  obtain ⟨hc, hn, hm, hr, hl, hh, hp, hplen, hdlen, hdget, hH⟩ := hσ
  -- 1. the parent pass
  obtain ⟨σ₁, hr1, hpost1⟩ :=
    ((parentCom_spec hadj hoff0 hNB hnsB hDB hpa_oa hpa_ta hpa_da).frame).run
      ⟨hc, hn, hm, hplen, hdlen, hdget⟩
  obtain ⟨⟨hc1, hda1, hpa1⟩, hfv1, hfa1, -, -⟩ := hpost1
  have h1vars : ∀ y, y ∉ ["sp.i", "sp.u", "sp.j", "sp.w"] →
      σ₁.vars y = σ.vars y := by
    intro y hy
    have h1 : y ≠ "sp.i" := by rintro rfl; exact hy (by decide)
    have h2 : y ≠ "sp.u" := by rintro rfl; exact hy (by decide)
    have h3 : y ≠ "sp.j" := by rintro rfl; exact hy (by decide)
    have h4 : y ≠ "sp.w" := by rintro rfl; exact hy (by decide)
    refine hfv1 y ?_
    rw [wvars_parentCom]
    simp [h1, h2, h3, h4]
  have h1ha : σ₁.arrs ha = σ.arrs ha := by
    refine hfa1 ha ?_
    rw [warrs_parentCom]
    simp [hha_pa]
  -- 2. the walk pass
  obtain ⟨σ₂, hr2, hda2, hpa2, hH2⟩ :=
    (histCom_spec (hist := hist) hD hNB hdB hlB hhB hLB hDB hdhb hha_da
      hha_pa).run
      ⟨by rw [h1vars _ (by decide)]; exact hn,
        by rw [h1vars _ (by decide)]; exact hr,
        by rw [h1vars _ (by decide)]; exact hl,
        by rw [h1vars _ (by decide)]; exact hh,
        by rw [h1vars _ (by decide)]; exact hp,
        hda1, hpa1, histArr_congr_arrs hH h1ha⟩
  -- assemble
  have hrun : Run B (supportsCom oa ta da pa ha) σ σ₂ (supportsK N ns d) := by
    have h := hr1.seq hr2
    exact h.mono (by simp [supportsK])
  have h2oa : σ₂.arrs oa = σ₁.arrs oa := by
    refine hr2.frame_arr oa ?_
    rw [warrs_histCom]
    simp [Ne.symm hha_oa]
  have h2ta : σ₂.arrs ta = σ₁.arrs ta := by
    refine hr2.frame_arr ta ?_
    rw [warrs_histCom]
    simp [Ne.symm hha_ta]
  refine ⟨σ₂, hrun, hc1.of_eq h2oa h2ta,
    by rw [hda2, length_arrOf],
    fun v => by rw [hda2, getD_arrOf _ v.2, supTab_coe],
    by rw [hpa2, length_arrOf],
    fun v => by rw [hpa2, getD_arrOf _ v.2, supTab_coe],
    hH2⟩

end Headline

section Seam

variable {B N ns d ℓp hb : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
  {oa ta da pa ha : String} {D : Fin N → ℕ} {s : Fin N} {e : Fin ℓp}

/-- **The routine at the head file's seam**: the same discharge stated
against `GraphCsr` — the form a frame block holds its arena in
(`ArenaSt`'s `csr` and `hist` projections are exactly this
precondition's region facts). -/
theorem supportsCom_spec_graphCsr
    (hD : BallTable G s d D)
    (hDd : ∀ v : Fin N, D v ≤ d + 1)
    (hdhb : d + 1 ≤ hb)
    (hNB : N < B) (hnsB : ns < B) (hdB : d + 2 < B)
    (hlB : ℓp < B) (hhB : hb + 1 < B) (hLB : N * ℓp * (hb + 1) < B)
    (hpa_oa : pa ≠ oa) (hpa_ta : pa ≠ ta) (hpa_da : pa ≠ da)
    (hha_oa : ha ≠ oa) (hha_ta : ha ≠ ta) (hha_da : ha ≠ da) (hha_pa : ha ≠ pa)
    (hist : Fin N → Fin ℓp → List (Fin N)) :
    Spec B
      (fun σ => GraphCsr oa ta G ns σ ∧
        σ.vars "sp.n" = N ∧ σ.vars "sp.m" = ns ∧ σ.vars "sp.r" = d ∧
        σ.vars "sp.l" = ℓp ∧ σ.vars "sp.h" = hb ∧ σ.vars "sp.p" = (e : ℕ) ∧
        (σ.arrs pa).length = N ∧
        (σ.arrs da).length = N ∧
        (∀ v : Fin N, (σ.arrs da).getD (v : ℕ) 0 = D v) ∧
        HistArr ha ℓp hb hist σ)
      (supportsCom oa ta da pa ha)
      (fun _ σ' => GraphCsr oa ta G ns σ' ∧
        (σ'.arrs da).length = N ∧
        (∀ v : Fin N, (σ'.arrs da).getD (v : ℕ) 0 = D v) ∧
        (σ'.arrs pa).length = N ∧
        (∀ v : Fin N, (σ'.arrs pa).getD (v : ℕ) 0 = leastParent G D v) ∧
        HistArr ha ℓp hb
          (fun v p => if p = e then descendCol G D d v else hist v p) σ')
      (supportsK N ns d) := by
  intro σ hσ
  obtain ⟨⟨off, tgt, hc, hoff0, hnd, hadj'⟩, hcells⟩ := hσ
  obtain ⟨σ', hrun, hc', hpost⟩ :=
    (supportsCom_spec hadj' hoff0 hD hDd hdhb hNB hnsB hdB hlB hhB hLB
      hpa_oa hpa_ta hpa_da hha_oa hha_ta hha_da hha_pa hist).run ⟨hc, hcells⟩
  exact ⟨σ', hrun, ⟨off, tgt, hc', hoff0, hnd, hadj'⟩, hpost⟩

end Seam

end Lax3Proofs.Prog
