import Lax3Proofs.RamDriverAugment

/-!
The **readback of one cluster**, walked: the obligation
`Lax3Proofs.RamDriverCluster.ReadbackStep` discharged, together with the
two pieces of bit arithmetic the driver's generated code is written in.

The readback is the last pass of a cluster's turn. It walks the current
block, and at every member the cover assigned to the centre being
processed it stores, for every formula of the depth's table, the value
of that formula's own boolean combination over the depth-`(j+1)` tables
and the scatter flags. `Lax3Proofs.RamDriver.sat_iff_eval_step` says
what that value *means*; this file says that the program computes it.

# What the walk needs

One loop, whose body is a conditional whose branch is a straight line of
stores. Three ingredients, in the order the walk consumes them.

* **The names are injective.** The store's target `tabName j i` and the
  arrays the store's expression reads — `tabName (j+1) i'`, one per
  local atom — must be different arrays, and so must two tables of one
  depth, or the block would overwrite what it has just written. The
  driver's names go through `Nat.repr`, for which the library has no
  injectivity lemma, so one is proved here: `decChars` is a left inverse
  of `Nat.toDigits 10`, `'_'` is not a digit, and `tabName_inj`
  follows. Every other name disequality of the readback — a table
  against `off`, `tgt`, a mask, a colour array, the assignment — is
  decided by the first character and needs none of this.
* **The arithmetic of a boolean combination**, `evalB_bcExpr`: a
  valuation of the atoms into `{0, 1}` gives `RamDriver.bcExpr` a value
  in `{0, 1}`, nonzero exactly when `BC.eval` of the corresponding
  predicate holds. Negation is `1 - u` and conjunction is a product, so
  the induction is two lines of truncated arithmetic per constructor.
  This is the one genuinely new induction of the readback.
* **The frame of one store**: `rbBase_setArr_tab`, that writing a
  depth-`j` table disturbs neither the level's surface nor the atom
  valuation. This is where the name injectivity is spent.

The walk itself is `RamAugment.blockScan` over the current cover block
with `Spec.ite` inside it, whose true branch is `block_spec` — an
induction along `List.drop p` of the depth's table list, one
`Spec.store` per entry — and whose false branch is `Spec.skip`, correct
because the postcondition speaks only of the vertices the cover
assigned to the centre. `readback_spec` is the result, and `rbCost` is
what it costs.

# Which obligation

`RamDriverCluster.ReadbackStep` is the obligation discharged here. The
readback `Prop` `Lax3Proofs.RamDriver` used to carry was not provable:
its valuation `val : ℕ → _ → Prop` was indexed by the table position
alone, while `RamDriver.atomExpr` reads the depth-`(j+1)` table *at the
vertex the counter stands on*, so a local atom's truth value varies
over the cluster and the stated `Prop` could not express what the loop
leaves. `ReadbackStep` is that obligation repaired — the valuation is
`RamDriverCluster.atomVal … v`, which is the shape
`RamDriver.sat_iff_eval_step` produces — and it is what `readbackStep`
below discharges, at the cost `rbCost`.

Nothing of that obligation's precondition is missing any longer:
`RamDriver.TablesSized` sizes the depth-`j` table arrays,
`RamDriver.TableInv`'s own bit clause is the depth-`(j+1)` cells, the
scatter phase's postcondition is the flags, and `σ.vars "c" < n` is a
conjunct of `ReadbackStep` itself. Two hypotheses of `readbackStep` are
plain facts about its parameters rather than about a state — `1 < B`
with `n < B`, and that the depth-`(j+1)` colour arrays hold
`RamDriver.stepColoringP`, which is `RamDriverCluster.ColourStep`'s own
postcondition and is in the caller's hand at the call site.

`readback_spec` is the walk itself, stated over the data it actually
uses; `readbackStep` is nothing but the translation of that data out of
the cluster's surface.

# The base case

`RamDriver.BaseImplements` is not discharged here. Its sizing gap is
now closed — `reprCom`'s `rep` array and the depth-`ℓ` tables are
conjuncts of its own precondition — but its walk is much larger: a nested scan
for the representative system and an induction over the formula for
`RamDriver.botCom`, with the fresh-name discipline of the generated
code to carry. What this file leaves for it is the arithmetic its
generated expressions are written in — `evalB_eqBitExpr`,
`evalB_orBitExpr` and `evalB_rowEqExpr`, the last being the row test
`BotEval.rowOf_eq_iff` translates — and the name injectivity above,
which its stores need for the same reason the readback's do.
-/

namespace Lax3Proofs.RamDriverBase

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster (TurnPre CoverHeld ClusterData ScatVal atomVal ReadbackStep
  masked_alv_eq)
open Lax3Proofs.RamBfs (masked)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ### The names of the driver are injective

Every per-depth array of the driver is addressed by a name built from
the depth and a position through `Nat.repr`, and a walk that stores
into one of them has to know that it is not one of the others. Two
facts do it, and both come off the library without unfolding
`Nat.toDigitsCore`: the decimal representation is injective, because
`Nat.toNat?_repr` reads it back, and the separator is not among its
characters, because `Nat.toDigits_eq_if` is a recursion equation whose
every contribution is a digit. -/

/-- No decimal digit is the separator of the driver's names. -/
theorem digitChar_ne_underscore {d : ℕ} (h : d < 10) : Nat.digitChar d ≠ '_' := by
  interval_cases d <;> decide

/-- **The separator does not occur in a decimal representation.**
Strong induction along `Nat.toDigits_eq_if`: the last character is a
digit and the rest is the representation of a smaller number. -/
theorem underscore_not_mem_toDigits : ∀ n : ℕ, '_' ∉ Nat.toDigits 10 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      simp only [List.mem_singleton]
      exact fun hc => digitChar_ne_underscore hlt hc.symm
    · rename_i hge
      have hpos : 0 < n := by omega
      simp only [List.mem_append, not_or]
      refine ⟨ih (n / 10) (Nat.div_lt_self hpos (by omega)), ?_⟩
      simp only [List.mem_singleton]
      exact fun hc => digitChar_ne_underscore (Nat.mod_lt _ (by omega)) hc.symm

/-- The decimal representation is the string of the digits. -/
theorem repr_eq_ofList (n : ℕ) : Nat.repr n = String.ofList (Nat.toDigits 10 n) := rfl

/-- **The decimal numeral determines the number**: the round trip
through `String.toNat?`. -/
theorem toString_inj {a b : ℕ} (h : toString a = toString b) : a = b := by
  have h' : (Nat.repr a).toNat? = (Nat.repr b).toNat? := by
    simp only [← Nat.toString_eq_repr]; rw [h]
  rw [Nat.toNat?_repr, Nat.toNat?_repr] at h'
  exact Option.some.inj h'

/-- **The decimal representation is injective.** -/
theorem toDigits_injective {m n : ℕ} (h : Nat.toDigits 10 m = Nat.toDigits 10 n) : m = n := by
  refine toString_inj ?_
  rw [Nat.toString_eq_repr, Nat.toString_eq_repr, repr_eq_ofList, repr_eq_ofList, h]

/-- A list splits at the first occurrence of a character that neither
prefix contains. -/
theorem append_cons_inj {c : Char} : ∀ {a b a' b' : List Char}, c ∉ a → c ∉ a' →
    a ++ c :: b = a' ++ c :: b' → a = a' ∧ b = b' := by
  intro a
  induction a with
  | nil =>
    intro b a' b' _ ha' h
    cases a' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons y ys =>
      have hcy : c = y := (List.cons.inj h).1
      subst hcy
      exact absurd List.mem_cons_self ha'
  | cons x xs ih =>
    intro b a' b' ha ha' h
    cases a' with
    | nil =>
      have hcx : x = c := (List.cons.inj h).1
      subst hcx
      exact absurd List.mem_cons_self ha
    | cons y ys =>
      obtain ⟨rfl, h'⟩ := List.cons.inj h
      obtain ⟨rfl, rfl⟩ := ih (fun hc => ha (List.mem_cons_of_mem _ hc))
        (fun hc => ha' (List.mem_cons_of_mem _ hc)) h'
      exact ⟨rfl, rfl⟩

/-- **The table arrays are addressed injectively**: the depth and the
position are both recoverable from the name. -/
theorem tabName_inj {j i j' i' : ℕ} (h : tabName j i = tabName j' i') : j = j' ∧ i = i' := by
  simp only [tabName, String.ext_iff] at h
  simp at h
  obtain ⟨h1, h2⟩ :=
    append_cons_inj (underscore_not_mem_toDigits j) (underscore_not_mem_toDigits j') h
  exact ⟨toDigits_injective h1, toDigits_injective h2⟩

/-- Two table arrays of different depths are different arrays. -/
theorem tabName_ne_succ (j i i' : ℕ) : tabName j i ≠ tabName (j + 1) i' :=
  fun h => by have := (tabName_inj h).1; omega

/-- Two table arrays at different positions of one depth are different
arrays. -/
theorem tabName_ne_of_ne (j : ℕ) {i i' : ℕ} (h : i ≠ i') : tabName j i ≠ tabName j i' :=
  fun hc => h (tabName_inj hc).2

/-- A table name carries the separator. -/
theorem underscore_mem_tabName (j i : ℕ) : '_' ∈ (tabName j i).toList := by
  rw [tabName]
  simp only [String.toList_append, List.mem_append]
  exact Or.inl (Or.inr (by simp))

/-- **A table array is none of the fixed scratch names**, since every
one of them is a literal without a separator and every table name has
one. On a concrete literal the hypothesis is `decide`. -/
theorem tabName_ne_lit (j i : ℕ) {q : String} (h : '_' ∉ q.toList) : tabName j i ≠ q :=
  fun he => h (he ▸ underscore_mem_tabName j i)

/-- The same, the way `Env.setArr` presents it. -/
theorem lit_ne_tabName {q : String} (h : '_' ∉ q.toList) (j i : ℕ) : q ≠ tabName j i :=
  fun he => h (he ▸ underscore_mem_tabName j i)

/-! ### Two collapses of environment updates -/

/-- Setting a scalar twice keeps the second value. -/
theorem setVar_setVar_same (σ : Env) (x : String) (u v : ℕ) :
    (σ.setVar x u).setVar x v = σ.setVar x v := by
  cases σ
  simp only [Env.setVar, Env.mk.injEq, and_true]
  funext y
  by_cases h : y = x <;> simp [h]

/-- A scalar update and an array update commute. -/
theorem setArr_setVar (σ : Env) (x : String) (v : ℕ) (a : String) (i u : ℕ) :
    (σ.setArr a i u).setVar x v = (σ.setVar x v).setArr a i u := rfl

/-! ### The arithmetic of a boolean combination

The one induction the readback needs: over `RamDriver.bcExpr`, that a
valuation of the atoms into `{0, 1}` gives the whole expression a value
in `{0, 1}`, nonzero exactly when `BC.eval` of the corresponding
predicate holds. Negation is a truncated subtraction from one and
conjunction is a product, so both halves are arithmetic on two bits. -/

/-- **The value of a boolean combination is a bit, and the bit is the
combination's truth value.** -/
theorem evalB_bcExpr {α : Type*} {B : ℕ} (hB : 1 < B) {σ : Env} {va : α → Expr} {p : α → Prop} :
    ∀ b : BC α, (∀ a ∈ b.atoms, ∃ u ≤ 1, (va a).evalB B σ = some u ∧ (u ≠ 0 ↔ p a)) →
      ∃ u ≤ 1, (bcExpr va b).evalB B σ = some u ∧ (u ≠ 0 ↔ BC.eval p b) := by
  intro b
  induction b with
  | atom a =>
    intro hva
    exact hva a (by rw [BCAlgebra.atoms_atom]; exact List.mem_cons_self)
  | tru =>
    intro _
    exact ⟨1, le_rfl, evalB_lit hB, by simp [BCAlgebra.eval_tru]⟩
  | not b ih =>
    intro hva
    obtain ⟨u, hu1, hueval, huiff⟩ := ih (fun a ha => hva a (by rwa [BCAlgebra.atoms_not]))
    refine ⟨1 - u, by omega, ?_, ?_⟩
    · exact evalB_bin (evalB_lit hB) hueval (by simp; omega)
    · rw [BCAlgebra.eval_not, ← huiff]
      omega
  | and b c ihb ihc =>
    intro hva
    obtain ⟨u, hu1, hueval, huiff⟩ := ihb (fun a ha =>
      hva a (by rw [BCAlgebra.atoms_and]; exact List.mem_append_left _ ha))
    obtain ⟨w, hw1, hweval, hwiff⟩ := ihc (fun a ha =>
      hva a (by rw [BCAlgebra.atoms_and]; exact List.mem_append_right _ ha))
    refine ⟨u * w, by nlinarith, ?_, ?_⟩
    · exact evalB_bin hueval hweval (by simp; nlinarith)
    · rw [BCAlgebra.eval_and, ← huiff, ← hwiff]
      constructor
      · intro h
        exact ⟨fun hc => h (by rw [hc, Nat.zero_mul]), fun hc => h (by rw [hc, Nat.mul_zero])⟩
      · rintro ⟨h1, h2⟩
        exact Nat.mul_ne_zero h1 h2

/-! ### The readback of one cluster -/

section Readback

variable {n : ℕ}

/-- The atoms of a depth-`j` combination: a local formula of the next
depth, or one of that depth's scatter sentences. -/
abbrev StepAtom (cap mb j : ℕ) : Type :=
  DistFO (sigL cap mb (j + 1)) 1 ⊕ ScatterSentence (sigL cap mb (j + 1))

open Classical in
/-- The cell the readback writes for the tabled formula at position
`i`: the value of that formula's own boolean combination, or zero
outside the rank condition. -/
noncomputable def rbCell (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i : ℕ)
    (β : DistFO (sigL cap mb j) 1) : Expr :=
  if h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' (stepFml cap mb j β) then
    bcExpr (atomExpr q_top cap mb φ j i β) (bcOf q_top (stepFml cap mb j β) h)
  else .lit 0

/-- The readback, with the store expression named. -/
theorem readbackCom_eq (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    readbackCom q_top cap mb φ j =
      Lax3Proofs.RamAugment.blockScan (xofName j) (xmmName j) (curName j) "z" "zend" "rv"
        (.ite (.eq (.get (asgName j) (.var "rv")) (.var (curName j)))
          (foldIdx (fun i β =>
              .store (tabName j i) (.var "rv") (rbCell q_top cap mb φ j i β)) 0
            (tablesAt q_top cap mb φ j))
          .skip) := rfl

/-- **The cell is a bit, and the bit is the combination.** -/
theorem evalB_rbCell {B q_top cap mb j i : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {β : DistFO (sigL cap mb j) 1} (hB : 1 < B) {σ : Env} {vl : StepAtom cap mb j → Prop}
    (hval : ∀ h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' (stepFml cap mb j β),
      ∀ a ∈ (bcOf q_top (stepFml cap mb j β) h).atoms, ∃ u ≤ 1,
      (atomExpr q_top cap mb φ j i β a).evalB B σ = some u ∧ (u ≠ 0 ↔ vl a)) :
    ∃ u ≤ 1, (rbCell q_top cap mb φ j i β).evalB B σ = some u ∧
      (u ≠ 0 ↔ ∃ h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' (stepFml cap mb j β),
        (bcOf q_top (stepFml cap mb j β) h).eval vl) := by
  classical
  by_cases h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' (stepFml cap mb j β)
  · obtain ⟨u, hu1, hueval, huiff⟩ :=
      evalB_bcExpr hB (bcOf q_top (stepFml cap mb j β) h) (hval h)
    refine ⟨u, hu1, ?_, ?_⟩
    · rw [rbCell, dif_pos h]; exact hueval
    · rw [huiff]; exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩
  · refine ⟨0, by omega, ?_, ?_⟩
    · rw [rbCell, dif_neg h]; exact evalB_lit (by omega)
    · simp only [ne_eq, not_true_eq_false, false_iff]
      rintro ⟨h', -⟩
      exact h h'

/-- What one table array of the depth holds at the slots of the current
block the readback has already passed. -/
noncomputable def TabOk (q_top cap mb j : ℕ) {n : ℕ}
    (Xoff Xmem asg : ℕ → ℕ) (cc : ℕ)
    (vl : Fin n → StepAtom cap mb j → Prop) (β : DistFO (sigL cap mb j) 1)
    (nm : String) (T₀ : ℕ → ℕ) (σ : Env) (bnd : ℕ) : Prop :=
  ∃ Tb : ℕ → ℕ, σ.arrs nm = arrOf n Tb ∧
    (∀ v : Fin n, asg (v : ℕ) ≠ cc → Tb (v : ℕ) = T₀ (v : ℕ)) ∧
    ∀ p, Xoff cc ≤ p → p < bnd → ∃ hp : Xmem p < n,
      asg (Xmem p) = cc →
        Tb (Xmem p) ≤ 1 ∧
        (Tb (Xmem p) ≠ 0 ↔
          ∃ h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧ DRank 1 q' (stepFml cap mb j β),
            (bcOf q_top (stepFml cap mb j β) h).eval (vl ⟨Xmem p, hp⟩))

/-- Everything the readback reads and never writes: the level's own
surface, the cover's block and assignment, the centre being processed,
the output tape, and the values of the atoms of every tabled formula at
every vertex **the turn was assigned**.

**Wave R1.8-T3-flip (c2b): at the visited vertices only.** The loop
evaluates an atom expression under the guard `asg[rv] = cc` and nowhere
else, so asking for the valuation off the guard asks for something the
walk never uses — and something the caller can no longer supply, since a
local atom reads the depth-`(j+1)` table row and a vertex outside
`alive ∪ kills` has no row. The clause below is the walk's real
precondition; `RamDriverCluster.ReadbackStep`'s own visited-vertex
clause is what turns it back into a statement about the cluster. -/
def RbBase (B q_top cap mb ns Ws j : ℕ) {n : ℕ} (φ : Lax3.FirstOrder.FO 0) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (Xoff Xmem asg : ℕ → ℕ) (cc : ℕ) (ou : List ℕ)
    (val : Fin n → ℕ → StepAtom cap mb j → Prop) (σ : Env) : Prop :=
  LevelPre B n cap mb ns Ws O T j M Gm C σ ∧
    σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
    σ.arrs (xmmName j) = arrOf (n * n) Xmem ∧
    σ.arrs (asgName j) = arrOf n asg ∧
    σ.vars (curName j) = cc ∧ cc < B ∧ σ.out = ou ∧
    ∀ (v : Fin n), asg (v : ℕ) = cc → ∀ (i : ℕ)
        (hi : i < (tablesAt q_top cap mb φ j).length)
        (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
          DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])),
        ∀ a ∈ (bcOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[i]) h).atoms,
          ∃ u ≤ 1,
      (atomExpr q_top cap mb φ j i (tablesAt q_top cap mb φ j)[i] a).evalB B
          (σ.setVar "rv" (v : ℕ)) = some u ∧ (u ≠ 0 ↔ val v i a)

/-! #### The frame of one store

The readback writes the depth-`j` tables and nothing else, and the
names of those arrays are different from every name it reads: from the
block structure and the two masks, from the colour arrays, from the
assignment, and — by `tabName_inj` — from the depth-`(j+1)` tables the
atoms are read out of. -/

/-- **A `Sized` clause survives any store**, and for the reason
`RamDriver.Sized.run` survives any run: a store never changes the length
of an array, so it does not matter whether the array it writes is one the
clause speaks about. -/
theorem sized_setArr {l : List (String × ℕ)} {σ : Env} {a : String} {idx v : ℕ}
    (h : Sized l σ) : Sized l (σ.setArr a idx v) :=
  fun _ hp => exists_arrOf ((length_arrs_setArr ..).trans (h.length hp))

/-- The engines' scratch is untouched by a table write, for the same
reason and at every one of its twenty-five arrays. -/
theorem orderMem_setArr_tab {B n ns Ws : ℕ} {σ : Env} (h : OrderMem B n ns Ws σ)
    (j i idx v : ℕ) : OrderMem B n ns Ws (σ.setArr (tabName j i) idx v) := by
  obtain ⟨hle, hlw, hsz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨hle, by simpa using hlw, sized_setArr hsz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "elm") (by decide) j i)]; exact h1)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "bh") (by decide) j i)]; exact h2)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "ooff") (by decide) j i)]; exact h3)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "noff") (by decide) j i)]; exact h4)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "stf") (by decide) j i)]; exact h5)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "sta") (by decide) j i)]; exact h6)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "std") (by decide) j i)]; exact h7)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "ste") (by decide) j i)]; exact h8)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "itg") (by decide) j i)]; exact h9)
    | (rw [arrs_setArr, if_neg (lit_ne_tabName (q := "ntg") (by decide) j i)]; exact h10)

/-- Writing a table leaves the level's surface alone. -/
theorem levelPre_setArr_tab {B cap mb ns Ws j : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {σ : Env}
    (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (i idx v : ℕ) :
    LevelPre B n cap mb ns Ws O T j M Gm C (σ.setArr (tabName j i) idx v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨hsz, hd, hq⟩, hdep, hm, hord, hpad0, hTB⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, h7, h8, h9, ⟨hsz.setArr _ idx v, ?_, ?_⟩,
    hdep.setArr _ idx v, hm, orderMem_setArr_tab hord j i idx v, hpad0, hTB⟩
  · rw [arrs_setArr, if_neg (by simp [tabName, String.ext_iff])]; exact h2
  · rw [arrs_setArr, if_neg (by simp [tabName, String.ext_iff])]; exact h3
  · rw [arrs_setArr, if_neg (by simp [tabName, alvName, String.ext_iff])]; exact h4
  · rw [arrs_setArr, if_neg (by simp [tabName, gamName, String.ext_iff])]; exact h5
  · intro c hc
    rw [arrs_setArr, if_neg (by simp [tabName, colName, String.ext_iff])]
    exact h6 c hc
  · rw [arrs_setArr, if_neg (lit_ne_tabName (q := "dist") (by decide) j i)]; exact hd
  · rw [arrs_setArr, if_neg (lit_ne_tabName (q := "q") (by decide) j i)]; exact hq

/-- Moving one of the readback's three private scalars leaves the
level's surface alone. -/
theorem levelPre_setVar_readback {B cap mb ns Ws j : ℕ} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ : Env} {x : String}
    (hxn : x ≠ "n") (hxm : x ≠ "m") (hxlw : x ≠ "lw") (hxmm : x ≠ mnumName j)
    (h : LevelPre B n cap mb ns Ws O T j M Gm C σ) (k : ℕ) :
    LevelPre B n cap mb ns Ws O T j M Gm C (σ.setVar x k) :=
  RamDriverCluster.levelPre_setVar h x hxn hxm hxlw hxmm k

/-- Writing a depth-`j` table leaves the atoms of the depth-`j`
combinations alone: they are read out of the depth-`(j+1)` tables and
out of the scatter flags. -/
theorem evalB_atomExpr_setArr {B q_top cap mb j i i' : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {β : DistFO (sigL cap mb j) 1} (a : StepAtom cap mb j) (σ : Env) (idx v : ℕ) :
    (atomExpr q_top cap mb φ j i β a).evalB B (σ.setArr (tabName j i') idx v)
      = (atomExpr q_top cap mb φ j i β a).evalB B σ := by
  cases a with
  | inl γ =>
    show (Expr.get (tabName (j + 1) _) (.var "rv")).evalB B _ = _
    rw [Expr.evalB, Expr.evalB, arrs_setArr,
      if_neg (Ne.symm (tabName_ne_succ j i' _))]
    rfl
  | inr σs => rfl

/-- Updating a private readback scalar does not change an atom after
the current vertex has been rebound in `"rv"`. -/
theorem evalB_atomExpr_setVar_readback {B q_top cap mb j i : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {β : DistFO (sigL cap mb j) 1}
    (a : StepAtom cap mb j) (σ : Env) {x : String} (k v : ℕ)
    (hflg : ∀ i' k', flgName j i' k' ≠ x) :
    (atomExpr q_top cap mb φ j i β a).evalB B ((σ.setVar x k).setVar "rv" v) =
      (atomExpr q_top cap mb φ j i β a).evalB B (σ.setVar "rv" v) := by
  cases a with
  | inl γ =>
    simp [atomExpr, Expr.evalB]
  | inr σs =>
    simp [atomExpr, Expr.evalB, hflg,
      (by simp [flgName, String.ext_iff] : flgName j i _ ≠ "rv")]

/-- **The frame of one store.** -/
theorem rbBase_setArr_tab {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {σ : Env}
    (h : RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ)
    (i idx v : ℕ) :
    RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val
      (σ.setArr (tabName j i) idx v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨levelPre_setArr_tab h1 i idx v, ?_, ?_, ?_, h5, h6, h7, ?_⟩
  · rw [arrs_setArr, if_neg (by simp [tabName, xofName, String.ext_iff])]; exact h2
  · rw [arrs_setArr, if_neg (by simp [tabName, xmmName, String.ext_iff])]; exact h3
  · rw [arrs_setArr, if_neg (by simp [tabName, asgName, String.ext_iff])]; exact h4
  · intro w hw p hp hr a ha
    obtain ⟨u, hu1, hueval, huiff⟩ := h8 w hw p hp hr a ha
    refine ⟨u, hu1, ?_, huiff⟩
    rw [setArr_setVar, evalB_atomExpr_setArr]
    exact hueval

/-- **The frame of a private readback scalar.** -/
theorem rbBase_setVar_readback {B q_top cap mb ns Ws j : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {σ : Env}
    {x : String} (hxn : x ≠ "n") (hxm : x ≠ "m") (hxlw : x ≠ "lw")
    (hxmm : x ≠ mnumName j) (hxcur : x ≠ curName j)
    (hflg : ∀ i k, flgName j i k ≠ x)
    (h : RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ) (k : ℕ) :
    RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val
      (σ.setVar x k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨levelPre_setVar_readback hxn hxm hxlw hxmm h1 k,
    by simpa using h2, by simpa using h3, by simpa using h4, ?_, h6, h7, ?_⟩
  · rw [vars_setVar, if_neg hxcur.symm]; exact h5
  · intro w hw p hp hr a ha
    obtain ⟨u, hu1, hueval, huiff⟩ := h8 w hw p hp hr a ha
    exact ⟨u, hu1, by
      rw [evalB_atomExpr_setVar_readback a σ k (w : ℕ) hflg]
      exact hueval, huiff⟩

theorem rbBase_setVar_z {B q_top cap mb ns Ws j : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {σ : Env}
    (h : RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ) (k : ℕ) :
    RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val
      (σ.setVar "z" k) :=
  rbBase_setVar_readback (by decide) (by decide) (by decide)
    (by simp [mnumName, String.ext_iff]) (by simp [curName, String.ext_iff])
    (by intro i p; simp [flgName, String.ext_iff]) h k

theorem rbBase_setVar_zend {B q_top cap mb ns Ws j : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {σ : Env}
    (h : RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ) (k : ℕ) :
    RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val
      (σ.setVar "zend" k) :=
  rbBase_setVar_readback (by decide) (by decide) (by decide)
    (by simp [mnumName, String.ext_iff]) (by simp [curName, String.ext_iff])
    (by intro i p; simp [flgName, String.ext_iff]) h k

theorem rbBase_setVar_rv {B q_top cap mb ns Ws j : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {σ : Env}
    (h : RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ) (k : ℕ) :
    RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val
      (σ.setVar "rv" k) :=
  rbBase_setVar_readback (by decide) (by decide) (by decide)
    (by simp [mnumName, String.ext_iff]) (by simp [curName, String.ext_iff])
    (by intro i p; simp [flgName, String.ext_iff]) h k

/-- Setting a scalar to the value it already holds changes nothing. -/
theorem setVar_self {σ : Env} {x : String} {v : ℕ} (h : σ.vars x = v) : σ.setVar x v = σ := by
  cases σ
  simp only [Env.setVar, Env.mk.injEq, and_true]
  funext y
  by_cases hy : y = x
  · subst hy; simpa using h.symm
  · simp [hy]

/-! #### One cell, one block

The block is a straight line of stores, one per tabled formula, and the
walk is an induction along the list. What one store contributes is the
value of its own cell, which `evalB_rbCell` reads; what it leaves alone
is every other table, which `tabName_inj` reads. -/

/-- The cost of one cell of the readback's block. -/
noncomputable def cellCost (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j i : ℕ)
    (β : DistFO (sigL cap mb j) 1) : ℕ := 2 + (rbCell q_top cap mb φ j i β).size

/-- The cost of the readback's block from position `p` on. -/
noncomputable def blockCost (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) :
    ℕ → List (DistFO (sigL cap mb j) 1) → ℕ
  | _, [] => 1
  | p, β :: l => cellCost q_top cap mb φ j p β + blockCost q_top cap mb φ j (p + 1) l

/-- **One cell of the block.** The store writes the vertex's own value
of the formula at position `p`, and leaves every other table where it
was. -/
theorem store_step_spec {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {T₀ : ℕ → ℕ → ℕ} (hB : 1 < B) (hn : n < B)
    {z₀ : ℕ} (hz₀ : Xmem z₀ < n) (hcc : asg (Xmem z₀) = cc) (p : ℕ)
    (hp : p < (tablesAt q_top cap mb φ j).length) :
    Spec B
      (fun σ => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ ∧
        σ.vars "z" = z₀ ∧ σ.vars "rv" = Xmem z₀ ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i) (tablesAt q_top cap mb φ j)[i]
            (tabName j i) (T₀ i) σ (if i < p then z₀ + 1 else z₀))
      (.store (tabName j p) (.var "rv") (rbCell q_top cap mb φ j p (tablesAt q_top cap mb φ j)[p]))
      (fun _ σ' => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ' ∧
        σ'.vars "z" = z₀ ∧ σ'.vars "rv" = Xmem z₀ ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i) (tablesAt q_top cap mb φ j)[i]
            (tabName j i) (T₀ i) σ' (if i < p + 1 then z₀ + 1 else z₀))
      (cellCost q_top cap mb φ j p (tablesAt q_top cap mb φ j)[p]) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hbase, hz, hrv, htab⟩ := hσ
  have hrvB : σ.vars "rv" < B := by rw [hrv]; omega
  have hidx : (Expr.var "rv").evalB B σ = some (Xmem z₀) := by
    rw [evalB_var hrvB, hrv]
  -- the value of the cell at the vertex the readback stands on
  have hval : ∀ h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
        DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[p]),
      ∀ a ∈ (bcOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[p]) h).atoms, ∃ u ≤ 1,
      (atomExpr q_top cap mb φ j p (tablesAt q_top cap mb φ j)[p] a).evalB B σ = some u ∧
        (u ≠ 0 ↔ val ⟨Xmem z₀, hz₀⟩ p a) := by
    intro h a ha
    obtain ⟨u, hu1, hueval, huiff⟩ :=
      hbase.2.2.2.2.2.2.2 ⟨Xmem z₀, hz₀⟩ hcc p hp h a ha
    exact ⟨u, hu1, by rwa [setVar_self hrv] at hueval, huiff⟩
  obtain ⟨u, hu1, hueval, huiff⟩ := evalB_rbCell (i := p) hB hval
  -- the array being written is there, at the carrier's length
  obtain ⟨Tb, hTb, hTb0, hTbval⟩ := htab p hp
  have hlen : Xmem z₀ < (σ.arrs (tabName j p)).length := by
    rw [hTb, length_arrOf]; exact hz₀
  refine ⟨σ.setArr (tabName j p) (Xmem z₀) u, _, Run.store hidx hueval hlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cellCost]
  · exact rbBase_setArr_tab hbase p (Xmem z₀) u
  · rw [vars_setArr]; exact hz
  · rw [vars_setArr]; exact hrv
  · intro i hi
    by_cases hip : i = p
    · subst hip
      refine ⟨fun k => if k = Xmem z₀ then u else Tb k, ?_, ?_, ?_⟩
      · rw [arrs_setArr, if_pos rfl, hTb, set_arrOf]
      · intro w hw
        dsimp only
        rw [if_neg (fun hc => hw (by rw [hc]; exact hcc))]
        exact hTb0 w hw
      · intro q hqlo hqhi
        rw [if_pos (by omega)] at hqhi
        dsimp only
        by_cases hqv : Xmem q = Xmem z₀
        · rw [if_pos hqv]
          have hqn : Xmem q < n := by rw [hqv]; exact hz₀
          refine ⟨hqn, fun _ => ⟨hu1, ?_⟩⟩
          rw [huiff]
          have hv : (⟨Xmem q, hqn⟩ : Fin n) = ⟨Xmem z₀, hz₀⟩ := Fin.ext hqv
          rw [hv]
        · rw [if_neg hqv]
          have hqne : q ≠ z₀ := fun h => hqv (by rw [h])
          refine hTbval q hqlo ?_
          rw [if_neg (lt_irrefl _)]
          omega
    · obtain ⟨Tc, hTc, hTc0, hTcval⟩ := htab i hi
      refine ⟨Tc, ?_, hTc0, ?_⟩
      · rw [arrs_setArr, if_neg (tabName_ne_of_ne j hip), hTc]
      · intro q hqlo hqhi
        refine hTcval q hqlo ?_
        by_cases hlt : i < p
        · rw [if_pos hlt]
          rw [if_pos (by omega : i < p + 1)] at hqhi
          exact hqhi
        · rw [if_neg hlt]
          rw [if_neg (by omega : ¬ i < p + 1)] at hqhi
          exact hqhi

/-- **The block of one vertex**, by induction along the table list: at
the end every table of the depth is right at the vertex the readback
stands on. -/
theorem block_spec {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {T₀ : ℕ → ℕ → ℕ} (hB : 1 < B) (hn : n < B)
    {z₀ : ℕ} (hz₀ : Xmem z₀ < n) (hcc : asg (Xmem z₀) = cc) :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (p : ℕ), l = (tablesAt q_top cap mb φ j).drop p →
      Spec B
        (fun σ => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ ∧
          σ.vars "z" = z₀ ∧ σ.vars "rv" = Xmem z₀ ∧
          ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
            TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i) (tablesAt q_top cap mb φ j)[i]
              (tabName j i) (T₀ i) σ (if i < p then z₀ + 1 else z₀))
        (foldIdx (fun i β => .store (tabName j i) (.var "rv") (rbCell q_top cap mb φ j i β)) p l)
        (fun _ σ' => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ' ∧
          σ'.vars "z" = z₀ ∧ σ'.vars "rv" = Xmem z₀ ∧
          ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
            TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i) (tablesAt q_top cap mb φ j)[i]
              (tabName j i) (T₀ i) σ' (if i < p + l.length then z₀ + 1 else z₀))
        (blockCost q_top cap mb φ j p l) := by
  intro l
  induction l with
  | nil =>
    intro p _
    exact Spec.skip.post (by rintro σ σ' hσ rfl; simpa using hσ)
  | cons β l ih =>
    intro p hl
    have hp : p < (tablesAt q_top cap mb φ j).length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hl
      exact absurd hl (by simp)
    rw [List.drop_eq_getElem_cons hp] at hl
    obtain ⟨hβ, hltail⟩ := List.cons.inj hl
    subst hβ
    have hstep := (store_step_spec (ns := ns) (O := O) (T := T) (M := M) (Gm := Gm) (C := C)
      (ou := ou) (val := val) hB hn hz₀ hcc p hp).seq (ih (p + 1) hltail)
      (fun _ _ _ hQ => hQ) (fun _ _ _ _ _ hQ' => hQ')
    refine hstep.post ?_ |>.mono (le_of_eq ?_)
    · intro σ σ' _ hQ
      refine ⟨hQ.1, hQ.2.1, hQ.2.2.1, ?_⟩
      intro i hi
      simp only [List.length_cons]
      have hq := hQ.2.2.2 i hi
      by_cases hlt : i < p + (l.length + 1)
      · rw [if_pos hlt]
        rwa [if_pos (by omega : i < p + 1 + l.length)] at hq
      · rw [if_neg hlt]
        rwa [if_neg (by omega : ¬ i < p + 1 + l.length)] at hq
    · rw [blockCost]

/-- The block always costs something: the empty block is a `skip`. -/
theorem one_le_blockCost (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j p : ℕ)
    (l : List (DistFO (sigL cap mb j) 1)) : 1 ≤ blockCost q_top cap mb φ j p l := by
  induction l generalizing p with
  | nil => rw [blockCost]
  | cons β l ih => rw [blockCost]; exact le_trans (ih (p + 1)) (Nat.le_add_left _ _)

theorem wvars_readbackFold (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) :
    ∀ (p : ℕ) (l : List (DistFO (sigL cap mb j) 1)),
      (foldIdx (fun i β => .store (tabName j i) (.var "rv")
        (rbCell q_top cap mb φ j i β)) p l).wvars = [] := by
  intro p l
  induction l generalizing p with
  | nil => rfl
  | cons β l ih => rw [foldIdx, Com.wvars, ih (p + 1), Com.wvars, List.append_nil]

/-- The assignment test of the readback's loop: the vertex is the one
the cover assigned to the centre being processed. -/
theorem evalB_asgCond {B j : ℕ} {asg : ℕ → ℕ} {cc z₀ : ℕ} {σ : Env}
    (hasg : σ.arrs (asgName j) = arrOf n asg) (hasgB : asg z₀ < B)
    (hc : σ.vars (curName j) = cc) (hcB : cc < B) (hrv : σ.vars "rv" = z₀)
    (hz₀ : z₀ < n) (hn : n < B) :
    ∃ b, (Cond.eq (.get (asgName j) (.var "rv")) (.var (curName j))).evalB B σ = some b ∧
      (b = true ↔ asg z₀ = cc) := by
  have hzB : σ.vars "rv" < B := by rw [hrv]; omega
  refine evalB_condEq_isSome (m := asg z₀) (n := cc) ?_ ?_
  · refine evalB_get (evalB_var hzB) ?_ hasgB
    rw [hrv, hasg]
    exact getElem?_arrOf _ hz₀
  · have h := evalB_var (x := curName j) (σ := σ) (B := B) (by omega)
    rwa [hc] at h

/-- The invariant of the readback's loop: the tables are right at every
member slot of the current block the slot pointer has passed. -/
def RbInv (B q_top cap mb ns Ws j : ℕ) {n : ℕ} (φ : Lax3.FirstOrder.FO 0) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (Xoff Xmem asg : ℕ → ℕ) (cc : ℕ) (ou : List ℕ)
    (val : Fin n → ℕ → StepAtom cap mb j → Prop) (T₀ : ℕ → ℕ → ℕ) (σ : Env) : Prop :=
  RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ ∧
    σ.vars "zend" = Xoff (cc + 1) ∧ Xoff cc ≤ σ.vars "z" ∧
    σ.vars "z" ≤ Xoff (cc + 1) ∧
    ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
      TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i) (tablesAt q_top cap mb φ j)[i] (tabName j i)
        (T₀ i) σ (σ.vars "z")

/-- **One turn of the readback's loop.** -/
theorem ite_spec {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {T₀ : ℕ → ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) {z₀ : ℕ}
    (hz₀ : Xmem z₀ < n) (hasgB : asg (Xmem z₀) < B) :
    Spec B
      (fun σ => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ ∧
        σ.vars "z" = z₀ ∧ σ.vars "rv" = Xmem z₀ ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i)
            (tablesAt q_top cap mb φ j)[i] (tabName j i) (T₀ i) σ z₀)
      (.ite (.eq (.get (asgName j) (.var "rv")) (.var (curName j)))
        (foldIdx (fun i β =>
            .store (tabName j i) (.var "rv") (rbCell q_top cap mb φ j i β)) 0
          (tablesAt q_top cap mb φ j)) .skip)
      (fun _ σ' => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ' ∧
        σ'.vars "z" = z₀ ∧ σ'.vars "rv" = Xmem z₀ ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i)
            (tablesAt q_top cap mb φ j)[i] (tabName j i) (T₀ i) σ' (z₀ + 1))
      (1 + 4 + blockCost q_top cap mb φ j 0 (tablesAt q_top cap mb φ j)) := by
  classical
  set L := (tablesAt q_top cap mb φ j).length with hL
  refine Spec.ite ?_ ?_ ?_
  · rintro σ ⟨hbase, hz, hrv, -⟩
    obtain ⟨b, hb, -⟩ := evalB_asgCond hbase.2.2.2.1
      hasgB hbase.2.2.2.2.1 hbase.2.2.2.2.2.1 hrv hz₀ hn
    exact ⟨b, hb⟩
  · refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨hbase, hz, hrv, htab⟩, hcond⟩ := hσ
    obtain ⟨b, hb, hbiff⟩ := evalB_asgCond hbase.2.2.2.1
      hasgB hbase.2.2.2.2.1 hbase.2.2.2.2.2.1 hrv hz₀ hn
    have hasgz : asg (Xmem z₀) = cc := hbiff.mp (Option.some.inj (hb.symm.trans hcond))
    have hpre : ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
        TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i)
          (tablesAt q_top cap mb φ j)[i] (tabName j i) (T₀ i) σ
          (if i < 0 then z₀ + 1 else z₀) := by
      intro i hi
      rw [if_neg (by omega : ¬ i < 0)]
      exact htab i hi
    have hdrop : tablesAt q_top cap mb φ j = (tablesAt q_top cap mb φ j).drop 0 := by
      rw [List.drop_zero]
    obtain ⟨σ', hrun, hQ⟩ :=
      (block_spec (ns := ns) (O := O) (T := T) (M := M) (Gm := Gm) (C := C)
        (ou := ou) (val := val) hB hn hz₀ hasgz (tablesAt q_top cap mb φ j) 0
        hdrop).run (σ := σ) ⟨hbase, hz, hrv, hpre⟩
    refine ⟨σ', _, hrun, le_rfl, hQ.1, hQ.2.1, hQ.2.2.1, ?_⟩
    intro i hi
    have hq := hQ.2.2.2 i hi
    rwa [if_pos (by omega : i < 0 + (tablesAt q_top cap mb φ j).length)] at hq
  · refine (Spec.skip.post ?_).mono (one_le_blockCost q_top cap mb φ j 0 _)
    rintro σ σ' ⟨⟨hbase, hz, hrv, htab⟩, hcond⟩ rfl
    obtain ⟨b, hb, hbiff⟩ := evalB_asgCond hbase.2.2.2.1
      hasgB hbase.2.2.2.2.1 hbase.2.2.2.2.2.1 hrv hz₀ hn
    have hbfalse : b = false := Option.some.inj (hb.symm.trans hcond)
    have hasgz : asg (Xmem z₀) ≠ cc := by
      intro hc
      rw [hbiff.mpr hc] at hbfalse
      exact absurd hbfalse (by simp)
    refine ⟨hbase, hz, hrv, ?_⟩
    intro i hi
    obtain ⟨Tb, hTb, hTb0, hTbval⟩ := htab i hi
    refine ⟨Tb, hTb, hTb0, ?_⟩
    intro q hqlo hqhi
    by_cases hq : q < z₀
    · exact hTbval q hqlo hq
    · have hqeq : q = z₀ := by omega
      have hqn : Xmem q < n := by rw [hqeq]; exact hz₀
      refine ⟨hqn, fun hqcc => ?_⟩
      exact (hasgz (by rwa [hqeq] at hqcc)).elim

/-- The cost of the readback: one guarded table block per member slot. -/
noncomputable def rbCost (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j s : ℕ) : ℕ :=
  (1 + 4 + blockCost q_top cap mb φ j 0 (tablesAt q_top cap mb φ j) + 11) * s + 12

theorem rbCost_mono (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) :
    Monotone (rbCost q_top cap mb φ j) := by
  intro a b hab
  simp only [rbCost]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hab) _

/-- **The readback walks the current cover block and writes every table.**
At every vertex the cover assigned to the centre being processed, the
bit of every tabled formula is the value of that formula's own boolean
combination over the atom valuation the caller supplies. -/
theorem readback_spec {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {Xoff Xmem asg : ℕ → ℕ} {cc : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop} {T₀ : ℕ → ℕ → ℕ}
    {G : SimpleGraph (Fin n)} {A₀ ord : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {r m : ℕ}
    (hB : 1 < B) (hn : n < B) (hcc : cc < n)
    (hout : RamCover.CoverOut G A₀ π ord r m Xoff Xmem asg) (hm : m ≤ n * n) (hmB : m < B) :
    Spec B
      (fun σ => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ ∧
        ∀ (i : ℕ), i < (tablesAt q_top cap mb φ j).length →
          σ.arrs (tabName j i) = arrOf n (T₀ i))
      (readbackCom q_top cap mb φ j)
      (fun _ σ' => RbBase B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val σ' ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          TabOk q_top cap mb j Xoff Xmem asg cc (fun v => val v i) (tablesAt q_top cap mb φ j)[i]
            (tabName j i) (T₀ i) σ' (Xoff (cc + 1)))
      (rbCost q_top cap mb φ j (Xoff (cc + 1) - Xoff cc)) := by
  rw [readbackCom_eq, rbCost]
  have hoff_le : ∀ k ≤ n, Xoff k ≤ m := by
    have key : ∀ d k, k + d = n → Xoff k ≤ Xoff n := by
      intro d
      induction d with
      | zero => intro k hk; rw [show k = n by omega]
      | succ d ih => intro k hk; exact le_trans (hout.mono k (by omega)) (ih (k + 1) (by omega))
    intro k hk
    rw [← hout.last]
    exact key (n - k) k (by omega)
  let I := RbInv B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg cc ou val T₀
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hbase₀, hsized⟩ := hσ
  obtain ⟨σ', K, hrun, hKr, hI, hz⟩ := RamDriverAugment.blockScan_run
    (B := B) (o := xofName j) (t := xmmName j) (x := curName j)
    (j := "z") (jend := "zend") (w := "rv")
    (c := .ite (.eq (.get (asgName j) (.var "rv")) (.var (curName j)))
      (foldIdx (fun i β => .store (tabName j i) (.var "rv")
        (rbCell q_top cap mb φ j i β)) 0 (tablesAt q_top cap mb φ j)) .skip)
    (nv := n) (len := n * n)
    (Kb := 1 + 4 + blockCost q_top cap mb φ j 0 (tablesAt q_top cap mb φ j))
    (v := cc) (off := Xoff) (tgt := Xmem) (I := I) (σ := σ)
    (by simp [curName, String.ext_iff]) (by decide) hB hcc (by omega)
    hbase₀.2.1 (hout.mono cc hcc)
    (le_trans (hoff_le (cc + 1) (by omega)) hm)
    (lt_of_le_of_lt (hoff_le (cc + 1) (by omega)) hmB)
    hbase₀.2.2.2.2.1
    (by intro τ hτ; exact hτ.1.2.2.1)
    (by intro p hp; exact lt_trans (hout.mem_lt p (lt_of_lt_of_le hp (hoff_le _ (by omega)))) hn)
    (by intro τ hτ; exact ⟨hτ.2.1, hτ.2.2.2.1⟩)
    (by
      refine ⟨rbBase_setVar_zend (rbBase_setVar_z hbase₀ (Xoff cc)) (Xoff (cc + 1)), ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simp [hout.mono cc hcc]
      · intro i hi
        refine ⟨T₀ i, by simpa using hsized i hi, fun _ _ => rfl, ?_⟩
        intro p hp hlt
        rw [show ((σ.setVar "z" (Xoff cc)).setVar "zend" (Xoff (cc + 1))).vars "z" =
          Xoff cc by simp] at hlt
        omega)
    (by
      intro τ hτ hlt
      obtain ⟨hbase, hend, hlo, hle, htab⟩ := hτ
      have hp_m : τ.vars "z" < m := lt_of_lt_of_le hlt (hoff_le _ (by omega))
      have hp_n : Xmem (τ.vars "z") < n := hout.mem_lt _ hp_m
      obtain ⟨τ', hrun, hbase', hz', hrv', htab'⟩ :=
        (ite_spec (ns := ns) (O := O) (T := T) (M := M) (Gm := Gm) (C := C)
          (Xoff := Xoff) (Xmem := Xmem) (asg := asg) (cc := cc) (ou := ou)
          (val := val) (T₀ := T₀) hB hn hp_n
          (lt_trans (hout.asg_lt _ hp_n) hn)).run (σ :=
            τ.setVar "rv" (Xmem (τ.vars "z")))
          ⟨rbBase_setVar_rv hbase _, by simp, by simp, by
            intro i hi
            simpa [TabOk] using htab i hi⟩
      have hzend : τ'.vars "zend" = τ.vars "zend" :=
        hrun.frame_var "zend" (by
          simp [Com.wvars, wvars_readbackFold])
      refine ⟨τ', _, hrun, le_rfl, hz', ?_⟩
      refine ⟨rbBase_setVar_z hbase' (τ.vars "z" + 1), ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_neg (by decide : "zend" ≠ "z"), hzend, hend]
      · rw [vars_setVar, if_pos rfl]; omega
      · rw [vars_setVar, if_pos rfl]; omega
      · intro i hi
        rw [vars_setVar, if_pos rfl]
        simpa [TabOk] using htab' i hi)
  refine ⟨σ', K, hrun, hKr, hI.1, ?_⟩
  intro i hi
  rw [← hz]
  exact hI.2.2.2.2 i hi

/-! #### The frame of the whole readback

Everything the readback does not write is read off its syntax by
`Lax13Proofs.Imp.Com.warrs` and `wvars`, and the two lemmas below are
what those two lists are: the depth's own tables, and the counter. -/

theorem wvars_foldIdx (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) :
    ∀ (p : ℕ) (l : List (DistFO (sigL cap mb j) 1)),
      (foldIdx (fun i β => .store (tabName j i) (.var "rv") (rbCell q_top cap mb φ j i β))
        p l).wvars = [] := by
  exact wvars_readbackFold q_top cap mb φ j

theorem mem_warrs_foldIdx {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} {j : ℕ} {a : String} :
    ∀ (p : ℕ) (l : List (DistFO (sigL cap mb j) 1)),
      a ∈ (foldIdx (fun i β => .store (tabName j i) (.var "rv") (rbCell q_top cap mb φ j i β))
        p l).warrs → ∃ i, a = tabName j i := by
  intro p l
  induction l generalizing p with
  | nil => intro h; exact absurd h (by rw [foldIdx, Com.warrs]; simp)
  | cons β l ih =>
    intro h
    rw [foldIdx, Com.warrs] at h
    rcases List.mem_append.mp h with h | h
    · rw [Com.warrs] at h
      exact ⟨p, by simpa using h⟩
    · exact ih (p + 1) h

/-- The readback stores into the depth's tables and into nothing
else. -/
theorem mem_warrs_readbackCom {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} {j : ℕ}
    {a : String} (h : a ∈ (readbackCom q_top cap mb φ j).warrs) : ∃ i, a = tabName j i := by
  rw [readbackCom_eq] at h
  simp only [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.warrs,
    List.append_nil, List.nil_append] at h
  exact mem_warrs_foldIdx 0 _ h

/-- The readback assigns its slot pointer, end pointer and loaded vertex only. -/
theorem not_mem_wvars_readbackCom {q_top cap mb : ℕ} {φ : Lax3.FirstOrder.FO 0} {j : ℕ}
    {y : String} (hyz : y ≠ "z") (hyend : y ≠ "zend") (hyrv : y ≠ "rv") :
    y ∉ (readbackCom q_top cap mb φ j).wvars := by
  rw [readbackCom_eq]
  simp only [RamAugment.blockScan, Csr.loadRow, Csr.scan, Com.wvars, wvars_foldIdx,
    List.append_nil, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_append]
  tauto

/-! ### The obligation

`RamDriverCluster.ReadbackStep` is the repaired readback obligation:
its valuation is indexed by the vertex, which is what the loop's
postcondition needs and what `RamDriver.sat_iff_eval_step` produces.
Everything the walk needs beyond it is now a conjunct of its own
precondition, so this file consumes it as it stands and carries no gap.

* **Lengths.** An out-of-range store has no derivation at all in IMP+,
  so a precondition that does not size the depth-`j` table arrays
  cannot support a specification for a program that stores into them.
  `RamDriver.TablesSized` is that clause, built on the driver's own
  `RamDriver.Sized`.
* **Bits.** `RamDriver.bcExpr` is truncated arithmetic on bits: a
  negation is `1 - u` and a conjunction is a product, so a cell or a
  flag holding something other than `0` or `1` makes the *value* of a
  combination wrong and can push it over the bound. That the
  depth-`(j+1)` cells are bits is now a clause of
  `RamDriver.TableInv`, and that the scatter flags are is now the
  scatter phase's own postcondition — both true of the passes that
  write them, `readback_spec` itself by `evalB_rbCell`.
* **The centre.** `σ.vars "c" < n` is a conjunct of `ReadbackStep`'s
  precondition and `n < B` a hypothesis here; the cover's block bound
  and `RamCover.CoverOut.asg_lt` supply the loaded member's bounds. -/

/-- A scatter flag is not the readback's counter. -/
theorem flgName_ne_z (j i k : ℕ) : flgName j i k ≠ "z" := by
  simp [flgName, String.ext_iff]

theorem flgName_ne_rv (j i k : ℕ) : flgName j i k ≠ "rv" := by
  simp [flgName, String.ext_iff]

/-- **The readback of one cluster, discharged.** -/
theorem readbackStep {B q_top cap mb ns Ws j : ℕ} {n : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {ord Xoff Xmem asg : ℕ → ℕ} {m k : ℕ} {X W : Set (Fin n)} {w : Fin mb → Fin n}
    {Alv' Gam' : ℕ → ℕ} {C' : ℕ → ℕ → ℕ} {K : ℕ} (hB : 1 < B) (hn : n < B)
    (hkn : k < n)
    (hK : RamCover.CoverOut G M π ord cap m Xoff Xmem asg →
      rbCost q_top cap mb φ j (Xoff (k + 1) - Xoff k) ≤ K) :
    ReadbackStep B q_top cap mb ns Ws j φ G O T M Gm C π ord Xoff Xmem asg m k X W w
      Alv' Gam' C' K := by
  classical
  intro σ hσ
  obtain ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htabinv, htsz, hck, hvis, hflag⟩ := hσ
  have hcn : σ.vars (curName j) < n := by rw [hck]; exact hkn
  have hcB : σ.vars (curName j) < B := lt_trans hcn hn
  -- the depth's own tables are there, and this names their cells
  set T₀ : ℕ → ℕ → ℕ := fun i v => (σ.arrs (tabName j i)).getD v 0 with hT₀def
  have hsz : ∀ (i : ℕ), i < (tablesAt q_top cap mb φ j).length →
      σ.arrs (tabName j i) = arrOf n (T₀ i) := by
    intro i hi
    obtain ⟨g, hg⟩ := htsz.get j hi
    rw [hg]
    refine arrOf_congr fun v hv => ?_
    rw [hT₀def]
    simp only [hg, getD_arrOf _ hv]
  obtain ⟨hlevel, hplayrec, hordA, hxoffA, hxmemA, hasgA, hxpA, hmn, hmB, hordlt, hcout⟩ := hturn
  -- **the atoms of every tabled formula, at every vertex the turn was assigned**
  -- (wave R1.8-T3-flip (c2b)). A visited vertex is in the cluster and alive at the
  -- parent depth (`hvis`), so it is either alive at the child depth or a vertex
  -- THIS turn killed — `RamDriverCluster.BatchData`'s pointwise clause is the
  -- dichotomy, and `Refine.DeadRowProbe.readback_dead_read_is_kill` is the design
  -- reading of it. Either way its row exists, which is all the local atom needs.
  have hrow : ∀ v : Fin n, asg (v : ℕ) = σ.vars (curName j) →
      v ∈ RamDriverCluster.rowDom M Alv' X W := by
    intro v hv
    by_cases hal : Alv' (v : ℕ) = 0
    · obtain ⟨hM, hX⟩ := hvis v hv
      refine Or.inr ⟨hM, hX, ?_⟩
      by_contra hW
      exact absurd hal ((hdata.1.2.2.2.2.2.2.1 v).2 ⟨hM, hX, hW⟩)
    · exact Or.inl hal
  have hatom : ∀ (v : Fin n), asg (v : ℕ) = σ.vars (curName j) →
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length)
      (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
        DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])),
      ∀ a ∈ (bcOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[i]) h).atoms,
        ∃ u ≤ 1, (atomExpr q_top cap mb φ j i (tablesAt q_top cap mb φ j)[i] a).evalB B
            (σ.setVar "rv" (v : ℕ)) = some u ∧
          (u ≠ 0 ↔ atomVal (stepArenaP (masked G M) X w)
            (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) v a) := by
    intro v hvcur i hi h a ha
    have hrvv : (σ.setVar "rv" (v : ℕ)).vars "rv" = (v : ℕ) := by
      rw [vars_setVar, if_pos rfl]
    cases a with
    | inl γ =>
      have hmemγ : γ ∈ tablesAt q_top cap mb φ (j + 1) :=
        bcLocals_subset_tablesAt_succ (List.getElem_mem hi) ((mem_bcAtomsOf_left h).mpr ha)
      obtain ⟨hlt, heq⟩ := getElem_posOf hmemγ
      obtain ⟨Tc, hTc, hTc1, hTcval⟩ := htabinv _ hlt
      have hvd : v ∈ RamDriverCluster.rowDom M Alv' X W := hrow v hvcur
      refine ⟨Tc (v : ℕ), hTc1 _ hvd, ?_, ?_⟩
      · show (Expr.get (tabName (j + 1) (posOf γ (tablesAt q_top cap mb φ (j + 1))))
          (.var "rv")).evalB B _ = _
        refine evalB_get (k := (v : ℕ)) ?_ ?_ (lt_of_le_of_lt (hTc1 _ hvd) hB)
        · rw [evalB_var (by rw [hrvv]; omega), hrvv]
        · rw [arrs_setVar, hTc]
          exact getElem?_arrOf _ v.isLt
      · rw [hTcval v hvd, heq, masked_alv_eq hdata, hcolread]
        exact Iff.rfl
    | inr σs =>
      have hmem : σs ∈ (bcAtomsOf q_top (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2 :=
        (mem_bcAtomsOf_right h).mpr ha
      obtain ⟨hf1, hfiff⟩ := hflag i hi σs hmem
      refine ⟨σ.vars (flgName j i (posOf σs (bcAtomsOf q_top
          (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)), hf1, ?_, hfiff⟩
      show (Expr.var (flgName j i _)).evalB B _ = _
      rw [evalB_var (by
          rw [vars_setVar, if_neg (flgName_ne_rv _ _ _)]; omega),
        vars_setVar, if_neg (flgName_ne_rv _ _ _)]
  -- the walk
  obtain ⟨σ', hrun, ⟨hbase', htab'⟩, hfv, hfa, -, -⟩ :=
    (readback_spec (ns := ns) (O := O) (T := T) (M := M) (Gm := Gm) (C := C)
      (Xoff := Xoff) (Xmem := Xmem) (asg := asg)
      (cc := σ.vars (curName j)) (ou := σ.out) (T₀ := T₀)
      (val := fun v _ a => atomVal (stepArenaP (masked G M) X w)
        (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) v a)
      hB hn hcn hcout hmn hmB).frame.run (σ := σ)
      ⟨⟨hlevel, hxoffA, hxmemA, hasgA, rfl, hcB, rfl, hatom⟩, hsz⟩
  have hframeA : ∀ a : String, (∀ i, a ≠ tabName j i) → σ'.arrs a = σ.arrs a :=
    fun a hane => hfa a (fun hm => by
      obtain ⟨i, hi⟩ := mem_warrs_readbackCom hm
      exact hane i hi)
  have hframeV : ∀ x : String, x ≠ "z" → x ≠ "zend" → x ≠ "rv" →
      σ'.vars x = σ.vars x :=
    fun x hxz hxe hxv => hfv x (not_mem_wvars_readbackCom hxz hxe hxv)
  have hKr : rbCost q_top cap mb φ j
      (Xoff (σ.vars (curName j) + 1) - Xoff (σ.vars (curName j))) ≤ K :=
    by simpa [hck] using hK hcout
  refine ⟨σ', hrun.mono hKr, ⟨hbase'.1,
    hplayrec.congr (fun a _ => hframeV (ctrName a)
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]))
      (fun a _ => hframeA (gamName a) (fun i => Ne.symm (by
        simp [tabName, gamName, String.ext_iff]))),
    ?_, ?_, ?_, hbase'.2.2.2.1, ?_, hmn, hmB, hordlt, hcout⟩,
    hbase'.2.2.2.2.2.2.1, hbase'.2.2.2.2.1, ?_⟩
  · rw [hframeA (ordName j) (fun i => Ne.symm (by
      simp [tabName, ordName, String.ext_iff]))]; exact hordA
  · rw [hframeA (xofName j) (fun i => Ne.symm (by
      simp [tabName, xofName, String.ext_iff]))]; exact hxoffA
  · rw [hframeA (xmmName j) (fun i => Ne.symm (by
      simp [tabName, xmmName, String.ext_iff]))]; exact hxmemA
  · rw [hframeV (xpName j) (by simp [xpName, String.ext_iff])
      (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff])]
    exact hxpA
  · intro i hi
    obtain ⟨Tb, hTb, hTb0, hTbval⟩ := htab' i hi
    refine ⟨Tb, T₀ i, hTb, hsz i hi, hTb0, fun v hv => ?_⟩
    have hcl : RamCover.InCluster (masked G M) π cap (ord (σ.vars (curName j))) (v : ℕ) := by
      have hs := hcout.asg_cover (v : ℕ) v.isLt (WalkDistance.mem_ball_self _ _ _)
      simpa [hv] using hs
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := (hcout.block _ hcn (v : ℕ)).mpr hcl
    obtain ⟨hpn, hrowp⟩ := hTbval p hp₁ hp₂
    obtain ⟨hbit, hval⟩ := hrowp (by rwa [hp₃])
    have hpv : (⟨Xmem p, hpn⟩ : Fin n) = v := Fin.ext hp₃
    refine ⟨by simpa [hp₃] using hbit, ?_⟩
    simpa [hp₃, hpv] using hval

end Readback

/-! ### The arithmetic of the base case's bits

`RamDriver.eqBitExpr`, `RamDriver.orBitExpr` and `RamDriver.rowEqExpr`
are the truncated-arithmetic connectives the base case is written in:
the representative scan tests row equality with a product of cell
equalities and accumulates its hit flag with a disjunction, and the
generated evaluator of `RamDriver.botCom` uses the same disjunction at
both quantifiers. Each is one arithmetic identity on values below the
bound, and none of them is about a program. -/

/-- **The equality bit.** -/
theorem evalB_eqBitExpr {B : ℕ} {σ : Env} {e f : Expr} {m k : ℕ} (hB : 1 < B)
    (hm : m < B) (hk : k < B) (he : e.evalB B σ = some m) (hf : f.evalB B σ = some k) :
    ∃ u ≤ 1, (eqBitExpr e f).evalB B σ = some u ∧ (u ≠ 0 ↔ m = k) := by
  refine ⟨1 - ((m - k) + (k - m)), by omega, ?_, by omega⟩
  refine evalB_bin (evalB_lit hB) ?_ (by simp; omega)
  exact evalB_bin (evalB_bin he hf (by simp; omega)) (evalB_bin hf he (by simp; omega))
    (by simp; omega)

/-- **The disjunction bit.** -/
theorem evalB_orBitExpr {B : ℕ} {σ : Env} {e f : Expr} {u w : ℕ} (hB : 1 < B)
    (hu1 : u ≤ 1) (hw1 : w ≤ 1) (he : e.evalB B σ = some u) (hf : f.evalB B σ = some w) :
    ∃ t ≤ 1, (orBitExpr e f).evalB B σ = some t ∧ (t ≠ 0 ↔ (u ≠ 0 ∨ w ≠ 0)) := by
  refine ⟨1 - (1 - u) * (1 - w), by omega, ?_, ?_⟩
  · refine evalB_bin (evalB_lit hB) ?_ (by simp; omega)
    refine evalB_bin (evalB_bin (evalB_lit hB) he (by simp; omega))
      (evalB_bin (evalB_lit hB) hf (by simp; omega)) ?_
    simp only [Bop.apply_mul]
    calc (1 - u) * (1 - w) ≤ 1 * 1 := Nat.mul_le_mul (by omega) (by omega)
      _ < B := by omega
  · constructor
    · intro h
      by_contra hc
      have h1 : u = 0 := by by_contra hu; exact hc (Or.inl hu)
      have h2 : w = 0 := by by_contra hw; exact hc (Or.inr hw)
      rw [h1, h2] at h
      exact h (by omega)
    · rintro (h | h)
      · have hu : u = 1 := by omega
        subst hu; simp
      · have hw : w = 1 := by omega
        subst hw; simp

/-- **The row-equality product**, over any list of colours. -/
theorem evalB_rowFold {B n j : ℕ} {σ : Env} {x y : String} {C : ℕ → ℕ → ℕ} (hB : 1 < B)
    (hx : σ.vars x < n) (hy : σ.vars y < n) (hn : n < B) :
    ∀ l : List ℕ, (∀ c ∈ l, σ.arrs (colName j c) = arrOf n (C c)) →
      (∀ c ∈ l, ∀ v < n, C c v < B) →
      ∃ u ≤ 1, (l.foldr (fun c e =>
          Expr.mul (eqBitExpr (Expr.get (colName j c) (.var x))
            (Expr.get (colName j c) (.var y))) e)
          (Expr.lit 1)).evalB B σ = some u ∧
        (u ≠ 0 ↔ ∀ c ∈ l, C c (σ.vars x) = C c (σ.vars y)) := by
  intro l
  induction l with
  | nil => exact fun _ _ => ⟨1, le_rfl, evalB_lit hB, by simp⟩
  | cons c l ih =>
    intro harr hbnd
    obtain ⟨u, hu1, hueval, huiff⟩ :=
      ih (fun d hd => harr d (List.mem_cons_of_mem _ hd))
        (fun d hd => hbnd d (List.mem_cons_of_mem _ hd))
    have hcell : ∀ s : String, σ.vars s < n →
        (Expr.get (colName j c) (.var s)).evalB B σ = some (C c (σ.vars s)) := by
      intro s hs
      refine evalB_get (evalB_var (by omega)) ?_ (hbnd c List.mem_cons_self _ hs)
      rw [harr c List.mem_cons_self]
      exact getElem?_arrOf _ hs
    obtain ⟨w, hw1, hweval, hwiff⟩ :=
      evalB_eqBitExpr hB (hbnd c List.mem_cons_self _ hx) (hbnd c List.mem_cons_self _ hy)
        (hcell x hx) (hcell y hy)
    refine ⟨w * u, by nlinarith, ?_, ?_⟩
    · refine evalB_bin hweval hueval ?_
      simp only [Bop.apply_mul]
      calc w * u ≤ 1 * 1 := Nat.mul_le_mul hw1 hu1
        _ < B := by omega
    · rw [List.forall_mem_cons, ← hwiff, ← huiff]
      constructor
      · intro h
        exact ⟨fun hc => h (by rw [hc, Nat.zero_mul]), fun hc => h (by rw [hc, Nat.mul_zero])⟩
      · rintro ⟨h1, h2⟩
        exact Nat.mul_ne_zero h1 h2

/-- **Two vertices carry the same colours** exactly when the depth's
row-equality expression is nonzero. -/
theorem evalB_rowEqExpr {B n j L : ℕ} {σ : Env} {x y : String} {C : ℕ → ℕ → ℕ} (hB : 1 < B)
    (hx : σ.vars x < n) (hy : σ.vars y < n) (hn : n < B)
    (harr : ∀ c < L, σ.arrs (colName j c) = arrOf n (C c))
    (hbnd : ∀ c < L, ∀ v < n, C c v < B) :
    ∃ u ≤ 1, (rowEqExpr j L x y).evalB B σ = some u ∧
      (u ≠ 0 ↔ ∀ c < L, C c (σ.vars x) = C c (σ.vars y)) := by
  obtain ⟨u, hu1, hueval, huiff⟩ :=
    evalB_rowFold (j := j) (C := C) hB hx hy hn (List.range L)
      (fun c hc => harr c (List.mem_range.mp hc)) (fun c hc => hbnd c (List.mem_range.mp hc))
  exact ⟨u, hu1, hueval, by rw [huiff]; simp [List.mem_range]⟩

end Lax3Proofs.RamDriverBase
