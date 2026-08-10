import Lax3Proofs.RamCover
import Lax13Proofs.Reasoning
import Lax13Proofs.Spec

/-!
# Driver-independent vocabulary used by the block engines

The block-scale engines must sit above the driver files they are meant
to discharge.  This module holds the small pieces of the driver's
surface that are independent of the driver itself: its size readings,
the compacted-centre contract, the mathematical value of one expansion,
and the generic prefix-copy walk used by the cover leaf.

The declarations keep their original namespaces and names.  Moving them
here changes only the import order; existing consumers continue to refer
to the same API.
-/

namespace Lax3Proofs.RamDriver

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-- The block members of the cluster arena of depth `j`: the level's copy
of the cover's `xmem`. -/
def xmmName (j : ℕ) : String := "xm" ++ toString j

/-- **The size of an arena**: how many of the carrier's vertices the
mask leaves alive. This is the size a level's cost is read at. -/
noncomputable def arenaSize (n : ℕ) (M : ℕ → ℕ) : ℕ :=
  {v : Fin n | M (v : ℕ) ≠ 0}.ncard

/-- **What the compaction scan leaves.** `cps` lists, in strictly
increasing order, exactly the `cnum` positions below `n` whose block is
nonempty **and whose centre the mask leaves alive**.

The emptiness predicate alone filters nothing —
`Refine.MassAlive.block_nonempty` — so the `alive` clause is the one the
Σ interface needs: `Refine.ArenaBlock.mass_of_alive_compaction` turns
it, with the cover's postcondition, into the whole cost supply of a
level. The scan that establishes the contract is `RamDriver.compactCom`. -/
structure Compacted (n cnum m : ℕ) (M ord Xoff cps : ℕ → ℕ) : Prop where
  /-- One turn per member of the cluster arena at most. -/
  le_mass : cnum ≤ m
  /-- And never more turns than there are positions. -/
  le_carrier : cnum ≤ n
  /-- Every listed position is a position. -/
  lt : ∀ k < cnum, cps k < n
  /-- The list is strictly increasing. -/
  mono : ∀ k k' : ℕ, k < k' → k' < cnum → cps k < cps k'
  /-- Every listed position has a nonempty block. -/
  nonempty : ∀ k < cnum, Xoff (cps k) < Xoff (cps k + 1)
  /-- Every listed centre is alive. This lets
  `Refine.ArenaBlock.cnum_le_arenaSize` count turns against the arena. -/
  alive : ∀ k < cnum, M (ord (cps k)) ≠ 0
  /-- Every nonempty block with a live centre is listed. A dead centre is
  deliberately omitted: its cluster is its singleton and the level's
  edgeless sweep has already written its row. -/
  covers : ∀ c < n, Xoff c < Xoff (c + 1) → M (ord c) ≠ 0 → ∃ k < cnum, cps k = c

/-- The compacted list has no repetitions, so its loop turns are distinct. -/
theorem Compacted.inj {n cnum m : ℕ} {M ord Xoff cps : ℕ → ℕ}
    (h : Compacted n cnum m M ord Xoff cps) {k k' : ℕ} (hk : k < cnum) (hk' : k' < cnum)
    (he : cps k = cps k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd he (Nat.ne_of_lt (h.mono k k' hlt hk'))
  · exact heq
  · exact absurd he.symm (Nat.ne_of_lt (h.mono k' k hgt hk))

/-- A flat pass over the first `bnd` cells of an array, writing the value
of `e` into each. -/
def fillUpto (a : String) (bnd e : Expr) : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") bnd) (Fill.put a "i" e))

/-- Copy the first `bnd` cells of one array into another. -/
def copyUpto (src dst : String) (bnd : Expr) : Com :=
  fillUpto dst bnd (.get src (.var "i"))

end Lax3Proofs.RamDriver

namespace Lax3Proofs.RamDriverCluster

open Lax3Proofs.RamBfs (CsrGraph MAdj masked)
open Lax13Proofs.Reasoning (arrOf)

/-- The set marked by a mask array. -/
def markSet (n : ℕ) (A : ℕ → ℕ) : Set (Fin n) := {v | A (v : ℕ) ≠ 0}

open Classical in
/-- **The cell one expansion step writes.** The source's own cell,
raised to one when some live neighbour of the vertex is marked. This is
what `RamDriver.expandStep` computes; its initial `hit := src[z]` is why
a marked vertex stays marked. -/
noncomputable def expandVal {n : ℕ} (G : SimpleGraph (Fin n)) (Msk Src : ℕ → ℕ) (z : ℕ) : ℕ :=
  if ∃ y : ℕ, MAdj G Msk z y ∧ Src y ≠ 0 then 1 else Src z

open Classical in
/-- **What a full block scan leaves.** The slots of the block name
exactly the neighbours of the vertex, so a complete CSR row scan
computes `expandVal`. -/
theorem hit_eq_expandVal {n ns z : ℕ} {G : SimpleGraph (Fin n)}
    {O T Msk Src : ℕ → ℕ} (hcsr : CsrGraph G ns O T) (hzn : z < n)
    (hmz : Msk z ≠ 0) :
    (if ∃ p, O z ≤ p ∧ p < O (z + 1) ∧ Msk (T p) ≠ 0 ∧ Src (T p) ≠ 0
      then 1 else Src z) = expandVal G Msk Src z := by
  classical
  unfold expandVal
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨p, h₁, h₂, hm, hs⟩
    exact ⟨T p, hcsr.madj_of_slot hzn h₁ h₂ hmz hm, hs⟩
  · rintro ⟨y, hy, hs⟩
    obtain ⟨p, h₁, h₂, rfl⟩ := hcsr.slot_of_madj hy
    exact ⟨p, h₁, h₂, hy.alive_right, hs⟩

end Lax3Proofs.RamDriverCluster

namespace Lax3Proofs.RamDriverDescend

open Lax3Proofs.RamBfs (MAdj)
open Lax3Proofs.RamDriverCluster (expandVal)

/-- **A dead vertex is not expanded into.** The step's conditional is
skipped there and the source's own cell stands: an arena edge needs both
of its ends alive. -/
theorem expandVal_of_dead {n : ℕ} {G : SimpleGraph (Fin n)} {Msk Src : ℕ → ℕ}
    {z : ℕ} (h : Msk z = 0) : expandVal G Msk Src z = Src z := by
  classical
  unfold expandVal
  rw [if_neg]
  rintro ⟨y, hy, -⟩
  exact hy.alive_left h

end Lax3Proofs.RamDriverDescend

namespace Lax3Proofs.RamDriverOrder

open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- **A counted scan from zero whose bound is an arbitrary expression.** -/
theorem forRangeZero' {B : ℕ} {c : Com} (x : String) (bnd : Expr) (I : Env → Prop)
    (N Kb : ℕ) (hB : 0 < B) (hxB : ∀ σ, I σ → σ.vars x < B)
    (hbnd : ∀ σ, I σ → bnd.evalB B σ = some N) (hxN : ∀ σ, I σ → σ.vars x ≤ N)
    (hbody : Spec B (fun σ => I σ ∧ σ.vars x < N) c
      (fun σ σ' => I σ' ∧ σ'.vars x = σ.vars x + 1) Kb) :
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) bnd) c))
      (fun _ σ' => I σ' ∧ σ'.vars x = N) ((Kb + bnd.size + 3) * N + bnd.size + 5) := by
  have hsize : (Cond.lt (Expr.var x) bnd).size = bnd.size + 2 := by
    simp only [Cond.size, size_var]; omega
  have hloop : Spec B I (.while (.lt (.var x) bnd) c)
      (fun _ σ' => I σ' ∧ (Cond.lt (Expr.var x) bnd).evalB B σ' = some false)
      ((Kb + bnd.size + 3) * N + bnd.size + 3) := by
    refine Spec.while_potential I (fun σ => (Kb + bnd.size + 3) * (N - σ.vars x))
      (fun σ hI => ⟨_, evalB_condLt (evalB_var (hxB σ hI)) (hbnd σ hI)⟩) ?_
      (fun _ h => h) ?_
    · intro σ hI hv
      have hlt : σ.vars x < N := by
        rw [evalB_condLt (evalB_var (hxB σ hI)) (hbnd σ hI)] at hv
        simpa using hv
      obtain ⟨σ', hr, hI', hx'⟩ := hbody σ ⟨hI, hlt⟩
      refine ⟨σ', Kb, hr, hI', ?_⟩
      show 1 + (Cond.lt (Expr.var x) bnd).size + Kb +
          (Kb + bnd.size + 3) * (N - σ'.vars x) ≤
        (Kb + bnd.size + 3) * (N - σ.vars x)
      rw [hsize]
      have hdrop : N - σ'.vars x + 1 = N - σ.vars x := by rw [hx']; omega
      refine le_of_eq ?_
      rw [← hdrop]
      ring
    · intro σ hI
      show (Kb + bnd.size + 3) * (N - σ.vars x) + 1 +
          (Cond.lt (Expr.var x) bnd).size ≤
        (Kb + bnd.size + 3) * N + bnd.size + 3
      rw [hsize]
      have : (Kb + bnd.size + 3) * (N - σ.vars x) ≤
          (Kb + bnd.size + 3) * N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ', hr, hI', hfalse⟩ := hloop.run (σ := σ.setVar x 0) hσ
  refine ⟨σ', _, Run.seq (Run.assign (v := 0) (evalB_lit hB)) hr, ?_, hI', ?_⟩
  · simp only [size_lit]; omega
  · rw [evalB_condLt (evalB_var (hxB σ' hI')) (hbnd σ' hI')] at hfalse
    have := hxN σ' hI'
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega

end Lax3Proofs.RamDriverOrder

namespace Lax3Proofs.RamDriverCompose

open Lax3Proofs.RamDriver (copyUpto fillUpto xmmName)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-- A decimal representation has at least one digit. -/
theorem toDigits_ne_nil (j : ℕ) : Nat.toDigits 10 j ≠ [] := by
  rw [Nat.toDigits_eq_if (by omega)]
  split <;> simp

@[local simp]
theorem toString_toList_ne_nil (j : ℕ) : (toString j).toList ≠ [] := by
  have h0 := toDigits_ne_nil j
  rw [Nat.toString_eq_repr, Nat.repr_eq_ofList_toDigits]
  simpa using h0

/-- Appending a decimal numeral changes a string. -/
theorem append_toString_ne (p : String) (j : ℕ) : p ++ toString j ≠ p := by
  intro h
  have hl := congrArg (fun s : String => s.toList.length) h
  simp only [String.toList_append, List.length_append] at hl
  have hz : (toString j).toList.length = 0 := by omega
  exact toString_toList_ne_nil j (List.eq_nil_of_length_eq_zero hz)

/-- A decimal representation contains only digits. -/
theorem notMem_toDigits {c : Char} (hc : ∀ d < 10, Nat.digitChar d ≠ c) :
    ∀ j : ℕ, c ∉ Nat.toDigits 10 j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · rename_i hlt
      simp only [List.mem_singleton]
      exact fun h => hc _ hlt h.symm
    · rename_i hge
      have hpos : 0 < j := by omega
      simp only [List.mem_append, not_or]
      refine ⟨ih (j / 10) (Nat.div_lt_self hpos (by omega)), ?_⟩
      simp only [List.mem_singleton]
      exact fun h => hc _ (Nat.mod_lt _ (by omega)) h.symm

/-- A decimal numeral, as a list of characters. -/
theorem toList_toString (j : ℕ) : (toString j).toList = Nat.toDigits 10 j := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_ofList_toDigits]
  simp

/-- **The member array of the cover is not the depth's copy of it.**
Both begin `xm`; what follows is `em` in the one and a decimal numeral
in the other. -/
theorem xmem_ne_xmmName (j : ℕ) : "xmem" ≠ xmmName j := by
  intro h
  rw [xmmName, String.ext_iff] at h
  have h' : Nat.toDigits 10 j = ['e', 'm'] := by
    rw [← toList_toString]
    exact (by simpa using h : ['e', 'm'] = (toString j).toList).symm
  exact notMem_toDigits (c := 'e') (by decide) j (by rw [h']; simp)

/-- **A flat pass over a prefix of an array**, whose allocation may be
longer than the bound. -/
theorem fillPrefix_spec {B : ℕ} (N Na : ℕ) (a : String) (bnd e : Expr)
    (F : ℕ → ℕ) (Q : Env → Prop) (hB : 0 < B) (hNB : N < B) (hNa : N ≤ Na)
    (hQfr : ∀ σ σ', Q σ → (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ a → σ'.arrs b = σ.arrs b) → Q σ')
    (hbnd : ∀ σ, Q σ → bnd.evalB B σ = some N)
    (he : ∀ σ, Q σ → σ.vars "i" < N → e.evalB B σ = some (F (σ.vars "i"))) :
    Spec B (fun σ => (∃ g, σ.arrs a = arrOf Na g) ∧ Q σ)
      (fillUpto a bnd e)
      (fun _ σ' => (∃ g, σ'.arrs a = arrOf Na g ∧ ∀ k < N, g k = F k) ∧
        σ'.vars "i" = N ∧ Q σ')
      ((e.size + bnd.size + 9) * N + bnd.size + 5) := by
  have hbody : Spec B
      (fun σ => ((∃ g, σ.arrs a = arrOf Na g ∧ ∀ k < σ.vars "i", g k = F k) ∧
        σ.vars "i" ≤ N ∧ Q σ) ∧ σ.vars "i" < N)
      (Fill.put a "i" e)
      (fun σ σ' => ((∃ g, σ'.arrs a = arrOf Na g ∧ ∀ k < σ'.vars "i", g k = F k) ∧
        σ'.vars "i" ≤ N ∧ Q σ') ∧ σ'.vars "i" = σ.vars "i" + 1) (6 + e.size) := by
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨⟨g, harr, hcell⟩, hle, hQ⟩, hlt⟩ := hσ
    have hval := he σ hQ hlt
    have h1 : Run B (.store a (.var "i") e) σ
        (σ.setArr a (σ.vars "i") (F (σ.vars "i"))) (1 + 1 + e.size) := by
      have h := Run.store (B := B) (σ := σ) (a := a) (i := .var "i") (e := e)
        (evalB_var (by omega)) hval (by rw [harr, length_arrOf]; omega)
      simpa using h
    have h2 : Run B (.assign "i" (.add (.var "i") (.lit 1)))
        (σ.setArr a (σ.vars "i") (F (σ.vars "i")))
        ((σ.setArr a (σ.vars "i") (F (σ.vars "i"))).setVar "i" (σ.vars "i" + 1))
        (1 + 3) := by
      have h := Run.assign (B := B) (σ := σ.setArr a (σ.vars "i") (F (σ.vars "i")))
        (x := "i") (e := .add (.var "i") (.lit 1))
        (evalB_bin (evalB_var (by rw [vars_setArr]; omega)) (evalB_lit (by omega))
          (by simp only [Bop.apply_add, vars_setArr]; omega))
      rw [Bop.apply_add, vars_setArr] at h
      simpa using h
    refine ⟨_, _, h1.seq h2, by omega,
      ⟨⟨upd g (σ.vars "i") (F (σ.vars "i")), ?_, ?_⟩,
        by rw [vars_setVar, if_pos rfl]; omega, ?_⟩, by simp⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, harr, set_arrOf_eq_upd]
    · intro k hk
      rw [vars_setVar, if_pos rfl] at hk
      rcases Nat.lt_or_ge k (σ.vars "i") with hklt | hkge
      · rw [upd_of_ne _ (by omega)]; exact hcell k hklt
      · have : k = σ.vars "i" := by omega
        rw [this, upd_self]
    · exact hQfr σ _ hQ (fun y hy => by rw [vars_setVar, if_neg hy, vars_setArr])
        (fun b hb => by rw [arrs_setVar, arrs_setArr, if_neg hb])
  refine (((Lax3Proofs.RamDriverOrder.forRangeZero' "i" bnd
    (fun σ => (∃ g, σ.arrs a = arrOf Na g ∧ ∀ k < σ.vars "i", g k = F k) ∧
      σ.vars "i" ≤ N ∧ Q σ) N (6 + e.size) hB
    (fun _ hσ => lt_of_le_of_lt hσ.2.1 hNB) (fun _ hσ => hbnd _ hσ.2.2)
    (fun _ hσ => hσ.2.1) hbody).pre ?_).post ?_).mono (le_of_eq (by ring))
  · rintro σ ⟨⟨g, harr⟩, hQ⟩
    refine ⟨⟨g, by rw [arrs_setVar]; exact harr, ?_⟩, by simp, ?_⟩
    · intro k hk; rw [vars_setVar, if_pos rfl] at hk; omega
    · exact hQfr σ _ hQ (fun y hy => by rw [vars_setVar, if_neg hy])
        (fun _ _ => by rw [arrs_setVar])
  · rintro σ σ' - ⟨⟨⟨g, harr, hcell⟩, -, hQ⟩, hiN⟩
    exact ⟨⟨g, harr, fun k hk => hcell k (by rw [hiN]; exact hk)⟩, hiN, hQ⟩

/-- **A copy into a prefix of a longer array.** -/
theorem copyPrefix_spec {B : ℕ} (N Na Ns : ℕ) (src dst : String) (bnd : Expr)
    (g : ℕ → ℕ) (Q : Env → Prop) (hB : 0 < B) (hNB : N < B) (hNa : N ≤ Na)
    (hNs : N ≤ Ns)
    (hQfr : ∀ σ σ', Q σ → (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ dst → σ'.arrs b = σ.arrs b) → Q σ')
    (hbnd : ∀ σ, Q σ → bnd.evalB B σ = some N)
    (hsrc : ∀ σ, Q σ → σ.arrs src = arrOf Ns g) (hgB : ∀ k < N, g k < B) :
    Spec B (fun σ => (∃ h, σ.arrs dst = arrOf Na h) ∧ Q σ)
      (copyUpto src dst bnd)
      (fun _ σ' => (∃ h, σ'.arrs dst = arrOf Na h ∧ ∀ k < N, h k = g k) ∧
        σ'.vars "i" = N ∧ Q σ')
      ((bnd.size + 11) * N + bnd.size + 5) :=
  (fillPrefix_spec N Na dst bnd (.get src (.var "i")) g Q hB hNB hNa hQfr hbnd
    (fun σ hQ hlt => evalB_get (evalB_var (by omega))
      (by rw [hsrc σ hQ, getElem?_arrOf g (by omega)]) (hgB _ hlt))).mono
    (le_of_eq (by simp only [size_get, size_var]; ring))

/-- The cost of the cover phase: the pass, the two copies that set it
up, the four of `RamDriver.coverSave` — the member copy charged at the
whole cluster arena — and the compaction scan. -/
def coverPhaseCost (n ns : ℕ) : ℕ :=
  Lax3Proofs.RamCover.coverCost n ns + 12 * (n * n) + 81 * n + 56

end Lax3Proofs.RamDriverCompose
