import Lax185574Proofs.TreeCanon
import Lax185574Proofs.TreeAlgo.Restriction
import Lax185574.Restriction
import Lax185574Proofs.Interface.Poly

/-!
The restriction of a type tree to a list of positions, on the word RAM.

The program is the one-pass transformation `jobProg` of
`Lax185574Proofs.Words.TreeJobs` with three hooks, followed by restoring
canonical form (`Lax185574Proofs.TreeCanon.treeCanon`). The arguments, the list
`J`, are read into a table: entry `24 + i` of `gt` is `j + 1` if `J`
names position `i` at place `j`, and `0` if it does not name `i`. The
first 24 entries of `gt` mark the entries of atom codes that are
positions. A position `v` at depth `d` is renamed to its place in `J`, or
the atom is dropped, if `v` is a position of the tuple (`v < ℓ`), and to
`v - ℓ + |J|` if it is one of the `d` new positions. Guards are renamed in
the same way, and an extension whose guard is dropped is dropped. Atom
codes of formulas that are not atoms (tags `6`, `7`, `8`) are dropped,
as in the semantic core `Lax185574Proofs.TreeAlgo.restrictNode`.
-/

namespace Lax185574Proofs.RestrictionRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-! ### The tables -/

/-- Entry `4 tag + k` is `1` if entry `k` of an atom code with this tag
is a position. -/
def posTab (c : ℕ) : ℕ :=
  if c = 1 ∨ c = 2 ∨ c = 5 ∨ c = 6 ∨ c = 9 ∨ c = 10 ∨ c = 14 ∨ c = 18 ∨ c = 19 ∨ c = 23 then 1 else 0

/-- Entry `k` of an atom code with tag `tg` is a position. -/
def IsPos (tg k : ℕ) : Prop := tg < 6 ∧ k < 4 ∧ posTab (tg * 4 + k) = 1

instance (tg k : ℕ) : Decidable (IsPos tg k) := by unfold IsPos; infer_instance

/-- The place of position `i` in `J`, plus one, and `0` if `J` does not
name `i`. -/
def jIdx {ℓ : ℕ} (J : List (Fin ℓ)) (i : ℕ) : ℕ :=
  if h : i < ℓ then ((listPInv J ⟨i, h⟩).map fun j => j.val + 1).getD 0 else 0

/-- The renaming of positions. -/
def gmap {ℓ : ℕ} (J : List (Fin ℓ)) (v : ℕ) : Option ℕ :=
  if v < ℓ then (if jIdx J v = 0 then none else some (jIdx J v - 1)) else some (v - ℓ + J.length)

/-- The map of the entries of atom codes. -/
def rsub {ℓ : ℕ} (J : List (Fin ℓ)) (tg k _d v : ℕ) : Option ℕ :=
  if k = 0 ∧ 5 < tg then none else if IsPos tg k then gmap J v else some v

/-- The map of the guards. -/
def rgsub {ℓ : ℕ} (J : List (Fin ℓ)) (_d i : ℕ) : Option ℕ := gmap J i

/-! ### The renaming at depth `d` -/

/-- The partial inverse at depth `d`: the positions of the tuple are
renamed along `J`, the `d` new positions are kept last. -/
def gD {ℓ : ℕ} (J : List (Fin ℓ)) : (d : ℕ) → Fin (ℓ + d) → Option (Fin (J.length + d))
  | 0 => listPInv J
  | d + 1 => liftPInv (gD J d)

theorem gD_val {ℓ : ℕ} (J : List (Fin ℓ)) : ∀ (d : ℕ) (i : Fin (ℓ + d)),
    (gD J d i).map Fin.val = gmap J i.val
  | 0, i => by
    have hi : i.val < ℓ := i.isLt
    simp only [gD, gmap, jIdx, dif_pos hi, if_pos hi]
    cases h : listPInv J i with
    | none => simp [h]
    | some j => simp [h]
  | d + 1, i => by
    show (liftPInv (gD J d) i).map Fin.val = _
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp only [liftPInv, Fin.lastCases_last, Option.map_some, Fin.val_last, gmap]
      have e : ¬ (ℓ + d < ℓ) := by omega
      simp only [Nat.add_eq] at e ⊢
      rw [if_neg e]
      erw [Fin.lastCases_last]
      simp only [Option.map_some, Fin.val_last, Option.some.injEq]
      omega
    · simp only [liftPInv, Fin.lastCases_castSucc, Option.map_map, Fin.val_castSucc]
      have := gD_val J d i'
      rw [← this]; rfl

theorem atomMap_code {ℓ : ℕ} (J : List (Fin ℓ)) (d : ℕ) (φ : DistFO (ℓ + d)) :
    atomMap (rsub J) d (toWord φ) = (pullAtom (gD J d) φ).map toWord := by
  cases φ with
  | eq i j =>
    simp only [toWord_atom, code, atomMap, atomMapAux, rsub, IsPos, posTab, pullAtom, ← gD_val J d]
    cases gD J d i <;> cases gD J d j <;> simp [toWord_atom, code]
  | edge i j =>
    simp only [toWord_atom, code, atomMap, atomMapAux, rsub, IsPos, posTab, pullAtom, ← gD_val J d]
    cases gD J d i <;> cases gD J d j <;> simp [toWord_atom, code]
  | nonEdge i j =>
    simp only [toWord_atom, code, atomMap, atomMapAux, rsub, IsPos, posTab, pullAtom, ← gD_val J d]
    cases gD J d i <;> cases gD J d j <;> simp [toWord_atom, code]
  | color Y i =>
    simp only [toWord_atom, code, atomMap, atomMapAux, rsub, IsPos, posTab, pullAtom, ← gD_val J d]
    cases gD J d i <;> simp [toWord_atom, code]
  | distLe r i j =>
    simp only [toWord_atom, code, atomMap, atomMapAux, rsub, IsPos, posTab, pullAtom, ← gD_val J d]
    cases gD J d i <;> cases gD J d j <;> simp [toWord_atom, code]
  | distColorLt r Y i =>
    simp only [toWord_atom, code, atomMap, atomMapAux, rsub, IsPos, posTab, pullAtom, ← gD_val J d]
    cases gD J d i <;> simp [toWord_atom, code]
  | not φ => simp [toWord_atom, code, atomMap, atomMapAux, rsub, pullAtom]
  | and φ ψ => simp [toWord_atom, code, atomMap, atomMapAux, rsub, pullAtom]
  | exLocal i s φ => simp [toWord_atom, code, atomMap, atomMapAux, rsub, pullAtom]

/-- **The program computes the core.** The transformation with the
renaming hooks is the restriction `restrictNode` along `gD J d`. -/
theorem treeOut_restrict {ℓ : ℕ} (J : List (Fin ℓ)) (X : List ℕ) :
    ∀ (h d : ℕ) (t : Node h (ℓ + d)) (p : ℕ) (r : List ℕ), X.drop p = toWord t ++ r →
      treeOut (rsub J) (rgsub J) h d X p = toWord (restrictNode (gD J d) t)
  | 0, d, t, p, r, hx => by
    rw [treeOut_zero, toWord_node_zero, atoms_restrictNode, pullAtoms]
    rw [toWord_node_zero] at hx
    rw [sortedDistinct_atomCands hx (pullAtom (gD J d)) (fun φ _ => atomMap_code J d φ)]
  | h + 1, d, t, p, r, hx => by
    obtain ⟨h1, h2⟩ := nodeSplit hx
    rw [treeOut_succ, toWord_node_succ, atoms_restrictNode, pullAtoms]
    rw [sortedDistinct_atomCands h1 (pullAtom (gD J d)) (fun φ _ => atomMap_code J d φ)]
    congr 1
    rw [sortedDistinct_extCands h2 (gD J d) (restrictNode (liftPInv (gD J d)))
      (fun i => (gD_val J d i).symm)
      (fun ε _ P r' hP => treeOut_restrict J X h (d + 1) ε.2 P r' hP)]
    rfl

/-! ### The hooks -/

/-- The data of the hooks: `g1 = ℓ`, `g2 = |J|`, and the tables in `gt`. -/
def RDat {ℓ : ℕ} (J : List (Fin ℓ)) (B : ℕ) (τ : Env) : Prop :=
  τ.vars "g1" = ℓ ∧ τ.vars "g2" = J.length ∧ J.length ≤ ℓ ∧ (τ.arrs "gt").length = ℓ + 24 ∧
    (∀ c < 24, (τ.arrs "gt").getD c 0 = posTab c) ∧
    (∀ i < ℓ, (τ.arrs "gt").getD (24 + i) 0 = jIdx J i) ∧ ℓ + 25 < B

theorem rdat_ok {ℓ : ℕ} (J : List (Fin ℓ)) (B : ℕ) : DatOK (RDat J B) := by
  intro τ τ' h1 h2 _ _ h5 ⟨d1, d2, d3, d4, d5, d6, d7⟩
  exact ⟨by rw [h1, d1], by rw [h2, d2], d3, by rw [h5, d4], by rw [h5]; exact d5, by rw [h5]; exact d6, d7⟩

/-- The first block of the entry hook: drop the code of a formula that is
not an atom. -/
def subA : Com :=
  .seq (.assign "nv" (.var "ev")) (.seq (.assign "drp" (.lit 0))
    (.ite (.eq (.var "kk") (.lit 0))
      (.ite (.lt (.lit 5) (.var "tg")) (.seq (.assign "drp" (.lit 1)) (.assign "nv" (.lit 0))) .skip)
      .skip))

/-- The second block: look up whether the entry is a position. -/
def subB : Com :=
  .seq (.assign "s1" (.lit 0))
    (.ite (.lt (.var "tg") (.lit 6))
      (.ite (.lt (.var "kk") (.lit 4))
        (.assign "s1" (.get "gt" (.add (.mul (.var "tg") (.lit 4)) (.var "kk")))) .skip) .skip)

/-- The third block: rename a position. -/
def subC : Com :=
  .ite (.eq (.var "s1") (.lit 1))
    (.ite (.lt (.var "ev") (.var "g1"))
      (.seq (.assign "s2" (.get "gt" (.add (.lit 24) (.var "ev"))))
        (.ite (.eq (.var "s2") (.lit 0)) (.seq (.assign "drp" (.lit 1)) (.assign "nv" (.lit 0)))
          (.assign "nv" (.sub (.var "s2") (.lit 1)))))
      (.assign "nv" (.add (.sub (.var "ev") (.var "g1")) (.var "g2"))))
    .skip

/-- The hook for the entries of atom codes. -/
def subCmd : Com := .seq subA (.seq subB subC)

theorem subA_spec (B : ℕ) (h2 : 6 < B) :
    Spec B (fun τ => τ.vars "ev" < B ∧ τ.vars "tg" < B ∧ τ.vars "kk" < B) subA
      (fun τ τ' => (∀ y, y ≠ "nv" → y ≠ "drp" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧
        (τ.vars "kk" = 0 ∧ 5 < τ.vars "tg" → τ'.vars "drp" = 1 ∧ τ'.vars "nv" = 0) ∧
        (¬ (τ.vars "kk" = 0 ∧ 5 < τ.vars "tg") → τ'.vars "drp" = 0 ∧ τ'.vars "nv" = τ.vars "ev")) 20 := by
  unfold subA
  run_vcg
  all_goals (refine ⟨fun y h1 h2 => by simp [h1, h2], rfl, ?_, ?_⟩ <;> simp_all)

theorem posTab_le (c : ℕ) : posTab c ≤ 1 := by unfold posTab; split_ifs <;> omega

theorem subB_spec (B : ℕ) (h2 : 25 < B) :
    Spec B (fun τ => τ.vars "tg" < B ∧ τ.vars "kk" < B ∧ 24 ≤ (τ.arrs "gt").length ∧
        ∀ c < 24, (τ.arrs "gt").getD c 0 = posTab c) subB
      (fun τ τ' => (∀ y, y ≠ "s1" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧
        τ'.vars "s1" = (if τ.vars "tg" < 6 ∧ τ.vars "kk" < 4 then
          posTab (τ.vars "tg" * 4 + τ.vars "kk") else 0)) 20 := by
  rintro τ ⟨htg, hkk, hgl, hgt⟩
  unfold subB
  by_cases h1 : τ.vars "tg" < 6
  · by_cases h3 : τ.vars "kk" < 4
    · have hv := hgt (τ.vars "tg" * 4 + τ.vars "kk") (by omega)
      have := posTab_le (τ.vars "tg" * 4 + τ.vars "kk")
      refine ⟨(τ.setVar "s1" 0).setVar "s1" (posTab (τ.vars "tg" * 4 + τ.vars "kk")),
        (Run.seq (Run.assign ?_) (Run.ite_true ?_ (Run.ite_true ?_ (Run.assign ?_)))).mono (by simp),
        fun y hy => by simp [hy], rfl, by simp [h1, h3]⟩
      · simp; omega
      · simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨τ.vars "tg", 6, ⟨by simp, by simp; omega⟩, ⟨rfl, by omega⟩, by simp [h1]⟩
      · simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨τ.vars "kk", 4, ⟨by simp, by simp; omega⟩, ⟨rfl, by omega⟩, by simp [h3]⟩
      · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, vars_setVar, arrs_setVar]
        refine ⟨τ.vars "tg" * 4 + τ.vars "kk", ⟨τ.vars "tg" * 4, τ.vars "kk",
          ⟨τ.vars "tg", 4, ⟨?_, ?_⟩, ⟨rfl, by omega⟩, rfl, ?_⟩,
          ⟨?_, ?_⟩, rfl, ?_⟩, ?_, by omega⟩
        all_goals try ((try simp) <;> omega)
        rw [← hv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    · refine ⟨τ.setVar "s1" 0, (Run.seq (Run.assign ?_) (Run.ite_true ?_ (Run.ite_false ?_ Run.skip))).mono
        (by simp), fun y hy => by simp [hy], rfl, by simp [h3]⟩
      · simp; omega
      · simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨τ.vars "tg", 6, ⟨by simp, by simp; omega⟩, ⟨rfl, by omega⟩, by simp [h1]⟩
      · simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨τ.vars "kk", 4, ⟨by simp, by simp; omega⟩, ⟨rfl, by omega⟩, by simp [h3]⟩
  · refine ⟨τ.setVar "s1" 0, (Run.seq (Run.assign ?_) (Run.ite_false ?_ Run.skip)).mono
      (by simp), fun y hy => by simp [hy], rfl, by simp [h1]⟩
    · simp; omega
    · simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨τ.vars "tg", 6, ⟨by simp, by simp; omega⟩, ⟨rfl, by omega⟩, by simp [h1]⟩

theorem jIdx_le {ℓ : ℕ} (J : List (Fin ℓ)) (i : ℕ) : jIdx J i ≤ J.length := by
  unfold jIdx
  split_ifs with h
  · cases listPInv J ⟨i, h⟩ with
    | none => simp
    | some j => simp
  · omega

theorem subC_spec {ℓ : ℕ} (J : List (Fin ℓ)) (B : ℕ) :
    Spec B (fun τ => RDat J B τ ∧ τ.vars "ev" < B ∧ τ.vars "s1" ≤ 1 ∧ τ.vars "nv" < B ∧
        τ.vars "drp" ≤ 1) subC
      (fun τ τ' => (∀ y, y ≠ "nv" → y ≠ "drp" → y ≠ "s2" → τ'.vars y = τ.vars y) ∧
        τ'.arrs = τ.arrs ∧
        τ'.vars "nv" = (if τ.vars "s1" = 1 then (gmap J (τ.vars "ev")).getD 0 else τ.vars "nv") ∧
        τ'.vars "drp" = (if τ.vars "s1" = 1 ∧ gmap J (τ.vars "ev") = none then 1 else τ.vars "drp"))
      30 := by
  rintro τ ⟨⟨hg1, hg2, hJl, hgl, -, hgt, hB⟩, hev, hs1, hnv, hdrp⟩
  have hjl := jIdx_le J (τ.vars "ev")
  have hgt' : τ.vars "ev" < ℓ → (τ.arrs "gt").getD (24 + τ.vars "ev") 0 = jIdx J (τ.vars "ev") :=
    fun h => hgt _ h
  unfold subC
  run_vcg
  all_goals first
    | (refine ⟨fun y a b c => by simp [a, b, c], rfl, ?_, ?_⟩)
    | skip
  all_goals (try simp only [vars_setVar, if_true, arrs_setVar, show ("s2" : String) = "nv" ↔ False by decide,
    show ("s2" : String) = "drp" ↔ False by decide, show ("nv" : String) = "drp" ↔ False by decide,
    show ("drp" : String) = "nv" ↔ False by decide, if_false])
  all_goals (simp_all [gmap] <;> (try split_ifs) <;> (try simp_all) <;> omega)

theorem gmap_lt {ℓ : ℕ} (J : List (Fin ℓ)) (hJ : J.length ≤ ℓ) {B v r : ℕ} (hv : v < B)
    (hℓ : ℓ < B) (h : gmap J v = some r) : r < B := by
  unfold gmap at h
  have := jIdx_le J v
  split_ifs at h with h1 h2 <;> simp at h <;> omega

theorem subCmd_ok {ℓ : ℕ} (J : List (Fin ℓ)) (B : ℕ) : SubOK subCmd (rsub J) (RDat J B) B 70 := by
  rintro τ ⟨hdat, htg, hkk, hdd, hev⟩
  have hdat' := hdat
  obtain ⟨hg1, hg2, hJl, hgl, hpt, hgt, hB⟩ := hdat'
  obtain ⟨τ1, hr1, hv1, ha1, hA1, hA2⟩ := subA_spec B (by omega) τ ⟨hev, htg, hkk⟩
  obtain ⟨τ2, hr2, hv2, ha2, hs1⟩ := subB_spec B (by omega) τ1
    ⟨by rw [hv1 "tg" (by decide) (by decide)]; exact htg, by rw [hv1 "kk" (by decide) (by decide)]; exact hkk,
      by rw [ha1]; omega, by rw [ha1]; exact hpt⟩
  rw [hv1 "tg" (by decide) (by decide), hv1 "kk" (by decide) (by decide)] at hs1
  have hdat2 : RDat J B τ2 := (rdat_ok J B) τ τ2
    (by rw [hv2 "g1" (by decide), hv1 "g1" (by decide) (by decide)])
    (by rw [hv2 "g2" (by decide), hv1 "g2" (by decide) (by decide)])
    (by rw [hv2 "g3" (by decide), hv1 "g3" (by decide) (by decide)])
    (by rw [hv2 "g4" (by decide), hv1 "g4" (by decide) (by decide)]) (by rw [ha2, ha1]) hdat
  have hs1le : τ2.vars "s1" ≤ 1 := by
    rw [hs1]; split_ifs
    · exact posTab_le _
    · omega
  have hev2 : τ2.vars "ev" = τ.vars "ev" := by rw [hv2 "ev" (by decide), hv1 "ev" (by decide) (by decide)]
  by_cases hA : τ.vars "kk" = 0 ∧ 5 < τ.vars "tg"
  · obtain ⟨hd1, hn1⟩ := hA1 hA
    obtain ⟨τ3, hr3, -, -, hn3, hd3⟩ := subC_spec J B τ2 ⟨hdat2, by rw [hev2]; exact hev, hs1le,
      by rw [hv2 "nv" (by decide), hn1]; omega, by rw [hv2 "drp" (by decide), hd1]⟩
    have hs10 : τ2.vars "s1" = 0 := by rw [hs1, if_neg (by omega)]
    have hr : rsub J (τ.vars "tg") (τ.vars "kk") (τ.vars "dd") (τ.vars "ev") = none := by
      simp [rsub, hA]
    refine ⟨τ3, (Run.seq hr1 (Run.seq hr2 hr3)).mono (by simp), ?_, ?_, ?_⟩
    · rw [hn3, hr, if_neg (by omega), hv2 "nv" (by decide), hn1]; rfl
    · rw [hn3, if_neg (by omega), hv2 "nv" (by decide), hn1]; omega
    · rw [hd3, hr, if_neg (by omega), hv2 "drp" (by decide), hd1]; rfl
  · obtain ⟨hd1, hn1⟩ := hA2 hA
    obtain ⟨τ3, hr3, -, -, hn3, hd3⟩ := subC_spec J B τ2 ⟨hdat2, by rw [hev2]; exact hev, hs1le,
      by rw [hv2 "nv" (by decide), hn1]; exact hev, by rw [hv2 "drp" (by decide), hd1]; omega⟩
    have hpos : τ2.vars "s1" = 1 ↔ IsPos (τ.vars "tg") (τ.vars "kk") := by
      rw [hs1, IsPos]
      by_cases h : τ.vars "tg" < 6 ∧ τ.vars "kk" < 4
      · rw [if_pos h]; simp [h]
      · rw [if_neg h]
        constructor
        · intro e; exact absurd e (by decide)
        · rintro ⟨a, b, -⟩; exact absurd ⟨a, b⟩ h
    refine ⟨τ3, (Run.seq hr1 (Run.seq hr2 hr3)).mono (by simp), ?_, ?_, ?_⟩
    · rw [hn3, hev2, hv2 "nv" (by decide), hn1]
      by_cases hp : IsPos (τ.vars "tg") (τ.vars "kk")
      · rw [if_pos (hpos.mpr hp)]; simp [rsub, hA, hp]
      · rw [if_neg (fun h => hp (hpos.mp h))]; simp [rsub, hA, hp]
    · rw [hn3, hev2, hv2 "nv" (by decide), hn1]
      split_ifs
      · cases hg : gmap J (τ.vars "ev") with
        | none => simp; omega
        | some r => simpa using gmap_lt J hJl hev (by omega) hg
      · exact hev
    · rw [hd3, hev2, hv2 "drp" (by decide), hd1]
      by_cases hp : IsPos (τ.vars "tg") (τ.vars "kk")
      · have := hpos.mpr hp
        cases hg : gmap J (τ.vars "ev") <;> simp [rsub, hA, hp, hg, this]
      · have : ¬ τ2.vars "s1" = 1 := fun h => hp (hpos.mp h)
        simp [rsub, hA, hp, this]

/-- The hook for the guards. -/
def grdCmd : Com :=
  .seq (.assign "drp" (.lit 0))
    (.ite (.lt (.var "gi") (.var "g1"))
      (.seq (.assign "s2" (.get "gt" (.add (.lit 24) (.var "gi"))))
        (.ite (.eq (.var "s2") (.lit 0)) (.seq (.assign "drp" (.lit 1)) (.assign "ng" (.lit 0)))
          (.assign "ng" (.sub (.var "s2") (.lit 1)))))
      (.assign "ng" (.add (.sub (.var "gi") (.var "g1")) (.var "g2"))))

theorem grdCmd_ok {ℓ : ℕ} (J : List (Fin ℓ)) (B : ℕ) : GrdOK grdCmd (rgsub J) (RDat J B) B 30 := by
  rintro τ ⟨⟨hg1, hg2, hJl, hgl, -, hgt, hB⟩, hgi, hdd⟩
  have hjl := jIdx_le J (τ.vars "gi")
  have hgt' : τ.vars "gi" < ℓ → (τ.arrs "gt").getD (24 + τ.vars "gi") 0 = jIdx J (τ.vars "gi") :=
    fun h => hgt _ h
  unfold grdCmd
  run_vcg
  all_goals (try simp only [vars_setVar, if_true, arrs_setVar, show ("s2" : String) = "ng" ↔ False by decide,
    show ("s2" : String) = "drp" ↔ False by decide, show ("ng" : String) = "drp" ↔ False by decide,
    show ("drp" : String) = "ng" ↔ False by decide, if_false])
  all_goals (simp_all [rgsub, gmap]; (try split_ifs) <;> (try simp_all) <;> omega)

/-- The hooks write only their scalars. -/
theorem subCmd_frame : HookFrame subCmd := by
  refine ⟨fun y hy => ?_, by simp [subCmd, subA, subB, subC, Com.warrs], by
    simp [subCmd, subA, subB, subC, Com.reads], by simp [subCmd, subA, subB, subC, Com.NoWrite]⟩
  simp [subCmd, subA, subB, subC, Com.wvars] at hy
  simp [hookVars]
  tauto

theorem grdCmd_frame : HookFrame grdCmd := by
  refine ⟨fun y hy => ?_, by simp [grdCmd, Com.warrs], by simp [grdCmd, Com.reads],
    by simp [grdCmd, Com.NoWrite]⟩
  simp [grdCmd, Com.wvars] at hy
  simp [hookVars]; tauto

/-! ### Reading `J` -/

/-- Mark the position entries of atom codes. -/
def ptStores : Com :=
  .seq (.store "gt" (.lit 1) (.lit 1)) (.seq (.store "gt" (.lit 2) (.lit 1))
  (.seq (.store "gt" (.lit 5) (.lit 1)) (.seq (.store "gt" (.lit 6) (.lit 1))
  (.seq (.store "gt" (.lit 9) (.lit 1)) (.seq (.store "gt" (.lit 10) (.lit 1))
  (.seq (.store "gt" (.lit 14) (.lit 1)) (.seq (.store "gt" (.lit 18) (.lit 1))
  (.seq (.store "gt" (.lit 19) (.lit 1)) (.store "gt" (.lit 23) (.lit 1))))))))))

/-- The table after `ptStores`. -/
def ptArr (n : ℕ) : List ℕ :=
  ((((((((((List.replicate n 0).set 1 1).set 2 1).set 5 1).set 6 1).set 9 1).set 10 1).set 14 1).set
    18 1).set 19 1).set 23 1

theorem ptStores_run (B n : ℕ) (hn : 24 ≤ n) (hB : 24 < B) (τ : Env)
    (h : τ.arrs "gt" = List.replicate n 0) :
    Run B ptStores τ (τ.setArr "gt" 1 1 |>.setArr "gt" 2 1 |>.setArr "gt" 5 1 |>.setArr "gt" 6 1
      |>.setArr "gt" 9 1 |>.setArr "gt" 10 1 |>.setArr "gt" 14 1 |>.setArr "gt" 18 1
      |>.setArr "gt" 19 1 |>.setArr "gt" 23 1) 30 := by
  unfold ptStores
  refine (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_)
    (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_)
    (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_)
      (Run.store ?_ ?_ ?_)))))))))).mono (by simp)
  all_goals simp [h]
  all_goals omega

/-- The first 24 entries of the table. -/
def pt24 : List ℕ := [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]

theorem ptArr_eq (n : ℕ) (hn : 24 ≤ n) : ptArr n = pt24 ++ List.replicate (n - 24) 0 := by
  have hs : List.replicate n 0 = List.replicate 24 0 ++ List.replicate (n - 24) 0 := by
    rw [← List.replicate_add]; congr 1; omega
  simp only [ptArr, hs]
  repeat rw [List.set_append_left _ _ (by simp)]
  rfl

theorem ptArr_low (n : ℕ) (hn : 24 ≤ n) : ∀ c < 24, (ptArr n).getD c 0 = posTab c := by
  intro c hc
  rw [ptArr_eq n hn, List.getD_append _ _ _ _ (by simp [pt24]; omega)]
  interval_cases c <;> rfl

theorem ptArr_high (n : ℕ) (hn : 24 ≤ n) (i : ℕ) : (ptArr n).getD (24 + i) 0 = 0 := by
  rw [ptArr_eq n hn, List.getD_append_right _ _ _ _ (by simp [pt24])]
  simp [pt24]

theorem ptArr_length (n : ℕ) (hn : 24 ≤ n) : (ptArr n).length = n := by
  rw [ptArr_eq n hn]; simp [pt24]; omega

/-- Record one entry of `J`. -/
def jBody : Com :=
  .seq (.read "r3") (.seq (.store "gt" (.add (.lit 24) (.var "r3")) (.add (.var "r2") (.lit 1)))
    (.assign "r2" (.add (.var "r2") (.lit 1))))

/-- Read `J` into the tables. -/
def readArgs : Com :=
  .seq (.read "r1") (.seq (.assign "g2" (.var "r1")) (.seq (.assign "ol" (.var "r1"))
    (.seq (.assign "g1" (.var "hl")) (.seq ptStores (.seq (.assign "r2" (.lit 0))
      (.while (.lt (.var "r2") (.var "r1")) jBody))))))

/-- The word of a list of positions. -/
theorem toWord_listFin {ℓ : ℕ} (J : List (Fin ℓ)) : toWord J = J.length :: J.map Fin.val := by
  change J.length :: (J.map toWord).flatten = _
  congr 1
  induction J with
  | nil => rfl
  | cons a J ih => simp [ih]; rfl

theorem jIdx_eq_succ {ℓ : ℕ} {J : List (Fin ℓ)} (hJ : J.Nodup) {i j : ℕ} (hj : j < J.length)
    (h : (J[j]).val = i) : jIdx J i = j + 1 := by
  have hi : i < ℓ := by rw [← h]; exact (J[j]).isLt
  have hp := (isPInv_listPInv hJ ⟨i, hi⟩ ⟨j, hj⟩).mpr (by ext; simp [h])
  simp [jIdx, hi, hp]

theorem jIdx_eq_zero {ℓ : ℕ} {J : List (Fin ℓ)} (hJ : J.Nodup) {i : ℕ} (hi : i < ℓ)
    (h : ∀ j (hj : j < J.length), (J[j]).val ≠ i) : jIdx J i = 0 := by
  unfold jIdx
  rw [dif_pos hi]
  cases hp : listPInv J ⟨i, hi⟩ with
  | none => rfl
  | some j =>
    have := (isPInv_listPInv hJ ⟨i, hi⟩ j).mp hp
    exact absurd (by have := congrArg Fin.val this; simpa using this) (h j.val j.isLt)

theorem readArgs_spec {ℓ : ℕ} (J : List (Fin ℓ)) (hJ : J.Nodup) (B : ℕ) (hB : ℓ + 25 < B) :
    Spec B (fun τ => τ.inp = toWord J ∧ τ.vars "hl" = ℓ ∧ τ.arrs "gt" = List.replicate (ℓ + 24) 0)
      readArgs (fun _ τ' => RDat J B τ' ∧ τ'.vars "ol" = J.length) (16 * J.length + 60) := by
  rintro τ ⟨hinp, hhl, hgt⟩
  have hJl : J.length ≤ ℓ := by simpa using hJ.length_le_card
  rw [toWord_listFin] at hinp
  set τ4 := (({ τ.setVar "r1" J.length with inp := J.map Fin.val }.setVar "g2" J.length).setVar "ol"
    J.length).setVar "g1" ℓ with hτ4
  have hr4 : Run B (.seq (.read "r1") (.seq (.assign "g2" (.var "r1")) (.seq (.assign "ol" (.var "r1"))
      (.assign "g1" (.var "hl"))))) τ τ4 10 := by
    refine (Run.seq (Run.read hinp) (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_)
      (Run.assign ?_)))).mono (by simp)
    · simp; omega
    · simp; omega
    · simp [hhl]; omega
  have hr5 := ptStores_run B (ℓ + 24) (by omega) (by omega) τ4 (by simp [hτ4, hgt])
  set τ5 := (τ4.setArr "gt" 1 1 |>.setArr "gt" 2 1 |>.setArr "gt" 5 1 |>.setArr "gt" 6 1
      |>.setArr "gt" 9 1 |>.setArr "gt" 10 1 |>.setArr "gt" 14 1 |>.setArr "gt" 18 1
      |>.setArr "gt" 19 1 |>.setArr "gt" 23 1) with hτ5
  have hgt5 : τ5.arrs "gt" = ptArr (ℓ + 24) := by simp [hτ5, hτ4, hgt, ptArr]
  set τ6 := τ5.setVar "r2" 0 with hτ6
  let I : Env → Prop := fun ρ => ρ.inp = (J.map Fin.val).drop (ρ.vars "r2") ∧ ρ.vars "r1" = J.length ∧
    ρ.vars "r2" ≤ J.length ∧ ρ.vars "g1" = ℓ ∧ ρ.vars "g2" = J.length ∧ ρ.vars "ol" = J.length ∧
    (ρ.arrs "gt").length = ℓ + 24 ∧ (∀ c < 24, (ρ.arrs "gt").getD c 0 = posTab c) ∧
    ∀ i < ℓ, (∀ j (hj : j < J.length), j < ρ.vars "r2" → (J[j]).val = i →
        (ρ.arrs "gt").getD (24 + i) 0 = j + 1) ∧
      ((∀ j (hj : j < J.length), j < ρ.vars "r2" → (J[j]).val ≠ i) → (ρ.arrs "gt").getD (24 + i) 0 = 0)
  have hI6 : I τ6 := by
    refine ⟨by simp [hτ6, hτ5, hτ4], by simp [hτ6, hτ5, hτ4], by simp [hτ6], by simp [hτ6, hτ5, hτ4],
      by simp [hτ6, hτ5, hτ4], by simp [hτ6, hτ5, hτ4], ?_, ?_, fun i hi => ⟨fun j _ hj => ?_, fun _ => ?_⟩⟩
    · have : (τ6.arrs "gt") = ptArr (ℓ + 24) := by simp [hτ6, hgt5]
      rw [this, ptArr_length _ (by omega)]
    · have : (τ6.arrs "gt") = ptArr (ℓ + 24) := by simp [hτ6, hgt5]
      rw [this]; exact ptArr_low _ (by omega)
    · simp [hτ6] at hj
    · have : (τ6.arrs "gt") = ptArr (ℓ + 24) := by simp [hτ6, hgt5]
      rw [this]; exact ptArr_high _ (by omega) i
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars "r2" < J.length) jBody
      (fun ρ ρ' => I ρ' ∧ ρ'.vars "r2" = ρ.vars "r2" + 1) 12 := by
    rintro ρ ⟨⟨hin, hr1, hle, h1, h2, hol, hgl, hlow, hhigh⟩, hlt⟩
    obtain ⟨j, hjd⟩ : ∃ j, ρ.vars "r2" = j := ⟨_, rfl⟩
    rw [hjd] at hin hle hhigh hlt
    have hinp' : ρ.inp = (J[j]).val :: (J.map Fin.val).drop (j + 1) := by
      rw [hin, List.drop_eq_getElem_cons (by simpa using hlt)]; simp
    set a := (J[j]).val with ha
    have haℓ : a < ℓ := (J[j]).isLt
    set ρ' := (({ ρ.setVar "r3" a with inp := (J.map Fin.val).drop (j + 1) }.setArr "gt" (24 + a)
      (j + 1)).setVar "r2" (j + 1)) with hρ'
    have hgt' : ρ'.arrs "gt" = (ρ.arrs "gt").set (24 + a) (j + 1) := by simp [hρ']
    refine ⟨ρ', ?_, ⟨by simp [hρ'], by simp [hρ', hr1], by simp [hρ']; omega, by simp [hρ', h1],
      by simp [hρ', h2], by simp [hρ', hol], by rw [hgt', List.length_set, hgl], ?_, ?_⟩,
      by simp [hρ', hjd]⟩
    · unfold jBody
      refine (Run.seq (Run.read hinp') (Run.seq (Run.store ?_ ?_ ?_) (Run.assign ?_))).mono (by simp)
      · simp; omega
      · simp [hjd]; omega
      · simp [hgl]; omega
      · simp [hjd]; omega
    · intro c hc
      rw [hgt', getD_set_of_lt (by omega), if_neg (by omega)]; exact hlow c hc
    · intro i hi
      have hr2' : ρ'.vars "r2" = j + 1 := by simp [hρ']
      rw [hr2', hgt', getD_set_of_lt (by omega)]
      by_cases hia : i = a
      · subst hia
        rw [if_pos rfl]
        refine ⟨fun j' hj' hj'1 he => ?_, fun h => absurd rfl (h j (by simpa using hlt) (by omega))⟩
        have : j' = j := (List.Nodup.getElem_inj_iff hJ).mp (Fin.ext he)
        rw [this]
      · rw [if_neg (by omega)]
        obtain ⟨hh1, hh2⟩ := hhigh i hi
        refine ⟨fun j' hj' hj'1 he => hh1 j' hj' ?_ he, fun h => hh2 fun j' hj' hj'1 => h j' hj' (by omega)⟩
        rcases Nat.lt_or_ge j' j with h | h
        · exact h
        · exfalso; obtain rfl : j' = j := by omega
          exact hia he.symm
  obtain ⟨τ', hr, hI', hend⟩ := (Spec.forRange (B := B) (c := jBody) (P := fun ρ => ρ = τ6) "r2" "r1" I
    J.length 12 (16 * J.length + 4) (fun ρ hI => by have := hI.2.2.1; omega)
    (fun ρ hI => by rw [hI.2.1]; omega) (fun ρ hI => hI.2.1) (fun ρ hI => hI.2.2.1) hbody
    (fun ρ h => h ▸ hI6) (fun ρ h => by subst h; simp [hτ6])).run rfl
  obtain ⟨-, -, -, h1', h2', hol', hgl', hlow', hhigh'⟩ := hI'
  rw [hend] at hhigh'
  refine ⟨τ', ?_, ⟨h1', h2', hJl, hgl', hlow', fun i hi => ?_, hB⟩, hol'⟩
  · unfold readArgs
    refine (Run.seq (Run.read hinp) (Run.seq (Run.assign (v := J.length) ?_) (Run.seq
      (Run.assign (v := J.length) ?_) (Run.seq (Run.assign (v := ℓ) ?_) (Run.seq hr5
        (Run.seq (Run.assign (v := 0) ?_) hr)))))).mono ?_
    · simp; omega
    · simp; omega
    · simp [hhl]; omega
    · simp; omega
    · simp only [Expr.size]; omega
  · obtain ⟨hh1, hh2⟩ := hhigh' i hi
    by_cases hex : ∃ j, ∃ hj : j < J.length, (J[j]).val = i
    · obtain ⟨j, hj, he⟩ := hex
      rw [hh1 j hj hj he, jIdx_eq_succ hJ hj he]
    · simp only [not_exists] at hex
      rw [hh2 fun j hj _ => hex j hj, jIdx_eq_zero hJ hi hex]

theorem readArgs_frame : ArgFrame readArgs := by
  refine ⟨fun y hy => ?_, fun b hb => ?_, by simp [readArgs, ptStores, jBody, Com.NoWrite]⟩
  · simp [readArgs, ptStores, jBody, Com.wvars] at hy
    simp; tauto
  · simp [readArgs, ptStores, jBody, Com.warrs] at hb
    tauto

/-! ### The program -/

/-- The one pass of the restriction, in IMP+. It writes the jobs of the
restricted tree, with sets in arbitrary order. -/
def prog : Com := jobProg readArgs subCmd grdCmd

/-- The scalars and arrays of `prog`. -/
def layout : Lax808846Proofs.Compile.Layout :=
  ⟨["hk", "hq", "hl", "ol", "xp", "e1", "e2", "e3", "vv", "ev", "nn", "u", "y", "dd", "b0", "m", "ap",
    "lf", "tg", "dr", "kk", "nv", "ng", "drp", "s1", "s2", "s3", "cc", "gi", "cs", "cl", "ck", "bp",
    "g1", "g2", "g3", "g4", "r1", "r2", "r3", "ci", "cj", "pa", "pb", "la", "lb", "k", "c", "fnd", "s",
    "ok", "best", "hp", "prev", "cnt", "t", "ow", "s0", "l0", "wk", "fi", "i", "j", "p", "n", "v"],
    ["x", "pos", "dep", "fc", "a", "st", "ln", "ord", "b", "bs", "bl", "gt"], 8⟩

theorem prog_ok : Lax808846Proofs.Compile.Com.Ok layout prog := by
  simp [prog, jobProg, readTree, cpList, cpFrame, cpEntries, cpEntry, readArgs, ptStores, jBody, bfs,
    bfsBody, skipList, skipBody, pushList, pushBody, fillRefs, forUpJ, fillBody, fillIdx, jobLoop,
    jobNode, atList, atFrame, atEntries, atEntry, subCmd, subA, subB, subC, exList, exFrame, exCopies,
    exCopy, grdCmd, writeAll, writeWord, writeEntry, rootRefs, rootIdx, layout,
    Lax808846Proofs.Compile.Com.Ok, Lax808846Proofs.Compile.Cond.Ok, Lax808846Proofs.Compile.condExpr,
    Lax808846Proofs.Compile.Expr.Ok]

theorem gmap_le {ℓ : ℕ} (J : List (Fin ℓ)) (hJ : J.length ≤ ℓ) {v r : ℕ} (h : gmap J v = some r) :
    r ≤ v ∨ r < J.length := by
  unfold gmap at h
  have := jIdx_le J v
  split_ifs at h with h1 h2 <;> simp at h <;> omega

theorem rsub_le {ℓ : ℕ} (J : List (Fin ℓ)) (hJ : J.length ≤ ℓ) {tg k d v r : ℕ}
    (h : rsub J tg k d v = some r) : r ≤ v ∨ r < J.length := by
  unfold rsub at h
  split_ifs at h with h1 h2
  · exact gmap_le J hJ h
  · simp at h; omega

theorem toWord_tree_pair {ℓ : ℕ} (T : TypeTree) (J : List (Fin ℓ)) :
    toWord (T, J) = [T.k, T.q, T.ℓ] ++ toWord T.root ++ toWord J := rfl

theorem toWord_tree (T : TypeTree) : toWord T = [T.k, T.q, T.ℓ] ++ toWord T.root := rfl

end Lax185574Proofs.RestrictionRam

namespace Lax185574Proofs.Restriction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.RestrictionRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574.PartialGraphs
open Lax185574Proofs.TreeCanon

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_restrict_old :
    ∃ (p : Lax808846.Ram.Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (J : List (Fin ℓ)), ℓ ≤ k → J.Nodup →
        Lax185574.Computing.Computes p e c (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨p, e, hp⟩ := treeCanon readArgs subCmd grdCmd layout prog_ok
  obtain ⟨C, hC⟩ := hp 200
  refine ⟨p, e, fun k q => ⟨C, e, fun n G ℓ u J _ hJ => ?_⟩⟩
  set t := node G k q u with ht
  have hx : toWord (tree G k q u, J) = [k, q, ℓ] ++ toWord t ++ toWord J := rfl
  intro w hadm
  rw [hx] at hadm ⊢
  set x := [k, q, ℓ] ++ toWord t ++ toWord J with hxdef
  set M := maxEntry x with hM
  have hmem : ∀ v ∈ x, v ≤ M := fun v hv => le_maxEntry hv
  have hJl : J.length ≤ ℓ := by simpa using hJ.length_le_card
  have hJm : J.length ≤ M := hmem _ (by rw [hxdef, toWord_listFin]; simp)
  have hℓm : ℓ ≤ M := hmem _ (by rw [hxdef]; simp)
  have hJx : J.length ≤ x.length := by rw [hxdef, toWord_listFin]; simp; omega
  set B := valBound 8 2 x with hB
  have hBdef : B = 8 * (x.length + M + 1) ^ 2 := rfl
  have hMB : M + 26 < B := by
    have h1 : 4 ≤ x.length := by rw [hxdef, toWord_listFin]; simp <;> omega
    have h2 : x.length + M + 1 ≤ (x.length + M + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [hBdef]; omega
  have hadm' : C * (x.length + M + 1) ^ e ≤ 2 ^ w := hadm M (maxEntry_mem (by simp [hxdef]))
  obtain ⟨h1, h2⟩ := hC (rsub J) (rgsub J) (RDat J B) 70 30 (16 * J.length + 60) k q ℓ t (toWord J)
    (ℓ + 24) J.length subCmd_frame grdCmd_frame readArgs_frame (subCmd_ok J B) (grdCmd_ok J B)
    (rdat_ok J B) (readArgs_spec J hJ B (by omega))
    (fun dd _ tg kk v r hv hr => by
      have hvM : v ≤ M := by
        rcases hv with hv | rfl
        · exact hmem v (by rw [hxdef]; simp [hv])
        · omega
      show r < B
      rcases rsub_le J hJl hr with h | h <;> omega)
    (fun dd _ i r hi hr => by
      have hiM : i ≤ M := by
        rcases hi with hi | rfl
        · exact hmem i (by rw [hxdef]; simp [hi])
        · omega
      show r < B
      rcases gmap_le J hJl hr with h | h <;> omega)
    (show J.length < B by omega) (show 70 + 30 + (16 * J.length + 60) ≤ 200 * (x.length + 1) by omega)
    w hadm'
  have hout : [k, q, J.length] ++ treeOut (rsub J) (rgsub J) q 0
      (toWord t ++ List.replicate (x.length + 1 - (toWord t).length) 0) 0 =
      toWord (tree G k q (fun i => u (J.get i))) := by
    rw [treeOut_restrict J _ q 0 t 0 (List.replicate (x.length + 1 - (toWord t).length) 0)
      (by simp), toWord_tree]
    rw [← restrictTree_tree G k q u J hJ]
    rfl
  rw [hout] at h1 h2
  refine ⟨h1, fun _ y hy => ?_⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨T, hT, hr⟩ := h2
  exact ⟨T, hT, hr⟩

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.Restriction.exists_program_restrict
---
The program is one pass over the tree followed by restoring canonical
form, as in the proof of the restriction lemma. The pass reads the tree
and `J`, the latter into a table of the places of the positions, lists
the nodes of the tree in breadth-first order, and writes for every node,
from the last to the first, its transformed atoms and its transformed
extensions. An atom is transformed by renaming its positions along `J`,
and dropped if a position lies outside `J`. An extension is transformed
by renaming its guard in the same way, and dropped if the guard lies
outside `J`, and its child is referred to by the indices of the jobs of
the child. Positions beyond the arity `ℓ`, the new positions of the
nodes below the root, are moved down by `ℓ - |J|`. Nothing is sorted in
the pass. The canonical form is then restored from the leaves up by the
program of the canonical form observation, called once for every set of
the result (`TreeCanon.treeCanon`). The result is the semantic core
`restrictNode` along the partial inverse of `J`, whose correctness is
`restrictTree_tree`. The sets of the result are no larger than those of
the input, so the time is polynomial in the length of the input.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_restrict :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (J : List (Fin ℓ)),
        ℓ ≤ k → J.Nodup →
          A.Computes c (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
            (((encode (tree G k q u)).length + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_restrict_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  refine ⟨c * (k + 1 + 1) ^ a, a, fun n G ℓ u J hℓ hJ => ?_⟩
  have hJl : J.length ≤ k := le_trans (by simpa using hJ.length_le_card) hℓ
  refine computes_of_old_nat (((encode (tree G k q u)).length + 1) ^ a) (by push_cast; rfl)
    (Nat.le_mul_of_pos_right _ (by positivity)) ?_ (h n G ℓ u J hℓ hJ)
  show c * ((encode (tree G k q u, J)).length + 1) ^ a ≤ _
  rw [length_encode_prod, length_encode_list_fin]
  refine le_trans ?_ (Nat.le_add_right _ _)
  rw [mul_assoc]
  exact Nat.mul_le_mul_left c (le_trans (Nat.pow_le_pow_left (by omega) a)
    (add_succ_pow_le (encode (tree G k q u)).length (k + 1) a))

end Lax185574Proofs.Restriction
