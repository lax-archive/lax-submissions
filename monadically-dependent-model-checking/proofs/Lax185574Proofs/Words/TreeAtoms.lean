import Lax185574Proofs.Words.TreeBuf
import Lax185574Proofs.Words.TreeBfs

/-!
The candidates for the atoms of a transformed node.

The command `atList` scans the list of atom codes of a node at `y` in the
array `x`, maps every code entry by entry with the hook command `subCmd`,
and keeps the codes that are not dropped as a list of words in the arrays
`a`, `st` and `ln` of `Lax185574Proofs.Words.Read`, ready for `collect`.

The hook is any command that computes `nv`, the new value of an entry, and
`drp`, `1` if the atom is dropped, from the tag `tg`, the index `kk` of the
entry, the depth `dd` and the value `ev`, as the function `sub` does
(`SubOK`). It may use data that the program has prepared before
(`Dat`), and it writes only the scalars of `HookFrame`.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

/-! ### Hooks -/

/-- The scalars a hook may write. -/
def hookVars : List String := ["nv", "ng", "drp", "s1", "s2", "s3"]

/-- A hook writes only the scalars of `hookVars`, no array, and does not
use the tapes. -/
def HookFrame (cmd : Com) : Prop :=
  (∀ y ∈ cmd.wvars, y ∈ hookVars) ∧ cmd.warrs = [] ∧ ¬ cmd.reads ∧ cmd.NoWrite

/-- The data of a hook lives in the scalars `g1`, …, `g4` and the array
`gt`, which no other part of the program writes. -/
def DatOK (Dat : Env → Prop) : Prop :=
  ∀ τ τ' : Env, τ'.vars "g1" = τ.vars "g1" → τ'.vars "g2" = τ.vars "g2" →
    τ'.vars "g3" = τ.vars "g3" → τ'.vars "g4" = τ.vars "g4" → τ'.arrs "gt" = τ.arrs "gt" →
    Dat τ → Dat τ'

/-- The hook `cmd` maps one entry of an atom code as `sub` does. -/
def SubOK (cmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (Dat : Env → Prop) (B Ks : ℕ) : Prop :=
  Spec B (fun τ => Dat τ ∧ τ.vars "tg" < B ∧ τ.vars "kk" < B ∧ τ.vars "dd" < B ∧ τ.vars "ev" < B)
    cmd (fun τ τ' =>
      τ'.vars "nv" = (sub (τ.vars "tg") (τ.vars "kk") (τ.vars "dd") (τ.vars "ev")).getD 0 ∧
      τ'.vars "nv" < B ∧
      τ'.vars "drp" = (if (sub (τ.vars "tg") (τ.vars "kk") (τ.vars "dd") (τ.vars "ev")).isSome
        then 0 else 1)) Ks

theorem HookFrame.var {cmd : Com} (h : HookFrame cmd) {B : ℕ} {τ τ' : Env} {K : ℕ}
    (hr : Run B cmd τ τ' K) (y : String) (hy : y ∉ hookVars) : τ'.vars y = τ.vars y :=
  hr.frame_var y fun hm => hy (h.1 y hm)

theorem HookFrame.arr {cmd : Com} (h : HookFrame cmd) {B : ℕ} {τ τ' : Env} {K : ℕ}
    (hr : Run B cmd τ τ' K) (a : String) : τ'.arrs a = τ.arrs a :=
  hr.frame_arr a (by rw [h.2.1]; simp)

/-! ### Mapping a code entry by entry -/

/-- The new value of entry `k` of the code `w` with tag `tg`. -/
def mapVal (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (tg d : ℕ) (w : List ℕ) (k : ℕ) : ℕ :=
  (sub tg k d (w.getD k 0)).getD 0

theorem atomMapAux_eq (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (tag d : ℕ) :
    ∀ (w : List ℕ) (k0 : ℕ), atomMapAux sub tag d k0 w =
      if (∀ k (h : k < w.length), (sub tag (k0 + k) d w[k]).isSome) then
        some ((List.range w.length).map fun k => (sub tag (k0 + k) d (w.getD k 0)).getD 0)
      else none
  | [], k0 => by simp [atomMapAux]
  | v :: w, k0 => by
    rw [atomMapAux, atomMapAux_eq sub tag d w (k0 + 1)]
    have hiff : (∀ k (h : k < (v :: w).length), (sub tag (k0 + k) d (v :: w)[k]).isSome) ↔
        (sub tag k0 d v).isSome ∧ ∀ k (h : k < w.length), (sub tag (k0 + 1 + k) d w[k]).isSome := by
      constructor
      · intro h
        refine ⟨by have := h 0 (by simp); simpa using this, fun k hk => ?_⟩
        have := h (k + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this
      · rintro ⟨h0, h⟩ k hk
        cases k with
        | zero => simpa using h0
        | succ k =>
          have := h k (by simp at hk; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this
    by_cases h1 : (sub tag k0 d v).isSome
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h1
      by_cases h2 : ∀ k (h : k < w.length), (sub tag (k0 + 1 + k) d w[k]).isSome
      · rw [if_pos h2, if_pos (hiff.mpr ⟨h1, h2⟩), ha]
        simp only [Option.bind_some, Option.map_some, List.length_cons, Option.some.injEq]
        rw [List.range_succ_eq_map]
        simp [ha, Nat.add_assoc, Nat.add_comm 1]
      · rw [if_neg h2, if_neg (fun h => h2 (hiff.mp h).2), ha]; rfl
    · rw [if_neg (fun h => h1 (hiff.mp h).1)]
      cases h : sub tag k0 d v with
      | none => rfl
      | some a => rw [h] at h1; simp at h1

theorem atomMap_eq (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (w : List ℕ) :
    atomMap sub d w = if (∀ k < w.length, (sub (w.headD 0) k d (w.getD k 0)).isSome) then
      some ((List.range w.length).map (mapVal sub (w.headD 0) d w)) else none := by
  rw [atomMap, atomMapAux_eq]
  have hiff : (∀ k (h : k < w.length), (sub (w.headD 0) (0 + k) d w[k]).isSome) ↔
      (∀ k < w.length, (sub (w.headD 0) k d (w.getD k 0)).isSome) := by
    constructor
    · intro h k hk; have := h k hk; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
    · intro h k hk; have := h k hk; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
  by_cases hc : ∀ k < w.length, (sub (w.headD 0) k d (w.getD k 0)).isSome
  · rw [if_pos (hiff.mpr hc), if_pos hc]; simp [mapVal]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]

/-! ### Words at a position -/

theorem length_frWord {X : List ℕ} {f : ℕ} (h : f + 1 + xg X f ≤ X.length) :
    (frWord X f).length = xg X f := by
  simp [frWord]; omega

theorem frWord_getD {X : List ℕ} {f : ℕ} {k : ℕ}
    (hk : k < xg X f) : (frWord X f).getD k 0 = xg X (f + 1 + k) := by
  have hk' : k < X[f]?.getD 0 := by simpa [xg, List.getD_eq_getElem?_getD] using hk
  simp only [frWord, xg, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hk']

theorem frWord_headD {X : List ℕ} {f : ℕ} (hk : 0 < xg X f) :
    (frWord X f).headD 0 = xg X (f + 1) := by
  have := frWord_getD hk
  rw [List.getD_eq_getElem?_getD] at this
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, this]

/-! ### Lists of words in the arrays -/

theorem WordsAt.set_a {ws : List (List ℕ)} {τ τ' : Env} (h : WordsAt ws τ) {i v : ℕ}
    (hi : total ws ≤ i) (ha : τ'.arrs "a" = (τ.arrs "a").set i v)
    (hst : τ'.arrs "st" = τ.arrs "st") (hln : τ'.arrs "ln" = τ.arrs "ln") : WordsAt ws τ' where
  st := by rw [hst]; exact h.st
  ln := by rw [hln]; exact h.ln
  a i' hi' j hj := by
    have := off_add_le hi'
    rw [ha, List.getElem?_set_ne (by omega)]
    exact h.a i' hi' j hj

theorem WordsAt.set_st {ws : List (List ℕ)} {τ τ' : Env} (h : WordsAt ws τ) {i v : ℕ}
    (hi : ws.length ≤ i) (hst : τ'.arrs "st" = (τ.arrs "st").set i v)
    (ha : τ'.arrs "a" = τ.arrs "a") (hln : τ'.arrs "ln" = τ.arrs "ln") : WordsAt ws τ' where
  st i' hi' := by rw [hst, List.getElem?_set_ne (by omega)]; exact h.st i' hi'
  ln := by rw [hln]; exact h.ln
  a := by rw [ha]; exact h.a

theorem WordsAt.set_ln {ws : List (List ℕ)} {τ τ' : Env} (h : WordsAt ws τ) {i v : ℕ}
    (hi : ws.length ≤ i) (hln : τ'.arrs "ln" = (τ.arrs "ln").set i v)
    (ha : τ'.arrs "a" = τ.arrs "a") (hst : τ'.arrs "st" = τ.arrs "st") : WordsAt ws τ' where
  st := by rw [hst]; exact h.st
  ln i' hi' := by rw [hln, List.getElem?_set_ne (by omega)]; exact h.ln i' hi'
  a := by rw [ha]; exact h.a

theorem off_append_self (ws : List (List ℕ)) (u : List ℕ) : off (ws ++ [u]) ws.length = total ws := by
  simp [off, total]

theorem WordsAt.snoc {ws : List (List ℕ)} {u : List ℕ} {τ : Env} (h : WordsAt ws τ)
    (hst : (τ.arrs "st")[ws.length]? = some (total ws))
    (hln : (τ.arrs "ln")[ws.length]? = some u.length)
    (ha : ∀ k (hk : k < u.length), (τ.arrs "a")[total ws + k]? = some u[k]) :
    WordsAt (ws ++ [u]) τ where
  st i hi := by
    rcases Nat.lt_or_ge i ws.length with h1 | h1
    · rw [h.st i h1]; simp [off, List.take_append_of_le_length h1.le]
    · obtain rfl : i = ws.length := by simp at hi; omega
      rw [hst, off_append_self]
  ln i hi := by
    rcases Nat.lt_or_ge i ws.length with h1 | h1
    · rw [h.ln i h1, List.getElem_append_left h1]
    · obtain rfl : i = ws.length := by simp at hi; omega
      rw [hln]; simp
  a i hi j hj := by
    rcases Nat.lt_or_ge i ws.length with h1 | h1
    · have hoff : off (ws ++ [u]) i = off ws i := by simp [off, List.take_append_of_le_length h1.le]
      rw [hoff]
      have e : (ws ++ [u])[i] = ws[i] := List.getElem_append_left h1
      have hj' : j < ws[i].length := by rw [← e]; exact hj
      have := h.a i h1 j hj'
      rw [this]
      simp only [e]
    · obtain rfl : i = ws.length := by simp at hi; omega
      rw [off_append_self]
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton] at hj ⊢
      exact ha j hj

/-! ### The entries of one code -/

/-- Map one entry: read it, run the hook, store the new value, and note a
drop. -/
def atEntry (subCmd : Com) : Com :=
  .seq (.assign "ev" (.get "x" (.add (.add (.var "y") (.lit 1)) (.var "kk"))))
    (.seq subCmd (.seq (.store "a" (.var "ap") (.var "nv"))
      (.seq (.assign "ap" (.add (.var "ap") (.lit 1)))
        (.seq (.ite (.eq (.var "drp") (.lit 0)) .skip (.assign "dr" (.lit 1)))
          (.assign "kk" (.add (.var "kk") (.lit 1)))))))

/-- The invariant of the loop over the entries of the code `w` at the
frame position `f`. -/
def AtEInv (X : List ℕ) (f d : ℕ) (w : List ℕ) (ws : List (List ℕ)) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ)
    (Dat : Env → Prop) (Alen : ℕ) (τ : Env) : Prop :=
  τ.arrs "x" = X ∧ τ.vars "y" = f ∧ τ.vars "lf" = w.length ∧ (0 < w.length → τ.vars "tg" = w.headD 0) ∧
    τ.vars "dd" = d ∧ Dat τ ∧ τ.vars "kk" ≤ w.length ∧ τ.vars "ap" = total ws + τ.vars "kk" ∧
    τ.vars "dr" ≤ 1 ∧
    (τ.vars "dr" = 0 ↔ ∀ k < τ.vars "kk", (sub (w.headD 0) k d (w.getD k 0)).isSome) ∧
    (∀ k < τ.vars "kk", (τ.arrs "a")[total ws + k]? = some (mapVal sub (w.headD 0) d w k)) ∧
    WordsAt ws τ ∧ (τ.arrs "a").length = Alen

theorem atEntry_spec (subCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (B Ks : ℕ) (hF : HookFrame subCmd) (hS : SubOK subCmd sub Dat B Ks) (hD : DatOK Dat)
    (X : List ℕ) (f d : ℕ) (ws : List (List ℕ)) (Alen : ℕ)
    (hfX : f + 1 + xg X f ≤ X.length)
    (hX : ∀ v ∈ X, v < B) (hXB : X.length < B) (hdB : d < B)
    (hA : total ws + xg X f ≤ Alen) (hAB : total ws + xg X f < B) :
    Spec B (fun τ => AtEInv X f d (frWord X f) ws sub Dat Alen τ ∧ τ.vars "kk" < (frWord X f).length)
      (atEntry subCmd)
      (fun τ τ' => AtEInv X f d (frWord X f) ws sub Dat Alen τ' ∧ τ'.vars "kk" = τ.vars "kk" + 1)
      (Ks + 30) := by
  rintro τ ⟨⟨hxa, hy, hlf, htg, hdd, hdat, hkle, hap, hdr1, hdr, hent, hwa, halen⟩, hk⟩
  set w := frWord X f with hwdef
  have hwl : w.length = xg X f := length_frWord hfX
  have htg := htg (by omega)
  obtain ⟨k, hkdef⟩ : ∃ k, τ.vars "kk" = k := ⟨_, rfl⟩
  rw [hkdef] at hkle hap hdr hent hk
  have hkL : k < xg X f := by omega
  set v := xg X (f + 1 + k) with hv
  have hwv : w.getD k 0 = v := frWord_getD hkL
  have hvB : v < B := xg_lt hX (by omega)
  have htgB : w.headD 0 < B := by
    rw [frWord_headD (by omega)]; exact xg_lt hX (by omega)
  set τ1 := τ.setVar "ev" v with hτ1
  have hev : (Expr.get "x" (.add (.add (.var "y") (.lit 1)) (.var "kk"))).evalB B τ = some v := by
    simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hxa, hy]
    refine ⟨f + 1 + k, ⟨f + 1, k, ⟨f, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
      ⟨hkdef.symm, by omega⟩, rfl, by omega⟩, ?_, hvB⟩
    simp only [hv, xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show f + 1 + k < X.length by omega),
      Option.getD_some]
  have hdat1 : Dat τ1 := hD τ τ1 (by simp [hτ1]) (by simp [hτ1]) (by simp [hτ1]) (by simp [hτ1])
    (by simp [hτ1]) hdat
  have h1tg : τ1.vars "tg" = w.headD 0 := by rw [hτ1, vars_setVar, if_neg (by decide), htg]
  have h1kk : τ1.vars "kk" = k := by simp [hτ1, hkdef]
  have h1dd : τ1.vars "dd" = d := by rw [hτ1, vars_setVar, if_neg (by decide), hdd]
  have h1ev : τ1.vars "ev" = v := by rw [hτ1, vars_setVar, if_pos rfl]
  obtain ⟨τ2, hr2, hnv, hnvB, hdrp⟩ := hS τ1 ⟨hdat1, by rw [h1tg]; exact htgB,
    by rw [h1kk]; omega, by rw [h1dd]; omega, by rw [h1ev]; exact hvB⟩
  have hv2 : ∀ y, y ∉ hookVars → τ2.vars y = τ1.vars y := hF.var hr2
  have ha2 : ∀ a, τ2.arrs a = τ1.arrs a := hF.arr hr2
  rw [h1tg, h1kk, h1dd, h1ev] at hnv hdrp
  have hnvm : τ2.vars "nv" = mapVal sub (w.headD 0) d w k := by rw [hnv, mapVal, hwv]
  have hap2 : τ2.vars "ap" = total ws + k := by rw [hv2 "ap" (by decide)]; simp [hτ1, hap]
  have hk2 : τ2.vars "kk" = k := by rw [hv2 "kk" (by decide)]; simp [hτ1, hkdef]
  have hdr2 : τ2.vars "dr" = τ.vars "dr" := by rw [hv2 "dr" (by decide)]; simp [hτ1]
  have hal2 : (τ2.arrs "a").length = Alen := by rw [ha2]; simp [hτ1, halen]
  have hx2 : τ2.arrs "x" = X := by rw [ha2]; simp [hτ1, hxa]
  have hy2 : τ2.vars "y" = f := by rw [hv2 "y" (by decide)]; simp [hτ1, hy]
  have hlf2 : τ2.vars "lf" = w.length := by rw [hv2 "lf" (by decide)]; simp [hτ1, hlf]
  have htg2 : τ2.vars "tg" = w.headD 0 := by rw [hv2 "tg" (by decide)]; simp [hτ1, htg]
  have htg2' : 0 < w.length → τ2.vars "tg" = w.headD 0 := fun _ => htg2
  have hdd2 : τ2.vars "dd" = d := by rw [hv2 "dd" (by decide)]; simp [hτ1, hdd]
  have hst2 : τ2.arrs "st" = τ.arrs "st" := by rw [ha2]; simp [hτ1]
  have hln2 : τ2.arrs "ln" = τ.arrs "ln" := by rw [ha2]; simp [hτ1]
  have haa2 : τ2.arrs "a" = τ.arrs "a" := by rw [ha2]; simp [hτ1]
  have hdat2 : Dat τ2 := hD τ τ2 (by rw [hv2 "g1" (by decide)]; simp [hτ1])
    (by rw [hv2 "g2" (by decide)]; simp [hτ1]) (by rw [hv2 "g3" (by decide)]; simp [hτ1])
    (by rw [hv2 "g4" (by decide)]; simp [hτ1]) (by rw [ha2]; simp [hτ1]) hdat
  -- the common part of the invariant after the store
  have hcommon : ∀ ρ : Env, ρ.arrs "x" = X → ρ.vars "y" = f → ρ.vars "lf" = w.length →
      (0 < w.length → ρ.vars "tg" = w.headD 0) → ρ.vars "dd" = d → Dat ρ → ρ.vars "kk" = k + 1 →
      ρ.vars "ap" = total ws + (k + 1) → ρ.vars "dr" ≤ 1 →
      (ρ.vars "dr" = 0 ↔ ∀ k' < k + 1, (sub (w.headD 0) k' d (w.getD k' 0)).isSome) →
      ρ.arrs "a" = (τ.arrs "a").set (total ws + k) (mapVal sub (w.headD 0) d w k) →
      ρ.arrs "st" = τ.arrs "st" → ρ.arrs "ln" = τ.arrs "ln" →
      AtEInv X f d w ws sub Dat Alen ρ := by
    intro ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    refine ⟨h1, h2, h3, h4, h5, h6, by omega, by omega, h9, by rw [h7]; exact h10, ?_,
      hwa.set_a (by omega) h11 h12 h13, by rw [h11, List.length_set, halen]⟩
    intro k' hk'
    rw [h7] at hk'
    rw [h11]
    rcases Nat.lt_or_ge k' k with hlt | hge
    · rw [List.getElem?_set_ne (by omega)]; exact hent k' hlt
    · obtain rfl : k' = k := by omega
      rw [List.getElem?_set_self (by omega)]
  set τ3 := τ2.setArr "a" (total ws + k) (τ2.vars "nv") with hτ3
  set τ4 := τ3.setVar "ap" (total ws + k + 1) with hτ4
  have hsome : (sub (w.headD 0) k d v).isSome ↔ (sub (w.headD 0) k d (w.getD k 0)).isSome := by rw [hwv]
  by_cases hs : (sub (w.headD 0) k d v).isSome
  · have hdrp0 : τ2.vars "drp" = 0 := by rw [hdrp, if_pos hs]
    set τ6 := τ4.setVar "kk" (k + 1) with hτ6
    refine ⟨τ6, ?_, ?_, by simp [hτ6, hkdef]⟩
    · unfold atEntry
      refine (Run.seq (Run.assign hev) (Run.seq hr2 (Run.seq (Run.store (idx := total ws + k)
        (v := τ2.vars "nv") ?_ ?_ ?_) (Run.seq (Run.assign (v := total ws + k + 1) ?_)
          (Run.seq (Run.ite_true ?_ Run.skip) (Run.assign (v := k + 1) ?_)))))).mono ?_
      · simp [hap2]; omega
      · simp; exact hnvB
      · rw [hal2]; omega
      · simp [hap2]; omega
      · simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨0, 0, ⟨by simp [hτ4, hτ3, hdrp0], by simp [hτ4, hτ3, hdrp0]; omega⟩, ⟨rfl, by omega⟩,
          by simp⟩
      · simp [hτ4, hτ3, hk2]; omega
      · simp; omega
    · refine hcommon τ6 (by simp [hτ6, hτ4, hτ3, hx2]) (by simp [hτ6, hτ4, hτ3, hy2])
        (by simp [hτ6, hτ4, hτ3, hlf2]) (fun _ => by simp [hτ6, hτ4, hτ3, htg2]) (by simp [hτ6, hτ4, hτ3, hdd2])
        (hD τ2 τ6 (by simp [hτ6, hτ4, hτ3]) (by simp [hτ6, hτ4, hτ3]) (by simp [hτ6, hτ4, hτ3])
          (by simp [hτ6, hτ4, hτ3]) (by simp [hτ6, hτ4, hτ3]) hdat2)
        (by simp [hτ6]) (by simp [hτ6, hτ4]; omega) (by simp [hτ6, hτ4, hτ3, hdr2]; exact hdr1)
        ?_ (by simp [hτ6, hτ4, hτ3, haa2, hnvm]) (by simp [hτ6, hτ4, hτ3, hst2])
        (by simp [hτ6, hτ4, hτ3, hln2])
      simp only [hτ6, hτ4, hτ3, vars_setVar, vars_setArr, hdr2]
      simp only [show ("dr" : String) = "kk" ↔ False by decide, show ("dr" : String) = "ap" ↔ False by decide,
        if_false, hdr]
      constructor
      · intro h k' hk'
        rcases Nat.lt_or_ge k' k with hlt | hge
        · exact h k' hlt
        · obtain rfl : k' = k := by omega
          exact hsome.mp hs
      · intro h k' hk'; exact h k' (by omega)
  · have hdrp1 : τ2.vars "drp" = 1 := by rw [hdrp, if_neg hs]
    set τ6 := (τ4.setVar "dr" 1).setVar "kk" (k + 1) with hτ6
    refine ⟨τ6, ?_, ?_, by simp [hτ6, hkdef]⟩
    · unfold atEntry
      refine (Run.seq (Run.assign hev) (Run.seq hr2 (Run.seq (Run.store (idx := total ws + k)
        (v := τ2.vars "nv") ?_ ?_ ?_) (Run.seq (Run.assign (v := total ws + k + 1) ?_)
          (Run.seq (Run.ite_false ?_ (Run.assign (v := 1) ?_)) (Run.assign (v := k + 1) ?_)))))).mono ?_
      · simp [hap2]; omega
      · simp; exact hnvB
      · rw [hal2]; omega
      · simp [hap2]; omega
      · simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨1, 0, ⟨by simp [hτ4, hτ3, hdrp1], by simp [hτ4, hτ3, hdrp1]; omega⟩, ⟨rfl, by omega⟩,
          by simp⟩
      · simp; omega
      · simp [hτ4, hτ3, hk2]; omega
      · simp; omega
    · refine hcommon τ6 (by simp [hτ6, hτ4, hτ3, hx2]) (by simp [hτ6, hτ4, hτ3, hy2])
        (by simp [hτ6, hτ4, hτ3, hlf2]) (fun _ => by simp [hτ6, hτ4, hτ3, htg2]) (by simp [hτ6, hτ4, hτ3, hdd2])
        (hD τ2 τ6 (by simp [hτ6, hτ4, hτ3]) (by simp [hτ6, hτ4, hτ3]) (by simp [hτ6, hτ4, hτ3])
          (by simp [hτ6, hτ4, hτ3]) (by simp [hτ6, hτ4, hτ3]) hdat2)
        (by simp [hτ6]) (by simp [hτ6, hτ4]; omega) (by simp [hτ6])
        ?_ (by simp [hτ6, hτ4, hτ3, haa2, hnvm]) (by simp [hτ6, hτ4, hτ3, hst2])
        (by simp [hτ6, hτ4, hτ3, hln2])
      simp only [hτ6, vars_setVar, show ("dr" : String) = "kk" ↔ False by decide, if_false, if_true]
      constructor
      · intro h; exact absurd h (by omega)
      · intro h; exact absurd (hsome.mpr (h k (by omega))) hs

/-- Map all entries of the code at the frame `y`. -/
def atEntries (subCmd : Com) : Com := .while (.lt (.var "kk") (.var "lf")) (atEntry subCmd)

theorem atEntries_spec (subCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (B Ks : ℕ) (hF : HookFrame subCmd) (hS : SubOK subCmd sub Dat B Ks) (hD : DatOK Dat)
    (X : List ℕ) (f d : ℕ) (ws : List (List ℕ)) (Alen : ℕ)
    (hfX : f + 1 + xg X f ≤ X.length)
    (hX : ∀ v ∈ X, v < B) (hXB : X.length < B) (hdB : d < B)
    (hA : total ws + xg X f ≤ Alen) (hAB : total ws + xg X f < B) :
    Spec B (fun τ => AtEInv X f d (frWord X f) ws sub Dat Alen τ ∧ τ.vars "kk" = 0)
      (atEntries subCmd)
      (fun _ τ' => AtEInv X f d (frWord X f) ws sub Dat Alen τ' ∧
        τ'.vars "kk" = (frWord X f).length)
      ((Ks + 34) * xg X f + 4) := by
  have hwl : (frWord X f).length = xg X f := length_frWord hfX
  have := Spec.forRange (B := B) (c := atEntry subCmd)
    (P := fun τ => AtEInv X f d (frWord X f) ws sub Dat Alen τ ∧ τ.vars "kk" = 0) "kk" "lf"
    (AtEInv X f d (frWord X f) ws sub Dat Alen) (frWord X f).length (Ks + 30) ((Ks + 34) * xg X f + 4)
    (fun τ hI => by have := hI.2.2.2.2.2.2.1; omega) (fun τ hI => by rw [hI.2.2.1]; omega)
    (fun τ hI => hI.2.2.1) (fun τ hI => hI.2.2.2.2.2.2.1)
    (atEntry_spec subCmd sub Dat B Ks hF hS hD X f d ws Alen hfX hX hXB hdB hA hAB)
    (fun τ h => h.1) (fun τ h => by rw [h.2, hwl]; simp)
  exact this.post fun _ _ _ h => h

theorem atEntries_var {subCmd : Com} (hF : HookFrame subCmd) {y : String} (hy : y ∉ hookVars)
    (h2 : y ∉ ["ev", "ap", "dr", "kk"]) : y ∉ (atEntries subCmd).wvars := by
  simp only [atEntries, atEntry, Com.wvars, List.mem_append, List.mem_singleton, List.nil_append,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at h2 ⊢
  intro h
  have := hF.1 y
  simp_all

theorem atEntries_arr {subCmd : Com} (hF : HookFrame subCmd) {b : String} (hb : b ≠ "a") :
    b ∉ (atEntries subCmd).warrs := by
  simp only [atEntries, atEntry, Com.warrs, hF.2.1, List.mem_append, List.mem_singleton,
    List.not_mem_nil, List.nil_append, List.append_nil]
  simp [hb]

/-- The candidates from the first `j` atom codes of the list at `P`. -/
def atCands (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (P j : ℕ) : List (List ℕ) :=
  (List.range j).filterMap fun i => atomMap sub d (frWord X (frPos X P i))

theorem atCands_succ (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (P j : ℕ) :
    atCands sub d X P (j + 1) = atCands sub d X P j ++
      (atomMap sub d (frWord X (frPos X P j))).toList := by
  simp only [atCands, List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases atomMap sub d (frWord X (frPos X P j)) <;> simp

theorem atCands_full (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (P : ℕ) :
    atCands sub d X P (xg X P) = atomCands sub d X P := by
  simp only [atCands, atomCands, listWords, List.filterMap_map]
  rfl

/-- The candidates take at most the room of their frames. -/
theorem atCands_le (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (P : ℕ) :
    ∀ j, (atCands sub d X P j).length + total (atCands sub d X P j) + P + 1 ≤ frPos X P j
  | 0 => by simp [atCands, total, frPos, skipFr]
  | j + 1 => by
    have ih := atCands_le sub d X P j
    rw [atCands_succ]
    have h3 : frPos X P (j + 1) = frPos X P j + 1 + xg X (frPos X P j) := skipFr_succ' _ _ _
    cases hm : atomMap sub d (frWord X (frPos X P j)) with
    | none => simp; omega
    | some u =>
      have hu := length_atomMap hm
      have hfw : (frWord X (frPos X P j)).length ≤ xg X (frPos X P j) := by simp [frWord]
      simp [total_append, total_singleton]; omega

/-- Map one atom code and keep it unless it is dropped. -/
def atFrame (subCmd : Com) : Com :=
  .seq (.assign "lf" (.get "x" (.var "y")))
    (.seq (.ite (.lt (.lit 0) (.var "lf")) (.assign "tg" (.get "x" (.add (.var "y") (.lit 1)))) .skip)
      (.seq (.store "st" (.var "m") (.var "ap")) (.seq (.assign "dr" (.lit 0))
        (.seq (.assign "kk" (.lit 0)) (.seq (atEntries subCmd)
          (.seq (.ite (.eq (.var "dr") (.lit 0))
              (.seq (.store "ln" (.var "m") (.var "lf")) (.assign "m" (.add (.var "m") (.lit 1))))
              (.assign "ap" (.get "st" (.var "m"))))
            (.seq (.assign "y" (.add (.add (.var "y") (.var "lf")) (.lit 1)))
              (.assign "e2" (.add (.var "e2") (.lit 1))))))))))

/-- The invariant of the loop over the atom codes of the list at `P`. -/
def AtLInv (X : List ℕ) (P d : ℕ) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (Alen Slen : ℕ) (τ : Env) : Prop :=
  τ.arrs "x" = X ∧ τ.vars "dd" = d ∧ Dat τ ∧ τ.vars "e1" = xg X P ∧ τ.vars "e2" ≤ xg X P ∧
    τ.vars "y" = frPos X P (τ.vars "e2") ∧ τ.vars "m" = (atCands sub d X P (τ.vars "e2")).length ∧
    τ.vars "ap" = total (atCands sub d X P (τ.vars "e2")) ∧
    WordsAt (atCands sub d X P (τ.vars "e2")) τ ∧ (τ.arrs "a").length = Alen ∧
    (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen

theorem atFrame_spec (subCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (B Ks : ℕ) (hF : HookFrame subCmd) (hS : SubOK subCmd sub Dat B Ks) (hD : DatOK Dat)
    (X : List ℕ) (P d : ℕ) (Alen Slen : ℕ) (hLF : ListFacts X P)
    (hX : ∀ v ∈ X, v < B) (hXB : 2 * X.length + 2 < B) (hdB : d < B)
    (hA : X.length ≤ Alen) (hS' : X.length < Slen) :
    Spec B (fun τ => AtLInv X P d sub Dat Alen Slen τ ∧ τ.vars "e2" < xg X P) (atFrame subCmd)
      (fun τ τ' => AtLInv X P d sub Dat Alen Slen τ' ∧ τ'.vars "e2" = τ.vars "e2" + 1)
      ((Ks + 34) * X.length + 60) := by
  rintro τ ⟨⟨hxa, hdd, hdat, he1, he2le, hy, hm, hap, hwa, halen, hstl, hlnl⟩, hlt⟩
  obtain ⟨j, hjdef⟩ : ∃ j, τ.vars "e2" = j := ⟨_, rfl⟩
  rw [hjdef] at he2le hy hm hap hwa hlt
  have hCle := atCands_le sub d X P j
  have hsucc := atCands_succ sub d X P j
  obtain ⟨C, hC⟩ : ∃ C, atCands sub d X P j = C := ⟨_, rfl⟩
  rw [hC] at hm hap hwa hCle hsucc
  have hs1' : frPos X P (j + 1) = frPos X P j + 1 + xg X (frPos X P j) := skipFr_succ' _ _ _
  obtain ⟨f, hf⟩ : ∃ f, frPos X P j = f := ⟨_, rfl⟩
  rw [hf] at hy hCle hs1' hsucc
  obtain ⟨L, hL⟩ : ∃ L, xg X f = L := ⟨_, rfl⟩
  have hs1 : frPos X P (j + 1) = f + 1 + L := by rw [hs1', hL]
  have hle1 := (hLF.frPos_le (j + 1) (by omega)).2
  have hend := hLF.end_le
  have hfX : f + 1 + L ≤ X.length := by omega
  have hfX' : f + 1 + xg X f ≤ X.length := by rw [hL]; exact hfX
  have hwl : (frWord X f).length = L := by rw [length_frWord hfX', hL]
  have hLB : L < B := by rw [← hL]; exact xg_lt hX (by omega)
  -- lf := x[y]
  set τ1 := τ.setVar "lf" L with hτ1
  have hev1 : (Expr.get "x" (.var "y")).evalB B τ = some L := by
    simp only [evalB_get_iff, evalB_var_iff, hxa, hy]
    refine ⟨f, ⟨rfl, by omega⟩, ?_, hLB⟩
    simp only [← hL, xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show f < X.length by omega),
      Option.getD_some]
  -- the tag
  obtain ⟨τ2, hr2, htg2, hτ2v, hτ2a⟩ : ∃ τ2, Run B (.ite (.lt (.lit 0) (.var "lf"))
      (.assign "tg" (.get "x" (.add (.var "y") (.lit 1)))) .skip) τ1 τ2 10 ∧
      (0 < (frWord X f).length → τ2.vars "tg" = (frWord X f).headD 0) ∧ (∀ y, y ≠ "tg" → τ2.vars y = τ1.vars y) ∧
      (∀ b, τ2.arrs b = τ1.arrs b) := by
    by_cases hL0 : 0 < L
    · have hv : xg X (f + 1) < B := xg_lt hX (by omega)
      refine ⟨τ1.setVar "tg" (xg X (f + 1)), (Run.ite_true ?_ (Run.assign ?_)).mono (by simp),
        fun _ => by rw [frWord_headD (by rw [hL]; exact hL0)]; simp, fun y hy => by simp [hy], fun b => by simp⟩
      · simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨0, L, ⟨rfl, by omega⟩, ⟨by simp [hτ1], by simp [hτ1]; omega⟩, by simp [hL0]⟩
      · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        refine ⟨f + 1, ⟨f, 1, ⟨by simp [hτ1, hy], by simp [hτ1, hy]; omega⟩, ⟨rfl, by omega⟩, rfl,
          by omega⟩, ?_, hv⟩
        simp only [hτ1, arrs_setVar, hxa, xg, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show f + 1 < X.length by omega), Option.getD_some]
    · refine ⟨τ1, (Run.ite_false ?_ Run.skip).mono (by simp), fun h => by omega,
        fun _ _ => rfl, fun _ => rfl⟩
      simp only [evalB_condLt_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨0, L, ⟨rfl, by omega⟩, ⟨by simp [hτ1], by simp [hτ1]; omega⟩, by simp; omega⟩
  have hm2 : τ2.vars "m" = C.length := by rw [hτ2v _ (by decide)]; simp [hτ1, hm]
  have hap2 : τ2.vars "ap" = total C := by rw [hτ2v _ (by decide)]; simp [hτ1, hap]
  have hst2 : τ2.arrs "st" = τ.arrs "st" := by rw [hτ2a]; simp [hτ1]
  set τ5 := ((τ2.setArr "st" C.length (total C)).setVar "dr" 0).setVar "kk" 0 with hτ5
  have hr5a : Run B (.store "st" (.var "m") (.var "ap")) τ2 (τ2.setArr "st" C.length (total C)) 3 :=
    (Run.store (by simp [hm2]; omega) (by simp [hap2]; omega) (by rw [hst2, hstl]; omega)).mono (by simp)
  have hr5b : Run B (.assign "dr" (.lit 0)) (τ2.setArr "st" C.length (total C))
      ((τ2.setArr "st" C.length (total C)).setVar "dr" 0) 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have hr5c : Run B (.assign "kk" (.lit 0)) ((τ2.setArr "st" C.length (total C)).setVar "dr" 0) τ5 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have hI5 : AtEInv X f d (frWord X f) C sub Dat Alen τ5 := by
    refine ⟨by simp [hτ5, hτ2a, hτ1, hxa], by simp [hτ5, hτ2v, hτ1, hy], by simp [hτ5, hτ2v, hτ1, hwl],
      fun h => by rw [show τ5.vars "tg" = τ2.vars "tg" by simp [hτ5]]; exact htg2 h,
      by simp [hτ5, hτ2v, hτ1, hdd],
      hD τ τ5 (by simp [hτ5, hτ2v, hτ1]) (by simp [hτ5, hτ2v, hτ1]) (by simp [hτ5, hτ2v, hτ1])
        (by simp [hτ5, hτ2v, hτ1]) (by simp [hτ5, hτ2a, hτ1]) hdat,
      by simp [hτ5], by simp [hτ5, hτ2v, hτ1, hap], by simp [hτ5], by simp [hτ5],
      fun k hk => by simp [hτ5] at hk, ?_, by simp [hτ5, hτ2a, hτ1, halen]⟩
    exact hwa.set_st (v := total C) le_rfl (by simp [hτ5, hst2, hτ1]) (by simp [hτ5, hτ2a, hτ1])
      (by simp [hτ5, hτ2a, hτ1])
  obtain ⟨τ6, hr6, hI6, hk6⟩ := atEntries_spec subCmd sub Dat B Ks hF hS hD X f d C Alen hfX' hX
    (by omega) (by omega) (by rw [hL]; omega) (by rw [hL]; omega) τ5 ⟨hI5, by simp [hτ5]⟩
  rw [hL] at hr6
  obtain ⟨hx6, hy6, hlf6, -, hdd6, hdat6, -, hap6, hdr61, hdr6, hent6, hwa6, hal6⟩ := hI6
  rw [hk6] at hap6 hdr6 hent6
  have hv6 : ∀ y, y ∉ hookVars → y ∉ ["ev", "ap", "dr", "kk"] → τ6.vars y = τ5.vars y :=
    fun y h1 h2 => hr6.frame_var y (atEntries_var hF h1 h2)
  have ha6 : ∀ b, b ≠ "a" → τ6.arrs b = τ5.arrs b := fun b hb => hr6.frame_arr b (atEntries_arr hF hb)
  have hm6 : τ6.vars "m" = C.length := by rw [hv6 "m" (by decide) (by decide)]; simp [hτ5, hm2]
  have he16 : τ6.vars "e1" = xg X P := by
    rw [hv6 "e1" (by decide) (by decide)]; simp [hτ5, hτ2v, hτ1, he1]
  have he26 : τ6.vars "e2" = j := by
    rw [hv6 "e2" (by decide) (by decide)]; simp [hτ5, hτ2v, hτ1, hjdef]
  have hst6 : τ6.arrs "st" = (τ.arrs "st").set C.length (total C) := by
    rw [ha6 "st" (by decide)]; simp [hτ5, hst2]
  have hln6 : τ6.arrs "ln" = τ.arrs "ln" := by
    rw [ha6 "ln" (by decide)]; simp [hτ5, hτ2a, hτ1]
  have hstC : (τ6.arrs "st")[C.length]? = some (total C) := by
    rw [hst6, List.getElem?_set_self (by omega)]
  have hcost6 : (Ks + 34) * L + 4 ≤ (Ks + 34) * X.length := by
    have : L + 1 ≤ X.length := by omega
    have := Nat.mul_le_mul_left (Ks + 34) this
    rw [Nat.mul_add] at this; omega
  have hlf6' : τ6.vars "lf" = L := by rw [hlf6, hwl]
  have hy6' : τ6.vars "y" = f := hy6
  have hamap := atomMap_eq sub d (frWord X f)
  -- the final steps, common to both branches
  have hfin : ∀ τ7 : Env, ∀ K7, Run B (.ite (.eq (.var "dr") (.lit 0))
        (.seq (.store "ln" (.var "m") (.var "lf")) (.assign "m" (.add (.var "m") (.lit 1))))
        (.assign "ap" (.get "st" (.var "m")))) τ6 τ7 K7 → K7 ≤ 15 →
      τ7.arrs "x" = X → τ7.vars "dd" = d → Dat τ7 → τ7.vars "e1" = xg X P →
      τ7.vars "y" = f → τ7.vars "lf" = L → τ7.vars "e2" = j →
      τ7.vars "m" = (atCands sub d X P (j + 1)).length →
      τ7.vars "ap" = total (atCands sub d X P (j + 1)) →
      WordsAt (atCands sub d X P (j + 1)) τ7 → (τ7.arrs "a").length = Alen →
      (τ7.arrs "st").length = Slen → (τ7.arrs "ln").length = Slen →
      ∃ τ', Run B (atFrame subCmd) τ τ' ((Ks + 34) * X.length + 60) ∧
        AtLInv X P d sub Dat Alen Slen τ' ∧ τ'.vars "e2" = τ.vars "e2" + 1 := by
    intro τ7 K7 hr7 hK7 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    set τ9 := (τ7.setVar "y" (f + L + 1)).setVar "e2" (j + 1) with hτ9
    refine ⟨τ9, ?_, ?_, by simp [hτ9, hjdef]⟩
    · unfold atFrame
      refine (Run.seq (Run.assign hev1) (Run.seq hr2 (Run.seq hr5a (Run.seq hr5b (Run.seq hr5c
        (Run.seq hr6 (Run.seq hr7 (Run.seq (Run.assign (v := f + L + 1) ?_)
          (Run.assign (v := j + 1) ?_))))))))).mono ?_
      · simp [h5, h6]; exact ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩
      · have hc1 := (hLF.frPos_le (xg X P) le_rfl)
        simp [h7]; exact ⟨by omega, by omega, by omega⟩
      · simp only [Expr.size]; omega
    · refine ⟨by simp [hτ9, h1], by simp [hτ9, h2], hD τ7 τ9 (by simp [hτ9]) (by simp [hτ9])
        (by simp [hτ9]) (by simp [hτ9]) (by simp [hτ9]) h3, by simp [hτ9, h4], by simp [hτ9]; omega,
        by simp [hτ9, hs1]; omega, by simp [hτ9, h8], by simp [hτ9, h9], ?_, by simp [hτ9, h11],
        by simp [hτ9, h12], by simp [hτ9, h13]⟩
      simp only [hτ9, vars_setVar, if_true]
      exact h10.of_arrs (by simp) (by simp) (by simp)
  have hap6' : τ6.vars "ap" = total C + L := by rw [hap6, hwl]
  have hdat6' : ∀ ρ : Env, (∀ y, y ∈ ["g1", "g2", "g3", "g4"] → ρ.vars y = τ6.vars y) →
      ρ.arrs "gt" = τ6.arrs "gt" → Dat ρ := fun ρ hv ha =>
    hD τ6 ρ (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp)) ha hdat6
  have hdd6' : τ6.vars "dd" = d := hdd6
  have hx6' : τ6.arrs "x" = X := hx6
  by_cases hdr0 : τ6.vars "dr" = 0
  · -- the code is kept
    have hall := hdr6.mp hdr0
    set u := (List.range (frWord X f).length).map (mapVal sub ((frWord X f).headD 0) d (frWord X f)) with hu
    have hul : u.length = L := by simp [hu, hwl]
    have hsome : atomMap sub d (frWord X f) = some u := by rw [hamap, if_pos hall]
    rw [hsome] at hsucc
    simp only [Option.toList_some] at hsucc
    set τ7 := (τ6.setArr "ln" C.length L).setVar "m" (C.length + 1) with hτ7
    have hw7 : WordsAt (C ++ [u]) τ7 := by
      have h0 : WordsAt C τ7 := (hwa6.set_ln (v := L) le_rfl (by simp [hτ7]) (by simp [hτ7])
        (by simp [hτ7])).of_arrs rfl rfl rfl
      refine h0.snoc (by simp [hτ7, hstC]) ?_ ?_
      · simp [hτ7, hln6, hul]; rw [List.getElem?_set_self (by omega)]
      · intro k hk
        simp only [hτ7, arrs_setVar, arrs_setArr, show ("a" : String) = "ln" ↔ False by decide, if_false]
        rw [hent6 k (by rw [hul] at hk; rw [hwl]; exact hk)]
        simp [hu]
    refine hfin τ7 11 ?_ (by omega) (by simp [hτ7, hx6']) (by simp [hτ7, hdd6'])
      (hdat6' τ7 (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [hτ7])
        (by simp [hτ7]))
      (by simp [hτ7, he16]) (by simp [hτ7, hy6']) (by simp [hτ7, hlf6']) (by simp [hτ7, he26])
      (by rw [hsucc]; simp [hτ7]) (by rw [hsucc, total_append, total_singleton, hul]; simp [hτ7, hap6'])
      (by rw [hsucc]; exact hw7) (by simp [hτ7, hal6]) (by simp [hτ7, hst6, hstl])
      (by simp [hτ7, hln6, hlnl])
    refine (Run.ite_true ?_ (Run.seq (Run.store ?_ ?_ ?_) (Run.assign ?_))).mono (by simp)
    · simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨0, 0, ⟨hdr0.symm, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
    · simp [hm6]; omega
    · simp [hlf6']; omega
    · rw [hln6, hlnl]; omega
    · simp [hm6]; omega
  · -- the code is dropped
    have hnone : atomMap sub d (frWord X f) = none := by
      rw [hamap, if_neg (fun h => hdr0 (hdr6.mpr h))]
    rw [hnone] at hsucc
    simp only [Option.toList_none, List.append_nil] at hsucc
    set τ7 := τ6.setVar "ap" (total C) with hτ7
    refine hfin τ7 8 ?_ (by omega) (by simp [hτ7, hx6']) (by simp [hτ7, hdd6'])
      (hdat6' τ7 (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> simp [hτ7])
        (by simp [hτ7]))
      (by simp [hτ7, he16]) (by simp [hτ7, hy6']) (by simp [hτ7, hlf6']) (by simp [hτ7, he26])
      (by rw [hsucc]; simp [hτ7, hm6]) (by rw [hsucc]; simp [hτ7])
      (by rw [hsucc]; exact hwa6.of_arrs (by simp [hτ7]) (by simp [hτ7]) (by simp [hτ7]))
      (by simp [hτ7, hal6]) (by simp [hτ7, hst6, hstl]) (by simp [hτ7, hln6, hlnl])
    refine (Run.ite_false ?_ (Run.assign ?_)).mono (by simp)
    · simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
      refine ⟨τ6.vars "dr", 0, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hdr0]⟩
    · simp only [evalB_get_iff, evalB_var_iff]
      exact ⟨C.length, ⟨hm6.symm, by omega⟩, hstC, by omega⟩

/-- The candidates for the atoms of the node at `y`. -/
def atList (subCmd : Com) : Com :=
  .seq (.assign "e1" (.get "x" (.var "y"))) (.seq (.assign "y" (.add (.var "y") (.lit 1)))
    (.seq (.assign "e2" (.lit 0)) (.seq (.assign "m" (.lit 0)) (.seq (.assign "ap" (.lit 0))
      (.while (.lt (.var "e2") (.var "e1")) (atFrame subCmd))))))

/-- **The atom candidates.** `atList` leaves the candidates for the atoms
of the transformed node at `P` in the arrays `a`, `st`, `ln`, their number
in `m`, and the end of the list of atom codes in `y`. -/
theorem atList_spec (subCmd : Com) (sub : ℕ → ℕ → ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (B Ks : ℕ) (hF : HookFrame subCmd) (hS : SubOK subCmd sub Dat B Ks) (hD : DatOK Dat)
    (X : List ℕ) (P d : ℕ) (Alen Slen : ℕ) (hLF : ListFacts X P)
    (hX : ∀ v ∈ X, v < B) (hXB : 2 * X.length + 2 < B) (hdB : d < B)
    (hA : X.length ≤ Alen) (hS' : X.length < Slen) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "y" = P ∧ τ.vars "dd" = d ∧ Dat τ ∧
        (τ.arrs "a").length = Alen ∧ (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen)
      (atList subCmd)
      (fun _ τ' => τ'.arrs "x" = X ∧ τ'.vars "y" = listEnd X P ∧ τ'.vars "dd" = d ∧ Dat τ' ∧
        τ'.vars "m" = (atomCands sub d X P).length ∧ WordsAt (atomCands sub d X P) τ' ∧
        (τ'.arrs "a").length = Alen ∧ (τ'.arrs "st").length = Slen ∧ (τ'.arrs "ln").length = Slen)
      (((Ks + 34) * X.length + 64) * X.length + 30) := by
  rintro τ ⟨hxa, hy, hdd, hdat, hal, hstl, hlnl⟩
  have hc1 := hLF.frPos_le (xg X P) le_rfl
  have hend := hLF.end_le
  have hP0 := hLF.frPos_le 0 (Nat.zero_le _)
  have hcB : xg X P < B := xg_lt hX (by omega)
  set τ0 := ((((τ.setVar "e1" (xg X P)).setVar "y" (P + 1)).setVar "e2" 0).setVar "m" 0).setVar "ap" 0
    with hτ0
  have hI0 : AtLInv X P d sub Dat Alen Slen τ0 := by
    refine ⟨by simp [hτ0, hxa], by simp [hτ0, hdd],
      hD τ τ0 (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) hdat,
      by simp [hτ0], by simp [hτ0], by simp [hτ0, frPos, skipFr], by simp [hτ0, atCands],
      by simp [hτ0, atCands, total], ?_, by simp [hτ0, hal], by simp [hτ0, hstl], by simp [hτ0, hlnl]⟩
    simp only [hτ0, vars_setVar, if_true, show ("e2" : String) = "m" ↔ False by decide,
      show ("e2" : String) = "ap" ↔ False by decide, if_false]
    exact ⟨fun i hi => by simp [atCands] at hi, fun i hi => by simp [atCands] at hi,
      fun i hi => by simp [atCands] at hi⟩
  have hbody : Spec B (fun ρ => AtLInv X P d sub Dat Alen Slen ρ ∧
      (Cond.lt (.var "e2") (.var "e1")).evalB B ρ = some true) (atFrame subCmd)
      (fun ρ ρ' => AtLInv X P d sub Dat Alen Slen ρ' ∧ xg X P - ρ'.vars "e2" < xg X P - ρ.vars "e2")
      ((Ks + 34) * X.length + 60) :=
    (atFrame_spec subCmd sub Dat B Ks hF hS hD X P d Alen Slen hLF hX hXB hdB hA hS').conseq
      (fun ρ ⟨hI, hc⟩ => ⟨hI, by have := lt_of_condLt_true hc; rwa [hI.2.2.2.1] at this⟩)
      (fun ρ ρ' ⟨hI, hc⟩ ⟨hI', he⟩ => ⟨hI', by
        have := lt_of_condLt_true hc; rw [hI.2.2.2.1] at this; omega⟩) le_rfl
  have hK : ∀ ρ, ρ = τ0 → (1 + (Cond.lt (.var "e2") (.var "e1")).size + ((Ks + 34) * X.length + 60)) *
      (xg X P - ρ.vars "e2") + 1 + (Cond.lt (.var "e2") (.var "e1")).size ≤
      ((Ks + 34) * X.length + 64) * X.length + 4 := by
    intro ρ h; subst h
    have h0 : τ0.vars "e2" = 0 := by simp [hτ0]
    simp only [h0, Cond.size, Expr.size, Nat.sub_zero]
    have h2 : 1 + (1 + 1 + 1) + ((Ks + 34) * X.length + 60) = (Ks + 34) * X.length + 64 := by ring
    rw [h2]
    have := Nat.mul_le_mul_left ((Ks + 34) * X.length + 64) (show xg X P ≤ X.length by omega)
    omega
  obtain ⟨τ', hr, hI', hfalse⟩ := (Spec.while_count (B := B) (P := fun ρ => ρ = τ0)
    (b := .lt (.var "e2") (.var "e1")) (c := atFrame subCmd)
    (K := ((Ks + 34) * X.length + 64) * X.length + 4)
    (AtLInv X P d sub Dat Alen Slen) (fun ρ => xg X P - ρ.vars "e2") ((Ks + 34) * X.length + 60)
    (fun ρ hI => evalB_condLt_vars (by have := hI.2.2.2.2.1; omega) (by rw [hI.2.2.2.1]; omega))
    hbody (fun ρ h => h ▸ hI0) hK).run rfl
  obtain ⟨hx', hdd', hdat', he1', he2', hy', hm', hap', hw', hal', hst', hln'⟩ := hI'
  have hend' : τ'.vars "e2" = xg X P := by
    have := le_of_condLt_false hfalse; rw [he1'] at this; omega
  rw [hend', atCands_full] at hm' hw'
  refine ⟨τ', ?_, hx', by rw [hy', hend']; rfl, hdd', hdat', hm', hw', hal', hst', hln'⟩
  unfold atList
  refine (Run.seq (Run.assign (v := xg X P) ?_) (Run.seq (Run.assign (v := P + 1) ?_)
    (Run.seq (Run.assign (v := 0) ?_) (Run.seq (Run.assign (v := 0) ?_)
      (Run.seq (Run.assign (v := 0) ?_) hr))))).mono ?_
  · simp only [evalB_get_iff, evalB_var_iff, hxa, hy]
    refine ⟨P, ⟨rfl, by omega⟩, ?_, hcB⟩
    simp only [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show P < X.length by omega),
      Option.getD_some]
  · simp [hy]; omega
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega

end Lax185574Proofs.Words
