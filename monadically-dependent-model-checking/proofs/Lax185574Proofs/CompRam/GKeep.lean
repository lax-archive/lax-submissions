import Lax185574Proofs.CompRam.GPure

/-!
The descriptions of segments and frames of the glue command of
lem:compose survive commands that leave their scalars and the array `x`
alone, and segments can be shortened at the front.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding

/-- The scalars that a frame description reads. -/
def slotVars : List String :=
  ["gd", "gk", "g1", "g2", "gp", "gi", "gAs", "gAl", "gBs", "gBl", "gSs", "gSl", "gTs", "gTl", "gUs",
    "gUl", "gEs", "gEl", "gx", "gg", "r1s", "r1l", "r2s", "r2l"]

/-- The scalars that the description of `EX` reads. -/
def exVars : List String := ["gEs", "gEl", "gx", "gg", "r1s", "r1l", "r2s", "r2l"]

/-- The scalars that a new frame description reads. -/
def freshVars : List String := ["cd", "ck", "c1", "c2", "cAs", "cAl", "cBs", "cBl"]

theorem SegIs.of_eq {M : ℕ} {σ σ' : Env} {s l : String} {w : List ℕ} (h : SegIs M σ s l w)
    (hs : σ'.vars s = σ.vars s) (hl : σ'.vars l = σ.vars l) (hx : σ'.arrs "x" = σ.arrs "x") :
    SegIs M σ' s l w := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hl, h1], by rw [hs]; exact h2, by rw [hs, hx]; exact h3⟩

theorem SegIs.ofr {M : ℕ} {σ σ' : Env} {xs : List String} {s l : String} {w : List ℕ}
    (h : SegIs M σ s l w) (hf : OFr σ σ' xs) (hs : s ∉ xs) (hl : l ∉ xs) : SegIs M σ' s l w :=
  h.of_eq (hf.vars s hs) (hf.vars l hl) (hf.arrs "x" (by decide))

theorem SegIs.drop_eq {M : ℕ} {σ : Env} {s l : String} {w : List ℕ} (h : SegIs M σ s l w) :
    (σ.arrs "x").drop (σ.vars s) = w ++ (σ.arrs "x").drop (σ.vars s + w.length) := by
  obtain ⟨-, -, h3⟩ := h
  conv_lhs => rw [← List.take_append_drop w.length ((σ.arrs "x").drop (σ.vars s))]
  rw [show ((σ.arrs "x").drop (σ.vars s)).take w.length = w from h3, List.drop_drop]

/-- A segment holding `w` gives one holding `w.drop k` from `k` cells on. -/
theorem seg_drop_front {X w : List ℕ} {s k : ℕ} (h : seg X s w.length = w) :
    seg X (s + k) (w.length - k) = w.drop k := by
  have h' : (X.drop s).take w.length = w := h
  have e : X.drop (s + k) = (X.drop s).drop k := by rw [List.drop_drop, Nat.add_comm]
  simp only [seg]
  rw [e, ← List.drop_take, h']

/-- A segment of `x` given by values. -/
theorem segIs_of {M : ℕ} {σ : Env} {s l : String} {w : List ℕ} {a : ℕ}
    (hs : σ.vars s = a) (hl : σ.vars l = w.length) (hM : a + w.length ≤ M)
    (hw : seg (σ.arrs "x") a w.length = w) : SegIs M σ s l w :=
  ⟨hl, by rw [hs]; exact hM, by rw [hs]; exact hw⟩

theorem ExIs.ofr {M : ℕ} {σ σ' : Env} {xs : List String} {EX : List (List ℕ)} (h : ExIs M σ EX)
    (hf : OFr σ σ' xs) (hxs : ∀ y ∈ exVars, y ∉ xs) : ExIs M σ' EX := by
  have hv : ∀ y ∈ exVars, σ'.vars y = σ.vars y := fun y hy => hf.vars y (hxs y hy)
  rcases h with ⟨h0, hE⟩ | ⟨h0, hg, E0, R1, R2, hEX, hE, h1, h2⟩
  · exact Or.inl ⟨by rw [hv "gx" (by decide)]; exact h0,
      hE.ofr hf (hxs _ (by decide)) (hxs _ (by decide))⟩
  · refine Or.inr ⟨by rw [hv "gx" (by decide)]; exact h0, by rw [hv "gg" (by decide)]; exact hg,
      E0, R1, R2, by rw [hv "gg" (by decide)]; exact hEX, hE.ofr hf (hxs _ (by decide)) (hxs _ (by decide)),
      h1.ofr hf (hxs _ (by decide)) (hxs _ (by decide)), h2.ofr hf (hxs _ (by decide)) (hxs _ (by decide))⟩

theorem SlotIs.ofr {M : ℕ} {σ σ' : Env} {xs : List String} {f : Fr} (h : SlotIs M σ f)
    (hf : OFr σ σ' xs) (hxs : ∀ y ∈ slotVars, y ∉ xs) : SlotIs M σ' f := by
  have hv : ∀ y ∈ slotVars, σ'.vars y = σ.vars y := fun y hy => hf.vars y (hxs y hy)
  exact ⟨by rw [hv "gd" (by decide)]; exact h.d, by rw [hv "gk" (by decide)]; exact h.kk,
    by rw [hv "g1" (by decide)]; exact h.l1, by rw [hv "g2" (by decide)]; exact h.l2,
    by rw [hv "gp" (by decide)]; exact h.ph, by rw [hv "gi" (by decide)]; exact h.i, h.nums,
    h.A.ofr hf (hxs _ (by decide)) (hxs _ (by decide)), h.B.ofr hf (hxs _ (by decide)) (hxs _ (by decide)),
    h.SA.ofr hf (hxs _ (by decide)) (hxs _ (by decide)), h.SB.ofr hf (hxs _ (by decide)) (hxs _ (by decide)),
    h.AT.ofr hf (hxs _ (by decide)) (hxs _ (by decide)),
    h.EX.ofr hf (fun y hy => hxs y (by
      simp only [exVars, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))⟩

theorem FreshIs.ofr {M : ℕ} {σ σ' : Env} {xs : List String} {d kk l1 l2 : ℕ} {A B : List ℕ}
    (h : FreshIs M σ d kk l1 l2 A B) (hf : OFr σ σ' xs) (hxs : ∀ y ∈ freshVars, y ∉ xs) :
    FreshIs M σ' d kk l1 l2 A B := by
  have hv : ∀ y ∈ freshVars, σ'.vars y = σ.vars y := fun y hy => hf.vars y (hxs y hy)
  exact ⟨by rw [hv "cd" (by decide)]; exact h.hd, by rw [hv "ck" (by decide)]; exact h.hk,
    by rw [hv "c1" (by decide)]; exact h.h1, by rw [hv "c2" (by decide)]; exact h.h2, h.nums,
    h.hA.ofr hf (hxs _ (by decide)) (hxs _ (by decide)), h.hB.ofr hf (hxs _ (by decide)) (hxs _ (by decide))⟩

/-- A frame description with some scalars changed. -/
theorem SlotIs.setVar {M : ℕ} {σ : Env} {f : Fr} (h : SlotIs M σ f) {y : String}
    (hy : y ∉ slotVars) (v : ℕ) : SlotIs M (σ.setVar y v) f :=
  h.ofr (OFr.setVar σ y v) (fun z hz hz' => by simp at hz'; subst hz'; exact hy hz)

theorem FreshIs.setVar {M : ℕ} {σ : Env} {d kk l1 l2 : ℕ} {A B : List ℕ}
    (h : FreshIs M σ d kk l1 l2 A B) {y : String} (hy : y ∉ freshVars) (v : ℕ) :
    FreshIs M (σ.setVar y v) d kk l1 l2 A B :=
  h.ofr (OFr.setVar σ y v) (fun z hz hz' => by simp at hz'; subst hz'; exact hy hz)

theorem SegIs.setVar {M : ℕ} {σ : Env} {s l : String} {w : List ℕ} (h : SegIs M σ s l w) {y : String}
    (hs : y ≠ s) (hl : y ≠ l) (v : ℕ) : SegIs M (σ.setVar y v) s l w :=
  h.of_eq (by simp [Ne.symm hs]) (by simp [Ne.symm hl]) (by simp)

theorem Filled.ofr {l : List ℕ} {σ σ' : Env} {xs : List String} (h : Filled "OB" "po" l σ)
    (hf : OFr σ σ' xs) (hpo : "po" ∉ xs) (hob : σ'.arrs "OB" = σ.arrs "OB") : Filled "OB" "po" l σ' :=
  h.congr (hf.vars "po" hpo) hob

end Lax185574Proofs.CompRam
