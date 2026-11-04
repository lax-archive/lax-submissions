import Lax185574Proofs.CompRam.SizeInv

/-!
A round of the stack machine of lem:compose keeps the size invariant
`ROKs`, if the answer is right (`round_ok`). The two ways of going on,
`advance` and `ret`, are `advance_ok` and `ret_ok`.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs

theorem length_toWord_le_of {ws : List (List ℕ)} {c : ℕ} (h : ∀ w ∈ ws, w.length ≤ c) :
    (toWord ws).length ≤ 1 + ws.length * (c + 1) := by
  rw [length_toWord_words]
  have : (ws.map fun w : List ℕ => w.length + 1).sum ≤ ws.length * (c + 1) := by
    have := List.sum_le_card_nsmul (ws.map fun w : List ℕ => w.length + 1) (c + 1)
      (fun x hx => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        have := h w hw; omega)
    simpa using this
  omega

theorem jList_lt (l1 l2 : ℕ) : ∀ e ∈ jList l1 l2, e < l1 + 1 + l2 := by
  intro e he
  simp only [jList, List.mem_map, List.mem_ofFn] at he
  obtain ⟨a, -, rfl⟩ := he
  exact a.isLt

theorem length_jList (l1 l2 : ℕ) : (jList l1 l2).length = l1 + l2 + 1 := by
  simp [jList]

section
variable {P : SzP}

theorem fok_ph3 {g : Fr} (h : FOK P { g with ph := 5 }) (hi : g.i < nA g + nB g) :
    FOK P { g with ph := 3 } where
  ar := h.ar
  rk := h.rk
  ph := by simp
  hd := fun _ => h.hd (by simp)
  A := h.A
  B := h.B
  SB := fun _ => h.SB (by simp)
  SA := fun _ => h.SA (by simp)
  AT := fun _ => h.AT (by simp)
  ex0 := fun h' => absurd h' (by simp)
  exl := h.exl
  exw := h.exw
  i34 := fun _ => hi
  i4 := fun h' => absurd h' (by simp)
  i5 := fun h' => absurd h' (by simp)
  sa0 := h.sa0
  sb0 := h.sb0
  at0 := h.at0

theorem fok_fresh {d kk l1 l2 : ℕ} {A B : List ℕ} (har : l1 + l2 ≤ kk) (hrk : kk + d ≤ P.K)
    (hA : NW d l1 A ∧ Small P.Λ P.B0 A) (hB : NW d l2 B ∧ Small P.Λ P.B0 B) :
    FOK P (fresh d kk l1 l2 A B) where
  ar := har
  rk := hrk
  ph := by simp [fresh]
  hd := fun h => absurd rfl h
  A := hA
  B := hB
  SB := fun h => absurd h (by simp [fresh])
  SA := fun h => absurd h (by simp [fresh])
  AT := fun h => absurd h (by simp [fresh])
  ex0 := fun _ => ⟨rfl, rfl⟩
  exl := by simp [fresh]
  exw := by simp [fresh]
  i34 := fun h => by simp [fresh] at h
  i4 := fun h => by simp [fresh] at h
  i5 := fun h => by simp [fresh] at h
  sa0 := ⟨by simp [fresh], by simp [fresh]⟩
  sb0 := ⟨by simp [fresh], by simp [fresh]⟩
  at0 := ⟨by simp [fresh], by simp [fresh]⟩

theorem small_infix {Λ B : ℕ} {u w : List ℕ} (h : u <:+: w) (hw : Small Λ B w) : Small Λ B u :=
  ⟨le_trans h.length_le hw.1, fun e he => hw.2 e (h.subset he)⟩

theorem fok_child {g : Fr} (h : FOK P { g with ph := 5 }) (hi : g.i < nA g + nB g) :
    FOK P (child g) := by
  have hd : 1 ≤ g.d := h.hd (by simp)
  have hA := h.A
  have hB := h.B
  have hSA := h.SA (by simp)
  have hSB := h.SB (by simp)
  have har := h.ar
  have hrk := h.rk
  simp only at hA hB hSA hSB har hrk
  rw [show g.d = g.d - 1 + 1 by omega] at hA hB
  by_cases hiA : g.i < nA g
  · rw [child_lt _ hiA]
    obtain ⟨c1, c2⟩ := nw_child hA.1 hiA
    exact fok_fresh (by omega) (by omega) ⟨c1, small_infix c2 hA.2⟩ hSB
  · rw [child_ge _ hiA]
    have hj : g.i - nA g < (extsOf g.B).length := by simp only [nA, nB] at hi hiA ⊢; omega
    obtain ⟨c1, c2⟩ := nw_child hB.1 hj
    exact fok_fresh (by omega) (by omega) hSA ⟨c1, small_infix c2 hB.2⟩

/-- **Going on with the next extension.** -/
theorem advance_ok {g : Fr} {S : List Fr} (hc : Chain P.q (g :: S)) (hS : ∀ f ∈ S, FOK P f)
    (hS3 : ∀ f ∈ S, f.ph = 3) (hg : FOK P { g with ph := 5 }) : ROKs P (advance g S) := by
  by_cases hi : g.i < nA g + nB g
  · rw [advance_lt _ _ hi]
    have hd : 1 ≤ g.d := hg.hd (by simp)
    refine ⟨⟨⟨?_, chain_top hc rfl⟩, ?_, ?_⟩, _, _, rfl, Or.inl ⟨child_ph g, rfl⟩⟩
    · have := (child_rank g).2.1; simp only; omega
    · intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | rfl | hf
      · exact fok_child hg hi
      · exact fok_ph3 hg hi
      · exact hS f hf
    · intro f hf
      simp only [List.tail_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · rfl
      · exact hS3 f hf
  · rw [advance_ge _ _ hi]
    refine ⟨⟨chain_top hc rfl, ?_, ?_⟩, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    · intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact hg
      · exact hS f hf
    · intro f hf
      exact hS3 f hf

/-- **Handing a result down.** -/
theorem ret_ok (hP : P.Λ + P.K + 3 ≤ P.B0) {f : Fr} {S : List Fr} {R : List ℕ}
    (hc : Chain P.q (f :: S)) (hS : ∀ p ∈ S, FOK P p) (hS3 : ∀ p ∈ S, p.ph = 3)
    (hR : Small (P.F f.d) P.B1 R) (hf : f.kk + f.d ≤ P.K) (hfl : f.l1 + f.l2 ≤ f.kk) :
    ROKs P (ret R [f.kk, f.d, f.l1 + f.l2] S) := by
  have hB1 : P.B0 + P.K + 1 ≤ P.B1 := by simp only [SzP.B1]; omega
  cases S with
  | nil =>
    have hq : f.d = P.q := by simpa using chain_length hc
    refine ⟨?_, fun e he => ?_⟩
    · have := hR.1; have := P.F_mono (le_of_eq hq); simp; omega
    · simp only [List.cons_append, List.nil_append, List.mem_cons] at he
      rcases he with rfl | rfl | rfl | he
      · omega
      · omega
      · omega
      · exact hR.2 e he
  | cons p S =>
    obtain ⟨hc', hpd⟩ := chain_pop hc
    have hp := hS p (by simp)
    have hp3 := hS3 p (by simp)
    have hS' : ∀ g ∈ S, FOK P g := fun g hg => hS g (by simp [hg])
    have hS3' : ∀ g ∈ S, g.ph = 3 := fun g hg => hS3 g (by simp [hg])
    have hd1 : p.d - 1 = f.d := by omega
    by_cases hi : p.i < nA p
    · rw [ret_lt _ _ _ _ hi]
      have hp4 : FOK P { p with ph := 4 } :=
        { ar := hp.ar, rk := hp.rk, ph := by simp, hd := fun _ => hp.hd (by omega), A := hp.A,
          B := hp.B, SB := fun _ => hp.SB (by omega), SA := fun _ => hp.SA (by omega),
          AT := fun _ => hp.AT (by omega), ex0 := fun h => absurd h (by simp), exl := hp.exl,
          exw := hp.exw, i34 := fun _ => hp.i34 (Or.inl hp3), i4 := fun _ => hi,
          i5 := fun h => absurd h (by simp), sa0 := hp.sa0, sb0 := hp.sb0, at0 := hp.at0 }
      refine ⟨⟨chain_top hc' rfl, ?_, ?_⟩, _, _, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, R, by simp only; rw [hd1]; exact hR, rfl⟩)))⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact hp4
        · exact hS' g hg
      · intro g hg; exact hS3' g hg
    · rw [ret_ge _ _ _ _ hi]
      have hi' := hp.i34 (Or.inl hp3)
      have hdp : 1 ≤ p.d := hp.hd (by omega)
      have hBp := hp.B
      rw [show p.d = p.d - 1 + 1 by omega] at hBp
      have hj : p.i - nA p < (extsOf p.B).length := by
        simp only [nA, nB] at hi' hi ⊢; omega
      have hhd := hBp.2.2 _ (ext_head_mem hBp.1 hj)
      have hl1 : p.l1 ≤ P.K := by have := hp.ar; have := hp.rk; omega
      refine advance_ok (chain_top hc' rfl) hS' hS3' ?_
      have hexl := hp.exl
      refine ⟨hp.ar, hp.rk, by simp, fun _ => hdp, hp.A, hp.B, fun _ => hp.SB (by omega),
        fun _ => hp.SA (by omega), fun _ => hp.AT (by omega), fun h => absurd h (by simp), ?_, ?_,
        fun h => by simp at h, fun h => by simp at h, fun _ => ?_, hp.sa0, hp.sb0, hp.at0⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hp.exw e he
        · refine ⟨?_, fun v hv => ?_⟩
          · simp only [List.length_cons]; rw [hd1]; have := hR.1; omega
          · simp only [List.mem_cons] at hv
            rcases hv with rfl | hv
            · omega
            · exact hR.2 v hv
      · simp only [nA, nB] at hi' ⊢; omega

end

end Lax185574Proofs.CompRam
