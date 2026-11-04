import Lax185574Proofs.CompRam.SizeStep

/-!
**A round keeps the size invariant** (`round_ok`), by the phase of the
top frame.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs

variable {P : SzP} {n : ℕ} {G : PartialGraph (Fin n)}

/-- The answer of a rank shift of a node word of a frame. -/
theorem sh_ans (hP : P.Λ + P.K + 3 ≤ P.B0) {kk d l : ℕ} {X b : List ℕ}
    (hX : Small P.Λ P.B0 X) (hk : kk + d ≤ P.K) (hl : l ≤ P.K)
    (hA : Ans G (.sh ([kk, d, l] ++ X)) b) :
    NW (d - 1) l (b.drop 3) ∧ Small P.Λ P.B0 (b.drop 3) := by
  obtain ⟨kk', d', l', u, h1, hl', hw, rfl⟩ := hA
  rw [toWord_tree_eq] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hw
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hw
  rw [toWord_tree_eq]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
    Nat.add_sub_cancel]
  have hs := hX
  obtain ⟨b1, b2⟩ := sh_bound G _ _ u h1 P.B0 hs.2 (by have := hs.1; omega) (by omega)
    (by omega) (by omega)
  exact ⟨⟨_, rfl⟩, by have := hs.1; omega, b2⟩

theorem exw_new {kk d l1 l2 h : ℕ} {R b : List ℕ} (hP : P.Λ + P.K + 3 ≤ P.B0)
    (hR : Small (P.F (d - 1)) P.B1 R) (hd : d ≤ P.q) (hk : kk + d ≤ P.K) (hl : l1 + l2 ≤ kk)
    (hh : h < P.B0)
    (hA : Ans G (.re ([kk + 1, d - 1, l1 + 1 + l2] ++ R ++ ((l1 + l2 + 1) :: jList l1 l2))) b) :
    Small (P.F (d - 1) + P.K + 8) P.B1 (h :: b.drop 3) := by
  obtain ⟨kk', d', l, u, J, hlk, hJ, hw, rfl⟩ := hA
  have e1 : toWord (tree G kk' d' u, J) = [kk', d', l] ++ toWord (node G kk' d' u) ++ toWord J := rfl
  rw [e1] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, List.append_assoc] at hw
  obtain ⟨rfl, rfl, rfl, hw⟩ := hw
  have hF := P.F_le_LX (d - 1) (by omega)
  have hB1 : P.B0 + P.K + 1 ≤ P.B1 := by simp only [SzP.B1]; omega
  have hpre : toWord (node G (kk + 1) (d - 1) u) <+: R ++ ((l1 + l2 + 1) :: jList l1 l2) := by
    rw [hw]; exact List.prefix_append _ _
  have hlen := hpre.length_le
  simp only [List.length_append, List.length_cons, length_jList] at hlen
  have hent : ∀ v ∈ toWord (node G (kk + 1) (d - 1) u), v < P.B1 := by
    intro v hv
    rcases List.mem_append.1 (hpre.subset hv) with hv | hv
    · exact hR.2 v hv
    · simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · omega
      · have := jList_lt l1 l2 v hv; omega
  have hR1 := hR.1
  have hB1' : P.F (d - 1) + P.K + 3 ≤ P.B1 := by
    have := P.F_mono (show d - 1 ≤ P.q by omega); simp only [SzP.B1]; omega
  obtain ⟨b1, b2⟩ := re_bound G (kk + 1) (d - 1) u J hJ P.B1 hent (by omega) (by omega) (by omega)
    (by omega)
  refine ⟨?_, fun v hv => ?_⟩
  · simp only [List.length_cons, List.length_drop]; omega
  · simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · omega
    · exact b2 v (List.mem_of_mem_drop hv)

/-- **A round keeps the size invariant.** -/
theorem round_ok (hP : P.Λ + P.K + 3 ≤ P.B0) {S : List Fr} {q : Qry} {b : List ℕ}
    (h : ROKs P (.call S q)) (hA : Ans G q b) : ROKs P (round S b) := by
  obtain ⟨⟨hc, hS, hS3⟩, f, S', rfl, hq⟩ := h
  have hf := hS f (by simp)
  have hS' : ∀ g ∈ S', FOK P g := fun g hg => hS g (by simp [hg])
  have hS3' : ∀ g ∈ S', g.ph = 3 := fun g hg => hS3 g (by simpa using hg)
  have hB1 : P.B0 + P.K + 1 ≤ P.B1 := by simp only [SzP.B1]; omega
  have hLX : 2 * P.Λ + 2 ≤ P.B1 := by simp only [SzP.B1, SzP.LX]; omega
  have hdq : f.d ≤ P.q := by have := chain_length hc; omega
  have har := hf.ar
  have hrk := hf.rk
  rcases hq with ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩ | ⟨h4, R, hR, rfl⟩ | ⟨h5, rfl⟩
  · -- the atoms
    simp only [Ans] at hA
    subst hA
    have hb := sd_small (atomsQ_small hf) (by omega)
    by_cases hd : f.d = 0
    · rw [round_ph0_zero f S' _ h0 hd]
      have := ret_ok hP hc hS' hS3' (R := toWord (sortedDistinct (atomsQ f)))
        (hb.mono (by rw [hd]; have := P.F_zero; omega) le_rfl) hrk har
      rwa [hd] at this
    · rw [round_ph0_succ f S' _ h0 hd]
      refine ⟨⟨chain_top hc rfl, ?_, hS3'⟩, _, _, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨hf.ar, hf.rk, by simp, fun _ => Nat.one_le_iff_ne_zero.2 hd, hf.A, hf.B, fun h => by simp at h,
          fun h => by simp at h, fun _ => hb.mono (by omega) le_rfl, fun _ => hf.ex0 (by omega),
          hf.exl, hf.exw, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
          hf.sa0, hf.sb0, hb.mono (by omega) le_rfl⟩
      · exact hS' g hg
  · -- the shift of the second node
    obtain ⟨c1, c2⟩ := sh_ans hP hf.B.2 hrk (by omega) hA
    rw [round_ph1 f S' b h1]
    refine ⟨⟨chain_top hc rfl, ?_, hS3'⟩, _, _, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨hf.ar, hf.rk, by simp, fun _ => hf.hd (by omega), hf.A, hf.B, fun _ => ⟨c1, c2⟩,
        fun h => by simp at h, fun _ => hf.AT (by omega), fun _ => hf.ex0 (by omega),
        hf.exl, hf.exw, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
        hf.sa0, c2, hf.at0⟩
    · exact hS' g hg
  · -- the shift of the first node
    have hl1 : f.l1 ≤ P.K := by omega
    obtain ⟨c1, c2⟩ := sh_ans hP hf.A.2 hrk hl1 hA
    rw [round_ph2 f S' b h2]
    have hex := hf.ex0 (by omega)
    refine advance_ok (chain_top hc rfl) hS' hS3' ⟨hf.ar, hf.rk, by simp, fun _ => hf.hd (by omega),
      hf.A, hf.B, fun _ => hf.SB (by omega), fun _ => ⟨c1, c2⟩, fun _ => hf.AT (by omega),
      fun h => by simp at h, by simp [hex.1], by simp [hex.1], fun h => by simp at h,
      fun h => by simp at h, fun _ => by simp, c2, hf.sb0, hf.at0⟩
  · -- the restriction of the result of a child
    rw [round_ph4 f S' b h4]
    have hd1 : 1 ≤ f.d := hf.hd (by omega)
    have hiA := hf.i4 h4
    have hAw := hf.A
    rw [show f.d = f.d - 1 + 1 by omega] at hAw
    have hhd := hAw.2.2 _ (ext_head_mem hAw.1 hiA)
    have hnew := exw_new hP hR hdq hrk har hhd hA
    have hi34 := hf.i34 (Or.inr h4)
    have hexl := hf.exl
    refine advance_ok (chain_top hc rfl) hS' hS3' ⟨hf.ar, hf.rk, by simp, fun _ => hd1,
      hf.A, hf.B, fun _ => hf.SB (by omega), fun _ => hf.SA (by omega), fun _ => hf.AT (by omega),
      fun h => by simp at h, by simp; omega, ?_, fun h => by simp at h,
      fun h => by simp at h, fun _ => by simp only [nA, nB] at hi34 ⊢; omega, hf.sa0, hf.sb0,
      hf.at0⟩
    intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hf.exw e he
    · exact hnew
  · -- the canonical form of the extensions
    simp only [Ans] at hA
    subst hA
    rw [round_ph5 f S' _ h5]
    have hd1 : 1 ≤ f.d := hf.hd (by omega)
    have hi := hf.i5 h5
    have hnA := nA_lt hf hd1
    have hnB := nB_lt hf hd1
    have hexl := hf.exl
    have hEX : Small P.LX P.B1 (toWord f.EX) := by
      have hl := length_toWord_le_of (c := P.F (f.d - 1) + P.K + 8) (fun w hw => (hf.exw w hw).1)
      have hF := P.F_mono (show f.d - 1 ≤ P.q by omega)
      refine ⟨?_, toWord_lt (by simp only [SzP.B1, SzP.LX]; nlinarith) fun w hw =>
        ⟨by have := (hf.exw w hw).1; simp only [SzP.B1]; omega, (hf.exw w hw).2⟩⟩
      have : f.EX.length * (P.F (f.d - 1) + P.K + 8 + 1) ≤ 2 * P.Λ * (P.F P.q + P.K + 9) := by
        have h1 : f.EX.length ≤ 2 * P.Λ := by omega
        have h2 : P.F (f.d - 1) + P.K + 8 + 1 ≤ P.F P.q + P.K + 9 := by omega
        exact Nat.mul_le_mul h1 h2
      simp only [SzP.LX]; omega
    have hb := sd_small hEX (by simp only [SzP.B1]; omega)
    have hAT := hf.AT (by omega)
    refine ret_ok hP hc hS' hS3' ⟨?_, fun e he => ?_⟩ hrk har
    · have hs := P.F_succ (f.d - 1)
      rw [show f.d - 1 + 1 = f.d by omega] at hs
      have hl := length_toWord_le_of (c := P.F (f.d - 1) + P.K + 8) (fun w hw => (hf.exw w hw).1)
      have hlb := length_toWord_sortedDistinct_le f.EX
      have : f.EX.length * (P.F (f.d - 1) + P.K + 8 + 1) ≤ 2 * P.Λ * (P.F (f.d - 1) + P.K + 9) :=
        Nat.mul_le_mul (by omega) (by omega)
      have := hAT.1
      simp only [List.length_append]; omega
    · rcases List.mem_append.1 he with he | he
      · exact hAT.2 e he
      · exact hb.2 e he

end Lax185574Proofs.CompRam
