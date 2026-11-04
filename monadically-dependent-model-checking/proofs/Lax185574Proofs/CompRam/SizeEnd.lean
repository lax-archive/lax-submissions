import Lax185574Proofs.CompRam.SizeAll

/-!
**The sizes along the script of an instance** (`size_ok`), from the
size invariant on the trajectory (`traj_ok`).
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim

theorem qWord_len_ent {q : Qry} {N : ℕ} (h : ∀ e ∈ realQ q, e < N) (hN : 8000 ≤ N) :
    (qWord q).length ≤ (realQ q).length + 40010 ∧
      ∀ e ∈ qWord q, e < N + (realQ q).length + 40010 := by
  have hS := length_dSq_le
  have hR : dRq.length = 5 := by rw [dRq_eq]; rfl
  have hR0 : ∀ e ∈ dRq, e = 0 := by rw [dRq_eq]; simp
  have hq := dSq_lt
  rw [qWord_parts]
  have hl := Lax185574Proofs.MC.swIn_length_le (qR q) (qS q) (qC q)
  refine ⟨?_, fun e he => ?_⟩
  · rw [hl]; cases q <;> simp [qR, qS, qC, realQ] <;> omega
  · simp only [swIn, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    cases q with
    | re w =>
      simp only [qR, qS, qC, realQ] at he h ⊢
      rcases he with (((rfl | rfl | rfl) | he) | he) | he
      · omega
      · omega
      · simp
      · have := h e he; omega
      · have := hq e he; omega
      · simp at he <;> omega
    | sh w =>
      simp only [qR, qS, qC, realQ] at he h ⊢
      rcases he with (((rfl | rfl | rfl) | he) | he) | he
      · omega
      · omega
      · simp
      · rw [hR0 e he]; omega
      · have := h e he; omega
      · simp at he <;> omega
    | ca ws =>
      simp only [qR, qS, qC, realQ] at he h ⊢
      rcases he with (((rfl | rfl | rfl) | he) | he) | he
      · omega
      · omega
      · omega
      · rw [hR0 e he]; omega
      · have := hq e he; omega
      · have := h e he; omega

theorem ansWord_len_ent {q : Qry} {b : List ℕ} {N : ℕ} (h : ∀ e ∈ b, e < N) (hN : 8000 ≤ N) :
    (ansWord q b).length ≤ b.length + 40010 ∧ ∀ e ∈ ansWord q b, e < N := by
  have hS := length_dSa_le
  have ha := dSa_lt
  have hR : dRa = [0, 0, 0, 0] := dRa_eq
  cases q with
  | re w =>
    refine ⟨by simp [ansWord]; omega, fun e he => ?_⟩
    simp only [ansWord, List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | rfl
    · exact h e he
    · have := ha e he; omega
    · omega
  | sh w =>
    refine ⟨by simp [ansWord, hR] <;> omega, fun e he => ?_⟩
    simp only [ansWord, List.mem_append, List.mem_singleton, hR] at he
    rcases he with (he | he) | rfl
    · simp at he <;> omega
    · exact h e he
    · omega
  | ca ws =>
    refine ⟨by simp [ansWord, hR]; omega, fun e he => ?_⟩
    simp only [ansWord, List.mem_append, hR] at he
    rcases he with (he | he) | he
    · simp at he <;> omega
    · have := ha e he; omega
    · exact h e he

section
variable {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
  {u₂ : Fin l2 → Fin n}

theorem xT_eq : xT G k q u₁ u₂ =
    [k, q, l1] ++ toWord (node G k q u₁) ++ [k, q, l2] ++ toWord (node G k q u₂) := rfl

/-- **The trajectory is good.** -/
theorem traj_ok (hI : Inst G k q u₁ u₂) {m : ℕ}
    (hcall : ∀ j < m, ∃ g S q', trT G k q u₁ u₂ j = .call (g :: S) q' ∧ Fits g.ph q' ∧
      Ans G q' (ansOf G q') ∧ RankLe (k + q + 1) q') :
    ∀ j ≤ m, ROKs (szP G k q u₁ u₂) (trT G k q u₁ u₂ j) := by
  obtain ⟨h1, h2, hk, -⟩ := hI
  have hP : (szP G k q u₁ u₂).Λ + (szP G k q u₁ u₂).K + 3 ≤ (szP G k q u₁ u₂).B0 := by
    simp only [szP]; omega
  intro j
  induction j with
  | zero =>
    intro _
    have hX : ∀ v ∈ toWord (node G k q u₁), v ∈ xT G k q u₁ u₂ := fun v hv => by
      rw [xT_eq]; simp [hv]
    have hY : ∀ v ∈ toWord (node G k q u₂), v ∈ xT G k q u₁ u₂ := fun v hv => by
      rw [xT_eq]; simp [hv]
    have hlX : (toWord (node G k q u₁)).length ≤ (xT G k q u₁ u₂).length := by
      rw [xT_eq]; simp; omega
    have hlY : (toWord (node G k q u₂)).length ≤ (xT G k q u₁ u₂).length := by
      rw [xT_eq]; simp; omega
    have hf := fok_fresh (P := szP G k q u₁ u₂) (d := q) (kk := k) (l1 := l1) (l2 := l2)
      (A := toWord (node G k q u₁)) (B := toWord (node G k q u₂)) hk (by simp only [szP]; omega)
      ⟨⟨_, rfl⟩, hlX, fun e he => by have := le_maxEntry (hX e he); simp only [szP]; omega⟩
      ⟨⟨_, rfl⟩, hlY, fun e he => by have := le_maxEntry (hY e he); simp only [szP]; omega⟩
    refine ⟨⟨rfl, fun f hf' => ?_, fun f hf' => by simp at hf'⟩, _, [], rfl, Or.inl ⟨rfl, rfl⟩⟩
    simp only [List.mem_singleton] at hf'
    subst hf'
    exact hf
  | succ j ih =>
    intro hj
    obtain ⟨g, S, q', htr, -, hA, -⟩ := hcall j (by omega)
    have := ih (by omega)
    rw [show trT G k q u₁ u₂ (j + 1) = round (g :: S) (ansOf G q') by
      unfold trT; rw [traj_succ]; unfold trT at htr; rw [htr]; rfl]
    rw [htr] at this
    exact round_ok hP this hA

/-- **The sizes along the script.** -/
theorem size_ok (hI : Inst G k q u₁ u₂) {m : ℕ} {z : List ℕ} (hend : trT G k q u₁ u₂ m = .done z)
    (hcall : ∀ j < m, ∃ g S q', trT G k q u₁ u₂ j = .call (g :: S) q' ∧ Fits g.ph q' ∧
      Ans G q' (ansOf G q') ∧ RankLe (k + q + 1) q') :
    SizeOK G k q u₁ u₂ m (Lsz (szP G k q u₁ u₂) m) (maxEntry (xT G k q u₁ u₂)) := by
  have hok := traj_ok hI hcall
  set P := szP G k q u₁ u₂ with hPdef
  have hK : P.K = k + q + 1 := rfl
  have hqK : P.q ≤ P.K := by simp only [hPdef, szP]; omega
  have hΛ : P.Λ = (xT G k q u₁ u₂).length := rfl
  have hB0 : P.B0 = maxEntry (xT G k q u₁ u₂) + (xT G k q u₁ u₂).length + (k + q + 1) + 3 := rfl
  have hF : 8 * (P.Λ + P.K + 10) ≤ P.F P.q := by
    simp only [SzP.F]; exact Nat.le_self_pow (by omega) _
  have hB1 : P.B1 = P.B0 + P.K + P.LX + P.F P.q + 10 := rfl
  have hLQ : P.LQ = P.LX + P.F P.q + P.K + 6 := rfl
  set L := Lsz P m with hL
  have hLd : L = 2 * P.LS + 4 * (P.LQ + 50000) + P.Λ + m + 2 * P.K + P.LX + P.F P.q + 60000 := rfl
  set N := P.B1 + P.LQ + 50000 with hN
  have hNL : N ≤ maxEntry (xT G k q u₁ u₂) + L := by omega
  have hLQB : P.LQ + P.K + 3 ≤ P.B1 := by rw [hB1, hLQ, hB0, hK]; omega
  have hN8 : P.B1 + 8000 + P.LQ + 40010 ≤ N := by omega
  -- the facts about a call state
  have hst : ∀ j < m, ∃ S q', trT G k q u₁ u₂ j = .call S q' ∧
      (toWord (stWords S)).length ≤ P.LS ∧ (∀ e ∈ toWord (stWords S), e < P.B1) ∧
      (qWord q').length ≤ P.LQ + 40010 ∧ (∀ e ∈ qWord q', e < N) ∧
      (ansWord q' (ansOf G q')).length ≤ P.LQ + 40010 ∧ (∀ e ∈ ansWord q' (ansOf G q'), e < N) := by
    intro j hj
    obtain ⟨g, S, q', htr, -, hA, hRk⟩ := hcall j hj
    have h := hok j hj.le
    rw [htr] at h
    obtain ⟨hS, f, S', he, hq⟩ := h
    obtain ⟨hs1, hs2⟩ := stw_small hS hqK
    rw [he] at hS
    have hqs := q_small hS hq
    have hb := ans_small hA hqs (by rw [hK]; exact hRk) hLQB
    obtain ⟨q1, q2⟩ := qWord_len_ent (N := P.B1 + 8000) (fun e h' => by have := hqs.2 e h'; omega)
      (by omega)
    obtain ⟨a1, a2⟩ := ansWord_len_ent (q := q') (N := N) (fun e h' => by have := hb.2 e h'; omega)
      (by omega)
    have h3 := hqs.1
    have h4 := hb.1
    exact ⟨g :: S, q', htr, hs1, hs2, by omega, fun e h' => by have := q2 e h'; omega,
      by omega, a2⟩
  have hstl : ∀ j (S : List Fr), (stWord j S).length = (toWord (stWords S)).length + 2 := by
    intro j S; simp [stWord]
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · -- inputs
    cases j with
    | zero => rw [uT_zero]; simp; omega
    | succ j =>
      obtain ⟨S, q', htr, l1', -, -, -, l3, -⟩ := hst j (by omega)
      show (lpU (xT G k q u₁ u₂) (aT G k q u₁ u₂ (j + 1)) (bT G k q u₁ u₂ (j + 1))).length ≤ L
      rw [show lpU (xT G k q u₁ u₂) (aT G k q u₁ u₂ (j + 1)) (bT G k q u₁ u₂ (j + 1)) =
        glueIn (j + 1) S (ansWord q' (ansOf G q')) from sU_succ k q l1 l2 _ _ G j htr]
      simp only [glueIn, List.length_append, List.length_cons, hstl]
      simp; omega
  · -- outputs
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · obtain ⟨S, q', htr, l1', -, l2', -, -, -⟩ := hst j hj
      rw [aT_succ, htr]
      simp only [outW, List.length_append, hstl]
      simp; omega
    · rw [aT_done hend]
      have := hok j hj
      rw [hend] at this
      have hFq := this.1
      simp; omega
  · -- entries
    intro e he
    rcases List.mem_append.1 he with he | he
    · cases j with
      | zero =>
        rw [uT_zero] at he
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
        rcases he with ((rfl | rfl) | he) | rfl
        · omega
        · omega
        · have := le_maxEntry he; omega
        · omega
      | succ j =>
        obtain ⟨S, q', htr, l1', e1, -, -, l3, e3⟩ := hst j (by omega)
        have hu : uT G k q u₁ u₂ (j + 1) = glueIn (j + 1) S (ansWord q' (ansOf G q')) :=
          sU_succ k q l1 l2 _ _ G j htr
        rw [hu] at he
        simp only [glueIn, stWord, List.mem_append, List.mem_cons, List.length_cons] at he
        rcases he with ((rfl | rfl | he) | rfl | rfl | he) | rfl | he
        · omega
        · omega
        · simp at he
        · omega
        · omega
        · have := e1 e he; omega
        · omega
        · have := e3 e he; omega
    · rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · obtain ⟨S, q', htr, l1', e1, l2', e2, -, -⟩ := hst j hj
        rw [aT_succ, htr] at he
        simp only [outW, stWord, List.mem_append, List.mem_cons, List.length_cons] at he
        rcases he with ((rfl | rfl | rfl | he) | rfl | rfl | he) | he
        · omega
        · omega
        · omega
        · simp at he
        · omega
        · omega
        · have := e1 e he; omega
        · have := e2 e he; omega
      · rw [aT_done hend] at he
        have := (hok j hj)
        rw [hend] at this
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · omega
        · have := this.2 e he; omega

end

end Lax185574Proofs.CompRam
