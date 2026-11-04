import Lax185574Proofs.CompRam.SizeTraj

/-!
**The sizes along the script** (`size_ok`): for an instance with `m`
calls, the inputs and outputs of the rounds have length at most
`Lsz P m` and entries at most `max x + Lsz P m`, where `P = szP` holds
the parameters of the instance.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim

/-- The parameters of an instance. -/
noncomputable def szP {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {l1 l2 : ℕ}
    (u₁ : Fin l1 → Fin n) (u₂ : Fin l2 → Fin n) : SzP :=
  ⟨(xT G k q u₁ u₂).length, k + q + 1,
    maxEntry (xT G k q u₁ u₂) + (xT G k q u₁ u₂).length + (k + q + 1) + 3, q⟩

/-- The length of the questions. -/
def SzP.LQ (P : SzP) : ℕ := P.LX + P.F P.q + P.K + 6

/-- The length of the word of the stack. -/
def SzP.LS (P : SzP) : ℕ := 1 + 7 * (P.q + 1) * (P.LX + 7)

/-- The bound on the sizes of the rounds. -/
def Lsz (P : SzP) (m : ℕ) : ℕ :=
  2 * P.LS + 4 * (P.LQ + 50000) + P.Λ + m + 2 * P.K + P.LX + P.F P.q + 60000

section
variable {P : SzP}

theorem chain_le {q : ℕ} : ∀ {S : List Fr}, Chain q S → ∀ f ∈ S, f.d ≤ q
  | [], _, f, hf => by simp at hf
  | [g], h, f, hf => by simp only [List.mem_singleton] at hf; subst hf; simp only [Chain] at h; omega
  | g :: g' :: S, h, f, hf => by
    have ih := chain_le h.2
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · have := ih g' (by simp); have := h.1; omega
    · exact ih f (by simpa using hf)

theorem ex_small {f : Fr} (hf : FOK P f) (hdq : f.d ≤ P.q) : Small P.LX P.B1 (toWord f.EX) := by
  have hi := i_le hf
  have hexl := hf.exl
  have hl := length_toWord_le_of (c := P.F (f.d - 1) + P.K + 8) (fun w hw => (hf.exw w hw).1)
  have hF := P.F_mono (show f.d - 1 ≤ P.q by omega)
  refine ⟨?_, toWord_lt (by simp only [SzP.B1, SzP.LX]; nlinarith) fun w hw =>
    ⟨by have := (hf.exw w hw).1; simp only [SzP.B1]; omega, (hf.exw w hw).2⟩⟩
  have : f.EX.length * (P.F (f.d - 1) + P.K + 8 + 1) ≤ 2 * P.Λ * (P.F P.q + P.K + 9) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [SzP.LX]; omega

theorem frWords_small {f : Fr} (hf : FOK P f) (hdq : f.d ≤ P.q) :
    ∀ w ∈ frWords f, Small (P.LX + 6) P.B1 w := by
  have hB1 : P.B0 + P.K + P.LX + 10 ≤ P.B1 := by simp only [SzP.B1]; omega
  have hLX : 2 * P.Λ + 2 ≤ P.LX := by simp only [SzP.LX]; omega
  have hi := i_le hf
  have hrk := hf.rk
  have hph := hf.ph
  have hl := hf.ar
  intro w hw
  simp only [frWords, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨by simp, fun e he => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hf.A.2.mono (by omega) (by omega)
  · exact hf.B.2.mono (by omega) (by omega)
  · exact hf.sa0.mono (by omega) (by omega)
  · exact hf.sb0.mono (by omega) (by omega)
  · exact hf.at0.mono (by omega) le_rfl
  · exact (ex_small hf hdq).mono (by omega) le_rfl

theorem stw_small {S : List Fr} (hS : SOK P S) (hqK : P.q ≤ P.K) :
    Small P.LS P.B1 (toWord (stWords S)) := by
  obtain ⟨hc, hf, -⟩ := hS
  have hlen : S.length ≤ P.q + 1 := by
    cases S with
    | nil => simp
    | cons f S => have := chain_length hc; simp; omega
  have hsl : (stWords S).length = 7 * S.length := by
    simp only [stWords, List.length_flatten, List.map_map]
    have : ∀ f ∈ S, ((List.length ∘ frWords) f) = 7 := fun f _ => by simp [frWords]
    rw [List.map_congr_left this]; simp; ring
  have hw : ∀ w ∈ stWords S, Small (P.LX + 6) P.B1 w := by
    intro w hw
    simp only [stWords, List.mem_flatten, List.mem_map] at hw
    obtain ⟨_, ⟨f, hfS, rfl⟩, hw⟩ := hw
    exact frWords_small (hf f hfS) (chain_le hc f hfS) w hw
  have hF : 8 * (P.Λ + P.K + 10) ≤ P.F P.q := by
    simp only [SzP.F]; exact Nat.le_self_pow (by omega) _
  have hB1 : P.LX + 10 + P.F P.q ≤ P.B1 := by simp only [SzP.B1]; omega
  refine ⟨?_, toWord_lt (by omega) fun w h => ⟨by have := (hw w h).1; omega, (hw w h).2⟩⟩
  have := length_toWord_le_of (c := P.LX + 6) (fun w h => (hw w h).1)
  have : (stWords S).length * (P.LX + 6 + 1) ≤ 7 * (P.q + 1) * (P.LX + 7) := by
    rw [hsl]; exact Nat.mul_le_mul (by omega) (by omega)
  simp only [SzP.LS]; omega

theorem q_small {f : Fr} {S : List Fr} {q' : Qry} (hS : SOK P (f :: S)) (hq : QOf P f q') :
    Small P.LQ P.B1 (realQ q') := by
  obtain ⟨hc, hfS, -⟩ := hS
  have hf := hfS f (by simp)
  have hB1 : P.B0 + P.K + P.LX + P.F P.q + 10 ≤ P.B1 := by simp only [SzP.B1]; omega
  have hLX : 2 * P.Λ + 2 ≤ P.LX := by simp only [SzP.LX]; omega
  have hrk := hf.rk
  have har := hf.ar
  have hdq : f.d ≤ P.q := by have := chain_length hc; omega
  simp only [SzP.LQ]
  rcases hq with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, R, hR, rfl⟩ | ⟨-, rfl⟩
  · exact (atomsQ_small hf).mono (by omega) le_rfl
  · have hB := hf.B.2
    refine ⟨by simp only [realQ, List.length_append]; have := hB.1; simp; omega, fun e he => ?_⟩
    simp only [realQ, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with (rfl | rfl | rfl) | he
    · omega
    · omega
    · omega
    · have := hB.2 e he; omega
  · have hA := hf.A.2
    refine ⟨by simp only [realQ, List.length_append]; have := hA.1; simp; omega, fun e he => ?_⟩
    simp only [realQ, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with (rfl | rfl | rfl) | he
    · omega
    · omega
    · omega
    · have := hA.2 e he; omega
  · have hF := P.F_mono (show f.d - 1 ≤ P.q by omega)
    have hR1 := hR.1
    refine ⟨?_, fun e he => ?_⟩
    · simp only [realQ, reQuery, List.length_append, List.length_cons, length_jList]; simp; omega
    · simp only [realQ, reQuery, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false] at he
      rcases he with ((rfl | rfl | rfl) | he) | rfl | he
      · omega
      · omega
      · omega
      · exact hR.2 e he
      · omega
      · have := jList_lt f.l1 f.l2 e he; omega
  · exact (ex_small hf hdq).mono (by omega) le_rfl

theorem ans_small {n : ℕ} {G : PartialGraph (Fin n)} {q' : Qry} {b : List ℕ} {Λq : ℕ}
    (hA : Ans G q' b) (hq : Small Λq P.B1 (realQ q')) (hK : RankLe P.K q')
    (hB : Λq + P.K + 3 ≤ P.B1) : Small Λq P.B1 b := by
  cases q' with
  | ca ws =>
    simp only [Ans] at hA; subst hA
    exact sd_small hq (by omega)
  | sh w =>
    obtain ⟨kk, d, l, u, h1, hl, rfl, rfl⟩ := hA
    simp only [realQ] at hq
    rw [toWord_tree_eq] at hq ⊢
    simp only [RankLe, toWord_tree_eq] at hK
    simp at hK
    have hn : ∀ v ∈ toWord (node G kk (d + 1) u), v < P.B1 := fun v hv =>
      hq.2 v (List.mem_append_right _ hv)
    have hd : d < P.B1 := hq.2 (d + 1) (by simp) |> fun h => by omega
    have hql := hq.1
    simp only [List.length_append] at hql
    obtain ⟨b1, b2⟩ := sh_bound G kk d u h1 P.B1 hn (by simp at hql; omega) (by omega) (by omega) hd
    refine ⟨by simp only [List.length_append]; simp at hql ⊢; omega, fun v hv => ?_⟩
    rcases List.mem_append.1 hv with hv | hv
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega
    · exact b2 v hv
  | re w =>
    obtain ⟨kk, d, l, u, J, hl, hJ, rfl, rfl⟩ := hA
    simp only [realQ] at hq
    have e1 : toWord (tree G kk d u, J) = [kk, d, l] ++ toWord (node G kk d u) ++ toWord J := rfl
    rw [e1] at hq
    have hn : ∀ v ∈ toWord (node G kk d u), v < P.B1 := fun v hv =>
      hq.2 v (List.mem_append_left _ (List.mem_append_right _ hv))
    have hk : kk < P.B1 := hq.2 kk (by simp)
    have hd : d < P.B1 := hq.2 d (by simp)
    have hql := hq.1
    simp only [List.length_append] at hql
    obtain ⟨b1, b2⟩ := re_bound G kk d u J hJ P.B1 hn (by simp at hql; omega) (by omega) hk hd
    exact ⟨by simp at hql; omega, b2⟩

end

end Lax185574Proofs.CompRam
