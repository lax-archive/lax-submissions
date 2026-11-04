import Lax185574Proofs.ResolveRam.LenBounds
import Lax185574Proofs.ResolveRam.SizeGlue.Graph

/-!
Size bounds on the calls of lem:resolve-lift that do not grow with `‖H‖`.

Write `M` for the largest size of a tree of the family, `T` for
`treeCount` and `Y = M + T + 1`. Every call other than the scatter type
has query, answer and time bound at most a constant times `(n + 1)
Y^A` (`call_le_nY`, `rcall_le_nY`). The answer of the scatter type is at
most a constant times `(n + 1)(M + 1)^A` (`stp_ans_le`).

Some answers have size independent of `n`: the rank shift of an item
(`shift_ans_le`), every member of the unfiltered far tree of an item
(`faOf_mem_le`) and the composition of the shifted item with such a
member (`compose_ans_le`) are at most a constant times `(M + 1)^A`, and
the output word of an item is at most `kidB T` (`outW_mem_le`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.TypeTreeSizes Lax185574Proofs.MC Lax185574.DistanceMatrix
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### The answer of the switch -/

theorem rY_len {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ) (c : RCall) :
    (rY G k₀ q₀ c).length ≤ fixLen + (realY G k₀ q₀ c).length := by
  unfold fixLen
  cases c <;> simp only [rY, yA, yB, yC, yE, yF, realY, List.length_append] <;> omega

theorem rQ_len {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ) (c : RCall) :
    (rQ G k₀ q₀ c).length ≤ fixLen + (realQ G k₀ q₀ c).length := by
  have := rQY_len G k₀ q₀ c
  have h2 := rY_len G k₀ q₀ c
  have h3 : (realY G k₀ q₀ c).length ≤ (rY G k₀ q₀ c).length := by
    cases c <;> simp only [rY, yA, yB, yC, yE, yF, realY, List.length_append] <;> omega
  omega

/-! ### The calls other than the scatter type -/

variable {k₀ q₀ : ℕ}

/-- **The calls other than the scatter type.** The time bound and the
real query of such a call are at most a constant times `(n + 1) Y^A`. -/
theorem call_le_nY (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ)
    (s : Bool), ∀ c ∈ downAll G P Q s k₀ q₀ ++ upAll G P Q s k₀ q₀,
      realT G k₀ q₀ c + (realQ G k₀ q₀ c).length ≤
        C * (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A := by
  obtain ⟨Cd, Ad, hdown⟩ := down_le (k₀ := k₀) (q₀ := q₀) hk
  set Cu := cCa * (upCst k₀ q₀ + 1) ^ aCa + upCst k₀ q₀ with hCu
  set Au := (q₀ + 2) * aCa + (q₀ + 2) with hAu
  refine ⟨Cd + Cu, Ad + Au, fun n G P Q s => ?_⟩
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hT
  set M := maxTreeSize G k₀ q₀ with hM
  set Y := M + T + 1 with hYd
  have hY : 1 ≤ Y := by omega
  set R1 := (Cd + Cu) * (n + 1) * Y ^ (Ad + Au)
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · simp only [downAll, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨d, hd, x, hx, hc⟩ := hc
    have h := hdown d hd n G P Q s x hx c hc
    simp only [← hM] at h
    have h2 : (M + 1) ^ Ad ≤ Y ^ (Ad + Au) :=
      le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right hY (by omega))
    have h3 : Cd * (n + 1) * (M + 1) ^ Ad ≤ Cd * (n + 1) * Y ^ (Ad + Au) :=
      Nat.mul_le_mul_left _ h2
    have h4 : Cd * (n + 1) * Y ^ (Ad + Au) ≤ R1 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  · have h := up_le k₀ q₀ hk G P Q s hc
    simp only [← hT, ← hCu, ← hAu] at h
    have h2 : (T + 1) ^ Au ≤ Y ^ (Ad + Au) :=
      le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right hY (by omega))
    have h3 : Cu * (T + 1) ^ Au ≤ Cu * (n + 1) * Y ^ (Ad + Au) := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (le_trans h2 (Nat.le_mul_of_pos_left _ (by omega)))
    have h4 : Cu * (n + 1) * Y ^ (Ad + Au) ≤ R1 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega

theorem mem_rest_of_ne_stp {n : ℕ} {G : PartialGraph (Fin n)} {P Q : ℕ} {s : Bool} {c : RCall}
    (hc : c ∈ rcalls G P Q s k₀ q₀) (hne : c ≠ .stp) :
    c ∈ downAll G P Q s k₀ q₀ ++ upAll G P Q s k₀ q₀ := by
  unfold rcalls at hc
  split_ifs at hc
  · simp at hc
  rcases List.mem_cons.1 hc with h | h
  · exact absurd h hne
  · exact h

/-- **The query and the answer of a call other than the scatter type.** -/
theorem rcall_le_nY (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ)
    (s : Bool), ∀ c ∈ rcalls G P Q s k₀ q₀, c ≠ .stp →
      realT G k₀ q₀ c + (realQ G k₀ q₀ c).length + (realY G k₀ q₀ c).length +
        (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length ≤
        C * (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A := by
  obtain ⟨C, A, h⟩ := call_le_nY (q₀ := q₀) hk
  refine ⟨2 * fixLen + 3 * C, A, fun n G P Q s c hc hne => ?_⟩
  have h1 := h n G P Q s c (mem_rest_of_ne_stp hc hne)
  have h2 := realY_le hk (callInst G P Q s k₀ q₀ hk c hc)
  have h3 := rQ_len G k₀ q₀ c
  have h4 := rY_len G k₀ q₀ c
  set Z := (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A
  have hZ : 1 ≤ Z := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e1 : C * (n + 1) * (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A =
      C * Z := by simp only [Z]; ring
  have e2 : (2 * fixLen + 3 * C) * (n + 1) *
      (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A =
      2 * fixLen * Z + 3 * (C * Z) := by simp only [Z]; ring
  rw [e1] at h1
  rw [e2]
  have : fixLen ≤ fixLen * Z := Nat.le_mul_of_pos_right _ hZ
  nlinarith

/-! ### The scatter type -/

/-- **The answer of the scatter type.** -/
theorem stp_ans_le (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)),
    (realY G k₀ q₀ .stp).length + (rY G k₀ q₀ .stp).length ≤
      C * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ A := by
  obtain ⟨c, a, h⟩ := stp_le k₀ q₀ hk
  refine ⟨fixLen + 2 * c, a, fun n G => ?_⟩
  have h1 := h 0 (Nat.zero_le _) n G
  simp only [Nat.add_zero, Nat.sub_zero] at h1
  have h2 := rY_len G k₀ q₀ .stp
  have e : (realY G k₀ q₀ .stp).length = wordLength (stp G k₀ q₀) := rfl
  have hZ : 1 ≤ (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ a := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e2 : (fixLen + 2 * c) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ a =
      fixLen * ((n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ a) +
        2 * (c * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ a) := by ring
  have : fixLen ≤ fixLen * ((n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ a) := Nat.le_mul_of_pos_right _ hZ
  omega

/-- The query of the scatter type. -/
theorem stp_query_le {n : ℕ} (G : PartialGraph (Fin n)) :
    (realQ G k₀ q₀ .stp).length ≤
      5 * (n + 1) ^ 2 + 3 + (1 + n * (n + 1)) + n * maxTreeSize G k₀ q₀ := by
  show wordLength (G, k₀, q₀, distMatrix G, family G k₀ q₀) ≤ _
  rw [wordLength_prod, wordLength_prod, wordLength_prod, wordLength_prod]
  have h1 : wordLength G ≤ 5 * (n + 1) ^ 2 := toWord_pgraph_le G
  have h2 : wordLength (family G k₀ q₀) ≤ 1 + n * maxTreeSize G k₀ q₀ :=
    length_toWord_fun (family G k₀ q₀) (ℓ := maxTreeSize G k₀ q₀)
      (fun i => Finset.le_sup (f := fun a : Fin n => wordLength (family G k₀ q₀ a)) (Finset.mem_univ i))
  have h3 : wordLength (distMatrix G) = 1 + n * (n + 1) := Lax185574Proofs.DistMatrix.length_toWord_distMatrix G
  have e1 : wordLength k₀ = 1 := rfl
  have e2 : wordLength q₀ = 1 := rfl
  omega

end Lax185574Proofs.ResolveRam
