import Lax185574Proofs.ResolveRam.LenCanon
import Lax185574Proofs.ResolveRam.Glue.Input

/-!
The length fields of `CallBounds`.

Write `Y = M + T + 1`. The calls of an item on the way down cost at most
a constant times `(|G| + 1) Y^A` (`down_le`), the calls on the way up a
constant times `Y^A` (`up_le`), and the call of lem:compute-stp a
constant times `(|G| + 1)² Y^A` (`stp_call_le`). The number of calls is
`|G|` times a polynomial in `T`. So the time bounds add up to `(|G| +
1)²` times a polynomial in `Y`. The query and the answer of a call are at
most the fixed words, the real query and the time bound. The output is
the word of `H`, at most `5 (|G| + 1)²`, the word of its distance matrix,
`1 + |G| (|G| + 1)` entries, and the family of `H`, whose trees have size
polynomial in `T` by `output_size`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.TypeTreeSizes Lax185574Proofs.MC Lax185574.DistanceMatrix
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

theorem size_le_resolve (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) :
    G.size ≤ (resolveBy G s P Q).size := by
  unfold PartialGraph.size
  have h : G.resolved ≤ (resolveBy G s P Q).resolved := by
    rw [resolveBy_resolved]; exact le_sup_left
  have := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h) (Set.toFinite _)
  omega

theorem le_size (G : PartialGraph (Fin n)) : n ≤ G.size := by
  unfold PartialGraph.size; omega

theorem toWord_pgraph_le (G : PartialGraph (Fin n)) : (toWord G).length ≤ 5 * (n + 1) ^ 2 :=
  (small_pgraph G (M := Finset.univ.sup G.color) (fun v => Finset.le_sup (Finset.mem_univ v))).1

theorem pow_le_Y {M T a : ℕ} : (M + 1) ^ a ≤ (M + T + 1) ^ a ∧ (T + 1) ^ a ≤ (M + T + 1) ^ a :=
  ⟨Nat.pow_le_pow_left (by omega) a, Nat.pow_le_pow_left (by omega) a⟩

/-- The bound on the number of calls. -/
theorem calls_le (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) :
    (rcalls G P Q s k₀ q₀).length ≤ (1 + 6 * (q₀ + 1) * ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀) * (n + 1) *
      (treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ (q₀ + 1) := by
  refine le_trans (length_rcalls_leT G P Q s k₀ q₀ hk) ?_
  unfold callMaxT exMaxT
  set T := treeCount G (resolveBy G s P Q) k₀ q₀
  set K := (k₀ + q₀ + 2) ^ 2
  have h1 : K * T + 1 ≤ (K + 1) * (T + 1) := by nlinarith
  have h2 : (K * T + 1) ^ q₀ ≤ (K + 1) ^ q₀ * (T + 1) ^ q₀ := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left h1 _
  have h3 : T + 6 ≤ 6 * (T + 1) := by omega
  have hP : 1 ≤ (n + 1) * (T + 1) ^ (q₀ + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h4 : (q₀ + 1) * ((T + 6) * (n * (K * T + 1) ^ q₀)) ≤
      (q₀ + 1) * ((6 * (T + 1)) * ((n + 1) * ((K + 1) ^ q₀ * (T + 1) ^ q₀))) := by
    gcongr; omega
  have e : (1 + 6 * (q₀ + 1) * (K + 1) ^ q₀) * (n + 1) * (T + 1) ^ (q₀ + 1) =
      (n + 1) * (T + 1) ^ (q₀ + 1) +
        (q₀ + 1) * ((6 * (T + 1)) * ((n + 1) * ((K + 1) ^ q₀ * (T + 1) ^ q₀))) := by ring
  omega

/-- The call of lem:compute-stp. -/
theorem stp_call_le (k₀ q₀ : ℕ) (G : PartialGraph (Fin n)) :
    realT G k₀ q₀ .stp + (realQ G k₀ q₀ .stp).length ≤
      (cSt k₀ q₀ + 9) * (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ (aSt k₀ q₀ + 1) := by
  set M := maxTreeSize G k₀ q₀
  set Y := M + 1
  have hY : 1 ≤ Y := by omega
  have t1 : realT G k₀ q₀ .stp ≤ cSt k₀ q₀ * (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) := by
    show cSt k₀ q₀ * (n + 1) ^ 2 * (M + 1) ^ aSt k₀ q₀ ≤ _
    have : (M + 1) ^ aSt k₀ q₀ ≤ Y ^ (aSt k₀ q₀ + 1) := Nat.pow_le_pow_right hY (by omega)
    rw [sq, ← mul_assoc]
    gcongr
  have q1 : (realQ G k₀ q₀ .stp).length ≤ 5 * (n + 1) ^ 2 + 3 + (1 + n * (n + 1)) + n * M := by
    show wordLength (G, k₀, q₀, distMatrix G, family G k₀ q₀) ≤ _
    rw [wordLength_prod, wordLength_prod, wordLength_prod, wordLength_prod]
    have h1 : wordLength G ≤ 5 * (n + 1) ^ 2 := toWord_pgraph_le G
    have h2 : wordLength (family G k₀ q₀) ≤ 1 + n * M := length_toWord_fun (family G k₀ q₀) (ℓ := M)
      (fun i => Finset.le_sup (f := fun a : Fin n => wordLength (family G k₀ q₀ a)) (Finset.mem_univ i))
    have h3 : wordLength (distMatrix G) = 1 + n * (n + 1) := Lax185574Proofs.DistMatrix.length_toWord_distMatrix G
    have e1 : wordLength k₀ = 1 := rfl
    have e2 : wordLength q₀ = 1 := rfl
    omega
  have q2 : 5 * (n + 1) ^ 2 + 3 + (1 + n * (n + 1)) + n * M ≤
      9 * (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) := by
    have hYa : Y ≤ Y ^ (aSt k₀ q₀ + 1) := Nat.le_self_pow (by omega) _
    have hnM : n * M ≤ (n + 1) * (n + 1) * Y := Nat.mul_le_mul (by nlinarith) (by omega)
    have h3 : (n + 1) * (n + 1) * Y ≤ (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) :=
      Nat.mul_le_mul_left _ hYa
    have h4 : (n + 1) * (n + 1) ≤ (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have e : 9 * (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) =
        9 * ((n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1)) := by ring
    have e2 : (n + 1) ^ 2 = (n + 1) * (n + 1) := sq _
    have e3 : n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have e : (cSt k₀ q₀ + 9) * (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) =
      cSt k₀ q₀ * (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) +
        9 * (n + 1) * (n + 1) * Y ^ (aSt k₀ q₀ + 1) := by ring
  omega

/-- The bound on the queries of the canonical form. -/
noncomputable def upCst (k₀ q₀ : ℕ) : ℕ :=
  (1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1))) +
    (1 + (k₀ + q₀ + 2) ^ 2 * (4 + ∑ m ∈ Finset.range (q₀ + 1),
      sizeCoeff (1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1))) (q₀ + 1) m))

theorem upW_le (k₀ q₀ T : ℕ) :
    atomQB k₀ q₀ T + kidQB k₀ q₀ T ≤ upCst k₀ q₀ * (T + 1) ^ (q₀ + 2) := by
  unfold atomQB atomCnt kidQB kidB exMaxT upCst
  set SC := ∑ m ∈ Finset.range (q₀ + 1),
      sizeCoeff (1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1))) (q₀ + 1) m
  set K := (k₀ + q₀ + 2) ^ 2
  set A := 1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1))
  set P := (T + 1) ^ (q₀ + 1)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos T)
  have e2 : (T + 1) ^ (q₀ + 2) = (T + 1) * P := by rw [pow_succ]; ring
  have ha : 1 + 6 * (rhoPlus k₀ q₀ + 1) * (T + 1) * ((q₀ + 1) * (q₀ + 1)) * 6 ≤ A * (T + 1) := by
    simp only [A]; nlinarith
  have hb : 1 + K * T * (3 + SC * P + 1) ≤ (1 + K * (4 + SC)) * ((T + 1) * P) := by
    have h1 : 3 + SC * P + 1 ≤ (4 + SC) * P := by nlinarith
    have h2 : K * T * (3 + SC * P + 1) ≤ K * (4 + SC) * ((T + 1) * P) := by
      calc K * T * (3 + SC * P + 1) ≤ K * (T + 1) * ((4 + SC) * P) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h1
        _ = K * (4 + SC) * ((T + 1) * P) := by ring
    have h3 : 1 ≤ (T + 1) * P := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hA : A * (T + 1) ≤ A * ((T + 1) * P) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hP)
  rw [e2]
  have := add_mul A (1 + K * (4 + SC)) ((T + 1) * P)
  omega

/-- **The calls on the way up.** -/
theorem up_le (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool)
    {c : RCall} (hc : c ∈ upAll G P Q s k₀ q₀) :
    realT G k₀ q₀ c + (realQ G k₀ q₀ c).length ≤
      (cCa * (upCst k₀ q₀ + 1) ^ aCa + upCst k₀ q₀) *
        (treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ ((q₀ + 2) * aCa + (q₀ + 2)) := by
  have hW : ∃ ws, c = .canon ws ∧ wordLength ws ≤
      upCst k₀ q₀ * (treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ (q₀ + 2) := by
    simp only [upAll, List.mem_flatMap, List.mem_reverse, List.mem_range] at hc
    obtain ⟨d, hd, y, hy, hc⟩ := hc
    have hyx := (List.mem_zipIdx' (x := y.1) (i := y.2) hy).2
    have hx : y.1 ∈ lvR G P Q s k₀ q₀ d := by rw [hyx]; exact List.getElem_mem _
    have hu := upW_le k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀)
    simp only [upCalls] at hc
    split_ifs at hc with hdq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨_, rfl, le_trans (atomQ_le G P Q s k₀ q₀ hk (by omega) hx) (by omega)⟩
      · exact ⟨_, rfl, le_trans (kidQ_le G P Q s k₀ q₀ hk hdq hy) (by omega)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨_, rfl, le_trans (atomQ_le G P Q s k₀ q₀ hk (by omega) hx) (by omega)⟩
  obtain ⟨ws, rfl, hws⟩ := hW
  show cCa * (wordLength ws + 1) ^ aCa + wordLength ws ≤ _
  have h1 := pc_comp (d := cCa) (b := aCa) hws
  have h2 := pc_exp h1 (show (q₀ + 2) * aCa ≤ (q₀ + 2) * aCa + (q₀ + 2) by omega)
  have h3 := pc_exp hws (show q₀ + 2 ≤ (q₀ + 2) * aCa + (q₀ + 2) by omega)
  rw [add_mul]
  omega

/-- The bound on the output. -/
theorem zOut_le (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), (zOut G k₀ q₀ P Q s).length ≤
      C * (n + 1) * (n + 1) *
        (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A := by
  obtain ⟨c, a, h⟩ := output_size k₀ q₀ hk
  refine ⟨8 + c, a, fun n G P Q s => ?_⟩
  set H := resolveBy G s P Q
  set T := treeCount G H k₀ q₀
  set Y := maxTreeSize G k₀ q₀ + T + 1
  show wordLength (H, distMatrix H, family H k₀ q₀) ≤ _
  rw [wordLength_prod, wordLength_prod]
  have h1 := toWord_pgraph_le H
  have h3 : wordLength (distMatrix H) = 1 + n * (n + 1) := Lax185574Proofs.DistMatrix.length_toWord_distMatrix H
  have h2 := length_toWord_fun (family H k₀ q₀) (ℓ := c * (T + 1) ^ a) (fun i => h n G P Q s i)
  show (toWord H).length + (wordLength (distMatrix H) + (toWord (family H k₀ q₀)).length) ≤ _
  have hTY : (T + 1) ^ a ≤ Y ^ a := Nat.pow_le_pow_left (by omega) a
  have hY : 1 ≤ Y ^ a := Nat.one_le_pow _ _ (by omega)
  have g1 : 5 * (n + 1) ^ 2 + 1 + (1 + n * (n + 1)) ≤ 8 * ((n + 1) * (n + 1) * Y ^ a) := by
    have : (n + 1) * (n + 1) ≤ (n + 1) * (n + 1) * Y ^ a := Nat.le_mul_of_pos_right _ hY
    have e3 : n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have g2 : n * (c * (T + 1) ^ a) ≤ c * ((n + 1) * (n + 1) * Y ^ a) := by
    have : n ≤ (n + 1) * (n + 1) := by nlinarith
    calc n * (c * (T + 1) ^ a) ≤ (n + 1) * (n + 1) * (c * Y ^ a) :=
          Nat.mul_le_mul this (Nat.mul_le_mul_left _ hTY)
      _ = c * ((n + 1) * (n + 1) * Y ^ a) := by ring
  have e : (8 + c) * (n + 1) * (n + 1) * Y ^ a =
      8 * ((n + 1) * (n + 1) * Y ^ a) + c * ((n + 1) * (n + 1) * Y ^ a) := by ring
  omega

theorem fin_le {x c a C A H N Y : ℕ} (h : x ≤ c * (H + 1) * (N + 1) * Y ^ a) (hc : c ≤ C)
    (ha : a ≤ A) (hY : 1 ≤ Y) : x ≤ C * (H + 1) * (N + 1) * Y ^ A :=
  le_trans h (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))
    (Nat.pow_le_pow_right hY ha))

set_option maxHeartbeats 1000000 in
/-- **The length fields of `CallBounds`.** -/
theorem lenBounds (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool),
    (rcalls G P Q s k₀ q₀).length ≤ C * (n + 1) * (treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A ∧
    ((rcalls G P Q s k₀ q₀).map (realT G k₀ q₀)).sum ≤ polyB G k₀ q₀ P Q s C A ∧
    (∀ c ∈ rcalls G P Q s k₀ q₀,
      (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length ≤ polyB G k₀ q₀ P Q s C A) ∧
    (zOut G k₀ q₀ P Q s).length ≤ polyB G k₀ q₀ P Q s C A := by
  obtain ⟨Cd, Ad, hdown⟩ := down_le (k₀ := k₀) (q₀ := q₀) hk
  obtain ⟨Cz, Az, hz⟩ := zOut_le k₀ q₀ hk
  set Cc := 1 + 6 * (q₀ + 1) * ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀ with hCc
  set Cu := cCa * (upCst k₀ q₀ + 1) ^ aCa + upCst k₀ q₀ with hCu
  set Au := (q₀ + 2) * aCa + (q₀ + 2) with hAu
  set Cs := cSt k₀ q₀ + 9 with hCs
  set As := aSt k₀ q₀ + 1 with hAs
  set A := As + (q₀ + 1) + Ad + Au + Az
  set C := Cs + Cc * (Cd + Cu) + (fixLen + Cs + Cd + Cu) + Cz + Cc
  refine ⟨C, A, fun n G P Q s => ?_⟩
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hT
  set M := maxTreeSize G k₀ q₀ with hM
  set Y := M + T + 1 with hYd
  have hY : 1 ≤ Y := by omega
  have hpb : polyB G k₀ q₀ P Q s C A = C * (n + 1) * (n + 1) * Y ^ A := rfl
  rw [hpb]
  have hH1 : ∀ x c a, x ≤ c * (n + 1) * Y ^ a → x ≤ c * (n + 1) * (n + 1) * Y ^ a := by
    intro x c a h
    refine le_trans h (Nat.mul_le_mul_right _ ?_)
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  -- the calls other than the scatter type
  set R1 := (Cd + Cu) * (n + 1) * Y ^ (Ad + Au)
  have hrest : ∀ c ∈ downAll G P Q s k₀ q₀ ++ upAll G P Q s k₀ q₀,
      realT G k₀ q₀ c + (realQ G k₀ q₀ c).length ≤ R1 := by
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
  have hstp' := stp_call_le k₀ q₀ G
  have hcalls := calls_le k₀ q₀ hk G P Q s
  simp only [← hM, ← hCs, ← hAs] at hstp'
  have hstp : realT G k₀ q₀ .stp + (realQ G k₀ q₀ .stp).length ≤ Cs * (n + 1) * (n + 1) * Y ^ As :=
    le_trans hstp' (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  simp only [← hT, ← hCc] at hcalls
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans hcalls (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega)))
  · unfold rcalls
    split_ifs with hn
    · simp
    rw [List.map_cons, List.sum_cons]
    set rest := downAll G P Q s k₀ q₀ ++ upAll G P Q s k₀ q₀
    have hs : (rest.map (realT G k₀ q₀)).sum ≤ rest.length * R1 := by
      have := List.sum_le_card_nsmul (rest.map (realT G k₀ q₀)) R1 (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨c, hc, rfl⟩ := hx
        have := hrest c hc; omega)
      simpa using this
    have hl : rest.length ≤ Cc * (n + 1) * (T + 1) ^ (q₀ + 1) := by
      have : (rcalls G P Q s k₀ q₀).length = rest.length + 1 := by
        simp [rcalls, hn, rest]
      omega
    have h1 : rest.length * R1 ≤ (Cc * (Cd + Cu)) * (n + 1) * (n + 1) * Y ^ ((q₀ + 1) + (Ad + Au)) := by
      have hT : (T + 1) ^ (q₀ + 1) ≤ Y ^ (q₀ + 1) := Nat.pow_le_pow_left (by omega) _
      calc rest.length * R1 ≤ (Cc * (n + 1) * Y ^ (q₀ + 1)) * R1 :=
            Nat.mul_le_mul_right _ (le_trans hl (Nat.mul_le_mul_left _ hT))
        _ = (Cc * (Cd + Cu)) * (n + 1) * (n + 1) * Y ^ ((q₀ + 1) + (Ad + Au)) := by
            simp only [R1, pow_add]; ring
        _ ≤ _ := by
            refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
            exact Nat.mul_le_mul_left _ (by omega)
    have g1 := fin_le (show realT G k₀ q₀ .stp ≤ Cs * (n + 1) * (n + 1) * Y ^ As by omega)
      (le_refl Cs) (show As ≤ A by omega) hY
    have g2 := fin_le h1 (le_refl _) (show (q₀ + 1) + (Ad + Au) ≤ A by omega) hY
    have e1 : C * (n + 1) * (n + 1) * Y ^ A = C * ((n + 1) * (n + 1) * Y ^ A) := by ring
    have e2 : Cs * (n + 1) * (n + 1) * Y ^ A = Cs * ((n + 1) * (n + 1) * Y ^ A) := by ring
    have e3 : Cc * (Cd + Cu) * (n + 1) * (n + 1) * Y ^ A =
        (Cc * (Cd + Cu)) * ((n + 1) * (n + 1) * Y ^ A) := by ring
    have e4 : (Cs + Cc * (Cd + Cu)) * ((n + 1) * (n + 1) * Y ^ A) ≤
        C * ((n + 1) * (n + 1) * Y ^ A) := Nat.mul_le_mul_right _ (by omega)
    have e5 := add_mul Cs (Cc * (Cd + Cu)) ((n + 1) * (n + 1) * Y ^ A)
    omega
  · intro c hc
    have h1 := rQY_len G k₀ q₀ c
    have h2 := realY_le hk (callInst G P Q s k₀ q₀ hk c hc)
    have hF : fixLen ≤ fixLen * (n + 1) * (n + 1) * Y ^ A := by
      have h0 : 1 ≤ (n + 1) * (n + 1) * Y ^ A := Nat.one_le_iff_ne_zero.2 (by positivity)
      calc fixLen ≤ fixLen * ((n + 1) * (n + 1) * Y ^ A) := Nat.le_mul_of_pos_right _ h0
        _ = _ := by ring
    have hq : realT G k₀ q₀ c + (realQ G k₀ q₀ c).length ≤
        (Cs + Cd + Cu) * (n + 1) * (n + 1) * Y ^ A := by
      unfold rcalls at hc
      split_ifs at hc
      · simp at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact fin_le hstp (by omega) (by omega) hY
      · exact fin_le (hH1 _ _ _ (hrest c hc)) (by omega) (by omega) hY
    have e : (fixLen + (Cs + Cd + Cu)) * (n + 1) * (n + 1) * Y ^ A ≤ C * (n + 1) * (n + 1) * Y ^ A :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
    have e2 : (fixLen + (Cs + Cd + Cu)) * (n + 1) * (n + 1) * Y ^ A =
        fixLen * (n + 1) * (n + 1) * Y ^ A + (Cs + Cd + Cu) * (n + 1) * (n + 1) * Y ^ A := by ring
    omega
  · have h := hz n G P Q s
    simp only [← hM, ← hT, ← hYd] at h
    exact fin_le h (by omega) (by omega) hY

end Lax185574Proofs.ResolveRam
