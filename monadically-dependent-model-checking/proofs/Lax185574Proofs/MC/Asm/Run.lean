import Lax185574Proofs.MC.Asm.Sound
import Lax185574Proofs.MC.Bounds.WordSizes

/-!
The runs of the callee of the pipeline within its time bounds.

`CalleeRun` collects the facts of the three callees that the forward
direction needs: the merge lift, the resolve lift and the evaluation
compute their answers within their time bounds at admissible word
lengths, and the fixed queries are answered within a constant `d` once
the word length exceeds `d`. `realT` is the time bound of the callee of a
call that does real work. `callee_run`: if the query of a call is small
for the literal exponents and the word lengths exceed the constants and
`realT`, then the three programs halt with the answer `callY` of the
call within `realT + 3 d` steps in total.
-/

namespace Lax185574Proofs.MC

open Lax185574Proofs.Words.Fast (maxLen)

open Lax808846.Ram Lax808846.RamComputes Lax185574.Computing Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.TypeTrees Lax185574.PartialGraphEncoding
open Lax185574.ResolveLift Lax185574Proofs.Simulate Lax185574.DistanceMatrix

/-- The constants of the three callees at one rank. -/
structure CCst where
  cM : ℕ
  aM : ℕ
  cR : ℕ
  aR : ℕ
  cE : ℕ
  aE : ℕ
  d : ℕ

open Classical in
/-- The facts about the three callees at rank `q` that the runs need. -/
structure CalleeRun (pM pR pE : Program) (eM eR eE q : ℕ) (k : CCst) : Prop where
  merge : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ), P ≠ Q →
    Computes pM eM k.cM (mjobs G q P Q) (mans G q P Q)
      (fun _ => k.cM * (n + 1) ^ 2 * (maxLen (mjobs G q P Q) + 1) ^ k.aM)
  resolve : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (sg : Bool),
    Computes pR eR k.cR (G, distMatrix G, P, Q, sg, family G 1 q)
      (resolveBy G sg P Q, distMatrix (resolveBy G sg P Q), family (resolveBy G sg P Q) 1 q)
      (fun _ => k.cR * (n + 1) ^ 2 *
        (maxTreeSize G 1 q + treeCount G (resolveBy G sg P Q) 1 q + 1) ^ k.aR)
  eval : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (a : Fin n) (φ : Lax3.FirstOrder.FO 0),
    Lax3.FirstOrder.rank φ = q →
    Computes pE eE k.cE (tree G 1 q ![a], loc q φ)
      (decide (Lax185574.DistanceLogic.DistFO.Sat G ![a] (loc q φ))) (fun m => k.cE * (m + 1) ^ k.aE)
  merge0 : ∀ w, k.d ≤ 2 ^ w → ∃ t ≤ k.d, RunsTo w pM qM0 yM0 t
  resolve0 : ∀ w, k.d ≤ 2 ^ w → ∃ t ≤ k.d, RunsTo w pR qR0 zR0 t
  eval0 : ∀ w, k.d ≤ 2 ^ w → ∃ t ≤ k.d, RunsTo w pE qE0 uE0 t

/-- The time bound of the callee that does real work in a call. -/
noncomputable def realT {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (k : CCst) : PCall n → ℕ
  | .merge t P Q => if P = Q then 0 else
      k.cM * (n + 1) ^ 2 * (maxLen (mjobs (sAt s t) q P Q) + 1) ^ k.aM
  | .resolve t sg P Q => k.cR * (n + 1) ^ 2 *
      (maxTreeSize (sAt s t) 1 q + treeCount (sAt s t) (resolveBy (sAt s t) sg P Q) 1 q + 1) ^ k.aR
  | .eval a => k.cE * ((callQE s q φ (.eval a)).length + 1) ^ k.aE

theorem maxEntry_le_of_sub {u w : List ℕ} (h : ∀ x ∈ u, x ∈ w) : maxEntry u ≤ maxEntry w :=
  foldr_max_le fun x hx => le_maxEntry (h x hx)

theorem part_guard {u w : List ℕ} {e E N : ℕ} (hsub : ∀ x ∈ u, x ∈ w) (hl : u.length ≤ w.length)
    (he : e ≤ E) (h : (w.length + maxEntry w + 1) ^ (E + 1) ≤ N) :
    (u.length + maxEntry u + 1) ^ (e + 1) ≤ N := by
  have := maxEntry_le_of_sub hsub
  calc (u.length + maxEntry u + 1) ^ (e + 1) ≤ (w.length + maxEntry w + 1) ^ (e + 1) :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (w.length + maxEntry w + 1) ^ (E + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ N := h

theorem swIn_parts (a b c : List ℕ) :
    ((∀ x ∈ a, x ∈ swIn a b c) ∧ a.length ≤ (swIn a b c).length) ∧
    ((∀ x ∈ b, x ∈ swIn a b c) ∧ b.length ≤ (swIn a b c).length) ∧
    ((∀ x ∈ c, x ∈ swIn a b c) ∧ c.length ≤ (swIn a b c).length) := by
  simp only [swIn, List.mem_append, List.length_append]
  refine ⟨⟨fun x hx => by simp [hx], by omega⟩, ⟨fun x hx => by simp [hx], by omega⟩,
    ⟨fun x hx => by simp [hx], by omega⟩⟩

theorem run_of_computes {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b : β} {T : ℕ → ℕ} (h : Computes p e c a b T) {w : ℕ}
    (hg : ((toWord a).length + maxEntry (toWord a) + 1) ^ (e + 1) ≤ 2 ^ w)
    (hc : c ^ (e + 1) ≤ 2 ^ w) (hT : T (wordLength a) ≤ 2 ^ w) :
    ∃ t ≤ T (wordLength a), RunsTo w p (toWord a) (toWord b) t :=
  (h w (adm_of_guard hg hc)).2 hT (toWord a) rfl

/-- **The runs of the callee in a call.** -/
theorem callee_run {pM pR pE : Program} {eM eR eE q : ℕ} {k : CCst}
    (hC : CalleeRun pM pR pE eM eR eE q k) {n : ℕ} {s : List (PartialGraph (Fin n))}
    {φ : Lax3.FirstOrder.FO 0} (hq : Lax3.FirstOrder.rank φ = q) (c : PCall n) {vA vB vC : ℕ}
    (hA : vC ≤ vA) (hB : vC ≤ vB)
    (hg : ((callQ s q φ c).length + maxEntry (callQ s q φ c) + 1) ^ (eM + eR + eE + 1) ≤ 2 ^ vC)
    (hbig : k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + k.d + realT s q φ k c ≤
      2 ^ vC) :
    ∃ y z u tA tB tC, RunsTo vA pM (callQM s q c) y tA ∧ RunsTo vB pR (callQR s q c) z tB ∧
      RunsTo vC pE (callQE s q φ c) u tC ∧ y ++ z ++ u = callY s q φ c ∧
      tA + tB + tC ≤ realT s q φ k c + 3 * k.d := by
  have pA : 2 ^ vC ≤ 2 ^ vA := two_pow_mono hA
  have pB : 2 ^ vC ≤ 2 ^ vB := two_pow_mono hB
  obtain ⟨⟨sM, lM⟩, ⟨sR, lR⟩, ⟨sE, lE⟩⟩ := swIn_parts (callQM s q c) (callQR s q c) (callQE s q φ c)
  have gM := part_guard sM lM (e := eM) (by omega) hg
  have gR := part_guard sR lR (e := eR) (by omega) hg
  have gE := part_guard sE lE (e := eE) (by omega) hg
  have hd : k.d ≤ 2 ^ vC := by omega
  obtain ⟨t1, ht1, r1⟩ := hC.merge0 vA (by omega)
  obtain ⟨t2, ht2, r2⟩ := hC.resolve0 vB (by omega)
  obtain ⟨t3, ht3, r3⟩ := hC.eval0 vC hd
  cases c with
  | merge t P Q =>
    by_cases hpq : P = Q
    · simp only [callQM, callQR, callQE, callY, callYM, callYR, callYE, realT, hpq,
        if_true] at gM r1 r2 r3 ⊢
      exact ⟨_, _, _, _, _, _, r1, r2, r3, rfl, by omega⟩
    · simp only [callQM, callQR, callQE, realT, hpq, if_false] at gM r2 r3 hbig ⊢
      obtain ⟨t0, ht0, r0⟩ := run_of_computes (hC.merge n (sAt s t) P Q hpq) (w := vA)
        (by omega) (by omega) (by omega)
      refine ⟨_, _, _, _, _, _, r0, r2, r3, ?_, ?_⟩
      · simp only [callY, callYM, callYR, callYE, hpq, if_false]
      · omega
  | resolve t sg P Q =>
    simp only [callQM, callQR, callQE, realT] at gR r1 r3 hbig ⊢
    obtain ⟨t0, ht0, r0⟩ := run_of_computes (hC.resolve n (sAt s t) P Q sg) (w := vB)
      (by omega) (by omega) (by omega)
    exact ⟨_, _, _, _, _, _, r1, r0, r3, by simp only [callY, callYM, callYR, callYE], by omega⟩
  | eval a =>
    simp only [callQM, callQR, callQE, realT] at gE r1 r2 hbig ⊢
    obtain ⟨t0, ht0, r0⟩ := run_of_computes (hC.eval n (sAt s (s.length - 1)) a φ hq) (w := vC)
      (by omega) (by omega) (by simp only [wordLength]; omega)
    refine ⟨_, _, _, _, _, _, r1, r2, r0, by simp only [callY, callYM, callYR, callYE], ?_⟩
    simp only [wordLength] at ht0; omega

open Classical in
/-- The facts about the callees from the three concepts. -/
theorem calleeRun_of {pM pR pE : Program} {eM eR eE : ℕ} (hM : MJSpec pM eM)
    (hR : RLSpec pR eR)
    (hE : ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (φ : Lax185574.DistanceLogic.DistFO ℓ), ℓ ≤ k → Lax185574.DistanceLogic.DistFO.DRank k q φ →
        Computes pE eE c (tree G k q u, φ) (decide (Lax185574.DistanceLogic.DistFO.Sat G u φ))
          (fun m => c * (m + 1) ^ a))
    (q : ℕ) : ∃ k : CCst, CalleeRun pM pR pE eM eR eE q k := by
  obtain ⟨cM, aM, hM1, m0⟩ := hM q
  obtain ⟨cR, aR, hR1⟩ := hR 1 q
  obtain ⟨dR, bR, hR0⟩ := hR 1 0
  obtain ⟨cE, aE, hE1⟩ := hE 1 q
  obtain ⟨dE, bE, hE0⟩ := hE 1 0
  have r0 := (hR0 0 G0 0 0 false le_rfl).1
  have e0 := hE0 1 G1 1 ![0] (.eq 0 0) le_rfl (.eq 0 0)
  set d := fixCst eM cM qM0 + cM + fixCst eR dR qR0 +
    dR * (0 + 1) ^ 2 *
      (maxTreeSize G0 1 0 + treeCount G0 (resolveBy G0 false 0 0) 1 0 + 1) ^ bR +
    fixCst eE dE qE0 + dE * (qE0.length + 1) ^ bE with hd
  refine ⟨⟨cM, aM, cR, aR, cE, aE, d⟩, ⟨fun n G P Q hPQ => hM1 n G P Q hPQ,
    fun n G P Q sg => (hR1 n G P Q sg le_rfl).1, fun n G a φ hq => ?_, ?_, ?_, ?_⟩⟩
  · have hd := loc_drank q φ (by omega)
    simp only [Nat.sub_zero, zero_add] at hd
    exact hE1 n G 1 ![a] (loc q φ) le_rfl hd
  · intro w hw
    change d ≤ 2 ^ w at hw
    show ∃ t ≤ d, _
    have h1 : fixCst eM cM qM0 ≤ 2 ^ w := by omega
    have h2 : cM ≤ 2 ^ w := by omega
    obtain ⟨t, ht, h⟩ := (m0 w (adm_of_fix h1)).2 h2 (toWord _) rfl
    beta_reduce at ht
    exact ⟨t, by omega, h⟩
  · intro w hw
    change d ≤ 2 ^ w at hw
    show ∃ t ≤ d, _
    have h1 : fixCst eR dR qR0 ≤ 2 ^ w := by omega
    have h2 : dR * (0 + 1) ^ 2 *
        (maxTreeSize G0 1 0 + treeCount G0 (resolveBy G0 false 0 0) 1 0 + 1) ^ bR ≤ 2 ^ w := by
      omega
    obtain ⟨t, ht, h⟩ := (r0 w (adm_of_fix h1)).2 h2 (toWord _) rfl
    beta_reduce at ht
    exact ⟨t, by omega, h⟩
  · intro w hw
    change d ≤ 2 ^ w at hw
    show ∃ t ≤ d, _
    have e : wordLength ((tree G1 1 0 ![(0 : Fin 1)],
      (Lax185574.DistanceLogic.DistFO.eq 0 0 : Lax185574.DistanceLogic.DistFO 1))) =
      qE0.length := rfl
    have h1 : fixCst eE dE qE0 ≤ 2 ^ w := by omega
    have h2 : dE * (qE0.length + 1) ^ bE ≤ 2 ^ w := by omega
    obtain ⟨t, ht, h⟩ := (e0 w (adm_of_fix h1)).2 (by rw [e]; exact h2) (toWord _) rfl
    rw [e] at ht
    beta_reduce at ht
    exact ⟨t, by omega, h⟩

end Lax185574Proofs.MC
