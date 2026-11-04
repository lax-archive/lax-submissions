import Lax185574Proofs.MC.Asm.Calls
import Lax185574Proofs.MC.Asm.Jobs

/-!
The answers of the callee of the pipeline.

The callee `switch MJ RL Ev D` runs the batched merge lift, the resolve
lift and the evaluation on the three parts of the query `callQ` of a call. If the
glue program has checked the guard `GuardOK` of the call at word length
`v`, and the word length of the callee is at most two below `v`, then
the part of the query that does real work is admissible for its program,
and the two fixed parts are admissible once the word length exceeds a
constant. So every halting run of the three programs gives the answer
`callY` of the call.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574.Computing
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.TypeTrees Lax185574.PartialGraphEncoding
open Lax185574.ResolveLift Lax185574.DistanceMatrix

/-- Clause 1 of `Computes`: every halting run at an admissible word
length outputs the answer. -/
def SoundOn {α β : Type*} [WordEncoding α] [WordEncoding β] (p : Program) (e c : ℕ) (a : α)
    (b : β) : Prop :=
  ∀ w : ℕ, WordAdmissible e c w (toWord a) → ∀ (y : List ℕ) (t : ℕ), RunsTo w p (toWord a) y t →
    y = toWord b

theorem soundOn_of {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b : β} {T : ℕ → ℕ} (h : Computes p e c a b T) : SoundOn p e c a b :=
  fun w hw => (h w hw).1

/-- The constant of a fixed word for a constant `c` and an exponent `e`. -/
def fixCst (e c : ℕ) (u : List ℕ) : ℕ := c * (u.length + maxEntry u + 1) ^ e

theorem adm_of_fix {e c v : ℕ} {u : List ℕ} (h : fixCst e c u ≤ 2 ^ v) :
    WordAdmissible e c v u := by
  intro x hx
  refine le_trans ?_ h
  unfold fixCst
  have := le_maxEntry hx
  gcongr

theorem adm_of_guard {e c v : ℕ} {u : List ℕ} (hg : (u.length + maxEntry u + 1) ^ (e + 1) ≤ 2 ^ v)
    (hc : c ^ (e + 1) ≤ 2 ^ v) : WordAdmissible e c v u := by
  intro x hx
  have hxm := le_maxEntry hx
  rcases le_total c (u.length + maxEntry u + 1) with h | h
  · refine le_trans ?_ hg
    rw [pow_succ']
    exact Nat.mul_le_mul h (Nat.pow_le_pow_left (by omega) _)
  · refine le_trans ?_ hc
    rw [pow_succ']
    exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) _)

open Classical in
/-- The soundness facts of the three callees at one rank `q`, with the
constants of the real calls (`cM`, `cR`, `cE`) and of the fixed ones
(`dM`, `dR`, `dE`). -/
structure CalleeSound (pM pR pE : Program) (eM eR eE q cM cR cE dM dR dE : ℕ) : Prop where
  merge : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ), P ≠ Q →
    SoundOn pM eM cM (mjobs G q P Q) (mans G q P Q)
  resolve : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (sg : Bool),
    SoundOn pR eR cR (G, distMatrix G, P, Q, sg, family G 1 q)
      (resolveBy G sg P Q, distMatrix (resolveBy G sg P Q), family (resolveBy G sg P Q) 1 q)
  eval : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (a : Fin n) (φ : Lax3.FirstOrder.FO 0),
    Lax3.FirstOrder.rank φ = q →
    SoundOn pE eE cE (tree G 1 q ![a], loc q φ)
      (decide (Lax185574.DistanceLogic.DistFO.Sat G ![a] (loc q φ)))
  merge0 : ∀ y t w, fixCst eM dM qM0 ≤ 2 ^ w → RunsTo w pM qM0 y t → y = yM0
  resolve0 : ∀ y t w, fixCst eR dR qR0 ≤ 2 ^ w → RunsTo w pR qR0 y t → y = zR0
  eval0 : ∀ y t w, fixCst eE dE qE0 ≤ 2 ^ w → RunsTo w pE qE0 y t → y = uE0

/-- The constant that the word lengths of the callees must exceed. -/
noncomputable def calleeBig (eM eR eE cM cR cE dM dR dE : ℕ) : ℕ :=
  cM ^ (eM + 1) + cR ^ (eR + 1) + cE ^ (eE + 1) + fixCst eM dM qM0 + fixCst eR dR qR0 +
    fixCst eE dE qE0

open Classical in
/-- The soundness facts from the three concepts. -/
theorem calleeSound_of {pM pR pE : Program} {eM eR eE : ℕ} (hM : MJSpec pM eM)
    (hR : RLSpec pR eR)
    (hE : ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (φ : Lax185574.DistanceLogic.DistFO ℓ), ℓ ≤ k → Lax185574.DistanceLogic.DistFO.DRank k q φ →
        Computes pE eE c (tree G k q u, φ) (decide (Lax185574.DistanceLogic.DistFO.Sat G u φ))
          (fun m => c * (m + 1) ^ a))
    (q : ℕ) : ∃ cM cR cE dM dR dE, CalleeSound pM pR pE eM eR eE q cM cR cE dM dR dE := by
  obtain ⟨cM, _, hM1, hM0⟩ := hM q
  obtain ⟨cR, _, hR1⟩ := hR 1 q
  obtain ⟨dR, _, hR0⟩ := hR 1 0
  obtain ⟨cE, _, hE1⟩ := hE 1 q
  obtain ⟨dE, _, hE0⟩ := hE 1 0
  refine ⟨cM, cR, cE, cM, dR, dE, fun n G P Q hPQ => soundOn_of (hM1 n G P Q hPQ),
    fun n G P Q sg => soundOn_of (hR1 n G P Q sg le_rfl).1, fun n G a φ hq => ?_, ?_, ?_, ?_⟩
  · have hd := loc_drank q φ (by omega)
    simp only [Nat.sub_zero, zero_add] at hd
    exact soundOn_of (hE1 n G 1 ![a] (loc q φ) le_rfl hd)
  · intro y t w hw h
    exact soundOn_of hM0 w (adm_of_fix hw) y t h
  · intro y t w hw h
    exact soundOn_of (hR0 0 G0 0 0 false le_rfl).1 w (adm_of_fix hw) y t h
  · intro y t w hw h
    exact soundOn_of (hE0 1 G1 1 ![0] (.eq 0 0) le_rfl (.eq 0 0)) w (adm_of_fix hw) y t h

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- **The answers of the callee.** -/
theorem callee_answers {pM pR pE : Program} {eM eR eE q cM cR cE dM dR dE : ℕ}
    (hS : CalleeSound pM pR pE eM eR eE q cM cR cE dM dR dE) {n : ℕ}
    {s : List (PartialGraph (Fin n))} {φ : Lax3.FirstOrder.FO 0} (hq : Lax3.FirstOrder.rank φ = q)
    {c : PCall n} {D v v' : ℕ} (hv : v ≤ v' + 2)
    (hg : GuardOK s q φ eM eR eE v (D + 16) c)
    (hB : calleeBig eM eR eE cM cR cE dM dR dE ≤ 2 ^ (v' - 8 - D))
    {y z u : List ℕ} {tA tB tC : ℕ} (hy : RunsTo (v' - 4 - D) pM (callQM s q c) y tA)
    (hz : RunsTo (v' - 6 - D) pR (callQR s q c) z tB)
    (hu : RunsTo (v' - 8 - D) pE (callQE s q φ c) u tC) :
    y ++ z ++ u = callY s q φ c := by
  have h4 : 2 ^ (v' - 8 - D) ≤ 2 ^ (v' - 4 - D) := two_pow_mono (by omega)
  have h6 : 2 ^ (v' - 8 - D) ≤ 2 ^ (v' - 6 - D) := two_pow_mono (by omega)
  have hg' : 2 ^ (v - (D + 16)) ≤ 2 ^ (v' - 8 - D) := two_pow_mono (by omega)
  unfold calleeBig at hB
  cases c with
  | merge t P Q =>
    simp only [GuardOK, callQM, callQR, callQE] at hg hy hz hu
    by_cases hPQ : P = Q
    · simp only [hPQ, if_true] at hy hg
      have e1 := hS.merge0 _ _ _ (by omega) hy
      have e2 := hS.resolve0 _ _ _ (by omega) hz
      have e3 := hS.eval0 _ _ _ (by omega) hu
      simp only [callY, callYM, callYR, callYE, e1, e2, e3, hPQ, if_true]
    simp only [hPQ, if_false] at hy hg
    have e1 := hS.merge n (sAt s t) P Q hPQ _
      (adm_of_guard (by omega) (by omega)) _ _ hy
    have e2 := hS.resolve0 _ _ _ (by omega) hz
    have e3 := hS.eval0 _ _ _ (by omega) hu
    simp only [callY, callYM, callYR, callYE, e1, e2, e3, hPQ, if_false]
  | resolve t sg P Q =>
    simp only [GuardOK, callQM, callQR, callQE] at hg hy hz hu
    have e1 := hS.merge0 _ _ _ (by omega) hy
    have e2 := hS.resolve n (sAt s t) P Q sg _ (adm_of_guard (by omega) (by omega)) _ _ hz
    have e3 := hS.eval0 _ _ _ (by omega) hu
    simp only [callY, callYM, callYR, callYE, e1, e2, e3]
  | eval a =>
    simp only [GuardOK, callQM, callQR, callQE] at hg hy hz hu
    have e1 := hS.merge0 _ _ _ (by omega) hy
    have e2 := hS.resolve0 _ _ _ (by omega) hz
    have e3 := hS.eval n (sAt s (s.length - 1)) a φ hq _
      (adm_of_guard (by omega) (by omega)) _ _ hu
    simp only [callY, callYM, callYR, callYE, e1, e2, e3]

end Lax185574Proofs.MC
