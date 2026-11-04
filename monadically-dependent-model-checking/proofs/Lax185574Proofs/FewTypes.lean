import Lax185574.FewTypes
import Lax185574.DefinableSequences
import Lax185574.DefinableToTypes
import Lax185574Proofs.Interface.Shim.DefinableToTypes
import Lax185574Proofs.RamSimulate
import Lax185574Proofs.Compose.Basic
import Lax185574Proofs.Interface.Shim.DefinableSequences
import Lax185574Proofs.LegacyInputs
import Lax185574Proofs.Interface.KitG3
import Lax185574Proofs.Interface.SeqBridge

/-!
Proof of thm:skel-few-types from thm:skel-def-seq and
lem:skel-def-to-types. The program runs the program of
`DefinableSequences` with the radius `r + 7^q` in place of `r`. On the
word level this replaces the first two entries `r, q` of the input by
the single entry `r + 7^q`, which is a rewrite of the input, so the
program is a simulation.
-/

namespace Lax185574Proofs.FewTypes

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax808846.RamComputes Lax271696.GraphEncoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.Width
open Lax185574Proofs.Simulate Lax185574Proofs.Compose

/-- The input rewrite: `r, q, rest ↦ r + 7^q, rest`. -/
def radiusRewrite : Rewrite 1 :=
  [.expr (.add (.entry 0 0) (.pow (.lit 7) (.entry 0 1))), .slice 0 (.lit 2) none]

theorem radiusRewrite_apply (r q : ℕ) (rest : List ℕ) :
    radiusRewrite.apply (fun _ => r :: q :: rest) = (r + 7 ^ q) :: rest := by
  simp [radiusRewrite, Rewrite.apply, Segment.apply, HExpr.eval]

theorem radiusRewrite_cost (r q : ℕ) (rest : List ℕ) :
    radiusRewrite.cost (fun _ => r :: q :: rest) = q + 9 := by
  simp [radiusRewrite, Rewrite.cost, Segment.cost, HExpr.cost, HExpr.eval]
  omega

theorem toWord_triple (r q : ℕ) (ε : ℚ) (g : List ℕ) :
    toWord (r, q, ε) ++ g = r :: q :: (toWord ε ++ g) := rfl

theorem toWord_pair (r : ℕ) (ε : ℚ) (g : List ℕ) :
    toWord (r, ε) ++ g = r :: (toWord ε ++ g) := rfl

/-- The rewritten input encodes the radius `r + 7^q`. -/
theorem encodesInput_rewrite {x : List ℕ} {r q : ℕ} {ε : ℚ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (hx : Lax185574.FewTypes.EncodesInput x r q ε n G) :
    Lax185574.DefinableSequences.EncodesInput (radiusRewrite.apply fun _ => x)
      (r + 7 ^ q) ε n G := by
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨g, hg, ?_⟩
  rw [toWord_triple, radiusRewrite_apply, toWord_pair]

/-- The time bound of the simulation: if `p₀` runs within the bound with
constant `c₀` and exponent `3 + η` on inputs for the radius `r + 7^q`,
then the simulation `p` runs within the bound with the same exponent and
any constant `c` above a threshold on the inputs for `r` and `q`. -/
theorem computesInTime_radiusRewrite {p₀ p : Program} {f₀ : List ℕ → List ℕ} {e₀ K : ℕ}
    (hsim : ∀ (w : ℕ) (x y : List ℕ) (t : ℕ),
        K ≤ 2 ^ (w - 1) → radiusRewrite.Fits w (fun _ => x) →
        RunsTo (w - 1) p₀ (radiusRewrite.apply fun _ => x) y t →
        ∃ t' ≤ K * t + K * radiusRewrite.cost (fun _ => x), RunsTo w p x y t')
    {r q : ℕ} {ε : ℚ} {η : ℝ} (hη : 0 < η) {n : ℕ} {G : SimpleGraph (Fin n)} {c₀ c : ℕ}
    (h₀ : ∀ w : ℕ, ComputesInTime w p₀
      {x | Lax185574.DefinableSequences.EncodesInput x (r + 7 ^ q) ε n G ∧
        ∀ v ∈ x, c₀ * (x.length + v + 1) ^ e₀ ≤ 2 ^ w}
      f₀ (fun x => ⌊(c₀ : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c₀ * x.length))
    (hc : K * c₀ + K * (q + 9) + 2 * c₀ * (7 ^ q + 1) ^ e₀ + 2 * K + 4 ≤ c) :
    ∀ w : ℕ, ComputesInTime w p
      {x | Lax185574.FewTypes.EncodesInput x r q ε n G ∧
        ∀ v ∈ x, c * (x.length + v + 1) ^ (e₀ + 1) ≤ 2 ^ w}
      (fun x => f₀ (radiusRewrite.apply fun _ => x))
      (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * x.length) := by
  intro w x ⟨hx, hadm⟩
  obtain ⟨g, hg, hxg⟩ := hx
  set rest := toWord ε ++ g
  have hxr : x = r :: q :: rest := by rw [hxg, toWord_triple]
  set x' := radiusRewrite.apply fun _ => x with hx'
  have hx'r : x' = (r + 7 ^ q) :: rest := by rw [hx', hxr, radiusRewrite_apply]
  have hlen : x.length = x'.length + 1 := by rw [hxr, hx'r]; simp
  -- the admissibility of `x` at `w`
  have hrx : r ∈ x := by rw [hxr]; simp
  have hqx : q ∈ x := by rw [hxr]; simp
  have hpow : ∀ v, 1 ≤ (x.length + v + 1) ^ (e₀ + 1) := fun v => Nat.one_le_pow _ _ (by omega)
  have hcw : c ≤ 2 ^ w := le_trans (Nat.le_mul_of_pos_right _ (hpow r)) (hadm r hrx)
  have hlenw : x.length < 2 ^ w := by
    have h1 : x.length + 1 ≤ (x.length + r + 1) ^ (e₀ + 1) :=
      le_trans (by omega) (Nat.le_self_pow (by omega) _)
    have h2 : (x.length + r + 1) ^ (e₀ + 1) ≤ c * (x.length + r + 1) ^ (e₀ + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have := hadm r hrx
    omega
  have hqw : q < 2 ^ w := by
    have h1 : q + 1 ≤ (x.length + q + 1) ^ (e₀ + 1) :=
      le_trans (by omega) (Nat.le_self_pow (by omega) _)
    have h2 : (x.length + q + 1) ^ (e₀ + 1) ≤ c * (x.length + q + 1) ^ (e₀ + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have := hadm q hqx
    omega
  have hw2 : 2 ≤ w := by
    by_contra h
    have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  -- the rewritten input is admissible one bit lower
  have hadm' : ∀ v ∈ x', c₀ * (x'.length + v + 1) ^ e₀ ≤ 2 ^ (w - 1) := by
    intro v hv
    obtain ⟨u, hu, hvu⟩ : ∃ u ∈ x, x'.length + v + 1 ≤ (7 ^ q + 1) * (x.length + u + 1) := by
      rw [hx'r, List.mem_cons] at hv
      rcases hv with rfl | hv
      · refine ⟨r, hrx, ?_⟩
        have : x'.length + (r + 7 ^ q) + 1 ≤ (x.length + r + 1) + 7 ^ q * (x.length + r + 1) := by
          have : 7 ^ q ≤ 7 ^ q * (x.length + r + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega
        linarith
      · refine ⟨v, by rw [hxr]; simp [hv], ?_⟩
        have : x.length + v + 1 ≤ (7 ^ q + 1) * (x.length + v + 1) :=
          Nat.le_mul_of_pos_left _ (by positivity)
        omega
    have h1 : (x'.length + v + 1) ^ e₀ ≤ (7 ^ q + 1) ^ e₀ * (x.length + u + 1) ^ (e₀ + 1) := by
      calc (x'.length + v + 1) ^ e₀ ≤ ((7 ^ q + 1) * (x.length + u + 1)) ^ e₀ :=
            Nat.pow_le_pow_left hvu _
        _ = (7 ^ q + 1) ^ e₀ * (x.length + u + 1) ^ e₀ := mul_pow _ _ _
        _ ≤ (7 ^ q + 1) ^ e₀ * (x.length + u + 1) ^ (e₀ + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 := hadm u hu
    have h3 : 2 * c₀ * (7 ^ q + 1) ^ e₀ ≤ c := by omega
    have h4 : 2 * (c₀ * (x'.length + v + 1) ^ e₀) ≤ c * (x.length + u + 1) ^ (e₀ + 1) := by
      calc 2 * (c₀ * (x'.length + v + 1) ^ e₀)
          ≤ 2 * (c₀ * ((7 ^ q + 1) ^ e₀ * (x.length + u + 1) ^ (e₀ + 1))) := by gcongr
        _ = (2 * c₀ * (7 ^ q + 1) ^ e₀) * (x.length + u + 1) ^ (e₀ + 1) := by ring
        _ ≤ c * (x.length + u + 1) ^ (e₀ + 1) := Nat.mul_le_mul_right _ h3
    omega
  obtain ⟨t₀, ht₀, hrun₀⟩ := h₀ (w - 1) x'
    ⟨encodesInput_rewrite ⟨g, hg, hxg⟩, hadm'⟩
  have hfits : radiusRewrite.Fits w (fun _ => x) := by
    refine ⟨fun _ => hlenw, ?_, ?_⟩
    · rw [← hx']; omega
    · intro seg hseg
      simp only [radiusRewrite, List.mem_cons, List.not_mem_nil, or_false] at hseg
      rcases hseg with rfl | rfl
      · refine ⟨(show 0 < 2 ^ w by positivity), trivial, ?_, ?_⟩
        · show 1 < 2 ^ w
          exact Nat.one_lt_two_pow (by omega)
        · show x.getD 1 0 < 2 ^ w
          rw [hxr]; exact hqw
      · refine ⟨trivial, ?_⟩
        show 2 < 2 ^ w
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw2
  obtain ⟨t, ht, hrun⟩ := hsim w x (f₀ x') t₀ (by omega) hfits hrun₀
  refine ⟨t, ?_, hrun⟩
  -- the time bound
  set P : ℝ := ((n : ℝ) + 1) ^ ((3 : ℝ) + η)
  have hP : 1 ≤ P := Real.one_le_rpow (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    (by linarith)
  have hcost : radiusRewrite.cost (fun _ => x) = q + 9 := by
    rw [hxr, radiusRewrite_cost]
  have ht' : t ≤ K * t₀ + K * (q + 9) := by rw [← hcost]; exact ht
  have ht₀' : t₀ ≤ ⌊(c₀ : ℝ) * P⌋₊ + c₀ * x'.length := ht₀
  have h1 : K * ⌊(c₀ : ℝ) * P⌋₊ + K * (q + 9) ≤ ⌊((K * c₀ + K * (q + 9) : ℕ) : ℝ) * P⌋₊ :=
    mul_floor_add_le hP
  have h2 : ⌊((K * c₀ + K * (q + 9) : ℕ) : ℝ) * P⌋₊ ≤ ⌊(c : ℝ) * P⌋₊ :=
    floor_mul_mono (by linarith) (by omega)
  have h3 : K * (c₀ * x'.length) ≤ c * x.length := by
    calc K * (c₀ * x'.length) = (K * c₀) * x'.length := by ring
      _ ≤ c * x.length := Nat.mul_le_mul (by omega) (by omega)
  have h4 : K * t₀ ≤ K * ⌊(c₀ : ℝ) * P⌋₊ + K * (c₀ * x'.length) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ ht₀'
  show t ≤ ⌊(c : ℝ) * P⌋₊ + c * x.length
  omega

/-- The statement for the older input format and the older notion of computing. -/
theorem exists_program_fewTypes_old :
    ∃ (p : Program) (f : List ℕ → List ℕ) (e : ℕ),
      (∀ (r q : ℕ) (ε : ℚ) (n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
        0 < ε → Lax185574.FewTypes.EncodesInput x r q ε n G →
          (∃ s, EncodesSequence (f x) s ∧ IsConstructionSequence G s) ∧
            ∀ v ∈ f x, v ≤ (f x).length + n) ∧
      ∀ (C : GraphClass), MonadicallyDependent C → ∀ q : ℕ,
        ∃ a : ℕ, 1 ≤ a ∧ ∀ (r : ℕ) (ε : ℚ), 0 < ε → ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
            (∀ w : ℕ, ComputesInTime w p
              {x | Lax185574.FewTypes.EncodesInput x r q ε n G ∧
                ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              f (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * x.length)) ∧
            ∀ (x : List ℕ) (s : List (PartialGraph (Fin n))),
              Lax185574.FewTypes.EncodesInput x r q ε n G → EncodesSequence (f x) s →
                (s.length : ℝ) ≤ c * ((n : ℝ) + 1) ^ (1 + (a : ℝ) * ε) ∧
                (width r q s : ℝ) ≤ c * ((n : ℝ) + 1) ^ ((a : ℝ) * ε) := by
  obtain ⟨p₀, f₀, e₀, A, hcorr, hclass⟩ :=
    Lax185574Proofs.Shim.DefinableSequences.exists_program_definableSequence
  obtain ⟨p, K, hsim⟩ := simulate p₀ radiusRewrite
  refine ⟨p, fun x => f₀ (radiusRewrite.apply fun _ => x), e₀ + 1, ?_, ?_⟩
  · intro r q ε n G x hε hx
    exact hcorr (r + 7 ^ q) ε n G _ (by have := Nat.one_le_pow q 7 (by norm_num); omega) hε
      (encodesInput_rewrite hx)
  intro C hC q
  obtain ⟨a₀, ha₀1, ha₀⟩ := hclass C hC
  obtain ⟨D, hD⟩ := Lax185574Proofs.Shim.DefinableToTypes.width_le_of_isRadiusDefinable q C hC 7
  refine ⟨a₀ * D + a₀, by omega, fun r ε hε η hη => ?_⟩
  have hr' : 1 ≤ r + 7 ^ q := by have := Nat.one_le_pow q 7 (by norm_num); omega
  obtain ⟨c₀, hc₀⟩ := ha₀ (r + 7 ^ q) ε hr' hε η hη
  obtain ⟨F, hF⟩ := hD (⌈(A : ℚ) * ((r + 7 ^ q : ℕ) : ℚ) / ε⌉₊ + A)
  set c := K * c₀ + K * (q + 9) + 2 * c₀ * (7 ^ q + 1) ^ e₀ + 2 * K + 4 + c₀ +
    F * (c₀ + 1) ^ D with hc
  refine ⟨c, fun n G hG =>
    ⟨computesInTime_radiusRewrite hsim hη (hc₀ n G hG).1 (by omega), fun x s hx hs => ?_⟩⟩
  · -- the bounds on the output
    have hlen := (hc₀ n G hG).2 _ s (encodesInput_rewrite hx) hs
    obtain ⟨hlen, hdef⟩ := hlen
    obtain ⟨⟨s', hs', hcs⟩, -⟩ := hcorr (r + 7 ^ q) ε n G _ hr' hε (encodesInput_rewrite hx)
    rw [encodesSequence_unique hs hs'] at hdef hlen
    have hW := hF r _ n G s' hG hcs hdef
    rw [encodesSequence_unique hs hs']
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hc₀c : (c₀ : ℝ) ≤ c := by exact_mod_cast (show c₀ ≤ c by omega)
    have haa : (a₀ : ℝ) ≤ ((a₀ * D + a₀ : ℕ) : ℝ) := by exact_mod_cast (show a₀ ≤ a₀ * D + a₀ by omega)
    constructor
    · refine hlen.trans ?_
      apply mul_le_mul hc₀c _ (by positivity) (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
    · set Q : ℝ := ((n : ℝ) + 1) ^ ((a₀ : ℝ) * ε)
      have hQ : 1 ≤ Q := Real.one_le_rpow hn1 (by positivity)
      have hs0 : ((⌊(c₀ : ℝ) * Q⌋₊ + 1 : ℕ) : ℝ) ≤ (c₀ + 1) * Q := by
        push_cast
        have := Nat.floor_le (show (0 : ℝ) ≤ c₀ * Q by positivity)
        nlinarith
      have hW' : (width r q s' : ℝ) ≤ F * (((c₀ : ℝ) + 1) * Q) ^ D := by
        have : (width r q s' : ℝ) ≤ (F : ℝ) * ((⌊(c₀ : ℝ) * Q⌋₊ + 1 : ℕ) : ℝ) ^ D := by
          exact_mod_cast hW
        refine this.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hs0 D
      refine hW'.trans ?_
      rw [mul_pow, ← mul_assoc]
      have hQD : Q ^ D = ((n : ℝ) + 1) ^ ((a₀ : ℝ) * ε * D) := by
        rw [Real.rpow_mul_natCast (by positivity)]
      rw [hQD]
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · have : ((F * (c₀ + 1) ^ D : ℕ) : ℝ) ≤ c := by exact_mod_cast (show F * (c₀ + 1) ^ D ≤ c by omega)
        push_cast at this; exact this
      · apply Real.rpow_le_rpow_of_exponent_le hn1
        push_cast
        nlinarith


open Lax185574.Graphs Lax185574.Algorithms Lax185574.Encoding Lax185574Proofs.Interface in
/--
---
conclusion: Lax185574.FewTypes.exists_program_fewTypes
---
The proof of the few-types theorem. Run the algorithm of the theorem on
definable construction sequences with radius `r + 7^q`, where `h = 7^q`
is the radius of the lemma passing from definability to few types. The
output is radius-`(r + 7^q)` definable with `⌈A(r + 7^q)/ε⌉ + A`
predicates and `s ≤ c₀ (n+1)^(a₀ε)` parameters, so its radius-`r`
depth-`q` width is at most `F (s+1)^D`, which is `O((n+1)^(a₀Dε))`. So
`a = a₀D + a₀` works for the width and the length, and `a ≥ 1` since `a₀
≥ 1`. The exponent `3 + η` of the time is passed on to the theorem on
definable construction sequences. The program is a simulation of the
program of the theorem on definable construction sequences on the
rewritten input, one word bit shorter, and the word-length exponent
grows by one to pay for the larger first entry.

The proof is carried out for the input format with the graph in
compressed sparse row form and the notion `Lax185574.Computing.Computes`. The algorithm converts the word of the
graph into compressed sparse rows (`Interface.nbr_bridge`) and runs the
program for that format. The script of a graph is the one whose encoding the program
outputs on the converted input.
-/
theorem exists_program_fewTypes :
    ∃ (A : Algorithm) (script : ℕ → ℕ → ℚ → (G : Graph) → Script G.n),
      (∀ (r q : ℕ) (ε : ℚ) (G : Graph), 0 < ε →
        IsConstructionSequence G.toSimpleGraph (script r q ε G).run ∧
          (script r q ε G).HasSmallNumbers) ∧
      ∀ C : Lax185574.Graphs.GraphClass, Lax185574.MonadicDependence.MonadicallyDependent C → ∀ q : ℕ,
        ∃ a : ℕ, 1 ≤ a ∧
        ∀ (r : ℕ) (ε : ℚ), 0 < ε → ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ G ∈ C,
            A.Computes c (r, q, ε, G) (script r q ε G) ((G.n : ℝ) ^ (3 + η)) ∧
            ((script r q ε G).run.length : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ (1 + (a : ℝ) * ε) ∧
            (width r q (script r q ε G).run : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ ((a : ℝ) * ε) := by
  obtain ⟨p, f, e, hcorr, hclass⟩ := exists_program_fewTypes_old
  obtain ⟨q', Kq, hq⟩ := nbr_bridge 5 p
  refine ⟨⟨q', e + 1⟩,
    fun r q ε G => scriptOf f G.n (encode (r, q, ε) ++ csrWord (nbLists G.toSimpleGraph)),
    fun r q ε G hε => ?_, fun C hC q => ?_⟩
  · obtain ⟨⟨s, hs, hcs⟩, hsm⟩ := hcorr r q ε G.n G.toSimpleGraph _ hε
      ⟨_, encodesGraph_csrWord _, rfl⟩
    obtain ⟨hfx, hrun⟩ := scriptOf_spec hs
    refine ⟨hrun ▸ hcs, fun v hv => ?_⟩
    rw [← hfx] at hv ⊢
    exact hsm v hv
  · obtain ⟨a, ha1, ha⟩ := hclass (toOld C) (monadicallyDependent_toOld hC) q
    refine ⟨a, ha1, fun r ε hε η hη => ?_⟩
    obtain ⟨c, hc⟩ := ha r ε hε η hη
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, (2 : ℝ) ^ (3 + η) ≤ Q := ⟨⌈(2 : ℝ) ^ (3 + η)⌉₊, Nat.le_ceil _⟩
    refine ⟨seqConst Kq c e Q 5, fun G hG => ?_⟩
    have hmem : toOld C G.n G.toSimpleGraph := (toOld_iff C G).mpr hG
    obtain ⟨hcomp, hout⟩ := hc G.n G.toSimpleGraph hmem
    have henc : Lax185574.FewTypes.EncodesInput
        (encode (r, q, ε) ++ csrWord (nbLists G.toSimpleGraph)) r q ε G.n G.toSimpleGraph :=
      ⟨_, encodesGraph_csrWord _, rfl⟩
    obtain ⟨⟨s, hs, -⟩, -⟩ := hcorr r q ε G.n G.toSimpleGraph _ hε henc
    obtain ⟨hfx, hrun⟩ := scriptOf_spec hs
    obtain ⟨hlen, hwid⟩ := hout _ s henc hs
    rw [hrun] at hlen hwid
    have hcc : (c : ℝ) ≤ seqConst Kq c e Q 5 := by exact_mod_cast le_seqConst Kq c e Q 5
    refine ⟨?_, le_trans hlen (mul_le_mul_of_nonneg_right hcc (by positivity)),
      le_trans hwid (mul_le_mul_of_nonneg_right hcc (by positivity))⟩
    have ha' : encode (r, q, ε, G) = encode (r, q, ε) ++ nbWord (nbLists G.toSimpleGraph) := by
      simp only [KitG3.encode_pair, encode_graph, toWord_graph_eq, List.append_assoc]
    refine seq_wrap hq (length_encode_nat_nat_rat r q ε) G.toSimpleGraph ha' hη hQ
      (fun w hw => ?_)
    rw [← hfx]
    exact hcomp w _ ⟨henc, hw⟩

end Lax185574Proofs.FewTypes
