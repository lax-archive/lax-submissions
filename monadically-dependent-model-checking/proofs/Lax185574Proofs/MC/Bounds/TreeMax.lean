import Lax185574Proofs.MC.Asm.Defs
import Lax185574Proofs.MC.Sizes
import Lax185574Proofs.RamPipeFwd
import Lax185574.MergeLift
import Lax185574.TypeTreeSizes
import Lax185574Proofs.Interface.Shim.MergeLift
import Lax185574Proofs.Interface.Shim.ResolveLift

/-!
The trees of the vertices along a construction sequence are polynomial
in the width.

For a partial graph `s[t]` that is not the last one this is
`tree_length_le_width`. The last partial graph is obtained by a step
from the one before. After a resolve, the second clause of the resolve
lift bounds its trees by the parameter `T`, which is at most the width
by `treeCount_le_count`. After a merge, the tree is the output of the
merge lift on a tree of the partial graph before, so it is no longer
than the running time of the merge lift, at a word length large enough
for its time bound. A sequence of length one consists of an initial
partial graph, in which every ball is a single vertex, so it realizes
one type of tuples in each ball.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax808846.RamComputes Lax185574.Computing Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.ConstructionSequences
open Lax185574.TypeTrees Lax185574.Width Lax185574.PartialGraphEncoding Lax185574.ResolveLift
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

/-- The output of a program that computes `b` from `a` is no longer than
its time bound. -/
theorem wordLength_le_time {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b : β} {T : ℕ → ℕ} (h : Computes p e c a b T) :
    wordLength b ≤ T (wordLength a) := by
  set W := c * ((toWord a).length + maxEntry (toWord a) + 1) ^ e + T (wordLength a)
  have hW : W < 2 ^ W := Nat.lt_two_pow_self
  have hadm : WordAdmissible e c W (toWord a) := by
    intro v hv
    have := le_maxEntry hv
    have : c * ((toWord a).length + v + 1) ^ e ≤
        c * ((toWord a).length + maxEntry (toWord a) + 1) ^ e := by gcongr
    omega
  obtain ⟨t, ht, hr⟩ := (h W hadm).2 (by omega) (toWord a) rfl
  exact le_trans (Lax185574Proofs.RamSim.runsTo_out_length hr) ht

theorem ball_initial {G : PartialGraph (Fin n)} (h0 : G.edge = ⊥) (h1 : G.nonEdge = ⊥) (r : ℕ)
    (v : Fin n) : G.ball r v ⊆ {v} := by
  intro u hu
  obtain ⟨p, -⟩ := hu
  have hres : G.resolved = ⊥ := by simp [PartialGraph.resolved, h0, h1]
  cases p with
  | nil => rfl
  | cons h _ => simp [hres] at h

theorem typeCount_singleton_le (G : PartialGraph (Fin n)) (k q : ℕ) {X : Set (Fin n)} {v : Fin n}
    (hX : X ⊆ {v}) : partialTypeCount G k q X ≤ 1 := by
  unfold partialTypeCount Lax185574.FirstOrderTypes.typeCount Lax185574.FirstOrderTypes.types
  have hs : Set.Subsingleton {u : Fin k → Fin n | ∀ i, u i ∈ X} := by
    intro a ha b hb
    funext i
    have h1 := hX (ha i)
    have h2 := hX (hb i)
    simp only [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2]
  rcases (hs.image (@Lax185574.FirstOrderTypes.rankType language (Fin n) G.structure q k)).eq_empty_or_singleton with h | ⟨y, h⟩
  · rw [h]; simp
  · rw [h]; simp

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- **Trees along a construction sequence.** -/
theorem treeMax_le (q : ℕ) : ∃ c a : ℕ, ∀ (n : ℕ) (Gr : SimpleGraph (Fin n))
    (s : List (PartialGraph (Fin n))) (K : ℕ), IsConstructionSequence Gr s →
    width (rhoPlus 1 q) (rhoPlus 1 q + 1 + q) s ≤ K → treeMax s q ≤ c * (K + 1) ^ a := by
  obtain ⟨c1, a1, h1⟩ := tree_length_le_width q
  obtain ⟨pM, eM, hM⟩ := Lax185574Proofs.Shim.MergeLift.exists_program_mergeLift
  obtain ⟨cM, aM, hM1⟩ := hM 1 q
  obtain ⟨pR, eR, hR⟩ := Lax185574Proofs.Shim.ResolveLift.exists_program_resolveLift
  obtain ⟨cR, aR, hR1⟩ := hR 1 q
  obtain ⟨c2, a2, h2⟩ := Lax185574.TypeTreeSizes.tree_length_le 1 q le_rfl
  refine ⟨c1 + cM * (c1 + 3) ^ aM + cR * ((q + 1) * (1 + q) + 1) ^ aR + c2 * 2 ^ a2,
    a1 + a1 * aM + aR, fun n Gr s K hcs hK => ?_⟩
  obtain ⟨hs, hinit, hstep, -, -, -⟩ := hcs
  set B := c1 + cM * (c1 + 3) ^ aM + cR * ((q + 1) * (1 + q) + 1) ^ aR + c2 * 2 ^ a2
  set Y := K + 1 with hYd
  have hY : 1 ≤ Y := by omega
  have hpow : ∀ b, b ≤ a1 + a1 * aM + aR → Y ^ b ≤ Y ^ (a1 + a1 * aM + aR) :=
    fun b hb => Nat.pow_le_pow_right hY hb
  -- the trees of a partial graph that is not the last one
  have hmid : ∀ (t : ℕ) (ht : t + 1 < s.length) (v : Fin n),
      wordLength (tree s[t] 1 q ![v]) ≤ c1 * Y ^ a1 := by
    intro t ht v
    exact le_trans (h1 n s hstep t ht v) (by gcongr; omega)
  have key : ∀ (t : ℕ) (ht : t < s.length) (v : Fin n),
      wordLength (tree s[t] 1 q ![v]) ≤ B * Y ^ (a1 + a1 * aM + aR) := by
    intro t ht v
    by_cases hlt : t + 1 < s.length
    · calc _ ≤ c1 * Y ^ a1 := hmid t hlt v
        _ ≤ B * Y ^ (a1 + a1 * aM + aR) := Nat.mul_le_mul (by omega) (hpow _ (by omega))
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · -- a sequence of length one
      have hhead : s.head hs = s[0] := List.head_eq_getElem hs
      obtain ⟨e0, e1, -⟩ := hinit
      rw [hhead] at e0 e1
      have hc := typeCount_singleton_le s[0] (rhoPlus 1 q + 1 + q) (rhoPlus 1 q + 1 + q)
        (ball_initial e0 e1 (rhoPlus 1 q) v)
      calc _ ≤ c2 * (partialTypeCount s[0] (rhoPlus 1 q + 1 + q) (rhoPlus 1 q + 1 + q)
            (s[0].ball (rhoPlus 1 q) v) + 1) ^ a2 := h2 n s[0] v
        _ ≤ c2 * 2 ^ a2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ ≤ B * 1 := by omega
        _ ≤ B * Y ^ (a1 + a1 * aM + aR) := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hY)
    -- the last partial graph
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    obtain ⟨P, Q, hst⟩ := hstep u ht
    have hw : ∀ a : Fin n, partialTypeCount s[u] (rhoPlus 1 q + 1 + q) (rhoPlus 1 q + 1 + q)
        (s[u + 1].ball (rhoPlus 1 q) a) ≤ K :=
      fun a => le_trans (le_width _ _ s ht a) hK
    rcases hst with ⟨hPQ, he⟩ | he | he
    · -- after a merge
      have hT := wordLength_le_time (hM1 n s[u] 1 ![v] P Q le_rfl hPQ)
      rw [← he] at hT
      have hin : wordLength (tree s[u] 1 q ![v], P, Q) = wordLength (tree s[u] 1 q ![v]) + 2 := by
        simp [wordLength, word_simps]
      rw [hin] at hT
      have hm := hmid u (by omega) v
      calc _ ≤ cM * (wordLength (tree s[u] 1 q ![v]) + 2 + 1) ^ aM := hT
        _ ≤ cM * ((c1 + 3) * Y ^ a1) ^ aM := by
          gcongr
          have : 1 ≤ Y ^ a1 := Nat.one_le_pow _ _ hY
          nlinarith
        _ = cM * (c1 + 3) ^ aM * Y ^ (a1 * aM) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ B * Y ^ (a1 + a1 * aM + aR) := Nat.mul_le_mul (by omega) (hpow _ (by omega))
    all_goals
      have hTc := treeCount_le_count s[u] s[u + 1] 1 q le_rfl K hw
      have hb : wordLength (tree s[u + 1] 1 q ![v]) ≤
          cR * (treeCount s[u] s[u + 1] 1 q + 1) ^ aR := by
        first
          | (have e : resolveBy s[u] true P Q = s[u + 1] := by rw [he]; rfl
             have hb := (hR1 n s[u] P Q true le_rfl).2 v
             rw [e] at hb; exact hb)
          | (have e : resolveBy s[u] false P Q = s[u + 1] := by rw [he]; rfl
             have hb := (hR1 n s[u] P Q false le_rfl).2 v
             rw [e] at hb; exact hb)
      calc _ ≤ cR * (treeCount s[u] s[u + 1] 1 q + 1) ^ aR := hb
        _ ≤ cR * (((q + 1) * (1 + q) + 1) * Y) ^ aR := by
          gcongr
          rw [hYd]; nlinarith [hTc]
        _ = cR * ((q + 1) * (1 + q) + 1) ^ aR * Y ^ aR := by rw [mul_pow]; ring
        _ ≤ B * Y ^ (a1 + a1 * aM + aR) := Nat.mul_le_mul (by omega) (hpow _ (by omega))
  unfold treeMax
  apply foldr_max_le
  intro z hz
  simp only [List.mem_map, List.mem_range] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  apply Finset.sup_le
  intro a _
  have : sAt s t = s[t] := by simp [sAt, List.getD_eq_getElem?_getD, ht]
  rw [this]
  exact key t ht a

end Lax185574Proofs.MC

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.ConstructionSequences
open Lax185574.SequenceEncoding

/-- The colors along the sequence of a script are entries of its word:
initial colors or targets of merges. -/
theorem color_mem_script {n : ℕ} (σ : Script n) {H : PartialGraph (Fin n)} (hH : H ∈ σ.run)
    (v : Fin n) : H.color v ∈ toWord σ := by
  have hw : toWord σ = toWord σ.colors ++ toWord σ.steps := rfl
  have hc : ∀ u, σ.colors u ∈ toWord σ := by
    intro u
    rw [hw]
    apply List.mem_append_left
    show σ.colors u ∈ (List.ofFn σ.colors).length ::
      ((List.ofFn σ.colors).map (toWord : ℕ → List ℕ)).flatten
    simp only [List.mem_cons, List.mem_flatten, List.mem_map, List.mem_ofFn]
    exact Or.inr ⟨[σ.colors u], ⟨σ.colors u, ⟨u, rfl⟩, rfl⟩, by simp⟩
  have hP : ∀ P Q, Step.merge P Q ∈ σ.steps → P ∈ toWord σ := by
    intro P Q hm
    rw [hw]
    apply List.mem_append_right
    show P ∈ σ.steps.length :: (σ.steps.map toWord).flatten
    simp only [List.mem_cons, List.mem_flatten, List.mem_map]
    exact Or.inr ⟨[0, P, Q], ⟨_, hm, rfl⟩, by simp⟩
  have key : ∀ (l : List Step) (G : PartialGraph (Fin n)), (∀ u, G.color u ∈ toWord σ) →
      (∀ P Q, Step.merge P Q ∈ l → P ∈ toWord σ) →
      ∀ H ∈ l.scanl apply G, ∀ u, H.color u ∈ toWord σ := by
    intro l
    induction l with
    | nil => intro G hG _ H hH; simp at hH; subst hH; exact hG
    | cons a l ih =>
      intro G hG hl H hH
      simp only [List.scanl_cons, List.mem_cons] at hH
      rcases hH with rfl | hH
      · exact hG
      refine ih (apply G a) ?_ (fun P Q h => hl P Q (by simp [h])) H hH
      intro u
      cases a with
      | merge P Q =>
        show (if G.color u = Q then P else G.color u) ∈ _
        split_ifs
        · exact hl P Q (by simp)
        · exact hG u
      | resolvePos P Q => exact hG u
      | resolveNeg P Q => exact hG u
  exact key σ.steps _ (fun u => hc u) hP H hH v

end Lax185574Proofs.MC
