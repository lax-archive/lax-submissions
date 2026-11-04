import Lax185574.DefinableSequences
import Lax185574.ComputingChains
import Lax185574.ChainConstructionSequences
import Lax185574Proofs.Interface.Shim.BoundedVCClasses
import Lax185574.NeighborhoodComplexityBound
import Lax185574Proofs.RamPipe
import Lax185574Proofs.Compose.CsrToGraph
import Lax185574Proofs.Compose.Monotone
import Lax185574Proofs.Compose.Basic
import Lax185574Proofs.ComputingChains
import Lax185574Proofs.Interface.Shim.ComputingChains
import Lax185574Proofs.Interface.Shim.ChainConstructionSequences
import Lax185574Proofs.Words.PrefixFree
import Lax185574Proofs.LegacyInputs
import Lax185574Proofs.Interface.KitG3
import Lax185574Proofs.Interface.SeqBridge

/-!
Proof of thm:skel-def-seq (`DefinableSequences`) from
thm:monadic-dependence-implies-definable-mw (`ComputingChains`),
lem:better-definable-mw-from-sets (`ChainConstructionSequences`),
obs:md-vc (`BoundedVCClasses`) and lem:ss (`NeighborhoodComplexityBound`).

The program converts the compressed sparse row word of the graph into
the word of the graph, computes a chain at radius `5r + 1` and turns it
into a construction sequence. The first phase is the command
`Compose.csrToGraph`, the other two are the programs of the cited
lemmas, and the phases are joined by `pipe`.
-/

namespace Lax185574Proofs.DefinableSequences

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax808846.RamComputes Lax271696.GraphEncoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.Chains
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.LocalDefinability
open Lax185574.Computing Lax185574.VCDimension Lax185574.ConstructionWidth
open Lax185574.DefinableSequences (EncodesInput)
open Lax185574.ChainConstructionSequences (chainBound)
open Lax185574Proofs.Simulate Lax185574Proofs.Compose Lax185574Proofs.Words

/-! ### Decoding the input -/

theorem toWord_rat_shape (ε : ℚ) : ∃ a b : ℕ, toWord ε = [a, b, ε.den] := by
  change ∃ a b : ℕ, toWord ε.num ++ [ε.den] = [a, b, ε.den]
  rcases h : ε.num with m | m
  · exact ⟨0, m, rfl⟩
  · exact ⟨1, m, rfl⟩

/-- The graph of a compressed sparse row word is determined by the
word. -/
theorem encodesGraph_unique {g : List ℕ} {n n' : ℕ} {G : SimpleGraph (Fin n)}
    {G' : SimpleGraph (Fin n')} (h : EncodesGraph g n G) (h' : EncodesGraph g n' G') :
    (⟨n, G⟩ : Σ n, SimpleGraph (Fin n)) = ⟨n', G'⟩ := by
  have hn : n = n' := h.vertexCount_eq.symm.trans h'.vertexCount_eq
  subst hn
  have : G = G' := by
    ext u v
    rw [h.adj_iff, h'.adj_iff]
  rw [this]

theorem encodesInput_unique {x : List ℕ} {r r' : ℕ} {ε ε' : ℚ} {n n' : ℕ}
    {G : SimpleGraph (Fin n)} {G' : SimpleGraph (Fin n')}
    (h : EncodesInput x r ε n G) (h' : EncodesInput x r' ε' n' G') :
    r = r' ∧ ε = ε' ∧ (⟨n, G⟩ : Σ n, SimpleGraph (Fin n)) = ⟨n', G'⟩ := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', he⟩ := h'
  obtain ⟨h1, h2⟩ := prefix_inj' he
  simp only [Prod.mk.injEq] at h1
  subst h2
  exact ⟨h1.1, h1.2, encodesGraph_unique hg hg'⟩

/-- The output of a function of the decoded input, and `[]` on words
that encode nothing. -/
noncomputable def decodeOut (F : ℕ → ℚ → (Σ n, SimpleGraph (Fin n)) → List ℕ) (x : List ℕ) :
    List ℕ :=
  open Classical in
  if h : ∃ p : ℕ × ℚ × (Σ n, SimpleGraph (Fin n)), EncodesInput x p.1 p.2.1 p.2.2.1 p.2.2.2 then
    F (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2 else []

theorem decodeOut_eq (F : ℕ → ℚ → (Σ n, SimpleGraph (Fin n)) → List ℕ) {x : List ℕ} {r : ℕ}
    {ε : ℚ} {n : ℕ} {G : SimpleGraph (Fin n)} (hx : EncodesInput x r ε n G) :
    decodeOut F x = F r ε ⟨n, G⟩ := by
  have h : ∃ p : ℕ × ℚ × (Σ n, SimpleGraph (Fin n)), EncodesInput x p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    ⟨(r, ε, ⟨n, G⟩), hx⟩
  unfold decodeOut
  rw [dif_pos h]
  obtain ⟨h1, h2, h3⟩ := encodesInput_unique (Classical.choose_spec h) hx
  have h3' : (Classical.choose h).2.2 = ⟨n, G⟩ := h3
  rw [h1, h2, h3']

/-! ### Sizes -/

theorem toWord_graph_entry_le {n : ℕ} (G : SimpleGraph (Fin n)) : ∀ v ∈ toWord G, v ≤ n := by
  classical
  intro v hv
  rw [toWord_graph] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact le_rfl
  · simp only [blocksWord, graphBlocks, List.mem_flatten, List.mem_map, List.mem_ofFn] at hv
    obtain ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, hvu⟩ := hv
    rcases List.mem_cons.mp hvu with rfl | hvu
    · have : (Finset.words (Finset.univ.filter (G.Adj u))).length ≤ n := by
        simp only [Finset.words, Finset.length_sort]
        exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
      rw [setBlock_length]; omega
    · simp only [setBlock, List.mem_flatten, List.mem_map] at hvu
      obtain ⟨_, ⟨w, hw, rfl⟩, hvw⟩ := hvu
      simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hw
      obtain ⟨a, -, rfl⟩ := hw
      change v ∈ [1, a.val] at hvw
      simp at hvw
      have := a.isLt
      omega

theorem setList_bounds {n : ℕ} (l : List (Finset (Fin n))) :
    (toWord l).length ≤ (l.length + 1) * (2 * n + 1) ∧ ∀ v ∈ toWord l, v ≤ l.length + n := by
  have hy := toWord_setList l
  have hblocks : ∀ u ∈ l.map setBlock, u.length ≤ 2 * n := by
    intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨S, -, rfl⟩ := hu
    rw [setBlock_length]
    have : (Finset.words S).length ≤ n := by
      simp only [Finset.words, Finset.length_sort]
      exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
    omega
  have hbw : ∀ bs : List (List ℕ), (∀ u ∈ bs, u.length ≤ 2 * n) →
      (blocksWord bs).length ≤ bs.length * (2 * n + 1) := by
    intro bs
    induction bs with
    | nil => intro _; simp [blocksWord]
    | cons u bs ih =>
        intro h
        rw [blocksWord_cons, List.length_append, List.length_cons]
        have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
        have := h u List.mem_cons_self
        simp only [blk, List.length_cons]
        have e : (bs.length + 1) * (2 * n + 1) = bs.length * (2 * n + 1) + 2 * n + 1 := by ring
        omega
  refine ⟨?_, ?_⟩
  · have := hbw _ hblocks
    rw [List.length_map] at this
    rw [hy, List.length_cons]
    have e : (l.length + 1) * (2 * n + 1) = l.length * (2 * n + 1) + 2 * n + 1 := by ring
    omega
  · intro v hv
    rw [hy] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · simp
    · simp only [blocksWord, List.map_map, List.mem_flatten, List.mem_map, Function.comp] at hv
      obtain ⟨_, ⟨S, -, rfl⟩, hvu⟩ := hv
      rcases List.mem_cons.mp hvu with rfl | hvu
      · have : (Finset.words S).length ≤ n := by
          simp only [Finset.words, Finset.length_sort]
          exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
        rw [setBlock_length]; omega
      · simp only [setBlock, List.mem_flatten, List.mem_map] at hvu
        obtain ⟨_, ⟨u, hu, rfl⟩, hvu⟩ := hvu
        simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hu
        obtain ⟨a, -, rfl⟩ := hu
        change v ∈ [1, a.val] at hvu
        simp at hvu
        have := a.isLt
        omega

/-- The room for the word of a list of sets next to the graph. -/
theorem setList_room {s m n A : ℕ} (hs : s ≤ m) (hn : n + 1 ≤ A) :
    (s + 1) * (2 * n + 1) + 1 ≤ 2 * (m + 1) * A ^ 2 := by
  have h1 : (s + 1) * (2 * n + 1) + 1 ≤ (s + 1) * (2 * n + 2) := by
    have : (s + 1) * (2 * n + 2) = (s + 1) * (2 * n + 1) + (s + 1) := by ring
    omega
  have h2 : (s + 1) * (2 * n + 2) ≤ (m + 1) * (2 * A) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : A ≤ A ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : (m + 1) * (2 * A) ≤ 2 * (m + 1) * A ^ 2 := by
    have : (m + 1) * (2 * A) = 2 * ((m + 1) * A) := by ring
    rw [this, mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h3)
  omega

theorem maxEntry_le_of_subset {x y : List ℕ} (hy : y ≠ []) (h : ∀ v ∈ y, v ∈ x) :
    maxEntry y ≤ maxEntry x :=
  le_maxEntry (h _ (maxEntry_mem hy))

/-! ### The rewrites -/

/-- The graph part of the input. -/
def ρGraphPart : Rewrite 1 := [.slice 0 (.lit 4) none]
/-- `r, a, b, den` of the input, then the length of the graph word and
the graph word. -/
def ρHead : Rewrite 2 :=
  [.expr (.entry 1 0), .expr (.entry 1 1), .expr (.entry 1 2), .expr (.entry 1 3), .expr (.len 0),
    .slice 0 (.lit 0) none]
/-- The word of `(5r+o, ε, G)`. The program of thm:skel-def-seq uses
`o = 1`. -/
def ρChain (o : ℕ) : Rewrite 1 :=
  [.expr (.add (.mul (.lit 5) (.entry 0 0)) (.lit o)), .expr (.entry 0 1), .expr (.entry 0 2),
    .expr (.entry 0 3), .slice 0 (.lit 5) none]
/-- The word of `(G, S)`. -/
def ρPair : Rewrite 2 := [.slice 1 (.lit 5) none, .slice 0 (.lit 0) none]

theorem ρGraphPart_apply (r a b c : ℕ) (g : List ℕ) :
    ρGraphPart.apply (fun _ => r :: a :: b :: c :: g) = g := by
  simp [ρGraphPart, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρHead_apply (r a b c : ℕ) (g yG : List ℕ) :
    ρHead.apply ![yG, r :: a :: b :: c :: g] = r :: a :: b :: c :: yG.length :: yG := by
  simp [ρHead, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρChain_apply (o r a b c m : ℕ) (yG : List ℕ) :
    (ρChain o).apply (fun _ => r :: a :: b :: c :: m :: yG) = (5 * r + o) :: a :: b :: c :: yG := by
  simp [ρChain, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρPair_apply (r a b c m : ℕ) (yG yS : List ℕ) :
    ρPair.apply ![yS, r :: a :: b :: c :: m :: yG] = yG ++ yS := by
  simp [ρPair, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρGraphPart_cost (xs : Fin 1 → List ℕ) : ρGraphPart.cost xs = 3 := by
  simp [ρGraphPart, Rewrite.cost, Segment.cost, HExpr.cost]
theorem ρHead_cost (xs : Fin 2 → List ℕ) : ρHead.cost xs = 13 := by
  simp [ρHead, Rewrite.cost, Segment.cost, HExpr.cost]
theorem ρChain_cost (o : ℕ) (xs : Fin 1 → List ℕ) : (ρChain o).cost xs = 15 := by
  simp [ρChain, Rewrite.cost, Segment.cost, HExpr.cost]
theorem ρPair_cost (xs : Fin 2 → List ℕ) : ρPair.cost xs = 5 := by
  simp [ρPair, Rewrite.cost, Segment.cost, HExpr.cost]

theorem ρGraphPart_fits {w : ℕ} {x : List ℕ} (hx : x.length < 2 ^ w) (h4 : 4 < 2 ^ w) :
    ρGraphPart.Fits w (fun _ => x) := by
  refine ⟨fun _ => hx, ?_, ?_⟩
  · simp only [ρGraphPart, Rewrite.apply, Segment.apply, HExpr.eval]; simp; omega
  · intro seg hs
    simp only [ρGraphPart, List.mem_singleton] at hs
    subst hs
    exact ⟨trivial, h4⟩

theorem ρHead_fits {w : ℕ} {yG x : List ℕ} (hy : yG.length + 5 < 2 ^ w) (hx : x.length < 2 ^ w) :
    ρHead.Fits w ![yG, x] := by
  have h3 : 3 < 2 ^ w := by omega
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> simp <;> omega
  · simp [ρHead, Rewrite.apply, Segment.apply, HExpr.eval]; omega
  · intro seg hs
    simp only [ρHead, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · show 0 < 2 ^ w; omega
    · show 1 < 2 ^ w; omega
    · show 2 < 2 ^ w; omega
    · show 3 < 2 ^ w; omega
    · trivial
    · exact ⟨trivial, by show 0 < 2 ^ w; omega⟩

theorem ρChain_fits (o : ℕ) {w : ℕ} {z : List ℕ} (hz : z.length + 5 < 2 ^ w) :
    (ρChain o).Fits w (fun _ => z) := by
  refine ⟨fun _ => show z.length < 2 ^ w by omega, ?_, ?_⟩
  · simp [ρChain, Rewrite.apply, Segment.apply, HExpr.eval]; omega
  · intro seg hs
    simp only [ρChain, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨trivial, by show 0 < 2 ^ w; omega⟩, trivial⟩
    · show 1 < 2 ^ w; omega
    · show 2 < 2 ^ w; omega
    · show 3 < 2 ^ w; omega
    · exact ⟨trivial, by show 5 < 2 ^ w; omega⟩

theorem ρPair_fits {w : ℕ} {yS z : List ℕ} (hy : yS.length < 2 ^ w) (hz : z.length + 5 < 2 ^ w)
    (h : yS.length + z.length < 2 ^ w) :
    ρPair.Fits w ![yS, z] := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> simp <;> omega
  · simp [ρPair, Rewrite.apply, Segment.apply, HExpr.eval]; omega
  · intro seg hs
    simp only [ρPair, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨trivial, by show 5 < 2 ^ w; omega⟩
    · exact ⟨trivial, by show 0 < 2 ^ w; omega⟩

/-! ### The composition -/

/-- The function computed: the construction sequence of
`ChainConstructionSequences` on the chain of `ComputingChains` at radius
`5r + 1`. -/
noncomputable def outFun (o : ℕ) (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) → Script n)
    (S : ∀ n : ℕ, ℕ → ℚ → SimpleGraph (Fin n) → List (Finset (Fin n))) :
    ℕ → ℚ → (Σ n, SimpleGraph (Fin n)) → List ℕ :=
  fun r ε p => toWord (M p.1 p.2 (S p.1 (5 * r + o) ε p.2))

theorem rpow_mono_exp {N : ℝ} (hN : 1 ≤ N) {a b : ℝ} (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN h

/-- The program of thm:skel-def-seq at every radius `r`, including
`r = 0`: the facts of the two cited lemmas about the chain and the
construction sequence, the width bound of the chain at radius `5r + 1`,
and the running time for every constant above a threshold `c₁`. -/
theorem exists_program_core (o : ℕ) (ho : 1 ≤ o) :
    ∃ (p : Program) (e AC A₂ : ℕ)
      (Sch : ∀ n : ℕ, ℕ → ℚ → SimpleGraph (Fin n) → List (Finset (Fin n)))
      (M₂ : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) → Script n),
      (∀ (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)), 1 ≤ r → 0 < ε →
        IsChain (Sch n r ε G) ∧ ((Sch n r ε G).length : ℚ) ≤ AC * r / ε + AC) ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        IsConstructionSequence G (M₂ n G S).run ∧
        (∀ v ∈ toWord (M₂ n G S), v ≤ wordLength (M₂ n G S) + n) ∧
        (M₂ n G S).run.length ≤ A₂ * (n + 1) * (chainBound G S 1 + 1) ∧
        ∀ r : ℕ, 1 ≤ r →
          constructionWidth r (M₂ n G S).run ≤ chainBound G S r ∧
            IsRadiusDefinable G (M₂ n G S).run r (2 * S.length + 1) (chainBound G S r) 7) ∧
      ∀ (C : GraphClass), MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 0 < ε →
        ∀ η : ℝ, 0 < η → ∃ cC c₁ : ℕ,
          (∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
            (chainWidth G (5 * r + o) (Sch n (5 * r + o) ε G) : ℝ) ≤
              cC * ((n : ℝ) + 1) ^ (ε : ℝ)) ∧
          ∀ c : ℕ, c₁ ≤ c → ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G → ∀ w : ℕ,
            ComputesInTime w p
              {x | EncodesInput x r ε n G ∧ ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              (decodeOut (outFun o M₂ Sch))
              (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * x.length) := by
  obtain ⟨pC, eC, AC, Sch, hSch, hclassC⟩ :=
    Lax185574Proofs.Shim.ComputingChains.exists_program_chain
  obtain ⟨p₂, e₂, A₂, M₂, hM₂, c₂, hc₂⟩ :=
    Lax185574Proofs.Shim.ChainConstructionSequences.exists_constructionSequence_of_chain
  obtain ⟨pI, KI, hI⟩ := pipe pC p₂ (ρChain o) ρPair
  obtain ⟨p, K₀, h₀⟩ := pipe (Lax808846Proofs.Compile.compileProgram csrLayout csrToGraph) pI
    ρGraphPart ρHead
  set F := outFun o M₂ Sch
  refine ⟨p, 2 * eC + 2 * e₂ + 4, AC, A₂, Sch, M₂, hSch, hM₂, ?_⟩
  intro C hC r ε hε η hη
  set δ : ℝ := min η 1
  have hδ : 0 < δ := lt_min hη one_pos
  obtain ⟨cC, hcC⟩ := hclassC C hC (5 * r + o) ε (by omega) hε δ hδ
  set Mr := AC * ((5 * r + o) * ε.den + 1)
  set c₁ := 16 * (cC * (13 + o) ^ eC + c₂ * (7 * (Mr + 1)) ^ e₂ + c₂ * (Mr + 1) + cC + KI + K₀ +
    2 * Mr + 12) + K₀ * (617 + KI * (cC + c₂ * (Mr + 1) + 20)) + 600 * K₀ with hc₁
  refine ⟨cC, c₁, fun n G hG => (hcC n G hG).1, fun c hc n G hG w x ⟨hx, hadm⟩ => ?_⟩
  obtain ⟨g, hg, hxg⟩ := hx
  obtain ⟨a, b, hεw⟩ := toWord_rat_shape ε
  have hxr : x = r :: a :: b :: ε.den :: g := by
    rw [hxg]; change [r] ++ toWord ε ++ g = _; rw [hεw]; rfl
  rw [decodeOut_eq F ⟨g, hg, hxg⟩]
  set yG := toWord G with hyG
  set S := Sch n (5 * r + o) ε G
  obtain ⟨hch, hlenQ⟩ := hSch n (5 * r + o) ε G (by omega) hε
  set yS := toWord S
  set z := toWord (M₂ n G S)
  have hFz : F r ε ⟨n, G⟩ = z := rfl
  rw [hFz]
  -- the admissibility at the largest entry
  have hxne : x ≠ [] := by rw [hxr]; simp
  set Mx := maxEntry x
  set A' := x.length + Mx + 1
  have hA1 : 1 ≤ A' := by omega
  set e := 2 * eC + 2 * e₂ + 4
  have hcA : c * A' ^ e ≤ 2 ^ w := hadm Mx (maxEntry_mem hxne)
  set W := 2 ^ (w - 4)
  have hw4 : 4 ≤ w := by
    by_contra hlt
    have h1 : 2 ^ w ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : c ≤ c * A' ^ e := Nat.le_mul_of_pos_right _ (pow_pos hA1 _)
    omega
  have h2w : 2 ^ w = 16 * W := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]; congr 1; omega
  have h2w2 : 2 ^ (w - 2) = 4 * W := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hw24 : w - 2 - 2 = w - 4 := by omega
  rw [h2w] at hcA
  have sm : ∀ k j, 16 * k ≤ c → j ≤ e → k * A' ^ j ≤ W :=
    fun k j hk hj => Lax185574Proofs.ChainConstructionSequences.small hcA hk hj hA1
  -- sizes
  have hglen := hg.length_eq
  have hxlen : x.length = 4 + g.length := by rw [hxr]; simp; omega
  have hnA : n + 1 ≤ A' := by omega
  have hrM : r ≤ Mx := le_maxEntry (by rw [hxr]; simp)
  have haM : a ≤ Mx := le_maxEntry (by rw [hxr]; simp)
  have hbM : b ≤ Mx := le_maxEntry (by rw [hxr]; simp)
  have hdM : ε.den ≤ Mx := le_maxEntry (by rw [hxr]; simp)
  have hyGlen : yG.length ≤ 3 * (n + 1) ^ 2 := toWord_graph_length_le G
  have hyGent : ∀ v ∈ yG, v ≤ n := toWord_graph_entry_le G
  have hA2 : (n + 1) ^ 2 ≤ A' ^ 2 := Nat.pow_le_pow_left hnA 2
  have hmM : S.length ≤ Mr := Lax185574Proofs.ComputingChains.length_le_of_rat hε hlenQ
  obtain ⟨hySlen, hySent⟩ := setList_bounds S
  have hMx : Mx ≤ A' := by omega
  have hA'A2 : A' ≤ A' ^ 2 := Nat.le_self_pow (by norm_num) _
  -- the conversion
  have hgM : maxEntry g ≤ Mx :=
    maxEntry_le_of_subset (by intro h; rw [h] at hglen; simp at hglen; omega)
      (fun v hv => by rw [hxr]; simp [hv])
  obtain ⟨tg, htg, hrung⟩ := csrToGraph_runsTo hg (w - 2) (by
    rw [h2w2]
    have := sm 6 1 (by omega) (by omega)
    rw [pow_one] at this
    omega)
  -- the chain
  set x₁ := toWord (5 * r + o, ε, G)
  have hx₁ : x₁ = (5 * r + o) :: a :: b :: ε.den :: yG := by
    change [5 * r + o] ++ (toWord ε ++ toWord G) = _; rw [hεw]; rfl
  have hoA : o ≤ o * A' := Nat.le_mul_of_pos_right _ hA1
  have hoA2 : o * A' ≤ o * A' ^ 2 := Nat.mul_le_mul_left _ hA'A2
  have hA'1 : 1 ≤ A' ^ 2 := Nat.one_le_pow _ _ hA1
  have hadm₁ : WordAdmissible eC cC (w - 4) x₁ := by
    intro v hv
    have hv' : v ≤ 6 * A' + o * A' := by
      rw [hx₁] at hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | rfl | rfl | hv
      · omega
      · omega
      · omega
      · omega
      · have := hyGent v hv; omega
    have hl : x₁.length + v + 1 ≤ (13 + o) * A' ^ 2 := by
      rw [hx₁, add_mul]; simp only [List.length_cons]; omega
    calc cC * (x₁.length + v + 1) ^ eC ≤ cC * ((13 + o) * A' ^ 2) ^ eC :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _)
      _ = (cC * (13 + o) ^ eC) * A' ^ (2 * eC) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ W := sm _ _ (by omega) (by omega)
  set N : ℝ := (n : ℝ) + 1
  have hN : 1 ≤ N := by simp only [N]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδη : δ ≤ η := min_le_left _ _
  have hT₁ : ⌊(cC : ℝ) * N ^ ((3 : ℝ) + δ)⌋₊ ≤ W := by
    have h4 : N ^ ((3 : ℝ) + δ) ≤ ((n + 1 : ℕ) : ℝ) ^ (4 : ℕ) := by
      calc N ^ ((3 : ℝ) + δ) ≤ N ^ ((4 : ℕ) : ℝ) := rpow_mono_exp hN (by push_cast; linarith)
        _ = ((n + 1 : ℕ) : ℝ) ^ (4 : ℕ) := by rw [Real.rpow_natCast]; push_cast; rfl
    have : ⌊(cC : ℝ) * N ^ ((3 : ℝ) + δ)⌋₊ ≤ cC * (n + 1) ^ 4 := by
      apply Nat.floor_le_of_le
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h4) (Nat.cast_nonneg _)
    refine this.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnA 4)).trans ?_)
    exact sm cC 4 (by omega) (by omega)
  obtain ⟨t₁, ht₁, hrun₁⟩ := ((hcC n G hG).2 (w - 4) hadm₁).2 hT₁ x₁ rfl
  -- the construction sequence
  have hx₂ : toWord (G, S) = yG ++ yS := rfl
  have hadm₂ : WordAdmissible e₂ c₂ (w - 4) (toWord (G, S)) := by
    intro v hv
    have hMA : (Mr + 1) * A' = Mr * A' + A' := by ring
    have hMA' : Mr ≤ Mr * A' := Nat.le_mul_of_pos_right _ hA1
    have hv' : v ≤ (Mr + 1) * A' := by
      rw [hx₂] at hv
      rcases List.mem_append.mp hv with hv | hv
      · have := hyGent v hv; omega
      · have := hySent v hv; omega
    have hl : (toWord (G, S)).length + v + 1 ≤ 7 * (Mr + 1) * A' ^ 2 := by
      rw [hx₂, List.length_append]
      have := setList_room hmM hnA
      have h1 : yS.length ≤ (S.length + 1) * (2 * n + 1) := hySlen
      have h2 : yG.length ≤ 3 * (n + 1) ^ 2 := hyGlen
      have hQ1 : (Mr + 1) * A' ≤ (Mr + 1) * A' ^ 2 := Nat.mul_le_mul_left _ hA'A2
      have hQ2 : A' ^ 2 ≤ (Mr + 1) * A' ^ 2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      have e2 : 2 * (Mr + 1) * A' ^ 2 = 2 * ((Mr + 1) * A' ^ 2) := by ring
      have e7 : 7 * (Mr + 1) * A' ^ 2 = 7 * ((Mr + 1) * A' ^ 2) := by ring
      omega
    calc c₂ * ((toWord (G, S)).length + v + 1) ^ e₂ ≤ c₂ * (7 * (Mr + 1) * A' ^ 2) ^ e₂ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _)
      _ = (c₂ * (7 * (Mr + 1)) ^ e₂) * A' ^ (2 * e₂) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ W := sm _ _ (by omega) (by omega)
  have hT₂ : c₂ * (S.length + 1) * (n + 1) ^ 3 ≤ W := by
    calc c₂ * (S.length + 1) * (n + 1) ^ 3 ≤ c₂ * (Mr + 1) * A' ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hnA 3)
      _ ≤ W := sm _ _ (by omega) (by omega)
  obtain ⟨t₂, ht₂, hrun₂⟩ := ((hc₂ n G S hch) (w - 4) hadm₂).2 hT₂ _ rfl
  -- the inner pipe
  set zIn := r :: a :: b :: ε.den :: yG.length :: yG
  have hyS : yS.length + 1 ≤ W := by
    have := sm (2 * (Mr + 1)) 2 (by omega) (by omega)
    have := setList_room hmM hnA
    have h1 : yS.length ≤ (S.length + 1) * (2 * n + 1) := hySlen
    omega
  have hzIn : zIn.length + 6 ≤ W := by
    have := sm 9 2 (by omega) (by omega)
    simp only [zIn, List.length_cons]
    omega
  have hzlen : zIn.length = yG.length + 5 := by simp [zIn]
  have hrunI₁ : RunsTo (w - 2 - 2) pC ((ρChain o).apply fun _ => zIn) yS t₁ := by
    rw [ρChain_apply, hw24, ← hx₁]; exact hrun₁
  have hrunI₂ : RunsTo (w - 2 - 2) p₂ (ρPair.apply ![yS, zIn]) z t₂ := by
    rw [ρPair_apply, hw24, ← hx₂]; exact hrun₂
  have hKI : KI ≤ 2 ^ (w - 2 - 2) := by
    rw [hw24]; have := sm KI 0 (by omega) (by omega); simpa using this
  obtain ⟨tI, htI, hrunI⟩ := hI (w - 2) zIn yS z t₁ t₂ hKI (by rw [hw24]; omega)
    (ρChain_fits o (by rw [h2w2]; omega)) (ρPair_fits (by rw [h2w2]; omega) (by rw [h2w2]; omega)
      (by rw [h2w2]; omega)) hrunI₁ hrunI₂
  -- the outer pipe
  have hrun₀ : RunsTo (w - 2) (Lax808846Proofs.Compile.compileProgram csrLayout csrToGraph)
      (ρGraphPart.apply fun _ => x) yG tg := by
    rw [hxr, ρGraphPart_apply]; exact hrung
  have hrunI' : RunsTo (w - 2) pI (ρHead.apply ![yG, x]) z tI := by
    rw [hxr, ρHead_apply]; exact hrunI
  have hK0 : K₀ ≤ 2 ^ (w - 2) := by
    rw [h2w2]; have := sm K₀ 0 (by omega) (by omega); simp at this; omega
  have hxW : x.length + 6 ≤ W := by
    have := sm 7 1 (by omega) (by omega); rw [pow_one] at this; omega
  obtain ⟨t, ht, hrun⟩ := h₀ w x yG z tg tI hK0 (by rw [h2w2]; omega)
    (ρGraphPart_fits (by rw [h2w]; omega) (by rw [h2w]; omega))
    (ρHead_fits (by rw [h2w]; omega) (by rw [h2w]; omega)) hrun₀ hrunI'
  refine ⟨t, ?_, hrun⟩
  -- the time bound
  rw [ρGraphPart_cost, ρHead_cost] at ht
  rw [ρChain_cost, ρPair_cost] at htI
  set P : ℝ := N ^ ((3 : ℝ) + η)
  have hP1 : 1 ≤ P := Real.one_le_rpow hN (by linarith)
  have hP2 : ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ P := by
    calc ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) = N ^ ((2 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ P := rpow_mono_exp hN (by push_cast; linarith)
  have hP3 : ((n + 1 : ℕ) : ℝ) ^ (3 : ℕ) ≤ P := by
    calc ((n + 1 : ℕ) : ℝ) ^ (3 : ℕ) = N ^ ((3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
      _ ≤ P := rpow_mono_exp hN (by push_cast; linarith)
  have ht₁' : (t₁ : ℝ) ≤ cC * P := by
    have := Nat.floor_le (show (0 : ℝ) ≤ cC * N ^ ((3 : ℝ) + δ) by positivity)
    have ht₁b : t₁ ≤ ⌊(cC : ℝ) * N ^ ((3 : ℝ) + δ)⌋₊ := ht₁
    calc (t₁ : ℝ) ≤ ⌊(cC : ℝ) * N ^ ((3 : ℝ) + δ)⌋₊ := by exact_mod_cast ht₁b
      _ ≤ cC * N ^ ((3 : ℝ) + δ) := this
      _ ≤ cC * P := mul_le_mul_of_nonneg_left (rpow_mono_exp hN (by linarith)) (Nat.cast_nonneg _)
  have ht₂' : (t₂ : ℝ) ≤ c₂ * (Mr + 1) * P := by
    have : t₂ ≤ c₂ * (Mr + 1) * (n + 1) ^ 3 :=
      ht₂.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    have h' : (t₂ : ℝ) ≤ c₂ * (Mr + 1) * ((n + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by exact_mod_cast this
    refine h'.trans ?_
    exact mul_le_mul_of_nonneg_left hP3 (by positivity)
  have htg' : tg ≤ 600 * (n + 1) ^ 2 + 600 * x.length + 1 := by omega
  have htI' : tI ≤ KI * (t₁ + t₂ + 20) := htI.trans (le_of_eq (by ring))
  have ht' : t ≤ K₀ * (tg + tI + 16) := ht.trans (le_of_eq (by ring))
  set Y := K₀ * (600 * (n + 1) ^ 2 + 17 + KI * (t₁ + t₂ + 20))
  have htY : t ≤ Y + 600 * K₀ * x.length := by
    have : tg + tI + 3 + 13 ≤ 600 * (n + 1) ^ 2 + 17 + KI * (t₁ + t₂ + 20) + 600 * x.length := by
      omega
    calc t ≤ K₀ * (tg + tI + 3 + 13) := ht'.trans (le_of_eq (by ring))
      _ ≤ K₀ * (600 * (n + 1) ^ 2 + 17 + KI * (t₁ + t₂ + 20) + 600 * x.length) :=
          Nat.mul_le_mul_left _ this
      _ = Y + 600 * K₀ * x.length := by simp only [Y]; ring
  have hY : Y ≤ ⌊(c : ℝ) * P⌋₊ := by
    apply Nat.le_floor
    have hK : ((K₀ * (617 + KI * (cC + c₂ * (Mr + 1) + 20)) : ℕ) : ℝ) ≤ c := by
      exact_mod_cast (show K₀ * (617 + KI * (cC + c₂ * (Mr + 1) + 20)) ≤ c by omega)
    have hK0' : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
    have hKI' : (0 : ℝ) ≤ KI := Nat.cast_nonneg _
    have hin : ((600 * (n + 1) ^ 2 + 17 + KI * (t₁ + t₂ + 20) : ℕ) : ℝ) ≤
        (617 + KI * (cC + c₂ * (Mr + 1) + 20)) * P := by
      push_cast
      push_cast at hP2
      have : (KI : ℝ) * (t₁ + t₂ + 20) ≤ KI * ((cC + c₂ * (Mr + 1) + 20) * P) := by
        apply mul_le_mul_of_nonneg_left _ hKI'
        linarith
      linarith
    calc (Y : ℝ) = K₀ * ((600 * (n + 1) ^ 2 + 17 + KI * (t₁ + t₂ + 20) : ℕ) : ℝ) := by
          simp only [Y]; push_cast; ring
      _ ≤ K₀ * ((617 + KI * (cC + c₂ * (Mr + 1) + 20)) * P) := mul_le_mul_of_nonneg_left hin hK0'
      _ = ((K₀ * (617 + KI * (cC + c₂ * (Mr + 1) + 20)) : ℕ) : ℝ) * P := by push_cast; ring
      _ ≤ c * P := mul_le_mul_of_nonneg_right hK (by linarith)
  have : 600 * K₀ * x.length ≤ c * x.length := Nat.mul_le_mul_right _ (by omega)
  show t ≤ ⌊(c : ℝ) * P⌋₊ + c * x.length
  omega

/-- The statement for the older input format and the older notion of computing. -/
theorem exists_program_definableSequence_old :
    ∃ (p : Program) (f : List ℕ → List ℕ) (e A : ℕ),
      (∀ (r : ℕ) (ε : ℚ) (n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
        1 ≤ r → 0 < ε → EncodesInput x r ε n G →
          (∃ s, EncodesSequence (f x) s ∧ IsConstructionSequence G s) ∧
            ∀ v ∈ f x, v ≤ (f x).length + n) ∧
      ∀ (C : GraphClass), MonadicallyDependent C →
        ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
          ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
            (∀ w : ℕ, ComputesInTime w p
              {x | EncodesInput x r ε n G ∧
                ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              f (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * x.length)) ∧
            ∀ (x : List ℕ) (s : List (PartialGraph (Fin n))),
              EncodesInput x r ε n G → EncodesSequence (f x) s →
                (s.length : ℝ) ≤ c * ((n : ℝ) + 1) ^ (1 + (a₀ : ℝ) * ε) ∧
                IsRadiusDefinable G s r (⌈(A : ℚ) * r / ε⌉₊ + A)
                  ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((a₀ : ℝ) * ε)⌋₊ 7 := by
  obtain ⟨p, e, AC, A₂, Sch, M₂, hSch, hM₂, hcore⟩ := exists_program_core 1 le_rfl
  set F := outFun 1 M₂ Sch
  refine ⟨p, decodeOut F, e, 12 * AC + 1, ?_, ?_⟩
  · intro r ε n G x hr hε hx
    rw [decodeOut_eq F hx]
    obtain ⟨hch, -⟩ := hSch n (5 * r + 1) ε G (by omega) hε
    obtain ⟨hcs, hent, -⟩ := hM₂ n G _ hch
    exact ⟨⟨_, ⟨_, rfl, rfl⟩, hcs⟩, hent⟩
  intro C hC
  obtain ⟨d, hvc⟩ := Lax185574Proofs.Shim.BoundedVCClasses.exists_vcDim_le C hC
  have hd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ k : ℕ, neighborhoodComplexity G k ≤ (k + 1) ^ d := fun n G hG k =>
    Lax185574.NeighborhoodComplexityBound.neighborhoodComplexity_le G d (hvc n G hG) k
  refine ⟨d + 1, by omega, fun r ε hr hε η hη => ?_⟩
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨cC, c₁, hcC, htime⟩ := hcore C hC r ε hε η hη
  set c := c₁ + A₂ * ((cC + 1) ^ (d + 1) + 1) + (cC + 1) ^ (d + 1) with hc
  refine ⟨c, fun n G hG => ⟨htime c (by omega) n G hG, fun x s hx hs => ?_⟩⟩
  rw [decodeOut_eq F hx] at hs
  set S := Sch n (5 * r + 1) ε G
  obtain ⟨hch, hlenQ⟩ := hSch n (5 * r + 1) ε G (by omega) hε
  obtain ⟨-, -, hlen, hw⟩ := hM₂ n G S hch
  have hs' : s = (M₂ n G S).run := encodesSequence_unique hs ⟨_, rfl, rfl⟩
  subst hs'
  obtain ⟨-, hdefin⟩ := hw r hr
  set N : ℝ := (n : ℝ) + 1
  have hN : 1 ≤ N := by simp only [N]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set k := chainWidth G (5 * r + 1) S
  have hk : (k : ℝ) ≤ cC * N ^ (ε : ℝ) := hcC n G hG
  have hNε : 1 ≤ N ^ (ε : ℝ) := Real.one_le_rpow hN hε'.le
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (cC + 1) * N ^ (ε : ℝ) := by push_cast; linarith
  have hwk : ∀ k', k' ≤ k → k' * neighborhoodComplexity G k' ≤ (k + 1) ^ (d + 1) := by
    intro k' hk'
    calc k' * neighborhoodComplexity G k' ≤ k' * (k' + 1) ^ d := Nat.mul_le_mul_left _ (hd n G hG k')
      _ ≤ (k + 1) * (k + 1) ^ d := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
      _ = (k + 1) ^ (d + 1) := by ring
  have hwr : chainBound G S r ≤ (k + 1) ^ (d + 1) := hwk k le_rfl
  have hw1 : chainBound G S 1 ≤ (k + 1) ^ (d + 1) :=
    hwk _ (chainWidth_mono G S (by omega))
  have hK : (((k + 1) ^ (d + 1) : ℕ) : ℝ) ≤ (cC + 1) ^ (d + 1) * N ^ (((d + 1 : ℕ) : ℝ) * ε) := by
    rw [Nat.cast_pow]
    calc (((k + 1 : ℕ) : ℝ)) ^ (d + 1) ≤ ((cC + 1) * N ^ (ε : ℝ)) ^ (d + 1) :=
          pow_le_pow_left₀ (by positivity) hk1 _
      _ = (cC + 1) ^ (d + 1) * N ^ (((d + 1 : ℕ) : ℝ) * ε) := by
          rw [mul_pow, ← Real.rpow_natCast (N ^ (ε : ℝ)), ← Real.rpow_mul (by linarith)]
          ring_nf
  have hc1 : ((cC + 1 : ℕ) : ℝ) ^ (d + 1) ≤ c := by
    exact_mod_cast (show (cC + 1) ^ (d + 1) ≤ c by omega)
  constructor
  · have h1 : ((M₂ n G S).run.length : ℝ) ≤ A₂ * N * ((cC + 1) ^ (d + 1) * N ^ (((d + 1 : ℕ) : ℝ) * ε) + 1) := by
      have : ((M₂ n G S).run.length : ℝ) ≤ A₂ * N * (chainBound G S 1 + 1) := by
        have := hlen; simp only [N]; exact_mod_cast this
      refine this.trans ?_
      gcongr
      exact (Nat.cast_le.mpr hw1).trans hK
    refine h1.trans ?_
    have hP : 1 ≤ N ^ (((d + 1 : ℕ) : ℝ) * ε) := Real.one_le_rpow hN (by positivity)
    have hsplit : N ^ (1 + ((d + 1 : ℕ) : ℝ) * ε) = N * N ^ (((d + 1 : ℕ) : ℝ) * ε) := by
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    rw [hsplit]
    have hA : ((A₂ * ((cC + 1) ^ (d + 1) + 1) : ℕ) : ℝ) ≤ c := by
      exact_mod_cast (show A₂ * ((cC + 1) ^ (d + 1) + 1) ≤ c by omega)
    push_cast at hA hc1
    have hA0 : (0 : ℝ) ≤ A₂ := Nat.cast_nonneg _
    have : (A₂ : ℝ) * N * ((cC + 1) ^ (d + 1) * N ^ (((d + 1 : ℕ) : ℝ) * ε) + 1) ≤
        (A₂ * ((cC + 1) ^ (d + 1) + 1)) * (N * N ^ (((d + 1 : ℕ) : ℝ) * ε)) := by
      have : (A₂ : ℝ) * N ≤ A₂ * N * N ^ (((d + 1 : ℕ) : ℝ) * ε) := by
        exact le_mul_of_one_le_right (mul_nonneg hA0 (by linarith)) hP
      linarith
    refine this.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  · refine isRadiusDefinable_mono ?_ ?_ hdefin
    · -- the number of predicates
      have hm : (S.length : ℚ) ≤ AC * ((5 * r + 1 : ℕ) : ℚ) / ε + AC := hlenQ
      have hq : (0 : ℚ) ≤ r / ε := div_nonneg (Nat.cast_nonneg _) hε.le
      have h6 : ((5 * r + 1 : ℕ) : ℚ) / ε ≤ 6 * (r / ε) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hε]
        have : ((5 * r + 1 : ℕ) : ℚ) ≤ 6 * r := by
          have : (1 : ℚ) ≤ r := by exact_mod_cast hr
          push_cast; linarith
        exact this
      have hAC : (0 : ℚ) ≤ AC := Nat.cast_nonneg _
      have h2 : ((2 * S.length + 1 : ℕ) : ℚ) ≤ ((12 * AC + 1 : ℕ) : ℚ) * r / ε + (12 * AC + 1 : ℕ) := by
        push_cast
        have : (AC : ℚ) * ((5 * r + 1 : ℕ) : ℚ) / ε ≤ AC * (6 * (r / ε)) := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h6 hAC
        rw [mul_div_assoc]
        push_cast at this hm
        linarith
      have h3 := Nat.le_ceil (((12 * AC + 1 : ℕ) : ℚ) * r / ε)
      have : ((2 * S.length + 1 : ℕ) : ℚ) ≤ ((⌈((12 * AC + 1 : ℕ) : ℚ) * r / ε⌉₊ + (12 * AC + 1) : ℕ) : ℚ) := by
        push_cast at h2 h3 ⊢; linarith
      exact_mod_cast this
    · apply Nat.le_floor
      refine (Nat.cast_le.mpr hwr).trans (hK.trans ?_)
      push_cast at hc1 ⊢
      exact mul_le_mul_of_nonneg_right hc1 (by positivity)


open Lax185574.Graphs Lax185574.Algorithms Lax185574.Encoding Lax185574Proofs.Interface in
/--
---
conclusion: Lax185574.DefinableSequences.exists_program_definableSequence
---
The proof of the theorem on definable construction sequences. Compute a
chain at radius `5r + 1` and accuracy `ε` (the chain theorem), of length
`m ≤ O(r/ε)`, and turn it into a construction sequence (the lemma
turning chains into construction sequences). With `k_r ≤ c (n+1)^ε` the
radius-`(5r+1)` width of the chain, `d` a bound on the VC-dimension of
the graphs of the class (the observation on bounded VC-dimension) and
`π_G(k) ≤ (k+1)^d` (the Sauer–Shelah lemma), `w_r ≤ (k_r + 1)^(d+1)`, so
`a₀ = d + 1`. The length is `O(n w₁) ≤ O(n w_r)`, as the width of a
chain grows with the radius. The number of predicates is `2m + 1 ≤ ⌈A
r/ε⌉ + A`. On the word RAM, a first phase converts the compressed sparse
row form of the graph into the word of the graph that the two cited
programs read.

The proof is carried out for the input format with the graph in
compressed sparse row form and the notion `Lax185574.Computing.Computes`. The algorithm converts the word
of the graph into compressed sparse rows (`Interface.nbr_bridge`) and
runs that program. The script of a graph is the one whose encoding the
program outputs on the converted input.
-/
theorem exists_program_definableSequence :
    ∃ (A : Algorithm) (K : ℕ) (script : ℕ → ℚ → (G : Graph) → Script G.n),
      (∀ (r : ℕ) (ε : ℚ) (G : Graph), 1 ≤ r → 0 < ε →
        IsConstructionSequence G.toSimpleGraph (script r ε G).run ∧
          (script r ε G).HasSmallNumbers) ∧
      ∀ C : Lax185574.Graphs.GraphClass, Lax185574.MonadicDependence.MonadicallyDependent C → ∃ a : ℕ, 1 ≤ a ∧
        ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε → ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ G ∈ C,
            A.Computes c (r, ε, G) (script r ε G) ((G.n : ℝ) ^ (3 + η)) ∧
            ((script r ε G).run.length : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ (1 + (a : ℝ) * ε) ∧
            IsRadiusDefinable G.toSimpleGraph (script r ε G).run r (⌈(K : ℚ) * r / ε⌉₊ + K)
              ⌊(c : ℝ) * ((G.n : ℝ) + 1) ^ ((a : ℝ) * ε)⌋₊ 7 := by
  obtain ⟨p, f, e, K, hcorr, hclass⟩ := exists_program_definableSequence_old
  obtain ⟨q, Kq, hq⟩ := nbr_bridge 4 p
  refine ⟨⟨q, e + 1⟩, K,
    fun r ε G => scriptOf f G.n (encode (r, ε) ++ csrWord (nbLists G.toSimpleGraph)),
    fun r ε G hr hε => ?_, fun C hC => ?_⟩
  · obtain ⟨⟨s, hs, hcs⟩, hsm⟩ := hcorr r ε G.n G.toSimpleGraph _ hr hε
      ⟨_, encodesGraph_csrWord _, rfl⟩
    obtain ⟨hfx, hrun⟩ := scriptOf_spec hs
    refine ⟨hrun ▸ hcs, fun v hv => ?_⟩
    rw [← hfx] at hv ⊢
    exact hsm v hv
  · obtain ⟨a, ha1, ha⟩ := hclass (toOld C) (monadicallyDependent_toOld hC)
    refine ⟨a, ha1, fun r ε hr hε η hη => ?_⟩
    obtain ⟨c, hc⟩ := ha r ε hr hε η hη
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, (2 : ℝ) ^ (3 + η) ≤ Q := ⟨⌈(2 : ℝ) ^ (3 + η)⌉₊, Nat.le_ceil _⟩
    refine ⟨seqConst Kq c e Q 4, fun G hG => ?_⟩
    have hmem : toOld C G.n G.toSimpleGraph := (toOld_iff C G).mpr hG
    obtain ⟨hcomp, hout⟩ := hc G.n G.toSimpleGraph hmem
    have henc : EncodesInput (encode (r, ε) ++ csrWord (nbLists G.toSimpleGraph)) r ε G.n
        G.toSimpleGraph := ⟨_, encodesGraph_csrWord _, rfl⟩
    obtain ⟨⟨s, hs, -⟩, -⟩ := hcorr r ε G.n G.toSimpleGraph _ hr hε henc
    obtain ⟨hfx, hrun⟩ := scriptOf_spec hs
    obtain ⟨hlen, hdef⟩ := hout _ s henc hs
    rw [hrun] at hlen hdef
    have hcc : (c : ℝ) ≤ seqConst Kq c e Q 4 := by exact_mod_cast le_seqConst Kq c e Q 4
    refine ⟨?_, le_trans hlen (mul_le_mul_of_nonneg_right hcc (by positivity)),
      Lax185574Proofs.Compose.isRadiusDefinable_mono le_rfl
        (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hcc (by positivity))) hdef⟩
    have ha' : encode (r, ε, G) = encode (r, ε) ++ nbWord (nbLists G.toSimpleGraph) := by
      simp only [KitG3.encode_pair, encode_graph, toWord_graph_eq, List.append_assoc]
    refine seq_wrap hq (length_encode_nat_rat r ε) G.toSimpleGraph ha' hη hQ (fun w hw => ?_)
    rw [← hfx]
    exact hcomp w _ ⟨henc, hw⟩

end Lax185574Proofs.DefinableSequences
