import Lax185574Proofs.ResolveRam.EntBound
import Lax185574Proofs.ResolveRam.Glue.Input

/-!
The entries of the queries and answers of the calls of lem:resolve-lift
and of the output.

Let `X` be the largest entry of the input. Every color of `G` and the
number of vertices are entries of the input, so they are at most `X`.
The constant `cK k₀ q₀` bounds the constants of the trees, roots and
atoms of all ranks and arities up to `k₀ + q₀ + 2`, the radii of the
scatter type and the entries of the fixed queries. Then the query of
every call is good (`Good (cK k₀ q₀) X`), and so is its answer, except
for the canonical form, whose answer has as entries its lengths and the
entries of its query. The output is good. `entBounds` turns this into the
bounds of `CallBounds`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.DistanceLogic Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.Simulate
open Lax3.DistFO (rhoMinus rhoPlus)
open Lax185574.DistanceMatrix

/-! ### The constant -/

/-- The bound of the ranks and arities. -/
def entN (k₀ q₀ : ℕ) : ℕ := k₀ + q₀ + 3

/-- The constants of one rank and arity. -/
def entTerm (k q ℓ : ℕ) : ℕ := k + q + nodeCst k q ℓ + atomCst k q ℓ + 9 ^ k * rhoMinus k q

/-- The largest entries of the fixed queries and answers. -/
noncomputable def fixEnt : ℕ :=
  maxEntry qA0 + maxEntry qB0 + maxEntry qC0 + maxEntry qE0 + maxEntry qF0 +
    maxEntry yA0 + maxEntry yB0 + maxEntry yC0 + maxEntry yE0 + maxEntry yF0

/-- The constant of the entries. -/
noncomputable def cK (k₀ q₀ : ℕ) : ℕ :=
  (∑ k ∈ Finset.range (entN k₀ q₀), ∑ q ∈ Finset.range (entN k₀ q₀),
    ∑ ℓ ∈ Finset.range (entN k₀ q₀), entTerm k q ℓ) + entN k₀ q₀ + fixEnt

theorem le_cK {k₀ q₀ k q ℓ : ℕ} (hk : k < entN k₀ q₀) (hq : q < entN k₀ q₀)
    (hℓ : ℓ < entN k₀ q₀) : entTerm k q ℓ ≤ cK k₀ q₀ := by
  have h1 := Finset.single_le_sum (f := fun ℓ => entTerm k q ℓ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hℓ)
  have h2 := Finset.single_le_sum
    (f := fun q => ∑ ℓ ∈ Finset.range (entN k₀ q₀), entTerm k q ℓ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hq)
  have h3 := Finset.single_le_sum
    (f := fun k => ∑ q ∈ Finset.range (entN k₀ q₀), ∑ ℓ ∈ Finset.range (entN k₀ q₀), entTerm k q ℓ)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hk)
  unfold cK
  omega

theorem tree_le_cK {k₀ q₀ k q ℓ : ℕ} (hk : k < entN k₀ q₀) (hq : q < entN k₀ q₀)
    (hℓ : ℓ < entN k₀ q₀) : k + q + nodeCst k q ℓ ≤ cK k₀ q₀ := by
  have := le_cK hk hq hℓ; unfold entTerm at this; omega

theorem node_le_cK {k₀ q₀ k q ℓ : ℕ} (hk : k < entN k₀ q₀) (hq : q < entN k₀ q₀)
    (hℓ : ℓ < entN k₀ q₀) : nodeCst k q ℓ ≤ cK k₀ q₀ := by
  have := le_cK hk hq hℓ; unfold entTerm at this; omega

theorem atom_le_cK {k₀ q₀ k q ℓ : ℕ} (hk : k < entN k₀ q₀) (hq : q < entN k₀ q₀)
    (hℓ : ℓ < entN k₀ q₀) : atomCst k q ℓ ≤ cK k₀ q₀ := by
  have := le_cK hk hq hℓ; unfold entTerm at this; omega

theorem rad_le_cK {k₀ q₀ k q : ℕ} (hk : k < entN k₀ q₀) (hq : q < entN k₀ q₀) :
    9 ^ k * rhoMinus k q ≤ cK k₀ q₀ := by
  have := le_cK (ℓ := 0) hk hq (by unfold entN; omega); unfold entTerm at this; omega

theorem entN_le_cK (k₀ q₀ : ℕ) : entN k₀ q₀ ≤ cK k₀ q₀ := by unfold cK; omega

theorem fix_le_cK (k₀ q₀ : ℕ) : fixEnt ≤ cK k₀ q₀ := by unfold cK; omega

/-! ### Atoms and roots -/

theorem cand_entry {k q ℓ : ℕ} {cs : List ℕ} {φ : DistFO ℓ} (hφ : φ ∈ candL k q ℓ cs) {e : ℕ}
    (he : e ∈ toWord φ) : e ≤ atomCst k q ℓ ∨ e ∈ cs := by
  have hi : ∀ i : Fin ℓ, (i : ℕ) ≤ atomCst k q ℓ := fun i => by
    have := i.2; simp only [atomCst]; omega
  rw [Lax185574Proofs.Legacy.encode_eq_code] at he
  simp only [candL, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_finRange, true_and] at hφ
  rcases hφ with (((((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨Y, hY, i, rfl⟩) |
    ⟨r, hr, p, -, rfl⟩) | ⟨r, hr, Y, hY, i, rfl⟩) <;>
    simp only [DistFO.code, List.mem_cons, List.not_mem_nil, or_false] at he
  · left; rcases he with rfl | rfl | rfl
    · simp [atomCst]
    · exact hi _
    · exact hi _
  · left; rcases he with rfl | rfl | rfl
    · simp only [atomCst]; omega
    · exact hi _
    · exact hi _
  · left; rcases he with rfl | rfl | rfl
    · simp only [atomCst]; omega
    · exact hi _
    · exact hi _
  · rcases he with rfl | rfl | rfl
    · left; simp only [atomCst]; omega
    · right; exact hY
    · left; exact hi _
  · left; rcases he with rfl | rfl | rfl | rfl
    · simp only [atomCst]; omega
    · simp only [atomCst]; omega
    · exact hi _
    · exact hi _
  · rcases he with rfl | rfl | rfl | rfl
    · left; simp only [atomCst]; omega
    · left; simp only [atomCst]; omega
    · right; exact hY
    · left; exact hi _

theorem toWord_rootAs {ν : TypeTree} {q ℓ : ℕ} {r : Node q ℓ} (h : TypeTree.rootAs ν q ℓ = some r) :
    toWord r = toWord ν.root := by
  rcases ν with ⟨k', q', ℓ', t⟩
  simp only [TypeTree.rootAs] at h
  split_ifs at h with hh
  obtain ⟨rfl, rfl⟩ := hh
  simp only [Option.some.injEq] at h
  subst h
  rfl

/-! ### The input -/

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem mem_xIn_G {e : ℕ} (he : e ∈ toWord G) : e ∈ xIn G k₀ q₀ P Q s := by
  unfold xIn; exact List.mem_append_left _ he

theorem mem_xIn_D {e : ℕ} (he : e ∈ toWord (distMatrix G)) : e ∈ xIn G k₀ q₀ P Q s := by
  unfold xIn; exact List.mem_append_right _ (List.mem_append_left _ he)

theorem mem_xIn_fam {e : ℕ} (he : e ∈ toWord (family G k₀ q₀)) : e ∈ xIn G k₀ q₀ P Q s := by
  unfold xIn
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ he))))

theorem color_le_x (v : Fin n) : G.color v ≤ maxEntry (xIn G k₀ q₀ P Q s) := by
  refine le_maxEntry (mem_xIn_G G P Q s k₀ q₀ ?_)
  show G.color v ∈ toWord G.color ++ _
  refine List.mem_append_left _ ?_
  rw [toWord_fun_eq]
  refine List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨[G.color v], List.mem_map.2
    ⟨G.color v, List.mem_ofFn.2 ⟨v, rfl⟩, rfl⟩, by simp⟩)

theorem n_le_x : n ≤ maxEntry (xIn G k₀ q₀ P Q s) := by
  refine le_maxEntry (mem_xIn_G G P Q s k₀ q₀ ?_)
  show n ∈ toWord G.color ++ _
  refine List.mem_append_left _ ?_
  rw [toWord_fun_eq]
  exact List.mem_cons_self

/-! ### The calls -/

local notation "KK" => cK k₀ q₀
local notation "XX" => maxEntry (xIn G k₀ q₀ P Q s)

theorem good_stp_mem {p : (ℕ × TypeTree) × ℕ} (hp : p ∈ stp G k₀ q₀) : Good KK XX (toWord p) := by
  unfold stp graphOn at hp
  obtain ⟨⟨i, b, hi1, hi, hr1, hr, hν⟩, hv⟩ := mem_of_mem_finsetOf hp
  obtain ⟨⟨r, ν⟩, v⟩ := p
  simp only at hν hv hr
  subst hν hv
  have hN : k₀ + i < entN k₀ q₀ := by unfold entN; omega
  have hN' : q₀ - i < entN k₀ q₀ := by unfold entN; omega
  show Good KK XX ((toWord r ++ toWord (tree G (k₀ + i) (q₀ - i) ![b])) ++ [value G k₀ q₀ (r, _)])
  refine (Good.append (good_of_le fun e he => ?_) (good_tree G _ _ _ (tree_le_cK hN hN'
    (by unfold entN; omega)) (color_le_x G P Q s k₀ q₀))).append (good_of_le fun e he => ?_)
  · simp only [word_simps, List.mem_singleton] at he
    have := rad_le_cK hN hN'; omega
  · simp only [List.mem_singleton] at he
    subst he
    have : value G k₀ q₀ (r, tree G (k₀ + i) (q₀ - i) ![b]) ≤ k₀ + q₀ := min_le_right _ _
    have := entN_le_cK k₀ q₀; unfold entN at this; omega

theorem good_stp : Good KK XX (toWord (stp G k₀ q₀)) :=
  good_finset _ fun _ hp => good_stp_mem G P Q s k₀ q₀ hp

theorem good_stpQ : Good KK XX (toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀)) := by
  refine good_of_le fun e he => ?_
  have hN := entN_le_cK k₀ q₀
  unfold entN at hN
  change e ∈ toWord G ++ ([k₀] ++ ([q₀] ++ (toWord (distMatrix G) ++ toWord (family G k₀ q₀)))) at he
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with h | rfl | rfl | h | h
  · have := le_maxEntry (mem_xIn_G G P Q s k₀ q₀ h); omega
  · omega
  · omega
  · have := le_maxEntry (mem_xIn_D G P Q s k₀ q₀ h); omega
  · have := le_maxEntry (mem_xIn_fam G P Q s k₀ q₀ h); omega

theorem good_fixQ {u : List ℕ} (h : maxEntry u ≤ fixEnt) : Good KK XX u :=
  good_fix (le_trans h (fix_le_cK k₀ q₀))

theorem entfA : maxEntry qA0 ≤ fixEnt := by unfold fixEnt; omega
theorem entfB : maxEntry qB0 ≤ fixEnt := by unfold fixEnt; omega
theorem entfC : maxEntry qC0 ≤ fixEnt := by unfold fixEnt; omega
theorem entfE : maxEntry qE0 ≤ fixEnt := by unfold fixEnt; omega
theorem entfF : maxEntry qF0 ≤ fixEnt := by unfold fixEnt; omega
theorem entgA : maxEntry yA0 ≤ fixEnt := by unfold fixEnt; omega
theorem entgB : maxEntry yB0 ≤ fixEnt := by unfold fixEnt; omega
theorem entgC : maxEntry yC0 ≤ fixEnt := by unfold fixEnt; omega
theorem entgE : maxEntry yE0 ≤ fixEnt := by unfold fixEnt; omega
theorem entgF : maxEntry yF0 ≤ fixEnt := by unfold fixEnt; omega

/-- The canonical-form calls come from the items of the levels. -/
theorem canon_mem {ws : List (List ℕ)} (hc : RCall.canon ws ∈ rcalls G P Q s k₀ q₀) :
    ∃ d ≤ q₀, ∃ y ∈ (lvR G P Q s k₀ q₀ d).zipIdx, ws = atomQ G P Q s k₀ q₀ y.1.2 ∨
      (d < q₀ ∧ ws = kidQ G P Q s k₀ q₀ d y.2 y.1.2) := by
  unfold rcalls at hc
  split_ifs at hc
  · simp at hc
  rcases List.mem_cons.1 hc with h | hc
  · cases h
  rcases List.mem_append.1 hc with hc | hc
  · exfalso
    simp only [downAll, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨d, -, x, -, hc⟩ := hc
    simp [downCalls] at hc
  · simp only [upAll, List.mem_flatMap, List.mem_reverse, List.mem_range] at hc
    obtain ⟨d, hd, y, hy, hc⟩ := hc
    refine ⟨d, by omega, y, hy, ?_⟩
    simp only [upCalls] at hc
    split_ifs at hc with hdq
    · simp only [List.mem_cons, RCall.canon.injEq, List.not_mem_nil, or_false] at hc
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hdq, h⟩
    · simp only [List.mem_cons, RCall.canon.injEq, List.not_mem_nil, or_false] at hc
      exact Or.inl hc

theorem famItems_good (hk : 1 ≤ k₀) : ∀ x ∈ famItems G k₀ q₀, GoodAt G k₀ q₀ 0 x := by
  intro x hx
  simp only [famItems, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  exact ⟨1, ![b], by simp [family], le_rfl, hk⟩

/-- The roots of the outputs of the children are good. -/
theorem good_kid_root (hk : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) {i : ℕ} {p : ℕ × TypeTree}
    (hp : p ∈ kidsOf (lvR G P Q s k₀ q₀ (d + 1)) (outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1)) i) :
    Good KK XX (toWord p.2.root) := by
  simp only [kidsOf, List.mem_map, List.mem_filter] at hp
  obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hp
  have hy2 := (List.of_mem_zip hy).2
  rw [outR, outsAt_eq (dataOf G P Q s k₀ q₀) (farMapOf G) (dataOf_spec G P Q s k₀ q₀)
    (farSpec_farMapOf G) (expandOK_exR G P Q s k₀ q₀) (famItems_good G k₀ q₀ hk)
    (q₀ - (d + 1)) (d + 1) (by omega)] at hy2
  obtain ⟨x, hx, hxy⟩ := List.mem_map.1 hy2
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk (by omega) hx
  simp only
  rw [← hxy, hu]
  show Good KK XX (toWord (resolveNodeF (dataOf G P Q s k₀ q₀) (farMapOf G) (k₀ + (d + 1))
    (q₀ - (d + 1)) (node G (k₀ + (d + 1)) (q₀ - (d + 1)) u)))
  rw [resolveNodeF_node (dataOf G P Q s k₀ q₀) (farMapOf G) (dataOf_spec G P Q s k₀ q₀)
    (farSpec_farMapOf G) (q₀ - (d + 1)) (k₀ + (d + 1)) u h1 hℓ (by omega) (by omega)]
  refine good_node _ _ _ u (node_le_cK (by unfold entN; omega) (by unfold entN; omega)
    (by unfold entN; omega)) (fun v => ?_)
  rw [resolveBy_color]; exact color_le_x G P Q s k₀ q₀ v

theorem good_kidQ (hk : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) (i : ℕ) (τ : TypeTree)
    (hℓ : τ.ℓ < entN k₀ q₀) : ∀ w ∈ kidQ G P Q s k₀ q₀ d i τ, Good KK XX w := by
  rcases τ with ⟨k, _ | q, ℓ, t⟩
  · simp [kidQ]
  · intro w hw
    simp only [kidQ, List.mem_map] at hw
    obtain ⟨e, he, rfl⟩ := hw
    simp only [kidL, List.mem_filterMap] at he
    obtain ⟨p, hp, hpe⟩ := he
    split_ifs at hpe with hlt
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hpe
    show Good KK XX ([p.1] ++ toWord r)
    refine Good.append (good_of_le fun e he => ?_) ?_
    · simp only [List.mem_singleton] at he
      have := entN_le_cK k₀ q₀
      simp only at hℓ
      omega
    · rw [toWord_rootAs hr]
      exact good_kid_root G P Q s k₀ q₀ hk hd hp

theorem good_atomQ {d : ℕ} {τ : TypeTree} (hk : τ.k < entN k₀ q₀) (hq : τ.q < entN k₀ q₀)
    (hℓ : τ.ℓ < entN k₀ q₀) : ∀ w ∈ atomQ G P Q s k₀ q₀ τ, Good KK XX w := by
  intro w hw
  simp only [atomQ, List.mem_map] at hw
  obtain ⟨φ, hφ, rfl⟩ := hw
  have hc := (List.mem_filter.1 hφ).1
  refine good_of_le fun e he => ?_
  rcases cand_entry hc he with h | h
  · have := atom_le_cK hk hq hℓ; omega
  · simp only [colsL, Finset.mem_sort, colsCore, Finset.mem_image, Finset.mem_univ,
      true_and] at h
    obtain ⟨v, rfl⟩ := h
    have := color_le_x G P Q s k₀ q₀ v; omega

theorem good_words {ws : List (List ℕ)} (h : ∀ w ∈ ws, Good KK XX w) : Good KK XX (toWord ws) :=
  good_list ws (fun w _ => by rw [toWord_listNat]; simp) (fun w hw => good_word (h w hw))

theorem canon_words (hk : 1 ≤ k₀) {ws : List (List ℕ)}
    (hc : RCall.canon ws ∈ rcalls G P Q s k₀ q₀) : ∀ w ∈ ws, Good KK XX w := by
  obtain ⟨d, hd, y, hy, h⟩ := canon_mem G P Q s k₀ q₀ hc
  have hy1 : y.1 ∈ lvR G P Q s k₀ q₀ d :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hy)
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd hy1
  have ek : y.1.2.k = k₀ + d := by rw [hu]; rfl
  have eq : y.1.2.q = q₀ - d := by rw [hu]; rfl
  have el : y.1.2.ℓ = ℓ := by rw [hu]; rfl
  rcases h with rfl | ⟨hdq, rfl⟩
  · exact good_atomQ G P Q s k₀ q₀ (d := d) (by rw [ek]; unfold entN; omega)
      (by rw [eq]; unfold entN; omega) (by rw [el]; unfold entN; omega)
  · exact good_kidQ G P Q s k₀ q₀ hk hdq _ _ (by rw [el]; unfold entN; omega)

/-- **Entries of a call.** -/
theorem ent_call (hk : 1 ≤ k₀) {c : RCall} (hc : c ∈ rcalls G P Q s k₀ q₀) :
    Good KK XX (rQ G k₀ q₀ c) ∧ ∀ e ∈ rY G k₀ q₀ c,
      e ≤ (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length + KK + XX := by
  have hci := callInst G P Q s k₀ q₀ hk c hc
  have hcol := color_le_x G P Q s k₀ q₀
  have qa := good_fixQ G P Q s k₀ q₀ entfA
  have qb := good_fixQ G P Q s k₀ q₀ entfB
  have qc := good_fixQ G P Q s k₀ q₀ entfC
  have qe := good_fixQ G P Q s k₀ q₀ entfE
  have qf := good_fixQ G P Q s k₀ q₀ entfF
  have ya := good_fixQ G P Q s k₀ q₀ entgA
  have yb := good_fixQ G P Q s k₀ q₀ entgB
  have yc := good_fixQ G P Q s k₀ q₀ entgC
  have ye := good_fixQ G P Q s k₀ q₀ entgE
  have yf := good_fixQ G P Q s k₀ q₀ entgF
  -- a good answer suffices except for the canonical form
  suffices h : Good KK XX (rQ G k₀ q₀ c) ∧ (Good KK XX (rY G k₀ q₀ c) ∨
      ∀ e ∈ rY G k₀ q₀ c, e ≤ (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length + KK + XX) by
    refine ⟨h.1, fun e he => ?_⟩
    rcases h.2 with h2 | h2
    · have := h2 e he; omega
    · exact h2 e he
  cases c with
  | stp =>
    exact ⟨good_sw5In qa qb qc qe (good_stpQ G P Q s k₀ q₀), Or.inl
      ((((ya.append yb).append yc).append ye).append (good_stp G P Q s k₀ q₀))⟩
  | shift τ =>
    obtain ⟨d, hd, ℓ, u, h1, hk', rfl⟩ := hci
    have gt := good_tree (K := KK) (X := XX) G (k₀ + d) (q₀ - d - 1 + 1) u
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
    have gs := good_tree (K := KK) (X := XX) G (k₀ + d + 1) (q₀ - d - 1) u
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
    refine ⟨good_sw5In gt qb qc qe qf, Or.inl ?_⟩
    show Good KK XX (toWord (shOf G _) ++ yB0 ++ yC0 ++ yE0 ++ yF0)
    rw [shOf_tree G u h1 hk']
    exact (((gs.append yb).append yc).append ye).append yf
  | ftree τ =>
    obtain ⟨d, hd, ℓ, u, h1, hk', rfl⟩ := hci
    have gt := good_tree (K := KK) (X := XX) G (k₀ + d) (q₀ - d - 1 + 1) u
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
    have gq : Good KK XX (qB G k₀ q₀ (.ftree (tree G (k₀ + d) (q₀ - d - 1 + 1) u))) := by
      show Good KK XX (toWord (tree G (k₀ + d) (q₀ - d - 1 + 1) u) ++ toWord (stpCut _ _))
      exact gt.append (good_finset _ fun p hp =>
        good_stp_mem G P Q s k₀ q₀ (mem_stpCut.1 hp).1)
    refine ⟨good_sw5In qa gq qc qe qf, Or.inl ?_⟩
    show Good KK XX (yA0 ++ toWord ((faOf G _).map toWord) ++ yC0 ++ yE0 ++ yF0)
    rw [toWord_faOf G u h1 hk']
    refine (((ya.append ?_).append yc).append ye).append yf
    refine good_finset _ fun ν hν => ?_
    obtain ⟨b, -, rfl⟩ := mem_of_mem_finsetOf hν
    exact good_tree G _ _ _
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
  | compose σ ν =>
    obtain ⟨d, hd, ℓ, u, b, h1, hk', hb, rfl, rfl⟩ := hci
    have g1 := good_tree (K := KK) (X := XX) G (k₀ + d + 1) (q₀ - d - 1) u
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
    have g2 := good_tree (K := KK) (X := XX) G (k₀ + d + 1) (q₀ - d - 1) ![b]
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
    have g3 := good_tree (K := KK) (X := XX) G (k₀ + d + 1) (q₀ - d - 1) (Fin.snoc u b)
      (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hcol
    refine ⟨good_sw5In qa qb (g1.append g2) qe qf, Or.inl ?_⟩
    show Good KK XX (yA0 ++ yB0 ++ toWord (coOf G _ _) ++ yE0 ++ yF0)
    rw [coOf_tree G u b h1 hk' hb]
    exact (((ya.append yb).append g3).append ye).append yf
  | canon ws =>
    have gw := good_words G P Q s k₀ q₀ (canon_words G P Q s k₀ q₀ hk hc)
    have gQ := good_sw5In qa qb qc gw qf
    refine ⟨gQ, Or.inr fun e he => ?_⟩
    have hY : rY G k₀ q₀ (.canon ws) = yA0 ++ yB0 ++ yC0 ++ canonW ws ++ yF0 := rfl
    have hQ : rQ G k₀ q₀ (.canon ws) = sw5In qA0 qB0 qC0 (toWord ws) qF0 := rfl
    rw [hY] at he ⊢
    rw [hQ]
    simp only [List.mem_append] at he
    simp only [List.length_append]
    rcases he with ((((h | h) | h) | h) | h)
    · have := ya e h; omega
    · have := yb e h; omega
    · have := yc e h; omega
    · rcases canonW_entry h with h' | ⟨w, hw, hew⟩
      · omega
      · have hm : e ∈ sw5In qA0 qB0 qC0 (toWord ws) qF0 := by
          simp only [sw5In, swIn, List.mem_append]
          exact Or.inl (Or.inr (mem_toWord_words hw hew))
        have := gQ e hm; omega
    · have := yf e h; omega

/-! ### The output -/

theorem good_sgraph {K X : ℕ} (E : SimpleGraph (Fin n)) (hn : n ≤ X) : Good K X (toWord E) := by
  classical
  change Good K X (toWord fun v : Fin n => Finset.univ.filter (E.Adj v))
  refine good_fun _ hn fun i => good_finset _ fun a _ => good_of_le fun e he => ?_
  simp only [word_simps, List.mem_singleton] at he
  have := a.isLt; omega

theorem good_pgraph {K X : ℕ} (H : PartialGraph (Fin n)) (hn : n ≤ X) (hc : ∀ v, H.color v ≤ X) :
    Good K X (toWord H) := by
  have h1 : Good K X (toWord H.color) := good_fun _ hn fun i => good_of_le fun e he => by
    simp only [word_simps, List.mem_singleton] at he
    have := hc i; omega
  show Good K X (toWord H.color ++ (toWord H.edge ++ toWord H.nonEdge))
  exact h1.append ((good_sgraph H.edge hn).append (good_sgraph H.nonEdge hn))

theorem good_zOut : Good KK XX (zOut G k₀ q₀ P Q s) := by
  have hn := n_le_x G P Q s k₀ q₀
  have hc : ∀ v, (resolveBy G s P Q).color v ≤ XX := fun v => by
    rw [resolveBy_color]; exact color_le_x G P Q s k₀ q₀ v
  show Good KK XX (toWord (resolveBy G s P Q) ++ (toWord (distMatrix (resolveBy G s P Q)) ++
    toWord (family (resolveBy G s P Q) k₀ q₀)))
  refine (good_pgraph _ hn hc).append (Good.append (good_of_le fun e he => ?_)
    (good_fun _ hn fun a => ?_))
  · have := Lax185574Proofs.DistMatrix.toWord_distMatrix_le _ e he; omega
  exact good_tree _ k₀ q₀ ![a]
    (tree_le_cK (by unfold entN; omega) (by unfold entN; omega) (by unfold entN; omega)) hc

/-! ### The bounds -/

theorem ent_arith {L K X Y : ℕ} (hXY : X + 1 ≤ Y) : L + K + X ≤ (K + 1) * (L + Y) := by
  nlinarith

/-- **The entry bounds of `CallBounds`.** -/
theorem entBounds (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ C : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool),
    (∀ c ∈ rcalls G P Q s k₀ q₀, maxEntry (rQ G k₀ q₀ c) + maxEntry (rY G k₀ q₀ c) ≤
      C * ((rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length + ySz (xIn G k₀ q₀ P Q s))) ∧
    maxEntry (zOut G k₀ q₀ P Q s) ≤ C * ((zOut G k₀ q₀ P Q s).length + ySz (xIn G k₀ q₀ P Q s)) := by
  refine ⟨2 * (cK k₀ q₀ + 1), fun n G P Q s => ⟨fun c hc => ?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := ent_call G P Q s k₀ q₀ hk hc
    have m1 := maxEntry_le_bound fun e he => h1 e he
    have m2 := maxEntry_le_bound h2
    have hXY : maxEntry (xIn G k₀ q₀ P Q s) + 1 ≤ ySz (xIn G k₀ q₀ P Q s) := by
      unfold ySz; omega
    have := ent_arith (L := (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length) (K := cK k₀ q₀) hXY
    rw [mul_assoc]
    omega
  · have m := maxEntry_le_bound (good_zOut G P Q s k₀ q₀)
    have hXY : maxEntry (xIn G k₀ q₀ P Q s) + 1 ≤ ySz (xIn G k₀ q₀ P Q s) := by
      unfold ySz; omega
    have := ent_arith (L := (zOut G k₀ q₀ P Q s).length) (K := cK k₀ q₀) hXY
    have h2 : (cK k₀ q₀ + 1) * ((zOut G k₀ q₀ P Q s).length + ySz (xIn G k₀ q₀ P Q s)) ≤
        2 * (cK k₀ q₀ + 1) * ((zOut G k₀ q₀ P Q s).length + ySz (xIn G k₀ q₀ P Q s)) := by
      rw [mul_assoc]; omega
    omega

end Lax185574Proofs.ResolveRam
