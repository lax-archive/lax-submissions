import Lax185574Proofs.ResolveRam.LenCalls

/-!
The lengths of the queries of the canonical form.

The atom query of an item lists the new atoms of its root without
repetition (`nodup_candL`), and these are atoms of `H` of a tuple reached
by guarded extensions in `H`. So there are at most a constant times
`T + 1` of them by lem:locality (`atomL_length_le`). The query of the
children of an item lists one word per member of its expansion, at most
`(k₀ + q₀ + 2)² T` (`length_kidsOf_le`), and each is a root of a tree of
`H` of a tuple reached by guarded extensions, of size polynomial in `T`
(`liftT_length_le`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.TypeTreeSizes Lax185574.DistanceLogic
open Lax3.DistFO (rhoMinus rhoPlus)

theorem nodup_pairsL (ℓ : ℕ) : (pairsL ℓ).Nodup := by
  unfold pairsL
  refine List.nodup_flatMap.2 ⟨fun i _ => (List.nodup_finRange ℓ).map (fun a b h => by simpa using h), ?_⟩
  refine (List.nodup_finRange ℓ).pairwise_of_forall_ne ?_
  intro i _ j _ hij
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
  exact hij (congrArg Prod.fst h).symm
theorem nodup_candL (k q ℓ : ℕ) {cs : List ℕ} (hcs : cs.Nodup) : (candL k q ℓ cs).Nodup := by
  have hp := nodup_pairsL ℓ
  unfold candL
  simp only [List.nodup_append]
  refine ⟨⟨⟨⟨⟨hp.map ?_, hp.map ?_, ?_⟩, hp.map ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [DistFO.eq.injEq] at h; rw [h.1, h.2]
  · rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [DistFO.edge.injEq] at h; rw [h.1, h.2]
  · intro a ha b hb; simp only [List.mem_map] at ha hb; aesop
  · rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [DistFO.nonEdge.injEq] at h; rw [h.1, h.2]
  · intro a ha b hb; simp only [List.mem_append, List.mem_map] at ha hb; aesop
  · refine List.nodup_flatMap.2 ⟨fun Y _ => (List.nodup_finRange ℓ).map (fun a b h => by simpa using h), ?_⟩
    refine hcs.pairwise_of_forall_ne ?_
    intro Y _ Z _ hYZ
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
    simp only [DistFO.color.injEq] at h
    exact hYZ h.1.symm
  · intro a ha b hb; simp only [List.mem_append, List.mem_map, List.mem_flatMap] at ha hb; aesop
  · refine List.nodup_flatMap.2 ⟨fun r _ => hp.map ?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [DistFO.distLe.injEq] at h; rw [h.2.1, h.2.2]
    refine (List.nodup_range).pairwise_of_forall_ne ?_
    intro Y _ Z _ hYZ
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
    simp only [DistFO.distLe.injEq] at h
    exact hYZ h.1.symm
  · intro a ha b hb; simp only [List.mem_append, List.mem_map, List.mem_flatMap] at ha hb; aesop
  · refine List.nodup_flatMap.2 ⟨fun r _ => ?_, ?_⟩
    · refine List.nodup_flatMap.2 ⟨fun Y _ => (List.nodup_finRange ℓ).map (fun a b h => by simpa using h), ?_⟩
      refine hcs.pairwise_of_forall_ne ?_
      intro Y _ Z _ hYZ
      simp only [Function.onFun, List.disjoint_left, List.mem_map]
      rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
      simp only [DistFO.distColorLt.injEq] at h
      exact hYZ h.2.1.symm
    refine (List.nodup_range).pairwise_of_forall_ne ?_
    intro Y _ Z _ hYZ
    simp only [Function.onFun, List.disjoint_left, List.mem_flatMap, List.mem_map]
    rintro _ ⟨c, -, a, -, rfl⟩ ⟨d, -, b, -, h⟩
    simp only [DistFO.distColorLt.injEq] at h
    exact hYZ h.1.symm
  · intro a ha b hb; simp only [List.mem_append, List.mem_map, List.mem_flatMap] at ha hb; aesop

theorem isAtom_candL {k q ℓ : ℕ} {cs : List ℕ} {φ : DistFO ℓ} (h : φ ∈ candL k q ℓ cs) :
    DistFO.IsAtom φ := by
  simp only [candL, List.mem_append, List.mem_map, List.mem_flatMap] at h
  aesop (add norm simp DistFO.IsAtom)

theorem wordLength_words_le {ws : List (List ℕ)} {B : ℕ} (h : ∀ w ∈ ws, w.length ≤ B) :
    wordLength ws ≤ 1 + ws.length * (B + 1) := by
  rw [wordLength_list]
  have h1 := List.sum_le_card_nsmul (ws.map wordLength) (B + 1) (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [wordLength_list_nat]; exact Nat.succ_le_succ (h w hw))
  simp only [List.length_map, smul_eq_mul] at h1
  omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The bound on the number of new atoms of an item. -/
def atomCnt (k₀ q₀ T : ℕ) : ℕ := 6 * (rhoPlus k₀ q₀ + 1) * (T + 1) * ((q₀ + 1) * (q₀ + 1))

theorem atomL_length_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) (w : Fin (d + 1) → Fin n)
    (hw : Guarded (resolveBy G s P Q) k₀ q₀ d w) :
    (atomL (dataOf G P Q s k₀ q₀) (k₀ + d) (q₀ - d) (colsL G) (node G (k₀ + d) (q₀ - d) w)).length ≤
      atomCnt k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  classical
  set H := resolveBy G s P Q
  set D := dataOf G P Q s k₀ q₀
  have hnd : (atomL D (k₀ + d) (q₀ - d) (colsL G) (node G (k₀ + d) (q₀ - d) w)).Nodup :=
    (nodup_candL _ _ _ (Finset.sort_nodup _ _)).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  have he : (atomL D (k₀ + d) (q₀ - d) (colsL G) (node G (k₀ + d) (q₀ - d) w)).toFinset =
      Node.atoms (node H (k₀ + d) (q₀ - d) w) := by
    have e : newAtoms D (k₀ + d) (q₀ - d) (node G (k₀ + d) (q₀ - d) w) =
        Node.atoms (node H (k₀ + d) (q₀ - d) w) :=
      newAtoms_node D (dataOf_spec G P Q s k₀ q₀) (k₀ + d) (q₀ - d) w
    rw [← e]
    ext φ
    rw [List.mem_toFinset, mem_atomL D _ _ (fun Y => mem_colsL G P Q s k₀ q₀ Y)]
  rw [he]
  have hsub : (↑(Node.atoms (node H (k₀ + d) (q₀ - d) w)) : Set (DistFO (d + 1))) ⊆
      atp H (k₀ + d) (q₀ - d) w := fun φ hφ => (mem_atoms_node H _ _ w φ).1 hφ
  have h1 := Set.ncard_le_ncard hsub (atp_finite H _ _ w)
  rw [Set.ncard_coe_finset] at h1
  have hloc := Lax185574.TreeLocality.ball_of_guarded H k₀ q₀ d hd w hw
  have hR := rhoPlus_shift_le k₀ q₀ d hd
  have hA := ncard_atp_le H (k₀ + d) (q₀ - d) (d + 1) w (rhoPlus k₀ q₀) hR
    (H.color '' H.ball (rhoPlus k₀ q₀) (w 0)) (Set.toFinite _)
    (fun φ hφ Y hY => by
      obtain ⟨u, hu, hc⟩ := hloc.2 φ hφ Y hY
      exact ⟨u, hu, hc⟩)
  have hc := (ballCounts_resolve G P Q s k₀ q₀ hk (w 0)).colors
  have : 6 * (rhoPlus k₀ q₀ + 1) * ((H.color '' H.ball (rhoPlus k₀ q₀) (w 0)).ncard + 1) *
      ((d + 1) * (d + 1)) ≤ atomCnt k₀ q₀ (treeCount G H k₀ q₀) := by
    unfold atomCnt
    gcongr <;> omega
  omega

/-- The bound on the word of the atom query of an item. -/
def atomQB (k₀ q₀ T : ℕ) : ℕ := 1 + atomCnt k₀ q₀ T * 6

theorem atomQ_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    wordLength (atomQ G P Q s k₀ q₀ x.2) ≤
      atomQB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk d hd x hx
  rw [hwx]
  have hl := atomL_length_le G P Q s k₀ q₀ hk hd w hw
  unfold atomQ
  refine le_trans (wordLength_words_le (B := 5) ?_) ?_
  · intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨φ, hφ, rfl⟩ := hu
    exact wordLength_atom_le φ (isAtom_candL (List.mem_filter.1 hφ).1)
  · simp only [List.length_map, tree]
    unfold atomQB
    have := Nat.mul_le_mul_right 6 hl
    omega

/-! ### The children of an item -/

theorem length_filter_zip {α β : Type*} (p : α → Bool) :
    ∀ (A : List α) (B : List β), ((A.zip B).filter (fun y => p y.1)).length ≤ (A.filter p).length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: A, b :: B => by
    have ih := length_filter_zip p A B
    simp only [List.zip_cons_cons, List.filter_cons]
    split_ifs <;> simp <;> omega

theorem filter_nextLevel_nil (ex : TypeTree → List (ℕ × TypeTree)) (L : List Item) {j i : ℕ}
    (h : i < j) : (((L.zipIdx j).flatMap fun x => (ex x.1.2).map fun gc => ((x.2, gc.1), gc.2)).filter
      (fun y => decide (y.1.1 = i))) = [] := by
  rw [List.filter_eq_nil_iff]
  intro y hy
  simp only [List.mem_flatMap, List.mem_map] at hy
  obtain ⟨x, hx, gc, -, rfl⟩ := hy
  have := List.le_snd_of_mem_zipIdx hx
  simp only [decide_eq_true_eq]
  omega

theorem length_filter_nextLevel (ex : TypeTree → List (ℕ × TypeTree)) (B i : ℕ) :
    ∀ (L : List Item) (j : ℕ), (∀ x ∈ L, (ex x.2).length ≤ B) →
      (((L.zipIdx j).flatMap fun x => (ex x.1.2).map fun gc => ((x.2, gc.1), gc.2)).filter
        (fun y => decide (y.1.1 = i))).length ≤ B
  | [], _, _ => by simp
  | a :: L, j, hB => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, List.length_append]
    by_cases hji : j = i
    · subst hji
      rw [filter_nextLevel_nil ex L (by omega), List.length_nil, Nat.add_zero]
      rw [List.filter_eq_self.2 (fun y hy => by
        simp only [List.mem_map] at hy; obtain ⟨gc, -, rfl⟩ := hy; simp)]
      simpa using hB a (by simp)
    · rw [List.filter_eq_nil_iff.2 (fun y hy => by
        simp only [List.mem_map] at hy; obtain ⟨gc, -, rfl⟩ := hy; simpa using hji)]
      simpa using length_filter_nextLevel ex B i L (j + 1) (fun x hx => hB x (by simp [hx]))

theorem length_kidsOf_le (ex : TypeTree → List (ℕ × TypeTree)) (L : List Item) (On : List TypeTree)
    (B i : ℕ) (hB : ∀ x ∈ L, (ex x.2).length ≤ B) : (kidsOf (nextLevel ex L) On i).length ≤ B := by
  unfold kidsOf
  rw [List.length_map]
  refine le_trans (length_filter_zip (fun y : Item => decide (y.1.1 = i)) _ On) ?_
  exact length_filter_nextLevel ex B i L 0 hB

theorem rootAs_length {ν : TypeTree} {q ℓ : ℕ} {r : Node q ℓ} (h : TypeTree.rootAs ν q ℓ = some r) :
    wordLength r + 3 ≤ wordLength ν := by
  rcases ν with ⟨k, q', ℓ', t⟩
  unfold TypeTree.rootAs at h
  split_ifs at h with hq
  · obtain ⟨rfl, rfl⟩ := hq
    simp only [Option.some.injEq] at h
    subst h
    rw [wordLength_tt]; simp only; omega

/-- The bound on the trees of `H` of tuples reached by guarded extensions. -/
noncomputable def kidB (k₀ q₀ T : ℕ) : ℕ :=
  3 + (∑ m ∈ Finset.range (q₀ + 1), sizeCoeff (1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1)))
    (q₀ + 1) m) * (T + 1) ^ (q₀ + 1)

theorem nodeH_le (hk : 1 ≤ k₀) {j : ℕ} (hj : j ≤ q₀) (w : Fin (j + 1) → Fin n)
    (hw : Guarded (resolveBy G s P Q) k₀ q₀ j w) :
    wordLength (node (resolveBy G s P Q) (k₀ + j) (q₀ - j) w) + 3 ≤
      kidB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  unfold kidB
  have h1 := node_length_le_of hk (ballCounts_resolve G P Q s k₀ q₀ hk (w 0)) (q₀ - j) j
    (by omega) w rfl hw
  set T := treeCount G (resolveBy G s P Q) k₀ q₀
  set A0 := 1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1))
  have hA : atomBound k₀ q₀ T ≤ A0 * (T + 1) := by
    unfold atomBound
    have e : A0 * (T + 1) = (T + 1) + 6 * (rhoPlus k₀ q₀ + 1) * (T + 1) * ((q₀ + 1) * (q₀ + 1)) * 6 := by
      simp only [A0]; ring
    omega
  have h2 := sizeBound_le _ A0 (q₀ + 1) T hA (q₀ - j)
  have h3 : sizeCoeff A0 (q₀ + 1) (q₀ - j) ≤ ∑ m ∈ Finset.range (q₀ + 1), sizeCoeff A0 (q₀ + 1) m :=
    Finset.single_le_sum (f := fun m => sizeCoeff A0 (q₀ + 1) m) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  have h4 : (T + 1) ^ (q₀ - j + 1) ≤ (T + 1) ^ (q₀ + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have := Nat.mul_le_mul h3 h4
  omega

theorem lift_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    wordLength (liftT (dataOf G P Q s k₀ q₀) (farMapOf G) x.2) ≤
      kidB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk d hd x hx
  rw [hwx]
  have e : liftT (dataOf G P Q s k₀ q₀) (farMapOf G) (tree G (k₀ + d) (q₀ - d) w) =
      ⟨k₀ + d, q₀ - d, d + 1, node (resolveBy G s P Q) (k₀ + d) (q₀ - d) w⟩ := by
    simp only [liftT, tree]
    rw [resolveNodeF_node _ (farMapOf G) (dataOf_spec G P Q s k₀ q₀) (farSpec_farMapOf G)
      (q₀ - d) (k₀ + d) w (by omega) (by omega) (by omega) (by omega)]
    rfl
  rw [e, wordLength_tt]
  have := nodeH_le G P Q s k₀ q₀ hk hd w hw
  simp only
  omega

/-- The bound on the word of the query of the children of an item. -/
noncomputable def kidQB (k₀ q₀ T : ℕ) : ℕ := 1 + exMaxT k₀ q₀ T * (kidB k₀ q₀ T + 1)

theorem kidQ_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) {y : Item × ℕ}
    (hy : y ∈ (lvR G P Q s k₀ q₀ d).zipIdx) :
    wordLength (kidQ G P Q s k₀ q₀ d y.2 y.1.2) ≤
      kidQB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  set T := treeCount G (resolveBy G s P Q) k₀ q₀
  obtain ⟨hi, hyx⟩ := List.mem_zipIdx' (x := y.1) (i := y.2) hy
  have hx : y.1 ∈ lvR G P Q s k₀ q₀ d := by rw [hyx]; exact List.getElem_mem _
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
  set m := q₀ - d - 1
  rw [show q₀ - d = m + 1 by omega] at hu
  rw [hu]
  show wordLength ((kidL m ℓ (kidsOf (lvR G P Q s k₀ q₀ (d + 1))
    (outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1)) y.2)).map toWord) ≤ _
  have hO : outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1) =
      (lvR G P Q s k₀ q₀ (d + 1)).map fun x => liftT (dataOf G P Q s k₀ q₀) (farMapOf G) x.2 := by
    refine outsAt_eq _ (farMapOf G) (dataOf_spec G P Q s k₀ q₀) (farSpec_farMapOf G)
      (expandOK_exR G P Q s k₀ q₀) ?_ _ _ (by omega)
    intro x hx
    simp only [famItems, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact ⟨1, ![b], by simp [family], le_rfl, hk⟩
  set kids := kidsOf (lvR G P Q s k₀ q₀ (d + 1)) (outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1)) y.2
  have hcnt : kids.length ≤ exMaxT k₀ q₀ T := by
    have := length_kidsOf_le (exR G P Q s k₀ q₀) (lvR G P Q s k₀ q₀ d)
      (outR G P Q s k₀ q₀ (q₀ - (d + 1)) (d + 1)) (exMaxT k₀ q₀ T) y.2
      (fun x hx => length_exR_leT G P Q s k₀ q₀ hk hd.le hx)
    have e : lvR G P Q s k₀ q₀ (d + 1) = nextLevel (exR G P Q s k₀ q₀) (lvR G P Q s k₀ q₀ d) := by
      unfold lvR; rw [levels_succ]
    simp only [kids, e]
    exact this
  have hkid : ∀ p ∈ kids, wordLength p.2 ≤ kidB k₀ q₀ T := by
    intro p hp
    simp only [kids, kidsOf, List.mem_map, List.mem_filter] at hp
    obtain ⟨z, ⟨hz, -⟩, rfl⟩ := hp
    have h2 := List.of_mem_zip hz
    rw [hO] at h2
    obtain ⟨x', hx', hzx⟩ := List.mem_map.1 h2.2
    rw [← hzx]
    exact lift_le G P Q s k₀ q₀ hk (by omega) hx'
  refine le_trans (wordLength_words_le (B := kidB k₀ q₀ T)
    (ws := (kidL m ℓ kids).map toWord) ?_) ?_
  · intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨e, he, rfl⟩ := hv
    simp only [kidL, List.mem_filterMap] at he
    obtain ⟨p, hp, hpe⟩ := he
    split_ifs at hpe with hpl
    rcases hr : TypeTree.rootAs p.2 m (ℓ + 1) with _ | r
    · rw [hr] at hpe; simp at hpe
    · rw [hr] at hpe
      simp only [Option.map_some, Option.some.injEq] at hpe
      subst hpe
      have h3 := rootAs_length hr
      have h4 := hkid p hp
      show wordLength ((⟨p.1, hpl⟩ : Fin ℓ), r) ≤ _
      rw [wordLength_prod]
      have : wordLength (⟨p.1, hpl⟩ : Fin ℓ) = 1 := rfl
      omega
  · have hl : (kidL m ℓ kids).length ≤ kids.length := List.length_filterMap_le _ _
    simp only [List.length_map]
    unfold kidQB
    have := Nat.mul_le_mul_right (kidB k₀ q₀ T + 1) (hl.trans hcnt)
    omega

end Lax185574Proofs.ResolveRam
