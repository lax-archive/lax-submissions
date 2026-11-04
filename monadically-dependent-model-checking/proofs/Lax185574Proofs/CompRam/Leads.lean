import Lax185574Proofs.CompRam.Machine
import Lax185574Proofs.EncodingInjectivity

/-!
Correctness of the stack machine of far composition.

The answers of the three programs are described by `Ans`: a rank shift
maps the word of `tree_{k,q+1}(u)` to that of `tree_{k+1,q}(u)`, a
restriction maps the word of `(tree_{k,q}(u), J)` to that of
`tree_{k,q}(u ↾ J)`, and the canonical form maps a list of words to its
sorted list of distinct words. All trees asked about are trees of the
graph `G`, as in the proof of lem:compose. `frame_leads` shows, by
induction on the depth, that a new frame for two far tuples leads, with
answers of this kind, to the hand-over of the word of their far
composition to the frame below, within `5 (N₁ + N₂)^(d+1)` rounds, where
`Nᵢ` are the numbers of nodes of the two trees.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n))

/-- The answers of the three programs on trees of `G`. -/
def Ans : Qry → List ℕ → Prop
  | .sh w, b => ∃ (kk d l : ℕ) (u : Fin l → Fin n), 1 ≤ l ∧ l ≤ kk ∧
      w = toWord (tree G kk (d + 1) u) ∧ b = toWord (tree G (kk + 1) d u)
  | .re w, b => ∃ (kk d l : ℕ) (u : Fin l → Fin n) (J : List (Fin l)), l ≤ kk ∧ J.Nodup ∧
      w = toWord (tree G kk d u, J) ∧ b = toWord (tree G kk d (fun i => u (J.get i)))
  | .ca ws, b => b = toWord (sortedDistinct ws)

theorem toWord_tree_eq (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n) :
    toWord (tree G kk d u) = [kk, d, l] ++ toWord (node G kk d u) := rfl

theorem toWord_tree_ofFn (kk d : ℕ) {l m : ℕ} (f : Fin m → Fin l) (u : Fin l → Fin n) :
    toWord (tree G kk d (fun i => u ((List.ofFn f).get i))) = toWord (tree G kk d (u ∘ f)) := by
  have key : ∀ (a : ℕ) (ha : a = m) (v : Fin a → Fin n), (∀ j, v j = (u ∘ f) (Fin.cast ha j)) →
      toWord (tree G kk d v) = toWord (tree G kk d (u ∘ f)) := by
    intro a ha v hv
    subst ha
    have : v = u ∘ f := funext fun j => hv j
    rw [this]
  exact key _ (List.length_ofFn) _ (fun j => by simp <;> rfl)

theorem far_snoc_left (kk d : ℕ) {l1 l2 : ℕ} {u₁ : Fin l1 → Fin n} {u₂ : Fin l2 → Fin n}
    (hfar : Far G (rhoMinus kk (d + 1)) u₁ u₂) (i : Fin l1) (b : Fin n)
    (hb : WithinDist G.resolved (rhoPlus (kk + 1) d) (u₁ i) b) :
    Far G (rhoMinus (kk + 1) d) (Fin.snoc u₁ b) u₂ := by
  have hfar' : Far G (rhoMinus (kk + 1) d) u₁ u₂ :=
    fun i j h => hfar i j (withinDist_mono (rhoMinus_succ_le kk d) h)
  have h2 := two_mul_rhoPlus_le_rhoMinus kk d
  have hm := rhoMinus_le_rhoPlus (kk + 1) d
  intro i' j h
  induction i' using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last] at h
    exact hfar i j (withinDist_mono (by omega) (withinDist_trans hb h))
  | cast i' =>
    rw [Fin.snoc_castSucc] at h
    exact hfar' i' j h

theorem far_snoc_right (kk d : ℕ) {l1 l2 : ℕ} {u₁ : Fin l1 → Fin n} {u₂ : Fin l2 → Fin n}
    (hfar : Far G (rhoMinus kk (d + 1)) u₁ u₂) (j : Fin l2) (b : Fin n)
    (hb : WithinDist G.resolved (rhoPlus (kk + 1) d) (u₂ j) b) :
    Far G (rhoMinus (kk + 1) d) u₁ (Fin.snoc u₂ b) := by
  have hfar' : Far G (rhoMinus (kk + 1) d) u₁ u₂ :=
    fun i j h => hfar i j (withinDist_mono (rhoMinus_succ_le kk d) h)
  have h2 := two_mul_rhoPlus_le_rhoMinus kk d
  have hm := rhoMinus_le_rhoPlus (kk + 1) d
  intro i j' h
  induction j' using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last] at h
    exact hfar i j (withinDist_mono (by omega) (withinDist_trans h (withinDist_symm hb)))
  | cast j' =>
    rw [Fin.snoc_castSucc] at h
    exact hfar' i j' h

theorem ext_word_inj {d l : ℕ} {a b : Fin l × Node d (l + 1)} (h : toWord a = toWord b) : a = b := by
  haveI := Lax185574Proofs.EncodingInjectivity.prefixFree_node d (l + 1)
  exact toWord_injective h

theorem atoms_isAtom (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n) :
    ∀ φ ∈ Node.atoms (node G kk d u), DistFO.IsAtom φ :=
  fun φ h => ((mem_atoms_node G kk d u φ).1 h).1

theorem mem_words_index {α : Type*} [WordEncoding α] {S : Finset α} {a : α} (ha : a ∈ S) :
    ∃ j < S.words.length, S.words.getD j [] = toWord a := by
  obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem (mem_words.mpr ⟨a, ha, rfl⟩)
  exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hjw⟩

theorem loop_bound (d c i m mc : ℕ) (hm : m ≤ 5 * i * (c - 1) ^ (d + 1)) (hc : mc ≤ 5 * (c - 1) ^ (d + 1)) :
    m + mc ≤ 5 * (i + 1) * (c - 1) ^ (d + 1) := by
  have : 5 * (i + 1) * (c - 1) ^ (d + 1) = 5 * i * (c - 1) ^ (d + 1) + 5 * (c - 1) ^ (d + 1) := by ring
  omega

theorem final_bound (d c N m : ℕ) (hc : 2 ≤ c) (hN : N + 2 ≤ c) (hm : m ≤ 5 * N * (c - 1) ^ (d + 1)) :
    3 + m + 1 + 1 ≤ 5 * c ^ (d + 1 + 1) := by
  obtain ⟨D, rfl⟩ : ∃ D, c = D + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm
  have hP : 1 ≤ D ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  have h1 : N * D ^ (d + 1) + 1 ≤ D * D ^ (d + 1) := by
    have : N + 1 ≤ D := by omega
    nlinarith
  have h2 : D * D ^ (d + 1) ≤ (D + 1) ^ (d + 1 + 1) := by
    rw [pow_succ (D + 1), Nat.mul_comm]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (by omega)
  nlinarith

/-- The frame of a call while it goes through the extensions. -/
def frm (d kk l1 l2 : ℕ) (X Y SX SY AT : List ℕ) (i : ℕ) (EX : List (List ℕ)) : Fr :=
  { d := d, kk := kk, l1 := l1, l2 := l2, ph := 0, i := i, A := X, B := Y, SA := SX, SB := SY,
    AT := AT, EX := EX }

theorem advance_congr {f g : Fr} (S : List Fr) (h : ({ f with ph := 0 } : Fr) = { g with ph := 0 }) :
    advance f S = advance g S := by
  have hf : advance f S = advance { f with ph := 0 } S := rfl
  have hg : advance g S = advance { g with ph := 0 } S := rfl
  rw [hf, hg, h]

/-- **The machine computes the far composition.** A new frame for the
trees of two far tuples leads to handing the word of their far
composition to the frame below. -/
theorem frame_leads : ∀ (d kk l1 l2 : ℕ) (u₁ : Fin l1 → Fin n) (u₂ : Fin l2 → Fin n)
    (S : List Fr), 1 ≤ l1 → 1 ≤ l2 → l1 + l2 ≤ kk → Far G (rhoMinus kk d) u₁ u₂ →
    ∃ m, m + 1 ≤ 5 * (Node.count (node G kk d u₁) + Node.count (node G kk d u₂)) ^ (d + 1) ∧
      Leads (Ans G)
        (.call (fresh d kk l1 l2 (toWord (node G kk d u₁)) (toWord (node G kk d u₂)) :: S)
          (.ca (atomsQ (fresh d kk l1 l2 (toWord (node G kk d u₁)) (toWord (node G kk d u₂))))))
        (ret (toWord (composeNode (node G kk d u₁) (node G kk d u₂))) [kk, d, l1 + l2] S) m := by
  intro d
  induction d with
  | zero =>
    intro kk l1 l2 u₁ u₂ S h1 h2 hk hfar
    set x := node G kk 0 u₁
    set y := node G kk 0 u₂
    set f := fresh 0 kk l1 l2 (toWord x) (toWord y) with hf
    refine ⟨1, ?_, ?_⟩
    · have := Node.one_le_count x
      have := Node.one_le_count y
      simp only [zero_add, pow_one]
      omega
    · have hc : toWord (sortedDistinct (atomsQ f)) = toWord (composeNode x y) := by
        rw [atomsQ_canon x y f rfl rfl rfl (atoms_isAtom G kk 0 u₁) (atoms_isAtom G kk 0 u₂),
          toWord_node_zero]
      refine Leads.step (b := toWord (sortedDistinct (atomsQ f))) rfl ?_
      rw [round_ph0_zero f S _ rfl rfl, hc]
      exact Leads.refl _
  | succ d ih =>
    intro kk l1 l2 u₁ u₂ S h1 h2 hk hfar
    set x := node G kk (d + 1) u₁ with hx
    set y := node G kk (d + 1) u₂ with hy
    set sx := node G (kk + 1) d u₁ with hsx
    set sy := node G (kk + 1) d u₂ with hsy
    have esx : shiftNode x = sx := shiftNode_node G kk d h1 u₁
    have esy : shiftNode y = sy := shiftNode_node G kk d h2 u₂
    set f0 := fresh (d + 1) kk l1 l2 (toWord x) (toWord y) with hf0
    set AT := toWord (sortedDistinct (atomsQ f0)) with hAT
    have hATw : AT = toWord (Node.atoms (composeNode x y)).words := by
      rw [hAT, atomsQ_canon x y f0 rfl rfl rfl (atoms_isAtom G kk _ u₁) (atoms_isAtom G kk _ u₂)]
    set c := Node.count x + Node.count y with hc
    set nA' := (Node.exts x).words.length with hnA'
    set nB' := (Node.exts y).words.length with hnB'
    /- The frame while it goes through the extensions. -/
    let F : ℕ → List (List ℕ) → Fr := fun i EX =>
      frm (d + 1) kk l1 l2 (toWord x) (toWord y) (toWord sx) (toWord sy) AT i EX
    have hnA : ∀ i EX, nA (F i EX) = nA' := fun i EX => by simp only [nA, F, frm]; rw [extsOf_node]
    have hnB : ∀ i EX, nB (F i EX) = nB' := fun i EX => by simp only [nB, F, frm]; rw [extsOf_node]
    let f1 : Fin l1 × Node d (l1 + 1) → Fin (l1 + l2) × Node d (l1 + l2 + 1) := fun e =>
      (Fin.castAdd l2 e.1, restrictNode (moveLastInv l1 l2) (composeNode e.2 (shiftNode y)))
    let f2 : Fin l2 × Node d (l2 + 1) → Fin (l1 + l2) × Node d (l1 + l2 + 1) := fun e =>
      (Fin.natAdd l1 e.1, composeNode (ℓ₁ := l1) (ℓ₂ := l2 + 1) (shiftNode x) e.2)
    /- What the list of extensions holds after `i` of them. -/
    let Char : ℕ → List (List ℕ) → Prop := fun i EX => ∀ u, u ∈ EX ↔ ∃ j < i,
      (j < nA' ∧ ∃ ε ∈ Node.exts x, toWord ε = (Node.exts x).words.getD j [] ∧ u = toWord (f1 ε)) ∨
      (nA' ≤ j ∧ ∃ ε ∈ Node.exts y, toWord ε = (Node.exts y).words.getD (j - nA') [] ∧
        u = toWord (f2 ε))
    have hD : ∀ (μ : ℕ) (ν : ℕ), μ < Node.count x → ν ≤ Node.count y →
        (μ + ν) ^ (d + 1) ≤ (c - 1) ^ (d + 1) := fun μ ν h1 h2 => Nat.pow_le_pow_left (by omega) _
    have hD' : ∀ (μ : ℕ) (ν : ℕ), μ ≤ Node.count x → ν < Node.count y →
        (μ + ν) ^ (d + 1) ≤ (c - 1) ^ (d + 1) := fun μ ν h1 h2 => Nat.pow_le_pow_left (by omega) _
    /- The loop over the extensions. -/
    have loop : ∀ i ≤ nA' + nB', ∃ EX m, Char i EX ∧ m ≤ 5 * i * (c - 1) ^ (d + 1) ∧
        Leads (Ans G) (advance (F 0 []) S) (advance (F i EX) S) m := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨[], 0, fun u => ?_, by simp, Leads.refl _⟩
        simp
      | succ i ihi =>
        intro hi
        obtain ⟨EX, m, hch, hm, hL⟩ := ihi (by omega)
        have hadv : advance (F i EX) S =
            .call (child (F i EX) :: { F i EX with ph := 3 } :: S) (.ca (atomsQ (child (F i EX)))) :=
          advance_lt _ _ (by rw [hnA, hnB]; show i < nA' + nB'; omega)
        by_cases hiA : i < nA'
        · -- an extension of the first tree
          obtain ⟨ε, hε, hεw⟩ := extsOf_getD x hiA
          have hεw' : (Node.exts x).words.getD i [] = toWord ε := by rw [← extsOf_node, hεw, toWord_ext]
          obtain ⟨g, b, hb, rfl⟩ := (mem_exts_node G kk d u₁ ε).1 hε
          have hch' : child (F i EX) = fresh d (kk + 1) (l1 + 1) l2
              (toWord (node G (kk + 1) d (Fin.snoc u₁ b))) (toWord sy) := by
            rw [child_lt _ (by rw [hnA]; exact hiA)]
            simp only [F, frm] at hεw ⊢
            rw [hεw]
            simp [fresh]
          obtain ⟨mc, hmc, hLc⟩ := ih (kk + 1) (l1 + 1) l2 (Fin.snoc u₁ b) u₂
            ({ F i EX with ph := 3 } :: S) (by omega) h2 (by omega) (far_snoc_left G kk d hfar g b hb)
          rw [← hch'] at hLc
          set w := Fin.append (Fin.snoc u₁ b) u₂ with hw
          have hcomp : composeNode (node G (kk + 1) d (Fin.snoc u₁ b)) (node G (kk + 1) d u₂) =
              node G (kk + 1) d w :=
            composeNode_node G d (kk + 1) _ _ (by omega) h2 (far_snoc_left G kk d hfar g b hb)
          have hret := ret_lt (toWord (composeNode (node G (kk + 1) d (Fin.snoc u₁ b))
            (node G (kk + 1) d u₂))) [kk + 1, d, l1 + 1 + l2] { F i EX with ph := 3 } S
            (by show i < nA (F i EX); rw [hnA]; exact hiA)
          rw [hret] at hLc
          set J := List.ofFn (moveLast l1 l2) with hJ
          set bR := toWord (tree G (kk + 1) d (w ∘ moveLast l1 l2)) with hbR
          have hans : Ans G (.re (reQuery { F i EX with ph := 3 } (toWord (composeNode
              (node G (kk + 1) d (Fin.snoc u₁ b)) (node G (kk + 1) d u₂))))) bR := by
            refine ⟨kk + 1, d, l1 + 1 + l2, w, J, by omega, nodup_jList l1 l2, ?_, ?_⟩
            · rw [hcomp]
              show [kk + 1, d + 1 - 1, l1 + 1 + l2] ++ toWord (node G (kk + 1) d w) ++
                ((l1 + l2 + 1) :: jList l1 l2) = toWord (tree G (kk + 1) d w) ++ toWord J
              rw [hJ, toWord_jList, toWord_tree_eq]
              simp
            · rw [hbR, hJ, toWord_tree_ofFn]
          have hitem : ((extsOf (F i EX).A).getD (F i EX).i []).headD 0 :: bR.drop 3 =
              toWord (f1 (g, node G (kk + 1) d (Fin.snoc u₁ b))) := by
            have hr : restrictNode (moveLastInv l1 l2)
                (composeNode (node G (kk + 1) d (Fin.snoc u₁ b)) (shiftNode y)) =
                node G (kk + 1) d (w ∘ moveLast l1 l2) := by
              rw [esy, hsy, hcomp, restrictNode_node G d (kk + 1) (isPInv_moveLast l1 l2)]
            show ((extsOf (toWord x)).getD i []).headD 0 :: bR.drop 3 = _
            rw [hεw, hbR, toWord_tree_eq]
            simp only [List.headD_cons, f1, toWord_ext, Fin.val_castAdd, hr]
            rfl
          have hround := round_ph4 ({ { F i EX with ph := 3 } with ph := 4 }) S bR rfl
          refine ⟨EX ++ [toWord (f1 (g, node G (kk + 1) d (Fin.snoc u₁ b)))], m + (mc + 1), ?_, ?_, ?_⟩
          · intro u
            rw [List.mem_append, hch u, List.mem_singleton]
            constructor
            · rintro (⟨j, hj, hj'⟩ | rfl)
              · exact ⟨j, by omega, hj'⟩
              · exact ⟨i, by omega, Or.inl ⟨hiA, _, hε, hεw'.symm, rfl⟩⟩
            · rintro ⟨j, hj, hj'⟩
              rcases Nat.lt_or_ge j i with hji | hji
              · exact Or.inl ⟨j, hji, hj'⟩
              · obtain rfl : j = i := by omega
                rcases hj' with ⟨-, ε', hε', hw', rfl⟩ | ⟨hle, -⟩
                · right
                  rw [hεw'] at hw'
                  rw [ext_word_inj hw']
                · omega
          · have hcc : Node.count (node G (kk + 1) d (Fin.snoc u₁ b)) < Node.count x :=
              Node.count_child_lt x hε
            have := hD _ (Node.count (node G (kk + 1) d u₂)) hcc
              (by have := count_shiftNode_le y; rw [esy] at this; exact this)
            exact loop_bound d c i m (mc + 1) hm (by omega)
          · refine hL.trans ?_
            rw [hadv]
            refine hLc.trans (Leads.step hans ?_)
            rw [hround]
            rw [advance_congr S (g := F (i + 1) (EX ++ [toWord (f1 (g, node G (kk + 1) d (Fin.snoc u₁ b)))]))
              (by rw [← hitem]; rfl)]
            exact Leads.refl _
        · -- an extension of the second tree
          have hiB : i - nA' < nB' := by omega
          obtain ⟨ε, hε, hεw⟩ := extsOf_getD y hiB
          have hεw' : (Node.exts y).words.getD (i - nA') [] = toWord ε := by
            rw [← extsOf_node, hεw, toWord_ext]
          obtain ⟨g, b, hb, rfl⟩ := (mem_exts_node G kk d u₂ ε).1 hε
          have hch' : child (F i EX) = fresh d (kk + 1) l1 (l2 + 1) (toWord sx)
              (toWord (node G (kk + 1) d (Fin.snoc u₂ b))) := by
            rw [child_ge _ (by rw [hnA]; exact hiA), hnA]
            simp only [F, frm] at hεw ⊢
            rw [hεw]
            simp [fresh]
          obtain ⟨mc, hmc, hLc⟩ := ih (kk + 1) l1 (l2 + 1) u₁ (Fin.snoc u₂ b)
            ({ F i EX with ph := 3 } :: S) h1 (by omega) (by omega) (far_snoc_right G kk d hfar g b hb)
          rw [← hch'] at hLc
          set R := toWord (composeNode (node G (kk + 1) d u₁) (node G (kk + 1) d (Fin.snoc u₂ b)))
            with hR
          have hret := ret_ge R [kk + 1, d, l1 + (l2 + 1)] { F i EX with ph := 3 } S
            (by show ¬ i < nA (F i EX); rw [hnA]; exact hiA)
          rw [hret] at hLc
          have hitem : (l1 + ((extsOf (toWord y)).getD (i - nA') []).headD 0) :: R =
              toWord (f2 (g, node G (kk + 1) d (Fin.snoc u₂ b))) := by
            rw [hεw, hR]
            simp only [List.headD_cons, f2, toWord_ext, Fin.val_natAdd, esx]
            rfl
          refine ⟨EX ++ [toWord (f2 (g, node G (kk + 1) d (Fin.snoc u₂ b)))], m + (mc + 0), ?_, ?_, ?_⟩
          · intro u
            rw [List.mem_append, hch u, List.mem_singleton]
            constructor
            · rintro (⟨j, hj, hj'⟩ | rfl)
              · exact ⟨j, by omega, hj'⟩
              · exact ⟨i, by omega, Or.inr ⟨by omega, _, hε, hεw'.symm, rfl⟩⟩
            · rintro ⟨j, hj, hj'⟩
              rcases Nat.lt_or_ge j i with hji | hji
              · exact Or.inl ⟨j, hji, hj'⟩
              · obtain rfl : j = i := by omega
                rcases hj' with ⟨hlt, -⟩ | ⟨-, ε', hε', hw', rfl⟩
                · omega
                · right
                  rw [hεw'] at hw'
                  rw [ext_word_inj hw']
          · have hcc : Node.count (node G (kk + 1) d (Fin.snoc u₂ b)) < Node.count y :=
              Node.count_child_lt y hε
            have := hD' (Node.count (node G (kk + 1) d u₁)) _
              (by have := count_shiftNode_le x; rw [esx] at this; exact this) hcc
            exact loop_bound d c i m (mc + 0) hm (by omega)
          · refine hL.trans ?_
            rw [hadv]
            refine hLc.trans ?_
            rw [advance_congr S (g := F (i + 1) (EX ++ [toWord (f2 (g, node G (kk + 1) d (Fin.snoc u₂ b)))]))
              (by rw [← hitem]; simp only [F, frm, nA, extsOf_node]; rfl)]
            exact Leads.refl _
    /- The three first rounds, the loop and the last round. -/
    obtain ⟨EX, ml, hch, hml, hL⟩ := loop (nA' + nB') le_rfl
    have hfin : sortedDistinct EX = (Node.exts (composeNode x y)).words := by
      refine sortedDistinct_eq_words _ _ fun u => ?_
      rw [hch u, exts_composeNode]
      simp only [Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨j, -, (⟨-, ε, hε, -, rfl⟩ | ⟨-, ε, hε, -, rfl⟩)⟩
        · exact ⟨f1 ε, Or.inl ⟨ε, hε, rfl⟩, rfl⟩
        · exact ⟨f2 ε, Or.inr ⟨ε, hε, rfl⟩, rfl⟩
      · rintro ⟨a, (⟨ε, hε, rfl⟩ | ⟨ε, hε, rfl⟩), rfl⟩
        · obtain ⟨j, hj, hjw⟩ := mem_words_index hε
          exact ⟨j, by omega, Or.inl ⟨hj, ε, hε, hjw.symm, rfl⟩⟩
        · obtain ⟨j, hj, hjw⟩ := mem_words_index hε
          exact ⟨nA' + j, by omega, Or.inr ⟨by omega, ε, hε,
            by rw [Nat.add_sub_cancel_left]; exact hjw.symm, rfl⟩⟩
    have hres : AT ++ toWord (sortedDistinct EX) = toWord (composeNode x y) := by
      rw [hATw, hfin, toWord_node_succ]
    have hlast : Leads (Ans G) (advance (F (nA' + nB') EX) S)
        (ret (toWord (composeNode x y)) [kk, d + 1, l1 + l2] S) 1 := by
      rw [advance_ge _ _ (by rw [hnA, hnB]; show ¬ nA' + nB' < nA' + nB'; omega)]
      refine Leads.step (b := toWord (sortedDistinct EX)) rfl ?_
      rw [round_ph5 _ S _ rfl]
      show Leads (Ans G) (ret (AT ++ toWord (sortedDistinct EX)) [kk, d + 1, l1 + l2] S) _ 0
      rw [hres]
      exact Leads.refl _
    let f2' : Fr := { { f0 with ph := 1, AT := AT } with ph := 2, SB := (toWord (tree G (kk + 1) d u₂)).drop 3 }
    have h3 : Leads (Ans G) (round (f2' :: S) (toWord (tree G (kk + 1) d u₁)))
        (ret (toWord (composeNode x y)) [kk, d + 1, l1 + l2] S) (ml + 1) := by
      rw [round_ph2 _ S _ rfl, advance_congr S (g := F 0 []) (by simp [F, frm, f2', hf0, fresh, toWord_tree_eq]; exact ⟨rfl, rfl⟩)]
      exact hL.trans hlast
    have h2' : Leads (Ans G) (round ({ f0 with ph := 1, AT := AT } :: S) (toWord (tree G (kk + 1) d u₂)))
        (ret (toWord (composeNode x y)) [kk, d + 1, l1 + l2] S) (ml + 1 + 1) := by
      rw [round_ph1 _ S _ rfl]
      exact Leads.step ⟨kk, d, l1, u₁, h1, by omega, rfl, rfl⟩ h3
    have h1' : Leads (Ans G) (round (f0 :: S) AT)
        (ret (toWord (composeNode x y)) [kk, d + 1, l1 + l2] S) (ml + 1 + 1 + 1) := by
      rw [round_ph0_succ _ S _ rfl (by simp [hf0, fresh])]
      exact Leads.step ⟨kk, d, l2, u₂, h2, by omega, rfl, rfl⟩ h2'
    refine ⟨ml + 1 + 1 + 1 + 1, ?_, Leads.step rfl h1'⟩
    have hnA1 : nA' < Node.count x := lt_of_le_of_lt (length_words_le _) (Node.card_exts_lt_count x)
    have hnB1 : nB' < Node.count y := lt_of_le_of_lt (length_words_le _) (Node.card_exts_lt_count y)
    have := final_bound d c (nA' + nB') ml (by omega) (by omega) hml
    omega

/-- **The machine from the first frame.** For far tuples `u₁`, `u₂` the
stack with the frame of their trees leads to the output of the word of
`tree_{k,q}(u₁ u₂)`. -/
theorem root_leads (k q l1 l2 : ℕ) (u₁ : Fin l1 → Fin n) (u₂ : Fin l2 → Fin n) (h1 : 1 ≤ l1)
    (h2 : 1 ≤ l2) (hk : l1 + l2 ≤ k)
    (hfar : ∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) :
    ∃ m, m + 1 ≤ 5 * (Node.count (node G k q u₁) + Node.count (node G k q u₂)) ^ (q + 1) ∧
      Leads (Ans G)
        (.call [fresh q k l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))]
          (.ca (atomsQ (fresh q k l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))))))
        (.done (toWord (tree G k q (Fin.append u₁ u₂)))) m := by
  obtain ⟨m, hm, hL⟩ := frame_leads G q k l1 l2 u₁ u₂ [] h1 h2 hk hfar
  refine ⟨m, hm, ?_⟩
  rw [composeNode_node G q k u₁ u₂ h1 h2 hfar] at hL
  exact hL

end Lax185574Proofs.CompRam
