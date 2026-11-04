import Lax185574Proofs.MainRam.Defs

/-!
Facts about the words handled by a thread: the entries of an instance
are at most its length, clipping leaves an instance alone, and the
output of the validation is always an instance of thm:mc on a
construction sequence.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim
open Lax3.FirstOrder Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionSequences Lax185574.PartialGraphs Lax185574.InstanceEncoding

/-! ### Entries -/

theorem code_entries_lt : ∀ {k : ℕ} (φ : FO k), ∀ v ∈ code φ, v < k + (code φ).length + 4
  | _, .adj i j => by
      intro v hv
      simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hv
      have := i.isLt; have := j.isLt
      rcases hv with rfl | rfl | rfl <;> simp [code] <;> omega
  | _, .eq i j => by
      intro v hv
      simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hv
      have := i.isLt; have := j.isLt
      rcases hv with rfl | rfl | rfl <;> simp [code] <;> omega
  | _, .not φ => by
      intro v hv
      simp only [code, List.mem_cons] at hv
      have ih := code_entries_lt φ
      rcases hv with rfl | hv
      · simp [code]
      · have := ih v hv; simp [code]; omega
  | _, .and φ ψ => by
      intro v hv
      simp only [code, List.mem_cons, List.mem_append] at hv
      have ih₁ := code_entries_lt φ
      have ih₂ := code_entries_lt ψ
      rcases hv with rfl | hv | hv
      · simp [code]
      · have := ih₁ v hv; simp [code]; omega
      · have := ih₂ v hv; simp [code]; omega
  | _, .ex φ => by
      intro v hv
      simp only [code, List.mem_cons] at hv
      have ih := code_entries_lt φ
      rcases hv with rfl | hv
      · simp [code]
      · have := ih v hv; simp [code]; omega

theorem toWord_fo (φ : FO 0) : toWord φ = code φ := Lax185574Proofs.Legacy.encode_eq_foCode φ

theorem graph_entries_le {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G) :
    ∀ v ∈ g, v ≤ g.length := by
  intro v hv
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have hl := hg.length_eq
  have hgd : ∀ i, g.getD i 0 = if h : i < g.length then g[i] else 0 := by
    intro i; split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]
  by_cases h0 : j = 0
  · subst h0
    have := hg.vertexCount_eq
    simp only [vertexCount, hgd, dif_pos hj] at this
    omega
  by_cases h1 : j = 1
  · subst h1
    have : g.getD 1 0 = edgeCount g := rfl
    rw [hgd, dif_pos hj] at this
    omega
  by_cases h2 : j < 3 + n
  · -- an offset, at most `2 E`
    have hmono : ∀ i ≤ n, offset g i ≤ 2 * edgeCount g := by
      intro i hi
      induction hi using Nat.decreasingInduction with
      | self => exact le_of_eq hg.offset_last
      | of_succ k hk ih => exact le_trans (hg.offset_mono k hk) ih
    have := hmono (j - 2) (by omega)
    simp only [offset, hgd, show 2 + (j - 2) = j by omega, dif_pos hj] at this
    omega
  · -- a target, below `n`
    have := hg.target_lt (j - (3 + n)) (by omega)
    simp only [target, hg.vertexCount_eq, hgd, show 3 + n + (j - (3 + n)) = j by omega,
      dif_pos hj] at this
    omega

/-- Every entry of an instance is at most its length. -/
theorem instance_entries_le {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (hg : EncodesGraph g n G) (φ : FO 0) : ∀ v ∈ g ++ toWord φ, v ≤ (g ++ toWord φ).length := by
  intro v hv
  have hl := hg.length_eq
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · have := graph_entries_le hg v hv; simp; omega
  · rw [toWord_fo] at hv; have := code_entries_lt φ v hv; simp [toWord_fo]; omega

theorem vertexCount_le {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G) :
    n ≤ g.length := by
  have := hg.length_eq; omega

/-! ### Clipping -/

theorem clipList_length (v : ℕ) (u : List ℕ) : (clipList v u).length = u.length := by
  simp [clipList]

/-- Clipping the input of the second half: the two lengths and `x` are
unchanged, the script is clipped. -/
theorem clipList_input {v : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ v)
    (hx : x.length + 1 < 2 ^ v) (hxe : ∀ a ∈ x, a ≤ x.length) :
    clipList v (y.length :: (x.length + 1) :: (y ++ x)) =
      y.length :: (x.length + 1) ::
        (y.map (fun a => min (a % 2 ^ v) (y.length + x.length + 2)) ++ x) := by
  simp only [clipList, List.map_cons, List.map_append, List.length_cons, List.length_append]
  have e1 : min (y.length % 2 ^ v) (y.length + x.length + 2) = y.length := by
    rw [Nat.mod_eq_of_lt hy]; omega
  have e2 : min ((x.length + 1) % 2 ^ v) (y.length + x.length + 2) = x.length + 1 := by
    rw [Nat.mod_eq_of_lt hx]; omega
  have e3 : x.map (fun a => min (a % 2 ^ v) (y.length + x.length + 2)) = x := by
    conv_rhs => rw [← List.map_id x]
    apply List.map_congr_left
    intro a ha
    have := hxe a ha
    rw [Nat.mod_eq_of_lt (by omega)]; simp; omega
  rw [show y.length + x.length + 1 + 1 = y.length + x.length + 2 by omega, e1, e2, e3]

/-- The clipped script: entries capped at `y.length + x.length + 2`. -/
def clipY (v L : ℕ) (y : List ℕ) : List ℕ := y.map fun a => min (a % 2 ^ v) L

theorem clipY_length (v L : ℕ) (y : List ℕ) : (clipY v L y).length = y.length := by
  simp [clipY]

theorem clipY_le {v L : ℕ} {y : List ℕ} : ∀ a ∈ clipY v L y, a ≤ L := by
  intro a ha
  simp only [clipY, List.mem_map] at ha
  obtain ⟨b, -, rfl⟩ := ha
  exact min_le_right _ _

/-- Clipping does nothing to a word with small entries. -/
theorem clipY_of_le {v L : ℕ} {y : List ℕ} (h : ∀ a ∈ y, a < 2 ^ v ∧ a ≤ L) : clipY v L y = y := by
  conv_rhs => rw [← List.map_id y]
  apply List.map_congr_left
  intro a ha
  obtain ⟨h1, h2⟩ := h a ha
  rw [Nat.mod_eq_of_lt h1]; simp; omega

/-! ### Instances of thm:mc -/

/-- The instance written by the validation, without the flag. -/
noncomputable def mcIn (n : ℕ) (G : SimpleGraph (Fin n)) (φ : FO 0) (g y : List ℕ) : List ℕ :=
  (vOut n G φ g y).tail

open Classical in
/-- The flag written by the validation. -/
noncomputable def vFlag (n : ℕ) (G : SimpleGraph (Fin n)) (y : List ℕ) : ℕ :=
  if ValidScript n G y then 1 else 0

theorem vOut_eq (n : ℕ) (G : SimpleGraph (Fin n)) (φ : FO 0) (g y : List ℕ) :
    vOut n G φ g y = vFlag n G y :: mcIn n G φ g y := by
  unfold mcIn vOut vFlag; split_ifs <;> rfl

theorem vFlag_le (n : ℕ) (G : SimpleGraph (Fin n)) (y : List ℕ) : vFlag n G y ≤ 1 := by
  unfold vFlag; split_ifs <;> omega

/-- The graph without vertices. -/
def emptyGraph : SimpleGraph (Fin 0) := ⊥

/-- The partial graph without vertices. -/
def emptyPartial : PartialGraph (Fin 0) := unresolved Fin.elim0

theorem dummy_encodes (φ : FO 0) :
    Lax185574.ConstructionModelChecking.EncodesInput (dummyWord ++ toWord φ) 0 emptyGraph
      [emptyPartial] φ := by
  refine ⟨[0, 0, 0], [0, 0], ?_, ?_, rfl⟩
  · exact
      { vertexCount_eq := rfl
        length_eq := rfl
        offset_zero := rfl
        offset_last := rfl
        offset_mono := fun i hi => absurd hi (Nat.not_lt_zero _)
        target_lt := fun j hj => absurd hj (by simp [edgeCount])
        adj_iff := fun u => Fin.elim0 u }
  · exact ⟨⟨Fin.elim0, []⟩, rfl, rfl⟩

theorem dummy_isConstruction : IsConstructionSequence emptyGraph [emptyPartial] := by
  refine ⟨by simp, ⟨rfl, rfl, fun a => Fin.elim0 a⟩, fun t ht => by simp at ht,
    fun u => Fin.elim0 u, ?_, ?_⟩
  · ext u; exact Fin.elim0 u
  · ext u; exact Fin.elim0 u

/-- The output of the validation is an instance of thm:mc on a
construction sequence: the given graph if the flag is `1`, the empty
graph otherwise. -/
theorem mcIn_valid {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G)
    (φ : FO 0) (y : List ℕ) (hv : ValidScript n G y) :
    ∃ s, Lax185574.ConstructionModelChecking.EncodesInput (mcIn n G φ g y) n G s φ ∧
      IsConstructionSequence G s ∧ EncodesSequence y s := by
  obtain ⟨σ, hσ, hcs⟩ := hv
  refine ⟨σ.run, ⟨g, y, hg, ⟨σ, hσ, rfl⟩, ?_⟩, hcs, ⟨σ, hσ, rfl⟩⟩
  unfold mcIn vOut
  rw [if_pos ⟨σ, hσ, hcs⟩]
  rfl

theorem mcIn_invalid {n : ℕ} {G : SimpleGraph (Fin n)} (φ : FO 0) (g y : List ℕ)
    (hv : ¬ ValidScript n G y) : mcIn n G φ g y = dummyWord ++ toWord φ := by
  unfold mcIn vOut
  rw [if_neg hv]
  rfl

theorem mcIn_length_le (n : ℕ) (G : SimpleGraph (Fin n)) (φ : FO 0) (g y : List ℕ) :
    (mcIn n G φ g y).length ≤ g.length + y.length + (toWord φ).length + 5 := by
  unfold mcIn vOut
  split_ifs <;> simp [dummyWord]; omega

theorem mcIn_entries_le {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} (hg : EncodesGraph g n G)
    (φ : FO 0) {y : List ℕ} {L : ℕ} (hy : ∀ a ∈ y, a ≤ L)
    (hL : (g ++ toWord φ).length ≤ L) : ∀ a ∈ mcIn n G φ g y, a ≤ L := by
  intro a ha
  have hx := instance_entries_le hg φ
  unfold mcIn vOut at ha
  split_ifs at ha
  · simp only [List.tail_cons, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact le_trans (hx a (by simp [ha])) hL
    · exact hy a ha
    · exact le_trans (hx a (by simp [ha])) hL
  · simp only [List.tail_cons, List.mem_append, dummyWord] at ha
    rcases ha with ha | ha
    · simp at ha; omega
    · exact le_trans (hx a (by simp [ha])) hL

end Lax185574Proofs.MainRam
