import Lax185574Proofs.CompRam.Callee
import Lax185574Proofs.MC.Asm.Script

/-!
The script of the loop driver for lem:compose and the specification of
the glue program.

The input of the composite is `x = [k, q, l1] ++ X ++ [k, q, l2] ++ Y`,
the word of the pair of trees with root words `X` and `Y`. The machine
starts from `r0`, the call with the frame of the two roots, and runs
along the trajectory `traj G r0`. Round `j` of the glue writes
`sA (j + 1) = outW (j + 1) (traj G r0 j)`, and the callee answers
`sB (j + 1) = ansWord q (ansOf G q)` to the question `q` of that state.

The glue program has two kinds of rounds (`GlueSpec`). In round `0` it
reads `[0, |x|] ++ x ++ [0]` and writes `outW 1 r0`. In round `j ≥ 1` it
reads `glueIn j S o` and writes
`gNext j S o = outW (j + 1) (round S (pick ph o))`,
where `ph` is the phase of the top frame, so that it picks its own part
of the answer of the switch (`round_spec`).

`ROK`: along the trajectory, the rank `(kk, d)` of every frame has
`kk + d ≤ k + q`, and every question asks about a tree whose rank
entries are at most `k + q + 1`, which bounds the constants of the
callees (`traj_rok`).
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim

/-! ### The trajectory one step at a time -/

/-- One step of the machine with the chosen answers. -/
noncomputable def stepR {n : ℕ} (G : PartialGraph (Fin n)) : Res → Res
  | .call S q => round S (ansOf G q)
  | r => r

theorem traj_succ {n : ℕ} (G : PartialGraph (Fin n)) : ∀ (r : Res) (j : ℕ),
    traj G r (j + 1) = stepR G (traj G r j)
  | .call _ _, 0 => rfl
  | .done _, 0 => rfl
  | .err, 0 => rfl
  | .call S q, j + 1 => traj_succ G (round S (ansOf G q)) j
  | .done _, _ + 1 => rfl
  | .err, _ + 1 => rfl

/-! ### The script -/

/-- The word of the pair of trees with root words `X` and `Y`. -/
def xIn (k q l1 l2 : ℕ) (X Y : List ℕ) : List ℕ := [k, q, l1] ++ X ++ [k, q, l2] ++ Y

/-- The first state of the machine. -/
def r0 (k q l1 l2 : ℕ) (X Y : List ℕ) : Res :=
  .call [fresh q k l1 l2 X Y] (.ca (atomsQ (fresh q k l1 l2 X Y)))

/-- The answer of the callee to the question of a state. -/
noncomputable def ansR {n : ℕ} (G : PartialGraph (Fin n)) : Res → List ℕ
  | .call _ q => ansWord q (ansOf G q)
  | _ => []

section script
variable {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (X Y : List ℕ)

/-- The states `a` of the loop driver. -/
noncomputable def sA : ℕ → List ℕ
  | 0 => lpA0 (xIn k q l1 l2 X Y)
  | j + 1 => outW (j + 1) (traj G (r0 k q l1 l2 X Y) j)

/-- The callee outputs `b` of the loop driver. -/
noncomputable def sB : ℕ → List ℕ
  | 0 => []
  | j + 1 => ansR G (traj G (r0 k q l1 l2 X Y) j)

end script

/-- The output of a later round of the glue on the state `S` and the
answer `o` of the switch. -/
noncomputable def gNext (j : ℕ) (S : List Fr) (o : List ℕ) : List ℕ :=
  outW (j + 1) (round S (pick ((S.headD (fresh 0 0 0 0 [] [])).ph) o))

theorem round_spec {n : ℕ} (G : PartialGraph (Fin n)) (j : ℕ) {g : Fr} {S : List Fr} {q : Qry}
    (hf : Fits g.ph q) :
    gNext j (g :: S) (ansR G (.call (g :: S) q)) = outW (j + 1) (stepR G (.call (g :: S) q)) := by
  simp only [gNext, ansR, stepR, List.headD_cons, pick_ansWord hf]

theorem sU_zero (k q l1 l2 : ℕ) (X Y : List ℕ) {n : ℕ} (G : PartialGraph (Fin n)) :
    lpU (xIn k q l1 l2 X Y) (sA G k q l1 l2 X Y 0) (sB G k q l1 l2 X Y 0) =
      [0, (xIn k q l1 l2 X Y).length] ++ xIn k q l1 l2 X Y ++ [0] := lpU_first _

theorem sU_succ (k q l1 l2 : ℕ) (X Y : List ℕ) {n : ℕ} (G : PartialGraph (Fin n)) (j : ℕ)
    {S : List Fr} {q' : Qry} (h : traj G (r0 k q l1 l2 X Y) j = .call S q') :
    lpU (xIn k q l1 l2 X Y) (sA G k q l1 l2 X Y (j + 1)) (sB G k q l1 l2 X Y (j + 1)) =
      glueIn (j + 1) S (ansWord q' (ansOf G q')) := by
  simp only [sA, sB, h, ansR]
  exact lpU_outW _ _ _ _ _

theorem sA_succ_call {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (X Y : List ℕ) (j : ℕ)
    {S : List Fr} {q' : Qry} (h : traj G (r0 k q l1 l2 X Y) j = .call S q') :
    sA G k q l1 l2 X Y (j + 1) = outW (j + 1) (.call S q') ∧
      lpQ (sA G k q l1 l2 X Y (j + 1)) = qWord q' ∧
      (sA G k q l1 l2 X Y (j + 1)).head? ≠ some 0 ∧ sA G k q l1 l2 X Y (j + 1) ≠ [] := by
  have e : sA G k q l1 l2 X Y (j + 1) = outW (j + 1) (.call S q') := by simp only [sA, h]
  rw [e]
  exact ⟨rfl, lpQ_outW _ _ _, by simp [outW], by simp [outW]⟩

theorem sB_succ_call {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (X Y : List ℕ) (j : ℕ)
    {S : List Fr} {q' : Qry} (h : traj G (r0 k q l1 l2 X Y) j = .call S q') :
    sB G k q l1 l2 X Y (j + 1) = ansWord q' (ansOf G q') := by
  simp only [sB, h, ansR]

/-- The output of round `j + 1` is the state after the next step. -/
theorem sA_next {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (X Y : List ℕ) (j : ℕ)
    {g : Fr} {S : List Fr} {q' : Qry} (h : traj G (r0 k q l1 l2 X Y) j = .call (g :: S) q')
    (hf : Fits g.ph q') :
    sA G k q l1 l2 X Y (j + 2) = gNext (j + 1) (g :: S) (ansWord q' (ansOf G q')) := by
  show outW (j + 2) (traj G (r0 k q l1 l2 X Y) (j + 1)) = _
  rw [traj_succ, h]
  have := round_spec G (j + 1) (S := S) hf
  simp only [ansR] at this
  rw [this]

/-! ### Every state of the trajectory fits -/

/-- The top frame of every call fits its question. -/
def TopFits : Res → Prop
  | .call S q => ∃ g S', S = g :: S' ∧ Fits g.ph q
  | _ => True

theorem topFits_round (S : List Fr) (b : List ℕ) : TopFits (round S b) := by
  rcases round_fits S b with h | ⟨z, h⟩ | ⟨g, S', q, h, hf⟩ <;> rw [h]
  · trivial
  · trivial
  · exact ⟨g, S', rfl, hf⟩

theorem traj_topFits {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (X Y : List ℕ) :
    ∀ j, TopFits (traj G (r0 k q l1 l2 X Y) j)
  | 0 => ⟨_, [], rfl, fresh_fits _ _ _ _ _ _⟩
  | j + 1 => by
    rw [traj_succ]
    cases h : traj G (r0 k q l1 l2 X Y) j with
    | call S q' => exact topFits_round _ _
    | done z => trivial
    | err => trivial

/-! ### Ranks along the trajectory -/

/-- The rank invariant of a stack. -/
def RInv (N : ℕ) (S : List Fr) : Prop :=
  (∀ f ∈ S, f.kk + f.d ≤ N ∧ (f.ph ≠ 0 → 1 ≤ f.d)) ∧ ∀ f ∈ S.tail, f.ph ≠ 0

/-- The rank invariant of a state. -/
def ROK (N : ℕ) : Res → Prop
  | .call S q => RInv N S ∧ RankLe (N + 1) q
  | _ => True

theorem child_rank (f : Fr) : (child f).kk = f.kk + 1 ∧ (child f).d = f.d - 1 ∧ (child f).ph = 0 := by
  unfold child; split <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_rok {N : ℕ} {f : Fr} {S : List Fr} (hf : f.kk + f.d ≤ N) (hd : 1 ≤ f.d)
    (hS : ∀ g ∈ S, g.kk + g.d ≤ N ∧ (g.ph ≠ 0 → 1 ≤ g.d)) (hS' : ∀ g ∈ S, g.ph ≠ 0) :
    ROK N (advance f S) := by
  obtain ⟨c1, c2, c3⟩ := child_rank f
  unfold advance
  split
  · refine ⟨⟨?_, ?_⟩, trivial⟩
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · rw [c1, c2, c3]; exact ⟨by omega, fun h => absurd rfl h⟩
      · exact ⟨hf, fun _ => hd⟩
      · exact hS g hg
    · intro g hg
      simp only [List.tail_cons, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp
      · exact hS' g hg
  · refine ⟨⟨?_, ?_⟩, trivial⟩
    · intro g hg
      simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨hf, fun _ => hd⟩
      · exact hS g hg
    · intro g hg
      exact hS' g hg

theorem ret_rok {N : ℕ} {R h : List ℕ} {S : List Fr}
    (hS : ∀ g ∈ S, g.kk + g.d ≤ N ∧ (g.ph ≠ 0 → 1 ≤ g.d)) (hS' : ∀ g ∈ S, g.ph ≠ 0) :
    ROK N (ret R h S) := by
  cases S with
  | nil => trivial
  | cons p S =>
    have hp := hS p (by simp)
    have hp' := hS' p (by simp)
    have hd := hp.2 hp'
    have hT : ∀ g ∈ S, g.kk + g.d ≤ N ∧ (g.ph ≠ 0 → 1 ≤ g.d) := fun g hg => hS g (by simp [hg])
    have hT' : ∀ g ∈ S, g.ph ≠ 0 := fun g hg => hS' g (by simp [hg])
    by_cases hi : p.i < nA p
    · rw [ret_lt _ _ _ _ hi]
      refine ⟨⟨?_, fun g hg => hT' g hg⟩, ?_⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨hp.1, fun _ => hd⟩
        · exact hT g hg
      · simp only [RankLe, reQuery]
        simp
        omega
    · rw [ret_ge _ _ _ _ hi]
      exact advance_rok hp.1 hd hT hT'

theorem round_rok {N : ℕ} {S : List Fr} (hS : RInv N S) (b : List ℕ) : ROK N (round S b) := by
  cases S with
  | nil => trivial
  | cons f S =>
    obtain ⟨hA, hB⟩ := hS
    have hf := hA f (by simp)
    have hT : ∀ g ∈ S, g.kk + g.d ≤ N ∧ (g.ph ≠ 0 → 1 ≤ g.d) := fun g hg => hA g (by simp [hg])
    have hT' : ∀ g ∈ S, g.ph ≠ 0 := fun g hg => hB g (by simpa using hg)
    by_cases h0 : f.ph = 0
    · by_cases hd : f.d = 0
      · rw [round_ph0_zero f S b h0 hd]; exact ret_rok hT hT'
      · rw [round_ph0_succ f S b h0 hd]
        refine ⟨⟨?_, fun g hg => hT' g hg⟩, ?_⟩
        · intro g hg
          simp only [List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact ⟨hf.1, fun _ => Nat.one_le_iff_ne_zero.2 hd⟩
          · exact hT g hg
        · simp only [RankLe]; simp; omega
    have hd := hf.2 h0
    by_cases h1 : f.ph = 1
    · rw [round_ph1 f S b h1]
      refine ⟨⟨?_, fun g hg => hT' g hg⟩, ?_⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨hf.1, fun _ => hd⟩
        · exact hT g hg
      · simp only [RankLe]; simp; omega
    by_cases h2 : f.ph = 2
    · rw [round_ph2 f S b h2]; exact advance_rok hf.1 hd hT hT'
    by_cases h4 : f.ph = 4
    · rw [round_ph4 f S b h4]; exact advance_rok hf.1 hd hT hT'
    by_cases h5 : f.ph = 5
    · rw [round_ph5 f S b h5]; exact ret_rok hT hT'
    simp [round, h0, h1, h2, h4, h5, ROK]

/-- **Ranks along the trajectory.** -/
theorem traj_rok {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (X Y : List ℕ) :
    ∀ j, ROK (k + q) (traj G (r0 k q l1 l2 X Y) j)
  | 0 => ⟨⟨fun f hf => by simp only [List.mem_singleton] at hf; subst hf; simp [fresh],
      fun f hf => by simp at hf⟩, trivial⟩
  | j + 1 => by
    rw [traj_succ]
    have ih := traj_rok G k q l1 l2 X Y j
    cases h : traj G (r0 k q l1 l2 X Y) j with
    | call S q' => rw [h] at ih; exact round_rok ih.1 _
    | done z => trivial
    | err => trivial

/-! ### The script of a far composition -/

open Lax185574.GaifmanGraph in
open Lax3.DistFO (rhoMinus) in
/-- **The script of a far composition.** For far tuples the trajectory
from `r0` ends after `m` calls with the word of `tree_{k,q}(u₁ u₂)`, and
before that every state is a call whose top frame fits the question,
which has an answer of rank at most `k + q + 1`. -/
theorem script_facts {n : ℕ} (G : PartialGraph (Fin n)) (k q l1 l2 : ℕ) (u₁ : Fin l1 → Fin n)
    (u₂ : Fin l2 → Fin n) (h1 : 1 ≤ l1) (h2 : 1 ≤ l2) (hk : l1 + l2 ≤ k)
    (hfar : ∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) :
    xIn k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) =
      toWord (tree G k q u₁, tree G k q u₂) ∧
    ∃ m, m + 1 ≤ 5 * (Node.count (node G k q u₁) + Node.count (node G k q u₂)) ^ (q + 1) ∧
      traj G (r0 k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))) m =
        .done (toWord (tree G k q (Fin.append u₁ u₂))) ∧
      ∀ j < m, ∃ g S q', traj G (r0 k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂))) j =
        .call (g :: S) q' ∧ Fits g.ph q' ∧ Ans G q' (ansOf G q') ∧ RankLe (k + q + 1) q' := by
  refine ⟨by simp [xIn]; rfl, ?_⟩
  obtain ⟨m, hm, hL⟩ := root_leads G k q l1 l2 u₁ u₂ h1 h2 hk hfar
  obtain ⟨hend, hcall⟩ := leads_traj G hL
  refine ⟨m, hm, hend, fun j hj => ?_⟩
  obtain ⟨S, q', hS, hA⟩ := hcall j hj
  have hT := traj_topFits G k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) j
  have hR := traj_rok G k q l1 l2 (toWord (node G k q u₁)) (toWord (node G k q u₂)) j
  simp only [r0] at hS hT hR ⊢
  rw [hS] at hT hR
  obtain ⟨g, S', rfl, hf⟩ := hT
  exact ⟨g, S', q', hS, hf, hA, hR.2⟩

end Lax185574Proofs.CompRam
