import Lax185574Proofs.ResolveRam.Glue.ClauseJ
import Lax185574Proofs.ResolveRam.SizeGlue.State

/-!
The size of the library of a round.

A round with a call builds a library `L` from the state `ws` at the
position of its answer `b`. Its output `o` holds the next state and the
next query. If the words that the round adds are at most as large as
the state, the answer and the output together, and their entries are
entries of these, then the size `sBig` of the room check is at most a
constant times the sizes of the input and the output of the round
(`sBig_le`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

/-- The library of a round is small relative to the state `ws`, the answer
`b` and the output `o`. -/
structure LibSm (L ws : List (List ℕ)) (b o : List ℕ) : Prop where
  len : total L + L.length ≤ 3 * (total ws + ws.length) + 3 * b.length + 3 * o.length + 10
  ent : ∀ w ∈ L, ∀ e ∈ w, e ≤ maxEntry (toWord ws) + maxEntry b + maxEntry o

theorem length_toWord_ws' (ws : List (List ℕ)) : (toWord ws).length = total ws + ws.length + 1 := by
  rw [length_toWord_ws]
  induction ws with
  | nil => simp [tot, total]
  | cons w ws ih =>
    rw [tot_cons, total_cons, List.length_cons]
    have : (toWord ws).length = 1 + tot ws := length_toWord_ws ws
    omega

theorem mem_toWord_lsz {ws : List (List ℕ)} {w : List ℕ} {e : ℕ} (hw : w ∈ ws) (he : e ∈ w) :
    e ∈ toWord ws := by
  change e ∈ ws.length :: (ws.map toWord).flatten
  refine List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨toWord w, List.mem_map_of_mem hw, ?_⟩)
  rw [toWord_listNat]; exact List.mem_cons_of_mem _ he

theorem ent_toWord {ws : List (List ℕ)} {w : List ℕ} {e : ℕ} (hw : w ∈ ws) (he : e ∈ w) :
    e ≤ maxEntry (toWord ws) := le_maxEntry (mem_toWord_lsz hw he)

theorem maxEntry_mono {a b : List ℕ} (h : ∀ v ∈ a, v ∈ b) : maxEntry a ≤ maxEntry b :=
  maxEntry_le fun v hv => le_maxEntry (h v hv)

theorem maxEntry_flatten_le {L : List (List ℕ)} {B : ℕ} (h : ∀ w ∈ L, ∀ e ∈ w, e ≤ B) :
    maxEntry L.flatten ≤ B :=
  maxEntry_le fun v hv => by
    obtain ⟨w, hw, hv⟩ := List.mem_flatten.1 hv
    exact h w hw v hv

/-- A library that extends the state by words that are small. -/
theorem libSm_of {L ws N : List (List ℕ)} {b o : List ℕ} (hL : L = ws ++ N)
    (hlen : total N + N.length ≤ 2 * (total ws + ws.length) + 2 * b.length + 3 * o.length + 10)
    (hent : ∀ w ∈ N, ∀ e ∈ w, e ≤ maxEntry (toWord ws) + maxEntry b + maxEntry o) :
    LibSm L ws b o := by
  subst hL
  refine ⟨?_, fun w hw e he => ?_⟩
  · rw [total_append, List.length_append]; omega
  · rcases List.mem_append.1 hw with h | h
    · have := ent_toWord h he; omega
    · exact hent w h e he

/-- **The size of the room check of a round.** -/
theorem sBig_le {L ws : List (List ℕ)} {b o x sc : List ℕ} {t k : ℕ} (hL : LibSm L ws b o) :
    sBig L b x.length (maxEntry (x.take k)) ≤
      100 * (ySz ([t, (sc ++ toWord ws).length] ++ x.take k ++ (sc ++ toWord ws) ++ (b.length :: b)) +
        ySz o + ySz x) := by
  set u := [t, (sc ++ toWord ws).length] ++ x.take k ++ (sc ++ toWord ws) ++ (b.length :: b)
  have hu1 : (toWord ws).length + b.length ≤ u.length := by
    simp only [u, List.length_append, List.length_cons]; omega
  have hm1 : maxEntry (toWord ws) ≤ maxEntry u :=
    maxEntry_mono fun v hv => by simp only [u, List.mem_append, List.mem_cons]; tauto
  have hm2 : maxEntry b ≤ maxEntry u :=
    maxEntry_mono fun v hv => by simp only [u, List.mem_append, List.mem_cons]; tauto
  have hm3 : maxEntry (x.take k) ≤ maxEntry x := maxEntry_mono fun v hv => List.mem_of_mem_take hv
  have hmL := maxEntry_flatten_le hL.ent
  have hlen := hL.len
  have htw := length_toWord_ws' ws
  unfold sBig sOf
  unfold ySz
  have : max (max (maxEntry (x.take k)) (maxEntry L.flatten)) (maxEntry b) ≤
      maxEntry x + maxEntry (toWord ws) + maxEntry b + maxEntry o + maxEntry b := by omega
  omega

/-! ### The output of a round -/

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem hdOf_ws (c : Cur) {w : List ℕ} {e : ℕ} (hw : w ∈ (swAt G P Q s k₀ q₀ c).ws) (he : e ∈ w) :
    e ∈ hdOf G P Q s k₀ q₀ c := by
  have := mem_toWord_lsz hw he
  simp only [hdOf, stOf, List.mem_cons, List.mem_append]; tauto

theorem hdOf_len (c : Cur) :
    total (swAt G P Q s k₀ q₀ c).ws + (swAt G P Q s k₀ q₀ c).ws.length + 1 ≤ (hdOf G P Q s k₀ q₀ c).length := by
  have := length_toWord_ws' (swAt G P Q s k₀ q₀ c).ws
  simp only [hdOf, stOf, List.length_cons, List.length_append]; omega

/-- The words of the next state are part of the output. -/
theorem out_ws {c : Cur} {o : List ℕ} (ho : ∃ r, o = hdOf G P Q s k₀ q₀ c ++ r) :
    (total (swAt G P Q s k₀ q₀ c).ws + (swAt G P Q s k₀ q₀ c).ws.length + 1 ≤ o.length) ∧
    ∀ w ∈ (swAt G P Q s k₀ q₀ c).ws, ∀ e ∈ w, e ≤ maxEntry o := by
  obtain ⟨r, rfl⟩ := ho
  refine ⟨by have := hdOf_len G P Q s k₀ q₀ c; simp only [List.length_append]; omega, fun w hw e he => ?_⟩
  exact le_maxEntry (List.mem_append_left _ (hdOf_ws G P Q s k₀ q₀ c hw he))

/-- The real query of the next call is part of the output. -/
theorem out_q {c : RCall} {o : List ℕ} (hc : c ≠ .stp) (ho : ∃ h, o = h ++ rQ G k₀ q₀ c) :
    (realQ G k₀ q₀ c).length ≤ o.length ∧ ∀ e ∈ realQ G k₀ q₀ c, e ≤ maxEntry o := by
  obtain ⟨h, rfl⟩ := ho
  obtain ⟨pre, post, hsp', -, -⟩ := kW_split (kindOf c) (realQ G k₀ q₀ c) (kindOf_le hc)
  rw [rQ_kind G k₀ q₀ _ hc, hsp']
  refine ⟨by simp only [List.length_append]; omega, fun e he => le_maxEntry ?_⟩
  simp [he]

/-- The real answer is a part of the answer of the switch. -/
theorem realY_sub (c : RCall) : ∀ e ∈ realY G k₀ q₀ c, e ∈ rY G k₀ q₀ c := by
  intro e he
  cases c <;> simp_all [rY, yA, yB, yC, yE, yF, realY]

theorem realY_len_le (c : RCall) : (realY G k₀ q₀ c).length ≤ (rY G k₀ q₀ c).length := by
  cases c <;> simp only [rY, yA, yB, yC, yE, yF, realY, List.length_append] <;> omega

end Lax185574Proofs.ResolveRam.Glue
