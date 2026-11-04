import Lax185574Proofs.ResolveRam.Glue.CaseKit
import Lax185574Proofs.ResolveRam.Glue.CaseFin

/-!
The new lengths of the levels after an item on the way down.

The word `LL` is word `3` of the library. `llC` writes into the buffer
the first `d + 1` entries of `LL`, the entry `tN + ne` (the old length
of level `d + 1` plus the number of new expansion words) and `tz`
zeros, and appends this word `llNew LL d ne tz` to the library, at the
index `iL` (`llC_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- Build the new lengths in the buffer and append them to the library. -/
def llC : Com :=
  .seq (asgs [("po", .lit 0), ("lS", .get "st" (.lit 3)), ("lD", .add (.var "dd") (.lit 1))])
  (.seq (cpSeg "a" "lS" "lD")
  (.seq (push1 "OB" "po" (.add (.var "lvN") (.var "ne")))
  (.seq (forUp "ci" (.var "lvZ") (push1 "OB" "po" (.lit 0)))
  (.seq (asgs [("ls", .lit 0), ("lL", .var "po"), ("iL", .var "m")]) (lbApp "OB")))))

/-- The scalars that `llC` may write. -/
def llCV : List String := ["po", "lS", "lD", "ci", "ls", "lL", "iL", "lt", "m"]

theorem seg_take {L : List (List ℕ)} {τ : Env} (hw : WordsAt L τ) {i : ℕ} (hi : i < L.length) {N : ℕ}
    (hN : N ≤ L[i].length) : seg (τ.arrs "a") (off L i) N = L[i].take N := by
  apply List.ext_getElem?
  intro j
  simp only [seg, List.getElem?_take, List.getElem?_drop]
  split_ifs with h
  · exact (hw.a i hi j (by omega)).trans (List.getElem?_eq_getElem (by omega)).symm
  · rfl

set_option maxHeartbeats 800000 in
/-- **The new lengths.** -/
theorem llC_run {W d e z : ℕ} {L : List (List ℕ)} {τ : Env}
    (hW : τ.vars "W" = W) (har : ArrW W τ) (hlt : EnvLt (W + 1) τ) (hL : Lib L τ) (h3 : 3 < L.length)
    (hdd : τ.vars "dd" = d) (hd : d + 1 < L[3].length) (htN : τ.vars "lvN" = L[3][d + 1])
    (hne : τ.vars "ne" = e) (htz : τ.vars "lvZ" = z) (hv : L[3][d + 1] + e ≤ W)
    (hroom : 2 * total L + L.length + d + z + 8 ≤ W) :
    ∃ τ', Run (W + 1) llC τ τ' (40 * (d + z) + 300) ∧ Lib (L ++ [llNew L[3] d e z]) τ' ∧
      τ'.vars "iL" = L.length ∧
      (∀ y, y ∉ llCV → τ'.vars y = τ.vars y) ∧ (∀ b, b ∉ ["a", "st", "ln", "OB"] → τ'.arrs b = τ.arrs b) ∧
      ArrW W τ' ∧ EnvLt (W + 1) τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hLv := lib_lt hL.at_ hlt
  have hoff := off_add_le h3
  have hst := hL.at_.st 3 h3
  have hoffW : off L 3 < W + 1 := hlt.arrs "st" _ (List.mem_of_getElem? hst)
  -- step 1
  let f1 : String → ℕ := fun y => if y = "lS" then off L 3 else if y = "lD" then d + 1 else 0
  obtain ⟨τ1, r1, s1, g1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ)
    (l := [("po", .lit 0), ("lS", .get "st" (.lit 3)), ("lD", .add (.var "dd") (.lit 1))]) (f := f1)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact evalB_lit (by omega)
      · exact evalB_get (evalB_lit (by omega)) hst hoffW
      · exact ev_add (ev_var hdd (by omega)) (evalB_lit (by omega)) (by omega))
    (by decide)
  have F1 : Filled "OB" "po" [] τ1 := ⟨by rw [s1 "po" (by simp)]; simp [f1], fun i h => absurd h (by simp)⟩
  have hOB : (τ1.arrs "OB").length = W + 1 := by rw [a1]; exact har "OB"
  -- step 2: the first entries
  have hseg := seg_take (τ := τ1) (hL.at_.of_arrs (by rw [a1]) (by rw [a1]) (by rw [a1])) h3
    (N := d + 1) (by omega)
  obtain ⟨τ2, r2, F2⟩ := cpSeg_run (B := W + 1) (src := "a") (s := "lS") (l := "lD") (σ := τ1) (pre := [])
    (a := off L 3) (N := d + 1) (by decide) (s1 "lS" (by simp)) (s1 "lD" (by simp)) (by decide) (by decide)
    (by decide) (by decide) F1 (by rw [a1, har "a"]; omega) (by rw [hOB]; simp; omega) (by omega)
    (by simp; omega)
    (by
      intro v hv
      rw [hseg] at hv
      have := hLv _ (List.getElem_mem h3) v (List.mem_of_mem_take hv); omega)
  rw [hseg, List.nil_append] at F2
  have hv2 : ∀ y, y ∉ ["ci", "po"] → τ2.vars y = τ1.vars y := fun y hy =>
    r2.frame_var_sub y (by decide) hy
  have ha2 : ∀ b, b ≠ "OB" → τ2.arrs b = τ1.arrs b := fun b hb =>
    r2.frame_arr b (fun h => hb (by
      have := (show (cpSeg "a" "lS" "lD").warrs ⊆ ["OB"] by decide) h; simpa using this))
  have hl2 : EnvLt (W + 1) τ2 := Run.envLt (Run.seq r1 r2) hlt
  -- step 3: the new entry
  have e3 : (Expr.add (.var "lvN") (.var "ne")).evalB (W + 1) τ2 = some (L[3][d + 1] + e) := by
    refine ev_add (ev_var (by rw [hv2 "lvN" (by decide), g1 "lvN" (by decide), htN]) (by omega))
      (ev_var (by rw [hv2 "ne" (by decide), g1 "ne" (by decide), hne]) (by omega)) (by omega)
  obtain ⟨τ3, r3, F3, v3, a3, l3, o3, i3⟩ := push1_run F2 e3 (by rw [Run.length_arrs r2, hOB]; simp; omega)
    (by simp; omega)
  -- step 4: the zeros
  let P4 : Env → Prop := fun ρ => ρ.vars "lvZ" = z ∧ (ρ.arrs "OB").length = W + 1 ∧
    (∀ y, y ≠ "po" → y ≠ "ci" → ρ.vars y = τ3.vars y) ∧ (∀ b, b ≠ "OB" → ρ.arrs b = τ3.arrs b)
  have hz3 : τ3.vars "lvZ" = z := by rw [v3 "lvZ" (by decide), hv2 "lvZ" (by decide), g1 "lvZ" (by decide), htz]
  obtain ⟨τ4, r4, P4', -, F4⟩ := forUp_push1 (B := W + 1) (N := z) (cap := W + 1) (i := "ci") (a := "OB")
    (pv := "po") (e := .lit 0) (bnd := .var "lvZ") (by decide) (fun _ => 0) P4
    (fun ρ v h => ⟨by simp [h.1], by simp [h.2.1], fun y h1 h2 => by simp [h2, h.2.2.1 y h1 h2],
      fun b hb => by simp [h.2.2.2 b hb]⟩)
    (fun ρ ρ' h hv ha hl => ⟨by rw [hv "lvZ" (by decide), h.1], by rw [hl, h.2.1],
      fun y h1 h2 => by rw [hv y h1, h.2.2.1 y h1 h2], fun b hb => by rw [ha b hb, h.2.2.2 b hb]⟩)
    (fun ρ h => h.2.1) (by omega)
    ⟨hz3, by rw [l3, Run.length_arrs r2, hOB], fun _ _ _ => rfl, fun _ _ => rfl⟩ F3
    (fun ρ h => ev_var h.1 (by omega)) (fun k _ ρ _ _ => evalB_lit (by omega)) (by simp; omega) (by simp; omega)
  obtain ⟨-, -, v4, a4⟩ := P4'
  have hzs : ∀ z' : ℕ, ((List.range z').flatMap fun _ => [(0 : ℕ)]) = List.replicate z' 0 := by
    intro z'
    induction z' with
    | zero => rfl
    | succ z' ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; rfl
  rw [hzs z] at F4
  set w := L[3].take (d + 1) ++ [L[3][d + 1] + e] ++ List.replicate z 0 with hw
  have hwl : w.length = d + 2 + z := by simp [w]; omega
  have hwe : w = llNew L[3] d e z := by
    simp only [w, llNew, List.getD_eq_getElem _ _ hd]
  have F4' : Filled "OB" "po" w τ4 := by simpa [w, List.append_assoc] using F4
  have hl4 : EnvLt (W + 1) τ4 := Run.envLt (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))) hlt
  -- step 5
  have hm4 : τ4.vars "m" = L.length := by
    rw [v4 "m" (by decide) (by decide), v3 "m" (by decide), hv2 "m" (by decide), g1 "m" (by decide), hL.m]
  obtain ⟨τ5, r5, s5, g5, a5, o5, i5⟩ := asgs_run (B := W + 1) (τ := τ4)
    (l := [("ls", .lit 0), ("lL", .var "po"), ("iL", .var "m")])
    (f := fun y => if y = "ls" then 0 else if y = "lL" then w.length else L.length)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simp
      · simp only [show ("lL" : String) ≠ "ls" by decide, if_false, if_true]
        exact ev_var F4'.pos (by omega)
      · simp only [show ("iL" : String) ≠ "ls" by decide, show ("iL" : String) ≠ "lL" by decide, if_false]
        exact ev_var hm4 (by omega))
    (by decide)
  have hL5 : Lib L τ5 := hL.of (by rw [g5 "m" (by decide), hm4, hL.m])
    (by rw [g5 "lt" (by decide), v4 "lt" (by decide) (by decide), v3 "lt" (by decide), hv2 "lt" (by decide),
      g1 "lt" (by decide)])
    (by rw [a5, a4 "a" (by decide), a3 "a" (by decide), ha2 "a" (by decide), a1])
    (by rw [a5, a4 "st" (by decide), a3 "st" (by decide), ha2 "st" (by decide), a1])
    (by rw [a5, a4 "ln" (by decide), a3 "ln" (by decide), ha2 "ln" (by decide), a1])
  have hseg5 : SegAt "OB" 0 w τ5 := fun j hj => by rw [a5, Nat.zero_add]; exact F4'.get j hj
  have hwv : ∀ v ∈ w, v ≤ W := by
    intro v hv
    simp only [w, List.mem_append, List.mem_singleton, List.mem_replicate] at hv
    rcases hv with (hv | hv) | hv
    · have := hLv _ (List.getElem_mem h3) v (List.mem_of_mem_take hv); omega
    · omega
    · omega
  have hAr : ∀ b, (τ5.arrs b).length = W + 1 := fun b => by
    rw [Run.length_arrs (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))) b]; exact har b
  obtain ⟨τ6, r6, L6, f6, a6, l6, o6, i6⟩ := lbApp_run (W := W) (src := "OB") (s := 0) hL5
    (by rw [s5 "ls" (by simp)]; simp) (by rw [s5 "lL" (by simp)]; simp) hseg5 (by decide) (by simp)
    (by rw [hAr]; omega) (by rw [hAr]; omega) (by rw [hAr]; omega) (by omega) (by omega) hwv
  rw [hwe] at L6
  have hrun : Run (W + 1) llC τ τ6 (40 * (d + z) + 300) := by
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    simp only [asgK, Expr.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  refine ⟨τ6, hrun, L6, ?_, fun y hy => ?_, fun b hb => ?_, fun b => by rw [l6]; exact hAr b,
    Run.envLt hrun hlt, hrun.out_eq (by decide), hrun.frame_inp (by decide)⟩
  · rw [f6 "iL" (by decide), s5 "iL" (by simp)]; simp
  · simp only [llCV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f6 y (by simp; tauto), g5 y (by simp; tauto), v4 y (by tauto) (by tauto), v3 y (by tauto),
      hv2 y (by simp; tauto), g1 y (by simp; tauto)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [a6 b (by simp; tauto), a5, a4 b hb.2.2.2, a3 b hb.2.2.2, ha2 b hb.2.2.2, a1]

end Lax185574Proofs.ResolveRam.Glue
