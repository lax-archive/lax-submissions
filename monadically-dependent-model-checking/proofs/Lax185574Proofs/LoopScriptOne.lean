import Lax185574Proofs.LoopScript

/-!
Scripts of the loop driver with one call.

The glue program writes `o` in its first round, the callee answers `z`
on the query of `o`, and the glue program writes `0 :: z` in its second
round. These are `loop_script_sound` and `loop_script_run` for this
script, stated without the functions of the script.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram Lax185574Proofs.RamSim

/-- The states of the script with one call. -/
def oneA (x o : List ℕ) : ℕ → List ℕ := fun j => if j = 0 then lpA0 x else o

/-- The answers of the script with one call. -/
def oneB (z : List ℕ) : ℕ → List ℕ := fun j => if j = 0 then [] else z

/-- **Soundness of a script with one call.** -/
theorem one_call_sound {G P p : Program}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)
    {w : ℕ} {x o z : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1))
    (hU0 : ∀ o' t, RunsTo (lpV w 0) G (lpU x (lpA0 x) []) o' t → o' = o)
    (hh : o.head? ≠ some 0)
    (hP : ∀ r t, RunsTo (lpV w 1) P (lpQ o) r t → r = z)
    (hU1 : ∀ o' t, RunsTo (lpV w 2) G (lpU x o z) o' t → o' = 0 :: z) :
    ∀ y t, RunsTo w p x y t → y = z :=
  loop_script_sound hp hw hx (A := oneA x o) (B := oneB z) (R := 1) rfl rfl
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact ⟨hU0, hh, hP⟩) hU1

/-- **Running a script with one call.** -/
theorem one_call_run {G P p : Program} {K : ℕ}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z T, LoopTrace w G P x 0 (lpA0 x) [] z T → ∃ t ≤ K * (T + z.length + 1), RunsTo w p x z t)
    {w : ℕ} {x o z : List ℕ} {t0 tP t1 : ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1))
    (hs0 : lpSize w 0 ≠ 0) (hr0 : RunsTo (lpV w 0) G (lpU x (lpA0 x) []) o t0)
    (hU0 : ∀ o' t, RunsTo (lpV w 0) G (lpU x (lpA0 x) []) o' t → o' = o)
    (hne : o ≠ []) (hh : o.head? ≠ some 0) (hcap0 : o.length ≤ lpCap w)
    (hs1 : lpSize w 1 ≠ 0) (hr1 : RunsTo (lpV w 1) P (lpQ o) z tP)
    (hP : ∀ r t, RunsTo (lpV w 1) P (lpQ o) r t → r = z) (hcapz : z.length ≤ lpCap w)
    (hs2 : lpSize w 2 ≠ 0) (hr2 : RunsTo (lpV w 2) G (lpU x o z) (0 :: z) t1)
    (hU1 : ∀ o' t, RunsTo (lpV w 2) G (lpU x o z) o' t → o' = 0 :: z)
    (hcap2 : (0 :: z).length ≤ lpCap w) :
    ∃ t ≤ K * (t0 + tP + 2 + (t1 + 1) + z.length + 1), RunsTo w p x z t := by
  have h := loop_script_run hp hw hx (A := oneA x o) (B := oneB z)
    (tG := fun j => if j = 0 then t0 else t1) (tP := fun _ => tP) (R := 1) rfl rfl
    (fun j hj => by
      obtain rfl : j = 0 := by omega
      exact ⟨hs0, hr0, hU0, hne, hh, hcap0, hs1, hr1, hP, hcapz⟩)
    ⟨hs2, hr2, hU1, hcap2⟩
  have hst : scriptTime (fun j => if j = 0 then t0 else t1) (fun _ => tP) 1 0 =
      t0 + tP + 2 + (t1 + 1) := by
    simp [scriptTime]
  rwa [hst] at h

end Lax185574Proofs.Simulate
