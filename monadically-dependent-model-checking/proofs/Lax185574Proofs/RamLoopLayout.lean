import Lax185574Proofs.RamLoopPhase
import Lax185574Proofs.RamOut

/-!
The layout of the loop driver.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

section layout

variable (G P : Program)

theorem lpBG_length :
    (blocks (lpCodeG G P) lpHG (blockLen lpKsG) G).length = blockLen lpKsG * G.length :=
  blocks_length (lpCodeG G P) _ _ _ le_rfl

theorem lpBP_length :
    (blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P).length = blockLen lpKsP * P.length :=
  blocks_length (lpCodeP G P) _ _ _ le_rfl

def lpPreG : Program := lpInit ++ (lpAllocCode (lpDie G P) lpLoop ++ lpPrelude 44 ++ lpRwG)

def lpPreP : Program :=
  lpPreG G P ++ blocks (lpCodeG G P) lpHG (blockLen lpKsG) G ++
    (lpExitGCode G P ++ lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G)

def lpPost : Program := lpSwap ++ lpOutCode G P ++ [.jump (lpDie G P)]

theorem lpPreG_length : (lpPreG G P).length = lpHG := by
  simp [lpPreG, lpInit, lpAllocCode, lpPrelude, lpHG, lpLoop]; omega

theorem lpPreP_length : (lpPreP G P).length = lpHP G := by
  simp only [lpPreP, List.length_append, lpPreG_length, lpBG_length]
  simp [lpExitGCode, lpAllocCode, lpPrelude, lpHP, lpStartP, lpExitG]; omega

theorem lpProg_G : lpProg G P = lpPreG G P ++ blocks (lpCodeG G P) lpHG (blockLen lpKsG) G ++
    ((lpExitGCode G P ++ lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G) ++
      blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P ++ lpPost G P) := by
  simp only [lpProg, lpPreG, lpPost, List.append_assoc]

theorem lpProg_P : lpProg G P = lpPreP G P ++ blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P ++
    lpPost G P := by
  simp only [lpProg, lpPreP, lpPreG, lpPost, List.append_assoc]

theorem lp_fits_init : Fits (lpProg G P) 0 lpInit := by
  rw [lpProg, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  exact fits_self _ _

theorem lp_fits_phG :
    Fits (lpProg G P) lpLoop (lpAllocCode (lpDie G P) lpLoop ++ lpPrelude 44 ++ lpRwG) := by
  have := fits_mid lpInit (lpAllocCode (lpDie G P) lpLoop ++ lpPrelude 44 ++ lpRwG)
    (blocks (lpCodeG G P) lpHG (blockLen lpKsG) G ++
      ((lpExitGCode G P ++ lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G) ++
        blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P ++ lpPost G P))
  rw [lpProg_G, lpPreG]
  simp only [List.append_assoc] at this ⊢
  exact this

theorem lp_fits_exitPart : Fits (lpProg G P) (lpExitG G)
    (lpExitGCode G P ++ lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G) := by
  have := fits_mid (lpPreG G P ++ blocks (lpCodeG G P) lpHG (blockLen lpKsG) G)
    (lpExitGCode G P ++ lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G)
    (blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P ++ lpPost G P)
  rw [lpProg_G]
  simp only [List.length_append, lpPreG_length, lpBG_length, List.append_assoc] at this ⊢
  exact this

theorem lp_fits_exitG : Fits (lpProg G P) (lpExitG G) (lpExitGCode G P) := by
  have := lp_fits_exitPart G P
  rw [List.append_assoc, List.append_assoc, fits_append] at this
  exact this.1

theorem lp_fits_phP : Fits (lpProg G P) (lpStartP G)
    (lpAllocCode (lpDie G P) (lpStartP G) ++ lpPrelude 46 ++ lpRwP G) := by
  have := lp_fits_exitPart G P
  rw [List.append_assoc, List.append_assoc, fits_append] at this
  have h := this.2
  simp only [lpExitGCode, List.length_cons, List.length_nil] at h
  rw [← List.append_assoc] at h
  exact h

theorem lp_fits_post : Fits (lpProg G P) (lpExitP G P) (lpPost G P) := by
  have := fits_self (lpPreP G P ++ blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P)
  have h := fits_mid (lpPreP G P ++ blocks (lpCodeP G P) (lpHP G) (blockLen lpKsP) P)
    (lpPost G P) []
  rw [List.append_nil] at h
  rw [lpProg_P]
  simp only [List.length_append, lpPreP_length, lpBP_length] at h
  exact h

theorem lp_fits_swap : Fits (lpProg G P) (lpExitP G P) lpSwap := by
  have := lp_fits_post G P
  rw [lpPost, List.append_assoc, fits_append] at this
  exact this.1

theorem lp_fits_out : Fits (lpProg G P) (lpOut G P) (lpOutCode G P) := by
  have := lp_fits_post G P
  rw [lpPost, List.append_assoc, fits_append, fits_append] at this
  exact this.2.1.congr (by simp [lpSwap, lpOut])

theorem lp_die_instr : (lpProg G P)[lpDie G P]? = some (.jump (lpDie G P)) := by
  have := lp_fits_post G P
  rw [lpPost, List.append_assoc, fits_append, fits_append] at this
  have h := this.2.2.head
  simpa [lpSwap, lpOutCode, lpDie, lpOut] using h

end layout

end Lax185574Proofs.RamSim
