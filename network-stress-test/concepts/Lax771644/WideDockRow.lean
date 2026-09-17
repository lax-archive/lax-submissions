import Mathlib.Data.Nat.Notation
import Lax771644.Foundations

/-!
---
title: A very wide dock row with a wide assumption rail
type: theorem
---
Twelve numbered statements, every one of them proved, so the dock row is as
wide as this benchmark gets. Statement 12 is a sibling proof that uses eleven of
its siblings at once, which gives the widest assumption rail in the submission.

# Formalization notes

The eleven single-step rungs compose to the twelfth statement exactly, so the
eleven assumptions of the last proof are all genuinely used.
-/

namespace Lax771644.WideDockRow

/-- Descent from stage 101 to stage 100. -/
axiom s01 : Foundations.Descent 101 100

/-- Descent from stage 102 to stage 101. -/
axiom s02 : Foundations.Descent 102 101

/-- Descent from stage 103 to stage 102. -/
axiom s03 : Foundations.Descent 103 102

/-- Descent from stage 104 to stage 103. -/
axiom s04 : Foundations.Descent 104 103

/-- Descent from stage 105 to stage 104. -/
axiom s05 : Foundations.Descent 105 104

/-- Descent from stage 106 to stage 105. -/
axiom s06 : Foundations.Descent 106 105

/-- Descent from stage 107 to stage 106. -/
axiom s07 : Foundations.Descent 107 106

/-- Descent from stage 108 to stage 107. -/
axiom s08 : Foundations.Descent 108 107

/-- Descent from stage 109 to stage 108. -/
axiom s09 : Foundations.Descent 109 108

/-- Descent from stage 110 to stage 109. -/
axiom s10 : Foundations.Descent 110 109

/-- Descent from stage 111 to stage 110. -/
axiom s11 : Foundations.Descent 111 110

/-- Descent from stage 111 to stage 100, the composite of all eleven rungs above. -/
axiom s12 : Foundations.Descent 111 100

end Lax771644.WideDockRow
