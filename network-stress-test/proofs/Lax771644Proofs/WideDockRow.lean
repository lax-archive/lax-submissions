import Lax771644Proofs.Ladder
import Lax771644.WideDockRow

/-!
Proofs for the concept `Lax771644.WideDockRow`.
-/

namespace Lax771644Proofs.WideDockRow

open Lax771644.Foundations
open Lax771644Proofs.Ladder

/--
---
conclusion: Lax771644.WideDockRow.s01
---
Statement 1 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s01 : Descent 101 100 :=
  descent 101 100 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s02
---
Statement 2 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s02 : Descent 102 101 :=
  descent 102 101 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s03
---
Statement 3 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s03 : Descent 103 102 :=
  descent 103 102 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s04
---
Statement 4 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s04 : Descent 104 103 :=
  descent 104 103 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s05
---
Statement 5 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s05 : Descent 105 104 :=
  descent 105 104 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s06
---
Statement 6 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s06 : Descent 106 105 :=
  descent 106 105 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s07
---
Statement 7 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s07 : Descent 107 106 :=
  descent 107 106 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s08
---
Statement 8 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s08 : Descent 108 107 :=
  descent 108 107 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s09
---
Statement 9 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s09 : Descent 109 108 :=
  descent 109 108 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s10
---
Statement 10 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s10 : Descent 110 109 :=
  descent 110 109 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s11
---
Statement 11 holds outright.

# Proof strategy

One application of the ladder's weakening lemma.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s11 : Descent 111 110 :=
  descent 111 110 (by omega)

/--
---
conclusion: Lax771644.WideDockRow.s12
assumptions:
  - Lax771644.WideDockRow.s01
  - Lax771644.WideDockRow.s02
  - Lax771644.WideDockRow.s03
  - Lax771644.WideDockRow.s04
  - Lax771644.WideDockRow.s05
  - Lax771644.WideDockRow.s06
  - Lax771644.WideDockRow.s07
  - Lax771644.WideDockRow.s08
  - Lax771644.WideDockRow.s09
  - Lax771644.WideDockRow.s10
  - Lax771644.WideDockRow.s11
---
Statement 12 composes all eleven of its siblings.

# Proof strategy

Descend one rung at a time, from stage 111 to stage 100.

# Attribution

Synthetic: written for this benchmark. The mathematics is a one-line
divisibility weakening; only the shape of the dependency edges is the point.
-/
theorem s12 : Descent 111 100 := by
  intro n hn
  have h0 : Stage 111 n := hn
  have h1 : Stage 110 n := Lax771644.WideDockRow.s11 n (weaken 111 111 (by omega) h0)
  have h2 : Stage 109 n := Lax771644.WideDockRow.s10 n (weaken 110 110 (by omega) h1)
  have h3 : Stage 108 n := Lax771644.WideDockRow.s09 n (weaken 109 109 (by omega) h2)
  have h4 : Stage 107 n := Lax771644.WideDockRow.s08 n (weaken 108 108 (by omega) h3)
  have h5 : Stage 106 n := Lax771644.WideDockRow.s07 n (weaken 107 107 (by omega) h4)
  have h6 : Stage 105 n := Lax771644.WideDockRow.s06 n (weaken 106 106 (by omega) h5)
  have h7 : Stage 104 n := Lax771644.WideDockRow.s05 n (weaken 105 105 (by omega) h6)
  have h8 : Stage 103 n := Lax771644.WideDockRow.s04 n (weaken 104 104 (by omega) h7)
  have h9 : Stage 102 n := Lax771644.WideDockRow.s03 n (weaken 103 103 (by omega) h8)
  have h10 : Stage 101 n := Lax771644.WideDockRow.s02 n (weaken 102 102 (by omega) h9)
  have h11 : Stage 100 n := Lax771644.WideDockRow.s01 n (weaken 101 101 (by omega) h10)
  exact weaken 100 100 (by omega) h11

end Lax771644Proofs.WideDockRow
