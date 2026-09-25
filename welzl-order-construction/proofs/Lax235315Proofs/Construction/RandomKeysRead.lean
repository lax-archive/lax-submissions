import Lax235315Proofs.Construction.RandomBits
import Mathlib.Tactic

/-! Reading the eight word-sized digits of one random vertex key. -/

namespace Lax235315Proofs.Construction.RandomKeysRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RandomBits

def keyName : Fin 8 → String
  | ⟨0, _⟩ => "key0"
  | ⟨1, _⟩ => "key1"
  | ⟨2, _⟩ => "key2"
  | ⟨3, _⟩ => "key3"
  | ⟨4, _⟩ => "key4"
  | ⟨5, _⟩ => "key5"
  | ⟨6, _⟩ => "key6"
  | ⟨7, _⟩ => "key7"
  | ⟨k + 8, h⟩ => by omega

def joined8 (b : Fin 8 → List ℕ) : List ℕ :=
  b 0 ++ b 1 ++ b 2 ++ b 3 ++ b 4 ++ b 5 ++ b 6 ++ b 7

def updateKeys (g : Fin 8 → ℕ → ℕ) (b : Fin 8 → List ℕ)
    (v : ℕ) (d : Fin 8) (i : ℕ) : ℕ :=
  if i = v then bitsValue (b d) else g d i

private theorem array_eq_update {n v value : ℕ} {g g' : ℕ → ℕ}
    (hat : g' v = value)
    (hother : ∀ i < n, i ≠ v → g' i = g i) :
    arrOf n g' = arrOf n (fun i => if i = v then value else g i) := by
  apply arrOf_congr
  intro i hi
  by_cases hiv : i = v
  · subst i
    simp [hat]
  · simp [hiv, hother i hi hiv]

/-- The fixed eight-digit block updates exactly the eight key arrays at `v`. -/
theorem readAllKeyDigits_run {B n v L : ℕ} {σ : Env}
    {g : Fin 8 → ℕ → ℕ} {b : Fin 8 → List ℕ} {rest : List ℕ}
    (hkeys : ∀ d, σ.arrs (keyName d) = arrOf n (g d))
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = L)
    (hlen : ∀ d, (b d).length = L)
    (hbits : ∀ d x, x ∈ b d → x ≤ 1)
    (hinp : σ.inp = joined8 b ++ rest)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B) :
    ∃ σ', Run B readAllKeyDigits σ σ' (120 * L + 88) ∧
      (∀ d, σ'.arrs (keyName d) = arrOf n (updateKeys g b v d)) ∧
      σ'.inp = rest ∧ σ'.vars "v" = v ∧ σ'.vars "L" = L := by
  let tail0 := b 1 ++ b 2 ++ b 3 ++ b 4 ++ b 5 ++ b 6 ++ b 7 ++ rest
  have hinp0 : σ.inp = b 0 ++ tail0 := by simpa [joined8, tail0] using hinp
  obtain ⟨σ₁, g₀, r₀, ha₀, hv₀, ho₀, hi₀, hsv₀, hsL₀⟩ :=
    readKeyDigit_run (key := "key0") (g := g 0) (bs := b 0) (rest := tail0)
      (hkeys 0) hv hvn hL (hlen 0) hinp0 (hbits 0) hpowB hnB htwoB
  have hk₀ : σ₁.arrs "key0" = arrOf n (updateKeys g b v 0) := by
    rw [ha₀, array_eq_update hv₀ ho₀]
    rfl
  let tail1 := b 2 ++ b 3 ++ b 4 ++ b 5 ++ b 6 ++ b 7 ++ rest
  have hi₁' : σ₁.inp = b 1 ++ tail1 := by simpa [tail0, tail1] using hi₀
  have hk₁in : σ₁.arrs "key1" = arrOf n (g 1) := by
    rw [r₀.frame_arr "key1" (by decide)]
    simpa [keyName] using hkeys (1 : Fin 8)
  obtain ⟨σ₂, g₁, r₁, ha₁, hv₁, ho₁, hi₁, hsv₁, hsL₁⟩ :=
    readKeyDigit_run (key := "key1") (g := g 1) (bs := b 1) (rest := tail1)
      hk₁in hsv₀ hvn hsL₀ (hlen 1) hi₁' (hbits 1) hpowB hnB htwoB
  have hk₁ : σ₂.arrs "key1" = arrOf n (updateKeys g b v 1) := by
    rw [ha₁, array_eq_update hv₁ ho₁]
    rfl
  let tail2 := b 3 ++ b 4 ++ b 5 ++ b 6 ++ b 7 ++ rest
  have hi₂' : σ₂.inp = b 2 ++ tail2 := by simpa [tail1, tail2] using hi₁
  have hk₂in : σ₂.arrs "key2" = arrOf n (g 2) := by
    rw [r₁.frame_arr "key2" (by decide), r₀.frame_arr "key2" (by decide)]
    simpa [keyName] using hkeys (2 : Fin 8)
  obtain ⟨σ₃, g₂, r₂, ha₂, hv₂, ho₂, hi₂, hsv₂, hsL₂⟩ :=
    readKeyDigit_run (key := "key2") (g := g 2) (bs := b 2) (rest := tail2)
      hk₂in hsv₁ hvn hsL₁ (hlen 2) hi₂' (hbits 2) hpowB hnB htwoB
  have hk₂ : σ₃.arrs "key2" = arrOf n (updateKeys g b v 2) := by
    rw [ha₂, array_eq_update hv₂ ho₂]
    rfl
  let tail3 := b 4 ++ b 5 ++ b 6 ++ b 7 ++ rest
  have hi₃' : σ₃.inp = b 3 ++ tail3 := by simpa [tail2, tail3] using hi₂
  have hk₃in : σ₃.arrs "key3" = arrOf n (g 3) := by
    rw [r₂.frame_arr "key3" (by decide), r₁.frame_arr "key3" (by decide),
      r₀.frame_arr "key3" (by decide)]
    simpa [keyName] using hkeys (3 : Fin 8)
  obtain ⟨σ₄, g₃, r₃, ha₃, hv₃, ho₃, hi₃, hsv₃, hsL₃⟩ :=
    readKeyDigit_run (key := "key3") (g := g 3) (bs := b 3) (rest := tail3)
      hk₃in hsv₂ hvn hsL₂ (hlen 3) hi₃' (hbits 3) hpowB hnB htwoB
  have hk₃ : σ₄.arrs "key3" = arrOf n (updateKeys g b v 3) := by
    rw [ha₃, array_eq_update hv₃ ho₃]
    rfl
  let tail4 := b 5 ++ b 6 ++ b 7 ++ rest
  have hi₄' : σ₄.inp = b 4 ++ tail4 := by simpa [tail3, tail4] using hi₃
  have hk₄in : σ₄.arrs "key4" = arrOf n (g 4) := by
    rw [r₃.frame_arr "key4" (by decide), r₂.frame_arr "key4" (by decide),
      r₁.frame_arr "key4" (by decide), r₀.frame_arr "key4" (by decide)]
    simpa [keyName] using hkeys (4 : Fin 8)
  obtain ⟨σ₅, g₄, r₄, ha₄, hv₄, ho₄, hi₄, hsv₄, hsL₄⟩ :=
    readKeyDigit_run (key := "key4") (g := g 4) (bs := b 4) (rest := tail4)
      hk₄in hsv₃ hvn hsL₃ (hlen 4) hi₄' (hbits 4) hpowB hnB htwoB
  have hk₄ : σ₅.arrs "key4" = arrOf n (updateKeys g b v 4) := by
    rw [ha₄, array_eq_update hv₄ ho₄]
    rfl
  let tail5 := b 6 ++ b 7 ++ rest
  have hi₅' : σ₅.inp = b 5 ++ tail5 := by simpa [tail4, tail5] using hi₄
  have hk₅in : σ₅.arrs "key5" = arrOf n (g 5) := by
    rw [r₄.frame_arr "key5" (by decide), r₃.frame_arr "key5" (by decide),
      r₂.frame_arr "key5" (by decide), r₁.frame_arr "key5" (by decide),
      r₀.frame_arr "key5" (by decide)]
    simpa [keyName] using hkeys (5 : Fin 8)
  obtain ⟨σ₆, g₅, r₅, ha₅, hv₅, ho₅, hi₅, hsv₅, hsL₅⟩ :=
    readKeyDigit_run (key := "key5") (g := g 5) (bs := b 5) (rest := tail5)
      hk₅in hsv₄ hvn hsL₄ (hlen 5) hi₅' (hbits 5) hpowB hnB htwoB
  have hk₅ : σ₆.arrs "key5" = arrOf n (updateKeys g b v 5) := by
    rw [ha₅, array_eq_update hv₅ ho₅]
    rfl
  let tail6 := b 7 ++ rest
  have hi₆' : σ₆.inp = b 6 ++ tail6 := by simpa [tail5, tail6] using hi₅
  have hk₆in : σ₆.arrs "key6" = arrOf n (g 6) := by
    rw [r₅.frame_arr "key6" (by decide), r₄.frame_arr "key6" (by decide),
      r₃.frame_arr "key6" (by decide), r₂.frame_arr "key6" (by decide),
      r₁.frame_arr "key6" (by decide), r₀.frame_arr "key6" (by decide)]
    simpa [keyName] using hkeys (6 : Fin 8)
  obtain ⟨σ₇, g₆, r₆, ha₆, hv₆, ho₆, hi₆, hsv₆, hsL₆⟩ :=
    readKeyDigit_run (key := "key6") (g := g 6) (bs := b 6) (rest := tail6)
      hk₆in hsv₅ hvn hsL₅ (hlen 6) hi₆' (hbits 6) hpowB hnB htwoB
  have hk₆ : σ₇.arrs "key6" = arrOf n (updateKeys g b v 6) := by
    rw [ha₆, array_eq_update hv₆ ho₆]
    rfl
  have hk₇in : σ₇.arrs "key7" = arrOf n (g 7) := by
    rw [r₆.frame_arr "key7" (by decide), r₅.frame_arr "key7" (by decide),
      r₄.frame_arr "key7" (by decide), r₃.frame_arr "key7" (by decide),
      r₂.frame_arr "key7" (by decide), r₁.frame_arr "key7" (by decide),
      r₀.frame_arr "key7" (by decide)]
    simpa [keyName] using hkeys (7 : Fin 8)
  obtain ⟨σ₈, g₇, r₇, ha₇, hv₇, ho₇, hi₇, hsv₇, hsL₇⟩ :=
    readKeyDigit_run (key := "key7") (g := g 7) (bs := b 7) (rest := rest)
      hk₇in hsv₆ hvn hsL₆ (hlen 7) (by simpa [tail6] using hi₆)
      (hbits 7) hpowB hnB htwoB
  have hk₇ : σ₈.arrs "key7" = arrOf n (updateKeys g b v 7) := by
    rw [ha₇, array_eq_update hv₇ ho₇]
    rfl
  refine ⟨σ₈, ?_, ?_, hi₇, hsv₇, hsL₇⟩
  · have rr := r₀.seq (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq r₇))))))
    simpa [readAllKeyDigits, keyNames, seqs] using rr.mono (by omega)
  · intro d
    fin_cases d
    · change σ₈.arrs "key0" = arrOf n (updateKeys g b v 0)
      rw [r₇.frame_arr "key0" (by decide), r₆.frame_arr "key0" (by decide),
        r₅.frame_arr "key0" (by decide), r₄.frame_arr "key0" (by decide),
        r₃.frame_arr "key0" (by decide), r₂.frame_arr "key0" (by decide),
        r₁.frame_arr "key0" (by decide), hk₀]
    · change σ₈.arrs "key1" = arrOf n (updateKeys g b v 1)
      rw [r₇.frame_arr "key1" (by decide), r₆.frame_arr "key1" (by decide),
        r₅.frame_arr "key1" (by decide), r₄.frame_arr "key1" (by decide),
        r₃.frame_arr "key1" (by decide), r₂.frame_arr "key1" (by decide), hk₁]
    · change σ₈.arrs "key2" = arrOf n (updateKeys g b v 2)
      rw [r₇.frame_arr "key2" (by decide), r₆.frame_arr "key2" (by decide),
        r₅.frame_arr "key2" (by decide), r₄.frame_arr "key2" (by decide),
        r₃.frame_arr "key2" (by decide), hk₂]
    · change σ₈.arrs "key3" = arrOf n (updateKeys g b v 3)
      rw [r₇.frame_arr "key3" (by decide), r₆.frame_arr "key3" (by decide),
        r₅.frame_arr "key3" (by decide), r₄.frame_arr "key3" (by decide), hk₃]
    · change σ₈.arrs "key4" = arrOf n (updateKeys g b v 4)
      rw [r₇.frame_arr "key4" (by decide), r₆.frame_arr "key4" (by decide),
        r₅.frame_arr "key4" (by decide), hk₄]
    · change σ₈.arrs "key5" = arrOf n (updateKeys g b v 5)
      rw [r₇.frame_arr "key5" (by decide), r₆.frame_arr "key5" (by decide), hk₅]
    · change σ₈.arrs "key6" = arrOf n (updateKeys g b v 6)
      rw [r₇.frame_arr "key6" (by decide), hk₆]
    · change σ₈.arrs "key7" = arrOf n (updateKeys g b v 7)
      exact hk₇

end Lax235315Proofs.Construction.RandomKeysRead
