import Lax185574Proofs.ResolveRam.Glue.CaseSz
import Lax185574Proofs.ResolveRam.Glue.SzKit
import Lax185574Proofs.ResolveRam.Glue.CUpB

/-!
The costs of the cases of the glue program.

Each case of a round costs at most a constant times `(n + 1) Y^B`. The
costs of the cases are sums of terms of three kinds: lengths of words of
the state, the answer and the next query, which are at most a constant
times `(n + 1) Y^A` by `SzKit`; constants; and the costs of the pieces,
which are products `c x y^a` of a constant, a length `x` of that kind and
a power of a quantity `y` that does not grow with `n` (`prodU`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TypeTreeSizes Lax3.DistFO

/-! ### Arithmetic -/

/-- **The cost of a piece.** -/
theorem prodU {c x y a Cz N Y A E : ℕ} (hY : 1 ≤ Y) (hx : x ≤ Cz * (N * Y ^ A)) (hy : y ≤ Cz * Y ^ A)
    (ha : a ≤ E) : c * x * y ^ a ≤ c * Cz * (Cz + 1) ^ E * (N * Y ^ (A * (E + 1))) := by
  have hYA : 1 ≤ Y ^ A := Nat.one_le_pow _ _ hY
  have hy1 : y ≤ (Cz + 1) * Y ^ A := le_trans hy (Nat.mul_le_mul_right _ (by omega))
  have hb : 1 ≤ (Cz + 1) * Y ^ A := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h2 : y ^ a ≤ ((Cz + 1) * Y ^ A) ^ E :=
    le_trans (Nat.pow_le_pow_left hy1 a) (Nat.pow_le_pow_right hb ha)
  calc c * x * y ^ a ≤ c * (Cz * (N * Y ^ A)) * ((Cz + 1) * Y ^ A) ^ E :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hx) h2
    _ = c * Cz * (Cz + 1) ^ E * (N * Y ^ (A * (E + 1))) := by
        rw [mul_pow, ← pow_mul, show A * (E + 1) = A + A * E by ring, pow_add]; ring

theorem lin_U {x Cz N Y A E : ℕ} (hY : 1 ≤ Y) (hx : x ≤ Cz * (N * Y ^ A)) :
    x ≤ Cz * (N * Y ^ (A * (E + 1))) :=
  le_trans hx (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hY (by nlinarith))))

theorem nf_lin {x Cz N Y A : ℕ} (hN : 1 ≤ N) (hx : x ≤ Cz * Y ^ A) : x ≤ Cz * (N * Y ^ A) :=
  le_trans hx (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega)))

theorem one_le_U {N Y A : ℕ} (hN : 1 ≤ N) (hY : 1 ≤ Y) : 1 ≤ N * Y ^ A :=
  Nat.mul_le_mul hN (Nat.one_le_pow _ _ hY)

/-! ### Items -/

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The size of the default item. -/
noncomputable def wl0 : ℕ := wordLength dItem.2

theorem itm_mem_or (d i : ℕ) : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d ∨ itm G P Q s k₀ q₀ d i = dItem := by
  by_cases h : i < (lvR G P Q s k₀ q₀ d).length
  · left; rw [itm_eq G P Q s k₀ q₀ h]; exact List.getElem_mem h
  · right; simp [itm, List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 h)]

theorem ell_lvR (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    x.2.ℓ ≤ k₀ + q₀ := by
  obtain ⟨ℓ, u, hu, -, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd hx
  rw [hu]; show ℓ ≤ _; omega

theorem itm_ell (hk : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) (i : ℕ) : (itm G P Q s k₀ q₀ d i).2.ℓ ≤ k₀ + q₀ := by
  rcases itm_mem_or G P Q s k₀ q₀ d i with h | h
  · exact ell_lvR G P Q s k₀ q₀ hk hd h
  · rw [h]; simp [dItem]

theorem itm_wl {C A : ℕ} (hK : SzKit G P Q s k₀ q₀ C A) {d : ℕ} (hd : d ≤ q₀) (i : ℕ) :
    wordLength (itm G P Q s k₀ q₀ d i).2 ≤ (C + wl0) * yQ G P Q s k₀ q₀ ^ A := by
  have hY : 1 ≤ yQ G P Q s k₀ q₀ ^ A := Nat.one_le_pow _ _ (one_le_yQ G P Q s k₀ q₀)
  rcases itm_mem_or G P Q s k₀ q₀ d i with h | h
  · have := hK.item d hd _ h; rw [add_mul]; omega
  · rw [h]; show wl0 ≤ _; rw [add_mul]; nlinarith

theorem itemW_itm {C A : ℕ} (hK : SzKit G P Q s k₀ q₀ C A) {d : ℕ} (hd : d ≤ q₀) (i : ℕ) :
    (itemW (itm G P Q s k₀ q₀ d i)).length ≤ (C + wl0 + 2) * yQ G P Q s k₀ q₀ ^ A := by
  have hY : 1 ≤ yQ G P Q s k₀ q₀ ^ A := Nat.one_le_pow _ _ (one_le_yQ G P Q s k₀ q₀)
  rw [length_itemW]
  have := itm_wl G P Q s k₀ q₀ hK hd i
  rw [add_mul, add_mul] at *; omega

/-- The rank shift of an item. -/
theorem sh_get (hk : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    (toWord (shOf G x.2)).getD 2 0 ≤ k₀ + q₀ ∧
      rhoPlus ((toWord (shOf G x.2)).getD 0 0) ((toWord (shOf G x.2)).getD 1 0) ≤ rhoPlus (k₀ + 1) q₀ := by
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
  rw [hu, show q₀ - d = (q₀ - d - 1) + 1 by omega, shOf_tree G u h1 hℓ,
    Lax185574Proofs.FarRam.toWord_typeTree]
  refine ⟨by simp [tree]; omega, ?_⟩
  simp only [tree, List.getD_cons_zero, List.getD_cons_succ]
  have := rho_lvl (k₀ := k₀) (q₀ := q₀) (d := d + 1) (by omega)
  rw [show k₀ + d + 1 = k₀ + (d + 1) by omega, show q₀ - d - 1 = q₀ - (d + 1) by omega]
  exact this

theorem maxLen_le_of {L : List (List ℕ)} {B : ℕ} (h : ∀ u ∈ L, u.length ≤ B) : maxLen L ≤ B := by
  unfold maxLen
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h v (by simp)) (ih fun u hu => h u (by simp [hu]))

theorem total_le_mul {L : List (List ℕ)} {B : ℕ} (h : ∀ w ∈ L, w.length ≤ B) : total L ≤ L.length * B := by
  induction L with
  | nil => simp [total]
  | cons w L ih =>
    rw [total_cons, List.length_cons]
    have h1 := h w (by simp)
    have h2 := ih fun v hv => h v (by simp [hv])
    nlinarith

theorem pow_two_A {Y A : ℕ} (hY : 1 ≤ Y) : Y ^ A ≤ Y ^ (2 * A) := Nat.pow_le_pow_right hY (by omega)

/-- The constant of the sizes. -/
noncomputable def czOf (C k₀ q₀ : ℕ) : ℕ := 4 * C * C + 4 * C + k₀ + q₀ + rhoPlus (k₀ + 1) q₀ + wl0 + 10

/-- A bound `a Y^A + b` is a bound `Cz Y^(2A)`. -/
theorem nf_cz {Y A x a b Cz : ℕ} (hY : 1 ≤ Y) (h : x ≤ a * Y ^ A + b) (hc : a + b ≤ Cz) :
    x ≤ Cz * Y ^ (2 * A) := by
  have h1 : 1 ≤ Y ^ A := Nat.one_le_pow _ _ hY
  have h2 := pow_two_A (A := A) hY
  calc x ≤ a * Y ^ A + b * Y ^ A := le_trans h (by nlinarith)
    _ = (a + b) * Y ^ A := by ring
    _ ≤ Cz * Y ^ (2 * A) := Nat.mul_le_mul hc h2

/-- A bound `a (N Y^A) + b N` is a bound `Cz (N Y^(2A))`. -/
theorem lin_cz {N Y A x a b Cz : ℕ} (hY : 1 ≤ Y) (hN : 1 ≤ N) (h : x ≤ a * (N * Y ^ A) + b * N)
    (hc : a + b ≤ Cz) : x ≤ Cz * (N * Y ^ (2 * A)) := by
  have h1 : 1 ≤ Y ^ A := Nat.one_le_pow _ _ hY
  have h2 := pow_two_A (A := A) hY
  have h3 : N ≤ N * Y ^ A := Nat.le_mul_of_pos_right _ h1
  calc x ≤ a * (N * Y ^ A) + b * (N * Y ^ A) := le_trans h (by nlinarith)
    _ = (a + b) * (N * Y ^ A) := by ring
    _ ≤ Cz * (N * Y ^ (2 * A)) := Nat.mul_le_mul hc (Nat.mul_le_mul_left _ h2)

section Pieces

variable {C A : ℕ} (hK : SzKit G P Q s k₀ q₀ C A)
include hK

/-- The number of the members of the filtered far tree of an item. -/
theorem faP_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    (faP G (dataOf G P Q s k₀ q₀) x.2).length ≤ C * yQ G P Q s k₀ q₀ ^ A := by
  obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk d hd.le _ hx
  have h3 : (faP G (dataOf G P Q s k₀ q₀) x.2).length ≤ treeCount G (resolveBy G s P Q) k₀ q₀ := by
    rw [hwx, show q₀ - d = (q₀ - d - 1) + 1 by omega]
    exact length_faP_leT G P Q s k₀ q₀ hk (show d + (q₀ - d - 1 + 1) = q₀ by omega) w hw
  exact le_trans h3 hK.T

/-- The answers of the compositions of an item. -/
theorem coW_le (hk : 1 ≤ k₀) {d : ℕ} (hd : d < q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    total (coW G P Q s k₀ q₀ x.2) + (coW G P Q s k₀ q₀ x.2).length ≤
      (C * C + C) * yQ G P Q s k₀ q₀ ^ (2 * A) := by
  have hY := one_le_yQ G P Q s k₀ q₀
  have hF := faP_le G P Q s k₀ q₀ hK hk hd hx
  have hw : ∀ w ∈ coW G P Q s k₀ q₀ x.2, w.length ≤ C * yQ G P Q s k₀ q₀ ^ A := by
    intro w hw
    simp only [coW, List.mem_map] at hw
    obtain ⟨ν, hν, rfl⟩ := hw
    exact hK.co d hd x hx ν (List.mem_filter.1 hν).1
  have ht := total_le_mul hw
  rw [length_coW] at ht ⊢
  have e : yQ G P Q s k₀ q₀ ^ (2 * A) = yQ G P Q s k₀ q₀ ^ A * yQ G P Q s k₀ q₀ ^ A := by
    rw [two_mul, pow_add]
  have h1 : 1 ≤ yQ G P Q s k₀ q₀ ^ A := Nat.one_le_pow _ _ hY
  rw [e]
  nlinarith

/-- **The cost of the piece of the far tree.** -/
theorem kFA_le (hk : 1 ≤ k₀) {d i E : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hb : (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))).length ≤ C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))
    (hE : aFA ≤ E) :
    kFA G P Q s k₀ q₀ d i ≤ cFA * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ E *
      ((n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (E + 1))) := by
  have hY := one_le_yQ G P Q s k₀ q₀
  have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
    rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
  have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  have hcall : callOf G P Q s k₀ q₀ (.dn d i 1) = .ftree (itm G P Q s k₀ q₀ d i).2 := by
    rw [callOf_dn' hi (by omega)]; simp
  have h1 : (toWord ((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord)).length ≤
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i 1))).length := by
    rw [hcall]; exact realY_len_le G k₀ q₀ (.ftree _)
  have h2 := ctW_len G P Q
  obtain ⟨g2, g01⟩ := sh_get G P Q s k₀ q₀ hk hd hx
  have h3 := hK.shift d hd _ hx
  have h4 : maxLen ((faOf G (itm G P Q s k₀ q₀ d i).2).map toWord) ≤ C * yQ G P Q s k₀ q₀ ^ A :=
    maxLen_le_of fun u hu => by
      simp only [List.mem_map] at hu
      obtain ⟨ν, hν, rfl⟩ := hu
      exact hK.fa d hd _ hx ν hν
  unfold kFA
  refine prodU hY (lin_cz (a := C) (b := 4) hY (by omega) ?_ ?_) (nf_cz (a := 2 * C)
    (b := k₀ + q₀ + rhoPlus (k₀ + 1) q₀ + 1) hY ?_ ?_) hE
  · have : (n + 1) * yQ G P Q s k₀ q₀ ^ A ≥ 1 := one_le_U (by omega) hY; omega
  · unfold czOf; nlinarith
  · have e : wordLength (shOf G (itm G P Q s k₀ q₀ d i).2) = (toWord (shOf G (itm G P Q s k₀ q₀ d i).2)).length := rfl
    have e2 : 2 * C * yQ G P Q s k₀ q₀ ^ A = 2 * (C * yQ G P Q s k₀ q₀ ^ A) := by ring
    omega
  · unfold czOf; nlinarith

/-- **The cost of the piece of the expansion of an item.** -/
theorem kEx_le (hk : 1 ≤ k₀) {d i E : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hE : aEx ≤ E) :
    cEx * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + (itm G P Q s k₀ q₀ d i).2.ℓ +
      total (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) + (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length +
      rhoPlus (k₀ + 1) q₀ + 1) ^ aEx ≤ cEx * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ E *
      ((n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (E + 1))) := by
  have hY := one_le_yQ G P Q s k₀ q₀
  have hx : itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
    rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi
  have h2 := ctW_len G P Q
  have h3 := itemW_itm G P Q s k₀ q₀ hK hd.le i
  have h4 := itm_ell G P Q s k₀ q₀ hk hd.le i
  have h5 := coW_le G P Q s k₀ q₀ hK hk hd hx
  have h6 := pow_two_A (A := A) hY
  have h7 : 1 ≤ yQ G P Q s k₀ q₀ ^ A := Nat.one_le_pow _ _ hY
  refine prodU hY (lin_cz (a := 0) (b := 4) hY (by omega) (by simp; omega) (by unfold czOf; omega)) ?_ hE
  calc _ ≤ (C + wl0 + 2) * yQ G P Q s k₀ q₀ ^ (2 * A) + (C * C + C) * yQ G P Q s k₀ q₀ ^ (2 * A) +
        (k₀ + q₀ + rhoPlus (k₀ + 1) q₀ + 1) * yQ G P Q s k₀ q₀ ^ (2 * A) := by
        have : (C + wl0 + 2) * yQ G P Q s k₀ q₀ ^ A ≤ (C + wl0 + 2) * yQ G P Q s k₀ q₀ ^ (2 * A) :=
          Nat.mul_le_mul_left _ h6
        have : 1 ≤ yQ G P Q s k₀ q₀ ^ (2 * A) := le_trans h7 h6
        nlinarith
    _ ≤ czOf C k₀ q₀ * yQ G P Q s k₀ q₀ ^ (2 * A) := by
        rw [← add_mul, ← add_mul]; exact Nat.mul_le_mul_right _ (by unfold czOf; nlinarith)

/-- **The cost of a piece of the atom words** (`cA (|CT| + 1) (|item| + ℓ + ρ + 1)^a`). -/
theorem kAtom_le (hk : 1 ≤ k₀) {d i E cA aA : ℕ} (hd : d ≤ q₀) (hE : aA ≤ E) :
    cA * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + (itm G P Q s k₀ q₀ d i).2.ℓ +
      rhoPlus (k₀ + 1) q₀ + 1) ^ aA ≤ cA * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ E *
      ((n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (E + 1))) := by
  have hY := one_le_yQ G P Q s k₀ q₀
  have h2 := ctW_len G P Q
  have h3 := itemW_itm G P Q s k₀ q₀ hK hd i
  have h4 := itm_ell G P Q s k₀ q₀ hk hd i
  refine prodU hY (lin_cz (a := 0) (b := 4) hY (by omega) (by simp; omega) (by unfold czOf; omega))
    (nf_cz (a := C + wl0 + 2) (b := k₀ + q₀ + rhoPlus (k₀ + 1) q₀ + 1) hY (by omega)
      (by unfold czOf; nlinarith)) hE

/-- **The cost of the children query of an item.** -/
theorem kKid_le {d i E : ℕ} (hd : d < q₀) (hE : aKd ≤ E) :
    cKd * ((lvR G P Q s k₀ q₀ (d + 1)).length + total (lvW G P Q s k₀ q₀ (d + 1)) +
      total (outW G P Q s k₀ q₀ (d + 1)) + 1) * ((itemW (itm G P Q s k₀ q₀ d i)).length + 1) ^ aKd ≤
      cKd * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ E * ((n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (E + 1))) := by
  have hY := one_le_yQ G P Q s k₀ q₀
  have h1 : 1 ≤ yQ G P Q s k₀ q₀ ^ A := Nat.one_le_pow _ _ hY
  have hl := hK.lv (d + 1) hd
  have hw : ∀ w ∈ lvW G P Q s k₀ q₀ (d + 1), w.length ≤ (C + 2) * yQ G P Q s k₀ q₀ ^ A := by
    intro w hw
    simp only [lvW, List.mem_map] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    have := hK.item (d + 1) hd x hx
    rw [length_itemW]; nlinarith
  have ho : ∀ w ∈ outW G P Q s k₀ q₀ (d + 1), w.length ≤ C * yQ G P Q s k₀ q₀ ^ A := hK.out (d + 1) hd
  have t1 := total_le_mul hw
  have t2 := total_le_mul ho
  rw [length_lvW] at t1
  rw [length_outW] at t2
  have h3 := itemW_itm G P Q s k₀ q₀ hK hd.le i
  refine prodU hY ?_ (nf_cz (a := C + wl0 + 2) (b := 1) hY (by omega) (by unfold czOf; nlinarith)) hE
  set N := (lvR G P Q s k₀ q₀ (d + 1)).length
  set V := yQ G P Q s k₀ q₀ ^ A
  have e : yQ G P Q s k₀ q₀ ^ (2 * A) = V * V := by rw [two_mul, pow_add]
  rw [e]
  have hN : N ≤ C * ((n + 1) * V) := by rw [← mul_assoc]; exact hl
  calc N + total (lvW G P Q s k₀ q₀ (d + 1)) + total (outW G P Q s k₀ q₀ (d + 1)) + 1
      ≤ N * (1 + (C + 2) * V + C * V) + 1 := by nlinarith
    _ ≤ (C * ((n + 1) * V)) * ((2 * C + 3) * V) + (n + 1) * (V * V) := by
        have hCV : 1 + (C + 2) * V + C * V ≤ (2 * C + 3) * V := by nlinarith
        have hVV : 1 ≤ V * V := Nat.mul_le_mul h1 h1
        have hnV : 1 ≤ (n + 1) * (V * V) := le_trans hVV (Nat.le_mul_of_pos_left _ (by omega))
        calc _ ≤ (C * ((n + 1) * V)) * ((2 * C + 3) * V) + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul hN hCV) _
          _ ≤ _ := by omega
    _ = (2 * C * C + 3 * C + 1) * ((n + 1) * (V * V)) := by ring
    _ ≤ czOf C k₀ q₀ * ((n + 1) * (V * V)) := Nat.mul_le_mul_right _ (by unfold czOf; nlinarith)

end Pieces

end Lax185574Proofs.ResolveRam.Glue
