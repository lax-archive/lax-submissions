import Lax185574.DistanceMatrix
import Lax185574Proofs.Legacy
import Lax185574.ResolveLift
import Lax185574Proofs.TreeAlgo.ResolveDist

/-!
The distance matrix `D_G` of a partial graph, as plain facts without
machines.

* `distMatrix_le_iff`: an entry is at most `r` exactly if the two
  vertices are within distance `r` in the graph of resolved pairs. The
  same holds for `SimpleGraph.edist` in any graph (`edist_le_iff`).
* The one-entry code of a distance (`dcode`, `0` for `∞` and `d + 1`
  otherwise), its test `0 < dcode d ≤ r + 1` for `d ≤ r`, and the word of
  a matrix: length `1 + n(n + 1)`, the entry `(u, v)` at position
  `2 + u(n + 1) + v` and the row headers at `1 + u(n + 1)`.
* `D_G` of an initial partial graph, and of a merge (unchanged).
* The distances after a resolve (eq:resolve-dist of the source), from the
  distances `distTo G u X` to the color classes. The formula of the source
  assumes that both color classes are nonempty, as the source does in the
  proof of the resolve lift. If one of them is empty, the resolve adds no
  pair and `D_H = D_G`. The version `distMatrix_resolveBy` covers all cases
  with a guard `occ` that is `0` if a color occurs and `∞` otherwise. The
  formula also holds for `P = Q`.
* The distance between two color classes (`distCls`), and its code as the
  first layer of a breadth-first search from a class (`code_eq_find`).
-/

namespace Lax185574Proofs.DistMatrix

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceMatrix Lax185574.PartialGraphEncoding Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574Proofs.TreeAlgo Lax185574Proofs.WalkDistance

/-! ### Extended distances and walks -/

section edist

variable {W : Type*} {H : SimpleGraph W} {u v : W}

/-- **The extended distance is at most `r` exactly within distance `r`.** -/
theorem edist_le_iff {r : ℕ} : H.edist u v ≤ r ↔ WithinDist H r u v := by
  constructor
  · intro h
    have hne : H.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top r) h
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
    refine ⟨p, ?_⟩
    rw [← hp] at h
    exact_mod_cast h
  · rintro ⟨p, hp⟩
    exact le_trans (SimpleGraph.edist_le p) (by exact_mod_cast hp)

theorem edist_eq_top_iff : H.edist u v = ⊤ ↔ ∀ r : ℕ, ¬ WithinDist H r u v := by
  constructor
  · intro h r hr
    have := (edist_le_iff (H := H)).2 hr
    rw [h] at this
    exact ENat.natCast_ne_top r (top_le_iff.1 this)
  · intro h
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
    exact h m ((edist_le_iff (H := H)).1 hm.symm.le)

/-- Two values of `ℕ∞` with the same bounds by natural numbers are
equal. -/
theorem enat_eq_of_le_iff {a b : ℕ∞} (h : ∀ r : ℕ, a ≤ r ↔ b ≤ r) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe m =>
      have := (h m).2 le_rfl
      exact absurd (top_le_iff.1 this) (ENat.natCast_ne_top m)
  | coe m =>
    have hb := (h m).1 le_rfl
    induction b using ENat.recTopCoe with
    | top => exact absurd (top_le_iff.1 hb) (ENat.natCast_ne_top m)
    | coe m' =>
      have ha := (h m').2 le_rfl
      have h1 : m ≤ m' := by exact_mod_cast ha
      have h2 : m' ≤ m := by exact_mod_cast hb
      rw [le_antisymm h1 h2]

end edist

/-! ### The distance matrix and `WithinDist` -/

variable {n : ℕ}

/-- **Entries of the distance matrix.** -/
theorem distMatrix_le_iff (G : PartialGraph (Fin n)) (u v : Fin n) (r : ℕ) :
    distMatrix G u v ≤ r ↔ WithinDist G.resolved r u v :=
  edist_le_iff

theorem distMatrix_eq_top_iff (G : PartialGraph (Fin n)) (u v : Fin n) :
    distMatrix G u v = ⊤ ↔ ∀ r : ℕ, ¬ WithinDist G.resolved r u v :=
  edist_eq_top_iff

theorem distMatrix_self (G : PartialGraph (Fin n)) (u : Fin n) : distMatrix G u u = 0 :=
  SimpleGraph.edist_self

theorem distMatrix_comm (G : PartialGraph (Fin n)) (u v : Fin n) :
    distMatrix G u v = distMatrix G v u :=
  SimpleGraph.edist_comm

/-- A vertex within some distance is within distance `n - 1`. -/
theorem withinDist_lt_card {G : PartialGraph (Fin n)} {u v : Fin n} {d : ℕ}
    (h : WithinDist G.resolved d u v) : WithinDist G.resolved (n - 1) u v := by
  classical
  obtain ⟨p, -⟩ := h
  refine ⟨p.bypass, ?_⟩
  have := p.bypass_isPath.length_lt
  rw [Fintype.card_fin] at this
  omega

/-- A finite entry is below `n`. -/
theorem distMatrix_lt (G : PartialGraph (Fin n)) (u v : Fin n) (h : distMatrix G u v ≠ ⊤) :
    (distMatrix G u v).toNat < n := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
  rw [← hm, ENat.toNat_natCast]
  have h1 := withinDist_lt_card ((distMatrix_le_iff G u v m).1 hm.symm.le)
  have h2 := (distMatrix_le_iff G u v (n - 1)).2 h1
  rw [← hm] at h2
  have h3 : m ≤ n - 1 := by exact_mod_cast h2
  have : 1 ≤ n := Fin.pos u
  omega

/-! ### The code of a distance -/

/-- The entry of a distance: `0` for `∞` and `d + 1` for `d`. -/
def dcode (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

theorem toWord_enat (d : ℕ∞) : toWord d = [dcode d] := rfl

@[simp] theorem dcode_top : dcode ⊤ = 0 := by simp [dcode]

@[simp] theorem dcode_coe (m : ℕ) : dcode m = m + 1 := by simp [dcode]

theorem dcode_eq_zero_iff (d : ℕ∞) : dcode d = 0 ↔ d = ⊤ := by
  unfold dcode; split_ifs with h <;> simp [h]

/-- **The test of an entry.** `d ≤ r` exactly if its code is positive and
at most `r + 1`. -/
theorem dcode_test (d : ℕ∞) (r : ℕ) : (0 < dcode d ∧ dcode d ≤ r + 1) ↔ d ≤ r := by
  induction d using ENat.recTopCoe with
  | top => simp
  | coe m => simp only [dcode_coe, Nat.cast_le]; omega

/-- The code of `d` is `t + 1` exactly if `d = t`. -/
theorem dcode_eq_succ (d : ℕ∞) (t : ℕ) : dcode d = t + 1 ↔ d = t := by
  induction d using ENat.recTopCoe with
  | top => simp
  | coe m => simp

/-- The codes of an entry of the distance matrix are at most `n`. -/
theorem dcode_distMatrix_le (G : PartialGraph (Fin n)) (u v : Fin n) :
    dcode (distMatrix G u v) ≤ n := by
  by_cases h : distMatrix G u v = ⊤
  · rw [h, dcode_top]; exact Nat.zero_le _
  · have := distMatrix_lt G u v h
    unfold dcode; rw [if_neg h]; omega

/-- **The code of a distance of the form `Nat.find`.** If the bounds
`d ≤ s` are the property `p s`, then `dcode d` is one more than the least
`s` with `p s`, and `0` if there is none. -/
theorem code_eq_find {d : ℕ∞} {p : ℕ → Prop} [DecidablePred p] [Decidable (∃ s, p s)]
    (h : ∀ s : ℕ, d ≤ s ↔ p s) :
    (if hp : ∃ s, p s then Nat.find hp + 1 else 0) = dcode d := by
  split_ifs with hp
  · have hs := Nat.find_spec hp
    have hd : d ≤ Nat.find hp := (h _).2 hs
    have hne : d ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hne
    have h1 : m ≤ Nat.find hp := by exact_mod_cast hd
    have h2 : Nat.find hp ≤ m := Nat.find_min' hp ((h m).1 le_rfl)
    rw [dcode_coe]; omega
  · have : d = ⊤ := by
      by_contra hne
      obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hne
      exact hp ⟨m, (h m).1 le_rfl⟩
    rw [this, dcode_top]

/-! ### The word of a matrix -/

/-- The word of an `n × n` matrix of codes: `n`, then every row as `n`
and its `n` entries. -/
def matWord (n : ℕ) (f : Fin n → Fin n → ℕ) : List ℕ :=
  n :: (List.ofFn fun u => n :: List.ofFn fun v => f u v).flatten

theorem flatten_ofFn_singleton {m : ℕ} (f : Fin m → ℕ∞) :
    (List.ofFn ((fun d : ℕ∞ => [if d = ⊤ then 0 else d.toNat + 1]) ∘ f)).flatten =
      List.ofFn fun v => dcode (f v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ]
    have := ih (fun i => f i.succ)
    simp only [Function.comp_def] at this ⊢
    rw [this]
    rfl

/-- **The word of a matrix of distances.** -/
theorem toWord_mat (M : Fin n → Fin n → ℕ∞) :
    toWord M = matWord n fun u v => dcode (M u v) := by
  have row : ∀ u, toWord (M u) = n :: List.ofFn fun v => dcode (M u v) := by
    intro u
    show toWord (List.ofFn (M u)) = _
    rw [Lax185574Proofs.Legacy.toWord_list, List.length_ofFn, List.map_ofFn]
    exact congrArg (n :: ·) (flatten_ofFn_singleton _)
  show toWord (List.ofFn M) = _
  rw [Lax185574Proofs.Legacy.toWord_list, List.length_ofFn, List.map_ofFn]
  exact congrArg (n :: ·) (congrArg List.flatten (congrArg List.ofFn (funext fun u => row u)))

theorem toWord_distMatrix (G : PartialGraph (Fin n)) :
    toWord (distMatrix G) = matWord n fun u v => dcode (distMatrix G u v) :=
  toWord_mat _

/-- A flatten of lists of the same length `m`. -/
theorem getElem?_flatten_const {α : Type*} (m : ℕ) :
    ∀ (L : List (List α)), (∀ l ∈ L, l.length = m) → ∀ (i j : ℕ), j < m →
      L.flatten[i * m + j]? = (L[i]?).bind fun l => l[j]?
  | [], _, i, j, _ => by simp
  | l :: L, hL, i, j, hj => by
    have hl : l.length = m := hL l (by simp)
    rcases i with _ | i
    · simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem?_cons_zero,
        Option.bind_some]
      rw [List.getElem?_append_left (by omega)]
    · simp only [List.flatten_cons, List.getElem?_cons_succ]
      rw [List.getElem?_append_right (by rw [hl]; nlinarith)]
      have : (i + 1) * m + j - l.length = i * m + j := by rw [hl]; ring_nf; omega
      rw [this]
      exact getElem?_flatten_const m L (fun l' hl' => hL l' (by simp [hl'])) i j hj

theorem length_flatten_const {α : Type*} (m : ℕ) :
    ∀ (L : List (List α)), (∀ l ∈ L, l.length = m) → L.flatten.length = L.length * m
  | [], _ => by simp
  | l :: L, hL => by
    have hl : l.length = m := hL l (by simp)
    rw [List.flatten_cons, List.length_append, length_flatten_const m L
      (fun l' hl' => hL l' (by simp [hl'])), hl, List.length_cons]
    ring

/-- **The length of the word of a matrix.** -/
theorem length_matWord (f : Fin n → Fin n → ℕ) : (matWord n f).length = 1 + n * (n + 1) := by
  unfold matWord
  rw [List.length_cons, length_flatten_const (n + 1)]
  · simp only [List.length_ofFn]; ring
  · intro l hl
    simp only [List.mem_ofFn] at hl
    obtain ⟨u, rfl⟩ := hl
    simp

theorem length_toWord_mat (M : Fin n → Fin n → ℕ∞) : (toWord M).length = 1 + n * (n + 1) := by
  rw [toWord_mat, length_matWord]

theorem length_toWord_distMatrix (G : PartialGraph (Fin n)) :
    (toWord (distMatrix G)).length = 1 + n * (n + 1) :=
  length_toWord_mat _

theorem getElem?_matWord_zero (f : Fin n → Fin n → ℕ) : (matWord n f)[0]? = some n := rfl

private theorem getElem?_matWord_aux (f : Fin n → Fin n → ℕ) (u : Fin n) (j : ℕ) (hj : j < n + 1) :
    (matWord n f)[1 + u * (n + 1) + j]? = (n :: List.ofFn fun v => f u v)[j]? := by
  unfold matWord
  rw [show 1 + u * (n + 1) + j = (u * (n + 1) + j) + 1 by ring, List.getElem?_cons_succ,
    getElem?_flatten_const (n + 1)]
  · simp
  · intro l hl
    simp only [List.mem_ofFn] at hl
    obtain ⟨u, rfl⟩ := hl
    simp
  · exact hj

/-- **The row header of row `u`** is at position `1 + u(n + 1)`. -/
theorem getElem?_matWord_head (f : Fin n → Fin n → ℕ) (u : Fin n) :
    (matWord n f)[1 + u * (n + 1)]? = some n := by
  have := getElem?_matWord_aux f u 0 (by omega)
  simpa using this

/-- **The entry `(u, v)`** is at position `2 + u(n + 1) + v`. -/
theorem getElem?_matWord (f : Fin n → Fin n → ℕ) (u v : Fin n) :
    (matWord n f)[2 + u * (n + 1) + v]? = some (f u v) := by
  have := getElem?_matWord_aux f u (v + 1) (by omega)
  rw [show 1 + u * (n + 1) + (v + 1) = 2 + u * (n + 1) + v by ring] at this
  rw [this, List.getElem?_cons_succ]
  simp

theorem getElem?_toWord_mat (M : Fin n → Fin n → ℕ∞) (u v : Fin n) :
    (toWord M)[2 + u * (n + 1) + v]? = some (dcode (M u v)) := by
  rw [toWord_mat, getElem?_matWord]

theorem getElem?_toWord_distMatrix (G : PartialGraph (Fin n)) (u v : Fin n) :
    (toWord (distMatrix G))[2 + u * (n + 1) + v]? = some (dcode (distMatrix G u v)) :=
  getElem?_toWord_mat _ u v

/-- Every position of the word of a matrix is the length header, a row
header or an entry. -/
theorem matWord_pos (i : ℕ) (hi : i < 1 + n * (n + 1)) :
    i = 0 ∨ (∃ u : Fin n, i = 1 + u * (n + 1)) ∨ ∃ u v : Fin n, i = 2 + u * (n + 1) + v := by
  rcases Nat.eq_zero_or_pos i with h | h
  · exact Or.inl h
  · right
    have hu : (i - 1) / (n + 1) < n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hd := Nat.div_add_mod (i - 1) (n + 1)
    have hm := Nat.mod_lt (i - 1) (show 0 < n + 1 by omega)
    rcases Nat.eq_zero_or_pos ((i - 1) % (n + 1)) with h0 | h0
    · left
      refine ⟨⟨(i - 1) / (n + 1), hu⟩, ?_⟩
      simp only
      rw [h0] at hd
      rw [Nat.mul_comm] at hd
      omega
    · right
      refine ⟨⟨(i - 1) / (n + 1), hu⟩, ⟨(i - 1) % (n + 1) - 1, by omega⟩, ?_⟩
      simp only
      rw [Nat.mul_comm] at hd
      omega

/-- **A word is the word of a matrix** if it has its length, its headers
and its entries. -/
theorem eq_matWord_iff (w : List ℕ) (f : Fin n → Fin n → ℕ) :
    w = matWord n f ↔ w.length = 1 + n * (n + 1) ∧ w[0]? = some n ∧
      (∀ u : Fin n, w[1 + u * (n + 1)]? = some n) ∧
      ∀ u v : Fin n, w[2 + u * (n + 1) + v]? = some (f u v) := by
  constructor
  · rintro rfl
    exact ⟨length_matWord f, getElem?_matWord_zero f, getElem?_matWord_head f,
      getElem?_matWord f⟩
  · rintro ⟨hl, h0, hh, he⟩
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 1 + n * (n + 1)
    · rcases matWord_pos i hi with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
      · rw [h0, getElem?_matWord_zero]
      · rw [hh, getElem?_matWord_head]
      · rw [he, getElem?_matWord]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [length_matWord]; omega)]

/-- The entries of the word of a matrix are the headers `n` and the
entries of the matrix. -/
theorem mem_matWord {f : Fin n → Fin n → ℕ} {e : ℕ} (h : e ∈ matWord n f) :
    e = n ∨ ∃ u v, e = f u v := by
  unfold matWord at h
  simp only [List.mem_cons, List.mem_flatten, List.mem_ofFn] at h
  rcases h with h | ⟨l, ⟨u, rfl⟩, h⟩
  · exact Or.inl h
  · simp only [List.mem_cons, List.mem_ofFn] at h
    rcases h with h | ⟨v, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨u, v, h.symm⟩

/-- **The entries of the word of `D_G` are at most `n`.** -/
theorem toWord_distMatrix_le (G : PartialGraph (Fin n)) :
    ∀ e ∈ toWord (distMatrix G), e ≤ n := by
  intro e he
  rw [toWord_distMatrix] at he
  rcases mem_matWord he with rfl | ⟨u, v, rfl⟩
  · exact le_rfl
  · exact dcode_distMatrix_le G u v

/-! ### Sizes -/

/-- **The size of a partial graph is at most `(n + 1)²`.** -/
theorem size_le_sq (G : PartialGraph (Fin n)) : G.size ≤ (n + 1) ^ 2 := by
  classical
  unfold PartialGraph.size
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.resolved)
  rw [Fintype.card_fin, Nat.choose_two_right] at h1
  have h2 : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
  have h3 : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  nlinarith

/-! ### Initial partial graphs and merges -/

/-- **`D_G` of a partial graph without resolved pairs.** -/
theorem distMatrix_of_bot (G : PartialGraph (Fin n)) (he : G.edge = ⊥) (hn : G.nonEdge = ⊥)
    (u v : Fin n) : distMatrix G u v = if u = v then 0 else ⊤ := by
  have : G.resolved = ⊥ := by rw [PartialGraph.resolved, he, hn, bot_sup_eq]
  unfold distMatrix
  rw [this, SimpleGraph.edist_bot]

theorem distMatrix_initial (G : PartialGraph (Fin n)) (h : IsInitial G) (u v : Fin n) :
    distMatrix G u v = if u = v then 0 else ⊤ :=
  distMatrix_of_bot G h.1 h.2.1 u v

theorem dcode_distMatrix_of_bot (G : PartialGraph (Fin n)) (he : G.edge = ⊥)
    (hn : G.nonEdge = ⊥) (u v : Fin n) :
    dcode (distMatrix G u v) = if u = v then 1 else 0 := by
  rw [distMatrix_of_bot G he hn]
  split_ifs
  · rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, dcode_coe]
  · exact dcode_top

/-- **A merge keeps `D_G`.** It changes only colors. -/
theorem distMatrix_merge (G : PartialGraph (Fin n)) (P Q : ℕ) :
    distMatrix (merge G P Q) = distMatrix G := rfl

/-! ### Distances to color classes -/

/-- The distance `dist^G(u, X)` from `u` to the color class `X`, and `∞`
if the class is empty. -/
noncomputable def distTo (G : PartialGraph (Fin n)) (u : Fin n) (X : ℕ) : ℕ∞ :=
  (Finset.univ.filter fun x => G.color x = X).inf (distMatrix G u)

/-- **Distances to a color class.** -/
theorem distTo_le_iff (G : PartialGraph (Fin n)) (u : Fin n) (X r : ℕ) :
    distTo G u X ≤ r ↔ NearC G u X r := by
  unfold distTo NearC
  rw [Finset.inf_le_iff (ENat.natCast_lt_top r)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, distMatrix_le_iff]

theorem distTo_eq_top_iff (G : PartialGraph (Fin n)) (u : Fin n) (X : ℕ) :
    distTo G u X = ⊤ ↔ ∀ x, G.color x = X → distMatrix G u x = ⊤ := by
  unfold distTo
  simp [Finset.inf_eq_top_iff]

theorem distTo_le (G : PartialGraph (Fin n)) (u x : Fin n) {X : ℕ} (hx : G.color x = X) :
    distTo G u X ≤ distMatrix G u x :=
  Finset.inf_le (by simp [hx])

/-- The distance from a color class `X` to a color class `Y`. -/
noncomputable def distCls (G : PartialGraph (Fin n)) (X Y : ℕ) : ℕ∞ :=
  (Finset.univ.filter fun y => G.color y = Y).inf fun y => distTo G y X

theorem distCls_le_iff (G : PartialGraph (Fin n)) (X Y r : ℕ) :
    distCls G X Y ≤ r ↔
      ∃ x y : Fin n, G.color x = X ∧ G.color y = Y ∧ WithinDist G.resolved r x y := by
  unfold distCls
  rw [Finset.inf_le_iff (ENat.natCast_lt_top r)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, distTo_le_iff, NearC]
  constructor
  · rintro ⟨y, hy, x, hx, h⟩
    exact ⟨x, y, hx, hy, withinDist_symm h⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨y, hy, x, hx, withinDist_symm h⟩

/-- `distCls G X Y` is the least `distTo G y X` over the vertices `y` of
color `Y`. -/
theorem distCls_le (G : PartialGraph (Fin n)) (X : ℕ) (y : Fin n) {Y : ℕ} (hy : G.color y = Y) :
    distCls G X Y ≤ distTo G y X :=
  Finset.inf_le (f := fun y => distTo G y X) (by simp [hy])

open Classical in
/-- **The table of class distances.** One more than the least `s` such
that a vertex of color `X` is within distance `s` of a vertex of color
`Y`, and `0` if there is none, is the code of `distCls G X Y`. -/
theorem find_eq_dcode_distCls (G : PartialGraph (Fin n)) (X Y : ℕ) :
    (if h : ∃ s, ∃ x y : Fin n, G.color x = X ∧ G.color y = Y ∧ WithinDist G.resolved s x y then
      Nat.find h + 1 else 0) = dcode (distCls G X Y) :=
  code_eq_find fun s => distCls_le_iff G X Y s

/-! ### Distances after a resolve (eq:resolve-dist) -/

/-- `0` if some vertex has color `X`, and `∞` otherwise. -/
noncomputable def occ (G : PartialGraph (Fin n)) (X : ℕ) : ℕ∞ :=
  open Classical in if ∃ x, G.color x = X then 0 else ⊤

theorem occ_eq_zero (G : PartialGraph (Fin n)) {X : ℕ} (h : ∃ x, G.color x = X) : occ G X = 0 := by
  unfold occ; rw [if_pos h]

theorem occ_eq_top (G : PartialGraph (Fin n)) {X : ℕ} (h : ¬ ∃ x, G.color x = X) : occ G X = ⊤ := by
  unfold occ; rw [if_neg h]

/-- An empty color class is at distance `∞`. -/
theorem distTo_of_empty (G : PartialGraph (Fin n)) (u : Fin n) {X : ℕ}
    (h : ¬ ∃ x, G.color x = X) : distTo G u X = ⊤ := by
  rw [distTo_eq_top_iff]
  intro x hx
  exact absurd ⟨x, hx⟩ h

theorem resolved_resolveBy (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    (resolveBy G s P Q).resolved = G.resolved ⊔ between G P Q := by
  cases s
  · exact resolved_resolveNeg G P Q
  · exact resolved_resolvePos G P Q

/-- The bound `a + c + b ≤ r` in `ℕ∞`, split over natural numbers. -/
theorem add_add_le_iff {a b : ℕ∞} {c r : ℕ} :
    a + c + b ≤ r ↔ ∃ s₁ s₂ : ℕ, s₁ + c + s₂ ≤ r ∧ a ≤ s₁ ∧ b ≤ s₂ := by
  induction a using ENat.recTopCoe with
  | top =>
    rw [top_add, top_add]
    constructor
    · intro h; exact absurd (top_le_iff.1 h) (ENat.natCast_ne_top r)
    · rintro ⟨s₁, s₂, -, h1, -⟩; exact absurd (top_le_iff.1 h1) (ENat.natCast_ne_top s₁)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      rw [add_top]
      constructor
      · intro h; exact absurd (top_le_iff.1 h) (ENat.natCast_ne_top r)
      · rintro ⟨s₁, s₂, -, -, h2⟩; exact absurd (top_le_iff.1 h2) (ENat.natCast_ne_top s₂)
    | coe b =>
      constructor
      · intro h
        exact ⟨a, b, by exact_mod_cast h, le_rfl, le_rfl⟩
      · rintro ⟨s₁, s₂, hs, h1, h2⟩
        have h1' : a ≤ s₁ := by exact_mod_cast h1
        have h2' : b ≤ s₂ := by exact_mod_cast h2
        have : a + c + b ≤ r := by omega
        exact_mod_cast this

theorem add_one_add_le_iff {a b : ℕ∞} {r : ℕ} :
    a + 1 + b ≤ r ↔ ∃ s₁ s₂ : ℕ, s₁ + 1 + s₂ ≤ r ∧ a ≤ s₁ ∧ b ≤ s₂ := by
  have := add_add_le_iff (a := a) (b := b) (c := 1) (r := r)
  rwa [Nat.cast_one] at this

theorem add_two_add_le_iff {a b : ℕ∞} {r : ℕ} :
    a + 2 + b ≤ r ↔ ∃ s₁ s₂ : ℕ, s₁ + 2 + s₂ ≤ r ∧ a ≤ s₁ ∧ b ≤ s₂ := by
  have := add_add_le_iff (a := a) (b := b) (c := 2) (r := r)
  rwa [Nat.cast_ofNat] at this

theorem occ_le_iff (G : PartialGraph (Fin n)) (X : ℕ) (a : ℕ∞) (r : ℕ) :
    a + occ G X ≤ r ↔ a ≤ r ∧ ∃ x, G.color x = X := by
  by_cases h : ∃ x, G.color x = X
  · rw [occ_eq_zero G h, add_zero]; tauto
  · rw [occ_eq_top G h, add_top]
    simp only [top_le_iff, ENat.natCast_ne_top, false_iff, not_and]
    exact fun _ => h

/-- **Distances after a resolve**, for all colors `P` and `Q`. The terms
through two new pairs need a vertex of the other color, which `occ`
records. -/
theorem distMatrix_resolveBy (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) (u v : Fin n) :
    distMatrix (resolveBy G s P Q) u v =
      min (distMatrix G u v)
        (min (distTo G u P + 1 + distTo G v Q)
          (min (distTo G u Q + 1 + distTo G v P)
            (min (distTo G u P + 2 + distTo G v P + occ G Q)
              (distTo G u Q + 2 + distTo G v Q + occ G P)))) := by
  apply enat_eq_of_le_iff
  intro r
  rw [distMatrix_le_iff, resolved_resolveBy, withinDist_resolve_iff]
  simp only [min_le_iff, occ_le_iff, add_one_add_le_iff, add_two_add_le_iff, distTo_le_iff, distMatrix_le_iff, Hop,
    Occurs]
  constructor
  · rintro (h | ⟨s₁, s₂, h⟩)
    · exact Or.inl h
    · right
      rcases h with ⟨hs, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨hs, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
      · exact Or.inl ⟨s₁, s₂, hs, h1, h2⟩
      · exact Or.inr (Or.inl ⟨s₁, s₂, hs, h1, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨s₁, s₂, hs, h1, h2⟩, h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨s₁, s₂, hs, h1, h2⟩, h3⟩))
  · rintro (h | ⟨s₁, s₂, hs, h1, h2⟩ | ⟨s₁, s₂, hs, h1, h2⟩ | ⟨⟨s₁, s₂, hs, h1, h2⟩, h3⟩ |
        ⟨⟨s₁, s₂, hs, h1, h2⟩, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s₁, s₂, Or.inl ⟨hs, Or.inl ⟨h1, h2⟩⟩⟩
    · exact Or.inr ⟨s₁, s₂, Or.inl ⟨hs, Or.inr ⟨h1, h2⟩⟩⟩
    · exact Or.inr ⟨s₁, s₂, Or.inr ⟨hs, Or.inl ⟨h1, h2, h3⟩⟩⟩
    · exact Or.inr ⟨s₁, s₂, Or.inr ⟨hs, Or.inr ⟨h1, h2, h3⟩⟩⟩

/-- **eq:resolve-dist.** The distances after a resolve of two nonempty
color classes, as in the source. This includes `P = Q`. -/
theorem distMatrix_resolveBy_of_occurs (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ)
    (hP : ∃ x, G.color x = P) (hQ : ∃ x, G.color x = Q) (u v : Fin n) :
    distMatrix (resolveBy G s P Q) u v =
      min (distMatrix G u v)
        (min (distTo G u P + 1 + distTo G v Q)
          (min (distTo G u Q + 1 + distTo G v P)
            (min (distTo G u P + 2 + distTo G v P) (distTo G u Q + 2 + distTo G v Q)))) := by
  rw [distMatrix_resolveBy, occ_eq_zero G hP, occ_eq_zero G hQ, add_zero, add_zero]

/-- **A resolve with an empty color class keeps `D_G`.** -/
theorem distMatrix_resolveBy_of_empty (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ)
    (h : (¬ ∃ x, G.color x = P) ∨ ¬ ∃ x, G.color x = Q) (u v : Fin n) :
    distMatrix (resolveBy G s P Q) u v = distMatrix G u v := by
  rw [distMatrix_resolveBy]
  rcases h with h | h
  · simp [distTo_of_empty G _ h, occ_eq_top G h]
  · simp [distTo_of_empty G _ h, occ_eq_top G h]

end Lax185574Proofs.DistMatrix
