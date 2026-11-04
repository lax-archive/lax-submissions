import Lax185574Proofs.StpRam.GlueOk
import Lax185574Proofs.StpRam.Bounds

/-!
The script of the composite of lem:compute-stp.

The input is the word `x` of `(G, k, q, D_G, (tree_{k,q}(a))_a)`. With
`Q = q · n`, the glue program writes in round `t ≤ Q` the state
`stS t` after `t` answers and asks for the shift of entry `idxS t` of
the list `F ++ A` of the family trees and the shifted trees: entry `t`
for `t < Q`, and the first family tree again for `t = Q`, a dummy call
after which all answers are in the state. Round `Q + 1` is the final
round. `Ao t` and `Bo t` are the outputs of the glue program and of
the rank shift before round `t`.

The rounds are stated for the compiled glue program at any word length
`v` with room for the value bound `vB`, a constant in `k, q` times the
cube of `|x| + max x + 1`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs
open Lax185574.ScatterTypes Lax185574.PartialGraphEncoding Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

variable {n : ℕ}

/-- The compiled glue program. -/
def gProg : Program := compileProgram layout glue

/-- The size factor of the layout. -/
def gsz : ℕ := layout.temps + 2 + layout.scalars.length + layout.arrays.length + 1

theorem gsz_eq : gsz = 112 := rfl

section
variable (G : PartialGraph (Fin n)) (k q : ℕ)

/-- The input. -/
noncomputable def xIn : List ℕ := toWord (G, k, q, distMatrix G, family G k q)

theorem xIn_eq : xIn G k q =
    (toWord G ++ [k, q]) ++ toWord (distMatrix G) ++ toWord (family G k q) := by
  simp [xIn, word_simps]

/-- The length of the window of the final round: the graph, `k`, `q` and
the distance matrix. -/
noncomputable def glW : ℕ := (toWord G).length + 2 + (toWord (distMatrix G)).length

/-- The words of the family trees. -/
noncomputable def famF : List (List ℕ) := famW (family G k q)

/-- The state after `t` answers. -/
noncomputable def stS (t : ℕ) : List ℕ :=
  stState n k q t (glW G) (famF G k q) ((answers G k q).take t)

/-- The index of the query of round `t`. -/
def idxS (Q t : ℕ) : ℕ := if t < Q then t else 0

/-- The tag of the output of round `t`. -/
def tagS (Q t : ℕ) : ℕ := if t < Q then 1 else 2

/-- The window of the output of round `t`. -/
def winS (Q gl t : ℕ) : ℕ := if t < Q then 0 else gl

/-- The query of round `t`. -/
noncomputable def qryS (t : ℕ) : List ℕ := (famF G k q ++ answers G k q).getD (idxS (q * n) t) []

/-- The answer to the query of round `t`. -/
noncomputable def ansS (t : ℕ) : List ℕ := (answers G k q).getD (idxS (q * n) t) []

/-- The outputs of the glue program, before round `t`. -/
noncomputable def Ao : ℕ → List ℕ
  | 0 => lpA0 (xIn G k q)
  | t + 1 => [tagS (q * n) t, (stS G k q t).length, winS (q * n) (glW G) t] ++ stS G k q t ++
      qryS G k q t

/-- The answers of the rank shift, before round `t`. -/
noncomputable def Bo : ℕ → List ℕ
  | 0 => []
  | t + 1 => ansS G k q t

/-- The bound of the radii. -/
def rK (k q : ℕ) : ℕ := radius k q 0 + radius k q 1 + 10

/-- The bound of the values of the glue program. -/
noncomputable def vB : ℕ :=
  64 * (rK k q + 1) * ((xIn G k q).length + maxEntry (xIn G k q) + 1) ^ 3

end

/-! ### The input and the output of the driver -/

theorem lpU_round (x S' Qr b : List ℕ) (tg w : ℕ) :
    lpU x ([tg, (0 :: S').length, w] ++ (0 :: S') ++ Qr) b =
      [tg, (0 :: S').length] ++ x.take w ++ (0 :: S') ++ (b.length :: b) := by
  simp [lpU]

theorem lpQ_round (S Qr : List ℕ) (tg w : ℕ) : lpQ ([tg, S.length, w] ++ S ++ Qr) = Qr := by
  simp only [lpQ, List.getD_eq_getElem?_getD, List.append_assoc, List.cons_append, List.nil_append]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [show 3 + S.length = (S.length + 3) by omega, ← List.drop_drop]
  simp

theorem stS_cons (G : PartialGraph (Fin n)) (k q t : ℕ) :
    stS G k q t = 0 :: ([n, k, q, t, glW G] ++ toWord (famF G k q) ++ toWord ((answers G k q).take t)) := by
  simp [stS, stState]

/-! ### Sizes of the input -/

section
variable (G : PartialGraph (Fin n)) (k q : ℕ)

theorem le_maxTreeSize (v : Fin n) : (toWord (family G k q v)).length ≤ maxTreeSize G k q :=
  Finset.le_sup (f := fun a : Fin n => wordLength (family G k q a)) (Finset.mem_univ v)

theorem length_famF : (famF G k q).length = n := length_famW _

theorem length_toWord_famF :
    (toWord (famF G k q)).length = (toWord (family G k q)).length + n := length_toWord_famW _

theorem mem_toWord_family {v : Fin n} {y : ℕ} (h : y ∈ toWord (family G k q v)) :
    y ∈ toWord (family G k q) := by
  rw [toWord_fam]
  exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, by rw [famW, List.mem_ofFn]; exact ⟨v, rfl⟩, h⟩)

theorem length_le_toWord_family (v : Fin n) :
    (toWord (family G k q v)).length + 1 ≤ (toWord (family G k q)).length := by
  rw [toWord_fam]
  have hm : toWord (family G k q v) ∈ famW (family G k q) := by
    rw [famW, List.mem_ofFn]; exact ⟨v, rfl⟩
  have := (List.infix_of_mem_flatten hm).length_le
  simp only [List.length_cons]; omega

theorem maxTreeSize_le : maxTreeSize G k q + 1 ≤ (toWord (family G k q)).length + 1 := by
  have : maxTreeSize G k q ≤ (toWord (family G k q)).length := by
    apply Finset.sup_le
    intro v _
    have := length_le_toWord_family G k q v
    simp only [wordLength]; omega
  omega

theorem n_le_toWord_family : n + 1 ≤ (toWord (family G k q)).length := by
  have h1 : ∀ u ∈ famW (family G k q), 1 ≤ u.length := by
    intro u hu; rw [famW, List.mem_ofFn] at hu; obtain ⟨v, rfl⟩ := hu; rw [toWord_typeTree]; simp
  have h2 : ∀ l : List (List ℕ), (∀ u ∈ l, 1 ≤ u.length) → l.length ≤ (l.map List.length).sum := by
    intro l; induction l with
    | nil => simp
    | cons u l ih => intro h; simp only [List.length_cons, List.map_cons, List.sum_cons]
                     have := h u (by simp); have := ih (fun v hv => h v (by simp [hv])); omega
  have := h2 _ h1
  rw [length_famW] at this
  rw [toWord_fam]; simp [List.length_flatten]; omega

end

theorem offL_le_sq (H : SimpleGraph (Fin n)) : ∀ v, offL H v ≤ v * n := by
  intro v
  induction v with
  | zero => simp [offL]
  | succ v ih =>
    rw [offL_succ]
    have := length_nbrL_le H v
    nlinarith

/-- The basic sizes, in terms of `X = |x| + max x + 1`. -/
structure Sizes (G : PartialGraph (Fin n)) (k q X : ℕ) : Prop where
  one : 1 ≤ X
  nX : n + 1 ≤ X
  len : (toWord G).length + 2 + (toWord (distMatrix G)).length + (toWord (family G k q)).length + 1 ≤ X
  ent : ∀ v ∈ xIn G k q, v + 1 ≤ X
  kX : k + 1 ≤ X
  qX : q + 1 ≤ X
  LX : maxTreeSize G k q + 1 ≤ X
  famL : ∀ v : Fin n, (toWord (family G k q v)).length ≤ maxTreeSize G k q
  famE : ∀ v : Fin n, ∀ y ∈ toWord (family G k q v), y + 1 ≤ X
  ansL : ∀ u ∈ answers G k q, u.length ≤ maxTreeSize G k q
  ansE : ∀ u ∈ answers G k q, ∀ y ∈ u, y < 3 * X
  QX : q * n ≤ X ^ 2
  totA : total (answers G k q) ≤ X ^ 3
  twA : (toWord (answers G k q)).length ≤ 3 * X ^ 3
  offE : offL G.edge n ≤ X ^ 2
  offN : offL G.nonEdge n ≤ X ^ 2

theorem sizes (G : PartialGraph (Fin n)) (k q : ℕ) :
    Sizes G k q ((xIn G k q).length + maxEntry (xIn G k q) + 1) := by
  set N := (xIn G k q).length with hN
  set M := maxEntry (xIn G k q) with hM
  have hx := xIn_eq G k q
  have hNl : N = (toWord G).length + 2 + (toWord (distMatrix G)).length +
      (toWord (family G k q)).length := by
    rw [hN, hx]; simp; omega
  have hmem : ∀ v ∈ xIn G k q, v ≤ M := fun v hv => le_maxEntry hv
  have hk : k ≤ M := hmem k (by rw [hx]; simp)
  have hq : q ≤ M := hmem q (by rw [hx]; simp)
  have hfe : ∀ v : Fin n, ∀ y ∈ toWord (family G k q v), y ≤ M := fun v y hy =>
    hmem y (by rw [hx]; exact List.mem_append_right _ (mem_toWord_family G k q hy))
  have hL := maxTreeSize_le G k q
  have hnf := n_le_toWord_family G k q
  have hfamL := le_maxTreeSize G k q
  set L := maxTreeSize G k q with hLd
  set X := N + M + 1 with hX
  have hans := answers_bound G k q L (3 * X) hfamL (fun v y hy => by have := hfe v y hy; omega)
    (by omega) (by omega)
  have hQ : q * n ≤ X ^ 2 := by
    have : q * n ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have htot : total (answers G k q) ≤ X ^ 3 := by
    have h1 := total_le (answers G k q) L (fun u hu => (hans u hu).1)
    rw [length_answers] at h1
    have : q * n * L ≤ X ^ 2 * X := Nat.mul_le_mul hQ (by omega)
    nlinarith
  have hX1 : 1 ≤ X := by omega
  refine ⟨hX1, by omega, by omega, fun v hv => by have := hmem v hv; omega, by omega, by omega, by omega,
    hfamL, fun v y hy => by have := hfe v y hy; omega, fun u hu => (hans u hu).1,
    fun u hu => (hans u hu).2, hQ, htot, ?_, ?_, ?_⟩
  · rw [length_toWord_words, length_answers]
    have : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
    have : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have := offL_le_sq G.edge n
    have : n * n ≤ X ^ 2 := by nlinarith
    omega
  · have := offL_le_sq G.nonEdge n
    have : n * n ≤ X ^ 2 := by nlinarith
    omega

end Lax185574Proofs.StpRam
