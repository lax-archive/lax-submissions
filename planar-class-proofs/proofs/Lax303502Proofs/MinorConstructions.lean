import Lax303502Proofs.CircularMinors
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace Lax303502Proofs

open Lax68.GraphMinors

theorem connected_image {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {S : Set V} (hS : (G.induce S).Connected) :
    (H.induce (f '' S)).Connected := by
  let g : G.induce S →g H.induce (f '' S) :=
    ⟨fun x => ⟨f x,⟨x,x.property,rfl⟩⟩,fun h => f.map_rel h⟩
  apply hS.map g
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

noncomputable def MinorModel.mapEmbedding {U V W : Type*}
    {K : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel K G) (f : G →g H) (hi : Function.Injective f) : MinorModel K H where
  branchSet v := f '' M.branchSet v
  connected v := connected_image f (M.connected v)
  disjoint := by
    intro a b hab
    rw [Set.disjoint_left]
    rintro x ⟨v,hv,rfl⟩ ⟨w,hw,he⟩
    have he' := hi he
    subst w
    exact Set.disjoint_left.mp (M.disjoint hab) hv hw
  adjacent := by
    intro a b hab
    obtain ⟨v,hv,w,hw,hvw⟩ := M.adjacent hab
    exact ⟨f v,⟨v,hv,rfl⟩,f w,⟨w,hw,rfl⟩,f.map_rel hvw⟩

theorem excludedMinors_induce {V : Type*} {G : SimpleGraph V}
    (hG : Lax68.Outerplanar.IsOuterplanarByExcludedMinors G) (S : Set V) :
    Lax68.Outerplanar.IsOuterplanarByExcludedMinors (G.induce S) := by
  constructor
  · rintro ⟨M⟩
    exact hG.1 ⟨MinorModel.mapEmbedding M (SimpleGraph.Embedding.induce S).toHom Subtype.val_injective⟩
  · rintro ⟨M⟩
    exact hG.2 ⟨MinorModel.mapEmbedding M (SimpleGraph.Embedding.induce S).toHom Subtype.val_injective⟩

def intervalVertices {V : Type*} (f : ℕ → V) (l r : ℕ) : Set V := f '' Set.Icc l r

theorem mem_intervalVertices {V : Type*} {f : ℕ → V} {l r i : ℕ}
    (hl : l ≤ i) (hr : i ≤ r) : f i  ∈  intervalVertices f l r := ⟨i,⟨hl,hr⟩,rfl⟩

theorem intervalVertices_connected {V : Type*} {G : SimpleGraph V} (f : ℕ → V)
    {l r : ℕ} (hlr : l ≤ r) (hedge : ∀ i, l ≤ i → i < r → G.Adj (f i) (f (i+1))) :
    (G.induce (intervalVertices f l r)).Connected := by
  let a : intervalVertices f l r := ⟨f l,mem_intervalVertices le_rfl hlr⟩
  have reach (i : ℕ) (hli : l ≤ i) (hir : i ≤ r) :
      (G.induce (intervalVertices f l r)).Reachable a ⟨f i,mem_intervalVertices hli hir⟩ := by
    induction i,hli using Nat.le_induction with
    | base => exact .rfl
    | succ i hi ih =>
      exact (ih (by omega)).trans (SimpleGraph.Adj.reachable (hedge i hi (by omega)))
  have : Nonempty (intervalVertices f l r) := ⟨a⟩
  refine ⟨?_⟩
  rintro ⟨x,i,hi,rfl⟩ ⟨y,j,hj,rfl⟩
  exact (reach i hi.1 hi.2).symm.trans (reach j hj.1 hj.2)

/-- Three disjoint connected sets attached to each of two separate vertices
give the branch sets of a `K₂,₃` minor. -/
noncomputable def theta_minor {V : Type*} {G : SimpleGraph V} {a b : V} (hab : a ≠ b)
    (S : Fin 3 → Set V) (hconn : ∀ i, (G.induce (S i)).Connected)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (ha : ∀ i, a ∉ S i) (hb : ∀ i, b ∉ S i)
    (ea : ∀ i, ∃ x ∈ S i, G.Adj a x) (eb : ∀ i, ∃ x ∈ S i, G.Adj b x) :
    MinorModel K23 G := by
  classical
  let B : Fin 2 ⊕ Fin 3 → Set V := Sum.elim (fun i => if i=0 then {a} else {b}) S
  refine ⟨B,?_,?_,?_⟩
  · intro i
    rcases i with i | i
    · fin_cases i <;> simp [B]
    · exact hconn i
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;> simp_all [B,Set.disjoint_left, ne_comm]
    · fin_cases i
      · simpa [B, Set.disjoint_left] using ha j
      · simpa [B, Set.disjoint_left] using hb j
    · fin_cases j
      · simpa [B, Set.disjoint_right] using ha i
      · simpa [B, Set.disjoint_right] using hb i
    · exact hdisj (by simpa using hij)
  · intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · simp at hij
    · fin_cases i
      · obtain ⟨x,hx,he⟩ := ea j
        exact ⟨a,by simp [B],x,hx,he⟩
      · obtain ⟨x,hx,he⟩ := eb j
        exact ⟨b,by simp [B],x,hx,he⟩
    · fin_cases j
      · obtain ⟨x,hx,he⟩ := ea i
        exact ⟨x,hx,a,by simp [B],he.symm⟩
      · obtain ⟨x,hx,he⟩ := eb i
        exact ⟨x,hx,b,by simp [B],he.symm⟩
    · simp at hij


theorem intervalVertices_disjoint {V : Type*} {f : ℕ → V} {n l r l' r' : ℕ}
    (hi : Set.InjOn f (Set.Iio n)) (hr : r < n) (hr' : r' < n) (hgap : r < l') :
    Disjoint (intervalVertices f l r) (intervalVertices f l' r') := by
  rw [Set.disjoint_left]
  rintro x ⟨i,hi',rfl⟩ ⟨j,hj,hij⟩
  have := hi (by exact lt_of_le_of_lt hi'.2 hr) (by exact lt_of_le_of_lt hj.2 hr') hij.symm
  have := hi'.2
  have := hj.1
  omega

theorem not_mem_intervalVertices {V : Type*} {f : ℕ → V} {n l r k : ℕ}
    (hi : Set.InjOn f (Set.Iio n)) (hr : r < n) (hk : k < n) (h : k < l ∨ r < k) :
    f k ∉ intervalVertices f l r := by
  rintro ⟨i,hi',he⟩
  have := hi (by exact lt_of_le_of_lt hi'.2 hr) hk he
  have := hi'.1
  have := hi'.2
  omega

/-- A cycle with a connected set outside it attached at nonconsecutive vertices
contains the three connected branches of a `K₂,₃` minor. -/
noncomputable def cycle_theta_minor {V : Type*} {G : SimpleGraph V}
    (f : ℕ → V) {n j : ℕ} (hi : Set.InjOn f (Set.Iio n))
    (hedge : ∀ i < n, G.Adj (f i) (f (i+1))) (hclose : f n = f 0)
    (hj : 2 ≤ j) (hjn : j+2 ≤ n) (T : Set V) (hT : (G.induce T).Connected)
    (hout : ∀ i < n, f i ∉ T)
    (ea : ∃ x ∈ T, G.Adj (f 0) x) (eb : ∃ x ∈ T, G.Adj (f j) x) :
    MinorModel K23 G := by
  let S : Fin 3 → Set V := ![intervalVertices f 1 (j-1), intervalVertices f (j+1) (n-1), T]
  have hzero : 0 < n := by omega
  have hjn' : j < n := by omega
  have hdis : Disjoint (intervalVertices f 1 (j-1)) (intervalVertices f (j+1) (n-1)) :=
    intervalVertices_disjoint hi (by omega) (by omega) (by omega)
  have hdisT {l r : ℕ} (hr : r < n) : Disjoint (intervalVertices f l r) T := by
    rw [Set.disjoint_left]
    rintro x ⟨i,hi',rfl⟩ hx
    exact hout i (lt_of_le_of_lt hi'.2 hr) hx
  apply theta_minor (a:=f 0) (b:=f j) (fun he => by have := hi hzero hjn' he; omega) S
  · intro i
    fin_cases i
    · exact intervalVertices_connected f (by omega) (fun i _ h => hedge i (by omega))
    · exact intervalVertices_connected f (by omega) (fun i _ h => hedge i (by omega))
    · exact hT
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp only [S] <;>
      first | exact False.elim (hik rfl) | exact hdis | exact hdis.symm |
        exact hdisT (by omega) | exact (hdisT (by omega)).symm
  · intro i
    fin_cases i
    · exact not_mem_intervalVertices hi (by omega) hzero (Or.inl (by omega))
    · exact not_mem_intervalVertices hi (by omega) hzero (Or.inl (by omega))
    · exact hout 0 hzero
  · intro i
    fin_cases i
    · exact not_mem_intervalVertices hi (by omega) hjn' (Or.inr (by omega))
    · exact not_mem_intervalVertices hi (by omega) hjn' (Or.inl (by omega))
    · exact hout j hjn'
  · intro i
    fin_cases i
    · exact ⟨f 1, mem_intervalVertices le_rfl (by omega), hedge 0 hzero⟩
    · refine ⟨f (n-1), mem_intervalVertices (by omega) le_rfl, ?_⟩
      have he := (hedge (n-1) (by omega)).symm
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), hclose] using he
    · exact ea
  · intro i
    fin_cases i
    · refine ⟨f (j-1), mem_intervalVertices (by omega) le_rfl, ?_⟩
      have he := (hedge (j-1) (by omega)).symm
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using he
    · exact ⟨f (j+1), mem_intervalVertices le_rfl (by omega), hedge j hjn'⟩
    · exact eb

/-- Six adjacent pairs of disjoint connected branch sets give a `K₄` minor. -/
noncomputable def four_minor {V : Type*} {G : SimpleGraph V}
    (S : Fin 4 → Set V) (hconn : ∀ i, (G.induce (S i)).Connected)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hedge : ∀ i j, i < j → ∃ x ∈ S i, ∃ y ∈ S j, G.Adj x y) : MinorModel K4 G := by
  refine ⟨S,hconn,fun {i j} h => hdisj h,?_⟩
  intro i j hij
  have hn : i ≠ j := hij.ne
  rcases lt_or_gt_of_ne hn with h | h
  · exact hedge i j h
  · obtain ⟨x,hx,y,hy,he⟩ := hedge j i h
    exact ⟨y,hy,x,hx,he.symm⟩


/-- Alternating chords of a cycle supply the two diagonals of a `K₄` minor. -/
noncomputable def cycle_four_minor {V : Type*} {G : SimpleGraph V}
    (f : ℕ → V) {n a b c d : ℕ} (hi : Set.InjOn f (Set.Iio n))
    (hedge : ∀ i < n, G.Adj (f i) (f (i+1))) (hclose : f n = f 0)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdn : d < n)
    (hac : G.Adj (f a) (f c)) (hbd : G.Adj (f b) (f d)) : MinorModel K4 G := by
  let S : Fin 4 → Set V := ![intervalVertices f 0 a, intervalVertices f (a+1) b,
    intervalVertices f (b+1) c, intervalVertices f (c+1) (n-1)]
  apply four_minor S
  · intro i
    fin_cases i <;> apply intervalVertices_connected f (by omega) <;>
      intro i _ h <;> exact hedge i (by omega)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · fin_cases i <;> fin_cases j <;> try { norm_num at h }
      all_goals apply intervalVertices_disjoint hi <;> omega
    · apply Disjoint.symm
      fin_cases i <;> fin_cases j <;> try { norm_num at h }
      all_goals apply intervalVertices_disjoint hi <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try { norm_num at hij }
    · exact ⟨f a, mem_intervalVertices (by omega) le_rfl,
        f (a+1), mem_intervalVertices le_rfl (by omega), hedge a (by omega)⟩
    · exact ⟨f a, mem_intervalVertices (by omega) le_rfl,
        f c, mem_intervalVertices (by omega) le_rfl, hac⟩
    · refine ⟨f 0, mem_intervalVertices le_rfl (by omega),
        f (n-1), mem_intervalVertices (by omega) le_rfl, ?_⟩
      have he := (hedge (n-1) (by omega)).symm
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), hclose] using he
    · exact ⟨f b, mem_intervalVertices (by omega) le_rfl,
        f (b+1), mem_intervalVertices le_rfl (by omega), hedge b (by omega)⟩
    · exact ⟨f b, mem_intervalVertices (by omega) le_rfl,
        f d, mem_intervalVertices (by omega) (by omega), hbd⟩
    · exact ⟨f c, mem_intervalVertices (by omega) le_rfl,
        f (c+1), mem_intervalVertices le_rfl (by omega), hedge c (by omega)⟩

end Lax303502Proofs
