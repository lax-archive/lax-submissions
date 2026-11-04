import Lax185574Proofs.RamPipeBack
import Lax185574Proofs.RamLower
import Lax185574Proofs.Interface.NbrToCsr
import Lax185574Proofs.Compose.CsrToGraph
import Lax185574Proofs.Compose.WordBounds

/-!
Converting a part of the input before running a program.

`pipe_conv` is the pipe of a converter `R` into a program `P`, for an
input on which the converter has a known run. The pipe halts whenever
`P` halts on the converted input, and every halting run of the pipe
comes from a halting run of `P` on the converted input. So the pipe
inherits both clauses of a statement about computing from `P`.

`nbr_bridge` and `csr_bridge` specialise this to the two converters
between the word of a graph and its compressed sparse row word. The
input is a prefix of fixed length `k`, the graph word and a rest. The
converter runs on the graph word, and the program runs on the prefix,
the converted graph word and the rest. Both bridges are stated for word
lengths at which the input is small compared with the word size.
-/

namespace Lax185574Proofs.Interface

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax808846Proofs.Compile Lax185574Proofs.Words Lax185574.WordEncoding
open Lax271696.GraphEncoding Lax185574Proofs.Compose Lax808846Proofs.Reasoning

/-- **A converter with a known run, followed by a program.** -/
theorem pipe_conv (R P : Program) (ρ : Rewrite 1) (ρ' : Rewrite 2) : ∃ (p : Program) (K : ℕ),
    ∀ (w : ℕ) (x y : List ℕ) (t₁ : ℕ), K ≤ 2 ^ (w - 2) → ρ.Fits w (fun _ => x) →
      y.length < 2 ^ (w - 2) → ρ'.Fits w ![y, x] →
      RunsTo (w - 2) R (ρ.apply fun _ => x) y t₁ →
      (∀ z t₂, RunsTo (w - 2) P (ρ'.apply ![y, x]) z t₂ →
        ∃ t ≤ K * (t₁ + t₂ + ρ.cost (fun _ => x) + ρ'.cost ![y, x]), RunsTo w p x z t) ∧
      (∀ z T, RunsTo w p x z T → ∃ t₂ ≤ T, RunsTo (w - 2) P (ρ'.apply ![y, x]) z t₂) := by
  obtain ⟨p, K, hp⟩ := pipe_sound R P ρ ρ'
  refine ⟨p, K, fun w x y t₁ hK hfit hy hfit' h₁ => ?_⟩
  obtain ⟨hf, hb⟩ := hp w x hK hfit
  refine ⟨fun z t₂ h₂ => hf y z t₁ t₂ hy.le hfit' h₁ h₂, fun z T h => ?_⟩
  obtain ⟨y', t₁', -, -, h₁', h₂'⟩ := hb z T h
  obtain ⟨rfl, -⟩ := runsTo_unique h₁' h₁
  exact h₂' hfit'

theorem two_pow_four {w : ℕ} (h : 4 ≤ 2 ^ w) : 2 ^ w = 4 * 2 ^ (w - 2) := by
  have hw : 2 ≤ w := by
    by_contra hw
    have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega

/-! ### From neighbor lists to compressed sparse rows -/

/-- The part of the input after the prefix. -/
def dropRw (k : ℕ) : Rewrite 1 := [.slice 0 (.lit k) none]

/-- The prefix, the converted graph word and the rest: from `![y, x]`
with `y = |g| :: y'`, the word `x.take k ++ y' ++ x.drop (k + |g|)`. -/
def nbrRw (k : ℕ) : Rewrite 2 :=
  [.slice 1 (.lit 0) (some (.lit k)), .slice 0 (.lit 1) none,
    .slice 1 (.add (.lit k) (.entry 0 0)) none]

theorem dropRw_apply (k : ℕ) (x : List ℕ) : (dropRw k).apply (fun _ => x) = x.drop k := by
  simp [dropRw, Rewrite.apply, Segment.apply, HExpr.eval]

theorem dropRw_cost (k : ℕ) (x : List ℕ) : (dropRw k).cost (fun _ => x) = 3 := by
  simp [dropRw, Rewrite.cost, Segment.cost, HExpr.cost]

theorem dropRw_fits {w k : ℕ} {x : List ℕ} (hx : x.length < 2 ^ w) (hk : k < 2 ^ w) :
    (dropRw k).Fits w (fun _ => x) := by
  refine ⟨fun _ => hx, ?_, ?_⟩
  · rw [dropRw_apply]; simp; omega
  · intro seg hs
    simp only [dropRw, List.mem_singleton] at hs
    subst hs
    exact ⟨trivial, by simpa [HExpr.eval] using hk⟩

theorem nbrRw_apply (k : ℕ) (y x : List ℕ) :
    (nbrRw k).apply ![y, x] = x.take k ++ y.drop 1 ++ x.drop (k + y.getD 0 0) := by
  simp [nbrRw, Rewrite.apply, Segment.apply, HExpr.eval]

theorem nbrRw_cost (k : ℕ) (y x : List ℕ) : (nbrRw k).cost ![y, x] = 10 := by
  simp [nbrRw, Rewrite.cost, Segment.cost, HExpr.cost]

theorem nbrRw_fits {w k : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ w) (hx : x.length < 2 ^ w)
    (h1 : 1 < 2 ^ w) (hk : k + y.getD 0 0 < 2 ^ w)
    (hr : ((nbrRw k).apply ![y, x]).length < 2 ^ w) :
    (nbrRw k).Fits w ![y, x] := by
  refine ⟨fun i => ?_, hr, ?_⟩
  · fin_cases i <;> simpa
  · intro seg hs
    simp only [nbrRw, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨trivial, by show 0 < 2 ^ w; omega, trivial, by show k < 2 ^ w; omega⟩
    · exact ⟨trivial, by show 1 < 2 ^ w; omega⟩
    · exact ⟨⟨trivial, by show 0 < 2 ^ w; omega⟩, by simpa [HExpr.eval] using hk⟩

theorem length_csrWord (ls : List (List ℕ)) :
    (csrWord ls).length = 3 + ls.length + ls.flatten.length := by
  simp only [csrWord, List.length_cons, List.length_append, length_arrOf]; omega

/-- The pipe `q` runs `p` on the input after converting the word of
neighbor lists behind a prefix of length `k` into compressed sparse
rows, with the constant `K`. -/
def NbrBridge (k : ℕ) (p q : Program) (K : ℕ) : Prop :=
    ∀ (w : ℕ) (P R : List ℕ) (ls : List (List ℕ)), P.length = k →
      K * ((P ++ nbWord ls ++ R).length + (P ++ nbWord ls ++ R).sum + 1) ≤ 2 ^ w →
      (∀ z t₂, RunsTo (w - 2) p (P ++ csrWord ls ++ R) z t₂ →
        ∃ t ≤ K * (t₂ + (P ++ nbWord ls ++ R).length + 1), RunsTo w q (P ++ nbWord ls ++ R) z t) ∧
      (∀ z T, RunsTo w q (P ++ nbWord ls ++ R) z T →
        ∃ t₂ ≤ T, RunsTo (w - 2) p (P ++ csrWord ls ++ R) z t₂)

/-- **Neighbor lists to compressed sparse rows after a prefix.** -/
theorem nbr_bridge (k : ℕ) (p : Program) : ∃ (q : Program) (K : ℕ), NbrBridge k p q K := by
  obtain ⟨q, K, hq⟩ := pipe_conv (compileProgram nbrLayout nbrToCsr) p (dropRw k) (nbrRw k)
  refine ⟨q, 1000 * K + 1000, fun w P R ls hP hw => ?_⟩
  set g := nbWord ls with hg
  set x := P ++ g ++ R with hx
  set y := g.length :: csrWord ls with hy
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x.length + x.sum + 1 := ⟨_, rfl⟩
  rw [← hZ] at hw
  have hZ1 : 1 ≤ Z := by omega
  have hKZ : (1000 * K + 1000) * 1 ≤ (1000 * K + 1000) * Z := Nat.mul_le_mul_left _ hZ1
  have h4 := two_pow_four (w := w) (by omega)
  set V := 2 ^ (w - 2) with hV
  have hgl := length_nbWord ls
  rw [← hg] at hgl
  have hcl := length_csrWord ls
  have hxl : x.length = k + g.length + R.length := by
    simp only [hx, List.length_append, hP]
  have hKZ' : 250 * (K + 1) * Z ≤ V := by
    have : (1000 * K + 1000) * Z = 4 * (250 * (K + 1) * Z) := by ring
    omega
  have hZV : 250 * Z ≤ V := le_trans (Nat.mul_le_mul_right _ (by nlinarith)) hKZ'
  have hKV : K ≤ V := by
    have : K * 1 ≤ 250 * (K + 1) * Z := Nat.mul_le_mul (by omega) hZ1
    omega
  -- the converter
  have hdrop : x.drop k = g ++ R := by
    rw [hx, List.append_assoc, List.drop_left' hP]
  have hM : maxEntry (g ++ R) ≤ x.sum := by
    by_cases hgr : g ++ R = []
    · rw [hgr]; simp [maxEntry]
    · refine le_trans (List.le_sum_of_mem (maxEntry_mem hgr)) ?_
      simp only [hx, List.sum_append]; omega
  have hgRl : (g ++ R).length ≤ x.length := by rw [hxl, List.length_append]; omega
  have hxs : x.sum = P.sum + g.sum + R.sum := by simp only [hx, List.sum_append]
  obtain ⟨t₁, ht₁, hr₁⟩ := nbrToCsr_runsTo ls R (w - 2) (by rw [← hV, ← hg]; omega)
  have happ : (nbrRw k).apply ![y, x] = P ++ csrWord ls ++ R := by
    rw [nbrRw_apply, hy]
    simp only [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero]
    have e1 : List.take k (P ++ g ++ R) = P := by
      rw [List.append_assoc]; exact List.take_left' hP
    have e2 : List.drop (k + g.length) (P ++ g ++ R) = R := by
      rw [List.append_assoc, ← hP]; simp
    rw [e1, e2, List.append_assoc]
  have hfit₁ : (dropRw k).Fits w (fun _ => x) := dropRw_fits (by omega) (by omega)
  have hfit₂ : (nbrRw k).Fits w ![y, x] := by
    refine nbrRw_fits (by rw [hy]; simp; omega) (by omega) (by omega) (by rw [hy]; simp; omega) ?_
    rw [happ]; simp; omega
  obtain ⟨hf, hb⟩ := hq w x y t₁ hKV hfit₁ (by rw [hy]; simp; omega) hfit₂
    (by rw [dropRw_apply, hdrop]; exact hr₁)
  rw [happ] at hf hb
  rw [← hg] at ht₁
  refine ⟨fun z t₂ h₂ => ?_, hb⟩
  obtain ⟨t, ht, hr⟩ := hf z t₂ h₂
  refine ⟨t, le_trans ht ?_, hr⟩
  rw [dropRw_cost, nbrRw_cost]
  have : t₁ + t₂ + 3 + 10 ≤ 1000 * (t₂ + x.length + 1) := by omega
  calc K * (t₁ + t₂ + 3 + 10) ≤ K * (1000 * (t₂ + x.length + 1)) := Nat.mul_le_mul_left _ this
    _ ≤ (1000 * K + 1000) * (t₂ + x.length + 1) := by nlinarith

/-! ### From compressed sparse rows to neighbor lists -/

/-- The length `3 + n + 2E` of a compressed sparse row word at position
`k` of the source `src`. -/
def csrLen {s : ℕ} (src : Fin s) (k : ℕ) : HExpr s :=
  .add (.lit 3) (.add (.entry src k) (.mul (.lit 2) (.entry src (k + 1))))

/-- The compressed sparse row word after the prefix. -/
def csrPartRw (k : ℕ) : Rewrite 1 := [.slice 0 (.lit k) (some (csrLen 0 k))]

/-- The prefix, the converted graph word and the rest. -/
def csrBackRw (k : ℕ) : Rewrite 2 :=
  [.slice 1 (.lit 0) (some (.lit k)), .slice 0 (.lit 0) none,
    .slice 1 (.add (.lit k) (csrLen 1 k)) none]

theorem csrLen_eval {s : ℕ} (xs : Fin s → List ℕ) (src : Fin s) (k : ℕ) :
    (csrLen src k).eval xs = 3 + (xs src).getD k 0 + 2 * (xs src).getD (k + 1) 0 := by
  simp [csrLen, HExpr.eval]; omega

theorem csrLen_cost {s : ℕ} (xs : Fin s → List ℕ) (src : Fin s) (k : ℕ) :
    (csrLen src k).cost xs = 7 := by
  simp [csrLen, HExpr.cost]

theorem csrPartRw_apply (k : ℕ) (x : List ℕ) :
    (csrPartRw k).apply (fun _ => x) =
      (x.drop k).take (3 + x.getD k 0 + 2 * x.getD (k + 1) 0) := by
  simp [csrPartRw, Rewrite.apply, Segment.apply, HExpr.eval, csrLen_eval]

theorem csrBackRw_apply (k : ℕ) (y x : List ℕ) :
    (csrBackRw k).apply ![y, x] =
      x.take k ++ y ++ x.drop (k + (3 + x.getD k 0 + 2 * x.getD (k + 1) 0)) := by
  simp [csrBackRw, Rewrite.apply, Segment.apply, HExpr.eval, csrLen_eval]

theorem csrPartRw_cost (k : ℕ) (x : List ℕ) : (csrPartRw k).cost (fun _ => x) = 10 := by
  simp [csrPartRw, Rewrite.cost, Segment.cost, HExpr.cost, csrLen_cost]

theorem csrBackRw_cost (k : ℕ) (y x : List ℕ) : (csrBackRw k).cost ![y, x] = 16 := by
  simp [csrBackRw, Rewrite.cost, Segment.cost, HExpr.cost, csrLen_cost]

theorem csrLen_fits {s w : ℕ} (xs : Fin s → List ℕ) (src : Fin s) (k : ℕ)
    (hk : k + 1 < 2 ^ w) : (csrLen src k).Fits w xs := by
  exact ⟨trivial, show k < 2 ^ w by omega, trivial, hk⟩

theorem csrPartRw_fits {w k : ℕ} {x : List ℕ} (hx : x.length < 2 ^ w)
    (hl : 3 + x.getD k 0 + 2 * x.getD (k + 1) 0 < 2 ^ w) (hk : k + 1 < 2 ^ w) :
    (csrPartRw k).Fits w (fun _ => x) := by
  refine ⟨fun _ => hx, ?_, ?_⟩
  · rw [csrPartRw_apply]; simp; omega
  · intro seg hs
    simp only [csrPartRw, List.mem_singleton] at hs
    subst hs
    exact ⟨trivial, by simp [HExpr.eval]; omega, csrLen_fits _ _ _ hk,
      by rw [csrLen_eval]; exact hl⟩

theorem csrBackRw_fits {w k : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ w) (hx : x.length < 2 ^ w)
    (hl : k + (3 + x.getD k 0 + 2 * x.getD (k + 1) 0) < 2 ^ w) (hk : k + 1 < 2 ^ w)
    (hr : ((csrBackRw k).apply ![y, x]).length < 2 ^ w) :
    (csrBackRw k).Fits w ![y, x] := by
  refine ⟨fun i => ?_, hr, ?_⟩
  · fin_cases i <;> simpa
  · intro seg hs
    simp only [csrBackRw, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨trivial, by show 0 < 2 ^ w; omega, trivial, by show k < 2 ^ w; omega⟩
    · exact ⟨trivial, by show 0 < 2 ^ w; omega⟩
    · refine ⟨⟨trivial, csrLen_fits _ _ _ hk⟩, ?_⟩
      simp only [HExpr.eval, csrLen_eval]
      simpa using hl

/-- The pipe `q` runs `p` on the input after converting the compressed
sparse row word behind a prefix of length `k` into the word of the
graph, with the constant `K`. -/
def CsrBridge (k : ℕ) (p q : Program) (K : ℕ) : Prop :=
    ∀ (w : ℕ) (P R g : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)), P.length = k →
      EncodesGraph g n G →
      K * ((P ++ g ++ R).length + maxEntry (P ++ g ++ R) + 1) ^ 2 ≤ 2 ^ w →
      (∀ z t₂, RunsTo (w - 2) p (P ++ toWord G ++ R) z t₂ →
        ∃ t ≤ K * (t₂ + (n + 1) ^ 2 + (P ++ g ++ R).length + 1),
          RunsTo w q (P ++ g ++ R) z t) ∧
      (∀ z T, RunsTo w q (P ++ g ++ R) z T →
        ∃ t₂ ≤ T, RunsTo (w - 2) p (P ++ toWord G ++ R) z t₂)

/-- **Compressed sparse rows to neighbor lists after a prefix.** -/
theorem csr_bridge (k : ℕ) (p : Program) : ∃ (q : Program) (K : ℕ), CsrBridge k p q K := by
  obtain ⟨q, K, hq⟩ := pipe_conv (compileProgram csrLayout csrToGraph) p (csrPartRw k)
    (csrBackRw k)
  refine ⟨q, 1000 * K + 1000, fun w P R g n G hP hg hw => ?_⟩
  set x := P ++ g ++ R with hx
  set y := toWord G with hy
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x.length + maxEntry x + 1 := ⟨_, rfl⟩
  rw [← hZ] at hw
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
  have hKZ : (1000 * K + 1000) * 1 ≤ (1000 * K + 1000) * Z ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hZ1)
  have h4 := two_pow_four (w := w) (by omega)
  set V := 2 ^ (w - 2) with hV
  have hKZ' : 250 * (K + 1) * Z ^ 2 ≤ V := by
    have : (1000 * K + 1000) * Z ^ 2 = 4 * (250 * (K + 1) * Z ^ 2) := by ring
    omega
  have hZV : 250 * Z ^ 2 ≤ V := le_trans (Nat.mul_le_mul_right _ (by nlinarith)) hKZ'
  have hKV : K ≤ V := by
    have : K * 1 ≤ 250 * (K + 1) * Z ^ 2 := Nat.mul_le_mul (by omega) (Nat.one_le_pow _ _ hZ1)
    omega
  have hglen := hg.length_eq
  have hxl : x.length = k + g.length + R.length := by
    simp only [hx, List.length_append, hP]
  -- the graph word inside the input
  have hgk : x.getD k 0 = n := by
    rw [hx, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hP, Nat.sub_self,
      List.getD_append _ _ _ _ (by omega)]
    exact hg.vertexCount_eq
  have hgk1 : x.getD (k + 1) 0 = edgeCount g := by
    rw [hx, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hP,
      show k + 1 - k = 1 by omega, List.getD_append _ _ _ _ (by omega)]
    rfl
  have hlen : 3 + x.getD k 0 + 2 * x.getD (k + 1) 0 = g.length := by rw [hgk, hgk1]; omega
  have hpart : (csrPartRw k).apply (fun _ => x) = g := by
    rw [csrPartRw_apply, hlen, hx, List.append_assoc, List.drop_left' hP, List.take_left]
  have happ : (csrBackRw k).apply ![y, x] = P ++ y ++ R := by
    rw [csrBackRw_apply, hlen]
    have e1 : List.take k (P ++ g ++ R) = P := by
      rw [List.append_assoc]; exact List.take_left' hP
    have e2 : List.drop (k + g.length) (P ++ g ++ R) = R := by
      rw [List.append_assoc, ← hP]; simp
    rw [e1, e2, List.append_assoc]
  -- sizes
  have hnM : n ≤ maxEntry x := le_maxEntry (by
    rw [hx]; simp only [List.mem_append]; left; right
    rw [← hg.vertexCount_eq]; unfold vertexCount
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hyl : y.length ≤ 3 * (n + 1) ^ 2 := toWord_graph_length_le G
  have hn2 : (n + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hgM : maxEntry g ≤ maxEntry x := by
    by_cases hg0 : g = []
    · rw [hg0]; simp [maxEntry]
    · exact le_maxEntry (by rw [hx]; simp [maxEntry_mem hg0])
  obtain ⟨t₁, ht₁, hr₁⟩ := csrToGraph_runsTo hg (w - 2) (by rw [← hV]; omega)
  have hfit₁ : (csrPartRw k).Fits w (fun _ => x) :=
    csrPartRw_fits (by omega) (by rw [hlen]; omega) (by omega)
  have hfit₂ : (csrBackRw k).Fits w ![y, x] := by
    refine csrBackRw_fits (by omega) (by omega) (by rw [hlen]; omega) (by omega) ?_
    rw [happ]; simp; omega
  obtain ⟨hf, hb⟩ := hq w x y t₁ hKV hfit₁ (by omega) hfit₂ (by rw [hpart]; exact hr₁)
  rw [happ] at hf hb
  refine ⟨fun z t₂ h₂ => ?_, hb⟩
  obtain ⟨t, ht, hr⟩ := hf z t₂ h₂
  refine ⟨t, le_trans ht ?_, hr⟩
  rw [csrPartRw_cost, csrBackRw_cost]
  have : t₁ + t₂ + 10 + 16 ≤ 1000 * (t₂ + (n + 1) ^ 2 + x.length + 1) := by omega
  calc K * (t₁ + t₂ + 10 + 16) ≤ K * (1000 * (t₂ + (n + 1) ^ 2 + x.length + 1)) :=
        Nat.mul_le_mul_left _ this
    _ ≤ (1000 * K + 1000) * (t₂ + (n + 1) ^ 2 + x.length + 1) := by nlinarith

end Lax185574Proofs.Interface
