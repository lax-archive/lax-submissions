import Lax185574Proofs.Legacy
import Lax808846Proofs.Transfer
import Lax808846Proofs.Spec
import Lax185574Proofs.Compose.Basic

/-!
The length of the word of a graph at the front of an input.

The word of a graph on `Fin n` is `n`, followed by one block per vertex.
The block of `v` is the number `d` of its neighbors, followed by `2d`
numbers, the words `1, u` of its neighbors `u`. The command
`prefixLength` reads such a sequence of blocks off the input tape and
writes the number of entries it has read. It reads only the graph and
leaves the rest of the input alone.
-/

namespace Lax185574Proofs.Compose

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile Lax808846Proofs.Simulation
open Lax185574.WordEncoding

/-- A block: half its length, then its entries. -/
def blk (u : List ℕ) : List ℕ := u.length / 2 :: u

/-- The blocks one after the other. -/
def blocksWord (bs : List (List ℕ)) : List ℕ := (bs.map blk).flatten

theorem blocksWord_cons (u : List ℕ) (bs : List (List ℕ)) :
    blocksWord (u :: bs) = blk u ++ blocksWord bs := rfl

theorem blocksWord_drop {bs : List (List ℕ)} {i : ℕ} (hi : i < bs.length) :
    blocksWord (bs.drop i) = blk bs[i] ++ blocksWord (bs.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, blocksWord_cons]

theorem blocksWord_append (as bs : List (List ℕ)) :
    blocksWord (as ++ bs) = blocksWord as ++ blocksWord bs := by
  simp [blocksWord]

theorem blocksWord_take_succ {bs : List (List ℕ)} {i : ℕ} (hi : i < bs.length) :
    (blocksWord (bs.take (i + 1))).length = (blocksWord (bs.take i)).length + (bs[i].length + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, blocksWord_append]
  simp [blocksWord, blk]

theorem blocksWord_take_le (bs : List (List ℕ)) (i : ℕ) :
    (blocksWord (bs.take i)).length ≤ (blocksWord bs).length := by
  conv_rhs => rw [← List.take_append_drop i bs, blocksWord_append, List.length_append]
  omega

/-! ### The command -/

/-- Skip the entries of one block: read `k` numbers. -/
def skipEntries : Com :=
  .seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "k"))
    (.seq (.read "v") (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Read one block and add its length to `g`. -/
def skipBlock : Com :=
  .seq (.read "d") (.seq (.assign "g" (.add (.add (.var "g") (.lit 1)) (.add (.var "d") (.var "d"))))
    (.seq (.assign "k" (.add (.var "d") (.var "d")))
      (.seq skipEntries (.assign "i" (.add (.var "i") (.lit 1))))))

/-- Read the number of blocks, skip the blocks, write the number of
entries read. -/
def prefixLength : Com :=
  .seq (.read "n") (.seq (.assign "g" (.lit 1))
    (.seq (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "n")) skipBlock))
      (.write (.var "g"))))

def prefixLayout : Layout where
  scalars := ["n", "g", "i", "d", "k", "j", "v"]
  arrays := []
  temps := 4

theorem prefixLength_ok : Com.Ok prefixLayout prefixLength := by
  simp [prefixLength, skipBlock, skipEntries, prefixLayout, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

/-! ### Its run -/

/-- All blocks have even length. -/
def EvenBlocks (bs : List (List ℕ)) : Prop := ∀ u ∈ bs, u.length % 2 = 0

theorem skipEntries_spec {B : ℕ} (u tail : List ℕ) (i₀ N g₀ : ℕ) (hB : u.length < B) :
    Spec B (fun σ => σ.vars "k" = u.length ∧ σ.inp = u ++ tail ∧ σ.vars "i" = i₀ ∧
        σ.vars "n" = N ∧ σ.vars "g" = g₀)
      skipEntries
      (fun _ σ' => σ'.inp = tail ∧ σ'.vars "i" = i₀ ∧ σ'.vars "n" = N ∧ σ'.vars "g" = g₀)
      (9 * u.length + 6) := by
  let J : Env → Prop := fun τ => τ.vars "j" ≤ u.length ∧ τ.vars "k" = u.length ∧
    τ.inp = u.drop (τ.vars "j") ++ tail ∧ τ.vars "i" = i₀ ∧ τ.vars "n" = N ∧ τ.vars "g" = g₀
  have hbody : Spec B (fun τ => J τ ∧ τ.vars "j" < u.length)
      (.seq (.read "v") (.assign "j" (.add (.var "j") (.lit 1))))
      (fun τ τ' => J τ' ∧ τ'.vars "j" = τ.vars "j" + 1) 5 := by
    rintro τ ⟨⟨hj, hk, hinp, hi, hn, hg⟩, hlt⟩
    have hinp' : τ.inp = u[τ.vars "j"] :: (u.drop (τ.vars "j" + 1) ++ tail) := by
      rw [hinp, List.drop_eq_getElem_cons hlt]; rfl
    refine ⟨_, (Run.seq (Run.read hinp') (Run.assign (v := τ.vars "j" + 1) ?_)).mono (by simp),
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp; omega
    all_goals simp [hk, hi, hn, hg]
    all_goals omega
  have h := Spec.forRangeZero (B := B) "j" "k" J u.length 5 hB (fun _ h => h.1) (fun _ h => h.2.1) hbody
  refine (h.conseq ?_ ?_ (by omega))
  · rintro σ ⟨hk, hinp, hi, hn, hg⟩
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hk, hinp, hi, hn, hg]
  · rintro σ σ' - ⟨⟨-, -, hinp, hi, hn, hg⟩, hj⟩
    rw [hj, List.drop_length, List.nil_append] at hinp
    exact ⟨hinp, hi, hn, hg⟩

/-- The run of `prefixLength` on blocks followed by anything. -/
theorem prefixLength_run (bs : List (List ℕ)) (hev : EvenBlocks bs) (rest : List ℕ) (B : ℕ)
    (hB : (blocksWord bs).length + bs.length + 2 < B) :
    ∃ σ', Run B prefixLength (initEnv (fun _ => 0) (bs.length :: (blocksWord bs ++ rest))) σ'
        ((9 * (blocksWord bs).length + 40) * (bs.length + 1)) ∧
      σ'.out = [1 + (blocksWord bs).length] := by
  set N := bs.length
  let I : Env → Prop := fun σ => σ.vars "i" ≤ N ∧ σ.vars "n" = N ∧
    σ.vars "g" = 1 + (blocksWord (bs.take (σ.vars "i"))).length ∧
    σ.inp = blocksWord (bs.drop (σ.vars "i")) ++ rest
  have hbw : ∀ i, (blocksWord (bs.take i)).length ≤ (blocksWord bs).length :=
    blocksWord_take_le bs
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "i" < N) skipBlock
      (fun σ σ' => I σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (9 * (blocksWord bs).length + 30) := by
    rintro σ ⟨⟨hi, hn, hg, hinp⟩, hlt⟩
    set i := σ.vars "i"
    have hts := blocksWord_take_succ hlt
    have hu : bs[i].length % 2 = 0 := hev _ (List.getElem_mem _)
    have hdrop := blocksWord_drop hlt
    generalize bs[i] = u at hts hu hdrop
    have hle := hbw (i + 1)
    have hinp' : σ.inp = u.length / 2 :: (u ++ (blocksWord (bs.drop (i + 1)) ++ rest)) := by
      rw [hinp, hdrop]; simp [blk]
    set g₁ := 1 + (blocksWord (bs.take (i + 1))).length
    set σ₁ : Env := { σ.setVar "d" (u.length / 2) with inp := u ++ (blocksWord (bs.drop (i + 1)) ++ rest) }
    have r₁ : Run B (.read "d") σ σ₁ 1 := Run.read hinp'
    have r₂ : Run B (.assign "g" (.add (.add (.var "g") (.lit 1)) (.add (.var "d") (.var "d")))) σ₁
        (σ₁.setVar "g" g₁) 8 := by
      refine (Run.assign ?_).mono (by simp)
      simp [σ₁, hg, g₁, hts]
      omega
    set σ₂ := σ₁.setVar "g" g₁
    have r₃ : Run B (.assign "k" (.add (.var "d") (.var "d"))) σ₂ (σ₂.setVar "k" u.length) 4 := by
      refine (Run.assign ?_).mono (by simp)
      simp [σ₂, σ₁]
      omega
    set σ₃ := σ₂.setVar "k" u.length
    obtain ⟨σ₄, r₄, hinp₄, hi₄, hn₄, hg₄⟩ := (skipEntries_spec (B := B) u
      (blocksWord (bs.drop (i + 1)) ++ rest) i N g₁ (by omega)).run
        (σ := σ₃) (by simp [σ₃, σ₂, σ₁, hn, i])
    have r₅ : Run B (.assign "i" (.add (.var "i") (.lit 1))) σ₄ (σ₄.setVar "i" (i + 1)) 4 := by
      refine (Run.assign ?_).mono (by simp)
      simp [hi₄]; omega
    refine ⟨_, (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (by omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals simp [hn₄, hg₄, hinp₄]
    all_goals (first | rfl | omega)
  have hloop := Spec.forRangeZero (B := B) "i" "n" I N (9 * (blocksWord bs).length + 30)
    (by omega) (fun _ h => h.1) (fun _ h => h.2.1) hbody
  set σ₀ := initEnv (fun _ => 0) (N :: (blocksWord bs ++ rest))
  have r₁ : Run B (.read "n") σ₀ { σ₀.setVar "n" N with inp := blocksWord bs ++ rest } 1 :=
    Run.read rfl
  set σ₁ := { σ₀.setVar "n" N with inp := blocksWord bs ++ rest }
  have r₂ : Run B (.assign "g" (.lit 1)) σ₁ (σ₁.setVar "g" 1) 2 := by
    refine (Run.assign ?_).mono (by simp)
    simp; omega
  obtain ⟨σ₃, r₃, ⟨-, -, hg₃, -⟩, hi₃⟩ := hloop.run (σ := σ₁.setVar "g" 1)
    (by refine ⟨by simp, by simp [σ₁], by simp [σ₁, blocksWord], by simp [σ₁]⟩)
  rw [hi₃, List.take_length] at hg₃
  have r₄ : Run B (.write (.var "g")) σ₃ { σ₃ with out := σ₃.out ++ [1 + (blocksWord bs).length] } 2 := by
    refine (Run.write ?_).mono (by simp)
    simp [hg₃]; omega
  have hout : σ₃.out = [] := by
    have := r₃.out_eq (by decide)
    simpa [σ₁, σ₀, initEnv] using this
  refine ⟨_, (r₁.seq (r₂.seq (r₃.seq r₄))).mono ?_, by simp [hout]⟩
  have : (9 * (blocksWord bs).length + 30 + 4) * N + 6 + 5 ≤
      (9 * (blocksWord bs).length + 40) * (N + 1) := by nlinarith
  omega

/-! ### The word of a graph is a sequence of blocks -/

theorem flatten_singletons_length :
    ∀ ws : List (List ℕ), (∀ u ∈ ws, u.length = 1) →
      ((ws.map toWord).flatten).length = 2 * ws.length
  | [], _ => rfl
  | u :: ws, h => by
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      rw [flatten_singletons_length ws (fun v hv => h v (List.mem_cons_of_mem _ hv)),
        toWord_list_nat, List.length_cons, h u List.mem_cons_self]
      ring

/-- The block of a set of vertices. -/
def setBlock {n : ℕ} (S : Finset (Fin n)) : List ℕ := ((Finset.words S).map toWord).flatten

theorem setBlock_length {n : ℕ} (S : Finset (Fin n)) :
    (setBlock S).length = 2 * (Finset.words S).length := by
  apply flatten_singletons_length
  intro u hu
  simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hu
  obtain ⟨v, -, rfl⟩ := hu
  rfl

theorem toWord_finset_fin {n : ℕ} (S : Finset (Fin n)) : toWord S = blk (setBlock S) := by
  change (Finset.words S).length :: _ = _
  simp only [blk, setBlock_length]
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  rfl

/-- The blocks of a graph, one per vertex. -/
noncomputable def graphBlocks {n : ℕ} (G : SimpleGraph (Fin n)) : List (List ℕ) :=
  open Classical in List.ofFn fun v : Fin n => setBlock (Finset.univ.filter (G.Adj v))

theorem graphBlocks_length {n : ℕ} (G : SimpleGraph (Fin n)) : (graphBlocks G).length = n := by
  simp [graphBlocks]

theorem graphBlocks_even {n : ℕ} (G : SimpleGraph (Fin n)) : EvenBlocks (graphBlocks G) := by
  intro u hu
  simp only [graphBlocks, List.mem_ofFn] at hu
  obtain ⟨v, rfl⟩ := hu
  rw [setBlock_length]; omega

theorem toWord_graph {n : ℕ} (G : SimpleGraph (Fin n)) :
    toWord G = n :: blocksWord (graphBlocks G) := by
  classical
  change toWord (List.ofFn fun v : Fin n => Finset.univ.filter (G.Adj v)) = _
  change List.length _ :: ((List.ofFn _).map toWord).flatten = _
  rw [List.length_ofFn, blocksWord, graphBlocks, List.map_ofFn, List.map_ofFn]
  congr 2
  congr 1
  funext v
  simp only [Function.comp, toWord_finset_fin]

/-! ### On the machine -/

/-- The program computing the length of a graph word at the front of
its input. -/
def graphLengthProg : Lax808846.Ram.Program := compileProgram prefixLayout prefixLength

theorem toWord_graph_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (toWord G).length = 1 + (blocksWord (graphBlocks G)).length := by
  rw [toWord_graph, List.length_cons]; omega

/-- **The length of a graph word.** On the word of a graph followed by
anything, the program outputs the length of the graph word, within
`10 (9|g| + 40)(n+1) + 1` steps, at every word length that holds the
entries of the input plus its length. -/
theorem graphLength_runsTo {n : ℕ} (G : SimpleGraph (Fin n)) (rest : List ℕ) (w B : ℕ)
    (hB : (toWord G).length + n + 2 < B) (hx : ∀ v ∈ toWord G ++ rest, v < B)
    (hw : B + 11 ≤ 2 ^ w) :
    ∃ t ≤ 10 * ((9 * (toWord G).length + 40) * (n + 1)) + 1,
      Lax808846.Ram.RunsTo w graphLengthProg (toWord G ++ rest) [(toWord G).length] t := by
  have hev := graphBlocks_even G
  have hlen := graphBlocks_length G
  have hgl := toWord_graph_length G
  obtain ⟨σ', ⟨k, hk, hbs⟩, hout⟩ := prefixLength_run (graphBlocks G) hev rest B
    (by rw [hlen]; omega)
  have hfit : prefixLayout.FitsWords B w :=
    ⟨by omega, by omega, by simp [Layout.span, prefixLayout]; omega⟩
  have hxeq : toWord G ++ rest = (graphBlocks G).length :: (blocksWord (graphBlocks G) ++ rest) := by
    rw [toWord_graph, hlen]; rfl
  rw [← hxeq] at hbs
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo hfit prefixLength_ok hx hbs
  rw [hout, ← hgl] at hrun
  refine ⟨t, ht.trans ?_, hrun⟩
  have : k ≤ (9 * (toWord G).length + 40) * (n + 1) := by
    refine hk.trans ?_
    rw [hlen]
    exact Nat.mul_le_mul_right _ (by omega)
  simp only [Layout.const]
  omega

end Lax185574Proofs.Compose
