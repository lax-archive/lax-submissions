import Lax185574Proofs.LegacyInstance
import Lax185574Proofs.Words.Computes
import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.Words.FinsetWords
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
From the word of a graph to its compressed sparse row form.

The word of a graph on `n` vertices (`Lax185574.WordEncoding`) is `n`,
followed for each vertex by the number `d` of its neighbors and the
words `1, u` of its neighbors `u` in increasing order. The compressed
sparse row word (`Lax271696.GraphEncoding`) is `n`, the number `E` of
edges, the `n + 1` offsets and the `2E` targets.

The command `nbrToCsr` reads the graph word off the front of its input
and leaves the rest of the input alone. It stores the neighbors one
after the other in an array, which becomes the targets, and records
where the block of each vertex ends, which gives the offsets. It then
writes the length of the graph word, followed by the compressed sparse
row word. It takes time linear in the length of the graph word.

The statements are first proved for any list of neighbor lists, and
then for the neighbor lists of a graph.
-/

namespace Lax185574Proofs.Interface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Simulation
open Lax185574.WordEncoding Lax271696.GraphEncoding Lax185574Proofs.Words

/-! ### The words -/

/-- The block of a vertex with the neighbor list `l`: its length, then
the words `1, u` of its entries. -/
def nbBlock (l : List ℕ) : List ℕ := l.length :: elemFrames l

/-- The word of a list of neighbor lists: their number, then the
blocks. -/
def nbWord (ls : List (List ℕ)) : List ℕ := ls.length :: (ls.map nbBlock).flatten

/-- The offset of the block of vertex `i` among the targets. -/
def offs (ls : List (List ℕ)) (i : ℕ) : ℕ := (ls.take i).flatten.length

/-- The compressed sparse row word of a list of neighbor lists. -/
def csrWord (ls : List (List ℕ)) : List ℕ :=
  ls.length :: ls.flatten.length / 2 :: (arrOf (ls.length + 1) (offs ls) ++ ls.flatten)

theorem length_blocks (ls : List (List ℕ)) :
    ((ls.map nbBlock).flatten).length = ls.length + 2 * ls.flatten.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, nbBlock,
      List.length_cons, length_elemFrames]
    ring

theorem length_nbWord (ls : List (List ℕ)) :
    (nbWord ls).length = 1 + ls.length + 2 * ls.flatten.length := by
  simp only [nbWord, List.length_cons, length_blocks]; ring

theorem flatten_take_succ {ls : List (List ℕ)} {u : ℕ} (hu : u < ls.length) :
    (ls.take (u + 1)).flatten = (ls.take u).flatten ++ ls[u] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hu, Option.toList_some, List.flatten_append,
    List.flatten_singleton]

theorem blocks_drop {ls : List (List ℕ)} {u : ℕ} (hu : u < ls.length) :
    ((ls.drop u).map nbBlock).flatten = nbBlock ls[u] ++ ((ls.drop (u + 1)).map nbBlock).flatten := by
  rw [List.drop_eq_getElem_cons hu, List.map_cons, List.flatten_cons]

theorem blocks_take_succ {ls : List (List ℕ)} {u : ℕ} (hu : u < ls.length) :
    ((ls.take (u + 1)).map nbBlock).flatten.length =
      ((ls.take u).map nbBlock).flatten.length + 1 + 2 * ls[u].length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hu, Option.toList_some, List.map_append,
    List.flatten_append, List.length_append]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    nbBlock, List.length_cons, length_elemFrames]
  ring

theorem offs_succ {ls : List (List ℕ)} {u : ℕ} (hu : u < ls.length) :
    offs ls (u + 1) = offs ls u + ls[u].length := by
  simp only [offs, flatten_take_succ hu, List.length_append]

theorem offs_le (ls : List (List ℕ)) (u : ℕ) : offs ls u ≤ ls.flatten.length := by
  unfold offs
  conv_rhs => rw [← List.take_append_drop u ls, List.flatten_append, List.length_append]
  omega

theorem offs_length (ls : List (List ℕ)) : offs ls ls.length = ls.flatten.length := by
  simp [offs]

/-! ### Arrays holding a prefix -/

/-- The array `a` holds the list `l` at its front. -/
def Holds (a l : List ℕ) : Prop := ∀ i (h : i < l.length), a[i]? = some l[i]

theorem Holds.nil (a : List ℕ) : Holds a [] := fun _ h => absurd h (by simp)

theorem Holds.snoc {a l : List ℕ} (v : ℕ) (h : Holds a l) (hlen : l.length < a.length) :
    Holds (a.set l.length v) (l ++ [v]) := by
  intro i hi
  rw [List.getElem?_set]
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hik : l.length = i
  · subst hik
    simp [hlen]
  · rw [if_neg hik]
    have : i < l.length := by omega
    rw [h i this, List.getElem_append_left this]

/-! ### The command -/

/-- Read the word `1, v` of one neighbor and append `v` to the targets. -/
def nbrBody : Com :=
  .seq (.read "v") (.seq (.read "v") (.seq (.store "tg" (.var "s") (.var "v"))
    (.assign "s" (.add (.var "s") (.lit 1)))))

/-- Read the block of vertex `u`, add its length to `k`, and record the
end of its targets as offset `u + 1`. -/
def vtxBody : Com :=
  .seq (.read "d") (.seq (.assign "k" (.add (.add (.var "k") (.lit 1)) (.add (.var "d") (.var "d"))))
    (.seq (forUp "j" (.var "d") nbrBody)
      (.seq (.store "of" (.add (.var "u") (.lit 1)) (.var "s"))
        (.assign "u" (.add (.var "u") (.lit 1))))))

/-- Read the graph word. -/
def readPhase : Com :=
  .seq (.read "n") (.seq (.assign "k" (.lit 1)) (.seq (.assign "s" (.lit 0))
    (.seq (.assign "u" (.lit 0)) (.while (.lt (.var "u") (.var "n")) vtxBody))))

/-- Write the entries `0, …, cnt - 1` of the array `a`. -/
def writeArr (a cnt : String) : Com := forUp "i" (.var cnt) (.write (.get a (.var "i")))

/-- Write the length of the graph word and the compressed sparse row
word. -/
def writePhase : Com :=
  .seq (.write (.var "k")) (.seq (.write (.var "n")) (.seq (.write (.div (.var "s") (.lit 2)))
    (.seq (.assign "c" (.add (.var "n") (.lit 1))) (.seq (writeArr "of" "c") (writeArr "tg" "s")))))

/-- From the word of a graph to the compressed sparse row word. -/
def nbrToCsr : Com := .seq readPhase writePhase

def nbrLayout : Layout where
  scalars := ["n", "k", "s", "u", "d", "j", "v", "i", "c"]
  arrays := ["of", "tg"]
  temps := 4

theorem nbrToCsr_ok : Com.Ok nbrLayout nbrToCsr := by
  simp [nbrToCsr, readPhase, writePhase, vtxBody, nbrBody, writeArr, forUp, nbrLayout,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr]

/-! ### Its run -/

theorem nbrBody_run {B : ℕ} {P rest : List ℕ} {v : ℕ} {τ : Env}
    (hinp : τ.inp = 1 :: v :: rest) (hs : τ.vars "s" = P.length)
    (htg : Holds (τ.arrs "tg") P) (hlen : P.length < (τ.arrs "tg").length)
    (hv : v < B) (hsB : P.length + 1 < B) :
    ∃ τ', Run B nbrBody τ τ' 9 ∧ τ'.inp = rest ∧ τ'.vars "s" = P.length + 1 ∧
      Holds (τ'.arrs "tg") (P ++ [v]) ∧ (τ'.arrs "tg").length = (τ.arrs "tg").length ∧
      (∀ y, y ≠ "v" → y ≠ "s" → τ'.vars y = τ.vars y) ∧
      (∀ a, a ≠ "tg" → τ'.arrs a = τ.arrs a) ∧ τ'.out = τ.out := by
  set τ1 : Env := { τ.setVar "v" 1 with inp := v :: rest }
  have r1 : Run B (.read "v") τ τ1 1 := Run.read hinp
  set τ2 : Env := { τ1.setVar "v" v with inp := rest }
  have r2 : Run B (.read "v") τ1 τ2 1 := Run.read rfl
  have hs2 : τ2.vars "s" = P.length := by simp [τ2, τ1, hs]
  have hv2 : τ2.vars "v" = v := by simp [τ2]
  have hl2 : τ2.arrs "tg" = τ.arrs "tg" := by simp [τ2, τ1]
  set τ3 := τ2.setArr "tg" P.length v
  have r3 : Run B (.store "tg" (.var "s") (.var "v")) τ2 τ3 3 :=
    (Run.store (idx := P.length) (v := v) (by rw [evalB_var (by rw [hs2]; omega), hs2])
      (by rw [evalB_var (by rw [hv2]; omega), hv2]) (by rw [hl2]; omega)).mono (by simp)
  have hs3 : τ3.vars "s" = P.length := by simp [τ3, hs2]
  have r4 : Run B (.assign "s" (.add (.var "s") (.lit 1))) τ3 (τ3.setVar "s" (P.length + 1)) 4 :=
    (Run.assign (by simp [hs3]; omega)).mono (by simp)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by norm_num), by simp [τ3, τ2], by simp, ?_,
    by simp [τ3, hl2], fun y h1 h2 => by simp [τ3, τ2, τ1, h1, h2], fun a ha => by
      simp [τ3, τ2, τ1, ha], by simp [τ3, τ2, τ1]⟩
  simp only [arrs_setVar, τ3, arrs_setArr, if_true]
  rw [hl2]
  exact htg.snoc v hlen

/-- The neighbors of one vertex. -/
theorem nbrLoop_run {B S : ℕ} {P l rest : List ℕ} {τ : Env}
    (hinp : τ.inp = elemFrames l ++ rest) (hd : τ.vars "d" = l.length)
    (hs : τ.vars "s" = P.length) (htg : Holds (τ.arrs "tg") P)
    (hlen : (τ.arrs "tg").length = S) (hPS : P.length + l.length ≤ S)
    (hv : ∀ v ∈ l, v < B) (hSB : S + 1 < B) :
    ∃ τ', Run B (forUp "j" (.var "d") nbrBody) τ τ' (17 * l.length + 6) ∧
      τ'.inp = rest ∧ τ'.vars "s" = P.length + l.length ∧
      Holds (τ'.arrs "tg") (P ++ l) ∧ (τ'.arrs "tg").length = S ∧
      (∀ y, y ≠ "v" → y ≠ "s" → y ≠ "j" → τ'.vars y = τ.vars y) ∧
      (∀ a, a ≠ "tg" → τ'.arrs a = τ.arrs a) ∧ τ'.out = τ.out := by
  let I : ℕ → Env → Prop := fun k ρ => ρ.inp = elemFrames (l.drop k) ++ rest ∧
    ρ.vars "d" = l.length ∧ ρ.vars "s" = P.length + k ∧ Holds (ρ.arrs "tg") (P ++ l.take k) ∧
    (ρ.arrs "tg").length = S ∧ (∀ y, y ≠ "v" → y ≠ "s" → y ≠ "j" → ρ.vars y = τ.vars y) ∧
    (∀ a, a ≠ "tg" → ρ.arrs a = τ.arrs a) ∧ ρ.out = τ.out
  obtain ⟨τ', hr, ⟨hi', hd', hs', ht', hl', hv', ha', ho'⟩, -⟩ :=
    forUp_run (B := B) (i := "j") (e := .var "d") (body := nbrBody) (N := l.length) (K := 9) I
      (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.2.1]; omega), hI.2.1])
      (σ := τ) ⟨by simp [hinp], by simp [hd], by simp [hs], by simpa using htg, by simp [hlen],
        fun y h1 h2 h3 => by simp [h3], fun a _ => by simp, by simp⟩
      (by
        rintro k hk ρ ⟨hi, hd, hs, ht, hl, hvs, has, ho⟩ hik
        have hinp' : ρ.inp = 1 :: l[k] :: (elemFrames (l.drop (k + 1)) ++ rest) := by
          rw [hi, List.drop_eq_getElem_cons hk, elemFrames_cons]; rfl
        have hPl : (P ++ l.take k).length = P.length + k := by simp; omega
        obtain ⟨ρ', r, hi2, hs2, ht2, hl2, hv2, ha2, ho2⟩ := nbrBody_run (B := B) hinp'
          (by rw [hs, hPl]) ht (by rw [hl, hPl]; omega) (hv _ (List.getElem_mem hk))
          (by rw [hPl]; omega)
        refine ⟨ρ', r, by rw [hv2 "j" (by decide) (by decide), hik], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hi2]
        · simp only [vars_setVar]; rw [if_neg (by decide), hv2 "d" (by decide) (by decide), hd]
        · simp only [vars_setVar]; rw [if_neg (by decide), hs2, hPl]; ring
        · simp only [arrs_setVar]
          rw [List.take_add_one, List.getElem?_eq_getElem hk]
          simpa using ht2
        · simp [hl2, hl]
        · intro y h1 h2 h3
          simp only [vars_setVar, if_neg h3]
          rw [hv2 y h1 h2, hvs y h1 h2 h3]
        · intro a h; simp only [arrs_setVar]; rw [ha2 a h, has a h]
        · simp [ho2, ho])
  refine ⟨τ', hr.mono (by simp; omega), by simpa [elemFrames] using hi', by rw [hs'], by simpa using ht', hl', hv', ha',
    ho'⟩

/-- One vertex. -/
theorem vtxBody_run {B S N u k₀ : ℕ} {P O l R : List ℕ} {τ : Env}
    (hinp : τ.inp = nbBlock l ++ R) (hu : τ.vars "u" = u) (hk : τ.vars "k" = k₀)
    (hs : τ.vars "s" = P.length) (htg : Holds (τ.arrs "tg") P)
    (hlen : (τ.arrs "tg").length = S) (hPS : P.length + l.length ≤ S)
    (hof : Holds (τ.arrs "of") O) (hO : O.length = u + 1) (hofl : (τ.arrs "of").length = N + 1)
    (huN : u < N) (hv : ∀ v ∈ l, v < B) (hSB : S + 1 < B) (hNB : N + 1 < B)
    (hkB : k₀ + 1 + 2 * l.length < B) :
    ∃ τ', Run B vtxBody τ τ' (17 * l.length + 30) ∧ τ'.inp = R ∧ τ'.vars "u" = u + 1 ∧
      τ'.vars "k" = k₀ + 1 + 2 * l.length ∧ τ'.vars "s" = P.length + l.length ∧
      Holds (τ'.arrs "tg") (P ++ l) ∧ (τ'.arrs "tg").length = S ∧
      Holds (τ'.arrs "of") (O ++ [P.length + l.length]) ∧ (τ'.arrs "of").length = N + 1 ∧
      (∀ y, y ≠ "d" → y ≠ "k" → y ≠ "j" → y ≠ "v" → y ≠ "s" → y ≠ "u" → τ'.vars y = τ.vars y) ∧
      τ'.out = τ.out := by
  set τ1 : Env := { τ.setVar "d" l.length with inp := elemFrames l ++ R }
  have r1 : Run B (.read "d") τ τ1 1 := Run.read (by rw [hinp]; rfl)
  set τ2 := τ1.setVar "k" (k₀ + 1 + (l.length + l.length))
  have r2 : Run B (.assign "k" (.add (.add (.var "k") (.lit 1)) (.add (.var "d") (.var "d")))) τ1 τ2 8 :=
    (Run.assign (by simp [τ1, hk]; omega)).mono (by simp)
  obtain ⟨τ3, r3, hi3, hs3, ht3, hl3, hv3, ha3, ho3⟩ := nbrLoop_run (B := B) (S := S) (P := P)
    (l := l) (rest := R) (τ := τ2) (by simp [τ2, τ1]) (by simp [τ2, τ1]) (by simp [τ2, τ1, hs])
    (by simpa [τ2, τ1] using htg) (by simpa [τ2, τ1] using hlen) hPS hv hSB
  have hu3 : τ3.vars "u" = u := by
    rw [hv3 "u" (by decide) (by decide) (by decide)]; simp [τ2, τ1, hu]
  have hof3 : τ3.arrs "of" = τ.arrs "of" := by
    rw [ha3 "of" (by decide)]; simp [τ2, τ1]
  set τ4 := τ3.setArr "of" (u + 1) (P.length + l.length)
  have r4 : Run B (.store "of" (.add (.var "u") (.lit 1)) (.var "s")) τ3 τ4 5 :=
    (Run.store (idx := u + 1) (v := P.length + l.length) (by simp [hu3]; omega)
      (by rw [evalB_var (by rw [hs3]; omega), hs3]) (by rw [hof3]; omega)).mono (by simp)
  have r5 : Run B (.assign "u" (.add (.var "u") (.lit 1))) τ4 (τ4.setVar "u" (u + 1)) 4 :=
    (Run.assign (by simp [τ4, hu3]; omega)).mono (by simp)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), by simp [τ4, hi3], by simp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [vars_setVar, τ4, vars_setArr]
    rw [if_neg (by decide), hv3 "k" (by decide) (by decide) (by decide)]
    simp [τ2]; omega
  · simp only [vars_setVar, τ4, vars_setArr]; rw [if_neg (by decide), hs3]
  · simpa [τ4] using ht3
  · simpa [τ4] using hl3
  · simp only [arrs_setVar, τ4, arrs_setArr, if_true]
    rw [hof3, show u + 1 = O.length by omega]
    exact hof.snoc _ (by rw [hofl]; omega)
  · simp [τ4, hof3, hofl]
  · intro y h1 h2 h3 h4 h5 h6
    simp only [vars_setVar, if_neg h6, τ4, vars_setArr]
    rw [hv3 y h4 h5 h3]
    simp [τ2, τ1, h1, h2]
  · simp [τ4, ho3, τ2, τ1]

/-- The loop over the vertices. -/
theorem vtxLoop_run {B : ℕ} (ls : List (List ℕ)) (rest : List ℕ) {σ : Env}
    (hB : (nbWord ls).length + 2 ≤ B) (hent : ∀ v ∈ ls.flatten, v < B)
    (hinp : σ.inp = ((ls.map nbBlock).flatten) ++ rest) (hn : σ.vars "n" = ls.length)
    (hk : σ.vars "k" = 1) (hs : σ.vars "s" = 0) (hu : σ.vars "u" = 0)
    (htg : (σ.arrs "tg").length = ls.flatten.length) (hof : Holds (σ.arrs "of") [0])
    (hofl : (σ.arrs "of").length = ls.length + 1) :
    ∃ σ' K, Run B (.while (.lt (.var "u") (.var "n")) vtxBody) σ σ' K ∧
      K ≤ 50 * ls.length + 20 * ls.flatten.length + 4 ∧
      σ'.inp = rest ∧ σ'.vars "n" = ls.length ∧ σ'.vars "k" = (nbWord ls).length ∧
      σ'.vars "s" = ls.flatten.length ∧ Holds (σ'.arrs "tg") ls.flatten ∧
      (σ'.arrs "tg").length = ls.flatten.length ∧
      Holds (σ'.arrs "of") (arrOf (ls.length + 1) (offs ls)) ∧ σ'.out = σ.out := by
  set N := ls.length
  set S := ls.flatten.length
  have hlenW := length_nbWord ls
  let I : Env → Prop := fun τ => ∃ u ≤ N, τ.vars "u" = u ∧ τ.vars "n" = N ∧
    τ.inp = ((ls.drop u).map nbBlock).flatten ++ rest ∧
    τ.vars "k" = 1 + ((ls.take u).map nbBlock).flatten.length ∧ τ.vars "s" = offs ls u ∧
    Holds (τ.arrs "tg") (ls.take u).flatten ∧ (τ.arrs "tg").length = S ∧
    Holds (τ.arrs "of") (arrOf (u + 1) (offs ls)) ∧ (τ.arrs "of").length = N + 1 ∧
    τ.out = σ.out
  have hlu : ∀ u, ((ls.take u).map nbBlock).flatten.length ≤ (nbWord ls).length := by
    intro u
    have : ((ls.map nbBlock).flatten).length + 1 = (nbWord ls).length := by simp [nbWord]
    rw [List.map_take]
    have h2 := List.take_append_drop u (ls.map nbBlock)
    have h3 : ((ls.map nbBlock).take u).flatten.length ≤ ((ls.map nbBlock).flatten).length := by
      conv_rhs => rw [← h2, List.flatten_append, List.length_append]
      omega
    omega
  obtain ⟨σ', K, hr, ⟨u, hu', huv, hn', hi', hk', hs', ht', hl', ho', hol', hout'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "u") (.var "n")) (c := vtxBody) I
      (fun τ => 50 * (N - τ.vars "u") + 20 * (S - τ.vars "s"))
      (fun τ ⟨u, hu, huv, hn, _⟩ => evalB_condLt_vars (by omega) (by omega))
      (by
        rintro τ ⟨u, hu, huv, hn, hi, hk, hs, ht, hl, ho, hol, hout⟩ hc
        have hlt : u < N := by
          have := lt_of_condLt_true hc; rwa [hn, huv] at this
        have hoff := offs_succ hlt
        have hoffS := offs_le ls (u + 1)
        have hku := hlu (u + 1)
        rw [blocks_take_succ hlt] at hku
        have hlB : ∀ v ∈ ls[u], v < B := fun v hv =>
          hent v (List.mem_flatten.mpr ⟨_, List.getElem_mem hlt, hv⟩)
        obtain ⟨τ', r, hi2, hu2, hk2, hs2, ht2, hl2, ho2, hol2, hv2, hout2⟩ :=
          vtxBody_run (B := B) (S := S) (N := N) (u := u) (P := (ls.take u).flatten)
            (O := arrOf (u + 1) (offs ls)) (l := ls[u]) (R := ((ls.drop (u + 1)).map nbBlock).flatten ++ rest)
            (by rw [hi, blocks_drop hlt, List.append_assoc]) huv hk (by rw [hs]; rfl) ht hl
            (by show offs ls u + _ ≤ S; omega) ho (by simp) hol hlt hlB (by omega) (by omega)
            (by omega)
        refine ⟨τ', _, r, ⟨u + 1, by omega, hu2, ?_, hi2, ?_, ?_, ?_, hl2, ?_, hol2, ?_⟩, ?_⟩
        · rw [hv2 "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hn]
        · rw [hk2, blocks_take_succ hlt]; ring
        · rw [hs2, hoff]; rfl
        · rw [flatten_take_succ hlt]; exact ht2
        · have : arrOf (u + 1 + 1) (offs ls) = arrOf (u + 1) (offs ls) ++ [offs ls (u + 1)] := by
            simp [arrOf, List.range_succ]
          rw [this, hoff]; exact ho2
        · rw [hout2, hout]
        · rw [hu2, huv, hs2, hs]
          simp only [Cond.size, Expr.size]
          have : (ls.take u).flatten.length = offs ls u := rfl
          omega)
      (show I σ from ⟨0, by omega, hu, hn, by simpa using hinp, by simpa using hk, by simp [hs, offs],
        Holds.nil _, htg, by simpa [arrOf, offs] using hof, hofl, rfl⟩)
  have huN : u = N := by
    have := le_of_condLt_false hfalse; rw [hn', huv] at this; omega
  subst huN
  refine ⟨σ', K, hr, ?_, by simpa [N] using hi', hn', ?_, ?_, by simpa [N] using ht', hl', ho', hout'⟩
  · simp only [Cond.size, Expr.size, hu, hs, Nat.sub_zero] at hK; omega
  · rw [hk', List.take_length]; simp [nbWord]; omega
  · rw [hs', offs_length]

/-- Read the graph word. -/
theorem readPhase_run {B : ℕ} (ls : List (List ℕ)) (rest : List ℕ) {σ : Env}
    (hB : (nbWord ls).length + 2 ≤ B) (hent : ∀ v ∈ ls.flatten, v < B)
    (hinp : σ.inp = nbWord ls ++ rest)
    (htg : (σ.arrs "tg").length = ls.flatten.length)
    (hof : σ.arrs "of" = List.replicate (ls.length + 1) 0) :
    ∃ σ', Run B readPhase σ σ' (50 * ls.length + 20 * ls.flatten.length + 20) ∧
      σ'.inp = rest ∧ σ'.vars "n" = ls.length ∧ σ'.vars "k" = (nbWord ls).length ∧
      σ'.vars "s" = ls.flatten.length ∧ Holds (σ'.arrs "tg") ls.flatten ∧
      (σ'.arrs "tg").length = ls.flatten.length ∧
      Holds (σ'.arrs "of") (arrOf (ls.length + 1) (offs ls)) ∧ σ'.out = σ.out := by
  have hlenW := length_nbWord ls
  set σ1 : Env := { σ.setVar "n" ls.length with inp := (ls.map nbBlock).flatten ++ rest }
  have r1 : Run B (.read "n") σ σ1 1 := Run.read (by rw [hinp]; rfl)
  set σa := σ1.setVar "k" 1
  have ra : Run B (.assign "k" (.lit 1)) σ1 σa 2 := (Run.assign (v := 1) (by simp; omega)).mono (by simp)
  set σb := σa.setVar "s" 0
  have rb : Run B (.assign "s" (.lit 0)) σa σb 2 := (Run.assign (v := 0) (by simp; omega)).mono (by simp)
  set σ2 := σb.setVar "u" 0
  have rc : Run B (.assign "u" (.lit 0)) σb σ2 2 := (Run.assign (v := 0) (by simp; omega)).mono (by simp)
  obtain ⟨σ', K, r3, hK, hi, hn, hk, hs, ht, hl, ho, hout⟩ := vtxLoop_run (B := B) ls rest (σ := σ2)
    hB hent (by simp [σ2, σb, σa, σ1]) (by simp [σ2, σb, σa, σ1]) (by simp [σ2, σb, σa])
    (by simp [σ2, σb]) (by simp [σ2])
    (by simpa [σ2, σb, σa, σ1] using htg)
    (by intro i h; simp at h; subst h; simp [σ2, σb, σa, σ1, hof])
    (by simp [σ2, σb, σa, σ1, hof])
  refine ⟨σ', (r1.seq (ra.seq (rb.seq (rc.seq r3)))).mono (by omega), hi, hn, hk, hs, ht, hl, ho, ?_⟩
  rw [hout]; simp [σ2, σb, σa, σ1]

/-- Writing the front of an array. -/
theorem writeArr_run {B : ℕ} (a cnt : String) (hc : cnt ≠ "i") {l : List ℕ} {τ : Env}
    (h : Holds (τ.arrs a) l) (hcnt : τ.vars cnt = l.length) (hB : l.length < B)
    (hl : ∀ v ∈ l, v < B) :
    ∃ τ', Run B (writeArr a cnt) τ τ' (l.length * 12 + 6) ∧ τ'.out = τ.out ++ l ∧
      (∀ y, y ≠ "i" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs := by
  let I : ℕ → Env → Prop := fun k ρ => ρ.arrs = τ.arrs ∧ (∀ y, y ≠ "i" → ρ.vars y = τ.vars y) ∧
    ρ.out = τ.out ++ l.take k
  obtain ⟨ρ, hr, ⟨ha, hv, ho⟩, -⟩ :=
    forUp_run (B := B) (i := "i") (e := .var cnt) (body := .write (.get a (.var "i")))
      (N := l.length) (K := 4) I hB
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.2.1 cnt hc]; omega), hI.2.1 cnt hc, hcnt])
      (σ := τ) ⟨by simp, fun y hy => by simp [hy], by simp⟩
      (by
        rintro k hk ρ ⟨ha, hv, ho⟩ hik
        refine ⟨_, (Run.write (v := l[k]) (evalB_get (by rw [evalB_var (by omega), hik])
          (by rw [ha]; exact h k hk) (hl _ (List.getElem_mem hk)))).mono (by simp), by simp [hik],
          by simp [ha], fun y hy => by simp [hy, hv y hy], ?_⟩
        simp only [out_setVar, ho]
        rw [List.take_add_one, List.getElem?_eq_getElem hk, List.append_assoc]
        rfl)
  refine ⟨ρ, hr.mono ?_, by rw [ho, List.take_length], hv, ha⟩
  simp only [size_var]
  nlinarith

/-- Write the result. -/
theorem writePhase_run {B : ℕ} (ls : List (List ℕ)) {τ : Env}
    (hB : (nbWord ls).length + 2 ≤ B) (hent : ∀ v ∈ ls.flatten, v < B)
    (hn : τ.vars "n" = ls.length) (hk : τ.vars "k" = (nbWord ls).length)
    (hs : τ.vars "s" = ls.flatten.length) (ht : Holds (τ.arrs "tg") ls.flatten)
    (ho : Holds (τ.arrs "of") (arrOf (ls.length + 1) (offs ls))) :
    ∃ τ', Run B writePhase τ τ' (12 * ls.length + 12 * ls.flatten.length + 40) ∧
      τ'.out = τ.out ++ ((nbWord ls).length :: csrWord ls) := by
  have hlenW := length_nbWord ls
  set τ1 : Env := { τ with out := τ.out ++ [(nbWord ls).length] }
  have r1 : Run B (.write (.var "k")) τ τ1 2 :=
    (Run.write (by rw [evalB_var (by rw [hk]; omega), hk])).mono (by simp)
  set τ2 : Env := { τ1 with out := τ1.out ++ [ls.length] }
  have r2 : Run B (.write (.var "n")) τ1 τ2 2 :=
    (Run.write (by rw [evalB_var (by simp [τ1, hn]; omega)]; simp [τ1, hn])).mono (by simp)
  set τ3 : Env := { τ2 with out := τ2.out ++ [ls.flatten.length / 2] }
  have hs2 : τ2.vars "s" = ls.flatten.length := hs
  have e3 := evalB_bin (B := B) (op := .div) (evalB_var (B := B) (σ := τ2) (x := "s") (by rw [hs2]; omega))
    (evalB_lit (B := B) (n := 2) (σ := τ2) (by omega)) (by rw [Bop.apply_div, hs2]; omega)
  rw [Bop.apply_div, hs2] at e3
  have r3 : Run B (.write (.div (.var "s") (.lit 2))) τ2 τ3 4 :=
    (Run.write e3).mono (by simp)
  set τ4 := τ3.setVar "c" (ls.length + 1)
  have r4 : Run B (.assign "c" (.add (.var "n") (.lit 1))) τ3 τ4 4 :=
    (Run.assign (by simp [τ3, τ2, τ1, hn]; omega)).mono (by simp)
  have hoffs : ∀ v ∈ arrOf (ls.length + 1) (offs ls), v < B := by
    intro v hv
    simp only [arrOf, List.mem_map, List.mem_range] at hv
    obtain ⟨i, -, rfl⟩ := hv
    have := offs_le ls i; omega
  obtain ⟨τ5, r5, ho5, hv5, ha5⟩ := writeArr_run (B := B) "of" "c" (by decide) (l := arrOf (ls.length + 1) (offs ls))
    (τ := τ4) (by simpa [τ4, τ3, τ2, τ1] using ho) (by simp [τ4]) (by simp; omega) hoffs
  obtain ⟨τ6, r6, ho6, -, -⟩ := writeArr_run (B := B) "tg" "s" (by decide) (l := ls.flatten)
    (τ := τ5) (by rw [ha5]; simpa [τ4, τ3, τ2, τ1] using ht)
    (by rw [hv5 "s" (by decide)]; simp [τ4, τ3, τ2, τ1, hs]) (by omega) hent
  refine ⟨τ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ?_⟩
  · simp only [length_arrOf]; ring_nf; omega
  · rw [ho6, ho5]; simp [τ4, τ3, τ2, τ1, csrWord]

/-- The array lengths of the run. -/
def nbrExt (ls : List (List ℕ)) : String → ℕ :=
  fun a => if a = "of" then ls.length + 1 else if a = "tg" then ls.flatten.length else 0

theorem nbrToCsr_run {B : ℕ} (ls : List (List ℕ)) (rest : List ℕ)
    (hB : (nbWord ls).length + 2 ≤ B) (hent : ∀ v ∈ ls.flatten, v < B) :
    ∃ σ', Run B nbrToCsr (initEnv (nbrExt ls) (nbWord ls ++ rest)) σ'
        (70 * (nbWord ls).length + 60) ∧ σ'.out = (nbWord ls).length :: csrWord ls := by
  have hlenW := length_nbWord ls
  obtain ⟨σ1, r1, -, hn, hk, hs, ht, -, ho, hout⟩ := readPhase_run (B := B) ls rest
    (σ := initEnv (nbrExt ls) (nbWord ls ++ rest)) hB hent rfl (by simp [initEnv, nbrExt])
    (by simp [initEnv, nbrExt])
  obtain ⟨σ2, r2, ho2⟩ := writePhase_run (B := B) ls hB hent hn hk hs ht ho
  refine ⟨σ2, (r1.seq r2).mono (by omega), ?_⟩
  rw [ho2, hout]; rfl

/-- **From the word of neighbor lists to the compressed sparse row
word**, on the word RAM, in linear time. The program reads the word
followed by anything and writes the length of the word followed by the
compressed sparse row word. -/
theorem nbrToCsr_runsTo (ls : List (List ℕ)) (rest : List ℕ) (w : ℕ)
    (hw : 2 * ((nbWord ls ++ rest).length + maxEntry (nbWord ls ++ rest) + 2) + 16 ≤ 2 ^ w) :
    ∃ t ≤ 700 * (nbWord ls).length + 601,
      Lax808846.Ram.RunsTo w (compileProgram nbrLayout nbrToCsr) (nbWord ls ++ rest)
        ((nbWord ls).length :: csrWord ls) t := by
  obtain ⟨B, hBd⟩ : ∃ B, B = (nbWord ls ++ rest).length + maxEntry (nbWord ls ++ rest) + 2 :=
    ⟨_, rfl⟩
  have hent : ∀ v ∈ ls.flatten, v < B := by
    intro v hv
    have : v ∈ nbWord ls ++ rest := by
      simp only [nbWord, List.mem_append, List.mem_cons, List.mem_flatten, List.mem_map]
      left; right
      obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp hv
      refine ⟨_, ⟨l, hl, rfl⟩, ?_⟩
      simp only [nbBlock, elemFrames, List.mem_cons, List.mem_flatMap]
      right; exact ⟨v, hvl, by simp⟩
    have := le_maxEntry this; omega
  obtain ⟨σ', ⟨k, hk, hbs⟩, hout⟩ := nbrToCsr_run (B := B) ls rest (by rw [hBd, List.length_append]; omega) hent
  have hfit : nbrLayout.FitsWords B w :=
    ⟨by omega, by omega, by simp [Layout.span, nbrLayout]; omega⟩
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo hfit nbrToCsr_ok
    (fun v hv => by have := le_maxEntry hv; omega) hbs
  rw [hout] at hrun
  refine ⟨t, ht.trans ?_, hrun⟩
  simp only [Layout.const]
  omega

/-! ### The neighbor lists of a graph -/

open Classical in
/-- The neighbor lists of a graph, each in increasing order. -/
noncomputable def nbLists {n : ℕ} (G : SimpleGraph (Fin n)) : List (List ℕ) :=
  List.ofFn fun v : Fin n => sortedVals (Finset.univ.filter (G.Adj v))

theorem length_nbLists {n : ℕ} (G : SimpleGraph (Fin n)) : (nbLists G).length = n := by
  simp [nbLists]

/-- The word of a graph is the word of its neighbor lists. -/
theorem toWord_graph_eq {n : ℕ} (G : SimpleGraph (Fin n)) : toWord G = nbWord (nbLists G) := by
  classical
  change toWord (List.ofFn fun v : Fin n => Finset.univ.filter (G.Adj v)) = _
  change List.length _ :: ((List.ofFn _).map toWord).flatten = _
  rw [nbWord, nbLists, List.length_ofFn, List.length_ofFn, List.map_ofFn, List.map_ofFn]
  congr 2
  congr 1
  funext v
  simp only [Function.comp, toWord_finset_fin, nbBlock, length_sortedVals]

theorem getD_flatten_block {ls : List (List ℕ)} {u j : ℕ} (hu : u < ls.length)
    (hj : j < ls[u].length) : ls.flatten.getD (offs ls u + j) 0 = ls[u][j] := by
  have h : ls.flatten = (ls.take u).flatten ++ (ls[u] ++ (ls.drop (u + 1)).flatten) := by
    have h1 := List.take_append_drop u ls
    rw [List.drop_eq_getElem_cons hu] at h1
    conv_lhs => rw [← h1]
    rw [List.flatten_append, List.flatten_cons]
  rw [h, offs, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  rfl

theorem flatten_nbLists_lt {n : ℕ} (G : SimpleGraph (Fin n)) {v : ℕ}
    (hv : v ∈ (nbLists G).flatten) : v < n := by
  obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp hv
  simp only [nbLists, List.mem_ofFn] at hl
  obtain ⟨u, rfl⟩ := hl
  exact sortedVals_lt hvl

theorem length_flatten_nbLists {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ m, (nbLists G).flatten.length = 2 * m := by
  classical
  refine ⟨G.edgeFinset.card, ?_⟩
  rw [← G.sum_degrees_eq_twice_card_edges, List.length_flatten, nbLists, List.map_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Function.comp, length_sortedVals]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

/-- **The compressed sparse row word of the neighbor lists encodes the
graph.** -/
theorem encodesGraph_csrWord {n : ℕ} (G : SimpleGraph (Fin n)) :
    EncodesGraph (csrWord (nbLists G)) n G := by
  classical
  set ls := nbLists G with hls
  have hN : ls.length = n := length_nbLists G
  obtain ⟨m, hev⟩ := length_flatten_nbLists G
  rw [← hls] at hev
  have hE : edgeCount (csrWord ls) = ls.flatten.length / 2 := rfl
  have hoff : ∀ i ≤ n, offset (csrWord ls) i = offs ls i := by
    intro i hi
    simp only [offset, csrWord, hN]
    rw [show 2 + i = (i + 1) + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    rw [getElem?_arrOf _ (by omega), Option.getD_some]
  have hvc : vertexCount (csrWord ls) = n := by simp [vertexCount, csrWord, hN]
  have htgt : ∀ j, target (csrWord ls) j = ls.flatten.getD j 0 := by
    intro j
    rw [target, hvc]
    simp only [csrWord, hN]
    rw [show 3 + n + j = (n + 1 + j) + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
    congr 2
    simp
  refine ⟨hvc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE]; simp only [csrWord, List.length_cons, List.length_append, length_arrOf, hN]; omega
  · rw [hoff 0 (Nat.zero_le _)]; simp [offs]
  · rw [hoff n le_rfl, hE, ← hN, offs_length]; omega
  · intro i hi
    rw [hoff i hi.le, hoff (i + 1) hi, offs_succ (by omega)]
    omega
  · intro j hj
    rw [htgt, hE] at *
    have hj' : j < ls.flatten.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    exact flatten_nbLists_lt G (List.getElem_mem hj')
  · intro u v
    have hu : (u : ℕ) < ls.length := by rw [hN]; exact u.2
    have hlu : ls[(u : ℕ)] = sortedVals (Finset.univ.filter (G.Adj u)) := by
      simp [hls, nbLists]
    rw [hoff u u.2.le, hoff (u + 1) (by omega), offs_succ hu]
    have hmem : G.Adj u v ↔ (v : ℕ) ∈ ls[(u : ℕ)] := by
      rw [hlu, mem_sortedVals]
      simp
    rw [hmem]
    constructor
    · intro h
      obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp h
      refine ⟨offs ls u + i, by omega, by omega, ?_⟩
      rw [htgt, getD_flatten_block hu hi, hiv]
    · rintro ⟨j, h1, h2, h3⟩
      rw [htgt, show j = offs ls u + (j - offs ls u) by omega,
        getD_flatten_block hu (by omega)] at h3
      rw [← h3]
      exact List.getElem_mem _

end Lax185574Proofs.Interface
