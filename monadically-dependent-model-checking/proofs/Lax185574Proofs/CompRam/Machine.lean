import Lax185574Proofs.TreeAlgo.FarComposition
import Lax185574Proofs.Words.TreeWord

/-!
The far composition of type trees as a machine on words with an explicit
stack, the plan of the glue program of lem:compose.

A frame stands for one call `τ₁ ∗ τ₂` of the recursion of `composeNode`
at depth `d` and rank `(kk, d)`, with the arities `l1`, `l2` and the
words `A`, `B` of the two nodes. It also holds the shifted nodes `SA`,
`SB`, the canonical word `AT` of the atoms of the result, the index `i`
of the current extension and the list `EX` of the words of the
extensions of the result computed so far. The phase `ph` says which
answer the frame waits for: `0` the canonical form of the atoms, `1` and
`2` the shifts of `B` and `A`, `3` the result of a child frame, `4` the
restriction of the result of a child, `5` the canonical form of the
extensions.

Every round of the machine takes one answer and asks one question: a
rank shift (`sh`), a restriction (`re`) or a canonical form (`ca`). The
stack is a list with its top first. The extensions of `A` come first,
then those of `B`. The child of extension `(i, μ)` of `A` is the call
`μ ∗ SB`, whose result is restricted along the positions `J` that move
the new vertex behind the second tuple. The child of an extension
`(j, ν)` of `B` is the call `SA ∗ ν`.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- A frame of the stack. -/
structure Fr where
  /-- The depth. -/
  d : ℕ
  /-- The first component of the rank. -/
  kk : ℕ
  /-- The arity of the first node. -/
  l1 : ℕ
  /-- The arity of the second node. -/
  l2 : ℕ
  /-- The phase. -/
  ph : ℕ
  /-- The index of the current extension. -/
  i : ℕ
  /-- The word of the first node. -/
  A : List ℕ
  /-- The word of the second node. -/
  B : List ℕ
  /-- The word of the shift of the first node. -/
  SA : List ℕ
  /-- The word of the shift of the second node. -/
  SB : List ℕ
  /-- The canonical word of the atoms of the result. -/
  AT : List ℕ
  /-- The words of the extensions of the result so far. -/
  EX : List (List ℕ)

/-- A question to one of the three programs. -/
inductive Qry where
  /-- A rank shift of the tree with this word. -/
  | sh (w : List ℕ)
  /-- A restriction, the word of a tree and a list of positions. -/
  | re (w : List ℕ)
  /-- The canonical form of a list of words. -/
  | ca (ws : List (List ℕ))

/-- The outcome of a round. -/
inductive Res where
  /-- The next stack and question. -/
  | call (S : List Fr) (q : Qry)
  /-- The final output. -/
  | done (z : List ℕ)
  /-- A stack that the machine never reaches. -/
  | err

/-- The atom words of a node word. -/
def atomsOf (X : List ℕ) : List (List ℕ) := listWords X 0

/-- The extension words of a node word of positive depth. -/
def extsOf (X : List ℕ) : List (List ℕ) := listWords X (listEnd X 0)

/-- The number of extensions of the first node. -/
def nA (f : Fr) : ℕ := (extsOf f.A).length

/-- The number of extensions of the second node. -/
def nB (f : Fr) : ℕ := (extsOf f.B).length

/-- Entry `k` of an atom code with opcode `t` is a position. -/
def posB (t k : ℕ) : Bool :=
  (t ≤ 2 && (k == 1 || k == 2)) || (t == 3 && k == 2) || (t == 4 && (k == 2 || k == 3)) ||
    (t == 5 && k == 3)

/-- The code of an atom with its positions moved up by `l`. -/
def renAtom (l : ℕ) (c : List ℕ) : List ℕ :=
  c.mapIdx fun k v => if posB (c.headD 0) k then v + l else v

/-- The atoms of the result of a frame, unsorted: those of the first node
as they stand, those of the second node behind the first tuple. -/
def atomsQ (f : Fr) : List (List ℕ) := atomsOf f.A ++ (atomsOf f.B).map (renAtom f.l1)

/-- The values of the positions `J` with `ā₁ ā₂ b = (ā₁ b ā₂) ↾ J`. -/
def jList (l1 l2 : ℕ) : List ℕ := (List.ofFn (moveLast l1 l2)).map Fin.val

/-- A new frame. -/
def fresh (d kk l1 l2 : ℕ) (A B : List ℕ) : Fr :=
  { d := d, kk := kk, l1 := l1, l2 := l2, ph := 0, i := 0, A := A, B := B, SA := [], SB := [],
    AT := [], EX := [] }

/-- The child frame of the current extension. -/
def child (f : Fr) : Fr :=
  if f.i < nA f then fresh (f.d - 1) (f.kk + 1) (f.l1 + 1) f.l2 (((extsOf f.A).getD f.i []).drop 1) f.SB
  else fresh (f.d - 1) (f.kk + 1) f.l1 (f.l2 + 1) f.SA (((extsOf f.B).getD (f.i - nA f) []).drop 1)

/-- Go on with the extension `f.i`: open its child, or ask for the
canonical form of the extensions once all are done. -/
def advance (f : Fr) (S : List Fr) : Res :=
  if f.i < nA f + nB f then .call (child f :: { f with ph := 3 } :: S) (.ca (atomsQ (child f)))
  else .call ({ f with ph := 5 } :: S) (.ca f.EX)

/-- The query of the restriction of the result `R` of the child of
frame `p`. -/
def reQuery (p : Fr) (R : List ℕ) : List ℕ :=
  [p.kk + 1, p.d - 1, p.l1 + 1 + p.l2] ++ R ++ ((p.l1 + p.l2 + 1) :: jList p.l1 p.l2)

/-- Hand the result `R` of the top frame to the frame below, or output it
with the header `h` if the stack is empty. -/
def ret (R h : List ℕ) : List Fr → Res
  | [] => .done (h ++ R)
  | p :: S =>
    if p.i < nA p then .call ({ p with ph := 4 } :: S) (.re (reQuery p R))
    else advance
      { p with i := p.i + 1, EX := p.EX ++ [(p.l1 + ((extsOf p.B).getD (p.i - nA p) []).headD 0) :: R] }
      S

/-- One round: the answer `b` to the question of the top frame. -/
def round : List Fr → List ℕ → Res
  | [], _ => .err
  | f :: S, b =>
    if f.ph = 0 then
      (if f.d = 0 then ret b [f.kk, 0, f.l1 + f.l2] S
       else .call ({ f with ph := 1, AT := b } :: S) (.sh ([f.kk, f.d, f.l2] ++ f.B)))
    else if f.ph = 1 then .call ({ f with ph := 2, SB := b.drop 3 } :: S) (.sh ([f.kk, f.d, f.l1] ++ f.A))
    else if f.ph = 2 then advance { f with SA := b.drop 3, i := 0 } S
    else if f.ph = 4 then
      advance { f with i := f.i + 1, EX := f.EX ++ [((extsOf f.A).getD f.i []).headD 0 :: b.drop 3] } S
    else if f.ph = 5 then ret (f.AT ++ b) [f.kk, f.d, f.l1 + f.l2] S
    else .err

/-- Runs of the machine: from `r` the answers satisfying `P` lead to
`r'` within `m` rounds. -/
inductive Leads (P : Qry → List ℕ → Prop) : Res → Res → ℕ → Prop where
  | refl (r : Res) : Leads P r r 0
  | step {S : List Fr} {q : Qry} {b : List ℕ} {r' : Res} {m : ℕ} :
      P q b → Leads P (round S b) r' m → Leads P (.call S q) r' (m + 1)

theorem Leads.trans {P : Qry → List ℕ → Prop} {r₁ r₂ r₃ : Res} {m m' : ℕ}
    (h₁ : Leads P r₁ r₂ m) (h₂ : Leads P r₂ r₃ m') : Leads P r₁ r₃ (m + m') := by
  induction h₁ with
  | refl => simpa using h₂
  | step hb _ ih => rw [Nat.add_right_comm]; exact .step hb (ih h₂)

/-! ### Words of nodes -/

theorem atomsOf_node {h ℓ : ℕ} (t : Node h ℓ) : atomsOf (toWord t) = (Node.atoms t).words := by
  cases h with
  | zero => exact listWords_eq (r := []) (by rw [toWord_node_zero]; simp)
  | succ h => exact listWords_eq (r := toWord (Node.exts t).words) (by rw [toWord_node_succ]; simp)

theorem extsOf_node {h ℓ : ℕ} (t : Node (h + 1) ℓ) : extsOf (toWord t) = (Node.exts t).words := by
  have hx : (toWord t).drop 0 = toWord t ++ [] := by simp
  exact listWords_eq (nodeSplit hx).2

theorem extsOf_getD {h ℓ : ℕ} (t : Node (h + 1) ℓ) {j : ℕ} (hj : j < (Node.exts t).words.length) :
    ∃ ε ∈ Node.exts t, (extsOf (toWord t)).getD j [] = ε.1.val :: toWord ε.2 := by
  obtain ⟨ε, hε, hw⟩ := getElem_words hj
  refine ⟨ε, hε, ?_⟩
  rw [extsOf_node, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
    ← hw, toWord_ext]

theorem length_words_le {α : Type*} [WordEncoding α] (S : Finset α) : S.words.length ≤ S.card := by
  unfold Finset.words
  rw [Finset.length_sort]
  exact Finset.card_image_le

/-- The canonical form of a list of words is the word list of a finite
set when the list has exactly the words of its elements. -/
theorem sortedDistinct_eq_words {α : Type*} [WordEncoding α] (S : Finset α) (L : List (List ℕ))
    (h : ∀ u, u ∈ L ↔ ∃ a ∈ S, toWord a = u) : sortedDistinct L = S.words := by
  unfold sortedDistinct Finset.words
  congr 1
  ext u
  simp only [List.mem_toFinset, Finset.mem_image, h]

/-! ### Renaming atom codes -/

theorem code_rename_castAdd {l1 : ℕ} (l2 : ℕ) (φ : DistFO l1) (h : DistFO.IsAtom φ) :
    code (rename (Fin.castAdd l2) φ) = code φ := by
  cases φ <;> simp only [DistFO.IsAtom] at h <;> simp [rename, code]

theorem renAtom_code (l1 : ℕ) {l2 : ℕ} (φ : DistFO l2) (h : DistFO.IsAtom φ) :
    renAtom l1 (code φ) = code (rename (Fin.natAdd l1) φ) := by
  cases φ <;> simp only [DistFO.IsAtom] at h <;>
    simp [rename, code, renAtom, posB, List.mapIdx_cons, Nat.add_comm]

/-- The canonical form of the atoms of a frame is the word list of the
atoms of the far composition. -/
theorem atomsQ_canon {d l1 l2 : ℕ} (x : Node d l1) (y : Node d l2) (f : Fr) (hA : f.A = toWord x)
    (hB : f.B = toWord y) (hl : f.l1 = l1) (hx : ∀ φ ∈ Node.atoms x, DistFO.IsAtom φ)
    (hy : ∀ φ ∈ Node.atoms y, DistFO.IsAtom φ) :
    sortedDistinct (atomsQ f) = (Node.atoms (composeNode x y)).words := by
  refine sortedDistinct_eq_words _ _ fun u => ?_
  rw [atomsQ, hA, hB, hl, atomsOf_node, atomsOf_node, atoms_composeNode]
  simp only [List.mem_append, List.mem_map, mem_words, Finset.mem_union, Finset.mem_image,
    Lax185574Proofs.Legacy.encode_eq_code]
  constructor
  · rintro (⟨φ, hφ, rfl⟩ | ⟨v, ⟨φ, hφ, rfl⟩, rfl⟩)
    · exact ⟨_, Or.inl ⟨φ, hφ, rfl⟩, code_rename_castAdd l2 φ (hx φ hφ)⟩
    · exact ⟨_, Or.inr ⟨φ, hφ, rfl⟩, (renAtom_code l1 φ (hy φ hφ)).symm⟩
  · rintro ⟨a, (⟨φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩), rfl⟩
    · exact Or.inl ⟨φ, hφ, (code_rename_castAdd l2 φ (hx φ hφ)).symm⟩
    · exact Or.inr ⟨code φ, ⟨φ, hφ, rfl⟩, renAtom_code l1 φ (hy φ hφ)⟩

/-! ### The positions `J` -/

theorem flatten_map_fin {m : ℕ} (L : List (Fin m)) : (L.map toWord).flatten = L.map Fin.val := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl

theorem toWord_jList (l1 l2 : ℕ) :
    toWord (List.ofFn (moveLast l1 l2)) = (l1 + l2 + 1) :: jList l1 l2 := by
  show (List.ofFn (moveLast l1 l2)).length :: ((List.ofFn (moveLast l1 l2)).map toWord).flatten = _
  rw [List.length_ofFn, flatten_map_fin]
  rfl

theorem nodup_jList (l1 l2 : ℕ) : (List.ofFn (moveLast l1 l2)).Nodup :=
  List.nodup_ofFn.mpr (isPInv_moveLast l1 l2).injective

/-! ### The rounds by phase -/

theorem round_ph0_zero (f : Fr) (S : List Fr) (b : List ℕ) (h0 : f.ph = 0) (hd : f.d = 0) :
    round (f :: S) b = ret b [f.kk, 0, f.l1 + f.l2] S := by
  simp [round, h0, hd]

theorem round_ph0_succ (f : Fr) (S : List Fr) (b : List ℕ) (h0 : f.ph = 0) (hd : f.d ≠ 0) :
    round (f :: S) b = .call ({ f with ph := 1, AT := b } :: S) (.sh ([f.kk, f.d, f.l2] ++ f.B)) := by
  simp [round, h0, hd]

theorem round_ph1 (f : Fr) (S : List Fr) (b : List ℕ) (h : f.ph = 1) :
    round (f :: S) b = .call ({ f with ph := 2, SB := b.drop 3 } :: S) (.sh ([f.kk, f.d, f.l1] ++ f.A)) := by
  simp [round, h]

theorem round_ph2 (f : Fr) (S : List Fr) (b : List ℕ) (h : f.ph = 2) :
    round (f :: S) b = advance { f with SA := b.drop 3, i := 0 } S := by
  simp [round, h]

theorem round_ph4 (f : Fr) (S : List Fr) (b : List ℕ) (h : f.ph = 4) :
    round (f :: S) b =
      advance { f with i := f.i + 1, EX := f.EX ++ [((extsOf f.A).getD f.i []).headD 0 :: b.drop 3] } S := by
  simp [round, h]

theorem round_ph5 (f : Fr) (S : List Fr) (b : List ℕ) (h : f.ph = 5) :
    round (f :: S) b = ret (f.AT ++ b) [f.kk, f.d, f.l1 + f.l2] S := by
  simp [round, h]

theorem ret_lt (R h : List ℕ) (p : Fr) (S : List Fr) (hi : p.i < nA p) :
    ret R h (p :: S) = .call ({ p with ph := 4 } :: S) (.re (reQuery p R)) := by
  simp [ret, hi]

theorem ret_ge (R h : List ℕ) (p : Fr) (S : List Fr) (hi : ¬ p.i < nA p) :
    ret R h (p :: S) = advance
      { p with i := p.i + 1, EX := p.EX ++ [(p.l1 + ((extsOf p.B).getD (p.i - nA p) []).headD 0) :: R] }
      S := by
  simp [ret, hi]

theorem advance_lt (f : Fr) (S : List Fr) (hi : f.i < nA f + nB f) :
    advance f S = .call (child f :: { f with ph := 3 } :: S) (.ca (atomsQ (child f))) := by
  simp [advance, hi]

theorem advance_ge (f : Fr) (S : List Fr) (hi : ¬ f.i < nA f + nB f) :
    advance f S = .call ({ f with ph := 5 } :: S) (.ca f.EX) := by
  simp [advance, hi]

theorem child_lt (f : Fr) (hi : f.i < nA f) :
    child f = fresh (f.d - 1) (f.kk + 1) (f.l1 + 1) f.l2 (((extsOf f.A).getD f.i []).drop 1) f.SB := by
  simp [child, hi]

theorem child_ge (f : Fr) (hi : ¬ f.i < nA f) :
    child f = fresh (f.d - 1) (f.kk + 1) f.l1 (f.l2 + 1) f.SA (((extsOf f.B).getD (f.i - nA f) []).drop 1) := by
  simp [child, hi]

end Lax185574Proofs.CompRam
