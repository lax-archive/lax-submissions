import Lax185574Proofs.Legacy
import Lax185574.Partitions
import Lax185574Proofs.Interface.Formula

/-!
The encodings of `Lax185574.Encodings` and the words of the older
encoding.

`toWord` is notation for `encode` (see `Lax185574Proofs.Legacy`),
so `encode_eq_toWord` holds by definition. The lemmas below record that
every encoding of this submission is the word that the older encoding
assigned to the value. Most hold by definition. The derived encodings of
Booleans, distance formulas and first-order formulas agree with the older
words only propositionally. A graph is encoded by the encoding of its
`SimpleGraph`, and a sentence by the encoding of its translation to
`Lax3.FirstOrder`.
-/

namespace Lax185574Proofs.Interface

open Lax185574.Encoding Lax185574.Encodings Lax185574.WordEncoding Lax185574Proofs.Legacy
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax3.FirstOrder
open Lax185574.PartialGraphs Lax185574.Partitions Lax185574.TypeTrees
open Lax185574.ConstructionSequences Lax185574.DistanceLogic

universe u

theorem encode_eq_toWord {α : Type u} [Encode α] (a : α) : encode a = toWord a := rfl

theorem encode_fun_eq_toWord {α : Type u} [Encode α] : (encode : α → List ℕ) = toWord := rfl

/-! ## The older words, type by type -/

theorem encode_bool (b : Bool) : encode b = [if b then 1 else 0] := by cases b <;> rfl

theorem encode_int (m : ℤ) :
    encode m = match m with | .ofNat m => [0, m] | .negSucc m => [1, m] := by
  cases m <;> rfl

theorem encode_rat (x : ℚ) : encode x = encode (x.num, x.den) := rfl

theorem encode_list {α : Type u} [Encode α] (l : List α) :
    encode l = l.length :: (l.map encode).flatten := rfl

theorem encode_fun {α : Type u} [Encode α] {n : ℕ} (f : Fin n → α) :
    encode f = encode (List.ofFn f) := rfl

theorem encode_finset {α : Type u} [Encode α] (S : Finset α) :
    encode S = encode (Finset.words S) := rfl

theorem encode_enat (d : ℕ∞) : encode d = [if d = ⊤ then 0 else d.toNat + 1] := rfl

theorem encode_simpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) :
    encode H = (open Classical in encode fun v : Fin n => Finset.univ.filter (H.Adj v)) := rfl

theorem encode_partialGraph {n : ℕ} (G : PartialGraph (Fin n)) :
    encode G = encode (G.color, G.edge, G.nonEdge) := rfl

theorem encode_setoid {n : ℕ} (P : Setoid (Fin n)) : encode P = encode (parts P) := rfl

theorem encode_typeTree (τ : TypeTree) :
    encode τ = encode (τ.k, τ.q, τ.ℓ) ++ encode τ.root := rfl

theorem encode_step (s : Step) : encode s = stepCode s := rfl

theorem encode_script {n : ℕ} (σ : Script n) : encode σ = encode (σ.colors, σ.steps) := rfl

theorem encode_distFO {ℓ : ℕ} (φ : DistFO ℓ) : encode φ = DistFO.code φ := encode_eq_code φ

theorem encode_fo {k : ℕ} (φ : FO k) : encode φ = FO.code φ := encode_eq_foCode φ

/-! ## Graphs and sentences -/

/-- A graph is encoded by the encoding of its `SimpleGraph`, the family
of its neighborhoods. -/
theorem encode_graph (G : Graph) : encode G = toWord G.toSimpleGraph := by
  classical
  show encode (fun v : Fin G.n => ({u | G.Adj v u} : Finset (Fin G.n))) = _
  rfl

/-- A formula without colors is encoded by the encoding of its
translation to `Lax3.FirstOrder`. -/
theorem encode_formula {k : ℕ} (φ : Formula Empty k) : encode φ = toWord (Formula.toFO φ) := by
  induction φ with
  | adj i j => rfl
  | eq i j => rfl
  | not φ ih => exact congrArg (2 :: ·) ih
  | and φ ψ ihφ ihψ =>
    show [3] ++ encode φ ++ encode ψ = [3] ++ toWord (Formula.toFO φ) ++ toWord (Formula.toFO ψ)
    rw [ihφ, ihψ]
  | ex φ ih => exact congrArg (4 :: ·) ih
  | color c _ => exact c.elim

/-- A model-checking instance, a graph and a sentence, is encoded by the
encoding of its `SimpleGraph` followed by that of the sentence. -/
theorem encode_graph_sentence (G : Graph) (φ : Sentence) :
    encode (G, φ) = toWord G.toSimpleGraph ++ toWord (Formula.toFO φ) := by
  show encode G ++ encode φ = _
  rw [encode_graph, encode_formula]

end Lax185574Proofs.Interface
