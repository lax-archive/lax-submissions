import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Mathlib.Data.Nat.Notation

/-!
---
title: Encoding data as lists of numbers
type: definition
---
A random access machine reads its input as a list of natural numbers and
writes its output as one. An object is handed to an algorithm through an
*encoding*, a map from its type to lists of numbers. The encodings in
this submission follow one rule, with a few exceptions.

* A natural number is the one-element list containing it.
* A value of an inductive type is a constructor applied to some
  arguments. Its encoding is the number of the constructor (counting
  from 0 in the order of declaration), followed by the encodings of the
  arguments in order. If the type has only one constructor, the number is
  left out.

Arguments that are proofs carry no information and are left out. So are
the implicit arguments that the type of the value determines, such as
the number of free variables of a formula.

For example, the pair `(3, true)` is encoded as `3, 1`, since `true` is
the second constructor of `Bool`. An element `i` of `Fin n` is a natural
number together with a proof that it is less than `n`, so it is encoded
as `i`.

The exceptions are listed in `Lax185574.Encodings`. The main ones are
lists and finite sets. A list is encoded by its length, followed by the
encodings of its entries, so the list `[7, 8]` is encoded as `2, 7, 8`.
A finite set is encoded by the list of the encodings of its elements, in
increasing order.

Each such encoding is a prefix code. An algorithm that knows the type
can read the encoding from the front, one constructor or one length at a
time, without knowing where it ends. The encoding has length linear in
the size of the value, and every number in it is a number of the value,
the number of a constructor or the length of a list. Some of the other
exceptions write further numbers, such as d + 1 for a finite value d of
ℕ∞.

# Formalization notes

The rule is the class `Encode` together with `deriving Encode`, a
deriving handler that writes the encoding function of an inductive type
from its declaration, by structural recursion. The handler is the
counterpart of Lean's own `deriving Hashable`, with the constructor number
and the encodings of the arguments in place of hashes. It supports
recursive types and indexed families. It rejects mutual and nested
inductive types, and it rejects an implicit argument that the type of the
constructor does not determine, since leaving such an argument out could
lose information. Natural numbers are the only base case. They are an
inductive type too, but their derived encoding would be unary, so their
instance is written by hand.

Lists are an inductive type as well. Their derived encoding would mark
every entry with the number of `cons`. The length in front is the usual
convention, and it lets an algorithm skip a list, or find its end,
without reading its entries.

Types whose values are not built from constructors, such as graphs given
by an adjacency relation, are encoded through an explicit representation
by an encodable type, as the graphs of `Lax185574.Encodings`.

The size of a value, in bounds on running times and on outputs, is the
length of its encoding, `wordLength`.

No decoding function is part of the definition. A statement about an
algorithm only fixes what it reads and what it must write, and these are
determined by the encoding alone.
-/

namespace Lax185574.Encoding

universe u

/-- An encoding of the values of `α` as lists of natural numbers. -/
class Encode (α : Type u) where
  /-- The list of numbers encoding a value. -/
  encode : α → List ℕ

export Encode (encode)

/-- The size `‖a‖` of a value, as used in running-time bounds: the
length of its encoding. -/
def wordLength {α : Type u} [Encode α] (a : α) : ℕ := (encode a).length

/-- A natural number is encoded as itself. -/
instance : Encode ℕ where
  encode n := [n]

section Deriving

open Lean Elab Command Meta Term Deriving
open Lean.Parser.Term

/-- The match expression of the derived encoding function: one
alternative per constructor, whose right-hand side is the constructor
number (if there are several constructors) followed by the encodings of
the explicit arguments that are not proofs. Recursive arguments are
encoded by a recursive call. -/
def mkEncodeMatch (ctx : Deriving.Context) (header : Header) (indVal : InductiveVal) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  if indVal.ctors.isEmpty then
    return ← `(nomatch $(mkIdent header.targetNames[0]!):ident)
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for ctorName in indVal.ctors, ctorIdx in [0:indVal.ctors.length] do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt : TSyntax ``matchAlt ← forallTelescopeReducing ctorInfo.type fun xs resultType => do
      let mut patterns : Array Term := #[]
      for _ in [0:indVal.numIndices] do
        patterns := patterns.push (← `(_))
      let mut ctorArgs : Array Term := #[]
      for _ in [0:indVal.numParams] do
        ctorArgs := ctorArgs.push (← `(_))
      let mut parts : Array Term := #[]
      if indVal.ctors.length > 1 then
        parts := parts.push (← `([$(quote ctorIdx)]))
      for i in [0:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]!
        let a := mkIdent (← mkFreshUserName `a)
        ctorArgs := ctorArgs.push a
        let decl ← x.fvarId!.getDecl
        let xTy ← whnf decl.type
        if ← isProp decl.type then
          continue
        unless decl.binderInfo.isExplicit do
          unless resultType.containsFVar x.fvarId! do
            throwError "deriving Encode: the implicit argument {decl.userName} of \
              {ctorName} is not determined by the type of the constructor"
          continue
        match xTy.getAppFn with
        | .const declName .. =>
          if declName == indVal.name then
            parts := parts.push (← `($(mkIdent ctx.auxFunNames[0]!) $a:ident))
          else
            parts := parts.push (← `(Encode.encode $a:ident))
        | _ => parts := parts.push (← `(Encode.encode $a:ident))
      patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
      let rhs : Term ← if parts.isEmpty then `(([] : List Nat))
        else parts[1:].foldlM (fun acc p => `($acc ++ $p)) parts[0]!
      `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
    alts := alts.push alt
  `(match $[$discrs],* with $alts:matchAlt*)

/-- The commands defining the encoding function of the inductive type
`declName` and its `Encode` instance. -/
def mkEncodeInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Encode "encode" declName
  if ctx.usePartial then
    throwError "deriving Encode: mutual and nested inductive types are not supported"
  let indVal := ctx.typeInfos[0]!
  let header ← mkHeader ``Encode 1 indVal
  let body ← mkEncodeMatch ctx header indVal
  let fn ← `(def $(mkIdent ctx.auxFunNames[0]!):ident $(header.binders):bracketedBinder* :
      List Nat := $body:term)
  return #[fn] ++ (← mkInstanceCmds ctx ``Encode #[declName])

/-- The deriving handler for `Encode`. -/
def mkEncodeHandler (declNames : Array Name) : CommandElabM Bool := do
  unless ← declNames.allM isInductive do
    return false
  for declName in declNames do
    let cmds ← liftTermElabM <| mkEncodeInstanceCmds declName
    cmds.forM elabCommand
  return true

initialize registerDerivingHandler ``Encode mkEncodeHandler

end Deriving

end Lax185574.Encoding
