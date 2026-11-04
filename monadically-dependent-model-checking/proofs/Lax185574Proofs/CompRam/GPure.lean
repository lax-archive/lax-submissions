import Lax185574Proofs.CompRam.GBase
import Lax185574Proofs.CompRam.SizeEnd

/-!
The words that the glue command of lem:compose writes, as lists.

The output of a call is the head `[1, L, 0, 0, j, count]` (with the
length `L` of the state filled in last, `outW_call`), the frames of the
words of the stack and the query of the switch. The three queries have a
fixed head of three lengths and the two fixed questions (`qWord_sh`,
`qWord_re`, `qWord_ca`), where the length `lDSq` of the fixed question
`dSq` of the rank shift is known.

`Built j r ob σ`: after the build of a round with outcome `r` and next
counter `j`, the buffer holds `ob`, the output `outW j r` is `ob` with
`dSq` inserted after `sp` cells if `dq = 1`, and the query of a call is
the segment `qa`, `ql` of the buffer, of kind `qk`.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574Proofs.Simulate

theorem length_dSq : dSq.length = lDSq := by
  rw [dSq_eq, toWord_ext_word]
  simp only [List.length_append, length_toWord_atL2, length_toWord_atL1]
  norm_num [lDSq]

theorem length_dRq : dRq.length = 5 := by rw [dRq_eq]; rfl

theorem length_dRa : dRa.length = 4 := by rw [dRa_eq]; rfl

theorem qWord_sh (w : List ℕ) : qWord (.sh w) = [5, w.length, 1, 0, 0, 0, 0, 0] ++ w ++ [0] := by
  show swIn dRq w [0] = _
  simp [swIn, dRq_eq]

theorem qWord_re (w : List ℕ) : qWord (.re w) = [w.length, lDSq, 1] ++ w ++ dSq ++ [0] := by
  show swIn w dSq [0] = _
  simp [swIn, length_dSq]

theorem qWord_ca (ws : List (List ℕ)) :
    qWord (.ca ws) = [5, lDSq, (toWord ws).length, 0, 0, 0, 0, 0] ++ dSq ++ toWord ws := by
  show swIn dRq dSq (toWord ws) = _
  simp [swIn, dRq_eq, length_dSq]

theorem stWords_cons (f : Fr) (S : List Fr) : stWords (f :: S) = frWords f ++ stWords S := by
  simp [stWords]

theorem length_stWords (S : List Fr) : (stWords S).length = 7 * S.length := by
  induction S with
  | nil => rfl
  | cons f S ih => rw [stWords_cons, List.length_append, ih]; simp [frWords]; ring

theorem stWords_drop7 (f : Fr) (S : List Fr) : (stWords (f :: S)).drop 7 = stWords S := by
  rw [stWords_cons]; exact List.drop_left' (by simp [frWords])

theorem stWords_take7 (f : Fr) (S : List Fr) : (stWords (f :: S)).take 7 = frWords f := by
  rw [stWords_cons]; exact List.take_left' (by simp [frWords])

theorem outW_call (j : ℕ) (S : List Fr) (q : Qry) :
    outW j (.call S q) = ([1, 0, 0, 0, j, (stWords S).length] ++ frames (stWords S)).set 1
      (([1, 0, 0, 0, j, (stWords S).length] ++ frames (stWords S)).length - 3) ++ qWord q := by
  simp only [outW, stWord, toWord_words, List.length_cons, List.cons_append,
    List.nil_append, List.set_cons_succ, List.set_cons_zero]
  congr 1

/-- The kind of a query, as the scalar `qk` holds it. -/
def qkind : Qry → ℕ
  | .re _ => 0
  | .sh _ => 1
  | .ca _ => 2

/-- The query of a call is the segment `qa`, `ql` of the buffer. -/
def QAt (r : Res) (ob : List ℕ) (σ : Env) : Prop :=
  match r with
  | .call _ q => σ.vars "qk" = qkind q ∧ σ.vars "qa" + σ.vars "ql" ≤ ob.length ∧
      seg ob (σ.vars "qa") (σ.vars "ql") = realQ q
  | _ => σ.vars "qk" = 3

/-- The buffer and the scalars after the build of a round. -/
def Built (j : ℕ) (r : Res) (ob : List ℕ) (σ : Env) : Prop :=
  Filled "OB" "po" ob σ ∧ σ.vars "sp" ≤ ob.length ∧ (σ.vars "dq" = 0 ∨ σ.vars "dq" = 1) ∧
    outW j r = ob.take (σ.vars "sp") ++ (if σ.vars "dq" = 1 then dSq else []) ++ ob.drop (σ.vars "sp") ∧
    QAt r ob σ

/-! ### The input of a round -/

/-- The cells of `x` after the input of round `j ≥ 1` is read. -/
def imgJ (j : ℕ) (S : List Fr) (o : List ℕ) : List ℕ := stWord j S ++ toWord o

theorem imgJ_drop2 (j : ℕ) (S : List Fr) (o : List ℕ) :
    (imgJ j S o).drop 2 = toWord (stWords S) ++ toWord o := by
  simp [imgJ, stWord]

theorem length_stWord (j : ℕ) (S : List Fr) :
    (stWord j S).length = 2 + (toWord (stWords S)).length := by
  simp [stWord]; omega

theorem imgJ_get1 (j : ℕ) (S : List Fr) (o : List ℕ) : (imgJ j S o).getD 1 0 = j := by
  simp [imgJ, stWord]

theorem imgJ_get2 (j : ℕ) (S : List Fr) (o : List ℕ) :
    (imgJ j S o).getD 2 0 = (stWords S).length := by
  simp [imgJ, stWord, toWord_words]

theorem imgJ_dropL (j : ℕ) (S : List Fr) (o : List ℕ) :
    (imgJ j S o).drop (stWord j S).length = o.length :: o := by
  simp [imgJ, toWord_listNat]

theorem glueIn_eq (j : ℕ) (S : List Fr) (o : List ℕ) :
    glueIn j S o = [1, (stWord j S).length] ++ (stWord j S ++ [o.length]) ++ o := by
  simp [glueIn]

/-! ### The part of the answer of a phase -/

theorem pick_re (o : List ℕ) : pick 4 o = (o.drop 0).take (o.length - 428) := by
  simp [pick, length_dSa]; omega

theorem pick_sh {ph : ℕ} (h : ph = 1 ∨ ph = 2) (o : List ℕ) :
    pick ph o = (o.drop 4).take (o.length - 5) := by
  have h4 : ph ≠ 4 := by omega
  simp only [pick, h4, if_false, h, if_true, length_dRa]
  congr 1

theorem pick_ca {ph : ℕ} (h4 : ph ≠ 4) (h1 : ph ≠ 1) (h2 : ph ≠ 2) (o : List ℕ) :
    pick ph o = (o.drop 431).take (o.length - 431) := by
  simp only [pick, h4, h1, h2, if_false, or_self, length_dRa, length_dSa]
  rw [List.take_of_length_le (by simp)]

end Lax185574Proofs.CompRam
