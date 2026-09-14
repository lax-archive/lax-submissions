/- Computability of the constructions used in the reduction of Theorem
`thm:equivalence-rational-functions` to Theorem `thm:equivalence-weighted-automata`: the product
weighted automaton `pairW` of `RequestProject/PartB/PairWeighted.lean` is a primitive recursive
function of the base `K` and of the two codes.

Mathlib's `Primrec` API has no arithmetic on `ℤ`, but the weights produced here
are the *natural* numbers `K ^ |x|`, `iota K x` and `1`, written as fractions
with denominator one; all that is needed is therefore the primitive recursiveness
of the coercion `ℕ → ℤ`, which is proved below from the fact that the encoding of
`ℤ` sends a nonnegative integer `n` to `2 * n`.
-/
import Lax132576Proofs.Source.PartB.PairWeighted
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace PairWeighted

open LabAut CodeMerge Iota LenDec

/-- The coercion `ℕ → ℤ` is primitive recursive: the standard encoding of `ℤ`
sends the nonnegative integer `n` to `2 * n`. -/
lemma primrec_intOfNat : Primrec (fun n : ℕ => (n : ℤ)) := by
  have h : Primrec (fun n : ℕ => 2 * n) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  exact Primrec.encode_iff.1 (h.of_eq (fun _ => rfl))

/-- Exponentiation is primitive recursive. -/
lemma primrec_pow : Primrec₂ (fun a b : ℕ => a ^ b) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The product of two lists is primitive recursive. -/
lemma primrec_sprod {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → List β} {g : α → List γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a) ×ˢ (g a)) := by
  have h : Primrec (fun a => (f a).flatMap (fun b => (g a).map (fun c => (b, c)))) :=
    Primrec.list_flatMap hf
      (Primrec.list_map (hg.comp Primrec.fst)
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact h.of_eq (fun _ => rfl)

lemma primrec_st : Primrec (fun z : (ℕ × ℕ) × ℕ => st z.1.1 z.1.2 z.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)))
    Primrec.snd

lemma primrec_bits : Primrec bits := by
  refine Primrec.ite (c := fun i : ℕ => i = 0) (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const (0, 0)) ?_
  exact Primrec.ite (c := fun i : ℕ => i = 1) (Primrec.eq.comp Primrec.id (Primrec.const 1))
    (Primrec.const (0, 1)) (Primrec.const (1, 1))

lemma primrec_selZ :
    Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => selZ z.1 z.2.1 z.2.2) := by
  -- the components of the argument
  have hK : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.1) := Primrec.fst
  have hs : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hi : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hb : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => bits z.2.2) :=
    primrec_bits.comp hi
  have hsrcArg : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      ((z.2.1.1.1, z.2.1.2.1), (bits z.2.2).1)) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp hs) (Primrec.fst.comp ht))
      (Primrec.fst.comp hb)
  have hsrc : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      st z.2.1.1.1 z.2.1.2.1 (bits z.2.2).1) :=
    (primrec_st.comp hsrcArg).of_eq (fun _ => rfl)
  have htgtArg : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      ((z.2.1.1.2.2.2, z.2.1.2.2.2.2), (bits z.2.2).2)) :=
    Primrec.pair (Primrec.pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hs)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ht))))
      (Primrec.snd.comp hb)
  have htgt : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      st z.2.1.1.2.2.2 z.2.1.2.2.2.2 (bits z.2.2).2) :=
    (primrec_st.comp htgtArg).of_eq (fun _ => rfl)
  have hlab : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hs)
  have hout : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.1.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hs))
  have hpow : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      ((z.1 ^ z.2.1.1.2.2.1.length : ℕ) : ℤ)) :=
    primrec_intOfNat.comp (primrec_pow.comp hK (Primrec.list_length.comp hout))
  have hiota : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      ((iota z.1 z.2.1.1.2.2.1 : ℕ) : ℤ)) :=
    primrec_intOfNat.comp (primrec_iota.comp hK hout)
  have hw : Primrec (fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ =>
      (if z.2.2 = 0 then ((z.1 ^ z.2.1.1.2.2.1.length : ℕ) : ℤ)
        else if z.2.2 = 1 then ((iota z.1 z.2.1.1.2.2.1 : ℕ) : ℤ) else (1 : ℤ))) := by
    refine Primrec.ite (c := fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.2 = 0)
      (Primrec.eq.comp hi (Primrec.const 0)) hpow ?_
    exact Primrec.ite (c := fun z : ℕ × (CodeMerge.Tr × CodeMerge.Tr) × ℕ => z.2.2 = 1)
      (Primrec.eq.comp hi (Primrec.const 1)) hiota (Primrec.const 1)
  exact (Primrec.pair hsrc (Primrec.pair hlab
    (Primrec.pair (Primrec.pair hw (Primrec.const 1)) htgt))).of_eq (fun _ => rfl)

lemma primrec_pairBase :
    Primrec (fun z : RelCode × RelCode => pairBase z.1 z.2) := by
  have hprod : Primrec (fun z : RelCode × RelCode => z.1.1 ×ˢ z.2.1) :=
    primrec_sprod (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hfil : Primrec (fun z : RelCode × RelCode =>
      (z.1.1 ×ˢ z.2.1).filter (fun y => decide (y.1.2.1 = y.2.2.1))) :=
    CodeMerge.primrec_filter hprod
      (primrec_decEq
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact (primrec_sprod hfil (Primrec.const [0, 1, 2])).of_eq (fun _ => rfl)

lemma primrec_pairW :
    Primrec (fun z : ℕ × RelCode × RelCode => pairW z.1 z.2.1 z.2.2) := by
  have hK : Primrec (fun z : ℕ × RelCode × RelCode => z.1) := Primrec.fst
  have hbase : Primrec (fun z : ℕ × RelCode × RelCode => pairBase z.2.1 z.2.2) :=
    primrec_pairBase.comp Primrec.snd
  have htrans : Primrec (fun z : ℕ × RelCode × RelCode => pairTrans z.1 z.2.1 z.2.2) := by
    have : Primrec (fun z : ℕ × RelCode × RelCode =>
        (pairBase z.2.1 z.2.2).map (fun zi => selZ z.1 zi.1 zi.2)) :=
      Primrec.list_map hbase
        (primrec_selZ.comp (Primrec.pair (hK.comp Primrec.fst)
          (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))).to₂
    exact this.of_eq (fun _ => rfl)
  have hinit : Primrec (fun z : ℕ × RelCode × RelCode => pairInit z.2.1 z.2.2) := by
    have hp : Primrec (fun z : ℕ × RelCode × RelCode => z.2.1.2.1 ×ˢ z.2.2.2.1) :=
      primrec_sprod (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have : Primrec (fun z : ℕ × RelCode × RelCode =>
        (z.2.1.2.1 ×ˢ z.2.2.2.1).map (fun y => st y.1 y.2 0)) :=
      Primrec.list_map hp
        (primrec_st.comp (Primrec.pair
          (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
          (Primrec.const 0))).to₂
    exact this.of_eq (fun _ => rfl)
  have hfin : Primrec (fun z : ℕ × RelCode × RelCode => pairFin z.2.1 z.2.2) := by
    have hp : Primrec (fun z : ℕ × RelCode × RelCode => z.2.1.2.2 ×ˢ z.2.2.2.2) :=
      primrec_sprod (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have : Primrec (fun z : ℕ × RelCode × RelCode =>
        (z.2.1.2.2 ×ˢ z.2.2.2.2).map (fun y => st y.1 y.2 1)) :=
      Primrec.list_map hp
        (primrec_st.comp (Primrec.pair
          (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
          (Primrec.const 1))).to₂
    exact this.of_eq (fun _ => rfl)
  exact (Primrec.pair htrans (Primrec.pair hinit hfin)).of_eq (fun _ => rfl)

end PairWeighted
end Lax132576Proofs.Transducers
