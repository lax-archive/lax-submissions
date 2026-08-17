import Lax3Proofs.Refine.CoverActiveBridge

/-!
# Synthesized active-prefix cover pass

The carrier-wide cover used one cell, `n`, for three roles: BFS carrier,
centre-loop bound, and assignment sentinel.  An active pass must separate
them.  Here `n` remains the BFS carrier, while `qn` stores the active count
`q` and is both the outer loop bound and the unassigned sentinel.

The implementation otherwise reuses the landed touched-only BFS and emission
loops verbatim.  In particular, it still scans only the reached queue prefix;
there is no carrier sweep inside a centre turn.
-/

namespace Lax3Proofs.Refine.CoverActiveSynth

open Lax13Proofs.Refine
open Lax13Proofs.Refine.Sepref Lax13Proofs.Refine.Ir Lax13Proofs.Refine.NRest
open Lax3Proofs.Refine.CoverSynth

/-! ## The active-sentinel emission rule -/

set_option maxHeartbeats 1000000 in
sepref_synth emitASynth (q c s kend xp₀ : ℕ) (reach dist xmem₀ asg₀ : List ℕ) :
  hnRefine (hnCtxt (natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn)
        (0, xp₀, xmem₀, asg₀) ("cvk", "xp", "xmem", "asg") ∗
      hnCtxt arrayAssn reach "q" ∗ hnCtxt arrayAssn dist "dist" ∗
      hnCtxt natAssn q "qn" ∗ hnCtxt natAssn c "c" ∗
      hnCtxt natAssn s "cvs" ∗ hnCtxt natAssn kend "tl" ∗
      hnCtxt natAssn 1 "one" ∗ junkCell "cvu" ∗ junkCell "cvd" ∗
      junkCell "cva" ∗ junkCell "cvw")
    _ _ ("cvk", "xp", "xmem", "asg")
      (natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn)
    (emitLoop reach dist q c s kend (0, xp₀, xmem₀, asg₀))

-- The comparison which decides whether an assignment is already set reads
-- `qn`, not the carrier cell `n`.
#guard emitASynth_impl =
  Com.while (Cond.lt (Operand.cell "cvk") (Operand.cell "tl"))
    ((Com.aget "cvu" "q" "cvk").seq
      ((Com.aget "cvd" "dist" "cvu").seq
        ((Com.aset "xmem" "xp" "cvu").seq
          ((Com.binop Lax13Proofs.Imp.Bop.add "xp" "xp" "one").seq
            ((Com.aget "cva" "asg" "cvu").seq
              ((Com.ite (Cond.lt (Operand.cell "cvd") (Operand.cell "cvs"))
                    (Com.ite (Cond.lt (Operand.cell "cva") (Operand.cell "qn"))
                      (Com.copy "cvw" "cva") (Com.copy "cvw" "c"))
                    (Com.ite (Cond.lt (Operand.cell "cva") (Operand.cell "qn"))
                      (Com.copy "cvw" "cva") (Com.copy "cvw" "cva"))).seq
                ((Com.aset "asg" "cvu" "cvw").seq
                  ((Com.binop Lax13Proofs.Imp.Bop.add "cvk" "cvk" "one").seq
                    (Com.skip.seq (Com.skip.seq Com.skip))))))))))

/-! ## One active centre and the active pass -/

/-- One active centre.  BFS is still over `n`; only emission uses `q` as its
sentinel. -/
noncomputable def turnFA (centre off tgt : List ℕ) (n q d s : ℕ) :
    CSt → NRest CSt ECost := fun t =>
  bindT mopZeroI fun i0 =>
    bindT (mopZeroIn t.2.2.1) fun h0 =>
      bindT (mopZeroIn t.2.2.2.1) fun k0 =>
        bindT (mopOrd centre t.1) fun src =>
          bindT (mopBfsE i0 h0 n d src off tgt t.2.2.2.2.2.2.1
              t.2.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2.2) fun st =>
            bindT (mopBinop .sub 1 st.2.2.2) fun z =>
              bindT (mopBinop .add st.2.2.2 z) fun kend =>
                bindT (pack4 k0 t.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1) fun e₀ =>
                  bindT (emitLoop st.2.1 st.1 q t.1 s kend e₀) fun e =>
                    bindT (mopAset t.2.2.2.2.2.2.1 src 0) fun A =>
                      bindT (mopSucc t.1) fun c' =>
                        bindT (mopAset t.2.2.2.2.2.2.2.1 c' e.2.1) fun XO =>
                          packC c' e.2.1 st.2.2.1 e.1 e.2.2.1 e.2.2.2
                            A XO st.1 st.2.1

def coverBfA (q : ℕ) : CSt → Bool := fun t => decide (t.1 < q)

/-- The active pass stops after `q` centres. -/
noncomputable def coverLoopA (centre off tgt : List ℕ) (n q d s : ℕ)
    (t₀ : CSt) : NRest CSt ECost :=
  irWhileIT coverI (coverBfA q) (turnFA centre off tgt n q d s) t₀

set_option maxHeartbeats 5000000 in
sepref_synth coverASynth (n q d s : ℕ) (centre off tgt : List ℕ) (t₀ : CSt) :
  hnRefine
    (hnCtxt (natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ
        arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn) t₀
        ("c", "xp", "head", "cvk", "xmem", "asg", "alv", "xoff", "dist", "q") ∗
      hnCtxt arrayAssn centre "ord" ∗ hnCtxt arrayAssn off "off" ∗
      hnCtxt arrayAssn tgt "tgt" ∗ hnCtxt natAssn n "n" ∗
      hnCtxt natAssn q "qn" ∗ hnCtxt natAssn (d + 1) "sent" ∗
      hnCtxt natAssn d "d" ∗ hnCtxt natAssn s "cvs" ∗
      hnCtxt natAssn 1 "one" ∗ hnCtxt natAssn 0 "cvz" ∗
      junkCell "i" ∗ junkCell "src" ∗ junkCell "a" ∗ junkCell "tl" ∗
      junkCell "v" ∗ junkCell "dv" ∗ junkCell "dv1" ∗ junkCell "k0" ∗
      junkCell "v1" ∗ junkCell "kend" ∗ junkCell "u" ∗ junkCell "au" ∗
      junkCell "du" ∗ junkCell "cvu" ∗ junkCell "cvd" ∗ junkCell "cva" ∗
      junkCell "cvw" ∗ junkCell "cvm" ∗ junkCell "cve")
    _ _ ("c", "xp", "head", "cvk", "xmem", "asg", "alv", "xoff", "dist", "q")
    (natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ natAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ
      arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn ×ₐ arrayAssn)
    (coverLoopA centre off tgt n q d s t₀)

-- Both active uses are pinned: the outer guard and the two assignment
-- comparisons read `qn`; the embedded BFS still reads carrier `n`.
#guard coverASynth_impl =
  Com.while (Cond.lt (Operand.cell "c") (Operand.cell "qn"))
    ((Com.const "i" 0).seq
      ((Com.binop Lax13Proofs.Imp.Bop.mul "head" "head" "cvz").seq
        ((Com.binop Lax13Proofs.Imp.Bop.mul "cvk" "cvk" "cvz").seq
          ((Com.aget "src" "ord" "c").seq
            (BfsQSynth.bfsQSynth_impl.seq
              ((Com.binop Lax13Proofs.Imp.Bop.sub "a" "one" "tl").seq
                ((Com.binop Lax13Proofs.Imp.Bop.add "i" "tl" "a").seq
                  ((Com.skip.seq (Com.skip.seq Com.skip)).seq
                    ((Com.while (Cond.lt (Operand.cell "cvk") (Operand.cell "i"))
                          ((Com.aget "v" "q" "cvk").seq
                            ((Com.aget "dv" "dist" "v").seq
                              ((Com.aset "xmem" "xp" "v").seq
                                ((Com.binop Lax13Proofs.Imp.Bop.add "xp" "xp" "one").seq
                                  ((Com.aget "dv1" "asg" "v").seq
                                    ((Com.ite (Cond.lt (Operand.cell "dv") (Operand.cell "cvs"))
                                          (Com.ite
                                            (Cond.lt (Operand.cell "dv1") (Operand.cell "qn"))
                                            (Com.copy "k0" "dv1") (Com.copy "k0" "c"))
                                          (Com.ite
                                            (Cond.lt (Operand.cell "dv1") (Operand.cell "qn"))
                                            (Com.copy "k0" "dv1") (Com.copy "k0" "dv1"))).seq
                                      ((Com.aset "asg" "v" "k0").seq
                                        ((Com.binop Lax13Proofs.Imp.Bop.add "cvk" "cvk" "one").seq
                                          (Com.skip.seq (Com.skip.seq Com.skip))))))))))).seq
                      ((Com.aset "alv" "src" "cvz").seq
                        ((Com.binop Lax13Proofs.Imp.Bop.add "c" "c" "one").seq
                          ((Com.aset "xoff" "c" "xp").seq
                            (Com.skip.seq
                              (Com.skip.seq
                                (Com.skip.seq
                                  (Com.skip.seq
                                    (Com.skip.seq
                                      (Com.skip.seq
                                        (Com.skip.seq (Com.skip.seq Com.skip))))))))))))))))))))

/-! ## A strict-prefix executable gate -/

/-- The carrier demo with active count and active assignment sentinel set to
`q`. -/
def gStateA (q : ℕ) : Ir.State :=
  let st := CoverSynth.gState 1 1
  { st with
    vars := fun x => if x = "qn" then q else st.vars x
    arrs := fun a => if a = "asg" then List.replicate 5 q else st.arrs a }

/-- Prefix offsets, the emitted arena, and assignments after three of five
centres. -/
def gRunA : Option (List ℕ) :=
  (Ir.evalFuel 200000 coverASynth_impl (gStateA 3)).bind fun p =>
    match p.1.arrs "xoff", p.1.arrs "xmem", p.1.arrs "asg" with
    | some xo, some xm, some ag => some (xo.take 4 ++ xm.take 8 ++ ag)
    | _, _, _ => none

-- The last vertex retains the active sentinel `3`; using carrier sentinel
-- `5` would leave every assignment equal to `3` and fail this gate.
#guard gRunA = some [0, 3, 6, 8, 0, 1, 2, 1, 2, 3, 2, 3, 0, 0, 1, 2, 3]

#print axioms emitASynth
#print axioms coverASynth

end Lax3Proofs.Refine.CoverActiveSynth
