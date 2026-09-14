/-
# Sipser's reduction: from acceptance to the Post Correspondence Problem

Putting the previous files together, we obtain Sipser's construction of Theorem 5.15:
for a Turing machine `M` and an input `w` we build a PCP instance `sipserPCP M w`
which has a match if and only if `M` accepts `w`.
-/
import Lax251941Proofs.Source.PCP.TuringMachine

namespace Lax251941Proofs.PCP

variable (M : TM) (w : List ℕ)

/-- The MPCP instance of Sipser's construction (parts 1–7 of the proof of Theorem 5.15). -/
def sipserMPCP : Inst Sym :=
  mpcpOf (M.fullSRS w) Sym.hash Sym.start (M.startCfg w) [Sym.state M.qacc]

/-- The PCP instance of Sipser's construction, obtained from the MPCP instance by the
`⋆` trick. -/
def sipserPCP : Inst Sym :=
  pcpOfMpcp Sym.star Sym.diamond (sipserMPCP M w)

lemma hash_not_mem_alphabet : Sym.hash ∉ M.alphabet w := by
  intro h
  simp [TM.alphabet] at h

lemma start_not_mem_alphabet : Sym.start ∉ M.alphabet w := by
  intro h
  simp [TM.alphabet] at h

lemma star_not_mem_alphabet : Sym.star ∉ M.alphabet w := by
  intro h
  simp [TM.alphabet] at h

lemma diamond_not_mem_alphabet : Sym.diamond ∉ M.alphabet w := by
  intro h
  simp [TM.alphabet] at h

/-- The hypotheses of the reduction from string rewriting to MPCP are satisfied. -/
lemma sipser_mpcpWF :
    MpcpWF (M.fullSRS w) Sym.hash Sym.start (M.startCfg w) [Sym.state M.qacc] where
  wf := fullSRS_wf M w
  hash_not_mem := hash_not_mem_alphabet M w
  start_not_mem := start_not_mem_alphabet M w
  hash_ne_start := by simp
  s_sub := startCfg_mem_alphabet M w
  t_sub := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact M.state_mem_alphabet w M.qacc_mem_states

/-- The hypotheses of the `⋆` trick are satisfied by the MPCP instance. -/
lemma sipser_starWF : StarWF Sym.star Sym.diamond (sipserMPCP M w) where
  star_ne_diamond := by simp
  star_not_top := by
    intro d hd hc
    rcases (mem_symbols_of_mem_mpcpOf (sipser_mpcpWF M w) hd).1 Sym.star hc with h | h | h
    · exact star_not_mem_alphabet M w h
    · simp at h
    · simp at h
  star_not_bot := by
    intro d hd hc
    rcases (mem_symbols_of_mem_mpcpOf (sipser_mpcpWF M w) hd).2 Sym.star hc with h | h | h
    · exact star_not_mem_alphabet M w h
    · simp at h
    · simp at h
  diamond_not_top := by
    intro d hd hc
    rcases (mem_symbols_of_mem_mpcpOf (sipser_mpcpWF M w) hd).1 Sym.diamond hc with h | h | h
    · exact diamond_not_mem_alphabet M w h
    · simp at h
    · simp at h
  diamond_not_bot := by
    intro d hd hc
    rcases (mem_symbols_of_mem_mpcpOf (sipser_mpcpWF M w) hd).2 Sym.diamond hc with h | h | h
    · exact diamond_not_mem_alphabet M w h
    · simp at h
    · simp at h
  top_ne_nil := fun d hd => (ne_nil_of_mem_mpcpOf (sipser_mpcpWF M w) hd).1
  bot_ne_nil := fun d hd => (ne_nil_of_mem_mpcpOf (sipser_mpcpWF M w) hd).2

/-- **The MPCP instance built from `M` and `w` has a match starting with its first domino
if and only if `M` accepts `w`.** -/
theorem hasMatchFirst_sipserMPCP_iff : HasMatchFirst (sipserMPCP M w) ↔ M.Accepts w :=
  (hasMatchFirst_mpcpOf_iff (sipser_mpcpWF M w)).trans (reaches_qacc_iff_accepts M w)

/-- **Sipser's Theorem 5.15, reduction step.**  The PCP instance built from `M` and `w`
has a match if and only if `M` accepts `w`. -/
theorem hasMatch_sipserPCP_iff : HasMatch (sipserPCP M w) ↔ M.Accepts w :=
  (hasMatch_pcpOfMpcp_iff (sipser_starWF M w)).trans (hasMatchFirst_sipserMPCP_iff M w)

end Lax251941Proofs.PCP
