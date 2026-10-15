import Lax457868Proofs.SourceRenaming
import Lax457868Proofs.ReusedOriginal.Construction.NearCollectSource
import Lax457868Proofs.ExceptionPhaseSource
import Lax11Proofs.CCGraph

/-! Degree-local, duplicate-tolerant collection of the two active
neighborhoods needed by a local repair draw. -/

namespace Lax457868Proofs.RepairDomainSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax11Proofs.CC
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ReusedOriginal.Construction.NearCollectSource
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionRefinementStep

noncomputable section

/-- Static names for reusing the old collector with any active mask and
private stamp/list/length arrays. Choose distinct literals at call sites. -/
def neighborhoodNames (activeName marks list len : String) : Names where
  scalar := Equiv.swap "neighborLen" len
  array := Equiv.swap "activeB" activeName *
    Equiv.swap "stamp" marks * Equiv.swap "neighbors" list

def repairCollectNames (marks list len : String) : Names :=
  neighborhoodNames "activeA" marks list len

def collectRepairB : Com :=
  renameCom (repairCollectNames "repairBMarks" "repairBList" "repairBLen")
    (.while (.lt (.var "j") (.var "jend")) collectNeighborBody)

def collectRepairR : Com :=
  renameCom (repairCollectNames "repairRMarks" "repairRList" "repairRLen")
    (.while (.lt (.var "j") (.var "jend")) collectNeighborBody)

/-- Initialize the shared CSR cursor from the runtime-selected vertex.
Only scalar state is written; the graph and private arrays stay intact. -/
def prepareNeighborAt (vertexVar lenName : String) : Com :=
  seqs [
    .assign "token" (.lit 1),
    .assign lenName (.lit 0),
    .assign "j" (.get "off" (.var vertexVar)),
    .assign "jend" (.get "off" (.add (.var vertexVar) (.lit 1)))]

def collectNeighborhoodAt (ρ : Names) (vertexVar lenName : String) : Com :=
  seqs [prepareNeighborAt vertexVar lenName,
    renameCom ρ (.while (.lt (.var "j") (.var "jend")) collectNeighborBody)]

def collectRepairBAt : Com :=
  collectNeighborhoodAt
    (repairCollectNames "repairBMarks" "repairBList" "repairBLen")
    "repairB" "repairBLen"

def collectRepairRAt : Com :=
  collectNeighborhoodAt
    (repairCollectNames "repairRMarks" "repairRList" "repairRLen")
    "repairRep" "repairRLen"

/-- Reading the two CSR offsets and resetting a private length costs a
constant number of source steps. -/
lemma prepareNeighborAt_run
    {B n b : ℕ} {off : ℕ → ℕ} {σ : Env} {vertexVar lenName : String}
    (hvertexNames : vertexVar ≠ "token" ∧ vertexVar ≠ lenName ∧
      vertexVar ≠ "j" ∧ vertexVar ≠ "jend")
    (hlenNames : lenName ≠ "token" ∧ lenName ≠ "j" ∧
      lenName ≠ "jend" ∧ lenName ≠ "n")
    (hvertex : σ.vars vertexVar = b)
    (hn : σ.vars "n" = n)
    (hoff : σ.arrs "off" = arrOf (n + 1) off)
    (hb : b < n) (hb1B : b + 1 < B)
    (hloB : off b < B) (hhiB : off (b + 1) < B)
    (honeB : 1 < B) :
    ∃ σ', Run B (prepareNeighborAt vertexVar lenName) σ σ' 18 ∧
      σ'.vars "j" = off b ∧ σ'.vars "jend" = off (b + 1) ∧
      σ'.vars "token" = 1 ∧ σ'.vars lenName = 0 ∧
      σ'.vars vertexVar = b ∧ σ'.vars "n" = n ∧
      σ'.arrs "off" = arrOf (n + 1) off ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₁ := σ.setVar "token" 1
  let σ₂ := σ₁.setVar lenName 0
  let σ₃ := σ₂.setVar "j" (off b)
  let σ₄ := σ₃.setVar "jend" (off (b + 1))
  have rtoken : Run B (.assign "token" (.lit 1)) σ σ₁ 2 := by
    simpa [σ₁] using (Run.assign (evalB_lit honeB))
  have rlen : Run B (.assign lenName (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hvertex₂ : σ₂.vars vertexVar = b := by
    simp [σ₂, σ₁, hvertex, hvertexNames.1, hvertexNames.2.1]
  have hgetLo : (σ₂.arrs "off")[b]? = some (off b) := by
    simpa [σ₂, σ₁, hoff] using
      (getElem?_arrOf off (show b < n + 1 by omega))
  have hevalLo : (Expr.get "off" (.var vertexVar)).evalB B σ₂ =
      some (off b) := by
    apply evalB_get
    · exact evalB_var (by rw [hvertex₂]; omega)
    · simpa [hvertex₂] using hgetLo
    · exact hloB
  have rj : Run B (.assign "j" (.get "off" (.var vertexVar)))
      σ₂ σ₃ 6 := (Run.assign hevalLo).mono (by norm_num [Expr.size])
  have hvertex₃ : σ₃.vars vertexVar = b := by
    simp [σ₃, hvertex₂, hvertexNames.2.2.1]
  have hevalAdd : (Expr.add (.var vertexVar) (.lit 1)).evalB B σ₃ =
      some (b + 1) := by
    apply evalB_bin
    · have hbound : σ₃.vars vertexVar < B := by rw [hvertex₃]; omega
      simpa [hvertex₃] using (evalB_var (B := B) hbound)
    · exact evalB_lit honeB
    · exact hb1B
  have hgetHi : (σ₃.arrs "off")[b + 1]? = some (off (b + 1)) := by
    simpa [σ₃, σ₂, σ₁, hoff] using
      (getElem?_arrOf off (show b + 1 < n + 1 by omega))
  have hevalHi : (Expr.get "off" (.add (.var vertexVar) (.lit 1))).evalB B
      σ₃ = some (off (b + 1)) :=
    evalB_get hevalAdd hgetHi hhiB
  have rjend : Run B
      (.assign "jend" (.get "off" (.add (.var vertexVar) (.lit 1))))
      σ₃ σ₄ 8 := (Run.assign hevalHi).mono (by norm_num [Expr.size])
  have rrun : Run B (prepareNeighborAt vertexVar lenName) σ σ₄ 18 := by
    simpa [prepareNeighborAt, seqs] using
      rtoken.seq (rlen.seq (rj.seq rjend))
  refine ⟨σ₄, rrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σ₄, σ₃]
  · simp [σ₄]
  · simp [σ₄, σ₃, σ₂, σ₁, Ne.symm hlenNames.1]
  · simp [σ₄, σ₃, σ₂, hlenNames.2.1, hlenNames.2.2.1]
  · simp [σ₄, hvertex₃, hvertexNames.2.2.2]
  · exact (rrun.frame_var "n" (by
      simp [prepareNeighborAt, seqs, Com.wvars,
        Ne.symm hlenNames.2.2.2])).trans hn
  · exact (rrun.frame_arr "off" (by
      simp [prepareNeighborAt, seqs, Com.warrs])).trans hoff
  · intro a; exact rrun.frame_arr a (by
      simp [prepareNeighborAt, seqs, Com.warrs])
  · exact rrun.frame_inp (by
      simp [prepareNeighborAt, seqs, Com.reads])
  · exact rrun.out_eq (by
      simp [prepareNeighborAt, seqs, Com.NoWrite])

/-- Transport of the verified duplicate-safe CSR collector to any statically
renamed active mask and private stamp/list/length arrays. It tolerates CSR
duplicates and produces the exact zero-one membership indicator. -/
lemma collectNeighborhood_run (ρ : Names)
    (activeName marksName listName lenName : String)
    (hjMap : ρ.scalar "j" = "j")
    (hjendMap : ρ.scalar "jend" = "jend")
    (htokenMap : ρ.scalar "token" = "token")
    (hnMap : ρ.scalar "n" = "n")
    (hlenMap : ρ.scalar "neighborLen" = lenName)
    (hactiveMap : ρ.array "activeB" = activeName)
    (htargetMap : ρ.array "tgt" = "tgt")
    (hmarksMap : ρ.array "stamp" = marksName)
    (hlistMap : ρ.array "neighbors" = listName)
    {B n targetCap lo hi : ℕ} {active target list : ℕ → ℕ} {σ : Env}
    (hj : σ.vars "j" = lo) (hjend : σ.vars "jend" = hi)
    (htoken : σ.vars "token" = 1) (hn : σ.vars "n" = n)
    (hlohi : lo ≤ hi) (hhi : hi ≤ targetCap)
    (hactive : σ.arrs activeName = arrOf n active)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hmarks : σ.arrs marksName = arrOf n (fun _ => 0))
    (hlist : σ.arrs listName = arrOf n list)
    (hlen : σ.vars lenName = 0)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (honeB : 1 < B) :
    ∃ σ' marks' list',
      Run B (renameCom ρ
        (.while (.lt (.var "j") (.var "jend")) collectNeighborBody))
        σ σ' (54 * (hi - lo) + 4) ∧
      σ'.arrs marksName = arrOf n marks' ∧
      σ'.arrs listName = arrOf n list' ∧
      σ'.vars lenName = (activeTargets target active lo hi).card ∧
      PrefixEnumerates (activeTargets target active lo hi).card list'
        (activeTargets target active lo hi) ∧
      (∀ v < n, marks' v = 1 ↔ v ∈ activeTargets target active lo hi) ∧
      (∀ v < n, marks' v ≤ 1) ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs "tgt" = arrOf targetCap target ∧
      σ'.vars "j" = hi ∧ σ'.vars "token" = 1 ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let τ := renameEnv ρ.inverse σ
  have hjτ : τ.vars "j" = lo := by
    change σ.vars (ρ.scalar "j") = lo
    rw [hjMap]; exact hj
  have hjendτ : τ.vars "jend" = hi := by
    change σ.vars (ρ.scalar "jend") = hi
    rw [hjendMap]; exact hjend
  have htokenτ : τ.vars "token" = 1 := by
    change σ.vars (ρ.scalar "token") = 1
    rw [htokenMap]; exact htoken
  have hnτ : τ.vars "n" = n := by
    change σ.vars (ρ.scalar "n") = n
    rw [hnMap]; exact hn
  have hactiveτ : τ.arrs "activeB" = arrOf n active := by
    change σ.arrs (ρ.array "activeB") = arrOf n active
    rw [hactiveMap]; exact hactive
  have htargetτ : τ.arrs "tgt" = arrOf targetCap target := by
    change σ.arrs (ρ.array "tgt") = arrOf targetCap target
    rw [htargetMap]; exact htarget
  have hmarksτ : τ.arrs "stamp" = arrOf n (fun _ => 0) := by
    change σ.arrs (ρ.array "stamp") = arrOf n (fun _ => 0)
    rw [hmarksMap]; exact hmarks
  have hlistτ : τ.arrs "neighbors" = arrOf n list := by
    change σ.arrs (ρ.array "neighbors") = arrOf n list
    rw [hlistMap]; exact hlist
  have hlenτ : τ.vars "neighborLen" = 0 := by
    change σ.vars (ρ.scalar "neighborLen") = 0
    rw [hlenMap]; exact hlen
  have hI : NeighborInv B n targetCap lo hi 1 active target τ :=
    neighborInv_initial hjτ hjendτ htokenτ hnτ hlohi hhi
      hactiveτ htargetτ hmarksτ hlistτ hlenτ
      (by intro v hv; decide)
      (by intro v hv; decide)
      (by intro v hv; omega)
  obtain ⟨τ', rcollect, hI', hjdone⟩ :=
    collectNeighborLoop_run hI htargetRange hactiveB hnB
      htargetCapB (by omega : 1 < B) honeB
  rcases hI' with ⟨marks', list', _hlo, _hhi, _hjend,
    htoken', _hn', _hcap, hactive', htarget', hmarks', hstack,
    henum, hmem, hbound, _hmarksB⟩
  rw [hjdone] at hstack henum hmem
  let σ' := renameEnv ρ τ'
  have hrun : Run B (renameCom ρ
      (.while (.lt (.var "j") (.var "jend")) collectNeighborBody))
      σ σ' (54 * (hi - lo) + 4) := by
    simpa [σ', τ] using run_rename ρ rcollect
  refine ⟨σ', marks', list', hrun, ?_, ?_, ?_, henum,
    hmem, hbound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmarksMap]
    simpa [σ'] using hmarks'
  · rw [← hlistMap]
    simpa [σ'] using hstack.arr
  · rw [← hlenMap]
    simpa [σ'] using (show τ'.vars "neighborLen" =
      (activeTargets target active lo hi).card by
        simpa [hjdone] using hstack.height)
  · rw [← hactiveMap]
    simpa [σ'] using hactive'
  · rw [← htargetMap]
    simpa [σ'] using htarget'
  · rw [← hjMap]
    simpa [σ'] using hjdone
  · rw [← htokenMap]
    simpa [σ'] using htoken'
  · exact hrun.frame_inp (by
      simp [renameCom, collectNeighborBody, seqs, inc, Com.reads])
  · exact hrun.out_eq (by
      simp [renameCom, collectNeighborBody, seqs, inc, Com.NoWrite])

/-- Read the selected vertex's offsets at runtime, then run the transported
duplicate-safe collector. No neighborhood set is supplied as an input
array; the certified set is reconstructed from CSR and the active mask. -/
lemma collectNeighborhoodAt_run
    (ρ : Names) (vertexVar activeName marksName listName lenName : String)
    (hvertexNames : vertexVar ≠ "token" ∧ vertexVar ≠ lenName ∧
      vertexVar ≠ "j" ∧ vertexVar ≠ "jend")
    (hlenNames : lenName ≠ "token" ∧ lenName ≠ "j" ∧
      lenName ≠ "jend" ∧ lenName ≠ "n")
    (hjMap : ρ.scalar "j" = "j")
    (hjendMap : ρ.scalar "jend" = "jend")
    (htokenMap : ρ.scalar "token" = "token")
    (hnMap : ρ.scalar "n" = "n")
    (hlenMap : ρ.scalar "neighborLen" = lenName)
    (hactiveMap : ρ.array "activeB" = activeName)
    (htargetMap : ρ.array "tgt" = "tgt")
    (hmarksMap : ρ.array "stamp" = marksName)
    (hlistMap : ρ.array "neighbors" = listName)
    {B n targetCap b : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {active list : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hvertex : σ.vars vertexVar = b) (hn : σ.vars "n" = n)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs activeName = arrOf n active)
    (hmarks : σ.arrs marksName = arrOf n (fun _ => 0))
    (hlist : σ.arrs listName = arrOf n list)
    (hb : b < n) (hactiveB : ∀ v < n, active v < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B) :
    ∃ σ' marks' list',
      Run B (collectNeighborhoodAt ρ vertexVar lenName) σ σ'
        (54 * (offset x (b + 1) - offset x b) + 22) ∧
      σ'.arrs marksName = arrOf n marks' ∧
      σ'.arrs listName = arrOf n list' ∧
      σ'.vars lenName =
        (activeTargets (target x) active (offset x b) (offset x (b + 1))).card ∧
      PrefixEnumerates
        (activeTargets (target x) active (offset x b) (offset x (b + 1))).card
        list' (activeTargets (target x) active (offset x b) (offset x (b + 1))) ∧
      (∀ v < n, marks' v = 1 ↔
        v ∈ activeTargets (target x) active (offset x b) (offset x (b + 1))) ∧
      (∀ v < n, marks' v ≤ 1) ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.vars "j" = offset x (b + 1) ∧
      σ'.vars "token" = 1 ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let lo := offset x b
  let hi := offset x (b + 1)
  have hlohi : lo ≤ hi := hx.offset_mono b hb
  have hhiCap : hi ≤ targetCap := by
    change offset x (b + 1) ≤ targetCap
    rw [htargetCap, ← hx.offset_last]
    exact offset_mono' hx (by omega) le_rfl
  have hloB : lo < B := lt_of_le_of_lt hlohi
    (lt_of_le_of_lt hhiCap htargetCapB)
  have hhiB : hi < B := lt_of_le_of_lt hhiCap htargetCapB
  obtain ⟨σ₁, rprep, hj₁, hjend₁, htoken₁, hlen₁,
    _hvertex₁, hn₁, _hoff₁, harrFrame, _hinp₁, _hout₁⟩ :=
    prepareNeighborAt_run hvertexNames hlenNames hvertex hn hoff
      hb (by omega) hloB hhiB (by omega)
  have htargetRange : ∀ j, lo ≤ j → j < hi → target x j < n := by
    intro j _ hjhi
    apply hx.target_lt j
    rw [← htargetCap]
    exact hjhi.trans_le hhiCap
  obtain ⟨σ₂, marks', list', rcollect, hmarks₂, hlist₂,
    hlen₂, henum₂, hmem₂, hbound₂, hactive₂, htarget₂,
    hj₂, htoken₂, _hinp₂, _hout₂⟩ :=
    collectNeighborhood_run ρ activeName marksName listName lenName
      hjMap hjendMap htokenMap hnMap hlenMap hactiveMap htargetMap
      hmarksMap hlistMap hj₁ hjend₁ htoken₁ hn₁ hlohi hhiCap
      ((harrFrame activeName).trans hactive)
      ((harrFrame "tgt").trans htarget)
      ((harrFrame marksName).trans hmarks)
      ((harrFrame listName).trans hlist) hlen₁
      htargetRange hactiveB (by omega) htargetCapB (by omega)
  have hrun : Run B (collectNeighborhoodAt ρ vertexVar lenName) σ σ₂
      (54 * (offset x (b + 1) - offset x b) + 22) := by
    have hseq : Run B (collectNeighborhoodAt ρ vertexVar lenName) σ σ₂
        (18 + (54 * (hi - lo) + 4)) := by
      simpa [collectNeighborhoodAt, seqs] using rprep.seq rcollect
    exact hseq.mono (by dsimp [lo, hi]; omega)
  exact ⟨σ₂, marks', list', hrun, hmarks₂, hlist₂,
    hlen₂, henum₂, hmem₂, hbound₂, hactive₂, htarget₂,
    hj₂, htoken₂, hrun.frame_inp (by
      simp [collectNeighborhoodAt, prepareNeighborAt, renameCom,
        collectNeighborBody, seqs, inc, Com.reads]),
    hrun.out_eq (by
      simp [collectNeighborhoodAt, prepareNeighborAt, renameCom,
        collectNeighborBody, seqs, inc, Com.NoWrite])⟩

/-- The duplicate-safe CSR set for a selected vertex is exactly its
active-side graph neighborhood. -/
lemma activeTargets_eq_numericNeighborhood_inter
    {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (A : Finset ℕ) (b : ℕ) (hb : b < n) :
    activeTargets (target x) (setFlag A) (offset x b) (offset x (b + 1)) =
      (numericNeighborhood G b) ∩ A := by
  ext v
  rw [mem_activeTargets_block hx hb]
  have hnum : v ∈ numericNeighborhood G b ↔ v < n ∧ Adjn G v b := by
    simp [numericNeighborhood]
  constructor
  · rintro ⟨hav, hadj⟩
    have hv : v < n := hadj.2.1
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · apply hnum.mpr
      obtain ⟨hb', hv', hAdj⟩ := hadj
      exact ⟨hv, hv', hb', (G.adj_comm _ _).mp hAdj⟩
    · simpa [setFlag] using hav
  · intro hv
    obtain ⟨hnear, hA⟩ := Finset.mem_inter.mp hv
    have hadj : Adjn G v b := (hnum.mp hnear).2
    refine ⟨by simpa [setFlag] using hA, ?_⟩
    obtain ⟨hv', hb', hAdj⟩ := hadj
    exact ⟨hb', hv', (G.adj_comm _ _).mp hAdj⟩

/-- Collect the selected vertex's distinct active-A neighbors into the
private B list and mark them with one. -/
lemma collectRepairB_run
    {B n targetCap lo hi : ℕ} {active target list : ℕ → ℕ} {σ : Env}
    (hj : σ.vars "j" = lo) (hjend : σ.vars "jend" = hi)
    (htoken : σ.vars "token" = 1) (hn : σ.vars "n" = n)
    (hlohi : lo ≤ hi) (hhi : hi ≤ targetCap)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hmarks : σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hlist : σ.arrs "repairBList" = arrOf n list)
    (hlen : σ.vars "repairBLen" = 0)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (honeB : 1 < B) :
    ∃ σ' marks' list',
      Run B collectRepairB σ σ' (54 * (hi - lo) + 4) ∧
      σ'.arrs "repairBMarks" = arrOf n marks' ∧
      σ'.arrs "repairBList" = arrOf n list' ∧
      σ'.vars "repairBLen" = (activeTargets target active lo hi).card ∧
      PrefixEnumerates (activeTargets target active lo hi).card list'
        (activeTargets target active lo hi) ∧
      (∀ v < n, marks' v = 1 ↔ v ∈ activeTargets target active lo hi) ∧
      (∀ v < n, marks' v ≤ 1) ∧
      σ'.arrs "activeA" = arrOf n active ∧
      σ'.arrs "tgt" = arrOf targetCap target ∧
      σ'.vars "j" = hi ∧ σ'.vars "token" = 1 ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  simpa [collectRepairB] using
    (collectNeighborhood_run (repairCollectNames "repairBMarks" "repairBList"
      "repairBLen") "activeA" "repairBMarks" "repairBList" "repairBLen"
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      hj hjend htoken hn hlohi hhi hactive htarget hmarks hlist hlen
      htargetRange hactiveB hnB htargetCapB honeB)

/-- The same duplicate-safe collector uses disjoint private state for the
stored representative's active-A neighbors. -/
lemma collectRepairR_run
    {B n targetCap lo hi : ℕ} {active target list : ℕ → ℕ} {σ : Env}
    (hj : σ.vars "j" = lo) (hjend : σ.vars "jend" = hi)
    (htoken : σ.vars "token" = 1) (hn : σ.vars "n" = n)
    (hlohi : lo ≤ hi) (hhi : hi ≤ targetCap)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hmarks : σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hlist : σ.arrs "repairRList" = arrOf n list)
    (hlen : σ.vars "repairRLen" = 0)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (honeB : 1 < B) :
    ∃ σ' marks' list',
      Run B collectRepairR σ σ' (54 * (hi - lo) + 4) ∧
      σ'.arrs "repairRMarks" = arrOf n marks' ∧
      σ'.arrs "repairRList" = arrOf n list' ∧
      σ'.vars "repairRLen" = (activeTargets target active lo hi).card ∧
      PrefixEnumerates (activeTargets target active lo hi).card list'
        (activeTargets target active lo hi) ∧
      (∀ v < n, marks' v = 1 ↔ v ∈ activeTargets target active lo hi) ∧
      (∀ v < n, marks' v ≤ 1) ∧
      σ'.arrs "activeA" = arrOf n active ∧
      σ'.arrs "tgt" = arrOf targetCap target ∧
      σ'.vars "j" = hi ∧ σ'.vars "token" = 1 ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  simpa [collectRepairR] using
    (collectNeighborhood_run (repairCollectNames "repairRMarks" "repairRList"
      "repairRLen") "activeA" "repairRMarks" "repairRList" "repairRLen"
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      hj hjend htoken hn hlohi hhi hactive htarget hmarks hlist hlen
      htargetRange hactiveB hnB htargetCapB honeB)

end

end Lax457868Proofs.RepairDomainSource
