import Lax3Proofs.SolveChainWin
import Lax3Proofs.SolveBlocksBotCom

/-!
# F6c6 (part 2) — the leaf stage, lifted to the windowed contract

The worked instance of `specWindow`: the landed leaf discharge
`botCom_spec` (exact-length `ArenaSt` in, exact-length `TableBits`
out), restated at the chain's windowed contract — `ArenaStW` in,
`ArenaStW ∧ TableBitsW` out, same command, same budget
`botComK`. This is the form the level chain's bottom block consumes
(the head file), and it is the template for lifting the other five
stages: the landed spec is applied to the *truncation* through
`specWindow`, and what a call site pays is exactly the gluing visible
below — evaluating the window assignment at the dozen names in play
(one `if`-chain each), transporting `ArenaSt` along the truncation
congruence, and reading the slot-count cell's stability off the
stage's own `wvars` frame data. No landed proof is re-entered.

The window assignment: the five arena regions at the arena's
dimensions (`arenaWs`), the table region at `A.N · |Fl|` on top; the
four leaf scratch regions (`na`/`fa`/`ea`/`xa`) carry **no window** —
their lengths are schedule constants (`2^Λ`, `2^Λ·(K+1)`, `K+1`), the
static layout allocates them exactly, and the precondition states them
directly, as the landed spec does.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning Lax67Proofs.Reasoning.Lib
open Lax3.ColoredGraphs
open Lax3.DistFO

open Classical in
/-- **The leaf stage at the windowed contract** (the `specWindow`
worked instance): from `ArenaStW` at an edgeless arena, the four
exact-length scratch regions and a table allocation of at least
`A.N·|Fl|` cells, `botCom` leaves the windowed contract intact and the
windowed table region holding exactly the `Sat A.G` values of the
schedule family, at the landed budget `botComK`. Hypotheses are the
landed spec's, plus the five region names' distinctness (the window
assignment's `if`-chain) — all supplied by the head file's `lv`
mechanism at every level. -/
theorem botCom_specW {B Lc K n₀ ℓp : ℕ} {na fa ea xa : String} (hb : ℕ)
    (nm : ArenaNames) (A : Impl.MArena Lc n₀ ℓp) (hbot : A.G = ⊥)
    (Fl : List (DistFO Lc 1))
    (hq : ∀ β ∈ Fl, qdepth β ≤ K)
    (hNB : A.N < B) (hNLB : A.N * Lc < B) (h2LB : 2 ^ Lc * (K + 1) < B)
    (hTB : A.N * Fl.length < B)
    (hnd : [nm.col, na, fa, ea, xa, nm.tab].Nodup)
    (hoff : nm.off ∉ [na, fa, ea, xa, nm.tab])
    (htgt : nm.tgt ∉ [na, fa, ea, xa, nm.tab])
    (hup : nm.up ∉ [na, fa, ea, xa, nm.tab])
    (hhist : nm.hist ∉ [na, fa, ea, xa, nm.tab])
    (hnN : nm.nN ∉ btScalars) (hnS : nm.nS ∉ btScalars)
    (hnd5 : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup) :
    Spec B
      (fun σ => ArenaStW nm hb A σ ∧
        (σ.arrs na).length = 2 ^ Lc ∧ (σ.arrs fa).length = 2 ^ Lc * (K + 1) ∧
        (σ.arrs ea).length = K + 1 ∧ (σ.arrs xa).length = K + 1 ∧
        A.N * Fl.length ≤ (σ.arrs nm.tab).length)
      (botCom nm.nN nm.col na fa ea xa nm.tab Lc K Fl)
      (fun _ σ' => ArenaStW nm hb A σ' ∧
        TableBitsW nm.tab Fl (fun v β => Sat A.G A.col (fun _ => v) β) σ')
      (botComK A.N Lc K Fl) := by
  -- the name disequalities, spelled out (working copies; the originals
  -- are consumed whole by the landed spec)
  have hndC := hnd
  have hnd5C := hnd5
  have hoffC := hoff
  have htgtC := htgt
  have hupC := hup
  have hhistC := hhist
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hndC hnd5C
  obtain ⟨⟨hca_na, hca_fa, hca_ea, hca_xa, hca_ta⟩,
    ⟨hna_fa, hna_ea, hna_xa, hna_ta⟩, ⟨hfa_ea, hfa_xa, hfa_ta⟩,
    ⟨hea_xa, hea_ta⟩, ⟨hxa_ta, -⟩⟩ := hndC
  obtain ⟨⟨hot, hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5C
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hoffC htgtC hupC hhistC
  obtain ⟨hoff_na, hoff_fa, hoff_ea, hoff_xa, hoff_ta⟩ := hoffC
  obtain ⟨htgt_na, htgt_fa, htgt_ea, htgt_xa, htgt_ta⟩ := htgtC
  obtain ⟨hup_na, hup_fa, hup_ea, hup_xa, hup_ta⟩ := hupC
  obtain ⟨hhist_na, hhist_fa, hhist_ea, hhist_xa, hhist_ta⟩ := hhistC
  intro σ hσ
  obtain ⟨⟨hfit, hst⟩, hnaL, hfaL, heaL, hxaL, htabL⟩ := hσ
  -- the window assignment: the arena's five regions plus the table
  set ns := σ.vars nm.nS with hns_def
  set ws0 : String → Option ℕ := arenaWs nm Lc ℓp hb A.N ns with hws0_def
  set ws : String → Option ℕ :=
    fun b => if b = nm.tab then some (A.N * Fl.length) else ws0 b with hws_def
  have hws_tab : ws nm.tab = some (A.N * Fl.length) := if_pos rfl
  have hws_ne : ∀ b, b ≠ nm.tab → ws b = ws0 b := fun b hb' => if_neg hb'
  have hws_off : ws nm.off = some (A.N + 1) := by
    rw [hws_ne _ hoff_ta, hws0_def, arenaWs_off]
  have hws_tgt : ws nm.tgt = some ns := by
    rw [hws_ne _ htgt_ta, hws0_def, arenaWs_tgt (Ne.symm hot)]
  have hws_col : ws nm.col = some (A.N * Lc) := by
    rw [hws_ne _ hca_ta, hws0_def, arenaWs_col (Ne.symm hoc) (Ne.symm htc)]
  have hws_up : ws nm.up = some A.N := by
    rw [hws_ne _ hup_ta, hws0_def,
      arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu)]
  have hws_hist : ws nm.hist = some (A.N * ℓp * (hb + 1)) := by
    rw [hws_ne _ hhist_ta, hws0_def,
      arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)]
  have hws_scr : ∀ b, b ≠ nm.tab → b ≠ nm.off → b ≠ nm.tgt → b ≠ nm.col →
      b ≠ nm.up → b ≠ nm.hist → ws b = none := by
    intro b h0 h1 h2 h3 h4 h5
    rw [hws_ne _ h0, hws0_def, arenaWs_none h1 h2 h3 h4 h5]
  have hws_na : ws na = none :=
    hws_scr na hna_ta (Ne.symm hoff_na) (Ne.symm htgt_na)
      (Ne.symm hca_na) (Ne.symm hup_na) (Ne.symm hhist_na)
  have hws_fa : ws fa = none :=
    hws_scr fa hfa_ta (Ne.symm hoff_fa) (Ne.symm htgt_fa)
      (Ne.symm hca_fa) (Ne.symm hup_fa) (Ne.symm hhist_fa)
  have hws_ea : ws ea = none :=
    hws_scr ea hea_ta (Ne.symm hoff_ea) (Ne.symm htgt_ea)
      (Ne.symm hca_ea) (Ne.symm hup_ea) (Ne.symm hhist_ea)
  have hws_xa : ws xa = none :=
    hws_scr xa hxa_ta (Ne.symm hoff_xa) (Ne.symm htgt_xa)
      (Ne.symm hca_xa) (Ne.symm hup_xa) (Ne.symm hhist_xa)
  -- the allocation fits the extended window assignment
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases hbt : b = nm.tab
    · subst hbt
      rw [hws_tab] at hbm
      cases hbm
      exact htabL
    · rw [hws_ne _ hbt] at hbm
      exact hfit b m hbm
  -- the truncation satisfies the landed precondition
  have hstW : ArenaSt nm hb A (winA ws σ) := by
    refine arenaSt_of_eq hst rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
      exact arrs_winA_congr (hws_ne _ (by assumption)) σ
  have hP : ArenaSt nm hb A (winA ws σ) ∧
      ((winA ws σ).arrs na).length = 2 ^ Lc ∧
      ((winA ws σ).arrs fa).length = 2 ^ Lc * (K + 1) ∧
      ((winA ws σ).arrs ea).length = K + 1 ∧
      ((winA ws σ).arrs xa).length = K + 1 ∧
      ((winA ws σ).arrs nm.tab).length = A.N * Fl.length := by
    refine ⟨hstW, ?_, ?_, ?_, ?_, ?_⟩
    · rw [arrs_winA_none hws_na]; exact hnaL
    · rw [arrs_winA_none hws_fa]; exact hfaL
    · rw [arrs_winA_none hws_ea]; exact heaL
    · rw [arrs_winA_none hws_xa]; exact hxaL
    · exact length_arrs_winA hws_tab htabL
  -- run the landed spec on the truncation, pad the derivation back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, -⟩ :=
    (specWindow (botCom_spec (B := B) hb nm A hbot Fl hq hNB hNLB h2LB hTB
      hnd hoff htgt hup hhist hnN hnS) ws) σ ⟨hFits, hP⟩
  obtain ⟨hst', htab'⟩ := hQ
  -- the slot-count cell survives: the leaf writes only its scratch cells
  have hnsv : σ'.vars nm.nS = ns := by
    rw [hns_def]
    exact hrun.frame_var nm.nS fun hm =>
      hnS (wvars_botCom nm.col na fa ea xa nm.tab nm.nN Lc K Fl hm)
  refine ⟨σ', hrun, ⟨?_, ?_⟩, ?_⟩
  · -- the windowed contract still fits, at the preserved slot count
    rw [hnsv]
    intro b m hbm
    have hb5 := arenaWs_some_elim hbm
    have hbt : b ≠ nm.tab := by
      rcases hb5 with rfl | rfl | rfl | rfl | rfl
      · exact hoff_ta
      · exact htgt_ta
      · exact hca_ta
      · exact hup_ta
      · exact hhist_ta
    exact hfit' b m (by rw [hws_ne _ hbt]; exact hbm)
  · -- the truncation still satisfies the exact contract
    rw [hnsv]
    refine arenaSt_of_eq hst' rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
      exact (arrs_winA_congr (hws_ne _ (by assumption)) σ').symm
  · -- the windowed table region, read back through its window
    exact tableBitsW_of_win hws_tab hfit' htab'

end Lax3Proofs.Prog
