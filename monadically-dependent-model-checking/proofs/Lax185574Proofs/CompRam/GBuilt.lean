import Lax185574Proofs.CompRam.GKeep

/-!
How the buffer of the glue command of lem:compose gives the output of a
round, for each kind of outcome: a call with a query of the canonical
form (`built_ca`), of a rank shift (`built_sh`), of a restriction
(`built_re`), and the final word (`built_done`). `Keep σ σ'`: the scalars `W`, `jr`, `ovf`, the arrays `x`, `wp`,
the length of `OB` and the tapes are unchanged. The head of a call is
written with a `0` in place of the length of the state, which is filled
in after the frames (`patchL`), and the length of the query of the
canonical form is filled in after the query.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding

theorem Run.seqs_cons {B : ℕ} {c : Com} {cs : List Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ} (hcs : cs ≠ [])
    (h1 : Run B c σ σ1 K1) (h2 : Run B (seqs cs) σ1 σ2 K2) : Run B (seqs (c :: cs)) σ σ2 (K1 + K2) := by
  match cs, hcs with
  | d :: ds, _ => exact Run.seq h1 h2

theorem Run.seqs_one {B : ℕ} {c : Com} {σ σ1 : Env} {K : ℕ} (h : Run B c σ σ1 K) :
    Run B (seqs [c]) σ σ1 K := h

/-- The head of the output of a call, with the length of the state still open. -/
def hd0 (j : ℕ) (S : List Fr) : List ℕ := [1, 0, 0, 0, j, (stWords S).length] ++ frames (stWords S)

/-- The head of the output of a call. -/
def hdS (j : ℕ) (S : List Fr) : List ℕ := (hd0 j S).set 1 ((hd0 j S).length - 3)

theorem length_hdS (j : ℕ) (S : List Fr) : (hdS j S).length = (hd0 j S).length := by
  simp [hdS]

theorem outW_call' (j : ℕ) (S : List Fr) (q : Qry) : outW j (.call S q) = hdS j S ++ qWord q :=
  outW_call j S q

theorem set_append_right' (A B : List ℕ) (k v : ℕ) :
    (A ++ B).set (A.length + k) v = A ++ B.set k v := by
  rw [List.set_append, if_neg (by omega)]
  simp

theorem seg_mid (A B C : List ℕ) : seg (A ++ B ++ C) A.length B.length = B := by
  simp [seg]

theorem take_append_len {A B : List ℕ} : (A ++ B).take A.length = A := by simp

theorem drop_append_len {A B : List ℕ} : (A ++ B).drop A.length = B := by simp

/-- **A call with a query of the canonical form.** -/
theorem built_ca {j : ℕ} {S : List Fr} {ws : List (List ℕ)} {σ : Env}
    (hF : Filled "OB" "po" ((hdS j S ++ [5, lDSq, 0, 0, 0, 0, 0, 0] ++ toWord ws).set
      ((hdS j S).length + 2) (toWord ws).length) σ)
    (hsp : σ.vars "sp" = (hdS j S).length + 8) (hdq : σ.vars "dq" = 1) (hqk : σ.vars "qk" = 2)
    (hqa : σ.vars "qa" = (hdS j S).length + 8) (hql : σ.vars "ql" = (toWord ws).length) :
    Built j (.call S (.ca ws)) (hdS j S ++ [5, lDSq, (toWord ws).length, 0, 0, 0, 0, 0] ++ toWord ws) σ := by
  have e : (hdS j S ++ [5, lDSq, 0, 0, 0, 0, 0, 0] ++ toWord ws).set ((hdS j S).length + 2)
      (toWord ws).length = hdS j S ++ [5, lDSq, (toWord ws).length, 0, 0, 0, 0, 0] ++ toWord ws := by
    rw [List.append_assoc, List.append_assoc, set_append_right']; simp
  rw [e] at hF
  refine ⟨hF, by rw [hsp]; simp, Or.inr hdq, ?_, ?_⟩
  · rw [hsp, hdq, if_pos rfl, outW_call', qWord_ca]
    have h8 : (hdS j S).length + 8 = (hdS j S ++ [5, lDSq, (toWord ws).length, 0, 0, 0, 0, 0]).length := by simp
    rw [h8, take_append_len, drop_append_len]
    simp
  · refine ⟨hqk, by rw [hqa, hql]; simp; omega, ?_⟩
    rw [hqa, hql]
    have h8 : (hdS j S).length + 8 = (hdS j S ++ [5, lDSq, (toWord ws).length, 0, 0, 0, 0, 0]).length := by simp
    rw [h8]
    have := seg_mid (hdS j S ++ [5, lDSq, (toWord ws).length, 0, 0, 0, 0, 0]) (toWord ws) []
    rw [List.append_nil] at this
    exact this

/-- **A call with a query of a rank shift.** -/
theorem built_sh {j : ℕ} {S : List Fr} {w : List ℕ} {σ : Env}
    (hF : Filled "OB" "po" (hdS j S ++ [5, w.length, 1, 0, 0, 0, 0, 0] ++ w ++ [0]) σ)
    (hsp : σ.vars "sp" = (hdS j S).length + 8 + w.length + 1) (hdq : σ.vars "dq" = 0)
    (hqk : σ.vars "qk" = 1) (hqa : σ.vars "qa" = (hdS j S).length + 8) (hql : σ.vars "ql" = w.length) :
    Built j (.call S (.sh w)) (hdS j S ++ [5, w.length, 1, 0, 0, 0, 0, 0] ++ w ++ [0]) σ := by
  have hlen : (hdS j S ++ [5, w.length, 1, 0, 0, 0, 0, 0] ++ w ++ [0]).length = (hdS j S).length + 8 + w.length + 1 := by
    simp; omega
  refine ⟨hF, by rw [hsp, hlen], Or.inl hdq, ?_, ?_⟩
  · rw [hsp, hdq, if_neg (by omega), ← hlen, List.take_length, List.drop_length, outW_call', qWord_sh]
    simp
  · refine ⟨hqk, by rw [hqa, hql]; simp; omega, ?_⟩
    rw [hqa, hql]
    have h8 : (hdS j S).length + 8 = (hdS j S ++ [5, w.length, 1, 0, 0, 0, 0, 0]).length := by simp
    rw [h8]
    exact seg_mid _ w [0]

/-- **A call with a query of a restriction.** -/
theorem built_re {j : ℕ} {S : List Fr} {w : List ℕ} {σ : Env}
    (hF : Filled "OB" "po" (hdS j S ++ [w.length, lDSq, 1] ++ w ++ [0]) σ)
    (hsp : σ.vars "sp" = (hdS j S).length + 3 + w.length) (hdq : σ.vars "dq" = 1)
    (hqk : σ.vars "qk" = 0) (hqa : σ.vars "qa" = (hdS j S).length + 3) (hql : σ.vars "ql" = w.length) :
    Built j (.call S (.re w)) (hdS j S ++ [w.length, lDSq, 1] ++ w ++ [0]) σ := by
  have hsp' : (hdS j S).length + 3 + w.length = (hdS j S ++ [w.length, lDSq, 1] ++ w).length := by simp; omega
  refine ⟨hF, by rw [hsp]; simp; omega, Or.inr hdq, ?_, ?_⟩
  · rw [hsp, hdq, if_pos rfl, hsp', take_append_len, drop_append_len, outW_call', qWord_re]
    simp
  · refine ⟨hqk, by rw [hqa, hql]; simp; omega, ?_⟩
    rw [hqa, hql]
    have h3 : (hdS j S).length + 3 = (hdS j S ++ [w.length, lDSq, 1]).length := by simp
    rw [h3]
    exact seg_mid _ w [0]

/-- **The final word.** -/
theorem built_done {j : ℕ} {z : List ℕ} {σ : Env} (hF : Filled "OB" "po" (0 :: z) σ)
    (hsp : σ.vars "sp" = z.length + 1) (hdq : σ.vars "dq" = 0) (hqk : σ.vars "qk" = 3) :
    Built j (.done z) (0 :: z) σ := by
  refine ⟨hF, by rw [hsp]; simp, Or.inl hdq, ?_, hqk⟩
  rw [hsp, hdq, if_neg (by omega), show z.length + 1 = (0 :: z).length from rfl, List.take_length,
    List.drop_length]
  simp [outW]

/-! ### Changing the frame description -/

theorem SlotIs.set_ph {M : ℕ} {σ : Env} {f : Fr} (h : SlotIs M σ f) {v : ℕ} (hv : v < 2 * M) :
    SlotIs M (σ.setVar "gp" v) { f with ph := v } :=
  ⟨by simp [h.d], by simp [h.kk], by simp [h.l1], by simp [h.l2], by simp, by simp [h.i],
    ⟨h.nums.1, h.nums.2.1, h.nums.2.2.1, h.nums.2.2.2.1, hv, h.nums.2.2.2.2.2⟩,
    h.A.setVar (by decide) (by decide) v, h.B.setVar (by decide) (by decide) v,
    h.SA.setVar (by decide) (by decide) v, h.SB.setVar (by decide) (by decide) v,
    h.AT.setVar (by decide) (by decide) v,
    h.EX.ofr (OFr.setVar σ "gp" v) (fun z hz hz' => by
      simp at hz'; subst hz'; exact absurd hz (by decide))⟩

/-- What the round commands leave alone. -/
structure Keep (σ σ' : Env) : Prop where
  W : σ'.vars "W" = σ.vars "W"
  jr : σ'.vars "jr" = σ.vars "jr"
  ovf : σ'.vars "ovf" = σ.vars "ovf"
  x : σ'.arrs "x" = σ.arrs "x"
  wp : σ'.arrs "wp" = σ.arrs "wp"
  ob : (σ'.arrs "OB").length = (σ.arrs "OB").length
  out : σ'.out = σ.out
  inp : σ'.inp = σ.inp

end Lax185574Proofs.CompRam
