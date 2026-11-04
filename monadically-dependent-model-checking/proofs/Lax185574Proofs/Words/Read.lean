import Lax185574Proofs.Legacy
import Lax808846Proofs.Spec
import Lax808846Proofs.Frame

/-!
Reading a list of words into arrays.

A list of words is encoded by its length followed by the frames of the
words, where the frame of a word is its length followed by its entries.
The command `readWords` reads such a list off the input tape, one number
at a time, and leaves it in three arrays: `a` holds the entries of all
words one after the other, and entry `i` of `st` and of `ln` is the
start of word `i` in `a` and its length. The scalar `m` holds the number
of words. The scalars `i`, `p`, `n`, `j` and `v` are used as counters
and scratch.

The arrays have to be long enough beforehand: `a` at least as long as
the total length of the words, `st` and `ln` at least as long as the
list. Their old contents beyond what is read are kept.

The relation `WordsAt ws σ` is what later phases use: it says where
every entry of every word of `ws` is, in terms of the arrays of `σ`.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

/-! ### Words and their frames -/

/-- The frames of a list of words: every word preceded by its length. -/
def frames (ws : List (List ℕ)) : List ℕ := (ws.map fun u => u.length :: u).flatten

theorem toWord_listNat (u : List ℕ) : toWord u = u.length :: u := by
  change u.length :: (u.map fun n => [n]).flatten = _
  congr 1
  induction u with
  | nil => rfl
  | cons a u ih => simp [ih]

theorem toWord_words (ws : List (List ℕ)) : toWord ws = ws.length :: frames ws := by
  change ws.length :: (ws.map toWord).flatten = _
  simp only [frames]
  congr 2
  exact List.map_congr_left fun u _ => toWord_listNat u

theorem frames_drop {ws : List (List ℕ)} {i : ℕ} (hi : i < ws.length) :
    frames (ws.drop i) = ws[i].length :: (ws[i] ++ frames (ws.drop (i + 1))) := by
  rw [List.drop_eq_getElem_cons hi]
  simp only [frames, List.map_cons, List.flatten_cons, List.cons_append]

/-- The start of word `i` in the concatenation of the words. -/
def off (ws : List (List ℕ)) (i : ℕ) : ℕ := ((ws.take i).flatten).length

theorem take_succ_flatten {ws : List (List ℕ)} {i : ℕ} (hi : i < ws.length) :
    (ws.take (i + 1)).flatten = (ws.take i).flatten ++ ws[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.flatten_append]
  simp

theorem off_succ {ws : List (List ℕ)} {i : ℕ} (hi : i < ws.length) :
    off ws (i + 1) = off ws i + ws[i].length := by
  simp [off, take_succ_flatten hi]

theorem off_length (ws : List (List ℕ)) : off ws ws.length = ws.flatten.length := by
  simp [off]

/-- The total length of the words. -/
def total (ws : List (List ℕ)) : ℕ := ws.flatten.length

theorem off_le_total (ws : List (List ℕ)) (k : ℕ) : off ws k ≤ total ws := by
  simp only [off, total]
  conv_rhs => rw [← List.take_append_drop k ws, List.flatten_append, List.length_append]
  omega

theorem off_add_le {ws : List (List ℕ)} {i : ℕ} (hi : i < ws.length) :
    off ws i + ws[i].length ≤ total ws := by
  rw [← off_succ hi]; exact off_le_total ws _

/-- Entry `j` of word `i` is entry `off ws i + j` of the concatenation. -/
theorem getElem?_flatten_off {ws : List (List ℕ)} {i j : ℕ} (hi : i < ws.length)
    (hj : j < ws[i].length) : ws.flatten[off ws i + j]? = some ws[i][j] := by
  have h : ws.flatten = (ws.take i).flatten ++ (ws[i] ++ (ws.drop (i + 1)).flatten) := by
    conv_lhs => rw [← List.take_append_drop i ws]
    rw [List.flatten_append, List.drop_eq_getElem_cons hi, List.flatten_cons]
  rw [h, off, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-- Storing at the end of a filled prefix extends the prefix. -/
theorem set_prefix {l o : List ℕ} (h : l.length < o.length) (v : ℕ) :
    (l ++ o.drop l.length).set l.length v = (l ++ [v]) ++ o.drop (l.length + 1) := by
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self]
  conv_lhs => rw [List.drop_eq_getElem_cons h]
  simp only [List.set_cons_zero, List.append_assoc, List.singleton_append]

theorem set_prefix' {l o : List ℕ} {n : ℕ} (hl : l.length = n) (h : n < o.length) (v : ℕ) :
    (l ++ o.drop n).set n v = (l ++ [v]) ++ o.drop (n + 1) := by
  subst hl; exact set_prefix h v

/-! ### Reading one word -/

/-- Read one entry into `a` at `p`, and advance `p` and `j`. -/
def readEntry : Com :=
  .seq (.read "v") (.seq (.store "a" (.var "p") (.var "v"))
    (.seq (.assign "p" (.add (.var "p") (.lit 1))) (.assign "j" (.add (.var "j") (.lit 1)))))

/-- Read `n` entries into `a` from position `p` on, counting with `j`. -/
def readEntries : Com := .while (.lt (.var "j") (.var "n")) readEntry

/-- The invariant of `readEntries`: `j` entries of the word `u` have been
read and stored after the filled prefix `pre` of the array, whose old
contents are `orig`. -/
def EntriesInv (pre orig u rest : List ℕ) (τ : Env) : Prop :=
  ∃ j ≤ u.length, τ.vars "j" = j ∧ τ.vars "n" = u.length ∧ τ.vars "p" = pre.length + j ∧
    τ.inp = u.drop j ++ rest ∧ τ.arrs "a" = (pre ++ u.take j) ++ orig.drop (pre.length + j)

theorem readEntries_run {B : ℕ} {pre orig u rest : List ℕ} {σ : Env}
    (hfit : pre.length + u.length ≤ orig.length) (hB : pre.length + u.length < B)
    (hu : ∀ v ∈ u, v < B) (hσ : EntriesInv pre orig u rest σ) (hj : σ.vars "j" = 0) :
    ∃ σ', Run B readEntries σ σ' (16 * u.length + 4) ∧
      σ'.vars "p" = pre.length + u.length ∧ σ'.vars "j" = u.length ∧ σ'.inp = rest ∧
      σ'.arrs "a" = (pre ++ u) ++ orig.drop (pre.length + u.length) := by
  have hstep : ∀ τ, EntriesInv pre orig u rest τ →
      (Cond.lt (.var "j") (.var "n")).evalB B τ = some true →
      ∃ τ', Run B readEntry τ τ' 12 ∧ EntriesInv pre orig u rest τ' ∧
        u.length - τ'.vars "j" < u.length - τ.vars "j" := by
    rintro τ ⟨j, hjle, hj, hn, hp, hinp, ha⟩ hc
    unfold readEntry
    have hjlt : j < u.length := by
      have := lt_of_condLt_true hc; rw [hj, hn] at this; exact this
    have hinp' : τ.inp = u[j] :: (u.drop (j + 1) ++ rest) := by
      rw [hinp, List.drop_eq_getElem_cons hjlt]; rfl
    have huj : u[j] < B := hu _ (List.getElem_mem _)
    have hlen : (pre ++ u.take j).length = pre.length + j := by simp; omega
    have hr : Run B readEntry τ
        (((({ τ.setVar "v" u[j] with inp := u.drop (j + 1) ++ rest }).setArr "a" (pre.length + j)
          u[j]).setVar "p" (pre.length + j + 1)).setVar "j" (j + 1)) 12 := by
      unfold readEntry
      refine (Run.seq (Run.read hinp') (Run.seq (Run.store ?_ ?_ ?_)
        (Run.seq (Run.assign ?_) (Run.assign ?_)))).mono (by simp)
      · simp [hp]; omega
      · simp; exact huj
      · simp [ha]; omega
      · simp [hp]; omega
      · simp [hj]; omega
    refine ⟨_, hr, ⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp [hn]
    · simp; omega
    · simp
    · simp only [arrs_setVar, arrs_setArr, if_true, ha]
      rw [← hlen, set_prefix (by simp; omega), hlen, List.take_add_one,
        List.getElem?_eq_getElem hjlt]
      simp [Nat.add_assoc]
    · simp [hj]; omega
  obtain ⟨σ', hrun, ⟨j, hjle, hj', hn, hp, hinp, ha⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "j") (.var "n")) (c := readEntry)
      (EntriesInv pre orig u rest) (fun τ => u.length - τ.vars "j") 12
      (fun τ ⟨j, hjle, hj, hn, _⟩ => evalB_condLt_vars (by rw [hj]; omega) (by rw [hn]; omega))
      hstep hσ
  have hju : j = u.length := by
    have := le_of_condLt_false hfalse; rw [hj', hn] at this; omega
  subst hju
  refine ⟨σ', hrun.mono (by simp [hj]), hp, hj', by simpa using hinp, ?_⟩
  rw [ha, List.take_length]

/-! ### Reading the list -/

/-- Read one word: its length into `n`, its start and length into `st`
and `ln` at `i`, its entries into `a`. -/
def readWord : Com :=
  .seq (.read "n") (.seq (.store "st" (.var "i") (.var "p"))
    (.seq (.store "ln" (.var "i") (.var "n"))
      (.seq (.assign "j" (.lit 0)) (.seq readEntries (.assign "i" (.add (.var "i") (.lit 1)))))))

/-- Read a list of words: its length into `m`, then the words. -/
def readWords : Com :=
  .seq (.read "m") (.seq (.assign "i" (.lit 0)) (.seq (.assign "p" (.lit 0))
    (.while (.lt (.var "i") (.var "m")) readWord)))

/-- The invariant of the loop of `readWords`: `i` words have been read. -/
def ReadInv (ws : List (List ℕ)) (oa ost oln rest : List ℕ) (τ : Env) : Prop :=
  ∃ i ≤ ws.length, τ.vars "i" = i ∧ τ.vars "m" = ws.length ∧ τ.vars "p" = off ws i ∧
    τ.inp = frames (ws.drop i) ++ rest ∧
    τ.arrs "a" = (ws.take i).flatten ++ oa.drop (off ws i) ∧
    τ.arrs "st" = (List.range i).map (off ws) ++ ost.drop i ∧
    τ.arrs "ln" = (ws.take i).map List.length ++ oln.drop i

theorem mem_toWord_words {ws : List (List ℕ)} {i : ℕ} (hi : i < ws.length) :
    ws[i].length ∈ toWord ws ∧ ∀ v ∈ ws[i], v ∈ toWord ws := by
  rw [toWord_words]
  have hmem : ws[i] ∈ ws := List.getElem_mem hi
  refine ⟨List.mem_cons_of_mem _ ?_, fun v hv => List.mem_cons_of_mem _ ?_⟩
  · simp only [frames, List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨ws[i], hmem, rfl⟩, List.mem_cons_self ..⟩
  · simp only [frames, List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨ws[i], hmem, rfl⟩, List.mem_cons_of_mem _ hv⟩

theorem length_toWord_words (ws : List (List ℕ)) :
    (toWord ws).length = 1 + ws.length + total ws := by
  rw [toWord_words]
  simp only [frames, total, List.length_cons, List.length_flatten, List.map_map]
  have : ∀ l : List (List ℕ), (l.map (List.length ∘ fun u => u.length :: u)).sum =
      l.length + (l.map List.length).sum := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.sum_cons, Function.comp, List.length_cons] at ih ⊢; omega
  rw [this]; omega

theorem readWord_step {B : ℕ} {ws : List (List ℕ)} {oa ost oln rest : List ℕ}
    (hoa : total ws ≤ oa.length) (host : ws.length ≤ ost.length) (holn : ws.length ≤ oln.length)
    (hB : (toWord ws).length < B) (hv : ∀ v ∈ toWord ws, v < B)
    {τ : Env} (hI : ReadInv ws oa ost oln rest τ)
    (hc : (Cond.lt (.var "i") (.var "m")).evalB B τ = some true) :
    ∃ τ' K, Run B readWord τ τ' K ∧ ReadInv ws oa ost oln rest τ' ∧
      1 + (Cond.lt (.var "i") (.var "m")).size + K +
        (21 * (ws.length - τ'.vars "i") + 16 * (total ws - τ'.vars "p")) ≤
        21 * (ws.length - τ.vars "i") + 16 * (total ws - τ.vars "p") := by
  obtain ⟨i, hile, hi, hm, hp, hinp, ha, hst, hln⟩ := hI
  have hilt : i < ws.length := by
    have := lt_of_condLt_true hc; rw [hi, hm] at this; exact this
  have hlenB := length_toWord_words ws
  have hofu := off_add_le hilt
  have hoff : off ws i = ((ws.take i).flatten).length := rfl
  have hinp' : τ.inp = ws[i].length :: (ws[i] ++ (frames (ws.drop (i + 1)) ++ rest)) := by
    rw [hinp, frames_drop hilt]; simp
  obtain ⟨huB, hu'⟩ := mem_toWord_words hilt
  have hts := take_succ_flatten hilt
  have hos := off_succ hilt
  have htl : (ws.take (i + 1)).map List.length = (ws.take i).map List.length ++ [ws[i].length] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hilt, List.map_append]; rfl
  generalize hu : ws[i] = u at *
  have hlst : ((List.range i).map (off ws)).length = i := by simp
  have hlln : ((ws.take i).map List.length).length = i := by simp; omega
  set τ4 : Env := (({ τ.setVar "n" u.length with inp := u ++ (frames (ws.drop (i + 1)) ++ rest) }.setArr
      "st" i (off ws i)).setArr "ln" i u.length).setVar "j" 0 with hτ4
  have hE : EntriesInv (ws.take i).flatten oa u (frames (ws.drop (i + 1)) ++ rest) τ4 := by
    refine ⟨0, by omega, by simp [hτ4], by simp [hτ4], ?_, by simp [hτ4], ?_⟩
    · simp [hτ4, hp, off]
    · simp [hτ4, ha, off]
  obtain ⟨τ5, hr5, hp5, hj5, hinp5, ha5⟩ := readEntries_run (B := B)
    (by rw [← hoff]; omega) (by rw [← hoff]; omega)
    (fun v hv' => hv v (hu' v hv')) hE (by simp [hτ4])
  have hr : Run B readWord τ (τ5.setVar "i" (i + 1)) (17 + 16 * u.length) := by
    unfold readWord
    refine (Run.seq (Run.read hinp') (Run.seq (Run.store ?_ ?_ ?_)
      (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.assign ?_) (Run.seq hr5 (Run.assign ?_)))))).mono
      (by simp; omega)
    · simp [hi]; omega
    · simp [hp]; omega
    · simp [hst]; omega
    · simp [hi]; omega
    · simp; exact hv _ huB
    · simp [hln]; omega
    · simp; omega
    · have hi5 : τ5.vars "i" = i := by
        rw [hr5.frame_var "i" (by decide)]; simp [hτ4, hi]
      simp [hi5]; omega
  have hfr : ∀ y, y ∉ readEntries.wvars → τ5.vars y = τ4.vars y := fun y hy => hr5.frame_var y hy
  have hfa : ∀ b, b ∉ readEntries.warrs → τ5.arrs b = τ4.arrs b := fun b hb => hr5.frame_arr b hb
  refine ⟨_, _, hr, ⟨i + 1, by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hfr "m" (by decide), hτ4, hm]
  · simp [hp5, hos, hoff]
  · simp [hinp5]
  · simp only [arrs_setVar, ha5, hts, hos, hoff, List.append_assoc]
  · simp only [arrs_setVar, hfa "st" (by decide), hτ4, arrs_setArr, if_true]
    simp only [show ("st" : String) = "ln" ↔ False by decide, if_false, hst]
    rw [set_prefix' hlst (by omega), List.range_succ, List.map_append]
    simp
  · simp only [arrs_setVar, hfa "ln" (by decide), hτ4, arrs_setArr, if_true]
    simp only [show ("ln" : String) = "st" ↔ False by decide, if_false, hln]
    rw [set_prefix' hlln (by omega), htl]
  · simp only [vars_setVar, if_true, hp5]
    simp only [show ("p" : String) = "i" ↔ False by decide, if_false]
    rw [hi, hp, ← hoff]
    simp
    omega

/-- **Reading a list of words.** Started on an input tape that begins
with the word of `ws`, with arrays `a`, `st` and `ln` long enough,
`readWords` reads the word of `ws` and leaves the entries of the words
in `a`, their starts in `st` and their lengths in `ln`, in time linear in
the length of the word. -/
theorem readWords_run {B : ℕ} {ws : List (List ℕ)} {rest : List ℕ} {σ : Env}
    (hinp : σ.inp = toWord ws ++ rest)
    (hoa : total ws ≤ (σ.arrs "a").length) (host : ws.length ≤ (σ.arrs "st").length)
    (holn : ws.length ≤ (σ.arrs "ln").length)
    (hB : (toWord ws).length < B) (hv : ∀ v ∈ toWord ws, v < B) :
    ∃ σ', Run B readWords σ σ' (21 * (toWord ws).length + 9) ∧
      σ'.vars "m" = ws.length ∧ σ'.inp = rest ∧
      σ'.arrs "a" = ws.flatten ++ (σ.arrs "a").drop (total ws) ∧
      σ'.arrs "st" = (List.range ws.length).map (off ws) ++ (σ.arrs "st").drop ws.length ∧
      σ'.arrs "ln" = ws.map List.length ++ (σ.arrs "ln").drop ws.length := by
  have hlenB := length_toWord_words ws
  have hinp' : σ.inp = ws.length :: (frames ws ++ rest) := by rw [hinp, toWord_words]; rfl
  set σ0 : Env := ({ σ.setVar "m" ws.length with inp := frames ws ++ rest }.setVar "i" 0).setVar
    "p" 0 with hσ0
  have hI0 : ReadInv ws (σ.arrs "a") (σ.arrs "st") (σ.arrs "ln") rest σ0 := by
    refine ⟨0, by omega, by simp [hσ0], by simp [hσ0], by simp [hσ0, off], by simp [hσ0], ?_, ?_, ?_⟩
    · simp [hσ0, off]
    · simp [hσ0]
    · simp [hσ0]
  obtain ⟨σ', K, hrun, ⟨i, hile, hi, hm, hp, hinp2, ha, hst, hln⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "i") (.var "m")) (c := readWord)
      (ReadInv ws (σ.arrs "a") (σ.arrs "st") (σ.arrs "ln") rest)
      (fun τ => 21 * (ws.length - τ.vars "i") + 16 * (total ws - τ.vars "p"))
      (fun τ ⟨i, hile, hi, hm, _⟩ => evalB_condLt_vars (by rw [hi]; omega) (by rw [hm]; omega))
      (fun τ hI hc => readWord_step hoa host holn hB hv hI hc) hI0
  have hiw : i = ws.length := by
    have := le_of_condLt_false hfalse; rw [hi, hm] at this; omega
  subst hiw
  refine ⟨σ', (Run.seq (Run.read hinp') (Run.seq (Run.assign (v := 0) (by simp; omega))
    (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun))).mono ?_, hm, by simpa [frames] using hinp2, ?_,
    hst, ?_⟩
  · have : σ0.vars "i" = 0 := by simp [hσ0]
    have : σ0.vars "p" = 0 := by simp [hσ0]
    simp only [Cond.size, Expr.size] at hK
    simp only [Expr.size]
    rw [hlenB]
    omega
  · rw [ha, List.take_length, off_length]; rfl
  · rw [hln, List.take_length]

/-! ### Where the words are -/

/-- The words `ws` are in the arrays of `σ`: entry `i` of `st` is the
start of word `i` in `a`, entry `i` of `ln` is its length, and its
entries follow in `a`. -/
structure WordsAt (ws : List (List ℕ)) (σ : Env) : Prop where
  /-- The starts. -/
  st : ∀ i (_ : i < ws.length), (σ.arrs "st")[i]? = some (off ws i)
  /-- The lengths. -/
  ln : ∀ i (_ : i < ws.length), (σ.arrs "ln")[i]? = some ws[i].length
  /-- The entries. -/
  a : ∀ i (h : i < ws.length) j (hj : j < ws[i].length),
    (σ.arrs "a")[off ws i + j]? = some ws[i][j]

/-- `WordsAt` only depends on the three arrays. -/
theorem WordsAt.of_arrs {ws : List (List ℕ)} {σ σ' : Env} (h : WordsAt ws σ)
    (ha : σ'.arrs "a" = σ.arrs "a") (hst : σ'.arrs "st" = σ.arrs "st")
    (hln : σ'.arrs "ln" = σ.arrs "ln") : WordsAt ws σ' :=
  ⟨by rw [hst]; exact h.st, by rw [hln]; exact h.ln, by rw [ha]; exact h.a⟩

theorem wordsAt_of_arrs {ws : List (List ℕ)} {σ : Env} {oa ost oln : List ℕ}
    (ha : σ.arrs "a" = ws.flatten ++ oa)
    (hst : σ.arrs "st" = (List.range ws.length).map (off ws) ++ ost)
    (hln : σ.arrs "ln" = ws.map List.length ++ oln) : WordsAt ws σ where
  st i h := by rw [hst, List.getElem?_append_left (by simpa using h)]; simp [h]
  ln i h := by rw [hln, List.getElem?_append_left (by simpa using h)]; simp [h]
  a i h j hj := by
    have := getElem?_flatten_off h hj
    rw [ha, List.getElem?_append_left]
    · exact this
    · exact (List.getElem?_eq_some_iff.mp this).1

/-- The postcondition of `readWords` in the form later phases use. -/
theorem readWords_wordsAt {B : ℕ} {ws : List (List ℕ)} {rest : List ℕ} {σ : Env}
    (hinp : σ.inp = toWord ws ++ rest)
    (hoa : total ws ≤ (σ.arrs "a").length) (host : ws.length ≤ (σ.arrs "st").length)
    (holn : ws.length ≤ (σ.arrs "ln").length)
    (hB : (toWord ws).length < B) (hv : ∀ v ∈ toWord ws, v < B) :
    ∃ σ', Run B readWords σ σ' (21 * (toWord ws).length + 9) ∧
      σ'.vars "m" = ws.length ∧ σ'.inp = rest ∧ WordsAt ws σ' := by
  obtain ⟨σ', hr, hm, hinp', ha, hst, hln⟩ := readWords_run hinp hoa host holn hB hv
  exact ⟨σ', hr, hm, hinp', wordsAt_of_arrs ha hst hln⟩

end Lax185574Proofs.Words
