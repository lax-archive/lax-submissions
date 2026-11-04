import Lax185574Proofs.RamSimBlock

/-!
The blocks for the single instructions of a simulated program.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec

variable {w : ℕ} {p : Program}
variable {g : Geo} {ks : List SegKind} {tb : ℕ} {mode : OutMode} {x' out₀ : List ℕ}

/-- After `n` steps the machine is at `pc` and represents `s'`. -/
def Reaches (w : ℕ) (p : Program) (g : Geo) (ks : List SegKind) (tb : ℕ) (mode : OutMode)
    (x' out₀ : List ℕ) (n : ℕ) (S : State) (pc : ℕ) (s' : State) : Prop :=
  ∃ S', Exec w p n S S' ∧ S'.pc = pc ∧ Rel w g ks tb mode x' out₀ s' S' ∧ Frame g S S'

theorem Reaches.mono {n m : ℕ} {S : State} {pc : ℕ} {s' : State}
    (h : Reaches w p g ks tb mode x' out₀ n S pc s') (hnm : n = m) :
    Reaches w p g ks tb mode x' out₀ m S pc s' := hnm ▸ h

theorem mod_mod_of_le {x v w : ℕ} (h : v ≤ w) : x % 2 ^ w % 2 ^ v = x % 2 ^ v :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

/-- Write the value `x` into simulated cell `j`. -/
theorem Rel.write_region {s S S' : State} {j x : ℕ} (R : Rel w g ks tb mode x' out₀ s S)
    (hj : j < 2 ^ g.v) (hx : x < 2 ^ g.v)
    (hm : ∀ b, (b < rT ∨ rU < b) → S'.mem b = if b = g.base + j then x else S.mem b)
    (hw : WordMem w S'.mem) (hi : S'.input = S.input) (hn : S'.inp = S.inp)
    (ho : S'.out = S.out) :
    Rel w g ks tb mode x' out₀ { s with mem := Function.update s.mem j x } S' ∧
      Frame g S S' := by
  have E := R.env
  have low := E.low
  have room := E.room
  have hX : g.W (g.base + j) := Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  have hfr : ∀ b, ¬ g.W b → S'.mem b = S.mem b := by
    intro b hb
    have h1 : b ≠ g.base + j := fun h => hb (h ▸ hX)
    have h2 : b < rT ∨ rU < b := by simp only [Geo.W] at hb; omega
    rw [hm b h2, if_neg h1]
  have hlow : ∀ b, b < rT → S'.mem b = S.mem b := by
    intro b hb; rw [hm b (Or.inl hb), if_neg (by omega)]
  refine ⟨
    { env := ⟨hw, by rw [hlow _ (by omega)]; exact E.zero, by rw [hlow _ (by omega)]; exact E.one,
        by rw [hlow _ (by omega)]; exact E.mask, by rw [hlow _ (by omega)]; exact E.baseCell,
        E.room, E.low, E.hv⟩
      cword := fun b => by
        simp only [Function.update_apply]; split_ifs
        · exact hx
        · exact R.cword b
      mem := fun b hb => by
        simp only [Function.update_apply]
        rw [hm _ (by omega)]
        by_cases hbj : b = j
        · subst hbj; simp
        · rw [if_neg (by omega), if_neg hbj]; exact R.mem b hb
      input := R.input
      cur := by rw [hlow _ (by omega)]; exact R.cur
      inp := by rw [hlow _ (by omega)]; exact R.inp
      tot := by rw [hlow _ (by omega)]; exact R.tot
      table := by
        obtain ⟨segs, hT, hx⟩ := R.table
        exact ⟨segs, hT.frame hfr hi, hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ?_ }, hi, hn, hfr⟩
  · have ho' := R.out
    cases mode with
    | direct => simp only [OutRel] at ho' ⊢; rw [ho, ho']
    | buffer ovf =>
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho'
        refine ⟨ho.trans h1, by rw [hlow _ (by omega)]; exact h2,
          by rw [hlow _ (by omega)]; exact h3, by rw [hlow _ (by omega)]; exact h4, h5, h6, h7, h8,
          fun k hk => ?_⟩
        have hk' : k < s.out.length := hk
        rw [hm _ (by omega), if_neg (by omega)]
        exact h9 k hk'

section instrs

variable {s S : State} {A : ℕ}

theorem set_spec {a n l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A ([.set rR n, .and rR rR rMask] ++ (stCode a rR ++ [.jump l]))) :
    Reaches w p g ks tb mode x' out₀ (2 + 5) S l
      { s with mem := setCell g.v s.mem a n } := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have e := (x_set (w := w) (s := S) (fetch hf1 (i := 0) (by simp [hpc]) rfl) (by omega)).trans
    (x_and (fetch hf1 (i := 1) (by simp [hpc]) rfl)
      (E.word.update _ (Nat.mod_lt _ (by positivity))) (by omega) (by omega) (by omega))
  obtain ⟨S1, e, hS1⟩ := (⟨_, e, rfl⟩ : ∃ S', Exec w p (1 + 1) S S' ∧ S' = _)
  have t1 : TempsOnly S S1 := by subst hS1; exact TempsOnly.update₂ (by omega) (by omega)
  obtain ⟨S', e', hpc', R', hfr⟩ := value_finish (val := n) (A₁ := A + 2) R e t1
    (by subst hS1; simp [hpc]) (hf2.congr (by simp)) (by
      subst hS1
      simp only [Function.update_self]
      rw [Function.update_of_ne (show (2 : ℕ) ≠ 12 by decide), E.mask, land_mask,
        mod_mod_of_le E.hv])
  exact ⟨S', e', hpc', R', hfr⟩

theorem load_spec {a b l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB b ++ ([.add rT rB rBase, .load rR rT] ++ (stCode a rR ++ [.jump l])))) :
    Reaches w p g ks tb mode x' out₀ (4 + 2 + 5) S l
      { s with mem := setCell g.v s.mem a (s.mem (s.mem (b % 2 ^ g.v) % 2 ^ g.v)) } := by
  obtain ⟨hf1, hf⟩ := fits_append.1 hf
  obtain ⟨hf2, hf3⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have low := E.low
  have room := E.room
  have hbv : b % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  set j := s.mem (b % 2 ^ g.v)
  have hj : j < 2 ^ g.v := R.cword _
  have hB1' : S1.mem rB = j := by rw [hB1, R.mem _ hbv]
  have e2 := e1.trans ((x_add (fetch hf2 (i := 0) (by simp [hpc1]) rfl) (by omega) (by omega)
    (by omega)).trans (x_load (fetch hf2 (i := 1) (by simp [hpc1]) rfl)
      (E1.word.update _ (Nat.mod_lt _ (by positivity))) (by omega) (by omega)))
  obtain ⟨S2, e2, hS2⟩ := (⟨_, e2, rfl⟩ : ∃ S', Exec w p (4 + (1 + 1)) S S' ∧ S' = _)
  have t2 : TempsOnly S S2 := t1.trans (by subst hS2; exact TempsOnly.update₂ (by omega) (by omega))
  obtain ⟨S', e', hpc', R', hfr⟩ := value_finish (val := s.mem (j % 2 ^ g.v)) (A₁ := A + 4 + 2) R e2 t2
    (by subst hS2; simp [hpc1]) (hf3.congr (by simp)) (by
      subst hS2
      simp only [Function.update_self, E1.baseCell, hB1']
      rw [Nat.mod_eq_of_lt (by omega : j + g.base < 2 ^ w), Function.update_of_ne (by omega),
        t1.1 _ (by omega), Nat.add_comm, R.mem _ hj, Nat.mod_eq_of_lt hj,
        Nat.mod_eq_of_lt (R.cword _)])
  exact ⟨S', e', hpc', R', hfr⟩

theorem store_spec {a b l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB a ++ (ldCode rC b ++ [.add rT rB rBase, .store rT rC, .jump l]))) :
    Reaches w p g ks tb mode x' out₀ (4 + 4 + 3) S l
      { s with mem := setCell g.v s.mem (s.mem (a % 2 ^ g.v)) (s.mem (b % 2 ^ g.v)) } := by
  obtain ⟨hf1, hf⟩ := fits_append.1 hf
  obtain ⟨hf2, hf3⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have low := E.low
  have room := E.room
  have hav : a % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  have hbv : b % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  obtain ⟨S2, e2, hpc2, hC2, o2, t2, E2⟩ := ld_spec' E1 hf2 (by simpa using hpc1)
    (V := rC) (by omega)
  set j := s.mem (a % 2 ^ g.v)
  have hj : j < 2 ^ g.v := R.cword _
  have hB2 : S2.mem rB = j := by rw [o2 _ (by decide) (by decide), hB1, R.mem _ hav]
  have hC2' : S2.mem rC = s.mem (b % 2 ^ g.v) := by
    rw [hC2, t1.1 _ (by omega), R.mem _ hbv]
  have e3 := (e1.trans e2).trans ((x_add (fetch hf3 (i := 0) (by simp [hpc2]) rfl) (by omega)
    (by omega) (by omega)).trans (x_store (fetch hf3 (i := 1) (by simp [hpc2]) rfl)
      (E2.word.update _ (Nat.mod_lt _ (by positivity))) (by omega) (by omega)))
  have e4 := e3.trans (x_jump (fetch hf3 (i := 2) (by simp [hpc2]) rfl))
  obtain ⟨S3, e4, hS3⟩ := (⟨_, e4, rfl⟩ : ∃ S', Exec w p (4 + 4 + (1 + 1) + 1) S S' ∧ S' = _)
  have hT : (S2.mem rB + S2.mem rBase) % 2 ^ w = g.base + j := by
    rw [hB2, E2.baseCell, Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  have hwr := R.write_region (S' := S3) hj (R.cword (b % 2 ^ g.v)) (fun c hc => by
      subst hS3
      simp only [Function.update_self, hT, Function.update_apply]
      rw [if_neg (show c ≠ rT by omega), if_neg (show (11 : ℕ) ≠ rT by decide), hC2']
      by_cases hc' : c = g.base + j
      · rw [if_pos hc', if_pos hc']
      · rw [if_neg hc', if_neg hc', t2.1 _ hc, t1.1 _ hc])
    (E.word.exec e4)
    (by subst hS3; exact t2.2.1.trans t1.2.1) (by subst hS3; exact t2.2.2.1.trans t1.2.2.1)
    (by subst hS3; exact t2.2.2.2.trans t1.2.2.2)
  refine ⟨S3, e4, by subst hS3; rfl, ?_, hwr.2⟩
  have : setCell g.v s.mem j (s.mem (b % 2 ^ g.v)) =
      Function.update s.mem j (s.mem (b % 2 ^ g.v)) := by
    rw [setCell_eq_update, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (R.cword _)]
  rw [this]; exact hwr.1

theorem not_spec {a b l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB b ++ ([.sub rR rMask rB] ++ (stCode a rR ++ [.jump l])))) :
    Reaches w p g ks tb mode x' out₀ (4 + 1 + 5) S l
      { s with mem := setCell g.v s.mem a (2 ^ g.v - 1 - s.mem (b % 2 ^ g.v)) } := by
  obtain ⟨hf1, hf⟩ := fits_append.1 hf
  obtain ⟨hf2, hf3⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hbv : b % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  have e2 := e1.trans (x_sub (fetch hf2 (i := 0) (by simp [hpc1]) rfl) E1.word (by omega)
    (by omega) (by omega))
  obtain ⟨S2, e2, hS2⟩ := (⟨_, e2, rfl⟩ : ∃ S', Exec w p (4 + 1) S S' ∧ S' = _)
  have t2 : TempsOnly S S2 := t1.trans (by subst hS2; exact TempsOnly.update (by omega))
  have hpos : 0 < 2 ^ g.v := by positivity
  obtain ⟨S', e', hpc', R', hfr⟩ := value_finish (val := 2 ^ g.v - 1 - s.mem (b % 2 ^ g.v))
    (A₁ := A + 4 + 1) R e2 t2
    (by subst hS2; simp [hpc1]) (hf3.congr (by simp)) (by
      subst hS2
      simp only [Function.update_self]
      rw [E1.mask, hB1, R.mem _ hbv,
        Nat.mod_eq_of_lt (show 2 ^ g.v - 1 - s.mem (b % 2 ^ g.v) < 2 ^ g.v by omega)])
  exact ⟨S', e', hpc', R', hfr⟩

theorem inputLength_spec {a l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A ([.and rR rTot rMask] ++ (stCode a rR ++ [.jump l]))) :
    Reaches w p g ks tb mode x' out₀ (1 + 5) S l
      { s with mem := setCell g.v s.mem a s.input.length } := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have e1 := x_and (w := w) (s := S) (fetch hf1 (i := 0) (by simp [hpc]) rfl) E.word
    (by omega) (by omega) (by omega)
  obtain ⟨S1, e1, hS1⟩ := (⟨_, e1, rfl⟩ : ∃ S', Exec w p 1 S S' ∧ S' = _)
  have t1 : TempsOnly S S1 := by subst hS1; exact TempsOnly.update (by omega)
  obtain ⟨S', e', hpc', R', hfr⟩ := value_finish (val := s.input.length) (A₁ := A + 1) R e1 t1
    (by subst hS1; simp [hpc]) (hf2.congr (by simp)) (by
      subst hS1
      simp only [Function.update_self]
      rw [E.mask, land_mask, R.tot, R.input])
  exact ⟨S', e', hpc', R', hfr⟩

theorem jump_spec {l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A [.jump l]) : Reaches w p g ks tb mode x' out₀ 1 S l s := by
  have e := x_jump (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl)
  exact ⟨_, e, rfl, R.tempsOnly TempsOnly.setPc R.env.word, TempsOnly.setPc.frame⟩

theorem jzero_spec {a l l' : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB a ++ [.jzero rB l, .jump l'])) :
    ∃ n ≤ 6, Reaches w p g ks tb mode x' out₀ n S
      (if s.mem (a % 2 ^ g.v) = 0 then l else l') s := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hav : a % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  have hB1' : S1.mem rB = s.mem (a % 2 ^ g.v) := by rw [hB1, R.mem _ hav]
  have R1 := R.tempsOnly t1 E1.word
  by_cases h0 : s.mem (a % 2 ^ g.v) = 0
  · have e := e1.trans (x_jzero_pos (fetch hf2 (i := 0) (by simp [hpc1]) rfl) (by omega)
      (by rw [hB1', h0]))
    refine ⟨4 + 1, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc E1.word,
      (t1.trans TempsOnly.setPc).frame⟩
  · have e := (e1.trans (x_jzero_neg (fetch hf2 (i := 0) (by simp [hpc1]) rfl) (by omega)
      (by rw [hB1']; exact h0))).trans (x_jump (fetch hf2 (i := 1) (by simp [hpc1]) rfl))
    refine ⟨4 + 1 + 1, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc E1.word,
      (t1.trans TempsOnly.setPc).frame⟩

theorem jeof_spec {l l' : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A [.sub rU rTot rCur, .jzero rU l, .jump l']) :
    ∃ n ≤ 3, Reaches w p g ks tb mode x' out₀ n S (if s.inp.isEmpty then l else l') s := by
  have E := R.env
  have hw := E.hw
  have e1 := x_sub (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) E.word (by omega)
    (by omega) (by omega)
  obtain ⟨S1, e1, hS1⟩ := (⟨_, e1, rfl⟩ : ∃ S', Exec w p 1 S S' ∧ S' = _)
  have t1 : TempsOnly S S1 := by subst hS1; exact TempsOnly.update (by omega)
  have hU : S1.mem rU = x'.length - S.mem rCur := by subst hS1; simp [R.tot]
  have hpc1 : S1.pc = A + 1 := by subst hS1; simp [hpc]
  have R1 := R.tempsOnly t1 (E.word.exec e1)
  have hm1 := E.word.exec e1
  have hcur := R.cur
  have hemp : s.inp.isEmpty ↔ x'.length - S.mem rCur = 0 := by
    rw [R.inp, List.isEmpty_iff, List.drop_eq_nil_iff]; omega
  by_cases h0 : s.inp.isEmpty
  · have e := e1.trans (x_jzero_pos (fetch hf (i := 1) (by simp [hpc1]) rfl) (by omega)
      (by rw [hU]; exact hemp.1 h0))
    refine ⟨1 + 1, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc hm1,
      (t1.trans TempsOnly.setPc).frame⟩
  · have e := (e1.trans (x_jzero_neg (fetch hf (i := 1) (by simp [hpc1]) rfl) (by omega)
      (by rw [hU]; exact fun h => h0 (hemp.2 h)))).trans
        (x_jump (fetch hf (i := 2) (by simp [hpc1]) rfl))
    refine ⟨1 + 1 + 1, by omega, _, e, by simp [h0], R1.tempsOnly TempsOnly.setPc hm1,
      (t1.trans TempsOnly.setPc).frame⟩

theorem W_temps (g : Geo) : g.W rR ∧ g.W rT ∧ g.W rU ∧ g.W rD := by
  simp only [Geo.W]; omega

/-- Fetch entry `rD` of the simulated input into `rR`, reduced to `v` bits. -/
theorem fetchEntry_spec {E' : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (chainCode ks tb A E' ++ [.and rR rR rMask])) (hE : E' = A + chainLen ks) :
    ∃ n ≤ 6 * ks.length + 2, ∃ S', Exec w p n S S' ∧ S'.pc = E' + 1 ∧
      S'.mem rR = x'.getD (S.mem rD) 0 % 2 ^ g.v ∧ TempsOnly S S' := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  obtain ⟨segs, hT, hx⟩ := R.table
  obtain ⟨n, m, hn, e1, hR1, hrest⟩ := chain_spec (W_temps g) E.word E.zero hw hT R.tb16 R.tbw
    hf1 hpc hE
  have e2 := e1.trans (x_and (fetch hf2 (i := 0) (by simp [chainCode_length, hE]) rfl)
    (E.word.exec e1) (by omega) (by omega) (by omega))
  refine ⟨n + 1, by omega, _, e2, by simp [hE], ?_, ?_⟩
  · simp only [Function.update_self]
    rw [hrest rMask (by decide) (by decide) (by decide) (by decide), E.mask, hR1, hx, land_mask,
      mod_mod_of_le E.hv]
  · refine ⟨fun b hb => ?_, rfl, rfl, rfl⟩
    show Function.update m rR _ b = S.mem b
    rw [Function.update_of_ne (by omega), hrest _ (by omega) (by omega) (by omega) (by omega)]

theorem inputLoad_spec {a b l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rD b ++ (chainCode ks tb (A + 4) (A + 4 + chainLen ks) ++
      ([.and rR rR rMask] ++ (stCode a rR ++ [.jump l]))))) :
    ∃ n ≤ 6 * ks.length + 11, Reaches w p g ks tb mode x' out₀ n S l
      { s with mem := setCell g.v s.mem a (s.input[s.mem (b % 2 ^ g.v) % 2 ^ g.v]?.getD 0) } := by
  obtain ⟨hf1, hf⟩ := fits_append.1 hf
  rw [← List.append_assoc] at hf
  obtain ⟨hf2, hf3⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hbv : b % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hD1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rD) (by omega)
  have R1 := R.tempsOnly t1 E1.word
  obtain ⟨n, hn, S2, e2, hpc2, hR2, t2⟩ := fetchEntry_spec R1 hpc1 (hf2.congr (by simp)) rfl
  obtain ⟨S', e', hpc', R', hfr⟩ := value_finish (val := x'.getD (S1.mem rD) 0)
    (A₁ := A + 4 + chainLen ks + 1) R (e1.trans e2) (t1.trans t2) (by rw [hpc2])
    (hf3.congr (by simp [chainCode_length]; omega)) hR2
  refine ⟨4 + n + 5, by omega, S', e', hpc', ?_, hfr⟩
  have hv : s.input[s.mem (b % 2 ^ g.v) % 2 ^ g.v]?.getD 0 = x'.getD (S1.mem rD) 0 := by
    rw [Nat.mod_eq_of_lt (R.cword _), R.input, ← List.getD_eq_getElem?_getD, ← R.mem _ hbv, ← hD1]
  rw [hv]
  exact R'

/-- Advance the cursor past one entry of the simulated input. -/
theorem Rel.advance {S' : State} {u : ℕ} {rest : List ℕ} (R : Rel w g ks tb mode x' out₀ s S)
    (hs : s.inp = u :: rest)
    (hm : S'.mem = Function.update S.mem rCur (S.mem rCur + 1))
    (hi : S'.input = S.input) (hn : S'.inp = S.inp) (ho : S'.out = S.out) :
    Rel w g ks tb mode x' out₀ { s with inp := rest } S' ∧ Frame g S S' ∧
      S.mem rCur < x'.length ∧ x'.getD (S.mem rCur) 0 = u := by
  have E := R.env
  have hinp := R.inp
  rw [hs] at hinp
  have hlt : S.mem rCur < x'.length := by
    by_contra h
    rw [List.drop_eq_nil_of_le (by omega)] at hinp
    cases hinp
  have hu : x'.getD (S.mem rCur) 0 = u := by
    rw [List.drop_eq_getElem_cons hlt] at hinp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact (List.cons.inj hinp).1.symm
  have hrest : rest = x'.drop (S.mem rCur + 1) := by
    rw [List.drop_eq_getElem_cons hlt] at hinp
    exact (List.cons.inj hinp).2
  have htot : S.mem rTot < 2 ^ w := E.word _
  have hfr : ∀ b, b ≠ rCur → S'.mem b = S.mem b := by
    intro b hb; rw [hm, Function.update_of_ne hb]
  have hw' : WordMem w S'.mem := by
    rw [hm]; exact E.word.update _ (by rw [R.tot] at htot; omega)
  refine ⟨
    { env := ⟨hw', by rw [hfr _ (by decide)]; exact E.zero, by rw [hfr _ (by decide)]; exact E.one,
        by rw [hfr _ (by decide)]; exact E.mask, by rw [hfr _ (by decide)]; exact E.baseCell,
        E.room, E.low, E.hv⟩
      cword := R.cword
      mem := fun b hb => by have := E.low; rw [hfr _ (by omega)]; exact R.mem b hb
      input := R.input
      cur := by rw [hm, Function.update_self]; omega
      inp := by rw [hm, Function.update_self]; exact hrest
      tot := by rw [hfr _ (by decide)]; exact R.tot
      table := by
        obtain ⟨segs, hT, hx⟩ := R.table
        exact ⟨segs, hT.frame (fun b hb => hfr b (fun h => hb (h ▸ Or.inl rfl))) hi, hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ?_ }, ⟨hi, hn, fun b hb => hfr b (fun h => hb (h ▸ Or.inl rfl))⟩, hlt, hu⟩
  have ho' := R.out
  cases mode with
  | direct => simp only [OutRel] at ho' ⊢; rw [ho, ho']
  | buffer ovf =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho'
      refine ⟨ho.trans h1, by rw [hfr _ (by decide)]; exact h2, by rw [hfr _ (by decide)]; exact h3,
        by rw [hfr _ (by decide)]; exact h4, h5, h6, h7, h8, fun k hk => ?_⟩
      rw [hfr _ (by omega)]
      exact h9 k hk

/-- The block of `read a`. -/
def readCode (ks : List SegKind) (tb A exit a l : ℕ) : Program :=
  [.sub rU rTot rCur, .jzero rU exit, .add rD rCur rZ] ++
    ((chainCode ks tb (A + 3) (A + 3 + chainLen ks) ++ [.and rR rR rMask]) ++
      ([.add rCur rCur rOne] ++ (stCode a rR ++ [.jump l])))

theorem read_none {exit a l : ℕ} (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (readCode ks tb A exit a l)) (hs : s.inp = []) :
    Reaches w p g ks tb mode x' out₀ 2 S exit s := by
  obtain ⟨hf1, -⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have e1 := x_sub (w := w) (s := S) (fetch hf1 (i := 0) (by simp [hpc]) rfl) E.word (by omega)
    (by omega) (by omega)
  have h0 : x'.length - S.mem rCur = 0 := by
    have := R.inp; rw [hs, eq_comm, List.drop_eq_nil_iff] at this; omega
  have e2 := e1.trans (x_jzero_pos (fetch hf1 (i := 1) (by simp [hpc]) rfl) (by omega)
    (by simp [R.tot, h0]))
  exact ⟨_, e2, rfl, R.tempsOnly (TempsOnly.update (by omega)) (E.word.exec e2),
    (TempsOnly.update (by omega)).frame⟩

theorem read_some {exit a l u : ℕ} {rest : List ℕ} (R : Rel w g ks tb mode x' out₀ s S)
    (hpc : S.pc = A) (hf : Fits p A (readCode ks tb A exit a l)) (hs : s.inp = u :: rest) :
    ∃ n ≤ 6 * ks.length + 12, Reaches w p g ks tb mode x' out₀ n S l
      { s with mem := setCell g.v s.mem a u, inp := rest } := by
  obtain ⟨hf1, hf⟩ := fits_append.1 hf
  obtain ⟨hf2, hf⟩ := fits_append.1 hf
  obtain ⟨hf3, hf4⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hcx : S.mem rCur < x'.length := by
    have := R.inp; rw [hs] at this
    by_contra h; rw [List.drop_eq_nil_of_le (by omega)] at this; cases this
  have e1 := x_sub (w := w) (s := S) (fetch hf1 (i := 0) (by simp [hpc]) rfl) E.word (by omega)
    (by omega) (by omega)
  have e2 := (e1.trans (x_jzero_neg (fetch hf1 (i := 1) (by simp [hpc]) rfl) (by omega)
    (by simp [R.tot]; omega))).trans (x_add (fetch hf1 (i := 2) (by simp [hpc]) rfl) (by omega)
      (by omega) (by omega))
  obtain ⟨S1, e2, hS1⟩ := (⟨_, e2, rfl⟩ : ∃ S', Exec w p (1 + 1 + 1) S S' ∧ S' = _)
  have t1 : TempsOnly S S1 := by subst hS1; exact TempsOnly.update₂ (by omega) (by omega)
  have hD1 : S1.mem rD = S.mem rCur := by
    subst hS1
    simp only [Function.update_self]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), E.zero,
      Nat.add_zero, Nat.mod_eq_of_lt (E.word _)]
  have R1 := R.tempsOnly t1 (E.word.exec e2)
  obtain ⟨n, hn, S2, e3, hpc2, hR2, t2⟩ := fetchEntry_spec R1 (by subst hS1; simp [hpc])
    hf2 rfl
  have hm2 := E.word.exec (e2.trans e3)
  have e4 := e3.trans (x_add (fetch hf3 (i := 0) (by simp [hpc2, chainCode_length]; omega) rfl) (by omega)
    (by omega) (by omega))
  obtain ⟨S3, e4, hS3⟩ := (⟨_, e4, rfl⟩ : ∃ S', Exec w p (n + 1) S1 S' ∧ S' = _)
  have R2 := R1.tempsOnly t2 hm2
  have hcur2 : S2.mem rCur = S.mem rCur := by
    rw [t2.1 _ (by omega), t1.1 _ (by omega)]
  obtain ⟨R3, fr3, -, hu⟩ := R2.advance (S' := S3) hs (by
      subst hS3
      simp only [E.one, hcur2]
      rw [t2.1 _ (by omega), t1.1 _ (by omega), E.one, Nat.mod_eq_of_lt]
      rw [R.tot] at *
      have := E.word rTot; rw [R.tot] at this; omega)
    (by subst hS3; rfl) (by subst hS3; rfl) (by subst hS3; rfl)
  have hR3 : S3.mem rR = u % 2 ^ g.v := by
    subst hS3
    show Function.update S2.mem rCur ((S2.mem rCur + S2.mem rOne) % 2 ^ w) rR = _
    rw [Function.update_of_ne (by decide), hR2, hD1, ← hu, hcur2]
  obtain ⟨S', e5, hpc', R', fr', -⟩ := finish_spec (A := A + 3 + chainLen ks + 1 + 1) (val := u)
    R3 (hf4.congr (by simp [chainCode_length]; omega)) (by subst hS3; simp [hpc2]) hR3
  refine ⟨3 + (n + 1) + 5, by omega, S', (e2.trans e4).trans e5, hpc', R', ?_⟩
  exact ((t1.frame.trans t2.frame).trans fr3).trans fr'

theorem Rel.out_direct {S' : State} {z : ℕ} (R : Rel w g ks tb .direct x' out₀ s S)
    (hm : S'.mem = S.mem) (hi : S'.input = S.input) (ho : S'.out = S.out ++ [z]) :
    Rel w g ks tb .direct x' out₀ { s with out := s.out ++ [z] } S' := by
  have E := R.env
  have hh : ∀ b, S'.mem b = S.mem b := fun b => by rw [hm]
  refine
    { env := ⟨fun b => by rw [hh]; exact E.word b, by rw [hh]; exact E.zero,
        by rw [hh]; exact E.one, by rw [hh]; exact E.mask, by rw [hh]; exact E.baseCell,
        E.room, E.low, E.hv⟩
      cword := R.cword
      mem := fun b hb => by rw [hh]; exact R.mem b hb
      input := R.input
      cur := by rw [hh]; exact R.cur
      inp := by rw [hh]; exact R.inp
      tot := by rw [hh]; exact R.tot
      table := by
        obtain ⟨segs, hT, hx⟩ := R.table
        exact ⟨segs, hT.frame (fun b _ => hh b) hi, hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ?_ }
  have ho' := R.out
  simp only [OutRel] at ho' ⊢
  rw [ho, ho', List.append_assoc]

theorem write_direct {a l : ℕ} (R : Rel w g ks tb .direct x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB a ++ [.write rB, .jump l])) :
    Reaches w p g ks tb .direct x' out₀ (4 + 1 + 1) S l
      { s with out := s.out ++ [s.mem (a % 2 ^ g.v) % 2 ^ g.v] } := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hav : a % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  have e := (e1.trans (x_write (fetch hf2 (i := 0) (by simp [hpc1]) rfl) E1.word
    (by omega))).trans (x_jump (fetch hf2 (i := 1) (by simp [hpc1]) rfl))
  have R1 := R.tempsOnly t1 E1.word
  refine ⟨_, e, rfl, ?_, ⟨t1.2.1, t1.2.2.1, fun b hb => t1.1 b (by simp only [Geo.W] at hb; omega)⟩⟩
  have hz : S1.mem rB = s.mem (a % 2 ^ g.v) % 2 ^ g.v := by
    rw [hB1, R.mem _ hav, Nat.mod_eq_of_lt (R.cword _)]
  exact R1.out_direct (S' := { S1 with pc := l, out := S1.out ++ [S1.mem rB] }) rfl rfl
    (by simp [hz])

theorem write_buffer {a l ovf : ℕ} (R : Rel w g ks tb (.buffer ovf) x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (ldCode rB a ++ [.sub rU rCap rOC, .jzero rU ovf, .add rT rOB rOC,
      .store rT rB, .add rOC rOC rOne, .jump l])) :
    (s.out.length < g.cap → Reaches w p g ks tb (.buffer ovf) x' out₀ (4 + 6) S l
      { s with out := s.out ++ [s.mem (a % 2 ^ g.v) % 2 ^ g.v] }) ∧
    (s.out.length = g.cap → ∃ S', Exec w p (4 + 2) S S' ∧ S'.pc = ovf ∧ Frame g S S' ∧
      S'.out = S.out) := by
  obtain ⟨hf1, hf2⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have low := E.low
  have room := E.room
  have hav : a % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  have R1 := R.tempsOnly t1 E1.word
  obtain ⟨ho1, hob, hoc, hcap, hle, hob16, hobw, hdisj, hbuf⟩ := R1.out
  have e2 := e1.trans (x_sub (fetch hf2 (i := 0) (by simp [hpc1]) rfl) E1.word (by omega)
    (by omega) (by omega))
  obtain ⟨S2, e2, hS2⟩ := (⟨_, e2, rfl⟩ : ∃ S', Exec w p (4 + 1) S S' ∧ S' = _)
  have t2 : TempsOnly S S2 := t1.trans (by subst hS2; exact TempsOnly.update (by omega))
  have hU2 : S2.mem rU = g.cap - s.out.length := by subst hS2; simp [hcap, hoc]
  have hpc2 : S2.pc = A + 4 + 1 := by subst hS2; simp [hpc1]
  constructor
  · intro hlt
    have hm2 := E.word.exec e2
    have hob2 : S2.mem rOB = g.ob := by rw [t2.1 _ (by omega), ← t1.1 _ (by omega), hob]
    have hoc2 : S2.mem rOC = s.out.length := by rw [t2.1 _ (by omega), ← t1.1 _ (by omega), hoc]
    have hB2 : S2.mem rB = s.mem (a % 2 ^ g.v) := by
      subst hS2; simp only; rw [Function.update_of_ne (by decide), hB1, R.mem _ hav]
    have e3 := (x_jzero_neg (w := w) (s := S2) (fetch hf2 (i := 1) (by simp [hpc2]) rfl) (by omega)
      (by rw [hU2]; omega)).trans (x_add (fetch hf2 (i := 2) (by simp [hpc2]) rfl) (by omega)
        (by omega) (by omega))
    obtain ⟨S4, e3, hS4⟩ := (⟨_, e3, rfl⟩ : ∃ S', Exec w p (1 + 1) S2 S' ∧ S' = _)
    set X := g.ob + s.out.length
    have hm4 : ∀ b, S4.mem b = if b = rT then X else S2.mem b := by
      intro b; subst hS4; dsimp only
      rw [Function.update_apply, hob2, hoc2, Nat.mod_eq_of_lt (by omega)]
    have hpc4 : S4.pc = A + 4 + 3 := by subst hS4; simp [hpc2]
    have hm4w := hm2.exec e3
    have e4 := (x_store (w := w) (s := S4) (fetch hf2 (i := 3) (by simp [hpc4]) rfl) hm4w (by omega)
      (by omega))
    obtain ⟨S5, e4, hS5⟩ := (⟨_, e4, rfl⟩ : ∃ S', Exec w p 1 S4 S' ∧ S' = _)
    have hm5 : ∀ b, S5.mem b = if b = X then s.mem (a % 2 ^ g.v) else S4.mem b := by
      intro b; subst hS5; dsimp only
      rw [Function.update_apply, hm4 rT, hm4 rB, if_pos rfl, if_neg (show (10 : ℕ) ≠ 9 by decide),
        hB2]
    have hpc5 : S5.pc = A + 4 + 4 := by subst hS5; simp [hpc4]
    have hm5w := hm4w.exec e4
    have e5 := (x_add (w := w) (s := S5) (fetch hf2 (i := 4) (by simp [hpc5]) rfl) (by omega) (by omega)
      (by omega)).trans (x_jump (fetch hf2 (i := 5) (by simp [hpc5]) rfl))
    obtain ⟨S', e5, hS'⟩ := (⟨_, e5, rfl⟩ : ∃ S', Exec w p (1 + 1) S5 S' ∧ S' = _)
    have hm' : ∀ b, S'.mem b = if b = rOC then s.out.length + 1 else S5.mem b := by
      intro b; subst hS'; dsimp only
      rw [Function.update_apply, hm5 rOC, hm5 rOne, if_neg (show (7 : ℕ) ≠ X by omega),
        if_neg (show (1 : ℕ) ≠ X by omega), hm4 rOC, hm4 rOne,
        if_neg (show (7 : ℕ) ≠ 9 by decide), if_neg (show (1 : ℕ) ≠ 9 by decide), hoc2,
        t2.1 _ (show (1 : ℕ) < 9 ∨ 14 < 1 by omega), E.one,
        Nat.mod_eq_of_lt (by omega)]
    -- the memory of `S'` cell by cell
    have hS'm : ∀ b, S'.mem b = if b = rOC then s.out.length + 1 else
        if b = X then s.mem (a % 2 ^ g.v) else if b = rT then X else S2.mem b := by
      intro b; rw [hm', hm5, hm4]
    have hfr : ∀ b, ¬ g.W b → S'.mem b = S.mem b := by
      intro b hb
      simp only [Geo.W] at hb
      rw [hS'm, if_neg (by omega), if_neg (by omega), if_neg (by omega), t2.1 _ (by omega)]
    have hlow : ∀ b, (b < rT ∨ rU < b) → b ≠ rOC → b ≠ X → S'.mem b = S.mem b := by
      intro b hb h1 h2
      rw [hS'm, if_neg h1, if_neg h2, if_neg (by omega), t2.1 _ hb]
    have hpcS : S'.pc = l := by subst hS'; rfl
    have hinS : S'.input = S.input := by
      subst hS'; subst hS5; subst hS4; exact t2.2.1
    have hinpS : S'.inp = S.inp := by
      subst hS'; subst hS5; subst hS4; exact t2.2.2.1
    have houtS : S'.out = S.out := by
      subst hS'; subst hS5; subst hS4; exact t2.2.2.2
    refine ⟨S', ((e2.trans e3).trans e4).trans e5, hpcS, ?_, hinS, hinpS, hfr⟩
    have hwS := hm5w.exec e5
    refine
      { env := ⟨hwS, by rw [hlow _ (by omega) (by decide) (by omega)]; exact E.zero,
          by rw [hlow _ (by omega) (by decide) (by omega)]; exact E.one,
          by rw [hlow _ (by omega) (by decide) (by omega)]; exact E.mask,
          by rw [hlow _ (by omega) (by decide) (by omega)]; exact E.baseCell, E.room, E.low, E.hv⟩
        cword := R.cword
        mem := fun b hb => by
          rw [hlow _ (by omega) (by omega) (by omega)]; exact R.mem b hb
        input := R.input
        cur := by rw [hlow _ (by omega) (by decide) (by omega)]; exact R.cur
        inp := by rw [hlow _ (by omega) (by decide) (by omega)]; exact R.inp
        tot := by rw [hlow _ (by omega) (by decide) (by omega)]; exact R.tot
        table := by
          obtain ⟨segs, hT, hx⟩ := R.table
          exact ⟨segs, hT.frame hfr hinS, hx⟩
        tb16 := R.tb16
        tbw := R.tbw
        out := ?_ }
    have hcap' : S'.mem rCap = g.cap := by
      rw [hlow _ (by omega) (by decide) (by omega), ← t1.1 _ (by omega), hcap]
    have hob' : S'.mem rOB = g.ob := by
      rw [hlow _ (by omega) (by decide) (by omega), ← t1.1 _ (by omega), hob]
    refine ⟨houtS.trans (t1.2.2.2.symm.trans ho1), hob', by rw [hS'm, if_pos rfl]; simp,
      hcap', by simp; omega, hob16, hobw, hdisj, fun j hj => ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    rw [hS'm, if_neg (by omega)]
    by_cases hjx : j = s.out.length
    · subst hjx
      rw [if_pos rfl, List.getD_eq_getElem?_getD]
      simp [Nat.mod_eq_of_lt (R.cword _)]
    · rw [if_neg (by omega), if_neg (by omega), t2.1 _ (by omega), ← t1.1 _ (by omega),
        hbuf j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
  · intro heq
    have e3 := e2.trans (x_jzero_pos (fetch hf2 (i := 1) (by simp [hpc2]) rfl) (by omega)
      (by rw [hU2]; omega))
    exact ⟨_, e3, rfl, (t2.trans TempsOnly.setPc).frame, t2.2.2.2⟩

end instrs

end Lax185574Proofs.RamSim
