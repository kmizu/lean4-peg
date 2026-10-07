import Complexity.OneTape.Track

/-!
# One step of `M` as a macro-step of the simulator

Fix a running configuration `c` of `M` (state and symbols in range, not halted) and its successor `M.step c`.

* `Good c`: the simulator is at cell `0` about to read tape `0` (`rNext k 0 c.state []`), its tape holding the
  columns of `c`.
* Reading (`rloop`): for each tape `i` the simulator seeks head `i`, records the symbol, and goes home (`rstep`).
* Computing (`calc_step`): with all symbols read, it stops in `M`'s new state if that halts, else starts writing.
* Writing (`wloop`): for each tape `i` it seeks head `i`, writes the new symbol, moves the flag like `M` moves the
  head, and goes home (`wstep`); before tape `i` the tape holds the columns of `M.step c` on the tapes below `i`
  and of `c` on the others (`mixPos`, `mixCells`).
* `macro_step`: `Good c` leads to `Good (M.step c)`, or, when `M.step c` halts, to the simulator in its state.
-/

namespace Complexity
namespace OneTape

variable {k : Nat} (M : TM k)

theorem Leads.ex {α : Type} {A : α → Prop} {B : α → Cfg 1 → Prop} {Q : Cfg 1 → Prop}
    (h : ∀ T, A T → Leads M (B T) Q) : Leads M (fun sc => ∃ T, A T ∧ B T sc) Q := by
  intro sc ⟨T, hA, hB⟩
  exact h T hA sc hB

theorem Leads.or_right {A Q Q' : Cfg 1 → Prop} (h : Leads M Q Q') :
    Leads M (fun sc => A sc ∨ Q sc) (fun sc => A sc ∨ Q' sc) := by
  intro sc hs
  rcases hs with hs | hs
  · exact ⟨0, Or.inl hs⟩
  · obtain ⟨n, h'⟩ := h sc hs
    exact ⟨n, Or.inr h'⟩

theorem ofFn_getD' {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem wf_rNext {i q : Nat} {rs : List Nat} (hi : i ≤ k) (hq : q < M.nq) (hl : rs.length = i)
    (hrs : ∀ a ∈ rs, a < M.na) : WF M (rNext k i q rs) := by
  unfold rNext; split
  · exact ⟨by show 0 < 6; decide, hi, hq, by simp [clen, hl], hrs⟩
  · exact ⟨by show 2 < 6; decide, hi, hq, by simp [clen]; omega, hrs⟩

theorem wf_wNext {i q : Nat} {rs : List Nat} (hi : i ≤ k) (hq : q < M.nq) (hl : rs.length = k)
    (hrs : ∀ a ∈ rs, a < M.na) : WF M (wNext M i q rs) := by
  unfold wNext; split
  · exact ⟨by show 3 < 6; decide, hi, hq, by simp [clen, hl], hrs⟩
  · have hrs' : ∀ j : Fin k, rs.getD j.val 0 < M.na := fun j => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact hrs _ (List.getElem_mem _)
    exact wf_rNext M (by omega) (M.delta_state _ _ hq hrs') rfl (by simp)

/-! ## Facts about the configuration being simulated -/

/-- The symbols `c` reads, as a list. -/
abbrev rds (c : Cfg k) : List Nat := List.ofFn c.read

variable {c : Cfg k}

theorem rds_lt (hsym : ∀ i j, c.cells i j < M.na) : ∀ a ∈ rds c, a < M.na := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
  exact hsym _ _

omit M in
theorem length_rds : (rds c).length = k := by simp

theorem mdelta_rds : mdelta M c.state (rds c) = M.delta c.state c.read := by
  unfold mdelta; congr 1; funext j; exact ofFn_getD' _ _ _

theorem step_state (hn : ¬ c.halted) : (M.step c).state = (M.delta c.state c.read).1 := by simp [TM.step, hn]

theorem step_pos (hn : ¬ c.halted) (i : Fin k) :
    (M.step c).pos i = ((M.delta c.state c.read).2.2 i).apply (c.pos i) := by
  simp [TM.step, hn]

theorem step_cells (hn : ¬ c.halted) (i : Fin k) (j : Nat) :
    (M.step c).cells i j = if j = c.pos i then (M.delta c.state c.read).2.1 i else c.cells i j := by
  simp [TM.step, hn]

/-! ## Reading -/

/-- Reading, before tape `i`: the symbols of the tapes below `i` are recorded. -/
def RAt (c : Cfg k) (i : Nat) (sc : Cfg 1) : Prop :=
  ∃ T, TapeRep M T c.pos c.cells ∧ At M (rNext k i c.state ((rds c).take i)) 0 T sc

/-- The simulator at the start of a macro-step for `c`. -/
def Good (c : Cfg k) (sc : Cfg 1) : Prop := RAt M c 0 sc

omit M in
theorem take_rds_succ (fi : Fin k) : (rds c).take fi.val ++ [c.read fi] = (rds c).take (fi.val + 1) := by
  rw [List.take_add_one, List.getElem?_ofFn, dif_pos fi.isLt]; rfl

theorem wf_take (hsym : ∀ i j, c.cells i j < M.na) (i : Nat) : ∀ a ∈ (rds c).take i, a < M.na :=
  fun a ha => rds_lt M hsym a (List.mem_of_mem_take ha)

omit M in
theorem length_take_rds {i : Nat} (hi : i ≤ k) : ((rds c).take i).length = i := by
  simp; omega

/-- **Reading tape `i`**: seek head `i`, record its symbol, go home. -/
theorem rstep (hq : c.state < M.nq) (hsym : ∀ i j, c.cells i j < M.na) (fi : Fin k) :
    Leads M (RAt M c fi.val) (RAt M c (fi.val + 1)) := by
  apply Leads.ex
  intro T hT
  have hi := fi.isLt
  let x : Ctl := ⟨0, fi.val, c.state, (rds c).take fi.val⟩
  let y : Ctl := ⟨1, fi.val + 1, c.state, (rds c).take (fi.val + 1)⟩
  have ex : rNext k fi.val c.state ((rds c).take fi.val) = x := by simp [rNext, hi, x]
  have hx : WF M x := ⟨by show 0 < 6; decide, by show fi.val ≤ k; omega, hq, by
    show ((rds c).take fi.val).length = clen k 0 fi.val; rw [length_take_rds (by omega)]; rfl,
    wf_take M hsym _⟩
  have hy : WF M y := ⟨by show 1 < 6; decide, by show fi.val + 1 ≤ k; omega, hq, by
    show ((rds c).take (fi.val + 1)).length = clen k 1 (fi.val + 1); rw [length_take_rds (by omega)]; rfl,
    wf_take M hsym _⟩
  have hw := wf_rNext M (i := fi.val + 1) (by omega) hq (length_take_rds (by omega)) (wf_take M hsym _)
  rw [ex]
  -- seek head `i`
  have s1 := seek M hx hT fi (fun a _ h => by
    have h' : ¬ cdig M a fi.val % 2 = 1 := h
    simp only [act, x]; simp [h'])
  -- record the symbol
  obtain ⟨hlt, _, hd⟩ := hT (c.pos fi)
  have hd := hd fi
  have hf : flag c.pos fi (c.pos fi) = 1 := by simp [flag]
  rw [hf] at hd
  have hodd : cdig M (T (c.pos fi)) fi.val % 2 = 1 := by omega
  have hsy : cdig M (T (c.pos fi)) fi.val / 2 = c.read fi := by show _ = c.cells fi (c.pos fi); omega
  have s2 := at_step M (p := c.pos fi) (T := T) (m := .S) hx hy hlt (by
    simp only [act, x, y]
    simp only [if_true, hodd, hsy, take_rds_succ fi])
  rw [write_same] at s2
  -- go home
  have s3 := home M hy (fun j => ⟨(hT j).1, (hT j).2.1⟩) (fun a _ h => by simp [act, y, h])
    (Move.S.apply (c.pos fi))
  -- the next tape
  have hl0 : clft (T 0) = true := (hT 0).2.1.2 rfl
  have s4 := at_step M (p := 0) (T := T) (m := .S) hy hw (hT 0).1 (by simp [act, y, hl0])
  rw [write_same] at s4
  exact Leads.mono M (Leads.trans M s1 (Leads.trans M s2 (Leads.trans M s3 s4))) fun sc h => ⟨T, hT, h⟩

theorem rloop (hq : c.state < M.nq) (hsym : ∀ i j, c.cells i j < M.na) :
    ∀ i, i ≤ k → Leads M (RAt M c 0) (RAt M c i)
  | 0, _ => Leads.of_imp M fun _ h => h
  | i + 1, hi => Leads.trans M (rloop hq hsym i (by omega)) (rstep M hq hsym ⟨i, by omega⟩)

/-! ## Writing -/

/-- The heads after the writes on the tapes below `i`. -/
def mixPos (c : Cfg k) (i : Nat) (i' : Fin k) : Nat := if i'.val < i then (M.step c).pos i' else c.pos i'

/-- The contents after the writes on the tapes below `i`. -/
def mixCells (c : Cfg k) (i : Nat) (i' : Fin k) (j : Nat) : Nat :=
  if i'.val < i then (M.step c).cells i' j else c.cells i' j

/-- Writing, before tape `i`. -/
def WAt (c : Cfg k) (i : Nat) (sc : Cfg 1) : Prop :=
  ∃ T, TapeRep M T (mixPos M c i) (mixCells M c i) ∧ At M (wNext M i c.state (rds c)) 0 T sc

omit M in
theorem mix_succ_ne {α : Type} (f g : Fin k → α) (fi i' : Fin k) (h : i' ≠ fi) :
    (if i'.val < fi.val + 1 then f i' else g i') = (if i'.val < fi.val then f i' else g i') := by
  have : i'.val ≠ fi.val := fun e => h (Fin.ext e)
  by_cases h' : i'.val < fi.val
  · rw [if_pos h', if_pos (by omega)]
  · rw [if_neg h', if_neg (by omega)]

/-- **Writing tape `i`**: seek head `i`, write, move the flag, go home. -/
theorem wstep (hq : c.state < M.nq) (hsym : ∀ i j, c.cells i j < M.na) (hn : ¬ c.halted) (fi : Fin k) :
    Leads M (WAt M c fi.val) (WAt M c (fi.val + 1)) := by
  apply Leads.ex
  intro T hT
  have hi := fi.isLt
  let x : Ctl := ⟨3, fi.val, c.state, rds c⟩
  let y1 : Ctl := ⟨4, fi.val, c.state, rds c⟩
  let y2 : Ctl := ⟨5, fi.val + 1, c.state, rds c⟩
  have ex : wNext M fi.val c.state (rds c) = x := by simp [wNext, hi, x]
  have hl : (rds c).length = k := length_rds
  have hx : WF M x := ⟨by show 3 < 6; decide, by show fi.val ≤ k; omega, hq, hl, rds_lt M hsym⟩
  have hy1 : WF M y1 := ⟨by show 4 < 6; decide, by show fi.val ≤ k; omega, hq, hl, rds_lt M hsym⟩
  have hy2 : WF M y2 := ⟨by show 5 < 6; decide, by show fi.val + 1 ≤ k; omega, hq, hl, rds_lt M hsym⟩
  have hw := wf_wNext M (i := fi.val + 1) (by omega) hq hl (rds_lt M hsym)
  have hv : (M.delta c.state c.read).2.1 fi < M.na := M.delta_sym _ _ hq (fun _ => hsym _ _) fi
  have h2v := two_v_lt M hv
  have hp : mixPos M c fi.val fi = c.pos fi := by simp [mixPos]
  have hp1 : mixPos M c (fi.val + 1) fi = ((M.delta c.state c.read).2.2 fi).apply (c.pos fi) := by
    simp only [mixPos, Nat.lt_succ_self, if_true]; exact step_pos M hn fi
  rw [ex]
  -- seek head `i`
  have s1 := seek M hx hT fi (fun a _ h => by
    have h' : ¬ cdig M a fi.val % 2 = 1 := h
    simp only [act, x]; simp [h'])
  rw [hp] at s1
  -- write the new symbol and move
  obtain ⟨hlt, _, hd⟩ := hT (c.pos fi)
  have hd := hd fi
  have hf : flag (mixPos M c fi.val) fi (c.pos fi) = 1 := by simp [flag, hp]
  rw [hf] at hd
  have hodd : cdig M (T (c.pos fi)) fi.val % 2 = 1 := by omega
  have s2 := at_step M (p := c.pos fi) (T := T) (m := (M.delta c.state c.read).2.2 fi) hx hy1
    (setDig_lt M (T (c.pos fi)) fi.val h2v) (by
      simp only [act, x, y1]
      simp only [if_true, hodd, mdelta_rds, ofFn_getD']
      simp)
  -- the tape after both writes
  have hrep := trackRep M hT hv (pos' := mixPos M c (fi.val + 1)) (cells' := mixCells M c (fi.val + 1))
    (fun i' h => by simp only [mixPos]; exact mix_succ_ne _ _ fi i' h)
    (fun i' h => by
      funext j; simp only [mixCells]
      exact mix_succ_ne (fun i => (M.step c).cells i j) (fun i => c.cells i j) fi i' h)
    (fun j => by
      simp only [mixCells, Nat.lt_succ_self, if_true, Nat.lt_irrefl, if_false]
      rw [step_cells M hn, hp])
  rw [hp, hp1] at hrep
  -- set the flag where the head lands
  have hfl := setFlag_lt M hT hv (((M.delta c.state c.read).2.2 fi).apply (c.pos fi)) (i := fi)
  rw [hp] at hfl
  have s3 := at_step M (p := ((M.delta c.state c.read).2.2 fi).apply (c.pos fi))
    (T := upd T (c.pos fi) (setDig M (T (c.pos fi)) fi.val (2 * (M.delta c.state c.read).2.1 fi)))
    (m := .S) hy1 hy2 (setDig_lt M (upd T (c.pos fi) (setDig M (T (c.pos fi)) fi.val
      (2 * (M.delta c.state c.read).2.1 fi)) (((M.delta c.state c.read).2.2 fi).apply (c.pos fi))) fi.val hfl)
    (by simp [act, y1]; rfl)
  -- go home
  have s4 := home M hy2 (fun j => ⟨(hrep j).1, (hrep j).2.1⟩) (fun a _ h => by simp [act, y2, h])
    (Move.S.apply (((M.delta c.state c.read).2.2 fi).apply (c.pos fi)))
  -- the next tape
  have hl0 := (hrep 0).2.1.2 rfl
  have s5 := at_step M (p := 0)
    (T := track2 M T fi (c.pos fi) (((M.delta c.state c.read).2.2 fi).apply (c.pos fi))
      ((M.delta c.state c.read).2.1 fi))
    (m := .S) hy2 hw (hrep 0).1 (by simp [act, y2, hl0])
  rw [write_same] at s5
  exact Leads.mono M (Leads.trans M s1 (Leads.trans M s2 (Leads.trans M s3 (Leads.trans M s4 s5))))
    fun sc h => ⟨_, hrep, h⟩

theorem wloop (hq : c.state < M.nq) (hsym : ∀ i j, c.cells i j < M.na) (hn : ¬ c.halted) :
    ∀ i, i ≤ k → Leads M (WAt M c 0) (WAt M c i)
  | 0, _ => Leads.of_imp M fun _ h => h
  | i + 1, hi => Leads.trans M (wloop hq hsym hn i (by omega)) (wstep M hq hsym hn ⟨i, by omega⟩)

/-! ## Computing and the whole macro-step -/

/-- **Computing**: with all symbols read, stop in `M`'s new state if it halts, else start writing. -/
theorem calc_step (hq : c.state < M.nq) (hsym : ∀ i j, c.cells i j < M.na) (hn : ¬ c.halted) :
    Leads M (RAt M c k) (fun sc => ((M.step c).halted ∧ sc.state = (M.step c).state) ∨
      (¬ (M.step c).halted ∧ WAt M c 0 sc)) := by
  apply Leads.ex
  intro T hT sc ⟨hs, hp, hc⟩
  let x : Ctl := ⟨2, k, c.state, rds c⟩
  have ex : rNext k k c.state ((rds c).take k) = x := by
    simp only [rNext, Nat.lt_irrefl, if_false, x]
    rw [List.take_of_length_le (Nat.le_of_eq length_rds)]
  rw [ex] at hs
  have hx : WF M x := ⟨by show 2 < 6; decide, by show k ≤ k; omega, hq, length_rds, rds_lt M hsym⟩
  have hr : sc.cells 0 (sc.pos 0) = T 0 := by rw [hp, hc]
  have hst := step_state M hn (c := c)
  refine ⟨1, ?_⟩
  by_cases hh : (M.step c).halted
  · have h01 : (M.delta c.state c.read).1 = 0 ∨ (M.delta c.state c.read).1 = 1 := by rw [← hst]; exact hh
    have ha : act M x (sc.cells 0 (sc.pos 0)) = ((M.delta c.state c.read).1, T 0, .S) := by
      rw [hr]; simp only [act, x]
      simp [mdelta_rds, h01]
    have h := step_ctl M hx hs (by rw [ha]; have := three_le_NQ M; omega)
      (by rw [ha]; exact (hT 0).1)
    rw [ha] at h
    exact Or.inl ⟨hh, by show ((sim M).step sc).state = _; rw [h.1, hst]⟩
  · have h01 : ¬ ((M.delta c.state c.read).1 = 0 ∨ (M.delta c.state c.read).1 = 1) := by rw [← hst]; exact hh
    have ha : act M x (sc.cells 0 (sc.pos 0)) = (enc M (wNext M 0 c.state (rds c)), T 0, .S) := by
      rw [hr]; simp only [act, x]
      simp [mdelta_rds, h01]
    have hw := wf_wNext M (i := 0) (by omega) hq length_rds (rds_lt M hsym)
    have h := step_ctl M hx hs (by rw [ha]; exact enc_lt M hw) (by rw [ha]; exact (hT 0).1)
    rw [ha] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine Or.inr ⟨hh, T, ?_, h1, ?_, ?_⟩
    · have e1 : mixPos M c 0 = c.pos := by funext i; simp [mixPos]
      have e2 : mixCells M c 0 = c.cells := by funext i j; simp [mixCells]
      rw [e1, e2]; exact hT
    · show ((sim M).step sc).pos 0 = 0; rw [h2, hp]; rfl
    · show ((sim M).step sc).cells 0 = T; rw [h3, hp, hc]; exact write_same T 0

/-- After the last tape, the simulator is at the start of the macro-step for `M.step c`. -/
theorem wfinal (hn : ¬ c.halted) (sc : Cfg 1) (h : WAt M c k sc) : Good M (M.step c) sc := by
  obtain ⟨T, hT, hs, hp, hc⟩ := h
  have e : wNext M k c.state (rds c) = rNext k 0 (M.step c).state ((rds (M.step c)).take 0) := by
    simp only [wNext, Nat.lt_irrefl, if_false, mdelta_rds, step_state M hn]; rfl
  have e1 : mixPos M c k = (M.step c).pos := by funext i; simp [mixPos, i.isLt]
  have e2 : mixCells M c k = (M.step c).cells := by funext i j; simp [mixCells, i.isLt]
  rw [e1, e2] at hT
  rw [e] at hs
  exact ⟨T, hT, hs, hp, hc⟩

/-- **The macro-step**: the simulator does one step of `M`. -/
theorem macro_step (hq : c.state < M.nq) (hsym : ∀ i j, c.cells i j < M.na) (hn : ¬ c.halted) :
    Leads M (Good M c) (fun sc => ((M.step c).halted ∧ sc.state = (M.step c).state) ∨
      (¬ (M.step c).halted ∧ Good M (M.step c) sc)) := by
  have h1 := Leads.trans M (rloop M hq hsym k (Nat.le_refl _)) (calc_step M hq hsym hn)
  have h2 := Leads.or_right M (A := fun sc => (M.step c).halted ∧ sc.state = (M.step c).state)
    (Q := fun sc => ¬ (M.step c).halted ∧ WAt M c 0 sc)
    (Q' := fun sc => ¬ (M.step c).halted ∧ Good M (M.step c) sc)
    (by
      intro sc ⟨hh, hw⟩
      obtain ⟨n, h⟩ := wloop M hq hsym hn k (Nat.le_refl _) sc hw
      exact ⟨n, hh, wfinal M hn _ h⟩)
  exact Leads.trans M h1 h2

end OneTape
end Complexity
