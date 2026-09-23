import PalPeg.ScaHeadGen
import PalPeg.GSPreprocess

/-!
# The head program `Decompose k` computes `GSPreprocess.decompose`

`Decompose k` (`ScaGsCoroutine.stepDecompose`, Python `_decompose` in
`docs/palindromes-in-peg/gs_heads.py:93-112`) is run alone, from its fresh frame, by the matcher
VM's `stepMatch` on a word `x ++ rest` with `Origin = 0` and `End = |x|`. The contract
`decompose_run` says that it returns within `(160k+418)·|x| + (20k+69)` steps, with
`Cut = (decompose x k).1`, the return value `true` exactly when a period exists, and then
`First`, `KFirst`, `Reach` at `Cut + p₁`, `Cut + k·p₁`, `Cut + r`.

The proof goes bottom up, one contract per generator, each on its own frame chain and lifted into
its caller with `ScaHeadGen.iterStep_lift` (`run_child`):

* `resetShiftF_run` / `periodShiftF_run` (the non-searching variants, `search = false`),
  `init_run` (`Initialize`);
* `first_run` (`First k bounded`) ↔ `firstOuter` / `firstInner`, with
  `n ≤ 10·firstOuterWork + 8`;
* `second_run` (`Second k`) ↔ `secondOuter` / `secondInner`, with `n ≤ 8·secondOuterWork + 7`
  (amortised with the potential `3q`);
* `extend_run` ↔ `extendReach`, `strip_run` ↔ `stripLoop`, `dec_loop` ↔ `decomposeLoop`;
  the step count is `10·decomposeWork + 38·|x| + 19`, and `GSPreprocess.decomposeWork_le` makes it
  linear.

Heads are tracked relationally: `HRel` gives `A = s + q`, `P = s + p`, `B = s + p + q`,
`KP = s + k·p` (the GS scan state `(p, q)` at `Cut = s`), and `Keeps S π0 π` says that only the
heads in `S` moved.
-/
set_option autoImplicit false
namespace PalPeg.ScaHeadDecompose
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen

/-! ## Heads that a run may move -/

/-- Only the heads in `S` differ between `π0` and `π`. -/
def Keeps (S : List String) (π0 π : String → ℤ) : Prop := ∀ h, h ∉ S → π h = π0 h

theorem keeps_refl (S : List String) (π : String → ℤ) : Keeps S π π := fun _ _ => rfl

theorem keeps_update {S : List String} {π0 π : String → ℤ} {X : String} (hX : X ∈ S) (a : ℤ)
    (h : Keeps S π0 π) : Keeps S π0 (Function.update π X a) := by
  intro h' hh'
  rw [Function.update_of_ne (by rintro rfl; exact hh' hX)]
  exact h h' hh'

theorem keeps_trans {S : List String} {π0 π1 π2 : String → ℤ} (h1 : Keeps S π0 π1)
    (h2 : Keeps S π1 π2) : Keeps S π0 π2 := fun h hh => (h2 h hh).trans (h1 h hh)

theorem keeps_mono {S S' : List String} {π0 π : String → ℤ} (hS : ∀ h, h ∈ S → h ∈ S')
    (h : Keeps S π0 π) : Keeps S' π0 π := fun h' hh' => h h' (fun hm => hh' (hS h' hm))

/-! ## One step, as a run combinator -/

theorem moveSeq_cons_ok (L : ℤ) (h : String) (d : ℤ) (ms : List Movement) (π : String → ℤ)
    (hr : h ∉ blind → 0 ≤ π h + d ∧ π h + d ≤ L) :
    moveSeq blind L (⟨h, d⟩ :: ms) π = moveSeq blind L ms (Function.update π h (π h + d)) := by
  simp only [moveSeq, Function.update_self]
  rw [if_neg]
  rintro ⟨hb, hc⟩; exact hc (hr hb)

theorem moveSeq_nil (L : ℤ) (π : String → ℤ) : moveSeq blind L [] π = some π := rfl

theorem moveSeq_AB (L : ℤ) (π : String → ℤ) (hA : 0 ≤ π "A" + 1 ∧ π "A" + 1 ≤ L)
    (hB : 0 ≤ π "B" + 1 ∧ π "B" + 1 ≤ L) :
    moveSeq blind L [⟨"A", 1⟩, ⟨"B", 1⟩] π =
      some (Function.update (Function.update π "A" (π "A" + 1)) "B" (π "B" + 1)) := by
  rw [moveSeq_cons_ok _ _ _ _ _ (fun _ => hA),
    moveSeq_cons_ok _ _ _ _ _ (fun _ => by simpa using hB), moveSeq_nil]
  simp

section Run
variable {v : HVM} {c : Config} {c' : Ctl} {n : ℕ} {w : Option HVM}

theorem run_copy {t s' : String} (hv : v.ctl = .pending c (.copy t s'))
    (hr : (Ctl.pending c (.copy t s')).resume matchTests false = c')
    (h : iterStep n { v with ctl := c', pos := Function.update v.pos t (v.pos s') } = w) :
    iterStep (n + 1) v = w := by
  simp only [iterStep, step_copy hv, Option.bind_some, hr]
  exact h

theorem run_move {ms : List Movement} {π : String → ℤ} (hv : v.ctl = .pending c (.move ms))
    (hm : moveSeq blind v.len ms v.pos = some π)
    (hr : (Ctl.pending c (.move ms)).resume matchTests false = c')
    (h : iterStep n { v with ctl := c', pos := π } = w) :
    iterStep (n + 1) v = w := by
  simp only [iterStep, step_move hv hm, Option.bind_some, hr]
  exact h

theorem run_move1 {h : String} {d : ℤ} (hv : v.ctl = .pending c (.move [⟨h, d⟩]))
    (hrange : h ∉ blind → 0 ≤ v.pos h + d ∧ v.pos h + d ≤ v.len)
    (hr : (Ctl.pending c (.move [⟨h, d⟩])).resume matchTests false = c')
    (h' : iterStep n { v with ctl := c', pos := Function.update v.pos h (v.pos h + d) } = w) :
    iterStep (n + 1) v = w :=
  run_move hv (moveSeq_cons_ok _ _ _ _ _ hrange) hr h'

theorem run_moveAB (hv : v.ctl = .pending c (.move [⟨"A", 1⟩, ⟨"B", 1⟩]))
    (hA : 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len) (hB : 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len)
    (hr : (Ctl.pending c (.move [⟨"A", 1⟩, ⟨"B", 1⟩])).resume matchTests false = c')
    (h : iterStep n { v with
      ctl := c'
      pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B" (v.pos "B" + 1) } = w) :
    iterStep (n + 1) v = w :=
  run_move hv (moveSeq_AB _ _ hA hB) hr h

theorem run_less {a b : String} {d : Bool} (hv : v.ctl = .pending c (.less a b))
    (hd : decide (v.pos a < v.pos b) = d)
    (hr : (Ctl.pending c (.less a b)).resume matchTests d = c')
    (h : iterStep n { v with ctl := c' } = w) :
    iterStep (n + 1) v = w := by
  simp only [iterStep, step_less hv, Option.bind_some, hd, hr]
  exact h

theorem run_equal {a b : String} {d : Bool} (hv : v.ctl = .pending c (.equal a b))
    (hd : decide (v.pos a = v.pos b) = d)
    (hr : (Ctl.pending c (.equal a b)).resume matchTests d = c')
    (h : iterStep n { v with ctl := c' } = w) :
    iterStep (n + 1) v = w := by
  simp only [iterStep, step_equal hv, Option.bind_some, hd, hr]
  exact h

theorem run_symbols {a b : String} {d : Bool} (hv : v.ctl = .pending c (.symbols a b))
    (ha : v.inRange a) (hb : v.inRange b)
    (hd : decide (v.word[(v.pos a).toNat]? = v.word[(v.pos b).toNat]?) = d)
    (hr : (Ctl.pending c (.symbols a b)).resume matchTests d = c')
    (h : iterStep n { v with ctl := c' } = w) :
    iterStep (n + 1) v = w := by
  simp only [iterStep, step_symbols hv ha hb, Option.bind_some, hd, hr]
  exact h

end Run

theorem iter_zero_eq {v : HVM} {c : Ctl} {π π' : String → ℤ} (h : π = π') :
    iterStep 0 { v with ctl := c, pos := π } = some { v with ctl := c, pos := π' } := by
  subst h; rfl

/-- A child's counted run, placed inside its caller `f`: the caller resumes with the value. -/
theorem run_child (f : Frame) (vc : HVM) (cs : Config) (e : Event) (hvc : vc.ctl = .pending cs e)
    (hcs : cs ≠ []) (n : ℕ) (val : Value) (π : String → ℤ)
    (hrun : iterStep n vc = some { vc with ctl := .returned val, pos := π }) (c' : Ctl)
    (hc' : liftCtl f (.returned val) = c') :
    iterStep n { vc with ctl := .pending (f :: cs) e } = some { vc with ctl := c', pos := π } := by
  have hl := iterStep_lift f n vc _ (by simp only [hvc, NonEmptyCtl]; exact hcs) hrun
  have e1 : liftVM f vc = { vc with ctl := .pending (f :: cs) e } := by
    simp only [liftVM, hvc, liftCtl]
  have e2 : liftVM f { vc with ctl := .returned val, pos := π } = { vc with ctl := c', pos := π } := by
    show { vc with ctl := liftCtl f (.returned val), pos := π } = _
    rw [hc']
  rw [e1, e2] at hl
  exact hl

/-- `run_child`, for a caller state whose chain already holds the child. -/
theorem run_child' (f : Frame) (v : HVM) (cs : Config) (e : Event)
    (hv : v.ctl = .pending (f :: cs) e) (hcs : cs ≠ []) (n : ℕ) (val : Value) (π : String → ℤ)
    (hrun : iterStep n { v with ctl := .pending cs e } =
      some { v with ctl := .returned val, pos := π }) (c' : Ctl)
    (hc' : liftCtl f (.returned val) = c') :
    iterStep n v = some { v with ctl := c', pos := π } := by
  have h1 : iterStep n { v with ctl := .pending (f :: cs) e } = some { v with ctl := c', pos := π } :=
    run_child f { v with ctl := .pending cs e } cs e rfl hcs n val π hrun c' hc'
  have e1 : { v with ctl := Ctl.pending (f :: cs) e } = v := by rw [← hv]
  rwa [e1] at h1

theorem iter_seq {v w : HVM} {m n : ℕ} {r : Option HVM} (h1 : iterStep m v = some w)
    (h2 : iterStep n w = r) : iterStep (m + n) v = r := by
  rw [iterStep_add, h1, Option.bind_some, h2]

/-- The word read at `Cut + i`, inside `x`. -/
theorem word_get (x rest : List (Fin 2)) (s i : ℕ) (h : s + i < x.length) (z : ℤ)
    (hz : z = (s : ℤ) + i) : (x ++ rest)[z.toNat]? = (x.drop s)[i]? := by
  subst hz
  rw [show ((s : ℤ) + i).toNat = s + i by omega, List.getElem?_append_left h, List.getElem?_drop]

theorem sym_decide (x rest : List (Fin 2)) (s i j : ℕ) (hi : s + i < x.length)
    (hj : s + j < x.length) (za zb : ℤ) (ha : za = (s : ℤ) + i) (hb : zb = (s : ℤ) + j) :
    decide ((x ++ rest)[za.toNat]? = (x ++ rest)[zb.toNat]?) =
      decide ((x.drop s)[i]? = (x.drop s)[j]?) := by
  rw [word_get x rest s i hi za ha, word_get x rest s j hj zb hb]

theorem div_succ_le (q k : ℕ) (hk : 2 ≤ k) (hq : 1 ≤ q) : q / k + 1 ≤ q := by
  have h1 : q / k ≤ q / 2 := Nat.div_le_div_left hk (by omega)
  omega

/-! ## `ResetShift k false` -/

/-- The non-searching shift: `P + 1`, `KP + k`. -/
def rsShiftF (k : ℕ) : Event := mv [("P", 1), ("KP", (k : ℤ))]

/-- The non-searching rewind: `A − 1`. -/
def rsBackF : Event := mv [("A", -1)]

/-- Loop head of `ResetShift k false`. -/
def rsLoopF (k ph : ℕ) (ne : Bool) : Ctl :=
  .pending [.resetShift k false ph (some ne) 2] (.equal "A" "Cut")

/-- Heads after rewinding `j` cells with `s` shifts (before the final `B := P`). -/
def rsPosF (k : ℕ) (π : String → ℤ) (j s : ℤ) : String → ℤ := fun h =>
  if h = "A" then π "A" - j
  else if h = "P" then π "P" + s
  else if h = "KP" then π "KP" + k * s
  else π h

theorem rsPosF_zero (k : ℕ) (π : String → ℤ) : rsPosF k π 0 0 = π := by
  funext h; simp only [rsPosF]; split_ifs <;> simp_all

theorem rsF_start (k : ℕ) :
    Ctl.ofOutcome (next [.resetShift k false 0 none 0] none) =
      .pending [.resetShift k false 0 none 1] (.equal "A" "Cut") := rfl

theorem rsF_first (k : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.resetShift k false 0 none 1] (.equal "A" "Cut")) :
    iterStep 1 v = some { v with ctl := rsLoopF k 0 (decide (v.pos "A" ≠ v.pos "Cut")) } := by
  simp only [iterStep, step_equal hv, Option.bind_some]
  congr 2
  by_cases h : v.pos "A" = v.pos "Cut" <;> simp [h, rsLoopF] <;> rfl

theorem rsF_resume_back (k ph : ℕ) (ne : Bool) :
    (rsLoopF k ph ne).resume matchTests false =
      .pending [.resetShift k false ph (some ne) 4] rsBackF := rfl

theorem rsF_resume_step (k ph : ℕ) (ne : Bool) (hph : ph + 1 < k) :
    (Ctl.pending [.resetShift k false ph (some ne) 4] rsBackF).resume matchTests false =
      rsLoopF k (ph + 1) ne := by
  have h : (ph + 1 == k) = false := by simp; omega
  have hs : stepFrame (.resetShift k false ph (some ne) 4) none =
      some (.emit (.equal "A" "Cut") (.resetShift k false (ph + 1) (some ne) 2)) := by
    simp only [stepFrame, stepResetShift, h]; rfl
  show Ctl.ofOutcome (next _ none) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rsF_resume_wrap (k ph : ℕ) (ne : Bool) (hph : ph + 1 = k) :
    (Ctl.pending [.resetShift k false ph (some ne) 4] rsBackF).resume matchTests false =
      .pending [.resetShift k false (ph + 1) (some ne) 6] (rsShiftF k) := by
  have h : (ph + 1 == k) = true := by simp; omega
  have hs : stepFrame (.resetShift k false ph (some ne) 4) none =
      some (.emit (rsShiftF k) (.resetShift k false (ph + 1) (some ne) 6)) := by
    simp only [stepFrame, stepResetShift, h]; rfl
  show Ctl.ofOutcome (next _ none) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rsF_resume_after_wrap (k ph : ℕ) (ne : Bool) :
    (Ctl.pending [.resetShift k false ph (some ne) 6] (rsShiftF k)).resume matchTests false =
      rsLoopF k 0 ne := rfl

theorem rsF_resume_exit_shift (k ph : ℕ) (ne : Bool) (h : (!ne || ph != 0) = true) :
    (rsLoopF k ph ne).resume matchTests true =
      .pending [.resetShift k false ph (some ne) 8] (rsShiftF k) := by
  have hs : stepFrame (.resetShift k false ph (some ne) 2) (some true) =
      some (.emit (rsShiftF k) (.resetShift k false ph (some ne) 8)) := by
    simp [stepFrame, stepResetShift, rsShiftF]
    cases ne <;> simp_all
  show Ctl.ofOutcome (next _ (some true)) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rsF_resume_exit_tail (k ph : ℕ) (ne : Bool) (h : (!ne || ph != 0) = false) :
    (rsLoopF k ph ne).resume matchTests true =
      .pending [.resetShift k false ph (some ne) 9] (.copy "B" "P") := by
  have hs : stepFrame (.resetShift k false ph (some ne) 2) (some true) =
      some (.emit (.copy "B" "P") (.resetShift k false ph (some ne) 9)) := by
    simp [stepFrame, stepResetShift]
    cases ne <;> simp_all
  show Ctl.ofOutcome (next _ (some true)) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rsF_resume_after_exit (k ph : ℕ) (ne : Bool) :
    (Ctl.pending [.resetShift k false ph (some ne) 8] (rsShiftF k)).resume matchTests false =
      .pending [.resetShift k false ph (some ne) 9] (.copy "B" "P") := rfl

theorem rsF_resume_done (k ph : ℕ) (ne : Bool) :
    (Ctl.pending [.resetShift k false ph (some ne) 9] (.copy "B" "P")).resume matchTests false =
      .returned none := rfl

theorem rsF_move_back (k : ℕ) (π : String → ℤ) (j s L : ℤ)
    (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ L) :
    moveSeq blind L [⟨"A", -1⟩] (rsPosF k π j s) = some (rsPosF k π (j + 1) s) := by
  rw [moveSeq_cons_ok _ _ _ _ _ (fun _ => by simp only [rsPosF, if_pos]; constructor <;> omega),
    moveSeq_nil]
  congr 1
  funext h
  by_cases h1 : h = "A"
  · subst h1; simp [rsPosF]; ring
  · simp only [Function.update_of_ne h1, rsPosF, if_neg h1]

theorem rsF_move_shift (k : ℕ) (π : String → ℤ) (j s L : ℤ)
    (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ L) :
    moveSeq blind L [⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩] (rsPosF k π j s) =
      some (rsPosF k π j (s + 1)) := by
  rw [moveSeq_cons_ok _ _ _ _ _ (fun _ => by simp [rsPosF]; constructor <;> omega),
    moveSeq_cons_ok _ _ _ _ _ (fun hb => absurd (by simp [blind]) hb), moveSeq_nil]
  congr 1
  funext h
  by_cases h1 : h = "KP"
  · subst h1; simp [rsPosF]; ring
  · by_cases h2 : h = "P"
    · subst h2; simp [rsPosF]; ring
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2, rsPosF, if_neg h1, if_neg h2]

theorem rsPosF_P (k : ℕ) (π : String → ℤ) (j s : ℤ) : rsPosF k π j s "P" = π "P" + s := by
  simp [rsPosF]

theorem rsPosF_A (k : ℕ) (π : String → ℤ) (j s : ℤ) : rsPosF k π j s "A" = π "A" - j := by
  simp [rsPosF]

theorem rsPosF_KP (k : ℕ) (π : String → ℤ) (j s : ℤ) : rsPosF k π j s "KP" = π "KP" + k * s := by
  simp [rsPosF]

theorem rsPosF_other (k : ℕ) (π : String → ℤ) (j s : ℤ) (h : String) (h1 : h ≠ "A") (h2 : h ≠ "P")
    (h3 : h ≠ "KP") : rsPosF k π j s h = π h := by
  simp [rsPosF, h1, h2, h3]

theorem rsF_iter (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 < k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len) :
    iterStep 2 v = some { v with ctl := rsLoopF k (ph + 1) ne, pos := rsPosF k π (j + 1) s } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPosF, hne]
  refine run_equal hv hd (rsF_resume_back k ph ne) ?_
  refine run_move (ms := [⟨"A", -1⟩]) (π := rsPosF k π (j + 1) s) rfl ?_
    (rsF_resume_step k ph ne hph) ?_
  · show moveSeq blind v.len _ v.pos = _
    rw [hp]; exact rsF_move_back k π j s _ hA
  rfl

theorem rsF_wrap (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 = k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len) :
    iterStep 3 v = some { v with ctl := rsLoopF k 0 ne, pos := rsPosF k π (j + 1) (s + 1) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPosF, hne]
  refine run_equal hv hd (rsF_resume_back k ph ne) ?_
  refine run_move (ms := [⟨"A", -1⟩]) (π := rsPosF k π (j + 1) s) rfl ?_
    (rsF_resume_wrap k ph ne hph) ?_
  · show moveSeq blind v.len _ v.pos = _
    rw [hp]; exact rsF_move_back k π j s _ hA
  refine run_move (ms := [⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩]) (π := rsPosF k π (j + 1) (s + 1)) rfl ?_
    (rsF_resume_after_wrap k (ph + 1) ne) ?_
  · show moveSeq blind v.len _ (rsPosF k π (j + 1) s) = _
    exact rsF_move_shift k π (j + 1) s _ hP
  rfl

theorem rsF_exit_shift (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = true) (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len) :
    iterStep 3 v = some { v with
      ctl := .returned none
      pos := Function.update (rsPosF k π j (s + 1)) "B" (π "P" + (s + 1)) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPosF, he]
  refine run_equal hv hd (rsF_resume_exit_shift k ph ne h) ?_
  refine run_move (ms := [⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩]) (π := rsPosF k π j (s + 1)) rfl ?_
    (rsF_resume_after_exit k ph ne) ?_
  · show moveSeq blind v.len _ v.pos = _
    rw [hp]; exact rsF_move_shift k π j s _ hP
  refine run_copy rfl (rsF_resume_done k ph ne) ?_
  refine iter_zero_eq ?_
  simp only [rsPosF_P]

theorem rsF_exit_tail (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = false) :
    iterStep 2 v = some { v with
      ctl := .returned none
      pos := Function.update (rsPosF k π j s) "B" (π "P" + s) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPosF, he]
  refine run_equal hv hd (rsF_resume_exit_tail k ph ne h) ?_
  refine run_copy rfl (rsF_resume_done k ph ne) ?_
  refine iter_zero_eq ?_
  simp only [hp, rsPosF_P]

theorem rsF_loop_run (k : ℕ) (hk : 1 ≤ k) (π : String → ℤ) (L : ℤ) (ne : Bool) (q : ℕ)
    (hne : ne = decide (q ≠ 0)) :
    ∀ (m : ℕ) (v : HVM) (j sh : ℕ), j + m = q → sh = j / k → v.ctl = rsLoopF k (j % k) ne →
      v.pos = rsPosF k π j sh → v.len = L →
      π "A" - q = π "Cut" → 0 ≤ π "Cut" → π "A" - j ≤ L → 0 ≤ π "P" →
      π "P" + (q / k : ℕ) + 1 ≤ L →
      ∃ n, n ≤ 3 * m + 3 ∧
        iterStep n v = some { v with
          ctl := .returned none
          pos := Function.update (rsPosF k π q (rsShifts k q : ℕ)) "B"
            (π "P" + (rsShifts k q : ℕ)) }
  | 0, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hP0, hPL => by
    have hj : j = q := by omega
    subst hj
    have hshq : sh = j / k := hsh
    by_cases hx : (!ne || j % k != 0) = true
    · refine ⟨3, by omega, ?_⟩
      rw [rsF_exit_shift k (j % k) ne v π j sh hv hp (by omega) hx
        ⟨by positivity, by rw [hshq]; omega⟩]
      have : (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx; simp at hx
        rcases hx with h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
      simp only [rsShifts, if_pos this, hshq, Nat.cast_add, Nat.cast_one]
    · refine ⟨2, by omega, ?_⟩
      have hx' : (!ne || j % k != 0) = false := by simpa using hx
      rw [rsF_exit_tail k (j % k) ne v π j sh hv hp (by omega) hx']
      have : ¬ (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx'; simp at hx'; omega
      simp only [rsShifts, if_neg this, Nat.add_zero, ← hshq]
  | m + 1, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hP0, hPL => by
    obtain ⟨hs1, hs2⟩ := modstep j k hk
    have hjq : sh ≤ q / k := by rw [hsh]; exact Nat.div_le_div_right (by omega)
    rcases Nat.lt_or_ge (j % k + 1) k with hph | hph
    · obtain ⟨hm1, hd1⟩ := hs1 hph
      have hstep := rsF_iter k (j % k) ne v π j sh hv hp (by omega) hph ⟨by omega, by omega⟩
      obtain ⟨n, hn, hrun⟩ := rsF_loop_run k hk π L ne q hne m
        { v with ctl := rsLoopF k (j % k + 1) ne, pos := rsPosF k π (↑j + 1) sh } (j + 1) sh
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hP0 hPL
      refine ⟨2 + n, by omega, ?_⟩
      rw [iterStep_add, hstep, Option.bind_some, hrun]
    · have hph' : j % k + 1 = k := by have := Nat.mod_lt j (show 0 < k by omega); omega
      obtain ⟨hm1, hd1⟩ := hs2 hph'
      have hj1 : sh + 1 ≤ q / k := by
        rw [hsh, ← hd1]; exact Nat.div_le_div_right (by omega)
      have hstep := rsF_wrap k (j % k) ne v π j sh hv hp (by omega) hph'
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      obtain ⟨n, hn, hrun⟩ := rsF_loop_run k hk π L ne q hne m
        { v with ctl := rsLoopF k 0 ne, pos := rsPosF k π (↑j + 1) (↑sh + 1) } (j + 1) (sh + 1)
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hP0 hPL
      refine ⟨3 + n, by omega, ?_⟩
      rw [iterStep_add, hstep, Option.bind_some, hrun]

/-- **`ResetShift k false`, from its fresh frame**: rewinding `q = A − Cut` cells, it returns
within `3q + 4` steps with `A = Cut`, `P + t`, `KP + k·t`, `B = P`, `t = max 1 ⌈q/k⌉`. -/
theorem resetShiftF_run (k : ℕ) (hk : 1 ≤ k) (v : HVM) (q : ℕ)
    (hv : v.ctl = .pending [.resetShift k false 0 none 1] (.equal "A" "Cut"))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hP0 : 0 ≤ v.pos "P") (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n, n ≤ 3 * q + 4 ∧
      iterStep n v = some { v with
        ctl := .returned none
        pos := Function.update (rsPosF k v.pos q (rsShifts k q : ℕ)) "B"
          (v.pos "P" + (rsShifts k q : ℕ)) } := by
  have h1 := rsF_first k v hv
  have hne : decide (v.pos "A" ≠ v.pos "Cut") = decide (q ≠ 0) := by
    simp only [decide_eq_decide]; omega
  rw [hne] at h1
  obtain ⟨n, hn, hrun⟩ := rsF_loop_run k hk v.pos v.len (decide (q ≠ 0)) q rfl q
    { v with ctl := rsLoopF k 0 (decide (q ≠ 0)) } 0 0 (by omega) (by simp) (by simp)
    (by simp [rsPosF_zero]) rfl (by omega) hC (by simp; omega) hP0 hPL
  refine ⟨1 + n, by omega, ?_⟩
  rw [iterStep_add, h1, Option.bind_some, hrun]

/-! ## `PeriodShift k false` -/

/-- Loop head of `PeriodShift k false`. -/
def psLoopF (k : ℕ) : Ctl := .pending [.periodShift k false 2] (.less "Walk" "First")

/-- The move of one non-searching `PeriodShift` iteration. -/
def psMoveF (k : ℕ) : Event := mv [("Walk", 1), ("A", -1), ("P", 1), ("KP", (k : ℤ))]

/-- Heads after `i` iterations of the `PeriodShift k false` loop. -/
def psPosF (k : ℕ) (π : String → ℤ) (i : ℤ) : String → ℤ := fun h =>
  if h = "Walk" then π "Cut" + i
  else if h = "A" then π "A" - i
  else if h = "P" then π "P" + i
  else if h = "KP" then π "KP" + k * i
  else π h

theorem psF_start (k : ℕ) :
    Ctl.ofOutcome (next [.periodShift k false 0] none) =
      .pending [.periodShift k false 1] (.copy "Walk" "Cut") := rfl

theorem psF_resume_start (k : ℕ) :
    (Ctl.pending [.periodShift k false 1] (.copy "Walk" "Cut")).resume matchTests false =
      psLoopF k := rfl

theorem psF_resume_go (k : ℕ) :
    (psLoopF k).resume matchTests true = .pending [.periodShift k false 4] (psMoveF k) := rfl

theorem psF_resume_stop (k : ℕ) : (psLoopF k).resume matchTests false = .returned none := rfl

theorem psF_resume_moved (k : ℕ) :
    (Ctl.pending [.periodShift k false 4] (psMoveF k)).resume matchTests false = psLoopF k := rfl

theorem psF_move (k : ℕ) (π : String → ℤ) (i L : ℤ)
    (hW : 0 ≤ π "Cut" + i + 1 ∧ π "Cut" + i + 1 ≤ L)
    (hA : 0 ≤ π "A" - i - 1 ∧ π "A" - i - 1 ≤ L)
    (hP : 0 ≤ π "P" + i + 1 ∧ π "P" + i + 1 ≤ L) :
    moveSeq blind L [⟨"Walk", 1⟩, ⟨"A", -1⟩, ⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩] (psPosF k π i) =
      some (psPosF k π (i + 1)) := by
  rw [moveSeq_cons_ok _ _ _ _ _ (fun _ => by simp [psPosF]; constructor <;> omega),
    moveSeq_cons_ok _ _ _ _ _ (fun _ => by simp [psPosF]; constructor <;> omega),
    moveSeq_cons_ok _ _ _ _ _ (fun _ => by simp [psPosF]; constructor <;> omega),
    moveSeq_cons_ok _ _ _ _ _ (fun hb => absurd (by simp [blind]) hb), moveSeq_nil]
  congr 1
  funext h
  by_cases h1 : h = "KP" <;> by_cases h2 : h = "P" <;> by_cases h3 : h = "A" <;>
    by_cases h4 : h = "Walk" <;> simp_all [psPosF] <;> ring

theorem psF_loop_run (k : ℕ) (π : String → ℤ) (L : ℤ) :
    ∀ (m : ℕ) (v : HVM) (i : ℤ), v.ctl = psLoopF k → v.pos = psPosF k π i → v.len = L →
      π "Cut" + i + m = π "First" → 0 ≤ π "Cut" + i → π "First" ≤ L →
      0 ≤ π "A" - (i + m) → π "A" - i ≤ L → 0 ≤ π "P" + i → π "P" + i + m ≤ L →
      iterStep (2 * m + 1) v = some { v with ctl := .returned none, pos := psPosF k π (i + m) }
  | 0, v, i, hv, hp, _, he, _, _, _, _, _, _ => by
    have hW : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPosF]
    have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPosF]
    refine run_less hv (d := false) (by simp; omega) (psF_resume_stop k) ?_
    refine iter_zero_eq ?_
    simp [hp]
  | m + 1, v, i, hv, hp, hL, he, h1, h2, h3, h4, h5, h6 => by
    have hW : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPosF]
    have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPosF]
    have hrec := psF_loop_run k π L m { v with ctl := psLoopF k, pos := psPosF k π (i + 1) } (i + 1)
      rfl rfl hL (by push_cast at he; omega) (by omega) h2 (by push_cast at h3; omega) (by omega)
      (by omega) (by push_cast at h6; omega)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring]
    refine run_less hv (d := true) (by simp; omega) (psF_resume_go k) ?_
    refine run_move (ms := [⟨"Walk", 1⟩, ⟨"A", -1⟩, ⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩])
      (π := psPosF k π (i + 1)) rfl ?_ (psF_resume_moved k) ?_
    · show moveSeq blind v.len _ v.pos = _
      rw [hp]
      exact psF_move k π i _ ⟨by omega, by omega⟩ ⟨by push_cast at h3; omega, by omega⟩
        ⟨by omega, by push_cast at h6; omega⟩
    rw [show ((i + (m + 1 : ℕ)) : ℤ) = i + 1 + m by push_cast; ring]
    exact hrec

theorem psPosF_zero (k : ℕ) (π : String → ℤ) : psPosF k π 0 = Function.update π "Walk" (π "Cut") := by
  funext h
  by_cases h1 : h = "Walk"
  · subst h1; simp [psPosF]
  · simp only [psPosF, Function.update_of_ne h1, if_neg h1]; split_ifs <;> simp_all

/-- **`PeriodShift k false`, from its fresh frame**: after `2t + 2` steps, `t = First − Cut`, it
returns with `Walk = First`, `A − t`, `P + t`, `KP + k·t`. -/
theorem periodShiftF_run (k : ℕ) (v : HVM) (t : ℕ)
    (hv : v.ctl = .pending [.periodShift k false 1] (.copy "Walk" "Cut"))
    (ht : v.pos "Cut" + t = v.pos "First") (h0 : 0 ≤ v.pos "Cut") (hF : v.pos "First" ≤ v.len)
    (hA : t ≤ v.pos "A") (hA' : v.pos "A" ≤ v.len) (hP : 0 ≤ v.pos "P")
    (hP' : v.pos "P" + t ≤ v.len) :
    iterStep (2 * t + 2) v = some { v with ctl := .returned none, pos := psPosF k v.pos t } := by
  rw [show 2 * t + 2 = (2 * t + 1) + 1 by ring]
  refine run_copy hv (psF_resume_start k) ?_
  have := psF_loop_run k v.pos v.len t { v with ctl := psLoopF k, pos := psPosF k v.pos 0 } 0 rfl
    rfl rfl (by omega) (by omega) hF (by omega) (by omega) (by omega) (by omega)
  rw [psPosF_zero] at this
  simpa using this

/-! ## `Initialize k` -/

/-- Heads after `Initialize`: `A = Cut`, `P = B = Cut + 1`, `KP = Cut + k`. -/
def initPos (k : ℕ) (π : String → ℤ) : String → ℤ := fun h =>
  if h = "A" then π "Cut"
  else if h = "P" then π "Cut" + 1
  else if h = "B" then π "Cut" + 1
  else if h = "KP" then π "Cut" + k
  else π h

theorem init_run (k : ℕ) (v : HVM) (hv : v.ctl = .pending [.initialize k 1] (.copy "A" "Cut"))
    (hC : 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len) :
    iterStep 6 v = some { v with ctl := .returned none, pos := initPos k v.pos } := by
  refine run_copy hv (c' := .pending [.initialize k 2] (.copy "P" "Cut")) rfl ?_
  refine run_copy rfl (c' := .pending [.initialize k 3] (mv [("P", 1)])) rfl ?_
  refine run_move1 rfl (fun _ => by simp only [HVM.len] at hC ⊢; simp; constructor <;> omega)
    (c' := .pending [.initialize k 4] (.copy "B" "P")) rfl ?_
  refine run_copy rfl (c' := .pending [.initialize k 5] (.copy "KP" "Cut")) rfl ?_
  refine run_copy rfl (c' := .pending [.initialize k 6] (mv [("KP", (k : ℤ))])) rfl ?_
  refine run_move1 rfl (fun hb => absurd (by simp [blind]) hb) (c' := .returned none) rfl ?_
  refine iter_zero_eq ?_
  funext h
  by_cases h1 : h = "A" <;> by_cases h2 : h = "P" <;> by_cases h3 : h = "B" <;>
    by_cases h4 : h = "KP" <;> simp_all [initPos]

/-! ## The scan state `(p, q)` at `Cut = s` -/

/-- Heads `First` may move. -/
def fHeads : List String := ["A", "P", "B", "KP"]

/-- Heads `Second` may move. -/
def sHeads : List String := ["A", "P", "B", "KP", "Walk"]

/-- Heads `Decompose` may move. -/
def dHeads : List String :=
  ["Cut", "A", "P", "B", "KP", "First", "KFirst", "Reach", "Second", "Walk"]

/-- The scan state `(p, q)` at `Cut = s`: `A = s + q`, `P = s + p`, `B = s + p + q`,
`KP = s + k·p`; only the heads of `S` differ from `π0`. -/
def HRel (S : List String) (k s p q : ℕ) (π0 π : String → ℤ) : Prop :=
  π "A" = (s : ℤ) + q ∧ π "P" = (s : ℤ) + p ∧ π "B" = (s : ℤ) + p + q ∧
    π "KP" = (s : ℤ) + (k : ℤ) * p ∧ Keeps S π0 π

theorem hrel_init {S : List String} (hA : "A" ∈ S) (hP : "P" ∈ S) (hB : "B" ∈ S)
    (hK : "KP" ∈ S) (k s : ℕ) (π0 : String → ℤ) (hs : π0 "Cut" = s) :
    HRel S k s 1 0 π0 (initPos k π0) := by
  refine ⟨by simp [initPos, hs], by simp [initPos, hs], by simp [initPos, hs],
    by simp [initPos, hs], ?_⟩
  intro h hh
  have h1 : h ≠ "A" := fun e => hh (e ▸ hA)
  have h2 : h ≠ "P" := fun e => hh (e ▸ hP)
  have h3 : h ≠ "B" := fun e => hh (e ▸ hB)
  have h4 : h ≠ "KP" := fun e => hh (e ▸ hK)
  simp [initPos, h1, h2, h3, h4]

theorem hrel_AB {S : List String} {k s p q : ℕ} {π0 π : String → ℤ} (h : HRel S k s p q π0 π)
    (hAS : "A" ∈ S) (hBS : "B" ∈ S) :
    HRel S k s p (q + 1) π0
      (Function.update (Function.update π "A" (π "A" + 1)) "B" (π "B" + 1)) := by
  obtain ⟨hA, hP, hB, hK, hkeep⟩ := h
  refine ⟨by simp [hA]; ring, by simp [hP], by simp [hB]; ring, by simp [hK],
    keeps_update hBS _ (keeps_update hAS _ hkeep)⟩

theorem keeps_rsPosF {S : List String} (hA : "A" ∈ S) (hP : "P" ∈ S) (hK : "KP" ∈ S) (k : ℕ)
    {π0 π : String → ℤ} (j t : ℤ) (h : Keeps S π0 π) : Keeps S π0 (rsPosF k π j t) := by
  intro h' hh'
  rw [rsPosF_other k π j t h' (fun e => hh' (e ▸ hA)) (fun e => hh' (e ▸ hP))
    (fun e => hh' (e ▸ hK))]
  exact h h' hh'

theorem hrel_reset {S : List String} (hA : "A" ∈ S) (hP : "P" ∈ S) (hB : "B" ∈ S)
    (hK : "KP" ∈ S) {k s p q : ℕ} {π0 π : String → ℤ} (h : HRel S k s p q π0 π) (t : ℕ) :
    HRel S k s (p + t) 0 π0 (Function.update (rsPosF k π q t) "B" (π "P" + t)) := by
  obtain ⟨hA', hP', hB', hK', hkeep⟩ := h
  refine ⟨by simp [rsPosF, hA'], by simp [rsPosF, hP']; ring, by simp [hP']; ring, ?_,
    keeps_update hB _ (keeps_rsPosF hA hP hK k _ _ hkeep)⟩
  simp [rsPosF, hK']; ring

/-! ## `First k bounded` -/

section FirstTrans
variable (k : ℕ) (b : Bool)

/-- After the `P < End` test succeeds: the bounded variant tests `P < Second` first. -/
def firstGo : Ctl :=
  if b then .pending [.first k true 3] (.less "P" "Second")
  else .pending [.first k false 4] (.less "B" "End")

theorem fr_init : liftCtl (.first k b 1) (.returned none) =
    .pending [.first k b 2] (.less "P" "End") := rfl
theorem fr2f : (Ctl.pending [.first k b 2] (.less "P" "End")).resume matchTests false =
    .returned (some false) := rfl
theorem fr2t : (Ctl.pending [.first k b 2] (.less "P" "End")).resume matchTests true =
    firstGo k b := by cases b <;> rfl
theorem fr2t_false : (Ctl.pending [.first k false 2] (.less "P" "End")).resume matchTests true =
    .pending [.first k false 4] (.less "B" "End") := rfl
theorem fr2t_true : (Ctl.pending [.first k true 2] (.less "P" "End")).resume matchTests true =
    .pending [.first k true 3] (.less "P" "Second") := rfl
theorem fr3f : (Ctl.pending [.first k true 3] (.less "P" "Second")).resume matchTests false =
    .returned (some false) := rfl
theorem fr3t : (Ctl.pending [.first k true 3] (.less "P" "Second")).resume matchTests true =
    .pending [.first k true 4] (.less "B" "End") := rfl
theorem fr4t : (Ctl.pending [.first k b 4] (.less "B" "End")).resume matchTests true =
    .pending [.first k b 5] (.less "B" "KP") := rfl
theorem fr4f : (Ctl.pending [.first k b 4] (.less "B" "End")).resume matchTests false =
    .pending [.first k b 8] (.equal "B" "KP") := rfl
theorem fr5t : (Ctl.pending [.first k b 5] (.less "B" "KP")).resume matchTests true =
    .pending [.first k b 6] (.symbols "A" "B") := rfl
theorem fr5f : (Ctl.pending [.first k b 5] (.less "B" "KP")).resume matchTests false =
    .pending [.first k b 8] (.equal "B" "KP") := rfl
theorem fr6t : (Ctl.pending [.first k b 6] (.symbols "A" "B")).resume matchTests true =
    .pending [.first k b 7] (mv [("A", 1), ("B", 1)]) := rfl
theorem fr6f : (Ctl.pending [.first k b 6] (.symbols "A" "B")).resume matchTests false =
    .pending [.first k b 8] (.equal "B" "KP") := rfl
theorem fr7 : (Ctl.pending [.first k b 7] (mv [("A", 1), ("B", 1)])).resume matchTests false =
    .pending [.first k b 4] (.less "B" "End") := rfl
theorem fr8t : (Ctl.pending [.first k b 8] (.equal "B" "KP")).resume matchTests true =
    .returned (some true) := rfl
theorem fr8f : (Ctl.pending [.first k b 8] (.equal "B" "KP")).resume matchTests false =
    .pending [.first k b 9, .resetShift k false 0 none 1] (.equal "A" "Cut") := rfl
theorem fr9 : liftCtl (.first k b 9) (.returned none) =
    .pending [.first k b 2] (.less "P" "End") := rfl

end FirstTrans

theorem nat_kp (k p : ℕ) (hk : 1 ≤ k) : (k - 1) * p + p = k * p := by
  rw [Nat.sub_one_mul]; have := Nat.le_mul_of_pos_left p (show 0 < k by omega); omega

/-- **`First`'s inner loop** (sites 4–7) computes `firstInner`, in fewer than `4·work` steps. -/
theorem first_inner (k : ℕ) (hk : 1 ≤ k) (b : Bool) (x rest : List (Fin 2)) (s p : ℕ)
    (π0 : String → ℤ) (hp : 0 < p) (hsx : s ≤ x.length) (hE : π0 "End" = x.length) :
    ∀ (fuel q : ℕ) (v : HVM), v.ctl = .pending [.first k b 4] (.less "B" "End") →
      v.word = x ++ rest → HRel fHeads k s p q π0 v.pos →
      p + q ≤ (x.drop s).length → (x.drop s).length ≤ fuel + q →
      ∃ n π', n + 1 ≤ 4 * firstInnerWork (x.drop s) k p fuel q ∧
        firstInner (x.drop s) k p fuel q + 1 ≤ firstInnerWork (x.drop s) k p fuel q + q ∧
        iterStep n v = some { v with
          ctl := .pending [.first k b 8] (.equal "B" "KP")
          pos := π' } ∧
        HRel fHeads k s p (firstInner (x.drop s) k p fuel q) π0 π' := by
  have hlen : (x.drop s).length = x.length - s := List.length_drop ..
  have hkp := nat_kp k p hk
  intro fuel
  induction fuel with
  | zero => intro q v _ _ _ hpq hf; omega
  | succ fuel ih =>
    intro q v hv hw hR hpq hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [fHeads])).trans hE
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases h1 : p + q < (x.drop s).length
    · by_cases h2 : q < (k - 1) * p
      · by_cases h3 : (x.drop s)[q]? = (x.drop s)[p + q]?
        · have hc : p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
              (x.drop s)[q]? = (x.drop s)[p + q]? := ⟨h1, h2, h3⟩
          obtain ⟨n, π', hn, hq', hrun, hR'⟩ := ih (q + 1)
            { v with
              ctl := .pending [.first k b 4] (.less "B" "End")
              pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
                (v.pos "B" + 1) }
            rfl hw (hrel_AB ⟨hA, hP, hB, hK, hkeep⟩ (by simp [fHeads]) (by simp [fHeads]))
            (by omega) (by omega)
          refine ⟨n + 1 + 1 + 1 + 1, π', ?_, ?_, ?_, ?_⟩
          · rw [firstInnerWork, if_pos hc]; omega
          · rw [firstInnerWork, if_pos hc, firstInner, if_pos hc]; omega
          · refine run_less hv (d := true) (by simp; omega) (fr4t k b) ?_
            refine run_less rfl (d := true) (by simp; omega) (fr5t k b) ?_
            refine run_symbols rfl (d := true) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
              (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (fr6t k b) ?_
            · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = true
              rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
                (by rw [hB]; push_cast; ring)]
              exact decide_eq_true h3
            refine run_moveAB rfl (show 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len by omega)
              (show 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len by omega) (fr7 k b) ?_
            exact hrun
          · rw [firstInner, if_pos hc]; exact hR'
        · have hc : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
              (x.drop s)[q]? = (x.drop s)[p + q]?) := fun h => h3 h.2.2
          refine ⟨1 + 1 + 1, v.pos, ?_, ?_, ?_, ?_⟩
          · rw [firstInnerWork, if_neg hc]; try omega
          · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]; try omega
          · refine run_less hv (d := true) (by simp; omega) (fr4t k b) ?_
            refine run_less rfl (d := true) (by simp; omega) (fr5t k b) ?_
            refine run_symbols rfl (d := false) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
              (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (fr6f k b) ?_
            · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = false
              rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
                (by rw [hB]; push_cast; ring)]
              exact decide_eq_false h3
            exact iter_zero_eq rfl
          · rw [firstInner, if_neg hc]; exact ⟨hA, hP, hB, hK, hkeep⟩
      · have hc : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
            (x.drop s)[q]? = (x.drop s)[p + q]?) := fun h => h2 h.2.1
        refine ⟨1 + 1, v.pos, ?_, ?_, ?_, ?_⟩
        · rw [firstInnerWork, if_neg hc]; try omega
        · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]; try omega
        · refine run_less hv (d := true) (by simp; omega) (fr4t k b) ?_
          refine run_less rfl (d := false) (by simp; omega) (fr5f k b) ?_
          exact iter_zero_eq rfl
        · rw [firstInner, if_neg hc]; exact ⟨hA, hP, hB, hK, hkeep⟩
    · have hc : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
          (x.drop s)[q]? = (x.drop s)[p + q]?) := fun h => h1 h.1
      refine ⟨1, v.pos, ?_, ?_, ?_, ?_⟩
      · rw [firstInnerWork, if_neg hc]; try omega
      · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]; try omega
      · refine run_less hv (d := false) (by simp; omega) (fr4f k b) ?_
        exact iter_zero_eq rfl
      · rw [firstInner, if_neg hc]; exact ⟨hA, hP, hB, hK, hkeep⟩

/-- Entering `First`'s inner loop from its outer head: one test, or two when bounded. -/
theorem first_enter (k : ℕ) (b : Bool) (v : HVM)
    (hv : v.ctl = .pending [.first k b 2] (.less "P" "End"))
    (h1 : v.pos "P" < v.pos "End") (h2 : b = true → v.pos "P" < v.pos "Second")
    (n : ℕ) (r : Option HVM)
    (h : iterStep n { v with ctl := .pending [.first k b 4] (.less "B" "End") } = r) :
    ∃ m, m ≤ 2 ∧ iterStep (n + m) v = r := by
  cases b with
  | false =>
    exact ⟨1, by omega, run_less hv (d := true) (by simp; omega) (fr2t_false k) h⟩
  | true =>
    refine ⟨2, le_refl _, ?_⟩
    show iterStep (n + 1 + 1) v = r
    refine run_less hv (d := true) (by simp; omega) (fr2t_true k) ?_
    exact run_less rfl (d := true) (by simp; exact h2 rfl) (fr3t k) h

/-- **`First`'s outer loop** (sites 2–9) computes `firstOuter`, in `10·work + 2` steps. -/
theorem first_outer (k : ℕ) (hk : 2 ≤ k) (b : Bool) (x rest : List (Fin 2)) (s bnd : ℕ)
    (π0 : String → ℤ) (hsx : s ≤ x.length) (hC : π0 "Cut" = s) (hE : π0 "End" = x.length)
    (hbT : b = true → π0 "Second" = (s : ℤ) + bnd)
    (hbF : b = false → (x.drop s).length ≤ bnd) :
    ∀ (fuel p : ℕ) (v : HVM), v.ctl = .pending [.first k b 2] (.less "P" "End") →
      v.word = x ++ rest → HRel fHeads k s p 0 π0 v.pos →
      0 < p → (x.drop s).length + 1 ≤ fuel + p →
      ∃ n π', n ≤ 10 * firstOuterWork (x.drop s) k bnd fuel p + 2 ∧
        iterStep n v = some { v with
          ctl := .returned (some (firstOuter (x.drop s) k bnd fuel p).isSome)
          pos := π' } ∧
        Keeps fHeads π0 π' ∧
        ∀ p₁ m, firstOuter (x.drop s) k bnd fuel p = some (p₁, m) →
          HRel fHeads k s p₁ ((k - 1) * p₁) π0 π' := by
  have hlen : (x.drop s).length = x.length - s := List.length_drop ..
  intro fuel
  induction fuel with
  | zero =>
    intro p v hv hw hR hp hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [fHeads])).trans hE
    refine ⟨1, v.pos, by simp [firstOuterWork], ?_, hkeep, by simp [firstOuter]⟩
    exact run_less hv (d := false) (by simp; omega) (fr2f k b) (iter_zero_eq rfl)
  | succ fuel ih =>
    intro p v hv hw hR hp hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [fHeads])).trans hE
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hg1 : p < (x.drop s).length
    · by_cases hg2 : p < bnd
      · have hg : p < (x.drop s).length ∧ p < bnd := ⟨hg1, hg2⟩
        obtain ⟨q', hq'⟩ : ∃ q', firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = q' :=
          ⟨_, rfl⟩
        have hqle := firstInner_le (x.drop s) k p ((x.drop s).length + 1) 0 (by omega)
        rw [hq'] at hqle
        obtain ⟨nin, πin, hnin, hqin, hrunin, hRin⟩ := first_inner k (by omega) b x rest s p π0 hp
          hsx hE ((x.drop s).length + 1) 0
          { v with ctl := .pending [.first k b 4] (.less "B" "End") } rfl hw
          ⟨hA, hP, hB, hK, hkeep⟩ (by omega) (by omega)
        rw [hq'] at hqin hRin
        have hkp := nat_kp k p (by omega)
        have hPS : b = true → v.pos "P" < v.pos "Second" := fun hb => by
          have h1 := hbT hb
          have h2 := hkeep "Second" (by simp [fHeads])
          omega
        obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hRin
        by_cases heq : q' = (k - 1) * p
        · have hfo : firstOuter (x.drop s) k bnd (fuel + 1) p = some (p, p + (k - 1) * p) := by
            rw [firstOuter, if_pos hg, hq', if_pos heq]
          have hwk : firstOuterWork (x.drop s) k bnd (fuel + 1) p =
              1 + firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 := by
            rw [firstOuterWork, if_pos hg, hq', if_pos heq, Nat.add_zero]
          have hC_ := iter_seq hrunin
            (run_equal rfl (d := true) (by simp; omega) (fr8t k b) (iter_zero_eq rfl))
          obtain ⟨m, hm, hD⟩ := first_enter k b v hv (by omega) hPS _ _ hC_
          refine ⟨nin + (0 + 1) + m, πin, ?_, ?_, hkeep2, ?_⟩
          · rw [hwk]; omega
          · rw [hfo]; exact hD
          · rw [hfo]
            rintro p₁ m' h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            rw [← heq]
            exact ⟨hA2, hP2, hB2, hK2, hkeep2⟩
        · have ht := rsShifts_eq k q' (by omega)
          have hfo : firstOuter (x.drop s) k bnd (fuel + 1) p =
              firstOuter (x.drop s) k bnd fuel (p + shiftNoPeriod q' k) := by
            rw [firstOuter, if_pos hg, hq', if_neg heq]
          have hwk : firstOuterWork (x.drop s) k bnd (fuel + 1) p =
              1 + firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 +
                firstOuterWork (x.drop s) k bnd fuel (p + shiftNoPeriod q' k) := by
            rw [firstOuterWork, if_pos hg, hq', if_neg heq]
          have hsp1 := shiftNoPeriod_pos q' k
          have hsmax := shiftNoPeriod_le_max q' k (by omega)
          have hdiv : p + q' / k + 1 ≤ (x.drop s).length := by
            rcases Nat.eq_zero_or_pos q' with h0 | h0
            · subst h0; simp; omega
            · have := div_succ_le q' k hk h0; omega
          obtain ⟨nrs, hnrs, hrs⟩ := resetShiftF_run k (by omega)
            { v with
              ctl := .pending [.resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin } q' rfl
            (by show πin "A" = πin "Cut" + q'
                have := hkeep2 "Cut" (by simp [fHeads]); omega)
            (by show 0 ≤ πin "Cut"; have := hkeep2 "Cut" (by simp [fHeads]); omega)
            (by show πin "A" ≤ v.len; omega) (by show 0 ≤ πin "P"; omega)
            (by show πin "P" + (q' / k : ℕ) + 1 ≤ v.len; omega)
          rw [ht] at hrs
          have hchild := run_child' (.first k b 9)
            { v with
              ctl := .pending [.first k b 9, .resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin }
            [.resetShift k false 0 none 1] (.equal "A" "Cut") rfl (by simp) nrs none
            (Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
              (πin "P" + (shiftNoPeriod q' k : ℕ))) hrs _ (fr9 k b)
          obtain ⟨nrec, πrec, hnrec, hrunrec, hkeeprec, hrelrec⟩ := ih (p + shiftNoPeriod q' k)
            { v with
              ctl := .pending [.first k b 2] (.less "P" "End")
              pos := Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
                (πin "P" + (shiftNoPeriod q' k : ℕ)) }
            rfl hw
            (hrel_reset (by simp [fHeads]) (by simp [fHeads]) (by simp [fHeads])
              (by simp [fHeads]) ⟨hA2, hP2, hB2, hK2, hkeep2⟩ _)
            (by omega) (by omega)
          have hA_ := iter_seq hchild hrunrec
          have hB_ := run_equal (v := { v with
              ctl := .pending [.first k b 8] (.equal "B" "KP")
              pos := πin }) rfl (d := false) (by simp; omega) (fr8f k b) hA_
          have hC_ := iter_seq hrunin hB_
          obtain ⟨m, hm, hD⟩ := first_enter k b v hv (by omega) hPS _ _ hC_
          refine ⟨nin + (nrs + nrec + 1) + m, πrec, ?_, ?_, hkeeprec, ?_⟩
          · rw [hwk]; omega
          · rw [hfo]; exact hD
          · rw [hfo]; exact hrelrec
      · obtain rfl : b = true := by
          cases b
          · exact absurd (hbF rfl) (by omega)
          · rfl
        have hng : ¬ (p < (x.drop s).length ∧ p < bnd) := fun h => hg2 h.2
        have hS : v.pos "Second" = (s : ℤ) + bnd := (hkeep "Second" (by simp [fHeads])).trans (hbT rfl)
        refine ⟨2, v.pos, by omega, ?_, hkeep, ?_⟩
        · rw [firstOuter, if_neg hng]
          show iterStep (0 + 1 + 1) v = _
          refine run_less hv (d := true) (by simp; omega) (fr2t_true k) ?_
          exact run_less rfl (d := false) (by simp; omega) (fr3f k) (iter_zero_eq rfl)
        · rw [firstOuter, if_neg hng]; simp
    · have hng : ¬ (p < (x.drop s).length ∧ p < bnd) := fun h => hg1 h.1
      refine ⟨1, v.pos, by omega, ?_, hkeep, ?_⟩
      · rw [firstOuter, if_neg hng]
        exact run_less hv (d := false) (by simp; omega) (fr2f k b) (iter_zero_eq rfl)
      · rw [firstOuter, if_neg hng]; simp

/-- **`First k bounded`, from its fresh frame**: it returns whether `firstOuter` finds a period
(`bnd` is `Second − Cut` when bounded, any bound `≥ |x| − s` otherwise), within
`10·firstOuterWork + 8` steps; when it finds `p₁`, `P = s + p₁`, `B = KP = s + k·p₁`. -/
theorem first_run (k : ℕ) (hk : 2 ≤ k) (b : Bool) (x rest : List (Fin 2)) (s bnd fuel : ℕ)
    (v : HVM) (hv : v.ctl = .pending [.first k b 1, .initialize k 1] (.copy "A" "Cut"))
    (hw : v.word = x ++ rest) (hC : v.pos "Cut" = s) (hE : v.pos "End" = x.length)
    (hsx : s ≤ x.length) (hs1 : (s : ℤ) + 1 ≤ v.len)
    (hbT : b = true → v.pos "Second" = (s : ℤ) + bnd)
    (hbF : b = false → (x.drop s).length ≤ bnd) (hf : (x.drop s).length ≤ fuel) :
    ∃ n π', n ≤ 10 * firstOuterWork (x.drop s) k bnd fuel 1 + 8 ∧
      iterStep n v = some { v with
        ctl := .returned (some (firstOuter (x.drop s) k bnd fuel 1).isSome)
        pos := π' } ∧
      Keeps fHeads v.pos π' ∧
      ∀ p₁ m, firstOuter (x.drop s) k bnd fuel 1 = some (p₁, m) →
        HRel fHeads k s p₁ ((k - 1) * p₁) v.pos π' := by
  have hinit := init_run k { v with ctl := .pending [.initialize k 1] (.copy "A" "Cut") } rfl
    (show 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len by omega)
  have hchild := run_child' (.first k b 1) v [.initialize k 1] (.copy "A" "Cut") hv (by simp) 6
    none (initPos k v.pos) hinit _ (fr_init k b)
  obtain ⟨n, π', hn, hrun, hkeep, hrel⟩ := first_outer k hk b x rest s bnd v.pos hsx hC hE hbT
    hbF fuel 1 { v with ctl := .pending [.first k b 2] (.less "P" "End"), pos := initPos k v.pos }
    rfl hw (hrel_init (by simp [fHeads]) (by simp [fHeads]) (by simp [fHeads]) (by simp [fHeads])
      k s v.pos hC) (by omega) (by omega)
  exact ⟨6 + n, π', by omega, iter_seq hchild hrun, hkeep, hrel⟩

/-! ## `Second k` -/

section SecondTrans
variable (k : ℕ)

theorem sr_init : liftCtl (.second k 1) (.returned none) =
    .pending [.second k 2] (.less "P" "End") := rfl
theorem sr2f : (Ctl.pending [.second k 2] (.less "P" "End")).resume matchTests false =
    .returned (some false) := rfl
theorem sr2t : (Ctl.pending [.second k 2] (.less "P" "End")).resume matchTests true =
    .pending [.second k 3] (.less "B" "End") := rfl
theorem sr3t : (Ctl.pending [.second k 3] (.less "B" "End")).resume matchTests true =
    .pending [.second k 4] (.symbols "A" "B") := rfl
theorem sr3f : (Ctl.pending [.second k 3] (.less "B" "End")).resume matchTests false =
    .pending [.second k 8] (.less "A" "KFirst") := rfl
theorem sr4t : (Ctl.pending [.second k 4] (.symbols "A" "B")).resume matchTests true =
    .pending [.second k 5] (mv [("A", 1), ("B", 1)]) := rfl
theorem sr4f : (Ctl.pending [.second k 4] (.symbols "A" "B")).resume matchTests false =
    .pending [.second k 8] (.less "A" "KFirst") := rfl
theorem sr5 : (Ctl.pending [.second k 5] (mv [("A", 1), ("B", 1)])).resume matchTests false =
    .pending [.second k 6] (.less "Reach" "B") := rfl
theorem sr6t : (Ctl.pending [.second k 6] (.less "Reach" "B")).resume matchTests true =
    .pending [.second k 7] (.less "B" "KP") := rfl
theorem sr6f : (Ctl.pending [.second k 6] (.less "Reach" "B")).resume matchTests false =
    .pending [.second k 3] (.less "B" "End") := rfl
theorem sr7t : (Ctl.pending [.second k 7] (.less "B" "KP")).resume matchTests true =
    .pending [.second k 3] (.less "B" "End") := rfl
theorem sr7f : (Ctl.pending [.second k 7] (.less "B" "KP")).resume matchTests false =
    .returned (some true) := rfl
theorem sr8t : (Ctl.pending [.second k 8] (.less "A" "KFirst")).resume matchTests true =
    .pending [.second k 11, .resetShift k false 0 none 1] (.equal "A" "Cut") := rfl
theorem sr8f : (Ctl.pending [.second k 8] (.less "A" "KFirst")).resume matchTests false =
    .pending [.second k 9] (.less "Reach" "A") := rfl
theorem sr9t : (Ctl.pending [.second k 9] (.less "Reach" "A")).resume matchTests true =
    .pending [.second k 11, .resetShift k false 0 none 1] (.equal "A" "Cut") := rfl
theorem sr9f : (Ctl.pending [.second k 9] (.less "Reach" "A")).resume matchTests false =
    .pending [.second k 10, .periodShift k false 1] (.copy "Walk" "Cut") := rfl
theorem sr10 : liftCtl (.second k 10) (.returned none) =
    .pending [.second k 2] (.less "P" "End") := rfl
theorem sr11 : liftCtl (.second k 11) (.returned none) =
    .pending [.second k 2] (.less "P" "End") := rfl

end SecondTrans

theorem keeps_psPosF {S : List String} (hW : "Walk" ∈ S) (hA : "A" ∈ S) (hP : "P" ∈ S)
    (hK : "KP" ∈ S) (k : ℕ) {π0 π : String → ℤ} (i : ℤ) (h : Keeps S π0 π) :
    Keeps S π0 (psPosF k π i) := by
  intro h' hh'
  have h1 : h' ≠ "Walk" := fun e => hh' (e ▸ hW)
  have h2 : h' ≠ "A" := fun e => hh' (e ▸ hA)
  have h3 : h' ≠ "P" := fun e => hh' (e ▸ hP)
  have h4 : h' ≠ "KP" := fun e => hh' (e ▸ hK)
  simp only [psPosF, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  exact h h' hh'

theorem hrel_period {k s p q p₁ : ℕ} {π0 π : String → ℤ} (h : HRel sHeads k s p q π0 π)
    (hle : p₁ ≤ q) :
    HRel sHeads k s (p + p₁) (q - p₁) π0 (psPosF k π p₁) := by
  obtain ⟨hA, hP, hB, hK, hkeep⟩ := h
  refine ⟨?_, ?_, ?_, ?_, keeps_psPosF (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads])
    (by simp [sHeads]) k _ hkeep⟩
  · simp [psPosF, hA]; omega
  · simp [psPosF, hP]; ring
  · simp [psPosF, hB]; omega
  · simp [psPosF, hK]; ring

/-- **`Second`'s inner loop** (sites 3–7) computes `secondInner`. -/
theorem second_inner (k : ℕ) (hk : 1 ≤ k) (x rest : List (Fin 2)) (s p r : ℕ)
    (π0 : String → ℤ) (hp : 0 < p) (hsx : s ≤ x.length) (hE : π0 "End" = x.length)
    (hR0 : π0 "Reach" = (s : ℤ) + r) :
    ∀ (fuel q : ℕ) (v : HVM), v.ctl = .pending [.second k 3] (.less "B" "End") →
      v.word = x ++ rest → HRel sHeads k s p q π0 v.pos →
      p + q ≤ (x.drop s).length → (x.drop s).length ≤ fuel + q →
      (∀ q', secondInner (x.drop s) k p r fuel q = some q' →
        ∃ n π', n + 3 ≤ 5 * secondInnerWork (x.drop s) k p r fuel q ∧
          q' + 1 ≤ secondInnerWork (x.drop s) k p r fuel q + q ∧
          iterStep n v = some { v with
            ctl := .pending [.second k 8] (.less "A" "KFirst")
            pos := π' } ∧
          HRel sHeads k s p q' π0 π') ∧
      (secondInner (x.drop s) k p r fuel q = none →
        ∃ n π', n ≤ 5 * secondInnerWork (x.drop s) k p r fuel q ∧
          iterStep n v = some { v with ctl := .returned (some true), pos := π' } ∧
          Keeps sHeads π0 π' ∧ π' "P" = (s : ℤ) + p) := by
  have hlen : (x.drop s).length = x.length - s := List.length_drop ..
  have hkp := nat_kp k p hk
  intro fuel
  induction fuel with
  | zero => intro q v _ _ _ hpq hf; omega
  | succ fuel ih =>
    intro q v hv hw hR hpq hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [sHeads])).trans hE
    have hR' : v.pos "Reach" = (s : ℤ) + r := (hkeep "Reach" (by simp [sHeads])).trans hR0
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hc : p + q < (x.drop s).length ∧ (x.drop s)[q]? = (x.drop s)[p + q]?
    · obtain ⟨h1, h3⟩ := hc
      -- the three steps to the `Reach < B` test
      have hpre : ∀ (n : ℕ) (rr : Option HVM),
          iterStep n { v with
            ctl := .pending [.second k 6] (.less "Reach" "B")
            pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
              (v.pos "B" + 1) } = rr →
          iterStep (n + 1 + 1 + 1) v = rr := by
        intro n rr h
        refine run_less hv (d := true) (by simp; omega) (sr3t k) ?_
        refine run_symbols rfl (d := true) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
          (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (sr4t k) ?_
        · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = true
          rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
            (by rw [hB]; push_cast; ring)]
          exact decide_eq_true h3
        refine run_moveAB rfl (show 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len by omega)
          (show 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len by omega) (sr5 k) ?_
        exact h
      have hR1 := hrel_AB ⟨hA, hP, hB, hK, hkeep⟩ (by simp [sHeads]) (by simp [sHeads])
      by_cases hfire : r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1
      · have hsi : secondInner (x.drop s) k p r (fuel + 1) q = none := by
          rw [secondInner, if_pos ⟨h1, h3⟩, if_pos hfire]
        have hwk : secondInnerWork (x.drop s) k p r (fuel + 1) q = 1 := by
          rw [secondInnerWork, if_pos ⟨h1, h3⟩, if_pos hfire]
        refine ⟨fun q' h => by rw [hsi] at h; exact absurd h (by simp), fun _ => ?_⟩
        refine ⟨0 + 1 + 1 + 1 + 1 + 1, _, by rw [hwk], ?_, hR1.2.2.2.2, by simp [hP]⟩
        refine hpre _ _ ?_
        refine run_less rfl (d := true) (by simp [hR', hB]; omega) (sr6t k) ?_
        refine run_less rfl (d := false) (by simp [hB, hK]; omega) (sr7f k) ?_
        exact iter_zero_eq rfl
      · have hsi : secondInner (x.drop s) k p r (fuel + 1) q =
            secondInner (x.drop s) k p r fuel (q + 1) := by
          rw [secondInner, if_pos ⟨h1, h3⟩, if_neg hfire]
        have hwk : secondInnerWork (x.drop s) k p r (fuel + 1) q =
            1 + secondInnerWork (x.drop s) k p r fuel (q + 1) := by
          rw [secondInnerWork, if_pos ⟨h1, h3⟩, if_neg hfire]
        -- back at the inner head with `q + 1`, after 4 or 5 steps
        have hback : ∀ (n : ℕ) (rr : Option HVM),
            iterStep n { v with
              ctl := .pending [.second k 3] (.less "B" "End")
              pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
                (v.pos "B" + 1) } = rr →
            ∃ m, m ≤ 5 ∧ iterStep (n + m) v = rr := by
          intro n rr h
          by_cases h6 : r < p + (q + 1)
          · have h7 : ¬ ((k - 1) * p ≤ q + 1) := fun h' => hfire ⟨h6, h'⟩
            refine ⟨5, le_refl _, ?_⟩
            show iterStep (n + 1 + 1 + 1 + 1 + 1) v = rr
            refine hpre _ _ ?_
            refine run_less rfl (d := true) (by simp [hR', hB]; omega) (sr6t k) ?_
            exact run_less rfl (d := true) (by simp [hB, hK]; omega) (sr7t k) h
          · refine ⟨4, by omega, ?_⟩
            show iterStep (n + 1 + 1 + 1 + 1) v = rr
            refine hpre _ _ ?_
            exact run_less rfl (d := false) (by simp [hR', hB]; omega) (sr6f k) h
        obtain ⟨ihs, ihn⟩ := ih (q + 1)
          { v with
            ctl := .pending [.second k 3] (.less "B" "End")
            pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
              (v.pos "B" + 1) }
          rfl hw hR1 (by omega) (by omega)
        refine ⟨fun q' h => ?_, fun h => ?_⟩
        · rw [hsi] at h
          obtain ⟨n, π', hn, hq', hrun, hR'⟩ := ihs q' h
          obtain ⟨m, hm, hrun'⟩ := hback _ _ hrun
          exact ⟨n + m, π', by rw [hwk]; omega, by rw [hwk]; omega, hrun', hR'⟩
        · rw [hsi] at h
          obtain ⟨n, π', hn, hrun, hkp', hP'⟩ := ihn h
          obtain ⟨m, hm, hrun'⟩ := hback _ _ hrun
          exact ⟨n + m, π', by rw [hwk]; omega, hrun', hkp', hP'⟩
    · have hsi : secondInner (x.drop s) k p r (fuel + 1) q = some q := by
        rw [secondInner, if_neg hc]
      have hwk : secondInnerWork (x.drop s) k p r (fuel + 1) q = 1 := by
        rw [secondInnerWork, if_neg hc]
      refine ⟨fun q' h => ?_, fun h => by rw [hsi] at h; exact absurd h (by simp)⟩
      rw [hsi] at h
      obtain rfl : q = q' := Option.some.inj h
      by_cases h1 : p + q < (x.drop s).length
      · have h3 : ¬ (x.drop s)[q]? = (x.drop s)[p + q]? := fun h' => hc ⟨h1, h'⟩
        refine ⟨0 + 1 + 1, v.pos, by rw [hwk], by rw [hwk]; omega, ?_,
          ⟨hA, hP, hB, hK, hkeep⟩⟩
        refine run_less hv (d := true) (by simp; omega) (sr3t k) ?_
        refine run_symbols rfl (d := false) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
          (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (sr4f k) ?_
        · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = false
          rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
            (by rw [hB]; push_cast; ring)]
          exact decide_eq_false h3
        exact iter_zero_eq rfl
      · refine ⟨0 + 1, v.pos, by rw [hwk]; omega, by rw [hwk]; omega, ?_, ⟨hA, hP, hB, hK, hkeep⟩⟩
        exact run_less hv (d := false) (by simp; omega) (sr3f k) (iter_zero_eq rfl)

/-- From `Second`'s decision point, the reset shift is chosen after one or two tests. -/
theorem second_to_reset (k : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.second k 8] (.less "A" "KFirst"))
    (hdec : v.pos "A" < v.pos "KFirst" ∨ v.pos "Reach" < v.pos "A") (n : ℕ) (rr : Option HVM)
    (h : iterStep n { v with
      ctl := .pending [.second k 11, .resetShift k false 0 none 1] (.equal "A" "Cut") } = rr) :
    ∃ m, m ≤ 2 ∧ iterStep (n + m) v = rr := by
  by_cases h1 : v.pos "A" < v.pos "KFirst"
  · exact ⟨1, by omega, run_less hv (d := true) (by simp; omega) (sr8t k) h⟩
  · have h2 : v.pos "Reach" < v.pos "A" := hdec.resolve_left h1
    refine ⟨2, le_refl _, ?_⟩
    show iterStep (n + 1 + 1) v = rr
    refine run_less hv (d := false) (by simp; omega) (sr8f k) ?_
    exact run_less rfl (d := true) (by simp; omega) (sr9t k) h

theorem so_bound_found (nin Win q : ℕ) (h : nin ≤ 5 * Win) :
    nin + 1 ≤ 8 * (1 + Win) + 3 * q + 1 := by omega

theorem so_bound_period (nin Win q q' p₁ nrec Wrec : ℕ) (h1 : nin + 3 ≤ 5 * Win)
    (h2 : q' + 1 ≤ Win + q) (h3 : nrec ≤ 8 * Wrec + 3 * (q' - p₁) + 1) (hp : p₁ ≤ q') :
    nin + (2 * p₁ + 2 + nrec + 1 + 1) + 1 ≤ 8 * (1 + Win + Wrec) + 3 * q + 1 := by omega

theorem so_bound_reset (nin Win q q' nrs nrec Wrec m : ℕ) (h1 : nin + 3 ≤ 5 * Win)
    (h2 : q' + 1 ≤ Win + q) (h3 : nrs ≤ 3 * q' + 4) (h4 : nrec ≤ 8 * Wrec + 3 * 0 + 1)
    (hm : m ≤ 2) : nin + (nrs + nrec + m) + 1 ≤ 8 * (1 + Win + Wrec) + 3 * q + 1 := by omega

set_option maxHeartbeats 1000000 in
/-- **`Second`'s outer loop** (sites 2–11) computes `secondOuter`; amortised with the potential
`3q`, it takes at most `8·work + 3q + 1` steps. -/
theorem second_outer (k : ℕ) (hk : 2 ≤ k) (x rest : List (Fin 2)) (s p₁ r : ℕ)
    (π0 : String → ℤ) (hsx : s ≤ x.length) (hC : π0 "Cut" = s) (hE : π0 "End" = x.length)
    (hF : π0 "First" = (s : ℤ) + p₁) (hKF : π0 "KFirst" = (s : ℤ) + (k : ℤ) * p₁)
    (hR0 : π0 "Reach" = (s : ℤ) + r) (hp₁ : 0 < p₁) :
    ∀ (fuel p q : ℕ) (v : HVM), v.ctl = .pending [.second k 2] (.less "P" "End") →
      v.word = x ++ rest → HRel sHeads k s p q π0 v.pos → 0 < p →
      (p < (x.drop s).length → p + q ≤ (x.drop s).length) →
      (x.drop s).length + 1 ≤ fuel + p →
      ∃ n π', n ≤ 8 * secondOuterWork (x.drop s) k p₁ r fuel p q + 3 * q + 1 ∧
        iterStep n v = some { v with
          ctl := .returned (some (secondOuter (x.drop s) k p₁ r fuel p q).isSome)
          pos := π' } ∧
        Keeps sHeads π0 π' ∧
        ∀ p₂, secondOuter (x.drop s) k p₁ r fuel p q = some p₂ → π' "P" = (s : ℤ) + p₂ := by
  have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
  intro fuel
  induction fuel with
  | zero =>
    intro p q v hv hw hR hp hinv hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [sHeads])).trans hE
    refine ⟨1, v.pos, by omega, ?_, hkeep, by simp [secondOuter]⟩
    exact run_less hv (d := false) (by simp; omega) (sr2f k) (iter_zero_eq rfl)
  | succ fuel ih =>
    intro p q v hv hw hR hp hinv hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [sHeads])).trans hE
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hg : p < (x.drop s).length
    · have hpq := hinv hg
      obtain ⟨ihs, ihn⟩ := second_inner k (by omega) x rest s p r π0 hp hsx hE hR0
        ((x.drop s).length + 1) q { v with ctl := .pending [.second k 3] (.less "B" "End") } rfl
        hw ⟨hA, hP, hB, hK, hkeep⟩ hpq (by omega)
      rcases hsi : secondInner (x.drop s) k p r ((x.drop s).length + 1) q with _ | q'
      · obtain ⟨nin, πin, hnin, hrunin, hkeepin, hPin⟩ := ihn hsi
        have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q = some p := by
          rw [secondOuter, if_pos hg]; simp only [hsi]
        have hwk : secondOuterWork (x.drop s) k p₁ r (fuel + 1) p q =
            1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q := by
          rw [secondOuterWork, if_pos hg]; simp only [hsi, Nat.add_zero]
        refine ⟨nin + 1, πin, by rw [hwk]; exact so_bound_found _ _ _ hnin, ?_, hkeepin, ?_⟩
        · rw [hso]
          exact run_less hv (d := true) (by simp; omega) (sr2t k) hrunin
        · rw [hso]; intro p₂ h; simp only [Option.some.injEq] at h; subst h; exact hPin
      · obtain ⟨nin, πin, hnin, hqin, hrunin, hRin⟩ := ihs q' hsi
        have hq'le := secondInner_le (x.drop s) k p r _ q q' hpq hsi
        obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hRin
        have hC2 : πin "Cut" = s := (hkeep2 "Cut" (by simp [sHeads])).trans hC
        have hF2 : πin "First" = (s : ℤ) + p₁ := (hkeep2 "First" (by simp [sHeads])).trans hF
        have hKF2 : πin "KFirst" = (s : ℤ) + (k : ℤ) * p₁ :=
          (hkeep2 "KFirst" (by simp [sHeads])).trans hKF
        have hR2 : πin "Reach" = (s : ℤ) + r := (hkeep2 "Reach" (by simp [sHeads])).trans hR0
        have hkp1 : ((k * p₁ : ℕ) : ℤ) = (k : ℤ) * p₁ := by push_cast; ring
        by_cases hper : k * p₁ ≤ q' ∧ q' ≤ r
        · have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q =
              secondOuter (x.drop s) k p₁ r fuel (p + p₁) (q' - p₁) := by
            rw [secondOuter, if_pos hg]; simp only [hsi, if_pos hper]
          have hwk : secondOuterWork (x.drop s) k p₁ r (fuel + 1) p q =
              1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q +
                secondOuterWork (x.drop s) k p₁ r fuel (p + p₁) (q' - p₁) := by
            rw [secondOuterWork, if_pos hg]; simp only [hsi, if_pos hper]
          have hp₁q : p₁ ≤ q' := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hper.1
          have hps := periodShiftF_run k
            { v with ctl := .pending [.periodShift k false 1] (.copy "Walk" "Cut"), pos := πin } p₁
            rfl (by show πin "Cut" + p₁ = πin "First"; omega) (by show 0 ≤ πin "Cut"; omega)
            (by show πin "First" ≤ v.len; omega) (by show (p₁ : ℤ) ≤ πin "A"; omega)
            (by show πin "A" ≤ v.len; omega) (by show 0 ≤ πin "P"; omega)
            (by show πin "P" + p₁ ≤ v.len; omega)
          have hchild := run_child' (.second k 10)
            { v with
              ctl := .pending [.second k 10, .periodShift k false 1] (.copy "Walk" "Cut")
              pos := πin }
            [.periodShift k false 1] (.copy "Walk" "Cut") rfl (by simp) (2 * p₁ + 2) none
            (psPosF k πin p₁) hps _ (sr10 k)
          obtain ⟨nrec, πrec, hnrec, hrunrec, hkeeprec, hPrec⟩ := ih (p + p₁) (q' - p₁)
            { v with ctl := .pending [.second k 2] (.less "P" "End"), pos := psPosF k πin p₁ }
            rfl hw (hrel_period ⟨hA2, hP2, hB2, hK2, hkeep2⟩ hp₁q) (by omega) (by intro _; omega)
            (by omega)
          have h1_ := iter_seq hchild hrunrec
          have h2_ := run_less (v := { v with
              ctl := .pending [.second k 9] (.less "Reach" "A")
              pos := πin }) rfl (d := false) (by simp; omega) (sr9f k) h1_
          have h3_ := run_less (v := { v with
              ctl := .pending [.second k 8] (.less "A" "KFirst")
              pos := πin }) rfl (d := false) (by simp; omega) (sr8f k) h2_
          have h4_ := iter_seq hrunin h3_
          refine ⟨nin + (2 * p₁ + 2 + nrec + 1 + 1) + 1, πrec, ?_, ?_, hkeeprec, ?_⟩
          · rw [hwk]; exact so_bound_period _ _ _ _ _ _ _ hnin hqin hnrec hp₁q
          · rw [hso]; exact run_less hv (d := true) (by simp; omega) (sr2t k) h4_
          · rw [hso]; exact hPrec
        · have ht := rsShifts_eq k q' (by omega)
          have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q =
              secondOuter (x.drop s) k p₁ r fuel (p + shiftNoPeriod q' k) 0 := by
            rw [secondOuter, if_pos hg]; simp only [hsi, if_neg hper]
          have hwk : secondOuterWork (x.drop s) k p₁ r (fuel + 1) p q =
              1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q +
                secondOuterWork (x.drop s) k p₁ r fuel (p + shiftNoPeriod q' k) 0 := by
            rw [secondOuterWork, if_pos hg]; simp only [hsi, if_neg hper]
          have hsp1 := shiftNoPeriod_pos q' k
          have hsmax := shiftNoPeriod_le_max q' k (by omega)
          have hdiv : p + q' / k + 1 ≤ (x.drop s).length := by
            rcases Nat.eq_zero_or_pos q' with h0 | h0
            · subst h0; simp; omega
            · have := div_succ_le q' k hk h0; omega
          obtain ⟨nrs, hnrs, hrs⟩ := resetShiftF_run k (by omega)
            { v with
              ctl := .pending [.resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin } q' rfl
            (by show πin "A" = πin "Cut" + q'; omega) (by show 0 ≤ πin "Cut"; omega)
            (by show πin "A" ≤ v.len; omega) (by show 0 ≤ πin "P"; omega)
            (by show πin "P" + (q' / k : ℕ) + 1 ≤ v.len; omega)
          rw [ht] at hrs
          have hchild := run_child' (.second k 11)
            { v with
              ctl := .pending [.second k 11, .resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin }
            [.resetShift k false 0 none 1] (.equal "A" "Cut") rfl (by simp) nrs none
            (Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
              (πin "P" + (shiftNoPeriod q' k : ℕ))) hrs _ (sr11 k)
          obtain ⟨nrec, πrec, hnrec, hrunrec, hkeeprec, hPrec⟩ := ih (p + shiftNoPeriod q' k) 0
            { v with
              ctl := .pending [.second k 2] (.less "P" "End")
              pos := Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
                (πin "P" + (shiftNoPeriod q' k : ℕ)) }
            rfl hw
            (hrel_reset (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads])
              (by simp [sHeads]) ⟨hA2, hP2, hB2, hK2, hkeep2⟩ _)
            (by omega) (by intro _; omega) (by omega)
          have h1_ := iter_seq hchild hrunrec
          obtain ⟨m, hm, h3_⟩ := second_to_reset k
            { v with ctl := .pending [.second k 8] (.less "A" "KFirst"), pos := πin } rfl
            (by
              show πin "A" < πin "KFirst" ∨ πin "Reach" < πin "A"
              rcases not_and_or.mp hper with h | h
              · left; omega
              · right; omega) _ _ h1_
          have h4_ := iter_seq hrunin h3_
          refine ⟨nin + (nrs + nrec + m) + 1, πrec, ?_, ?_, hkeeprec, ?_⟩
          · rw [hwk]; exact so_bound_reset _ _ _ _ _ _ _ _ hnin hqin hnrs hnrec hm
          · rw [hso]; exact run_less hv (d := true) (by simp; omega) (sr2t k) h4_
          · rw [hso]; exact hPrec
    · have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q = none := by
        rw [secondOuter, if_neg hg]
      refine ⟨1, v.pos, by omega, ?_, hkeep, by rw [hso]; simp⟩
      rw [hso]
      exact run_less hv (d := false) (by simp; omega) (sr2f k) (iter_zero_eq rfl)

/-- **`Second k`, from its fresh frame** (with `First = s + p₁`, `KFirst = s + k·p₁`,
`Reach = s + r`): it returns whether `secondOuter` finds a second period `p₂`, within
`8·secondOuterWork + 7` steps, and then `P = s + p₂`. -/
theorem second_run (k : ℕ) (hk : 2 ≤ k) (x rest : List (Fin 2)) (s p₁ r fuel : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.second k 1, .initialize k 1] (.copy "A" "Cut"))
    (hw : v.word = x ++ rest) (hC : v.pos "Cut" = s) (hE : v.pos "End" = x.length)
    (hF : v.pos "First" = (s : ℤ) + p₁) (hKF : v.pos "KFirst" = (s : ℤ) + (k : ℤ) * p₁)
    (hR0 : v.pos "Reach" = (s : ℤ) + r) (hsx : s ≤ x.length) (hs1 : (s : ℤ) + 1 ≤ v.len)
    (hp₁ : 0 < p₁) (hf : (x.drop s).length ≤ fuel) :
    ∃ n π', n ≤ 8 * secondOuterWork (x.drop s) k p₁ r fuel 1 0 + 7 ∧
      iterStep n v = some { v with
        ctl := .returned (some (secondOuter (x.drop s) k p₁ r fuel 1 0).isSome)
        pos := π' } ∧
      Keeps sHeads v.pos π' ∧
      ∀ p₂, secondOuter (x.drop s) k p₁ r fuel 1 0 = some p₂ → π' "P" = (s : ℤ) + p₂ := by
  have hinit := init_run k { v with ctl := .pending [.initialize k 1] (.copy "A" "Cut") } rfl
    (show 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len by omega)
  have hchild := run_child' (.second k 1) v [.initialize k 1] (.copy "A" "Cut") hv (by simp) 6
    none (initPos k v.pos) hinit _ (sr_init k)
  obtain ⟨n, π', hn, hrun, hkeep, hP⟩ := second_outer k hk x rest s p₁ r v.pos hsx hC hE hF hKF
    hR0 hp₁ fuel 1 0 { v with ctl := .pending [.second k 2] (.less "P" "End"), pos := initPos k v.pos }
    rfl hw (hrel_init (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads])
      k s v.pos hC) (by omega) (by intro _; omega) (by omega)
  exact ⟨6 + n, π', by omega, iter_seq hchild hrun, hkeep, hP⟩

/-! ## `Decompose k` -/

section DecTrans
variable (k : ℕ)

theorem dc0 : Ctl.ofOutcome (next [.decompose k 0] none) =
    .pending [.decompose k 1] (.copy "Cut" "Origin") := rfl
theorem dc1 : (Ctl.pending [.decompose k 1] (.copy "Cut" "Origin")).resume matchTests false =
    .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut") := rfl
theorem dc2f : liftCtl (.decompose k 2) (.returned (some false)) = .returned (some false) := rfl
theorem dc2t : liftCtl (.decompose k 2) (.returned (some true)) =
    .pending [.decompose k 3] (.copy "First" "P") := rfl
theorem dc3 : (Ctl.pending [.decompose k 3] (.copy "First" "P")).resume matchTests false =
    .pending [.decompose k 4] (.copy "KFirst" "B") := rfl
theorem dc4 : (Ctl.pending [.decompose k 4] (.copy "KFirst" "B")).resume matchTests false =
    .pending [.decompose k 5] (.less "B" "End") := rfl
theorem dc5t : (Ctl.pending [.decompose k 5] (.less "B" "End")).resume matchTests true =
    .pending [.decompose k 6] (.symbols "A" "B") := rfl
theorem dc5f : (Ctl.pending [.decompose k 5] (.less "B" "End")).resume matchTests false =
    .pending [.decompose k 8] (.copy "Reach" "B") := rfl
theorem dc6t : (Ctl.pending [.decompose k 6] (.symbols "A" "B")).resume matchTests true =
    .pending [.decompose k 7] (mv [("A", 1), ("B", 1)]) := rfl
theorem dc6f : (Ctl.pending [.decompose k 6] (.symbols "A" "B")).resume matchTests false =
    .pending [.decompose k 8] (.copy "Reach" "B") := rfl
theorem dc7 : (Ctl.pending [.decompose k 7] (mv [("A", 1), ("B", 1)])).resume matchTests false =
    .pending [.decompose k 5] (.less "B" "End") := rfl
theorem dc8 : (Ctl.pending [.decompose k 8] (.copy "Reach" "B")).resume matchTests false =
    .pending [.decompose k 9, .second k 1, .initialize k 1] (.copy "A" "Cut") := rfl
theorem dc9f : liftCtl (.decompose k 9) (.returned (some false)) = .returned (some true) := rfl
theorem dc9t : liftCtl (.decompose k 9) (.returned (some true)) =
    .pending [.decompose k 10] (.copy "Second" "P") := rfl
theorem dc10 : (Ctl.pending [.decompose k 10] (.copy "Second" "P")).resume matchTests false =
    .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut") := rfl
theorem dc11t : liftCtl (.decompose k 11) (.returned (some true)) =
    .pending [.decompose k 12] (.less "Cut" "P") := rfl
theorem dc11f : liftCtl (.decompose k 11) (.returned (some false)) =
    .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut") := rfl
theorem dc12t : (Ctl.pending [.decompose k 12] (.less "Cut" "P")).resume matchTests true =
    .pending [.decompose k 13] (mv [("Cut", 1), ("Second", 1)]) := rfl
theorem dc12f : (Ctl.pending [.decompose k 12] (.less "Cut" "P")).resume matchTests false =
    .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut") := rfl
theorem dc13 :
    (Ctl.pending [.decompose k 13] (mv [("Cut", 1), ("Second", 1)])).resume matchTests false =
      .pending [.decompose k 12] (.less "Cut" "P") := rfl

end DecTrans

/-- **The `reach` extension** (sites 5–7) computes `extendReach`, in `3·work` steps. -/
theorem extend_run (k : ℕ) (x rest : List (Fin 2)) (s p₁ : ℕ) (hsx : s ≤ x.length) :
    ∀ (fuel r : ℕ) (v : HVM), v.ctl = .pending [.decompose k 5] (.less "B" "End") →
      v.word = x ++ rest → v.pos "End" = x.length → v.pos "A" = (s : ℤ) + (r - p₁ : ℕ) →
      v.pos "B" = (s : ℤ) + r → p₁ ≤ r → r ≤ (x.drop s).length →
      (x.drop s).length < fuel + r →
      ∃ n π', n ≤ 3 * extendReachWork (x.drop s) p₁ fuel r ∧
        iterStep n v = some { v with
          ctl := .pending [.decompose k 8] (.copy "Reach" "B")
          pos := π' } ∧
        π' "B" = (s : ℤ) + extendReach (x.drop s) p₁ fuel r ∧ Keeps ["A", "B"] v.pos π' := by
  have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
  intro fuel
  induction fuel with
  | zero => intro r v _ _ _ _ _ _ hr hf; omega
  | succ fuel ih =>
    intro r v hv hw hE hA hB hpr hr hf
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hc : r < (x.drop s).length ∧ (x.drop s)[r - p₁]? = (x.drop s)[r]?
    · obtain ⟨h1, h3⟩ := hc
      obtain ⟨n, π', hn, hrun, hB', hkeep'⟩ := ih (r + 1)
        { v with
          ctl := .pending [.decompose k 5] (.less "B" "End")
          pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B" (v.pos "B" + 1) }
        rfl hw (by simp [hE]) (by simp [hA]; omega) (by simp [hB]; ring) (by omega) (by omega)
        (by omega)
      refine ⟨n + 1 + 1 + 1, π', ?_, ?_, ?_, ?_⟩
      · rw [extendReachWork, if_pos ⟨h1, h3⟩]; omega
      · refine run_less hv (d := true) (by simp; omega) (dc5t k) ?_
        refine run_symbols rfl (d := true) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
          (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (dc6t k) ?_
        · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = true
          rw [hw, sym_decide x rest s (r - p₁) r (by omega) (by omega) _ _ hA hB]
          exact decide_eq_true h3
        refine run_moveAB rfl (show 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len by omega)
          (show 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len by omega) (dc7 k) ?_
        exact hrun
      · rw [extendReach, if_pos ⟨h1, h3⟩]; exact hB'
      · exact keeps_trans (keeps_update (by simp) _ (keeps_update (by simp) _ (keeps_refl _ _)))
          hkeep'
    · refine ⟨if r < (x.drop s).length then 2 else 1, v.pos, ?_, ?_, ?_, keeps_refl _ _⟩
      · rw [extendReachWork, if_neg hc]; split_ifs <;> omega
      · by_cases h1 : r < (x.drop s).length
        · have h3 : ¬ (x.drop s)[r - p₁]? = (x.drop s)[r]? := fun h' => hc ⟨h1, h'⟩
          rw [if_pos h1]
          show iterStep (0 + 1 + 1) v = _
          refine run_less hv (d := true) (by simp; omega) (dc5t k) ?_
          refine run_symbols rfl (d := false) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
            (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (dc6f k) ?_
          · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = false
            rw [hw, sym_decide x rest s (r - p₁) r (by omega) (by omega) _ _ hA hB]
            exact decide_eq_false h3
          exact iter_zero_eq rfl
        · rw [if_neg h1]
          exact run_less hv (d := false) (by simp; omega) (dc5f k) (iter_zero_eq rfl)
      · rw [extendReach, if_neg hc]; exact hB

theorem moveSeq_CS (L : ℤ) (π : String → ℤ) (hC : 0 ≤ π "Cut" + 1 ∧ π "Cut" + 1 ≤ L) :
    moveSeq blind L [⟨"Cut", 1⟩, ⟨"Second", 1⟩] π =
      some (Function.update (Function.update π "Cut" (π "Cut" + 1)) "Second" (π "Second" + 1)) := by
  rw [moveSeq_cons_ok _ _ _ _ _ (fun _ => hC),
    moveSeq_cons_ok _ _ _ _ _ (fun hb => absurd (by simp [blind]) hb), moveSeq_nil]
  simp

/-- **The cut advance** (sites 12–13): `Cut` and `Second` move `j` cells in lockstep. -/
theorem cut_run (k : ℕ) :
    ∀ (j : ℕ) (v : HVM), v.ctl = .pending [.decompose k 12] (.less "Cut" "P") →
      v.pos "P" = v.pos "Cut" + j → v.pos "P" ≤ v.len → 0 ≤ v.pos "Cut" →
      ∃ π', iterStep (2 * j + 1) v = some { v with
          ctl := .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut")
          pos := π' } ∧
        π' "Cut" = v.pos "Cut" + j ∧ π' "Second" = v.pos "Second" + j ∧
        Keeps ["Cut", "Second"] v.pos π'
  | 0, v, hv, hP, _, _ => by
    refine ⟨v.pos, ?_, by simp, by simp, keeps_refl _ _⟩
    exact run_less hv (d := false) (by simp; omega) (dc12f k) (iter_zero_eq rfl)
  | j + 1, v, hv, hP, hPL, hC0 => by
    obtain ⟨π', hrun, hC', hS', hkeep'⟩ := cut_run k j
      { v with
        ctl := .pending [.decompose k 12] (.less "Cut" "P")
        pos := Function.update (Function.update v.pos "Cut" (v.pos "Cut" + 1)) "Second"
          (v.pos "Second" + 1) }
      rfl (by simp; omega) (by simp only [HVM.len] at hPL ⊢; simp; omega) (by simp; omega)
    refine ⟨π', ?_, ?_, ?_, ?_⟩
    · show iterStep (2 * j + 1 + 1 + 1) v = _
      refine run_less hv (d := true) (by simp; omega) (dc12t k) ?_
      refine run_move (ms := [⟨"Cut", 1⟩, ⟨"Second", 1⟩]) rfl
        (moveSeq_CS _ _ (show 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len by omega)) (dc13 k) ?_
      exact hrun
    · rw [hC']; simp; ring
    · rw [hS']; simp; ring
    · exact keeps_trans (keeps_update (by simp) _ (keeps_update (by simp) _ (keeps_refl _ _)))
        hkeep'

theorem strip_bound (nf Wf p SW' d nrec : ℕ) (hnf : nf ≤ 10 * Wf + 8)
    (hrec : nrec ≤ 10 * SW' + 11 * d + 8) (hp : 1 ≤ p) :
    nf + (2 * p + 1 + nrec) ≤ 10 * (Wf + SW') + 11 * (d + p) + 8 := by omega

/-- **The strip loop** (sites 10–13): `First k true` is re-run from each new cut until it fails;
this computes `stripLoop`. -/
theorem strip_run (k : ℕ) (hk : 2 ≤ k) (x rest : List (Fin 2)) (p₂ : ℕ) :
    ∀ (fuel s : ℕ) (v : HVM),
      v.ctl = .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut") →
      v.word = x ++ rest → v.pos "Cut" = s → v.pos "End" = x.length →
      v.pos "Second" = (s : ℤ) + p₂ → s ≤ x.length → (s : ℤ) + 1 ≤ v.len →
      x.length < fuel + s →
      ∃ n π', n ≤ 10 * stripLoopWork x k p₂ fuel s + 11 * (stripLoop x k p₂ fuel s - s) + 8 ∧
        iterStep n v = some { v with
          ctl := .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
          pos := π' } ∧
        π' "Cut" = stripLoop x k p₂ fuel s ∧ Keeps dHeads v.pos π' := by
  intro fuel
  induction fuel with
  | zero => intro s v _ _ _ _ _ hs _ hf; omega
  | succ fuel ih =>
    intro s v hv hw hC hE hS hs hs1 hf
    have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    obtain ⟨nf, πf, hnf, hrunf, hkeepf, hrelf⟩ := first_run k hk true x rest s p₂ (x.length + 1)
      { v with ctl := .pending [.first k true 1, .initialize k 1] (.copy "A" "Cut") } rfl hw hC hE
      hs hs1 (fun _ => hS) (fun h => by cases h) (by omega)
    have hCf : πf "Cut" = s := (hkeepf "Cut" (by simp [fHeads])).trans hC
    rcases hfo : firstOuter (x.drop s) k p₂ (x.length + 1) 1 with _ | ⟨p, m⟩
    · rw [hfo] at hrunf
      have hchild := run_child' (.decompose k 11) v [.first k true 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some false) πf hrunf _ (dc11f k)
      have hsw : stripLoopWork x k p₂ (fuel + 1) s =
          firstOuterWork (x.drop s) k p₂ (x.length + 1) 1 := by
        rw [stripLoopWork, hfo]; rfl
      have hsl : stripLoop x k p₂ (fuel + 1) s = s := by rw [stripLoop, hfo]
      refine ⟨nf, πf, ?_, hchild, ?_, keeps_mono (by simp [fHeads, dHeads]) hkeepf⟩
      · rw [hsw, hsl, Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact hnf
      · rw [hsl]; exact hCf
    · rw [hfo] at hrunf
      have hchild := run_child' (.decompose k 11) v [.first k true 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some true) πf hrunf _ (dc11t k)
      obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hrelf p m hfo
      have hplt := firstOuter_lt (x.drop s) k p₂ (x.length + 1) 1 p m (by omega) hfo
      have hsw : stripLoopWork x k p₂ (fuel + 1) s =
          firstOuterWork (x.drop s) k p₂ (x.length + 1) 1 + stripLoopWork x k p₂ fuel (s + p) := by
        rw [stripLoopWork, hfo]
      have hsl : stripLoop x k p₂ (fuel + 1) s = stripLoop x k p₂ fuel (s + p) := by
        rw [stripLoop, hfo]
      have hEf : πf "End" = x.length := (hkeepf "End" (by simp [fHeads])).trans hE
      have hSf : πf "Second" = (s : ℤ) + p₂ := (hkeepf "Second" (by simp [fHeads])).trans hS
      obtain ⟨πc, hrunc, hCc, hSc, hkeepc⟩ := cut_run k p
        { v with ctl := .pending [.decompose k 12] (.less "Cut" "P"), pos := πf } rfl
        (by show πf "P" = πf "Cut" + p; omega) (by show πf "P" ≤ v.len; omega)
        (by show 0 ≤ πf "Cut"; omega)
      have hEc : πc "End" = x.length := (hkeepc "End" (by simp)).trans hEf
      obtain ⟨nrec, πrec, hnrec, hrunrec, hCrec, hkeeprec⟩ := ih (s + p)
        { v with
          ctl := .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut")
          pos := πc }
        rfl hw (by show πc "Cut" = ((s + p : ℕ) : ℤ); rw [hCc]; push_cast; omega) hEc
        (by show πc "Second" = ((s + p : ℕ) : ℤ) + p₂; rw [hSc]; push_cast; omega) (by omega)
        (by show ((s + p : ℕ) : ℤ) + 1 ≤ v.len; push_cast; omega) (by omega)
      have hge := stripLoop_ge x k p₂ fuel (s + p)
      have hd : stripLoop x k p₂ fuel (s + p) - s = stripLoop x k p₂ fuel (s + p) - (s + p) + p := by
        omega
      refine ⟨nf + (2 * p + 1 + nrec), πrec, ?_, iter_seq hchild (iter_seq hrunc hrunrec), ?_, ?_⟩
      · rw [hsw, hsl, hd]; exact strip_bound _ _ _ _ _ _ hnf hnrec hplt.1
      · rw [hsl]; exact hCrec
      · exact keeps_trans (keeps_mono (by simp [fHeads, dHeads]) hkeepf)
          (keeps_trans (keeps_mono (by simp [dHeads]) hkeepc) hkeeprec)

/-- A strip loop started after a second period `p₂ > p₁` was found makes progress: the bounded
search from the same cut finds the least period `p₁ < p₂` again. -/
theorem strip_progress (x : List (Fin 2)) (k s : ℕ) (hk : 4 ≤ k) (hs : s ≤ x.length)
    {p₁ m p₂ : ℕ} (hfp : firstPeriod (x.drop s) k = some (p₁, m))
    (hsp : secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m) = some p₂) :
    s < stripLoop x k p₂ (x.length + 1) s := by
  have hvlen : (x.drop s).length = x.length - s := by simp
  obtain ⟨hleast, rfl⟩ := firstPeriod_some (x.drop s) k (by omega) hfp
  have hp₁ : 0 < p₁ := hleast.1.1
  have hkp₁len : k * p₁ ≤ (x.drop s).length := hleast.1.2.1
  obtain ⟨hrge, hreach⟩ :=
    extendReach_spec (x.drop s) p₁ (x.length + 1) (k * p₁) (by omega)
      (Nat.le_mul_of_pos_left p₁ (by omega)) hkp₁len hleast.1.2.2
  obtain ⟨hsecond, hsecmin⟩ :=
    secondOuter_some (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) (k * p₁)) (by omega)
      hleast hreach.2.1 hreach.1 ((x.drop s).length + 1) 1 0 p₂ (by omega)
      (by
        intro hlt
        refine ⟨by omega, ?_, ?_⟩
        · rw [hasPeriod_take_iff (by omega)]
          intro i hi; exact absurd hi (by omega)
        · rintro ⟨-, h4⟩
          rw [Nat.mul_one] at h4
          omega)
      (by intro p' hp'; rintro ⟨h4, -, -⟩; omega) hsp
  have hprim : Primitive ((x.drop s).take p₂) := second_primitive_of_least (by omega) hsecond hsecmin
  have hkrep₂ : KRep (x.drop s) k p₂ := kRep_of_second hsecond
  have hle₁₂ : p₁ ≤ p₂ := hleast.2 p₂ hkrep₂
  have hne₁₂ : p₁ ≠ p₂ := by
    rintro rfl
    exact not_second_reach hreach hsecond
  have hlt : p₁ < p₂ := by omega
  rw [stripLoop]
  rcases hfo : firstOuter (x.drop s) k p₂ (x.length + 1) 1 with _ | ⟨p, m'⟩
  · exact absurd hleast.1 (firstOuter_none_bnd (x.drop s) k p₂ (by omega) (x.length + 1) 1
      (by omega) (by omega) (by intro p' hp'; rintro ⟨h1, -, -⟩; omega) hfo p₁ hlt)
  · simp only []
    have := firstOuter_lt (x.drop s) k p₂ (x.length + 1) 1 p m' (by omega) hfo
    have := stripLoop_ge x k p₂ x.length (s + p)
    omega

theorem stripLoop_lt (x : List (Fin 2)) (k b : ℕ) :
    ∀ (fuel s : ℕ), s < stripLoop x k b fuel s → stripLoop x k b fuel s < x.length := by
  intro fuel
  induction fuel with
  | zero => intro s h; simp [stripLoop] at h
  | succ fuel ih =>
    intro s h
    rw [stripLoop] at h ⊢
    rcases hfo : firstOuter (x.drop s) k b (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only [hfo] at h; omega
    · simp only [hfo] at h ⊢
      have hlt := firstOuter_lt (x.drop s) k b (x.length + 1) 1 p m (by omega) hfo
      have hge := stripLoop_ge x k b fuel (s + p)
      rcases Nat.lt_or_ge (s + p) (stripLoop x k b fuel (s + p)) with h1 | h1
      · exact ih (s + p) h1
      · have : (x.drop s).length = x.length - s := by simp
        omega

theorem keeps_upd1 {S : List String} {X : String} (hX : X ∈ S) (π : String → ℤ) (a : ℤ) :
    Keeps S π (Function.update π X a) := keeps_update hX a (keeps_refl S π)

theorem dec_bound_stop (nf Wf L : ℕ) (hf : nf ≤ 10 * Wf + 8) : nf ≤ 10 * Wf + 38 * L + 18 := by
  omega

theorem dec_bound_found (nf Wf ner Wer ns Ws L : ℕ) (hf : nf ≤ 10 * Wf + 8) (her : ner ≤ 3 * Wer)
    (hs : ns ≤ 8 * Ws + 7) :
    nf + (ner + (ns + 1) + 1 + 1) ≤ 10 * (Wf + (Wer + Ws)) + 38 * L + 18 := by omega

theorem dec_bound_more (nf Wf ner Wer ns Ws nst SW nrec Wrec d L' : ℕ) (hf : nf ≤ 10 * Wf + 8)
    (her : ner ≤ 3 * Wer) (hs : ns ≤ 8 * Ws + 7) (hst : nst ≤ 10 * SW + 11 * d + 8)
    (hrec : nrec ≤ 10 * Wrec + 38 * L' + 18) (hd : 1 ≤ d) :
    nf + (ner + (ns + (nst + nrec + 1) + 1) + 1 + 1) ≤
      10 * (Wf + (Wer + Ws) + (SW + Wrec)) + 38 * (d + L') + 18 := by omega

set_option maxHeartbeats 1000000 in
/-- **`Decompose`'s outer loop** (from the call of `First k false`) computes `decomposeLoop`, in
`10·decomposeLoopWork + 38·(|x| − s) + 18` steps. -/
theorem dec_loop (k : ℕ) (hk : 4 ≤ k) (x rest : List (Fin 2)) :
    ∀ (fuel s : ℕ) (v : HVM),
      v.ctl = .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut") →
      v.word = x ++ rest → v.pos "Cut" = s → v.pos "End" = x.length → s ≤ x.length →
      (s : ℤ) + 1 ≤ v.len → x.length < fuel + s →
      ∃ n b π', n ≤ 10 * decomposeLoopWork x k fuel s + 38 * (x.length - s) + 18 ∧
        iterStep n v = some { v with ctl := .returned (some b), pos := π' } ∧
        Keeps dHeads v.pos π' ∧
        π' "Cut" = (decomposeLoop x k fuel s).1 ∧
        (b = true ↔ (decomposeLoop x k fuel s).2.1 ≠ 0) ∧
        (b = true →
          π' "First" = ((decomposeLoop x k fuel s).1 : ℤ) + (decomposeLoop x k fuel s).2.1 ∧
          π' "KFirst" = ((decomposeLoop x k fuel s).1 : ℤ) +
            (k : ℤ) * (decomposeLoop x k fuel s).2.1 ∧
          π' "Reach" = ((decomposeLoop x k fuel s).1 : ℤ) + (decomposeLoop x k fuel s).2.2) := by
  intro fuel
  induction fuel with
  | zero => intro s v _ _ _ _ hs _ hf; omega
  | succ fuel ih =>
    intro s v hv hw hC hE hs hs1 hf
    have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    obtain ⟨nf, πf, hnf, hrunf, hkeepf, hrelf⟩ := first_run k (by omega) false x rest s
      (x.drop s).length ((x.drop s).length + 1)
      { v with ctl := .pending [.first k false 1, .initialize k 1] (.copy "A" "Cut") } rfl hw hC hE
      hs hs1 (fun h => by cases h) (fun _ => le_refl _) (by omega)
    have hCf : πf "Cut" = s := (hkeepf "Cut" (by simp [fHeads])).trans hC
    have hEf : πf "End" = x.length := (hkeepf "End" (by simp [fHeads])).trans hE
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · have hfp' : firstOuter (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 = none := hfp
      rw [hfp'] at hrunf
      have hchild := run_child' (.decompose k 2) v [.first k false 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some false) πf hrunf _ (dc2f k)
      have hdl : decomposeLoop x k (fuel + 1) s = (s, 0, 0) := by rw [decomposeLoop, hfp]
      have hdw : decomposeLoopWork x k (fuel + 1) s =
          firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 := by
        rw [decomposeLoopWork, decomposeStepWork, hfp]; rfl
      refine ⟨nf, false, πf, ?_, hchild, keeps_mono (by simp [fHeads, dHeads]) hkeepf, ?_, ?_,
        fun h => by cases h⟩
      · rw [hdw]; exact dec_bound_stop _ _ _ hnf
      · rw [hdl]; exact hCf
      · rw [hdl]; simp
    · have hfp' : firstOuter (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 =
          some (p₁, m) := hfp
      obtain ⟨hleast, hm⟩ := firstPeriod_some (x.drop s) k (by omega) hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      have hkp₁len : k * p₁ ≤ (x.drop s).length := hleast.1.2.1
      have hkp := nat_kp k p₁ (by omega)
      obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hrelf p₁ m hfp'
      rw [hfp'] at hrunf
      have hchild1 := run_child' (.decompose k 2) v [.first k false 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some true) πf hrunf _ (dc2t k)
      -- the reach extension, from `A = s + (k−1)p₁`, `B = s + k·p₁`
      obtain ⟨ner, πe, hner, hrune, hBe, hkeepe⟩ := extend_run k x rest s p₁ hs (x.length + 1) m
        { v with
          ctl := .pending [.decompose k 5] (.less "B" "End")
          pos := Function.update (Function.update πf "First" (πf "P")) "KFirst"
            (Function.update πf "First" (πf "P") "B") }
        rfl hw (by simp [hEf]) (by simp [hA2]; rw [hm]; omega)
        (by simp [hB2]; rw [hm]; push_cast; omega) (by rw [hm]; omega) (by rw [hm]; omega)
        (by omega)
      have hrle := (extendReach_spec (x.drop s) p₁ (x.length + 1) m (by omega) (by rw [hm]; omega)
        (by rw [hm]; exact hkp₁len) (by rw [hm]; exact hleast.1.2.2)).1
      -- facts on the heads before `Second`
      have hFe : πe "First" = (s : ℤ) + p₁ := by
        rw [hkeepe "First" (by simp)]; simp [hP2]
      have hKFe : πe "KFirst" = (s : ℤ) + (k : ℤ) * p₁ := by
        have hkpZ : ((k - 1 : ℕ) : ℤ) * p₁ + p₁ = (k : ℤ) * p₁ := by exact_mod_cast hkp
        rw [hkeepe "KFirst" (by simp)]; simp [hB2]; linarith
      have hCe : πe "Cut" = s := by rw [hkeepe "Cut" (by simp)]; simp [hCf]
      have hEe : πe "End" = x.length := by rw [hkeepe "End" (by simp)]; simp [hEf]
      obtain ⟨ns, πs, hns, hruns, hkeeps, hPs⟩ := second_run k (by omega) x rest s p₁
        (extendReach (x.drop s) p₁ (x.length + 1) m) ((x.drop s).length + 1)
        { v with
          ctl := .pending [.second k 1, .initialize k 1] (.copy "A" "Cut")
          pos := Function.update πe "Reach" (πe "B") }
        rfl hw (by simp [hCe]) (by simp [hEe]) (by simp [hFe]) (by simp [hKFe]) (by simp [hBe])
        hs hs1 hp₁ (by omega)
      have hFs : πs "First" = (s : ℤ) + p₁ := by
        rw [hkeeps "First" (by simp [sHeads])]; simp [hFe]
      have hKFs : πs "KFirst" = (s : ℤ) + (k : ℤ) * p₁ := by
        rw [hkeeps "KFirst" (by simp [sHeads])]; simp [hKFe]
      have hRs : πs "Reach" = (s : ℤ) + extendReach (x.drop s) p₁ (x.length + 1) m := by
        rw [hkeeps "Reach" (by simp [sHeads])]; simp [hBe]
      have hCs : πs "Cut" = s := by rw [hkeeps "Cut" (by simp [sHeads])]; simp [hCe]
      have hEs : πs "End" = x.length := by rw [hkeeps "End" (by simp [sHeads])]; simp [hEe]
      have hkeep_s : Keeps dHeads v.pos πs :=
        keeps_trans (keeps_mono (by simp [fHeads, dHeads]) hkeepf)
          (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
            (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
              (keeps_trans (keeps_mono (by simp [dHeads]) hkeepe)
                (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
                  (keeps_mono (by simp [sHeads, dHeads]) hkeeps)))))
      rcases hsp : secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
        with _ | p₂
      · have hsp' : secondOuter (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
            ((x.drop s).length + 1) 1 0 = none := hsp
        rw [hsp'] at hruns
        have hchild2 := run_child' (.decompose k 9)
          { v with
            ctl := .pending [.decompose k 9, .second k 1, .initialize k 1] (.copy "A" "Cut")
            pos := Function.update πe "Reach" (πe "B") }
          [.second k 1, .initialize k 1] (.copy "A" "Cut") rfl (by simp) ns (some false) πs hruns _
          (dc9f k)
        have hS2 := run_copy (v := { v with
            ctl := .pending [.decompose k 8] (.copy "Reach" "B")
            pos := πe }) rfl (dc8 k) hchild2
        have hE2 := iter_seq hrune hS2
        have hC2 := run_copy (v := { v with
            ctl := .pending [.decompose k 3] (.copy "First" "P")
            pos := πf }) rfl (dc3 k) (run_copy rfl (dc4 k) hE2)
        have hall := iter_seq hchild1 hC2
        have hdl : decomposeLoop x k (fuel + 1) s =
            (s, p₁, extendReach (x.drop s) p₁ (x.length + 1) m) := by
          rw [decomposeLoop, hfp]; simp only [hsp]
        have hdw : decomposeLoopWork x k (fuel + 1) s =
            firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
              (extendReachWork (x.drop s) p₁ (x.length + 1) m +
                secondOuterWork (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
                  ((x.drop s).length + 1) 1 0) := by
          rw [decomposeLoopWork, decomposeStepWork, hfp]; simp only [hsp, Nat.add_zero]
        refine ⟨nf + (ner + (ns + 1) + 1 + 1), true, πs, ?_, hall, hkeep_s, ?_, ?_, ?_⟩
        · rw [hdw]; exact dec_bound_found _ _ _ _ _ _ _ hnf hner hns
        · rw [hdl]; exact hCs
        · rw [hdl]; simp; omega
        · intro _; rw [hdl]; exact ⟨hFs, hKFs, hRs⟩
      · have hsp' : secondOuter (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
            ((x.drop s).length + 1) 1 0 = some p₂ := hsp
        have hP₂ := hPs p₂ hsp'
        rw [hsp'] at hruns
        have hchild2 := run_child' (.decompose k 9)
          { v with
            ctl := .pending [.decompose k 9, .second k 1, .initialize k 1] (.copy "A" "Cut")
            pos := Function.update πe "Reach" (πe "B") }
          [.second k 1, .initialize k 1] (.copy "A" "Cut") rfl (by simp) ns (some true) πs hruns _
          (dc9t k)
        have hprog := strip_progress x k s hk hs hfp hsp
        have hs'le := stripLoop_le x k p₂ (x.length + 1) s hs
        have hs'lt := stripLoop_lt x k p₂ (x.length + 1) s hprog
        obtain ⟨nst, πst, hnst, hrunst, hCst, hkeepst⟩ := strip_run k (by omega) x rest p₂
          (x.length + 1) s
          { v with
            ctl := .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut")
            pos := Function.update πs "Second" (πs "P") }
          rfl hw (by simp [hCs]) (by simp [hEs]) (by simp [hP₂]) hs hs1 (by omega)
        have hEst : πst "End" = x.length := by
          rw [hkeepst "End" (by simp [dHeads])]; simp [hEs]
        obtain ⟨nrec, b, πrec, hnrec, hrunrec, hkeeprec, hCrec, hiff, hheads⟩ :=
          ih (stripLoop x k p₂ (x.length + 1) s)
            { v with
              ctl := .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
              pos := πst }
            rfl hw hCst hEst hs'le (by show _ + 1 ≤ v.len; omega) (by omega)
        have hA_ := iter_seq hrunst hrunrec
        have hB_ := run_copy (v := { v with
            ctl := .pending [.decompose k 10] (.copy "Second" "P")
            pos := πs }) rfl (dc10 k) hA_
        have hC_ := iter_seq hchild2 hB_
        have hS2 := run_copy (v := { v with
            ctl := .pending [.decompose k 8] (.copy "Reach" "B")
            pos := πe }) rfl (dc8 k) hC_
        have hE2 := iter_seq hrune hS2
        have hC2 := run_copy (v := { v with
            ctl := .pending [.decompose k 3] (.copy "First" "P")
            pos := πf }) rfl (dc3 k) (run_copy rfl (dc4 k) hE2)
        have hall := iter_seq hchild1 hC2
        have hdl : decomposeLoop x k (fuel + 1) s =
            decomposeLoop x k fuel (stripLoop x k p₂ (x.length + 1) s) := by
          rw [decomposeLoop, hfp]; simp only [hsp]
        have hdw : decomposeLoopWork x k (fuel + 1) s =
            firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
              (extendReachWork (x.drop s) p₁ (x.length + 1) m +
                secondOuterWork (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
                  ((x.drop s).length + 1) 1 0) +
              (stripLoopWork x k p₂ (x.length + 1) s +
                decomposeLoopWork x k fuel (stripLoop x k p₂ (x.length + 1) s)) := by
          rw [decomposeLoopWork, decomposeStepWork, hfp]; simp only [hsp]
        have hd : x.length - s = (stripLoop x k p₂ (x.length + 1) s - s) +
            (x.length - stripLoop x k p₂ (x.length + 1) s) := by omega
        refine ⟨nf + (ner + (ns + (nst + nrec + 1) + 1) + 1 + 1), b, πrec, ?_, hall, ?_, ?_, ?_, ?_⟩
        · rw [hdw, hd]; exact dec_bound_more _ _ _ _ _ _ _ _ _ _ _ _ hnf hner hns hnst hnrec
            (by omega)
        · exact keeps_trans hkeep_s (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
            (keeps_trans hkeepst hkeeprec))
        · rw [hdl]; exact hCrec
        · rw [hdl]; exact hiff
        · rw [hdl]; exact hheads

/-- **`Decompose k`, from its fresh frame**, on the word `x ++ rest` with `Origin = 0` and
`End = |x|`: it returns a value `b` within `(160k+418)·|x| + (20k+69)` steps, with
`Cut = s`, `b` exactly when a period exists, and then `First = s + p₁`, `KFirst = s + k·p₁`,
`Reach = s + r`, where `(s, p₁, r) = GSPreprocess.decompose x k`. Only the heads of `dHeads`
move (so `Origin`, `End`, `Tail`, `OriginalEnd`, `U`, … are kept). -/
theorem decompose_run (k : ℕ) (hk : 4 ≤ k) (x rest : List (Fin 2)) (v : HVM)
    (hv : v.ctl = Ctl.ofOutcome (next [.decompose k 0] none))
    (hw : v.word = x ++ rest) (hO : v.pos "Origin" = 0) (hE : v.pos "End" = x.length)
    (hne : x ++ rest ≠ []) :
    ∃ n b π', n ≤ (160 * k + 418) * x.length + (20 * k + 69) ∧
      iterStep n v = some { v with ctl := .returned (some b), pos := π' } ∧
      Keeps dHeads v.pos π' ∧ π' "Origin" = 0 ∧ π' "End" = x.length ∧
      π' "Cut" = (decompose x k).1 ∧
      (b = true ↔ (decompose x k).2.1 ≠ 0) ∧
      (b = true →
        π' "First" = ((decompose x k).1 : ℤ) + (decompose x k).2.1 ∧
        π' "KFirst" = ((decompose x k).1 : ℤ) + (k : ℤ) * (decompose x k).2.1 ∧
        π' "Reach" = ((decompose x k).1 : ℤ) + (decompose x k).2.2) := by
  rw [dc0] at hv
  have hL : (1 : ℤ) ≤ v.len := by
    have : 0 < (x ++ rest).length := List.length_pos_of_ne_nil hne
    simp only [HVM.len, hw]
    omega
  obtain ⟨n, b, π', hn, hrun, hkeep, hC, hiff, hheads⟩ := dec_loop k hk x rest (x.length + 1) 0
    { v with
      ctl := .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
      pos := Function.update v.pos "Cut" (v.pos "Origin") }
    rfl hw (by simp [hO]) (by simp [hE]) (Nat.zero_le _)
    (by show ((0 : ℕ) : ℤ) + 1 ≤ v.len; simpa using hL) (by omega)
  have hkeep' : Keeps dHeads v.pos π' :=
    keeps_trans (keeps_upd1 (by simp [dHeads]) _ _) hkeep
  have hwork := decomposeWork_le x k hk
  have e0 : decomposeWork x k = decomposeLoopWork x k (x.length + 1) 0 := rfl
  have e1 : (160 * k + 418) * x.length = 10 * ((16 * k + 38) * x.length) + 38 * x.length := by
    ring
  refine ⟨n + 1, b, π', ?_, run_copy hv (dc1 k) hrun, hkeep', ?_, ?_, hC, hiff, hheads⟩
  · rw [e0] at hwork
    omega
  · rw [hkeep' "Origin" (by simp [dHeads]), hO]
  · rw [hkeep' "End" (by simp [dHeads]), hE]

end PalPeg.ScaHeadDecompose
