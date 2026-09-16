import PalPeg.GSPreprocessProg69

/-! # Sentinel-controlled rightward positioning for finite cleanup -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank : Fin sc}

def rightSentinelProg (i : Fin 15) (endSym : Fin sc) : Prog (ActG 15 sc) (CondG 15 sc) :=
  .loop (i, endSym) (TAct.keep i .right).act .skip

def rightTrace (i : Fin 15) (n : ℕ) : List (TAct 15 sc) :=
  List.replicate n (.keep i .right)

theorem rightSentinel_exec {i : Fin 15} {endSym : Fin sc} {w : List (Fin sc)}
    (hend : endSym ∉ w) :
    ∀ (n b : ℕ) (S : Tapes sc), b + n = w.length →
      Tape.SeqView blank (S i) (w ++ [endSym]) b →
      ExecG Terminal blank (rightSentinelProg i endSym) S (rightTrace i n) := by
  intro n
  induction n with
  | zero =>
    intro b S hlen he
    have hb : b = w.length := by omega
    have hf := he.focus_eq
    rw [hb, List.getElem?_append_right (by omega)] at hf
    have hc : (S i).focus = endSym := by simpa using hf.symm
    exact execG_loop_stop (by simp [condOfG, hc])
  | succ n ih =>
    intro b S hlen he
    have hb : b < w.length := by omega
    have hf := he.focus_eq
    rw [List.getElem?_append_left hb] at hf
    have hn : (S i).focus ≠ endSym := by
      intro hc
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hf
      exact hend (hc ▸ hget ▸ List.getElem_mem hlt)
    change ExecG Terminal blank (.loop (i, endSym) (TAct.keep i .right).act .skip) S
      (TAct.keep i .right :: ([] ++ rightTrace i n))
    refine execG_loop_cont (a := TAct.keep i .right) ?_ execG_skip ?_
    · simp [condOfG, hn]
    · apply ih (b + 1) _ (by omega)
      change Tape.SeqView blank (applyG blank S (.keep i .right) i) _ _
      rw [applyG_keep_self]
      exact Tape.seq_move_right he (by simp; omega)

theorem rightTrace_view (i : Fin 15) (n : ℕ) (S : Tapes sc)
    {w : List (Fin sc)} {p : ℕ} (h : Tape.SeqView blank (S i) w p)
    (hn : p + n < w.length) :
    Tape.SeqView blank (runG blank (rightTrace i n) S i) w (p + n) := by
  induction n generalizing S p with
  | zero => simpa [rightTrace] using h
  | succ n ih =>
    have hs : Tape.SeqView blank (applyG blank S (.keep i .right) i) w (p + 1) := by
      rw [applyG_keep_self]
      exact Tape.seq_move_right h (by omega)
    simpa [rightTrace, List.replicate_succ, runG_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih _ hs (by omega)

theorem rightTrace_other {i j : Fin 15} (hji : j ≠ i) (n : ℕ) (S : Tapes sc) :
    runG blank (rightTrace i n) S j = S j := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    simp only [rightTrace, List.replicate_succ, runG_cons] at *
    rw [ih, applyG_ne blank _ (TAct.keep i .right) hji]

def eraseLeftSentinelProg (i : Fin 15) (start : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .loop (i, start) (TAct.put i blank .left).act .skip

def eraseLeftTrace (i : Fin 15) (n : ℕ) : List (TAct 15 sc) :=
  List.replicate n (.put i blank .left)

theorem eraseLeftSentinel_spec (i : Fin 15) (start : Fin sc) :
    ∀ (l : List (Fin sc)) (a : Fin sc) (S : Tapes sc),
      start ∉ a :: l →
      Tape.StackTopView blank (S i) a (l ++ [start]) →
      ExecG Terminal blank (eraseLeftSentinelProg (blank := blank) i start) S
        (eraseLeftTrace (blank := blank) i (l.length + 1)) ∧
      Tape.StackTopView blank
        (runG blank (eraseLeftTrace (blank := blank) i (l.length + 1)) S i) start [] := by
  intro l
  induction l with
  | nil =>
    intro a S hn h
    have hs : Tape.StackTopView blank
        (applyG blank S (.put i blank .left) i) start [] := by
      rw [applyG_put_self, Tape.step_left_of_left_cons h.left_eq]
      exact ⟨rfl, rfl, h.right_blanks.cons⟩
    constructor
    · change ExecG Terminal blank (.loop (i, start) (TAct.put i blank .left).act .skip) S
        (TAct.put i blank .left :: ([] ++ []))
      refine execG_loop_cont (a := TAct.put i blank .left) ?_ execG_skip ?_
      · simp [condOfG, h.focus_eq, show a ≠ start from fun e => hn (by simp [e])]
      · apply execG_loop_stop
        change decide ((applyG blank S (.put i blank .left) i).focus ≠ start) = false
        rw [hs.focus_eq]
        simp
    · simpa [eraseLeftTrace, runG_cons] using hs
  | cons b l ih =>
    intro a S hn h
    have hs : Tape.StackTopView blank
        (applyG blank S (.put i blank .left) i) b (l ++ [start]) := by
      rw [applyG_put_self, Tape.step_left_of_left_cons h.left_eq]
      exact ⟨rfl, rfl, h.right_blanks.cons⟩
    obtain ⟨he, hv⟩ := ih b (applyG blank S (.put i blank .left))
      (fun hm => hn (List.mem_cons_of_mem a hm)) hs
    constructor
    · change ExecG Terminal blank (.loop (i, start) (TAct.put i blank .left).act .skip) S
        (TAct.put i blank .left :: ([] ++ eraseLeftTrace (blank := blank) i (l.length + 1)))
      refine execG_loop_cont (a := TAct.put i blank .left) ?_ execG_skip he
      simp [condOfG, h.focus_eq, show a ≠ start from fun e => hn (by simp [e])]
    · simpa [eraseLeftTrace, List.replicate_succ, runG_cons] using hv

def eraseThroughSentinelProg (i : Fin 15) (start : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (eraseLeftSentinelProg (blank := blank) i start) (ACT (.put i blank .stay))

theorem eraseThroughSentinel_spec (i : Fin 15) (start a : Fin sc)
    (l : List (Fin sc)) (S : Tapes sc) (hn : start ∉ a :: l)
    (h : Tape.StackTopView blank (S i) a (l ++ [start])) :
    let trace := eraseLeftTrace (blank := blank) i (l.length + 1) ++ [.put i blank .stay]
    ExecG Terminal blank (eraseThroughSentinelProg (blank := blank) i start) S trace ∧
      Tape.StackView blank (runG blank trace S i) [] := by
  obtain ⟨he, hv⟩ := eraseLeftSentinel_spec (Terminal := Terminal) i start l a S hn h
  constructor
  · exact execG_seq he (execG_act _ _)
  · simp only [runG_append, runG_cons, runG_nil, applyG_put_self]
    exact Tape.pop_erase hv

theorem seqEnd_stackTop {i : Fin 15} {start endSym : Fin sc}
    {w : List (Fin sc)} {S : Tapes sc}
    (h : Tape.SeqView blank (S i) (start :: w ++ [endSym]) (w.length + 1)) :
    Tape.StackTopView blank (S i) endSym (w.reverse ++ [start]) := by
  constructor
  · simpa [List.take_succ_cons, List.take_append] using h.left_eq
  · have hf := h.focus_eq
    simpa using hf.symm
  · obtain ⟨t, ht, hb⟩ := h.right_eq
    have he : (S i).right = t := by simpa [List.drop_succ_cons] using ht
    exact he ▸ hb

def clearSentinelProg (i : Fin 15) (start endSym : Fin sc) :
    Prog (ActG 15 sc) (CondG 15 sc) :=
  .seq (rightSentinelProg i endSym) (eraseThroughSentinelProg (blank := blank) i start)

theorem clearSentinel_spec (i : Fin 15) (start endSym : Fin sc)
    (w : List (Fin sc)) (p : ℕ) (S : Tapes sc)
    (hne : start ≠ endSym) (hs : start ∉ w) (he : endSym ∉ w)
    (h : Tape.SeqView blank (S i) (start :: w ++ [endSym]) p) :
    ∃ trace, ExecG Terminal blank (clearSentinelProg (blank := blank) i start endSym) S trace ∧
      Tape.StackView blank (runG blank trace S i) [] := by
  have hp := h.lt
  have hpos : p + (w.length + 1 - p) = w.length + 1 := by simp at hp; omega
  have er := rightSentinel_exec (Terminal := Terminal) (i := i)
    (w := start :: w) (by simp [hne.symm, he]) (w.length + 1 - p) p S
    (by simpa using hpos) h
  have vr := rightTrace_view i (w.length + 1 - p) S h (by simp; omega)
  rw [hpos] at vr
  have vt := seqEnd_stackTop vr
  obtain ⟨ee, ve⟩ := eraseThroughSentinel_spec (Terminal := Terminal) i start endSym
    w.reverse (runG blank (rightTrace i (w.length + 1 - p)) S)
    (by simpa using And.intro hne hs) vt
  refine ⟨_, execG_seq er ee, ?_⟩
  simpa only [runG_append] using ve

theorem eraseLeftTrace_other {i j : Fin 15} (hji : j ≠ i) (n : ℕ) (S : Tapes sc) :
    runG blank (eraseLeftTrace (blank := blank) i n) S j = S j := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    simp only [eraseLeftTrace, List.replicate_succ, runG_cons] at *
    rw [ih, applyG_ne blank _ (TAct.put i blank .left) hji]

theorem clearSentinel_spec_frame (i : Fin 15) (start endSym : Fin sc)
    (w : List (Fin sc)) (p : ℕ) (S : Tapes sc)
    (hne : start ≠ endSym) (hs : start ∉ w) (he : endSym ∉ w)
    (h : Tape.SeqView blank (S i) (start :: w ++ [endSym]) p) :
    ∃ trace, ExecG Terminal blank (clearSentinelProg (blank := blank) i start endSym) S trace ∧
      Tape.StackView blank (runG blank trace S i) [] ∧
      (∀ j, j ≠ i → runG blank trace S j = S j) ∧
      trace.length = (w.length + 1 - p) + w.length + 2 := by
  have hp := h.lt
  have hpos : p + (w.length + 1 - p) = w.length + 1 := by simp at hp; omega
  have er := rightSentinel_exec (Terminal := Terminal) (i := i)
    (w := start :: w) (by simp [hne.symm, he]) (w.length + 1 - p) p S
    (by simpa using hpos) h
  have vr := rightTrace_view i (w.length + 1 - p) S h (by simp; omega)
  rw [hpos] at vr
  obtain ⟨ee, ve⟩ := eraseThroughSentinel_spec (Terminal := Terminal) i start endSym
    w.reverse (runG blank (rightTrace i (w.length + 1 - p)) S)
    (by simpa using And.intro hne hs) (seqEnd_stackTop vr)
  refine ⟨_, execG_seq er ee, ?_, ?_, ?_⟩
  · simpa only [runG_append] using ve
  · intro j hji
    simp only [runG_append, runG_cons, runG_nil]
    rw [applyG_ne blank _ (TAct.put i blank .stay) hji,
      eraseLeftTrace_other hji, rightTrace_other hji]
  · simp [rightTrace, eraseLeftTrace, Nat.add_assoc]

end PalPeg.PrepInstance
