import PalPeg.VerifierFeedShared

/-! A finite instruction bank for the existing ten-tape verifier source.
Each Txt2 right move includes a closed FIFO fill before the source resumes.
A stationary Txt2 instruction fills the current cell without moving it. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedPrimitive
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.VerifierFeed PalPeg.VerifierFeedShared

variable {k : ℕ} {Terminal : Type}

def fromS (T : STape (Fin k)) : TapeConfiguration k := ⟨T.left, T.focus, T.right⟩

def fromTapes (T : Fin 10 → STape (Fin k)) : GSVTapes.VTapes' k :=
  (fun j => fromS (T (GSVProg.e8 j)), ⟨fromS (T GSVProg.tU), fromS (T GSVProg.tX)⟩)

theorem vTS_fromTapes (T : Fin 10 → STape (Fin k)) : GSVProg.vTS (fromTapes T) = T := by
  funext j
  fin_cases j <;> rfl

theorem fromTapes_vTS (vt : GSVTapes.VTapes' k) : fromTapes (GSVProg.vTS vt) = vt := by
  apply Prod.ext
  · funext j
    change fromS (GSVProg.vTS vt (GSVProg.e8 j)) = vt.1 j
    rw [GSVProg.vTS_e8]
    rfl
  · rfl

def primitive (e : Env k) (a : GSVProg.Act10) (M : VMachine' k) : VMachine' k :=
  { M with
    vt := fromTapes (applyTrace e.blank (GSVProg.vTS M.vt)
      [actVec (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym) a (GSVProg.vTS M.vt)])
    R1 := ⟨M.R1.qt, M.R1.cost + 1⟩ }

theorem primitive_UR (e : Env k) (M : VMachine' k) :
    primitive e (GSVProg.tU, true, .right) M = vmoveUR e.blank M := by
  have ht : applyTrace e.blank (GSVProg.vTS M.vt)
      [actVec (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym)
        (GSVProg.tU, true, .right) (GSVProg.vTS M.vt)] = GSVProg.vTS (vmoveUR e.blank M).vt := by
    funext j
    fin_cases j <;> try rfl
    change (RTQueueProg.toS M.vt.2.U).applyAction e.blank (M.vt.2.U.focus, .right) =
      RTQueueProg.toS (Tape.step e.blank M.vt.2.U M.vt.2.U.focus .right)
    rw [RTQueueProg.toS_step]
  unfold primitive
  rw [ht, fromTapes_vTS]
  rfl

def isXR (a : GSVProg.Act10) : Prop := a = (GSVProg.tX, true, .right)

instance (a : GSVProg.Act10) : Decidable (isXR a) :=
  inferInstanceAs (Decidable (a = (GSVProg.tX, true, .right)))

/-- A stationary Txt2 probe also fills its current frontier cell. -/
def isXS (a : GSVProg.Act10) : Prop := a = (GSVProg.tX, true, .stay)

instance (a : GSVProg.Act10) : Decidable (isXS a) :=
  inferInstanceAs (Decidable (a = (GSVProg.tX, true, .stay)))

noncomputable def low (e : Env k) (a : GSVProg.Act10) : Prog (VerifierFeedShared.Act k) (Cond k) :=
  if isXR a then liftFeed (VerifierFeedClosed.stepXR e.blank e.mark)
  else if isXS a then liftFeed (TextFeedTiming.fillIf e.blank e.mark) else .act (.inr a)

noncomputable def effect (e : Env k) (a : GSVProg.Act10) (M : VMachine' k) : VMachine' k :=
  if isXR a then vstepXR e.blank e.mark M
  else if isXS a then vfillHead2 e.blank e.mark M else primitive e a M

theorem primitive_exec (e : Env k) (a : GSVProg.Act10) (qt : QT k) (m : Mode) (M : VMachine' k) :
    ∃ tr, Exec (shared (Terminal := Terminal) e) e.blank (.act (.inr a)) (bundle e qt m M) tr ∧
      tr.length = 1 ∧ applyTrace e.blank (bundle e qt m M) tr = bundle e qt m (primitive e a M) := by
  have he := exec_act (I := GSVProg.I10 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym)
    (blank := e.blank) (GSVProg.inputFree_I10 e.blank e.endSym e.mark e.startSym) a (GSVProg.vTS M.vt)
  have hex := exec_map (I₂ := shared (Terminal := Terminal) e) (fa := Sum.inr) (fc := Sum.inr)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport he verifierSlot (bundle e qt m M))
  have hinit : extend verifierSlot (GSVProg.vTS M.vt) (bundle e qt m M) = bundle e qt m M := by
    simp only [verifierSlot, bundle, extend_natAdd_append]
  rw [hinit] at hex
  refine ⟨_, hex, rfl, ?_⟩
  have ht := applyTrace_extend verifierSlot e.blank (bundle e qt m M)
    [actVec (GSVProg.I10 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym) a (GSVProg.vTS M.vt)]
    (GSVProg.vTS M.vt)
  rw [hinit] at ht
  simpa only [primitive, bundle, verifierSlot, extend_natAdd_append, vTS_fromTapes,
    actVec, GSVProg.I10, GSVProg.actOf10] using ht

theorem vstepXR_encoded {e : Env k} {M : VMachine' k} (hmb : e.mark ≠ e.blank)
    (hi : Inv M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    Encodes e.blank e.mark (vstepXR e.blank e.mark M).R2.qt (vstepXR e.blank e.mark M).Q2 := by
  unfold vstepXR vfillHead2
  split_ifs
  · exact tailT_encodes hmb (headT_encodes hb) hi
  · exact headT_encodes hb

theorem vfillHead2_encoded {e : Env k} {M : VMachine' k} (hmb : e.mark ≠ e.blank)
    (hi : Inv M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    Encodes e.blank e.mark (vfillHead2 e.blank e.mark M).R2.qt (vfillHead2 e.blank e.mark M).Q2 := by
  unfold vfillHead2
  split_ifs
  · exact tailT_encodes hmb (headT_encodes hb) hi
  · exact headT_encodes hb

/-- The real call bound is independent of the input, pattern, queue
length, and suspended source continuation. The source may resume only
after this entire bounded block, including a needed fill, has completed. -/
theorem low_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2)
    (a : GSVProg.Act10) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank (low e a) (bundle e qt m M) tr ∧
      tr.length ≤ 48 ∧ applyTrace e.blank (bundle e qt m M) tr = bundle e qt' m' (effect e a M) ∧
      Ready e.blank e.mark qt' m' (effect e a M).Q2 ∧
      Encodes e.blank e.mark (effect e a M).R2.qt (effect e a M).Q2 := by
  by_cases ha : isXR a
  · obtain ⟨tr, qt', m', he, hn, ht, hr⟩ := VerifierFeedShared.step_matches (Terminal := Terminal) hc hmb h hb
    simpa only [low, effect, if_pos ha] using
      Exists.intro tr (Exists.intro qt' (Exists.intro m' ⟨he, hn, ht, hr, vstepXR_encoded hmb h.inv hb⟩))
  · by_cases hs : isXS a
    · obtain ⟨ticks, qt', m', hn, he, hr⟩ := VerifierFeedClosed.fill_matches (Terminal := Terminal) hc hmb h hb
      obtain ⟨tr, he', ht, hout⟩ := run_feed he
        (congrFun (vfillHead2_vt1 e.blank e.mark M) GSTapes.tT) (vfillHead2_U e.blank e.mark M)
      refine ⟨tr, qt', m', ?_, by omega, ?_, ?_, ?_⟩
      · simpa only [low, if_neg ha, if_pos hs] using he'
      · simpa only [effect, if_neg ha, if_pos hs] using hout
      · simpa only [effect, if_neg ha, if_pos hs] using hr
      · simpa only [effect, if_neg ha, if_pos hs] using vfillHead2_encoded hmb h.inv hb
    · obtain ⟨tr, he, hn, ht⟩ := primitive_exec (Terminal := Terminal) e a qt m M
      refine ⟨tr, qt, m, ?_, by omega, ?_, ?_, ?_⟩
      · simpa only [low, if_neg ha, if_neg hs] using he
      · simpa only [effect, if_neg ha, if_neg hs] using ht
      · simpa only [effect, if_neg ha, if_neg hs, primitive] using h
      · simpa only [effect, if_neg ha, if_neg hs, primitive] using hb

/-- info: 'PalPeg.VerifierFeedPrimitive.low_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms low_matches

end PalPeg.VerifierFeedPrimitive
