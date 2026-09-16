import PalPeg.RTQueueInit
import PalPeg.TextFeedStream

/-! Initialize the feeder's private queue from blank tapes while preserving
the scanner produced by preprocessing. All instructions use the existing alphabet. -/
set_option autoImplicit false

namespace PalPeg.TextFeedInit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg PalPeg.RTQueueControl
open PalPeg.RTQueueClosed PalPeg.RTQueueInit PalPeg.ProgLangBank
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.TextFeedInput
open PalPeg.TextFeedAtomic PalPeg.TextFeedSchedule PalPeg.TextFeedRefine PalPeg.GSProg

variable {k : ℕ} {Terminal : Type}

def blankBundle (blank : Fin k) (t : ℕ) : Fin t → STape (Fin k) := fun _ => STape.blankTape blank

def queueBoot (blank mark : Fin k) : CP k :=
  .seq (liftQ (RTQueueInit.initProg blank mark)) (storeMode initialMode)

/-- Eleven queue writes/moves and one literal write of the finite mode. -/
theorem queueBoot_exec (e : Env k) :
    ∃ tr, Exec (IC Terminal e.code) e.blank (queueBoot e.blank e.mark)
      (Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)) tr ∧
      tr.length = 12 ∧ applyTrace e.blank
        (Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)) tr =
        RTQueueControl.tapes e.code (initQT e.blank e.mark) initialMode := by
  obtain ⟨tr, he, hlen, hout⟩ := RTQueueInit.init_exec (Terminal := Terminal) e.blank e.mark
  let T₁ := blankBundle e.blank 10
  let T₂ := blankBundle e.blank 1
  let mtr := [actVec (IM Terminal e.code) initialMode T₂]
  have hm := exec_act (I := IM Terminal e.code) (blank := e.blank)
    (fun _ _ _ => rfl) initialMode T₂
  have hmout : applyTrace e.blank T₂ mtr = RTQueueControl.cell e.code initialMode := rfl
  have hmid := applyTrace_extend (Fin.castAddEmb 1) e.blank (Fin.append T₁ T₂) tr T₁
  simp only [extend_castAdd_append] at hmid
  have hlast := applyTrace_extend (Fin.natAddEmb 10) e.blank
    (Fin.append (applyTrace e.blank T₁ tr) T₂) mtr T₂
  simp only [extend_natAdd_append] at hlast
  refine ⟨_, exec_sum_seq he hm, ?_, ?_⟩
  · simp only [List.length_append, List.length_map, hlen, List.length_cons, List.length_nil]
  · change applyTrace e.blank (Fin.append T₁ T₂)
      (tr.map (extendVec (Fin.castAddEmb 1) (Fin.append T₁ T₂)) ++
        mtr.map (extendVec (Fin.natAddEmb 10) (Fin.append (applyTrace e.blank T₁ tr) T₂))) = _
    rw [applyTrace_append, hmid, hlast, hmout]
    rw [show applyTrace e.blank T₁ tr = TSQ (initQT e.blank e.mark) from hout]
    rfl

def unprepared (e : Env k) (S : Stage k) (old : Fin k) : Fin 20 → STape (Fin k) :=
  Fin.append (Fin.append (Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)) S) (TextFeedInput.cell old)

def bootProg (blank mark : Fin k) : RP k :=
  liftWorker (TextFeedTiming.lift (liftQueue (queueBoot blank mark)))

/-- Bootstrap acts only on the eleven private queue tapes. The existing
GS scanner and the captured input register survive unchanged. -/
theorem boot_exec (e : Env k) (S : Stage k) (old : Fin k) :
    ∃ tr, Exec (IR (Terminal := Terminal) e) e.blank (bootProg e.blank e.mark)
      (unprepared e S old) tr ∧ tr.length = 12 ∧
      applyTrace e.blank (unprepared e S old) tr =
        rtapes e (initQT e.blank e.mark) initialMode S old := by
  obtain ⟨tr, he, hn, ht⟩ := queueBoot_exec (Terminal := Terminal) e
  let Q := Fin.append (blankBundle e.blank 10) (blankBundle e.blank 1)
  let F := Fin.append Q S
  let trF := tr.map (extendVec (Fin.castAddEmb 8) F)
  have heF := exec_sum_inl (I2 := IS (Terminal := Terminal) e) he F
  rw [extend_castAdd_append] at heF
  have htF := applyTrace_extend (Fin.castAddEmb 8) e.blank F tr Q
  simp only [F, Q, extend_castAdd_append, ht] at htF
  have heT := exec_map (I₂ := IT (Terminal := Terminal) e) (fa := id) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) heF
  have heR := exec_sum_inl (I2 := IReg (Terminal := Terminal) (k := k)) heT (unprepared e S old)
  rw [unprepared, extend_castAdd_append] at heR
  refine ⟨_, heR, ?_, ?_⟩
  · simp only [List.length_map, hn]
  · have htR := applyTrace_extend (Fin.castAddEmb 1) e.blank (unprepared e S old) trF F
    simp only [unprepared, extend_castAdd_append] at htR
    apply htR.trans
    change Fin.append (applyTrace e.blank F trF) _ = _
    rw [show applyTrace e.blank F trF = Fin.append (RTQueueControl.tapes e.code
      (initQT e.blank e.mark) initialMode) S from htF]
    rfl

def seedModel (e : Env k) (ts : GSTapes.TapesState' k) : TextFeed.Machine' k :=
  ⟨0, ts, empty, ⟨initQT e.blank e.mark, 0⟩, ⟨0, 0⟩⟩

noncomputable def initialCtrl (e : Env k) (R rate : ℕ) :
    CallCtrl (programs e.blank e.mark) (Outer R rate) :=
  ((⟨0, Nat.zero_lt_succ R⟩, startCtrlS (worker rate)),
    encode .idle, initialBank (programs e.blank e.mark), false)

theorem seed_feedInv {e : Env k} {ts : GSTapes.TapesState' k} {v Text : List (Fin k)}
    {rate p₁ rem : ℕ}
    (hs : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem ts ⟨0, 0⟩) :
    TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem 0 (seedModel e ts) := by
  refine ⟨hs, initQT_encodes e.blank e.mark, inv_empty, ?_, Nat.le_refl 0, Nat.le_refl 0, Nat.zero_le _⟩
  simp only [seedModel, toList_empty, List.take_zero, List.drop_zero]

/-- The post-bootstrap tape representation satisfies the exact initial
invariant used by the continuous real-input deadline proof. -/
theorem seed_sim {e : Env k} {ts : GSTapes.TapesState' k} {v Text : List (Fin k)}
    {R rate p₁ rem : ℕ} (old : Fin k)
    (hs : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem ts ⟨0, 0⟩) :
    Sim e v Text R rate p₁ rem 0 (seedModel e ts) .loop
      (initialCtrl e R rate, rtapes e (initQT e.blank e.mark) initialMode (TS ts) old) old := by
  refine ⟨seed_feedInv hs, initialBank_boundary _, rfl, trivial, ?_⟩
  exact ⟨initQT e.blank e.mark, initialMode, rfl, initial_ready e.blank e.mark⟩

/-- No marked queue, private mode, or initial queue invariant is supplied
by the caller: the fixed bootstrap constructs them from eleven blank tapes. -/
theorem boot_to_sim {e : Env k} {ts : GSTapes.TapesState' k} {v Text : List (Fin k)}
    {R rate p₁ rem : ℕ} (old : Fin k)
    (hs : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem ts ⟨0, 0⟩) :
    ∃ tr, Exec (IR (Terminal := Terminal) e) e.blank (bootProg e.blank e.mark)
      (unprepared e (TS ts) old) tr ∧ tr.length = 12 ∧
      Sim e v Text R rate p₁ rem 0 (seedModel e ts) .loop
        (initialCtrl e R rate, applyTrace e.blank (unprepared e (TS ts) old) tr) old := by
  obtain ⟨tr, he, hn, ht⟩ := boot_exec (Terminal := Terminal) e (TS ts) old
  refine ⟨tr, he, hn, ?_⟩
  rw [ht]
  exact seed_sim old hs

/-- info: 'PalPeg.TextFeedInit.boot_to_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boot_to_sim

end PalPeg.TextFeedInit
