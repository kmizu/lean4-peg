import PalPeg.TextFeedPrepBootstrap

/-! Productive preparation frames starting at the finite task's real
initial control, including bootstrap of its initially blank FIFO. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepStartupFrames
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2 PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepInterrupt PalPeg.TextFeedPrepBootstrap

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

/-- Every input is physically captured once, starting with the first one;
the source program is advanced by the exact total number of worker calls. -/
theorem started_frames {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) (hR : 0 < R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = true)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView T = TextFeedInit.unprepared e S old)
    (hs : c.1.2.2.val = [task e leftSym rate]) (a : Terminal) (word : List Terminal)
    (hall : ∀ b ∈ a :: word, enc b ≠ e.mark)
    (htrace : (trace (source e) e.blank (List.replicate ((a :: word).length * R) none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).length =
        (a :: word).length * R) :
    let z := (a :: word).foldl (machine e leftSym enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T }
    let u := runInputs (source e) e.blank (List.replicate ((a :: word).length * R) none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)
    ∃ c' T', z = { state := ((c', ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T' } ∧
      prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' ((a :: word).foldl (fun q b => snoc q (enc b)) empty)
        ((a :: word).foldl (fun _ b => enc b) old) ∧
      c'.1.2.2.val = u.1.map TextFeedPrepResume.lift ++
        [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr] ∧
      c'.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧ c'.1.2.1 = false := by
  have hsize : (a :: word).length * R = R + word.length * R := by
    simp only [List.length_cons, Nat.succ_mul]; omega
  rw [hsize] at htrace
  obtain ⟨hpre, htail⟩ := TextFeedPrepFrames.live_split e _ (prepView T) R (word.length * R) htrace
  obtain ⟨c1, T1, hz1, hv1, hb1, hr1, hs1, hc1, hf1⟩ := initial_frame
    hc hmb leftSym enc R rate hR c T hb hf hc0 S old hx hs a (hall a List.mem_cons_self) hpre
  have hz := TextFeedPrepFrames.busy_frames hc hmb leftSym enc R rate word c1 T1 hb1 hf1 hc1 hr1
    (runInputs (source e) e.blank (List.replicate R none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).1
    [(TextFeedSchedule.worker rate).map Sum.inr Sum.inr]
    (runInputs (source e) e.blank (List.replicate R none)
      ([finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate], prepView T)).2
    hv1 hs1 htail (fun b hb => hall b (List.mem_cons_of_mem a hb))
  simpa only [List.foldl_cons, hz1, hsize, List.replicate_add, runInputs_append, Prod.mk.eta] using hz

/-- info: 'PalPeg.TextFeedPrepStartupFrames.started_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms started_frames

end PalPeg.TextFeedPrepStartupFrames
