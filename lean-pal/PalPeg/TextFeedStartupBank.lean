import PalPeg.TextFeedStartup

/-! Shared-tape atomic bank for preparation and streaming. The preparation
program uses tapes 11..25; the FIFO uses 0..10 and input uses 26. After
preparation the worker reuses 11..18, without copying or resetting them. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.PrepInstance

variable {k : ℕ} {Terminal : Type}

def prepSlot : Fin 15 ↪ Fin 27 :=
  (Fin.natAddEmb 11).trans (Fin.castAddEmb 1)

abbrev Act (k : ℕ) := (AP k ⊕ Empty) ⊕ PrepAct k
abbrev Cond (k : ℕ) := (CT k ⊕ Fin k) ⊕ PrepCond k

/-- A sum of instruction alphabets, not a sum of tape bundles. -/
noncomputable def shared (e : Env k) : Interp Terminal (Act k) (Cond k) (Fin k) 27 where
  actOf
    | .inl a => ((IR e).transport feedSlot).actOf a
    | .inr a => ((prepInterp e.blank e.endSym e.mark).transport prepSlot).actOf a
  condOf
    | .inl c => ((IR (Terminal := Terminal) e).transport feedSlot).condOf c
    | .inr c => ((prepInterp (Terminal := Terminal) e.blank e.endSym e.mark).transport prepSlot).condOf c

inductive Label (k : ℕ) where
  | feed (a : TextFeedAtomic.Label k)
  | first (a : Fin k)
  | prep (a : PrepAct k)
  deriving DecidableEq, Fintype

noncomputable def low (e : Env k) : Label k → Prog (Act k) (Cond k)
  | .feed a => (TextFeedAtomic.low e.blank e.mark a).map Sum.inl Sum.inl
  | .first a => (TextFeedStartup.firstEnqueue e.blank e.mark a).map Sum.inl Sum.inl
  | .prep a => .act (.inr a)

theorem exec_feed {e : Env k} {p : RP k} {T : Fin 20 → STape (Fin k)}
    {tr : List (Fin 20 → Fin k × Move)}
    (h : Exec (IR (Terminal := Terminal) e) e.blank p T tr)
    (rest : Fin 27 → STape (Fin k)) :
    Exec (shared (Terminal := Terminal) e) e.blank (p.map Sum.inl Sum.inl)
      (extend feedSlot T rest) (tr.map (extendVec feedSlot rest)) :=
  exec_map (I₂ := shared e) (fa := Sum.inl) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h feedSlot rest)

theorem exec_prep {e : Env k} {p : Prog (PrepAct k) (PrepCond k)}
    {T : Fin 15 → STape (Fin k)} {tr : List (Fin 15 → Fin k × Move)}
    (h : Exec (prepInterp (Terminal := Terminal) e.blank e.endSym e.mark) e.blank p T tr)
    (rest : Fin 27 → STape (Fin k)) :
    Exec (shared (Terminal := Terminal) e) e.blank (p.map Sum.inr Sum.inr)
      (extend prepSlot T rest) (tr.map (extendVec prepSlot rest)) :=
  exec_map (I₂ := shared e) (fa := Sum.inr) (fc := Sum.inr)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h prepSlot rest)

/-- An individual prep call uses one primitive clock, even inside the
decomposition loops. Its other tapes are preserved, including the FIFO. -/
theorem prep_exec (e : Env k) (a : PrepAct k) (T : Fin 15 → STape (Fin k))
    (rest : Fin 27 → STape (Fin k)) :
    ∃ tr, Exec (shared (Terminal := Terminal) e) e.blank (low e (.prep a))
      (extend prepSlot T rest) tr ∧ tr.length = 1 ∧
      applyTrace e.blank (extend prepSlot T rest) tr =
        extend prepSlot
          (applyTrace e.blank T [actVec (prepInterp (Terminal := Terminal)
            e.blank e.endSym e.mark) a T]) rest := by
  have h := exec_act (blank := e.blank)
    (prepInterp_inputFree (Terminal := Terminal) e.blank e.endSym e.mark) a T
  exact ⟨_, exec_prep h rest, rfl, applyTrace_extend prepSlot e.blank rest _ T⟩

/-- Startup is a real bounded call of the same shared interpreter. -/
theorem first_exec {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (S : Stage k) (old a : Fin k) (ha : a ≠ e.mark)
    (rest : Fin 27 → STape (Fin k)) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank (low e (.first a))
      (extend feedSlot (TextFeedInit.unprepared e S old) rest) tr ∧
      tr.length ≤ 46 ∧
      applyTrace e.blank (extend feedSlot (TextFeedInit.unprepared e S old) rest) tr =
        extend feedSlot (rtapes e qt' m' S old) rest ∧
      RTQueueClosed.Ready e.blank e.mark qt' m' (RTQueue.snoc RTQueue.empty a) := by
  obtain ⟨tr, qt', m', he, hn, ht, hr⟩ :=
    TextFeedStartup.firstEnqueue_exec (Terminal := Terminal) hc hmb S old a ha
  refine ⟨_, qt', m', exec_feed he rest, ?_, ?_, hr⟩
  · simpa only [List.length_map] using hn
  · rw [applyTrace_extend, ht]

theorem feed_exec {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : RTQueueTapes.QT k} {m : RTQueueControl.Mode}
    {q : RTQueue.Queue (Fin k)} (h : RTQueueClosed.Ready e.blank e.mark qt m q)
    (S : Stage k) (old : Fin k) (a : TextFeedAtomic.Label k)
    (ha : TextFeedAtomic.allowed e.mark a) (rest : Fin 27 → STape (Fin k)) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank (low e (.feed a))
      (extend feedSlot (rtapes e qt m S old) rest) tr ∧ tr.length ≤ 47 ∧
      applyTrace e.blank (extend feedSlot (rtapes e qt m S old) rest) tr =
        extend feedSlot (rtapes e qt' m' (TextFeedAtomic.effect e a q S).2 old) rest ∧
      RTQueueClosed.Ready e.blank e.mark qt' m' (TextFeedAtomic.effect e a q S).1 := by
  obtain ⟨n, qt', m', hn, ⟨tr, he, hlen, ht⟩, hr⟩ :=
    TextFeedAtomic.low_bounded (Terminal := Terminal) hc hmb h S old a ha
  refine ⟨_, qt', m', exec_feed he rest, ?_, ?_, hr⟩
  · simpa only [List.length_map, hlen] using hn
  · rw [applyTrace_extend, ht]

/-- info: 'PalPeg.TextFeedStartupBank.first_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_exec

/-- info: 'PalPeg.TextFeedStartupBank.prep_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prep_exec

end PalPeg.TextFeedStartupBank
