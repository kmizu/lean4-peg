import PalPeg.TextFeedPipelinePrefixPrepared

/-! The second FIFO and its untouched text head survive prefix work;
at return they supply the actual verifier representation. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixReserve
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPrefixRank

variable {k : ℕ}

structure Reserve (e : Env k) (Text : List (Fin k)) (n : ℕ) (z : State k) : Prop where
  inv : Inv z.2.q₂
  word : toList z.2.q₂ = Text.take n
  text : Tape.SeqView e.blank z.2.X (TextFeed.padW e.blank Text 0) 0

theorem Reserve.work {e : Env k} {Text : List (Fin k)} {n : ℕ} {z : State k}
    (h : Reserve e Text n z) : Reserve e Text n (work e z) := ⟨h.inv, h.word, h.text⟩

theorem Reserve.works {e : Env k} {Text : List (Fin k)} {n : ℕ} {z : State k}
    (h : Reserve e Text n z) (N : ℕ) : Reserve e Text n ((TextFeedPipelinePrefixLink.work e)^[N] z) := by
  induction N with
  | zero => exact h
  | succ N ih => simpa only [Function.iterate_succ_apply'] using ih.work

theorem Reserve.arrival {e : Env k} {Text : List (Fin k)} {n : ℕ} {z : State k}
    (h : Reserve e Text n z) {a : Fin k} (hn : n < Text.length) (ha : Text[n]? = some a) :
    Reserve e Text (n + 1) (arrival a z) := by
  refine ⟨inv_snoc h.inv a, ?_, h.text⟩
  change toList (snoc z.2.q₂ a) = _
  rw [toList_snoc h.inv, h.word]
  exact TextFeedPrefixVerifier.valid_take_append (TextFeedPrefixDeadline.Valid.cons ha
    (TextFeedPrefixDeadline.Valid.nil (by omega)))

theorem endpoint_ready {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    {leftSym : Fin k} {R rate : ℕ} {z : State k} {x : Phys e leftSym R rate}
    (hl : Link e leftSym R rate z x) (hg : Good e u v Text d p r n 0 (erase z))
    (hr : Reserve e Text n z) :
    stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) [afterPrefix rate] ∧
    ∃ M U qt₁ m₁ qt₂ m₂,
      z.2.worker = TextFeedPrefixFinish.data M U ∧
      x.2 = TextFeedPrefixMachine.tapes e qt₁ m₁ qt₂ m₂ z.2 ∧
      Ready e.blank e.mark qt₁ m₁ M.Q ∧ Ready e.blank e.mark qt₂ m₂ z.2.q₂ ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n
        (TextFeedPrefixReady.model M U z.2.X z.2.q₂ ⟨qt₂ ∘ m₂.roles, 0⟩) ∧
      M.st.pos = u.length ∧ M.st.q = 0 ∧ M.m = u.length := by
  obtain ⟨hs, M, U, hD, hrep, hm⟩ := hl.finished hg
  obtain ⟨qt₁, m₁, qt₂, m₂, ht, _, _, h₁, h₂, _⟩ := hl
  refine ⟨hs, M, U, qt₁, m₁, qt₂, m₂, hD, ht, ?_, h₂, ?_, hrep.pos, hrep.q, hm⟩
  · simpa only [hD, TextFeedPrefixFinish.data] using h₁
  · exact TextFeedPrefixReady.model_feedInv hrep.feed hrep.pos hrep.pat hr.text h₂.enc hr.inv hr.word

/-- info: 'PalPeg.TextFeedPipelinePrefixReserve.endpoint_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms endpoint_ready

end PalPeg.TextFeedPipelinePrefixReserve
