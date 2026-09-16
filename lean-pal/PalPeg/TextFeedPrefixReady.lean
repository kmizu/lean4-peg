import PalPeg.TextFeedPrefixControl
import PalPeg.VerifierFeed
import PalPeg.ProgLangBlankEq

/-! Alignment yields the verifier's real initial position, while its
second text FIFO remains untouched. Padding is only a proof representation. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixReady
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeed PalPeg.VerifierFeed
open PalPeg.GSVProgZLoop (RunsTo)

variable {k : ℕ} {Terminal : Type}

def model (M : Machine' k) (U X : TapeConfiguration k) (q₂ : Queue (Fin k)) (R₂ : RTQueueTapes.Run k) :
    VMachine' k :=
  ⟨M.m, 0, (M.ts, ⟨U, X⟩), M.Q, q₂, M.R, R₂, (M.st, 0)⟩

theorem model_feedInv {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    {M : Machine' k} {U X : TapeConfiguration k} {q₂ : Queue (Fin k)} {R₂ : RTQueueTapes.Run k}
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M)
    (hpos : M.st.pos = u.length)
    (hu : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) 1)
    (hx : Tape.SeqView e.blank X (padW e.blank Text 0) 0)
    (hbuf : Encodes e.blank e.mark R₂.qt q₂) (hq : Inv q₂) (hl : toList q₂ = Text.take n) :
    VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n (model M U X q₂ R₂) := by
  refine ⟨h.scan, hu, ?_, h.buf, h.qinv, h.qlist, h.mle, hbuf, hq,
    ?_, Nat.zero_le n, h.hd, ?_, h.qle, Nat.zero_le _, ?_⟩
  · change Tape.SeqView e.blank X (padW e.blank Text 0) (M.st.pos - u.length + 0)
    simpa only [hpos, Nat.sub_self, Nat.zero_add] using hx
  · simpa only [model, List.drop_zero] using hl
  · change M.st.pos - u.length + 0 ≤ 0
    omega
  · change u.length ≤ M.st.pos
    omega

/-- The final nineteen tapes contain Txt2, six prep/input slots, Q2's
eleven tapes, and the direction tape, at the shared physical addresses. -/
def rest (e : Env k) (qt₂ : QT k) (m₂ : Mode) (X : TapeConfiguration k)
    (aux : Fin 6 → STape (Fin k)) (dir : STape (Fin k)) : Fin 19 → STape (Fin k) :=
  Fin.append (fun _ : Fin 1 => GSProg.toS X)
    (Fin.append aux (Fin.append (RTQueueControl.tapes e.code qt₂ m₂) (fun _ : Fin 1 => dir)))

noncomputable def interp (e : Env k) :=
  (TextFeedPrefixControl.interp (Terminal := Terminal) e).transport (Fin.castAddEmb 19)

theorem shared_runs {e : Env k} {p : TextFeedPrefixControl.PProg k}
    {T U : Fin 20 → STape (Fin k)} {ticks : ℕ}
    (h : RunsTo (TextFeedPrefixControl.interp (Terminal := Terminal) e) e.blank p T U ticks)
    (R : Fin 19 → STape (Fin k)) :
    RunsTo (interp (Terminal := Terminal) e) e.blank p (Fin.append T R) (Fin.append U R) ticks := by
  obtain ⟨tr, he, ht, hn⟩ := h
  have hh := exec_transport he (Fin.castAddEmb 19) (Fin.append T R)
  rw [extend_castAdd_append] at hh
  refine ⟨_, hh, ?_, by simpa only [List.length_map] using hn⟩
  have hx := applyTrace_extend (Fin.castAddEmb 19) e.blank (Fin.append T R) tr T
  simpa only [extend_castAdd_append, ht] using hx

/-- Both actual FIFOs are represented, but only Q1 is consumed by this
prefix phase. The resulting verifier invariant has pos = |u|, not zero. -/
theorem ready_after_prefix {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hend : e.endSym ∉ u) (hsu : e.startSym ∉ u) (hse : e.startSym ≠ e.endSym)
    (hn : n ≤ Text.length) (hroom : u.length ≤ n)
    (M : Machine' k) (qt₁ : QT k) (m₁ : Mode) (U X : TapeConfiguration k)
    (qt₂ : QT k) (m₂ : Mode) (q₂ : Queue (Fin k)) (aux : Fin 6 → STape (Fin k)) (dir : STape (Fin k))
    (hq₁ : Ready e.blank e.mark qt₁ m₁ M.Q) (hq₂ : Ready e.blank e.mark qt₂ m₂ q₂)
    (hf : TextFeedAlign.AtFront M) (hm : M.m = 0)
    (h : FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n M)
    (hu : Tape.SeqView e.blank U (GSPre.pword e.startSym e.endSym u) 1)
    (hx : Tape.SeqView e.blank X (padW e.blank Text 0) 0) (hl₂ : toList q₂ = Text.take n) :
    let R := rest e qt₂ m₂ X aux dir
    ∃ ticks qt₁' m₁' M' U', ticks ≤ 51 * u.length + 2 ∧
      RunsTo (interp (Terminal := Terminal) e) e.blank (TextFeedPrefixControl.program e)
        (Fin.append (TextFeedPrefixControl.tapes (TextFeedControl.tapes e qt₁ m₁ (GSProg.TS M.ts)) U) R)
        (Fin.append (TextFeedPrefixControl.tapes (TextFeedControl.tapes e qt₁' m₁' (GSProg.TS M'.ts)) U') R) ticks ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q ∧
      VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n
        (model M' U' X q₂ ⟨qt₂ ∘ m₂.roles, 0⟩) ∧
      M'.st.pos = u.length ∧ M'.st.q = 0 ∧ M'.m = u.length := by
  obtain ⟨ticks, qt₁', m₁', M', U', hlen, he, hr, hi, hp, hq, hm', hu'⟩ :=
    TextFeedPrefixControl.program_runs (Terminal := Terminal) hc hmb hblank hmark hend hsu hse
      hn hroom M qt₁ m₁ U hq₁ hf hm h hu
  exact ⟨ticks, qt₁', m₁', M', U', hlen, shared_runs he _, hr,
    model_feedInv hi hp hu' hx hq₂.enc hq₂.inv hl₂, hp, hq, hm'⟩

/-- Exact right-padding lists are not required of the real tapes. Any
blank-equivalent representation executes the same trace with the same cost. -/
theorem unpadded_runs {e : Env k} {p : TextFeedPrefixControl.PProg k}
    {T U V : Fin 39 → STape (Fin k)} {ticks : ℕ}
    (h : RunsTo (interp (Terminal := Terminal) e) e.blank p T U ticks)
    (hv : ∀ j, STape.BlankEq e.blank (T j) (V j)) :
    ∃ V', RunsTo (interp (Terminal := Terminal) e) e.blank p V V' ticks ∧
      ∀ j, STape.BlankEq e.blank (U j) (V' j) := by
  obtain ⟨tr, he, ht, hn⟩ := h
  refine ⟨applyTrace e.blank V tr, ⟨tr, exec_blankEq (fun j => (hv j).symm) he, rfl, hn⟩, ?_⟩
  rw [← ht]
  exact applyTrace_blankEq hv tr

/-- info: 'PalPeg.TextFeedPrefixReady.ready_after_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready_after_prefix

/-- info: 'PalPeg.TextFeedPrefixReady.unpadded_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpadded_runs

end PalPeg.TextFeedPrefixReady
