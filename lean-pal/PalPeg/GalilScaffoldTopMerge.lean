import PalPeg.GalilScaffoldTopVM
import PalPeg.GalilScaffoldTopFallback
import PalPeg.GalilScaffoldTopFpp
import PalPeg.GalilScaffoldTopMarks

/-!
# Merging the per-mode frames on the unified VM

Each mode's frame, pulled back along its lens, is a `Frame GalilVM` whose
fields for the other modes are empty. `galilFrame` takes every field from the
frame of the mode that uses it. A tick of a pulled per-mode frame whose source
mode is that mode is a tick of `galilFrame`: the constructors of one mode
only consult that mode's fields, so the transfer is by cases.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- Parameters shared by all modes: output refresh, init and replayStart
effects (instantiated later). -/
structure Shared where
  onLetter : GalilVM → Prop
  leftFirst : GalilVM → Prop
  init : GalilVM → GalilVM → Prop
  replayStart : GalilVM → GalilVM → Prop
  replayPos : GalilVM → Bool
  replayExhausted : GalilVM → Bool
  /-- `chain.canShift && chain.prediction() == right.read()` (chain-side guard). -/
  shiftGuard : GalilVM → Prop
  /-- `beginChainShift` VM part. -/
  beginShift : GalilVM → GalilVM → Prop
  /-- `beginFallback` VM part. -/
  beginFallback : GalilVM → GalilVM → Prop
  /-- The Broken-chain restart. -/
  restart : GalilVM → GalilVM → Prop
  /-- The centre symbol of the chain start (decoded from the heads by the
  input-supply layer). -/
  centre : GalilVM → Fin 3
  /-- The centre place of the chain start. -/
  place : GalilVM → GalilScaffoldPlace.Place

/-- `galilFrame`: scan fields from `scanFrame`, shift fields from
`shiftFrame`, copy/home from `fallbackFrame`, fpp from `fppFrame`, markEnd
from `marksFrame`, choose/rewind from `rewindFrame`, the rest from `P`. -/
def galilFrame (P : Shared) (q : ℕ) (first : Fin 9) : Frame GalilVM :=
  let S := Frame.pull scanLens (scanFrame (fun _ => True) (fun _ => True))
  let H := Frame.pull shiftLens (shiftFrame (fun _ => True) (fun _ => True))
  let B := Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))
  let Fp := Frame.pull fppLens (fppFrame q first (fun _ => True) (fun _ => True))
  let M := Frame.pull fppLens (marksFrame first (fun _ => True) (fun _ => True))
  let R := Frame.pull rewindLens (rewindFrame first (fun _ => True) (fun _ => True))
  { init := P.init
    available := S.available
    background := S.background
    compare := S.compare
    matched := S.matched
    shiftGuard := P.shiftGuard
    matchedPlace := fun b s t => t = (if b then {s with replay := GalilScaffoldCounter.dec s.replay} else s)
    replayExhausted := P.replayExhausted
    onLetter := P.onLetter
    leftFirst := P.leftFirst
    beginShift := P.beginShift
    beginFallback := P.beginFallback
    remainingPos := fun s => H.remainingPos s ∨ B.remainingPos s
    shiftOne := H.shiftOne
    copyOne := B.copyOne
    copyEnd := B.copyEnd
    atLeft := B.atLeft
    fppStart := B.fppStart
    homeStep := B.homeStep
    fppSlice := Fp.fppSlice
    fppDone := Fp.fppDone
    atEnd := M.atEnd
    markBack := R.markBack
    markForward := M.markForward
    markSet := R.markSet
    choose := R.choose
    atFirst := R.atFirst
    fppReset := R.fppReset
    rewindOne := R.rewindOne
    rewindPair := R.rewindPair
    replayStart := P.replayStart
    replayPos := P.replayPos
    restart := P.restart }

/-- Kill the constructors whose source mode differs from `c.mode`. -/
macro "wrong_mode" : tactic => `(tactic| (exfalso; simp_all; done))

/-- Shift-mode ticks of the pulled shift frame transfer to `galilFrame`;
the copy reading of `remainingPos` must be false. -/
theorem shift_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .shift)
    (hcopy : ¬ (Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))).remainingPos s)
    (h : Tick (Frame.pull shiftLens (shiftFrame (fun v => P.onLetter (shiftLens.set s v))
      (fun v => P.leftFirst (shiftLens.set s v)))) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case shift_one =>
    rename_i hp h1
    exact .shift_one c s t hm (Or.inl hp) h1
  case shift_done =>
    rename_i o hm' hp ho
    refine .shift_done c s o hm (fun h => h.elim hp hcopy) ?_
    simp only [refresh, Frame.pull, galilFrame, shiftFrame, shiftLens] at ho ⊢
    simpa using ho

/-- Copy/home-mode ticks of the pulled fallback frame transfer; the shift
reading of `remainingPos` must be false. -/
theorem fallback_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (f g : FppControl.State → Prop)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .copy ∨ c.mode = .home)
    (hshift : ¬ (Frame.pull shiftLens (shiftFrame (fun _ => True) (fun _ => True))).remainingPos s)
    (h : Tick (Frame.pull fppLens (fallbackFrame f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case copy_one =>
    rename_i hm' hp h1
    exact .copy_one c s t hm' (Or.inr hp) h1
  case copy_done =>
    rename_i hm' hp h1
    exact .copy_done c s t hm' (fun h => h.elim hshift hp) h1
  case home_start =>
    rename_i hm' hl h1
    exact .home_start c s t hm' hl h1
  case home_step =>
    rename_i hm' hl h1
    exact .home_step c s t hm' hl h1

theorem fpp_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (f g : FppControl.State → Prop)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .fpp)
    (h : Tick (Frame.pull fppLens (fppFrame q first f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case fpp_slice =>
    rename_i h1
    exact .fpp_slice c s t hm h1
  case fpp_done =>
    rename_i h1
    exact .fpp_done c s t hm h1

theorem markEnd_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (f g : FppControl.State → Prop)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .markEnd)
    (h : Tick (Frame.pull fppLens (marksFrame first f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case markEnd_found =>
    rename_i he h1
    refine .markEnd_found c s t hm he ?_
    -- `markBack` in `galilFrame` is the rewind lens reading; both are the same MARKS move
    obtain ⟨⟨hl, hy⟩, ht⟩ := h1
    have hy' : t.fpp = markStep s.fpp GalilScaffoldTape.moveLeft := hy
    have ht' : t = {s with fpp := t.fpp} := ht
    have hteq : t = {s with fpp := markStep s.fpp GalilScaffoldTape.moveLeft} := by
      rw [ht', hy']
    subst hteq
    exact ⟨⟨hl, rfl⟩, rfl⟩
  case markEnd_step =>
    rename_i he h1
    exact .markEnd_step c s t hm he h1

theorem rewind_transfer (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (f g : RewindVM → Prop)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .choose ∨ c.mode = .rewind)
    (h : Tick (Frame.pull rewindLens (rewindFrame first f g)) delay ⟨c, s⟩ ⟨c', t⟩) :
    Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ := by
  cases h <;> try wrong_mode
  case choose_select =>
    rename_i hm' ho hs h1
    exact .choose_select c s t hm' ho hs h1
  case choose_step =>
    rename_i hm' hs h1
    exact .choose_step c s t hm' hs h1
  case rewind_done =>
    rename_i hm' hf h1
    exact .rewind_done c s t hm' hf h1
  case rewind_one =>
    exact .rewind_one c s t ‹_› ‹_› ‹_› ‹_›
  case rewind_pair =>
    exact .rewind_pair c s t ‹_› ‹_› ‹_› ‹_›

#print axioms shift_transfer
#print axioms fallback_transfer
#print axioms fpp_transfer
#print axioms markEnd_transfer
#print axioms rewind_transfer

end PalPeg.GalilScaffoldChainInputSupply
