import PalPeg.GalilTickFair
import PalPeg.CloseoutRadPack3
import PalPeg.GalilFrontier


/-!
# The counters of the scaffold are canonical along a trace

`LocalCounter.absCtr` lands in the canonical counters only (`pos = [] ∨ neg = []`), so a local
state can abstract to a scaffold state only if the ten counters the abstraction reads are
canonical.  They are, at every state of a pre-loaded trace (`countersCanonical_trace`): every
tick keeps them canonical (`allCanonical_tick`).  The restart of a broken chain copies the `last`
counter of the verifier into `radius`, so the verifier counters of the chain are carried along
(`ChainLastCan`, `chainLastCan_vmTick`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (Canonical)

namespace PalPeg.CountersCanonicalTrace

/-- Every counter the abstraction reads is canonical. -/
structure AllCanonical (s : GalilVM) : Prop where
  cycle : Canonical s.cycle
  remaining : Canonical s.remaining
  radius : Canonical s.radius
  length : Canonical s.length
  replay : Canonical s.replay
  lower : Canonical s.lower
  fppWork : Canonical s.fpp.work
  span : Canonical s.search.span
  work : Canonical s.search.work
  debt : Canonical s.search.debt

/-- A search restart starts from canonical counters. -/
theorem begin_canonical {lower radius : PalPeg.GalilScaffoldCounter.Counter}
    (hlower : Canonical lower) (hradius : Canonical radius) :
    Canonical (GalilScaffoldSearchFinish.begin lower radius).span ∧
      Canonical (GalilScaffoldSearchFinish.begin lower radius).work ∧
      Canonical (GalilScaffoldSearchFinish.begin lower radius).debt := by
  refine ⟨Or.inr rfl, ?_, hradius.symm⟩
  show Canonical (if PalPeg.GalilScaffoldCounter.zero lower then
    PalPeg.GalilScaffoldCounter.inc lower else lower)
  split
  · exact PalPeg.GalilScaffoldCounter.inc_canonical _ hlower
  · exact hlower

/-- The three counters of a search state are canonical. -/
def SearchCan (st : GalilScaffoldSearchFinish.State) : Prop :=
  Canonical st.span ∧ Canonical st.work ∧ Canonical st.debt

theorem searchCan_advance (a : Bool) {st : GalilScaffoldSearchFinish.State}
    (h : SearchCan st) : SearchCan (GalilScaffoldSearchRun.advance a st) := by
  unfold GalilScaffoldSearchRun.advance
  split
  · exact ⟨h.1, h.2.1, PalPeg.GalilScaffoldCounter.dec_canonical _ h.2.2⟩
  · exact h

theorem searchCan_waitStep (enabled : Bool) {st : GalilScaffoldSearchFinish.State}
    (h : SearchCan st) : SearchCan (GalilScaffoldDouble.waitStep enabled st) := by
  unfold GalilScaffoldDouble.waitStep
  split
  · exact ⟨Or.inr rfl, h.1, h.2.2⟩
  · exact h

theorem searchCan_doubleStep {st : GalilScaffoldSearchFinish.State}
    (h : SearchCan st) : SearchCan (GalilScaffoldDouble.step st) := by
  refine ⟨PalPeg.GalilScaffoldCounter.inc_canonical _
      (PalPeg.GalilScaffoldCounter.inc_canonical _ h.1),
    PalPeg.GalilScaffoldCounter.dec_canonical _ h.2.1, ?_⟩
  show Canonical (if st.quarter.val = 3 then PalPeg.GalilScaffoldCounter.inc st.debt
    else st.debt)
  split
  · exact PalPeg.GalilScaffoldCounter.inc_canonical _ h.2.2
  · exact h.2.2

theorem searchCan_finish (enabled done : Bool) (pc : ℕ)
    {st : GalilScaffoldSearchFinish.State} (h : SearchCan st) :
    SearchCan (GalilScaffoldSearchFinish.finish st enabled done pc) := by
  unfold GalilScaffoldSearchFinish.finish
  split
  · split
    · exact h
    · split
      · exact h
      · split
        · exact ⟨Or.inr rfl, h.1, h.2.2⟩
        · exact h
  · exact h

theorem searchCan_safeCalls {st landed : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hcalls : GalilScaffoldSearchRun.SafeCalls st x bs landed y) (h : SearchCan st) :
    SearchCan landed := by
  induction hcalls with
  | nil => exact h
  | cons st x y z b bs landed ht hsafe hrest ih =>
    exact ih (searchCan_finish _ _ _ h)

theorem searchCan_safeQuanta {st landed : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (hquanta : GalilScaffoldSearchRun.SafeQuanta st x as landed y) (h : SearchCan st) :
    SearchCan landed := by
  induction hquanta with
  | nil => exact h
  | cons st middle landed x y z a as hm hcalls hrest ih =>
    exact ih (searchCan_advance a (searchCan_safeCalls hcalls h))

/-- The three counters of a preparation state are canonical. -/
def PrepCan (p : GalilScaffoldPrepareControl.State) : Prop :=
  Canonical p.work ∧ Canonical p.span ∧ Canonical p.debt

theorem prepCan_tick {b : Bool} {x y : GalilScaffoldPrepareControl.State}
    (h : PrepCan x) (ht : GalilScaffoldPrepareControl.Tick b x y) : PrepCan y := by
  cases ht
  case idle => exact h
  case lowerBit => exact ⟨PalPeg.GalilScaffoldCounter.dec_canonical _ h.1, h.2.1, h.2.2⟩
  case lowerEnd => exact h
  case lowerLeft => exact h
  case beginCopy => exact ⟨PalPeg.GalilScaffoldCounter.inc_canonical _ h.2.1, h.2.1, h.2.2⟩
  case copyBit => exact ⟨PalPeg.GalilScaffoldCounter.dec_canonical _ h.1, h.2.1, h.2.2⟩
  case copyEnd => exact h
  case sourceLeft => exact h
  case startRun => exact h

theorem prepCan_growStep {p : GalilScaffoldPrepareControl.State} (h : PrepCan p) :
    PrepCan (GalilScaffoldStagePrepare.growStep p) :=
  ⟨PalPeg.GalilScaffoldCounter.dec_canonical _ h.1,
    PalPeg.GalilScaffoldGrow.add_canonical 8 _ h.2.1,
    PalPeg.GalilScaffoldGrow.add_canonical 2 _ h.2.2⟩

theorem prepCan_prepare {p : GalilScaffoldPrepareControl.State}
    {lower : PalPeg.GalilScaffoldCounter.Counter} (center : GalilScaffoldPlace.Place)
    (h : PrepCan p) (hlower : Canonical lower) :
    PrepCan (GalilScaffoldPrepareControl.prepare p lower center) :=
  ⟨hlower, h.2.1, h.2.2⟩

theorem prepCan_afterAdvance (a : Bool) {p : GalilScaffoldPrepareControl.State}
    (h : PrepCan p) : PrepCan (GalilScaffoldPreparePaced.afterAdvance a p) := by
  unfold GalilScaffoldPreparePaced.afterAdvance
  split
  · exact ⟨h.1, h.2.1, PalPeg.GalilScaffoldCounter.dec_canonical _ h.2.2⟩
  · exact h

/-- The search quantum keeps the four counters of the search canonical. -/
theorem searchCanonical {P : Shared} {a : Bool} {s : GalilVM} {vq : SearchVM}
    (hsource : AllCanonical s) (h : searchEffect P a s vq) :
    Canonical vq.search.span ∧ Canonical vq.search.work ∧ Canonical vq.search.debt ∧
      Canonical vq.lower := by
  rcases h with ⟨hidle, hstep⟩ | ⟨_, hsame⟩
  · unfold searchStep at hstep
    cases hmode : (searchLens.get s).search.mode <;> simp only [hmode] at hstep
    all_goals first
      | (subst hstep; exact ⟨hsource.span, hsource.work, hsource.debt, hsource.lower⟩)
      | skip
    case wait =>
      subst hstep
      obtain ⟨hspan, hwork, hdebt⟩ := searchCan_advance a
        (searchCan_waitStep true ⟨hsource.span, hsource.work, hsource.debt⟩)
      exact ⟨hspan, hwork, hdebt, hsource.lower⟩
    case double =>
      split at hstep
      · subst hstep
        obtain ⟨hspan, hwork, hdebt⟩ := searchCan_advance a
          (searchCan_doubleStep ⟨hsource.span, hsource.work, hsource.debt⟩)
        exact ⟨hspan, hwork, hdebt, hsource.lower⟩
      · subst hstep
        obtain ⟨hwork, hspan, hdebt⟩ := prepCan_afterAdvance a
          (prepCan_prepare _ (p := (searchLens.get s).toPrep)
            ⟨hsource.work, hsource.span, hsource.debt⟩ hsource.lower)
        exact ⟨hspan, hwork, hdebt, hsource.lower⟩
    case grow =>
      split at hstep
      · subst hstep
        obtain ⟨hwork, hspan, hdebt⟩ := prepCan_afterAdvance a
          (prepCan_growStep (p := (searchLens.get s).toPrep)
            ⟨hsource.work, hsource.span, hsource.debt⟩)
        exact ⟨hspan, hwork, hdebt, hsource.lower⟩
      · subst hstep
        obtain ⟨hwork, hspan, hdebt⟩ := prepCan_afterAdvance a
          (prepCan_prepare _ (p := (searchLens.get s).toPrep)
            ⟨hsource.work, hsource.span, hsource.debt⟩ hsource.lower)
        exact ⟨hspan, hwork, hdebt, hsource.lower⟩
    all_goals first
      | (obtain ⟨landed, htick, hstep⟩ := hstep
         subst hstep
         obtain ⟨hwork, hspan, hdebt⟩ := prepCan_afterAdvance a
           (prepCan_tick ⟨hsource.work, hsource.span, hsource.debt⟩ htick)
         exact ⟨hspan, hwork, hdebt, hsource.lower⟩)
      | skip
    case run =>
      obtain ⟨hquanta, hlower, -⟩ := hstep
      obtain ⟨hspan, hwork, hdebt⟩ := searchCan_safeQuanta hquanta
        ⟨hsource.span, hsource.work, hsource.debt⟩
      exact ⟨hspan, hwork, hdebt, hlower ▸ hsource.lower⟩
  · subst hsame
    exact ⟨hsource.span, hsource.work, hsource.debt, hsource.lower⟩

/-- A scan background tick keeps every counter canonical, given the search part. -/
theorem allCanonical_background (P : Shared) (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (hsource : AllCanonical s) (hb : (galilFrameS P q first).background s t) :
    AllCanonical t := by
  obtain ⟨-, -, -, -, -, hradius, hlength, hcycle, hremaining, hreplay, hfpp, hsearch⟩ :=
    backgroundS_fields P q first hb
  obtain ⟨hspan, hwork, hdebt, hlower⟩ := searchCanonical hsource hsearch
  refine ⟨?_, hremaining ▸ hsource.remaining, hradius ▸ hsource.radius,
    hlength ▸ hsource.length, hreplay ▸ hsource.replay, hlower, hfpp ▸ hsource.fppWork,
    hspan, hwork, hdebt⟩
  rw [hcycle]
  split
  · exact Or.inr rfl
  · exact hsource.cycle

/-- The birth of a chain resets `cycle`, which is canonical. -/
theorem allCanonical_afterBirth (born : Bool) {x : GalilVM} (h : AllCanonical x) :
    AllCanonical (afterBirth born x) := by
  cases born
  · exact h
  · exact ⟨Or.inr rfl, h.remaining, h.radius, h.length, h.replay, h.lower, h.fppWork, h.span,
      h.work, h.debt⟩

/-- The comparison of a scan tick keeps every counter canonical. -/
theorem allCanonical_compare (P : Shared) (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (hsource : AllCanonical s) (hcompare : (galilFrameS P q first).compare s t) :
    AllCanonical t := by
  obtain ⟨vs, vq, a, -, -, -, hsearch, -, hlanding⟩ : compareFound P q first s t := hcompare
  obtain ⟨hspan, hwork, hdebt, hlower⟩ := searchCanonical hsource hsearch
  have hradius : Canonical (radiusAfter s) :=
    PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.radius
  have hcycle : Canonical (cycleAfter s) := by
    unfold cycleAfter
    split
    · exact PalPeg.GalilScaffoldCounter.dec_canonical _ hsource.cycle
    · exact hsource.cycle
  rw [hlanding]
  apply allCanonical_afterBirth
  cases a
  · exact ⟨hsource.cycle, hsource.remaining, hradius, hsource.length, hsource.replay, hlower,
      hsource.fppWork, hspan, hwork, hdebt⟩
  · exact ⟨hcycle, hsource.remaining, hradius,
      PalPeg.GalilScaffoldCounter.inc_canonical _
        (PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.length),
      hsource.replay, hlower, hsource.fppWork, hspan, hwork, hdebt⟩

section ChainPart

open PalPeg.GalilScaffoldCounter

/-- The three counters of the consume machine are canonical. -/
def ConsumeCan (st : GalilScaffoldChainConsume.State) : Prop :=
  Canonical st.distance ∧ Canonical st.boundary ∧ Canonical st.last

theorem consumeCan_consume (seen : Option (Fin 3))
    {st : GalilScaffoldChainConsume.State} (h : ConsumeCan st) :
    ConsumeCan (GalilScaffoldChainConsume.consume st seen) := by
  unfold GalilScaffoldChainConsume.consume
  simp only
  split_ifs
  all_goals first
    | exact h
    | exact ⟨inc_canonical _ h.1, inc_canonical _ h.1, h.2.1⟩
    | exact ⟨inc_canonical _ h.1, h.2.1, h.2.2⟩


/-- The three counters of the verifier inside a watch state are canonical. -/
def WatchCan (w : GalilScaffoldChainWatch.State) : Prop := ConsumeCan w.machine.control

theorem watchCan_tick {w landed : GalilScaffoldChainWatch.State} {b : Bool}
    (htick : GalilScaffoldChainWatch.Tick w b landed) (h : WatchCan w) : WatchCan landed := by
  cases htick
  rename_i middle hinternal houter
  have hmiddle : WatchCan middle := by
    cases hinternal with
    | idle => exact h
    | take => exact consumeCan_consume _ h
  cases houter with
  | idle => exact hmiddle
  | queued => exact hmiddle
  | immediate => exact consumeCan_consume _ hmiddle


open PalPeg.GalilScaffoldChainInputSupply in
/-- The verifier counters of a watching or broken chain are canonical. -/
def ChainLastCan : PalPeg.GalilScaffoldChainInputSupply.ChainVM → Prop
  | .watch w => WatchCan w
  | .broken w => WatchCan w
  | _ => True

open PalPeg.GalilScaffoldChainInputSupply in
theorem chainLastCan_step {x y : ChainVM} (hstep : ChainStep x y)
    (h : ChainLastCan x) : ChainLastCan y := by
  cases hstep with
  | idle => trivial
  | brokenIdle => exact h
  | copyBit => trivial
  | copyEnd => trivial
  | backStep => trivial
  | backDone => exact ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
  | watchStep w w' ht =>
    cases ht with
    | idle => exact h
    | take => exact consumeCan_consume _ h
  | watchBreak => exact h

open PalPeg.GalilScaffoldChainInputSupply in
theorem chainLastCan_matched {x y : ChainVM} (hmatched : ChainMatched x y)
    (h : ChainLastCan x) : ChainLastCan y := by
  cases hmatched with
  | idle => trivial
  | copy => trivial
  | back => trivial
  | watch w w' ho =>
    cases ho with
    | queued => exact h
    | immediate => exact consumeCan_consume _ h
  | breaks w w' hb =>
    obtain ⟨-, -, letter, -, -, hlanding⟩ := hb
    rw [hlanding]
    exact consumeCan_consume _ h
  | brokenMatched => exact h


open PalPeg.GalilScaffoldChainInputSupply in
theorem chainLastCan_tick {a : Bool} {x z : ChainVM} (htick : ChainTick a x z)
    (h : ChainLastCan x) : ChainLastCan z := by
  obtain ⟨middle, hstep, hmatched⟩ := htick
  have hmiddle := chainLastCan_step hstep h
  cases a
  · rw [show z = middle from hmatched]; exact hmiddle
  · exact chainLastCan_matched hmatched hmiddle

open PalPeg.GalilScaffoldChainInputSupply in
/-- The chain effect of a scan tick keeps the verifier counters canonical. -/
theorem chainLastCan_chainAt {a found : Bool} {answer : GalilScaffoldTape.Tape}
    {c : Fin 3} {walker : GalilScaffoldPlace.Place}
    {ver : GalilScaffoldInputHead.PlaceHead} {radius : GalilScaffoldCounter.Counter}
    {x z : ChainVM} (hat : chainAt a found answer c walker ver radius x z)
    (h : ChainLastCan x) : ChainLastCan z := by
  rcases hat with ⟨-, htick⟩ | ⟨-, -, hidle⟩ | ⟨-, -, hborn⟩
  · exact chainLastCan_tick htick h
  · rw [hidle]; trivial
  · cases a
    · rw [show z = chainStart answer c walker ver radius from hborn]; trivial
    · exact chainLastCan_matched hborn trivial

open PalPeg.GalilScaffoldChainInputSupply in
/-- A shift unit decrements the three verifier counters. -/
theorem watchCan_chainShiftOne {w : GalilScaffoldChainWatch.State} (h : WatchCan w) :
    WatchCan (chainShiftOne w) :=
  ⟨dec_canonical _ h.1, dec_canonical _ h.2.1, dec_canonical _ h.2.2⟩


open PalPeg.GalilScaffoldChainInputSupply in
/-- The comparison of a scan tick keeps the verifier counters of the chain canonical. -/
theorem chainLastCan_compare (P : Shared) (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (hsource : ChainLastCan s.chain) (hcompare : (galilFrameS P q first).compare s t) :
    ChainLastCan t.chain := by
  obtain ⟨vs, vq, a, -, -, -, -, hat, hlanding⟩ : compareFound P q first s t := hcompare
  have hlanded := chainLastCan_chainAt hat hsource
  rw [hlanding]
  cases chainBorn (decide (vq.search.mode = .found)) s.chain <;> cases a <;> exact hlanded

open PalPeg.GalilScaffoldChainInputSupply in
/-- A tick of the scaffold keeps the verifier counters of the chain canonical. -/
theorem chainLastCan_vmTick (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hsource : ChainLastCan s.chain)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ChainLastCan t.chain := by
  cases h <;> first
    | exact hsource
    | skip
  case init hm hrel =>
    obtain ⟨-, -, -, -, -, -, -, -, -, hchain, -, -, -, -, -⟩ : initVM entry s t := hrel
    rw [hchain]; trivial
  case replayStart hm ho ho' hrel =>
    obtain ⟨-, -, -, -, -, -, -, -, -, hchain, -, -, -, -, -⟩ : replayStartVM entry s t := hrel
    rw [hchain]; trivial
  case scan_wait =>
    rename_i hb
    obtain ⟨-, -, hat, -⟩ := backgroundS_fields _ q first hb
    exact chainLastCan_chainAt hat hsource
  case scan_count =>
    rename_i hb
    obtain ⟨-, -, hat, -⟩ := backgroundS_fields _ q first hb
    exact chainLastCan_chainAt hat hsource
  -- the restart lands on an idle chain
  all_goals first
    | (rename_i hrel
       obtain ⟨broken, -, -, -, -, hlanding⟩ : restartVM entry s t := hrel
       rw [hlanding]; trivial)
    | skip
  -- the fallback phases and the rewind keep the chain: the frame equation carries it
  all_goals first
    | (rename_i hrel
       obtain ⟨hstep, hframe⟩ := hrel
       rw [hstep] at hframe
       subst hframe
       exact hsource)
    | (rename_i hrel
       obtain ⟨⟨_, hstep⟩, hframe⟩ := hrel
       rw [hstep] at hframe
       subst hframe
       exact hsource)
    | (rename_i hrel
       obtain ⟨⟨letter, _, hstep⟩, hframe⟩ := hrel
       rw [hstep] at hframe
       subst hframe
       exact hsource)
    | skip
  case fpp_done =>
    rename_i hrel
    obtain ⟨⟨-, program, -, -, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact hsource
  case fpp_slice =>
    rename_i hrel
    obtain ⟨-, hframe⟩ := hrel
    rw [hframe]
    exact hsource
  case shift_one =>
    rename_i hrel
    obtain ⟨⟨-, -, -, watching, hchain, hstep⟩, hframe⟩ := hrel
    have hwatching : WatchCan watching := by
      have hsourceChain := hsource
      rw [show s.chain = ChainVM.watch watching from hchain] at hsourceChain
      exact hsourceChain
    rw [hstep] at hframe
    subst hframe
    exact watchCan_chainShiftOne hwatching
  case scan_match =>
    rename_i hcmp _ hpl _
    have hmiddle := chainLastCan_compare _ q first hsource hcmp
    have hlanding : t = replayDec c.replaying _ := hpl
    rw [hlanding, replayDec_chain]
    exact hmiddle
  case scan_shift =>
    rename_i hcmp _ hb
    have hmiddle := chainLastCan_compare _ q first hsource hcmp
    obtain ⟨watching, hchain, hlanding⟩ : beginShiftVM' _ t := hb
    rw [hchain] at hmiddle
    rw [hlanding]
    exact consumeCan_consume _ hmiddle
  case scan_fallback =>
    rename_i hb
    obtain ⟨landingPlace, hfallback, -⟩ : beginFallbackVM' _ t := hb
    have hlanding : t = _ := hfallback
    rw [hlanding]
    trivial

open PalPeg.GalilScaffoldChainInputSupply in
theorem allCanonical_tick (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hsource : AllCanonical s)
    (hchain : ChainLastCan s.chain)
    (h : Tick (galilFrameS (PalPeg.GalilScaffoldChainInputSupply.sharedC onLetter leftFirst centre place entry)
      q first) delay ⟨c, s⟩ ⟨c', t⟩) : AllCanonical t := by
  cases h <;> first
    | exact hsource
    | skip
  case choose_select hm ho hs hrel =>
    obtain ⟨hstep, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨hsource.cycle, hsource.remaining, Or.inr rfl,
      PalPeg.GalilScaffoldCounter.ofNat_canonical 1, hsource.replay, hsource.lower,
      hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩
  case rewind_done hm hf hrel =>
    obtain ⟨hstep, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨hsource.cycle, hsource.remaining, hsource.radius, hsource.length, hsource.replay,
      hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩
  case rewind_one hm hf hp hrel =>
    obtain ⟨⟨_, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨hsource.cycle, hsource.remaining, hsource.radius,
      PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.length, hsource.replay,
      hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩
  case rewind_pair hm hf hp hrel =>
    obtain ⟨⟨_, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨hsource.cycle, hsource.remaining,
      PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.radius,
      PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.length, hsource.replay,
      hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩
  case copy_one hm hp hrel =>
    obtain ⟨⟨letter, _, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨hsource.cycle, hsource.remaining, hsource.radius, hsource.length, hsource.replay,
      hsource.lower, PalPeg.GalilScaffoldCounter.dec_canonical _ hsource.fppWork, hsource.span,
      hsource.work, hsource.debt⟩
  case init hm hrel =>
    obtain ⟨-, -, -, hlength, hradius, hremaining, hreplay, hcycle, hfpp, -, hsearch, hlower,
      -, -, -⟩ : initVM entry s t := hrel
    have hbegin := begin_canonical (Or.inr rfl :
      Canonical PalPeg.GalilScaffoldCounter.reset) hsource.radius
    exact ⟨hcycle ▸ hsource.cycle, hremaining ▸ hsource.remaining, hradius ▸ hsource.radius,
      hlength ▸ PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.length,
      hreplay ▸ hsource.replay, hlower ▸ Or.inr rfl, hfpp ▸ hsource.fppWork,
      hsearch ▸ hbegin.1, hsearch ▸ hbegin.2.1, hsearch ▸ hbegin.2.2⟩
  case replayStart hm ho ho' hrel =>
    obtain ⟨hreplay, -, -, -, hradius, hlength, hremaining, hcycle, hfpp, -, hsearch, hlower,
      -, -, -⟩ : replayStartVM entry s t := hrel
    have hbegin := begin_canonical
      (Or.inr rfl : Canonical PalPeg.GalilScaffoldCounter.reset)
      (Or.inr rfl : Canonical PalPeg.GalilScaffoldCounter.reset)
    exact ⟨hcycle ▸ hsource.cycle, hremaining ▸ hsource.remaining, hradius ▸ Or.inr rfl,
      hlength ▸ PalPeg.GalilScaffoldCounter.ofNat_canonical 1, hreplay ▸ hsource.radius,
      hlower ▸ Or.inr rfl, hfpp ▸ hsource.fppWork, hsearch ▸ hbegin.1, hsearch ▸ hbegin.2.1,
      hsearch ▸ hbegin.2.2⟩
  case fpp_done hm hrel =>
    obtain ⟨⟨-, program, -, -, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨hsource.cycle, hsource.remaining, hsource.radius, hsource.length, hsource.replay,
      hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩
  case fpp_slice hm hrel =>
    obtain ⟨⟨-, -, -, hstep⟩, hframe⟩ := hrel
    have hwork : t.fpp.work = s.fpp.work :=
      (congrArg FppControl.State.work hstep).trans rfl
    exact ⟨by rw [hframe]; exact hsource.cycle, by rw [hframe]; exact hsource.remaining,
      by rw [hframe]; exact hsource.radius, by rw [hframe]; exact hsource.length,
      by rw [hframe]; exact hsource.replay, by rw [hframe]; exact hsource.lower,
      hwork ▸ hsource.fppWork, by rw [hframe]; exact hsource.span,
      by rw [hframe]; exact hsource.work, by rw [hframe]; exact hsource.debt⟩
  case shift_one hm hp hrel =>
    obtain ⟨⟨-, -, -, watch, -, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨PalPeg.GalilScaffoldCounter.inc_canonical _
        (PalPeg.GalilScaffoldCounter.inc_canonical _ hsource.cycle),
      PalPeg.GalilScaffoldCounter.dec_canonical _ hsource.remaining,
      PalPeg.GalilScaffoldCounter.dec_canonical _ hsource.radius,
      PalPeg.GalilScaffoldCounter.dec_canonical _
        (PalPeg.GalilScaffoldCounter.dec_canonical _ hsource.length),
      hsource.replay, hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩
  case scan_wait => exact allCanonical_background _ q first hsource ‹_›
  case scan_match hmt hcmp hav hpl ho =>
    have hmiddle := allCanonical_compare _ q first hsource hcmp
    have hlanding : t = replayDec c.replaying _ := hpl
    rw [hlanding]
    unfold replayDec
    split
    · exact ⟨hmiddle.cycle, hmiddle.remaining, hmiddle.radius, hmiddle.length,
        PalPeg.GalilScaffoldCounter.dec_canonical _ hmiddle.replay, hmiddle.lower,
        hmiddle.fppWork, hmiddle.span, hmiddle.work, hmiddle.debt⟩
    · exact hmiddle
  case scan_shift hmt hg hcmp hav hb =>
    have hmiddle := allCanonical_compare _ q first hsource hcmp
    obtain ⟨watch, -, hlanding⟩ : beginShiftVM' _ t := hb
    rw [hlanding]
    exact ⟨Or.inr rfl, PalPeg.GalilScaffoldCounter.ofNat_canonical _, hmiddle.radius,
      PalPeg.GalilScaffoldCounter.inc_canonical _
        (PalPeg.GalilScaffoldCounter.inc_canonical _ hmiddle.length),
      hmiddle.replay, hmiddle.lower, hmiddle.fppWork, hmiddle.span, hmiddle.work, hmiddle.debt⟩
  case scan_fallback hmt hg hcmp hav hb =>
    have hmiddle := allCanonical_compare _ q first hsource hcmp
    obtain ⟨landingPlace, hfallback, -⟩ : beginFallbackVM' _ t := hb
    have hlanding : t = _ := hfallback
    rw [hlanding]
    exact ⟨hmiddle.cycle, hmiddle.remaining, hmiddle.radius, hmiddle.length, hmiddle.replay,
      hmiddle.lower, PalPeg.GalilScaffoldCounter.inc_canonical _ hmiddle.length, hmiddle.span,
      hmiddle.work, hmiddle.debt⟩
  case scan_count => exact allCanonical_background _ q first hsource ‹_›
  all_goals first
    | (rename_i hrel
       obtain ⟨hstep, hframe⟩ := hrel
       rw [hstep] at hframe
       subst hframe
       exact ⟨hsource.cycle, hsource.remaining, hsource.radius, hsource.length, hsource.replay, hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩)
    | (rename_i hrel
       obtain ⟨⟨_, hstep⟩, hframe⟩ := hrel
       rw [hstep] at hframe
       subst hframe
       exact ⟨hsource.cycle, hsource.remaining, hsource.radius, hsource.length, hsource.replay, hsource.lower, hsource.fppWork, hsource.span, hsource.work, hsource.debt⟩)
    | skip
  case restart =>
    rename_i hrel
    obtain ⟨broken, hbroken, -, -, -, hlanding⟩ : restartVM entry s t := hrel
    have hlast : Canonical broken.machine.control.last := by
      have hbrokenCan := hchain
      rw [hbroken] at hbrokenCan
      exact hbrokenCan.2.2
    have hbegin := begin_canonical hlast hsource.radius
    rw [hlanding]
    exact ⟨hsource.cycle, hsource.remaining, hsource.radius, hsource.length, hsource.replay,
      hlast, hsource.fppWork, hbegin.1, hbegin.2.1, hbegin.2.2⟩


open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilFinalAssembly in
/-- Every counter is canonical at every state of a pre-loaded trace. -/
theorem countersCanonical_trace (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → AllCanonical (st i).vm ∧ ChainLastCan (st i).vm.chain := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hP.start]
    exact ⟨⟨Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl,
      Or.inr rfl, Or.inr rfl, Or.inr rfl⟩, trivial⟩
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    obtain ⟨hcounters, hchain⟩ := ih (by omega)
    have htick := hP.trace.tick i hlt
    exact ⟨allCanonical_tick (onLetterVM w) leftFirstVM centre place entry q first 2048
        hcounters hchain htick,
      chainLastCan_vmTick (onLetterVM w) leftFirstVM centre place entry q first 2048
        hchain htick⟩

#print axioms countersCanonical_trace

end ChainPart

end PalPeg.CountersCanonicalTrace
