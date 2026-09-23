import PalPeg.GalilChainCoupling

/-!
# The stored copy counter is the period length

Copy increments its counter exactly when it appends a period cell; marking and
rewinding preserve both. This connects the last copy of h at back-to-watch to
the semiperiod read by beginShiftVM. The property is carried through real VM
ticks using the existing block invariant.
-/
set_option autoImplicit false
namespace PalPeg.ChainStoredPeriod
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilBranchInvariants
open PalPeg.GalilScaffoldCounter
open PalPeg.GalilScaffoldChainPeriod (Tape)

/-- Only copy/back carry the stored h. Watch keeps its period but forgets h
in the abstract VM; the physical mirror must retain that last copy. -/
def Stored : ChainVM → Prop
  | .copy _ h _ v _ _ _ | .back v h _ _ _ => h = ofNat (v.left.length + v.right.length)
  | _ => True

theorem step {x y : ChainVM} (ht : ChainStep x y) (hs : Stored x) (hb : BlockInv x) :
    Stored y := by
  cases ht <;> first | exact hs | trivial | skip
  case copyBit t h p v lag credit ver a one legal present =>
    change h = ofNat (v.left.length + v.right.length) at hs
    change OnPrefix v at hb
    change inc h = ofNat _
    rw [hs, inc_ofNat]
    have hlen := PalPeg.GalilShiftH.cells_put v a hb.1
    unfold PalPeg.GalilShiftH.cells at hlen
    congr 1
    omega
  case backStep v h lag credit ver hf =>
    change h = ofNat (v.left.length + v.right.length) at hs
    change h = ofNat _
    rw [hs]
    have hlen := PalPeg.GalilShiftH.cells_moveLeft v
    unfold PalPeg.GalilShiftH.cells at hlen
    congr 1
    omega

theorem matched {x y : ChainVM} (ht : ChainMatched x y) (hs : Stored x) : Stored y := by
  cases ht <;> exact hs

theorem tick {a : Bool} {x y : ChainVM} (ht : ChainTick a x y) (hs : Stored x)
    (hb : BlockInv x) : Stored y := by
  obtain ⟨middle, hstep, hmatched⟩ := ht
  have hm := step hstep hs hb
  cases a with
  | false => rw [show y = middle from hmatched]; exact hm
  | true => exact matched hmatched hm

theorem chainAt {a found : Bool} {answer : PalPeg.GalilScaffoldTape.Tape} {c : Fin 3}
    {walker : PalPeg.GalilScaffoldPlace.Place} {ver : PalPeg.GalilScaffoldInputHead.PlaceHead}
    {radius : Counter} {x y : ChainVM}
    (ht : PalPeg.GalilScaffoldChainInputSupply.chainAt a found answer c walker ver radius x y)
    (hs : Stored x) (hb : BlockInv x) : Stored y := by
  rcases ht with ⟨_, htick⟩ | ⟨_, _, hidle⟩ | ⟨_, _, hborn⟩
  · exact tick htick hs hb
  · rw [hidle]; trivial
  · cases a with
    | false => rw [show y = chainStart answer c walker ver radius from hborn]; rfl
    | true => exact matched hborn rfl

theorem compare (P : Shared) (q : ℕ) (first : Fin 9) {s t : GalilVM}
    (hs : Stored s.chain) (hb : BlockInv s.chain)
    (ht : (galilFrameS P q first).compare s t) : Stored t.chain := by
  obtain ⟨vs, vq, a, _, _, _, _, hat, hlanding⟩ : compareFound P q first s t := ht
  have hlanded := chainAt hat hs hb
  rw [hlanding]
  cases chainBorn (decide (vq.search.mode = .found)) s.chain <;> cases a <;> exact hlanded

theorem vmTick (onLetter leftFirst : GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hsource : Stored s.chain)
    (hblock : BlockInv s.chain)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : Stored t.chain := by
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
    exact chainAt hat hsource hblock
  case scan_count =>
    rename_i hb
    obtain ⟨-, -, hat, -⟩ := backgroundS_fields _ q first hb
    exact chainAt hat hsource hblock
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
    rw [hstep] at hframe
    subst hframe
    trivial
  case scan_match =>
    rename_i hcmp _ hpl _
    have hmiddle := compare _ q first hsource hblock hcmp
    have hlanding : t = replayDec c.replaying _ := hpl
    rw [hlanding, replayDec_chain]
    exact hmiddle
  case scan_shift =>
    rename_i hcmp _ hb
    obtain ⟨watching, hchain, hlanding⟩ : beginShiftVM' _ t := hb
    rw [hlanding]
    trivial
  case scan_fallback =>
    rename_i hb
    obtain ⟨landingPlace, hfallback, -⟩ : beginFallbackVM' _ t := hb
    have hlanding : t = _ := hfallback
    rw [hlanding]
    trivial

/-- info: 'PalPeg.ChainStoredPeriod.vmTick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vmTick

end PalPeg.ChainStoredPeriod
