import PalPeg.GalilScaffoldTop

/-!
# One controller tick as a function of the state

`GalilScaffoldTop.Tick` is a relation: its guards can fail (a left move at the left edge, a
`read` whose dispatch table has no entry for the symbol under the head), so a state need not
have a successor, and three of the frame's relations (`init`, `beginFallback`, `replayStart`)
admit several.  A machine, on the other hand, computes: it needs one value per state.

This file closes that gap in the direction a simulation needs.  `FrameFun` is the frame with
functions and Boolean tests in place of relations and predicates, `Computes F G t` says the
functions compute the relations (the three open ones only at the target `t`), and `tickFun`
runs the controller on them.  `tick_eq_tickFun` then reads: **whenever the relation has a
successor, it is the value of the function.**  The existence comes from elsewhere (a run), the
value from the machine, and the equation from the two together, with the restart of a broken
chain given priority exactly as `GalilTickFair.Canonical.restartFirst` prescribes.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldTop
open GalilScaffoldController

/-- the VM-side effects of the controller steps as functions and tests. -/
structure FrameFun (σ : Type) where
  init : σ → σ
  available : σ → Bool
  background : σ → σ
  compare : σ → σ
  matched : σ → Bool
  shiftGuard : σ → Bool
  matchedPlace : Bool → σ → σ
  onLetter : σ → Bool
  leftFirst : σ → Bool
  beginShift : σ → σ
  beginFallback : σ → σ
  remainingPos : σ → Bool
  shiftOne : σ → σ
  copyOne : σ → σ
  copyEnd : σ → σ
  atLeft : σ → Bool
  fppStart : σ → σ
  homeStep : σ → σ
  fppHalts : σ → Bool
  fppSlice : σ → σ
  fppDone : σ → σ
  atEnd : σ → Bool
  markBack : σ → σ
  markForward : σ → σ
  markSet : σ → Bool
  choose : σ → σ
  atFirst : σ → Bool
  fppReset : σ → σ
  rewindOne : σ → σ
  rewindPair : σ → σ
  replayStart : σ → σ
  restartGuard : σ → Bool
  restart : σ → σ

variable {σ : Type}

/-- the functions compute the relations of the frame.  The three relations the frame
leaves open (`init`, `beginFallback`, `replayStart`) are asked for the target `t` only. -/
structure Computes (F : Frame σ) (G : FrameFun σ) (t : σ) : Prop where
  init : ∀ s, F.init s t → t = G.init s
  available : ∀ s, F.available s ↔ G.available s = true
  background : ∀ s s', F.background s s' → s' = G.background s
  compare : ∀ s s', F.compare s s' → s' = G.compare s
  matched : ∀ s, F.matched s ↔ G.matched s = true
  shiftGuard : ∀ s, F.shiftGuard s ↔ G.shiftGuard s = true
  matchedPlace : ∀ b s s', F.matchedPlace b s s' → s' = G.matchedPlace b s
  onLetter : ∀ s, F.onLetter s ↔ G.onLetter s = true
  leftFirst : ∀ s, F.leftFirst s ↔ G.leftFirst s = true
  beginShift : ∀ s s', F.beginShift s s' → s' = G.beginShift s
  beginFallback : ∀ s, F.beginFallback s t → t = G.beginFallback s
  remainingPos : ∀ s, F.remainingPos s ↔ G.remainingPos s = true
  shiftOne : ∀ s s', F.shiftOne s s' → s' = G.shiftOne s
  copyOne : ∀ s s', F.copyOne s s' → s' = G.copyOne s
  copyEnd : ∀ s s', F.copyEnd s s' → s' = G.copyEnd s
  atLeft : ∀ s, F.atLeft s ↔ G.atLeft s = true
  fppStart : ∀ s s', F.fppStart s s' → s' = G.fppStart s
  homeStep : ∀ s s', F.homeStep s s' → s' = G.homeStep s
  fppSlice : ∀ s s', F.fppSlice s s' → G.fppHalts s = false ∧ s' = G.fppSlice s
  fppDone : ∀ s s', F.fppDone s s' → G.fppHalts s = true ∧ s' = G.fppDone s
  atEnd : ∀ s, F.atEnd s ↔ G.atEnd s = true
  markBack : ∀ s s', F.markBack s s' → s' = G.markBack s
  markForward : ∀ s s', F.markForward s s' → s' = G.markForward s
  markSet : ∀ s, F.markSet s ↔ G.markSet s = true
  choose : ∀ s s', F.choose s s' → s' = G.choose s
  atFirst : ∀ s, F.atFirst s ↔ G.atFirst s = true
  fppReset : ∀ s s', F.fppReset s s' → s' = G.fppReset s
  rewindOne : ∀ s s', F.rewindOne s s' → s' = G.rewindOne s
  rewindPair : ∀ s s', F.rewindPair s s' → s' = G.rewindPair s
  replayStart : ∀ s, F.replayStart s t → t = G.replayStart s
  restart : ∀ s s', F.restart s s' → G.restartGuard s = true ∧ s' = G.restart s

/-- the output refresh, as a function. -/
def refreshFun (G : FrameFun σ) (s : σ) (old : Bool) : Bool :=
  if G.onLetter s then G.leftFirst s else old

theorem refresh_eq_refreshFun {F : Frame σ} {G : FrameFun σ} {t : σ}
    (hG : Computes F G t) {s : σ} {old o : Bool} (h : refresh F s old o) :
    o = refreshFun G s old := by
  unfold refreshFun
  by_cases hletter : G.onLetter s = true
  · rw [if_pos hletter]
    have hiff := h.1 ((hG.onLetter s).mpr hletter)
    rw [hG.leftFirst s] at hiff
    cases o <;> cases hfirst : G.leftFirst s <;> simp_all
  · rw [if_neg hletter]
    exact h.2 (fun hon => hletter ((hG.onLetter s).mp hon))

/-- **one controller tick, as a function of the state.**  The restart of a broken chain
comes first (the scheduling policy of `GalilTickFair.Canonical`). -/
def tickFun (G : FrameFun σ) (F : Frame σ) (delay : ℕ) (x : State σ) : State σ :=
  match x.ctl.mode with
  | .init => ⟨{x.ctl with mode := .scan, output := true}, G.init x.vm⟩
  | .scan =>
      if G.restartGuard x.vm then ⟨{x.ctl with clock := delay}, G.restart x.vm⟩
      else if !x.ctl.replaying && !G.available x.vm then ⟨x.ctl, G.background x.vm⟩
      else if 1 < x.ctl.clock then ⟨{x.ctl with clock := x.ctl.clock - 1}, G.background x.vm⟩
      else if G.matched (G.compare x.vm) then
        ⟨{x.ctl with clock := delay, output := refreshFun G (G.matchedPlace x.ctl.replaying (G.compare x.vm)) x.ctl.output, replaying := x.ctl.replaying && !F.replayExhausted (G.matchedPlace x.ctl.replaying (G.compare x.vm))}, G.matchedPlace x.ctl.replaying (G.compare x.vm)⟩
      else if G.shiftGuard (G.compare x.vm) then
        ⟨{x.ctl with clock := delay, mode := .shift}, G.beginShift (G.compare x.vm)⟩
      else ⟨{x.ctl with clock := delay, mode := .copy}, G.beginFallback (G.compare x.vm)⟩
  | .shift =>
      if G.remainingPos x.vm then ⟨x.ctl, G.shiftOne x.vm⟩
      else ⟨{x.ctl with mode := .scan, output := refreshFun G x.vm x.ctl.output}, x.vm⟩
  | .copy =>
      if G.remainingPos x.vm then ⟨x.ctl, G.copyOne x.vm⟩
      else ⟨{x.ctl with mode := .home}, G.copyEnd x.vm⟩
  | .home =>
      if G.atLeft x.vm then ⟨{x.ctl with mode := .fpp}, G.fppStart x.vm⟩
      else ⟨x.ctl, G.homeStep x.vm⟩
  | .fpp =>
      if G.fppHalts x.vm then ⟨{x.ctl with mode := .markEnd}, G.fppDone x.vm⟩
      else ⟨x.ctl, G.fppSlice x.vm⟩
  | .markEnd =>
      if G.atEnd x.vm then ⟨{x.ctl with mode := .choose, odd := false}, G.markBack x.vm⟩
      else ⟨x.ctl, G.markForward x.vm⟩
  | .choose =>
      if x.ctl.odd && G.markSet x.vm then
        ⟨{x.ctl with mode := .rewind, pair := false}, G.choose x.vm⟩
      else ⟨{x.ctl with odd := !x.ctl.odd}, G.markBack x.vm⟩
  | .rewind =>
      if G.atFirst x.vm then ⟨{x.ctl with mode := .replayStart}, G.fppReset x.vm⟩
      else if x.ctl.pair then ⟨{x.ctl with pair := false}, G.rewindPair x.vm⟩
      else ⟨{x.ctl with pair := true}, G.rewindOne x.vm⟩
  | .replayStart =>
      ⟨{x.ctl with mode := .scan, clock := delay, output := (if F.replayPos (G.replayStart x.vm) then x.ctl.output else refreshFun G (G.replayStart x.vm) x.ctl.output), replaying := F.replayPos (G.replayStart x.vm)}, G.replayStart x.vm⟩

#print axioms refresh_eq_refreshFun

theorem bool_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- **a tick of the frame is the value of the tick function**, when the functions compute
the frame at the target and the restart of a broken chain comes first. -/
theorem tick_eq_tickFun {F : Frame σ} {G : FrameFun σ} {delay : ℕ} {x y : State σ}
    (hG : Computes F G y.vm) (h : Tick F delay x y)
    (hrestartFirst : x.ctl.mode = .scan → G.restartGuard x.vm = true →
      y = ⟨{x.ctl with clock := delay}, G.restart x.vm⟩) :
    y = tickFun G F delay x := by
  cases h with
  | init c s s' hm hinit =>
    have hvalue : s' = G.init s := hG.init s hinit
    simp only [tickFun, hm, hvalue]
  | scan_wait c s s' hm hwait hb =>
    have hvalue : s' = G.background s := hG.background s s' hb
    by_cases hguard : G.restartGuard s = true
    · rw [hrestartFirst hm hguard]
      simp only [tickFun, hm, hguard, if_true]
    · have havailable : G.available s = false :=
        bool_ne_true (fun ha => hwait.2 ((hG.available s).mpr ha))
      simp only [tickFun, hm, bool_ne_true hguard, hwait.1, havailable, hvalue,
        Bool.false_eq_true, if_false, Bool.not_false, Bool.and_self, if_true]
  | scan_count c s s' hm hready hc hb =>
    have hvalue : s' = G.background s := hG.background s s' hb
    by_cases hguard : G.restartGuard s = true
    · rw [hrestartFirst hm hguard]
      simp only [tickFun, hm, hguard, if_true]
    · have hnotWait : (!c.replaying && !G.available s) = false := by
        rcases hready with hrep | hav
        · rw [hrep]; rfl
        · rw [(hG.available s).mp hav]; simp
      simp only [tickFun, hm, bool_ne_true hguard, hnotWait, hvalue, Bool.false_eq_true, if_false,
        if_pos hc]
  | scan_match c s s' s'' o hm hready hc hcmp hmt hpl ho =>
    by_cases hguard : G.restartGuard s = true
    · rw [hrestartFirst hm hguard]
      simp only [tickFun, hm, hguard, if_true]
    · have hnotWait : (!c.replaying && !G.available s) = false := by
        rcases hready with hrep | hav
        · rw [hrep]; rfl
        · rw [(hG.available s).mp hav]; simp
      have hclock : ¬ 1 < c.clock := by omega
      have hcompare : s' = G.compare s := hG.compare s s' hcmp
      subst hcompare
      have hplace : s'' = G.matchedPlace c.replaying (G.compare s) :=
        hG.matchedPlace c.replaying _ s'' hpl
      subst hplace
      have hmatched : G.matched (G.compare s) = true := (hG.matched _).mp hmt
      have houtput := refresh_eq_refreshFun hG ho
      simp only [tickFun, hm, bool_ne_true hguard, hnotWait, hmatched, houtput,
        Bool.false_eq_true, if_false, if_neg hclock, if_true]
  | scan_shift c s s' s'' hm hready hc hcmp hmt hr hg hb =>
    by_cases hguard : G.restartGuard s = true
    · rw [hrestartFirst hm hguard]
      simp only [tickFun, hm, hguard, if_true]
    · have hnotWait : (!c.replaying && !G.available s) = false := by
        rcases hready with hrep | hav
        · rw [hr] at hrep; exact absurd hrep (by decide)
        · rw [(hG.available s).mp hav]; simp
      have hclock : ¬ 1 < c.clock := by omega
      have hcompare : s' = G.compare s := hG.compare s s' hcmp
      subst hcompare
      have hmatched : G.matched (G.compare s) = false :=
        bool_ne_true (fun hm' => hmt ((hG.matched _).mpr hm'))
      have hshift : G.shiftGuard (G.compare s) = true := (hG.shiftGuard _).mp hg
      have hvalue : s'' = G.beginShift (G.compare s) := hG.beginShift _ s'' hb
      simp only [tickFun, hm, bool_ne_true hguard, hnotWait, hmatched, hshift, hvalue,
        Bool.false_eq_true, if_false, if_neg hclock, if_true]
  | scan_fallback c s s' s'' hm hready hc hcmp hmt hg hr hb =>
    by_cases hguard : G.restartGuard s = true
    · rw [hrestartFirst hm hguard]
      simp only [tickFun, hm, hguard, if_true]
    · have hnotWait : (!c.replaying && !G.available s) = false := by
        rcases hready with hrep | hav
        · rw [hr] at hrep; exact absurd hrep (by decide)
        · rw [(hG.available s).mp hav]; simp
      have hclock : ¬ 1 < c.clock := by omega
      have hcompare : s' = G.compare s := hG.compare s s' hcmp
      subst hcompare
      have hmatched : G.matched (G.compare s) = false :=
        bool_ne_true (fun hm' => hmt ((hG.matched _).mpr hm'))
      have hnoShift : G.shiftGuard (G.compare s) = false := by
        refine bool_ne_true (fun hs => ?_)
        rcases hg with hrep | hng
        · rw [hr] at hrep; exact absurd hrep (by decide)
        · exact hng ((hG.shiftGuard _).mpr hs)
      have hvalue : s'' = G.beginFallback (G.compare s) := hG.beginFallback _ hb
      simp only [tickFun, hm, bool_ne_true hguard, hnotWait, hmatched, hnoShift, hvalue,
        Bool.false_eq_true, if_false, if_neg hclock]
  | shift_one c s s' hm hp hstep =>
    have hvalue : s' = G.shiftOne s := hG.shiftOne s s' hstep
    simp only [tickFun, hm, (hG.remainingPos s).mp hp, hvalue, if_true]
  | shift_done c s o hm hp ho =>
    have hnot : G.remainingPos s = false :=
      bool_ne_true (fun h' => hp ((hG.remainingPos s).mpr h'))
    simp only [tickFun, hm, hnot, refresh_eq_refreshFun hG ho, Bool.false_eq_true, if_false]
  | copy_one c s s' hm hp hstep =>
    have hvalue : s' = G.copyOne s := hG.copyOne s s' hstep
    simp only [tickFun, hm, (hG.remainingPos s).mp hp, hvalue, if_true]
  | copy_done c s s' hm hp hstep =>
    have hnot : G.remainingPos s = false :=
      bool_ne_true (fun h' => hp ((hG.remainingPos s).mpr h'))
    have hvalue : s' = G.copyEnd s := hG.copyEnd s s' hstep
    simp only [tickFun, hm, hnot, hvalue, Bool.false_eq_true, if_false]
  | home_start c s s' hm hl hstep =>
    have hvalue : s' = G.fppStart s := hG.fppStart s s' hstep
    simp only [tickFun, hm, (hG.atLeft s).mp hl, hvalue, if_true]
  | home_step c s s' hm hl hstep =>
    have hnot : G.atLeft s = false := bool_ne_true (fun h' => hl ((hG.atLeft s).mpr h'))
    have hvalue : s' = G.homeStep s := hG.homeStep s s' hstep
    simp only [tickFun, hm, hnot, hvalue, Bool.false_eq_true, if_false]
  | fpp_slice c s s' hm hstep =>
    obtain ⟨hhalts, hvalue⟩ := hG.fppSlice s s' hstep
    simp only [tickFun, hm, hhalts, hvalue, Bool.false_eq_true, if_false]
  | fpp_done c s s' hm hstep =>
    obtain ⟨hhalts, hvalue⟩ := hG.fppDone s s' hstep
    simp only [tickFun, hm, hhalts, hvalue, if_true]
  | markEnd_found c s s' hm he hstep =>
    have hvalue : s' = G.markBack s := hG.markBack s s' hstep
    simp only [tickFun, hm, (hG.atEnd s).mp he, hvalue, if_true]
  | markEnd_step c s s' hm he hstep =>
    have hnot : G.atEnd s = false := bool_ne_true (fun h' => he ((hG.atEnd s).mpr h'))
    have hvalue : s' = G.markForward s := hG.markForward s s' hstep
    simp only [tickFun, hm, hnot, hvalue, Bool.false_eq_true, if_false]
  | choose_select c s s' hm ho hs hstep =>
    have hvalue : s' = G.choose s := hG.choose s s' hstep
    simp only [tickFun, hm, ho, (hG.markSet s).mp hs, hvalue, Bool.and_self, if_true]
  | choose_step c s s' hm hs hstep =>
    have hnot : (c.odd && G.markSet s) = false := by
      rcases hs with heven | hnotSet
      · rw [heven]; rfl
      · rw [bool_ne_true (fun h' => hnotSet ((hG.markSet s).mpr h'))]; simp
    have hvalue : s' = G.markBack s := hG.markBack s s' hstep
    simp only [tickFun, hm, hnot, hvalue, Bool.false_eq_true, if_false]
  | rewind_done c s s' hm hf hstep =>
    have hvalue : s' = G.fppReset s := hG.fppReset s s' hstep
    simp only [tickFun, hm, (hG.atFirst s).mp hf, hvalue, if_true]
  | rewind_one c s s' hm hf hp hstep =>
    have hnot : G.atFirst s = false := bool_ne_true (fun h' => hf ((hG.atFirst s).mpr h'))
    have hvalue : s' = G.rewindOne s := hG.rewindOne s s' hstep
    simp only [tickFun, hm, hnot, hp, hvalue, Bool.false_eq_true, if_false]
  | rewind_pair c s s' hm hf hp hstep =>
    have hnot : G.atFirst s = false := bool_ne_true (fun h' => hf ((hG.atFirst s).mpr h'))
    have hvalue : s' = G.rewindPair s := hG.rewindPair s s' hstep
    simp only [tickFun, hm, hnot, hp, hvalue, Bool.false_eq_true, if_false, if_true]
  | replayStart c s s' o hm hstep hpos hneg =>
    have hvalue : s' = G.replayStart s := hG.replayStart s hstep
    have houtput : o = (if F.replayPos s' then c.output else refreshFun G s' c.output) := by
      by_cases hp : F.replayPos s' = true
      · rw [if_pos hp]; exact hpos hp
      · rw [if_neg hp]
        exact refresh_eq_refreshFun hG (hneg (bool_ne_true hp))
    simp only [tickFun, hm, ← hvalue, houtput]
  | restart c s s' hm hb =>
    obtain ⟨hguard, hvalue⟩ := hG.restart s s' hb
    rw [hrestartFirst hm hguard]
    simp only [tickFun, hm, hguard, if_true]

#print axioms tick_eq_tickFun

end PalPeg.GalilScaffoldTop
