import PalPeg.CanonicalSearchHistory
import PalPeg.PhysicalDpPreload

/-! # Every DP bank the search can retire is dense

A reset flips the DP bank at a prepare dispatch from `grow` or `double`, so
the retired tapes are whatever the search left there: a partial preload, a
halted or paused run, or an untouched bank. This module carries the density
of all twelve DP tapes along the actual search step. Run quanta extend the
executed history held by `ProgramInv`; `wait` and `double` keep the program. -/
set_option autoImplicit false
namespace PalPeg.PhysicalDpHistory
open PalPeg GalilScaffoldChainInputSupply GalilScaffoldCounter
open GalilScaffoldSearchRun GalilBranchInvariants2 CanonicalSearchProgram
open PalPeg.PhysicalEncoding (encTape)
open PalPeg.PhysicalProgramErase (Dense)

theorem safeCalls_run {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : SafeCalls s x bs t y) : ∃ cs, GalilScaffoldControl.Run GalilDpCode.code x cs y := by
  induction hr with
  | nil => exact ⟨[],.nil _⟩
  | cons s x y z b bs t ht _ _ ih =>
    obtain ⟨cs,hcs⟩ := ih
    exact ⟨_,.cons _ _ _ _ _ ht hcs⟩

theorem safeQuanta_run {s t : GalilScaffoldSearchFinish.State}
    {x y : GalilScaffoldControl.Machine 12} {as : List Bool}
    (hr : SafeQuanta s x as t y) : ∃ cs, GalilScaffoldControl.Run GalilDpCode.code x cs y := by
  induction hr with
  | nil => exact ⟨[],.nil _⟩
  | cons s u t x y z a as _ hq _ ih =>
    obtain ⟨cs,hcs⟩ := safeCalls_run hq
    obtain ⟨ds,hds⟩ := ih
    exact ⟨_,GalilScaffoldControl.run_append hcs hds⟩

theorem dense_of_reached {w : List (Fin 3)} {lower : ℕ}
    {s0 s : GalilScaffoldSearchFinish.State} {bs : List Bool}
    {x : GalilScaffoldControl.Machine 12} (h : DpReached w lower s0 bs s x) :
    ∀ i, Dense (encTape (x.config.tapes i)) := by
  obtain ⟨cs,hcs⟩ := safeQuanta_run h
  exact PalPeg.PhysicalDpDensity.dense_onRun w lower hcs

theorem dense_of_inv {x : GalilScaffoldPrepareControl.State} (h : PalPeg.PhysicalDpPreload.Inv x) :
    ∀ i, Dense (encTape (x.program.config.tapes i)) := by
  intro i
  obtain ⟨n,hn⟩ := h.solid i
  exact PalPeg.PhysicalDpDensity.dense_of_shape _ n hn

/-- Dense DP tapes, and the loading shape while a preparation is running. -/
structure DpHistory (v : SearchVM) : Prop where
  dense : ∀ i, Dense (encTape (v.dp.config.tapes i))
  prep : Preparing v.search.mode → PalPeg.PhysicalDpPreload.Inv v.toPrep

theorem dpHistory_begin (v : SearchVM) (lower : ℕ) (rad : Counter)
    (hd : ∀ i, Dense (encTape (v.dp.config.tapes i))) :
    DpHistory ({ v with search := GalilScaffoldSearchFinish.begin (ofNat lower) rad, lower := ofNat lower }) :=
  ⟨hd,by simp [Preparing,GalilScaffoldSearchFinish.begin]⟩

private theorem dpHistory_ofPrep (p : GalilScaffoldPrepareControl.State) (q : Fin 4)
    (l : Counter) (a : Bool) (h : PalPeg.PhysicalDpPreload.Inv p) :
    DpHistory (SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a p) q l) := by
  have h' : PalPeg.PhysicalDpPreload.Inv (GalilScaffoldPreparePaced.afterAdvance a p) := by
    cases a
    · exact h
    · exact ⟨h.solid,h.lower,h.untouched,h.source⟩
  exact ⟨dense_of_inv h',fun _ => h'⟩

/-- The search step keeps every DP tape dense, whichever mode it is in. -/
theorem dpHistory_step {p : GalilScaffoldPlace.Place} {lower : ℕ} {v v' : SearchVM} {a : Bool}
    (hprogram : ProgramInv p lower v) (hh : DpHistory v) (ht : searchStep p a v v') :
    DpHistory v' := by
  cases hm : v.search.mode with
  | idle | found | missed => simp only [searchStep,hm] at ht; subst v'; exact hh
  | lower | lowerHome | copy | home =>
    simp only [searchStep,hm] at ht
    obtain ⟨u,hu,rfl⟩ := ht
    exact dpHistory_ofPrep u _ _ a
      (PalPeg.PhysicalDpPreload.tick_inv hu (hh.prep (by simp [Preparing,hm])))
  | run =>
    simp only [searchStep,hm] at ht
    obtain ⟨hq,_,_⟩ := ht
    obtain ⟨_,_,_,_,_,hr⟩ := hprogram.running hm
    refine ⟨dense_of_reached (dpReached_step hr hq),?_⟩
    have hexit := safe_quanta_exit hq (by simp [ExitMode,hm])
    intro hp
    rcases hp with hp|hp|hp|hp <;> simp_all [ExitMode]
  | grow =>
    simp only [searchStep,hm] at ht
    split at ht
    · subst v'
      refine ⟨?_,?_⟩
      · cases a <;> exact hh.dense
      · cases a <;> simp [Preparing,SearchVM.ofPrep,SearchVM.toPrep,
          GalilScaffoldStagePrepare.runState,GalilScaffoldPreparePaced.afterAdvance,
          GalilScaffoldStagePrepare.growStep,hm]
    · subst v'
      exact dpHistory_ofPrep _ _ _ a (PalPeg.PhysicalDpPreload.prepare_inv _ _ _)
  | double =>
    simp only [searchStep,hm] at ht
    split at ht
    · subst v'
      exact ⟨hh.dense,by cases a <;> simp [Preparing,advance,GalilScaffoldDouble.step,hm]⟩
    · subst v'
      exact dpHistory_ofPrep _ _ _ a (PalPeg.PhysicalDpPreload.prepare_inv _ _ _)
  | wait =>
    simp only [searchStep,hm] at ht
    subst v'
    refine ⟨hh.dense,?_⟩
    cases a <;> simp [Preparing,advance,GalilScaffoldDouble.waitStep,
      GalilScaffoldDouble.enter,hm] <;> split <;> simp_all

theorem dense_reset (entry : ℕ) (d : GalilScaffoldControl.Machine 12) (i : Fin 12) :
    Dense (encTape ((GalilScaffoldControl.reset entry d).config.tapes i)) :=
  ⟨[],1,by simp,rfl⟩

private theorem dpHistory_of_reset {v : SearchVM} {entry : ℕ} {d : GalilScaffoldControl.Machine 12}
    (hdp : v.dp = GalilScaffoldControl.reset entry d) (hm : v.search.mode = .grow) : DpHistory v :=
  ⟨by rw [hdp]; exact dense_reset entry d,by intro h; rcases h with h|h|h|h <;> simp_all⟩

private theorem dpHistory_congr {v v' : SearchVM} (h : DpHistory v)
    (hdp : v'.dp = v.dp) (hm : v'.search.mode = v.search.mode) : DpHistory v' := by
  obtain ⟨hd,hp⟩ := h
  cases v; cases v'
  simp only at hdp hm
  subst hdp
  refine ⟨hd,fun hq => ?_⟩
  have hi := hp (by simpa [hm] using hq)
  exact ⟨hi.solid,fun h => hi.lower (by simpa [SearchVM.toPrep,hm] using h),
    fun h => hi.untouched (by simpa [SearchVM.toPrep,hm] using h),
    fun h => hi.source (by simpa [SearchVM.toPrep,hm] using h)⟩

private theorem dpHistory_effect {P : Shared} {a : Bool} {s : GalilVM} {vq : SearchVM}
    (hprogram : s.chain = .idle → ∃ lower, ProgramInv (P.place s) lower (searchLens.get s))
    (hh : DpHistory (searchLens.get s)) (he : searchEffect P a s vq) : DpHistory vq := by
  rcases he with ⟨hidle,hs⟩ | ⟨_,rfl⟩
  · obtain ⟨lower,hi⟩ := hprogram hidle
    exact dpHistory_step hi hh hs
  · exact hh

section Trace
open GalilScaffoldTop GalilScaffoldController GalilRunSkeleton GalilInvPlus3
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

private theorem dpHistory_compare {raw : List (Fin 2)} {s t : GalilVM}
    (hprogram : s.chain = .idle → ∃ lower,
      ProgramInv ((PofC centre place entry raw).place s) lower (searchLens.get s))
    (hh : DpHistory (searchLens.get s))
    (hc : (galilFrameS (PofC centre place entry raw) q first).compare s t) :
    DpHistory (searchLens.get t) := by
  obtain ⟨vs,vq,a,_,_,_,hs,_,heq⟩ := hc
  have hget : searchLens.get t = vq := by
    rw [heq, afterBirth_searchGet]
    cases a <;> rfl
  rw [hget]
  exact dpHistory_effect hprogram hh hs

/-- Along every canonical tick, including restart, init and replayStart, the
DP bank that a reset could retire is dense. -/
theorem dpHistory_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (hi : CanonicalSearchHistory.AtState centre place entry raw x)
    (hh : DpHistory (searchLens.get x.vm))
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y) :
    DpHistory (searchLens.get y.vm) := by
  cases ht with
  | init c s t hm ht =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hs,_,hdp,_⟩ := ht
    exact dpHistory_of_reset hdp (by simp [searchLens,hs,GalilScaffoldSearchFinish.begin])
  | replayStart c s t o hm hr _ _ =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hs,_,hdp,_⟩ := hr
    exact dpHistory_of_reset hdp (by simp [searchLens,hs,GalilScaffoldSearchFinish.begin])
  | restart c s t hm hr =>
    obtain ⟨_,_,_,_,_,rfl⟩ := hr
    exact dpHistory_of_reset (d := s.dp) rfl (by simp [searchLens,GalilScaffoldSearchFinish.begin])
  | scan_wait c s t hm _ hb | scan_count c s t hm _ _ hb =>
    obtain ⟨-,-,-,-,-,-,-,-,-,-,-,hse⟩ := backgroundS_fields _ q first hb
    exact dpHistory_effect (hi.scan hm) hh hse
  | scan_match c s t u o hm _ _ hc _ hp _ =>
    have hget : searchLens.get u = searchLens.get t := by rw [hp]; split <;> rfl
    rw [hget]
    exact dpHistory_compare centre place entry q first (hi.scan hm) hh hc
  | scan_shift c s t u hm _ _ hc _ _ _ hb =>
    obtain ⟨w,_,rfl⟩ := hb
    exact (dpHistory_compare centre place entry q first (hi.scan hm) hh hc :)
  | scan_fallback c s t u hm _ _ hc _ _ _ hb =>
    obtain ⟨p,rfl,_⟩ := hb
    have ht := dpHistory_compare centre place entry q first (hi.scan hm) hh hc
    exact ⟨ht.dense,by simp [Preparing,searchLens]⟩
  | shift_done => exact hh
  | shift_one c s t _ _ h | copy_one c s t _ _ h | copy_done c s t _ _ h
  | home_start c s t _ _ h | home_step c s t _ _ h | fpp_slice c s t _ h | fpp_done c s t _ h
  | markEnd_found c s t _ _ h | markEnd_step c s t _ _ h | choose_select c s t _ _ _ h
  | choose_step c s t _ _ h | rewind_done c s t _ _ h | rewind_one c s t _ _ _ h
  | rewind_pair c s t _ _ _ h =>
    obtain ⟨_,he⟩ := h
    rw [he]
    exact hh

theorem dpHistory_boot (w : List (Fin 2)) :
    DpHistory (searchLens.get (PalPeg.GalilFinalAssembly.boot w).vm) :=
  ⟨fun _ => ⟨[],1,by simp,rfl⟩,by
    simp [Preparing,searchLens,PalPeg.GalilFinalAssembly.boot,GalilBootVM.initVM0]⟩

/-- Along a pre-loaded trace whose ticks record their restart landings, every
state carries the search certificate and dense DP tapes. -/
theorem dpHistory_alongTrace {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : Decodes (PofC centre place entry w))
    (hpre : PalPeg.GalilFinalAssembly.PreTrace centre place entry q first w st Tc)
    (hticks : ∀ i, i < Tc w.length → PalPeg.ShapedRun.OracleTick entry w (st i) (st (i+1))) :
    ∀ i, i ≤ Tc w.length → CanonicalSearchHistory.AtState centre place entry w (st i) ∧
      DpHistory (searchLens.get (st i).vm) := by
  have h0 : CanonicalSearchHistory.AtState centre place entry w (st 0) ∧
      DpHistory (searchLens.get (st 0).vm) := by
    rw [hpre.start]
    refine ⟨⟨fun h => ?_,fun h => ?_⟩,dpHistory_boot w⟩ <;>
      simp [PalPeg.GalilFinalAssembly.boot,GalilScaffoldController.initial] at h
  exact hpre.trace.carried
    (Pk := fun x => CanonicalSearchHistory.AtState centre place entry w x ∧
      DpHistory (searchLens.get x.vm)) h0 fun i hi ht hx =>
    ⟨CanonicalSearchHistory.atState_tick centre place entry q first hP hx.1 ht
        (fun hm hr => (hticks i hi).restartStage hm hr),
      dpHistory_tick centre place entry q first hx.1 hx.2 ht⟩

end Trace

/-- info: 'PalPeg.PhysicalDpHistory.dpHistory_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dpHistory_step

end PalPeg.PhysicalDpHistory
