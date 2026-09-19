import PalPeg.CanonicalSearchProgram
import PalPeg.ShapedRun
import PalPeg.GalilLeafDp

/-! # The actual search program along a finite canonical run

The certificate is reset at init/replayStart, transported through idle-chain
scan ticks, and unused while a chain is active.  This connects the DP result
to the chain birth in `OracleReady` without a completed trace.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PalPeg.CanonicalSearchHistory
open PalPeg GalilScaffoldTop GalilScaffoldController GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilRunSkeleton GalilInvPlus3 CanonicalSearchProgram

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

structure AtState (raw : List (Fin 2)) (x : State GalilVM) : Prop where
  scan : x.ctl.mode = .scan → x.vm.chain = .idle →
    ∃ lower, ProgramInv ((PofC centre place entry raw).place x.vm) lower (searchLens.get x.vm)
  shift : x.ctl.mode = .shift → x.vm.chain ≠ .idle

private theorem reset_program {p : GalilScaffoldPlace.Place} {v : SearchVM} {rad : Counter}
    (hl : v.lower = reset) (hs : v.search = GalilScaffoldSearchFinish.begin reset rad) :
    ProgramInv p 0 v := by
  have h := programInv_begin p v 0 rad
  have he : ({v with search := GalilScaffoldSearchFinish.begin (ofNat 0) rad, lower := ofNat 0}) = v := by
    cases v; simp_all [ofNat,reset]
  rwa [he] at h

private theorem idle_source {a found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {wk : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead} {rad : Counter}
    {x y : ChainVM} (h : chainAt a found ans cc wk ver rad x y) (hy : y = .idle) : x = .idle := by
  rcases h with ⟨hx,ht⟩ | ⟨hx,_,_⟩ | ⟨hx,_,_⟩
  · exact ((chainTick_ne_idle ht hx) hy).elim
  · exact hx
  · exact hx

private theorem background_program {raw : List (Fin 2)} {s t : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hi : s.chain = .idle → ∃ lower,
      ProgramInv ((PofC centre place entry raw).place s) lower (searchLens.get s))
    (hb : (galilFrameS (PofC centre place entry raw) q first).background s t)
    (hidle : t.chain = .idle) :
    ∃ lower, ProgramInv ((PofC centre place entry raw).place t) lower (searchLens.get t) := by
  obtain ⟨_,_,hs,hch,heq⟩ := hb
  have hi₀ := idle_source hch hidle
  obtain ⟨lower,hinv⟩ := hi hi₀
  have hstep : searchStep ((PofC centre place entry raw).place s) false
      (searchLens.get s) (searchLens.get t) := by
    rcases hs with ⟨_,hh⟩ | ⟨hn,_⟩
    · exact hh
    · exact (hn hi₀).elim
  have hcenter : t.center = s.center := by
    rw [heq, afterBirth_center]
    simp [searchLens, scanLens]
  rw [hP.2 t s hcenter]
  exact ⟨lower,programInv_step hinv hstep⟩

private theorem compare_program {raw : List (Fin 2)} {s t : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hi : s.chain = .idle → ∃ lower,
      ProgramInv ((PofC centre place entry raw).place s) lower (searchLens.get s))
    (hc : (galilFrameS (PofC centre place entry raw) q first).compare s t)
    (hidle : t.chain = .idle) :
    ∃ lower, ProgramInv ((PofC centre place entry raw).place t) lower (searchLens.get t) := by
  obtain ⟨vs,vq,a,_,_,_,hs,hch,heq⟩ := hc
  have hchain : t.chain = vs.chain := by rw [heq,afterBirth_chain]; cases a <;> rfl
  have hi₀ := idle_source hch (hchain.symm.trans hidle)
  obtain ⟨lower,hinv⟩ := hi hi₀
  have hstep : searchStep ((PofC centre place entry raw).place s) a (searchLens.get s) vq := by
    rcases hs with ⟨_,hh⟩ | ⟨hn,_⟩
    · exact hh
    · exact (hn hi₀).elim
  have hcenter : t.center = s.center := by rw [heq,afterBirth_center]; cases a <;> rfl
  have hget : searchLens.get t = vq := by
    rw [heq, afterBirth_searchGet]
    cases a <;> rfl
  rw [hget,hP.2 t s hcenter]
  exact ⟨lower,programInv_step hinv hstep⟩

private theorem atState_restart {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {rad : ℕ} {last : Counter} (hm : c.mode = .scan) (hr : Restarted raw s rad last) :
    AtState centre place entry raw ⟨c,s⟩ := by
  obtain ⟨_,_,_,_,_,_,hs,hl,hcan,hn⟩ := hr
  have he : last = ofNat (value last).toNat := by
    apply PalPeg.CloseoutPreload5.canonical_eq_ofNat hcan
    omega
  refine ⟨fun _ _ => ⟨(value last).toNat,?_⟩,
    fun h _ => by
      have hc : c.mode = .shift := by simpa using h
      rw [hm] at hc
      cases hc⟩
  have h := programInv_begin ((PofC centre place entry raw).place s) (searchLens.get s)
    (value last).toNat s.radius
  let w := searchLens.get s
  let b := GalilScaffoldSearchFinish.begin (ofNat (value last).toNat) s.radius
  have hv : ({w with search := b, lower := ofNat (value last).toNat}) = searchLens.get s := by
    dsimp [w,b]
    rw [← he]
    simp only [searchLens]
    rw [← hs, ← hl]
  rwa [hv] at h

/-- Every actual canonical tick transports the semantic search certificate. -/
theorem atState_tick {raw : List (Fin 2)} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hi : AtState centre place entry raw x)
    (ht : Tick (galilFrameS (PofC centre place entry raw) q first) 2048 x y)
    (hrestart : x.ctl.mode = .scan → restartVM entry x.vm y.vm →
      ∃ (Rad : ℕ) (last : Counter), Restarted raw y.vm Rad last ∧ StageEntry Rad last ∧
        y.ctl.mode = .scan ∧ y.ctl.clock = 2048) :
    AtState centre place entry raw y := by
  cases ht with
  | init c s t hm ht =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hs,hl,_⟩ := ht
    exact ⟨fun _ _ => ⟨0,reset_program hl hs⟩,fun h => by cases h⟩
  | scan_wait c s t hm _ hb | scan_count c s t hm _ _ hb =>
    exact ⟨fun _ => background_program centre place entry q first hP (hi.scan hm) hb,
      fun h => by simp_all⟩
  | scan_match c s t u o hm _ _ hc _ hp _ =>
    have hchain : u.chain = t.chain := by rw [hp]; split <;> rfl
    have hcenter : u.center = t.center := by rw [hp]; split <;> rfl
    have hget : searchLens.get u = searchLens.get t := by rw [hp]; split <;> rfl
    refine ⟨fun _ hidle => ?_,fun h => by simp_all⟩
    obtain ⟨lower,hinv⟩ := compare_program centre place entry q first hP (hi.scan hm) hc
      (hchain.symm.trans hidle)
    rw [hget,hP.2 u t hcenter]
    exact ⟨lower,hinv⟩
  | scan_shift c s t u hm _ _ _ _ _ _ hb =>
    obtain ⟨v,_,rfl⟩ := hb
    exact ⟨(fun hs _ => by simp_all), (fun _ h => by cases h)⟩
  | shift_one c s t hm _ ho =>
    obtain ⟨_,_,_,wv,hw,hget⟩ := ho.1
    have hset := ho.2
    rw [hget] at hset
    rw [hset]
    exact ⟨(fun _ _ => by contradiction), (fun _ h => by cases h)⟩
  | shift_done c s o hm _ _ =>
    exact ⟨fun _ hidle => (hi.shift hm hidle).elim,fun h => by cases h⟩
  | replayStart c s t o hm hr _ _ =>
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hs,hl,_⟩ := hr
    exact ⟨fun _ _ => ⟨0,reset_program hl hs⟩,fun h => by cases h⟩
  | restart c s t hm hr =>
    obtain ⟨Rad,last,hR,_,hmode,_⟩ := hrestart hm hr
    exact atState_restart centre place entry hmode hR
  | scan_fallback | copy_one | copy_done | home_start | home_step | fpp_slice | fpp_done
  | markEnd_step | markEnd_found | choose_select | choose_step | rewind_done | rewind_one | rewind_pair =>
    constructor
    · intro hs hi
      simp_all
    · intro hs h
      simp_all

theorem atState_shaped {raw : List (Fin 2)} {n : ℕ} {x y : State GalilVM}
    (hP : Decodes (PofC centre place entry raw)) (hi : AtState centre place entry raw x)
    (hr : ShapedRun.ShapedSteps centre place entry q first raw n x y) :
    AtState centre place entry raw y := by
  induction hr with
  | zero => exact hi
  | succ ht hnr _ _ ih => exact ih (atState_tick centre place entry q first hP hi ht hnr)

/-- The origin already records the search segment from its last restart. -/
theorem atState_invLPS {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hi : InvLPS (PofC centre place entry raw) q first raw c s) :
    AtState centre place entry raw ⟨c,s⟩ := by
  obtain ⟨r,rad,last,es,c₀,hr,_,_,hseg⟩ := hi.2
  have hm : c.mode = .scan := (PalPeg.GalilOracleLocal.invS_mode hi.1.1.1.1.1).1
  have hm₀ := ShapedRun.watchSegE_first_mode q first hseg hm
  obtain ⟨n,hshape⟩ := ShapedRun.watchSegE_shaped centre place entry q first hseg
  exact atState_shaped centre place entry q first hP
    (atState_restart centre place entry hm₀ hr) hshape

/-- The prefix is enough; the cycle oracle is not assumed. -/
theorem atState_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y) :
    AtState centre place entry raw y := by
  obtain ⟨g,h0,hk,ht,hcan,_⟩ := hr
  have hall : ∀ i, i ≤ k → AtState centre place entry raw (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact atState_invLPS centre place entry q first hP hI
    | succ i ih =>
      intro hn
      exact atState_tick centre place entry q first hP (ih (by omega))
        (ht.tick i (by omega)) (hcan i (by omega)).restartStage
  simpa only [hk] using hall k le_rfl

/-- BirthCopy, the final residue of chain readiness, now follows from its actual DP history. -/
theorem birthCopy_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) : CanonicalChainReady.BirthCopy centre place entry raw y.vm := by
  intro a vq hidle he hf
  obtain ⟨lower,hi⟩ := (atState_packed centre place entry q first hP hI hr).scan hm hidle
  have hs : searchStep ((PofC centre place entry raw).place y.vm) a (searchLens.get y.vm) vq := by
    rcases he with ⟨_,hh⟩ | ⟨hn,_⟩
    · exact hh
    · exact (hn hidle).elim
  exact programInv_found_copy (programInv_step hi hs) hf _

/-- At an idle-chain birth, expose the actual DP result that produced it. -/
theorem birthResult_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) {a : Bool} {vq : SearchVM}
    (hidle : y.vm.chain = .idle)
    (he : searchEffect (PofC centre place entry raw) a y.vm vq)
    (hf : vq.search.mode = .found) :
    ∃ lower span, vq.lower = ofNat lower ∧
      GalilDpCorrect.Result
        ((GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).take (span+1))
        lower 0 (GalilScaffoldProgram.denote vq.dp.config) := by
  obtain ⟨lower,hi⟩ := (atState_packed centre place entry q first hP hI hr).scan hm hidle
  have hs : searchStep ((PofC centre place entry raw).place y.vm) a
      (searchLens.get y.vm) vq := by
    rcases he with ⟨_,hh⟩ | ⟨hn,_⟩
    · exact hh
    · exact (hn hidle).elim
  have hi' := programInv_step hi hs
  obtain ⟨span,hres⟩ := programInv_found_result hi' hf
  exact ⟨lower,span,hi'.lower_eq,hres⟩

/-- An idle-chain comparison that parks the search in `missed` retains the
actual completed DP result; no future-fuel premise is involved. -/
theorem missedResult_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) {a : Bool} {vq : SearchVM}
    (hidle : y.vm.chain = .idle)
    (he : searchEffect (PofC centre place entry raw) a y.vm vq)
    (hmiss : vq.search.mode = .missed) :
    ∃ lower span, vq.lower = ofNat lower ∧
      (GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).length ≤ span+1 ∧
      GalilDpCorrect.Result
        ((GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).take (span+1))
        lower 0 (GalilScaffoldProgram.denote vq.dp.config) ∧
      (GalilScaffoldProgram.denote vq.dp.config).pc = 347 := by
  obtain ⟨lower,hi⟩ := (atState_packed centre place entry q first hP hI hr).scan hm hidle
  have hs : searchStep ((PofC centre place entry raw).place y.vm) a
      (searchLens.get y.vm) vq := by
    rcases he with ⟨_,hh⟩ | ⟨hn,_⟩
    · exact hh
    · exact (hn hidle).elim
  have hi' := programInv_step hi hs
  obtain ⟨span,hfull,hres,hpc⟩ := programInv_missed_result hi' hmiss
  exact ⟨lower,span,hi'.lower_eq,hfull,hres,hpc⟩

/-- The parked final miss supplies the whole mismatch DP pack once the
already-searched lower interval is supplied by the chain history. -/
theorem dpPack_of_idle_missed_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) {Rad : ℕ}
    (hscan : ScanInvariant raw (position y.vm.center) Rad y.vm.left y.vm.right)
    (hcen : PalPeg.GalilInvPlus2.CentreRep raw y.vm) {a : Bool} {vq : SearchVM}
    (hidle : y.vm.chain = .idle)
    (he : searchEffect (PofC centre place entry raw) a y.vm vq)
    (hmiss : vq.search.mode = .missed)
    (hlow : ∀ δ, 0 < δ → δ ≤ (value vq.lower).toNat →
      ¬ HasPeriod (Span raw (position y.vm.center) Rad) (2*δ)) :
    PalPeg.GalilLeafMismatch.DpPack raw y.vm Rad := by
  obtain ⟨lower,span,hlower,hfull,hres,hpc⟩ :=
    missedResult_packed centre place entry q first hP hI hr hm hidle he hmiss
  obtain ⟨a₀,ls₀,rs₀,q₀,hdec,hraw⟩ :=
    represents_decompose y.vm.center raw hcen.1 hcen.2
  obtain ⟨_,hplace⟩ := hP.1 y.vm a₀ ls₀ rs₀ q₀ y.vm.center.gap hdec
  have hstream :
      (GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).length =
        position y.vm.center := by
    rw [hplace]
    exact stream_length_of_place a₀ ls₀ rs₀ q₀ hdec
  have hspan : Rad ≤ span := by
    rw [hstream] at hfull
    have := scan_radius_lt hscan
    omega
  refine ⟨a₀,ls₀,rs₀,q₀,y.vm.center.gap,lower,span,
    GalilScaffoldProgram.denote vq.dp.config,hraw,congrArg position hdec,hspan,?_,hpc,?_⟩
  · rw [← hplace]
    exact hres
  · intro δ hd hδ
    apply hlow δ hd
    rw [hlower,ofNat_value,Int.toNat_natCast]
    exact hδ

/-- The least-candidate certificate and copy invariant at an actual packed
chain birth, retained together for the chain semantic invariant. -/
theorem birthMinimal_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) {a : Bool} {vq : SearchVM}
    (hidle : y.vm.chain = .idle)
    (he : searchEffect (PofC centre place entry raw) a y.vm vq)
    (hf : vq.search.mode = .found) :
    ∃ lower span h, vq.lower = ofNat lower ∧
      GalilDpCorrect.Result
        ((GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).take (span+1))
        lower 0 (GalilScaffoldProgram.denote vq.dp.config) ∧
      GalilDpCorrect.Candidate
        ((GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).take (span+1))
        lower h ∧
      (∀ g, g < h → ¬ GalilDpCorrect.Candidate
        ((GalilScaffoldPlace.stream ((PofC centre place entry raw).place y.vm)).take (span+1))
        lower g) ∧
      GalilBranchInvariants.CopyInv (vq.dp.config.tapes 11) reset
        ((PofC centre place entry raw).place y.vm)
        (GalilScaffoldChainPeriod.start ((PofC centre place entry raw).centre y.vm)) h := by
  obtain ⟨lower,hi⟩ := (atState_packed centre place entry q first hP hI hr).scan hm hidle
  have hs : searchStep ((PofC centre place entry raw).place y.vm) a
      (searchLens.get y.vm) vq := by
    rcases he with ⟨_,hh⟩ | ⟨hn,_⟩
    · exact hh
    · exact (hn hidle).elim
  have hi' := programInv_step hi hs
  obtain ⟨span,h,hres,hcand,hmin,hcopy⟩ :=
    programInv_found_birth hi' hf ((PofC centre place entry raw).centre y.vm)
  exact ⟨lower,span,h,hi'.lower_eq,hres,hcand,hmin,hcopy⟩

/-- On the booted (`lower = 0`) run, an actual birth installs both the copy
datum and the future minimal-period certificate at its birth centre. -/
theorem birthMinimals_packed {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hP : Decodes (PofC centre place entry raw))
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {y : State GalilVM}
    (hr : CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ y)
    (hm : y.ctl.mode = .scan) {a : Bool} {vq : SearchVM}
    (hidle : y.vm.chain = .idle)
    (he : searchEffect (PofC centre place entry raw) a y.vm vq)
    (hf : vq.search.mode = .found)
    (hexcluded : ∀ lower, vq.lower = ofNat lower →
      LowerExcluded raw (position y.vm.center) lower) :
    ∃ h,
      GalilBranchInvariants.CopyInv (vq.dp.config.tapes 11) reset
        ((PofC centre place entry raw).place y.vm)
        (GalilScaffoldChainPeriod.start ((PofC centre place entry raw).centre y.vm)) h ∧
      FutureMinimal raw (position y.vm.center) h ∧
      MoveAbove raw (position y.vm.center) (value vq.lower).toNat h := by
  obtain ⟨lower,span,h,hlower,hres,hcand,hmin,hcopy⟩ :=
    birthMinimal_packed centre place entry q first hP hI hr hm hidle he hf
  have hexcludedLower := hexcluded lower hlower
  have hp := PalPeg.CloseoutCheckW.ipackMW_last_of_stepsIMWC centre place entry q first hr
  have hcen := (hp.win hP).centreRep (Or.inl hm)
  obtain ⟨a,ls,rs,suffix,hdec,hraw⟩ :=
    represents_decompose y.vm.center raw hcen.1 hcen.2
  obtain ⟨_,hplace⟩ := hP.1 y.vm a ls rs suffix y.vm.center.gap hdec
  refine ⟨h,hcopy,?_,?_⟩
  rw [hraw]
  apply futureMinimal_of_candidate a ls rs suffix y.vm.center.gap
    (congrArg position hdec)
  · rw [← hplace]
    exact hcand
  · intro g hg
    rw [← hplace]
    exact hmin g hg
  · rw [← hraw]
    exact hexcludedLower
  · have hlowerNat : (value vq.lower).toNat = lower := by
      rw [hlower,ofNat_value,Int.toNat_natCast]
    rw [hraw,hlowerNat]
    apply moveAbove_of_candidate a ls rs suffix y.vm.center.gap
      (congrArg position hdec)
    · rw [← hplace]
      exact hcand
    · intro g hg
      rw [← hplace]
      exact hmin g hg

#print axioms birthCopy_packed
end PalPeg.CanonicalSearchHistory
