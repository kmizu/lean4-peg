import PalPeg.GalilScaffoldTopFoundLoop

/-!
# The fallback path on `galilFrameS`

The fallback phases (copy, home, fpp, markEnd, choose, rewind, replayStart)
never compare, so their ticks of `galilFrame` are ticks of `galilFrameS`
(`tick_S_of_tick`). The phase runs and their composition `fallback_to_scan`
are restated on `galilFrameS`, the frame of the main loop.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem steps_transfer_fallback_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .copy ∨ c.mode = .home) (hi : ShiftIdle s)
    (h : Steps (Frame.pull fppLens (fallbackFrame (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrameS P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic fppLens _ _ delay (fun m => m = .copy ∨ m = .home) (fun m => m = .fpp) ShiftIdle
    (fun ht hi => shiftIdle_fpp delay _ ht hi) (fun hm' ht => step_fallback _ delay hm' ht)
    (fun hm' ht => no_tick_fallback delay hm' ht)
    (fun hm' hi' ht => tick_S_of_tick P q first delay (fallback_transfer P q first delay _ _ hm' hi' ht)
      (by rcases hm' with h | h <;> rw [h] <;> decide)) n hm hi h

theorem steps_transfer_fpp_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .fpp) (hi : ShiftIdle s)
    (h : Steps (Frame.pull fppLens (fppFrame q first (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrameS P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic fppLens _ _ delay (fun m => m = .fpp) (fun m => m = .markEnd) ShiftIdle
    (fun ht hi => shiftIdle_fpp delay _ ht hi) (fun hm' ht => step_fpp _ delay hm' ht)
    (fun hm' ht => no_tick_fpp q first delay hm' ht)
    (fun hm' _ ht => tick_S_of_tick P q first delay (fpp_transfer P q first delay _ _ hm' ht)
      (by rw [hm']; decide)) n hm hi h

theorem steps_transfer_markEnd_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .markEnd) (hi : ShiftIdle s)
    (h : Steps (Frame.pull fppLens (marksFrame first (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrameS P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic' fppLens _ _ delay (fun m => m = .markEnd) (fun m => m = .choose) ShiftIdle
    (fun ht hi => shiftIdle_fpp delay _ ht hi) (fun hm' ht => step_markEnd _ delay hm' ht)
    (fun hm' ht => step_marks_choose first _ _ delay hm' ht)
    (fun hm' _ ht => by
      rcases hm' with hm' | hm'
      · exact tick_S_of_tick P q first delay (markEnd_transfer P q first delay _ _ hm' ht) (by rw [hm']; decide)
      · exact tick_S_of_tick P q first delay (marks_choose_transfer P q first delay _ _ hm' ht) (by rw [hm']; decide))
    n (Or.inl hm) hi h

theorem steps_transfer_rewind_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (n : ℕ)
    {c c' : Control} {s t : GalilVM} (hm : c.mode = .choose ∨ c.mode = .rewind) (hi : ShiftIdle s)
    (h : Steps (Frame.pull rewindLens (rewindFrame first (fun _ => True) (fun _ => True))) delay n ⟨c, s⟩ ⟨c', t⟩) :
    Steps (galilFrameS P q first) delay n ⟨c, s⟩ ⟨c', t⟩ ∧ ShiftIdle t :=
  steps_transfer_generic rewindLens _ _ delay (fun m => m = .choose ∨ m = .rewind) (fun m => m = .replayStart) ShiftIdle
    (fun ht hi => shiftIdle_rewind delay _ ht hi) (fun hm' ht => step_rewind _ delay hm' ht)
    (fun hm' ht => no_tick_rewind first delay hm' ht)
    (fun hm' _ ht => tick_S_of_tick P q first delay (rewind_transfer P q first delay _ _ hm' ht)
      (by rcases hm' with h | h <;> rw [h] <;> decide)) n hm hi h

theorem copy_home_start_S (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    ∃ t : FppControl.State,
      Steps (galilFrameS P q first) delay (2*w.length+3) ⟨c, s⟩ ⟨{c with mode := .fpp}, {s with fpp := t}⟩ ∧
      t.mode = .run ∧ t.program = ⟨fppInitial w, false⟩ ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream p).length ≤ ℓ+1) ∧
      ShiftIdle {s with fpp := t} := by
  intro w
  obtain ⟨t, hrun, hmode, hprog, hfin⟩ := FppControl.fallback_prepared old p length hc ℓ hv
  have hm' : c.mode = (FppControl.beginFallback old p length).mode.toController := by
    rw [hm]; rfl
  have hst := fpp_control_run_lift (fun _ => True) (fun _ => True) delay (2*w.length+3) c hm' hrun
  rw [hmode] at hst
  have hst' := steps_pull fppLens _ delay (2*w.length+3) c _ s t (by rw [show fppLens.get s = s.fpp from rfl, hs]; exact hst)
  obtain ⟨hg, hi'⟩ := steps_transfer_fallback_S P q first delay (2*w.length+3) (Or.inl hm) hi hst'
  exact ⟨t, hg, hmode, hprog, hfin, hi'⟩

/-- The whole fallback on the merged frame: from `copy` mode with the decoded
`beginFallback` state to `replayStart` mode, with L and C rewound to the
longest odd palindromic prefix of the reversed window (`r = chosenRadius w`),
`length = 2r+1`, `radius = r`, the FPP program reset. -/
theorem fpp_then_markEnd_S (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .fpp) (s : GalilVM) (hi : ShiftIdle s)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hw : 1 ≤ w.length)
    (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (y : FppControl.State),
      Steps (galilFrameS P q first) delay (n+1 + (w.length-1+1)) ⟨c, s⟩
        ⟨{c with mode := .choose, odd := false}, {s with fpp := y}⟩ ∧
      GalilScaffoldTape.denote (marksTape y) = Function.update (GalilFppMarkedLayout.marks w) 1 first ∧
      GalilScaffoldTape.head (marksTape y) = w.length ∧
      y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧ y.finalStage = s.fpp.finalStage ∧
      ShiftIdle {s with fpp := y} := by
  obtain ⟨v, hpc, hpos, ht7, ht8, hsched⟩ := fpp_scheduled w
  obtain ⟨n, p, y1, hs1, hprog, hmode, hwk, hwork, hfin, hd, hrun⟩ :=
    fpp_phase_vm q hq first (fun _ => True) (fun _ => True) delay c hm s hx w hp
  obtain ⟨hg1, hi1⟩ := steps_transfer_fpp_S P q first delay (n+1) hm hi hs1
  have hpv : p = ⟨v, true⟩ := fpp_outcome_program q w s.fpp hp v hsched n p hd hrun
  subst hpv
  obtain ⟨hden, hhead⟩ := marks_after_fpp first w v hpos ht8
  have hden1 : GalilScaffoldTape.denote (marksTape y1) = Function.update (GalilFppMarkedLayout.marks w) 1 first := by
    show GalilScaffoldTape.denote (y1.program.config.tapes 8) = _
    rw [hprog]; exact hden
  have hhead1 : GalilScaffoldTape.head (marksTape y1) = 2 := by
    show GalilScaffoldTape.head (y1.program.config.tapes 8) = 2
    rw [hprog]; exact hhead
  have hm1 : ({c with mode := .markEnd} : Control).mode = .markEnd := rfl
  have hne : ∀ j, j < w.length - 1 →
      GalilScaffoldTape.denote (marksTape ({s with fpp := y1} : GalilVM).fpp)
        (GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + j) ≠ 5 := by
    intro j hj
    show GalilScaffoldTape.denote (marksTape y1) (GalilScaffoldTape.head (marksTape y1) + j) ≠ 5
    rw [hden1, hhead1, Function.update_of_ne (by omega)]
    exact marks_no_end w (2+j) (by omega) (by omega)
  have hend : GalilScaffoldTape.denote (marksTape ({s with fpp := y1} : GalilVM).fpp)
      (GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + (w.length - 1)) = 5 := by
    show GalilScaffoldTape.denote (marksTape y1) (GalilScaffoldTape.head (marksTape y1) + (w.length - 1)) = 5
    rw [hden1, hhead1, Function.update_of_ne (by omega), show 2 + (w.length - 1) = w.length + 1 by omega]
    exact marks_end w
  have hpos' : 0 < GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + (w.length - 1) := by
    show 0 < GalilScaffoldTape.head (marksTape y1) + (w.length - 1)
    rw [hhead1]; omega
  obtain ⟨y2, hs2, hsame, hhead2⟩ := markEnd_phase_vm first (fun _ => True) (fun _ => True) delay
    {c with mode := .markEnd} hm1 {s with fpp := y1} (w.length - 1) hne hend hpos'
  obtain ⟨hg2, hi2⟩ := steps_transfer_markEnd_S P q first delay (w.length - 1 + 1) hm1 hi1 hs2
  refine ⟨n, y2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi2⟩
  · exact steps_trans hg1 hg2
  · rw [hsame.denote]; exact hden1
  · rw [hhead2]
    show GalilScaffoldTape.head (marksTape y1) + (w.length - 1) - 1 = w.length
    rw [hhead1]; omega
  · rw [hsame.mode]; exact hmode
  · rw [hsame.walker]; exact hwk
  · rw [hsame.work]; exact hwork
  · rw [hsame.finalStage]; exact hfin


theorem choose_then_rewind_S (P : Shared) (q : ℕ) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (delay : ℕ) (c : Control) (hm : c.mode = .choose) (ho : c.odd = false) (s : GalilVM) (hi : ShiftIdle s)
    (w : List (Fin 3)) (hw : 1 ≤ w.length) (heven : w.length % 2 = 0) (r : ℕ) (hr : r = chosenRadius w)
    (hden : GalilScaffoldTape.denote (marksTape s.fpp) = Function.update (GalilFppMarkedLayout.marks w) 1 first)
    (hhead : GalilScaffoldTape.head (marksTape s.fpp) = w.length) :
    ∃ y : RewindVM, Steps (galilFrameS P q first) delay ((w.length - (2*r+1) + 1) + (2*r + 1)) ⟨c, s⟩
        ⟨{c with mode := .replayStart, odd := oddAt c.odd (w.length - (2*r+1)), pair := pairAt (2*r)},
          rewindLens.set s y⟩ ∧
      y.left = GalilScaffoldInputHead.left^[2*r] s.right ∧
      y.center = GalilScaffoldInputHead.left^[r] s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat (2*r+1) ∧ y.radius = GalilScaffoldCounter.ofNat r ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program ∧ ShiftIdle (rewindLens.set s y) := by
  have hne : w ≠ [] := by intro h; rw [h] at hw; simp at hw
  have hspec := chosen_spec w hne
  rw [← hr] at hspec
  obtain ⟨hr1, hpal⟩ := hspec
  have hcell : ∀ i, 2 ≤ i → GalilScaffoldTape.denote (marksTape s.fpp) i = GalilFppMarkedLayout.marks w i := by
    intro i hi
    rw [hden, Function.update_of_ne (by omega)]
  have hcell1 : GalilScaffoldTape.denote (marksTape s.fpp) 1 = first := by
    rw [hden, Function.update_self]
  have hget : (rewindLens.get s).marks = marksTape s.fpp := rfl
  have hnotfirst : ∀ i, 2 ≤ i → i ≤ w.length → GalilScaffoldTape.denote (marksTape s.fpp) i ≠ first := by
    intro i hi2 hiw h
    rw [hcell i hi2] at h
    rcases marks_val w i (by omega) hiw with hv | hv
    · rw [hv] at h; exact h7 h.symm
    · rw [hv] at h; exact h8 h.symm
  -- ## choose
  have hkle : w.length - (2*r+1) ≤ GalilScaffoldTape.head (rewindLens.get s).marks := by
    rw [hget, hhead]; omega
  have hno : ∀ j, j < w.length - (2*r+1) → ¬ (oddAt c.odd j = true ∧ SetAt first (rewindLens.get s) j) := by
    intro j hj ⟨hoj, hset⟩
    rw [ho, oddAt_false] at hoj
    unfold SetAt at hset
    rw [hget, hhead] at hset
    have hi2 : 2 ≤ w.length - j := by omega
    have hiw : w.length - j ≤ w.length := by omega
    rcases hset with hset | hset
    · rw [hcell _ hi2, marks_cell] at hset
      obtain ⟨_, _, hp⟩ := hset
      -- the cell `|w|-j` is odd: `|w|-j = 2r'+1` with `r' > r`
      have hodd' : (w.length - j) % 2 = 1 := by omega
      have hr' := chosen_greatest w ((w.length - j - 1)/2) (by omega) (by
        rw [show 2*((w.length - j - 1)/2)+1 = w.length - j by omega]; exact hp)
      rw [← hr] at hr'
      omega
    · exact hnotfirst _ hi2 hiw hset
  have hodd : oddAt c.odd (w.length - (2*r+1)) = true := by
    rw [ho, oddAt_false]; omega
  have hset : SetAt first (rewindLens.get s) (w.length - (2*r+1)) := by
    unfold SetAt
    rw [hget, hhead, show w.length - (w.length - (2*r+1)) = 2*r+1 by omega]
    by_cases hr0 : r = 0
    · subst hr0
      right
      simpa using hcell1
    · left
      rw [hcell _ (by omega), marks_cell]
      exact ⟨by omega, hr1, hpal⟩
  obtain ⟨y1, hs1, hsame1, hl1, hc1, hr1', hlen1, hrad1, hhead1⟩ :=
    choose_phase_vm first (fun _ => True) (fun _ => True) delay c hm s (w.length - (2*r+1)) hkle hno hodd hset
  obtain ⟨hg1, hi1⟩ := steps_transfer_rewind_S P q first delay _ (Or.inl hm) hi hs1
  -- ## rewind
  have hm1 : ({c with odd := oddAt c.odd (w.length - (2*r+1)), mode := .rewind, pair := false} : Control).mode = .rewind := rfl
  have hp1 : ({c with odd := oddAt c.odd (w.length - (2*r+1)), mode := .rewind, pair := false} : Control).pair = false := rfl
  have hget1 : rewindLens.get (rewindLens.set s y1) = y1 := rewindLens.get_set s y1
  have hden1 : GalilScaffoldTape.denote y1.marks = GalilScaffoldTape.denote (marksTape s.fpp) := hsame1.denote
  have hhead1' : GalilScaffoldTape.head y1.marks = 2*r+1 := by
    rw [hhead1, hget, hhead]; omega
  have hk2 : 2*r ≤ GalilScaffoldTape.head (rewindLens.get (rewindLens.set s y1)).marks := by
    rw [hget1, hhead1']; omega
  have hno2 : ∀ j, j < 2*r → GalilScaffoldTape.denote (rewindLens.get (rewindLens.set s y1)).marks
      (GalilScaffoldTape.head (rewindLens.get (rewindLens.set s y1)).marks - j) ≠ first := by
    intro j hj
    rw [hget1, hden1, hhead1']
    exact hnotfirst _ (by omega) (by omega)
  have hfirst2 : GalilScaffoldTape.denote (rewindLens.get (rewindLens.set s y1)).marks
      (GalilScaffoldTape.head (rewindLens.get (rewindLens.set s y1)).marks - 2*r) = first := by
    rw [hget1, hden1, hhead1', show 2*r+1 - 2*r = 1 by omega]
    exact hcell1
  obtain ⟨y2, hs2, hl2, hc2, hr2, hlen2, hrad2, hprog2⟩ :=
    rewind_phase_vm first (fun _ => True) (fun _ => True) delay _ hm1 hp1 (rewindLens.set s y1) (2*r) hk2 hno2 hfirst2
  obtain ⟨hg2, hi2⟩ := steps_transfer_rewind_S P q first delay _ (Or.inr rfl) hi1 hs2
  rw [rewindLens.set_set] at hg2 hi2
  refine ⟨y2, ?_, ?_, ?_, ?_, ?_, ?_, hprog2, hi2⟩
  · exact steps_trans hg1 hg2
  · rw [hl2]
    show GalilScaffoldInputHead.left^[2*r] y1.left = _
    rw [hl1]
  · rw [hc2]
    show GalilScaffoldInputHead.left^[2*r/2] y1.center = _
    rw [hc1, show 2*r/2 = r by omega]
  · rw [hr2]; exact hr1'
  · rw [hlen2]
    show GalilScaffoldCounter.inc^[2*r] y1.length = _
    rw [hlen1, iterate_inc_ofNat, Nat.add_comm]
  · rw [hrad2]
    show GalilScaffoldCounter.inc^[2*r/2] y1.radius = _
    rw [hrad1, reset_eq_ofNat, iterate_inc_ofNat, show 2*r/2 = r by omega, Nat.zero_add]

theorem fallback_chain_S (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
    (delay : ℕ) (c : Control) (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius w
    ∃ (n : ℕ) (y : RewindVM),
      Steps (galilFrameS P q first) delay n ⟨c, s⟩
        ⟨{c with mode := .replayStart, odd := oddAt false (w.length - (2*r+1)), pair := pairAt (2*r)},
          rewindLens.set s y⟩ ∧
      y.left = GalilScaffoldInputHead.left^[2*r] s.right ∧
      y.center = GalilScaffoldInputHead.left^[r] s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat (2*r+1) ∧ y.radius = GalilScaffoldCounter.ofNat r ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program ∧ ShiftIdle (rewindLens.set s y) := by
  intro w r
  have hw : 1 ≤ w.length := by
    show 1 ≤ ((GalilScaffoldPlace.stream p).take (ℓ+1)).length
    rw [List.length_take]
    have : 0 < (GalilScaffoldPlace.stream p).length := List.length_pos_iff.mpr hne
    omega
  obtain ⟨t, hg1, hmode, hprog, _, hi1⟩ := copy_home_start_S P q first delay c hm s hi old p length hc ℓ hv hs
  have hm1 : ({c with mode := .fpp} : Control).mode = .fpp := rfl
  obtain ⟨n2, y2, hg2, hden2, hhead2, _, _, _, _, hi2⟩ :=
    fpp_then_markEnd_S P q hq first delay {c with mode := .fpp} hm1 {s with fpp := t} hi1 hmode w hw hprog
  have hm2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).mode = .choose := rfl
  have ho2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).odd = false := rfl
  obtain ⟨y3, hg3, hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩ :=
    choose_then_rewind_S P q first h7 h8 delay _ hm2 ho2 {({s with fpp := t} : GalilVM) with fpp := y2} hi2
      w hw heven r rfl hden2 hhead2
  exact ⟨_, y3, steps_trans hg1 (steps_trans hg2 hg3), hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩

theorem fallback_to_scan_S (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ) (c : Control) (hm : c.mode = .copy) (s : GalilVM)
    (hi : ShiftIdle s) (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let win := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius win
    ∃ (n : ℕ) (o : Bool) (t : GalilVM),
      Steps (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay (n+1) ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < r), odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)}, t⟩ ∧
      t.left = GalilScaffoldInputHead.left^[r] s.right ∧ t.right = GalilScaffoldInputHead.left^[r] s.right ∧
      t.center = GalilScaffoldInputHead.left^[r] s.right ∧
      t.replay = GalilScaffoldCounter.ofNat r ∧ t.radius = GalilScaffoldCounter.reset ∧
      t.length = GalilScaffoldCounter.ofNat 1 ∧ t.chain = .idle ∧
      t.fpp.program = GalilScaffoldControl.reset 320 t.fpp.program ∧ ShiftIdle t ∧
      (0 < r → o = c.output) ∧
      t.search = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset ∧
      t.lower = GalilScaffoldCounter.reset ∧ t.chain = .idle := by
  intro win r
  obtain ⟨n, y, hg, hl, hc', hr, hlen, hrad, hprog, hi'⟩ :=
    fallback_chain_S (galilShared onLetter leftFirst guard bs bf rs centre place entry) q hq first h7 h8 delay c hm s hi old p length hc ℓ hv hs hne heven
  have hm' : ({c with mode := .replayStart, odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)} : Control).mode = .replayStart := rfl
  obtain ⟨o, t, ht, hrep, hR, hL, hC, hrad', hlen', hrem, hcyc, hfpp, hw, ho, _, hsearch, hlower, _⟩ :=
    replayStart_tick onLetter leftFirst guard bs bf rs centre place entry q first delay _ hm' (rewindLens.set s y)
  have hrad'' : (rewindLens.set s y).radius = GalilScaffoldCounter.ofNat r := hrad
  have hcen : (rewindLens.set s y).center = GalilScaffoldInputHead.left^[r] s.right := hc'
  rw [hrad'', positive_ofNat] at ht ho
  have htS := tick_S_of_tick _ q first delay ht (by rw [hm']; decide)
  refine ⟨n, o, t, steps_trans hg (.succ htS (.zero _)), ?_, ?_, ?_, ?_, hrad', hlen', hw, ?_, ?_, ?_, hsearch, hlower, hw⟩
  · rw [hL, hcen]
  · rw [hR, hcen]
  · rw [hC, hcen]
  · rw [hrep, hrad'']
  · rw [hfpp]; exact hprog
  · rw [shiftIdle_iff, hrem]
    show GalilScaffoldCounter.positive s.remaining = false
    exact (shiftIdle_iff s).1 hi
  · intro hr0
    exact ho (by simpa using hr0)

#print axioms fallback_chain_S
#print axioms fallback_to_scan_S

end PalPeg.GalilScaffoldChainInputSupply
