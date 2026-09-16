import PalPeg.GalilScaffoldTopFallbackCycleS

/-!
# A tick bound for the fallback cycle

`fallback_chain_S` (`PalPeg.GalilScaffoldTopFallbackS`) runs the fallback from
`copy` to `replayStart` in an existentially quantified number of controller
ticks: the copy/home phase costs `2·|w|+3`, the markEnd phase `|w|`, the
choose/rewind phase `|w|+1`, and the FPP phase `n+1`, where `n` is the number
of quanta the FPP program needs.  The bound on `n` is present in
`fpp_phase_scheduled` only as the *input* `M := ⌈(1584·|w|+830)/q⌉` of
`fpp_phase_lift`; `FppOutcome` drops it again.  This module re-runs the slicing
argument carrying the bound (`FppOutcomeLe`, `fpp_slices_le`) and threads it
through the chain, giving

  `fallback_ticks_le : … n ≤ 1588*(ℓ+1) + 836`.

The constant `1588 = 4 + 1584` is the FPP instruction cost per window letter
(`GalilFppMarkedCost`) plus the four linear scans of the window; `836` collects
the additive `830` of the FPP cost, the `+1` of the ceiling, and the constant
ticks of the copy/home, markEnd and choose/rewind phases.  The bound is stated
for `q = 1` instruction per quantum, which is the worst case: a larger quantum
`q` divides the FPP summand (`(1584·|w|+830)/q`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- `FppOutcome` with the number of quanta bounded by `B`. -/
def FppOutcomeLe (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : Control) (x : FppControl.State) (B : ℕ) : Prop :=
  ∃ (n : ℕ) (p : GalilScaffoldControl.Machine 9) (y : FppControl.State), n ≤ B ∧
    Steps (fppFrame q first onLetter leftFirst) delay (n+1) ⟨c, x⟩ ⟨{c with mode := .markEnd}, y⟩ ∧
    y.program = markNew p first ∧ y.mode = .run ∧ y.walker = x.walker ∧ y.work = x.work ∧
    y.finalStage = x.finalStage ∧ p.done = true ∧
    GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate ((n+1)*q) true) p

/-- `fpp_slices` with the quantum count of the outcome bounded by `M`. -/
theorem fpp_slices_le (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop)
    (delay : ℕ) (c : Control) (hm : c.mode = .fpp) (x : FppControl.State) (hx : x.mode = .run)
    (M : ℕ) (v : GalilScaffoldProgram.Config 9)
    (hbig : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate (M*q) true) ⟨v,true⟩) :
    ∀ m, m ≤ M →
      (∃ y : FppControl.State, Steps (fppFrame q first onLetter leftFirst) delay m ⟨c, x⟩ ⟨c, y⟩ ∧
        y.mode = .run ∧ y.walker = x.walker ∧ y.work = x.work ∧ y.finalStage = x.finalStage ∧
        GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate (m*q) true) y.program ∧
        y.program.done = false) ∨
      FppOutcomeLe q first onLetter leftFirst delay c x M := by
  intro m
  induction m with
  | zero =>
    intro _
    by_cases hd : x.program.done = true
    · right
      have hidle : ∀ k, GalilScaffoldControl.Run GalilFppMarkedCode.code x.program
          (List.replicate k true) x.program := by
        intro k
        induction k with
        | zero => exact .nil _
        | succ k ih =>
          rw [List.replicate_succ]
          exact .cons _ _ _ _ _ (.idle _ _ (Or.inr hd)) ih
      refine ⟨0, x.program, {x with program := markNew x.program first}, Nat.zero_le _, ?_, rfl, hx,
        rfl, rfl, rfl, hd, ?_⟩
      · exact .succ (GalilScaffoldTop.Tick.fpp_done c x _ hm ⟨hx, x.program, hidle q, hd, rfl⟩) (.zero _)
      · simpa using hidle q
    · left
      refine ⟨x, .zero _, hx, rfl, rfl, rfl, by simpa using GalilScaffoldControl.Run.nil x.program, ?_⟩
      cases h : x.program.done
      · rfl
      · exact absurd h hd
  | succ m ih =>
    intro hle
    rcases ih (Nat.le_of_succ_le hle) with ⟨y, hs, hym, hyw, hyk, hyf, hyr, hyd⟩ | hout
    · have hsplit : List.replicate (M*q) true =
          List.replicate (m*q) true ++ (List.replicate q true ++ List.replicate ((M-(m+1))*q) true) := by
        rw [← List.replicate_add, ← List.replicate_add]
        congr 1
        have : M*q = m*q + q + (M-(m+1))*q := by
          rw [← Nat.succ_mul, ← Nat.add_mul]
          congr 1
          omega
        omega
      rw [hsplit] at hbig
      obtain ⟨y1, h1, h2⟩ := control_run_split hbig
      obtain ⟨y2, h21, _⟩ := control_run_split h2
      have hy1 : y1 = y.program := control_run_unique marked_wellFormed h1 hyr
      subst hy1
      have hrun : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program
          (List.replicate ((m+1)*q) true) y2 := by
        rw [Nat.succ_mul, List.replicate_add]
        exact control_run_append hyr h21
      by_cases hd : y2.done = true
      · right
        refine ⟨m, y2, {y with program := markNew y2 first}, by omega, ?_, rfl, hym, hyw, hyk, hyf, hd, hrun⟩
        exact steps_trans hs (.succ (GalilScaffoldTop.Tick.fpp_done c y _ hm ⟨hym, y2, h21, hd, rfl⟩) (.zero _))
      · left
        have hd' : y2.done = false := by
          cases h : y2.done
          · rfl
          · exact absurd h hd
        refine ⟨{y with program := y2}, ?_, hym, hyw, hyk, hyf, hrun, hd'⟩
        exact steps_trans hs (.succ (GalilScaffoldTop.Tick.fpp_slice c y _ hm ⟨hym, h21, hd', rfl⟩) (.zero _))
    · exact Or.inr hout

/-- `fpp_phase_lift` keeping the bound `M` on the number of quanta. -/
theorem fpp_phase_lift_le (q : ℕ) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop)
    (delay : ℕ) (c : Control) (hm : c.mode = .fpp) (x : FppControl.State) (hx : x.mode = .run)
    (M : ℕ) (v : GalilScaffoldProgram.Config 9)
    (hbig : GalilScaffoldControl.Run GalilFppMarkedCode.code x.program (List.replicate (M*q) true) ⟨v,true⟩) :
    FppOutcomeLe q first onLetter leftFirst delay c x M := by
  rcases fpp_slices_le q first onLetter leftFirst delay c hm x hx M v hbig M (le_refl _) with
    ⟨y, _, _, _, _, _, hyr, hyd⟩ | hout
  · exfalso
    have := control_run_unique marked_wellFormed hyr hbig
    rw [this] at hyd
    cases hyd
  · exact hout

/-- `fpp_phase_scheduled` keeping the bound `⌈(1584·|w|+830)/q⌉` on the quanta. -/
theorem fpp_phase_scheduled_le (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ) (c : Control) (hm : c.mode = .fpp)
    (x : FppControl.State) (hx : x.mode = .run) (w : List (Fin 3))
    (hp : x.program = ⟨fppInitial w, false⟩) :
    FppOutcomeLe q first onLetter leftFirst delay c x ((1584*w.length+830)/q + 1) := by
  obtain ⟨v, _, _, _, _, hrun⟩ := fpp_scheduled w
  have hM : 1584*w.length+830 ≤ ((1584*w.length+830)/q + 1) * q := by
    have := Nat.lt_div_mul_add (a := 1584*w.length+830) hq
    rw [Nat.add_mul, Nat.one_mul]
    omega
  apply fpp_phase_lift_le q first onLetter leftFirst delay c hm x hx ((1584*w.length+830)/q + 1) v
  rw [hp]
  apply hrun
  rw [count_true_replicate]
  exact hM

/-- `fpp_phase_vm` with the quantum count bounded. -/
theorem fpp_phase_vm_le (q : ℕ) (hq : 0 < q) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop)
    (delay : ℕ) (c : GalilScaffoldController.Control) (hm : c.mode = .fpp) (s : GalilVM)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (p : GalilScaffoldControl.Machine 9) (y : FppControl.State),
      n ≤ (1584*w.length+830)/q + 1 ∧
      Steps (Frame.pull fppLens (fppFrame q first onLetter leftFirst)) delay (n+1) ⟨c, s⟩
        ⟨{c with mode := .markEnd}, {s with fpp := y}⟩ ∧
      y.program = markNew p first ∧ y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧
      y.finalStage = s.fpp.finalStage ∧ p.done = true ∧
      GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate ((n+1)*q) true) p := by
  obtain ⟨n, p, y, hb, hs, hprog, hmode, hw, hk, hf, hd, hrun⟩ :=
    fpp_phase_scheduled_le q hq first onLetter leftFirst delay c hm s.fpp hx w hp
  exact ⟨n, p, y, hb, steps_pull fppLens _ delay (n+1) c _ s y hs, hprog, hmode, hw, hk, hf, hd, hrun⟩

/-- `fpp_then_markEnd_S` with the quantum count bounded. -/
theorem fpp_then_markEnd_le (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .fpp) (s : GalilVM) (hi : ShiftIdle s)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hw : 1 ≤ w.length)
    (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (y : FppControl.State), n ≤ (1584*w.length+830)/q + 1 ∧
      Steps (galilFrameS P q first) delay (n+1 + (w.length-1+1)) ⟨c, s⟩
        ⟨{c with mode := .choose, odd := false}, {s with fpp := y}⟩ ∧
      GalilScaffoldTape.denote (marksTape y) = Function.update (GalilFppMarkedLayout.marks w) 1 first ∧
      GalilScaffoldTape.head (marksTape y) = w.length ∧
      y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧ y.finalStage = s.fpp.finalStage ∧
      ShiftIdle {s with fpp := y} := by
  obtain ⟨v, hpc, hpos, ht7, ht8, hsched⟩ := fpp_scheduled w
  obtain ⟨n, p, y1, hb, hs1, hprog, hmode, hwk, hwork, hfin, hd, hrun⟩ :=
    fpp_phase_vm_le q hq first (fun _ => True) (fun _ => True) delay c hm s hx w hp
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
  refine ⟨n, y2, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi2⟩
  · exact steps_trans hg1 hg2
  · rw [hsame.denote]; exact hden1
  · rw [hhead2]
    show GalilScaffoldTape.head (marksTape y1) + (w.length - 1) - 1 = w.length
    rw [hhead1]; omega
  · rw [hsame.mode]; exact hmode
  · rw [hsame.walker]; exact hwk
  · rw [hsame.work]; exact hwork
  · rw [hsame.finalStage]; exact hfin

/-- The fallback chain of `fallback_chain_S`, with its tick count bounded by an
affine function of the window bound `ℓ+1`: the fallback costs at most
`1588·(ℓ+1) + 836` controller ticks. -/
theorem fallback_ticks_le (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8)
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
      n ≤ 1588*(ℓ+1) + 836 ∧
      y.left = GalilScaffoldInputHead.left^[2*r] s.right ∧
      y.center = GalilScaffoldInputHead.left^[r] s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat (2*r+1) ∧ y.radius = GalilScaffoldCounter.ofNat r ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program ∧ ShiftIdle (rewindLens.set s y) := by
  intro w r
  have hwl : w.length ≤ ℓ+1 := by
    show ((GalilScaffoldPlace.stream p).take (ℓ+1)).length ≤ ℓ+1
    rw [List.length_take]; omega
  have hw : 1 ≤ w.length := by
    show 1 ≤ ((GalilScaffoldPlace.stream p).take (ℓ+1)).length
    rw [List.length_take]
    have : 0 < (GalilScaffoldPlace.stream p).length := List.length_pos_iff.mpr hne
    omega
  have hwne : w ≠ [] := by
    intro h
    rw [h] at hw
    simp at hw
  have hr1 : 2*r+1 ≤ w.length := (chosen_spec w hwne).1
  obtain ⟨t, hg1, hmode, hprog, _, hi1⟩ := copy_home_start_S P q first delay c hm s hi old p length hc ℓ hv hs
  have hm1 : ({c with mode := .fpp} : Control).mode = .fpp := rfl
  obtain ⟨n2, y2, hb2, hg2, hden2, hhead2, _, _, _, _, hi2⟩ :=
    fpp_then_markEnd_le P q hq first delay {c with mode := .fpp} hm1 {s with fpp := t} hi1 hmode w hw hprog
  have hm2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).mode = .choose := rfl
  have ho2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).odd = false := rfl
  obtain ⟨y3, hg3, hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩ :=
    choose_then_rewind_S P q first h7 h8 delay _ hm2 ho2 {({s with fpp := t} : GalilVM) with fpp := y2} hi2
      w hw heven r rfl hden2 hhead2
  have hb2' : n2 ≤ 1584*w.length+831 :=
    hb2.trans (Nat.add_le_add_right (Nat.div_le_self (1584*w.length+830) q) 1)
  have hlink : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length = w.length := rfl
  refine ⟨_, y3, steps_trans hg1 (steps_trans hg2 hg3), ?_, hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩
  omega

#print axioms fallback_ticks_le
