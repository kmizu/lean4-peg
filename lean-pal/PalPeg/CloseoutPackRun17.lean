import PalPeg.CloseoutPackRun16

/-!
# `CloseoutPackRun17`: `ChooseLayout` along runs, and the guarded residual

`CloseoutPackRun16` left one hypothesis: `ChooseLayout first s` at every
selecting `choose` state of a run — the FPP layout of a window `w` with
`FIRST` at cell `1`, `1 ≤ mh s ≤ |w|`, and the *tight* window bound
`|w| ≤ position R`.  This file produces it along every run of the concrete
scaffold `galilFrameS (sharedC …)`, next to `GalilCentreLive.CPack`.

* §1 **`WindowInOrigin`** — **(NAMED, the one new hypothesis)** at a `copy`
  state the walker's stream is at most `position R` long.  In the model the
  fallback place `p` of `beginFallbackVM'` is existential (`beginFallback_exists`
  uses `⟨[], false⟩`), so nothing ties it to the right head; on the machine `p`
  *is* the place of `R`, and `position` counts half-steps
  (`position = 2·|left|` or `2·|left| − 1`, `GalilScaffoldChainInputSupply`),
  which is exactly `(stream p).length` for the represented place.  So the
  hypothesis is the "copy walker never crosses the origin" fact, and it is
  supplied by whatever fixes the fallback witness to `P.place s` (the `Fair`
  landing of `GalilTickFair` / `beginFallback_heads`), not by a tick-local
  argument.

* §2 `WPack` — the window pack: `copy`/`home` carry the pending FPP run to
  `⟨fppInitial w, false⟩` with `|w| ≤ position R`; `fpp` the scheduled run;
  `markEnd` the layout `update (marks w) 1 first`; `choose` the layout with
  `mh s ≤ |w|`.  `wpack_tick` preserves it on every tick (the `scan_fallback`
  entry reads `WindowInOrigin` at the landing state; `|take (ℓ+1) (stream p)|
  ≤ |stream p|`), `wpack_steps` carries it with `CPack` along runs.

* §3 Evenness is **not** needed.  The `choose` walk could only select at cell
  `0` if `markSet` held there; cell `0` of the layout is `4`, so with
  `first ≠ 4` (a side condition on the marker, like the `first ≠ 7`,
  `first ≠ 8` already used by `scan_fallback_cycle`) the head is at cell `≥ 1`
  at every selection (`chooseLayout_of_wpack`), and `marksEntry'_of_layout`
  closes the residual: `marksEntry'_of_run`.  The run-restricted
  `MarksInv'` and both guarded corners follow (`marksInv'_of_run'`,
  `corners_of_marks'_run`), with no `H_marksEntry'`.

## Honest status

Standard axioms only; unconditional `PAL ∈ PEG` remains open.  New
hypothesis: `WindowInOrigin` at the run's `copy` states (`hwin`), plus the
side condition `first ≠ 4`; `hfloor` is inherited from `CPack`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun17

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun13 PalPeg.CloseoutPackRun15 PalPeg.CloseoutPackRun16
open PalPeg.GalilCentreLive (mh CPack cpack_tick compare_len future_step future_run
  toController_copy toController_home)

/-! ## 1. The one new hypothesis -/

/-- **(NAMED) the copy walker never crosses the origin.**  The stream of the
FPP walker's place is at most `position R` long. -/
def WindowInOrigin (s : GalilVM) : Prop :=
  (GalilScaffoldPlace.stream s.fpp.walker).length ≤ position s.right

/-- The `END` cells of the layout: `|w| + 1`, or cell `1` when `first = 5`. -/
theorem layout_end_eq (first : Fin 9) (w : List (Fin 3)) (e : ℕ)
    (h5 : Function.update (GalilFppMarkedLayout.marks w) 1 first e = 5) :
    e = 1 ∨ e = w.length + 1 := by
  by_cases h1 : e = 1
  · exact Or.inl h1
  rw [Function.update_of_ne h1] at h5
  unfold GalilFppMarkedLayout.marks at h5
  by_cases h0 : e = 0
  · simp only [h0, if_true] at h5; exact absurd h5 (by decide)
  simp only [h0, if_false] at h5
  by_cases hl : e ≤ w.length
  · simp only [hl, if_true] at h5
    split at h5 <;> exact absurd h5 (by decide)
  · simp only [hl, if_false] at h5
    by_cases h2 : e = w.length + 1
    · exact Or.inr h2
    · simp only [h2, if_false] at h5; exact absurd h5 (by decide)

#print axioms layout_end_eq

/-! ## 2. The window pack -/

/-- The window pack: the tight window bound through the fallback phases. -/
structure WPack (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) : Prop where
  copy : c.mode = Mode.copy ∨ c.mode = Mode.home →
    ∃ (w : List (Fin 3)) (k : ℕ) (t0 : FppControl.State),
      w.length ≤ position s.right ∧ s.fpp.mode.toController = c.mode ∧
      FppControl.Run s.fpp (List.replicate k true) t0 ∧ t0.mode = FppControl.Mode.run ∧
      t0.program = ⟨fppInitial w, false⟩
  fpp : c.mode = Mode.fpp → ∃ (w : List (Fin 3)) (n : ℕ), w.length ≤ position s.right ∧
    GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩
      (List.replicate (n*q) true) s.fpp.program
  markEnd : c.mode = Mode.markEnd → ∃ w : List (Fin 3),
    GalilScaffoldTape.denote (marksTape s.fpp) =
      Function.update (GalilFppMarkedLayout.marks w) 1 first ∧ w.length ≤ position s.right
  choose : c.mode = Mode.choose → ∃ w : List (Fin 3),
    GalilScaffoldTape.denote (marksTape s.fpp) =
      Function.update (GalilFppMarkedLayout.marks w) 1 first ∧ w.length ≤ position s.right ∧
      mh s ≤ w.length

/-- Outside the fallback phases the pack is vacuous. -/
theorem wpack_of_mode {q : ℕ} {first : Fin 9} {c : Control} {s : GalilVM} {m : Mode}
    (h1 : m ≠ Mode.copy) (h2 : m ≠ Mode.home) (h3 : m ≠ Mode.fpp) (h4 : m ≠ Mode.markEnd)
    (h5 : m ≠ Mode.choose) (hm : c.mode = m) : WPack q first c s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (hx | hx) <;> rw [hm] at hx
    · exact absurd hx h1
    · exact absurd hx h2
  · intro hx; rw [hm] at hx; exact absurd hx h3
  · intro hx; rw [hm] at hx; exact absurd hx h4
  · intro hx; rw [hm] at hx; exact absurd hx h5

/-- **`ChooseLayout` at a selecting `choose` state**, from the pack: the head
cannot be at cell `0` (which reads `4`, not a mark) when `first ≠ 4`. -/
theorem chooseLayout_of_wpack {q : ℕ} {first : Fin 9} {c : Control} {s : GalilVM}
    (h4 : first ≠ 4) (hW : WPack q first c s) (hm : c.mode = Mode.choose)
    (hs : (marksTape s.fpp).focus = 8 ∨ (marksTape s.fpp).focus = first) :
    ChooseLayout first s := by
  obtain ⟨w, hden, hwr, hmw⟩ := hW.choose hm
  refine ⟨w, hden, ?_, hmw, hwr⟩
  by_contra hlt
  have h0 : mh s = 0 := by omega
  have hf : (marksTape s.fpp).focus = 4 := by
    rw [← GalilScaffoldTape.focus_eq]
    show GalilScaffoldTape.denote (marksTape s.fpp) (mh s) = 4
    rw [h0, hden, Function.update_of_ne (by decide)]
    rfl
  rcases hs with h | h
  · rw [hf] at h; exact absurd h (by decide)
  · rw [hf] at h; exact h4 h.symm

#print axioms chooseLayout_of_wpack

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **(KEY) one tick preserves `WPack`**, reading `WindowInOrigin` at a
`copy` landing. -/
theorem wpack_tick {c c' : Control} {s t : GalilVM} (hP : CPack q c s)
    (hfl : c.mode = Mode.scan → 0 ≤ value s.length)
    (hwin : c'.mode = Mode.copy → WindowInOrigin t)
    (hW : WPack q first c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : WPack q first c' t := by
  cases h
  all_goals try (refine ⟨?_, ?_, ?_, ?_⟩ <;> vac)
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨-, -, -, -, hs'len⟩ :=
      compare_len onLetter leftFirst centre place entry q first hcmp
    have hl := hs'len hmt
    obtain ⟨pl, ht, -⟩ : beginFallbackVM' s' t := hb
    have h0 := hfl hm
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, value s.length = ℓ := ⟨(value s.length).toNat, by omega⟩
    have hwin' := hwin rfl
    subst ht
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    have hc' : Canonical s'.length := by rw [hl]; exact hP.canon
    have hv' : value s'.length = ℓ := by rw [hl]; exact hℓ
    obtain ⟨t0, hrun, hmode, hprog, -⟩ :=
      FppControl.fallback_prepared s'.fpp.program pl s'.length hc' ℓ hv'
    refine ⟨(GalilScaffoldPlace.stream pl).take (ℓ+1), _, t0, ?_, rfl, hrun, hmode, hprog⟩
    have hw : (GalilScaffoldPlace.stream pl).length ≤ position s'.right := hwin'
    show _ ≤ position s'.right
    rw [List.length_take]
    exact le_trans (min_le_right _ _) hw
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨a, ha, hv⟩ : ∃ a : Fin 3, GalilScaffoldPlace.read s.fpp.walker = some a ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec s.fpp.work, walker := GalilScaffoldPlace.left s.fpp.walker} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hidle := hP.idle (by rw [hm]; decide)
    have hB : ¬ (GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true) :=
      hp.resolve_left hidle
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hW.copy (Or.inl hm)
    have hw : zero s.fpp.work = false := by
      cases hz : zero s.fpp.work
      · rfl
      · exact absurd (Or.inr hz) hB
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .copyBit s.fpp a (toController_copy (hmode.trans hm)) ha hw
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, k', t0, hb, ?_, hrun', h0, hprog⟩
    show t.fpp.mode.toController = c.mode
    rw [hv]; exact hmode
  case copy_done =>
    rename_i hm hp hi
    have hv : t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read s.fpp.walker).isNone} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hW.copy (Or.inl hm)
    have he : GalilScaffoldPlace.read s.fpp.walker = none ∨ zero s.fpp.work = true :=
      Classical.byContradiction (fun hn => hp (Or.inr hn))
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .copyEnd s.fpp (toController_copy (hmode.trans hm)) he
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, k', t0, hb, ?_, hrun', h0, hprog⟩
    show t.fpp.mode.toController = Mode.home
    rw [hv]; rfl
  case home_step =>
    rename_i hm hl hi
    obtain ⟨hleft, hv⟩ : (s.fpp.program.config.tapes 7).left ≠ [] ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 GalilScaffoldTape.moveLeft} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hW.copy (Or.inr hm)
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .sourceLeft s.fpp (toController_home (hmode.trans hm)) hl hleft
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, k', t0, hb, ?_, hrun', h0, hprog⟩
    show t.fpp.mode.toController = c.mode
    rw [hv]; exact hmode
  case home_start =>
    rename_i hm hl hi
    have hv : t.fpp = {s.fpp with program := GalilScaffoldControl.start 320 s.fpp.program, mode := .run} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    obtain ⟨w, k, t0, hb, hmode, hrun, h0, hprog⟩ := hW.copy (Or.inr hm)
    have hft : FppControl.Tick true s.fpp t.fpp := by
      rw [hv]; exact .startRun s.fpp (toController_home (hmode.trans hm)) hl
    obtain ⟨k', hrun'⟩ := future_step hrun h0 hft
    have heq : t.fpp = t0 := future_run hrun' (by rw [hv])
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, 0, hb, ?_⟩
    show GalilScaffoldControl.Run _ _ _ t.fpp.program
    rw [Nat.zero_mul, List.replicate_zero, heq, hprog]
    exact .nil _
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hq, -, -⟩ : s.fpp.mode = .run ∧
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) t.fpp.program ∧
        t.fpp.program.done = false ∧ t.fpp = {s.fpp with program := t.fpp.program} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    obtain ⟨w, n, hb, hrun⟩ := hW.fpp hm
    have hrun2 : GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩
        (List.replicate ((n+1)*q) true) t.fpp.program := by
      rw [Nat.succ_mul, List.replicate_add]; exact GalilScaffoldControl.run_append hrun hq
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _; exact ⟨w, n+1, hb, hrun2⟩
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, p, hq, hd, hv⟩ : s.fpp.mode = .run ∧ ∃ p : GalilScaffoldControl.Machine 9,
        GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) p ∧
        p.done = true ∧ t.fpp = {s.fpp with program := markNew p first} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    obtain ⟨w, n, hb, hrun⟩ := hW.fpp hm
    have hrun2 : GalilScaffoldControl.Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩
        (List.replicate ((n+1)*q) true) p := by
      rw [Nat.succ_mul, List.replicate_add]; exact GalilScaffoldControl.run_append hrun hq
    obtain ⟨v, -, hpos, -, h8, hsched⟩ := fpp_scheduled w
    have hpv : p = ⟨v, true⟩ :=
      fpp_outcome_program q w {s.fpp with program := ⟨fppInitial w, false⟩} rfl v hsched n p hd hrun2
    obtain ⟨hden, -⟩ := marks_after_fpp first w v hpos h8
    have hmt : marksTape t.fpp = (markNew ⟨v, true⟩ first).config.tapes 8 := by
      rw [hv, ← hpv]; rfl
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, ?_, hb⟩
    show GalilScaffoldTape.denote (marksTape t.fpp) = _
    rw [hmt, hden]
  case markEnd_step =>
    rename_i hm he hi
    have hv : t.fpp = markStep s.fpp GalilScaffoldTape.moveRight := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    have hmt : marksTape t.fpp = GalilScaffoldTape.moveRight (marksTape s.fpp) := by
      rw [hv, markStep_tape]
    obtain ⟨w, hden, hb⟩ := hW.markEnd hm
    rw [ht]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, ?_, hb⟩
    show GalilScaffoldTape.denote (marksTape t.fpp) = _
    rw [hmt, GalilScaffoldTape.right_denote, hden]
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨hleft, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    have hfocus : (marksTape s.fpp).focus = 5 := he
    obtain ⟨w, hden, hb⟩ := hW.markEnd hm
    have h5 : Function.update (GalilFppMarkedLayout.marks w) 1 first (mh s) = 5 := by
      rw [← hden]; unfold mh; rw [GalilScaffoldTape.focus_eq]; exact hfocus
    have hend := layout_end_eq first w (mh s) h5
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, ?_, hb, ?_⟩
    · show GalilScaffoldTape.denote (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) = _
      rw [markStep_tape, GalilScaffoldTape.left_denote, hden]
    · show GalilScaffoldTape.head (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) ≤ w.length
      rw [markStep_tape, GalilScaffoldTape.left_head _ hpos]
      unfold mh at hend; omega
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨hleft, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    subst ht
    have hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) :=
      (GalilScaffoldTape.left_legal _).1 hleft
    obtain ⟨w, hden, hb, hmw⟩ := hW.choose hm
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try vac
    intro _
    refine ⟨w, ?_, hb, ?_⟩
    · show GalilScaffoldTape.denote (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) = _
      rw [markStep_tape, GalilScaffoldTape.left_denote, hden]
    · show GalilScaffoldTape.head (marksTape (markStep s.fpp GalilScaffoldTape.moveLeft)) ≤ w.length
      rw [markStep_tape, GalilScaffoldTape.left_head _ hpos]
      unfold mh at hmw; omega

#print axioms wpack_tick

/-- `CPack` and `WPack` travel together along any run whose `scan` states
have a non-negative length counter and whose `copy` states satisfy
`WindowInOrigin`. -/
theorem wpack_steps {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwin : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.copy → WindowInOrigin z.vm)
    (hP : CPack q x.ctl x.vm) (hW : WPack q first x.ctl x.vm) :
    CPack q y.ctl y.vm ∧ WPack q first y.ctl y.vm := by
  induction h with
  | zero x => exact ⟨hP, hW⟩
  | @succ n x w y ht _ ih =>
    refine ih (fun m z hz => hfl (m+1) z (.succ ht hz))
      (fun m z hz => hwin (m+1) z (.succ ht hz)) ?_ ?_
    · exact cpack_tick onLetter leftFirst centre place entry q first delay hP
        (hfl 0 x (.zero x)) ht
    · exact wpack_tick onLetter leftFirst centre place entry q first delay hP
        (hfl 0 x (.zero x)) (fun hm => hwin 1 w (.succ ht (.zero w)) hm) hW ht

#print axioms wpack_steps

/-! ## 3. The deliverables -/

/-- **`ChooseLayout` at every selecting `choose` state of a run.** -/
theorem chooseLayout_of_run (h4 : first ≠ 4) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwin : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.copy → WindowInOrigin z.vm)
    (hP : CPack q x.ctl x.vm) (hW : WPack q first x.ctl x.vm)
    (hm : y.ctl.mode = Mode.choose)
    (hs : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).markSet y.vm) :
    ChooseLayout first y.vm :=
  chooseLayout_of_wpack h4
    (wpack_steps onLetter leftFirst centre place entry q first delay h hfl hwin hP hW).2 hm hs

/-- **The guarded residual `MarksEntry'` at every selecting `choose` state of
a run** (the run-restricted `H_marksEntry'`). -/
theorem marksEntry'_of_run (h4 : first ≠ 4) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwin : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.copy → WindowInOrigin z.vm)
    (hP : CPack q x.ctl x.vm) (hW : WPack q first x.ctl x.vm)
    (hm : y.ctl.mode = Mode.choose)
    (hs : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).markSet y.vm) :
    MarksEntry' first y.vm :=
  marksEntry'_of_layout
    (chooseLayout_of_run onLetter leftFirst centre place entry q first delay h4 h hfl hwin hP hW hm hs)

#print axioms chooseLayout_of_run
#print axioms marksEntry'_of_run

/-- `CPack`, `WPack` and `MarksInv'` together, with no `H_marksEntry'`. -/
theorem marks_steps (h4 : first ≠ 4) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwin : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.copy → WindowInOrigin z.vm)
    (hP : CPack q x.ctl x.vm) (hW : WPack q first x.ctl x.vm)
    (hI : MarksInv' first x.ctl x.vm) :
    CPack q y.ctl y.vm ∧ WPack q first y.ctl y.vm ∧ MarksInv' first y.ctl y.vm := by
  induction h with
  | zero x => exact ⟨hP, hW, hI⟩
  | @succ n x w y ht _ ih =>
    refine ih (fun m z hz => hfl (m+1) z (.succ ht hz))
      (fun m z hz => hwin (m+1) z (.succ ht hz)) ?_ ?_ ?_
    · exact cpack_tick onLetter leftFirst centre place entry q first delay hP
        (hfl 0 x (.zero x)) ht
    · exact wpack_tick onLetter leftFirst centre place entry q first delay hP
        (hfl 0 x (.zero x)) (fun hm => hwin 1 w (.succ ht (.zero w)) hm) hW ht
    · exact marksInv'_tick (sharedC onLetter leftFirst centre place entry) q first delay hI
        (fun hm _ hs => marksEntry'_of_layout (chooseLayout_of_wpack h4 hW hm hs)) ht

/-- **`MarksInv'` on every state of a run** parked outside `rewind` and the
fallback phases, with no `H_marksEntry'`. -/
theorem marksInv'_of_run' (h4 : first ≠ 4) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwin : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.copy → WindowInOrigin z.vm)
    (hP : CPack q x.ctl x.vm) (hx : x.ctl.mode = Mode.scan) :
    MarksInv' first y.ctl y.vm :=
  (marks_steps onLetter leftFirst centre place entry q first delay h4 h hfl hwin hP
    (wpack_of_mode (by decide) (by decide) (by decide) (by decide) (by decide) hx)
    (marksInv'_of_mode (by decide) hx)).2.2

/-- **Both guarded corners** at every `rewind` state off the `FIRST` cell of
a run started in `scan`, with no `H_marksEntry'`. -/
theorem corners_of_marks'_run (h4 : first ≠ 4) {n : ℕ} {x y : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x y)
    (hfl : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length)
    (hwin : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x z →
      z.ctl.mode = Mode.copy → WindowInOrigin z.vm)
    (hP : CPack q x.ctl x.vm) (hx : x.ctl.mode = Mode.scan)
    (hm : y.ctl.mode = Mode.rewind)
    (hnf : ¬ (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).atFirst y.vm) :
    0 < position (GalilScaffoldInputHead.left y.vm.left) ∧
      0 < position (GalilScaffoldInputHead.left y.vm.center) := by
  have hi := marksInv'_of_run' onLetter leftFirst centre place entry q first delay h4 h hfl hwin hP hx
  exact ⟨rewindLeft_of_marksInv' _ q hi hm hnf, rewindCentre_of_marksInv' _ q hi hm hnf⟩

#print axioms marks_steps
#print axioms marksInv'_of_run'
#print axioms corners_of_marks'_run

end Tick

end PalPeg.CloseoutPackRun17
