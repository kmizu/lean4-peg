import PalPeg.GalilIntervalCost
import PalPeg.GalilFallbackLanding
import PalPeg.GalilScaffoldTopShiftCycle
import PalPeg.GalilLedgerObligations2
import PalPeg.GalilChainReadyProgress
import PalPeg.GalilSearchContractStage
import PalPeg.GalilPeriodCentre
import PalPeg.GalilLiveCentreFallback
import PalPeg.GalilSpanCounter
import PalPeg.GalilFallbackCost

/-!
# Machine events for the interval ledger

`GalilIntervalCost` works with abstract `ShiftEv` / `FallbackEv` records.  This
module builds them from the machine:

* `shiftEv_of_run`: a chain shift phase of `h ≥ 1` units (`ChainShiftRun`
  exhausting `remaining`) is an `h+1`-tick `StepsAll` run
  (`shift_phase_stepsAll_S`) that moves the centre by exactly `h`
  (`shift_run_center`).  `shiftEv_of_begin` specialises to the state produced
  by `beginShiftVM h w`.
* `window_eq_cons_span`: the fallback window `(stream p).take (2k+2)` at the
  mismatch place `C+k+1` is `x :: Span raw C k`.
* `fallbackEv_of_landing`: from the scan invariant at the mismatching state,
  `RadiusRep`/`SpanRep` (giving `ℓ+1 = 2k+2`), the stage-window search contract
  inputs, the fallback tick bound `fb ≤ 1588(ℓ+1)+836` (`fallback_ticks_le`)
  and a replay of `R·M` ticks with `R` the chosen radius, a `FallbackEv M`
  with `k = Rad`, `r = R`, whose advance is the landing centre's advance over
  the old centre.
-/

set_option autoImplicit false

namespace PalPeg.GalilPlaceEvents

open PalPeg PalPeg.GalilIntervalCost PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## (1) Chain shifts -/

/-- A chain shift run forgets to a plain shift run. -/
theorem shiftRun_of_chain {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} {n : ℕ} (hr : ChainShiftRun s w cycle n t v finish) :
    ShiftRun s n t := by
  induction hr with
  | stop s w cycle => exact .stop s
  | next s w cycle he hc hl hl' rest ih => exact .next s he hc hl hl' ih

/-- **`shiftEv_of_run`.**  The shift phase from shift mode: `h` unit shifts and
the exit tick, `h+1` ticks in all, moving the centre by exactly `h`. -/
theorem shiftEv_of_run (Q : State GalilVM → Prop)
    (hQM : ∀ (c : Control) (s : GalilVM), c.mode = .shift → Q ⟨c, s⟩)
    (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s2 : GalilVM) (hi : CopyIdle s2) (w : GalilScaffoldChainWatch.State)
    (hs : s2.chain = .watch w) {h : ℕ} (hpos : 0 < h) {t : ShiftState}
    {v : GalilScaffoldChainWatch.State} {finish : Counter}
    (hr : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩ w s2.cycle h t v finish)
    (hz : positive t.remaining = false) (o : Bool)
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t, .watch v, finish⟩) c.output o)
    (hQend : Q ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩)
    (raw : List (Fin 2)) (hrep : GalilScaffoldInputTrace.Represents s2.center.head raw)
    (hfoc : s2.center.head.focus ≠ none) :
    ∃ e : ShiftEv, e.ticks = h + 1 ∧ e.adv = h ∧
      StepsAll (galilFrameS P q first) delay Q e.ticks ⟨c, s2⟩
        ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩ ∧
      position (shiftLens.set s2 ⟨t, .watch v, finish⟩).center = position s2.center + e.adv := by
  have hst := shift_phase_stepsAll_S Q hQM P q first delay c hm s2 hi w hs hr hz o ho hQend
  obtain ⟨_, _, hc⟩ := shift_run_center (shiftRun_of_chain hr) raw hrep hfoc
  exact ⟨⟨h + 1, h, hpos, le_rfl⟩, rfl, rfl, hst, hc⟩

/-- **`shiftEv_of_begin`.**  The same, from the state `beginShiftVM h w0` left:
`remaining = ofNat h`, so the exit guard holds after exactly `h` units. -/
theorem shiftEv_of_begin (Q : State GalilVM → Prop)
    (hQM : ∀ (c : Control) (s : GalilVM), c.mode = .shift → Q ⟨c, s⟩)
    (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .shift) (s1 s2 : GalilVM) (w0 : GalilScaffoldChainWatch.State) {h : ℕ}
    (hb : beginShiftVM h w0 s1 s2) (hi : CopyIdle s2) (hpos : 0 < h)
    (hcr : Canonical s2.radius) (hcl : Canonical s2.length)
    {t : ShiftState} {v : GalilScaffoldChainWatch.State} {finish : Counter}
    (hr : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩
      (GalilScaffoldChainWatch.immediate w0) s2.cycle h t v finish) (o : Bool)
    (ho : refresh (galilFrameS P q first) (shiftLens.set s2 ⟨t, .watch v, finish⟩) c.output o)
    (hQend : Q ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩)
    (raw : List (Fin 2)) (hrep : GalilScaffoldInputTrace.Represents s2.center.head raw)
    (hfoc : s2.center.head.focus ≠ none) :
    ∃ e : ShiftEv, e.ticks = h + 1 ∧ e.adv = h ∧
      StepsAll (galilFrameS P q first) delay Q e.ticks ⟨c, s2⟩
        ⟨{c with mode := .scan, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩ ∧
      position (shiftLens.set s2 ⟨t, .watch v, finish⟩).center = position s2.center + e.adv := by
  have hrem : s2.remaining = ofNat h := by rw [hb.2]
  have hs : s2.chain = .watch (GalilScaffoldChainWatch.immediate w0) := by rw [hb.2]
  have hcan : ShiftCanonical ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩ :=
    ⟨by rw [hrem]; exact ofNat_canonical h, hcr, hcl⟩
  have hz := (shift_run_exit (shiftRun_of_chain hr) hcan (by show value s2.remaining = h; rw [hrem, ofNat_value])).2.2
  exact shiftEv_of_run Q hQM P q first delay c hm s2 hi _ hs hpos hr hz o ho hQend raw hrep hfoc

/-! ## (2) Fallbacks -/

/-- **The fallback window is `x :: Span`.**  At a represented place of scan
length `C+k+1` with `PalAt … C k` (`k < C`), the window of length `2k+2` read
leftwards is the letter at the place followed by the span of the palindrome. -/
theorem window_eq_cons_span (a : Fin 2) (xs rs q : List (Fin 2)) (g : Bool) {C k : ℕ}
    (hL : (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).length = C + k + 1) (hkC : k < C)
    (hpal : PalAt (encoded ((a :: xs).reverse ++ rs ++ q)) C k) :
    ∃ x, (GalilScaffoldPlace.stream ⟨a :: xs,g⟩).take (2*k+2) =
      x :: Span ((a :: xs).reverse ++ rs ++ q) C k := by
  set T := GalilScaffoldPlace.stream ⟨a :: xs,g⟩ with hT
  set e := encoded ((a :: xs).reverse ++ rs ++ q) with he
  obtain ⟨x, rest, hxr⟩ : ∃ x rest, T = x :: rest := by
    cases hc : T with
    | nil => rw [hc] at hL; simp at hL
    | cons x rest => exact ⟨x, rest, rfl⟩
  refine ⟨x, ?_⟩
  have hidx : ∀ i, i < T.length → T[i]? = e[T.length-i]? := fun i hi =>
    stream_index a xs rs q g i hi
  rw [hxr, show 2*k+2 = (2*k+1)+1 from rfl, List.take_succ_cons]
  congr 1
  have hrl : rest.length = C + k := by
    have := hL; rw [hxr, List.length_cons] at this; omega
  have hSlen : (Span ((a :: xs).reverse ++ rs ++ q) C k).length = 2*k+1 :=
    length_span_of_palAt hpal
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2*k+1
  · rw [List.getElem?_take_of_lt hi]
    have h1 : rest[i]? = T[i+1]? := by rw [hxr]; rfl
    rw [h1, hidx (i+1) (by rw [hL]; omega), hL]
    unfold Span
    rw [getElem?_take_drop hi]
    obtain ⟨_, _, hsym⟩ := hpal
    rcases Nat.le_total i k with hik | hik
    · have hs := hsym (k - i) (by omega)
      rw [show C - (k - i) = C - k + i from by omega,
        show C + (k - i) = C + k + 1 - (i + 1) from by omega] at hs
      exact hs.symm
    · have hs := hsym (i - k) (by omega)
      rw [show C - (i - k) = C + k + 1 - (i + 1) from by omega,
        show C + (i - k) = C - k + i from by omega] at hs
      exact hs
  · have h1 : (rest.take (2*k+1))[i]? = none :=
      List.getElem?_eq_none (by rw [List.length_take]; omega)
    have h2 : (Span ((a :: xs).reverse ++ rs ++ q) C k)[i]? = none :=
      List.getElem?_eq_none (by rw [hSlen]; omega)
    rw [h1, h2]

/-- The fallback tick bound of `fallback_ticks_le` on a window `ℓ+1 = 2k+2`,
in the `∀ δ, k ≤ 4δ → …` shape of `fallbackEv_of_window`. -/
theorem fb_move_of_ticks {fb ℓ k : ℕ} (hfb : fb ≤ 1588*(ℓ+1) + 836) (hwin : ℓ + 1 = 2*k + 2) :
    ∀ δ, k ≤ 4*δ → fb ≤ 12704*δ + 4012 := by
  intro δ hδ
  rw [hwin] at hfb
  omega

/-- The replay bound: `R ≤ k` rounds of `M` ticks each. -/
theorem replay_le_of_rounds {replay R k M : ℕ} (hrep : replay = R * M) (hRk : R ≤ k) :
    replay ≤ 2*M*k := by
  subst hrep
  have : R * M ≤ k * M := Nat.mul_le_mul_right _ hRk
  have e : 2*M*k = k*M + k*M := by ring
  omega

/-- **`fallbackEv_of_landing`.**  The mismatching comparison at `s`
(scan invariant with centre `C = position s.center`, radius `Rad`, the right
head moving onto the mismatch place `right s.right`), the span bookkeeping
(`RadiusRep`, `SpanRep`: window `ℓ+1 = 2·Rad+2`), the stage-window search
contract inputs at the centre (`search_contract_of_stage`), the fallback tick
bound of `fallback_ticks_le` and a replay of `R` rounds of `M` ticks (`R` the
chosen radius, `replay_after_fallback`) give a `FallbackEv M` of radius `Rad`
and chosen radius `R`; its advance is exactly the landing centre's advance
over the old centre, `position t.center = C + (Rad + 1 - R)`. -/
theorem fallbackEv_of_landing (M : ℕ) {raw : List (Fin 2)} {s t : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right) (hav : canRight s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hkC : Rad < position s.center)
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (hraw : raw = (a :: xs).reverse ++ rs' ++ q')
    -- the search contract at the centre (ledger obligation 3, stage window)
    (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) {lower span : ℕ}
    {y : GalilFppWide.Config 12}
    (hraw₀ : raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀)
    (hC₀ : position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀))
    (hspan : Rad ≤ span)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ))
    -- the costs
    (fb replay R : ℕ)
    (hR : R = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
    (hfb : fb ≤ 1588*(ℓ+1) + 836) (hrep : replay = R * M)
    -- the landing centre (`fallback_landing`)
    (hpos : position t.center = position (right s.right) - R) :
    ∃ e : FallbackEv M, e.k = Rad ∧ e.r = R ∧ e.fb = fb ∧ e.replay = replay ∧
      e.adv = Rad + 1 - R ∧ position t.center = position s.center + e.adv := by
  -- window length
  have hwin : ℓ + 1 = 2*Rad + 2 := by
    have h1 : value s.length = 2 * value s.radius + 1 := hS
    have h2 : value s.radius = Rad := hRR.2
    omega
  -- the mismatch place
  have hrpos : position (right s.right) = position s.center + Rad + 1 := by
    have := right_position s.right hav (represented_position _ raw hi.rightRep hi.rightPresent).1
    have h2 := hi.rightPos
    omega
  have hL : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).length
      = position s.center + Rad + 1 := by
    rw [stream_length_of_place a xs rs' q' hdec, hrpos]
  -- the window is `x :: Span`
  have hpal : PalAt (encoded ((a :: xs).reverse ++ rs' ++ q')) (position s.center) Rad := by
    rw [← hraw]; exact hi.palindrome
  obtain ⟨x, hW⟩ := window_eq_cons_span a xs rs' q' (right s.right).gap hL hkC hpal
  rw [← hraw] at hW
  have hWℓ : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)
      = x :: Span raw (position s.center) Rad := by rw [hwin]; exact hW
  -- the span
  have hP : IsPal (Span raw (position s.center) Rad) := isPal_span_of_palAt hi.palindrome
  have hlen : (Span raw (position s.center) Rad).length = 2*Rad + 1 :=
    length_span_of_palAt hi.palindrome
  -- the search contract
  have contract : ∀ p, 0 < p → HasPeriod (Span raw (position s.center) Rad) p → Rad < 2*p := by
    have hc := search_contract_of_stage a₀ ls₀ rs₀ q₀ gap₀ hC₀ hkC hspan
      (by rw [← hraw₀]; exact hi.palindrome) hres hidle (by rw [← hraw₀]; exact hlow)
    rw [← hraw₀] at hc
    exact hc
  -- the chosen radius
  have hRx : R = chosenRadius (x :: Span raw (position s.center) Rad) := by rw [hR, hWℓ]
  have hRk : R ≤ Rad := by
    have h := (chosen_spec (x :: Span raw (position s.center) Rad) (List.cons_ne_nil _ _)).1
    rw [List.length_cons, hlen] at h
    omega
  refine ⟨fallbackEv_of_window M x _ hP Rad fb replay hlen contract
    (fb_move_of_ticks hfb hwin) (replay_le_of_rounds hrep hRk), rfl, hRx.symm, rfl, rfl, ?_, ?_⟩
  · show Rad + 1 - chosenRadius (x :: Span raw (position s.center) Rad) = Rad + 1 - R
    rw [hRx]
  · show position t.center = position s.center + (Rad + 1 - chosenRadius (x :: _))
    rw [← hRx, hpos, hrpos]
    omega

/-- The instance used by the ledger: `M = delay = 2048`. -/
theorem fallbackEv2048_of_landing {raw : List (Fin 2)} {s t : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right) (hav : canRight s.right)
    (hRR : RadiusRep s.radius Rad) (hS : SpanRep s) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hkC : Rad < position s.center)
    (a : Fin 2) (xs rs' q' : List (Fin 2))
    (hdec : right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q')
    (hraw : raw = (a :: xs).reverse ++ rs' ++ q')
    (a₀ : Fin 2) (ls₀ rs₀ q₀ : List (Fin 2)) (gap₀ : Bool) {lower span : ℕ}
    {y : GalilFppWide.Config 12}
    (hraw₀ : raw = (a₀ :: ls₀).reverse ++ rs₀ ++ q₀)
    (hC₀ : position s.center = position (represent ⟨a₀ :: ls₀,gap₀⟩ (rs₀.map some) q₀))
    (hspan : Rad ≤ span)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a₀ :: ls₀,gap₀⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span raw (position s.center) Rad) (2*δ))
    (fb : ℕ) (es : List Bool) (R : ℕ)
    (hR : R = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
    (hfb : fb ≤ 1588*(ℓ+1) + 836) (hes : es.length = R * 2048)
    (hpos : position t.center = position (right s.right) - R) :
    ∃ e : FallbackEv 2048, e.k = Rad ∧ e.r = R ∧ e.fb = fb ∧ e.replay = es.length ∧
      e.adv = Rad + 1 - R ∧ position t.center = position s.center + e.adv :=
  fallbackEv_of_landing 2048 hi hav hRR hS ℓ hv hkC a xs rs' q' hdec hraw a₀ ls₀ rs₀ q₀ gap₀
    hraw₀ hC₀ hspan hres hidle hlow fb es.length R hR hfb hes hpos

#print axioms shiftRun_of_chain
#print axioms shiftEv_of_run
#print axioms shiftEv_of_begin
#print axioms window_eq_cons_span
#print axioms fb_move_of_ticks
#print axioms replay_le_of_rounds
#print axioms fallbackEv_of_landing
#print axioms fallbackEv2048_of_landing

end PalPeg.GalilPlaceEvents
