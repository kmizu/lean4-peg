import PalPeg.GalilScaffoldChainInputSupply

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier GalilScaffoldChainVerifyRun

/-! # Read-based shift origins

`OnlyOrigin` fixes a fresh watch `Run`. After a shift the chain control is no
longer literally the fresh sweep, so a second shift cannot rebuild the same
origin. Here the origin is stated through the actual verifier reads and a
uniform counter offset instead, which every shift and every compare preserve.
-/

/-- The chain control `c` is the reference sweep `d` with all three counters
lowered uniformly by `k`; period, direction and failure agree. This is exactly
the effect of `k` chain shifts, and `consume` commutes with it. -/
structure Offset (k : ℤ) (c d : GalilScaffoldChainConsume.State) : Prop where
  prediction : GalilScaffoldChainPrediction.SamePrediction c d
  broken : c.broken = d.broken
  distance : GalilScaffoldCounter.value c.distance = GalilScaffoldCounter.value d.distance - k
  boundary : GalilScaffoldCounter.value c.boundary = GalilScaffoldCounter.value d.boundary - k
  last : GalilScaffoldCounter.value c.last = GalilScaffoldCounter.value d.last - k

theorem Offset.refl (c : GalilScaffoldChainConsume.State) : Offset 0 c c :=
  ⟨⟨rfl,rfl⟩,rfl,by simp,by simp,by simp⟩

theorem Offset.of_eq {c d : GalilScaffoldChainConsume.State} (h : c = d) : Offset 0 c d := by
  subst h
  exact Offset.refl c

theorem Offset.consume {k : ℤ} {c d : GalilScaffoldChainConsume.State} (h : Offset k c d)
    (seen : Option (Fin 3)) :
    Offset k (GalilScaffoldChainConsume.consume c seen)
      (GalilScaffoldChainConsume.consume d seen) := by
  obtain ⟨⟨hp,hf⟩,hb,hd,hbd,hl⟩ := h
  simp only [GalilScaffoldChainConsume.consume,hp,hf]
  split_ifs <;>
    first
    | exact ⟨⟨rfl,rfl⟩,hb,
        by (try simp only [GalilScaffoldCounter.inc_value]); omega,
        by (try simp only [GalilScaffoldCounter.inc_value]); omega,
        by (try simp only [GalilScaffoldCounter.inc_value]); omega⟩
    | exact ⟨⟨rfl,rfl⟩,rfl,hd,hbd,hl⟩

theorem Offset.run {k : ℤ} {c d : GalilScaffoldChainConsume.State} (h : Offset k c d)
    (xs : List (Fin 3)) :
    Offset k (GalilScaffoldChainSweep.run c xs) (GalilScaffoldChainSweep.run d xs) := by
  induction xs generalizing c d with
  | nil => exact h
  | cons a xs ih => exact ih (h.consume (some a))

theorem Offset.trans {k m : ℤ} {c d e : GalilScaffoldChainConsume.State}
    (h1 : Offset k c d) (h2 : Offset m d e) : Offset (k+m) c e :=
  ⟨⟨h1.prediction.1.trans h2.prediction.1,h1.prediction.2.trans h2.prediction.2⟩,
    h1.broken.trans h2.broken,by rw [h1.distance,h2.distance]; ring,
    by rw [h1.boundary,h2.boundary]; ring,by rw [h1.last,h2.last]; ring⟩

/-- A chain shift of `n` steps lowers the offset by `n` and keeps the reference. -/
theorem Offset.shift {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) {k : ℤ}
    {d : GalilScaffoldChainConsume.State} (h : Offset k w.machine.control d) :
    Offset (k+n) v.machine.control d := by
  obtain ⟨hd,hb,hl,_⟩ := chain_shift_values hr
  refine ⟨⟨(chain_shift_prediction hr).1.trans h.prediction.1,
    (chain_shift_prediction hr).2.trans h.prediction.2⟩,
    (chain_shift_broken hr).trans h.broken,?_,?_,?_⟩
  · rw [hd,h.distance]; ring
  · rw [hb,h.boundary]; ring
  · rw [hl,h.last]; ring

theorem Offset.ordered {k : ℤ} {c d : GalilScaffoldChainConsume.State} (h : Offset k c d)
    (ho : GalilScaffoldChainRestart.Ordered d) : GalilScaffoldChainRestart.Ordered c := by
  unfold GalilScaffoldChainRestart.Ordered at *
  have h1 := h.distance
  have h2 := h.boundary
  have h3 := h.last
  omega

/-- Read-based replacement for `watch_input_cycle`: a successful sweep from
the ready control over the actual reads pins every read symbol. -/
theorem reads_input_cycle {p q : PlaceHead} {pre : List (Fin 3)}
    (hr : Reads p pre q) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none)
    (center b : Fin 3) (xs : List (Fin 3))
    (hb : (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready center xs b) pre).broken = false) :
    position q = position p + pre.length ∧
      ∀ i, i < pre.length → (encoded raw)[position p+(i+1)]? =
        (GalilScaffoldChainSweep.bounce center b xs)[i % (2*(xs.length+1))]? := by
  have he := GalilScaffoldChainPrediction.successful_cycles center b xs pre hb
  refine ⟨reads_position hr raw hh hp,?_⟩
  intro i hi
  have hlen := congrArg List.length he
  simp only [List.length_take] at hlen
  have hb' : i < (GalilScaffoldChainPrediction.cycles
      (GalilScaffoldChainSweep.bounce center b xs) pre.length).length := by omega
  have hx := congrArg (fun w : List (Fin 3) => w[i]?) he
  simp only [List.getElem?_take,hi,if_true] at hx
  rw [GalilScaffoldChainPrediction.cycles_index _ _ _ hb'] at hx
  have hsize : (GalilScaffoldChainSweep.bounce center b xs).length =
      2*(xs.length+1) := by simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hsize,reads_index hr raw hh hp i hi] at hx
  exact hx.symm

/-- Read-based replacement for `watch_previous_window`. -/
theorem reads_previous_window {p q : PlaceHead} {pre : List (Fin 3)}
    (hr : Reads p pre q) (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents p.head raw) (hp : p.head.focus ≠ none)
    (center b : Fin 3) (xs : List (Fin 3))
    (hb : (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready center xs b) pre).broken = false)
    (hfull : 2*(xs.length+1) ≤ pre.length) :
    ∀ k, 0 < k → k ≤ 2*(xs.length+1) →
      (GalilScaffoldChainSweep.bounce center b xs)[(pre.length+k-1) % (2*(xs.length+1))]? =
        (encoded raw)[position q-2*(xs.length+1)+k]? := by
  obtain ⟨hn,hcycle⟩ := reads_input_cycle hr raw hh hp center b xs hb
  intro k hk hkend
  let i := pre.length-2*(xs.length+1)+k-1
  have hi : i < pre.length := by dsimp only [i]; omega
  have he := hcycle i hi
  have hidx : position p+(i+1) = position q-2*(xs.length+1)+k := by dsimp only [i]; omega
  have hadd : pre.length+k-1 = i+2*(xs.length+1) := by dsimp only [i]; omega
  rw [hadd,Nat.add_mod]
  simp only [Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  rw [hidx] at he
  exact he.symm

/-- `m+1` full bounces from an aligned forward state: the last boundary sits
one half period below the final distance. -/
theorem cycles_last (center b : Fin 3) (xs : List (Fin 3)) (m : ℕ)
    (s : GalilScaffoldChainConsume.State)
    (hp : s.period = (GalilScaffoldChainConsume.ready center xs b).period)
    (hf : s.forward = true) :
    let t := GalilScaffoldChainSweep.run s
      (GalilScaffoldChainPrediction.cycles (GalilScaffoldChainSweep.bounce center b xs) (m+1))
    t.period = s.period ∧ t.forward = true ∧
    GalilScaffoldCounter.value t.distance =
      GalilScaffoldCounter.value s.distance + 2*(m+1)*(xs.length+1) ∧
    GalilScaffoldCounter.value t.last =
      GalilScaffoldCounter.value s.distance + (2*m+1)*(xs.length+1) := by
  induction m generalizing s with
  | zero =>
    obtain ⟨hperiod,hd,_,hl,_,hforward,_⟩ := GalilScaffoldChainSweep.round_trip center b xs s hp hf
    simp only [GalilScaffoldChainPrediction.cycles,List.append_nil]
    refine ⟨hperiod,hforward,?_,?_⟩
    · rw [hd]; push_cast; ring
    · rw [hl]; push_cast; ring
  | succ m ih =>
    obtain ⟨hperiod,hd,_,_,_,hforward,_⟩ := GalilScaffoldChainSweep.round_trip center b xs s hp hf
    obtain ⟨hperiod',hforward',hd',hl'⟩ :=
      ih (GalilScaffoldChainSweep.run s (GalilScaffoldChainSweep.bounce center b xs))
        (hperiod.trans hp) hforward
    rw [show GalilScaffoldChainPrediction.cycles (GalilScaffoldChainSweep.bounce center b xs) (m+1+1) =
      GalilScaffoldChainSweep.bounce center b xs ++
        GalilScaffoldChainPrediction.cycles (GalilScaffoldChainSweep.bounce center b xs) (m+1) from rfl,
      GalilScaffoldChainSweep.run_append]
    refine ⟨hperiod'.trans hperiod,hforward',?_,?_⟩
    · rw [hd',hd]; push_cast; ring
    · rw [hl',hd]; push_cast; ring

/-- Multi-period version of `watch_last_lower`, from the sweep alone. -/
theorem sweep_last_lower (center b : Fin 3) (xs actual : List (Fin 3)) (m : ℕ)
    (ha : (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready center xs b) actual).broken = false)
    (hlen : 2*(m+1)*(xs.length+1) ≤ actual.length) :
    ((2*m+1)*(xs.length+1) : ℤ) ≤ GalilScaffoldCounter.value
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) actual).last := by
  let initial := GalilScaffoldChainConsume.ready center xs b
  let word := GalilScaffoldChainSweep.bounce center b xs
  let expected := GalilScaffoldChainPrediction.cycles word (m+1)
  have hcyc := GalilScaffoldChainPrediction.cycles_run center b xs (m+1) initial rfl rfl
  have he : (GalilScaffoldChainSweep.run initial expected).broken = false := hcyc.2.2
  have hexp : expected.length = 2*(m+1)*(xs.length+1) := by
    have hw : word.length = 2*(xs.length+1) := by
      simp [word,GalilScaffoldChainSweep.bounce]; omega
    simp only [expected,GalilScaffoldChainPrediction.cycles_length,hw]; ring
  have hlen' : expected.length ≤ actual.length := by rw [hexp]; exact hlen
  have hp := GalilScaffoldChainPrediction.successful_prefix expected actual initial he ha hlen'
  have hsplit : actual = expected ++ actual.drop expected.length := by
    have heq := List.take_append_drop expected.length actual
    rw [hp] at heq
    exact heq.symm
  have ho : GalilScaffoldChainRestart.Ordered initial := by
    simp [GalilScaffoldChainRestart.Ordered,initial,GalilScaffoldChainConsume.ready,
      GalilScaffoldCounter.reset,GalilScaffoldCounter.value]
  have hm := GalilScaffoldChainRestart.run_order initial expected ho
  have hl := GalilScaffoldChainRestart.run_order (GalilScaffoldChainSweep.run initial expected)
    (actual.drop expected.length) hm.1
  have hlast := (cycles_last center b xs m initial rfl rfl).2.2.2
  have hz : GalilScaffoldCounter.value initial.distance = 0 := rfl
  rw [hz,zero_add] at hlast
  rw [hsplit,GalilScaffoldChainSweep.run_append]
  change ((2*m+1)*(xs.length+1) : ℤ) ≤ GalilScaffoldCounter.value
    (GalilScaffoldChainSweep.run (GalilScaffoldChainSweep.run initial expected)
      (actual.drop expected.length)).last
  have := hl.2
  rw [hlast] at this
  exact this

#print axioms Offset.run
#print axioms Offset.shift
#print axioms reads_previous_window
#print axioms sweep_last_lower

/-- Read-based `shifted_prediction_window`: the reference sweep is reached
through the actual reads and a uniform offset instead of a fresh watch run. -/
theorem read_prediction_window {start w v : GalilScaffoldChainWatch.State}
    {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ} {k : ℤ}
    {pre : List (Fin 3)} (center b : Fin 3) (xs extra : List (Fin 3))
    (hreads : Reads start.machine.verifier pre w.machine.verifier)
    (hoff : Offset k w.machine.control
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre))
    (hb : w.machine.control.broken = false)
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2))
    (hh : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw)
    (hp : start.machine.verifier.head.focus ≠ none)
    (hfull : 2*(xs.length+1) ≤ pre.length)
    (hextra : extra.length < 2*(xs.length+1))
    (hsuccess : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false) :
    GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run v.machine.control extra).period.focus =
      (encoded raw)[position w.machine.verifier-2*(xs.length+1)+(extra.length+1)]? := by
  have hoff' := Offset.shift hr hoff
  have hpred := GalilScaffoldChainPrediction.continued_prediction center b xs pre extra
    v.machine.control hoff'.prediction hoff'.broken hsuccess
  have hb' : (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready center xs b) pre).broken = false := by
    rw [← hoff.broken]; exact hb
  have hwindow := reads_previous_window hreads raw hh hp center b xs hb' hfull
    (extra.length+1) (by omega) (by omega)
  have he : pre.length+(extra.length+1)-1 = pre.length+extra.length := by omega
  rw [he] at hwindow
  exact hpred.trans hwindow

/-- Read-based `shifted_check_pair`. -/
theorem read_check_pair {start w v : GalilScaffoldChainWatch.State}
    {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ} {k : ℤ}
    {pre : List (Fin 3)} (center b : Fin 3) (xs extra : List (Fin 3))
    (hreads : Reads start.machine.verifier pre w.machine.verifier)
    (hoff : Offset k w.machine.control
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre))
    (hb : w.machine.control.broken = false)
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2)) (c radius : ℕ) (l r resumeLeft currentLeft : PlaceHead)
    (hi : ScanInvariant raw c radius l r) (hcan : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right r))
    (hh : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw)
    (hp : start.machine.verifier.head.focus ≠ none)
    (hfull : 2*(xs.length+1) ≤ pre.length)
    (hend : position w.machine.verifier = c+radius+1)
    (hsize : 2*(xs.length+1) ≤ radius) (hextra : extra.length < 2*(xs.length+1))
    (hsuccess : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false)
    (hresume : ScanInvariant raw (c+(xs.length+1)) (radius+1-(xs.length+1))
      resumeLeft (right r))
    (hmoves : LeftMoves resumeLeft (extra.length+1) currentLeft) :
    (GalilScaffoldInputHead.read currentLeft = GalilScaffoldChainConsume.symbol
      (GalilScaffoldChainSweep.run v.machine.control extra).period.focus ↔
      extra.length+1 < 2*(xs.length+1)) := by
  have hpred := read_prediction_window center b xs extra hreads hoff hb hr raw hh hp
    hfull hextra hsuccess
  obtain ⟨hlrep,hmpos⟩ := left_moves_position hmoves raw hresume.leftRep
  have hrespos := hresume.leftPos
  have hlt := scan_radius_lt hi
  have hlpos : (position currentLeft : ℤ) =
      (c : ℤ)-radius-1+2*(xs.length+1)-(extra.length+1) := by omega
  rw [hend] at hpred
  rw [represented_signed_read currentLeft raw hlrep,hlpos,hpred]
  exact scan_continuation_pair hi hcan hne (xs.length+1) (extra.length+1)
    (fun i => (encoded raw)[c+radius+1-2*(xs.length+1)+i]?)
    hsize (by omega) (by omega) (by intros; rfl)

/-- Read-based `only_history_check_pair`. -/
theorem read_history_check_pair {start w v current : GalilScaffoldChainWatch.State}
    {s t : ShiftState} {cycle finish currentCycle : GalilScaffoldCounter.Counter}
    {n : ℕ} {k : ℤ} {pre : List (Fin 3)} (center b : Fin 3) (xs extra : List (Fin 3))
    (hreads : Reads start.machine.verifier pre w.machine.verifier)
    (hoff : Offset k w.machine.control
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready center xs b) pre))
    (hb : w.machine.control.broken = false)
    (hr : ChainShiftRun s w cycle n t v finish)
    (raw : List (Fin 2)) (c radius currentCenter currentRadius : ℕ)
    (l r resumeLeft currentLeft currentRight : PlaceHead)
    (hi : ScanInvariant raw c radius l r) (hcan : canRight r)
    (hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right r))
    (hh : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw)
    (hp : start.machine.verifier.head.focus ≠ none)
    (hfull : 2*(xs.length+1) ≤ pre.length)
    (hend : position w.machine.verifier = c+radius+1) (hsize : 2*(xs.length+1) ≤ radius)
    (hresume : ScanInvariant raw (c+(xs.length+1)) (radius+1-(xs.length+1))
      resumeLeft (right r))
    (hcurrent : OnlyScan raw currentCenter currentRadius (2*(xs.length+1)) extra.length
      currentLeft currentRight current currentCycle)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine)
    (hl : LeftMoves resumeLeft extra.length currentLeft) :
    GalilScaffoldCounter.positive currentCycle = true ∧
      (GalilScaffoldInputHead.read (GalilScaffoldInputHead.left currentLeft) =
        GalilScaffoldChainConsume.symbol current.machine.control.period.focus ↔
        GalilScaffoldCounter.singlePositive currentCycle = false) := by
  have hsuccess : (GalilScaffoldChainSweep.run v.machine.control extra).broken = false := by
    rw [← ht.control]
    exact hcurrent.caught.unbroken
  have hmoves := left_moves_append hl
    (LeftMoves.next currentLeft hcurrent.caught.scan.leftPresent (.stop _))
  have hpair := read_check_pair center b xs extra hreads hoff hb hr raw c radius l r resumeLeft
    (GalilScaffoldInputHead.left currentLeft) hi hcan hne hh hp hfull hend hsize
    hcurrent.available hsuccess hresume hmoves
  rw [← ht.control] at hpair
  obtain ⟨hpositive,hdispatch⟩ := only_scan_dispatch hcurrent
  refine ⟨hpositive,hpair.trans ?_⟩
  have havail := hcurrent.available
  cases hc : GalilScaffoldCounter.singlePositive currentCycle with
  | false =>
    have hn : extra.length+1 ≠ 2*(xs.length+1) := by
      intro he
      have := hdispatch.mpr he
      simp [hc] at this
    simp only [Bool.false_eq_true,iff_true]
    omega
  | true =>
    have he := hdispatch.mp hc
    simp only [Bool.true_eq_false,iff_false]
    omega

/-- Read-based `watch_shift_last_positive`: only the control invariants at the
shift origin are needed, not the fresh watch run. -/
theorem read_last_positive {w v : GalilScaffoldChainWatch.State}
    {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish)
    (ho : GalilScaffoldChainRestart.Ordered w.machine.control)
    (hl : GalilScaffoldCounter.Canonical w.machine.control.last)
    (hb : GalilScaffoldCounter.Canonical w.machine.control.boundary)
    (hd : GalilScaffoldCounter.Canonical w.machine.control.distance)
    (hpos : (n : ℤ) < GalilScaffoldCounter.value w.machine.control.last)
    (extra : List (Fin 3)) :
    GalilScaffoldCounter.positive
      (GalilScaffoldChainSweep.run v.machine.control extra).last = true :=
  chain_shift_future_last hr ho hl hb hd hpos extra

/-- Read-based `history_terminal_last`. -/
theorem read_terminal_last {w v current : GalilScaffoldChainWatch.State}
    {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (extra : List (Fin 3))
    (hr : ChainShiftRun s w cycle n t v finish)
    (ho : GalilScaffoldChainRestart.Ordered w.machine.control)
    (hl : GalilScaffoldCounter.Canonical w.machine.control.last)
    (hb : GalilScaffoldCounter.Canonical w.machine.control.boundary)
    (hd : GalilScaffoldCounter.Canonical w.machine.control.distance)
    (hpos : (n : ℤ) < GalilScaffoldCounter.value w.machine.control.last)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine) :
    GalilScaffoldCounter.positive (consume current.machine).control.last = true := by
  cases ha : GalilScaffoldInputHead.read (right current.machine.verifier) with
  | none =>
    have hl' := read_last_positive hr ho hl hb hd hpos extra
    rw [← ht.control] at hl'
    cases htoken : GalilScaffoldChainConsume.symbol current.machine.control.period.focus <;>
      simpa [consume,ha,GalilScaffoldChainConsume.consume,htoken] using hl'
  | some a =>
    have hl' := read_last_positive hr ho hl hb hd hpos (extra ++ [a])
    rw [GalilScaffoldChainSweep.run_append,← ht.control] at hl'
    simpa [consume,ha,GalilScaffoldChainSweep.run] using hl'

/-- Read-based `history_terminal_canonical`. -/
theorem read_terminal_canonical {w v current : GalilScaffoldChainWatch.State}
    {s t : ShiftState} {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (extra : List (Fin 3))
    (hr : ChainShiftRun s w cycle n t v finish)
    (hl : GalilScaffoldCounter.Canonical w.machine.control.last)
    (hb : GalilScaffoldCounter.Canonical w.machine.control.boundary)
    (hd : GalilScaffoldCounter.Canonical w.machine.control.distance)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra current.machine) :
    GalilScaffoldCounter.Canonical (consume current.machine).control.last := by
  have hv := chain_shift_control_canonical hr hl hb hd
  have hcurrent := GalilScaffoldChainRestart.run_canonical v.machine.control extra
    hv.1 hv.2.1 hv.2.2
  rw [← ht.control] at hcurrent
  exact (GalilScaffoldChainRestart.consume_canonical current.machine.control _
    hcurrent.1 hcurrent.2.1 hcurrent.2.2).1

/-- Read-based `only_compare_restart`. -/
theorem read_compare_restart {s t : OnlyCompareState} {n : ℕ}
    (run : OnlyCompareRun s n t)
    {w v : GalilScaffoldChainWatch.State}
    {shiftStart shiftEnd : ShiftState} {cycle finish : GalilScaffoldCounter.Counter}
    (xs extra : List (Fin 3))
    (hr : ChainShiftRun shiftStart w cycle (xs.length+1) shiftEnd v finish)
    (ho : GalilScaffoldChainRestart.Ordered w.machine.control)
    (hcl : GalilScaffoldCounter.Canonical w.machine.control.last)
    (hcb : GalilScaffoldCounter.Canonical w.machine.control.boundary)
    (hcd : GalilScaffoldCounter.Canonical w.machine.control.distance)
    (hpos : ((xs.length+1 : ℕ) : ℤ) < GalilScaffoldCounter.value w.machine.control.last)
    {raw : List (Fin 2)} {center radius : ℕ} {initialLeft : PlaceHead}
    (hi : OnlyScan raw center radius (2*(xs.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace v.machine extra s.watch.machine)
    (hl : LeftMoves initialLeft extra.length s.left)
    (hcenter : GalilScaffoldInputHead.read s.center ≠ none)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hcheck : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldChainConsume.symbol t.watch.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive t.cycle = false)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldInputHead.read (right t.right)) :
    let endState := onlyCompareNext t
    ScanInvariant raw center (radius+n+1) endState.left endState.right ∧
      endState.watch.machine.control.broken = true ∧
      GalilScaffoldCounter.negative endState.watch.margin = false ∧
      GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
      GalilScaffoldCounter.zero endState.watch.lag = true ∧
      GalilScaffoldInputHead.read endState.center ≠ none ∧
      RadiusRep endState.radius (radius+n+1) ∧
      GalilScaffoldCounter.negative endState.radius = false ∧
      (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
        endState.radius).work = endState.watch.machine.control.last ∧
      GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  obtain ⟨heq,actual,_,htrace,_,hscan,hcr,hra⟩ :=
    only_compare_history run extra hi hcredit hrad ht hl
  obtain ⟨hscan',hbroken,hmargin,hrad',hnonneg⟩ :=
    only_terminal_radius hscan hcr hra hend hc hcheck hmatch
  have hlast := read_terminal_last actual hr ho hcl hcb hcd hpos htrace
  have hz := hscan.caught.lagZero
  have hread : GalilScaffoldInputHead.read t.center ≠ none := by
    rw [heq]
    exact hcenter
  exact ⟨hscan',hbroken,hmargin,hlast,hz,hread,hrad',hnonneg,
    (GalilScaffoldSearchFinish.begin_positive _ _ hlast).2.1,
    read_terminal_canonical actual hr hcl hcb hcd htrace⟩

#print axioms read_history_check_pair
#print axioms read_compare_restart

theorem phase_four_consume (s : GalilScaffoldChainConsume.State) (seen : Option (Fin 3))
    (h : s.phase = 4) : (GalilScaffoldChainConsume.consume s seen).phase = 4 := by
  have h1 := GalilScaffoldChainPrediction.consume_phase_mono s seen
  rw [h] at h1
  change 4 ≤ (GalilScaffoldChainConsume.consume s seen).phase.val at h1
  have h2 := (GalilScaffoldChainConsume.consume s seen).phase.isLt
  exact Fin.ext (by change _ = 4; omega)

theorem phase_four_run (s : GalilScaffoldChainConsume.State) (xs : List (Fin 3))
    (h : s.phase = 4) : (GalilScaffoldChainSweep.run s xs).phase = 4 := by
  induction xs generalizing s with
  | nil => exact h
  | cons a xs ih => exact ih _ (phase_four_consume s (some a) h)

theorem chain_shift_phase {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : GalilScaffoldCounter.Counter} {n : ℕ}
    (hr : ChainShiftRun s w cycle n t v finish) :
    v.machine.control.phase = w.machine.control.phase := by
  induction hr with
  | stop s w cycle => rfl
  | next s w cycle he hc hl hl' rest ih => exact ih

/-- A shift origin stated through the actual reads since the fresh start and
the uniform counter offset accumulated by `shifts` earlier shifts. Fresh
origins have `shifts = 0`; every further shift rebuilds one of these. -/
structure ReadOrigin (raw : List (Fin 2)) where
  start : GalilScaffoldChainWatch.State
  watched : GalilScaffoldChainWatch.State
  shifted : GalilScaffoldChainWatch.State
  pre : List (Fin 3)
  shifts : ℕ
  shiftStart : ShiftState
  shiftEnd : ShiftState
  cycle : GalilScaffoldCounter.Counter
  finish : GalilScaffoldCounter.Counter
  center : ℕ
  radius : ℕ
  left : PlaceHead
  rightHead : PlaceHead
  resumeLeft : PlaceHead
  token : Fin 3
  boundary : Fin 3
  interior : List (Fin 3)
  reads : Reads start.machine.verifier pre watched.machine.verifier
  offset : Offset ((shifts*(interior.length+1) : ℕ) : ℤ) watched.machine.control
    (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready token interior boundary) pre)
  unbroken : watched.machine.control.broken = false
  phase : watched.machine.control.phase = 4
  canonicalLast : GalilScaffoldCounter.Canonical watched.machine.control.last
  canonicalBoundary : GalilScaffoldCounter.Canonical watched.machine.control.boundary
  canonicalDistance : GalilScaffoldCounter.Canonical watched.machine.control.distance
  length : 2*(shifts+2)*(interior.length+1) ≤ pre.length
  shiftRun : ChainShiftRun shiftStart watched cycle (interior.length+1) shiftEnd shifted finish
  scan : ScanInvariant raw center radius left rightHead
  available : canRight rightHead
  mismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left left) ≠
    GalilScaffoldInputHead.read (right rightHead)
  represents : GalilScaffoldInputTrace.Represents start.machine.verifier.head raw
  present : start.machine.verifier.head.focus ≠ none
  startBefore : position start.machine.verifier ≤ center
  endPosition : position watched.machine.verifier = center+radius+1
  size : 2*(interior.length+1) ≤ radius
  resumed : ScanInvariant raw (center+(interior.length+1))
    (radius+1-(interior.length+1)) resumeLeft (right rightHead)

namespace ReadOrigin

variable {raw : List (Fin 2)}

theorem sweep_unbroken (o : ReadOrigin raw) :
    (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready o.token o.interior o.boundary) o.pre).broken = false := by
  rw [← o.offset.broken]; exact o.unbroken

theorem shifted_phase (o : ReadOrigin raw) : o.shifted.machine.control.phase = 4 := by
  rw [chain_shift_phase o.shiftRun]; exact o.phase

theorem full (o : ReadOrigin raw) : 2*(o.interior.length+1) ≤ o.pre.length :=
  le_trans (Nat.mul_le_mul_right _ (by omega)) o.length

theorem ordered (o : ReadOrigin raw) : GalilScaffoldChainRestart.Ordered o.watched.machine.control := by
  have hinit : GalilScaffoldChainRestart.Ordered
      (GalilScaffoldChainConsume.ready o.token o.interior o.boundary) := by
    simp [GalilScaffoldChainRestart.Ordered,GalilScaffoldChainConsume.ready,
      GalilScaffoldCounter.reset,GalilScaffoldCounter.value]
  exact o.offset.ordered (GalilScaffoldChainRestart.run_order _ o.pre hinit).1

/-- The last boundary at the origin exceeds one half period, with `shifts`
half periods of slack already spent on earlier shifts. -/
theorem last_lower (o : ReadOrigin raw) :
    ((o.interior.length+1 : ℕ) : ℤ) < GalilScaffoldCounter.value o.watched.machine.control.last := by
  have hl := sweep_last_lower o.token o.boundary o.interior o.pre (o.shifts+1) o.sweep_unbroken
    (by have := o.length; omega)
  have hoff := o.offset.last
  have hk : (0:ℤ) ≤ (o.shifts : ℤ) * ((o.interior.length : ℤ)+1) := by positivity
  push_cast at hl hoff ⊢
  nlinarith [hl,hoff,hk]

theorem check_pair (o : ReadOrigin raw)
    {c radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw c radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus ↔
      GalilScaffoldCounter.singlePositive s.cycle = false :=
  (read_history_check_pair o.token o.boundary o.interior extra o.reads o.offset o.unbroken
    o.shiftRun raw o.center o.radius c radius o.left o.rightHead o.resumeLeft s.left s.right
    o.scan o.available o.mismatch o.represents o.present o.full o.endPosition o.size
    o.resumed hi ht hl).2

theorem joined_reads (o : ReadOrigin raw)
    {current : GalilScaffoldChainVerifier.State} (extra : List (Fin 3))
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra current)
    (hb : current.control.broken = false) :
    Reads o.start.machine.verifier (o.pre ++ extra) current.verifier ∧
      (GalilScaffoldChainSweep.run
        (GalilScaffoldChainConsume.ready o.token o.interior o.boundary)
        (o.pre ++ extra)).broken = false := by
  have hver := (chain_shift_values o.shiftRun).2.2.2.2.2.1
  have hreads : Reads o.watched.machine.verifier extra current.verifier := by
    simpa only [hver] using ht.reads
  have hoff := (Offset.shift o.shiftRun o.offset).run extra
  rw [← ht.control,← GalilScaffoldChainSweep.run_append] at hoff
  refine ⟨GalilScaffoldChainVerifyRun.reads_append o.reads hreads,?_⟩
  rw [← hoff.broken]
  exact hb

theorem joined_input_period (o : ReadOrigin raw)
    {current : GalilScaffoldChainVerifier.State} (extra : List (Fin 3))
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra current)
    (hb : current.control.broken = false) :
    ∀ j, position o.start.machine.verifier < j →
      j+2*(o.interior.length+1) ≤ position current.verifier →
      (encoded raw)[j]? = (encoded raw)[j+2*(o.interior.length+1)]? := by
  obtain ⟨hreads,hsuccess⟩ := o.joined_reads extra ht hb
  have he := GalilScaffoldChainPrediction.successful_cycles
    o.token o.boundary o.interior (o.pre ++ extra) hsuccess
  have hp := hasPeriod_take (k := (o.pre ++ extra).length)
    (GalilScaffoldChainPrediction.cycles_period
      (GalilScaffoldChainSweep.bounce o.token o.boundary o.interior) (o.pre ++ extra).length)
  rw [he] at hp
  have hlen : (GalilScaffoldChainSweep.bounce o.token o.boundary o.interior).length =
      2*(o.interior.length+1) := by simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hlen] at hp
  have hpos := reads_position hreads raw o.represents o.present
  intro j hj hbound
  let i := j-position o.start.machine.verifier-1
  have hi : i+2*(o.interior.length+1) < (o.pre ++ extra).length := by dsimp [i]; omega
  have hperiod := hp i hi
  rw [reads_index hreads raw o.represents o.present i (by omega),
    reads_index hreads raw o.represents o.present (i+2*(o.interior.length+1)) hi] at hperiod
  have h1 : position o.start.machine.verifier+(i+1) = j := by dsimp [i]; omega
  have h2 : position o.start.machine.verifier+(i+2*(o.interior.length+1)+1) =
      j+2*(o.interior.length+1) := by dsimp [i]; omega
  simpa only [h1,h2] using hperiod

theorem reshift_compare (o : ReadOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus) :
    GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
      GalilScaffoldInputHead.read (right s.right) ∧
    GalilScaffoldChainWatch.Good s.watch ∧
    GalilScaffoldChainVerifyRun.Run s.watch.machine 1 (consume s.watch.machine) ∧
    (consume s.watch.machine).control.broken = false ∧
    ∃ a, (extra ++ [a]).length = 2*(o.interior.length+1) ∧
      GalilScaffoldChainWatchTrace.Trace o.shifted.machine (extra ++ [a])
        (consume s.watch.machine) ∧
      LeftMoves o.resumeLeft (extra ++ [a]).length
        (GalilScaffoldInputHead.left s.left) := by
  have hcheck := o.check_pair extra hi ht hl
  have hne : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.left) ≠
      GalilScaffoldInputHead.read (right s.right) := by
    intro he
    have hf := hcheck.mp (he.trans hprediction)
    simp [hend] at hf
  obtain ⟨hg,hr,hb⟩ := matched_left_prediction s.watch s.right (right s.right) raw
    hi.caught.verifierRep hi.caught.scan.rightRep hi.caught.verifierPresent
    hi.caught.scan.rightPresent hc hi.caught.aligned hprediction rfl
  obtain ⟨a,ha⟩ := GalilScaffoldChainWatchTrace.one hg
  have hlength := (only_scan_dispatch hi).2.mp hend
  have hleft := left_moves_append hl
    (LeftMoves.next s.left hi.caught.scan.leftPresent (.stop _))
  refine ⟨hne,hg,hr,hb.trans hi.caught.unbroken,a,?_,
    GalilScaffoldChainWatchTrace.append ht ha,?_⟩
  · simpa only [List.length_append,List.length_singleton] using hlength
  · simpa only [List.length_append,List.length_singleton] using hleft

theorem reshift_palindrome (o : ReadOrigin raw)
    {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw (o.center+(o.interior.length+1)) (o.radius+(o.interior.length+1))
      (2*(o.interior.length+1)) extra.length s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hprediction : GalilScaffoldInputHead.read (right s.right) =
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus) :
    Manacher.PalAt (encoded raw) (o.center+2*(o.interior.length+1)) (o.radius+1) := by
  obtain ⟨_,hg,_,hb,a,_,htrace,_⟩ := o.reshift_compare extra hi ht hl hend hc hprediction
  have hperiod := o.joined_input_period (extra ++ [a]) htrace hb
  have hvpos := right_position s.watch.machine.verifier hg.1
    (represented_position _ raw hi.caught.verifierRep hi.caught.verifierPresent).1
  have hrpos := right_position s.right hc
    (represented_position _ raw hi.caught.scan.rightRep hi.caught.scan.rightPresent).1
  have hpos : position (consume s.watch.machine).verifier =
      o.center+(o.interior.length+1)+(o.radius+(o.interior.length+1))+1 := by
    change position (right s.watch.machine.verifier) = _
    rw [hvpos,hi.caught.aligned,hi.caught.scan.rightPos]
  have hbound := position_bound (right s.right) raw
    (right_word s.right raw hi.caught.scan.rightRep hc)
    (right_present s.right raw hi.caught.scan.rightRep hi.caught.scan.rightPresent hc)
  rw [hrpos,hi.caught.scan.rightPos] at hbound
  have hstart := o.startBefore
  apply reshift_from_right (encoded raw) o.center o.radius (o.interior.length+1)
    ⟨by have := o.scan.palindrome.1; have := o.size; omega,
      by have := o.scan.palindrome.2.1; have := o.size; omega,
      fun i hi => o.scan.palindrome.2.2 i (by have := o.size; omega)⟩
      hi.caught.scan.palindrome (by omega) (by have := o.size; omega) hbound
  intro j hj hj'
  apply hperiod j (by omega)
  rw [hpos]
  exact hj'

theorem matched_checked (o : ReadOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t)
    {center radius : ℕ} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left) : OnlyCompareRun s n t := by
  induction run generalizing radius extra with
  | stop s => exact .stop s
  | next s available continuing matched rest ih =>
    have hcheck := o.check_pair extra hi ht hl
    obtain ⟨a,ht',hl',hi',hcredit',hrad'⟩ :=
      only_history_matched extra hi hcredit s.radius hrad ht hl
        available continuing hcheck matched
    exact .next s available continuing hcheck matched
      (ih (extra ++ [a]) hi' hcredit' hrad' ht' hl')

/-- Read-based `only_matched_restart`; the distance lower bound is now carried
by the origin itself. -/
theorem matched_restart (o : ReadOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t)
    {center radius : ℕ} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle) (hrad : RadiusRep s.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hcenter : GalilScaffoldInputHead.read s.center ≠ none)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldInputHead.read (right t.right)) :
    let endState := onlyCompareNext t
    ScanInvariant raw center (radius+n+1) endState.left endState.right ∧
      endState.watch.machine.control.broken = true ∧
      GalilScaffoldCounter.negative endState.watch.margin = false ∧
      GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
      GalilScaffoldCounter.zero endState.watch.lag = true ∧
      GalilScaffoldInputHead.read endState.center ≠ none ∧
      RadiusRep endState.radius (radius+n+1) ∧
      GalilScaffoldCounter.negative endState.radius = false ∧
      (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
        endState.radius).work = endState.watch.machine.control.last ∧
      GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  have checked := o.matched_checked run extra hi hcredit hrad ht hl
  obtain ⟨_,actual,_,htrace,hleft,hscan,_,_⟩ :=
    only_compare_history checked extra hi hcredit hrad ht hl
  have hcheck := o.check_pair actual hscan htrace hleft
  exact read_compare_restart checked o.interior extra o.shiftRun o.ordered o.canonicalLast
    o.canonicalBoundary o.canonicalDistance o.last_lower hi hcredit hrad ht hl hcenter
    hend hc hcheck hmatch

/-- A fresh origin (`OnlyOrigin`) is a read origin with no earlier shift, once
its watched distance has reached four half periods. -/
theorem ofOnly (o : OnlyOrigin raw) (hsteps : o.steps = o.interior.length+1)
    (hd : 4*(o.interior.length+1) ≤
      GalilScaffoldCounter.value o.watched.machine.control.distance)
    (hphase : o.watched.machine.control.phase = 4) :
    ∃ o' : ReadOrigin raw, o'.start = o.start ∧ o'.watched = o.watched ∧
      o'.shifted = o.shifted ∧ o'.shifts = 0 ∧ o'.center = o.center ∧ o'.radius = o.radius ∧
      o'.interior = o.interior ∧ o'.token = o.token ∧ o'.boundary = o.boundary ∧
      o'.resumeLeft = o.resumeLeft ∧ o'.rightHead = o.rightHead ∧ o'.left = o.left := by
  obtain ⟨pre,ht,_⟩ := GalilScaffoldChainWatchTrace.run_trace o.watchRun
  have hcontrol : o.watched.machine.control = GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready o.token o.interior o.boundary) pre := by
    rw [ht.control,o.ready]
  have hc := GalilScaffoldChainRestart.run_canonical
    (GalilScaffoldChainConsume.ready o.token o.interior o.boundary) pre
    (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  rw [← hcontrol] at hc
  have hv := ht.distance
  rw [o.ready] at hv
  have hz : GalilScaffoldCounter.value
      (GalilScaffoldChainConsume.ready o.token o.interior o.boundary).distance = 0 := rfl
  rw [hz,zero_add] at hv
  refine ⟨{
      start := o.start
      watched := o.watched
      shifted := o.shifted
      pre := pre
      shifts := 0
      shiftStart := o.shiftStart
      shiftEnd := o.shiftEnd
      cycle := o.cycle
      finish := o.finish
      center := o.center
      radius := o.radius
      left := o.left
      rightHead := o.rightHead
      resumeLeft := o.resumeLeft
      token := o.token
      boundary := o.boundary
      interior := o.interior
      reads := ht.reads
      offset := by simpa using Offset.of_eq hcontrol
      unbroken := by rw [ht.broken,o.ready]; rfl
      phase := hphase
      canonicalLast := hc.1
      canonicalBoundary := hc.2.1
      canonicalDistance := hc.2.2
      length := by omega
      shiftRun := by simpa only [hsteps] using o.shiftRun
      scan := o.scan
      available := o.available
      mismatch := o.mismatch
      represents := o.represents
      present := o.present
      startBefore := le_of_eq o.startPosition
      endPosition := o.endPosition
      size := o.size
      resumed := o.resumed },
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- After a full period of matched comparisons ending at `cycleEnd`, with the
predicted right symbol actually present, the re-shift by one half period
yields a new read origin: centre and radius grow by a half period, one more
shift is accounted for, and the resumed comparison entry is returned. -/
theorem reshift_origin (o : ReadOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t)
    (hi : OnlyScan raw (o.center+(o.interior.length+1))
      (o.radius+1-(o.interior.length+1)) (2*(o.interior.length+1)) 0
      s.left s.right s.watch s.cycle)
    (hcredit : OnlyCredit s.watch s.cycle)
    (hrad : RadiusRep s.radius (o.radius+1-(o.interior.length+1)))
    (hmachine : s.watch.machine = o.shifted.machine) (hleft : s.left = o.resumeLeft)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hprediction : GalilScaffoldInputHead.read (right t.right) =
      GalilScaffoldChainConsume.symbol t.watch.machine.control.period.focus)
    (hcenter : GalilScaffoldInputTrace.Represents t.center.head raw)
    (hpcenter : t.center.head.focus ≠ none)
    (hpos : position t.center = o.center+(o.interior.length+1))
    (lengthCounter : GalilScaffoldCounter.Counter)
    (hlen : GalilScaffoldCounter.Canonical lengthCounter) :
    ∃ (o' : ReadOrigin raw) (t' : ShiftState) (v : GalilScaffoldChainWatch.State)
      (cycle : GalilScaffoldCounter.Counter),
      o'.start = o.start ∧ o'.center = o.center+(o.interior.length+1) ∧
      o'.radius = o.radius+(o.interior.length+1) ∧ o'.interior = o.interior ∧
      o'.token = o.token ∧ o'.boundary = o.boundary ∧ o'.shifts = o.shifts+1 ∧
      o'.shifted = v ∧ o'.resumeLeft = t'.left ∧ o'.rightHead = t.right ∧
      o'.watched = GalilScaffoldChainWatch.immediate t.watch ∧
      position t'.center = o.center+2*(o.interior.length+1) ∧
      ShiftRun ⟨t.center,GalilScaffoldInputHead.left t.left,
        GalilScaffoldCounter.ofNat (o.interior.length+1),
        GalilScaffoldCounter.inc t.radius,lengthCounter⟩ (o.interior.length+1) t' ∧
      ChainShiftRun ⟨t.center,GalilScaffoldInputHead.left t.left,
        GalilScaffoldCounter.ofNat (o.interior.length+1),
        GalilScaffoldCounter.inc t.radius,lengthCounter⟩
        (GalilScaffoldChainWatch.immediate t.watch) GalilScaffoldCounter.reset
        (o.interior.length+1) t' v cycle ∧
      OnlyScan raw (position t'.center) (o.radius+1) (2*(o.interior.length+1)) 0
        t'.left (right t.right) v cycle ∧ OnlyCredit v cycle ∧
      RadiusRep t'.radius (o.radius+1) := by
  have ht0 : GalilScaffoldChainWatchTrace.Trace o.shifted.machine [] s.watch.machine := by
    rw [hmachine]
    exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o.resumeLeft 0 s.left := by rw [hleft]; exact .stop _
  have checked := o.matched_checked run [] hi hcredit hrad ht0 hl0
  obtain ⟨_,actual,hlen',htrace,hleft',hscan,hcredit',hrad'⟩ :=
    only_compare_history checked [] hi hcredit hrad ht0 hl0
  have hcount := (only_scan_dispatch hscan).2.mp hend
  simp only [List.length_nil,Nat.zero_add] at hlen' hcount
  have hr : o.radius+1-(o.interior.length+1)+n = o.radius+(o.interior.length+1) := by
    have := o.size
    omega
  rw [hr] at hscan hrad'
  obtain ⟨hne,hg,_,hb,a,hlen2,htrace2,_⟩ :=
    o.reshift_compare actual hscan htrace hleft' hend hc hprediction
  have hpal := o.reshift_palindrome actual hscan htrace hleft' hend hc hprediction
  -- geometry of the terminal compare
  have hv := right_word t.watch.machine.verifier raw hscan.caught.verifierRep hg.1
  have hp := right_present t.watch.machine.verifier raw hscan.caught.verifierRep
    hscan.caught.verifierPresent hg.1
  have hvpos := right_position t.watch.machine.verifier hg.1
    (represented_position _ raw hscan.caught.verifierRep hscan.caught.verifierPresent).1
  have hrpos := right_position t.right hc
    (represented_position _ raw hscan.caught.scan.rightRep hscan.caught.scan.rightPresent).1
  have halign : position (consume t.watch.machine).verifier = position (right t.right) := by
    change position (right t.watch.machine.verifier) = _
    rw [hvpos,hrpos,hscan.caught.aligned]
  have hend' : position (consume t.watch.machine).verifier =
      o.center+(o.interior.length+1)+(o.radius+(o.interior.length+1))+1 := by
    change position (right t.watch.machine.verifier) = _
    rw [hvpos,hscan.caught.aligned,hscan.caught.scan.rightPos]
  have hcounter : GalilScaffoldCounter.value (GalilScaffoldCounter.inc t.radius) =
      ((o.radius+(o.interior.length+1) : ℕ) : ℤ)+1 := by
    rw [GalilScaffoldCounter.inc_value,hrad'.2]
  have hcycle := (GalilScaffoldCounter.singlePositive_iff t.cycle hscan.canonical).1 hend
  have hm : 0 ≤ GalilScaffoldCounter.value (GalilScaffoldChainWatch.immediate t.watch).margin := by
    change 0 ≤ GalilScaffoldCounter.value (GalilScaffoldCounter.inc t.watch.margin)
    rw [GalilScaffoldCounter.inc_value]
    have := hcredit'.2
    omega
  have hscan' : ScanInvariant raw (position t.center) (o.radius+(o.interior.length+1))
      t.left t.right := by simpa only [hpos] using hscan.caught.scan
  have he : o.radius+(o.interior.length+1)+1-(o.interior.length+1) = o.radius+1 := by omega
  have hnew : Manacher.PalAt (encoded raw) (position t.center+(o.interior.length+1))
      (o.radius+(o.interior.length+1)+1-(o.interior.length+1)) := by
    have hc' : position t.center+(o.interior.length+1) = o.center+2*(o.interior.length+1) := by
      rw [hpos]; omega
    rw [he,hc']
    exact hpal
  obtain ⟨t',v,cycle,hrun,hchain,_,hs,hcr,hra,_⟩ :=
    shift_to_only_initialized raw t.center t.left t.right (o.radius+(o.interior.length+1))
      (o.interior.length+1) (GalilScaffoldCounter.inc t.radius) lengthCounter
      (GalilScaffoldChainWatch.immediate t.watch) hcounter
      (GalilScaffoldCounter.inc_canonical _ hrad'.1) hlen
      (GalilScaffoldCounter.inc_canonical _ hcredit'.1) hm hcenter hpcenter hscan'
      (by omega) (by omega) hc hnew hv hp halign hscan.caught.lagZero hb
  obtain ⟨_,_,hposc⟩ := shift_run_center hrun raw hcenter hpcenter
  have hposc' : position t'.center = o.center+2*(o.interior.length+1) := by
    rw [hposc,hpos]; omega
  -- the new origin's read history and control offset
  have hver := (chain_shift_values o.shiftRun).2.2.2.2.2.1
  have hreads2 : Reads o.watched.machine.verifier (actual ++ [a])
      (consume t.watch.machine).verifier := by
    simpa only [hver] using htrace2.reads
  have hoff2 := (Offset.shift o.shiftRun o.offset).run (actual ++ [a])
  rw [← htrace2.control,← GalilScaffoldChainSweep.run_append] at hoff2
  have hk : (((o.shifts+1)*(o.interior.length+1) : ℕ) : ℤ) =
      ((o.shifts*(o.interior.length+1) : ℕ) : ℤ)+((o.interior.length+1 : ℕ) : ℤ) := by
    push_cast; ring
  have hcs := chain_shift_control_canonical o.shiftRun o.canonicalLast o.canonicalBoundary
    o.canonicalDistance
  have hcanon := GalilScaffoldChainRestart.run_canonical o.shifted.machine.control
    (actual ++ [a]) hcs.1 hcs.2.1 hcs.2.2
  rw [← htrace2.control] at hcanon
  have hphase' : (GalilScaffoldChainWatch.immediate t.watch).machine.control.phase = 4 := by
    change (GalilScaffoldChainConsume.consume t.watch.machine.control _).phase = 4
    apply phase_four_consume
    rw [htrace.control]
    exact phase_four_run _ _ o.shifted_phase
  have hlength : 2*(o.shifts+1+2)*(o.interior.length+1) ≤ (o.pre ++ (actual ++ [a])).length := by
    rw [List.length_append,hlen2]
    have h2 : 2*(o.shifts+1+2)*(o.interior.length+1) =
        2*(o.shifts+2)*(o.interior.length+1)+2*(o.interior.length+1) := by ring
    have := o.length
    omega
  refine ⟨{
      start := o.start
      watched := GalilScaffoldChainWatch.immediate t.watch
      shifted := v
      pre := o.pre ++ (actual ++ [a])
      shifts := o.shifts+1
      shiftStart := ⟨t.center,GalilScaffoldInputHead.left t.left,
        GalilScaffoldCounter.ofNat (o.interior.length+1),
        GalilScaffoldCounter.inc t.radius,lengthCounter⟩
      shiftEnd := t'
      cycle := GalilScaffoldCounter.reset
      finish := cycle
      center := o.center+(o.interior.length+1)
      radius := o.radius+(o.interior.length+1)
      left := t.left
      rightHead := t.right
      resumeLeft := t'.left
      token := o.token
      boundary := o.boundary
      interior := o.interior
      reads := GalilScaffoldChainVerifyRun.reads_append o.reads hreads2
      offset := by rw [hk]; exact hoff2
      unbroken := hb
      phase := hphase'
      canonicalLast := hcanon.1
      canonicalBoundary := hcanon.2.1
      canonicalDistance := hcanon.2.2
      length := hlength
      shiftRun := hchain
      scan := hscan.caught.scan
      available := hc
      mismatch := hne
      represents := o.represents
      present := o.present
      startBefore := le_trans o.startBefore (Nat.le_add_right _ _)
      endPosition := hend'
      size := by have := o.size; omega
      resumed := by
        have := hs.caught.scan
        rw [hposc,hpos] at this
        exact this },
    t',v,cycle,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hposc',hrun,hchain,he ▸ hs,hcr,he ▸ hra⟩

#print axioms ofOnly
#print axioms reshift_origin

end ReadOrigin

theorem shift_run_unique {s t t' : ShiftState} {n : ℕ}
    (h1 : ShiftRun s n t) (h2 : ShiftRun s n t') : t = t' := by
  induction h1 generalizing t' with
  | stop s => cases h2; rfl
  | next s _ _ _ _ _ ih =>
    cases h2 with
    | next _ _ _ _ _ rest' => exact ih rest'

theorem chain_shift_unique {s t t' : ShiftState} {w v v' : GalilScaffoldChainWatch.State}
    {cycle finish finish' : GalilScaffoldCounter.Counter} {n : ℕ}
    (h1 : ChainShiftRun s w cycle n t v finish)
    (h2 : ChainShiftRun s w cycle n t' v' finish') :
    t = t' ∧ v = v' ∧ finish = finish' := by
  induction h1 generalizing t' v' finish' with
  | stop s w cycle => cases h2; exact ⟨rfl,rfl,rfl⟩
  | next s w cycle _ _ _ _ _ ih =>
    cases h2 with
    | next _ _ _ _ _ _ _ rest' => exact ih rest'

theorem matched_run_center {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t) :
    t.center = s.center := by
  induction run with
  | stop s => rfl
  | next s _ _ _ _ ih => exact ih

/-- The resumed comparison entry of an origin: exactly what one further
round of comparisons needs. -/
structure Entry (raw : List (Fin 2)) (o : ReadOrigin raw) (s : OnlyCompareState) : Prop where
  scan : OnlyScan raw (o.center+(o.interior.length+1)) (o.radius+1-(o.interior.length+1))
    (2*(o.interior.length+1)) 0 s.left s.right s.watch s.cycle
  credit : OnlyCredit s.watch s.cycle
  radius : RadiusRep s.radius (o.radius+1-(o.interior.length+1))
  machine : s.watch.machine = o.shifted.machine
  left : s.left = o.resumeLeft
  centerRep : GalilScaffoldInputTrace.Represents s.center.head raw
  centerPresent : s.center.head.focus ≠ none
  centerPos : position s.center = o.center+(o.interior.length+1)

/-- Repeated re-shift rounds of the actual controller with half period `h`:
a full period of matched comparisons, the terminal `cycleEnd` compare with the
predicted right symbol present, then the half-period shift executed by the
heads and counters. The origins are proof artefacts and do not appear. -/
inductive CompareRounds (h : ℕ) : OnlyCompareState → ℕ → OnlyCompareState → Prop
  | stop (s) : CompareRounds h s 0 s
  | next (s : OnlyCompareState) {n m : ℕ} {t s' : OnlyCompareState} {t' : ShiftState}
      {v : GalilScaffoldChainWatch.State} {cycle lengthCounter : GalilScaffoldCounter.Counter}
      (run : OnlyMatchedRun s n t)
      (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
      (hprediction : GalilScaffoldInputHead.read (right t.right) =
        GalilScaffoldChainConsume.symbol t.watch.machine.control.period.focus)
      (hlen : GalilScaffoldCounter.Canonical lengthCounter)
      (hrun : ShiftRun ⟨t.center,GalilScaffoldInputHead.left t.left,
        GalilScaffoldCounter.ofNat h,GalilScaffoldCounter.inc t.radius,lengthCounter⟩ h t')
      (hchain : ChainShiftRun ⟨t.center,GalilScaffoldInputHead.left t.left,
        GalilScaffoldCounter.ofNat h,GalilScaffoldCounter.inc t.radius,lengthCounter⟩
        (GalilScaffoldChainWatch.immediate t.watch) GalilScaffoldCounter.reset h t' v cycle)
      (rest : CompareRounds h ⟨t'.center,t'.left,right t.right,v,cycle,t'.radius⟩ m s') :
      CompareRounds h s (m+1) s'

/-- Every round preserves the read origin: after `m` rounds the centre and the
radius have advanced by `m` half periods and `m` more shifts are accounted for. -/
theorem rounds_origin {raw : List (Fin 2)} {h : ℕ} {s s' : OnlyCompareState} {m : ℕ}
    (rounds : CompareRounds h s m s') :
    ∀ o : ReadOrigin raw, o.interior.length+1 = h → Entry raw o s →
      ∃ o' : ReadOrigin raw, Entry raw o' s' ∧ o'.start = o.start ∧
        o'.interior = o.interior ∧ o'.token = o.token ∧ o'.boundary = o.boundary ∧
        o'.shifts = o.shifts+m ∧ o'.center = o.center+m*h ∧ o'.radius = o.radius+m*h := by
  induction rounds with
  | stop s =>
    intro o _ he
    exact ⟨o,he,rfl,rfl,rfl,rfl,by simp,by simp,by simp⟩
  | next s run hend hc hprediction hlen hrun hchain rest ih =>
    intro o hh he
    subst hh
    rename_i n m t s' t' v cycle lengthCounter
    have hcen := matched_run_center run
    have hrepT : GalilScaffoldInputTrace.Represents t.center.head raw := by
      rw [hcen]; exact he.centerRep
    have hpresT : t.center.head.focus ≠ none := by
      rw [hcen]; exact he.centerPresent
    have hposT : position t.center = o.center+(o.interior.length+1) := by
      rw [hcen]; exact he.centerPos
    obtain ⟨o',t'',v'',cycle'',hstart,hcenter,hradius,hinterior,htoken,hboundary,hshifts,
      hshifted,hresume,_,_,hposc,hrun',hchain',hs,hcr,hra⟩ :=
      o.reshift_origin run he.scan he.credit he.radius he.machine he.left hend hc hprediction
        hrepT hpresT hposT _ hlen
    obtain rfl := shift_run_unique hrun' hrun
    obtain ⟨_,rfl,rfl⟩ := chain_shift_unique hchain' hchain
    obtain ⟨hrep,hpres,_⟩ := shift_run_center hrun raw hrepT hpresT
    have hh' : o'.interior.length+1 = o.interior.length+1 := by rw [hinterior]
    have he' : Entry raw o' ⟨_,_,_,_,_,_⟩ :=
      { scan := by
          have e1 : o'.center+(o'.interior.length+1) = position t''.center := by
            rw [hposc,hcenter,hinterior]; omega
          have e2 : o'.radius+1-(o'.interior.length+1) = o.radius+1 := by
            rw [hradius,hinterior]; omega
          rw [e1,e2,hh']
          exact hs
        credit := hcr
        radius := by
          have e2 : o'.radius+1-(o'.interior.length+1) = o.radius+1 := by
            rw [hradius,hinterior]; omega
          rw [e2]
          exact hra
        machine := by show v''.machine = o'.shifted.machine; rw [hshifted]
        left := hresume.symm
        centerRep := hrep
        centerPresent := hpres
        centerPos := by
          show position t''.center = _
          rw [hposc,hcenter,hinterior]; omega }
    obtain ⟨o'',he'',hstart'',hinterior'',htoken'',hboundary'',hshifts'',hcenter'',hradius''⟩ :=
      ih o' hh' he'
    refine ⟨o'',he'',hstart''.trans hstart,hinterior''.trans hinterior,htoken''.trans htoken,
      hboundary''.trans hboundary,?_,?_,?_⟩
    · rw [hshifts'',hshifts]; omega
    · rw [hcenter'',hcenter]; ring
    · rw [hradius'',hradius]; ring

#print axioms rounds_origin

/-- After any number of re-shift rounds, a final period of matches that ends
at `cycleEnd` with the outer symbols equal but the prediction failing is the
restart branch: the scan grows by one and the chain breaks, with all the
`Search.start` entry conditions on the same state. -/
theorem rounds_restart {raw : List (Fin 2)} {h : ℕ} {s s' t : OnlyCompareState} {m n : ℕ}
    (rounds : CompareRounds h s m s') (o : ReadOrigin raw) (hh : o.interior.length+1 = h)
    (he : Entry raw o s) (run : OnlyMatchedRun s' n t)
    (hcenter : GalilScaffoldInputHead.read s'.center ≠ none)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) =
      GalilScaffoldInputHead.read (right t.right)) :
    let endState := onlyCompareNext t
    let center := o.center+(m+1)*h
    let radius := o.radius+1+m*h-h
    ScanInvariant raw center (radius+n+1) endState.left endState.right ∧
      endState.watch.machine.control.broken = true ∧
      GalilScaffoldCounter.negative endState.watch.margin = false ∧
      GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
      GalilScaffoldCounter.zero endState.watch.lag = true ∧
      GalilScaffoldInputHead.read endState.center ≠ none ∧
      RadiusRep endState.radius (radius+n+1) ∧
      GalilScaffoldCounter.negative endState.radius = false ∧
      (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
        endState.radius).work = endState.watch.machine.control.last ∧
      GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  obtain ⟨o',he',_,hinterior,_,_,_,hcenter',hradius'⟩ := rounds_origin rounds o hh he
  have hh' : o'.interior.length+1 = h := by rw [hinterior]; exact hh
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s'.watch.machine := by
    rw [he'.machine]
    exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s'.left := by rw [he'.left]; exact .stop _
  have hres := o'.matched_restart run [] he'.scan he'.credit he'.radius ht0 hl0 hcenter hend hc hmatch
  have e1 : o'.center+(o'.interior.length+1) = o.center+(m+1)*h := by
    rw [hh',hcenter']; ring
  have e2 : o'.radius+1-(o'.interior.length+1) = o.radius+1+m*h-h := by
    rw [hh',hradius']; omega
  rw [e1,e2] at hres
  exact hres

#print axioms rounds_restart

/-- The resumed entry of a fresh shift, as `scan_prediction_shift` produces it,
is an `Entry` of the corresponding read origin with no earlier shift. -/
theorem entry_of_only {raw : List (Fin 2)} (o : OnlyOrigin raw)
    (hsteps : o.steps = o.interior.length+1)
    (hd : 4*(o.interior.length+1) ≤
      GalilScaffoldCounter.value o.watched.machine.control.distance)
    (hphase : o.watched.machine.control.phase = 4)
    {endpoint : ShiftState} {l : PlaceHead} {radiusCounter lengthCounter : GalilScaffoldCounter.Counter}
    (hrun : ShiftRun ⟨o.start.machine.verifier,l,GalilScaffoldCounter.ofNat (o.interior.length+1),
      radiusCounter,lengthCounter⟩ (o.interior.length+1) endpoint)
    {r : PlaceHead} {cycle : GalilScaffoldCounter.Counter}
    (hscan : OnlyScan raw (position endpoint.center) (o.radius+1-(o.interior.length+1))
      (2*(o.interior.length+1)) 0 endpoint.left r o.shifted cycle)
    (hcredit : OnlyCredit o.shifted cycle)
    (hrad : RadiusRep endpoint.radius (o.radius+1-(o.interior.length+1)))
    (hleft : o.resumeLeft = endpoint.left) :
    ∃ o' : ReadOrigin raw,
      Entry raw o' ⟨endpoint.center,endpoint.left,r,o.shifted,cycle,endpoint.radius⟩ ∧
      o'.start = o.start ∧ o'.shifts = 0 ∧ o'.interior = o.interior ∧
      o'.center = o.center ∧ o'.radius = o.radius := by
  obtain ⟨o',hstart,_,hshifted,hshifts,hcenter,hradius,hinterior,_,_,hresume,_,_⟩ :=
    ReadOrigin.ofOnly o hsteps hd hphase
  obtain ⟨hrep,hpres,hpos⟩ := shift_run_center hrun raw o.represents o.present
  have hposc : position endpoint.center = o'.center+(o'.interior.length+1) := by
    show position endpoint.center = _
    rw [hpos,hcenter,hinterior]
    exact congrArg (· + (o.interior.length+1)) o.startPosition
  refine ⟨o',?_,hstart,hshifts,hinterior,hcenter,hradius⟩
  exact
    { scan := by
        rw [← hposc,hradius,hinterior]
        exact hscan
      credit := hcredit
      radius := by rw [hradius,hinterior]; exact hrad
      machine := by show o.shifted.machine = _; rw [hshifted]
      left := by show endpoint.left = _; rw [hresume,hleft]
      centerRep := hrep
      centerPresent := hpres
      centerPos := hposc }

#print axioms entry_of_only

/-- End to end on the actual states: the fresh mismatch shift of
`scan_prediction_shift`, then any number of full-period re-shift rounds, then a
terminal period ending at `cycleEnd` with equal outer symbols and a failing
prediction. The restart entry conditions hold at that terminal state, with the
centre and the scan radius advanced by the accumulated half periods. -/
theorem fresh_rounds_restart {s t : GalilScaffoldChainWatch.State} {bs : List Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t)
    (a : Fin 2) (ls suffix : List (Fin 2)) (gap : Bool)
    (w : List (Fin 3)) (span lower radius : ℕ) (c b : Fin 3) (xs : List (Fin 3))
    (hw : w = (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take span)
    (hc : GalilDpCorrect.Candidate w lower (xs.length+1))
    (hh : GalilScaffoldInputTrace.Represents s.machine.verifier.head ((a :: ls).reverse ++ suffix))
    (hp : s.machine.verifier.head.focus ≠ none)
    (hs : s.machine.control = GalilScaffoldChainConsume.ready c xs b)
    (hstart : position s.machine.verifier =
      if gap then 2*(ls.length+1) else 2*(ls.length+1)-1)
    (l outer : PlaceHead)
    (hi : ScanInvariant ((a :: ls).reverse ++ suffix) (position s.machine.verifier) radius l outer)
    (hphase : t.machine.control.phase = 4)
    (initialRadius : ℕ) (hlag : GalilScaffoldCounter.value s.lag = initialRadius)
    (hzero : GalilScaffoldCounter.zero t.lag = true)
    (hcount : initialRadius+bs.count true = radius)
    (hcan : canRight outer) (predicted : Fin 3)
    (hpred : GalilScaffoldChainConsume.symbol t.machine.control.period.focus = some predicted)
    (hread : GalilScaffoldInputHead.read (right outer) = some predicted)
    (radiusCounter lengthCounter : GalilScaffoldCounter.Counter)
    (hcounter : GalilScaffoldCounter.value radiusCounter = (radius : ℤ)+1)
    (hrcanon : GalilScaffoldCounter.Canonical radiusCounter)
    (hlcanon : GalilScaffoldCounter.Canonical lengthCounter)
    (prepRadius : GalilScaffoldCounter.Counter)
    (hprepCanonical : GalilScaffoldCounter.Canonical prepRadius)
    (startMatch doneMatch : Bool) (copyMatches backMatches : List Bool)
    (hcopyLength : copyMatches.length = xs.length+1)
    (hprepLag : s.lag = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start prepRadius)
      (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)).lag)
    (hprepMargin : s.margin = (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start prepRadius)
      (GalilScaffoldChainCredits.prepEvents startMatch doneMatch copyMatches backMatches)).margin)
    (hmismatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left l) ≠
      GalilScaffoldInputHead.read (right outer)) :
    ∃ endpoint watchEnd cycleEnd,
      ShiftRun ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩ (xs.length+1) endpoint ∧
      ChainShiftRun ⟨s.machine.verifier,GalilScaffoldInputHead.left l,
        GalilScaffoldCounter.ofNat (xs.length+1),radiusCounter,lengthCounter⟩
        (GalilScaffoldChainWatch.immediate t) GalilScaffoldCounter.reset (xs.length+1)
        endpoint watchEnd cycleEnd ∧
      ∀ (m n : ℕ) (s' final : OnlyCompareState),
        CompareRounds (xs.length+1)
          ⟨endpoint.center,endpoint.left,right outer,watchEnd,cycleEnd,endpoint.radius⟩ m s' →
        OnlyMatchedRun s' n final →
        GalilScaffoldInputHead.read s'.center ≠ none →
        GalilScaffoldCounter.singlePositive final.cycle = true → canRight final.right →
        GalilScaffoldInputHead.read (GalilScaffoldInputHead.left final.left) =
          GalilScaffoldInputHead.read (right final.right) →
        let endState := onlyCompareNext final
        let center := position s.machine.verifier+(m+1)*(xs.length+1)
        let radius' := radius+1+m*(xs.length+1)-(xs.length+1)
        ScanInvariant ((a :: ls).reverse ++ suffix) center (radius'+n+1)
            endState.left endState.right ∧
          endState.watch.machine.control.broken = true ∧
          GalilScaffoldCounter.negative endState.watch.margin = false ∧
          GalilScaffoldCounter.positive endState.watch.machine.control.last = true ∧
          GalilScaffoldCounter.zero endState.watch.lag = true ∧
          GalilScaffoldInputHead.read endState.center ≠ none ∧
          RadiusRep endState.radius (radius'+n+1) ∧
          GalilScaffoldCounter.negative endState.radius = false ∧
          (GalilScaffoldSearchFinish.begin endState.watch.machine.control.last
            endState.radius).work = endState.watch.machine.control.last ∧
          GalilScaffoldCounter.Canonical endState.watch.machine.control.last := by
  obtain ⟨_,endpoint,watchEnd,cycleEnd,hshift,hchain,_,_,_,hscan,hcredit,hrad,_,_,_,origin,
      hostart,howatched,hoshifted,_,horesume,hointerior,hosteps,_,hocenter,horadius,hd,_⟩ :=
    scan_prediction_shift hr a ls suffix gap w span lower radius c b xs hw hc hh hp hs hstart
      l outer hi hphase initialRadius hlag hzero hcount hcan predicted hpred hread
      radiusCounter lengthCounter hcounter hrcanon hlcanon prepRadius hprepCanonical
      startMatch doneMatch copyMatches backMatches hcopyLength hprepLag hprepMargin hmismatch
  refine ⟨endpoint,watchEnd,cycleEnd,hshift,hchain,?_⟩
  intro m n s' final rounds run hcenter hend hc' hmatch
  have hsteps' : origin.steps = origin.interior.length+1 := by rw [hosteps,hointerior]
  have hd' : 4*(origin.interior.length+1) ≤
      GalilScaffoldCounter.value origin.watched.machine.control.distance := by
    rw [hointerior,howatched]; exact hd
  have hrun' : ShiftRun ⟨origin.start.machine.verifier,GalilScaffoldInputHead.left l,
      GalilScaffoldCounter.ofNat (origin.interior.length+1),radiusCounter,lengthCounter⟩
      (origin.interior.length+1) endpoint := by
    rw [hostart,hointerior]; exact hshift
  have hscan' : OnlyScan ((a :: ls).reverse ++ suffix) (position endpoint.center)
      (origin.radius+1-(origin.interior.length+1)) (2*(origin.interior.length+1)) 0
      endpoint.left (right outer) origin.shifted cycleEnd := by
    rw [hoshifted,hointerior,horadius]; exact hscan
  have hcredit' : OnlyCredit origin.shifted cycleEnd := by rw [hoshifted]; exact hcredit
  have hrad' : RadiusRep endpoint.radius (origin.radius+1-(origin.interior.length+1)) := by
    rw [hointerior,horadius]; exact hrad
  have hphase' : origin.watched.machine.control.phase = 4 := by
    rw [howatched]
    exact phase_four_consume _ _ hphase
  obtain ⟨o,he,_,_,hinterior,hcenter',hradius'⟩ :=
    entry_of_only origin hsteps' hd' hphase' hrun' hscan' hcredit' hrad' horesume
  rw [hoshifted] at he
  have hh : o.interior.length+1 = xs.length+1 := by rw [hinterior,hointerior]
  have hres := rounds_restart rounds o hh he run hcenter hend hc' hmatch
  rw [hcenter',hocenter,hradius',horadius] at hres
  exact hres

#print axioms fresh_rounds_restart

/-- Read-based `dispatch_only_match`. -/
theorem ReadOrigin.dispatch_match {raw : List (Fin 2)} (o : ReadOrigin raw)
    {center radius n slots : ℕ} (s : RestartState n slots) (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.scan.left s.scan.right s.scan.watch s.scan.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.scan.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.scan.left)
    (hm : s.chainMode = .watch) (ho : s.periodOnly = true) (hc : canRight s.scan.right)
    (he : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
      GalilScaffoldInputHead.read (right s.scan.right)) :
    dispatchOnlyMatch s = some (matchedRestartState s) := by
  have hp := (only_scan_dispatch hi).1
  have hcheck := o.check_pair extra hi ht hl
  have hz := hi.caught.lagZero
  unfold dispatchOnlyMatch
  exact if_pos ⟨hm,ho,hz,hc,hp,hcheck,he⟩

/-- Read-based `terminal_dispatch_next_tick`: no phase hypothesis and no fixed
step count, so it applies after any number of earlier shifts. -/
theorem read_terminal_dispatch_next_tick {raw : List (Fin 2)} (o : ReadOrigin raw)
    {center radius n slots : ℕ} (s : RestartState n slots) (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.scan.left s.scan.right s.scan.watch s.scan.cycle)
    (hcredit : OnlyCredit s.scan.watch s.scan.cycle) (hrad : RadiusRep s.scan.radius radius)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.scan.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.scan.left)
    (hcenter : GalilScaffoldInputHead.read s.scan.center ≠ none)
    (hm : s.chainMode = .watch) (ho : s.periodOnly = true)
    (hend : GalilScaffoldCounter.singlePositive s.scan.cycle = true)
    (hc : canRight s.scan.right)
    (he : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
      GalilScaffoldInputHead.read (right s.scan.right)) (entry delay : ℕ)
    (hdelay : 1 < delay) (replaying trailing : Bool) (input : Option (Fin 2)) :
    ∃ t, (dispatchOnlyMatch s).bind (restartInputTick entry delay replaying trailing input) = some t ∧
      ScanInvariant (raw ++ input.toList) center (radius+1) t.scan.left t.scan.right ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧
      t.clock = (if scanAvailable replaying trailing
        (receiveRestart (matchedRestartState s) input).scan.right then delay-1 else delay) ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.scheduler.mode = .grow := by
  have hready : OnlyRestartReady raw center (radius+1) (onlyCompareNext s.scan) :=
    o.matched_restart (.stop s.scan) extra hi hcredit hrad ht hl hcenter hend hc he
  have hdispatch := o.dispatch_match s extra hi ht hl hm ho hc he
  have hbroken : (matchedRestartState s).chainMode = .broken := by
    simp only [matchedRestartState,hready.2.1,ite_true]
  obtain ⟨t,hrestart,hscan,hmode,hcount,hclock,hprogram,hgrow⟩ :=
    restart_input_tick (matchedRestartState s) hready hbroken entry delay hdelay
      replaying trailing input
  refine ⟨t,?_,hscan,hmode,hcount,hclock,hprogram,hgrow⟩
  simpa only [hdispatch,Option.bind_some] using hrestart

/-- After `m` re-shift rounds from an origin entry, the terminal `cycleEnd`
compare with equal outer symbols dispatches into the restart and the next
tick, with the centre and radius advanced by the accumulated half periods. -/
theorem rounds_dispatch_next_tick {raw : List (Fin 2)} {h : ℕ} {s0 : OnlyCompareState}
    {m n slots : ℕ} (s : RestartState n slots) (rounds : CompareRounds h s0 m s.scan)
    (o : ReadOrigin raw) (hh : o.interior.length+1 = h) (he : Entry raw o s0)
    (hcenter : GalilScaffoldInputHead.read s.scan.center ≠ none)
    (hm : s.chainMode = .watch) (ho : s.periodOnly = true)
    (hend : GalilScaffoldCounter.singlePositive s.scan.cycle = true)
    (hc : canRight s.scan.right)
    (hmatch : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left s.scan.left) =
      GalilScaffoldInputHead.read (right s.scan.right)) (entry delay : ℕ)
    (hdelay : 1 < delay) (replaying trailing : Bool) (input : Option (Fin 2)) :
    let center := o.center+(m+1)*h
    let radius := o.radius+1+m*h-h
    ∃ t, (dispatchOnlyMatch s).bind (restartInputTick entry delay replaying trailing input) = some t ∧
      ScanInvariant (raw ++ input.toList) center (radius+1) t.scan.left t.scan.right ∧
      t.chainMode = .idle ∧ t.restarts = s.restarts+1 ∧
      t.clock = (if scanAvailable replaying trailing
        (receiveRestart (matchedRestartState s) input).scan.right then delay-1 else delay) ∧
      GalilScaffoldRawTick.Represents t.search.program
        ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
      t.search.scheduler.mode = .grow := by
  obtain ⟨o',he',_,hinterior,_,_,_,hcenter',hradius'⟩ := rounds_origin rounds o hh he
  have hh' : o'.interior.length+1 = h := by rw [hinterior]; exact hh
  have ht0 : GalilScaffoldChainWatchTrace.Trace o'.shifted.machine [] s.scan.watch.machine := by
    rw [he'.machine]
    exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o'.resumeLeft 0 s.scan.left := by rw [he'.left]; exact .stop _
  have hres := read_terminal_dispatch_next_tick o' s [] he'.scan he'.credit he'.radius ht0 hl0
    hcenter hm ho hend hc hmatch entry delay hdelay replaying trailing input
  have e1 : o'.center+(o'.interior.length+1) = o.center+(m+1)*h := by
    rw [hh',hcenter']; ring
  have e2 : o'.radius+1-(o'.interior.length+1) = o.radius+1+m*h-h := by
    rw [hh',hradius']; omega
  rw [e1,e2] at hres
  exact hres

#print axioms read_terminal_dispatch_next_tick
#print axioms rounds_dispatch_next_tick

/-- At the end of a matched period, with the predicted right symbol present,
the decoded conditions of Scala's shift branch hold: `Chain.canShift` in the
two-semiperiod continuation (`lag = 0`, `phase = 4`, `cycleEnd`), the outer
symbols differ (so `matchedPlace` is not taken), and the prediction agrees
with the right read. Chain mode and `periodOnly` are controller fields. -/
theorem ReadOrigin.shift_guard {raw : List (Fin 2)} (o : ReadOrigin raw)
    {s t : OnlyCompareState} {n : ℕ} (run : OnlyMatchedRun s n t) (he : Entry raw o s)
    (hend : GalilScaffoldCounter.singlePositive t.cycle = true) (hc : canRight t.right)
    (hprediction : GalilScaffoldInputHead.read (right t.right) =
      GalilScaffoldChainConsume.symbol t.watch.machine.control.period.focus) :
    GalilScaffoldCounter.zero t.watch.lag = true ∧
      t.watch.machine.control.phase = 4 ∧
      GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left) ≠
        GalilScaffoldInputHead.read (right t.right) := by
  have ht0 : GalilScaffoldChainWatchTrace.Trace o.shifted.machine [] s.watch.machine := by
    rw [he.machine]
    exact GalilScaffoldChainWatchTrace.empty _
  have hl0 : LeftMoves o.resumeLeft 0 s.left := by rw [he.left]; exact .stop _
  have checked := o.matched_checked run [] he.scan he.credit he.radius ht0 hl0
  obtain ⟨_,actual,_,htrace,hleft,hscan,_,_⟩ :=
    only_compare_history checked [] he.scan he.credit he.radius ht0 hl0
  have hne := (o.reshift_compare actual hscan htrace hleft hend hc hprediction).1
  refine ⟨hscan.caught.lagZero,?_,hne⟩
  rw [htrace.control]
  exact phase_four_run _ _ o.shifted_phase

#print axioms ReadOrigin.shift_guard

end PalPeg.GalilScaffoldChainInputSupply
