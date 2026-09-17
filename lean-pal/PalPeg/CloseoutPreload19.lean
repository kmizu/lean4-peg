import PalPeg.CloseoutPreload18

/-!
# The clock phase, and the liveness the `.wait` leg needs

`CloseoutPreload18` §4 leaves two gaps.  This file settles the first and
delimits the second.

* §1 (gap (a), the clock phase).  `CloseoutPreload18.PrefixPhase bs` is a
  *lower* bound on the comparison count of `bs`, so it cannot come from
  `CloseoutReadyStage.PacedL` (which is an upper bound only — see §3).  Its real
  source is the controller clock `GalilScaffoldMatchClock.run`, whose
  conservation law `run_invariant` says `ticks + clock' = clock + 2048 * fires`.
  With `1 ≤ clock' ` and `clock ≤ 2048` this is exactly `PrefixPhase`
  (`prefixPhase_of_clock`).  The hypothesis it needs is that every tick of the
  prefix is an *available* scan tick: an unavailable tick does not decrement the
  clock, so the phase of a stalled prefix grows without bound.
* §2 (gap (b), the `.wait` leg).  Under an explicit liveness clause `LiveL`
  ("every window of `d` consecutive ticks holds a comparison") a list is short:
  `liveL_length_le`.  Combined with `CloseoutPreload18.wait_leg_count` this is
  the upper bound `CloseoutPreload18` §4 asks for:
  `wait_leg_length_le : len ≤ 2048 * (debt + 1)`.
* §3 records, with a witness, that `PacedL` carries no such lower bound, so
  `LiveL` is genuinely new information and must be supplied by the machine.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload19

open PalPeg
open PalPeg.GalilScaffoldChainInputSupply (SearchVM)
open PalPeg.GalilScaffoldSearchFinish (Mode)
open PalPeg.GalilScaffoldCounter (Canonical value zero zero_iff)
open PalPeg.CloseoutReadyStage (PacedL)
open PalPeg.CloseoutPreload14 (WaitTrace)
open PalPeg.CloseoutPreload18 (PrefixPhase wait_leg_count)

/-! ## 1. `PrefixPhase` comes from the controller clock -/

/-- **NAMED — the phase inequality, arithmetically.**  A clock that starts in
phase `clock ≤ 2048`, ends at `1 ≤ clock'`, and fires `F` times over `L` ticks
satisfies the conservation law `L + clock' = clock + 2048 * F`; hence
`L ≤ 2048 * F + 2047`. -/
theorem phase_bound {L F clock clock' : ℕ}
    (hclock : clock ≤ 2048) (hclock' : 1 ≤ clock')
    (hcons : L + clock' = clock + F * 2048) :
    L ≤ 2048 * F + 2047 := by
  omega

/-- An all-available tick list counts every position. -/
theorem count_true_of_all {ts : List Bool} (h : ∀ b ∈ ts, b = true) :
    ts.count true = ts.length := by
  induction ts with
  | nil => simp
  | cons a ts ih =>
    have ha : a = true := h a (by simp)
    subst ha
    have ih' := ih (fun b hb => h b (by simp [hb]))
    simp [ih']

/-- **NAMED — gap (a) of `CloseoutPreload18` §4, closed.**  The preparation
prefix of a stage is phase-bounded, provided every one of its ticks is an
available scan tick: `bs` is the list of *comparisons* (one `true` per firing of
the match clock), `ts` the list of ticks that drove them.  This is the machine
fact `CloseoutPreload18` §4 called for — a statement about
`GalilScaffoldMatchClock`, not about `PacedL`. -/
theorem prefixPhase_of_clock {bs ts : List Bool} {clock : ℕ}
    (hc1 : 1 ≤ clock) (hc2 : clock ≤ 2048)
    (hall : ∀ b ∈ ts, b = true)
    (hlen : bs.length = ts.length)
    (hcnt : bs.count true = (PalPeg.GalilScaffoldMatchClock.run 2048 clock ts).2) :
    PrefixPhase bs := by
  obtain ⟨h1, h2, h3⟩ :=
    PalPeg.GalilScaffoldMatchClock.run_invariant 2048 clock ts (by norm_num) ⟨hc1, hc2⟩
  rw [count_true_of_all hall] at h3
  unfold PrefixPhase
  rw [hlen, hcnt]
  omega

#print axioms phase_bound
#print axioms count_true_of_all
#print axioms prefixPhase_of_clock

/-- The special case the stage entry uses: a fresh clock (`clock = 2048`). -/
theorem prefixPhase_of_fresh_clock {bs ts : List Bool}
    (hall : ∀ b ∈ ts, b = true) (hlen : bs.length = ts.length)
    (hcnt : bs.count true = (PalPeg.GalilScaffoldMatchClock.run 2048 2048 ts).2) :
    PrefixPhase bs :=
  prefixPhase_of_clock (by norm_num) (by norm_num) hall hlen hcnt

#print axioms prefixPhase_of_fresh_clock

/-! ## 2. Liveness, and the upper bound on the `.wait` leg -/

/-- **NAMED — the liveness clause.**  `LiveL d as` says no window of `d`
consecutive ticks of `as` is comparison-free: as long as input keeps arriving,
a comparison fires at least once per quantum.  This is the dual of `PacedL`
(which forbids *more* than one comparison per `d` ticks). -/
def LiveL (d : ℕ) (as : List Bool) : Prop :=
  ∀ n : ℕ, n + d ≤ as.length → 0 < ((as.drop n).take d).count true

theorem liveL_drop {d : ℕ} {as : List Bool} (h : LiveL d as) : LiveL d (as.drop d) := by
  intro n hn
  have hlen : (as.drop d).length = as.length - d := by simp
  have h2 := h (d + n) (by omega)
  have hdd : (as.drop d).drop n = as.drop (d + n) := by
    rw [List.drop_drop, Nat.add_comm]
  rw [hdd]
  exact h2

/-- **NAMED — a live list is short.**  Under `LiveL d`, the length of a list is
at most `d * (comparisons + 1)`. -/
theorem liveL_length_le {d : ℕ} (hd : 0 < d) :
    ∀ (n : ℕ) (as : List Bool), as.length = n → LiveL d as →
      as.length ≤ d * (as.count true + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro as hn hl
    by_cases hle : as.length ≤ d
    · have hm : d * 1 ≤ d * (as.count true + 1) :=
        Nat.mul_le_mul_left d (by omega)
      simp only [Nat.mul_one] at hm
      omega
    · push_neg at hle
      have h1 : 0 < ((as.drop 0).take d).count true := hl 0 (by omega)
      rw [List.drop_zero] at h1
      have hdlen : (as.drop d).length = as.length - d := by simp
      have h2 := ih (as.drop d).length (by omega) (as.drop d) rfl (liveL_drop hl)
      have hcount : as.count true = (as.take d).count true + (as.drop d).count true := by
        conv_lhs => rw [← List.take_append_drop d as]
        rw [List.count_append]
      have hmul : d * ((as.drop d).count true + 2)
          = d * ((as.drop d).count true + 1) + d := by ring
      have hstep : d * ((as.drop d).count true + 2) ≤ d * (as.count true + 1) :=
        Nat.mul_le_mul_left d (by omega)
      omega

#print axioms liveL_drop
#print axioms liveL_length_le

/-- **NAMED — gap (b) of `CloseoutPreload18` §4, closed *under liveness*.**  A
`.wait` leg that fires holds exactly `debt` comparisons
(`CloseoutPreload18.wait_leg_count`); if the leg is live, it therefore lasts at
most `2048 * (debt + 1)` ticks.  This is the upper bound conjectured — in the
wrong form — in `CloseoutPreload17` §3 (2), now with the liveness clause that
`CloseoutPreload18` §4 identified as its missing input made explicit. -/
theorem wait_leg_length_le {as : List Bool} {v t : SearchVM} {debt : ℕ}
    (hr : WaitTrace as v t) (hmt : t.search.mode = Mode.wait)
    (hz : zero t.search.debt = true) (hc : Canonical t.search.debt)
    (hlive : LiveL 2048 as) (hd : value v.search.debt = (debt : ℤ)) :
    as.length ≤ 2048 * (debt + 1) := by
  have h1 := wait_leg_count hr hmt hz hc
  have h3 : ((as.count true : ℕ) : ℤ) = (debt : ℤ) := by rw [h1, hd]
  have h4 : as.count true = debt := by exact_mod_cast h3
  have h5 := liveL_length_le (d := 2048) (by norm_num) as.length as rfl hlive
  omega

#print axioms wait_leg_length_le

/-! ## 3. `PacedL` carries no lower bound -/

/-- **NAMED — `PacedL` is an upper bound only.**  For every `n` there is a
comparison-free stream of length `n` that is perfectly paced; so neither
`PacedL` nor anything derived from it alone can bound a leg's length from above,
and `CloseoutPreload.RdPaced` — whose payload is a `PacedL` — inherits the same
silence.  `LiveL` (or the machine fact behind it) is strictly new information. -/
theorem pacedL_no_lower_bound (n : ℕ) :
    ∃ as : List Bool, PacedL 2048 0 as ∧ as.length = n ∧ as.count true = 0 := by
  refine ⟨List.replicate n false, PalPeg.CloseoutReadyStage.pacedL_replicate_false 2048 0 n,
    by simp, ?_⟩
  simp [List.count_replicate]

#print axioms pacedL_no_lower_bound

/-!
## 4. What is left

* Gap (a) is closed at the list level: `prefixPhase_of_clock` derives
  `PrefixPhase` from `GalilScaffoldMatchClock.run_invariant`.  What remains is
  purely a bookkeeping identification — that the `bs` of
  `CloseoutPreload18.pacedL_suffix_2047` really is the firing list of the
  controller clock over the stage's preparation ticks, all of which are
  available.
* Gap (b) is closed *modulo liveness*: `wait_leg_length_le` is the wanted
  `len ≤ 2048 * (debt + 1)`, from `LiveL 2048 as`.  §3 shows `LiveL` cannot be
  recovered from `PacedL`/`RdPaced`, so the machine must supply it: the scan
  tick supply must be shown never to stall for a full quantum inside a `.wait`
  leg.

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.CloseoutPreload19
