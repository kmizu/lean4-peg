import PalPeg.GalilTruncTick
import PalPeg.GalilFinalBaseNeed
import PalPeg.GalilFrontMono
import PalPeg.GalilCheckpoints
import PalPeg.GalilTraceCost

/-!
# The pointwise `needL` bound: the head arithmetic, and an obstruction

Target (`GalilFinalBaseNeed.H_needLB`):
`∀ m < |w|, ∀ i ≤ Tc (m+1), needL w st i ≤ m+1`.

* §1 `two_usedPH_of_rep` — under `Represents`, consumption is read off the place:
  `2·usedPH = position + [letter] + 2·|right stack|`.  Consequences
  `usedPH_le_of_position` / `usedPH_right_le_of_position`: a head with an empty
  right stack at a place `≤ 2(m+1)-1` has consumed `≤ m+1` letters, and so has
  its one-move lookahead (the `R`-part of `look`).
* §2 **Obstruction.** `lookChain` charges the chain verifier *two* moves.  A
  verifier standing on a letter place with an empty right stack and a
  non-empty FIFO pays one extra letter (`lookChain_eq_succ`).  At a checkpoint
  `m+1 < |w|` (right head on the letter place `2(m+1)-1`, empty right stack)
  whose chain verifier *is* the right head (a caught-up watch, `lag = 0`, the
  steady state of `GalilScaffoldChainWatch`), `needL = m+2`
  (`needL_checkpoint_gt`), so `H_needLB` fails on any such pre-loaded trace
  (`not_needLB_of_caughtUp`).  The actual tick consumes at most one verifier
  move there (`Internal.idle` at `lag = 0`), so the over-approximation is in
  `GalilTruncTick.lookChain`, not in the machine.
-/

set_option autoImplicit false

namespace PalPeg.GalilNeedBound

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTruncTick

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. Consumption from the place -/

/-- **Consumption is read off the place.** -/
theorem two_usedPH_of_rep (raw : List (Fin 2)) (p : PH)
    (hr : GalilScaffoldInputTrace.Represents p.head raw) (hs : GalilFrontMono.Sane p) :
    2 * usedPH raw.length p =
      position p + (if p.gap then 0 else 1) + 2 * p.head.right.length := by
  have hu := usedPH_eq_arrived raw p hr
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp only [GalilFrontMono.Sane] at hs
  simp only [arrived] at hu
  cases g
  · simp only [Bool.false_eq_true, false_or] at hs
    simp only [position, Bool.false_eq_true, if_false]
    omega
  · simp only [position, if_true]
    omega

/-- A head with an empty right stack at a place `≤ 2(m+1)-1` has consumed at most
`m+1` letters. -/
theorem usedPH_le_of_position (raw : List (Fin 2)) (p : PH) (m : ℕ)
    (hr : GalilScaffoldInputTrace.Represents p.head raw) (hs : GalilFrontMono.Sane p)
    (hrl : p.head.right = []) (hpos : position p ≤ 2 * (m+1) - 1) :
    usedPH raw.length p ≤ m+1 := by
  have h := two_usedPH_of_rep raw p hr hs
  rw [hrl, List.length_nil] at h
  split_ifs at h <;> omega

/-- The one-move lookahead of such a head also stays within `m+1` letters
(the `R`-part of `look`). -/
theorem usedPH_right_le_of_position (raw : List (Fin 2)) (p : PH) (m : ℕ)
    (hr : GalilScaffoldInputTrace.Represents p.head raw) (hs : GalilFrontMono.Sane p)
    (hrl : p.head.right = []) (hpos : position p ≤ 2 * (m+1) - 1) :
    usedPH raw.length (GalilScaffoldChainVerifier.right p) ≤ m+1 := by
  have h := two_usedPH_of_rep raw p hr hs
  rw [hrl, List.length_nil] at h
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp only at hrl
  subst hrl
  cases g
  · rw [usedPH_right_letter raw.length _ rfl]
    simp only [position, Bool.false_eq_true, if_false] at h hpos ⊢
    omega
  · simp only [position, if_true] at h hpos
    cases q with
    | nil =>
      simp only [usedPH, GalilScaffoldChainVerifier.right, if_true,
        GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight] at h ⊢
      omega
    | cons a q =>
      simp only [usedPH, GalilScaffoldChainVerifier.right, if_true,
        GalilScaffoldChainVerifier.headRight, GalilScaffoldInputTrace.moveRight,
        List.length_cons] at h ⊢
      omega

/-! ## 2. The two-move chain lookahead overshoots at a caught-up checkpoint -/

/-- Two right moves from a letter place with an empty right stack and a non-empty
FIFO pop exactly one letter. -/
theorem usedPH_right_right_eq (n : ℕ) (p : PH) (hg : p.gap = false) (hrl : p.head.right = [])
    (hq : p.head.incoming ≠ []) (hle : p.head.incoming.length ≤ n) :
    usedPH n (GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right p)) =
      usedPH n p + 1 := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  simp only at hg hrl hq hle
  subst hg; subst hrl
  cases q with
  | nil => exact absurd rfl hq
  | cons a q =>
    simp only [usedPH, GalilScaffoldChainVerifier.right, Bool.false_eq_true, if_false,
      Bool.not_false, if_true, GalilScaffoldChainVerifier.headRight,
      GalilScaffoldInputTrace.moveRight, List.length_cons] at hle ⊢
    omega

theorem lookChain_eq_succ (n : ℕ) (x : ChainVM) (p : PH) (hv : verOf x = some p)
    (hg : p.gap = false) (hrl : p.head.right = []) (hq : p.head.incoming ≠ [])
    (hle : p.head.incoming.length ≤ n) : lookChain n x = usedPH n p + 1 := by
  simp only [lookChain, hv]
  exact usedPH_right_right_eq n p hg hrl hq hle

/-- **The checkpoint overshoot.** In scan mode, with the right head on the letter
place `2(m+1)-1` with an empty right stack, `m+1 < |w|`, and the chain verifier
equal to the right head, `look = m+2`. -/
theorem look_checkpoint_eq (w : List (Fin 2)) (x : State GalilVM) (m : ℕ)
    (hscan : x.ctl.mode = .scan)
    (hr : GalilScaffoldInputTrace.Represents x.vm.right.head w)
    (hg : x.vm.right.gap = false) (hrl : x.vm.right.head.right = [])
    (hpos : position x.vm.right = 2 * (m+1) - 1) (hm : m + 1 < w.length)
    (hver : verOf x.vm.chain = some x.vm.right) :
    look w x = m + 2 := by
  have hs : GalilFrontMono.Sane x.vm.right := by
    right
    simp only [position, hg, Bool.false_eq_true, if_false] at hpos
    omega
  have h2 := two_usedPH_of_rep w x.vm.right hr hs
  rw [hrl, List.length_nil, hg] at h2
  simp only [Bool.false_eq_true, if_false] at h2
  have hu : usedPH w.length x.vm.right = m + 1 := by omega
  have hq : x.vm.right.head.incoming ≠ [] := by
    intro he
    simp only [usedPH, he, List.length_nil, Nat.sub_zero] at hu
    omega
  have hle : x.vm.right.head.incoming.length ≤ w.length := by
    obtain ⟨xs, rs, q, hh, hw⟩ := hr
    have : x.vm.right.head.incoming = q := by rw [hh]; cases xs <;> rfl
    rw [this, hw]; simp; omega
  have hc := lookChain_eq_succ w.length x.vm.chain x.vm.right hver hg hrl hq hle
  have hR := usedPH_right_letter w.length x.vm.right hg
  unfold look
  rw [if_pos hscan, hc, hR, hu]
  omega

theorem needL_checkpoint_gt (w : List (Fin 2)) (st : ℕ → State GalilVM) (i m : ℕ)
    (hscan : (st i).ctl.mode = .scan)
    (hr : GalilScaffoldInputTrace.Represents (st i).vm.right.head w)
    (hg : (st i).vm.right.gap = false) (hrl : (st i).vm.right.head.right = [])
    (hpos : position (st i).vm.right = 2 * (m+1) - 1) (hm : m + 1 < w.length)
    (hver : verOf (st i).vm.chain = some (st i).vm.right) :
    m + 1 < needL w st i := by
  have := look_checkpoint_eq w (st i) m hscan hr hg hrl hpos hm hver
  unfold needL
  omega

/-- **`H_needLB` is refuted by one caught-up checkpoint.**  If some pre-loaded trace
of a nonempty `w` has, at a checkpoint `m+1 < |w|`, the chain verifier equal to
the right head (letter place, empty right stack, scan mode), the pointwise target
of `GalilTruncTick.needLe_of_pointwise` is false. -/
theorem not_needLB_of_caughtUp (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (hw : 0 < w.length) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hB : GalilFinalBaseNeed.PreTraceB centre place entry q first w st Tc) (m : ℕ)
    (hm : m + 1 < w.length)
    (hscan : (st (Tc (m+1))).ctl.mode = .scan)
    (hr : GalilScaffoldInputTrace.Represents (st (Tc (m+1))).vm.right.head w)
    (hrl : (st (Tc (m+1))).vm.right.head.right = [])
    (hver : verOf (st (Tc (m+1))).vm.chain = some (st (Tc (m+1))).vm.right) :
    ¬ GalilFinalBaseNeed.H_needLB centre place entry q first := by
  intro hN
  have hrep := hB.pre.report (m+1) (by omega) (by omega)
  have hpos := hrep.atPrefix
  have hg : (st (Tc (m+1))).vm.right.gap = false := by
    cases hgg : (st (Tc (m+1))).vm.right.gap
    · rfl
    · simp only [position, hgg, if_true] at hpos; omega
  have h1 := hN w hw st Tc hB m (by omega) (Tc (m+1)) le_rfl
  have h2 := needL_checkpoint_gt w st (Tc (m+1)) m hscan hr hg hrl hpos hm hver
  omega

#print axioms two_usedPH_of_rep
#print axioms usedPH_le_of_position
#print axioms usedPH_right_le_of_position
#print axioms usedPH_right_right_eq
#print axioms lookChain_eq_succ
#print axioms look_checkpoint_eq
#print axioms needL_checkpoint_gt
#print axioms not_needLB_of_caughtUp

end PalPeg.GalilNeedBound
