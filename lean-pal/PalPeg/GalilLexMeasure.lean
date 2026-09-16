import PalPeg.GalilCheckpoints
import PalPeg.GalilTraceCost
import PalPeg.GalilOracleMC
import PalPeg.GalilFoundLandingL

/-!
# The lexicographic cycle measure

A found cycle that breaks before any shift (`foundRouteMC_noshift`) keeps the
centre and strictly advances the right head.  `CycleOutMC` demands strict centre
progress, so such a cycle is not an admissible exit.  Here the progress clause is
weakened to the lexicographic measure

  `mu raw r = (2|raw| − position r.center) · (2|raw| + 1) + (2|raw| − position r.right)`,

which decreases when the centre strictly advances, or when the centre stays and
the right head strictly advances (both heads bounded by `2|raw|` at `InvL`).

* `CycleOutMC'` / `CycleOracleMC'` — the oracle with `mu sT < mu r`.
* `mu_lt_of_centre`, `mu_lt_of_right` — the two progress forms.
* `cycleOracleMC'_of_MC` — the old oracle is an instance.
* `reachC_fuel'`, `reachC_from_invL'` — the recursion on `mu`.
* `cycleOracleMC_of_MC'` — hence the new oracle yields the old one (every
  exit becomes a `ReachAtC`), so `checkpoints_cost'` is `checkpoints_cost`.

`interval_cost_of_costedRun` only uses the total centre advance of the costed
run between checkpoints (`CostedRun.centre`, a sum of piece advances) and
`right_mono`; a zero-advance cycle contributes a zero summand and is harmless.
-/

set_option autoImplicit false

namespace PalPeg.GalilLexMeasure

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints
open PalPeg.GalilTraceCost
open PalPeg.GalilIntervalCost PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly

/-! ## Bounds and the measure -/

theorem invS_right_le {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : InvS raw c r) :
    position r.right ≤ 2 * raw.length := by
  rcases h with h | ⟨k, h⟩
  · exact PalPeg.GalilEndOfInput.position_le r.right raw h.input
  · exact PalPeg.GalilEndOfInput.position_le r.right raw h.input

theorem invL_right_le {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : InvL raw c r) :
    position r.right ≤ 2 * raw.length := invS_right_le h.1

/-- The lexicographic measure (centre first, then the right head). -/
def mu (raw : List (Fin 2)) (r : GalilVM) : ℕ :=
  (2 * raw.length - position r.center) * (2 * raw.length + 1) +
    (2 * raw.length - position r.right)

theorem lex_lt (B x x' y y' : ℕ) (hx : x' < x) (hy' : y' ≤ B) :
    x' * (B + 1) + y' < x * (B + 1) + y := by
  have h1 : (x' + 1) * (B + 1) ≤ x * (B + 1) := Nat.mul_le_mul_right _ hx
  have h2 : (x' + 1) * (B + 1) = x' * (B + 1) + B + 1 := by ring
  omega

/-- Centre progress decreases `mu`. -/
theorem mu_lt_of_centre {raw : List (Fin 2)} {cT : Control} {r sT : GalilVM}
    (hr : position r.center ≤ 2 * raw.length) (hIT : InvL raw cT sT)
    (h : position r.center < position sT.center) : mu raw sT < mu raw r := by
  have := invS_center_le hIT.1
  unfold mu
  exact lex_lt (2 * raw.length) _ _ _ _ (by omega) (by omega)

/-- Equal centre and right-head progress decrease `mu`. -/
theorem mu_lt_of_right {raw : List (Fin 2)} {cT : Control} {r sT : GalilVM}
    (hIT : InvL raw cT sT) (hc : position sT.center = position r.center)
    (h : position r.right < position sT.right) : mu raw sT < mu raw r := by
  have := invL_right_le hIT
  unfold mu
  rw [hc]
  omega

/-! ## The oracle with lexicographic progress -/

/-- `CycleOutMC` with the progress clause `mu sT < mu r`. -/
def CycleOutMC' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ReachAtC P q first raw m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvL raw cT sT ∧ mu raw sT < mu raw r ∧
      position sT.right ≤ 2 * m - 1

/-- **The costed per-target cycle oracle, lexicographic progress.** -/
def CycleOracleMC' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length → InvL raw c r →
    position r.right ≤ 2 * m - 1 → CycleOutMC' P q first raw m c r

/-- Conversion from the centre-progress exit. -/
theorem cycleOutMC'_of_MC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (hI : InvL raw c r) (h : CycleOutMC P q first raw m c r) :
    CycleOutMC' P q first raw m c r := by
  rcases h with h | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨cT, sT, k, L, hst, hcr, hIT, mu_lt_of_centre (invS_center_le hI.1) hIT hlt, hp⟩

/-- Conversion from the no-shift exit (centre kept, right head strictly up). -/
theorem cycleOutMC'_of_noshift {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvL raw cT sT)
    (hc : position sT.center = position r.center) (hlt : position r.right < position sT.right)
    (hp : position sT.right ≤ 2 * m - 1) :
    CycleOutMC' P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT, mu_lt_of_right hIT hc hlt, hp⟩

/-- **The old oracle is an instance of the new one.** -/
theorem cycleOracleMC'_of_MC {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (h : CycleOracleMC P q first raw) : CycleOracleMC' P q first raw :=
  fun m c r h1 h2 hI hp => cycleOutMC'_of_MC hI (h m c r h1 h2 hI hp)

/-! ## The recursion on `mu` -/

theorem reachC_fuel' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC' P q first raw) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu raw r ≤ n →
      InvL raw c r → position r.right ≤ 2 * m - 1 → ReachAtC P q first raw m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, _, _, _, hlt, _⟩
    · exact hdone
    · omega
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpT⟩
    · exact hdone
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hcont⟩ := ih cT sT (by omega) hIT hpT
      exact ⟨y, k + k', L ++ L', stepsAll_trans hst hst', costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachC_from_invL' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC' P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvL raw c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtC P q first raw m c r :=
  reachC_fuel' P q first raw hor m hm1 hmle _ c r le_rfl hI hp

/-- **The new oracle yields the old one**: every admissible state reaches its
target, so the `ReachAtC` disjunct always holds. -/
theorem cycleOracleMC_of_MC' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (h : CycleOracleMC' P q first raw) : CycleOracleMC P q first raw :=
  fun _ _ _ h1 h2 hI hp => Or.inl (reachC_from_invL' P q first raw h h1 h2 hI hp)

/-! ## The checkpoint trace with costs -/

/-- **`checkpoints_cost'`** — `checkpoints_cost` from the lexicographic oracle. -/
theorem checkpoints_cost' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC' P q first raw)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 x0 ⟨c, r⟩)
    (hI : InvL raw c r) (hpos : position r.right ≤ 1) :
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS P q first) 2048 (SoundScanNR raw) st (Tc raw.length) ∧
      (∀ m m', m ≤ m' → m' ≤ raw.length → Tc m ≤ Tc m') ∧
      (∀ m, 1 ≤ m → m ≤ raw.length →
        PalPeg.GalilLedgerAssembly.ReportPointAt P q first raw m (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < raw.length →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw raw (m+1) - Cw raw m) + beta' 2048) :=
  checkpoints_cost P q first raw (cycleOracleMC_of_MC' hor) hpre hI hpos

#print axioms invS_right_le
#print axioms invL_right_le
#print axioms lex_lt
#print axioms mu_lt_of_centre
#print axioms mu_lt_of_right
#print axioms cycleOutMC'_of_MC
#print axioms cycleOutMC'_of_noshift
#print axioms cycleOracleMC'_of_MC
#print axioms reachC_fuel'
#print axioms reachC_from_invL'
#print axioms cycleOracleMC_of_MC'
#print axioms checkpoints_cost'

end PalPeg.GalilLexMeasure
