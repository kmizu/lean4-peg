import PalPeg.GalilOracleLocal

/-!
# The run trace: remembering the cycles

`PalPeg.GalilOracleLocal.run_from_invL` builds a `LocalReport` but forgets the
cycles it went through.  The real-time ledger needs them, so this module
re-runs the same well-founded recursion (measure `2 * raw.length - position
centre`, as in `runL_fuel`) and keeps a relational trace.

Each cycle is recorded as a `CycleRec`: its tick count, the centre before and
after, the right-head position before and after, and the **frontier**
`front s = position s.right + value s.replay` before and after.  The final
report segment is recorded separately as a `ReportRec` (tick count and report
point), an extra index of `CycleTrace`.

Right-head positions are *not* monotone (a fallback moves the right head back
to the centre).  What should be monotone is the frontier.  `CycleOutL` carries
no information about the right head, so the frontier step is added as an
explicit field in `CycleOutL'` / `CycleOracleL'` (an **obligation** for
whoever discharges the oracle; `cycleOracleL_of_L'` forgets it).
-/

set_option autoImplicit false

namespace PalPeg.GalilRunTrace

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier
open GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge
open PalPeg.GalilOracleLocal

/-! ## Records -/

/-- The frontier: right-head position plus the pending replay. -/
def front (s : GalilVM) : ℤ :=
  (position s.right : ℤ) + GalilScaffoldCounter.value s.replay

theorem front_ofNat {s : GalilVM} {m : ℕ} (h : s.replay = GalilScaffoldCounter.ofNat m) :
    front s = (position s.right : ℤ) + m := by
  simp [front, h, GalilScaffoldCounter.value, GalilScaffoldCounter.ofNat]

/-- Under `Frontier`, the frontier is bounded by the arrived material. -/
theorem front_le_arrived {s : GalilVM} {m : ℕ} (h : s.replay = GalilScaffoldCounter.ofNat m)
    (hF : Frontier s) : front s ≤ 2 * (arrived s.right : ℤ) := by
  rw [front_ofNat h]; have := hF m h; omega

/-- One cycle of the main loop. -/
structure CycleRec where
  k : ℕ
  cenLo : ℕ
  cenHi : ℕ
  rightLo : ℕ
  rightHi : ℕ
  frontLo : ℤ
  frontHi : ℤ

/-- The final report segment: its tick count and the report point. -/
structure ReportRec where
  k : ℕ
  y : State GalilVM

/-- The record of a cycle from `r` to `sT` taking `k` ticks. -/
def recOf (k : ℕ) (r sT : GalilVM) : CycleRec :=
  ⟨k, position r.center, position sT.center, position r.right, position sT.right,
    front r, front sT⟩

/-! ## The trace -/

/-- The relational trace of a run: a list of cycles followed by one report
segment (recorded in the extra index `ReportRec`). -/
inductive CycleTrace (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) :
    Control → GalilVM → List CycleRec → ReportRec → Prop
  | report (c : Control) (r : GalilVM) (k : ℕ) (y : State GalilVM)
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ y)
      (hrp : ReportPoint raw y) (hfr : Refreshed P q first y) :
      CycleTrace P q first raw c r [] ⟨k, y⟩
  | cycle (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (k : ℕ)
      {l : List CycleRec} {R : ReportRec}
      (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
      (hI : InvL raw cT sT) (hlt : position r.center < position sT.center)
      (rest : CycleTrace P q first raw cT sT l R) :
      CycleTrace P q first raw c r (recOf k r sT :: l) R

/-! ## Construction -/

theorem trace_fuel {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleL P q first raw) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      InvL raw c r → ∃ l R, CycleTrace P q first raw c r l R := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI
    rcases hor c r hI with ⟨y, ⟨k, hst⟩, hrp, hfr⟩ | ⟨cT, sT, k, _, hIT, hlt⟩
    · exact ⟨[], ⟨k, y⟩, .report c r k y hst hrp hfr⟩
    · exact absurd (invS_center_le hIT.1) (by have := invS_center_le hI.1; omega)
  | succ n ih =>
    intro c r hn hI
    rcases hor c r hI with ⟨y, ⟨k, hst⟩, hrp, hfr⟩ | ⟨cT, sT, k, hst, hIT, hlt⟩
    · exact ⟨[], ⟨k, y⟩, .report c r k y hst hrp hfr⟩
    · obtain ⟨l, R, ht⟩ := ih cT sT (by have := invS_center_le hIT.1; omega) hIT
      exact ⟨_, R, .cycle c r cT sT k hst hIT hlt ht⟩

/-- **The trace exists** from every `InvL` state. -/
theorem trace_from_invL {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleL P q first raw) {c : Control} {r : GalilVM} (hI : InvL raw c r) :
    ∃ l R, CycleTrace P q first raw c r l R :=
  trace_fuel hor _ c r le_rfl hI

/-! ## Ticks -/

/-- **Total ticks**: the concatenated run takes `Σ cycle ticks + report ticks`
and ends at the recorded report point. -/
theorem trace_total_ticks {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw)
        ((l.map CycleRec.k).sum + R.k) ⟨c, r⟩ R.y ∧
      ReportPoint raw R.y ∧ Refreshed P q first R.y := by
  induction h with
  | report c r k y hst hrp hfr => exact ⟨by simpa using hst, hrp, hfr⟩
  | cycle c r cT sT k hst _ _ _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, h2, h3⟩
    have := stepsAll_trans hst h1
    simpa [recOf, Nat.add_assoc] using this

/-! ## Linkage and centres -/

/-- The first record starts at the current state. -/
theorem trace_head {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    ∀ x ∈ l.head?, x.cenLo = position r.center ∧ x.rightLo = position r.right ∧
      x.frontLo = front r := by
  cases h with
  | report => simp
  | cycle => simp [recOf]

theorem isChain_cons_of {α : Type} {Rl : α → α → Prop} {a : α} {l : List α}
    (h : ∀ y ∈ l.head?, Rl a y) (hl : l.IsChain Rl) : (a :: l).IsChain Rl := by
  cases l with
  | nil => exact .singleton a
  | cons y l => exact List.isChain_cons_cons.mpr ⟨h y (by simp), hl⟩

/-- Consecutive records are glued: each cycle starts where the previous ended. -/
theorem trace_linked {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    l.IsChain (fun a b => a.cenHi = b.cenLo ∧ a.rightHi = b.rightLo ∧ a.frontHi = b.frontLo) := by
  induction h with
  | report => exact .nil
  | cycle c r cT sT k _ _ _ rest ih =>
    refine isChain_cons_of (fun y hy => ?_) ih
    obtain ⟨h1, h2, h3⟩ := trace_head rest y hy
    exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem trace_above {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    ∀ b ∈ l, position r.center ≤ b.cenLo ∧ position r.center < b.cenHi := by
  induction h with
  | report => simp
  | cycle c r cT sT k _ _ hlt _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨le_rfl, hlt⟩
    · obtain ⟨h1, h2⟩ := ih b hb; exact ⟨by omega, by omega⟩

/-- **Centres strictly increase** along the trace (within each cycle and from
cycle to cycle). -/
theorem trace_centres_mono {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    (∀ x ∈ l, x.cenLo < x.cenHi) ∧
      l.Pairwise (fun a b => a.cenLo < b.cenLo ∧ a.cenHi < b.cenHi) := by
  induction h with
  | report => simp
  | cycle c r cT sT k _ _ hlt rest ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, List.Pairwise.cons ?_ ih2⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hlt
      · exact ih1 x hx
    · intro b hb
      obtain ⟨h1, h2⟩ := trace_above rest b hb
      simp only [recOf]
      exact ⟨by omega, by have := ih1 b hb; omega⟩

/-- Every landing centre is within the doubled input. -/
theorem trace_centre_bound {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    ∀ x ∈ l, x.cenHi ≤ 2 * raw.length := by
  induction h with
  | report => simp
  | cycle c r cT sT k _ hI _ _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact invS_center_le hI.1
    · exact ih x hx

/-- The number of cycles is bounded by the measure. -/
theorem trace_length {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) :
    l.length ≤ 2 * raw.length - position r.center := by
  induction h with
  | report => simp
  | cycle c r cT sT k _ hI hlt _ ih =>
    have := invS_center_le hI.1
    simp only [List.length_cons]; omega

/-! ## The frontier -/

/-- The oracle output with the frontier obligation added to the cycle exit. -/
def CycleOutL' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (c : Control) (r : GalilVM) : Prop :=
  LocalReport P q first raw c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      InvL raw cT sT ∧ position r.center < position sT.center ∧ front r ≤ front sT

def CycleOracleL' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (c : Control) (r : GalilVM), InvL raw c r → CycleOutL' P q first raw c r

theorem cycleOracleL_of_L' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (h : CycleOracleL' P q first raw) : CycleOracleL P q first raw := by
  intro c r hI
  rcases h c r hI with h | ⟨cT, sT, k, hst, hIT, hlt, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨cT, sT, k, hst, hIT, hlt⟩

/-- Every cycle's frontier does not decrease. -/
def FrontOK (l : List CycleRec) : Prop := ∀ x ∈ l, x.frontLo ≤ x.frontHi

theorem trace_fuel' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleL' P q first raw) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), 2 * raw.length - position r.center ≤ n →
      InvL raw c r → ∃ l R, CycleTrace P q first raw c r l R ∧ FrontOK l := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI
    rcases hor c r hI with ⟨y, ⟨k, hst⟩, hrp, hfr⟩ | ⟨cT, sT, k, _, hIT, hlt, _⟩
    · exact ⟨[], ⟨k, y⟩, .report c r k y hst hrp hfr, by simp [FrontOK]⟩
    · exact absurd (invS_center_le hIT.1) (by have := invS_center_le hI.1; omega)
  | succ n ih =>
    intro c r hn hI
    rcases hor c r hI with ⟨y, ⟨k, hst⟩, hrp, hfr⟩ | ⟨cT, sT, k, hst, hIT, hlt, hfront⟩
    · exact ⟨[], ⟨k, y⟩, .report c r k y hst hrp hfr, by simp [FrontOK]⟩
    · obtain ⟨l, R, ht, hok⟩ := ih cT sT (by have := invS_center_le hIT.1; omega) hIT
      refine ⟨_, R, .cycle c r cT sT k hst hIT hlt ht, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hfront
      · exact hok x hx

/-- **The trace with the frontier obligation.** -/
theorem trace_from_invL' {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleL' P q first raw) {c : Control} {r : GalilVM} (hI : InvL raw c r) :
    ∃ l R, CycleTrace P q first raw c r l R ∧ FrontOK l :=
  trace_fuel' hor _ c r le_rfl hI

theorem trace_front_above {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) (hok : FrontOK l) :
    ∀ b ∈ l, front r ≤ b.frontLo ∧ front r ≤ b.frontHi := by
  induction h with
  | report => simp
  | cycle c r cT sT k _ _ _ _ ih =>
    intro b hb
    have hself : front r ≤ front sT := hok _ (List.mem_cons_self ..)
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨le_rfl, hself⟩
    · obtain ⟨h1, h2⟩ := ih (fun x hx => hok x (List.mem_cons_of_mem _ hx)) b hb
      exact ⟨le_trans hself h1, le_trans hself h2⟩

/-- **The frontier is non-decreasing** along the trace (the right head itself
is not: a fallback moves it back to the centre). -/
theorem trace_front_mono {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    {c : Control} {r : GalilVM} {l : List CycleRec} {R : ReportRec}
    (h : CycleTrace P q first raw c r l R) (hok : FrontOK l) :
    l.Pairwise (fun a b => a.frontLo ≤ b.frontLo ∧ a.frontHi ≤ b.frontHi) := by
  induction h with
  | report => simp
  | cycle c r cT sT k _ _ _ rest ih =>
    have hok' : FrontOK _ := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    have hself : front r ≤ front sT := hok _ (List.mem_cons_self ..)
    refine List.Pairwise.cons ?_ (ih hok')
    intro b hb
    obtain ⟨h1, -⟩ := trace_front_above rest hok' b hb
    simp only [recOf]
    exact ⟨le_trans hself h1, h1.trans (hok' b hb)⟩

#print axioms front_le_arrived
#print axioms trace_from_invL
#print axioms trace_total_ticks
#print axioms trace_head
#print axioms trace_linked
#print axioms trace_centres_mono
#print axioms trace_centre_bound
#print axioms trace_length
#print axioms cycleOracleL_of_L'
#print axioms trace_from_invL'
#print axioms trace_front_mono

end PalPeg.GalilRunTrace
