import PalPeg.TextFeedPipelineCoupled
import PalPeg.GSVerifierZ

/-! The report predicate uses only four tape focuses and one bounded FIFO
peek. In particular, neither input length nor a ghost counter is read. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineReport
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineVerifier PalPeg.GSVerifierZ
variable {k : ℕ}

def report (e : Env k) (σ : Fin 39 → Fin k) (head : Fin k) : Bool :=
  decide (σ 11 = e.endSym ∧ σ 19 = e.endSym ∧ σ 38 = e.mark ∧
    σ 12 = e.blank ∧ head = e.mark)

/-- Blank at the scan head means the written frontier, not necessarily
the arrival frontier. The FIFO test is essential to distinguish them. -/
theorem frontier_iff {e : Env k} {Text leftPat rightPat : List (Fin k)}
    {rate p r n : ℕ} {u : Snapshot k} {z : VStateZ}
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hghost : u.model.z = (z.1, z.2.head))
    (hq : Ready e.blank e.mark u.qt1 u.mode1 u.model.Q1)
    (hb : e.blank ∉ Text) (hn : n ≤ Text.length) :
    (Tape.read (u.model.vt.1 GSTapes.tT) = e.blank ∧
      (toList u.model.Q1).head?.getD e.mark = e.mark) ↔ z.1.pos + z.1.q = n := by
  have hblank := VerifierFeedRaw.read1_blank_iff hb hn (VerifierFeedRaw.of_feedInv hfeed).one
  rw [hghost] at hblank
  have hempty : toList u.model.Q1 = [] ↔ u.model.m1 = n := by
    rw [hfeed.qlist1, List.drop_eq_nil_iff, List.length_take, Nat.min_eq_left hn]
    have hle := hfeed.m1le
    omega
  have hhead := hfeed.hd1
  rw [hghost] at hhead
  dsimp only at hblank hhead
  rw [hblank, peek_marker_iff hq, hempty]
  have hle := hfeed.m1le
  constructor
  · rintro ⟨h, h'⟩; exact h.trans h'
  · intro h; exact ⟨by omega, by omega⟩

/-- At a verified macro boundary, the finite physical observation is
exactly the ideal report bit, including its input-time equality. -/
theorem report_eq {e : Env k} {Text leftPat rightPat : List (Fin k)}
    {rate p r n : ℕ} {u : Snapshot k} {z : VStateZ}
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hghost : u.model.z = (z.1, z.2.head))
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hq : Ready e.blank e.mark u.qt1 u.mode1 u.model.Q1)
    (hb : e.blank ∉ Text) (hn : n ≤ Text.length) (hmb : e.mark ≠ e.blank)
    (hel : e.endSym ∉ leftPat) (her : e.endSym ∉ rightPat) :
    report e (fun j => (tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir j).focus)
      ((toList u.model.Q1).head?.getD e.mark) = zReportFlag leftPat rightPat n z := by
  have hp : Tape.read (u.model.vt.1 GSTapes.tP) = e.endSym ↔ z.1.q = rightPat.length := by
    have hh := hfeed.qle
    rw [hghost] at hh
    change z.1.q ≤ rightPat.length at hh
    constructor
    · intro h
      by_contra he
      have hlt : u.model.z.1.q < rightPat.length := by rw [hghost]; dsimp; omega
      exact GSTapes.read_P_ne_end' her hfeed.scan hlt h
    · intro h
      apply GSTapes.read_P_end' hfeed.scan
      simpa only [hghost] using h
  have hu : Tape.read u.model.vt.2.U = e.endSym ↔ z.2.head = leftPat.length := by
    have hh := hfeed.cle
    rw [hghost] at hh
    change z.2.head ≤ leftPat.length at hh
    constructor
    · intro h
      by_contra he
      have hlt : u.model.z.2 < leftPat.length := by rw [hghost]; dsimp; omega
      exact GSVTapes.read_U_ne_end hel hfeed.pat hlt h
    · intro h
      apply GSVTapes.read_U_end hfeed.pat
      simpa only [hghost] using h
  have hd : u.dir.focus = e.mark ↔ z.2.up = true := by
    rw [hdir]
    cases z.2.up <;> simp [GSVProgZLoop.dirTape, GSVProgZLoop.dirSymbol, Ne.symm hmb]
  have hf := frontier_iff hfeed hghost hq hb hn
  apply Bool.eq_iff_iff.mpr
  simp only [report, decide_eq_true_eq]
  change (Tape.read (u.model.vt.1 GSTapes.tP) = e.endSym ∧
    Tape.read u.model.vt.2.U = e.endSym ∧ u.dir.focus = e.mark ∧
    Tape.read (u.model.vt.1 GSTapes.tT) = e.blank ∧
    (toList u.model.Q1).head?.getD e.mark = e.mark) ↔ _
  rw [hp, hu, hd, hf]
  simp only [zReportFlag, Bool.and_eq_true, decide_eq_true_eq, zdone]
  constructor
  · rintro ⟨hp, hu, hd, hn⟩
    exact ⟨⟨hp, by omega⟩, hd, hu⟩
  · rintro ⟨⟨hp, hn⟩, hd, hu⟩
    exact ⟨hp, hu, hd, by omega⟩

/-- info: 'PalPeg.TextFeedPipelineReport.report_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms report_eq

open PalPeg.RTQueueProg PalPeg.RTQueueDispatch

def frontIdx (ρ : Role) : Fin 39 := Fin.castAdd 29 (ridx ρ)

noncomputable def frontRole (e : Env k) (tag : Fin k) : Role :=
  if h : ∃ m : Mode, e.code m = tag then (Classical.choose h).roles .front else .front

theorem frontRole_code {e : Env k} (hc : Function.Injective e.code) (m : Mode) :
    frontRole e (e.code m) = m.roles .front := by
  have h : ∃ m' : Mode, e.code m' = e.code m := ⟨m, rfl⟩
  simp only [frontRole, dif_pos h]
  rw [hc (Classical.choose_spec h)]

def probe (e : Env k) (ρ : Role) (T : Fin 39 → STape (Fin k)) : Fin 39 → STape (Fin k) :=
  fun j => if j = frontIdx ρ then (T j).applyAction e.blank (e.blank, .left) else T j

def restore (e : Env k) (ρ : Role) (T : Fin 39 → STape (Fin k)) : Fin 39 → STape (Fin k) :=
  fun j => if j = frontIdx ρ then (T j).applyAction e.blank ((T j).focus, .right) else T j

/-- A two-microstep observer. The first step decodes the finite role tag
and probes Q1; the second stores the report bit in finite control and
restores the head. It does not consume or copy a queue element. -/
noncomputable def reader (e : Env k) : StructuredMachine Unit (Bool × Role × Bool) (Fin k) 39 2 where
  tapeCount_pos := by decide
  blank := e.blank
  initial := (false, .front, false)
  accepting q := q.2.2
  micro q _ σ :=
    if q.1 then
      ((false, q.2.1, report e σ (σ (frontIdx q.2.1))),
        fun j => (σ j, if j = frontIdx q.2.1 then .right else .stay))
    else
      let ρ := frontRole e (σ 10)
      ((true, ρ, q.2.2), fun j => if j = frontIdx ρ then (e.blank, .left) else (σ j, .stay))

theorem reader_probe (e : Env k) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k))
    (a : Option Unit) :
    (reader e).sMicroStep ⟨(false, ρ, b), T⟩ a =
      ⟨(true, frontRole e (T 10).focus, b), probe e (frontRole e (T 10).focus) T⟩ := by
  unfold StructuredMachine.sMicroStep reader
  dsimp only
  congr 1
  funext j
  by_cases h : j = frontIdx (frontRole e (T 10).focus) <;> simp [probe, h, STape.applyAction]

theorem reader_restore (e : Env k) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k))
    (a : Option Unit) :
    (reader e).sMicroStep ⟨(true, ρ, b), T⟩ a =
      ⟨(false, ρ, report e (fun j => (T j).focus) (T (frontIdx ρ)).focus), restore e ρ T⟩ := by
  unfold StructuredMachine.sMicroStep reader
  dsimp only
  congr 1
  funext j
  by_cases h : j = frontIdx ρ <;> simp [restore, h, STape.applyAction]

theorem reader_round (e : Env k) (ρ : Role) (b : Bool) (T : Fin 39 → STape (Fin k)) :
    (reader e).sRound ⟨(false, ρ, b), T⟩ () =
      let ρ' := frontRole e (T 10).focus
      let U := probe e ρ' T
      ⟨(false, ρ', report e (fun j => (U j).focus) (U (frontIdx ρ')).focus), restore e ρ' U⟩ := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs, List.replicate_succ,
    List.replicate_zero, List.foldl_cons, List.foldl_nil]
  rw [reader_probe, reader_restore]

theorem probe_spec {e : Env k} {ρ : Role} {T : Fin 39 → STape (Fin k)}
    {tp : TapeConfiguration k} {l : List (Fin k)}
    (hT : T (frontIdx ρ) = toS tp) (hs : SStack e.blank e.mark tp l) :
    (probe e ρ T (frontIdx ρ)).focus = l.head?.getD e.mark ∧ restore e ρ (probe e ρ T) = T := by
  have hp : probe e ρ T (frontIdx ρ) = toS (Tape.step e.blank tp e.blank .left) := by
    simp only [probe, ite_true, hT, toS_step]
  refine ⟨?_, ?_⟩
  · rw [hp]
    exact sstack_probe hs
  · funext j
    by_cases hj : j = frontIdx ρ
    · subst j
      simp only [restore, ite_true, hp, toS_focus, ← toS_step]
      exact (congrArg toS (stack_probe_restore hs)).trans hT.symm
    · simp only [restore, probe, if_neg hj]

theorem probe_report (e : Env k) (ρ : Role) (T : Fin 39 → STape (Fin k)) (head : Fin k) :
    report e (fun j => (probe e ρ T j).focus) head = report e (fun j => (T j).focus) head := by
  have hlt : (frontIdx ρ).val < 10 := (ridx ρ).isLt
  have hne : ∀ j : Fin 39, 10 ≤ j.val → j ≠ frontIdx ρ := by
    intro j hj he
    have := congrArg Fin.val he
    omega
  simp only [report, probe, if_neg (hne 11 (by decide)), if_neg (hne 12 (by decide)),
    if_neg (hne 19 (by decide)), if_neg (hne 38 (by decide))]

/-- Queue readiness alone suffices for a non-destructive observation;
no GS macro invariant is needed to restore the tapes. -/
theorem reader_front {e : Env k} (hc : Function.Injective e.code)
    (T : Fin 39 → STape (Fin k)) (qt : QT k) (mode : Mode) (Q : Queue (Fin k))
    (htag : (T 10).focus = e.code mode)
    (hview : ∀ ρ : Role, T (frontIdx ρ) = toS (qt ρ))
    (hq : Ready e.blank e.mark qt mode Q) (ρ : Role) (b : Bool) :
    (reader e).sRound ⟨(false, ρ, b), T⟩ () =
      ⟨(false, mode.roles .front,
        report e (fun j => (T j).focus) ((toList Q).head?.getD e.mark)), T⟩ := by
  rw [reader_round]
  simp only [htag, frontRole_code hc]
  obtain ⟨hr, ht⟩ := probe_spec (hview (mode.roles .front)) hq.enc.front
  have hh : Q.front.head? = (toList Q).head? := head?_eq hq.inv
  rw [ht, hr, probe_report, hh]

theorem reader_queue {e : Env k} (hc : Function.Injective e.code) (u : Snapshot k)
    (hq : Ready e.blank e.mark u.qt1 u.mode1 u.model.Q1) (ρ : Role) (b : Bool) :
    let T := tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
    (reader e).sRound ⟨(false, ρ, b), T⟩ () =
      ⟨(false, u.mode1.roles .front,
        report e (fun j => (T j).focus) ((toList u.model.Q1).head?.getD e.mark)), T⟩ :=
  reader_front hc _ u.qt1 u.mode1 u.model.Q1 rfl (by intro ρ'; cases ρ' <;> rfl) hq ρ b

/-- The actual two-step observer restores all 39 tapes, and its finite
accepting bit equals the ideal report at this encoded boundary. -/
theorem reader_report {e : Env k} (hc : Function.Injective e.code)
    {Text leftPat rightPat : List (Fin k)} {rate p r n : ℕ} {u : Snapshot k} {z : VStateZ}
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hghost : u.model.z = (z.1, z.2.head))
    (hdir : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hq : Ready e.blank e.mark u.qt1 u.mode1 u.model.Q1)
    (hb : e.blank ∉ Text) (hn : n ≤ Text.length) (hmb : e.mark ≠ e.blank)
    (hel : e.endSym ∉ leftPat) (her : e.endSym ∉ rightPat) (ρ : Role) (b : Bool) :
    let T := tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
    (reader e).sRound ⟨(false, ρ, b), T⟩ () =
      ⟨(false, u.mode1.roles .front, zReportFlag leftPat rightPat n z), T⟩ := by
  dsimp only
  rw [reader_queue hc u hq, report_eq hfeed hghost hdir hq hb hn hmb hel her]

/-- info: 'PalPeg.TextFeedPipelineReport.reader_report' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reader_report

end PalPeg.TextFeedPipelineReport
