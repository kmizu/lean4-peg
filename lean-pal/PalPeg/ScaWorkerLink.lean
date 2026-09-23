import PalPeg.ScaHeadGen
import PalPeg.ScaWindowInstance
import PalPeg.ScaWorkerRegs
import PalPeg.ScaGsCertFunctional
import PalPeg.ScaMatcherReaders

/-!
# The real matcher worker, operation by operation, as the logical head VM

`ScaHeadVM.match_step_certified` relates **one** step of the coroutine matcher worker to one
`stepMatch` step of the logical head VM. This file lifts that to the operations the window
controller calls on the **real** (table-compiled) matcher `ScaWindowInstance.matcher`:

* `link_step` — one active table step is one `stepMatch` step;
* `service_link` — `service` (`quantum = 2048` steps, each active iff `mode = run`) is
  `iterStep quantum` of the head VM; `service_returned` (a returned coroutine faults: the table
  sits in its `halt` sink), `service_idle` (a non-running worker does nothing);
* `arrive_link` (`arrive` = `HVM.append`), `start_link` (`start` = `matchInitial` on the
  reversed text read so far);
* `tick_run` / `tick_birth` / `tick_idle` / `tick_returned`: `matcherTick` = arrive, start on
  `birth`, service; `stageRound_run` / `stageRound_birth` / `stageRound_idle`: the same inside
  the controller's `ScaWindowPal.stageRound` (`stageRound_self`, `stageRound_other`).

Before its first `start` a matcher is only `Ready` (register invariant for some ghost, `end` at
the frontier, register-file sizes): `ready_initial`, `ready_arrive`, `ready_of_link`.

## The relation

`Link W ρ s v` relates a real matcher state `s` to a head VM `v`, with the pattern boundary `W`
(the `end` at the last `start`) and a ghost orientation `ρ` (which heads are reversed):

* `sim` — the head VM's coroutine control is simulated by the table row `s.pc` (the certificate);
* `heads` — `ScaHeadVM.MatchRel` for the readers live at `s.pc` (word, heads);
* `orient` — the `reverse` bits of the live readers are `ρ`;
* `inv` — `ScaWorkerRegs.Inv`: the distance registers are the head-position differences of the
  pairs live at `s.pc` (with the head VM's positions as the ghost), and the counter keys;
* `endText` — `end` is the arrival frontier.

The ghost orientation moves with the head VM (`orientAt`: a `copy t s` gives `t` the orientation
of `s`), so every side condition is a statement about the head-VM run.

## The side conditions (`StepSide`), on the head-VM states `iterStep i v`, `i < quantum`

* `reads` — a `symbols a b` reads `a`, `b` on their side (`OnSide`: reversed heads in `[0, W)`,
  forward heads at `≥ W`);
* `available` — `available h` tests a forward head;
* `moves` — a moved reversed reader stays at `≤ W`;
* `matchB` — at `match`, `B` is forward and has reached the arrival frontier (the worker's
  extra `require`, `ScaHeadVM.matchLate`).

## What is assumed about the table (`ReaderFacts`)

Five finite facts about `liveReaders matcherWorker` (post-fixpoint, proper colouring on each
after-set, every live reader coloured, the start row's readers inside `{Origin, Tail}`, `B` live
before each `match` row); all five evaluate to `true` under `#eval`. `decide +kernel` evaluates
`liveReaders` in about a minute but needs about 17 GB, so they are a hypothesis here. They are
proved by certificate in `ScaMatcherReaders` (`⟨fix, proper, colored, startLive, matchB⟩` fills
`ReaderFacts`); that module is not imported here.
-/

set_option autoImplicit false

namespace PalPeg.ScaWorkerLink

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaGsCert PalPeg.ScaWindowWorker
  PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM PalPeg.ScaHeadGen

/-! ## The matcher's static data -/

/-- The matcher's worker data. -/
abbrev spec : WorkerSpec := ScaGsTables.matcherWorker

/-- The matcher's certificate. -/
abbrev vs : List Entry := ScaGsCertData.matcherCert

/-- The coroutine matcher worker certified against the table. -/
abbrev cw : CoWorker := certWorker spec matchTests matcherInitial vs

theorem certified : Certified spec cw vs := ScaGsCertFunctional.matcher_certified

/-- The real matcher is the table worker of `spec`. -/
theorem matcher_eq : ScaWindowInstance.matcher = Worker.ofSpec spec := rfl

/-- The service quantum. -/
theorem quantum_eq : spec.quantum = 2048 := rfl

theorem isFlags_eq : spec.isFlags = false := rfl

/-- The readers live before row `r`. -/
def readersAt (r : ℕ) : List String := (liveReaders spec).getD r []

/-- The readers live after `row`. -/
def afterR (row : Row) : List String := successorsUnion (liveReaders spec) row.targets

theorem lookupFirst_mem {α β : Type} [DecidableEq α] {a : α} {xs : List (α × β)} {b : β}
    (h : lookupFirst a xs = some b) : ∃ p ∈ xs, p.1 = a ∧ p.2 = b := by
  unfold lookupFirst at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp, rfl⟩

theorem colorsBound : ColorsBound spec := by
  intro h i hc
  obtain ⟨p, hp, -, rfl⟩ := lookupFirst_mem hc
  have key : ∀ q ∈ spec.readers.colors, q.2 < spec.readers.registers := by decide
  exact key p hp

theorem notBlind : ReadersNotBlind spec blind := by
  intro h i hc
  obtain ⟨p, hp, rfl, -⟩ := lookupFirst_mem hc
  have key : ∀ q ∈ spec.readers.colors, q.1 ∉ blind := by decide
  exact key p hp

theorem color_origin : color spec "Origin" = some 1 := by decide
theorem color_tail : color spec "Tail" = some 4 := by decide
theorem color_B : color spec "B" = some 2 := by decide
theorem color_originalEnd : color spec "OriginalEnd" = none := by decide

/-- No distance register tracks a pair with `OriginalEnd` (the matcher never reads it). -/
theorem distColor_originalEnd {p : Pair} {i : ℕ}
    (h : lookupFirst p spec.distances.colors = some i) :
    p.1 ≠ "OriginalEnd" ∧ p.2 ≠ "OriginalEnd" := by
  obtain ⟨q, hq, rfl, -⟩ := lookupFirst_mem h
  have key : ∀ q ∈ spec.distances.colors, q.1.1 ≠ "OriginalEnd" ∧ q.1.2 ≠ "OriginalEnd" := by
    decide
  exact key q hq

/-! ## Move batches name each head once, so both move semantics agree -/

theorem sumDelta_eq_zero {ms : List Movement} {h : String} (hn : h ∉ ms.map (·.head)) :
    sumDelta ms h = 0 := by
  by_contra hne
  obtain ⟨m, hm, hmh⟩ := exists_of_sumDelta_ne hne
  exact hn (List.mem_map.mpr ⟨m, hm, hmh⟩)

/-- With pairwise distinct heads, the ROM's `lookupLast` delta is Python's summed delta. -/
theorem moveDelta_eq_sumDelta : ∀ {ms : List Movement}, (ms.map (·.head)).Nodup → ∀ h,
    ScaWorkerRegs.moveDelta ms h = sumDelta ms h
  | [], _, h => rfl
  | m :: ms, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih := moveDelta_eq_sumDelta hnd.2 h
    rw [sumDelta_cons]
    unfold ScaWorkerRegs.moveDelta lookupLast at ih ⊢
    rw [List.map_cons, List.reverse_cons, List.find?_append]
    by_cases hmh : m.head = h
    · subst hmh
      have hnone : (ms.map fun m => (m.head, m.delta)).reverse.find?
          (fun x => decide (x.1 = m.head)) = none := by
        rw [List.find?_eq_none]
        intro x hx
        simp only [List.mem_reverse, List.mem_map] at hx
        obtain ⟨m', hm', rfl⟩ := hx
        simp only [decide_eq_true_eq]
        intro heq
        exact hnd.1 (List.mem_map.mpr ⟨m', hm', heq⟩)
      rw [hnone, sumDelta_eq_zero hnd.1]
      simp
    · simp [hmh, ih]

theorem headStep_eq_movePos {e : Event} (hnd : ∀ ms, e = .move ms → (ms.map (·.head)).Nodup)
    (π : String → ℤ) : ScaWorkerRegs.headStep e π = movePos e π := by
  cases e with
  | move ms =>
    funext h
    show π h + ScaWorkerRegs.moveDelta ms h = π h + sumDelta ms h
    rw [moveDelta_eq_sumDelta (hnd ms rfl)]
  | copy t src =>
    funext h
    show (if h = t then π src else π h) = Function.update π t (π src) h
    rw [Function.update_apply]
  | _ => rfl

/-- Every move row of the matcher names each head once. -/
def movesNodupB : Bool :=
  spec.program.code.all fun row =>
    match row.event with
    | .move ms => decide ((ms.map (·.head)).Nodup)
    | _ => true

theorem movesNodupB_eq : movesNodupB = true := by decide +kernel

theorem moves_nodup {r : ℕ} {row : Row} (hrow : spec.program.code[r]? = some row) :
    ∀ ms, row.event = .move ms → (ms.map (·.head)).Nodup := by
  intro ms hms
  have h := movesNodupB_eq
  unfold movesNodupB at h
  rw [List.all_eq_true] at h
  have hr := h row (List.mem_of_getElem? hrow)
  rw [hms] at hr
  simpa using hr

/-! ## The distance registers answer the comparisons -/

/-- `ScaWorkerRegs.RegInv` gives `ScaHeadVM`'s register hypothesis `hregs` at the current row. -/
theorem regsValue_of_regInv {pos : String → ℤ} {s : WorkerState}
    (hinv : ScaWorkerRegs.RegInv spec pos s) {row : Row}
    (hrow : spec.program.code[s.pc]? = some row) :
    RegsValue ((Worker.ofSpec spec).fields s.pc) s pos row.event := by
  intro a b hcmp
  rw [fields_ofSpec spec hrow]
  obtain ⟨event, targets⟩ := row
  have hcompare : event = .less a b ∨ event = .equal a b ∨ event = .assertEqual a b := by
    rcases hcmp with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  obtain ⟨htest, hreverse⟩ := ScaWorkerRegs.fieldsAt_test (spec := spec) (liveReaders spec)
    (liveDistances spec) s.pc targets hcompare
  have hlive : ∀ {q : Pair}, pairOf spec.names a b = some q →
      ScaWorkerRegs.Tracks spec pos s.regs q := fun hpair =>
    hinv.live _ (ScaWorkerRegs.matcher_tableFacts.transferLive s.pc _ hrow _
      (ScaWorkerRegs.mem_transfer_compare hcompare hpair))
  rw [htest, hreverse]
  rcases ScaWorkerRegs.canonical_cases spec.names a b with
    ⟨hsame, hcan, _⟩ | ⟨hcan, hpair⟩ | ⟨hcan, hpair⟩
  · rw [hcan]
    subst hsame
    simp [selectReg]
  · obtain ⟨j, hj, hval⟩ := hlive hpair
    have hval' : s.regs[j]?.getD 0 = pos a - pos b := by
      rw [← List.getD_eq_getElem?_getD]; exact hval
    rw [hcan]
    simp [selectReg, hj, hval']
  · obtain ⟨j, hj, hval⟩ := hlive hpair
    have hval' : s.regs[j]?.getD 0 = pos b - pos a := by
      rw [← List.getD_eq_getElem?_getD]; exact hval
    rw [hcan]
    simp [selectReg, hj, hval']

/-! ## The reader-liveness facts assumed of the table -/

/-- Finite facts about the reader liveness `liveReaders spec` of the matcher table (the table
hypotheses `hfix`, `hproper`, `hcolored` of `ScaHeadVM.match_step_certified`, for every row,
and two facts for `start` and `match`). -/
structure ReaderFacts : Prop where
  /-- `liveReaders` is a post-fixpoint of `readerTransfer`. -/
  fix : ∀ (r : ℕ) (row : Row), spec.program.code[r]? = some row →
    ∀ x ∈ readerTransfer row (afterR row), x ∈ readersAt r
  /-- Distinct readers live after a row have distinct registers. -/
  proper : ∀ (r : ℕ) (row : Row), spec.program.code[r]? = some row → Proper spec (afterR row)
  /-- Every live reader has a register. -/
  colored : ∀ r : ℕ, Colored spec (readersAt r)
  /-- At the start row only `Origin` and `Tail` are live. -/
  startLive : ∀ h ∈ readersAt spec.program.start, h = "Origin" ∨ h = "Tail"
  /-- `B` is live before every `match` row. -/
  matchB : ∀ (r : ℕ) (row : Row), spec.program.code[r]? = some row →
    ∀ h, row.event = .«match» h → "B" ∈ readersAt r

/-! ## The ghost orientation, carried along the head-VM run -/

/-- The orientations after the head VM's pending instruction (`copy t s`: `t` takes `s`'s). -/
def orientStep (v : HVM) (ρ : String → Bool) : String → Bool :=
  match v.ctl with
  | .pending _ e => moveRev e ρ
  | _ => ρ

/-- The orientations after `n` head-VM steps (frozen where the run stops). -/
def orientAt : ℕ → HVM → (String → Bool) → String → Bool
  | 0, _, ρ => ρ
  | n + 1, v, ρ =>
    match stepMatch v with
    | some v' => orientAt n v' (orientStep v ρ)
    | none => ρ

theorem orientAt_succ {n : ℕ} {v v' : HVM} (ρ : String → Bool) (h : stepMatch v = some v') :
    orientAt (n + 1) v ρ = orientAt n v' (orientStep v ρ) := by
  rw [orientAt, h]

theorem iterStep_succ_of {n : ℕ} {v v' : HVM} (h : stepMatch v = some v') :
    iterStep (n + 1) v = iterStep n v' := by
  rw [iterStep, h, Option.bind_some]

theorem orientStep_pending {v : HVM} {c : Config} {e : Event} (h : v.ctl = .pending c e)
    (ρ : String → Bool) : orientStep v ρ = moveRev e ρ := by
  rw [orientStep, h]

/-! ## The side conditions, on one head-VM state -/

/-- What the matcher program keeps at the head-VM state `u`, with orientations `ρ` and pattern
boundary `W` (the logical form of `ScaHeadVM.MatchSide`, plus the worker's `match` timing). -/
structure StepSide (W : ℕ) (ρ : String → Bool) (u : HVM) : Prop where
  /-- A `symbols` reads both heads on their side. -/
  reads : ∀ c a b, u.ctl = .pending c (.symbols a b) →
    OnSide W (ρ a) (u.pos a) ∧ OnSide W (ρ b) (u.pos b)
  /-- `available` tests a forward head. -/
  available : ∀ c h, u.ctl = .pending c (.available h) → ρ h = false
  /-- A moved reversed reader stays inside the pattern. -/
  moves : ∀ c ms, u.ctl = .pending c (.move ms) → ∀ h, (color spec h).isSome → ρ h = true →
    sumDelta ms h ≠ 0 → u.pos h + sumDelta ms h ≤ W
  /-- At `match`, `B` is forward and has reached the arrival frontier. -/
  matchB : ∀ c h, u.ctl = .pending c (.«match» h) → ρ "B" = false ∧ u.len ≤ u.pos "B"

/-! ## The link between the real matcher and the head VM -/

/-- The real matcher state `s` encodes the head VM `v`, with pattern boundary `W` and the
orientations `ρ` of the live readers. -/
structure Link (W : ℕ) (ρ : String → Bool) (s : WorkerState) (v : HVM) : Prop where
  sim : SimCtl vs v.ctl s.pc
  heads : MatchRel spec (readersAt s.pc) W ⟨s, v.ctl⟩ v
  orient : RevAgree spec (readersAt s.pc) s ρ
  inv : ScaWorkerRegs.Inv spec ⟨v.pos, 0⟩ s
  endText : s.end = s.text.length

/-- `MatchRel` only reads the body's registers and text: it moves to any body that agrees with
the coroutine state's up to `pc`. -/
theorem matchRel_transfer {L : List String} {W : ℕ} {t : CoState} {v : HVM} {b : WorkerState}
    (h : MatchRel spec L W t v) (hb : b = { t.body with pc := b.pc }) :
    MatchRel spec L W ⟨b, v.ctl⟩ v := by
  have hd : b.data = t.body.data := by have h := congrArg WorkerState.data hb; exact h
  have hr : b.reverse = t.body.reverse := by have h := congrArg WorkerState.reverse hb; exact h
  have hx : b.text = t.body.text := by have h := congrArg WorkerState.text hb; exact h
  refine ⟨rfl, ?_, ?_, ?_, ?_, h.patternSize, ?_⟩
  · change b.data.length = _
    rw [hd]; exact h.dataLen
  · change b.reverse.length = _
    rw [hr]; exact h.revLen
  · change W ≤ b.text.length
    rw [hx]; exact h.frontier
  · change v.word = matchWord b.text W
    rw [hx]; exact h.word
  · intro x hxL i hc
    change (b.data.getD i 0 : ℤ) = (⟨0, W⟩ : Emb).phys (b.reverse.getD i false) (v.pos x)
    rw [hd, hr]
    exact h.heads x hxL i hc

theorem revAgree_transfer {L : List String} {s b : WorkerState} {ρ : String → Bool}
    (h : RevAgree spec L s ρ) (hr : b.reverse = s.reverse) : RevAgree spec L b ρ := by
  intro x hx i hc
  rw [hr]
  exact h x hx i hc

theorem revAgree_mono {L L' : List String} {s : WorkerState} {ρ : String → Bool}
    (h : RevAgree spec L s ρ) (hsub : ∀ x ∈ L', x ∈ L) : RevAgree spec L' s ρ :=
  fun x hx i hc => h x (hsub x hx) i hc

/-- The logical side conditions give `ScaHeadVM.MatchSide` at the current row. -/
theorem matchSide_of {W : ℕ} {ρ : String → Bool} {s : WorkerState} {v : HVM} {c : Config}
    {e : Event} {row : Row} (hR : ReaderFacts) (hlink : Link W ρ s v)
    (hctl : v.ctl = .pending c e) (hrow : spec.program.code[s.pc]? = some row)
    (hevent : row.event = e) (hcov : Covers e (readersAt s.pc) (afterR row))
    (hside : StepSide W ρ v) :
    MatchSide spec W (readersAt s.pc) (afterR row) s v.pos e where
  reads := by
    intro a b he h hh i hc
    subst he
    obtain ⟨haL, hbL⟩ := hcov.reads a b rfl
    obtain ⟨ha, hb⟩ := hside.reads c a b hctl
    rcases hh with rfl | rfl
    · rw [hlink.orient _ haL i hc]; exact ha
    · rw [hlink.orient _ hbL i hc]; exact hb
  available := by
    intro h he i hc
    subst he
    rw [hlink.orient h (hcov.avail h rfl) i hc]
    exact hside.available c h hctl
  moves := by
    intro ms he h hA i hc hrev
    subst he
    have hL : h ∈ readersAt s.pc := hcov.keep h hA (fun t' s' he => by cases he)
    have hρ : ρ h = true := by rw [← hlink.orient h hL i hc]; exact hrev
    by_cases hne : sumDelta ms h = 0
    · have hp := hlink.heads.heads h hL i hc
      change (s.data.getD i 0 : ℤ) = (⟨0, W⟩ : Emb).phys (s.reverse.getD i false) (v.pos h) at hp
      rw [hrev] at hp
      simp only [Emb.phys, if_true] at hp
      rw [hne]
      omega
    · exact hside.moves c ms hctl h (by rw [hc]; rfl) hρ hne
  matchB := by
    intro h he
    subst he
    have hBL := hR.matchB s.pc row hrow h hevent
    refine ⟨hBL, 2, color_B, ?_⟩
    rw [hlink.orient "B" hBL 2 color_B]
    exact (hside.matchB c h hctl).1

/-- The moves fit (`ScaHeadVM.MoveFits`), as in the proof of `ScaHeadVM.match_step`. -/
theorem moveFits_of {W : ℕ} {L A : List String} {s : WorkerState} {v : HVM} {e : Event}
    (hrel : MatchRel spec L W ⟨s, v.ctl⟩ v) (hok : matchOk v e)
    (hside : MatchSide spec W L A s v.pos e) :
    MoveFits spec ⟨0, W⟩ A s v.pos e := by
  intro ms hms h hA i hc hne
  subst hms
  obtain ⟨π', hπ'⟩ := Option.isSome_iff_exists.mp hok
  obtain ⟨hform, hrange⟩ := moveSeq_some hπ'
  obtain ⟨m, hm, hmh⟩ := exists_of_sumDelta_ne hne
  have hin := hrange m hm (hmh ▸ notBlind h i hc)
  have hlen : v.len = s.text.length := hrel.len_eq
  rw [hmh, hform, hlen] at hin
  simp only at hin
  have hfr : W ≤ s.text.length := hrel.frontier
  unfold Emb.phys
  cases hr : s.reverse.getD i false
  · simp only [Bool.false_eq_true, if_false, zero_add]; exact hin
  · have hle := hside.moves ms rfl h hA i hc hr
    simp only [if_true]
    constructor <;> omega

/-! ## One active step -/

theorem effect_mode (f : Fields) (s : WorkerState) : (effect spec f true s).mode = s.mode := by
  rw [effect_eq', (finish_matcher spec isFlags_eq f true _).2.2]
  exact (preFinish_proj spec f s).2.2.2

theorem matchLate_eq_false {W : ℕ} {ρ : String → Bool} {v : HVM} {c : Config} {e : Event}
    (hctl : v.ctl = .pending c e) (hside : StepSide W ρ v) : matchLate v e = false := by
  cases e with
  | «match» h =>
    have hB := (hside.matchB c h hctl).2
    simp only [matchLate, decide_eq_false_iff_not, not_lt]
    exact hB
  | _ => rfl

/-- A pending row has a successor. -/
theorem targets_ne_nil {c : Config} {e : Event} {r : ℕ} {row : Row} (hsim : Sim vs c e r)
    (hrow : spec.program.code[r]? = some row) : row.targets ≠ [] := by
  obtain ⟨row', hrow', -, hlen, -⟩ := sim_step certified.certOk hsim
  rw [hrow] at hrow'
  cases hrow'
  intro hnil
  rw [hnil] at hlen
  unfold responsesFor at hlen
  split at hlen <;> simp at hlen

theorem readersAt_sub_afterR {row : Row} {t : ℕ} (ht : t ∈ row.targets) :
    ∀ x ∈ readersAt t, x ∈ afterR row := by
  unfold readersAt afterR
  exact live_sub_successorsUnion (liveReaders spec) ht

/-- The fields of a state that agrees with `x` up to `pc`. -/
theorem agree_proj {b x : WorkerState} (h : b = { x with pc := b.pc }) :
    b.data = x.data ∧ b.reverse = x.reverse ∧ b.text = x.text ∧ b.fault = x.fault ∧
      b.output = x.output ∧ b.mode = x.mode ∧ b.«end» = x.«end» := by
  have h1 := congrArg WorkerState.data h
  have h2 := congrArg WorkerState.reverse h
  have h3 := congrArg WorkerState.text h
  have h4 := congrArg WorkerState.fault h
  have h5 := congrArg WorkerState.output h
  have h6 := congrArg WorkerState.mode h
  have h7 := congrArg WorkerState.«end» h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem step_true_pc (w : Worker) (s : WorkerState) :
    (step w true s).pc =
      if decision (w.fields s.pc) s then (w.fields s.pc).yes else (w.fields s.pc).no :=
  rfl

/-- **One active step of the real matcher is one `stepMatch` step.** Under `Link`, at a
pending head-VM control whose side conditions hold, if `StreamingMatcher.step` succeeds, the
active table step keeps `Link` (the orientations follow the executed copy), raises no fault,
raises `output` exactly on `match`, and keeps `mode`. -/
theorem link_step (hR : ReaderFacts) {W : ℕ} {ρ : String → Bool} {s : WorkerState}
    {v v' : HVM} {c : Config} {e : Event} (hlink : Link W ρ s v)
    (hctl : v.ctl = .pending c e) (hside : StepSide W ρ v) (hstep : stepMatch v = some v') :
    Link W (moveRev e ρ) (step (Worker.ofSpec spec) true s) v' ∧
      (step (Worker.ofSpec spec) true s).fault = s.fault ∧
      (step (Worker.ofSpec spec) true s).output = (s.output || isOp e "match") ∧
      (step (Worker.ofSpec spec) true s).mode = s.mode := by
  have hsim : Sim vs c e s.pc := by
    have h := hlink.sim
    rw [hctl] at h
    exact h
  obtain ⟨row, hrow, hevent, -, -⟩ := sim_step certified.certOk hsim
  have hfields : (Worker.ofSpec spec).fields s.pc =
      fieldsAt spec (liveReaders spec) (liveDistances spec) s.pc row := fields_ofSpec spec hrow
  have hrelT : Rel vs s ⟨s, v.ctl⟩ := ⟨rfl, hlink.sim⟩
  have hrom : cw.rom v.ctl = (Worker.ofSpec spec).fields s.pc := certified.rom_eq hlink.sim
  have hdec : Decodes spec (afterR row) e (cw.rom v.ctl) := by
    rw [hrom, hfields, ← hevent]
    exact decodes_fieldsAt _ _ _ _ _
  have hcov : Covers e (readersAt s.pc) (afterR row) := by
    rw [← hevent]
    exact covers_of_transfer (hR.fix s.pc row hrow)
  have hregs : RegsValue (cw.rom v.ctl) s v.pos e := by
    rw [hrom, ← hevent]
    exact regsValue_of_regInv hlink.inv.regs hrow
  have hcolored := hR.colored s.pc
  have hproper := hR.proper s.pc row hrow
  have hms : MatchSide spec W (readersAt s.pc) (afterR row) s v.pos e :=
    matchSide_of hR hlink hctl hrow hevent hcov hside
  obtain ⟨hok, hv'⟩ := stepMatch_some hctl hstep
  obtain ⟨hmrel, hfault, hout⟩ := match_step (t := ⟨s, v.ctl⟩) certified.specEq isFlags_eq rfl
    hlink.heads hctl hdec hcov hproper hcolored colorsBound notBlind hregs hms hstep
  -- the table step, and the coroutine step it simulates
  have hrel1 := rel_step certified hrelT true
  have hag := hrel1.agree
  have hbody1 : (cw.step true ⟨s, v.ctl⟩).body = effect spec (cw.rom v.ctl) true s :=
    CoWorker.step_body cw true ⟨s, v.ctl⟩
  have hpc1 := step_true_pc (Worker.ofSpec spec) s
  have hmem : (step (Worker.ofSpec spec) true s).pc ∈ row.targets := by
    rw [hpc1]
    exact next_mem_targets hrow (targets_ne_nil hsim hrow) _
  have hsub : ∀ x ∈ readersAt (step (Worker.ofSpec spec) true s).pc, x ∈ afterR row :=
    readersAt_sub_afterR hmem
  -- the reverse bits after the step
  have hfit : MoveFits spec ⟨0, W⟩ (afterR row) s v.pos e := moveFits_of hlink.heads hok hms
  obtain ⟨-, -, -, -, -, hrevAfter⟩ := posAgree_after hdec hcov hproper hcolored colorsBound
    hlink.heads.dataLen hlink.heads.revLen hlink.heads.heads hfit
  obtain ⟨-, hrev1, htext1, hfault1, hout1, hmode1, hend1⟩ := agree_proj hag
  rw [hbody1] at hrev1 htext1 hfault1 hout1 hmode1 hend1 hfault hout
  -- the registers after the step
  have hinv1 := ScaWorkerRegs.step_inv ScaWorkerRegs.matcher_tableFacts hlink.inv true
  have hghost : ScaWorkerRegs.ghostStep spec true s ⟨v.pos, 0⟩ = ⟨v'.pos, 0⟩ := by
    have hnd := moves_nodup hrow
    rw [hevent] at hnd
    have hpos' : v'.pos = movePos e v.pos := by rw [hv']
    show (⟨ScaWorkerRegs.headStep ((Worker.ofSpec spec).fields s.pc).event v.pos, 0⟩ :
      ScaWorkerRegs.Ghost) = _
    rw [hfields, ScaWorkerCoroutine.fieldsAt_event, hevent, headStep_eq_movePos hnd, hpos']
  rw [hghost] at hinv1
  have hcounters := (ScaWorkerRegs.effect_counters spec (cw.rom v.ctl) true s).1
  have hend2 : (effect spec (cw.rom v.ctl) true s).«end» = s.«end» := by
    have h := congrArg (fun x : ℕ × ℕ × ℤ × ℤ => x.2.1) hcounters
    exact h
  have htext2 := (effect_data spec (cw.rom v.ctl) s).1
  refine ⟨⟨?_, ?_, ?_, hinv1, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hmrel.ctl]
    exact hrel1.sim
  · exact matchRel_transfer (hmrel.mono hsub) hag
  · exact revAgree_mono (revAgree_transfer (hrevAfter ρ hlink.orient) hrev1) hsub
  · rw [hend1, htext1, hend2, htext2]
    exact hlink.endText
  · rw [hfault1, hfault, matchLate_eq_false hctl hside, Bool.or_false]
  · rw [hout1, hout]
  · rw [hmode1, effect_mode]

/-! ## `service`: `quantum` steps -/

/-- One step of `service`: active iff `mode = run` (`ScaWindowWorker.service`). -/
def mstep (s : WorkerState) : WorkerState :=
  step (Worker.ofSpec spec) (decide (s.mode = .run)) s

theorem foldl_range_const {α : Type} (g : α → α) (n : ℕ) (a : α) :
    (List.range n).foldl (fun x _ => g x) a = g^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Function.iterate_succ_apply']

/-- `service` is `quantum` iterations of `mstep`. -/
theorem service_eq (s : WorkerState) :
    service ScaWindowInstance.matcher s = mstep^[spec.quantum] s := by
  rw [matcher_eq]
  unfold service
  rw [ScaWorkerCoroutine.ofSpec_spec]
  exact foldl_range_const mstep _ s

theorem mstep_run {s : WorkerState} (hrun : s.mode = .run) :
    mstep s = step (Worker.ofSpec spec) true s := by
  unfold mstep
  rw [hrun]
  rfl

theorem isOp_match_length (v : HVM) (e : Event) :
    (matchOut v e).length = if isOp e "match" = true then 1 else 0 := by
  cases e <;> rfl

/-- **`n` steps** of the running worker are `n` head-VM steps, while the side conditions hold
along the head-VM run. -/
theorem link_run (hR : ReaderFacts) (n : ℕ) :
    ∀ {W : ℕ} {ρ : String → Bool} {s : WorkerState} {v v' : HVM},
      Link W ρ s v → s.mode = .run → iterStep n v = some v' →
      (∀ i, i < n → ∀ u, iterStep i v = some u → StepSide W (orientAt i v ρ) u) →
      Link W (orientAt n v ρ) (mstep^[n] s) v' ∧ (mstep^[n] s).fault = s.fault ∧
        (mstep^[n] s).mode = .run ∧
        (mstep^[n] s).output = (s.output || decide (v.outputs.length < v'.outputs.length)) ∧
        v.outputs <+: v'.outputs := by
  induction n with
  | zero =>
    intro W ρ s v v' hlink hrun hvm hside
    have hv : v' = v := by
      simp only [iterStep, Option.some.injEq] at hvm
      exact hvm.symm
    subst hv
    refine ⟨hlink, rfl, hrun, ?_, List.prefix_refl _⟩
    simp
  | succ n ih =>
    intro W ρ s v v' hlink hrun hvm hside
    cases hstep : stepMatch v with
    | none =>
      rw [iterStep, hstep] at hvm
      cases hvm
    | some v1 =>
      rw [iterStep_succ_of hstep] at hvm
      obtain ⟨c, e, hctl, -⟩ := ScaHeadRun.stepMatch_ctl hstep
      have hside0 : StepSide W ρ v := hside 0 (Nat.succ_pos n) v rfl
      obtain ⟨hlink1, hfault1, hout1, hmode1⟩ := link_step hR hlink hctl hside0 hstep
      rw [← mstep_run hrun] at hlink1 hfault1 hout1 hmode1
      have hrun1 : (mstep s).mode = .run := by rw [hmode1, hrun]
      have hside1 : ∀ i, i < n → ∀ u, iterStep i v1 = some u →
          StepSide W (orientAt i v1 (moveRev e ρ)) u := by
        intro i hi u hu
        have h := hside (i + 1) (by omega) u (by rw [iterStep_succ_of hstep]; exact hu)
        rw [orientAt_succ ρ hstep, orientStep_pending hctl] at h
        exact h
      obtain ⟨hlinkN, hfaultN, hmodeN, houtN, hprefN⟩ := ih hlink1 hrun1 hvm hside1
      obtain ⟨-, hv1⟩ := stepMatch_some hctl hstep
      have hv1o : v1.outputs = v.outputs ++ matchOut v e := by rw [hv1]
      have hlen1 : v1.outputs.length =
          v.outputs.length + (if isOp e "match" = true then 1 else 0) := by
        rw [hv1o, List.length_append, isOp_match_length]
      have hle : v1.outputs.length ≤ v'.outputs.length := hprefN.length_le
      rw [Function.iterate_succ_apply, orientAt_succ ρ hstep, orientStep_pending hctl]
      refine ⟨hlinkN, hfaultN.trans hfault1, hmodeN, ?_,
        (List.prefix_append v.outputs (matchOut v e)).trans (hv1o ▸ hprefN)⟩
      rw [houtN, hout1]
      cases hm : isOp e "match"
      · rw [hm] at hlen1
        simp only [Bool.false_eq_true, if_false, add_zero] at hlen1
        rw [hlen1, Bool.or_false]
      · rw [hm] at hlen1
        simp only [if_true] at hlen1
        have hlt : v.outputs.length < v'.outputs.length := by omega
        simp [hlt]

/-- **`service` is `quantum` head-VM steps.** A running real matcher linked to `v`, whose
head VM runs `quantum` steps to `v'` with the side conditions at every state on the way, ends
`service` linked to `v'` (with the orientations moved along); its fault bit and `mode` are
kept; its `output` is raised iff `match` fired on the way (`outputs` grew). -/
theorem service_link (hR : ReaderFacts) {W : ℕ} {ρ : String → Bool} {s : WorkerState}
    {v v' : HVM} (hlink : Link W ρ s v) (hrun : s.mode = .run)
    (hvm : iterStep spec.quantum v = some v')
    (hside : ∀ i, i < spec.quantum → ∀ u, iterStep i v = some u → StepSide W (orientAt i v ρ) u) :
    Link W (orientAt spec.quantum v ρ) (service ScaWindowInstance.matcher s) v' ∧
      (service ScaWindowInstance.matcher s).fault = s.fault ∧
      (service ScaWindowInstance.matcher s).mode = .run ∧
      (service ScaWindowInstance.matcher s).output =
        (s.output || decide (v.outputs.length < v'.outputs.length)) ∧
      v.outputs <+: v'.outputs := by
  rw [service_eq]
  exact link_run hR spec.quantum hlink hrun hvm hside

/-! ## Composing side conditions along a run -/

/-- The side conditions along the first `n` head-VM steps from `v` (the hypothesis `hside` of
`service_link` is `SideRun W ρ spec.quantum v`). -/
def SideRun (W : ℕ) (ρ : String → Bool) (n : ℕ) (v : HVM) : Prop :=
  ∀ i, i < n → ∀ u, iterStep i v = some u → StepSide W (orientAt i v ρ) u

theorem orientAt_add (m n : ℕ) :
    ∀ {v w : HVM} (ρ : String → Bool), iterStep m v = some w →
      orientAt (m + n) v ρ = orientAt n w (orientAt m v ρ) := by
  induction m with
  | zero =>
    intro v w ρ h
    simp only [iterStep, Option.some.injEq] at h
    subst h
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    intro v w ρ h
    cases hstep : stepMatch v with
    | none =>
      rw [iterStep, hstep] at h
      cases h
    | some v1 =>
      rw [iterStep_succ_of hstep] at h
      rw [show m + 1 + n = (m + n) + 1 by omega, orientAt_succ ρ hstep, orientAt_succ ρ hstep]
      exact ih _ h

/-- Side conditions compose along consecutive runs. -/
theorem sideRun_add {W : ℕ} {ρ : String → Bool} {m n : ℕ} {v w : HVM}
    (h1 : SideRun W ρ m v) (hw : iterStep m v = some w)
    (h2 : SideRun W (orientAt m v ρ) n w) : SideRun W ρ (m + n) v := by
  intro i hi u hu
  by_cases him : i < m
  · exact h1 i him u hu
  · obtain ⟨k, rfl⟩ : ∃ k, i = m + k := ⟨i - m, by omega⟩
    rw [iterStep_add, hw, Option.bind_some] at hu
    rw [orientAt_add m k _ hw]
    exact h2 k (by omega) u hu

/-! ## `service` when the coroutine has returned, and when the worker is idle -/

theorem step_true_proj (w : Worker) (s : WorkerState) :
    (step w true s).mode = (effect w.spec (w.fields s.pc) true s).mode ∧
      (step w true s).fault = (effect w.spec (w.fields s.pc) true s).fault :=
  ⟨rfl, rfl⟩

/-- An active step keeps `mode` and never clears the fault bit. -/
theorem step_true_mode_fault (s : WorkerState) :
    (step (Worker.ofSpec spec) true s).mode = s.mode ∧
      (s.fault = true → (step (Worker.ofSpec spec) true s).fault = true) := by
  obtain ⟨hm, hf⟩ := step_true_proj (Worker.ofSpec spec) s
  rw [ScaWorkerCoroutine.ofSpec_spec] at hm hf
  refine ⟨hm.trans (effect_mode _ s), fun hfs => ?_⟩
  rw [hf, (effect_fault_matcher spec isFlags_eq _ s).1,
    (checks_fault_matcher spec isFlags_eq _ true s).1, hfs]
  rfl

theorem iterate_run_fault (n : ℕ) :
    ∀ {s : WorkerState}, s.mode = .run → s.fault = true →
      (mstep^[n] s).mode = .run ∧ (mstep^[n] s).fault = true := by
  induction n with
  | zero => intro s hrun hf; exact ⟨hrun, hf⟩
  | succ n ih =>
    intro s hrun hf
    rw [Function.iterate_succ_apply]
    obtain ⟨hm, hf'⟩ := step_true_mode_fault s
    rw [← mstep_run hrun] at hm hf'
    exact ih (hm.trans hrun) (hf' hf)

/-- **A returned coroutine faults.** The head-program coroutine never returns in a correct run:
if it has, the table sits in its `halt` sink row, and the first active step faults (the matcher
has no `done` mode). -/
theorem service_returned {W : ℕ} {ρ : String → Bool} {s : WorkerState} {v : HVM}
    {val : Value} (hlink : Link W ρ s v) (hrun : s.mode = .run) (hret : v.ctl = .returned val) :
    (service ScaWindowInstance.matcher s).fault = true ∧
      (service ScaWindowInstance.matcher s).mode = .run := by
  have hpc : s.pc = 0 := by
    have h := hlink.sim
    rw [hret] at h
    exact h
  obtain ⟨-, -, hsinkFault⟩ := step_sink matcherWorker_sinkRow s hpc
  have hf1 : (mstep s).fault = true := by rw [mstep_run hrun]; exact hsinkFault isFlags_eq
  have hm1 : (mstep s).mode = .run := by
    rw [mstep_run hrun, (step_true_mode_fault s).1, hrun]
  rw [service_eq, quantum_eq, Function.iterate_succ_apply]
  obtain ⟨hmN, hfN⟩ := iterate_run_fault 2047 hm1 hf1
  exact ⟨hfN, hmN⟩

theorem moveReg_false (f : Fields) (sp : Option ℕ) (sr : Option Bool) (s : WorkerState)
    (i : ℕ) : moveReg f false sp sr s i = s := by
  unfold moveReg
  simp only [Bool.false_and, Bool.or_false, Bool.false_eq_true, if_false]

theorem foldl_moveReg_false (f : Fields) (sp : Option ℕ) (sr : Option Bool) :
    ∀ (l : List ℕ) (s : WorkerState), l.foldl (moveReg f false sp sr) s = s
  | [], _ => rfl
  | i :: l, s => by
    rw [List.foldl_cons, moveReg_false]
    exact foldl_moveReg_false f sp sr l s

/-- An inactive step does nothing. -/
theorem effect_false (f : Fields) (s : WorkerState) : effect spec f false s = s := by
  unfold effect moves
  rw [foldl_moveReg_false]
  unfold finish execute checks
  simp only [isFlags_eq, Bool.false_eq_true, if_false, Bool.false_and, Bool.or_false]

theorem step_false (w : Worker) (s : WorkerState) :
    step w false s = effect w.spec (w.fields s.pc) false s := rfl

/-- **An idle worker's `service` does nothing.** -/
theorem service_idle {s : WorkerState} (hidle : s.mode ≠ .run) :
    service ScaWindowInstance.matcher s = s := by
  have hfix : mstep s = s := by
    unfold mstep
    rw [decide_eq_false hidle, step_false, ScaWorkerCoroutine.ofSpec_spec, effect_false]
  rw [service_eq]
  exact Function.iterate_fixed hfix _

/-! ## Registers under a change of the ghost positions -/

theorem regInv_congr {pos pos' : String → ℤ} {s : WorkerState}
    (h : ScaWorkerRegs.RegInv spec pos s)
    (hp : ∀ p ∈ ScaWorkerRegs.liveAt spec s.pc, pos' p.1 - pos' p.2 = pos p.1 - pos p.2) :
    ScaWorkerRegs.RegInv spec pos' s := by
  refine ⟨h.regsLength, h.pcInRange, fun p hpl => ?_⟩
  obtain ⟨i, hi, hv⟩ := h.live p hpl
  exact ⟨i, hi, hv.trans (hp p hpl).symm⟩

/-- Moving `OriginalEnd` changes no tracked difference: no distance register involves it. -/
theorem regInv_originalEnd {pos : String → ℤ} {s : WorkerState}
    (h : ScaWorkerRegs.RegInv spec pos s) (x : ℤ) :
    ScaWorkerRegs.RegInv spec (Function.update pos "OriginalEnd" x) s := by
  refine regInv_congr h fun p hpl => ?_
  obtain ⟨i, hi, -⟩ := h.live p hpl
  obtain ⟨h1, h2⟩ := distColor_originalEnd hi
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

/-! ## `arrive` -/

/-- The fields of `arrive` on a matcher-like worker. -/
theorem arrive_fields (w : Worker) (hw : w.spec.isFlags = false) (a : Fin 2) (s : WorkerState) :
    (arrive w a s).pc = s.pc ∧ (arrive w a s).mode = s.mode ∧ (arrive w a s).output = false ∧
      (arrive w a s).data = s.data ∧ (arrive w a s).reverse = s.reverse ∧
      (arrive w a s).text = s.text ++ [a] ∧ (arrive w a s).«end» = s.«end» + 1 ∧
      (s.«end» = s.text.length → (arrive w a s).fault = s.fault) := by
  unfold arrive
  rw [hw]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun hend => ?_⟩
  simp only [Bool.false_eq_true, if_false, WorkerState.canMoveTo, List.length_append,
    List.length_singleton, hend]
  have h0 : (0 : ℤ) ≤ (s.text.length : ℤ) + 1 := by omega
  simp [h0]

/-- **`arrive` is `HVM.append`.** A letter arriving at the linked real matcher is
`StreamingMatcher.append` of the same letter; `output` restarts, nothing faults, `mode` and the
orientations are kept. -/
theorem arrive_link (hR : ReaderFacts) {W : ℕ} {ρ : String → Bool} {s : WorkerState} {v : HVM}
    (hlink : Link W ρ s v) (a : Fin 2) :
    Link W ρ (arrive ScaWindowInstance.matcher a s) (v.append a) ∧
      (arrive ScaWindowInstance.matcher a s).fault = s.fault ∧
      (arrive ScaWindowInstance.matcher a s).output = false ∧
      (arrive ScaWindowInstance.matcher a s).mode = s.mode := by
  rw [matcher_eq]
  obtain ⟨hpc, hmode, hout, -, hrev, htext, hend, hfault⟩ :=
    arrive_fields (Worker.ofSpec spec) isFlags_eq a s
  have hOE : "OriginalEnd" ∉ readersAt s.pc := by
    intro hmem
    obtain ⟨i, hi⟩ := hR.colored s.pc "OriginalEnd" hmem
    rw [color_originalEnd] at hi
    cases hi
  have hrelA := rel_arrive certified (⟨rfl, hlink.sim⟩ : Rel vs s ⟨s, v.ctl⟩) a
  obtain ⟨hmrel, -⟩ := match_arrive (cw := cw) hlink.heads hOE a
  have hinvA := ScaWorkerRegs.arrive_inv hlink.inv a
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hfault hlink.endText, hout, hmode⟩
  · rw [hpc]
    exact hlink.sim
  · rw [hpc]
    exact matchRel_transfer hmrel hrelA.agree
  · rw [hpc]
    exact revAgree_transfer hlink.orient hrev
  · exact ⟨regInv_originalEnd hinvA.regs _, hinvA.keys⟩
  · rw [hend, htext, List.length_append, List.length_singleton, hlink.endText]

/-! ## `start` -/

/-- The orientations `start` sets up: `Origin` reversed, every other head forward. -/
def startOrient : String → Bool := fun h => decide (h = "Origin")

/-- The coroutine control `start` restarts. -/
def startCtl : Ctl := Ctl.ofOutcome (next matcherInitial none)

/-- The real matcher's state, before any head-VM correspondence: the register invariant for
some ghost, the arrival frontier, the register-file sizes. Every reachable matcher state has it
(`ready_initial`, `ready_arrive`, `ready_of_link`, `tick_idle`). -/
structure Ready (s : WorkerState) : Prop where
  inv : ∃ pos, ScaWorkerRegs.Inv spec ⟨pos, 0⟩ s
  endText : s.«end» = s.text.length
  dataLen : s.data.length = spec.readers.registers
  revLen : s.reverse.length = spec.readers.registers

theorem ready_of_link {W : ℕ} {ρ : String → Bool} {s : WorkerState} {v : HVM}
    (hlink : Link W ρ s v) : Ready s :=
  ⟨⟨v.pos, hlink.inv⟩, hlink.endText, hlink.heads.dataLen, hlink.heads.revLen⟩

theorem ready_initial : Ready ScaWindowInstance.matcherInit := by
  refine ⟨⟨fun _ => 0, ScaWorkerRegs.initial_inv ScaWorkerRegs.matcher_tableFacts⟩, rfl, ?_, ?_⟩
  · simp [ScaWindowInstance.matcherInit, WorkerState.initial]
  · simp [ScaWindowInstance.matcherInit, WorkerState.initial]

theorem ready_arrive {s : WorkerState} (hready : Ready s) (a : Fin 2) :
    Ready (arrive ScaWindowInstance.matcher a s) ∧
      (arrive ScaWindowInstance.matcher a s).fault = s.fault ∧
      (arrive ScaWindowInstance.matcher a s).output = false ∧
      (arrive ScaWindowInstance.matcher a s).mode = s.mode ∧
      (arrive ScaWindowInstance.matcher a s).text = s.text ++ [a] := by
  rw [matcher_eq]
  obtain ⟨-, hmode, hout, hdata, hrev, htext, hend, hfault⟩ :=
    arrive_fields (Worker.ofSpec spec) isFlags_eq a s
  obtain ⟨pos, hinv⟩ := hready.inv
  refine ⟨⟨⟨pos, ScaWorkerRegs.arrive_inv hinv a⟩, ?_, ?_, ?_⟩, hfault hready.endText, hout, hmode,
    htext⟩
  · rw [hend, htext, List.length_append, List.length_singleton, hready.endText]
  · rw [hdata]; exact hready.dataLen
  · rw [hrev]; exact hready.revLen

theorem startBody_congr (w w' : Worker) (h : w.spec = w'.spec) (enabled : Bool)
    (s : WorkerState) : startBody w enabled s = startBody w' enabled s := by
  unfold startBody rawStart
  rw [h]

theorem start_true_eq (w : Worker) (s : WorkerState) :
    start w true s = { startBody w true s with pc := w.spec.program.start, mode := .run } :=
  rfl

theorem startBody_matcher (s : WorkerState) :
    startBody (specWorker spec) true s =
      initializeValues spec matcherStartMapping true
        (rawStart (specWorker spec) "Tail" s.«end» false true
          (rawStart (specWorker spec) "Origin" s.«end» true true s)) := by
  unfold startBody
  have hf : (specWorker spec).spec.isFlags = false := isFlags_eq
  simp only [hf, Bool.false_eq_true, if_false]
  rfl

/-- `initializeValues` writes only the distance registers. -/
theorem initFold_regs : ∀ (M : List (Pair × Option (DistKey × Int))) (s : WorkerState),
    ∃ r, M.foldl (ScaWorkerRegs.initStep spec) s = { s with regs := r }
  | [], s => ⟨s.regs, rfl⟩
  | e :: M, s => by
    obtain ⟨r1, h1⟩ : ∃ r, ScaWorkerRegs.initStep spec s e = { s with regs := r } := by
      unfold ScaWorkerRegs.initStep
      split
      · exact ⟨s.regs, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    obtain ⟨r2, h2⟩ := initFold_regs M { s with regs := r1 }
    exact ⟨r2, by rw [List.foldl_cons, h1, h2]⟩

/-- The fields of an enabled `start` of the real matcher. -/
theorem start_fields (s : WorkerState) :
    (start (Worker.ofSpec spec) true s).pc = spec.program.start ∧
      (start (Worker.ofSpec spec) true s).mode = .run ∧
      (start (Worker.ofSpec spec) true s).fault = s.fault ∧
      (start (Worker.ofSpec spec) true s).output = s.output ∧
      (start (Worker.ofSpec spec) true s).text = s.text ∧
      (start (Worker.ofSpec spec) true s).«end» = s.«end» ∧
      (start (Worker.ofSpec spec) true s).data = (s.data.set 1 s.«end»).set 4 s.«end» ∧
      (start (Worker.ofSpec spec) true s).reverse = (s.reverse.set 1 true).set 4 false := by
  have h1 := start_true_eq (Worker.ofSpec spec) s
  rw [startBody_congr (Worker.ofSpec spec) (specWorker spec) rfl, startBody_matcher,
    rawStart_some color_origin, rawStart_some color_tail,
    ScaWorkerRegs.initializeValues_true] at h1
  obtain ⟨r, hr⟩ := initFold_regs matcherStartMapping
    { { s with data := s.data.set 1 s.«end», reverse := s.reverse.set 1 true } with
      data := (s.data.set 1 s.«end»).set 4 s.«end»
      reverse := (s.reverse.set 1 true).set 4 false }
  rw [hr] at h1
  rw [h1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`start` is `StreamingMatcher(pattern)`.** An enabled `start` of a real matcher that has
read `text` links it to the fresh head VM on the pattern `x = text.reverse` (all of `text` is the
pattern: `start` is called when `end` is the frontier), with boundary `W = |text|` and
orientations `startOrient`; it faults on nothing and leaves `output`; `mode := run`. -/
theorem start_link (hR : ReaderFacts) {s : WorkerState} (hready : Ready s) :
    Link s.text.length startOrient (start ScaWindowInstance.matcher true s)
        (matchInitial s.text.reverse startCtl) ∧
      (start ScaWindowInstance.matcher true s).fault = s.fault ∧
      (start ScaWindowInstance.matcher true s).output = s.output ∧
      (start ScaWindowInstance.matcher true s).mode = .run := by
  rw [matcher_eq]
  obtain ⟨hpc, hmode, hfault, hout, htext, hend, -, hrev⟩ := start_fields s
  -- the heads, from `ScaHeadVM.match_start` on the coroutine worker
  have hms := match_start (cw := cw) (t := ⟨s, startCtl⟩) (L := readersAt spec.program.start)
    certified.specEq isFlags_eq hready.dataLen hready.revLen hready.endText color_origin
    color_tail (by decide) (by decide) (by decide) hR.startLive
  have hagree : start (Worker.ofSpec spec) true s =
      { (cw.start true ⟨s, startCtl⟩).body with pc := (start (Worker.ofSpec spec) true s).pc } := by
    have hb : (cw.start true ⟨s, startCtl⟩).body =
        { startBody (specWorker spec) true s with mode := .run } := rfl
    rw [hb, start_true_eq, startBody_congr (Worker.ofSpec spec) (specWorker spec) rfl]
  have hmsT := matchRel_transfer hms hagree
  have hctl0 : (cw.start true ⟨s, startCtl⟩).ctl = startCtl := rfl
  rw [hctl0, hready.endText, List.take_length] at hmsT
  -- the registers
  obtain ⟨pos, hinv⟩ := hready.inv
  have hinvS := ScaWorkerRegs.start_inv ScaWorkerRegs.matcher_tableFacts hinv true
  have hghost : ScaWorkerRegs.ghostStart spec true s ⟨pos, 0⟩ =
      ⟨ScaWorkerRegs.startPos spec s.length s.h, 0⟩ := rfl
  rw [hghost] at hinvS
  have hbegin : s.begin = 0 := by
    have h := hinv.keys.beginLeMark
    change s.begin ≤ 0 at h
    omega
  have hlength : s.length = s.text.length := by
    rw [hinv.keys.lengthEq, hbegin, hready.endText]; simp
  have hregs : ScaWorkerRegs.RegInv spec (matchInitial s.text.reverse startCtl).pos
      (start (Worker.ofSpec spec) true s) := by
    refine regInv_congr hinvS.regs fun p hpl => ?_
    rw [hpc] at hpl
    obtain ⟨val, hmem⟩ := ScaWorkerRegs.matcher_tableFacts.startLiveMapped p hpl
    have hp : p = ("Origin", "Tail") := by
      simp only [ScaWorkerRegs.startMapping, isFlags_eq, Bool.false_eq_true, if_false,
        matcherStartMapping, List.mem_singleton, Prod.mk.injEq] at hmem
      exact hmem.1
    subst hp
    simp [matchInitial, ScaWorkerRegs.startPos, hlength, isFlags_eq]
  refine ⟨⟨?_, ?_, ?_, ⟨hregs, hinvS.keys⟩, ?_⟩, hfault, hout, hmode⟩
  · rw [hpc]
    exact simCtl_start certified
  · rw [hpc]
    exact hmsT
  · intro h hL i hc
    rw [hpc] at hL
    rw [hrev]
    rcases hR.startLive h hL with rfl | rfl
    · rw [color_origin] at hc
      cases hc
      rw [getD_set_ne _ (by decide : (4 : ℕ) ≠ 1),
        getD_set_self (by rw [hready.revLen]; decide)]
      decide
    · rw [color_tail] at hc
      cases hc
      rw [getD_set_self (by rw [List.length_set, hready.revLen]; decide)]
      decide
  · rw [hend, htext]
    exact hready.endText

/-! ## One tick of the matcher inside `stageRound` -/

/-- The matcher's part of `ScaWindowPal.stageRound` (`ScaWindowPal.lean:201-221`): `arrive a`,
`start birth`, `service` (the flag worker's calls and `consume` in between do not touch it). -/
def matcherTick (birth : Bool) (a : Fin 2) (m : WorkerState) : WorkerState :=
  ScaWindowInstance.matcherOps.service
    (ScaWindowInstance.matcherOps.start birth (ScaWindowInstance.matcherOps.arrive a m))

theorem opsOf_ops (w : Worker) :
    (ScaWindowInstance.opsOf w).service = service w ∧ (ScaWindowInstance.opsOf w).start = start w ∧
      (ScaWindowInstance.opsOf w).arrive = arrive w ∧
      (ScaWindowInstance.opsOf w).output = ScaWindowWorker.output ∧
      (ScaWindowInstance.opsOf w).faulted = fun s => s.fault :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem matcherOps_eq :
    ScaWindowInstance.matcherOps = ScaWindowInstance.opsOf ScaWindowInstance.matcher := by
  unfold ScaWindowInstance.matcherOps
  rfl

theorem matcherTick_eq (birth : Bool) (a : Fin 2) (m : WorkerState) :
    matcherTick birth a m =
      service ScaWindowInstance.matcher
        (start ScaWindowInstance.matcher birth (arrive ScaWindowInstance.matcher a m)) := by
  obtain ⟨h1, h2, h3, -, -⟩ := opsOf_ops ScaWindowInstance.matcher
  unfold matcherTick
  rw [matcherOps_eq, h1, h2, h3]

theorem rawStart_false (w : Worker) (head : String) (src : ℕ) (r : Bool) (s : WorkerState) :
    rawStart w head src r false s = s := by
  unfold rawStart
  split <;> rfl

theorem start_false_eq (w : Worker) (s : WorkerState) : start w false s = startBody w false s :=
  rfl

/-- A disabled `start` does nothing. -/
theorem start_false (s : WorkerState) : start ScaWindowInstance.matcher false s = s := by
  rw [matcher_eq, start_false_eq, startBody_congr (Worker.ofSpec spec) (specWorker spec) rfl]
  unfold startBody
  have hf : (specWorker spec).spec.isFlags = false := isFlags_eq
  simp only [hf, Bool.false_eq_true, if_false, rawStart_false]
  rfl

/-- **A running matcher's tick** (no birth): `arrive a` then `service` is `append a` then
`quantum` head-VM steps. The tick's `output` is whether `match` fired during it. -/
theorem tick_run (hR : ReaderFacts) {W : ℕ} {ρ : String → Bool} {m : WorkerState} {v v' : HVM}
    (hlink : Link W ρ m v) (hrun : m.mode = .run) (a : Fin 2)
    (hvm : iterStep spec.quantum (v.append a) = some v')
    (hside : ∀ i, i < spec.quantum → ∀ u, iterStep i (v.append a) = some u →
      StepSide W (orientAt i (v.append a) ρ) u) :
    Link W (orientAt spec.quantum (v.append a) ρ) (matcherTick false a m) v' ∧
      (matcherTick false a m).fault = m.fault ∧ (matcherTick false a m).mode = .run ∧
      (matcherTick false a m).output = decide (v.outputs.length < v'.outputs.length) ∧
      v.outputs <+: v'.outputs := by
  obtain ⟨hlinkA, hfaultA, houtA, hmodeA⟩ := arrive_link hR hlink a
  rw [hrun] at hmodeA
  obtain ⟨hlinkS, hfaultS, hmodeS, houtS, hpref⟩ := service_link hR hlinkA hmodeA hvm hside
  rw [matcherTick_eq, start_false]
  refine ⟨hlinkS, hfaultS.trans hfaultA, hmodeS, ?_, hpref⟩
  rw [houtS, houtA, Bool.false_or]
  rfl

/-- The head VM a stage's matcher is born into when the letter `a` arrives at `m`: the pattern
is everything read so far, reversed. -/
def birthVM (m : WorkerState) (a : Fin 2) : HVM := matchInitial (m.text ++ [a]).reverse startCtl

/-- **A birth tick**: `arrive a`, `start` (enabled), `service` is the fresh head VM on the
pattern `(text ++ [a]).reverse` run for `quantum` steps. -/
theorem tick_birth (hR : ReaderFacts) {m : WorkerState} {v' : HVM} (hready : Ready m)
    (a : Fin 2) (hvm : iterStep spec.quantum (birthVM m a) = some v')
    (hside : ∀ i, i < spec.quantum → ∀ u, iterStep i (birthVM m a) = some u →
      StepSide (m.text.length + 1) (orientAt i (birthVM m a) startOrient) u) :
    Link (m.text.length + 1) (orientAt spec.quantum (birthVM m a) startOrient)
        (matcherTick true a m) v' ∧
      (matcherTick true a m).fault = m.fault ∧ (matcherTick true a m).mode = .run ∧
      (matcherTick true a m).output = decide (0 < v'.outputs.length) := by
  obtain ⟨hreadyA, hfaultA, houtA, -, htextA⟩ := ready_arrive hready a
  obtain ⟨hlinkS, hfaultS, houtS, hmodeS⟩ := start_link hR hreadyA
  rw [htextA, List.length_append, List.length_singleton] at hlinkS
  obtain ⟨hlinkV, hfaultV, hmodeV, houtV, -⟩ := service_link hR hlinkS hmodeS hvm hside
  rw [matcherTick_eq]
  refine ⟨hlinkV, ?_, hmodeV, ?_⟩
  · rw [hfaultV, hfaultS, hfaultA]
  · rw [houtV, houtS, houtA, Bool.false_or]
    rfl

/-- **An idle matcher's tick** (never started, no birth): only the letter arrives. -/
theorem tick_idle {m : WorkerState} (hready : Ready m) (hidle : m.mode ≠ .run) (a : Fin 2) :
    matcherTick false a m = arrive ScaWindowInstance.matcher a m ∧
      Ready (matcherTick false a m) ∧ (matcherTick false a m).fault = m.fault ∧
      (matcherTick false a m).output = false ∧ (matcherTick false a m).mode = m.mode := by
  obtain ⟨hreadyA, hfaultA, houtA, hmodeA, -⟩ := ready_arrive hready a
  have heq : matcherTick false a m = arrive ScaWindowInstance.matcher a m := by
    rw [matcherTick_eq, start_false, service_idle (by rw [hmodeA]; exact hidle)]
  rw [heq]
  exact ⟨rfl, hreadyA, hfaultA, houtA, hmodeA⟩

/-- **A returned head-program coroutine faults the tick.** -/
theorem tick_returned (hR : ReaderFacts) {W : ℕ} {ρ : String → Bool} {m : WorkerState}
    {v : HVM} {val : Value} (hlink : Link W ρ m v) (hrun : m.mode = .run)
    (hret : v.ctl = .returned val) (a : Fin 2) : (matcherTick false a m).fault = true := by
  obtain ⟨hlinkA, -, -, hmodeA⟩ := arrive_link hR hlink a
  rw [matcherTick_eq, start_false]
  exact (service_returned hlinkA (hmodeA.trans hrun) hret).1

/-! ## Inside the controller's `stageRound` -/

theorem stageRound_matchers {Wf : Type} (fOps : ScaWindowPal.WorkerOps Wf) (a i : Fin 2)
    (s : ScaWindowPal.PalState WorkerState Wf) :
    (ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers =
      Function.update s.matchers i (matcherTick (s.stages i).birth a (s.matchers i)) := by
  unfold ScaWindowPal.stageRound
  rfl

theorem stageRound_other {Wf : Type} (fOps : ScaWindowPal.WorkerOps Wf) (a i : Fin 2)
    (s : ScaWindowPal.PalState WorkerState Wf) (j : Fin 2) (hj : j ≠ i) :
    (ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers j =
      s.matchers j := by
  rw [stageRound_matchers, Function.update_of_ne hj]

theorem stageRound_self {Wf : Type} (fOps : ScaWindowPal.WorkerOps Wf) (a i : Fin 2)
    (s : ScaWindowPal.PalState WorkerState Wf) :
    (ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i =
      matcherTick (s.stages i).birth a (s.matchers i) := by
  rw [stageRound_matchers, Function.update_self]

theorem matcherOps_output (m : WorkerState) :
    ScaWindowInstance.matcherOps.output m = m.output := by
  rw [matcherOps_eq, (opsOf_ops ScaWindowInstance.matcher).2.2.2.1]
  rfl

theorem matcherOps_faulted (m : WorkerState) :
    ScaWindowInstance.matcherOps.faulted m = m.fault := by
  rw [matcherOps_eq, (opsOf_ops ScaWindowInstance.matcher).2.2.2.2]

/-- **`stageRound`, running matcher, no birth.** The other stage's matcher is untouched; stage
`i`'s matcher, linked to `v`, ends linked to `quantum` head-VM steps after `append a`; its fault
bit is kept; its `output` says whether `match` fired in the tick. -/
theorem stageRound_run (hR : ReaderFacts) {Wf : Type} (fOps : ScaWindowPal.WorkerOps Wf)
    (a i : Fin 2) (s : ScaWindowPal.PalState WorkerState Wf) {W : ℕ} {ρ : String → Bool}
    {v v' : HVM} (hbirth : (s.stages i).birth = false) (hlink : Link W ρ (s.matchers i) v)
    (hrun : (s.matchers i).mode = .run)
    (hvm : iterStep spec.quantum (v.append a) = some v')
    (hside : ∀ k, k < spec.quantum → ∀ u, iterStep k (v.append a) = some u →
      StepSide W (orientAt k (v.append a) ρ) u) :
    Link W (orientAt spec.quantum (v.append a) ρ)
        ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) v' ∧
      ScaWindowInstance.matcherOps.faulted
          ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) =
        ScaWindowInstance.matcherOps.faulted (s.matchers i) ∧
      ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i).mode = .run ∧
      ScaWindowInstance.matcherOps.output
          ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) =
        decide (v.outputs.length < v'.outputs.length) := by
  rw [stageRound_self, hbirth, matcherOps_faulted, matcherOps_faulted, matcherOps_output]
  obtain ⟨hl, hf, hm, ho, -⟩ := tick_run hR hlink hrun a hvm hside
  exact ⟨hl, hf, hm, ho⟩

/-- **`stageRound`, birth.** Stage `i`'s matcher (any reachable state) is started on the pattern
of everything read, and runs `quantum` head-VM steps. -/
theorem stageRound_birth (hR : ReaderFacts) {Wf : Type} (fOps : ScaWindowPal.WorkerOps Wf)
    (a i : Fin 2) (s : ScaWindowPal.PalState WorkerState Wf) {v' : HVM}
    (hbirth : (s.stages i).birth = true) (hready : Ready (s.matchers i))
    (hvm : iterStep spec.quantum (birthVM (s.matchers i) a) = some v')
    (hside : ∀ k, k < spec.quantum → ∀ u, iterStep k (birthVM (s.matchers i) a) = some u →
      StepSide ((s.matchers i).text.length + 1)
        (orientAt k (birthVM (s.matchers i) a) startOrient) u) :
    Link ((s.matchers i).text.length + 1)
        (orientAt spec.quantum (birthVM (s.matchers i) a) startOrient)
        ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) v' ∧
      ScaWindowInstance.matcherOps.faulted
          ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) =
        ScaWindowInstance.matcherOps.faulted (s.matchers i) ∧
      ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i).mode = .run ∧
      ScaWindowInstance.matcherOps.output
          ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) =
        decide (0 < v'.outputs.length) := by
  rw [stageRound_self, hbirth, matcherOps_faulted, matcherOps_faulted, matcherOps_output]
  exact tick_birth hR hready a hvm hside

/-- **`stageRound`, idle matcher, no birth.** Only the letter arrives. -/
theorem stageRound_idle {Wf : Type} (fOps : ScaWindowPal.WorkerOps Wf) (a i : Fin 2)
    (s : ScaWindowPal.PalState WorkerState Wf) (hbirth : (s.stages i).birth = false)
    (hready : Ready (s.matchers i)) (hidle : (s.matchers i).mode ≠ .run) :
    (ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i =
        arrive ScaWindowInstance.matcher a (s.matchers i) ∧
      Ready ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i) ∧
      ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i).fault =
        (s.matchers i).fault ∧
      ((ScaWindowPal.stageRound ScaWindowInstance.matcherOps fOps a i s).matchers i).mode =
        (s.matchers i).mode := by
  rw [stageRound_self, hbirth]
  obtain ⟨heq, hr, hf, -, hm⟩ := tick_idle hready hidle a
  exact ⟨heq, hr, hf, hm⟩

/-! ## Axiom audit -/

/-- info: 'PalPeg.ScaWorkerLink.link_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms link_step

/-- info: 'PalPeg.ScaWorkerLink.service_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms service_link

/-- info: 'PalPeg.ScaWorkerLink.arrive_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms arrive_link

/-- info: 'PalPeg.ScaWorkerLink.start_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms start_link

/-- info: 'PalPeg.ScaWorkerLink.stageRound_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageRound_run

/-- info: 'PalPeg.ScaWorkerLink.stageRound_birth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageRound_birth

/-- info: 'PalPeg.ScaWorkerLink.stageRound_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stageRound_idle

/-- **The matcher table's reader facts**, from the certificate of `ScaMatcherReaders`. -/
theorem readerFacts : ReaderFacts :=
  ⟨ScaMatcherReaders.fix, ScaMatcherReaders.proper, ScaMatcherReaders.colored,
    ScaMatcherReaders.startLive, ScaMatcherReaders.matchB⟩

end PalPeg.ScaWorkerLink
