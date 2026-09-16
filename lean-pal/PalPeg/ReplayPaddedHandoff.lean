import PalPeg.ReplayLoopEventPadding

set_option autoImplicit false
namespace PalPeg.ReplayPaddedHandoff
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ReplayLoop PalPeg.ReplayLoopEvents
variable {Terminal Q : Type} [Fintype Q] [DecidableEq Q] {k t B : ℕ}
local instance : DecidableEq (Control Q B) := inferInstance

/-- An actual recycled configuration follows the same first recovery
handoff as its canonical model, even with interleaved real arrivals. -/
theorem recovery (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (y : SConfig (Fin 3 → Fin 3) (Fin k) 3) (n : ℕ)
    (hdone : ∀ j, (HistoryRecover.run M.blank n y).state j = 2) (hn : n < work es)
    (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (ReplayLoopRecovery.lift roles log x y)) :
    ∃ pre post, es = pre ++ .tick :: post ∧ work pre ≤ n ∧
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          ⟨(x.state, roles, .inr ⟨0, hB⟩),
            (ReplayLoopRecovery.lift (B := B) roles (appendLog M.blank enc (arrivals pre) log) x
              (HistoryRecover.run M.blank n y)).tape⟩) := by
  obtain ⟨pre, post, he, hw, hr⟩ := ReplayLoopEventCut.recovery_handoff
    M hB enc decode roles es log x y n hdone hn
  exact ⟨pre, post, he, hw, ReplayLoopEventPadding.transfer M hB enc decode es hactual hr⟩

/-- The next frozen batch includes every arrival preceding the first
replay handoff, without normalizing the physical tapes beforehand. -/
theorem replay (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (F : Fin 4 → STape (Fin k))
    (x : SConfig (Q × Fin B) (Fin k) (1 + t)) (n : ℕ)
    (hdone : (TapeReplay.run M hB decode n x).state.2.val = 0 ∧
      ((TapeReplay.run M hB decode n x).tape TapeReplay.sourceAddr).focus = M.blank)
    (hn : n < work es) (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (ReplayLoopReplay.lift roles F x)) :
    ∃ pre post, es = pre ++ .tick :: post ∧ work pre ≤ n ∧
      let F' := appendBuffers M.blank enc roles (arrivals pre) F
      let z := TapeReplay.run M hB decode n x
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          (ReplayLoopRecovery.lift (rotate.trans roles) (F' (roles 0))
            (ReplayLoopRotation.matcher z) ⟨fun _ => 0, ReplayLoopRotation.nextBuffers roles F' z⟩)) := by
  obtain ⟨pre, post, he, hw, hr⟩ := ReplayLoopEventCut.replay_handoff
    M hB enc decode roles es F x n hdone hn
  exact ⟨pre, post, he, hw, ReplayLoopEventPadding.transfer M hB enc decode es hactual hr⟩

/-- Both autonomous handoffs fit in the sum of the phase budgets, even
when arrivals occur between ticks. The suffix starts in rotated recovery. -/
theorem cycle (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal) (roles : Fin 4 ≃ Fin 4)
    (es : List (Event Terminal)) (log : STape (Fin k)) (x : SConfig Q (Fin k) t)
    (y : SConfig (Fin 3 → Fin 3) (Fin k) 3) (n m : ℕ)
    (hdone : ∀ j, (HistoryRecover.run M.blank n y).state j = 2)
    (hreplay :
      let r := TapeReplay.run M hB decode m
        (TapeReplay.pack ⟨0, hB⟩ ((HistoryRecover.run M.blank n y).tape 2) x)
      r.state.2.val = 0 ∧ (r.tape TapeReplay.sourceAddr).focus = M.blank)
    (hbudget : n + m + 2 ≤ work es)
    (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (ReplayLoopRecovery.lift roles log x y)) :
    ∃ pre mid post, es = pre ++ .tick :: (mid ++ .tick :: post) ∧
      work (pre ++ .tick :: (mid ++ [.tick])) ≤ n + m + 2 ∧
      let F := ReplayLoopRotation.recoveredBuffers roles
        (appendLog M.blank enc (arrivals pre) log) (HistoryRecover.run M.blank n y).tape
      let F' := appendBuffers M.blank enc roles (arrivals mid) F
      let z := TapeReplay.run M hB decode m
        (TapeReplay.pack ⟨0, hB⟩ ((HistoryRecover.run M.blank n y).tape 2) x)
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          (ReplayLoopRecovery.lift (rotate.trans roles) (F' (roles 0))
            (ReplayLoopRotation.matcher z) ⟨fun _ => 0, ReplayLoopRotation.nextBuffers roles F' z⟩)) := by
  obtain ⟨pre, rest, he, hp, hr⟩ := recovery M hB enc decode roles es log x y n
    hdone (by omega) actual hactual
  have hc := (ReplayLoopEventCut.cut_accounting pre rest).2
  rw [← he] at hc
  have hm : m < work rest := by omega
  let T := (HistoryRecover.run M.blank n y).tape
  let L := appendLog M.blank enc (arrivals pre) log
  let F := ReplayLoopRotation.recoveredBuffers roles L T
  let r := TapeReplay.pack (Q := Q) ⟨0, hB⟩ (T 2) x
  have hs : HistoryRecover.run M.blank n y = ⟨fun _ => 2, T⟩ := by
    have hh : (HistoryRecover.run M.blank n y).state = fun _ => 2 := funext hdone
    cases hz : HistoryRecover.run M.blank n y
    simp only [hz] at hh
    cases hh
    dsimp only [T]
    rw [hz]
  rw [hs, ReplayLoopRotation.recovery_to_replay] at hr
  change ConfigBlankEq M.blank (run M hB enc decode es actual)
    (run M hB enc decode rest (ReplayLoopReplay.lift roles F r)) at hr
  obtain ⟨mid, post, hmdecomp, hmid, hresult⟩ := ReplayLoopEventCut.replay_handoff
    M hB enc decode roles rest F r m hreplay hm
  rw [hresult] at hr
  refine ⟨pre, mid, post, ?_, ?_, hr⟩
  · rw [he, hmdecomp]
  · rw [ReplayLoopEventCut.work_append]
    simp only [work]
    rw [ReplayLoopEventCut.work_append]
    simp only [work]
    omega

/-- Concrete tape lengths discharge both phase-completion premises.
The replay result also identifies the entire matcher configuration. -/
theorem phase_bounds (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (x : SConfig Q (Fin k) t) (old : List (Fin k)) (ho : M.blank ∉ old)
    (w : List Terminal) (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = ⟨old.reverse ++ [M.blank], M.blank, []⟩)
    (h1 : T 1 = ⟨[M.blank], M.blank, []⟩)
    (h2 : T 2 = ⟨(w.map enc).reverse ++ [M.blank], M.blank, []⟩) :
    let y := HistoryRecover.run M.blank (max old.length w.length + 2) ⟨fun _ => 0, T⟩
    (∀ j, y.state j = 2) ∧
      STape.BlankEq M.blank (y.tape 0) ⟨[M.blank], M.blank, []⟩ ∧
      STape.BlankEq M.blank (y.tape 1) ⟨[M.blank], M.blank, []⟩ ∧
      ConfigBlankEq M.blank
        (TapeReplay.run M hB decode (w.length * B) (TapeReplay.pack ⟨0, hB⟩ (y.tape 2) x))
        (TapeReplay.pack ⟨0, hB⟩
          (TapeReplay.source M.blank [] ((w.map enc).reverse ++ [M.blank]))
          (w.foldl M.sRound x)) := by
  let N := max old.length w.length + 2
  have hw : M.blank ∉ w.map enc := by
    intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    exact henc a ha
  have ha := HistoryRecover.erase_lane M.blank 0 (by decide) old.reverse (by simpa using ho)
    N (by dsimp only [N]; simp) T h0
  have hb := HistoryRecover.erase_lane M.blank 1 (by decide) [] (by simp)
    N (by dsimp only [N]; simp) T h1
  have hc := HistoryRecover.rewind_lane M.blank (w.map enc) hw N
    (by dsimp only [N]; simp) T h2
  refine ⟨?_, ha.2, hb.2, ?_⟩
  · intro j
    fin_cases j
    · exact ha.1
    · exact hb.1
    · exact hc.1
  · have hp : ConfigBlankEq M.blank
        (TapeReplay.pack (Q := Q) ⟨0, hB⟩ ((HistoryRecover.run M.blank N ⟨fun _ => 0, T⟩).tape 2) x)
        (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (w.map enc) [M.blank]) x) := by
      refine ⟨rfl, ?_⟩
      intro j
      simp only [TapeReplay.pack]
      cases hj : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin t) with
      | inl i => exact hc.2
      | inr i => exact STape.BlankEq.refl _ _
    have hr := (TapeReplay.machine M hB decode).runFrom_blankEq
      (List.replicate (w.length * B) ()) hp
    change ConfigBlankEq M.blank (TapeReplay.run M hB decode _ _) (TapeReplay.run M hB decode _ _) at hr
    rw [TapeReplay.encoded_word M hB enc decode hdec henc w [M.blank] x _ (by omega)] at hr
    exact hr

/-- A full interleaved batch cycle, with no caller-supplied phase
completion assumptions. Physical padding is allowed in the initial state. -/
theorem batch_cycle (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (es : List (Event Terminal)) (log : STape (Fin k))
    (x : SConfig Q (Fin k) t) (old : List (Fin k)) (ho : M.blank ∉ old)
    (w : List Terminal) (T : Fin 3 → STape (Fin k))
    (h0 : T 0 = ⟨old.reverse ++ [M.blank], M.blank, []⟩)
    (h1 : T 1 = ⟨[M.blank], M.blank, []⟩)
    (h2 : T 2 = ⟨(w.map enc).reverse ++ [M.blank], M.blank, []⟩)
    (hbudget : max old.length w.length + w.length * B + 4 ≤ work es)
    (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (ReplayLoopRecovery.lift roles log x ⟨fun _ => 0, T⟩)) :
    let y := HistoryRecover.run M.blank (max old.length w.length + 2) ⟨fun _ => 0, T⟩
    let z := TapeReplay.run M hB decode (w.length * B) (TapeReplay.pack ⟨0, hB⟩ (y.tape 2) x)
    STape.BlankEq M.blank (y.tape 0) ⟨[M.blank], M.blank, []⟩ ∧
    STape.BlankEq M.blank (y.tape 1) ⟨[M.blank], M.blank, []⟩ ∧
    ConfigBlankEq M.blank z
      (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank [] ((w.map enc).reverse ++ [M.blank]))
        (w.foldl M.sRound x)) ∧
    ∃ pre mid post, es = pre ++ .tick :: (mid ++ .tick :: post) ∧
      work (pre ++ .tick :: (mid ++ [.tick])) ≤ max old.length w.length + w.length * B + 4 ∧
      let F := ReplayLoopRotation.recoveredBuffers roles
        (appendLog M.blank enc (arrivals pre) log) y.tape
      let F' := appendBuffers M.blank enc roles (arrivals mid) F
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          (ReplayLoopRecovery.lift (rotate.trans roles) (F' (roles 0))
            (ReplayLoopRotation.matcher z) ⟨fun _ => 0, ReplayLoopRotation.nextBuffers roles F' z⟩)) := by
  obtain ⟨hd, hfree0, hfree1, hz⟩ := phase_bounds M hB enc decode hdec henc x old ho w T h0 h1 h2
  refine ⟨hfree0, hfree1, hz, ?_⟩
  have hterminal :
      let z := TapeReplay.run M hB decode (w.length * B)
        (TapeReplay.pack ⟨0, hB⟩ ((HistoryRecover.run M.blank (max old.length w.length + 2)
          ⟨fun _ => 0, T⟩).tape 2) x)
      z.state.2.val = 0 ∧ (z.tape TapeReplay.sourceAddr).focus = M.blank := by
    constructor
    · exact congrArg (fun s => s.2.val) hz.1
    · exact (hz.2 TapeReplay.sourceAddr).focus
  obtain ⟨pre, mid, post, he, hw, hr⟩ := cycle M hB enc decode roles es log x ⟨fun _ => 0, T⟩
    (max old.length w.length + 2) (w.length * B) hd hterminal (by omega) actual hactual
  exact ⟨pre, mid, post, he, by omega, hr⟩

theorem appendBuffers_other (blank : Fin k) (enc : Terminal → Fin k) (roles : Fin 4 ≃ Fin 4)
    (as : List Terminal) (F : Fin 4 → STape (Fin k)) (i : Fin 4) (hi : i ≠ roles 3) :
    appendBuffers blank enc roles as F i = F i := by
  induction as generalizing F with
  | nil => rfl
  | cons a as ih =>
    change appendBuffers blank enc roles as (ReplayLoopCapture.store blank (enc a) roles F) i = _
    rw [ih]
    simp [ReplayLoopCapture.store, hi]

theorem appendLog_blankEq (blank : Fin k) (enc : Terminal → Fin k) (as : List Terminal)
    {S U : STape (Fin k)} (h : STape.BlankEq blank S U) :
    STape.BlankEq blank (appendLog blank enc as S) (appendLog blank enc as U) := by
  induction as generalizing S U with
  | nil => exact h
  | cons a as ih => exact ih (h.applyAction _)

/-- The output layout satisfies the next cycle's frontier contract.
All arrivals from both phases follow the previously pending word. -/
theorem next_layout (blank : Fin k) (hB : 0 < B) (enc : Terminal → Fin k)
    (roles : Fin 4 ≃ Fin 4) (pending as bs w : List Terminal)
    (log : STape (Fin k)) (U : Fin 3 → STape (Fin k)) (x : SConfig Q (Fin k) t)
    (z : SConfig (Q × Fin B) (Fin k) (1 + t))
    (hlog : STape.BlankEq blank log ⟨(pending.map enc).reverse ++ [blank], blank, []⟩)
    (h0 : STape.BlankEq blank (U 0) ⟨[blank], blank, []⟩)
    (h1 : STape.BlankEq blank (U 1) ⟨[blank], blank, []⟩)
    (hz : ConfigBlankEq blank z (TapeReplay.pack ⟨0, hB⟩
      (TapeReplay.source blank [] ((w.map enc).reverse ++ [blank])) x)) :
    let F := ReplayLoopRotation.recoveredBuffers roles (appendLog blank enc as log) U
    let F' := appendBuffers blank enc roles bs F
    ConfigBlankEq blank
      (ReplayLoopRecovery.lift (B := B) (rotate.trans roles) (F' (roles 0))
        (ReplayLoopRotation.matcher z) ⟨fun _ => 0, ReplayLoopRotation.nextBuffers roles F' z⟩)
      (ReplayLoopRecovery.lift (rotate.trans roles) ⟨[blank], blank, []⟩ x
        ⟨fun _ => 0, ![⟨(w.map enc).reverse ++ [blank], blank, []⟩,
          ⟨[blank], blank, []⟩,
          ⟨((pending ++ as ++ bs).map enc).reverse ++ [blank], blank, []⟩]⟩) := by
  let F := ReplayLoopRotation.recoveredBuffers roles (appendLog blank enc as log) U
  let F' := appendBuffers blank enc roles bs F
  have hf0 : F' (roles 0) = U 0 := by
    change appendBuffers blank enc roles bs F (roles 0) = _
    rw [appendBuffers_other blank enc roles bs F (roles 0) (by simp)]
    simp [F, ReplayLoopRotation.recoveredBuffers]
  have hf1 : F' (roles 1) = U 1 := by
    change appendBuffers blank enc roles bs F (roles 1) = _
    rw [appendBuffers_other blank enc roles bs F (roles 1) (by simp)]
    simp [F, ReplayLoopRotation.recoveredBuffers]
  have hf3 : STape.BlankEq blank (F' (roles 3))
      ⟨((pending ++ as ++ bs).map enc).reverse ++ [blank], blank, []⟩ := by
    change STape.BlankEq blank (appendBuffers blank enc roles bs F (roles 3)) _
    rw [appendBuffers_log]
    have hf : F (roles 3) = appendLog blank enc as log := by
      simp [F, ReplayLoopRotation.recoveredBuffers]
    rw [hf]
    have hh := appendLog_blankEq blank enc bs (appendLog_blankEq blank enc as hlog)
    rw [appendLog_frontier, appendLog_frontier] at hh
    simpa only [List.map_append, List.reverse_append, List.append_assoc] using hh
  have ht : ∀ i, STape.BlankEq blank (ReplayLoopRotation.nextBuffers roles F' z i)
      (![⟨(w.map enc).reverse ++ [blank], blank, []⟩, ⟨[blank], blank, []⟩,
        ⟨((pending ++ as ++ bs).map enc).reverse ++ [blank], blank, []⟩] i) := by
    intro i
    fin_cases i
    · exact hz.2 TapeReplay.sourceAddr
    · change STape.BlankEq blank (F' (roles 1)) _
      rw [hf1]
      exact h1
    · exact hf3
  have hm : ConfigBlankEq blank (ReplayLoopRotation.matcher z) x := by
    refine ⟨congrArg Prod.fst hz.1, ?_⟩
    intro j
    simpa [ReplayLoopRotation.matcher, TapeReplay.pack, TapeReplay.targetAddr] using hz.2 (TapeReplay.targetAddr j)
  refine ⟨?_, ?_⟩
  · change ((ReplayLoopRotation.matcher z).state, rotate.trans roles, Sum.inl (fun _ => 0)) = _
    rw [hm.1]
    rfl
  · intro j
    change STape.BlankEq blank
      ((ReplayLoopRecovery.lift (B := B) (rotate.trans roles) (F' (roles 0))
        (ReplayLoopRotation.matcher z) ⟨fun _ => 0, ReplayLoopRotation.nextBuffers roles F' z⟩).tape j) _
    simp only [ReplayLoopRecovery.lift]
    cases hj : (finSumFinEquiv.symm j : Fin 4 ⊕ Fin t) with
    | inl i =>
      by_cases hi : ((rotate.trans roles).symm i).val < 3
      · simpa only [hi, ↓reduceDIte] using ht ⟨_, hi⟩
      · simpa only [hi, ↓reduceDIte, hf0] using h0
    | inr i => exact hm.2 i

/-- Canonical cycle boundary; BlankEq permits the physical recycled tapes. -/
def boundary (blank : Fin k) (enc : Terminal → Fin k) (roles : Fin 4 ≃ Fin 4)
    (old : List (Fin k)) (batch pending : List Terminal) (x : SConfig Q (Fin k) t) :
    SConfig (Control Q B) (Fin k) (4 + t) :=
  ReplayLoopRecovery.lift roles ⟨(pending.map enc).reverse ++ [blank], blank, []⟩ x
    ⟨fun _ => 0, ![⟨old.reverse ++ [blank], blank, []⟩, ⟨[blank], blank, []⟩,
      ⟨(batch.map enc).reverse ++ [blank], blank, []⟩]⟩

/-- A cycle returns to the same boundary predicate, advancing the matcher
and retaining exactly all unprocessed input, with a concrete worker bound. -/
theorem boundary_cycle (M : StructuredMachine Terminal Q (Fin k) t B) (hB : 0 < B)
    (enc : Terminal → Fin k) (decode : Fin k → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (roles : Fin 4 ≃ Fin 4) (es : List (Event Terminal))
    (old : List (Fin k)) (ho : M.blank ∉ old) (batch pending : List Terminal)
    (x : SConfig Q (Fin k) t)
    (hbudget : max old.length batch.length + batch.length * B + 4 ≤ work es)
    (actual : SConfig (Control Q B) (Fin k) (4 + t))
    (hactual : ConfigBlankEq M.blank actual (boundary M.blank enc roles old batch pending x)) :
    ∃ seg post, es = seg ++ post ∧
      work seg ≤ max old.length batch.length + batch.length * B + 4 ∧
      2 ≤ work seg ∧
      ConfigBlankEq M.blank (run M hB enc decode es actual)
        (run M hB enc decode post
          (boundary M.blank enc (rotate.trans roles) (batch.map enc)
            (pending ++ arrivals seg) [] (batch.foldl M.sRound x))) := by
  let T : Fin 3 → STape (Fin k) := ![⟨old.reverse ++ [M.blank], M.blank, []⟩,
    ⟨[M.blank], M.blank, []⟩, ⟨(batch.map enc).reverse ++ [M.blank], M.blank, []⟩]
  let log : STape (Fin k) := ⟨(pending.map enc).reverse ++ [M.blank], M.blank, []⟩
  obtain ⟨h0, h1, hz, pre, mid, post, he, hw, hr⟩ := batch_cycle M hB enc decode hdec henc
    roles es log x old ho batch T rfl rfl rfl hbudget actual hactual
  have hl := next_layout M.blank hB enc roles pending (arrivals pre) (arrivals mid) batch log
    (HistoryRecover.run M.blank (max old.length batch.length + 2) ⟨fun _ => 0, T⟩).tape
    (batch.foldl M.sRound x) _ (STape.BlankEq.refl _ _) h0 h1 hz
  have hp := ReplayLoopEventPadding.run_blankEq M hB enc decode post hl
  have hh : ConfigBlankEq M.blank (run M hB enc decode es actual) _ :=
    ⟨hr.1.trans hp.1, fun j => (hr.2 j).trans (hp.2 j)⟩
  let seg := pre ++ .tick :: (mid ++ [.tick])
  have ha : arrivals seg = arrivals pre ++ arrivals mid := by
    simp [seg, arrivals]
  refine ⟨seg, post, ?_, hw, ?_, ?_⟩
  · simpa [seg, List.append_assoc] using he
  · simp only [seg, ReplayLoopEventCut.work_append, work]
    omega
  · rw [ha]
    simpa only [boundary, List.map_nil, List.reverse_nil, List.nil_append, List.append_assoc] using hh

/-- info: 'PalPeg.ReplayPaddedHandoff.boundary_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boundary_cycle

/-- info: 'PalPeg.ReplayPaddedHandoff.next_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_layout

/-- info: 'PalPeg.ReplayPaddedHandoff.batch_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_cycle

/-- info: 'PalPeg.ReplayPaddedHandoff.phase_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase_bounds

/-- info: 'PalPeg.ReplayPaddedHandoff.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycle

/-- info: 'PalPeg.ReplayPaddedHandoff.replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replay

/-- info: 'PalPeg.ReplayPaddedHandoff.recovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recovery

end PalPeg.ReplayPaddedHandoff
