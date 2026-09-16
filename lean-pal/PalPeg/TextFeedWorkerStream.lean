import PalPeg.TextFeedWorkerArrival
import PalPeg.TextFeedOffsetStream

/-! Continuous execution of the combined finite machine preserves the
feeder refinement across every real arrival, without a controller reset. -/
set_option autoImplicit false

namespace PalPeg.TextFeedWorkerBridge
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput
open PalPeg.TextFeedPrepare PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule
open PalPeg.TextFeedStartupSafety

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (TextFeedSchedule.Outer R rate) :=
  Classical.decEq _

noncomputable def workerRun (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (x : Phys e leftSym R rate) (word : List Terminal) :=
  word.foldl (TextFeedStartupSchedule.machine e leftSym enc R rate).sRound
    { state := ((x.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := x.2 }

theorem workerRun_link {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} {x : Phys e leftSym R rate} {y : TextFeedRefine.Phys e R rate}
    (h : Link e leftSym R rate x y) {q : RTQueue.Queue (Fin k)} {old : Fin k}
    (hq : ReadyAt e x.2 q old) (enc : Terminal → Fin k) (word : List Terminal)
    (hall : ∀ a ∈ word, enc a ≠ e.mark) :
    let u := workerRun e leftSym enc R rate x word
    let v := TextFeedRefine.preparedRun e enc R rate y word
    Link e leftSym R rate (u.state.1.1, u.tape) (v.state.1.1, v.tape) ∧
      (∃ q' old', ReadyAt e u.tape q' old') ∧
      u.state.1.2 = ⟨0, by omega⟩ ∧ u.state.2 = ⟨0, by omega⟩ ∧
      v.state.1.2 = ⟨0, by omega⟩ ∧ v.state.2 = ⟨0, by omega⟩ := by
  induction word using List.reverseRecOn with
  | nil => exact ⟨h, ⟨q, old, hq⟩, rfl, rfl, rfl, rfl⟩
  | append_singleton word a ih =>
    obtain ⟨hl, ⟨q', old', hr⟩, hu1, hu2, hv1, hv2⟩ := ih
      (fun b hb => hall b (List.mem_append_left _ hb))
    let u := workerRun e leftSym enc R rate x word
    let v := TextFeedRefine.preparedRun e enc R rate y word
    have hueta : { state := ((u.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := u.tape } = u := by
      have hh : u.state = ((u.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩) :=
        Prod.ext (Prod.ext rfl hu1) hu2
      rw [← hh]
    have hveta : { state := ((v.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := v.tape } = v := by
      have hh : v.state = ((v.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩) :=
        Prod.ext (Prod.ext rfl hv1) hv2
      rw [← hh]
    have hf := frame_link hc hmb hl hr enc a (hall a (by simp))
    dsimp only at hf
    rw [hueta, hveta] at hf
    obtain ⟨hl', ⟨q'', hr'⟩, hu1', hu2', hv1', hv2'⟩ := hf
    simpa only [workerRun, TextFeedRefine.preparedRun, List.foldl_append,
      List.foldl_cons, List.foldl_nil, u, v] using
      And.intro hl' (And.intro (Exists.intro q'' (Exists.intro (enc a) hr'))
        ⟨hu1', hu2', hv1', hv2'⟩)

set_option maxHeartbeats 800000 in
theorem workerRun_offset_deadline {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {leftSym : Fin k} {v : List (Fin k)} {R rate p₁ rem base : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (enc : Terminal → Fin k) (input : List Terminal)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc)
    (hK : KSimple v rate p₁ rem) (hR : TextFeedRefine.workRate rate ≤ R)
    {M₀ : TextFeed.Machine' k} {ph₀ : TextFeedRefine.Phase}
    {x : Phys e leftSym R rate} {y : TextFeedRefine.Phys e R rate} {old : Fin k}
    (hlink : Link e leftSym R rate x y) {q : RTQueue.Queue (Fin k)}
    (hq : ReadyAt e x.2 q old)
    (h₀ : TextFeedRefine.Sim e v (input.map enc) R rate p₁ rem base M₀ ph₀ y old)
    (hcounter₀ : y.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (hc₀ : TextFeedRefine.workScale rate * ((rate + 1) * base) ≤
      TextFeedRefine.workCredit v rate (M₀, ph₀))
    (hs₀ : ScanInv v (input.map enc) M₀.st)
    {i n : ℕ} (hn : base + n < input.length) (hocc : OccAt v (input.map enc) i)
    (hpos₀ : M₀.st.pos ≤ i) (hd : i + v.length = base + n + 1)
    (a : Terminal) (ha : input[base + n]? = some a) :
    let u := workerRun e leftSym enc R rate x ((input.drop base).take n)
    let captured : Phys e leftSym R rate :=
      (u.state.1.1, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) u.tape)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      TextFeedSchedule.stageSymbols (fun t =>
        (((run (Terminal := Terminal) e leftSym R rate)^[j + 1] captured).2 (feedSlot t)).focus)
        GSTapes.tP = e.endSym := by
  have hall : ∀ b ∈ input, enc b ≠ e.mark := by
    intro b hb he
    exact hmark (he ▸ List.mem_map.mpr ⟨b, hb, rfl⟩)
  have hpref : ∀ b ∈ (input.drop base).take n, enc b ≠ e.mark := by
    intro b hb
    exact hall b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  obtain ⟨hl, ⟨q', old', hr⟩, _⟩ := workerRun_link hc hmb hlink hq enc
    ((input.drop base).take n) hpref
  obtain ⟨j, hj1, hjR, hreport⟩ := TextFeedRefine.preparedRun_offset_deadline
    hc hmb hk hv hend hstart enc input hblank hmark hK hR h₀ hcounter₀ hc₀ hs₀
    hn hocc hpos₀ hd a ha
  have ha' := hall a (List.mem_of_getElem? ha)
  have hl' := (run_link_iterate (Terminal := Terminal) hc hmb (capture_link hl enc a)
    (TextFeedStartupRun.capture_ready enc a hr) ha' (j + 1)).1
  refine ⟨j, hj1, hjR, ?_⟩
  change TextFeedSchedule.stageSymbols (fun t => (feedView _ t).focus) GSTapes.tP = e.endSym
  rw [hl'.tapes]
  exact hreport

/-- info: 'PalPeg.TextFeedWorkerBridge.workerRun_offset_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms workerRun_offset_deadline

/-- info: 'PalPeg.TextFeedWorkerBridge.workerRun_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms workerRun_link

end PalPeg.TextFeedWorkerBridge
