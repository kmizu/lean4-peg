import PalPeg.TextFeedStartupBoundary

/-! A fixed-rate finite startup reaches the continuous streaming
invariant. Prep cost, startup credit, and the source endpoint are proved,
not separate assumptions on the resulting running configuration. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStageStartup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.PrepInstance PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepEndpoint PalPeg.TextFeedRefine
open PalPeg.TextFeedStartupBudget

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

noncomputable def callInitial (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    CallCtrl (programs e) (Outer e leftSym R rate) :=
  ((⟨0, Nat.zero_lt_succ R⟩, true, startCtrlS (task e leftSym rate)), encode (.feed .idle),
    initialBank (programs e), false)

theorem callInitial_machine (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) :
    (machine e leftSym enc R rate).initial =
      ((callInitial e leftSym R rate, ⟨0, by omega⟩), ⟨0, by omega⟩) := rfl

theorem before_prepView (e : Env k) (S : PatternTapes.Tapes k) (old : Fin k) :
    prepView (before e S old) = TSg S := by
  funext j
  fin_cases j <;> rfl

theorem before_feedView (e : Env k) (S : PatternTapes.Tapes k) (old : Fin k) :
    feedView (before e S old) = TextFeedInit.unprepared e (GSProg.TS (toGS S)) old := by
  funext j
  fin_cases j <;> rfl

/-- This predicate is a proof about the live 27-tape machine; the
existential reference machine and model are not stored in its control. -/
def StreamReady (e : Env k) (leftSym : Fin k) (R rate : ℕ) (v Text : List (Fin k))
    (p₁ rem n : ℕ) (x : TextFeedWorkerBridge.Phys e leftSym R rate) : Prop :=
  ∃ (y : Phys e R rate) (M : TextFeed.Machine' k) (ph : Phase) (q : Queue (Fin k)) (old : Fin k),
    TextFeedWorkerBridge.Link e leftSym R rate x y ∧ ReadyAt e x.2 q old ∧
    Sim e v Text R rate p₁ rem n M ph y old ∧
    workScale rate * ((rate + 1) * n) ≤ workCredit v rate (M, ph) ∧
    ScanInv v Text M.st ∧ (∀ i, OccAt v Text i → M.st.pos ≤ i) ∧
    y.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧ x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩

set_option maxHeartbeats 800000 in
theorem setup_reaches_boundary {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {w : List (Fin k)} {L : ℕ} {S : PatternTapes.Tapes k}
    (enc : Terminal → Fin k) (input : List Terminal) (old : Fin k)
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w (input.map enc) S)
    (hL : 4 ≤ L) (htext : L / 2 ≤ input.length)
    (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc) :
    let d := PrepInstances.prepRes w L
    let v := (PrepInstances.stagePat w L).drop d.1
    let R := startupRate 8
    ∃ n, 1 ≤ n ∧ n ≤ L / 2 ∧
      let z := stateBefore e leftSym enc R 8 (callInitial e leftSym R 8) (before e S old) (input.take n)
      StreamReady e leftSym R 8 v (input.map enc) d.2.1 d.2.2 n (z.state.1.1, z.tape) ∧
        z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  let R := startupRate 8
  let d := PrepInstances.prepRes w L
  let v := (PrepInstances.stagePat w L).drop d.1
  let c := callInitial e leftSym R 8
  let T := before e S old
  obtain ⟨tr, S', he, hout, hscan, hcost⟩ := finitePrepSetup_exec (Terminal := Unit)
    8 hmb hpre hstart hend hne
  let q := tr.length / R
  let J := tr.length % R
  have hJ : J < R := Nat.mod_lt _ (startupRate_pos 8)
  have hsplit : q * R + J = tr.length := by
    dsimp only [q, J]
    simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div tr.length R
  have hframes : frames 8 tr.length = q + 1 := frames_of_split hsplit hJ
  have hcost' : tr.length ≤ TextFeedStartupBudget.slope 8 * L + offset 8 := hcost
  have hhalf : q + 1 ≤ L / 2 := by
    rw [← hframes]
    exact frames_half hL hcost'
  have hq : q < input.length := by omega
  let a := input[q]
  have ha : input[q]? = some a := List.getElem?_eq_getElem hq
  have htake : input.take (q + 1) = input.take q ++ [a] := by
    rw [List.take_add_one, ha]; rfl
  have htlen : (input.take q).length = q := List.length_take_of_le (by omega)
  have hprefix : (input.take q ++ [a]).map enc = (input.map enc).take ((input.take q).length + 1) := by
    rw [htlen, ← htake, List.map_take]
  have hall : ∀ b ∈ input.take q ++ [a], enc b ≠ e.mark := by
    intro b hb heq
    rw [← htake] at hb
    exact hmark (heq ▸ List.mem_map.mpr ⟨b, List.mem_of_mem_take hb, rfl⟩)
  have hvlen : v.length = L - d.1 := by
    rw [List.length_drop, PrepInstances.stagePat_length hpre.hle]
  have hcut : 7 * d.1 < L := PrepInstances.prep_cut_bound hpre.hpos hpre.hle
  have hv : 0 < v.length := by rw [hvlen]; omega
  have hK : KSimple v 8 d.2.1 d.2.2 := (PrepInstances.prep_core w L).ksimple_eff
  have hsV : e.startSym ∉ v := fun hh => hstart (List.mem_of_mem_drop hh)
  have heV : e.endSym ∉ v := fun hh => hend (List.mem_of_mem_drop hh)
  have hdelay : (8 + 1) * ((input.take q).length + 1) ≤ 8 * v.length := by
    rw [htlen, hvlen, ← hframes]
    exact frames_credit (by omega) hL hcost' hcut
  have he' : Exec (source e) e.blank
      (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark 8) (prepView T) tr := by
    rw [before_prepView]
    exact he
  have hout' : applyTrace e.blank (prepView T) tr = TSg S' := by
    rw [before_prepView]
    exact hout
  have hb : AtBoundary (programs e) c.2.2.1 := initialBank_boundary _
  have hz := TextFeedStartupBoundary.end_at_boundary hc hmb (by omega : 0 < 8) hv heV hsV
    hblank hmark hK hJ enc c T hb rfl rfl (GSProg.TS (toGS S)) old
    (before_feedView e S old) rfl (input.take q) a hall hprefix
    (by rw [htlen, List.length_map]; omega) tr S' he' hout'
    (by rw [htlen]; exact hsplit) hscan.1 hdelay
  obtain ⟨y, M, ph, queue, hl, hr, hi, hcredit, hs, hp, hyc, hxc, hlocal, hglobal⟩ := hz
  refine ⟨q + 1, by omega, hhalf, ?_⟩
  rw [htake]
  refine ⟨?_, hlocal, hglobal⟩
  exact ⟨y, M, ph, queue, enc a, hl, hr, by simpa only [htlen] using hi,
    by simpa only [htlen] using hcredit, hs, hp, hyc, hxc⟩

/-- info: 'PalPeg.TextFeedStageStartup.setup_reaches_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_reaches_boundary

end PalPeg.TextFeedStageStartup
