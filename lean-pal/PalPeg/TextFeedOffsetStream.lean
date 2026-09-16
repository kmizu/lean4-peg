import PalPeg.TextFeedOffset
import PalPeg.TextFeedStream

/-! Physical streaming after startup consumes only the not-yet-arrived
suffix. The existing backlog remains in the prepared configuration. -/
set_option autoImplicit false

namespace PalPeg.TextFeedRefine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (Outer R rate) := Classical.decEq _

theorem preparedRun_offset_refine {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v : List (Fin k)} {R rate p₁ rem base : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (enc : Terminal → Fin k) (input : List Terminal)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {x₀ : Phys e R rate} {old₀ : Fin k}
    (h₀ : Sim e v (input.map enc) R rate p₁ rem base M₀ ph₀ x₀ old₀)
    (hcounter₀ : x₀.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (n : ℕ) (hn : base + n ≤ input.length) :
    let z := preparedRun e enc R rate x₀ ((input.drop base).take n)
    let m := onlineWorkFrom e v (input.map enc) R rate p₁ rem base M₀ ph₀ n
    ∃ old, Sim e v (input.map enc) R rate p₁ rem (base + n) m.1 m.2
      (z.state.1.1, z.tape) old ∧
      z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  induction n with
  | zero => exact ⟨old₀, h₀, hcounter₀, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨old, hsim, hcounter, hlocal, hglobal⟩ := ih (by omega)
    have hn' : base + n < input.length := by omega
    let a := input[base + n]
    have ha : input[base + n]? = some a := List.getElem?_eq_getElem hn'
    have had : (input.drop base)[n]? = some a := by
      simpa only [List.getElem?_drop] using ha
    have hat : (input.map enc)[base + n]? = some (enc a) := by
      simp only [List.getElem?_map, ha, Option.map_some]
    have htake : (input.drop base).take (n + 1) = (input.drop base).take n ++ [a] := by
      rw [List.take_add_one, had]; rfl
    let z := preparedRun e enc R rate x₀ ((input.drop base).take n)
    have hzstate : z.state = ((z.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩) :=
      Prod.ext (Prod.ext rfl hlocal) hglobal
    have hzeta : { state := ((z.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := z.tape } = z := by
      rw [← hzstate]
    have hnext : preparedRun e enc R rate x₀ ((input.drop base).take (n + 1)) =
        (TextFeedSchedule.machine e enc R rate).sRound z a := by
      rw [htake]
      simp only [preparedRun, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    have hstep := frame_step hcode hmb hk hv hend hstart hblank hmark
      (show base + n < (input.map enc).length by simpa only [List.length_map] using hn')
      enc a hat z.state.1.1 z.tape old hsim hcounter
    dsimp only at hstep ⊢
    rw [hnext]
    refine ⟨enc a, ?_⟩
    simpa only [onlineWorkFrom, hat, Option.getD_some, hzeta, Nat.add_assoc] using hstep

set_option maxHeartbeats 800000 in
theorem preparedRun_offset_deadline {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v : List (Fin k)} {R rate p₁ rem base : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (enc : Terminal → Fin k) (input : List Terminal)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc)
    (hK : KSimple v rate p₁ rem) (hR : workRate rate ≤ R)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {x₀ : Phys e R rate} {old₀ : Fin k}
    (h₀ : Sim e v (input.map enc) R rate p₁ rem base M₀ ph₀ x₀ old₀)
    (hcounter₀ : x₀.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (hc₀ : workScale rate * ((rate + 1) * base) ≤ workCredit v rate (M₀, ph₀))
    (hs₀ : ScanInv v (input.map enc) M₀.st)
    {i n : ℕ} (hn : base + n < input.length) (hocc : OccAt v (input.map enc) i)
    (hpos₀ : M₀.st.pos ≤ i) (hd : i + v.length = base + n + 1)
    (a : Terminal) (ha : input[base + n]? = some a) :
    let z := preparedRun e enc R rate x₀ ((input.drop base).take n)
    let captured : Phys e R rate :=
      (z.state.1.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) z.tape)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      stageSymbols (fun t =>
        (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j + 1] captured).2 t).focus)
        GSTapes.tP = e.endSym := by
  obtain ⟨old, hsim, hcounter, _, _⟩ := preparedRun_offset_refine hcode hmb hk hv hend hstart
    enc input hblank hmark h₀ hcounter₀ n (by omega)
  have hat : (input.map enc)[base + n]? = some (enc a) := by
    simp only [List.getElem?_map, ha, Option.map_some]
  have hw : WorkInv e v (input.map enc) rate p₁ rem base (M₀, ph₀) :=
    ⟨h₀.reference, h₀.work⟩
  exact offset_frame_deadline (base := base) (n := n) hcode hmb hk hv hend hstart hblank hmark
    (by simpa only [List.length_map] using hn) hK hR enc a hat
    hw hc₀ hs₀ hsim hcounter hocc hpos₀ hd

/-- info: 'PalPeg.TextFeedRefine.preparedRun_offset_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preparedRun_offset_deadline

end PalPeg.TextFeedRefine
