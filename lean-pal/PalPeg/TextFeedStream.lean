import PalPeg.TextFeedPhysicalDeadline

/-! Continuous real-input execution from a prepared feeder configuration.
This is deliberately distinct from constructing that configuration on blank tapes. -/
set_option autoImplicit false

namespace PalPeg.TextFeedRefine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (Outer R rate) := Classical.decEq _

noncomputable def preparedRun (e : Env k) (enc : Terminal → Fin k) (R rate : ℕ)
    (x : Phys e R rate) (input : List Terminal) :=
  input.foldl (TextFeedSchedule.machine e enc R rate).sRound
    { state := ((x.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := x.2 }

/-- One initial Sim suffices for every prefix of the actual input stream;
there is no independent per-round simulation assumption. -/
theorem preparedRun_refine {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v : List (Fin k)} {R rate p₁ rem : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (enc : Terminal → Fin k) (input : List Terminal)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {x₀ : Phys e R rate} {old₀ : Fin k}
    (h₀ : Sim e v (input.map enc) R rate p₁ rem 0 M₀ ph₀ x₀ old₀)
    (hcounter₀ : x₀.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (n : ℕ) (hn : n ≤ input.length) :
    let z := preparedRun e enc R rate x₀ (input.take n)
    let m := onlineWork e v (input.map enc) R rate p₁ rem M₀ ph₀ n
    ∃ old, Sim e v (input.map enc) R rate p₁ rem n m.1 m.2 (z.state.1.1, z.tape) old ∧
      z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  induction n with
  | zero => exact ⟨old₀, h₀, hcounter₀, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨old, hsim, hcounter, hlocal, hglobal⟩ := ih (by omega)
    have hn' : n < input.length := by omega
    let a := input[n]
    have ha : input[n]? = some a := List.getElem?_eq_getElem hn'
    have hat : (input.map enc)[n]? = some (enc a) := by simp only [List.getElem?_map, ha, Option.map_some]
    have htake : input.take (n + 1) = input.take n ++ [a] := by
      rw [List.take_add_one, ha]; rfl
    let z := preparedRun e enc R rate x₀ (input.take n)
    have hzstate : z.state = ((z.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩) :=
      Prod.ext (Prod.ext rfl hlocal) hglobal
    have hzeta : { state := ((z.state.1.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := z.tape } = z := by
      rw [← hzstate]
    have hnext : preparedRun e enc R rate x₀ (input.take (n + 1)) =
        (TextFeedSchedule.machine e enc R rate).sRound z a := by
      rw [htake]
      simp only [preparedRun, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    have hstep := frame_step hcode hmb hk hv hend hstart hblank hmark
      (show n < (input.map enc).length by simpa only [List.length_map] using hn')
      enc a hat z.state.1.1 z.tape old hsim hcounter
    dsimp only at hstep ⊢
    rw [hnext]
    refine ⟨enc a, ?_⟩
    simpa only [onlineWork, hat, Option.getD_some, hzeta] using hstep

/-- A single prepared initial configuration gives physical deadline
reports throughout the complete real input stream. No assumed per-round
credit, simulation, or no-skipping invariant remains in the premises. -/
theorem preparedRun_deadline {e : Env k} (hcode : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {v : List (Fin k)} {R rate p₁ rem : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (enc : Terminal → Fin k) (input : List Terminal)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc)
    (hK : KSimple v rate p₁ rem) (hR : workRate rate ≤ R)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {x₀ : Phys e R rate} {old₀ : Fin k}
    (h₀ : Sim e v (input.map enc) R rate p₁ rem 0 M₀ ph₀ x₀ old₀)
    (hcounter₀ : x₀.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {i n : ℕ} (hn : n < input.length) (hocc : OccAt v (input.map enc) i)
    (hd : i + v.length = n + 1) (a : Terminal) (ha : input[n]? = some a) :
    let z := preparedRun e enc R rate x₀ (input.take n)
    let captured : Phys e R rate :=
      (z.state.1.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) z.tape)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      stageSymbols (fun t =>
        (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j + 1] captured).2 t).focus)
        GSTapes.tP = e.endSym := by
  obtain ⟨old, hsim, hcounter, _, _⟩ := preparedRun_refine hcode hmb hk hv hend hstart
    enc input hblank hmark h₀ hcounter₀ n (by omega)
  have hwork₀ : WorkInv e v (input.map enc) rate p₁ rem 0 (M₀, ph₀) := ⟨h₀.reference, h₀.work⟩
  have hq₀ : M₀.st.q = 0 := by
    have hh : M₀.st.pos + M₀.st.q ≤ M₀.m := h₀.reference.hd
    have hm : M₀.m ≤ 0 := h₀.reference.mle
    omega
  have hs₀ : ScanInv v (input.map enc) M₀.st := by
    refine ⟨?_, h₀.reference.qle⟩
    rw [hq₀]
    exact matchLen_zero _ _ _
  have hpos₀ : M₀.st.pos ≤ i := by
    have hh : M₀.st.pos + M₀.st.q ≤ M₀.m := h₀.reference.hd
    have hm : M₀.m ≤ 0 := h₀.reference.mle
    omega
  have hat : (input.map enc)[n]? = some (enc a) := by simp only [List.getElem?_map, ha, Option.map_some]
  exact online_frame_deadline hcode hmb hk hv hend hstart hblank hmark
    (by simpa only [List.length_map] using hn) hK hR enc a hat hwork₀ hs₀
    hsim hcounter hocc hpos₀ hd

/-- info: 'PalPeg.TextFeedRefine.preparedRun_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preparedRun_refine

/-- info: 'PalPeg.TextFeedRefine.preparedRun_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preparedRun_deadline

end PalPeg.TextFeedRefine
