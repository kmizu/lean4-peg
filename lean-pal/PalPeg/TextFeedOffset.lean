import PalPeg.TextFeedPhysicalDeadline

/-! Streaming service from a real, nonzero arrival count. Previously
buffered symbols remain in M₀; only subsequent arrivals are enqueued. -/
set_option autoImplicit false

namespace PalPeg.TextFeedRefine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule PalPeg.TextFeedScan

variable {k : ℕ} {Terminal : Type}
variable {e : Env k} {v Text : List (Fin k)} {rate p₁ rem base : ℕ}

noncomputable def onlineWorkFrom (e : Env k) (v Text : List (Fin k))
    (R rate p₁ rem base : ℕ) (M₀ : TextFeed.Machine' k) (ph₀ : Phase) :
    ℕ → TextFeed.Machine' k × Phase
  | 0 => (M₀, ph₀)
  | n + 1 =>
    let z := onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n
    modelRun e v Text rate p₁ rem (base + n + 1) R
      (TextFeed.arrive' e.blank e.mark (Text[base + n]?.getD e.blank) z.1) z.2

theorem onlineWorkFrom_credit (hk : 0 < rate) (hp : 0 < p₁) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) {R : ℕ} (hR : workRate rate ≤ R)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase}
    (h₀ : WorkInv e v Text rate p₁ rem base (M₀, ph₀))
    (hc₀ : workScale rate * ((rate + 1) * base) ≤ workCredit v rate (M₀, ph₀))
    (n : ℕ) (hn : base + n ≤ Text.length) :
    let z := onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n
    WorkInv e v Text rate p₁ rem (base + n) z ∧
      workScale rate * ((rate + 1) * (base + n)) ≤ workCredit v rate z := by
  induction n with
  | zero => exact ⟨h₀, hc₀⟩
  | succ n ih =>
    obtain ⟨hi, hc⟩ := ih (by omega)
    have hn' : base + n < Text.length := by omega
    have ha : Text[base + n]? = some (Text[base + n]?.getD e.blank) := by
      simp only [List.getElem?_eq_getElem hn', Option.getD_some]
    exact frame_work_credit hk hp hmb hv hend hstart hblank hn' hR ha hi hc

theorem onlineWorkFrom_scanInv (hK : KSimple v rate p₁ rem) (R : ℕ)
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} (h₀ : ScanInv v Text M₀.st) (n : ℕ) :
    ScanInv v Text (onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n).1.st := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact modelRun_scanInv hK R ih

theorem onlineWorkFrom_no_skip_before (hk : 0 < rate) (hmb : e.mark ≠ e.blank)
    (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hK : KSimple v rate p₁ rem)
    {R : ℕ} (hR : workRate rate ≤ R) {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {i : ℕ}
    (h₀ : WorkInv e v Text rate p₁ rem base (M₀, ph₀))
    (hc₀ : workScale rate * ((rate + 1) * base) ≤ workCredit v rate (M₀, ph₀))
    (hs₀ : ScanInv v Text M₀.st) (hocc : OccAt v Text i) (hpos₀ : M₀.st.pos ≤ i)
    (n : ℕ) (hn : base + n ≤ Text.length) (hbefore : base + n < i + v.length) :
    (onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n).1.st.pos ≤ i := by
  induction n with
  | zero => exact hpos₀
  | succ n ih =>
    have hn' : base + n < Text.length := by omega
    have ha : Text[base + n]? = some (Text[base + n]?.getD e.blank) := by
      simp only [List.getElem?_eq_getElem hn', Option.getD_some]
    have hi := (onlineWorkFrom_credit hk hK.period_pos hmb hv hend hstart hblank hR
      h₀ hc₀ n (by omega)).1
    have hiA := arrive_workInv hmb hn' ha hi
    have hs := onlineWorkFrom_scanInv (e := e) (base := base) (ph₀ := ph₀) hK R hs₀ n
    have hp := ih (by omega) (by omega)
    apply modelRun_no_skip (M := TextFeed.arrive' e.blank e.mark (Text[base + n]?.getD e.blank)
      (onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n).1) hK hk R hs hocc hp
    intro j hj
    exact workInv_not_hit_before
      (modelRun_workInv hk hmb hv hend hstart hblank hn j hiA) hbefore

/-- Startup credit is paid once at the actual starting count. Subsequent
physical deadline windows need no fresh credit or no-skipping assumption. -/
theorem offset_frame_deadline (hcode : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {R n : ℕ} (hk : 0 < rate) (hv : 0 < v.length)
    (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : base + n < Text.length)
    (hK : KSimple v rate p₁ rem) (hR : workRate rate ≤ R)
    (enc : Terminal → Fin k) (a : Terminal) (ha : Text[base + n]? = some (enc a))
    {M₀ : TextFeed.Machine' k} {ph₀ : Phase} {x : Phys e R rate} {old : Fin k} {i : ℕ}
    (h₀ : WorkInv e v Text rate p₁ rem base (M₀, ph₀))
    (hc₀ : workScale rate * ((rate + 1) * base) ≤ workCredit v rate (M₀, ph₀))
    (hs₀ : ScanInv v Text M₀.st)
    (h : Sim e v Text R rate p₁ rem (base + n)
      (onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n).1
      (onlineWorkFrom e v Text R rate p₁ rem base M₀ ph₀ n).2 x old)
    (hcounter : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    (hocc : OccAt v Text i) (hpos₀ : M₀.st.pos ≤ i) (hd : i + v.length = base + n + 1) :
    let captured : Phys e R rate :=
      (x.1, ProgLangPersist2.arriveA e.blank (capture enc) (some a) x.2)
    ∃ j, 1 ≤ j ∧ j ≤ R ∧
      stageSymbols (fun t =>
        (((TextFeedSchedule.run (Terminal := Terminal) e R rate)^[j + 1] captured).2 t).focus)
        GSTapes.tP = e.endSym := by
  have hs := onlineWorkFrom_scanInv (e := e) (base := base) (ph₀ := ph₀) hK R hs₀ n
  have hpos := onlineWorkFrom_no_skip_before hk hmb hv hend hstart hblank hK hR
    h₀ hc₀ hs₀ hocc hpos₀ n (by omega) (by omega)
  have hc := (onlineWorkFrom_credit hk hK.period_pos hmb hv hend hstart hblank hR
    h₀ hc₀ n (by omega)).2
  exact frame_deadline hcode hmb hk hv hend hstart hblank hmark hn hK hR enc a ha
    h hcounter hs hocc hpos hd hc

/-- info: 'PalPeg.TextFeedRefine.offset_frame_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms offset_frame_deadline

end PalPeg.TextFeedRefine
