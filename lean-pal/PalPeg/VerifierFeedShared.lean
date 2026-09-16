import PalPeg.VerifierFeedClosed
import PalPeg.GSVerifierProg

/-! Co-locate the closed verifier FIFO and all ten scanner/verifier tapes.
The supply view omits the first text tape and U; it writes only Txt2. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedShared
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.VerifierFeed PalPeg.VerifierFeedClosed

variable {k : ℕ} {Terminal : Type}

/-- In the 19-tape supply view index 12 is the text target. In the
21-tape bundle that target is index 20, the verifier's Txt2. -/
def feedSlot : Fin 19 ↪ Fin 21 where
  toFun j := if j.val = 12 then ⟨20, by omega⟩ else ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    by_cases hi : i.val = 12 <;> by_cases hj : j.val = 12 <;>
      simp only [hi, hj, ↓reduceIte] at hh <;> have := i.isLt <;> have := j.isLt <;> omega

def verifierSlot : Fin 10 ↪ Fin 21 := Fin.natAddEmb 11

def bundle (e : Env k) (qt : QT k) (m : Mode) (M : VMachine' k) : Fin 21 → STape (Fin k) :=
  Fin.append (RTQueueControl.tapes e.code qt m) (GSVProg.vTS M.vt)

theorem bundle_view (e : Env k) (qt : QT k) (m : Mode) (M : VMachine' k) :
    (fun j => bundle e qt m M (feedSlot j)) = TextFeedControl.tapes e qt m (stage M) := by
  funext j
  fin_cases j <;> rfl

theorem omitted_text : proj feedSlot (12 : Fin 21) = none := by
  apply proj_eq_none
  decide

theorem omitted_U : proj feedSlot (19 : Fin 21) = none := by
  apply proj_eq_none
  decide

theorem extend_bundle (e : Env k) (qt qt' : QT k) (m m' : Mode) (M M' : VMachine' k)
    (htext : M'.vt.1 GSTapes.tT = M.vt.1 GSTapes.tT) (hU : M'.vt.2.U = M.vt.2.U) :
    extend feedSlot (TextFeedControl.tapes e qt' m' (stage M')) (bundle e qt m M) =
      bundle e qt' m' M' := by
  funext j
  have hcover : ∀ j : Fin 21, j = 12 ∨ j = 19 ∨ ∃ i, feedSlot i = j := by decide
  rcases hcover j with rfl | rfl | ⟨i, rfl⟩
  · rw [extend_of_proj_none omitted_text]
    change RTQueueProg.toS (M.vt.1 GSTapes.tT) = RTQueueProg.toS (M'.vt.1 GSTapes.tT)
    rw [htext]
  · rw [extend_of_proj_none omitted_U]
    change RTQueueProg.toS M.vt.2.U = RTQueueProg.toS M'.vt.2.U
    rw [hU]
  · rw [extend_ι]
    exact (congrFun (bundle_view e qt' m' M') i).symm

abbrev Act (k : ℕ) := AP k ⊕ GSVProg.Act10
abbrev Cond (k : ℕ) := ((CQ k ⊕ GSProg.Cond8) ⊕ Test) ⊕ GSVProg.Cond10

noncomputable def shared (e : Env k) : Interp Terminal (Act k) (Cond k) (Fin k) 21 where
  actOf
    | .inl a => ((IT e).transport feedSlot).actOf a
    | .inr a => ((GSVProg.I10 e.blank e.endSym e.mark e.startSym).transport verifierSlot).actOf a
  condOf
    | .inl c => ((IT (Terminal := Terminal) e).transport feedSlot).condOf c
    | .inr c => ((GSVProg.I10 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym).transport verifierSlot).condOf c

def liftFeed (p : TP k) : Prog (Act k) (Cond k) := p.map Sum.inl Sum.inl

theorem exec_feed {e : Env k} {p : TP k} {T : Fin 19 → STape (Fin k)}
    {tr : List (Fin 19 → Fin k × Move)}
    (he : Exec (IT (Terminal := Terminal) e) e.blank p T tr) (rest : Fin 21 → STape (Fin k)) :
    Exec (shared (Terminal := Terminal) e) e.blank (liftFeed p) (extend feedSlot T rest)
      (tr.map (extendVec feedSlot rest)) :=
  exec_map (I₂ := shared e) (fa := Sum.inl) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport he feedSlot rest)

theorem run_feed {e : Env k} {p : TP k} {qt qt' : QT k} {m m' : Mode}
    {M M' : VMachine' k} {ticks : ℕ}
    (he : TExec (Terminal := Terminal) e p qt m (stage M) ticks qt' m' (stage M'))
    (htext : M'.vt.1 GSTapes.tT = M.vt.1 GSTapes.tT) (hU : M'.vt.2.U = M.vt.2.U) :
    ∃ tr, Exec (shared (Terminal := Terminal) e) e.blank (liftFeed p) (bundle e qt m M) tr ∧
      tr.length = ticks ∧ applyTrace e.blank (bundle e qt m M) tr = bundle e qt' m' M' := by
  obtain ⟨tr, he, hn, hout⟩ := he
  have hex := exec_feed he (bundle e qt m M)
  have hinit := extend_bundle e qt qt m m M M rfl rfl
  rw [hinit] at hex
  refine ⟨_, hex, by simpa only [List.length_map] using hn, ?_⟩
  have ht := applyTrace_extend feedSlot e.blank (bundle e qt m M) tr (TextFeedControl.tapes e qt m (stage M))
  rw [hinit, hout, extend_bundle e qt qt' m m' M M' htext hU] at ht
  exact ht

/-- All ten verifier/scanner tapes are present throughout this real
48-action block; the first text tape and U are preserved exactly. -/
theorem step_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank
      (liftFeed (stepXR e.blank e.mark)) (bundle e qt m M) tr ∧ tr.length ≤ 48 ∧
      applyTrace e.blank (bundle e qt m M) tr = bundle e qt' m' (vstepXR e.blank e.mark M) ∧
      Ready e.blank e.mark qt' m' (vstepXR e.blank e.mark M).Q2 := by
  obtain ⟨ticks, qt', m', hn, he, hr⟩ := VerifierFeedClosed.step_matches (Terminal := Terminal) hc hmb h hb
  obtain ⟨tr, he, ht, hout⟩ := run_feed he
    (congrFun (vstepXR_vt1 e.blank e.mark M) GSTapes.tT) (vstepXR_U e.blank e.mark M)
  exact ⟨tr, qt', m', he, ht ▸ hn, hout, hr⟩

theorem step_safe {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VMachine' k} {Text : List (Fin k)} {n i : ℕ}
    (h : Ready e.blank e.mark qt m M.Q2)
    (htxt : Txt2Inv e.blank e.mark Text n M i) (hok : Ok2 n M i)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hnext : i + 1 ≤ n) :
    ∃ tr qt' m', Exec (shared (Terminal := Terminal) e) e.blank
      (liftFeed (stepXR e.blank e.mark)) (bundle e qt m M) tr ∧ tr.length ≤ 48 ∧
      applyTrace e.blank (bundle e qt m M) tr = bundle e qt' m' (vstepXR e.blank e.mark M) ∧
      Ready e.blank e.mark qt' m' (vstepXR e.blank e.mark M).Q2 ∧
      Txt2Inv e.blank e.mark Text n (vstepXR e.blank e.mark M) (i + 1) ∧
      Ok2 n (vstepXR e.blank e.mark M) (i + 1) := by
  obtain ⟨tr, qt', m', he, hlen, ht, hr⟩ := step_matches (Terminal := Terminal) hc hmb h htxt.buf
  exact ⟨tr, qt', m', he, hlen, ht, hr, vstepXR_inv hmb hblank hmark hn htxt hok hnext⟩

/-- info: 'PalPeg.VerifierFeedShared.step_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_safe

/-- info: 'PalPeg.VerifierFeedShared.step_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_matches

end PalPeg.VerifierFeedShared
