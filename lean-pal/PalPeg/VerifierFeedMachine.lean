import PalPeg.VerifierFeedPrimitive
import PalPeg.ProgLangCallFrame

/-! A finite controller executes a verifier source program one bounded
call at a time. The source cannot observe the middle of a Txt2 fill. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedMachine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.VerifierFeed PalPeg.VerifierFeedShared

variable {k : ℕ} {Terminal : Type}

abbrev Source := Prog GSVProg.Act10 GSVProg.Cond10
abbrev Index := Fin (Fintype.card GSVProg.Act10)

noncomputable def encode (a : GSVProg.Act10) : Index := Fintype.equivFin _ a
noncomputable def decode (a : Index) : GSVProg.Act10 := (Fintype.equivFin _).symm a
@[simp] theorem decode_encode (a : GSVProg.Act10) : decode (encode a) = a := Equiv.symm_apply_apply _ _

def idle : GSVProg.Act10 := (GSVProg.tU, true, .stay)

noncomputable def programs (e : Env k) (i : Index) := VerifierFeedPrimitive.low e (decode i)

noncomputable def interp (e : Env k) :
    InterpF Terminal (VerifierFeedShared.Act k) (VerifierFeedShared.Cond k) (Fin k) 21 where
  toInterp := shared e
  flagOf _ := none

def sourceCond (e : Env k) (σ : Fin 21 → Fin k) : GSVProg.Cond10 → Bool :=
  fun c => GSVProg.condOf10 e.endSym e.mark e.startSym c (fun j => σ (verifierSlot j))

noncomputable def choose (e : Env k) (p : Source) (c : CtrlS p) (σ : Fin 21 → Fin k) :
    CtrlS p × Index :=
  (stepCtrlS p (sourceCond e σ) c, encode ((stepStack (sourceCond e σ) c.val).2.getD idle))

noncomputable def run (e : Env k) (p : Source) :=
  callRun (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e p) 49 e.blank

noncomputable local instance : DecidableEq (VerifierFeedShared.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (VerifierFeedShared.Cond k) := Classical.decEq _
noncomputable local instance (p : Source) : DecidableEq (CtrlS p) := Classical.decEq _

/-- Fifty physical microsteps per source action, independent of the
pattern and input lengths. Real arrivals will be separate enqueue calls. -/
noncomputable def machine (e : Env k) (p : Source) :=
  callMachine (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e p) 49 e.blank
    (by omega : 0 < 21) (startCtrlS p) (encode idle)

def modelCond (e : Env k) (M : VMachine' k) : GSVProg.Cond10 → Bool :=
  fun c => GSVProg.condOf10 e.endSym e.mark e.startSym c (fun j => (GSVProg.vTS M.vt j).focus)

noncomputable def modelStep (e : Env k) (p : Source) (z : CtrlS p × VMachine' k) :
    CtrlS p × VMachine' k :=
  (stepCtrlS p (modelCond e z.2) z.1,
    VerifierFeedPrimitive.effect e ((stepStack (modelCond e z.2) z.1.val).2.getD idle) z.2)

theorem sourceCond_bundle (e : Env k) (qt : QT k) (m : Mode) (M : VMachine' k) :
    sourceCond e (fun j => (bundle e qt m M j).focus) = modelCond e M := by
  have hh : (fun j => (bundle e qt m M (verifierSlot j)).focus) =
      (fun j => (GSVProg.vTS M.vt j).focus) := by
    funext j
    fin_cases j <;> rfl
  funext c
  change GSVProg.condOf10 e.endSym e.mark e.startSym c _ =
    GSVProg.condOf10 e.endSym e.mark e.startSym c _
  rw [hh]

theorem run_refine {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (p : Source) (x : CallCtrl (programs e) (CtrlS p) × (Fin 21 → STape (Fin k)))
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (hx : x.2 = bundle e qt m M) (hb : AtBoundary (programs e) x.1.2.2.1)
    (h : Ready e.blank e.mark qt m M.Q2) (henc : Encodes e.blank e.mark M.R2.qt M.Q2) :
    let z := modelStep e p (x.1.1, M)
    let y := run (Terminal := Terminal) e p x
    ∃ qt' m', y.1.1 = z.1 ∧ y.2 = bundle e qt' m' z.2 ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ Ready e.blank e.mark qt' m' z.2.Q2 ∧
      Encodes e.blank e.mark z.2.R2.qt z.2.Q2 := by
  let a := (stepStack (modelCond e M) x.1.1.val).2.getD idle
  have hs : decode (choose e p x.1.1 (fun j => (x.2 j).focus)).2 = a := by
    rw [hx]
    simp only [choose, sourceCond_bundle, decode_encode]
    rfl
  obtain ⟨tr, qt', m', he, hn, ht, hr, henc'⟩ := VerifierFeedPrimitive.low_matches
    (Terminal := Terminal) hc hmb h henc a
  have he' : Exec (interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e p x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (shared e) e.blank (VerifierFeedPrimitive.low e (decode _)) x.2 tr
    rw [hs, hx]
    exact he
  obtain ⟨hout, hb', _, _⟩ := callRun_exec (programs e) (fun _ => interp (Terminal := Terminal) e)
    (choose e p) 49 e.blank x hb tr he' (by omega)
  rw [hx, ht] at hout
  refine ⟨qt', m', ?_, hout, hb', hr, henc'⟩
  change (choose e p x.1.1 (fun j => (x.2 j).focus)).1 = _
  rw [hx]
  simp only [choose, sourceCond_bundle, modelStep]

/-- The model is proof data only: the actual machine stores CtrlS p
and the bounded-call bank. No whole tape or unbounded FIFO is inspected
when choosing the next instruction. -/
theorem run_refine_iterate {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (p : Source) (x : CallCtrl (programs e) (CtrlS p) × (Fin 21 → STape (Fin k)))
    {qt : QT k} {m : Mode} {M : VMachine' k}
    (hx : x.2 = bundle e qt m M) (hb : AtBoundary (programs e) x.1.2.2.1)
    (h : Ready e.blank e.mark qt m M.Q2) (henc : Encodes e.blank e.mark M.R2.qt M.Q2) (N : ℕ) :
    let z := (modelStep e p)^[N] (x.1.1, M)
    let y := (run (Terminal := Terminal) e p)^[N] x
    ∃ qt' m', y.1.1 = z.1 ∧ y.2 = bundle e qt' m' z.2 ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ Ready e.blank e.mark qt' m' z.2.Q2 ∧
      Encodes e.blank e.mark z.2.R2.qt z.2.Q2 := by
  induction N generalizing x qt m M with
  | zero => exact ⟨qt, m, rfl, hx, hb, h, henc⟩
  | succ N ih =>
    obtain ⟨qt', m', hc', ht', hb', hr', he'⟩ := run_refine (Terminal := Terminal) hc hmb p x hx hb h henc
    have hh := ih ((run (Terminal := Terminal) e p) x) ht' hb' hr' he'
    rw [hc'] at hh
    simpa only [Function.iterate_succ_apply, Prod.mk.eta] using hh

theorem machine_blocks (e : Env k) (p : Source) (N : ℕ)
    (x : CallCtrl (programs e) (CtrlS p) × (Fin 21 → STape (Fin k))) :
    (List.replicate (N * 50) none).foldl (machine (Terminal := Terminal) e p).sMicroStep
      { state := (x.1, ⟨0, by omega⟩), tape := x.2 } =
      let y := (run (Terminal := Terminal) e p)^[N] x
      { state := (y.1, ⟨0, by omega⟩), tape := y.2 } :=
  callMachine_noneBlocks (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e p)
    49 e.blank (by omega) (startCtrlS p) (encode idle) N x

/-- info: 'PalPeg.VerifierFeedMachine.machine_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_blocks

/-- info: 'PalPeg.VerifierFeedMachine.run_refine_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refine_iterate

end PalPeg.VerifierFeedMachine
