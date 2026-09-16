import PalPeg.TextFeedPipelineInputRun
import PalPeg.TextFeedPipelineMacroBoundary

/-! A return located inside a real input sequence restores the next GS
macro invariant at that very physical endpoint and arrival frontier. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineInputMacro
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineInputRun PalPeg.TextFeedPipelineMacroBoundary PalPeg.GSVerifierZ
variable {k : ℕ} {Terminal : Type}

structure Start (e : Env k) (Text leftPat rightPat : List (Fin k))
    (rate p r n : ℕ) (u : Snapshot k) (z : VStateZ) : Prop where
  feed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
    leftPat rightPat Text rate p r n u.model
  ghost : u.model.z = (z.1, z.2.head)
  wf : ZWf leftPat.length z.2
  direction : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0
  code : u.frames = [.code (GSVProgZLoop.stepProg rate)]

/-- Symbol-separation and positive-parameter conditions. The finite-word
fit condition is derived from the actual completed execution, not assumed. -/
structure Conditions (e : Env k) (Text leftPat rightPat : List (Fin k))
    (rate p r : ℕ) (z : VStateZ) : Prop where
  mark_blank : e.mark ≠ e.blank
  blank_text : e.blank ∉ Text
  mark_text : e.mark ∉ Text
  positive_rate : 0 < rate
  positive_p : 0 < p
  start_right : e.startSym ∉ rightPat
  end_right : e.endSym ∉ rightPat
  end_left : e.endSym ∉ leftPat
  start_left : e.startSym ∉ leftPat
  start_end : e.startSym ≠ e.endSym

def Restored (e : Env k) (leftSym : Fin k) (R rate : ℕ) (Text leftPat rightPat : List (Fin k))
    (p r n : ℕ) (x : Config e leftSym R rate) (v : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (z : VStateZ) : Prop :=
  (next (taskEval e (fun j => (x.2 j).focus)) v.frames).2 = .halt ∧
    Valid e leftSym R rate Text n x (annotate v z) caller ∧
    VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n (annotate v z).model ∧
    ZWf leftPat.length z.2 ∧
    (annotate v z).dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0 ∧
    (annotate v z).model.z = (z.1, z.2.head)

def Returned (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (Text leftPat rightPat : List (Fin k)) (p r n : ℕ) (as : List Terminal)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (z : VStateZ) : Prop :=
  ∃ pre a post m v ws, as = pre ++ a :: post ∧ m < R ∧ ws.length = R * pre.length + m ∧
    let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
      (captured e leftSym R rate enc a (frames e leftSym R rate enc pre x))
    Follows e u ws v ∧
    Restored e leftSym R rate Text leftPat rightPat p r (n + pre.length + 1) y v caller
      (vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z)

theorem return_boundary {e : Env k} (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {z : VStateZ} {as : List Terminal}
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller)
    (hs : Start e Text leftPat rightPat rate p r n u z)
    (hc : Conditions e Text leftPat rightPat rate p r z)
    (hn : n + as.length ≤ Text.length)
    (hret : ReturnsIn e leftSym R rate enc Text n as x u caller) :
    Returned e leftSym R rate enc Text leftPat rightPat p r n as x u caller z := by
  obtain ⟨pre, a, post, m, v, ws, hsplit, hmR, hlen, hv, ht, hhalt⟩ := hret
  have hfront : n + pre.length + 1 ≤ Text.length := by
    rw [hsplit, List.length_append, List.length_cons] at hn
    omega
  refine ⟨pre, a, post, m, v, ws, hsplit, hmR, hlen, ht, ?_⟩
  refine ⟨hhalt, ?_⟩
  exact compiled_boundary leftSym R rate x _ u v caller hu hv hs.feed hs.ghost
    hc.mark_blank hc.blank_text hc.mark_text hfront ht hhalt hc.positive_rate hc.positive_p
    hc.start_right hc.end_right hc.end_left hc.start_left hc.start_end hs.wf hs.direction hs.code

/-- No termination premise: if the macro returns in these inputs, its
next streaming invariant is recovered; otherwise the full prefix has
actually been executed and still refines the GS interpreter. -/
theorem frames_macro {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {z : VStateZ} (as : List Terminal)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller)
    (hs : Start e Text leftPat rightPat rate p r n u z)
    (hc : Conditions e Text leftPat rightPat rate p r z)
    (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false) :
    (∃ v ws, Valid e leftSym R rate Text (n + as.length)
      (frames e leftSym R rate enc as x) v caller ∧ Follows e u ws v ∧ ws.length = R * as.length) ∨
    Returned e leftSym R rate enc Text leftPat rightPat p r n as x u caller z := by
  rcases frames_or_return hcode hc.mark_blank leftSym R rate enc hc.blank_text hc.mark_text
    as hn ha x u caller hu hz hfirst with hfull | hret
  · exact Or.inl hfull
  · exact Or.inr (return_boundary leftSym R rate enc x u caller hu hs hc hn hret)

/-- info: 'PalPeg.TextFeedPipelineInputMacro.frames_macro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_macro

end PalPeg.TextFeedPipelineInputMacro
