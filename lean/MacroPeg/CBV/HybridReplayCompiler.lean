import MacroPeg.CBV.HybridReplayFusion

/-! Collect only the finite flags from source syntax. The runtime head capture
is deliberately excluded from the palette and has no global length bound. -/
namespace Shallot.MacroPeg.CBV.HybridReplayCompiler
open HybridReplayFusion

def FlagShape : MExp → Prop
  | .lit _ | .param (_+1) => True
  | _ => False

def Shape (d : Nat) : MExp → Prop
  | .call _ (a::args) => args.length=d ∧ Shape d a ∧ ∀ b ∈ args, FlagShape b
  | .call _ [] => False
  | .seq a b | .alt a b => Shape d a ∧ Shape d b
  | .star a | .notP a => Shape d a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

def collect : MExp → List (List Char)
  | .call _ (a::args) => collect a ++ args.filterMap (fun b => match b with | .lit w => some w | _ => none)
  | .seq a b | .alt a b => collect a ++ collect b
  | .star a | .notP a => collect a
  | _ => []

theorem supported_of_shape {d : Nat} {V : List (List Char)} :
    ∀ e, Shape d e → (∀ w ∈ collect e, w ∈ V) → Supported d V e
  | .call _ (a::args), he, hc => by
    refine ⟨he.1,supported_of_shape a he.2.1 (fun w hw => hc w (List.mem_append_left _ hw)),?_⟩
    intro b hb
    have hs := he.2.2 b hb
    cases b with
    | lit w => exact hc w (List.mem_append_right _ (List.mem_filterMap.mpr ⟨.lit w,hb,rfl⟩))
    | param k => cases k; exact False.elim hs; trivial
    | _ => exact False.elim hs
  | .seq a b, he, hc | .alt a b, he, hc =>
    ⟨supported_of_shape a he.1 (fun w hw => hc w (List.mem_append_left _ hw)),
      supported_of_shape b he.2 (fun w hw => hc w (List.mem_append_right _ hw))⟩
  | .star a, he, hc | .notP a, he, hc => supported_of_shape a he hc
  | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ | .param _, _, _ => trivial
  | .call _ [], he, _ | .dbg _, he, _ | .lam _ _, he, _ | .callParam _ _, he, _ | .invoke _ _ _, he, _ => False.elim he

def palette (tails : List MExp) (e : MExp) : List (List Char) := tails.flatMap collect ++ collect e

def translate (d : Nat) (tails : List MExp) (e : MExp) : MGrammar := seqGrammar d (palette tails e) tails
def start (d : Nat) (tails : List MExp) (e : MExp) : MExp := compile d (palette tails e) tails [] e

theorem tails_supported {d : Nat} {tails : List MExp} (hf : ∀ body ∈ tails, Shape d body) (e : MExp) :
    ∀ body ∈ tails, Supported d (palette tails e) body := by
  intro body hb
  exact supported_of_shape body (hf body hb) (fun w hw => List.mem_append_left _ (List.mem_flatMap.mpr ⟨body,hb,hw⟩))

theorem root_supported {d : Nat} (tails : List MExp) {e : MExp} (he : Shape d e) :
    Supported d (palette tails e) e := supported_of_shape e he (fun _ hw => List.mem_append_right _ hw)

theorem translate_firstOrder (d : Nat) (tails : List MExp) (e : MExp) : (translate d tails e).FirstOrder :=
  seq_firstOrder _ _ _
theorem start_firstOrder (d : Nat) (tails : List MExp) (e : MExp) : (start d tails e).FirstOrder :=
  compile_firstOrder _ _ _ _ _

theorem observations_iff {d : Nat} {tails : List MExp} (hf : ∀ body ∈ tails, Shape d body)
    {e : MExp} (he : Shape d e) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar d tails) .callByValuePar e x r ↔
      SObs (translate d tails e) .callByValueSeq (start d tails e) x r :=
  HybridReplayFusion.observations_iff (tails_supported hf e) (root_supported tails he) x r

theorem language_translation {d : Nat} {tails : List MExp} (hf : ∀ body ∈ tails, Shape d body)
    {e : MExp} (he : Shape d e) :
    ∃ (out : MGrammar) (entry : MExp), out.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (parGrammar d tails) .callByValuePar e x (some []) ↔
        SObs out .callByValueSeq entry x (some []) :=
  ⟨translate d tails e,start d tails e,translate_firstOrder _ _ _,start_firstOrder _ _ _,
    fun x => observations_iff hf he x (some [])⟩

/-- Duplication is allowed in the dynamic head argument; the finite palette
is imposed only on the second argument, not on the growing captured word. -/
theorem duplication_shape : Shape 1 (.call 0 [.seq (.param 0) (.param 0),.param 1]) := by
  simp [Shape,FlagShape]

end Shallot.MacroPeg.CBV.HybridReplayCompiler
