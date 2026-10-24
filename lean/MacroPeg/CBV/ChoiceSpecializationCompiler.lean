import MacroPeg.CBV.ChoiceSpecialization

/-! Input-independent palette collection for ordered choices of literals and
forwarded values. Captures may depend on the original input. -/
namespace Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler
open ChoiceArguments ChoiceSpecialization
open LiteralSpecialization (specs)

def Atom : MExp → Prop
  | .lit _ | .param _ => True
  | .alt a b => Atom a ∧ Atom b
  | _ => False

def Shape : MExp → Prop
  | .call _ args => ∀ a ∈ args, Atom a
  | .seq a b | .alt a b => Shape a ∧ Shape b
  | .star a | .notP a => Shape a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

def collectArg : MExp → List (List Char)
  | .lit w => [w]
  | .alt a b => collectArg a ++ collectArg b
  | _ => []

def collect : MExp → List (List Char)
  | .call _ args => args.flatMap collectArg
  | .seq a b | .alt a b => collect a ++ collect b
  | .star a | .notP a => collect a
  | _ => []

theorem arg_mono {V W : List (List Char)} (h : ∀ w ∈ V, w ∈ W) :
    ∀ a, Arg V a → Arg W a
  | .lit w, ha => h w ha
  | .param _, _ => trivial
  | .alt a b, ha => ⟨arg_mono h a ha.1,arg_mono h b ha.2⟩
  | .eps, ha | .any, ha | .chr _, ha | .range _ _, ha | .call _ _, ha | .seq _ _, ha
  | .star _, ha | .notP _, ha | .dbg _, ha | .lam _ _, ha | .callParam _ _, ha | .invoke _ _ _, ha => False.elim ha

theorem collectArg_supported : ∀ a, Atom a → Arg (collectArg a) a
  | .lit w, _ => by simp [Arg,collectArg]
  | .param _, _ => trivial
  | .alt a b, ha =>
    ⟨arg_mono (fun _ hw => List.mem_append_left _ hw) a (collectArg_supported a ha.1),
      arg_mono (fun _ hw => List.mem_append_right _ hw) b (collectArg_supported b ha.2)⟩
  | .eps, ha | .any, ha | .chr _, ha | .range _ _, ha | .call _ _, ha | .seq _ _, ha
  | .star _, ha | .notP _, ha | .dbg _, ha | .lam _ _, ha | .callParam _ _, ha | .invoke _ _ _, ha => False.elim ha

theorem supported_mono {V W : List (List Char)} (h : ∀ w ∈ V, w ∈ W) :
    ∀ e, Supported V e → Supported W e
  | .call _ _, he => by intro a ha; exact arg_mono h a (he a ha)
  | .seq a b, he | .alt a b, he => ⟨supported_mono h a he.1,supported_mono h b he.2⟩
  | .star a, he | .notP a, he => supported_mono h a he
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .dbg _, he | .lam _ _, he | .callParam _ _, he | .invoke _ _ _, he => False.elim he

theorem collect_supported : ∀ e, Shape e → Supported (collect e) e
  | .call _ args, he => by
    intro a ha
    apply arg_mono (V := collectArg a) _ a (collectArg_supported a (he a ha))
    intro w hw
    exact List.mem_flatMap.mpr ⟨a,ha,hw⟩
  | .seq a b, he | .alt a b, he =>
    ⟨supported_mono (fun w hw => List.mem_append_left _ hw) a (collect_supported a he.1),
      supported_mono (fun w hw => List.mem_append_right _ hw) b (collect_supported b he.2)⟩
  | .star a, he | .notP a, he => collect_supported a he
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .dbg _, he | .lam _ _, he | .callParam _ _, he | .invoke _ _ _, he => False.elim he

def GrammarShape (g : MGrammar) : Prop := ∀ r ∈ g.rules, Shape r.body

def palette (g : MGrammar) (e : MExp) : List (List Char) :=
  g.rules.flatMap (fun r => collect r.body) ++ collect e

def translate (g : MGrammar) (e : MExp) : MGrammar := target g (palette g e)
def start (g : MGrammar) (e : MExp) : MExp := compile g (specs g (palette g e)) [] e

theorem grammar_supported {g : MGrammar} (hg : GrammarShape g) (e : MExp) :
    GrammarSupported (palette g e) g := by
  intro r hr
  apply supported_mono (V := collect r.body) _ r.body (collect_supported r.body (hg r hr))
  intro w hw
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨r,hr,hw⟩)

theorem root_supported (g : MGrammar) {e : MExp} (he : Shape e) : Supported (palette g e) e :=
  supported_mono (fun _ hw => List.mem_append_right _ hw) e (collect_supported e he)

theorem translate_firstOrder (g : MGrammar) (e : MExp) : (translate g e).FirstOrder := target_firstOrder _ _
theorem start_firstOrder (g : MGrammar) (e : MExp) : (start g e).FirstOrder := compile_firstOrder _ _ _ _

/-- This is a fixed finite Seq grammar computed from the source syntax alone.
The original body need not begin by replaying any captured parameter. -/
theorem observations_iff {g : MGrammar} (hg : GrammarShape g) {e : MExp} (he : Shape e)
    (x : List Char) (r : Option (List Char)) :
    SObs g .callByValuePar e x r ↔ SObs (translate g e) .callByValueSeq (start g e) x r :=
  ChoiceSpecialization.observations_iff (grammar_supported hg e) (root_supported g he) x r

theorem language_translation {g : MGrammar} (hg : GrammarShape g) {e : MExp} (he : Shape e) :
    ∃ (out : MGrammar) (entry : MExp), out.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs g .callByValuePar e x (some []) ↔ SObs out .callByValueSeq entry x (some []) :=
  ⟨translate g e,start g e,translate_firstOrder g e,start_firstOrder g e,
    fun x => observations_iff hg he x (some [])⟩

end Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler
