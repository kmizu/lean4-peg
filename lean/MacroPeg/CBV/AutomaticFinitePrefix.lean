import MacroPeg.CBV.FinitePrefixMachines

namespace Shallot.MacroPeg.CBV.AutomaticFinitePrefix
open FinitePrefixControl (Prefix outputs)
open FinitePrefixMachines (Word Size machine read finish)
open GuardedFinitePrefix (compile atom look guard choose)
open GuardedReplayControl (Expr)

/-- All literal offsets inspected by CPS, including tests in failed branches
and inside negation. Successful outputs alone would omit such offsets. -/
def support : Prefix → List Char → List (List Char)
  | .lit w,u => [u,u++w]
  | .query _,u => [u]
  | .seq a b,u => support a u ++ (outputs a).flatMap (fun v => support b (u++v))
  | .alt a b,u => support a u++support b u
  | .notP a,u => u::support a u

theorem output_supported : ∀ e u v, v∈outputs e → u++v∈support e u
  | .lit w,u,v,hv => by obtain rfl := List.mem_singleton.mp hv; simp [support]
  | .query _,u,v,hv | .notP _,u,v,hv => by
    obtain rfl := List.mem_singleton.mp hv; simp [support]
  | .seq a b,u,v,hv => by
    obtain ⟨v1,h1,h2⟩ := List.mem_flatMap.mp hv
    obtain ⟨v2,hv2,rfl⟩ := List.mem_map.mp h2
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨v1,h1,by
      simpa [List.append_assoc] using output_supported b (u++v1) v2 hv2⟩)
  | .alt a b,u,v,hv => by
    rcases List.mem_append.mp hv with hv | hv
    · exact List.mem_append_left _ (output_supported a u v hv)
    · exact List.mem_append_right _ (output_supported b u v hv)

theorem prefix_checked (alphabet : List Char) (words : List (List Char)) : ∀ e u,
    support e u⊆words → GuardedFinitePrefix.checkAt (read alphabet words) (finish words) e u=true
  | .lit w,u,h => Bool.and_eq_true_iff.mpr
      ⟨(FinitePrefixMachines.read_checked alphabet words u (h (by simp [support]))).1,
       (FinitePrefixMachines.read_checked alphabet words (u++w) (h (by simp [support]))).1⟩
  | .query _,u,h => Bool.and_eq_true_iff.mpr
      ⟨(FinitePrefixMachines.read_checked alphabet words u (h (by simp [support]))).1,
       (FinitePrefixMachines.finish_checked alphabet words u (h (by simp [support]))).1⟩
  | .seq a b,u,h => Bool.and_eq_true_iff.mpr
      ⟨prefix_checked alphabet words a u (fun _ hv => h (List.mem_append_left _ hv)),
       List.all_eq_true.mpr (fun v hv => prefix_checked alphabet words b (u++v)
         (fun w hw => h (List.mem_append_right _ (List.mem_flatMap.mpr ⟨v,hv,hw⟩))))⟩
  | .alt a b,u,h => Bool.and_eq_true_iff.mpr
      ⟨prefix_checked alphabet words a u (fun _ hv => h (List.mem_append_left _ hv)),
       prefix_checked alphabet words b u (fun _ hv => h (List.mem_append_right _ hv))⟩
  | .notP a,u,h => Bool.and_eq_true_iff.mpr
      ⟨(FinitePrefixMachines.read_checked alphabet words u (h List.mem_cons_self)).1,
       prefix_checked alphabet words a u (fun v hv => h (List.mem_cons_of_mem _ hv))⟩

theorem atom_checked (alphabet : List Char) (words : List (List Char)) (e : Prefix)
    (h : support e []⊆words) : GuardedFinitePrefix.atomCheck (read alphabet words) (finish words) e=true :=
  Bool.and_eq_true_iff.mpr ⟨prefix_checked alphabet words e [] h,
    List.all_eq_true.mpr (fun v hv => (FinitePrefixMachines.finish_checked alphabet words v
      (h (by simpa using output_supported e [] v hv))).1)⟩

/-- The three finite frontend obligations, before any actual recursive run. -/
def Good {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char)
    (c : GuardedReplayControl.Expr n) : Prop :=
  GuardedReplayControl.check M c=true ∧
  AlphabetCaptureProfiles.literalCheck alphabet (RecursiveScannerProductCompiler.rawControlArg c)=true ∧
  ∀ P∈AlphabetCaptureProfiles.domain (DynamicScannerCapture.observer M) alphabet,
    GuardedReplayControl.captureCheck P c=true

theorem good_seq {n : Nat} {M : StatefulScanner.Machine n} {alphabet : List Char}
    {a b : GuardedReplayControl.Expr n} (ha : Good M alphabet a) (hb : Good M alphabet b) :
    Good M alphabet (.seq a b) :=
  ⟨Bool.and_eq_true_iff.mpr ⟨ha.1,hb.1⟩,Bool.and_eq_true_iff.mpr ⟨ha.2.1,hb.2.1⟩,
    fun P hP => Bool.and_eq_true_iff.mpr ⟨ha.2.2 P hP,hb.2.2 P hP⟩⟩

theorem good_alt {n : Nat} {M : StatefulScanner.Machine n} {alphabet : List Char}
    {a b : GuardedReplayControl.Expr n} (ha : Good M alphabet a) (hb : Good M alphabet b) :
    Good M alphabet (.alt a b) :=
  ⟨Bool.and_eq_true_iff.mpr ⟨ha.1,hb.1⟩,Bool.and_eq_true_iff.mpr ⟨ha.2.1,hb.2.1⟩,
    fun P hP => Bool.and_eq_true_iff.mpr ⟨ha.2.2 P hP,hb.2.2 P hP⟩⟩

theorem good_not {n : Nat} {M : StatefulScanner.Machine n} {alphabet : List Char}
    {a : GuardedReplayControl.Expr n} (ha : Good M alphabet a) : Good M alphabet (.notP a) := ha

theorem good_star {n : Nat} {M : StatefulScanner.Machine n} {alphabet : List Char}
    {a : GuardedReplayControl.Expr n} (ha : Good M alphabet a) : Good M alphabet (.star a) := ha

theorem good_guard {n : Nat} {M : StatefulScanner.Machine n} {alphabet : List Char}
    {a b : GuardedReplayControl.Expr n} (ha : Good M alphabet a) (hb : Good M alphabet b) :
    Good M alphabet (guard a b) := good_seq (good_not (good_not ha)) hb

theorem good_choose {n : Nat} {M : StatefulScanner.Machine n} {alphabet : List Char}
    {a b c : GuardedReplayControl.Expr n} (ha : Good M alphabet a) (hb : Good M alphabet b)
    (hc : Good M alphabet c) : Good M alphabet (choose a b c) :=
  good_alt (good_guard ha hb) (good_guard (good_not ha) hc)

private theorem literal_word (alphabet u : List Char) (hw : Word alphabet u) :
    AlphabetCaptureProfiles.literalCheck alphabet (.lit u)=true :=
  List.all_eq_true.mpr (fun c hc => List.contains_iff_mem.mpr (hw c hc))

theorem read_good (alphabet : List Char) (words : List (List Char))
    (hw : ∀ w∈words, Word alphabet w) (u : List Char) (hu : u∈words) :
    Good (machine alphabet words) alphabet (read alphabet words u) := by
  refine ⟨(FinitePrefixMachines.read_checked alphabet words u hu).2,?_,?_⟩
  · simpa [FinitePrefixMachines.read,RecursiveScannerProductCompiler.rawControlArg,
      FinitePrefixMachines.read_label words u hu,AlphabetCaptureProfiles.literalCheck] using literal_word alphabet u (hw u hu)
  · intro P hP
    obtain ⟨w,hw,rfl⟩ := AlphabetCaptureProfiles.generated _ (DynamicScannerCapture.observer_valid _) alphabet P hP
    exact FinitePrefixMachines.read_capture alphabet words u w hw

theorem finish_good (alphabet : List Char) (words : List (List Char))
    (hw : ∀ w∈words, Word alphabet w) (u : List Char) (hu : u∈words) :
    Good (machine alphabet words) alphabet (finish words u) := by
  refine ⟨(FinitePrefixMachines.finish_checked alphabet words u hu).2,?_,
    fun P _ => FinitePrefixMachines.finish_capture words u P⟩
  by_cases hn : u=[]
  · simp [finish,hn,RecursiveScannerProductCompiler.rawControlArg,AlphabetCaptureProfiles.literalCheck]
  · simpa [finish,hn,RecursiveScannerProductCompiler.rawControlArg,
      FinitePrefixMachines.finish_label words u hu hn,AlphabetCaptureProfiles.literalCheck]
      using literal_word alphabet u (hw u hu)

theorem compile_good (alphabet : List Char) (words : List (List Char))
    (hw : ∀ w∈words, Word alphabet w) : ∀ e u,
    support e u⊆words → ∀ K,
    (∀ v∈outputs e, Good (machine alphabet words) alphabet (K (u++v))) →
    Good (machine alphabet words) alphabet (compile (read alphabet words) (finish words) e u K)
  | .lit w,u,hs,K,hK => good_guard
      (read_good alphabet words hw (u++w) (hs (by simp [support])))
      (hK w (by simp [outputs]))
  | .query positive,u,hs,K,hK => by
    have hh := finish_good alphabet words hw u (hs (by simp [support]))
    have hk := hK [] (by simp [outputs])
    simp only [List.append_nil] at hk
    cases positive
    · exact good_guard (good_not hh) hk
    · exact good_guard hh hk
  | .seq a b,u,hs,K,hK => by
    apply compile_good alphabet words hw a u (fun v hv => hs (List.mem_append_left _ hv))
    intro v hv
    apply compile_good alphabet words hw b (u++v)
      (fun w hw => hs (List.mem_append_right _ (List.mem_flatMap.mpr ⟨v,hv,hw⟩)))
    intro w hw
    simpa [List.append_assoc] using hK (v++w)
      (List.mem_flatMap.mpr ⟨v,hv,List.mem_map.mpr ⟨w,hw,rfl⟩⟩)
  | .alt a b,u,hs,K,hK => by
    have ha : support a u⊆words := fun v hv => hs (List.mem_append_left _ hv)
    have hb : support b u⊆words := fun v hv => hs (List.mem_append_right _ hv)
    exact good_choose
      (compile_good alphabet words hw a u ha _ (fun v hv => read_good alphabet words hw _ (ha (output_supported a u v hv))))
      (compile_good alphabet words hw a u ha K (fun v hv => hK v (List.mem_append_left _ hv)))
      (compile_good alphabet words hw b u hb K (fun v hv => hK v (List.mem_append_right _ hv)))
  | .notP a,u,hs,K,hK => by
    have ha : support a u⊆words := fun v hv => hs (List.mem_cons_of_mem _ hv)
    have hk := hK [] (by simp [outputs])
    simp only [List.append_nil] at hk
    exact good_guard (good_not (compile_good alphabet words hw a u ha _
      (fun v hv => read_good alphabet words hw _ (ha (output_supported a u v hv))))) hk


/-- Source control has no state indices or residual annotations. -/
inductive Control where
  | finite (e : Prefix)
  | retain
  | seq (a b : Control)
  | alt (a b : Control)
  | notP (a : Control)
  | star (a : Control)

def controlSupport : Control → List (List Char)
  | .finite e => support e []
  | .retain => []
  | .seq a b | .alt a b => controlSupport a++controlSupport b
  | .notP a | .star a => controlSupport a

def annotate (alphabet : List Char) (words : List (List Char)) : Control → GuardedFinitePrefix.Control (Size words)
  | .finite e => .finite e
  | .retain => .ready .replayQuery
  | .seq a b => .seq (annotate alphabet words a) (annotate alphabet words b)
  | .alt a b => .alt (annotate alphabet words a) (annotate alphabet words b)
  | .notP a => .notP (annotate alphabet words a)
  | .star a => .star (annotate alphabet words a)

def normalized (alphabet : List Char) (words : List (List Char)) (c : Control) :=
  GuardedFinitePrefix.normalize (read alphabet words) (finish words) (annotate alphabet words c)

theorem control_checked (alphabet : List Char) (words : List (List Char)) : ∀ c,
    controlSupport c⊆words →
    GuardedFinitePrefix.controlCheck (read alphabet words) (finish words) (annotate alphabet words c)=true
  | .finite e,h => atom_checked alphabet words e h
  | .retain,_ => rfl
  | .seq a b,h | .alt a b,h => Bool.and_eq_true_iff.mpr
      ⟨control_checked alphabet words a (fun _ hv => h (List.mem_append_left _ hv)),
       control_checked alphabet words b (fun _ hv => h (List.mem_append_right _ hv))⟩
  | .notP a,h | .star a,h => control_checked alphabet words a h

theorem normalized_good (alphabet : List Char) (words : List (List Char))
    (hw : ∀ w∈words, Word alphabet w) : ∀ c,
    controlSupport c⊆words → Good (machine alphabet words) alphabet (normalized alphabet words c)
  | .finite e,h => compile_good alphabet words hw e [] h _
      (fun v hv => finish_good alphabet words hw _ (h (output_supported e [] v hv)))
  | .retain,_ => ⟨rfl,rfl,fun _ _ => rfl⟩
  | .seq a b,h => good_seq
      (normalized_good alphabet words hw a (fun _ hv => h (List.mem_append_left _ hv)))
      (normalized_good alphabet words hw b (fun _ hv => h (List.mem_append_right _ hv)))
  | .alt a b,h => good_alt
      (normalized_good alphabet words hw a (fun _ hv => h (List.mem_append_left _ hv)))
      (normalized_good alphabet words hw b (fun _ hv => h (List.mem_append_right _ hv)))
  | .notP a,h => good_not (normalized_good alphabet words hw a h)
  | .star a,h => good_star (normalized_good alphabet words hw a h)

def words (scripts : List Control) : List (List Char) := scripts.flatMap controlSupport

def scriptAt (scripts : List Control) (i : Nat) : Control := scripts[i]?.getD .retain

theorem script_supported (scripts : List Control) (i : Nat) : controlSupport (scriptAt scripts i)⊆words scripts := by
  unfold scriptAt
  cases hs : scripts[i]? with
  | none => intro v hv; cases hv
  | some c => exact fun v hv => List.mem_flatMap.mpr ⟨c,List.mem_of_getElem? hs,hv⟩

def controls (alphabet : List Char) (scripts : List Control) : Nat → GuardedFinitePrefix.Control (Size (words scripts)) :=
  fun i => annotate alphabet (words scripts) (scriptAt scripts i)

open RecursiveScannerProductCompiler (Arg sourceExpr target plain)
open RecursiveCaptureProfiles (scopeCheck)

/-- Only source scope and literal alphabet membership are supplied.
Every observer, residual, and actual-profile frontier check is derived. -/
def check (alphabet : List Char) (scripts : List Control) (bodies : List Arg) : Bool :=
  (words scripts).all (fun w => w.all (fun c => alphabet.contains c)) &&
    bodies.all (fun b => scopeCheck bodies b && AlphabetCaptureProfiles.literalCheck alphabet b)

def source (alphabet : List Char) (scripts : List Control) (bodies : List Arg) : MGrammar :=
  GuardedFinitePrefix.source (machine alphabet (words scripts)) (controls alphabet scripts) bodies

def compiled (alphabet : List Char) (scripts : List Control) (bodies : List Arg) : MGrammar :=
  target (machine alphabet (words scripts))
    (GuardedFinitePrefix.entries (read alphabet (words scripts)) (finish (words scripts)) (controls alphabet scripts)) bodies

theorem certificates (alphabet : List Char) (scripts : List Control) (bodies : List Arg)
    (h : check alphabet scripts bodies=true) :
    GuardedFinitePrefix.check (machine alphabet (words scripts)) (read alphabet (words scripts))
      (finish (words scripts)) (controls alphabet scripts) bodies alphabet=true := by
  obtain ⟨hw,hb⟩ := Bool.and_eq_true_iff.mp h
  have hW : ∀ w∈words scripts, Word alphabet w := fun w hw' c hc =>
    List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp hw) w hw')) c hc)
  refine Bool.and_eq_true_iff.mpr ⟨?_,?_⟩
  · apply List.all_eq_true.mpr
    intro bi _
    exact control_checked alphabet (words scripts) (scriptAt scripts bi.2) (script_supported scripts bi.2)
  · refine Bool.and_eq_true_iff.mpr ⟨FinitePrefixMachines.machine_alphabet alphabet (words scripts) hW,?_⟩
    apply List.all_eq_true.mpr
    intro bi hbi
    obtain ⟨b,i⟩ := bi
    have hbi := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hbi)
    have hB := (List.all_eq_true.mp hb) b hbi
    have hG := normalized_good alphabet (words scripts) hW (scriptAt scripts i) (script_supported scripts i)
    exact Bool.and_eq_true_iff.mpr ⟨hB,Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨hG.1,hG.2.1⟩,List.all_eq_true.mpr hG.2.2⟩⟩

theorem language_translation (alphabet : List Char) (scripts : List Control) (bodies : List Arg)
    (h : check alphabet scripts bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source alphabet scripts bodies) .callByValuePar
        (sourceExpr (machine alphabet (words scripts)) e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  GuardedFinitePrefix.language_translation _ _ _ _ bodies alphabet (certificates alphabet scripts bodies h) e he ha

theorem observations_iff (alphabet : List Char) (scripts : List Control) (bodies : List Arg)
    (h : check alphabet scripts bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source alphabet scripts bodies) .callByValuePar (sourceExpr (machine alphabet (words scripts)) e) x rest ↔
      SObs (compiled alphabet scripts bodies) .callByValueSeq (plain (machine alphabet (words scripts)) bodies [] e) x rest :=
  GuardedFinitePrefix.observations_iff _ _ _ _ bodies alphabet (certificates alphabet scripts bodies h) e he ha x rest

theorem defined_iff (alphabet : List Char) (scripts : List Control) (bodies : List Arg)
    (h : check alphabet scripts bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source alphabet scripts bodies) x .callByValuePar (tblV (source alphabet scripts bodies) x .callByValuePar k)
      [] (sourceExpr (machine alphabet (words scripts)) e) x.length=some v) ↔
    (∃ k, evV (compiled alphabet scripts bodies) x .callByValueSeq (tblV (compiled alphabet scripts bodies) x .callByValueSeq k)
      [] (plain (machine alphabet (words scripts)) bodies [] e) x.length=some v) :=
  GuardedFinitePrefix.defined_iff _ _ _ _ bodies alphabet (certificates alphabet scripts bodies h) e he ha x v

theorem undefined_iff (alphabet : List Char) (scripts : List Control) (bodies : List Arg)
    (h : check alphabet scripts bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (ha : AlphabetCaptureProfiles.literalCheck alphabet e=true) (x : List Char) :
    (∀ k, evV (source alphabet scripts bodies) x .callByValuePar (tblV (source alphabet scripts bodies) x .callByValuePar k)
      [] (sourceExpr (machine alphabet (words scripts)) e) x.length=none) ↔
    (∀ k, evV (compiled alphabet scripts bodies) x .callByValueSeq (tblV (compiled alphabet scripts bodies) x .callByValueSeq k)
      [] (plain (machine alphabet (words scripts)) bodies [] e) x.length=none) :=
  GuardedFinitePrefix.undefined_iff _ _ _ _ bodies alphabet (certificates alphabet scripts bodies h) e he ha x


/-- The capture alphabet is collected from the finite source syntax. -/
def argAlphabet : Arg → List Char
  | .lit w => w
  | .param _ => []
  | .user _ a | .notP a | .star a => argAlphabet a
  | .seq a b | .alt a b => argAlphabet a++argAlphabet b

def alphabet (scripts : List Control) (bodies : List Arg) (root : Arg) : List Char :=
  ((words scripts).flatten ++ bodies.flatMap argAlphabet ++ argAlphabet root).eraseDups

theorem arg_literal_checked (letters : List Char) : ∀ e,
    (∀ c∈argAlphabet e, c∈letters) → AlphabetCaptureProfiles.literalCheck letters e=true
  | .lit w,h => literal_word letters w h
  | .param _,_ => rfl
  | .user _ a,h | .notP a,h | .star a,h => arg_literal_checked letters a h
  | .seq a b,h | .alt a b,h => Bool.and_eq_true_iff.mpr
      ⟨arg_literal_checked letters a (fun c hc => h c (List.mem_append_left _ hc)),
       arg_literal_checked letters b (fun c hc => h c (List.mem_append_right _ hc))⟩

/-- All metadata and alphabet tests succeed once source references are in
scope. No semantic row annotations or observer assignments are parameters. -/
theorem automatic_check (scripts : List Control) (bodies : List Arg) (root : Arg)
    (hb : bodies.all (scopeCheck bodies)=true) : check (alphabet scripts bodies root) scripts bodies=true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_,?_⟩
  · apply List.all_eq_true.mpr
    intro w hw
    apply List.all_eq_true.mpr
    intro c hc
    exact List.contains_iff_mem.mpr (List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatten.mpr ⟨w,hw,hc⟩))))
  · apply List.all_eq_true.mpr
    intro b hB
    refine Bool.and_eq_true_iff.mpr ⟨(List.all_eq_true.mp hb) b hB,?_⟩
    apply arg_literal_checked
    intro c hc
    exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hB,hc⟩)))

theorem root_literal_checked (scripts : List Control) (bodies : List Arg) (root : Arg) :
    AlphabetCaptureProfiles.literalCheck (alphabet scripts bodies root) root=true :=
  arg_literal_checked _ root (fun _ hc => List.mem_eraseDups.mpr (List.mem_append_right _ hc))

theorem automatic_language_translation (scripts : List Control) (bodies : List Arg) (root : Arg)
    (hb : bodies.all (scopeCheck bodies)=true) (he : scopeCheck bodies root=true) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source (alphabet scripts bodies root) scripts bodies) .callByValuePar
        (sourceExpr (machine (alphabet scripts bodies root) (words scripts)) root) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  language_translation _ scripts bodies (automatic_check scripts bodies root hb) root he
    (root_literal_checked scripts bodies root)


def rawControl : Control → MExp
  | .finite e => .seq (FinitePrefixControl.raw e) (.andP (.param 0))
  | .retain => .andP (.param 0)
  | .seq a b => .seq (rawControl a) (rawControl b)
  | .alt a b => .alt (rawControl a) (rawControl b)
  | .notP a => .notP (rawControl a)
  | .star a => .star (rawControl a)

theorem original_annotate (letters : List Char) (pool : List (List Char)) : ∀ c,
    GuardedFinitePrefix.original (annotate letters pool c)=rawControl c
  | .finite _ | .retain => rfl
  | .seq a b | .alt a b => by
    simp only [annotate,GuardedFinitePrefix.original,rawControl,original_annotate letters pool a,original_annotate letters pool b]
  | .notP a | .star a => by
    simp only [annotate,GuardedFinitePrefix.original,rawControl,original_annotate letters pool a]

theorem source_rule (letters : List Char) (scripts : List Control) (bodies : List Arg)
    (i : Nat) (b : Arg) (hi : bodies[i]?=some b) :
    ruleAtM (source letters scripts bodies).rules (RecursiveScannerProductCompiler.offset (machine letters (words scripts))+i)=
      some ⟨1,.seq (.seq (rawControl (scriptAt scripts i)) (.param 0)) (sourceExpr (machine letters (words scripts)) b)⟩ := by
  simpa only [source,controls,original_annotate] using
    GuardedFinitePrefix.source_rule (machine letters (words scripts)) (controls letters scripts) bodies i b hi

end Shallot.MacroPeg.CBV.AutomaticFinitePrefix
