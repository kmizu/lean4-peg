import MacroPeg.CBV.NestedScannerArguments
import MacroPeg.CBV.PrefixFamilyTestFusion

/-! A reverse compiler for independently evaluated, nested greedy scanners.
Source arguments are not cumulative parser expressions. Their runtime
prefix differences are discovered by ordinary consecutive target scans. -/
namespace Shallot.MacroPeg.CBV.NestedScannerFusion
open NestedScannerArguments

def Supported : MExp → Prop
  | .call _ args => ∃ classes : List (List Char), classes.Pairwise Included ∧ args = classes.map scan
  | .seq a b | .alt a b => Supported a ∧ Supported b
  | .star a | .notP a => Supported a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

def source (scope : Nat) : MExp → MExp
  | .param k => if k < scope then .param k else MExp.failAlways
  | .call i args => .call i args
  | .seq a b => .seq (source scope a) (source scope b)
  | .alt a b => .alt (source scope a) (source scope b)
  | .star a => .star (source scope a)
  | .notP a => .notP (source scope a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem source_firstOrder (scope : Nat) : ∀ e, Supported e → (source scope e).FirstOrder
  | .param k, _ => by by_cases hk : k < scope <;> simp [source,hk,MExp.FirstOrder,MExp.failAlways]
  | .call _ args, h => by
    obtain ⟨classes,_,rfl⟩ := h
    have hh : ∀ classes : List (List Char), MExp.FirstOrderArgs (classes.map scan) := by
      intro classes
      induction classes with
      | nil => trivial
      | cons A classes ih => exact ⟨scan_firstOrder A,ih⟩
    exact hh classes
  | .seq a b, h | .alt a b, h => ⟨source_firstOrder scope a h.1,source_firstOrder scope b h.2⟩
  | .star a, h | .notP a, h => source_firstOrder scope a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem render_choice (parallel : Bool) (scope : Nat) (A : List Char) :
    PrefixFamilyFusion.render parallel scope (choice A) = choice A := by
  induction A <;> simp_all [choice,PrefixFamilyFusion.render,MExp.failAlways]

theorem render_scan (parallel : Bool) (scope : Nat) (A : List Char) :
    PrefixFamilyFusion.render parallel scope (scan A) = scan A := by
  simp [scan,PrefixFamilyFusion.render,render_choice]

theorem render_scans (parallel : Bool) (scope : Nat) (classes : List (List Char)) :
    PrefixFamilyFusion.renderArgs parallel scope (classes.map scan) = classes.map scan := by
  induction classes <;> simp_all [PrefixFamilyFusion.renderArgs,render_scan]

theorem scan_arguments_tables (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char))
    (classes : List (List Char)) (p : Nat) (hp : p ≤ x.length) :
    evParArgs g x s T E (classes.map scan) p = evParArgs h x t U E (classes.map scan) p := by
  induction classes with
  | nil => rfl
  | cons A classes ih => simp only [List.map_cons,evParArgs,scan_eval _ _ _ _ _ A p hp,ih]

def parGrammar (rules : List MRule) : MGrammar :=
  ⟨rules.map (fun r => ⟨r.arity,.seq (PrefixFamilyFusion.replay r.arity) (source r.arity r.body)⟩)⟩

theorem par_rule (rules : List MRule) (i : Nat) :
    ruleAtM (parGrammar rules).rules i =
      (rules[i]?).map (fun r => ⟨r.arity,.seq (PrefixFamilyFusion.replay r.arity) (source r.arity r.body)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

theorem par_firstOrder {rules : List MRule} (h : ∀ r ∈ rules, Supported r.body) :
    (parGrammar rules).FirstOrder := by
  intro r hr
  change r ∈ rules.map (fun r => ⟨r.arity,.seq (PrefixFamilyFusion.replay r.arity) (source r.arity r.body)⟩) at hr
  obtain ⟨r,hmem,rfl⟩ := List.mem_map.mp hr
  exact ⟨PrefixFamilyFusion.replay_firstOrder _,source_firstOrder _ _ (h r hmem)⟩

/-- Independent scanner calls and their prefix-factored counterparts agree
under related recursive tables, before taking a fixed point. -/
theorem evaluator_of_tables {rules : List MRule} {x : List Char}
    {T U : Nat → List (List Char) → Val} (hOk : OkTV x.length T)
    (hTable : ∀ i W p, p ≤ x.length → valAt (T i W) p = valAt (U i W) p) :
    ∀ e, Supported e → ∀ scope E p, p ≤ x.length →
      evV (parGrammar rules) x .callByValuePar T E (source scope e) p =
        evV (PrefixFamilyFusion.parGrammar rules) x .callByValuePar U E
          (PrefixFamilyFusion.render true scope e) p
  | .param k, _, scope, E, p, _ => by
    by_cases hk : k < scope <;> simp [source,PrefixFamilyFusion.render,hk,evV,MExp.failAlways]
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _
  | .range _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h
  | .call i args, h, scope, E, p, hp => by
    obtain ⟨classes,hclasses,rfl⟩ := h
    change evV _ _ _ _ _ (.call i (classes.map scan)) p =
      evV _ _ _ _ _ (.call i (PrefixFamilyFusion.parsers
        (PrefixFamilyFusion.renderArgs true scope (classes.map scan)))) p
    rw [render_scans]
    cases hr : rules[i]? with
    | none => simp [evV,par_rule,PrefixFamilyFusion.par_rule,hr]
    | some rule =>
      by_cases ha : rule.arity = (classes.map scan).length
      · have hrp : ruleAtM (parGrammar rules).rules i = some
            ⟨rule.arity,.seq (PrefixFamilyFusion.replay rule.arity) (source rule.arity rule.body)⟩ := by
          rw [par_rule,hr]; rfl
        have hrq : ruleAtM (PrefixFamilyFusion.parGrammar rules).rules i = some
            ⟨rule.arity,.seq (PrefixFamilyFusion.replay rule.arity)
              (PrefixFamilyFusion.render true rule.arity rule.body)⟩ := by
          rw [PrefixFamilyFusion.par_rule,hr]; rfl
        rw [evV_call_par hrp ha (by decide),
          evV_call_par hrq (by simpa [PrefixFamilyFusion.parsers_length] using ha) (by decide),
          independent_arguments _ _ _ _ _ classes hclasses p hp,
          scan_arguments_tables (parGrammar rules) (PrefixFamilyFusion.parGrammar rules) x
            .callByValuePar .callByValuePar T U E classes p hp]
        cases evParArgs (PrefixFamilyFusion.parGrammar rules) x .callByValuePar U E (classes.map scan) p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some W => exact hTable i W p hp
      · have ha' : ¬rule.arity = classes.length := by simpa using ha
        simp [evV,par_rule,PrefixFamilyFusion.par_rule,hr,PrefixFamilyFusion.parsers_length,ha']
  | .seq a b, h, scope, E, p, hp => by
    have heq := evaluator_of_tables (rules := rules) hOk hTable a h.1 scope E p hp
    cases hv : evV (parGrammar rules) x .callByValuePar T E (source scope a) p with
    | none => simp only [source,PrefixFamilyFusion.render,evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some result => cases result with
      | none => simp only [source,PrefixFamilyFusion.render,evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        simp only [source,PrefixFamilyFusion.render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_tables (rules := rules) hOk hTable b h.2 scope E q (evV_ok hOk _ p hp q hv)
  | .alt a b, h, scope, E, p, hp => by
    have heq := evaluator_of_tables (rules := rules) hOk hTable a h.1 scope E p hp
    cases hv : evV (parGrammar rules) x .callByValuePar T E (source scope a) p with
    | none => simp only [source,PrefixFamilyFusion.render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [source,PrefixFamilyFusion.render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_tables (rules := rules) hOk hTable b h.2 scope E p hp
      | some q => simp only [source,PrefixFamilyFusion.render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, h, scope, E, p, hp => by
    simp only [source,PrefixFamilyFusion.render,evV]
    rw [evaluator_of_tables (rules := rules) hOk hTable a h scope E p hp]
  | .star a, h, scope, E, p, hp => by
    simp only [source,PrefixFamilyFusion.render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_tables (rules := rules) hOk hTable a h scope E q (by omega))

theorem source_replay (n : Nat) : source n (PrefixFamilyFusion.replay n) = PrefixFamilyFusion.replay n := by
  cases n <;> simp [source,PrefixFamilyFusion.replay]
theorem render_replay (n : Nat) :
    PrefixFamilyFusion.render true n (PrefixFamilyFusion.replay n) = PrefixFamilyFusion.replay n := by
  cases n <;> simp [PrefixFamilyFusion.render,PrefixFamilyFusion.replay]
theorem replay_supported (n : Nat) : Supported (PrefixFamilyFusion.replay n) := by cases n <;> trivial

theorem tables_eq {rules : List MRule} (h : ∀ r ∈ rules, Supported r.body)
    (x : List Char) (m : Nat) : ∀ i W p, p ≤ x.length →
    valAt (tblV (parGrammar rules) x .callByValuePar m i W) p =
      valAt (tblV (PrefixFamilyFusion.parGrammar rules) x .callByValuePar m i W) p := by
  induction m with
  | zero => intro i W p hp; rfl
  | succ m ih =>
    intro i W p hp
    cases hr : rules[i]? with
    | none => simp [tblV,par_rule,PrefixFamilyFusion.par_rule,hr,valAt_nil]
    | some rule =>
      have hrp : ruleAtM (parGrammar rules).rules i = some
          ⟨rule.arity,.seq (PrefixFamilyFusion.replay rule.arity) (source rule.arity rule.body)⟩ := by
        rw [par_rule,hr]; rfl
      have hrq : ruleAtM (PrefixFamilyFusion.parGrammar rules).rules i = some
          ⟨rule.arity,.seq (PrefixFamilyFusion.replay rule.arity)
            (PrefixFamilyFusion.render true rule.arity rule.body)⟩ := by
        rw [PrefixFamilyFusion.par_rule,hr]; rfl
      rw [valAt_tblV_succ hrp W hp,valAt_tblV_succ hrq W hp]
      have he := evaluator_of_tables (rules := rules) (tblV_ok _ _ _ m) ih
        (.seq (PrefixFamilyFusion.replay rule.arity) rule.body)
        ⟨replay_supported _,h rule (List.mem_of_getElem? hr)⟩ rule.arity W p hp
      simpa only [source,PrefixFamilyFusion.render,source_replay,render_replay] using he


theorem iterBound_eq (rules : List MRule) (x : List Char) :
    iterBoundV (parGrammar rules) x = iterBoundV (PrefixFamilyFusion.parGrammar rules) x := by
  have hlen : (parGrammar rules).rules.length = (PrefixFamilyFusion.parGrammar rules).rules.length := by
    simp [parGrammar,PrefixFamilyFusion.parGrammar]
  unfold iterBoundV
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [par_rule,PrefixFamilyFusion.par_rule]
  cases rules[i]? <;> rfl

theorem decide_eq {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body)
    {e : MExp} (he : Supported e) (x : List Char) :
    decideObsV .callByValuePar (parGrammar rules) x (source 0 e) =
      decideObsV .callByValuePar (PrefixFamilyFusion.parGrammar rules) x
        (PrefixFamilyFusion.render true 0 e) := by
  unfold decideObsV
  have hh := evaluator_of_tables (rules := rules) (tblV_ok _ _ _ _)
    (tables_eq hf x (iterBoundV (parGrammar rules) x)) e he 0 [] x.length (Nat.le_refl _)
  rw [hh,iterBound_eq]

/-- A fixed first-order Seq grammar recognizes exactly the same original
character strings as the independent-scanner Par source, for all inputs. -/
theorem observations_iff {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body)
    {e : MExp} (he : Supported e) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar rules) .callByValuePar (source 0 e) x r ↔
      SObs (PrefixFamilyFusion.seqGrammar rules) .callByValueSeq
        (PrefixFamilyFusion.render false 0 e) x r := by
  have hh : SObs (parGrammar rules) .callByValuePar (source 0 e) x r ↔
      SObs (PrefixFamilyFusion.parGrammar rules) .callByValuePar
        (PrefixFamilyFusion.render true 0 e) x r := by
    rw [← decideObsV_iff (par_firstOrder hf) (by decide) (source_firstOrder 0 e he),
      ← decideObsV_iff (PrefixFamilyFusion.par_firstOrder rules) (by decide)
        (PrefixFamilyFusion.render_firstOrder true 0 e),decide_eq hf he x]
  exact hh.trans (PrefixFamilyFusion.observations_iff rules e x r)

theorem language_translation {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body)
    {e : MExp} (he : Supported e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar rules) .callByValuePar (source 0 e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨PrefixFamilyFusion.seqGrammar rules,PrefixFamilyFusion.render false 0 e,
    PrefixFamilyFusion.seq_firstOrder _,PrefixFamilyFusion.render_firstOrder _ _ _,
    fun x => observations_iff hf he x (some [])⟩


namespace Test

theorem choice_render (A : List Char) : CallLookahead.render (choice A) = choice A := by
  induction A <;> simp_all [choice,CallLookahead.render,MExp.failAlways]

theorem scans_render (classes : List (List Char)) :
    CallLookahead.renderArgs (classes.map scan) = classes.map scan := by
  induction classes <;> simp_all [scan,CallLookahead.renderArgs,CallLookahead.render,choice_render]

theorem supported_render : ∀ e, Supported e → Supported (CallLookahead.render e)
  | .call i args, h => by
    obtain ⟨classes,hclasses,rfl⟩ := h
    simp only [CallLookahead.render,scans_render,MExp.andP,Supported]
    exact ⟨classes,hclasses,rfl⟩
  | .seq a b, h | .alt a b, h => ⟨supported_render a h.1,supported_render b h.2⟩
  | .star a, h | .notP a, h => supported_render a h
  | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem source_commute (scope : Nat) : ∀ e, Supported e →
    CallLookahead.render (source scope e) = source scope (CallLookahead.render e)
  | .call i args, h => by
    obtain ⟨classes,hclasses,rfl⟩ := h
    simp [source,CallLookahead.render,scans_render,MExp.andP]
  | .param k, _ => by
    by_cases hk : k < scope <;> simp [source,hk,CallLookahead.render,MExp.failAlways]
  | .seq a b, h | .alt a b, h => by
    simp only [source,CallLookahead.render]
    rw [source_commute scope a h.1,source_commute scope b h.2]
  | .star a, h | .notP a, h => by
    simp only [source,CallLookahead.render]
    rw [source_commute scope a h]
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem tested_supported {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body) :
    ∀ r ∈ PrefixFamilyTestFusion.testedRules rules, Supported r.body := by
  intro r hr
  change r ∈ rules.map (fun r => ⟨r.arity,CallLookahead.render r.body⟩) at hr
  obtain ⟨r,hmem,rfl⟩ := List.mem_map.mp hr
  exact supported_render r.body (hf r hmem)

theorem wrapped_eq {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body) :
    CallLookahead.wrapped (parGrammar rules) =
      parGrammar (PrefixFamilyTestFusion.testedRules rules) := by
  unfold CallLookahead.wrapped parGrammar PrefixFamilyTestFusion.testedRules
  simp only [List.map_map,Function.comp_def]
  apply congrArg MGrammar.mk
  apply List.map_congr_left
  intro r hr
  simp only [CallLookahead.render]
  rw [source_commute r.arity r.body (hf r hr)]
  have hh : CallLookahead.render (PrefixFamilyFusion.replay r.arity) =
      PrefixFamilyFusion.replay r.arity := by cases r.arity <;> rfl
  rw [hh]

/-- Scanner factorization also works when source calls are tests: captured
values stay bound inside the callee and each caller position is restored. -/
theorem observations_iff {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body)
    {e : MExp} (he : Supported e) (x : List Char) (r : Option (List Char)) :
    SObs (CallLookahead.tested (parGrammar rules)) .callByValuePar (source 0 e) x r ↔
      SObs (PrefixFamilyFusion.seqGrammar (PrefixFamilyTestFusion.testedRules rules)) .callByValueSeq
        (PrefixFamilyFusion.render false 0 (CallLookahead.render e)) x r := by
  have hh := CallLookahead.observations_iff (par_firstOrder hf) (source 0 e)
    (source_firstOrder 0 e he) x r
  rw [wrapped_eq hf,source_commute 0 e he] at hh
  exact hh.trans (NestedScannerFusion.observations_iff (tested_supported hf) (supported_render e he) x r)

theorem language_translation {rules : List MRule} (hf : ∀ r ∈ rules, Supported r.body)
    {e : MExp} (he : Supported e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (CallLookahead.tested (parGrammar rules)) .callByValuePar (source 0 e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨PrefixFamilyFusion.seqGrammar (PrefixFamilyTestFusion.testedRules rules),
    PrefixFamilyFusion.render false 0 (CallLookahead.render e),
    PrefixFamilyFusion.seq_firstOrder _,PrefixFamilyFusion.render_firstOrder _ _ _,
    fun x => observations_iff hf he x (some [])⟩

end Test

end Shallot.MacroPeg.CBV.NestedScannerFusion
