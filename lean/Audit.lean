import Shallot.Peg.Separation.CBVSeqSpace
import Shallot.Basic
import Shallot.Data.RBVerify
import Shallot.Data.RBBalance
import Shallot.Lang.TypeCheckVerify
import Shallot.Lang.EvalLemmas
import Shallot.Opt.ConstFoldVerify
import Shallot.Lang.TypeSound
import Shallot.Vm.Correct
import Shallot.Syntax.Roundtrip
import Json.Roundtrip
import Shallot.Peg.Props
import Shallot.Peg.Fuel
import Shallot.Peg.Soundness
import Shallot.Peg.Determinism
import Shallot.Peg.Completeness
import Shallot.Peg.Examples
import Shallot.Peg.Palindrome
import Shallot.Peg.PowerTwoHelper
import Shallot.Peg.PalindromeEpsFirst
import Shallot.Peg.PalindromeEpsMiddle
import Shallot.Peg.PalindromeAllOrders
import Shallot.Peg.MidPoint
import Shallot.Peg.MidPointGeneral
import Shallot.Peg.PalindromeGeneral
import Shallot.Peg.PalindromeGeneralN
import Shallot.Peg.MidpointObstruction
import Shallot.Peg.GrammarExtend
import MacroPeg
import Cfg
import Complexity
import Shallot
import Shallot.Peg.Separation.MacroStrict
import Shallot.Peg.Separation.CBVStrict
import Shallot.Peg.Separation.CBVStrategies
import MacroPeg.CBV.Decide
import MacroPeg.CBV.Address
import MacroPeg.CBV.SpanCost
import MacroPeg.CBV.TableRead
import MacroPeg.CBV.SpanBuild
import MacroPeg.CBV.MirrorBuild
import MacroPeg.CBV.ParamMachine
import MacroPeg.CBV.ControlMachine
import MacroPeg.CBV.CallFrames
import MacroPeg.CBV.PositionSweep
import MacroPeg.CBV.SequentialParamPackedMachine
import MacroPeg.CBV.SequentialEightTapeMachine
import MacroPeg.CBV.SequentialActiveDispatchMachine
import MacroPeg.CBV.SequentialPackedLoopMachine
import Shallot.Peg.Separation.CBVSeqLinearSpace

/-!
# Axiom audit

Every flagship theorem must depend on nothing beyond the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — ideally fewer. `#guard_msgs`
turns any drift (a stray axiom or unproven hole) into a **build failure**,
so `lake build` itself is the audit.

Add one `#guard_msgs in #print axioms <theorem>` block per flagship theorem.
-/

/-- info: 'Shallot.hello_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.hello_length

/-! ## PEG framework (M4): T0–T3 + P1 -/

/-- info: 'Shallot.pegRun_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.pegRun_mono

/-- info: 'Shallot.derives_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.derives_suffix

/-- info: 'Shallot.pegRun_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.pegRun_sound

/-- info: 'Shallot.derives_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.derives_det

/-- info: 'Shallot.pegRun_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.pegRun_complete

/-! ## RBMap (M6): order theory, BST invariant, model refinement, balance -/

/-- info: 'Shallot.cmpStr_lt_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.cmpStr_lt_trans

/-- info: 'Shallot.RBNode.ordered_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBNode.ordered_insert

/-- info: 'Shallot.RBNode.find_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBNode.find_insert

/-- info: 'Shallot.RBNode.find_fromList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBNode.find_fromList

/-- info: 'Shallot.RBBalance.rb_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.RBBalance.rb_insert

/-! ## Typechecker (M6): soundness and completeness -/

/-- info: 'Shallot.typecheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.typecheck_sound

/-- info: 'Shallot.typecheck_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.typecheck_complete

/-- info: 'Shallot.checkProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.checkProgram_sound

/-- info: 'Shallot.checkProgram_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.checkProgram_complete

/-! ## Interpreter + optimizer (M8, part 1): L4, O1, O2 -/

/-- info: 'Shallot.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.eval_mono

/-- info: 'Shallot.optExpr_hasType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.optExpr_hasType

/-- info: 'Shallot.optExpr_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.optExpr_eval

/-! ## Type soundness + program-level optimizer preservation (M8, part 2) -/

/-- info: 'Shallot.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.eval_sound

/-- info: 'Shallot.runProgram_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.runProgram_sound

/-- info: 'Shallot.optProgram_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.optProgram_run

/-! ## Compiler correctness (M10) — the flagship -/

/-- info: 'Shallot.vmRun_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.vmRun_mono

/-- info: 'Shallot.compile_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.compile_sim

/-- info: 'Shallot.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.compile_correct

/-! ## Parser roundtrip + pipeline composition (M11) — the closing theorems -/

/-- info: 'Shallot.derives_printExpr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.derives_printExpr

/-- info: 'Shallot.derives_printProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.derives_printProgram

/-- info: 'Shallot.parse_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.parse_print

/-- info: 'Shallot.pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.pipeline_correct

/-! ## Verified JSON parser (J-series) — RFC 8259 roundtrip -/

/-- info: 'Shallot.Json.derives_printJson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Json.derives_printJson

/-- info: 'Shallot.Json.parse_print_json' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Json.parse_print_json

/-! ## Macro PEG (M-PEG / M-PEG-2): call-by-name + call-by-value-par — T0–T3 -/

/-- info: 'Shallot.MacroPeg.mpegRun_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mpegRun_mono

/-- info: 'Shallot.MacroPeg.mderives_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mderives_suffix

/-- info: 'Shallot.MacroPeg.mpegRun_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mpegRun_sound

/-- info: 'Shallot.MacroPeg.mderives_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mderives_det

/-- info: 'Shallot.MacroPeg.mpegRun_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mpegRun_complete

/-- info: 'Shallot.MacroPeg.copy_language_ww' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.copy_language_ww

/-! ## T1: plain PEG embeds into arity-0 Macro PEG (both directions) -/

/-- info: 'Shallot.MacroPeg.peg_embed_complete' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.peg_embed_complete

/-- info: 'Shallot.MacroPeg.peg_embed_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.peg_embed_sound

/-! ## `aⁿbⁿcⁿ` — a non-context-free language a plain PEG recognizes -/

/-- info: 'Shallot.S_char' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.S_char

/-! ## T2: GNF CFG embeds into arity-1 Macro PEG (both directions) -/

/-- info: 'Shallot.Cfg.cfg_cps_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfg_cps_complete

/-- info: 'Shallot.Cfg.cfg_cps_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfg_cps_sound

/-! ## T3: `CFL ⊊ MPEL^CBN_1` — the language-hierarchy theorem -/

/-- info: 'Shallot.Cfg.cfl_proper_subset_mpel1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfl_proper_subset_mpel1

/-! ## T7: `CFL ⊆ PEL` — the settled half (`PEL ⊄ CFL`); the other
direction is an open problem, documented not proved (`Cfg/OpenProblems.lean`) -/

/-- info: 'Shallot.Cfg.abc_isPEL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.abc_isPEL

/-- info: 'Shallot.Cfg.pel_not_subset_cfl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.pel_not_subset_cfl

/-! ## T7 evidence: the textbook palindrome CFG, read literally as a plain
PEG, is sound but incomplete (`Shallot/Peg/Palindrome.lean`) -/

/-- info: 'Shallot.exists_palindrome_palGrammar_rejects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.exists_palindrome_palGrammar_rejects

/-- info: 'Shallot.palGrammar_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.palGrammar_sound

/-- info: 'Shallot.palGrammar_accepts_only_palindromes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.palGrammar_accepts_only_palindromes

/-! ## T7 evidence, positive side: Loff–Moreira–Reis's Theorem 8 mechanism
(`Shallot/Peg/PowerTwoHelper.lean`) -/

/-- info: 'Shallot.helper_consumption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.helper_consumption

/-- info: 'Shallot.helper_full_on_power_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.helper_full_on_power_of_two

/-! ## T7 evidence, another natural construction tried: eps-first priority
order rejects every non-empty input (`Shallot/Peg/PalindromeEpsFirst.lean`) -/

/-- info: 'Shallot.palEpsFirst_rejects_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.palEpsFirst_rejects_nonempty

/-! ## T7 evidence, a third priority order tried: eps-middle makes an
alternative structurally unreachable (`Shallot/Peg/PalindromeEpsMiddle.lean`) -/

/-- info: 'Shallot.palEpsMiddle_rejects_bb' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.palEpsMiddle_rejects_bb

/-! ## T7 evidence: complete classification of all 6 priority orders of the
peel-both-ends family (`Shallot/Peg/PalindromeAllOrders.lean`) -/

/-- info: 'Shallot.all_six_peel_orders_incomplete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.all_six_peel_orders_incomplete

/-! ## T7 evidence: even a midpoint-only requirement (no end-matching)
already breaks this construction style (`Shallot/Peg/MidPoint.lean`) -/

/-- info: 'Shallot.midGrammar_rejects_bab' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.midGrammar_rejects_bab

/-! ## T7 theorem: PEG cannot locate the midpoint, quantified over every
2-letter alphabet (`Shallot/Peg/MidPointGeneral.lean`) -/

/-- info: 'Shallot.genMid_rejects_c1c0c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.genMid_rejects_c1c0c1

/-! ## T7: `palGrammar`'s incompleteness generalized over any alphabet
(`Shallot/Peg/PalindromeGeneral.lean`) and any alphabet SIZE
(`Shallot/Peg/PalindromeGeneralN.lean`) -/

/-- info: 'Shallot.genPal_rejects_c0c0c0c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.genPal_rejects_c0c0c0c0

/-- info: 'Shallot.genPalN_rejects_c0c0c0c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.genPalN_rejects_c0c0c0c0

/-! ## T7: the sharpest general (grammar-shape-agnostic) form of the
midpoint obstruction (`Shallot/Peg/MidpointObstruction.lean`) -/

/-- info: 'Shallot.no_suffix_only_midpoint_decider' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.no_suffix_only_midpoint_decider

/-! ## T7: routing around Ford's empty-string restriction on predicate
elimination (`Shallot/Peg/GrammarExtend.lean`, `Cfg/NonemptyReduction.lean`) -/

/-- info: 'Shallot.Cfg.isPEL_nonemptyRestriction_of_isPEL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.isPEL_nonemptyRestriction_of_isPEL

/-- info: 'Shallot.Cfg.not_isPEL_evenPalindromes_of_not_isPEL_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.not_isPEL_evenPalindromes_of_not_isPEL_nonempty

/-- info: 'Shallot.Cfg.evenPalindromes_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.Cfg.evenPalindromes_nil

/-! ## Counterexample corpus (CE-001, CE-002 — Lean side; CE-003 is Scala-only,
see `MacroPeg/Counterexamples.lean`'s module docstring) -/

/-- info: 'Shallot.MacroPeg.ce001_callByName' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_callByName

/-- info: 'Shallot.MacroPeg.ce001_callByValueSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_callByValueSeq

/-- info: 'Shallot.MacroPeg.ce001_callByValuePar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_callByValuePar

/-- info: 'Shallot.MacroPeg.ce001_strategies_disagree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce001_strategies_disagree

/-- info: 'Shallot.MacroPeg.selfCall_loop_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.selfCall_loop_none

/-- info: 'Shallot.MacroPeg.selfCallDiverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.selfCallDiverges

/-! ## M-PEG-6: macro expansion preserves call-by-name semantics (`MacroPeg/ExpandSemantics.lean`)

`expand_preserves_cbn` is the headline (T-exp); `expand_agrees_cbn` adds determinism,
`expand_preserves_cbn_run` is the fuel-interpreter reading, `expandGrammar_preserves_start`
the whole-grammar/start-rule form `ParserGenerator` relies on. CE-004/005/006 are the
machine-checked witnesses for the `subst` fix and for the two side conditions. -/

/-- info: 'Shallot.MacroPeg.subst_subst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.subst_subst

/-- info: 'Shallot.MacroPeg.expand_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expand_subst

/-- info: 'Shallot.MacroPeg.expand_preserves_cbn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expand_preserves_cbn

/-- info: 'Shallot.MacroPeg.expand_agrees_cbn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expand_agrees_cbn

/-- info: 'Shallot.MacroPeg.expand_preserves_cbn_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expand_preserves_cbn_run

/-- info: 'Shallot.MacroPeg.expandGrammar_preserves_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expandGrammar_preserves_start

/-- info: 'Shallot.MacroPeg.ce004_passThrough_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce004_passThrough_eval

/-- info: 'Shallot.MacroPeg.ce004_passThrough_expanded_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce004_passThrough_expanded_eval

/-- info: 'Shallot.MacroPeg.ce005_arity_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce005_arity_eval

/-- info: 'Shallot.MacroPeg.ce005_arity_expanded_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce005_arity_expanded_eval

/-- info: 'Shallot.MacroPeg.ce005_arity_not_arityOk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce005_arity_not_arityOk

/-- info: 'Shallot.MacroPeg.ce006_closureReturn_not_noCallableRules' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce006_closureReturn_not_noCallableRules

/-! ## Macro PEG properties: finite specialization (A), argument equivalence (B), strategies (C), reachable (D) -/

/-- info: 'Shallot.MacroPeg.macroObs_iff_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.macroObs_iff_run

/-- info: 'Shallot.MacroPeg.pegObs_iff_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.pegObs_iff_run

/-- info: 'Shallot.MacroPeg.FGrammar.wfB_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.wfB_sound

/-- info: 'Shallot.MacroPeg.FGrammar.validVecB_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.validVecB_sound

/-- info: 'Shallot.MacroPeg.length_vecs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.length_vecs

/-- info: 'Shallot.MacroPeg.mem_vecs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mem_vecs

/-- info: 'Shallot.MacroPeg.FGrammar.mem_specs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.mem_specs

/-- info: 'Shallot.MacroPeg.FGrammar.length_specs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.length_specs

/-- info: 'Shallot.MacroPeg.FGrammar.specs_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specs_code

/-- info: 'Shallot.MacroPeg.FGrammar.validVec_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.validVec_call

/-- info: 'Shallot.MacroPeg.FGrammar.specialize_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specialize_size

/-- info: 'Shallot.MacroPeg.FGrammar.specialize_size_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specialize_size_le

/-- info: 'Shallot.MacroPeg.codeOn_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.codeOn_inj

/-- info: 'Shallot.MacroPeg.FGrammar.specializeOn_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specializeOn_decode

/-- info: 'Shallot.MacroPeg.FGrammar.specializeOn_selfContained' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specializeOn_selfContained

/-- info: 'Shallot.MacroPeg.FGrammar.specialize_selfContained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specialize_selfContained

/-- info: 'Shallot.MacroPeg.FGrammar.specs_specSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.specs_specSet

/-- info: 'Shallot.MacroPeg.FGrammar.entryNt_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.entryNt_lt

/-- info: 'Shallot.MacroPeg.subst_embedExp_any' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.subst_embedExp_any

/-- info: 'Shallot.MacroPeg.rel_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rel_spec

/-- info: 'Shallot.MacroPeg.spec_preserve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.spec_preserve

/-- info: 'Shallot.MacroPeg.spec_reflect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.spec_reflect

/-- info: 'Shallot.MacroPeg.rel_obs_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rel_obs_iff

/-- info: 'Shallot.MacroPeg.finite_specialization_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.finite_specialization_on

/-- info: 'Shallot.MacroPeg.finite_specialization_cbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.finite_specialization_cbn

/-- info: 'Shallot.MacroPeg.finite_specialization_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.finite_specialization_accepts

/-- info: 'Shallot.MacroPeg.finite_specialization_recognizesAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.finite_specialization_recognizesAll

/-- info: 'Shallot.MacroPeg.finite_specialization_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.finite_specialization_run

/-- info: 'Shallot.MacroPeg.peg_obs_as_fragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.peg_obs_as_fragment

/-- info: 'Shallot.MacroPeg.fragment_lang_is_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.fragment_lang_is_peg

/-- info: 'Shallot.MacroPeg.peg_lang_is_fragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.peg_lang_is_fragment

/-- info: 'Shallot.MacroPeg.env_obs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.env_obs_iff

/-- info: 'Shallot.MacroPeg.FGrammar.reach_specSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.reach_specSet

/-- info: 'Shallot.MacroPeg.FGrammar.entry_mem_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.FGrammar.entry_mem_reach

/-- info: 'Shallot.MacroPeg.reachable_specialization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.reachable_specialization

/-- info: 'Shallot.MacroPeg.reach_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.reach_length_le

/-- info: 'Shallot.MacroPeg.reach_selfContained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.reach_selfContained

/-- info: 'Shallot.MacroPeg.loopF_no_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.loopF_no_obs

/-- info: 'Shallot.MacroPeg.no_derives_selfLoop' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.no_derives_selfLoop

/-- info: 'Shallot.MacroPeg.sim_subst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.sim_subst

/-- info: 'Shallot.MacroPeg.sim_preserve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.sim_preserve

/-- info: 'Shallot.MacroPeg.subst_obsEquiv_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.subst_obsEquiv_general

/-- info: 'Shallot.MacroPeg.subst_obsEquiv_of_argEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.subst_obsEquiv_of_argEquiv

/-- info: 'Shallot.MacroPeg.same_recognizesAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.same_recognizesAll

/-- info: 'Shallot.MacroPeg.ce_call_argA' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce_call_argA

/-- info: 'Shallot.MacroPeg.ce_call_argAEnd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce_call_argAEnd

/-- info: 'Shallot.MacroPeg.ce_not_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce_not_accepts

/-- info: 'Shallot.MacroPeg.argA_not_equiv_argAEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.argA_not_equiv_argAEnd

/-- info: 'Shallot.MacroPeg.row1_cbn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row1_cbn

/-- info: 'Shallot.MacroPeg.row1_par' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row1_par

/-- info: 'Shallot.MacroPeg.row1_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row1_seq

/-- info: 'Shallot.MacroPeg.row2_cbn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row2_cbn

/-- info: 'Shallot.MacroPeg.row2_par' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row2_par

/-- info: 'Shallot.MacroPeg.row2_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row2_seq

/-- info: 'Shallot.MacroPeg.row3_cbn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row3_cbn

/-- info: 'Shallot.MacroPeg.row3_par' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row3_par

/-- info: 'Shallot.MacroPeg.row3_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row3_seq

/-- info: 'Shallot.MacroPeg.row4_cbn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row4_cbn

/-- info: 'Shallot.MacroPeg.row4_par' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row4_par

/-- info: 'Shallot.MacroPeg.row4_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.row4_seq

/-- info: 'Shallot.MacroPeg.rowAnd_cbn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rowAnd_cbn

/-- info: 'Shallot.MacroPeg.rowAnd_par' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rowAnd_par

/-- info: 'Shallot.MacroPeg.rowAnd_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rowAnd_seq

/-- info: 'Shallot.MacroPeg.andA_zero_on_a' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.andA_zero_on_a

/-- info: 'Shallot.MacroPeg.loop_no_derivation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.loop_no_derivation

/-- info: 'Shallot.MacroPeg.loop_no_obs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.loop_no_obs

/-- info: 'Shallot.MacroPeg.cbn_unused_first_fails' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cbn_unused_first_fails

/-- info: 'Shallot.MacroPeg.cbn_unused_first_loops' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cbn_unused_first_loops

/-- info: 'Shallot.MacroPeg.par_shortCircuit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.par_shortCircuit

/-- info: 'Shallot.MacroPeg.seq_shortCircuit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.seq_shortCircuit

/-- info: 'Shallot.MacroPeg.par_first_loops' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.par_first_loops

/-- info: 'Shallot.MacroPeg.seq_first_loops' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.seq_first_loops

/-- info: 'Shallot.MacroPeg.zr_subst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.zr_subst

/-- info: 'Shallot.MacroPeg.zr_preserve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.zr_preserve

/-- info: 'Shallot.MacroPeg.strategy_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.strategy_agree

/-- info: 'Shallot.MacroPeg.strategy_agree_eps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.strategy_agree_eps

/-! ## Macro PEG memo-table bounds: linear for the finite-argument fragment, not linear in general -/

/-- info: 'Shallot.MacroPeg.visits_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.visits_suffix

/-- info: 'Shallot.MacroPeg.cbn_call_body' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cbn_call_body

/-- info: 'Shallot.MacroPeg.visits_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.visits_derivable

/-- info: 'Shallot.MacroPeg.Visits.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Visits.trans

/-- info: 'Shallot.MacroPeg.visits_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.visits_rel

/-- info: 'Shallot.MacroPeg.rel_call_nt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rel_call_nt

/-- info: 'Shallot.MacroPeg.rel_call_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rel_call_inj

/-- info: 'Shallot.MacroPeg.memo_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.memo_bound

/-- info: 'Shallot.MacroPeg.memo_bound_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.memo_bound_sum

/-- info: 'Shallot.MacroPeg.argOf_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.argOf_inj

/-- info: 'Shallot.MacroPeg.expF_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expF_fails

/-- info: 'Shallot.MacroPeg.exp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.exp_step

/-- info: 'Shallot.MacroPeg.exp_visits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.exp_visits

/-- info: 'Shallot.MacroPeg.exp_visits_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.exp_visits_all

/-- info: 'Shallot.MacroPeg.length_allWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.length_allWords

/-- info: 'Shallot.MacroPeg.nodup_allWords' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.nodup_allWords

/-- info: 'Shallot.MacroPeg.nodup_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.nodup_length_le

/-- info: 'Shallot.MacroPeg.exists_pow_gt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.exists_pow_gt

/-- info: 'Shallot.MacroPeg.no_linear_memo_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.no_linear_memo_bound

/-! ## Macro PEG recognition complexity: PSPACE-hard (QBF) and decidable in exponential time -/

/-- info: 'Shallot.MacroPeg.obs_seq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.obs_seq

/-- info: 'Shallot.MacroPeg.obs_alt_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.obs_alt_none

/-- info: 'Shallot.MacroPeg.obs_call' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.obs_call

/-- info: 'Shallot.MacroPeg.macroObs_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.macroObs_unique

/-- info: 'Shallot.MacroPeg.cNum_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cNum_ok

/-- info: 'Shallot.MacroPeg.cNum_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cNum_fail

/-- info: 'Shallot.MacroPeg.codeP_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.codeP_match

/-- info: 'Shallot.MacroPeg.asg_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.asg_match

/-- info: 'Shallot.MacroPeg.code_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.code_ok

/-- info: 'Shallot.MacroPeg.lit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.lit_ok

/-- info: 'Shallot.MacroPeg.lits_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.lits_star

/-- info: 'Shallot.MacroPeg.tl_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tl_match

/-- info: 'Shallot.MacroPeg.fl_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.fl_match

/-- info: 'Shallot.MacroPeg.cl_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cl_match

/-- info: 'Shallot.MacroPeg.clauses_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.clauses_star

/-- info: 'Shallot.MacroPeg.m_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.m_match

/-- info: 'Shallot.MacroPeg.q_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.q_match

/-- info: 'Shallot.MacroPeg.qbf_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.qbf_obs

/-- info: 'Shallot.MacroPeg.qbf_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.qbf_reduction

/-- info: 'Shallot.MacroPeg.qbf_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.qbf_reject

/-- info: 'Shallot.MacroPeg.enc_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.enc_length

/-- info: 'Shallot.MacroPeg.ev_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_mono

/-- info: 'Shallot.MacroPeg.tbl_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tbl_mono

/-- info: 'Shallot.MacroPeg.tbl_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tbl_step

/-- info: 'Shallot.MacroPeg.ev_tbl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_tbl_le

/-- info: 'Shallot.MacroPeg.ev_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_ok

/-- info: 'Shallot.MacroPeg.tbl_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tbl_ok

/-- info: 'Shallot.MacroPeg.firstOrder_subst' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.firstOrder_subst

/-- info: 'Shallot.MacroPeg.ev_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_subst

/-- info: 'Shallot.MacroPeg.ev_call_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_call_step

/-- info: 'Shallot.MacroPeg.derives_ev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.derives_ev

/-- info: 'Shallot.MacroPeg.ev_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_sound

/-- info: 'Shallot.MacroPeg.tbl_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tbl_sound

/-- info: 'Shallot.MacroPeg.ev_derives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_derives

/-- info: 'Shallot.MacroPeg.length_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.length_words

/-- info: 'Shallot.MacroPeg.mem_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.mem_words

/-- info: 'Shallot.MacroPeg.ev_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ev_agree

/-- info: 'Shallot.MacroPeg.agree_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.agree_succ

/-- info: 'Shallot.MacroPeg.agree_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.agree_from

/-- info: 'Shallot.MacroPeg.agree_of_count_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.agree_of_count_eq

/-- info: 'Shallot.MacroPeg.defCount_le_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.defCount_le_bound

/-- info: 'Shallot.MacroPeg.tbl_fix_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tbl_fix_exists

/-- info: 'Shallot.MacroPeg.tbl_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tbl_stable

/-- info: 'Shallot.MacroPeg.decideObs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.decideObs_iff

/-- info: 'Shallot.MacroPeg.decideObs_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.decideObs_none_iff

/-- info: 'Shallot.MacroPeg.recognizesAll_decide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.recognizesAll_decide

/-- info: 'Shallot.MacroPeg.iterBound_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.iterBound_eq

/-- info: 'Shallot.MacroPeg.iterBound_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.iterBound_le

/-- info: 'Shallot.MacroPeg.qbfG_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.qbfG_firstOrder

/-- info: 'Shallot.MacroPeg.qbf_by_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.qbf_by_decision

/-! ## Macro PEG call-by-value recognition: decidable with polynomially many rounds -/

/-- info: 'Shallot.MacroPeg.evV_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evV_mono

/-- info: 'Shallot.MacroPeg.evParArgs_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evParArgs_mono

/-- info: 'Shallot.MacroPeg.evSeqArgs_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evSeqArgs_mono

/-- info: 'Shallot.MacroPeg.tblV_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tblV_step

/-- info: 'Shallot.MacroPeg.evV_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evV_subst

/-- info: 'Shallot.MacroPeg.evParArgs_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evParArgs_subst

/-- info: 'Shallot.MacroPeg.evSeqArgs_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evSeqArgs_subst

/-- info: 'Shallot.MacroPeg.derivesV_ev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.derivesV_ev

/-- info: 'Shallot.MacroPeg.evV_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evV_sound

/-- info: 'Shallot.MacroPeg.evParArgs_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evParArgs_sound

/-- info: 'Shallot.MacroPeg.evSeqArgs_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evSeqArgs_sound

/-- info: 'Shallot.MacroPeg.tblV_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tblV_sound

/-- info: 'Shallot.MacroPeg.evV_derives' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evV_derives

/-- info: 'Shallot.MacroPeg.evV_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evV_ok

/-- info: 'Shallot.MacroPeg.tblV_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tblV_ok

/-- info: 'Shallot.MacroPeg.pre_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.pre_mem

/-- info: 'Shallot.MacroPeg.length_subStrs_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.length_subStrs_le

/-- info: 'Shallot.MacroPeg.evV_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.evV_agree

/-- info: 'Shallot.MacroPeg.agreeV_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.agreeV_succ

/-- info: 'Shallot.MacroPeg.agreeV_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.agreeV_from

/-- info: 'Shallot.MacroPeg.agreeV_of_count_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.agreeV_of_count_eq

/-- info: 'Shallot.MacroPeg.defCountV_le_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.defCountV_le_bound

/-- info: 'Shallot.MacroPeg.tblV_fix_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tblV_fix_exists

/-- info: 'Shallot.MacroPeg.tblV_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tblV_stable

/-- info: 'Shallot.MacroPeg.decideObsV_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.decideObsV_iff

/-- info: 'Shallot.MacroPeg.decideObsV_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.decideObsV_none_iff

/-- info: 'Shallot.MacroPeg.iterBoundV_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.iterBoundV_le

/-! ## Macro PEG decision procedures: cost of one evaluation, one round, and the whole run -/

/-- info: 'Shallot.MacroPeg.costStar_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.costStar_le

/-- info: 'Shallot.MacroPeg.costV_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.costV_le

/-- info: 'Shallot.MacroPeg.cbV_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cbV_le

/-- info: 'Shallot.MacroPeg.roundCostV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.roundCostV_le

/-- info: 'Shallot.MacroPeg.totalCostV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.totalCostV_le

/-- info: 'Shallot.MacroPeg.totalCostV_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.totalCostV_poly

/-- info: 'Shallot.MacroPeg.costN_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.costN_le

/-- info: 'Shallot.MacroPeg.cbN_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.cbN_le

/-- info: 'Shallot.MacroPeg.roundCostN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.roundCostN_le

/-- info: 'Shallot.MacroPeg.totalCostN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.totalCostN_le

/-- info: 'Shallot.MacroPeg.totalCostN_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.totalCostN_exp

/-! ## Macro PEG: linear-space alternating Turing machines (EXPTIME-hardness) -/

/-- info: 'Shallot.MacroPeg.ATM.val_functional' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ATM.val_functional

/-- info: 'Shallot.MacroPeg.ATM.valList_functional' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ATM.valList_functional

/-- info: 'Shallot.MacroPeg.subst_scanBody' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.subst_scanBody

/-- info: 'Shallot.MacroPeg.atmG_scan' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atmG_scan

/-- info: 'Shallot.MacroPeg.atmG_ft' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atmG_ft

/-- info: 'Shallot.MacroPeg.sitesStr_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.sitesStr_length

/-- info: 'Shallot.MacroPeg.codeE_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.codeE_ok

/-- info: 'Shallot.MacroPeg.siteE_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.siteE_ok

/-- info: 'Shallot.MacroPeg.tape0_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tape0_rep

/-- info: 'Shallot.MacroPeg.fact_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.fact_rep

/-- info: 'Shallot.MacroPeg.ft_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ft_hit

/-- info: 'Shallot.MacroPeg.ft_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ft_miss

/-- info: 'Shallot.MacroPeg.head_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.head_hit

/-- info: 'Shallot.MacroPeg.head_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.head_miss

/-- info: 'Shallot.MacroPeg.sym_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.sym_test

/-- info: 'Shallot.MacroPeg.scan_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.scan_ok

/-- info: 'Shallot.MacroPeg.br_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.br_ok

/-- info: 'Shallot.MacroPeg.chain_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.chain_all

/-- info: 'Shallot.MacroPeg.chain_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.chain_any

/-- info: 'Shallot.MacroPeg.step_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.step_ok

/-- info: 'Shallot.MacroPeg.atm_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atm_sim

/-- info: 'Shallot.MacroPeg.atm_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atm_reduction

/-- info: 'Shallot.MacroPeg.atmG_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atmG_firstOrder

-- The callable-value slice (M-PEG-4) reduces to first-order grammars (`Properties/DefunCorrect.lean`).

/-- info: 'Shallot.MacroPeg.tr_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.tr_subst

/-- info: 'Shallot.MacroPeg.defun_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.defun_firstOrder

/-- info: 'Shallot.MacroPeg.defun_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.defun_obs

/-- info: 'Shallot.MacroPeg.decideSlice_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.decideSlice_iff

/-- info: 'Shallot.MacroPeg.decideSlice_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.decideSlice_none_iff

-- Higher-order Macro PEG with closures (`MacroPeg/HigherOrder/`).

/-- info: 'Shallot.MacroPeg.HO.hrun_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.hrun_mono

/-- info: 'Shallot.MacroPeg.HO.hobs_det' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.hobs_det

/-- info: 'Shallot.MacroPeg.HO.instArgs_emb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.instArgs_emb

/-- info: 'Shallot.MacroPeg.HO.emb_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.emb_obs

/-- info: 'Shallot.MacroPeg.HO.embGrammar_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.embGrammar_order

-- Higher-order Macro PEG is decidable: a finite monotone model (`HigherOrder/Decide.lean`).

/-- info: 'Shallot.MacroPeg.HO.hrun_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.hrun_suffix

/-- info: 'Shallot.MacroPeg.HO.den_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.den_mono

/-- info: 'Shallot.MacroPeg.HO.iter_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.iter_stable

/-- info: 'Shallot.MacroPeg.HO.inst_substC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.inst_substC

/-- info: 'Shallot.MacroPeg.HO.sound_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.sound_iter

/-- info: 'Shallot.MacroPeg.HO.complete_fix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.complete_fix

/-- info: 'Shallot.MacroPeg.HO.decideHO_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.decideHO_iff

/-- info: 'Shallot.MacroPeg.HO.decideHO_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.decideHO_none_iff

/-- info: 'Shallot.MacroPeg.HO.elems_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.elems_length_le

/-- info: 'Shallot.MacroPeg.HO.maxCount_parsers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.maxCount_parsers

/-- info: 'Shallot.MacroPeg.atmG_arityOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atmG_arityOk

/-- info: 'Shallot.MacroPeg.atm_reduction_HO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atm_reduction_HO

-- Order-2 Macro PEG is 2-EXPTIME-hard (`HigherOrder/ExpSpace/`); well-typed grammars are decided.

/-- info: 'Shallot.MacroPeg.HO.HGrammar.WellTyped.toTGrammar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.HGrammar.WellTyped.toTGrammar

/-- info: 'Shallot.MacroPeg.HO.decide_wellTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.decide_wellTyped

/-- info: 'Shallot.MacroPeg.ExpSpace.eq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.eq_ok

/-- info: 'Shallot.MacroPeg.ExpSpace.inc_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.inc_rep

/-- info: 'Shallot.MacroPeg.ExpSpace.wr_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.wr_rep

/-- info: 'Shallot.MacroPeg.ExpSpace.atm2_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.atm2_reduction

/-- info: 'Shallot.MacroPeg.ExpSpace.g2_wellTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.g2_wellTyped

/-- info: 'Shallot.MacroPeg.ExpSpace.g2_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.g2_order

/-- info: 'Shallot.MacroPeg.ExpSpace.order2_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ExpSpace.order2_hard

/-- info: 'Shallot.MacroPeg.atm_by_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atm_by_decision

/-! ## Order-k Macro PEG is k-EXPTIME-hard; the cost of deciding order k is a tower of height k -/

/-- info: 'Shallot.MacroPeg.HO.decideCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.decideCost_le

/-- info: 'Shallot.MacroPeg.Levels.spec_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Levels.spec_all

/-- info: 'Shallot.MacroPeg.Tableau.tableau_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Tableau.tableau_sim

/-- info: 'Shallot.MacroPeg.Tableau.start_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Tableau.start_obs

/-- info: 'Shallot.MacroPeg.Tableau.gT_wellTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Tableau.gT_wellTyped

/-- info: 'Shallot.MacroPeg.Tableau.gT_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Tableau.gT_order

/-- info: 'Shallot.MacroPeg.KExp.enc_polytime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.enc_polytime

/-- info: 'Shallot.MacroPeg.KExp.kexp_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.kexp_reduction

/-- info: 'Shallot.MacroPeg.KExp.kexp_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.kexp_hard

/-- info: 'Shallot.MacroPeg.KExp.serIn_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.serIn_inj

/-- info: 'Shallot.MacroPeg.KExp.umpeg_toBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.umpeg_toBits

/-- info: 'Shallot.MacroPeg.KExp.uniform_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.uniform_hard

/-- info: 'Shallot.MacroPeg.Mach.mainP_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Mach.mainP_halts

/-- info: 'Shallot.MacroPeg.Mach.mainCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.Mach.mainCost_le

/-- info: 'Shallot.MacroPeg.KExp.umpeg_kexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.umpeg_kexp

/-- info: 'Shallot.MacroPeg.KExp.umpeg_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.umpeg_complete

/-- info: 'Complexity.frun_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.frun_rep

/-- info: 'Complexity.Univ.simP_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.Univ.simP_runs

/-- info: 'Shallot.MacroPeg.KExp.diag_not_kexp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.diag_not_kexp

/-- info: 'Shallot.MacroPeg.KExp.diag_kexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.diag_kexp

/-- info: 'Shallot.MacroPeg.KExp.kexp_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.kexp_strict

/-- info: 'Shallot.MacroPeg.KExp.kexp_reduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.kexp_reduces

/-- info: 'Shallot.MacroPeg.KExp.mpeg_kexp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.mpeg_kexp

/-- info: 'Shallot.MacroPeg.KExp.order_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.KExp.order_strict

/-! ## TQBF is PSPACE-complete (Complexity) -/

/-- info: 'Complexity.reduction_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.reduction_correct

/-- info: 'Complexity.tqbf_in_pspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.tqbf_in_pspace

/-- info: 'Complexity.tqbf_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.tqbf_hard

/-- info: 'Complexity.tqbf_pspace_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.tqbf_pspace_complete

/-! CE-007 (no `CallByValueSeq` analogue of T-exp) and idempotence of `expand`. -/

/-- info: 'Shallot.MacroPeg.ce007_hypotheses_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce007_hypotheses_hold

/-- info: 'Shallot.MacroPeg.ce007_expanded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce007_expanded

/-- info: 'Shallot.MacroPeg.ce007_callByValueSeq_expanded_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce007_callByValueSeq_expanded_rejects

/-- info: 'Shallot.MacroPeg.ce007_callByValueSeq_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce007_callByValueSeq_diverges

/-- info: 'Shallot.MacroPeg.expand_of_hasCall_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expand_of_hasCall_false

/-- info: 'Shallot.MacroPeg.expand_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expand_idempotent

/-- info: 'Shallot.MacroPeg.expandGrammar_of_callFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expandGrammar_of_callFree

/-- info: 'Shallot.MacroPeg.expandGrammar_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.expandGrammar_idempotent

/-! ## M-PEG-7: well-formedness implies termination on the first-order fragment (`MacroPeg/Termination.lean`)

`wf_total` is the headline (T-total); `generated_parser_total` is the whole-pipeline form
(expanded grammar passes `wfB` ⇒ the generated parser terminates on every input). The
`rightRec_*`/`leftRec_*`/`nullStar_*`/`ce002_not_wf` entries show the checker is neither
vacuous nor blind: it accepts right recursion, rejects left recursion and nullable
repetition, and does not vouch for CE-002's diverging macro grammar. -/

/-- info: 'Shallot.MacroPeg.nullExp_of_nonconsuming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.nullExp_of_nonconsuming

/-- info: 'Shallot.MacroPeg.consumes_of_not_nullExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.consumes_of_not_nullExp

/-- info: 'Shallot.MacroPeg.rankAdj_lt_of_acyclic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rankAdj_lt_of_acyclic

/-- info: 'Shallot.MacroPeg.lrank_body_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.lrank_body_lt

/-- info: 'Shallot.MacroPeg.wf_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.wf_struct

/-- info: 'Shallot.MacroPeg.wf_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.wf_total

/-- info: 'Shallot.MacroPeg.wf_total_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.wf_total_start

/-- info: 'Shallot.MacroPeg.wf_total_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.wf_total_run

/-- info: 'Shallot.MacroPeg.generated_parser_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.generated_parser_total

/-- info: 'Shallot.MacroPeg.rightRec_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rightRec_wf

/-- info: 'Shallot.MacroPeg.rightRec_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.rightRec_total

/-- info: 'Shallot.MacroPeg.leftRec_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.leftRec_not_wf

/-- info: 'Shallot.MacroPeg.nullStar_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.nullStar_not_wf

/-- info: 'Shallot.MacroPeg.ce002_not_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.ce002_not_wf

/-- info: 'Shallot.ford_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.ford_iff

/-- info: 'Shallot.ford_equiv_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.ford_equiv_iff

/-- info: 'Shallot.ford_complete_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.ford_complete_iff

/-- info: 'Shallot.fordG_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.fordG_complete

/-- info: 'Complexity.oneTape_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.oneTape_decides

/-- info: 'Complexity.k1_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.k1_undecidable

/-- info: 'Complexity.Undec.tm_sr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.Undec.tm_sr

/-- info: 'Complexity.Undec.sr_mpcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.Undec.sr_mpcp

/-- info: 'Complexity.Undec.mpcp_pcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.Undec.mpcp_pcp

/-- info: 'Shallot.pcpN_pcp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.pcpN_pcp

/-- info: 'Shallot.k1_grammar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.k1_grammar

/-- info: 'Shallot.peg_empty_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.peg_empty_undecidable

/-- info: 'Shallot.peg_equiv_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.peg_equiv_undecidable

/-- info: 'Shallot.peg_complete_undecidable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.peg_complete_undecidable

/-- info: 'Shallot.Cfg.l0_cfl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.l0_cfl

/-- info: 'Shallot.Cfg.greibach_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.greibach_std

/-- info: 'Shallot.Cfg.stdForm_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.stdForm_exists

/-- info: 'Shallot.Cfg.isPEL_invHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.isPEL_invHom

/-- info: 'Shallot.Cfg.cfl_pel_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Cfg.cfl_pel_iff

/-- info: 'Shallot.isPEL_allNtTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.isPEL_allNtTotal

/-- info: 'Shallot.isPEL_iff_isTotalPEL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.isPEL_iff_isTotalPEL

/-- info: 'Shallot.Dpda.DPDA.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Dpda.DPDA.sound

/-- info: 'Shallot.Dpda.DPDA.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Dpda.DPDA.complete

/-- info: 'Shallot.Dpda.dpda_isPEL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Dpda.dpda_isPEL

/-- info: 'Shallot.Dpda.dpda_isTotalPEL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Dpda.dpda_isTotalPEL

/-! ## Bounded packrat recognition -/

/-- info: 'Shallot.Packrat.iter_eq_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.iter_eq_run

/-- info: 'Shallot.Packrat.iter_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.iter_sound

/-- info: 'Shallot.Packrat.iter_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.iter_complete

/-- info: 'Shallot.Packrat.bound_stationary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.bound_stationary

/-- info: 'Shallot.Packrat.bounded_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.bounded_iff

/-- info: 'Shallot.Packrat.bounded_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.bounded_none_iff

/-- info: 'Shallot.Packrat.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.accepts_iff

/-- info: 'Shallot.Packrat.stored_eq_iter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.stored_eq_iter

/-- info: 'Shallot.Packrat.storedParse_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.storedParse_iff

/-- info: 'Shallot.Packrat.storedParse_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.storedParse_none_iff

/-! ## Stack-machine packrat cells -/

/-- info: 'Shallot.Packrat.fullAccepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.fullAccepts_iff

/-- info: 'Shallot.Packrat.Machine.start_full_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.start_full_iff

/-- info: 'Shallot.Packrat.Machine.step_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.step_encode

/-- info: 'Shallot.Packrat.Machine.nruns_readRow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_readRow

/-- info: 'Shallot.Packrat.Machine.nruns_seqCell_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_seqCell_round

/-- info: 'Shallot.Packrat.Machine.nruns_altCell_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_altCell_round

/-- info: 'Shallot.Packrat.Machine.nruns_starCell_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_starCell_round

/-- info: 'Shallot.Packrat.Machine.nruns_notCell_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_notCell_round

/-! ## Lexical cells, expression compiler, and table sweep -/

/-- info: 'Shallot.Packrat.Machine.nruns_readTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_readTest

/-- info: 'Shallot.Packrat.Machine.chrTest_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.chrTest_char

/-- info: 'Shallot.Packrat.Machine.rangeTest_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.rangeTest_char

/-- info: 'Shallot.Packrat.Machine.nruns_lexCell_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_lexCell_input

/-- info: 'Shallot.Packrat.Machine.literalScan_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.literalScan_value

/-- info: 'Shallot.Packrat.Machine.nruns_literalCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_literalCell

/-- info: 'Shallot.Packrat.Machine.literalCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.literalCost_le

/-- info: 'Shallot.Packrat.Machine.layout_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.layout_disjoint

/-- info: 'Shallot.Packrat.Machine.nruns_compileCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_compileCell

/-- info: 'Shallot.Packrat.Machine.nruns_fillRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_fillRow

/-- info: 'Shallot.Packrat.Machine.nruns_sweep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_sweep

/-- info: 'Shallot.Packrat.Machine.sweepCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.sweepCost_le

/-! ## Complete PEG machine and uniform polynomial time -/

/-- info: 'Shallot.Packrat.Machine.nruns_replaceRow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_replaceRow

/-- info: 'Shallot.Packrat.Machine.nruns_roundP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_roundP

/-- info: 'Shallot.Packrat.Machine.roundCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.roundCost_le

/-- info: 'Shallot.Packrat.Machine.nruns_iterateBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_iterateBound

/-- info: 'Shallot.Packrat.Machine.iterateCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.iterateCost_le

/-- info: 'Shallot.Packrat.Machine.nruns_initialize' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_initialize

/-- info: 'Shallot.Packrat.Machine.nruns_load_nInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nruns_load_nInit

/-- info: 'Shallot.Packrat.Machine.nhalts_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.nhalts_finish

/-- info: 'Shallot.Packrat.Machine.program_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.program_halts

/-- info: 'Shallot.Packrat.Machine.program_halts_fullAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.program_halts_fullAccepts

/-- info: 'Shallot.Packrat.Machine.programCost_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.programCost_le

/-- info: 'Shallot.Packrat.Machine.program_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.program_tm

/-- info: 'Shallot.Packrat.Machine.tmTime_degree15' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.tmTime_degree15

/-- info: 'Shallot.Packrat.Machine.bitLanguage_time15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.Packrat.Machine.bitLanguage_time15

/-! ## Strict inclusion of binary PEG languages in polynomial time -/

/-- info: 'Shallot.PegSeparation.polyDiag_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyDiag_code

/-- info: 'Shallot.PegSeparation.polyDiag_not_time' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyDiag_not_time

/-- info: 'Shallot.PegSeparation.polyDiag_not_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyDiag_not_peg

/-- info: 'Shallot.PegSeparation.polyFront_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyFront_ok

/-- info: 'Shallot.PegSeparation.polyFront_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyFront_bad

/-- info: 'Shallot.PegSeparation.polyDiagP_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyDiagP_halts

/-- info: 'Shallot.PegSeparation.polyDiagBound_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyDiagBound_poly

/-- info: 'Shallot.PegSeparation.nprog_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.nprog_in_P

/-- info: 'Shallot.PegSeparation.polyDiag_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polyDiag_in_P

/-- info: 'Shallot.PegSeparation.isBitPEL_iff_restriction' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.PegSeparation.isBitPEL_iff_restriction

/-- info: 'Shallot.PegSeparation.bitPEL_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.bitPEL_in_P

/-- info: 'Shallot.PegSeparation.polynomial_non_PEL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.polynomial_non_PEL

/-- info: 'Shallot.PegSeparation.pel_strict_in_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.pel_strict_in_p

/-- info: 'Shallot.PegSeparation.lifted_polyDiag_not_PEL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.lifted_polyDiag_not_PEL

/-- info: 'Shallot.PegSeparation.character_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.character_counterexample


-- Ordinary PEG versus first-order CBN Macro PEG.

/-- info: 'Shallot.PegSeparation.closeBoundN_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.closeBoundN_poly

/-- info: 'Shallot.PegSeparation.p_reduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.p_reduces

/-- info: 'Shallot.MacroPeg.HO.emb_firstGrammar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.emb_firstGrammar

/-- info: 'Shallot.MacroPeg.HO.firstGrammar_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.firstGrammar_obs

/-- info: 'Shallot.MacroPeg.HO.tableau_firstShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.tableau_firstShape

/-- info: 'Shallot.MacroPeg.HO.first_order_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.HO.first_order_hard

/-- info: 'Shallot.PegSeparation.readToken_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.readToken_spec

/-- info: 'Shallot.PegSeparation.tokenLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.tokenLoop_spec

/-- info: 'Shallot.PegSeparation.nruns_loadTokens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.nruns_loadTokens

/-- info: 'Shallot.PegSeparation.tokenProgram_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.tokenProgram_halts

/-- info: 'Shallot.PegSeparation.tokenLanguage_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.tokenLanguage_in_P

/-- info: 'Shallot.PegSeparation.pel_subset_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.pel_subset_firstOrder

/-- info: 'Shallot.PegSeparation.firstOrder_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_witness

/-- info: 'Shallot.PegSeparation.firstOrder_non_PEL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_non_PEL

/-- info: 'Shallot.PegSeparation.pel_strict_in_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.pel_strict_in_firstOrder


-- Finite numeric CBV tables and verified interval lookup.

/-- info: 'Shallot.MacroPeg.CBV.unpack_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.unpack_pack

/-- info: 'Shallot.MacroPeg.CBV.iterate_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.iterate_pack

/-- info: 'Shallot.MacroPeg.CBV.eval_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.eval_correct

/-- info: 'Shallot.MacroPeg.CBV.numericIterate_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.numericIterate_pack

/-- info: 'Shallot.MacroPeg.CBV.numericObservation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.numericObservation_iff

/-- info: 'Shallot.MacroPeg.CBV.numericAccept_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.numericAccept_iff

/-- info: 'Shallot.MacroPeg.CBV.numericIterate_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.numericIterate_size

/-- info: 'Shallot.MacroPeg.CBV.keys_get_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.keys_get_address

/-- info: 'Shallot.MacroPeg.CBV.pack_get_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.pack_get_address

/-- info: 'Shallot.MacroPeg.CBV.spanLookup_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.spanLookup_runs

/-- info: 'Shallot.MacroPeg.CBV.spanLookupCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.spanLookupCost_poly

/-- info: 'Shallot.MacroPeg.CBV.AddrExpr.compile_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.AddrExpr.compile_runs

/-- info: 'Shallot.MacroPeg.CBV.AddrExpr.value_addressExpr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.AddrExpr.value_addressExpr

/-- info: 'Shallot.MacroPeg.CBV.AddrExpr.cost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.AddrExpr.cost_poly

/-- info: 'Shallot.MacroPeg.CBV.tableRead_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.tableRead_runs

/-- info: 'Shallot.MacroPeg.CBV.tableRead_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.tableRead_cell

/-- info: 'Shallot.MacroPeg.CBV.tableRead_cost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.tableRead_cost_poly

-- Concrete CBV dictionary construction, literal matching and control.

/-- info: 'Shallot.MacroPeg.CBV.spanBuild_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.spanBuild_runs

/-- info: 'Shallot.MacroPeg.CBV.spanBuildCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.spanBuildCost_poly

/-- info: 'Shallot.MacroPeg.CBV.mirrorBuild_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.mirrorBuild_runs

/-- info: 'Shallot.MacroPeg.CBV.spanLiteral_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.spanLiteral_runs

/-- info: 'Shallot.MacroPeg.CBV.spanLiteralCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.spanLiteralCost_poly

/-- info: 'Shallot.MacroPeg.CBV.pairRead_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.pairRead_runs

/-- info: 'Shallot.MacroPeg.CBV.paramLiteral_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.paramLiteral_runs

/-- info: 'Shallot.MacroPeg.CBV.paramLiteralCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.paramLiteralCost_poly

/-- info: 'Shallot.MacroPeg.CBV.fixedLiteral_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.fixedLiteral_runs

/-- info: 'Shallot.MacroPeg.CBV.fixedLiteralCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.fixedLiteralCost_poly

/-- info: 'Shallot.MacroPeg.CBV.remainingLex_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.remainingLex_runs

/-- info: 'Shallot.MacroPeg.CBV.remainingLex_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.remainingLex_any

/-- info: 'Shallot.MacroPeg.CBV.remainingLex_chr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.remainingLex_chr

/-- info: 'Shallot.MacroPeg.CBV.remainingLex_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.remainingLex_range

/-- info: 'Shallot.MacroPeg.CBV.altEval_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.altEval_runs

/-- info: 'Shallot.MacroPeg.CBV.notAfter_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.notAfter_runs

/-- info: 'Shallot.MacroPeg.CBV.seqAfter_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.seqAfter_runs

-- CBV repetition, registration, scalar call addresses and expression frames.

/-- info: 'Shallot.MacroPeg.CBV.AddrExpr.compile_runs_used' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.AddrExpr.compile_runs_used

/-- info: 'Shallot.MacroPeg.CBV.tableRead_runs_used' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.tableRead_runs_used

/-- info: 'Shallot.MacroPeg.CBV.starAfter_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.starAfter_runs

/-- info: 'Shallot.MacroPeg.CBV.starLoop_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.starLoop_runs

/-- info: 'Shallot.MacroPeg.CBV.starEval_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.starEval_runs

/-- info: 'Shallot.MacroPeg.CBV.starEvalCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.starEvalCost_poly

/-- info: 'Shallot.MacroPeg.CBV.registerSpan_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.registerSpan_runs

/-- info: 'Shallot.MacroPeg.CBV.registerSpanCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.registerSpanCost_poly

/-- info: 'Shallot.MacroPeg.CBV.rankUpdate_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.rankUpdate_runs

/-- info: 'Shallot.MacroPeg.CBV.rankAddressExpr_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.rankAddressExpr_value

/-- info: 'Shallot.MacroPeg.CBV.ruleRead_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ruleRead_runs

/-- info: 'Shallot.MacroPeg.CBV.rankUpdateCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.rankUpdateCost_poly

/-- info: 'Shallot.MacroPeg.CBV.ruleReadCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ruleReadCost_poly

/-- info: 'Shallot.MacroPeg.CBV.EvalReady.frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.EvalReady.frame

/-- info: 'Shallot.MacroPeg.CBV.paramEval_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.paramEval_runs

/-- info: 'Shallot.MacroPeg.CBV.callPrepare_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.callPrepare_runs

/-- info: 'Shallot.MacroPeg.CBV.callCleanup_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.callCleanup_runs

/-- info: 'Shallot.MacroPeg.CBV.argPosition_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.argPosition_runs

-- Complete CBV expression compiler and all-position sweeps.

/-- info: 'Shallot.MacroPeg.CBV.rankedArgs_seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.rankedArgs_seq

/-- info: 'Shallot.MacroPeg.CBV.rankedArgs_par' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.rankedArgs_par

/-- info: 'Shallot.MacroPeg.CBV.rankedCall_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.rankedCall_eval

/-- info: 'Shallot.MacroPeg.CBV.exprBudget_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.exprBudget_poly

/-- info: 'Shallot.MacroPeg.CBV.argsBudget_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.argsBudget_poly

/-- info: 'Shallot.MacroPeg.CBV.argAfter_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.argAfter_runs

/-- info: 'Shallot.MacroPeg.CBV.argsProgram_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.argsProgram_runs

/-- info: 'Shallot.MacroPeg.CBV.ruleRead_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ruleRead_bounded

/-- info: 'Shallot.MacroPeg.CBV.exprProgram_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.exprProgram_runs

/-- info: 'Shallot.MacroPeg.CBV.positionSweep_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.positionSweep_runs

/-- info: 'Shallot.MacroPeg.CBV.positionSweepCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.positionSweepCost_poly

-- Complete CBV machine upper bound and common CBN separation witness.

/-- info: 'Shallot.MacroPeg.CBV.envSweep_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.envSweep_runs

/-- info: 'Shallot.MacroPeg.CBV.envSweepCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.envSweepCost_poly

/-- info: 'Shallot.MacroPeg.CBV.roundProgram_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.roundProgram_runs

/-- info: 'Shallot.MacroPeg.CBV.roundCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.roundCost_poly

/-- info: 'Shallot.MacroPeg.CBV.tableInit_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.tableInit_runs

/-- info: 'Shallot.MacroPeg.CBV.tableInitCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.tableInitCost_poly

/-- info: 'Shallot.MacroPeg.CBV.saturation_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.saturation_runs

/-- info: 'Shallot.MacroPeg.CBV.saturationCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.saturationCost_poly

/-- info: 'Shallot.MacroPeg.CBV.loadedProgram_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.loadedProgram_halts

/-- info: 'Shallot.MacroPeg.CBV.loadedCost_poly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.loadedCost_poly

/-- info: 'Shallot.MacroPeg.CBV.setup_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.setup_runs

/-- info: 'Shallot.MacroPeg.CBV.inputProgram_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.inputProgram_halts

/-- info: 'Shallot.MacroPeg.CBV.language_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.language_in_P

/-- info: 'Shallot.PegSeparation.firstOrder_cbn_not_cbv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_cbn_not_cbv

/-! ## CBV-to-CBN construction: captured intervals and bounded control -/

/-- info: 'Shallot.MacroPeg.CBVtoCBN.LenRep.seq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.LenRep.seq

/-- info: 'Shallot.MacroPeg.CBVtoCBN.skipN_rep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.skipN_rep

/-- info: 'Shallot.MacroPeg.CBVtoCBN.equalPosition_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.equalPosition_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.lePosition_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.lePosition_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.ltPosition_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.ltPosition_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.ifP_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.ifP_true_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.ifP_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.ifP_false_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.findLength_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.findLength_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.findComplement_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.findComplement_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.lengthWrapper_obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.lengthWrapper_obs

/-- info: 'Shallot.MacroPeg.CBVtoCBN.spanEq_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.spanEq_obs

/-- info: 'Shallot.MacroPeg.CBVtoCBN.spanEq_rep_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.spanEq_rep_obs

/-- info: 'Shallot.MacroPeg.CBVtoCBN.capturedLiteral_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.capturedLiteral_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.anyPosition_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.anyPosition_obs

/-- info: 'Shallot.MacroPeg.CBVtoCBN.complementContext_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.complementContext_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.decrement_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.decrement_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.fullClock_sufficient' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.fullClock_sufficient

/-- info: 'Shallot.MacroPeg.CBVtoCBN.fullClock_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.fullClock_eval_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.emptyInputP_obs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.emptyInputP_obs

/-- info: 'Shallot.MacroPeg.CBVtoCBN.emptyInputP_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.emptyInputP_correct

/-! ## CBV-to-CBN: generated clock, partial-result predicates, and argument capture -/

/-- info: 'Shallot.MacroPeg.CBVtoCBN.predClock_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.predClock_spec

/-- info: 'Shallot.MacroPeg.CBVtoCBN.borrowExpr_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.borrowExpr_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.clockBlock_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.clockBlock_firstOrder

/-- info: 'Shallot.MacroPeg.CBVtoCBN.clockBlock_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.clockBlock_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.clockStartBlock_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.clockStartBlock_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.RootTest.seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.RootTest.seq

/-- info: 'Shallot.MacroPeg.CBVtoCBN.RootTest.alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.RootTest.alt

/-- info: 'Shallot.MacroPeg.CBVtoCBN.RootTest.notP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.RootTest.notP

/-- info: 'Shallot.MacroPeg.CBVtoCBN.anyPair_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.anyPair_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.pairSearchBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.pairSearchBlock_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.altSuccess_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.altSuccess_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.altFailure_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.altFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.notSuccess_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.notSuccess_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.notFailure_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.notFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.sequenceSuccessBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.sequenceSuccessBlock_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.sequenceFailureBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.sequenceFailureBlock_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.finishPar_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.finishPar_cons

/-- info: 'Shallot.MacroPeg.CBVtoCBN.finishSeq_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.finishSeq_cons

/-- info: 'Shallot.MacroPeg.CBVtoCBN.evV_call_finishPar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.evV_call_finishPar

/-- info: 'Shallot.MacroPeg.CBVtoCBN.evV_call_finishSeq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.evV_call_finishSeq

/-- info: 'Shallot.MacroPeg.CBVtoCBN.evaluatedCapture_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.evaluatedCapture_le

/-- info: 'Shallot.MacroPeg.CBVtoCBN.captureBlock_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.captureBlock_firstOrder

/-- info: 'Shallot.MacroPeg.CBVtoCBN.captureBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.captureBlock_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.captureSuccess_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.captureSuccess_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.captureFailure_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.captureFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.clockTable_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.clockTable_step

/-- info: 'Shallot.MacroPeg.CBVtoCBN.clockTable_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.clockTable_zero

/-! ## CBV-to-CBN: repetition, leaves, generated grammar and static layout -/

/-- info: 'Shallot.MacroPeg.CBVtoCBN.RootTest.guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.RootTest.guarded

/-- info: 'Shallot.MacroPeg.CBVtoCBN.evStar_success_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.evStar_success_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.repetitionBlock_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.repetitionBlock_firstOrder

/-- info: 'Shallot.MacroPeg.CBVtoCBN.repetitionBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.repetitionBlock_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.repetitionFailure_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.repetitionFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.Atom.obs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.Atom.obs

/-- info: 'Shallot.MacroPeg.CBVtoCBN.Atom.source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.Atom.source

/-- info: 'Shallot.MacroPeg.CBVtoCBN.terminalSuccess_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.terminalSuccess_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.terminalFailure_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.terminalFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.atomSuccess_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.atomSuccess_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.atomFailure_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.atomFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.stripPrefix_length_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.stripPrefix_length_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.capturedValue_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.capturedValue_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.parameterSuccess_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.parameterSuccess_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.parameterFailureBlock_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.parameterFailureBlock_firstOrder

/-- info: 'Shallot.MacroPeg.CBVtoCBN.parameterFailureBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.parameterFailureBlock_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.parameterSource_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.parameterSource_success

/-- info: 'Shallot.MacroPeg.CBVtoCBN.parameterSource_failure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.parameterSource_failure

/-- info: 'Shallot.MacroPeg.CBVtoCBN.parameterMissing_tests' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.parameterMissing_tests

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compileCandidate_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compileCandidate_firstOrder

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compileCandidate_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compileCandidate_at

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compilerNodes_start' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compilerNodes_start

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compilerNodes_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compilerNodes_body

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compilerNodes_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compilerNodes_lookup

/-! ## CBV-to-CBN: actual compiled expression semantics and structural induction -/

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compilerStart_available' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compilerStart_available

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compilerBody_available' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compilerBody_available

/-- info: 'Shallot.MacroPeg.CBVtoCBN.ExprAvailable.call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.ExprAvailable.call

/-- info: 'Shallot.MacroPeg.CBVtoCBN.ArgsAvailable.cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.ArgsAvailable.cons

/-- info: 'Shallot.MacroPeg.CBVtoCBN.evalArgs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.evalArgs_length

/-- info: 'Shallot.MacroPeg.CBVtoCBN.CompilerConfig.expr_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.CompilerConfig.expr_unfold

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledAtom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledAtom_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledAlt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledAlt_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.CompilerConfig.block_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.CompilerConfig.block_at

/-- info: 'Shallot.MacroPeg.CBVtoCBN.RulesAt.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.RulesAt.split

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledFailureAdapter_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledFailureAdapter_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledSequence_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledSequence_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledStar_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledStar_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledNot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledNot_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.evalArgs_env_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.evalArgs_env_get

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledParameter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledParameter_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.argumentResult_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.argumentResult_zero

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledCall_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledCall_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledCall_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledCall_missing

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledCall_badArity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledCall_badArity

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledSyntax_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledSyntax_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledSyntaxArgs_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledSyntaxArgs_correct

/-! ## CBV-to-CBN: unconditional simulation, recognition preservation and both strict inclusions -/

/-- info: 'Shallot.MacroPeg.CBVtoCBN.subst_lookupClockParams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.subst_lookupClockParams

/-- info: 'Shallot.MacroPeg.CBVtoCBN.subst_lookupBodyParams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.subst_lookupBodyParams

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledLookup_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledLookup_rule

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledLookup_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledLookup_clock

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledLookup_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledLookup_pack

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledLookup_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledLookup_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.argumentResult_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.argumentResult_cons

/-- info: 'Shallot.MacroPeg.CBVtoCBN.RulesAt.capture_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.RulesAt.capture_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledArguments_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledArguments_done

/-- info: 'Shallot.MacroPeg.CBVtoCBN.argumentEval_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.argumentEval_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.argumentFailure_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.argumentFailure_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.argumentNext_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.argumentNext_test

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledArguments_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledArguments_step

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledArguments_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledArguments_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.callHandler_of_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.callHandler_of_lookup

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compiledEvaluator_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compiledEvaluator_correct

/-- info: 'Shallot.MacroPeg.CBVtoCBN.finiteSource_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.finiteSource_accepts

/-- info: 'Shallot.MacroPeg.CBVtoCBN.compilerBootstrap_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.compilerBootstrap_iff

/-- info: 'Shallot.MacroPeg.CBVtoCBN.translate_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.translate_firstOrder

/-- info: 'Shallot.MacroPeg.CBVtoCBN.translate_recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBVtoCBN.translate_recognizes

/-- info: 'Shallot.PegSeparation.firstOrder_cbv_subset_cbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_cbv_subset_cbn

/-- info: 'Shallot.PegSeparation.firstOrder_par_strict_cbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_par_strict_cbn

/-- info: 'Shallot.PegSeparation.firstOrder_seq_strict_cbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_seq_strict_cbn

/-- info: 'Shallot.PegSeparation.firstOrder_cbv_par_seq_strict_cbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_cbv_par_seq_strict_cbn

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.equal_obs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.equal_obs_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.predecessor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.predecessor_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.counterGrammar_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.counterGrammar_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.counterGrammar_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.counterGrammar_interval

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.exists_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.exists_obs

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.anyFrom_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.anyFrom_true_iff

/-- info: 'Shallot.MacroPeg.CBV.RootObservation.branch_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RootObservation.branch_true_iff

/-- info: 'Shallot.MacroPeg.CBV.RootObservation.branch_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RootObservation.branch_false_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.literal_endpoint_obs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.literal_endpoint_obs

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.endpoint_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.endpoint_success

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.endpoint_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.endpoint_failure

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.sequence_success_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.sequence_success_test

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.sequence_failure_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.sequence_failure_test

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.alternative_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.alternative_success

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.alternative_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.alternative_failure

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.negation_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.negation_success

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.exists_predicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.exists_predicate

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.terminal_success_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.terminal_success_test

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.terminal_failure_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.terminal_failure_test

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.le_predicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.le_predicate

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.captured_success_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.captured_success_test

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.captured_failure_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.captured_failure_test

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledParameter_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledParameter_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.repetition_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.repetition_test

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledStar_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledStar_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledNot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledNot_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledSequence_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledSequence_correct

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.clockBorrow_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.clockBorrow_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.clockBlock_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.clockBlock_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.clockBlock_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.clockBlock_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compileCandidate_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compileCandidate_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compileCandidate_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compileCandidate_at

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledAtom_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledAtom_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledAlt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledAlt_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledLookup_obs_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledLookup_obs_iff

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledLookup_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledLookup_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledArguments_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledArguments_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compiledEvaluator_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compiledEvaluator_correct

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.compilerBootstrap_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.compilerBootstrap_iff

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.translate_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.translate_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParSimulation.translate_recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParSimulation.translate_recognizes

/-- info: 'Shallot.PegSeparation.firstOrder_seq_subset_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_seq_subset_par

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptures.partition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptures.partition

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptures.length_accounting' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptures.length_accounting

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptures.stationary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptures.stationary

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptures.forward_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptures.forward_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptures.strict_progress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptures.strict_progress

/-- info: 'Shallot.MacroPeg.CBV.ReplayFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ReplayFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ReplayFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.ReplayFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ReplayFusion.recognizes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFusion.recognizes_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairFusion.parameters_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairFusion.parameters_eq

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairFusion.recognizes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairFusion.recognizes_iff

/-- info: 'Shallot.MacroPeg.CBV.CaptureObservability.evaluator_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureObservability.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.CaptureObservability.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureObservability.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.CaptureObservability.dead_environment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureObservability.dead_environment

/-- info: 'Shallot.MacroPeg.CBV.CaptureObservability.absent_character' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureObservability.absent_character

/-- info: 'Shallot.MacroPeg.CBV.CaptureObservability.no_literal_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureObservability.no_literal_residual

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.prefix_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.prefix_dead

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.no_finite_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.no_finite_summary

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.consume_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.consume_prefix

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.balanced_observation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.balanced_observation

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.balanced_recognizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.balanced_recognizes

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.no_balanced_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.no_balanced_factorization

/-- info: 'Shallot.MacroPeg.CBV.SequentialClock.arguments_metadata' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialClock.arguments_metadata

/-- info: 'Shallot.MacroPeg.CBV.SequentialClock.expression_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialClock.expression_agree

/-- info: 'Shallot.MacroPeg.CBV.SequentialClock.position_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialClock.position_stable

/-- info: 'Shallot.MacroPeg.CBV.SequentialClock.finite_eval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialClock.finite_eval_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialClock.decide_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialClock.decide_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialClock.decide_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialClock.decide_none_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialRecompute.query_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRecompute.query_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialRecompute.observation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRecompute.observation_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialRecompute.observation_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRecompute.observation_none_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanRecompute.matchCount_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanRecompute.matchCount_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanRecompute.query_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanRecompute.query_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanRecompute.arguments_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanRecompute.arguments_valid

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanRecompute.observation_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanRecompute.observation_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanRecompute.observation_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanRecompute.observation_none_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanRecompute.run_accepts_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanRecompute.run_accepts_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialStack.initial_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStack.initial_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStack.result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStack.result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialStack.drive_result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStack.drive_result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialStack.drive_accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStack.drive_accepts_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackRank.step_ranked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackRank.step_ranked

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackRank.reachable_stack_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackRank.reachable_stack_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackRank.stack_linear_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackRank.stack_linear_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackPayload.step_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackPayload.step_typed

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackPayload.reachable_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackPayload.reachable_typed

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackPayload.reachable_payload_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackPayload.reachable_payload_bounds

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackPayload.reachable_capture_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackPayload.reachable_capture_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCode.step_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCode.step_code

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCode.reachable_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCode.reachable_code

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackPool.reachable_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackPool.reachable_ok

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCodec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCodec.decode_encode

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCodec.reachable_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCodec.reachable_roundtrip

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCodec.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCodec.encode_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCodecBound.reachable_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCodecBound.reachable_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackCodecBound.reachable_numbers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackCodecBound.reachable_numbers

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackBinary.unpack_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackBinary.unpack_pack

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackBinary.reachable_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackBinary.reachable_roundtrip

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackBinary.numberBound_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackBinary.numberBound_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackBinary.reachable_bit_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackBinary.reachable_bit_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackBinary.stepBits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackBinary.stepBits_correct

/-- info: 'Shallot.MacroPeg.CBV.SequentialStackBinary.stepBits_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStackBinary.stepBits_bound

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.succClock_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.succClock_spec

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.pred_succClock' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.pred_succClock

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.successorBody_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.successorBody_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.successor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.successor_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.tupleAny_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.tupleAny_true_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.tupleRules_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.tupleRules_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.tupleRules_rules' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.tupleRules_rules

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.tupleBlock_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.tupleBlock_test

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.tupleSearch_predicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.tupleSearch_predicate

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.digitsOf_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.digitsOf_value

/-- info: 'Shallot.MacroPeg.CBV.PrefixCounters.clockValue_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixCounters.clockValue_lt

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.compile_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.compile_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.start_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.start_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.compile_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.compile_at

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.timed_call_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.timed_call_iff

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.stateNext_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.stateNext_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.headNext_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.headNext_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.cellNext_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.cellNext_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.compiled_read_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.compiled_read_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.initialCell_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.initialCell_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.zeroBody_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.zeroBody_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.incHead_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.incHead_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.decHead_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.decHead_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.movedHead_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.movedHead_test

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.tableau_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.tableau_sim

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.read_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.read_sim

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.start_recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.start_recognizes

/-- info: 'Shallot.MacroPeg.CBV.ParTableau.polynomial_recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParTableau.polynomial_recognizes

/-- info: 'Shallot.PegSeparation.firstOrder_par_contains_P_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_par_contains_P_projection

/-- info: 'Shallot.PegSeparation.firstOrder_par_contains_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.firstOrder_par_contains_P

/-- info: 'Shallot.PegSeparation.readLetter_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.readLetter_spec

/-- info: 'Shallot.PegSeparation.nruns_loadLetters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.nruns_loadLetters

/-- info: 'Shallot.MacroPeg.CBV.bitWordProgram_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.bitWordProgram_halts

/-- info: 'Shallot.MacroPeg.CBV.bitWordLanguage_in_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.bitWordLanguage_in_P

/-- info: 'Shallot.PegSeparation.binary_par_iff_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_par_iff_P

/-- info: 'Shallot.PegSeparation.binary_reverse_iff_seq_covers_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_reverse_iff_seq_covers_P

/-- info: 'Shallot.PegSeparation.original_reverse_requires_seq_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.original_reverse_requires_seq_P

/-- info: 'Shallot.PegSeparation.binary_P_witness_separates_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_P_witness_separates_original

/-- info: 'Complexity.BinaryWord.take_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.take_runs

/-- info: 'Complexity.BinaryWord.horner_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.horner_runs

/-- info: 'Complexity.BinaryWord.read_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.read_runs

/-- info: 'Complexity.BinaryWord.runs_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.runs_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRead.read_word_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRead.read_word_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRead.read_word_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRead.read_word_tape

/-- info: 'Complexity.BinaryWord.half_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.half_runs

/-- info: 'Complexity.BinaryWord.digit_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.digit_runs

/-- info: 'Complexity.BinaryWord.emit_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.emit_runs

/-- info: 'Complexity.BinaryWord.write_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.write_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordWrite.write_word_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordWrite.write_word_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordWrite.write_word_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordWrite.write_word_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordCycle.cycle_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordCycle.cycle_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordCycle.cycle_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordCycle.cycle_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordCycle.fieldSpace_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordCycle.fieldSpace_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordCycle.field_cycle_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordCycle.field_cycle_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordCycle.field_cycle_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordCycle.field_cycle_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialFront.step_front' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFront.step_front

/-- info: 'Shallot.MacroPeg.CBV.SequentialFront.local_stack_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFront.local_stack_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialFront.encoded_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFront.encoded_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialFront.reachable_prefix_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFront.reachable_prefix_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialFront.reachable_step_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFront.reachable_step_prefix

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRead.read_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRead.read_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRead.read_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRead.read_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRead.frontSpace_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRead.frontSpace_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRead.reachable_read_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRead.reachable_read_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRead.reachable_read_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRead.reachable_read_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialFieldFetch.fetch_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFieldFetch.fetch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFieldFetch.repeat_fetch_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFieldFetch.repeat_fetch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFieldFetch.counted_fetch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFieldFetch.counted_fetch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScan.parser_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScan.parser_correct

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScan.splitFront_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScan.splitFront_correct

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScanMachine.eval_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScanMachine.eval_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScanMachine.compile_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScanMachine.compile_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScanMachine.parser_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScanMachine.parser_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScanMachine.reachable_parser_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScanMachine.reachable_parser_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontScanMachine.reachable_parser_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontScanMachine.reachable_parser_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontWrite.pull_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontWrite.pull_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontWrite.body_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontWrite.body_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontWrite.loop_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontWrite.loop_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontWrite.write_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontWrite.write_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontWrite.write_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontWrite.write_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRoundtrip.roundtrip_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRoundtrip.roundtrip_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRoundtrip.roundtrip_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRoundtrip.roundtrip_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrontRoundtrip.write_attach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrontRoundtrip.write_attach

/-- info: 'Complexity.LExec.rename_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.LExec.rename_frame

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturn.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturn.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturn.scratchSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturn.scratchSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturn.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturn.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturn.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturn.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturn.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturn.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturnMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturnMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNotReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNotReturnMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialLocalPipeline.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLocalPipeline.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturn.resume_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturn.resume_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturn.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturn.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturn.scratchSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturn.scratchSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturn.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturn.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturn.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturn.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturn.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturn.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturnMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturnMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeqReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeqReturnMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialNumericBlock.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNumericBlock.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNumericBlock.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNumericBlock.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturn.resume_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturn.resume_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturn.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturn.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturn.scratchSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturn.scratchSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturn.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturn.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturn.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturn.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturnMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturnMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAltReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAltReturnMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallReturn.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallReturn.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallReturn.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallReturn.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallReturn.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallReturn.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallReturnMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturn.success_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturn.success_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturn.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturn.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturn.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturn.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturn.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturn.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentBind.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentBind.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentBind.bind_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentBind.bind_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentBind.bind_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentBind.bind_tape

/-! Shrinking comparison and capture endpoint selection. -/

/-- info: 'Complexity.NShrinkingCompare.exec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NShrinkingCompare.exec

/-- info: 'Complexity.NShrinkingCompare.empty_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NShrinkingCompare.empty_iff

/-- info: 'Complexity.NShrinkingCompare.positive_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NShrinkingCompare.positive_iff

/-- info: 'Complexity.NShrinkingCompare.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NShrinkingCompare.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureMin.exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureMin.exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureMin.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureMin.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNumericBlock.frame_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNumericBlock.frame_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNumericBlock.annotated_local_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNumericBlock.annotated_local_runs

/-! Complete argument-head returns, including capture creation. -/

/-- info: 'Complexity.NShrinkingCompare.caseTop_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NShrinkingCompare.caseTop_exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadReturn.numeric_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadReturn.numeric_exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadReturn.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadReturn.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadReturn.scratchSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadReturn.scratchSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.core_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.core_exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.numeric_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.numeric_exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadDispatch.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadReturnMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadReturnMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadReturnMachine.transition_tape

/-! Repetition returns and fixed source-expression lookup. -/

/-- info: 'Complexity.NTableLookup.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NTableLookup.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarLookup.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarLookup.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturn.prepare_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturn.prepare_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturn.resume_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturn.resume_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturn.stop_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturn.stop_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturn.base_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturn.base_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturn.core_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturn.core_exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturn.scratchSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturn.scratchSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarDispatch.numeric_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarDispatch.numeric_exec

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarDispatch.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarDispatch.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarDispatch.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarDispatch.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturnMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturnMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarReturnMachine.transition_tape

/-! Input-driven dispatch across all return frames. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnScan.lift_trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnScan.lift_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnScan.frame_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnScan.frame_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnScan.parser_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnScan.parser_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnScan.compile_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnScan.compile_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnScanMachine.selected_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnScanMachine.selected_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnMachine.transition_tape

/-! Capture-preserving argument evaluation entry. -/

/-- info: 'Complexity.NCountedTransfer.words_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NCountedTransfer.words_runs

/-- info: 'Complexity.NCountedTransfer.counted_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NCountedTransfer.counted_runs

/-- info: 'Complexity.NCountedTransfer.copyAll_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NCountedTransfer.copyAll_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNumericFive.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNumericFive.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialNumericFive.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialNumericFive.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntry.startCons_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntry.startCons_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntry.nil_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntry.nil_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntry.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntry.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntry.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntry.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntry.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntry.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgsEntryMachine.transition_tape

/-! Input-driven rule queries with clock and capture preservation. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialRuleLookup.exists_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRuleLookup.exists_rule

/-- info: 'Shallot.MacroPeg.CBV.SequentialRuleLookup.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRuleLookup.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntry.prepare_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntry.prepare_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntry.resume_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntry.resume_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntry.nil_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntry.nil_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntry.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntry.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntry.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntry.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntry.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntry.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEntryMachine.transition_tape

/-! Source-selected structural expression entry and frame construction. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrameBuild.seq_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrameBuild.seq_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrameBuild.both_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrameBuild.both_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrameBuild.not_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrameBuild.not_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialFrameBuild.runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFrameBuild.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntry.readHead_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntry.readHead_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntry.capture_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntry.capture_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntry.body_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntry.body_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntry.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntry.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntry.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntry.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntry.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntry.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStructuralEntryMachine.transition_tape

/-! Arity-checked call entry with capture preservation. -/

/-- info: 'Complexity.NPushFields.runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NPushFields.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.allowed_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.allowed_bounds

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.startArgs_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.startArgs_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.finishCall_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.finishCall_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.valid_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.valid_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.invalid_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.invalid_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.local_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.local_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntry.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntry.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntryMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntryMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntryMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntryMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntryMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntryMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallEntryMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallEntryMachine.transition_tape

/-! Restoring character reads with direct intermediate space bounds. -/

/-- info: 'Complexity.NBoundedTransfer.move_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NBoundedTransfer.move_runs

/-- info: 'Complexity.NBoundedTransfer.family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NBoundedTransfer.family

/-- info: 'Complexity.NBoundedTransfer.counted_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NBoundedTransfer.counted_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.positive_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.positive_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.zero_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.zero_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.code_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.code_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.code_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.code_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.encoded_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.read_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.read_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.result_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.result_zero_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputRead.read_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputRead.read_tape

/-! Ambient numeric register frames and restoring two-cursor comparisons. -/

/-- info: 'Complexity.NPrim.rename_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NPrim.rename_apply

/-- info: 'Complexity.nfits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.nfits_frame

/-- info: 'Complexity.NExec.rename_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NExec.rename_frame

/-- info: 'Complexity.NExec.post' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Complexity.NExec.post

/-- info: 'Complexity.NBoundedTransfer.FitsRuns.rename_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NBoundedTransfer.FitsRuns.rename_frame

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.read_into' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.read_into

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.pair_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.pair_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.linear_pair_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.linear_pair_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.equalTest_compared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.equalTest_compared

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.compare_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.compare_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.compiled_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.compiled_compare

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.compare_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.compare_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.code_eq_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.code_eq_test

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPair.matchCount_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPair.matchCount_step

/-! Original-input capture-interval loops with linear intermediate workspace. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.reg_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.reg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.body_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.body_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.loop_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.loop_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.scan_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.scan_correct

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.setup_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.setup_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.value_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.value_output

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.span_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.span_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.span_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.span_value

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.compiled_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.compiled_span

/-- info: 'Shallot.MacroPeg.CBV.SequentialSpanMachine.span_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSpanMachine.span_tape

/-! Header-bounded environment lookup and original-input parameter matching. -/

/-- info: 'Complexity.NExec.weaken' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Complexity.NExec.weaken

/-- info: 'Complexity.NBoundedTransfer.FitsRuns.mono_space' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Complexity.NBoundedTransfer.FitsRuns.mono_space

/-- info: 'Shallot.MacroPeg.CBV.SequentialEnvLookup.drain_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEnvLookup.drain_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEnvLookup.search_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEnvLookup.search_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEnvLookup.lookup_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEnvLookup.lookup_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEnvLookup.lookup_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEnvLookup.lookup_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.spanReg_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.spanReg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.envReg_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.envReg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.param_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.param_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.param_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.param_value

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.capacity_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.capacity_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.linear_param_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.linear_param_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.compiled_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.compiled_param

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMachine.param_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMachine.param_tape

/-! Original-input character predicates and fixed literal scans. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialCodeTest.interval_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCodeTest.interval_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCodeTest.predicate_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCodeTest.predicate_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCodeTest.predicate_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCodeTest.predicate_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.testReg_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.testReg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.capacity_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.capacity_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.character_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.character_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.value_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.value_output

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.character_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.character_value

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.compiled_character' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.compiled_character

/-- info: 'Shallot.MacroPeg.CBV.SequentialCharacterMachine.character_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCharacterMachine.character_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.capacity_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.capacity_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.literal_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.literal_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.scan_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.scan_correct

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.value_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.value_final

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.literal_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.literal_value

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.compiled_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.compiled_literal

/-- info: 'Shallot.MacroPeg.CBV.SequentialLiteralRead.literal_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialLiteralRead.literal_tape

/-! Expression-ID atom dispatch and ordinary value-task result encoding. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.prepareTail_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.prepareTail_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.prepare_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.prepare_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.finish_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.finish_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.prepare_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.prepare_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.finish_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.finish_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.selected_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.selected_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.original_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.original_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.input_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.input_prefix

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomCodec.output_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomCodec.output_prefix

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.drain_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.drain_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.body_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.body_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.atom_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.atom_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.space_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.space_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.compiled_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.compiled_numeric

/-- info: 'Shallot.MacroPeg.CBV.SequentialSimpleAtom.numeric_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSimpleAtom.numeric_tape

/-! Original-input read adapters returning ordinary encoded value tasks. -/

/-- info: 'Complexity.NBoundedConstant.push_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.NBoundedConstant.push_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.reg_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.reg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.normalize_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.normalize_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.result_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.result_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.space_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.space_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.bounded_result_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.bounded_result_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.input_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.input_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomResult.frame_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomResult.frame_size

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.scan_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.scan_bounds

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.final_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.final_view

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.view_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.view_bounds

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.capacity_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.capacity_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.param_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.param_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.compiled_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.compiled_param

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamResult.param_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamResult.param_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.reg_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.reg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.return_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.return_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.character_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.character_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.literal_scan_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.literal_scan_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.literal_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.literal_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.characterSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.characterSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.literalSpace_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.literalSpace_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.compiled_character' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.compiled_character

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.compiled_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.compiled_literal

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.character_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.character_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadResult.literal_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadResult.literal_tape

/-! Uniform source-ID selection of every original-input atomic transition. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomBranch.discard_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomBranch.discard_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomBranch.branch_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomBranch.branch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomBranch.reserve_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomBranch.reserve_affine

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.prepReg_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.prepReg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.branchReg_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.branchReg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.selected_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.selected_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.space_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.space_affine

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.capacity_affine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.capacity_affine

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.bounded_selected_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.bounded_selected_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.compiled_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.compiled_selected

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomSelect.selected_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomSelect.selected_tape

/-! Original-input-preserving atomic transitions between binary machine states. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.old_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.old_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.extend_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.extend_get

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.extend_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.extend_project

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.extend_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.extend_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.old_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.old_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.atomReg_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.atomReg_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputHost.atom_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputHost.atom_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputPipeline.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputPipeline.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomMachine.transition_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomMachine.transition_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialAtomMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAtomMachine.space_bound

/-! Actual task/source selection for every input-preserving nonterminal step. -/

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepScan.parser_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepScan.parser_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputScan.compile_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputScan.compile_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepScanMachine.selected_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepScanMachine.selected_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepMachine.component_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepMachine.component_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepMachine.transition_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepMachine.transition_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepMachine.space_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepMachine.space_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialTerminalTest.numeric_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTerminalTest.numeric_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTerminalTest.compiled_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTerminalTest.compiled_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTerminalTest.space_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTerminalTest.space_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialTerminalMachine.handler_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTerminalMachine.handler_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTerminalMachine.terminal_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTerminalMachine.terminal_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTerminalMachine.space_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTerminalMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialEvaluationMachine.state_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEvaluationMachine.state_test

/-- info: 'Shallot.MacroPeg.CBV.SequentialEvaluationMachine.reachable_space' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEvaluationMachine.reachable_space

/-- info: 'Shallot.MacroPeg.CBV.SequentialEvaluationMachine.loop_of_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEvaluationMachine.loop_of_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEvaluationMachine.initialized_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEvaluationMachine.initialized_halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialEvaluationMachine.initialized_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEvaluationMachine.initialized_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialEvaluationMachine.answer_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEvaluationMachine.answer_iff

/-- info: 'Complexity.BinaryWord.bitLength_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.bitLength_step

/-- info: 'Complexity.BinaryWord.width_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.width_runs

/-- info: 'Complexity.BinaryWord.positive_width_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.positive_width_runs

/-- info: 'Complexity.BinaryWord.width_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BinaryWord.width_tape

/-- info: 'Complexity.affine_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.affine_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationNumbers.bound_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationNumbers.bound_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationNumbers.runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationNumbers.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationNumbers.tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationNumbers.tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationNumbers.space_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationNumbers.space_linear

/-- info: 'Complexity.append_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.append_runs

/-- info: 'Complexity.moveAll_runs_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.moveAll_runs_bounded

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationFields.assemble_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationFields.assemble_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationFields.initial_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationFields.initial_fields

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationFields.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationFields.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInitializationFields.space_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInitializationFields.space_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeedMachine.halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeedMachine.halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeedMachine.tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeedMachine.tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeedMachine.recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeedMachine.recognizes

/-- info: 'Shallot.MacroPeg.CBV.SequentialSeedMachine.space_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSeedMachine.space_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputLength.scan_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputLength.scan_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputLength.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputLength.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputLength.encS_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputLength.encS_count

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputLength.original_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputLength.original_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialInputLength.space_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialInputLength.space_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialEncodedMachine.halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEncodedMachine.halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialEncodedMachine.tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEncodedMachine.tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialEncodedMachine.recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEncodedMachine.recognizes

/-- info: 'Shallot.MacroPeg.CBV.SequentialEncodedMachine.space_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEncodedMachine.space_bound

/-- info: 'Complexity.LProg.ConstOK.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Complexity.LProg.ConstOK.mono

/-- info: 'Complexity.LProg.exists_constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.LProg.exists_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryLoader.reverseFields_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryLoader.reverseFields_reverse

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryLoader.scan_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryLoader.scan_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryLoader.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryLoader.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.lists_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.lists_halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.recognizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.recognizes

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.machine

/-- info: 'Complexity.TM.SpaceBounded.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Complexity.TM.SpaceBounded.mono

/-- info: 'Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.space_nlog_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialBinaryInputMachine.space_nlog_bound

/-- info: 'Shallot.PegSeparation.binary_seq_in_nlog_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_seq_in_nlog_space

/-- info: 'Shallot.PegSeparation.binary_reverse_requires_P_nlog_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_reverse_requires_P_nlog_space

/-- info: 'Shallot.PegSeparation.original_reverse_requires_P_nlog_space' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.original_reverse_requires_P_nlog_space

/-- info: 'Shallot.PegSeparation.P_outside_nlog_space_separates_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.P_outside_nlog_space_separates_original

/-- info: 'Shallot.MacroPeg.CBV.CallLookahead.render_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CallLookahead.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.CallLookahead.evaluator_of_peek' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CallLookahead.evaluator_of_peek

/-- info: 'Shallot.MacroPeg.CBV.CallLookahead.tables_peeked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CallLookahead.tables_peeked

/-- info: 'Shallot.MacroPeg.CBV.CallLookahead.evaluator_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CallLookahead.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.CallLookahead.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CallLookahead.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ReplayTestFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayTestFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ReplayTestFusion.recognizes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayTestFusion.recognizes_iff

/-- info: 'Shallot.MacroPeg.CBV.ReplayTestFusion.language_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayTestFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairTestFusion.render_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairTestFusion.render_commute

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairTestFusion.wrapped_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairTestFusion.wrapped_pair

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairTestFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairTestFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixPairTestFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixPairTestFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.LiteralArguments.guards_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralArguments.guards_eval

/-- info: 'Shallot.MacroPeg.CBV.LiteralArguments.arguments_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralArguments.arguments_eval

/-- info: 'Shallot.MacroPeg.CBV.LiteralArguments.resolveArgs_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralArguments.resolveArgs_bounds

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.mem_specs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.mem_specs

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.target_zero_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.target_zero_arity

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.evaluator_of_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.evaluator_of_related

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.tables_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.tables_related

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.limit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.limit_eq

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecialization.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecialization.language_translation

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.collect_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.collect_supported

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.grammar_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.grammar_supported

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.LiteralSpecializationCompiler.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ChoiceArguments.branch_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceArguments.branch_eval

/-- info: 'Shallot.MacroPeg.CBV.ChoiceArguments.select_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceArguments.select_eval

/-- info: 'Shallot.MacroPeg.CBV.ChoiceArguments.selectArgs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceArguments.selectArgs_eval

/-- info: 'Shallot.MacroPeg.CBV.ChoiceArguments.arguments_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceArguments.arguments_bounds

/-- info: 'Shallot.MacroPeg.CBV.ChoiceArguments.plain_distribution_changes_result' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceArguments.plain_distribution_changes_result

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecialization.target_zero_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecialization.target_zero_arity

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecialization.evaluator_of_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecialization.evaluator_of_related

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecialization.tables_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecialization.tables_related

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecialization.limit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecialization.limit_eq

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecialization.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecialization.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.collectArg_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.collectArg_supported

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.grammar_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.grammar_supported

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ChoiceSpecializationCompiler.language_translation

/-- info: 'Shallot.MacroPeg.CBV.SequenceArguments.success_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArguments.success_prefix

/-- info: 'Shallot.MacroPeg.CBV.SequenceArguments.probe_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArguments.probe_eval

/-- info: 'Shallot.MacroPeg.CBV.SequenceArguments.pre_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArguments.pre_concat

/-- info: 'Shallot.MacroPeg.CBV.SequenceArguments.selectAt_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArguments.selectAt_eval

/-- info: 'Shallot.MacroPeg.CBV.SequenceArguments.selectArgs_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArguments.selectArgs_eval

/-- info: 'Shallot.MacroPeg.CBV.SequenceArgumentDomain.success_possible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArgumentDomain.success_possible

/-- info: 'Shallot.MacroPeg.CBV.SequenceArgumentDomain.arguments_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArgumentDomain.arguments_bounds

/-- info: 'Shallot.MacroPeg.CBV.SequenceArgumentDomain.closedB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArgumentDomain.closedB_iff

/-- info: 'Shallot.MacroPeg.CBV.SequenceArgumentDomain.supportedB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArgumentDomain.supportedB_iff

/-- info: 'Shallot.MacroPeg.CBV.SequenceArgumentDomain.no_nonempty_palette_for_duplication' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArgumentDomain.no_nonempty_palette_for_duplication

/-- info: 'Shallot.MacroPeg.CBV.SequenceArgumentDomain.concrete_concatenation_checked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceArgumentDomain.concrete_concatenation_checked

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.target_zero_arity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.target_zero_arity

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.tables_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.tables_related

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.limit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.limit_eq

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.check_iff

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.checked_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.checked_observations

/-- info: 'Shallot.MacroPeg.CBV.SequenceSpecialization.checked_language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequenceSpecialization.checked_language_translation

/-- info: 'Shallot.MacroPeg.CBV.HybridFlags.args_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridFlags.args_eval

/-- info: 'Shallot.MacroPeg.CBV.HybridFlags.resolve_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridFlags.resolve_bounds

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayFusion.target_arity_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayFusion.target_arity_one

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayFusion.limit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayFusion.limit_eq

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayCompiler.supported_of_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayCompiler.supported_of_shape

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayCompiler.tails_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayCompiler.tails_supported

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayCompiler.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayCompiler.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayCompiler.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayCompiler.language_translation

/-- info: 'Shallot.MacroPeg.CBV.HybridReplayCompiler.duplication_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HybridReplayCompiler.duplication_shape

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.controls_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.controls_length

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.differences_scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.differences_scan

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.chunks_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.chunks_prefix

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.storage_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.storage_bound

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.reconstruct

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.ranks_mem_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.ranks_mem_controls

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.par_prefixes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.par_prefixes

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.par_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.par_representation

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.prefixExpr_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.prefixExpr_eval

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.evV_rebind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.evV_rebind

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.body_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.body_view

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.common_origin_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.common_origin_body

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.variants_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.variants_length

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.finite_body_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.finite_body_choice

/-- info: 'Shallot.MacroPeg.CBV.CaptureViews.par_body_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureViews.par_body_representation

/-- info: 'Shallot.MacroPeg.CBV.FiniteResidualControl.no_nat_embedding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FiniteResidualControl.no_nat_embedding

/-- info: 'Shallot.MacroPeg.CBV.CommonOriginCaptures.chunks_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CommonOriginCaptures.chunks_cover

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.signature_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.signature_finite

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.signature_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.signature_agree

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.agree_iff_signature' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.agree_iff_signature

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.no_finite_tuple_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.no_finite_tuple_summary

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.partition_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.partition_dead

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.no_partitioned_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.no_partitioned_factorization

/-- info: 'Shallot.MacroPeg.CBV.PartitionResidualControl.no_common_origin_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PartitionResidualControl.no_common_origin_factorization

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.sequenceArgs_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.sequenceArgs_eval

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.render_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.evaluator_of_peek' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.evaluator_of_peek

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.arguments_of_peek' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.arguments_of_peek

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.tables_peeked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.tables_peeked

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.evaluator_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.language_translation

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallLookahead.plain_peek_changes_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallLookahead.plain_peek_changes_result

/-- info: 'Shallot.MacroPeg.CBV.ForwardQueryScan.strip_identifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardQueryScan.strip_identifier

/-- info: 'Shallot.MacroPeg.CBV.ForwardQueryScan.seek_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardQueryScan.seek_before

/-- info: 'Shallot.MacroPeg.CBV.ForwardQueryScan.seek_header_skip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardQueryScan.seek_header_skip

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.grammar_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.grammar_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.readId_obs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.readId_obs

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.query_of_search' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.query_of_search

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.gate_observation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.gate_observation

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.search_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.search_spec

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.query_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.query_observation

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.table_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.table_correct

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.program_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.program_observation

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.table_recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.table_recognizes

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.normalized_program_recognizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.normalized_program_recognizes

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanProgram.accepted_identifier_unbounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanProgram.accepted_identifier_unbounded

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.readId_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.readId_sound

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.gateSyntax_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.gateSyntax_sound

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.recordSyntax_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.recordSyntax_sound

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_sound

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_complete

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_iff

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.syntax_total

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.language_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.language_iff

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.nonserialization_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.nonserialization_failure

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.entry_decides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.entry_decides

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.normalized_language_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.normalized_language_iff

/-- info: 'Shallot.PegSeparation.forwardBoolean_is_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.forwardBoolean_is_seq

/-- info: 'Shallot.PegSeparation.forwardBoolean_normalized_is_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.forwardBoolean_normalized_is_seq

/-- info: 'Shallot.PegSeparation.forwardBoolean_is_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.forwardBoolean_is_par

/-- info: 'Shallot.MacroPeg.CBV.ForwardBooleanSyntax.normalized_entry_decides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ForwardBooleanSyntax.normalized_entry_decides

/-- info: 'Complexity.BoolCircuit.values_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Complexity.BoolCircuit.values_length

/-- info: 'Complexity.BoolCircuit.wellFormed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.BoolCircuit.wellFormed_bound

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.lookup_snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.lookup_snoc

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.compileFrom_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.compileFrom_correct

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.program_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.program_length

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.program_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.program_correct

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.table_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.table_correct

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.recognizes

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.input_language_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.input_language_iff

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.normalized_recognizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.normalized_recognizes

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.program_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.program_bounded

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.encode_length_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.encode_length_bound

/-- info: 'Shallot.MacroPeg.CBV.CircuitProgram.input_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CircuitProgram.input_length_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.Window.weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.Window.weight

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.Window.valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.Window.valid

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.Window.decoded_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.Window.decoded_weight

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.old_new_order' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.old_new_order

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.atom_descending' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.atom_descending

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.return_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.return_scoped

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.step_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.step_scoped

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_scoped

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_past' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_past

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_arguments

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_decoded_arguments' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureRegions.reachable_decoded_arguments

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStack.query_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStack.query_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStack.original_result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStack.original_result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStack.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStack.accepts_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStack.drive_result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStack.drive_result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedSpace.step_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedSpace.step_scoped

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedSpace.reachable_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedSpace.reachable_weight

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedSpace.reachable_captured_characters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedSpace.reachable_captured_characters

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.step_commutes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.step_commutes

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.Runs.lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.Runs.lift

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.step_clock_mass' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.step_clock_mass

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.initial_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.initial_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.reachable_clock_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.reachable_clock_bounds

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.accepts_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.drive_result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.drive_result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedClock.reachable_captured_characters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedClock.reachable_captured_characters

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedRank.step_erases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedRank.step_erases

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedRank.runs_erase' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedRank.runs_erase

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedRank.eraseStack_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedRank.eraseStack_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedRank.stack_linear_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedRank.stack_linear_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedPayload.step_envs_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedPayload.step_envs_ok

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedPayload.reachable_envs_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedPayload.reachable_envs_ok

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedPayload.reachable_frame_captures' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedPayload.reachable_frame_captures

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedPayload.capture_records_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedPayload.capture_records_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedPayload.reachable_valid_captures' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedPayload.reachable_valid_captures

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.atom_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.atom_decode

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.step_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.step_commutes

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.runs_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.runs_decode

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.runs_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.runs_lift

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.original_result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.original_result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.accepts_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWords.drive_result_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWords.drive_result_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWordSpace.reachable_word_characters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWordSpace.reachable_word_characters

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWordSpace.reachable_word_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWordSpace.reachable_word_records

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWordSpace.stack_linear_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWordSpace.stack_linear_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWordSpace.decodeWords_encodeWords' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWordSpace.decodeWords_encodeWords

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedWordSpace.capture_stream_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedWordSpace.capture_stream_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.restore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.restore

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.delta_sum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.delta_sum

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorChain.decodeDeltas_encodeDeltas' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorChain.decodeDeltas_encodeDeltas

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.decode_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.decode_encode

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorChain.Chain.encode_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedCursors.reachable_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedCursors.reachable_chain

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedCursors.cursor_stream_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedCursors.cursor_stream_correct

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedCursors.reachable_cursor_bits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedCursors.reachable_cursor_bits

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedCursors.cursor_bits_linear' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedCursors.cursor_bits_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedPool.reachable_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedPool.reachable_ok

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateCodec.readTask_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateCodec.readTask_write

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateCodec.readFrame_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateCodec.readFrame_write

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateCodec.read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateCodec.read_write

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateCodec.reachable_decode_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateCodec.reachable_decode_encode

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateCodec.encode_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateCodec.encode_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateCodec.reachable_step_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateCodec.reachable_step_commutes

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.reachable_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.reachable_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.exprs_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.exprs_cost

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.task_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.task_cost

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.frame_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.frame_cost

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.reachable_control_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.reachable_control_cost

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.reachable_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.reachable_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialSharedStateBound.encoded_state_linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSharedStateBound.encoded_state_linear

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEdit.drop_relative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEdit.drop_relative

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEdit.duplicate_current' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEdit.duplicate_current

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEdit.drop_saved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEdit.drop_saved

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.scan_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.scan_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.dropBlock_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.dropBlock_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.duplicate_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.duplicate_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.dropSaved_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.dropSaved_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.drop_current_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.drop_current_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.duplicate_current_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.duplicate_current_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.drop_saved_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.drop_saved_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEditMachine.tape_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEditMachine.tape_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEntryMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEntryMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEntryMachine.cursor_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEntryMachine.cursor_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorEntryMachine.cursor_update_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorEntryMachine.cursor_update_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecrease.lowerRest_relative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecrease.lowerRest_relative

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecrease.lower_current' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecrease.lower_current

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement_current_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement_current_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consume_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consume_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consumeFixed_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consumeFixed_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consume_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consume_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement_constOK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.decrement_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consumeFixed_constOK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorDecreaseMachine.consumeFixed_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.actual_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.cursor_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.cursor_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.cursor_update_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.cursor_update_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.finite_alphabet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyCursorMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.blocks_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.blocks_append

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.moveBlock_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.moveBlock_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.discardHead_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.discardHead_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.saveMany_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.saveMany_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.discardMany_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.discardMany_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.replace_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.replace_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.replace_constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.replace_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.after_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.after_layout

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.control_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.control_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.finite_alphabet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialAnyPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.incrementSecond_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.incrementSecond_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialControlEditMachine.incrementSecond_constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialControlEditMachine.incrementSecond_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.after_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.after_layout

/-- info: 'Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEntryPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnControlMachine.decrementSecond_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnControlMachine.decrementSecond_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnControlMachine.decrementSecond_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnControlMachine.decrementSecond_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnControlMachine.dispatch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnControlMachine.dispatch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnControlMachine.dispatch_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnControlMachine.dispatch_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.after_layout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.after_layout

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.cursor_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.cursor_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.control_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.control_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.transfer_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.transfer_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.capture_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.capture_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.wordCode_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.wordCode_encode

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.pre_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.pre_length

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.original_input_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.original_input_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.original_input_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.original_input_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.withInput_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.withInput_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.reachable_buffer_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.reachable_buffer_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.reachable_buffer_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.reachable_buffer_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.wordTape_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.wordTape_append

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.argHead_word_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.argHead_word_target

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.character_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureCopyMachine.character_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.moveLast_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.moveLast_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.scanWord_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.scanWord_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.moveWord_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.moveWord_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.saveEnv_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.saveEnv_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.stash_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.stash_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.splice_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.splice_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.splice_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.splice_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCaptureSpliceMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.before_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.before_words

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.after_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.after_words

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.withInput_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.withInput_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgCapturePackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.bad_after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.bad_after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.bad_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.bad_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.stashAfter_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.stashAfter_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.incrementAfter_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.incrementAfter_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.rotate_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.rotate_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.discard_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.discard_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.stashAfter_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.stashAfter_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.incrementAfter_constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.incrementAfter_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRotateMachine.discard_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRotateMachine.discard_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.before_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.before_words

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.after_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.after_words

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_words

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.bad_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgConsReturnPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.success_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.success_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.unsuccessful_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.unsuccessful_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.other_streams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.other_streams

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.control_only_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.control_only_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialCallPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCallPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryInstallMachine.install_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryInstallMachine.install_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryInstallMachine.constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryInstallMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryInstallMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryInstallMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.other_streams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.other_streams

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.clock_pop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.clock_pop

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.control_clock_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.control_clock_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryEnterPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.reachable_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.reachable_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.aborted_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.aborted_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.word_streams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.word_streams

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.abort_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.abort_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialTagDispatchMachine.dispatch_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTagDispatchMachine.dispatch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTagDispatchMachine.constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTagDispatchMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeControlMachine.restore_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeControlMachine.restore_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeControlMachine.constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeControlMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.swap_twice' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.swap_twice

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.swap_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.swap_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.stashReturnWords_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.stashReturnWords_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.discardCurrent_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.discardCurrent_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.preserveReturnWords_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.preserveReturnWords_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.discardCurrent_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.discardCurrent_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.preserveReturnWords_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.preserveReturnWords_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.result_words_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.result_words_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopeWordMachine.wordProgram_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopeWordMachine.wordProgram_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.word_streams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.word_streams

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.cursor_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.cursor_stream

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.clock_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.clock_push

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.all_changed_streams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.all_changed_streams

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.branch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.branch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.args_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.args_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.fields_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.fields_split

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialScopePackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialScopePackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine.dispatch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine.dispatch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine.compare_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine.compare_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine.constOK' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSymbolDispatchMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.trace_exists' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.trace_exists

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.Trace.split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.Trace.split

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.Trace.stripPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.Trace.stripPrefix

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.stop_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.stop_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.advance_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.advance_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.loop_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.loop_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordMatchMachine.constOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordMatchMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.success_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.success_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.record_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.record_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.restore_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.restore_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.match_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.match_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.constOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordRestoreMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordInputMachine.prepare_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordInputMachine.prepare_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordInputMachine.original_input_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordInputMachine.original_input_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialWordInputMachine.constOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialWordInputMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialCountGuardMachine.guard_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCountGuardMachine.guard_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCountGuardMachine.constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCountGuardMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMatchMachine.skipWords_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMatchMachine.skipWords_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMatchMachine.present_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMatchMachine.present_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMatchMachine.missing_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMatchMachine.missing_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMatchMachine.match_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMatchMachine.match_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamMatchMachine.constOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamMatchMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.finish_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.finish_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialParamPackedMachine.finite_alphabet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialParamPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.reject_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.reject_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.accept_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.accept_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.advance_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.advance_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.match_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.match_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.constOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenMatchMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenInputMachine.original_input_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenInputMachine.original_input_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialTokenInputMachine.constOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialTokenInputMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadTests.literal_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadTests.literal_run

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadTests.atom_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadTests.atom_result

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadPackedMachine.actual_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialReadPackedMachine.finite_alphabet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReadPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.fields

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.unchanged_streams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.unchanged_streams

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.count_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.count_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStaticPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialEightTapeMachine.registers_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEightTapeMachine.registers_injective

/-- info: 'Shallot.MacroPeg.CBV.SequentialEightTapeMachine.lift_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEightTapeMachine.lift_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEightTapeMachine.entry_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEightTapeMachine.entry_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEightTapeMachine.return_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEightTapeMachine.return_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialEightTapeMachine.constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialEightTapeMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorProgressMachine.gap_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorProgressMachine.gap_test

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorProgressMachine.dispatch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorProgressMachine.dispatch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialCursorProgressMachine.constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialCursorProgressMachine.constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.actual_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.actual_step

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.after_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.after_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.before_positions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.before_positions

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.after_positions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.after_positions

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.cursor_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.cursor_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.complete_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.complete_update

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.branch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.branch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.cursor_constOK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.cursor_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.branch_constOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.branch_constOK

/-- info: 'Shallot.MacroPeg.CBV.SequentialStarPackedMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStarPackedMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.execute_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.execute_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.writeExprs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.writeExprs_eq

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.execute_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.execute_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.parse_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.parse_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialQueryDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialQueryDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.kind_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.kind_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialActiveDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine.parse_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine.parse_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine.program_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine.program_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialSyntaxListDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgHeadDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgHeadDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.execute_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.execute_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRefReturnDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnFields.frame_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnFields.frame_fields

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnFields.frame_tag_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnFields.frame_tag_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnFields.value_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnFields.value_fields

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnFields.before_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnFields.before_control

/-- info: 'Shallot.MacroPeg.CBV.SequentialReturnFields.dispatch_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialReturnFields.dispatch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.branch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.branch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.finite_alphabet' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialExpressionReturnDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.rule_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.rule_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.branch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.branch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.frames_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.frames_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialArgumentsReturnDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.task_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.task_fields

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.task_tag_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.task_tag_bound

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.control_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.control_fields

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.branch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.branch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.transition_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.transition_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.transition_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.transition_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialStepDispatchMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialFieldPresenceMachine.dispatch_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialFieldPresenceMachine.dispatch_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialRunningMachine.step_running' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRunningMachine.step_running

/-- info: 'Shallot.MacroPeg.CBV.SequentialRunningMachine.flag_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRunningMachine.flag_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialRunningMachine.running_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialRunningMachine.running_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.reachable_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.reachable_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.marked_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.marked_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.unmark_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.unmark_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.loop_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.loop_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.run_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.run_trace

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.evaluate_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.evaluate_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.evaluate_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.evaluate_tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedLoopMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.input_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.input_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.stage_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.stage_fits

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.body_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.body_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.scan_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.scan_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.seed_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.seed_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.program_runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.program_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.initial_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.initial_shape

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedInitMachine.initialize_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedInitMachine.initialize_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.halt_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.halt_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.final_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.final_halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.recognize_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.recognize_halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.answer_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedHaltMachine.answer_iff

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryLoader.scan_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryLoader.scan_runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryLoader.runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryLoader.runs

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.input_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.input_capacity

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.lists_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.lists_halts

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.tape

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.recognizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.recognizes

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.finite_alphabet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.finite_alphabet

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.machine

/-- info: 'Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.space_linear_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SequentialPackedBinaryInputMachine.space_linear_bound

/-- info: 'Complexity.SpaceLinear.to_nlog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Complexity.SpaceLinear.to_nlog

/-- info: 'Shallot.PegSeparation.binary_seq_in_linear_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_seq_in_linear_space

/-- info: 'Shallot.PegSeparation.binary_reverse_requires_P_linear_space' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_reverse_requires_P_linear_space

/-- info: 'Shallot.PegSeparation.original_reverse_requires_P_linear_space' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.original_reverse_requires_P_linear_space

/-- info: 'Shallot.PegSeparation.P_outside_linear_space_separates_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.P_outside_linear_space_separates_original

/-- info: 'Shallot.PegSeparation.binary_seq_in_P_and_linear_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.PegSeparation.binary_seq_in_P_and_linear_space

-- Arbitrary-arity cumulative-prefix reverse compilation.

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.words_get' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.words_get

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.parsers_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.parsers_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.parameters_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.parameters_eq

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.par_prepend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.par_prepend

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.arguments_factor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.arguments_factor

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.arguments_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.arguments_prefix

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.replay_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.replay_eval

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.arguments_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.arguments_of_shift

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.iterBound_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.iterBound_eq

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.render_commute' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.render_commute

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.parsers_render' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.parsers_render

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.wrapped_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.wrapped_family

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PrefixFamilyTestFusion.language_translation

-- Independent greedy scanner arguments and their fixed reverse compilers.

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.choice_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.choice_eval

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.scan_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.scan_eval

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.scan_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.scan_absorb

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.parsers_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.parsers_collapse

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.arguments_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.arguments_congr

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.independent_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.independent_arguments

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.covers_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.covers_iff

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerArguments.cumulative_nested' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerArguments.cumulative_nested

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.source_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.source_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.render_scans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.render_scans

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.evaluator_of_tables' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.evaluator_of_tables

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.tables_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.tables_eq

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.Test.supported_render' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.Test.supported_render

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.Test.wrapped_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.Test.wrapped_eq

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.Test.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.Test.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.NestedScannerFusion.Test.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.NestedScannerFusion.Test.language_translation

-- Runtime endpoint ordering for independent, non-nested scanner pairs.

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.accepts_intersection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.accepts_intersection

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.first_remainder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.first_remainder

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.guard_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.guard_eval

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.final_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.final_resume

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.pre_concat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.pre_concat

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.sequential_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.sequential_arguments

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.parallel_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.parallel_arguments

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.dispatch_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.dispatch_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.branch_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.branch_eval

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.dispatch_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.dispatch_eval

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.call_of_body_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.call_of_body_relation

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.body_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.body_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.body_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.body_eval

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.dispatch_body_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.dispatch_body_eval

/-- info: 'Shallot.MacroPeg.CBV.ScannerFrontier.stopping_order_switches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerFrontier.stopping_order_switches

-- Recursive fixed compiler for independent, non-nested scanner pairs.

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.par_rule_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.par_rule_count

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.seq_rule_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.seq_rule_count

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.seq_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.chunks_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.chunks_split

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.stable_result_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.stable_result_eq

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ScannerPairFusion.language_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPairFusion.language_translation

-- Compiled finite-state residual selectors and synchronized capture frontiers.

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.run_after_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.run_after_prefix

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.run_suffix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.run_suffix

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.block_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.block_length

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.grammar_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.grammar_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.grammar_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.grammar_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.branches_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.branches_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.query_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.query_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.entry_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.entry_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.grammar_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.grammar_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.grammar_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.grammar_length

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.grammar_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.grammar_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.entry_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.entry_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.probe_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.probe_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.entry_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.entry_observation

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.probe_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.probe_observation

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerBridge.run_stateless' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerBridge.run_stateless

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerBridge.stateless_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerBridge.stateless_observation

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerBridge.resetting_changes_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerBridge.resetting_changes_result

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.next_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.next_joint

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.product_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.product_next

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.run_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.run_product

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.residual_runs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.residual_runs

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.common_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.common_prefix

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.common_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.common_entry

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.common_probe_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.common_probe_observation

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.frontier_stops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.frontier_stops

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerFamily.capture_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerFamily.capture_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerProduct.common_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerProduct.common_capture

-- Combined finite-state scanner arguments, runtime controls, and actual user-body entry.

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.block_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.block_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.block_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.block_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulScanner.entry_of_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScanner.entry_of_layout

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.grammar_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.grammar_length

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.common_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.common_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.left_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.left_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.right_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.right_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.grammar_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.grammar_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.left_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.left_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.right_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.right_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.common_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.common_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.first_remainder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.first_remainder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.common_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.common_bound

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.arguments_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.arguments_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.next_enabled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.next_enabled

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.stopTest_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.stopTest_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.caseGuard_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.caseGuard_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.independent_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.independent_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.final_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.final_bound

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.capture_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.capture_reconstruction

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.controls_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.controls_mem

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.goodCase_iff_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.goodCase_iff_eq

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.dispatch_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.dispatch_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.dispatch_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.dispatch_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.complete_dispatch_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.complete_dispatch_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairArguments.complete_dispatch_body_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairArguments.complete_dispatch_body_eval

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.step_physical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.step_physical

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.step_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.step_mono

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.frozen_rows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.frozen_rows

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.frozen_user_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.frozen_user_step

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.frozen_le_physical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.frozen_le_physical

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.physical_le_frozen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.physical_le_frozen

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.frozen_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.frozen_mono

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.frozen_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.frozen_ok

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.defined_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.defined_iff

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.stable_defined_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.stable_defined_iff

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.rows_ignore_environment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.rows_ignore_environment

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.row_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.row_length

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.rows_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.rows_stable

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.helpers_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.helpers_stable

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.frozen_le_physical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.frozen_le_physical

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.physical_le_frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.physical_le_frozen

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.defined_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.defined_iff

/-- info: 'Shallot.MacroPeg.CBV.StatefulScannerStability.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulScannerStability.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.left_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.left_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.right_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.right_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.common_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.common_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.arguments_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.arguments_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.caseGuard_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.caseGuard_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.independent_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.independent_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.capture_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.capture_reconstruction

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.dispatch_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.dispatch_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.complete_dispatch_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.complete_dispatch_eval

/-- info: 'Shallot.MacroPeg.CBV.FrozenPairArguments.complete_dispatch_body_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FrozenPairArguments.complete_dispatch_body_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.replay_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.replay_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.replay_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.replay_eval

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.render_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.user_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.user_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.par_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.seq_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.chunks_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.chunks_split

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.StatefulPairFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.StatefulPairFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.closed_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.closed_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.closedArgs_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.closedArgs_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.subst_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.subst_closed

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.substArgs_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.substArgs_closed

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.closed_env' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.closed_env

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.render_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.render_closed

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.seq_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.evaluator_of_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ReplayFallbackFusion.fallback_returns_before_capture' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayFallbackFusion.fallback_returns_before_capture

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.all_of_forall' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.all_of_forall

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.all_imp' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.all_imp

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.eval_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.eval_congr

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.eval_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.eval_none

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.exp_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.exp_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.exp_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.Plan.exp_eval

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.callLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.callLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.sourceLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.sourceLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.callLeaf_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.callLeaf_eval

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ReplayControlFusion.capture_dependent_fallback' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ReplayControlFusion.capture_dependent_fallback

/-- info: 'Shallot.MacroPeg.CBV.WordArguments.word_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordArguments.word_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordArguments.word_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordArguments.word_eval

/-- info: 'Shallot.MacroPeg.CBV.WordArguments.value_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordArguments.value_of_success

/-- info: 'Shallot.MacroPeg.CBV.WordArguments.duplication' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordArguments.duplication

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.Plan.firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.Plan.firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.Plan.eval_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.Plan.eval_congr

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.supported_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.supported_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.callLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.callLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.render_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.render_word

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.gate_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.gate_rule

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.callLeaf_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.callLeaf_word

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.enter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.enter_word

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.language_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.WordControlFusion.consuming_prefix_and_repetition' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordControlFusion.consuming_prefix_and_repetition

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.origin_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.origin_congr

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.supported_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.supported_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.word_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.word_supported

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.word_fragment_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.word_fragment_supported

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.physical_gate_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.physical_gate_ok

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.callLeaf_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.callLeaf_congr

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.enter_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.enter_origin

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.evaluator_of_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.MixedControlFusion.fresh_parser_then_consuming_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedControlFusion.fresh_parser_then_consuming_call

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.arg_equiv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.arg_equiv

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.probe_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.probe_eval

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.word_arg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.word_arg

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.selectAt_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.selectAt_eval

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.select_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.select_eval

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.selectAt_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.selectAt_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SymbolicWordSelection.select_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SymbolicWordSelection.select_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.supported_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.supported_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.arg_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.arg_supported

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.mixed_fragment_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.mixed_fragment_supported

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.gate_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.gate_rule

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.physical_gate_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.physical_gate_ok

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.callLeaf_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.callLeaf_congr

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.enter_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.enter_origin

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.callLeaf_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.callLeaf_word

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.enter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.enter_word

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.evaluator_of_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.chosen_word_stays_committed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.chosen_word_stays_committed

/-- info: 'Shallot.MacroPeg.CBV.SelectedControlFusion.growing_argument_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SelectedControlFusion.growing_argument_supported

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.shapeB_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.shapeB_iff

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.checks_imp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.checks_imp

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.arg_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.arg_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.arg_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.arg_eval

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.probe_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.probe_eval

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.selectAt_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.selectAt_eval

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.select_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.select_eval

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.argRender_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.argRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedWordSelection.selectAt_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedWordSelection.selectAt_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.scanArg_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.scanArg_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.chooseAt_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.chooseAt_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.render_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.predicate_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.predicate_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.supported_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.supported_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.shape_of_arg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.shape_of_arg

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.selected_fragment_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.selected_fragment_supported

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.gate_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.gate_rule

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.physical_gate_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.physical_gate_ok

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.callLeaf_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.callLeaf_congr

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.enter_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.enter_origin

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.callLeaf_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.callLeaf_word

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.enter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.enter_word

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.evaluator_of_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.predicate_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.predicate_checks

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.predicate_at_argument_position' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.predicate_at_argument_position

/-- info: 'Shallot.MacroPeg.CBV.GuardedControlFusion.undefined_predicate_stays_undefined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedControlFusion.undefined_predicate_stays_undefined

-- Finite Word selection cannot manufacture arbitrary fresh repetition captures.

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.candidates_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.candidates_word

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.selectAt_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.selectAt_congr

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.success_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.success_candidate

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.value_le_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.value_le_budget

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.capture_le_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.capture_le_budget

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.scanner_replicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.scanner_replicate

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.no_finite_word_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.no_finite_word_family

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.scanner_exceeds_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.scanner_exceeds_family

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.no_shape_scanner_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.no_shape_scanner_equivalent

/-- info: 'Shallot.MacroPeg.CBV.WordSelectionBoundary.scanner_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordSelectionBoundary.scanner_observations

-- Fresh parser captures with repeated-prefix body entry.

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.pure_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.pure_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.pure_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.pure_eval

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.tables_shifted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.evaluator_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.copy_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.copy_valid

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.copy_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.copy_word

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.beyond_finite_word_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.beyond_finite_word_selection

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.nested_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.nested_valid

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.nested_captures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.nested_captures

/-- info: 'Shallot.MacroPeg.CBV.ParserPrefixFusion.nullable_repetition_keeps_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParserPrefixFusion.nullable_repetition_keeps_undefined

-- Independent recursive argument parsers and repeated-prefix fusion.

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.installed

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.lexical_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.lexical_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.lexical_zero_iff_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.lexical_zero_iff_pure

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.lexical_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.lexical_eval

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.helper_rows_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.helper_rows_eq

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.floor_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.floor_agree

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.row_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.row_length

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.helpers_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.helpers_stable

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.frozen_lexical_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.frozen_lexical_eval

/-- info: 'Shallot.MacroPeg.CBV.RecursiveParserStability.cycle_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveParserStability.cycle_undefined

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.render_without_helpers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.render_without_helpers

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.without_helpers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.without_helpers

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.valid_without_helpers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.valid_without_helpers

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.tables_shifted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.evaluator_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_valid

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_prefix_observation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_prefix_observation

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_copy

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_physical_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.balanced_physical_execution

/-- info: 'Shallot.MacroPeg.CBV.RecursivePrefixFusion.recursive_argument_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursivePrefixFusion.recursive_argument_undefined

-- Mixed fixed-parser/replay entries with recursive capture-dependent arguments.

/-- info: 'Shallot.MacroPeg.CBV.ClockFreezing.frozen_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ClockFreezing.frozen_sound

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.render_lift' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.render_lift

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.grammars_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.grammars_lift

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.valid_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.valid_lift

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.language_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.example_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.example_valid

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.mixed_recursive_capture_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.mixed_recursive_capture_execution

/-- info: 'Shallot.MacroPeg.CBV.MixedPrefixFusion.recursive_argument_choice_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedPrefixFusion.recursive_argument_choice_undefined

-- Caller-position control over fresh recursive and arbitrary replay captures.

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.lexical_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.lexical_closed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.callLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.callLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.invoke_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.invoke_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.plan_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.plan_closed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.callLeaf_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.callLeaf_closed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.invoke_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.invoke_closed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.render_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.render_closed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.par_installed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.par_rule

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.entry_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.entry_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.sourceLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.sourceLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.callLeaf_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.callLeaf_eval

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.call_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.call_eval

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.seq_user_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.seq_user_step

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.language_translation

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.example_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.example_valid

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.origin_fallback_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.origin_fallback_execution

/-- info: 'Shallot.MacroPeg.CBV.OriginPrefixControl.undefined_argument_before_local_branch' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OriginPrefixControl.undefined_argument_before_local_branch

-- Fresh origin captures and consuming control with retained Word arguments.

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.originPlan_atOrigin' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.originPlan_atOrigin

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.originPlan_exp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.originPlan_exp

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.lexical_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.lexical_closed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.invoke_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.invoke_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.plan_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.plan_closed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_closed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.invoke_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.invoke_closed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.render_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.render_closed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.par_installed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.par_rule

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.entry_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.entry_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.sourceLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.sourceLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.gate_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.gate_rule

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.frozen_gate_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.frozen_gate_ok

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.render_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.render_word

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.origin_eval_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.origin_eval_congr

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_congr

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.enter_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.enter_origin

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.callLeaf_word

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.enter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.enter_word

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.call_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.call_eval

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.enter_of_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.enter_of_success

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.evaluator_of_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_user_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.seq_user_step

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.leaf_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.leaf_step

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.example_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.example_valid

/-- info: 'Shallot.MacroPeg.CBV.ConsumingPrefixControl.fresh_capture_consuming_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ConsumingPrefixControl.fresh_capture_consuming_execution

-- Fresh recursive captures with guarded selected arguments and consuming control.

/-- info: 'Shallot.MacroPeg.CBV.MappedGuardedWordSelection.arg_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MappedGuardedWordSelection.arg_eval

/-- info: 'Shallot.MacroPeg.CBV.MappedGuardedWordSelection.probe_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MappedGuardedWordSelection.probe_eval

/-- info: 'Shallot.MacroPeg.CBV.MappedGuardedWordSelection.selectAt_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MappedGuardedWordSelection.selectAt_eval

/-- info: 'Shallot.MacroPeg.CBV.MappedGuardedWordSelection.select_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MappedGuardedWordSelection.select_eval

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.originPlan_atOrigin' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.originPlan_atOrigin

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.originPlan_exp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.originPlan_exp

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.word_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.word_shape

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.consuming_supported' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.consuming_supported

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.consuming_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.consuming_valid

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.scanArg_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.scanArg_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.chooseAt_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.chooseAt_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.render_arg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.render_arg

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.source_render_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.source_render_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.lexical_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.lexical_closed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.invoke_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.invoke_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.render_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.predicate_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.predicate_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.plan_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.plan_closed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_closed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.invoke_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.invoke_closed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.render_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.render_closed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.source_grammar_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.source_grammar_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.par_installed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.par_rule

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.entry_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.entry_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.sourceLeaf_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.sourceLeaf_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.gate_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.gate_rule

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.frozen_gate_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.frozen_gate_ok

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.render_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.render_word

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.origin_eval_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.origin_eval_congr

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_congr

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.enter_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.enter_origin

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.callLeaf_word

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.enter_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.enter_word

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.call_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.call_eval

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.enter_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.enter_of_success

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.evaluator_of_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.predicate_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.predicate_checks

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_user_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.seq_user_step

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.leaf_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.leaf_step

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.language_translation

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.original_observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.original_observations_iff

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.original_language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.original_language_translation

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.example_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.example_valid

/-- info: 'Shallot.MacroPeg.CBV.GuardedPrefixControl.fresh_selected_consuming_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GuardedPrefixControl.fresh_selected_consuming_execution

-- Absorbing recursive captures into consuming scanner prefixes.

/-- info: 'Shallot.MacroPeg.CBV.ScannerAbsorption.dropWhile_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerAbsorption.dropWhile_append

/-- info: 'Shallot.MacroPeg.CBV.ScannerAbsorption.literal_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerAbsorption.literal_safe

/-- info: 'Shallot.MacroPeg.CBV.ScannerAbsorption.evaluator_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerAbsorption.evaluator_safe

/-- info: 'Shallot.MacroPeg.CBV.ScannerAbsorption.physical_rows_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerAbsorption.physical_rows_safe

/-- info: 'Shallot.MacroPeg.CBV.ScannerAbsorption.frozen_rows_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerAbsorption.frozen_rows_safe

/-- info: 'Shallot.MacroPeg.CBV.ScannerAbsorption.scan_after_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerAbsorption.scan_after_success

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.same_grammar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.same_grammar

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.example_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.example_valid

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.scanner_before_capture_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.scanner_before_capture_execution

/-- info: 'Shallot.MacroPeg.CBV.ScannerPrefixFusion.recursive_argument_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ScannerPrefixFusion.recursive_argument_undefined

-- Absorbing fresh scanners and arbitrary recursive replay arguments.

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.tables_shifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.render_liftScanner' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.render_liftScanner

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.grammars_liftScanner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.grammars_liftScanner

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.valid_liftScanner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.valid_liftScanner

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.example_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.example_valid

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.scanner_to_recursive_argument_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.scanner_to_recursive_argument_execution

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.unbounded_suffix_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.unbounded_suffix_capture

/-- info: 'Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.recursive_argument_choice_undefined' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MixedScannerPrefixFusion.recursive_argument_choice_undefined

-- Commuting a short unary prefix across a fresh overlapping capture.

/-- info: 'Shallot.MacroPeg.CBV.CaptureCommutation.all_of_dropWhile_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureCommutation.all_of_dropWhile_append

/-- info: 'Shallot.MacroPeg.CBV.CaptureCommutation.captured_alphabet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureCommutation.captured_alphabet

/-- info: 'Shallot.MacroPeg.CBV.CaptureCommutation.unary_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureCommutation.unary_word

/-- info: 'Shallot.MacroPeg.CBV.CaptureCommutation.unary_commutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureCommutation.unary_commutes

/-- info: 'Shallot.MacroPeg.CBV.CaptureCommutation.prefix_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureCommutation.prefix_swap

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.example_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.example_valid

/-- info: 'Shallot.MacroPeg.CBV.UnaryOverlapFusion.overlapping_capture_execution' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.UnaryOverlapFusion.overlapping_capture_execution

-- Periodic block captures and genuinely noncommuting overlap.

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.copies_add' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.copies_add

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.copies_commute' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.copies_commute

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.rotate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.rotate

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.related_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.related_refl

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.related_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.related_trans

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.evaluator_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.evaluator_safe

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.physical_rows_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.physical_rows_safe

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.frozen_rows_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.frozen_rows_safe

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.head_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.head_capture

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.prefix_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.prefix_rotate

/-- info: 'Shallot.MacroPeg.CBV.BlockCapture.ab_noncommuting' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.BlockCapture.ab_noncommuting

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.render_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.par_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.seq_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.par_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.par_rule

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.seq_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.seq_rule

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.evaluator_of_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.evaluator_of_shift

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.lexical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.lexical_eq

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.example_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.example_valid

/-- info: 'Shallot.MacroPeg.CBV.PeriodicOverlapFusion.rotated_overlap_execution' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicOverlapFusion.rotated_overlap_execution

-- Necessary periodicity for arbitrary actual captures and finite rotations.

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.prefix_periodic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.prefix_periodic

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.rotations_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.rotations_length

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.prefix_has_rotation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.prefix_has_rotation

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.prefix_iff_rotation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.prefix_iff_rotation

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.common_input_rotation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.common_input_rotation

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.actual_capture_rotation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.actual_capture_rotation

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.rotation_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.rotation_unique

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.rotation_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.rotation_length

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.actual_capture_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.actual_capture_periodic

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.rotated_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.rotated_execution

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.chooseRotations_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.chooseRotations_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.OverlapNecessity.rotation_choice_false_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.OverlapNecessity.rotation_choice_false_positive

-- Generated finite-state capture filters: local laws and physical executions.

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.run_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.run_append

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.run_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.run_bound

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.core_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.core_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.grammar_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.grammar_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.original_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.original_rule

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.decode

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_rule

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_body_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_body_eval

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.original_call_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.original_call_eval

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.product_call_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.product_call_eval

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.helper_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.helper_valid

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.original_installed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.original_installed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_step

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_commit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_commit

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.left_cycle_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.left_cycle_undefined

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.nullable_star_undefined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.nullable_star_undefined

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.alternating_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.alternating_valid

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.scanner_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.scanner_valid

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.scanner_filter_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.scanner_filter_execution

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.prioritized_filter_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.prioritized_filter_execution

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_eval_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_eval_unique

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.literal_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.literal_correct

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.star_filter_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.star_filter_execution

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.predicate_filter_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.predicate_filter_execution

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.guarded_rotation_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.guarded_rotation_execution

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.defined_at_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.defined_at_fixed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.row_at_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.row_at_fixed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_at_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.filter_at_fixed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.physical_success_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.physical_success_prefix

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.literal_at_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.literal_at_fixed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.select_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.select_success

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.row_success_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.row_success_prefix

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.finite_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.finite_success

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.product_at_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.product_at_fixed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.bound_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.bound_fixed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.product_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.product_correct

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.canonical_helpers_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.canonical_helpers_eq

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.product_source_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.product_source_correct

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.product_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.product_observations

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.next_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.next_bound

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.valid

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.step_sink' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.step_sink

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_sink' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_sink

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.phase_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.phase_step

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_rotation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_rotation

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_take

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.run_copies

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.prefix_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.prefix_run

/-- info: 'Shallot.MacroPeg.CBV.PeriodicCaptureMachine.prefix_iff_nonsink' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.PeriodicCaptureMachine.prefix_iff_nonsink

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.key_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.key_bound

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.lexical_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.lexical_mono

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_lexical' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.choice_lexical

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.core_lexical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.core_lexical

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.component_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.component_valid

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.component_installed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.component_installed

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.extension_call_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.extension_call_eq

/-- info: 'Shallot.MacroPeg.CBV.RegularCaptureProduct.extension_product_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RegularCaptureProduct.extension_product_correct

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.tail_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.tail_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.tail_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.tail_eval

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.source_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.source_rule

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.target_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.target_rule

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.canonical_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.canonical_row

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.source_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.source_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.target_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.target_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.targetStart_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.targetStart_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.choice_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.choice_none

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.choice_fail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.choice_fail

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.replay_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.replay_rotation

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.nonperiodic_replay_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.nonperiodic_replay_fail

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.decide_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.decide_eq

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.language_translation

/-- info: 'Shallot.MacroPeg.CBV.FilteredOverlapCaller.retained_capture_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FilteredOverlapCaller.retained_capture_execution

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rows

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.user_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.user_step

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.frozen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.frozen_le

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.le_frozen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.le_frozen

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.physical_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.physical_bound

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.defined_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.defined_iff

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.prefixSeed_rows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.prefixSeed_rows

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.prefixSeed_lower' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.prefixSeed_lower

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.prefixSeed_upper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.prefixSeed_upper

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.prefixSeed_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.prefixSeed_query

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rounds_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rounds_bound

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rounds_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rounds_ok

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rounds_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rounds_sound

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rounds_lexical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rounds_lexical

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rounds_defined_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rounds_defined_iff

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.word_eval_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.word_eval_eq

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.rounds_failed_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.rounds_failed_prefix

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.stable_defined_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.stable_defined_iff

/-- info: 'Shallot.MacroPeg.CBV.SeededClock.observations_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.SeededClock.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.render_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.par_installed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.par_installed

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.seq_installed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.seq_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.query_eq

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.choice_none' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.choice_none

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.choice_fail' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.choice_fail

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.entry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.entry_eq

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.evaluator_of_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.evaluator_of_rows

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.tables_shifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.language_translation

/-- info: 'Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.recursive_capture_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.RecursiveFilteredOverlap.recursive_capture_execution

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_length

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_get' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_get

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_mem

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.profiles_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.profiles_length

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.member_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.member_length

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.member_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.member_bound

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.profile_append

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.compose_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.compose_correct

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.single_phase_insufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.single_phase_insufficient

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.checks_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.checks_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.guard_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.guard_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.checks_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.checks_eval

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.checks_iff_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.checks_iff_profile

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.guard_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.guard_correct

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.choice_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.choice_unique

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.choice_failed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.choice_failed

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.select_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.select_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.CaptureTransitionProfile.select_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureTransitionProfile.select_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.render_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.render_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.filter_firstOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.filter_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.success_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.success_prefix

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.atom_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.atom_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.correct

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.environment_accurate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.environment_accurate

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.render_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.render_eq

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.correct_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.correct_par

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.guard_accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.guard_accurate

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.guarded_argument_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.guarded_argument_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentCaptureFilter.dependent_argument_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentCaptureFilter.dependent_argument_execution

-- Retained-value-dependent captures through recursive profile-specialized rows.

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.subst_lexical' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.subst_lexical

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.canonical_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.canonical_eval

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.rounds_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.rounds_eval

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.rounds_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.rounds_base

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.render_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.render_safe

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.choice_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.choice_safe

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.filter_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.filter_safe

/-- info: 'Shallot.MacroPeg.CBV.ParametricHelperControl.filter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ParametricHelperControl.filter_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.checks_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.checks_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.guard_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.guard_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.select_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.select_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.filter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.filter_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.checks_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.checks_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.guard_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.guard_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.select_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.select_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.index_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.index_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.specialized_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.specialized_rule

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.specialized_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.specialized_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.entry_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.entry_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.entry_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.entry_correct

/-- info: 'Shallot.MacroPeg.CBV.DependentProfileCall.entry_par_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.DependentProfileCall.entry_par_correct

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.parRender_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.parRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.seqRender_firstOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.seqRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.seq_firstOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.par_installed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.seq_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.entry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.entry_eq

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.evaluator_of_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.evaluator_of_rows

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.nonperiodic_replay_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.nonperiodic_replay_fail

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.prefix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.prefix_eq

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.tables_shifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.evaluator_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.ProfiledDependentRecursion.dependent_recursive_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.ProfiledDependentRecursion.dependent_recursive_execution

-- Mutual retained-value-dependent user families.

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.parRender_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.parRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.seqRender_firstOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.seqRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.source_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.source_rule

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.key_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.key_mem

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.target_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.target_rule

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.seq_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.par_installed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.seq_installed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.selected_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.selected_call

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.entry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.entry_eq

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.evaluator_of_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.evaluator_of_rows

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.tables_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.evaluator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.MutualProfiledRecursion.mutual_capture_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.MutualProfiledRecursion.mutual_capture_execution

-- Heterogeneous fixed shifts in mutually recursive captured-value users.

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.sum_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.sum_valid

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.run_left' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.run_left

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.run_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.run_right

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.combine_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.combine_valid

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.offset_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.offset_bound

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.run_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.run_component

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.profile_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.profile_component

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.phase_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.phase_valid

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.machines_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.machines_valid

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.valid

/-- info: 'Shallot.MacroPeg.CBV.CaptureMachineFamily.phase_profile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureMachineFamily.phase_profile

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.parRender_firstOrder' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.parRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.seqRender_firstOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.seqRender_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.source_rule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.source_rule

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.key_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.key_mem

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.target_rule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.target_rule

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.par_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.par_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.seq_firstOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.seq_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.par_installed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.par_installed

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.seq_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.seq_installed

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.selected_call

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.entry_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.entry_eq

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.evaluator_of_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.evaluator_of_rows

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.tailPrefix_actual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.tailPrefix_actual

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.prefix_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.prefix_eq

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.tables_shifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.tables_shifted

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.evaluator_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.evaluator_eq

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.observations_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.observations_iff

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.language_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousProfiledRecursion.language_translation

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.nodes_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.nodes_valid

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.users_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.users_valid

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.joint_phase_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.joint_phase_execution

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.source_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.source_execution

/-- info: 'Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.translated_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.HeterogeneousReplayExamples.translated_observations

-- Inline retained-Word stars in dependent capture arguments.

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.orbit_add' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.orbit_add

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.orbit_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.orbit_bound

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.nodup_subset_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.nodup_subset_length

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.bounded_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.bounded_collision

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.orbit_shift' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.orbit_shift

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.loop_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.loop_mul

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.mem_descriptors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.mem_descriptors

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.descriptors_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.descriptors_sound

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.descriptors_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.descriptors_complete

/-- info: 'Shallot.MacroPeg.CBV.CaptureOrbit.descriptors_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CaptureOrbit.descriptors_iff

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.trace_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.trace_le

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.trace_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.trace_lt

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.trace_steps' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.trace_steps

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.trace_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.trace_split

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.overrun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.overrun

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.star_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.star_trace

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.trace_star' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.trace_star

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.copies_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.copies_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.pattern_firstOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.pattern_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.copies_eval' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.copies_eval

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.finish_trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.finish_trace

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.grouped_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.grouped_finish

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.pattern_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.pattern_eval

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.fits_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.fits_iff

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.evaluatePattern_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.evaluatePattern_trace

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.pattern_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.pattern_ok

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.pattern_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.pattern_fail

/-- info: 'Shallot.MacroPeg.CBV.InlineRepeat.choice_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.InlineRepeat.choice_success

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.transition_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.transition_bound

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.summary_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.summary_correct

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.step_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.step_correct

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.success_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.success_prefix

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.trace_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.trace_run

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.filter_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.filter_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.correct

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.word_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.word_safe

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.copies_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.copies_safe

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.pattern_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.pattern_safe

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.choice_safe' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.choice_safe

/-- info: 'Shallot.MacroPeg.CBV.WordStarFilter.filter_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarFilter.filter_safe

/-- info: 'Shallot.MacroPeg.CBV.WordStarExamples.greedy_filter_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarExamples.greedy_filter_execution

/-- info: 'Shallot.MacroPeg.CBV.WordStarExamples.nodes_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarExamples.nodes_valid

/-- info: 'Shallot.MacroPeg.CBV.WordStarExamples.users_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarExamples.users_valid

/-- info: 'Shallot.MacroPeg.CBV.WordStarExamples.source_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarExamples.source_execution

/-- info: 'Shallot.MacroPeg.CBV.WordStarExamples.translated_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.WordStarExamples.translated_observations

-- General inline star via first-return state elimination.

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.run_head' does not depend on any axioms -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.run_head

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.run_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.run_length

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_sound

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_mem

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.run_positions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.run_positions

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_position_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_position_le

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_eliminate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_eliminate

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.hit_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.hit_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.step_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.step_last

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.step_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.step_cons

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.hit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.hit_correct

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_source

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_ends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_ends

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.scan_reaches_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.scan_reaches_end

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.returns_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.returns_correct

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.finished_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.finished_correct

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.step_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.step_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.finished_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.finished_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.step_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.step_safe

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.hit_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.hit_safe

/-- info: 'Shallot.MacroPeg.CBV.FirstReturn.finished_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.FirstReturn.finished_safe

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarFilter.lift_trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarFilter.lift_trace

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarFilter.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarFilter.correct

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarFilter.filter_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarFilter.filter_firstOrder

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarFilter.filter_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarFilter.filter_safe

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarExamples.varying_capture_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarExamples.varying_capture_execution

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarExamples.nodes_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarExamples.nodes_valid

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarExamples.users_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarExamples.users_valid

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarExamples.source_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarExamples.source_execution

/-- info: 'Shallot.MacroPeg.CBV.GeneralStarExamples.translated_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.GeneralStarExamples.translated_observations

-- Physical captured-prefix rows and observer handoff.

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.captured_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.captured_word

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.prefix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.prefix_eq

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.shifted_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.shifted_of_rows

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.rows

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.filter_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.filter_prefix

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.row_success_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.row_success_prefix

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.filtered_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.filtered_rows

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.filtered_rows_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.filtered_rows_profile

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.rows_of_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.rows_of_capture

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.users_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.users_valid

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.source_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.source_execution

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.target_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.target_execution

/-- info: 'Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.observer_handoff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.CBV.CapturePrefixRows.Examples.observer_handoff
