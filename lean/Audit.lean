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
