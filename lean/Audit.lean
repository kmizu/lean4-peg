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

/-- info: 'Shallot.MacroPeg.atm_by_decision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shallot.MacroPeg.atm_by_decision

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
