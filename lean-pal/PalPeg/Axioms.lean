import PalPeg.Basic
import PalPeg.Existence
import PalPeg.EvenLength
import PalPeg.Words
import PalPeg.Chain
import PalPeg.Structure
import PalPeg.Groups
import PalPeg.GroupsLog
import PalPeg.GroupsLogBound
import PalPeg.Matching
import PalPeg.GSScan
import PalPeg.GSDecomp
import PalPeg.GSDecompL1
import PalPeg.GSPreprocess
import PalPeg.GSRealTime
import PalPeg.GSVerifier
import PalPeg.GSScanTapes
import PalPeg.GSVerifierTapes
import PalPeg.TextFeed
import PalPeg.BorderJob
import PalPeg.BorderJobTapes
import PalPeg.RTQueue
import PalPeg.RTQueueTapes
import PalPeg.Manacher
import PalPeg.ManacherHeads
import PalPeg.MiddleJob
import PalPeg.Stages
import PalPeg.Assembly
import PalPeg.StageMatcher
import PalPeg.OnlineMachine
import PalPeg.Schedule
import PalPeg.TapeLib
import PalPeg.Speedup
import PalPeg.ProgramMachine
import PalPeg.Main

/-!
# 公理 guard

主定理の `#print axioms` を `#guard_msgs` で固定する。Lean / Mathlib の標準公理
`propext`, `Classical.choice`, `Quot.sound` 以外（`sorryAx` を含む）が現れれば
このファイルのビルドが失敗する。
-/

/-- info: 'PalPeg.PAL_reverse_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.PAL_reverse_mem

/-- info: 'PalPeg.PAL_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.PAL_reverse

/-- info: 'PalPeg.pal_in_peg_of_realTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_in_peg_of_realTime

/-- info: 'PalPeg.pal_recognizedByTotalPEG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_recognizedByTotalPEG

/-- info: 'PalPeg.evenLength_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.evenLength_isRegular

/-- info: 'PalPeg.oddLength_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.oddLength_isRegular

/-- info: 'PalPeg.evenPal_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.evenPal_of_pal

/-- info: 'PalPeg.oddPal_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.oddPal_of_pal

/-- info: 'PalPeg.mem_PAL_inf_EvenLength_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.mem_PAL_inf_EvenLength_iff

/-- info: 'PalPeg.evenPal_ww_reverse_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.evenPal_ww_reverse_of_pal

/-- info: 'PalPeg.fineWilf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.fineWilf

/-- info: 'PalPeg.hasPeriod_minimal_of_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.hasPeriod_minimal_of_suffix

/-- info: 'PalPeg.isPal_drop_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.isPal_drop_iff

/-- info: 'PalPeg.mem_chain_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.mem_chain_iff

/-- info: 'PalPeg.mem_PAL_iff_length_mem_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.mem_PAL_iff_length_mem_chain

/-- info: 'PalPeg.suffixPal_replica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.suffixPal_replica

/-- info: 'PalPeg.pal_prefix_length_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_prefix_length_ge

/-- info: 'PalPeg.lsp_shift_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.lsp_shift_bound

/-- info: 'PalPeg.expandAll_groupChainRev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.expandAll_groupChainRev

/-- info: 'PalPeg.group_members_same_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.group_members_same_symbol

/-- info: 'PalPeg.predictability_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.predictability_step

/-- info: 'PalPeg.work_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.work_le

/-- info: 'PalPeg.border_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.border_snapshot

/-- info: 'PalPeg.RTQueue.toList_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.RTQueue.toList_snoc

/-- info: 'PalPeg.RTQueue.toList_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.RTQueue.toList_tail

/-- info: 'PalPeg.RTQueue.inv_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.RTQueue.inv_tail

/-- info: 'PalPeg.Manacher.manacher_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Manacher.manacher_spec

/-- info: 'PalPeg.Manacher.prefixPalFlagsFromRad_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Manacher.prefixPalFlagsFromRad_eq

/-- info: 'PalPeg.Manacher.work_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Manacher.work_le

/-- info: 'PalPeg.expandAll_groupChainRevN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.expandAll_groupChainRevN

/-- info: 'PalPeg.canonical_groupChainRevN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.canonical_groupChainRevN

/-- info: 'PalPeg.boundary_shrink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.boundary_shrink

/-- info: 'PalPeg.pal_prefix_iff_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_prefix_iff_stage

/-- info: 'PalPeg.stageOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.stageOf_spec

/-- info: 'PalPeg.live_stages' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.live_stages

/-- info: 'PalPeg.Schedule.finishTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Schedule.finishTime_le

/-- info: 'PalPeg.Schedule.fifo_meets_deadlines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Schedule.fifo_meets_deadlines

/-- info: 'PalPeg.Manacher.headMove_total_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Manacher.headMove_total_run

/-- info: 'PalPeg.Tape.push_spec' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Tape.push_spec

/-- info: 'PalPeg.safe_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.safe_shift

/-- info: 'PalPeg.scan_sound_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.scan_sound_complete

/-- info: 'PalPeg.scanSteps_le_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.scanSteps_le_bound

/-- info: 'PalPeg.MiddleJob.middle_flag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.MiddleJob.middle_flag_spec

/-- info: 'PalPeg.MiddleJob.padFlag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.MiddleJob.padFlag_spec

/-- info: 'PalPeg.groupCount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.groupCount_le

/-- info: 'PalPeg.kRepetition_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.kRepetition_periods

/-- info: 'PalPeg.GSCore.ksimple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.GSCore.ksimple

/-- info: 'PalPeg.Speedup.multiStep_recognizedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Speedup.multiStep_recognizedBy

/-- info: 'PalPeg.online_answer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.online_answer_correct

/-- info: 'PalPeg.dyadicAnswer_length_iff_mem_PAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.dyadicAnswer_length_iff_mem_PAL

/-- info: 'PalPeg.vAnswer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.vAnswer_correct

/-- info: 'PalPeg.dyadic_gs_mem_PAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.dyadic_gs_mem_PAL

/-- info: 'PalPeg.Program.StructuredMachine.structured_recognizedBy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.Program.StructuredMachine.structured_recognizedBy

/-- info: 'PalPeg.GSTapes.encodes_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.GSTapes.encodes_step

/-- info: 'PalPeg.palPrefixFlagsGS_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.palPrefixFlagsGS_spec

/-- info: 'PalPeg.RTQueueTapes.queue_on_tapes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.RTQueueTapes.queue_on_tapes

/-- info: 'PalPeg.decompose_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.decompose_spec

/-- info: 'PalPeg.output_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.output_correct

/-- info: 'PalPeg.GSTapes.encodes_step'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.GSTapes.encodes_step'

/-- info: 'PalPeg.GSVTapes.vrun_tape_cost_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.GSVTapes.vrun_tape_cost_init

/-- info: 'PalPeg.TextFeed.feed_online' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.TextFeed.feed_online

/-- info: 'PalPeg.output_correctH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.output_correctH

/-- info: 'PalPeg.round_cost_leH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.round_cost_leH

/-- info: 'PalPeg.pal_in_peg_of_structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_in_peg_of_structured

/-- info: 'PalPeg.gsDecomp_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.gsDecomp_exists

/-- info: 'PalPeg.stageOK_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.stageOK_exists

/-- info: 'PalPeg.BorderTapes.flags_on_tape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.BorderTapes.flags_on_tape
