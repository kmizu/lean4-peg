import Complexity.TM
import Complexity.Prog
import Complexity.Qbf
import Complexity.QbfCodec
import Complexity.Formula
import Complexity.Circuit
import Complexity.Count
import Complexity.CfgEnc
import Complexity.WfSem
import Complexity.StepSem
import Complexity.Vars
import Complexity.Savitch
import Complexity.TopFormula
import Complexity.Hardness
import Complexity.ListTime
import Complexity.NStack
import Complexity.NStackSpec
import Complexity.NStackIO
import Complexity.NSpace
import Complexity.NKit
import Complexity.NMacros
import Complexity.NArith
import Complexity.NTable
import Complexity.Univ.Code
import Complexity.Univ.CodeSize
import Complexity.Univ.Growth
import Complexity.Univ.Load
import Complexity.Univ.Output
import Complexity.Univ.Sim
import Complexity.Univ.SimBound
import Complexity.Univ.SimHorner
import Complexity.Univ.SimKit
import Complexity.Univ.SimLook
import Complexity.Univ.SimRead
import Complexity.Univ.SimRows
import Complexity.Univ.SimRun
import Complexity.Univ.SimSpec
import Complexity.Univ.SimStep
import Complexity.Univ.SimTrav
import Complexity.Univ.SimWrite
import Complexity.Univ.Table
import Complexity.Comp.Basic
import Complexity.Comp.HaltSim
import Complexity.Comp.NDecide
import Complexity.Comp.Reduce
import Complexity.OneTape.Code
import Complexity.OneTape.Machine
import Complexity.OneTape.Macro
import Complexity.OneTape.Main
import Complexity.OneTape.Sweep
import Complexity.OneTape.Track
import Complexity.Undec.Defs
import Complexity.Undec.K1
import Complexity.Undec.K1Defs
import Complexity.Undec.MPCP
import Complexity.Undec.SRMPCP
import Complexity.Undec.TMSR
import Complexity.Undec.TMSRDefs
import Complexity.Undec.TMSRSim
import Complexity.Undec.TMSRStep

/-!
# TQBF is PSPACE-complete

The root of the complexity development: Turing machines and PSPACE (`TM`), structured programs and list programs
compiled to machines, QBFs and their encoding, the Savitch-style formula of a space-bounded computation
(`reduction_correct`), the decider (`tqbf_in_pspace`) and the polynomial-time reduction (`tqbf_hard`), giving
`tqbf_pspace_complete : PSPACEComplete TQBF`.
-/
