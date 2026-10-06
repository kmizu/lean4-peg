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

/-!
# TQBF is PSPACE-complete

The root of the complexity development: Turing machines and PSPACE (`TM`), structured programs and list programs
compiled to machines, QBFs and their encoding, the Savitch-style formula of a space-bounded computation
(`reduction_correct`), the decider (`tqbf_in_pspace`) and the polynomial-time reduction (`tqbf_hard`), giving
`tqbf_pspace_complete : PSPACEComplete TQBF`.
-/
