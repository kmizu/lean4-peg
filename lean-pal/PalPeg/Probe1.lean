import PalPeg.LocalState
open PalPeg.GalilScaffoldChainInputSupply
attribute [ext] GalilVM
#check @GalilVM.ext
example (s : GalilVM) (r : PalPeg.GalilScaffoldCounter.Counter) :
    ({s with radius := r} : GalilVM) = {s with radius := r} := by ext <;> rfl
