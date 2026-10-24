import Complexity.NMacros

/-! A fixed finite lookup table compiled into control flow. Only the top of the
selected register is replaced; every other number and register is preserved. -/
namespace Complexity.NTableLookup
variable {K : Nat}

def program (i : Fin K) (table : List Nat) : NProg K :=
  caseTop i (table.map (npushC i)) (.halt false)

theorem runs (i : Fin K) (table : List Nat) (v : Nat) (hv : v < table.length)
    (S : Lists K) (l : List Nat) (hi : S i = l ++ [v]) :
    NRuns (program i table) S (S.set i (l ++ [table[v]])) (2 * v + table[v] + 3) := by
  have hr := caseTop_runs i (table.map (npushC i)) (.halt false) v (by simpa using hv)
    S l hi (S.set i (l ++ [table[v]])) (table[v]+1) (by
      simpa [Lists.set_set_u] using nruns_pushC i (S.set i l) table[v])
  exact hr.mono (by omega)
end Complexity.NTableLookup
