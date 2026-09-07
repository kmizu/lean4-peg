import Mathlib.Data.List.Basic

example (m n : ℕ) : List.range (m+n) = List.range m ++ (List.range n).map (m + ·) :=
  List.range_add m n
