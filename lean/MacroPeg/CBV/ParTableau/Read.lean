import MacroPeg.CBV.ParTableau.Routing
import MacroPeg.CBV.PrefixNumerals

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (clockValue subst_paramsFrom_slice subst_param_at)
open Complexity (TM Cfg)

theorem readEntry_subst (entry leaf digits : Nat) (N : MExp) (time position : List MExp)
    (ht : time.length = digits) :
    MExp.subst (N :: (time ++ position))
      (tupleSearch entry leaf digits (.param 0 :: timeRefs digits)) =
        tupleSearch entry leaf digits (N :: time) := by
  rw [tupleSearch_subst]
  have hh := subst_paramsFrom_slice [N] time position
  simp only [List.length_cons, List.length_nil, List.singleton_append] at hh
  simp only [MExp.substArgs, MExp.subst, argAt, timeRefs]
  rw [← ht, hh]

theorem readLeaf_subst {k : Nat} (M : TM k) (digits : Nat) (i : Fin k) (s : Nat)
    (N : MExp) (time position : List MExp) (ht : time.length = digits) (hp : position.length = digits) :
    MExp.subst (position ++ N :: time) (readLeaf M digits i s) =
      .seq (.call (address M digits (.head i)) (N :: (time ++ position)))
        (.call (address M digits (.cell i s)) (N :: (time ++ position))) := by
  have hn := subst_param_at position N time
  have htime := subst_paramsFrom_slice (position ++ [N]) time []
  have hpos := subst_paramsFrom_slice [] position (N :: time)
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.append_assoc, List.singleton_append, List.append_nil, List.nil_append] at htime hpos
  simp only [hp] at hn htime hpos
  simp only [ht] at htime
  simp only [readLeaf, MExp.subst]
  have hargs : MExp.substArgs (position ++ N :: time)
      (.param digits :: (CBVtoCBN.paramsFrom (digits + 1) digits ++ CBVtoCBN.paramsFrom 0 digits)) =
        N :: (time ++ position) := by
    simp only [MExp.substArgs, CBVtoCBN.substArgs_append, hn, htime, hpos]
  rw [hargs]

/-- Correct head and cell tests at one time suffice to decide the read
symbol. The bounded position search is proved complete, not assumed. -/
theorem compiled_read_test {k : Nat} (M : TM k) (digits : Nat) (x : List Char)
    (time position : List Nat) (ht : time.length = digits) (hp : position.length = digits)
    (c : Cfg k) (i : Fin k) (s : Nat) (hs : s < M.na)
    (hbound : c.pos i < (x.length + 1) ^ digits)
    (hhead : ∀ ds, ds.length = digits → (∀ a ∈ ds, a ≤ x.length) →
      Test (compile M digits) .callByValuePar
        (.call (address M digits (.head i)) (prefixValues x (x.length :: (time ++ ds)))) x
          (c.pos i == clockValue x.length ds))
    (hcell : ∀ ds, ds.length = digits → (∀ a ∈ ds, a ≤ x.length) →
      Test (compile M digits) .callByValuePar
        (.call (address M digits (.cell i s)) (prefixValues x (x.length :: (time ++ ds)))) x
          (c.cells i (clockValue x.length ds) == s)) :
    Test (compile M digits) .callByValuePar
      (.call (address M digits (.read i s)) (prefixValues x (x.length :: (time ++ position)))) x
        (c.read i == s) := by
  let base := address M digits (.read i s)
  let P := fun ds => (c.pos i == clockValue x.length ds) && (c.cells i (clockValue x.length ds) == s)
  have hleaf : ∀ ds, ds.length = digits → (∀ a ∈ ds, a ≤ x.length) →
      Test (compile M digits) .callByValuePar
        (.call (base + zeroSlot digits) (prefixValues x (ds ++ x.length :: time))) x (P ds) := by
    intro ds hd hv
    apply (par_call_iff (read_leaf_rule M digits i s hs) (by
      simp only [prefixValues_length, List.length_append, List.length_cons, ht, hd, width]; omega)
        (prefixValues_args _ x (ds ++ x.length :: time)) _).mpr
    simp only [prefixValues_append, prefixValues]
    rw [readLeaf_subst M digits i s _ _ _ (by simp [ht]) (by simp [hd])]
    simpa only [Test, P, prefixValues, prefixValues_append] using test_seq (hhead ds hd hv) (hcell ds hd hv)
  have hr := tuple_rules_of_at (read_search_at M digits i s hs)
  have hr' : TupleRules (compile M digits) (base + 1) (base + zeroSlot digits) digits
      (x.length :: time).length := by simpa only [List.length_cons, ht, base, Nat.add_comm 1 digits] using hr
  have hsearch := tupleSearch_test (base + 1) (base + zeroSlot digits) digits (x.length :: time) hr' x P
    (by intro ds hd hv; exact hleaf ds hd hv)
  have hvalue : tupleAny x.length digits P = (c.read i == s) := by
    rw [Bool.eq_iff_iff, tupleAny_true_iff]
    constructor
    · rintro ⟨ds, _, _, hh⟩
      obtain ⟨hpos, hsym⟩ := Bool.and_eq_true_iff.mp hh
      have he := eq_of_beq hpos
      simpa only [Cfg.read, ← he] using hsym
    · intro hsym
      let ds := digitsOf x.length digits (c.pos i)
      have he : clockValue x.length ds = c.pos i := digitsOf_value _ _ _ hbound
      exact ⟨ds, digitsOf_length _ _ _, digitsOf_valid _ _ _, by simpa only [P, he, beq_self_eq_true,
        Bool.true_and, Cfg.read] using hsym⟩
  rw [hvalue] at hsearch
  apply (par_call_iff (read_entry_rule M digits i s hs) (by
    simp only [prefixValues_length, List.length_append, List.length_cons, ht, hp, width]; omega)
      (prefixValues_args _ x (x.length :: (time ++ position))) _).mpr
  simp only [prefixValues, prefixValues_append]
  rw [readEntry_subst _ _ _ _ _ _ (by simp [ht])]
  exact hsearch

end Shallot.MacroPeg.CBV.ParTableau
