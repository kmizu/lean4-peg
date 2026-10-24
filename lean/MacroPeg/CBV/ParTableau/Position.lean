import MacroPeg.CBV.ParTableau.Atoms

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (clockValue predClock predClock_spec RulesAt subst_paramsFrom_slice)
open Complexity (TM Cfg Move)

theorem swappedRefs_subst (digits : Nat) (N : MExp) (first second : List MExp)
    (hf : first.length = digits) (hs : second.length = digits) :
    MExp.substArgs (N :: (first ++ second)) (swappedRefs digits) = N :: (second ++ first) := by
  have hf' := subst_paramsFrom_slice [N] first second
  have hs' := subst_paramsFrom_slice (N :: first) second []
  simp only [List.length_cons, List.length_nil, List.singleton_append, hf] at hf'
  simp only [List.length_cons, List.append_nil, List.cons_append, hf, hs] at hs'
  simp only [swappedRefs, timeRefs, posRefs, MExp.substArgs, MExp.subst, argAt,
    CBVtoCBN.substArgs_append]
  rw [hf', show 1 + digits = digits + 1 by omega, hs']

theorem posRefs_subst (digits : Nat) (N : MExp) (time position : List MExp)
    (ht : time.length = digits) (hp : position.length = digits) :
    MExp.substArgs (N :: (time ++ position)) (posRefs digits) = position := by
  have hh := subst_paramsFrom_slice (N :: time) position []
  simp only [List.length_cons, List.append_nil, List.cons_append, ht, hp] at hh
  simpa only [posRefs, Nat.add_comm 1 digits] using hh

theorem inc_entry_rule {k : Nat} (M : TM k) (d : Nat) (i : Fin k) :
    ruleAtM (compile M d).rules (address M d (.incHead i)) =
      some ⟨width d, successorBody 0 (address M d (.incHead i) + 1) 1 d d⟩ := by
  have hh := compile_at M d (.incHead i) (incHead_mem M i) 0 (by unfold slotSize; omega)
  simpa only [Nat.add_zero, rawRules, List.getElem?_cons_zero, Option.getD_some] using hh

theorem inc_adapter_rule {k : Nat} (M : TM k) (d : Nat) (i : Fin k) :
    ruleAtM (compile M d).rules (address M d (.incHead i) + 1) =
      some ⟨width d, headAdapter M d i⟩ := by
  have hh := compile_at M d (.incHead i) (incHead_mem M i) 1 (by unfold slotSize; omega)
  simpa only [rawRules, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] using hh

theorem dec_clock_at {k : Nat} (M : TM k) (d : Nat) (i : Fin k) :
    RulesAt (compile M d) (address M d (.decHead i))
      (clockBlock (address M d (.decHead i)) 0 (address M d (.decHead i) + zeroSlot d) 1 d d) := by
  intro j hj
  have hh := compile_raw_at M d (.decHead i) (decHead_mem M i) j (by
    simp only [rawRules, List.length_append]; omega)
  rw [rawRules, List.getElem?_append_left hj] at hh
  simpa only [ruleAtM_eq_getElem?] using hh

theorem dec_adapter_rule {k : Nat} (M : TM k) (d : Nat) (i : Fin k) :
    ruleAtM (compile M d).rules (address M d (.decHead i) + zeroSlot d) =
      some ⟨width d, headAdapter M d i⟩ := by
  have hh := compile_at M d (.decHead i) (decHead_mem M i) (zeroSlot d) (by unfold zeroSlot slotSize; omega)
  rw [rawRules] at hh
  have hl : zeroSlot d = (clockBlock (address M d (.decHead i)) 0
      (address M d (.decHead i) + zeroSlot d) 1 d d).length := by simp only [zeroSlot, clockBlock_length]
  rw [List.getElem?_append_right (by omega), ← hl, Nat.sub_self] at hh
  exact hh

theorem head_adapter_iff {k : Nat} (M : TM k) (d entry : Nat) (i : Fin k)
    (hr : ruleAtM (compile M d).rules entry = some ⟨width d, headAdapter M d i⟩)
    (x : List Char) (time position : List Nat) (ht : time.length = d) (hp : position.length = d)
    (r : Option (List Char)) :
    SObs (compile M d) .callByValuePar (.call entry (prefixValues x (x.length :: (position ++ time)))) x r ↔
      SObs (compile M d) .callByValuePar
        (.call (address M d (.head i)) (prefixValues x (x.length :: (time ++ position)))) x r := by
  rw [par_call_iff hr (by simp only [prefixValues_length, List.length_cons, List.length_append, ht, hp, width]; omega)
    (prefixValues_args _ x (x.length :: (position ++ time)))]
  simp only [headAdapter, MExp.subst, prefixValues, prefixValues_append]
  rw [swappedRefs_subst d _ _ _ (by simp [hp]) (by simp [ht])]

theorem overflow_fail {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time : List Nat)
    (ht : time.length = d) :
    SObs (compile M d) .callByValuePar (.call 1 (prefixValues x time)) x none := by
  apply par_call (overflow_rule M d) (by simp [ht]) (prefixValues_args _ x time)
  exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩

theorem incHead_test {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time position : List Nat)
    (ht : time.length = d) (hp : position.length = d) (hv : ∀ a ∈ position, a ≤ x.length)
    (i : Fin k) (c : Cfg k) (hb : c.pos i < (x.length + 1) ^ d)
    (hh : ∀ ds, ds.length = d → (∀ a ∈ ds, a ≤ x.length) →
      Test (compile M d) .callByValuePar
        (.call (address M d (.head i)) (prefixValues x (x.length :: (time ++ ds)))) x
          (c.pos i == clockValue x.length ds)) :
    Test (compile M d) .callByValuePar
      (.call (address M d (.incHead i)) (prefixValues x (x.length :: (position ++ time)))) x
        (c.pos i == clockValue x.length position + 1) := by
  have hr : ruleAtM (compile M d).rules (address M d (.incHead i)) =
      some ⟨1 + d + time.length, successorBody 0 (address M d (.incHead i) + 1) 1 d time.length⟩ := by
    simpa only [ht, width, Nat.two_mul, Nat.add_assoc] using inc_entry_rule M d i
  apply (successor_iff time hr (equal_rule M d) x position hp hv _).mpr
  have hn := succClock_spec x.length position hv
  cases hs : succClock x.length position with
  | none =>
    simp only [hs, hp] at hn ⊢
    have hfalse : (c.pos i == clockValue x.length position + 1) = false := by
      apply Bool.eq_false_iff.mpr
      intro he
      have := eq_of_beq he
      omega
    simp only [hfalse, Bool.false_eq_true, if_false]
    exact overflow_fail M d x time ht
  | some out =>
    simp only [hs] at hn ⊢
    apply (head_adapter_iff M d _ i (inc_adapter_rule M d i) x time out ht (hn.1.trans hp) _).mpr
    simpa only [Test, hn.2.2] using hh out (hn.1.trans hp) hn.2.1

theorem decHead_test {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time position : List Nat)
    (ht : time.length = d) (hp : position.length = d) (hv : ∀ a ∈ position, a ≤ x.length)
    (i : Fin k) (c : Cfg k)
    (hh : ∀ ds, ds.length = d → (∀ a ∈ ds, a ≤ x.length) →
      Test (compile M d) .callByValuePar
        (.call (address M d (.head i)) (prefixValues x (x.length :: (time ++ ds)))) x
          (c.pos i == clockValue x.length ds)) :
    Test (compile M d) .callByValuePar
      (.call (address M d (.decHead i)) (prefixValues x (x.length :: (position ++ time)))) x
        (c.pos i + 1 == clockValue x.length position) := by
  have hc : RulesAt (compile M d) (address M d (.decHead i))
      (clockBlock (address M d (.decHead i)) 0 (address M d (.decHead i) + zeroSlot d) 1 d time.length) := by
    simpa only [ht] using dec_clock_at M d i
  apply (ParSimulation.RulesAt.clock_iff time hc (equal_rule M d) x position hp hv _).mpr
  have hn := predClock_spec x.length position hv
  cases hs : predClock x.length position with
  | none =>
    simp only [hs] at hn ⊢
    simp only [hn, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, beq_iff_eq, if_false]
    exact overflow_fail M d x time ht
  | some out =>
    simp only [hs] at hn ⊢
    apply (head_adapter_iff M d _ i (dec_adapter_rule M d i) x time out ht (hn.1.trans hp) _).mpr
    have hb : (c.pos i == clockValue x.length out) = (c.pos i + 1 == clockValue x.length position) := by
      rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, hn.2.2]; omega
    rw [← hb]
    exact hh out (hn.1.trans hp) hn.2.1

theorem movedHead_test {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time position : List Nat)
    (ht : time.length = d) (hp : position.length = d) (hv : ∀ a ∈ position, a ≤ x.length)
    (i : Fin k) (c : Cfg k) (hb : c.pos i < (x.length + 1) ^ d)
    (hh : ∀ ds, ds.length = d → (∀ a ∈ ds, a ≤ x.length) →
      Test (compile M d) .callByValuePar
        (.call (address M d (.head i)) (prefixValues x (x.length :: (time ++ ds)))) x
          (c.pos i == clockValue x.length ds)) (mv : Move) :
    Test (compile M d) .callByValuePar
      (MExp.subst (prefixValues x (x.length :: (time ++ position))) (movedHead M d i mv)) x
        (mv.apply (c.pos i) == clockValue x.length position) := by
  let args := prefixValues x (x.length :: (time ++ position))
  change Test (compile M d) .callByValuePar (MExp.subst args (movedHead M d i mv)) x _
  have hl : args.length = width d := by simp only [args, prefixValues_length, List.length_cons,
    List.length_append, ht, hp, width]; omega
  have hswap : MExp.substArgs args (swappedRefs d) = prefixValues x (x.length :: (position ++ time)) := by
    simpa only [args, prefixValues, prefixValues_append] using
      swappedRefs_subst d (.lit (x.take x.length)) (prefixValues x time) (prefixValues x position)
        (by simp [ht]) (by simp [hp])
  have hpos : MExp.substArgs args (posRefs d) = prefixValues x position := by
    simpa only [args, prefixValues, prefixValues_append] using
      posRefs_subst d (.lit (x.take x.length)) (prefixValues x time) (prefixValues x position)
        (by simp [ht]) (by simp [hp])
  cases mv with
  | S =>
    simp only [movedHead, MExp.subst, subst_allRefs _ _ hl]
    exact hh position hp hv
  | R =>
    simp only [movedHead, MExp.subst, hswap]
    exact decHead_test M d x time position ht hp hv i c hh
  | L =>
    have hi := incHead_test M d x time position ht hp hv i c hb hh
    have hz := zeroDigits_test (equal_rule M d) x position hv
    have ha := test_alt hi (test_seq hz (hh position hp hv))
    have he : ((c.pos i == clockValue x.length position + 1) ||
        ((clockValue x.length position == 0) && (c.pos i == clockValue x.length position))) =
          ((c.pos i - 1) == clockValue x.length position) := by
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      omega
    rw [he] at ha
    simpa only [movedHead, MExp.subst, hswap, zeroDigits_subst, hpos, subst_allRefs _ _ hl,
      Move.apply] using ha

end Shallot.MacroPeg.CBV.ParTableau
