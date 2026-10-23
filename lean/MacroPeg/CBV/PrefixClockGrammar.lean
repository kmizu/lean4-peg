import MacroPeg.CBV.PrefixClock

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation
open CBVtoCBN (paramsFrom paramsFrom_firstOrder subst_paramsFrom_slice subst_paramsFrom_cons
  subst_paramsFrom firstOrderArgs_append substArgs_append ruleAtM_append_offset predClock)

theorem clockBorrow_subst (args : List MExp) (base equal onZero i : Nat) (N : MExp)
    (ds ctx : List MExp) :
    MExp.subst args (clockBorrow base equal onZero i N ds ctx) =
      clockBorrow base equal onZero i (MExp.subst args N)
        (MExp.substArgs args ds) (MExp.substArgs args ctx) := by
  induction ds generalizing i with
  | nil => rfl
  | cons k ds ih =>
    simp only [clockBorrow, branch, MExp.subst, MExp.substArgs, substArgs_append, ih]

theorem clockBorrow_firstOrder (base equal onZero i : Nat) (N : MExp) (hN : N.FirstOrder)
    (ds ctx : List MExp) (hd : MExp.FirstOrderArgs ds) (hc : MExp.FirstOrderArgs ctx) :
    (clockBorrow base equal onZero i N ds ctx).FirstOrder := by
  induction ds generalizing i with
  | nil => exact hc
  | cons k ds ih =>
    exact ⟨⟨⟨hd.1, trivial, trivial⟩, ih (i + 1) hd.2⟩,
      ⟨⟨hd.1, trivial, trivial⟩, hd.1, trivial, hN, firstOrderArgs_append hd.2 hc⟩⟩

def clockStepBody (base equal onZero digits ctxSize : Nat) : MExp :=
  clockBorrow base equal onZero 0 (.param 0) (paramsFrom 1 digits) (paramsFrom (1 + digits) ctxSize)

theorem clockStepBody_firstOrder (base equal onZero digits ctxSize : Nat) :
    (clockStepBody base equal onZero digits ctxSize).FirstOrder :=
  clockBorrow_firstOrder base equal onZero 0 (.param 0) trivial _ _
    (paramsFrom_firstOrder 1 digits) (paramsFrom_firstOrder (1 + digits) ctxSize)

theorem clockStepBody_subst (base equal onZero : Nat) (N : MExp) (ds ctx : List MExp) :
    MExp.subst (N :: (ds ++ ctx)) (clockStepBody base equal onZero ds.length ctx.length) =
      clockBorrow base equal onZero 0 N ds ctx := by
  rw [clockStepBody, clockBorrow_subst]
  have hD := subst_paramsFrom_slice [N] ds ctx
  have hC := subst_paramsFrom_slice (N :: ds) ctx []
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.singleton_append] at hD
  simp only [List.length_cons, List.append_nil, List.cons_append] at hC
  rw [show 1 + ds.length = ds.length + 1 by omega, hD, hC]
  rfl

theorem clockStep_iff {g : MGrammar} {entry base equal next onZero digits : Nat}
    (ctx : List Nat)
    (hEntry : ruleAtM g.rules entry = some ⟨1 + digits + ctx.length, clockStepBody base equal onZero digits ctx.length⟩)
    (hRules : ClockRules g base equal next digits ctx.length)
    (hEqual : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (r : Option (List Char)) :
    SObs g .callByValuePar (.call entry (prefixValues x (x.length :: (ds ++ ctx)))) x r ↔
      match predClock x.length ds with
      | none => SObs g .callByValuePar (.call onZero (prefixValues x ctx)) x r
      | some out => SObs g .callByValuePar (.call next (prefixValues x (x.length :: (out ++ ctx)))) x r := by
  rw [par_call_iff hEntry (by simp [hd]; omega) (prefixValues_args g x (x.length :: (ds ++ ctx)))]
  simp only [prefixValues, prefixValues_append]
  rw [show digits = (prefixValues x ds).length by simp [hd],
    show ctx.length = (prefixValues x ctx).length by simp,
    clockStepBody_subst]
  have h := clockBorrow_iff (onZero := onZero) ctx hRules hEqual x ds hv 0 (by omega) r
  cases hpred : predClock x.length ds with
  | none => simpa only [hpred] using h
  | some out =>
    simpa only [hpred, List.replicate_zero, List.nil_append, prefixValues, prefixValues_append] using h

theorem clockPackBody_firstOrder (next lower restSize : Nat) :
    (clockPackBody next lower restSize).FirstOrder := by
  have hr : MExp.FirstOrderArgs (List.replicate lower (.param 1)) := by
    induction lower with
    | zero => trivial
    | succ lower ih => exact ⟨trivial, ih⟩
  exact ⟨trivial, firstOrderArgs_append hr ⟨trivial, paramsFrom_firstOrder 2 restSize⟩⟩

def clockAuxFrom (base equal next digits ctxSize : Nat) : Nat → Nat → List MRule
  | _, 0 => []
  | i, count + 1 => clockHelperRule base equal digits ctxSize i :: clockPackRule next digits ctxSize i ::
      clockAuxFrom base equal next digits ctxSize (i + 1) count

theorem clockAuxFrom_length (base equal next digits ctxSize start count : Nat) :
    (clockAuxFrom base equal next digits ctxSize start count).length = 2 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [clockAuxFrom, List.length_cons, ih]; omega

theorem clockAuxFrom_at (base equal next digits ctxSize start count j : Nat) (hj : j < count)
    (tail : List MRule) :
    ruleAtM (clockAuxFrom base equal next digits ctxSize start count ++ tail) (2 * j) =
      some (clockHelperRule base equal digits ctxSize (start + j)) ∧
    ruleAtM (clockAuxFrom base equal next digits ctxSize start count ++ tail) (2 * j + 1) =
      some (clockPackRule next digits ctxSize (start + j)) := by
  induction count generalizing start j with
  | zero => omega
  | succ count ih =>
    cases j with
    | zero => simp [clockAuxFrom, ruleAtM]
    | succ j =>
      have h := ih (start + 1) j (by omega)
      have h0 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      simp only [clockAuxFrom, List.cons_append, h0, ruleAtM]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def clockBlock (entry equal next onZero digits ctxSize : Nat) : List MRule :=
  ⟨1 + digits + ctxSize, clockStepBody (entry + 1) equal onZero digits ctxSize⟩ ::
    clockAuxFrom (entry + 1) equal next digits ctxSize 0 digits

theorem clockBlock_length (entry equal next onZero digits ctxSize : Nat) :
    (clockBlock entry equal next onZero digits ctxSize).length = 1 + 2 * digits := by
  simp only [clockBlock, List.length_cons, clockAuxFrom_length]
  omega

theorem clockBlock_firstOrder (entry equal next onZero digits ctxSize : Nat) :
    ∀ rule ∈ clockBlock entry equal next onZero digits ctxSize, rule.body.FirstOrder := by
  have hAux : ∀ start count rule,
      rule ∈ clockAuxFrom (entry + 1) equal next digits ctxSize start count → rule.body.FirstOrder := by
    intro start count
    induction count generalizing start with
    | zero => intro rule h; cases h
    | succ count ih =>
      intro rule h
      rcases List.mem_cons.mp h with rfl | h
      · exact predecessorBody_firstOrder _ _ _ _
      rcases List.mem_cons.mp h with rfl | h
      · exact clockPackBody_firstOrder _ _ _
      · exact ih (start + 1) rule h
  intro rule h
  rcases List.mem_cons.mp h with rfl | h
  · exact clockStepBody_firstOrder _ _ _ _ _
  · exact hAux 0 digits rule h

theorem clockBlock_rules (pre tail : List MRule) (equal next onZero digits ctxSize : Nat) :
    ClockRules ⟨pre ++ (clockBlock pre.length equal next onZero digits ctxSize ++ tail)⟩
      (pre.length + 1) equal next digits ctxSize := by
  intro i hi
  have h := clockAuxFrom_at (pre.length + 1) equal next digits ctxSize 0 digits i hi tail
  simp only [Nat.zero_add] at h
  constructor
  · rw [show pre.length + 1 + 2 * i = pre.length + (2 * i + 1) by omega,
      ruleAtM_append_offset]
    simpa only [clockBlock, List.cons_append, ruleAtM] using h.1
  · rw [show pre.length + 1 + 2 * i + 1 = pre.length + ((2 * i + 1) + 1) by omega,
      ruleAtM_append_offset]
    simpa only [clockBlock, List.cons_append, ruleAtM] using h.2

/-- The physically generated finite clock block preserves both successful
and failing continuation observations on the original character input. -/
theorem clockBlock_iff (pre tail : List MRule) (equal next onZero digits : Nat) (ctx : List Nat)
    (hEqual : ruleAtM (pre ++ (clockBlock pre.length equal next onZero digits ctx.length ++ tail)) equal =
      some ⟨2, equalBody equal⟩)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (r : Option (List Char)) :
    SObs ⟨pre ++ (clockBlock pre.length equal next onZero digits ctx.length ++ tail)⟩ .callByValuePar
      (.call pre.length (prefixValues x (x.length :: (ds ++ ctx)))) x r ↔
    match predClock x.length ds with
    | none => SObs ⟨pre ++ (clockBlock pre.length equal next onZero digits ctx.length ++ tail)⟩ .callByValuePar
        (.call onZero (prefixValues x ctx)) x r
    | some out => SObs ⟨pre ++ (clockBlock pre.length equal next onZero digits ctx.length ++ tail)⟩ .callByValuePar
        (.call next (prefixValues x (x.length :: (out ++ ctx)))) x r := by
  apply clockStep_iff ctx _ (clockBlock_rules pre tail equal next onZero digits ctx.length) hEqual x ds hd hv r
  rw [show pre.length = pre.length + 0 by omega, ruleAtM_append_offset]
  rfl

end Shallot.MacroPeg.CBV.PrefixCounters
