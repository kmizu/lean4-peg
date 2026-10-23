import MacroPeg.CBVtoCBN.ClockStep

namespace Shallot.MacroPeg.CBVtoCBN

theorem subst_borrowExpr (args : List MExp) (base onZero i : Nat) (N : MExp)
    (ps : List (MExp × MExp)) (ctx : List MExp) :
    MExp.subst args (borrowExpr base onZero i N ps ctx) =
      borrowExpr base onZero i (MExp.subst args N) (substPairs args ps) (MExp.substArgs args ctx) := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih =>
    simp only [borrowExpr, substPairs, List.map_cons, ifP, exactLengthP, andP,
      MExp.subst, MExp.substArgs, substArgs_append, subst_pairArgs, ih]

theorem borrowExpr_firstOrder (base onZero i : Nat) (N : MExp) (hN : N.FirstOrder)
    (ps : List (MExp × MExp)) (hp : ∀ p ∈ ps, p.1.FirstOrder ∧ p.2.FirstOrder)
    (ctx : List MExp) (hc : MExp.FirstOrderArgs ctx) :
    (borrowExpr base onZero i N ps ctx).FirstOrder := by
  induction ps generalizing i with
  | nil => exact hc
  | cons p ps ih =>
    have hps : ∀ q ∈ ps, q.1.FirstOrder ∧ q.2.FirstOrder := fun q hq => hp q (by simp [hq])
    have hpair : MExp.FirstOrderArgs (pairArgs ps) := by
      have aux : ∀ qs : List (MExp × MExp), (∀ q ∈ qs, q.1.FirstOrder ∧ q.2.FirstOrder) →
          MExp.FirstOrderArgs (pairArgs qs) := by
        intro qs
        induction qs with
        | nil => intro _; trivial
        | cons q qs ihq =>
          intro hq
          have hh := hq q (by simp)
          exact ⟨hh.1, hh.2, ihq (fun a ha => hq a (by simp [ha]))⟩
      exact aux ps hps
    have hh := hp p (by simp)
    exact ifP_firstOrder ⟨hh.2, trivial⟩ (ih (i + 1) hps)
      ⟨⟨hh.2, trivial⟩, trivial, hN, firstOrderArgs_append hpair hc⟩

theorem pairRefs_firstOrder (start d : Nat) :
    ∀ p ∈ pairRefs start d, p.1.FirstOrder ∧ p.2.FirstOrder := by
  induction d generalizing start with
  | zero => intro p hp; cases hp
  | succ d ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨trivial, trivial⟩
    · exact ih (start + 2) p hp

/-- Entry rule for a fixed number of clock digits and enclosing context arguments. -/
def clockStepBody (base onZero digits ctxSize : Nat) : MExp :=
  borrowExpr base onZero 0 (.param 0) (pairRefs 1 digits) (paramsFrom (1 + 2 * digits) ctxSize)

theorem clockStepBody_firstOrder (base onZero digits ctxSize : Nat) :
    (clockStepBody base onZero digits ctxSize).FirstOrder :=
  borrowExpr_firstOrder base onZero 0 (.param 0) trivial _ (pairRefs_firstOrder 1 digits)
    _ (paramsFrom_firstOrder (1 + 2 * digits) ctxSize)

theorem clockStepBody_subst (base onZero : Nat) (N : MExp)
    (ps : List (MExp × MExp)) (ctx : List MExp) :
    MExp.subst (N :: (pairArgs ps ++ ctx)) (clockStepBody base onZero ps.length ctx.length) =
      borrowExpr base onZero 0 N ps ctx := by
  rw [clockStepBody, subst_borrowExpr]
  have hp := subst_pairRefs [N] ps ctx
  simp only [List.singleton_append, List.length_cons, List.length_nil, Nat.zero_add] at hp
  rw [hp]
  have hc := subst_paramsFrom_slice (N :: pairArgs ps) ctx []
  simp only [List.append_nil, List.cons_append, List.length_cons, pairArgs_length] at hc
  rw [show 1 + 2 * ps.length = 2 * ps.length + 1 by omega, hc]
  rfl

theorem clockStep_iff {g : MGrammar} (hg : g.FirstOrder) {entry base next onZero digits : Nat}
    (ctx : List MExp)
    (he : ruleAtM g.rules entry = some ⟨1 + 2 * digits + ctx.length, clockStepBody base onZero digits ctx.length⟩)
    (hr : BorrowRules g base next digits ctx.length)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (r : Option (List Char)) :
    MacroObs g (.call entry (skipN x.length :: (clockArgs x.length ds ++ ctx))) x r ↔
      match predClock x.length ds with
      | none => MacroObs g (.call onZero ctx) x r
      | some out => MacroObs g (.call next (skipN x.length :: (clockArgs x.length out ++ ctx))) x r := by
  rw [obs_call_iff he (by simp only [List.length_cons, List.length_append, clockArgs_length]; omega)]
  have hplen : (clockPairs x.length ds).length = digits := by simp [clockPairs, hd]
  rw [← hplen]
  simp only [clockArgs]
  rw [clockStepBody_subst]
  have h := borrowExpr_iff (onZero := onZero) hg ctx hr x ds hv 0 (by omega) r
  cases ho : predClock x.length ds with
  | none => simpa only [ho] using h
  | some out => simpa only [ho, clockArgs, List.replicate_zero, List.nil_append] using h

/-- Helper and packing rule for a specified digit. -/
def clockHelperRule (base digits ctxSize i : Nat) : MRule :=
  ⟨3 + 2 * (digits - i - 1) + ctxSize,
    complementContextBody (base + 2 * i) (base + 2 * i + 1) (1 + 2 * (digits - i - 1) + ctxSize)⟩

def clockPackRule (next digits ctxSize i : Nat) : MRule :=
  ⟨3 + 2 * (digits - i - 1) + ctxSize,
    packClockBody next i (2 * (digits - i - 1) + ctxSize)⟩

/-- Two actual named rules per digit, laid out consecutively. -/
def clockAuxFrom (base next digits ctxSize : Nat) : Nat → Nat → List MRule
  | _, 0 => []
  | i, d + 1 => clockHelperRule base digits ctxSize i :: clockPackRule next digits ctxSize i ::
      clockAuxFrom base next digits ctxSize (i + 1) d

theorem clockAuxFrom_length (base next digits ctxSize start count : Nat) :
    (clockAuxFrom base next digits ctxSize start count).length = 2 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [clockAuxFrom, List.length_cons, ih]; omega

theorem clockAuxFrom_at (base next digits ctxSize start count j : Nat) (hj : j < count)
    (tail : List MRule) :
    ruleAtM (clockAuxFrom base next digits ctxSize start count ++ tail) (2 * j) =
      some (clockHelperRule base digits ctxSize (start + j)) ∧
    ruleAtM (clockAuxFrom base next digits ctxSize start count ++ tail) (2 * j + 1) =
      some (clockPackRule next digits ctxSize (start + j)) := by
  induction count generalizing start j with
  | zero => omega
  | succ count ih =>
    cases j with
    | zero => simp [clockAuxFrom, ruleAtM]
    | succ j =>
      have hi := ih (start + 1) j (by omega)
      have h0 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      simp only [clockAuxFrom, List.cons_append, h0, ruleAtM]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

/-- A finite CBN grammar fragment. Its two continuation addresses are supplied by the compiler. -/
def clockBlock (entry next onZero digits ctxSize : Nat) : List MRule :=
  ⟨1 + 2 * digits + ctxSize, clockStepBody (entry + 1) onZero digits ctxSize⟩ ::
    clockAuxFrom (entry + 1) next digits ctxSize 0 digits

theorem clockBlock_length (entry next onZero digits ctxSize : Nat) :
    (clockBlock entry next onZero digits ctxSize).length = 1 + 2 * digits := by
  simp only [clockBlock, List.length_cons, clockAuxFrom_length]
  omega

theorem clockBlock_firstOrder (entry next onZero digits ctxSize : Nat) :
    ∀ rule ∈ clockBlock entry next onZero digits ctxSize, rule.body.FirstOrder := by
  have ha : ∀ start count rule, rule ∈ clockAuxFrom (entry + 1) next digits ctxSize start count →
      rule.body.FirstOrder := by
    intro start count
    induction count generalizing start with
    | zero => intro rule hr; cases hr
    | succ count ih =>
      intro rule hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact complementContextBody_firstOrder _ _ _
      rcases List.mem_cons.mp hr with rfl | hr
      · exact packClockBody_firstOrder _ _ _
      · exact ih (start + 1) rule hr
  intro rule hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact clockStepBody_firstOrder _ _ _ _
  · exact ha 0 digits rule hr

/-- Appending the generated fragment establishes all helper-rule lookup obligations. -/
theorem clockBlock_rules (pre tail : List MRule) (next onZero digits ctxSize : Nat) :
    BorrowRules ⟨pre ++ (clockBlock pre.length next onZero digits ctxSize ++ tail)⟩
      (pre.length + 1) next digits ctxSize := by
  intro i hi
  have h := clockAuxFrom_at (pre.length + 1) next digits ctxSize 0 digits i hi tail
  constructor
  · rw [show pre.length + 1 + 2 * i = pre.length + (2 * i + 1) by omega,
      ruleAtM_append_offset]
    change ruleAtM (clockAuxFrom _ _ _ _ _ _ ++ tail) (2 * i) = _
    simpa only [Nat.zero_add, Nat.add_zero, clockHelperRule, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
  · rw [show pre.length + 1 + 2 * i + 1 = pre.length + ((2 * i + 1) + 1) by omega,
      ruleAtM_append_offset]
    change ruleAtM (clockAuxFrom _ _ _ _ _ _ ++ tail) (2 * i + 1) = _
    simpa only [Nat.zero_add, clockPackRule] using h.2

/-- The generated grammar fragment decrements the clock on the original input, preserving context.
This theorem discharges its rule-layout requirements from the actual list of generated rules. -/
theorem clockBlock_iff (pre tail : List MRule) (next onZero digits : Nat) (ctx : List MExp)
    (hg : MGrammar.FirstOrder ⟨pre ++ (clockBlock pre.length next onZero digits ctx.length ++ tail)⟩)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits) (hv : ∀ k ∈ ds, k ≤ x.length)
    (r : Option (List Char)) :
    let g : MGrammar := ⟨pre ++ (clockBlock pre.length next onZero digits ctx.length ++ tail)⟩
    MacroObs g (.call pre.length (skipN x.length :: (clockArgs x.length ds ++ ctx))) x r ↔
      match predClock x.length ds with
      | none => MacroObs g (.call onZero ctx) x r
      | some out => MacroObs g (.call next (skipN x.length :: (clockArgs x.length out ++ ctx))) x r := by
  apply clockStep_iff hg ctx _ (clockBlock_rules pre tail next onZero digits ctx.length) x ds hd hv r
  rw [show pre.length = pre.length + 0 by omega, ruleAtM_append_offset]
  rfl

/-- Initialize every digit from the frozen input-length counter. -/
def clockInitBody (next digits ctxSize : Nat) : MExp :=
  .call next (.param 0 :: (repeatPair (.param 0) .eps digits ++ paramsFrom 1 ctxSize))

theorem clockInitBody_firstOrder (next digits ctxSize : Nat) : (clockInitBody next digits ctxSize).FirstOrder :=
  ⟨trivial, firstOrderArgs_append (repeatPair_firstOrder (a := .param 0) (b := .eps) trivial trivial digits)
    (paramsFrom_firstOrder _ _)⟩

theorem clockInitBody_subst (next digits : Nat) (n : Nat) (ctx : List MExp) :
    MExp.subst (skipN n :: ctx) (clockInitBody next digits ctx.length) =
      .call next (skipN n :: (clockArgs n (List.replicate digits n) ++ ctx)) := by
  simp [clockInitBody, MExp.subst, MExp.substArgs, substArgs_append, subst_repeatPair,
    argAt, subst_paramsFrom_cons, subst_paramsFrom, clockArgs_replicate]

/-- A fixed two-rule prefix discovers the input length and initializes the complete clock. -/
def clockStartBlock (entry next digits : Nat) : List MRule :=
  [⟨1, findLengthBody entry (entry + 1)⟩, ⟨1, clockInitBody next digits 0⟩]

theorem clockStartBlock_firstOrder (entry next digits : Nat) :
    ∀ rule ∈ clockStartBlock entry next digits, rule.body.FirstOrder := by
  intro rule hr
  simp only [clockStartBlock, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact findLengthBody_firstOrder _ _
  · exact clockInitBody_firstOrder _ _ _

/-- Clock initialization is performed by the fixed target grammar, without changing its input. -/
theorem clockStartBlock_iff (pre tail : List MRule) (next digits : Nat) (x : List Char)
    (r : Option (List Char)) :
    let g : MGrammar := ⟨pre ++ (clockStartBlock pre.length next digits ++ tail)⟩
    MacroObs g (.call pre.length [.eps]) x r ↔
      MacroObs g (.call next (skipN x.length :: clockArgs x.length (List.replicate digits x.length))) x r := by
  let g : MGrammar := ⟨pre ++ (clockStartBlock pre.length next digits ++ tail)⟩
  have hf : ruleAtM g.rules pre.length = some ⟨1, findLengthBody pre.length (pre.length + 1)⟩ := by
    rw [show pre.length = pre.length + 0 by omega]
    exact (ruleAtM_append_offset pre _ 0).trans rfl
  have hi : ruleAtM g.rules (pre.length + 1) = some ⟨1, clockInitBody next digits 0⟩ := by
    rw [ruleAtM_append_offset]
    rfl
  have h := findLength_iff hf x 0 (by omega) r
  apply h.trans
  rw [obs_call_iff hi rfl]
  change MacroObs g (MExp.subst (skipN x.length :: []) (clockInitBody next digits ([] : List MExp).length)) x r ↔ _
  rw [clockInitBody_subst, List.append_nil]

/-- The same predecessor implemented by the generated CBN clock is exactly one source table round.
Arguments are evaluated at the current round; this decrement is taken only when entering the called body. -/
theorem clockTable_step {source : MGrammar} {x : List Char} {s : Strategy} {i : Nat} {rule : MRule}
    (hr : ruleAtM source.rules i = some rule) (W : List (List Char))
    (ds out : List Nat) (hv : ∀ k ∈ ds, k ≤ x.length) (hc : predClock x.length ds = some out)
    {p : Nat} (hp : p ≤ x.length) :
    valAt (tblV source x s (clockValue x.length ds) i W) p =
      evV source x s (tblV source x s (clockValue x.length out)) W rule.body p := by
  have hs := predClock_spec x.length ds hv
  rw [hc] at hs
  rw [hs.2.2]
  exact valAt_tblV_succ hr W hp

/-- An exhausted clock means an unknown table entry, including for a call whose arguments already succeeded. -/
theorem clockTable_zero (source : MGrammar) (x : List Char) (s : Strategy) (i : Nat) (W : List (List Char))
    (ds : List Nat) (hv : ∀ k ∈ ds, k ≤ x.length) (hc : predClock x.length ds = none) (p : Nat) :
    valAt (tblV source x s (clockValue x.length ds) i W) p = none := by
  have hs := predClock_spec x.length ds hv
  rw [hc] at hs
  rw [hs]
  exact valAt_nil p

end Shallot.MacroPeg.CBVtoCBN
