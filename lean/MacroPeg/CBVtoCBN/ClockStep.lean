import MacroPeg.CBVtoCBN.Routing
import MacroPeg.CBVtoCBN.ClockBound

namespace Shallot.MacroPeg.CBVtoCBN

def clockPairs (n : Nat) (ds : List Nat) : List (MExp × MExp) :=
  ds.map (fun k => (skipN k, skipN (n - k)))

def clockArgs (n : Nat) (ds : List Nat) : List MExp := pairArgs (clockPairs n ds)

theorem clockArgs_length (n : Nat) (ds : List Nat) : (clockArgs n ds).length = 2 * ds.length := by
  simp [clockArgs, pairArgs_length, clockPairs]

theorem clockArgs_append (n : Nat) (a b : List Nat) :
    clockArgs n (a ++ b) = clockArgs n a ++ clockArgs n b := by
  induction a with
  | nil => rfl
  | cons k ks ih => simpa only [clockArgs, clockPairs, List.map_cons, List.map_append,
      pairArgs, List.cons_append] using congrArg (fun es => skipN k :: skipN (n - k) :: es) ih

theorem clockArgs_replicate (n d : Nat) : clockArgs n (List.replicate d n) = repeatPair (skipN n) .eps d := by
  induction d with
  | zero => rfl
  | succ d ih => simpa only [List.replicate_succ, clockArgs, clockPairs, List.map_cons,
      pairArgs, Nat.sub_self, skipN, repeatPair] using congrArg (fun es => skipN n :: .eps :: es) ih

/-- Fixed-width predecessor in base `n+1`, with the least-significant digit first. -/
def predClock (n : Nat) : List Nat → Option (List Nat)
  | [] => none
  | k :: ds => if k = 0 then (predClock n ds).map (n :: ·) else some ((k - 1) :: ds)

theorem predClock_spec (n : Nat) (ds : List Nat) (hv : ∀ k ∈ ds, k ≤ n) :
    match predClock n ds with
    | none => clockValue n ds = 0
    | some out => out.length = ds.length ∧ (∀ k ∈ out, k ≤ n) ∧ clockValue n ds = clockValue n out + 1 := by
  induction ds with
  | nil => rfl
  | cons k ds ih =>
    have hk := hv k (by simp)
    have ht : ∀ j ∈ ds, j ≤ n := fun j hj => hv j (by simp [hj])
    have hi := ih ht
    by_cases he : k = 0
    · subst k
      cases hd : predClock n ds with
      | none =>
        simp only [hd] at hi
        simp only [predClock, if_true, hd, Option.map_none, clockValue, hi, Nat.mul_zero, Nat.zero_add]
      | some out =>
        simp only [hd] at hi
        simp only [predClock, if_true, hd, Option.map_some, List.length_cons]
        refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ hi.1, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact Nat.le_refl _
          · exact hi.2.1 j hj
        · simp only [clockValue, hi.2.2, Nat.mul_add, Nat.mul_one, Nat.zero_add]
          omega
    · simp only [predClock, if_neg he, List.length_cons]
      refine ⟨True.intro, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · exact ht j hj
      · simp only [clockValue]; omega

/-- Inline borrowing only inspects digit guards. Complement discovery is delegated to a named rule. -/
def borrowExpr (base onZero i : Nat) (N : MExp) : List (MExp × MExp) → List MExp → MExp
  | [], ctx => .call onZero ctx
  | (_, suf) :: ps, ctx =>
    ifP (exactLengthP suf) (borrowExpr base onZero (i + 1) N ps ctx)
      (.call (base + 2 * i) (.seq suf .any :: .eps :: N :: (pairArgs ps ++ ctx)))

/-- After complement discovery, restore the pair order and reset all borrowed lower digits. -/
def packClockBody (next lower restSize : Nat) : MExp :=
  .call next (.param 2 :: (repeatPair (.param 2) .eps lower ++
    (.param 1 :: .param 0 :: paramsFrom 3 restSize)))

theorem packClockBody_subst (next lower : Nat) (suf pre N : MExp) (rest : List MExp) :
    MExp.subst (suf :: pre :: N :: rest) (packClockBody next lower rest.length) =
      .call next (N :: (repeatPair N .eps lower ++ (pre :: suf :: rest))) := by
  simp [packClockBody, MExp.subst, MExp.substArgs, substArgs_append, subst_repeatPair,
    argAt, subst_paramsFrom_cons, subst_paramsFrom]

theorem packClockBody_firstOrder (next lower restSize : Nat) : (packClockBody next lower restSize).FirstOrder :=
  ⟨trivial, firstOrderArgs_append (repeatPair_firstOrder (a := .param 2) (b := .eps) trivial trivial lower)
    ⟨trivial, trivial, paramsFrom_firstOrder 3 restSize⟩⟩

/-- The two rules allocated for every digit: complement discovery, then static repacking. -/
def BorrowRules (g : MGrammar) (base next digits ctxSize : Nat) : Prop :=
  ∀ i, i < digits →
    ruleAtM g.rules (base + 2 * i) = some
      ⟨3 + 2 * (digits - i - 1) + ctxSize,
        complementContextBody (base + 2 * i) (base + 2 * i + 1) (1 + 2 * (digits - i - 1) + ctxSize)⟩ ∧
    ruleAtM g.rules (base + 2 * i + 1) = some
      ⟨3 + 2 * (digits - i - 1) + ctxSize,
        packClockBody next i (2 * (digits - i - 1) + ctxSize)⟩

/-- The concrete CBN borrowing expression implements predecessor on an entire fixed-width clock.
Zero and positive continuations preserve all observations, with the captured context unchanged. -/
theorem borrowExpr_iff {g : MGrammar} (hg : g.FirstOrder) {base next onZero digits : Nat}
    (ctx : List MExp) (hr : BorrowRules g base next digits ctx.length)
    (x : List Char) (ds : List Nat) (hv : ∀ k ∈ ds, k ≤ x.length) (i : Nat)
    (hi : i + ds.length = digits) (r : Option (List Char)) :
    MacroObs g (borrowExpr base onZero i (skipN x.length) (clockPairs x.length ds) ctx) x r ↔
      match predClock x.length ds with
      | none => MacroObs g (.call onZero ctx) x r
      | some out => MacroObs g (.call next
          (skipN x.length :: (clockArgs x.length (List.replicate i x.length ++ out) ++ ctx))) x r := by
  induction ds generalizing i with
  | nil => rfl
  | cons k ds ih =>
    have hk := hv k (by simp)
    have hds : ∀ j ∈ ds, j ≤ x.length := fun j hj => hv j (by simp [hj])
    change MacroObs g (ifP (exactLengthP (skipN (x.length - k)))
      (borrowExpr base onZero (i + 1) (skipN x.length) (clockPairs x.length ds) ctx)
      (.call (base + 2 * i) (.seq (skipN (x.length - k)) .any :: .eps :: skipN x.length ::
        (clockArgs x.length ds ++ ctx)))) x r ↔ _
    have ht := exactLength_obs (skipN_rep g (x.length - k)) x
    by_cases he : k = 0
    · subst k
      simp only [Nat.sub_zero, if_true] at ht ⊢
      rw [ifP_true_iff ht r, ih hds (i + 1) (by simp only [List.length_cons] at hi; omega)]
      cases hd : predClock x.length ds with
      | none => simp only [predClock, if_true, hd, Option.map_none]
      | some out =>
        simp only [predClock, if_true, hd, Option.map_some]
        rw [List.replicate_succ', List.append_assoc]
        rfl
    · have hn : x.length - k ≠ x.length := by omega
      rw [if_neg hn] at ht
      rw [ifP_false_iff ht r]
      have hdlen : digits - i - 1 = ds.length := by simp only [List.length_cons] at hi; omega
      obtain ⟨hh, hp⟩ := hr i (by simp only [List.length_cons] at hi; omega)
      let tailArgs := clockArgs x.length ds ++ ctx
      let helperCtx := skipN x.length :: tailArgs
      have hh' : ruleAtM g.rules (base + 2 * i) = some
          ⟨helperCtx.length + 2, complementContextBody (base + 2 * i) (base + 2 * i + 1) helperCtx.length⟩ := by
        have hsz : helperCtx.length = 1 + 2 * (digits - i - 1) + ctx.length := by
          simp only [helperCtx, tailArgs, List.length_cons, List.length_append, clockArgs_length, hdlen]
          omega
        have har : helperCtx.length + 2 = 3 + 2 * (digits - i - 1) + ctx.length := by omega
        rw [har, hsz]
        exact hh
      have hp' : ruleAtM g.rules (base + 2 * i + 1) = some
          ⟨tailArgs.length + 3, packClockBody next i tailArgs.length⟩ := by
        simpa only [tailArgs, List.length_append, clockArgs_length, hdlen,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
      change MacroObs g (.call (base + 2 * i)
        (.seq (skipN (x.length - k)) .any :: skipN 0 :: helperCtx)) x r ↔ _
      rw [call_pair_len_equiv hg (base + 2 * i) helperCtx
        ((skipN_rep g (x.length - k)).seq (lenRep_any g)) (skipN_rep g 0)
        (skipN_rep g (x.length - k + 1)) (skipN_rep g 0) x r]
      rw [complementContext_iff helperCtx hh' x (x.length - k + 1) 0 (by omega) r]
      rw [obs_call_iff hp' (by simp [helperCtx, tailArgs]), packClockBody_subst]
      have hpre : x.length - (x.length - k + 1) = k - 1 := by omega
      have hsuf : x.length - k + 1 = x.length - (k - 1) := by omega
      rw [hpre, hsuf]
      simp only [predClock, if_neg he, clockArgs_append, clockArgs_replicate]
      simp only [clockArgs, clockPairs, List.map_cons, pairArgs, tailArgs, List.append_assoc, List.cons_append]

end Shallot.MacroPeg.CBVtoCBN
