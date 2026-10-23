import MacroPeg.CBV.PrefixDecrement
import MacroPeg.CBVtoCBN.ClockStep

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation
open CBVtoCBN (paramsFrom paramsFrom_firstOrder subst_paramsFrom_cons subst_paramsFrom
  predClock substArgs_append)

theorem prefixValues_append (x : List Char) (a b : List Nat) :
    prefixValues x (a ++ b) = prefixValues x a ++ prefixValues x b := by
  induction a with
  | nil => rfl
  | cons k a ih => simp [prefixValues, ih]

theorem prefixValues_replicate (x : List Char) (k d : Nat) :
    prefixValues x (List.replicate d k) = List.replicate d (.lit (x.take k)) := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, prefixValues, ih]

theorem substArgs_replicate (args : List MExp) (a : MExp) (d : Nat) :
    MExp.substArgs args (List.replicate d a) = List.replicate d (MExp.subst args a) := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, MExp.substArgs, ih]

def clockPackBody (next lower restSize : Nat) : MExp :=
  .call next (.param 1 :: (List.replicate lower (.param 1) ++ .param 0 :: paramsFrom 2 restSize))

theorem clockPackBody_subst (next lower : Nat) (k N : MExp) (ctx : List MExp) :
    MExp.subst (k :: N :: ctx) (clockPackBody next lower ctx.length) =
      .call next (N :: (List.replicate lower N ++ k :: ctx)) := by
  simp [clockPackBody, MExp.subst, MExp.substArgs, substArgs_append,
    substArgs_replicate, argAt, subst_paramsFrom_cons, subst_paramsFrom]

def clockBorrow (base equal onZero : Nat) (i : Nat) (N : MExp) :
    List MExp → List MExp → MExp
  | [], ctx => .call onZero ctx
  | k :: ds, ctx =>
    branch (.call equal [k, .lit []])
      (clockBorrow base equal onZero (i + 1) N ds ctx)
      (.call (base + 2 * i) (k :: .lit [] :: N :: (ds ++ ctx)))

def clockHelperRule (base equal digits ctxSize i : Nat) : MRule :=
  ⟨3 + (digits - i - 1) + ctxSize,
    predecessorBody (base + 2 * i) equal (base + 2 * i + 1)
      (1 + (digits - i - 1) + ctxSize)⟩

def clockPackRule (next digits ctxSize i : Nat) : MRule :=
  ⟨2 + (digits - i - 1) + ctxSize, clockPackBody next i (digits - i - 1 + ctxSize)⟩

def ClockRules (g : MGrammar) (base equal next digits ctxSize : Nat) : Prop :=
  ∀ i, i < digits →
    ruleAtM g.rules (base + 2 * i) = some (clockHelperRule base equal digits ctxSize i) ∧
    ruleAtM g.rules (base + 2 * i + 1) = some (clockPackRule next digits ctxSize i)

/-- One fixed-width clock predecessor. Earlier zero digits are restored to
the input length, and all enclosing counters survive unchanged. This is an
observation equivalence even for an undefined continuation. -/
theorem clockBorrow_iff {g : MGrammar} {base equal next onZero digits : Nat}
    (ctx : List Nat) (hr : ClockRules g base equal next digits ctx.length)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (ds : List Nat) (hv : ∀ k ∈ ds, k ≤ x.length) (i : Nat)
    (hi : i + ds.length = digits) (r : Option (List Char)) :
    SObs g .callByValuePar
      (clockBorrow base equal onZero i (.lit (x.take x.length))
        (prefixValues x ds) (prefixValues x ctx)) x r ↔
      match predClock x.length ds with
      | none => SObs g .callByValuePar (.call onZero (prefixValues x ctx)) x r
      | some out => SObs g .callByValuePar
          (.call next (prefixValues x (x.length :: ((List.replicate i x.length ++ out) ++ ctx)))) x r := by
  induction ds generalizing i with
  | nil => rfl
  | cons k ds ih =>
    have hk := hv k List.mem_cons_self
    have hds : ∀ j ∈ ds, j ≤ x.length := fun j hj => hv j (List.mem_cons_of_mem _ hj)
    change SObs g .callByValuePar
      (branch (.call equal [.lit (x.take k), .lit []])
        (clockBorrow base equal onZero (i + 1) (.lit (x.take x.length)) (prefixValues x ds) (prefixValues x ctx))
        (.call (base + 2 * i)
          (.lit (x.take k) :: .lit [] :: .lit (x.take x.length) :: (prefixValues x ds ++ prefixValues x ctx)))) x r ↔ _
    have hEq := equal_obs he x k 0 hk (by omega)
    by_cases h0 : k = 0
    · subst k
      simp only [equalCall, List.take_zero] at hEq
      simp only [List.take_zero]
      rw [branch_true_iff hEq r, ih hds (i + 1) (by simp only [List.length_cons] at hi; omega)]
      cases hd : predClock x.length ds with
      | none => simp only [predClock, if_true, hd, Option.map_none]
      | some out =>
        simp only [predClock, if_true, hd, Option.map_some]
        rw [List.replicate_succ', List.append_assoc]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
    · simp only [if_neg h0, equalCall, List.take_zero] at hEq
      rw [branch_false_iff hEq r]
      have hdlen : digits - i - 1 = ds.length := by simp only [List.length_cons] at hi; omega
      obtain ⟨hHelper, hPack⟩ := hr i (by simp only [List.length_cons] at hi; omega)
      let helperCtx := x.length :: (ds ++ ctx)
      have hHelper' : ruleAtM g.rules (base + 2 * i) = some
          ⟨helperCtx.length + 2, predecessorBody (base + 2 * i) equal (base + 2 * i + 1) helperCtx.length⟩ := by
        simpa only [clockHelperRule, helperCtx, List.length_cons, List.length_append, hdlen,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hHelper
      have hPack' : ruleAtM g.rules (base + 2 * i + 1) = some
          ⟨(ds ++ ctx).length + 2, clockPackBody next i (ds ++ ctx).length⟩ := by
        simpa only [clockPackRule, List.length_append, hdlen,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hPack
      have hStart : .lit (x.take k) :: .lit [] :: .lit (x.take x.length) ::
          (prefixValues x ds ++ prefixValues x ctx) =
          .lit (x.take k) :: .lit (x.take 0) :: prefixValues x helperCtx := by
        simp only [helperCtx, prefixValues, List.take_zero, prefixValues_append]
      rw [hStart, predecessor_iff helperCtx hHelper' he x k 0 hk (by omega) r]
      change SObs g .callByValuePar
        (.call (base + 2 * i + 1) (.lit (x.take (k - 1)) :: .lit (x.take x.length) :: prefixValues x (ds ++ ctx))) x r ↔ _
      have hvPack := prefixValues_args g x ((k - 1) :: x.length :: (ds ++ ctx))
      simp only [prefixValues] at hvPack
      rw [par_call_iff hPack' (by simp) hvPack]
      rw [show (ds ++ ctx).length = (prefixValues x (ds ++ ctx)).length by simp,
        clockPackBody_subst]
      simp only [predClock, if_neg h0, prefixValues, prefixValues_append, prefixValues_replicate,
        List.append_assoc, List.cons_append]

end Shallot.MacroPeg.CBV.PrefixCounters
