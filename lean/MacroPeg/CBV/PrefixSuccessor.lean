import MacroPeg.CBV.PrefixClock

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation
open CBVtoCBN (clockValue paramsFrom paramsFrom_firstOrder firstOrderArgs_append
  substArgs_append subst_paramsFrom_slice predClock)

/-- Fixed-width successor in base `n+1`, least-significant digit first. -/
def succClock (n : Nat) : List Nat → Option (List Nat)
  | [] => none
  | k :: ds => if k = n then (succClock n ds).map (0 :: ·) else some ((k + 1) :: ds)

theorem succClock_spec (n : Nat) (ds : List Nat) (hv : ∀ k ∈ ds, k ≤ n) :
    match succClock n ds with
    | none => clockValue n ds + 1 = (n + 1) ^ ds.length
    | some out => out.length = ds.length ∧ (∀ k ∈ out, k ≤ n) ∧
        clockValue n out = clockValue n ds + 1 := by
  induction ds with
  | nil => rfl
  | cons k ds ih =>
    have hk := hv k (by simp)
    have ht : ∀ j ∈ ds, j ≤ n := fun j hj => hv j (by simp [hj])
    have hi := ih ht
    by_cases he : k = n
    · subst k
      cases hd : succClock n ds with
      | none =>
        simp only [hd] at hi
        simp only [succClock, if_true, hd, Option.map_none, clockValue, List.length_cons,
          Nat.pow_succ]
        rw [← hi, Nat.mul_comm (clockValue n ds + 1) (n + 1), Nat.mul_add, Nat.mul_one]
        omega
      | some out =>
        simp only [hd] at hi
        simp only [succClock, if_true, hd, Option.map_some, List.length_cons]
        refine ⟨by omega, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · omega
          · exact hi.2.1 j hj
        · simp only [clockValue, Nat.zero_add, hi.2.2, Nat.mul_add, Nat.mul_one]
          omega
    · simp only [succClock, if_neg he, List.length_cons]
      refine ⟨True.intro, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · omega
        · exact ht j hj
      · simp only [clockValue]; omega

theorem pred_succClock (n : Nat) (ds out : List Nat)
    (h : succClock n ds = some out) : predClock n out = some ds := by
  induction ds generalizing out with
  | nil => simp [succClock] at h
  | cons k ds ih =>
    by_cases hk : k = n
    · subst k
      cases ht : succClock n ds with
      | none => simp [succClock, ht] at h
      | some tail =>
        simp only [succClock, if_true, ht, Option.map_some, Option.some.injEq] at h
        subst out
        simp [predClock, ih tail ht]
    · simp only [succClock, if_neg hk, Option.some.injEq] at h
      subst out
      simp [predClock]

def carryExpr (equal next overflow lower : Nat) (N : MExp) :
    List MExp → List MExp → MExp
  | [], ctx => .call overflow ctx
  | k :: ds, ctx =>
    branch (.call equal [k, N])
      (carryExpr equal next overflow (lower + 1) N ds ctx)
      (.call next (N :: (List.replicate lower (.lit []) ++ .seq k .any :: (ds ++ ctx))))

theorem carryExpr_subst (args : List MExp) (equal next overflow lower : Nat) (N : MExp)
    (ds ctx : List MExp) :
    MExp.subst args (carryExpr equal next overflow lower N ds ctx) =
      carryExpr equal next overflow lower (MExp.subst args N)
        (MExp.substArgs args ds) (MExp.substArgs args ctx) := by
  induction ds generalizing lower with
  | nil => rfl
  | cons k ds ih =>
    simp only [carryExpr, branch, MExp.subst, MExp.substArgs, substArgs_append,
      substArgs_replicate, ih]

theorem carryExpr_firstOrder (equal next overflow lower : Nat) (N : MExp) (hN : N.FirstOrder)
    (ds ctx : List MExp) (hd : MExp.FirstOrderArgs ds) (hc : MExp.FirstOrderArgs ctx) :
    (carryExpr equal next overflow lower N ds ctx).FirstOrder := by
  induction ds generalizing lower with
  | nil => exact hc
  | cons k ds ih =>
    have hz : MExp.FirstOrderArgs (List.replicate lower (.lit [])) := by
      induction lower with
      | zero => trivial
      | succ lower ih => exact ⟨trivial, ih⟩
    have hg : (MExp.call equal [k, N]).FirstOrder := ⟨hd.1, hN, trivial⟩
    have hn : (MExp.call next (N :: (List.replicate lower (.lit []) ++
        .seq k .any :: (ds ++ ctx)))).FirstOrder :=
      ⟨hN, firstOrderArgs_append hz ⟨⟨hd.1, trivial⟩, firstOrderArgs_append hd.2 hc⟩⟩
    exact ⟨⟨hg, ih (lower + 1) hd.2⟩, hg, hn⟩

theorem prefixValues_prepend_args {g : MGrammar} {x : List Char} {args vals : List MExp}
    (h : DerivesArgsPar g .callByValuePar x args vals) (ks : List Nat) :
    DerivesArgsPar g .callByValuePar x (prefixValues x ks ++ args) (prefixValues x ks ++ vals) := by
  induction ks with
  | nil => exact h
  | cons k ks ih =>
    exact .cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x k) (prefix_eq x k) ih

theorem par_prefix_args_iff {g : MGrammar} {x : List Char} {i : Nat}
    {args : List MExp} {ks : List Nat}
    (h : DerivesArgsPar g .callByValuePar x args (prefixValues x ks)) (r : Option (List Char)) :
    SObs g .callByValuePar (.call i args) x r ↔
      SObs g .callByValuePar (.call i (prefixValues x ks)) x r := by
  have hlen : ∀ {as vs : List MExp}, DerivesArgsPar g .callByValuePar x as vs → as.length = vs.length := by
    intro as
    induction as with
    | nil => intro vs hv; cases hv; rfl
    | cons a as ih =>
      intro vs hv
      cases hv with
      | cons _ _ _ _ _ _ _ _ _ ht => simpa only [List.length_cons] using congrArg Nat.succ (ih ht)
  have hl := hlen h
  cases hr : ruleAtM g.rules i with
  | none =>
    have ha : SObs g .callByValuePar (.call i args) x none := ⟨_, .callMissing i args x hr, rfl⟩
    have hb : SObs g .callByValuePar (.call i (prefixValues x ks)) x none :=
      ⟨_, .callMissing i (prefixValues x ks) x hr, rfl⟩
    rw [unique_iff ha r, unique_iff hb r]
  | some rule =>
    by_cases he : rule.arity = args.length
    · rw [par_call_iff hr he h, par_call_iff hr (he.trans hl) (prefixValues_args g x ks)]
    · have he' : rule.arity ≠ (prefixValues x ks).length := by omega
      have ha : SObs g .callByValuePar (.call i args) x none := ⟨_, .callArity i args rule x hr he, rfl⟩
      have hb : SObs g .callByValuePar (.call i (prefixValues x ks)) x none :=
        ⟨_, .callArity i (prefixValues x ks) rule x hr he', rfl⟩
      rw [unique_iff ha r, unique_iff hb r]

/-- All other counters survive. The continuation may fail or be undefined:
the guard never restarts the overflow branch after a failed continuation. -/
theorem carryExpr_iff {g : MGrammar} {equal next overflow : Nat}
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (ds ctx : List Nat) (hv : ∀ k ∈ ds, k ≤ x.length)
    (lower : Nat) (r : Option (List Char)) :
    SObs g .callByValuePar
      (carryExpr equal next overflow lower (.lit (x.take x.length))
        (prefixValues x ds) (prefixValues x ctx)) x r ↔
      match succClock x.length ds with
      | none => SObs g .callByValuePar (.call overflow (prefixValues x ctx)) x r
      | some out => SObs g .callByValuePar
          (.call next (prefixValues x (x.length :: ((List.replicate lower 0 ++ out) ++ ctx)))) x r := by
  induction ds generalizing lower with
  | nil => rfl
  | cons k ds ih =>
    have hk := hv k (by simp)
    have ht : ∀ j ∈ ds, j ≤ x.length := fun j hj => hv j (by simp [hj])
    have hg := equal_obs he x k x.length hk (by omega)
    change SObs g .callByValuePar
      (branch (.call equal [.lit (x.take k), .lit (x.take x.length)])
        (carryExpr equal next overflow (lower + 1) (.lit (x.take x.length))
          (prefixValues x ds) (prefixValues x ctx))
        (.call next (.lit (x.take x.length) :: (List.replicate lower (.lit []) ++
          .seq (.lit (x.take k)) .any :: (prefixValues x ds ++ prefixValues x ctx))))) x r ↔ _
    by_cases hmax : k = x.length
    · simp only [equalCall, if_pos hmax] at hg
      rw [branch_true_iff hg r, ih ht (lower + 1)]
      cases hs : succClock x.length ds with
      | none => simp only [succClock, if_pos hmax, hs, Option.map_none]
      | some out =>
        simp only [succClock, if_pos hmax, hs, Option.map_some]
        rw [List.replicate_succ', List.append_assoc]
        simp only [List.cons_append, List.nil_append, List.append_assoc]
    · simp only [equalCall, if_neg hmax] at hg
      rw [branch_false_iff hg r]
      simp only [succClock, if_neg hmax]
      obtain ⟨t, hd⟩ := grow_obs g x k (by omega)
      have ha : DerivesArgsPar g .callByValuePar x
          (.lit (x.take x.length) :: (List.replicate lower (.lit []) ++
            .seq (.lit (x.take k)) .any :: (prefixValues x ds ++ prefixValues x ctx)))
          (prefixValues x (x.length :: ((List.replicate lower 0 ++ (k + 1) :: ds) ++ ctx))) := by
        have hb : DerivesArgsPar g .callByValuePar x
            (.seq (.lit (x.take k)) .any :: prefixValues x (ds ++ ctx))
            (.lit (x.take (k + 1)) :: prefixValues x (ds ++ ctx)) :=
          .cons _ _ _ _ _ _ _ hd (prefix_eq x (k + 1)) (prefixValues_args g x (ds ++ ctx))
        have hh := prefixValues_prepend_args hb (x.length :: List.replicate lower 0)
        simpa only [prefixValues, prefixValues_append, prefixValues_replicate, List.take_zero,
          List.cons_append, List.append_assoc] using hh
      exact par_prefix_args_iff ha r

def successorBody (equal next overflow digits ctxSize : Nat) : MExp :=
  carryExpr equal next overflow 0 (.param 0) (paramsFrom 1 digits) (paramsFrom (1 + digits) ctxSize)

theorem successorBody_firstOrder (equal next overflow digits ctxSize : Nat) :
    (successorBody equal next overflow digits ctxSize).FirstOrder :=
  carryExpr_firstOrder equal next overflow 0 (.param 0) (by trivial) _ _
    (paramsFrom_firstOrder 1 digits) (paramsFrom_firstOrder (1 + digits) ctxSize)

theorem successorBody_subst (equal next overflow : Nat) (N : MExp) (ds ctx : List MExp) :
    MExp.subst (N :: (ds ++ ctx)) (successorBody equal next overflow ds.length ctx.length) =
      carryExpr equal next overflow 0 N ds ctx := by
  rw [successorBody, carryExpr_subst]
  have hd := subst_paramsFrom_slice [N] ds ctx
  have hc := subst_paramsFrom_slice (N :: ds) ctx []
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.singleton_append] at hd
  simp only [List.length_cons, List.append_nil, List.cons_append] at hc
  rw [show 1 + ds.length = ds.length + 1 by omega, hd, hc]
  rfl

/-- One named rule performs the successor on the same original input.
Digits and the context width are fixed by the grammar, not by the input. -/
theorem successor_iff {g : MGrammar} {entry equal next overflow digits : Nat} (ctx : List Nat)
    (hr : ruleAtM g.rules entry =
      some ⟨1 + digits + ctx.length, successorBody equal next overflow digits ctx.length⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits)
    (hv : ∀ k ∈ ds, k ≤ x.length) (r : Option (List Char)) :
    SObs g .callByValuePar (.call entry (prefixValues x (x.length :: (ds ++ ctx)))) x r ↔
      match succClock x.length ds with
      | none => SObs g .callByValuePar (.call overflow (prefixValues x ctx)) x r
      | some out => SObs g .callByValuePar
          (.call next (prefixValues x (x.length :: (out ++ ctx)))) x r := by
  rw [par_call_iff hr (by simp [hd]; omega) (prefixValues_args g x (x.length :: (ds ++ ctx)))]
  simp only [prefixValues, prefixValues_append]
  rw [show digits = (prefixValues x ds).length by simp [hd],
    show ctx.length = (prefixValues x ctx).length by simp, successorBody_subst]
  have hh := carryExpr_iff (next := next) (overflow := overflow) he x ds ctx hv 0 r
  simpa only [List.replicate_zero, List.nil_append, prefixValues, prefixValues_append] using hh

end Shallot.MacroPeg.CBV.PrefixCounters
