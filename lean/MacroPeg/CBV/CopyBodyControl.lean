import MacroPeg.CBV.DelimitedWordPattern

namespace Shallot.MacroPeg.CBV.CopyBodyControl

inductive Body where
  | eps | fail | segment (i : Nat)
  | seq (a b : Body) | alt (a b : Body) | notP (a : Body) | star (a : Body)
  deriving Repr

def zeroWidth : Body → Bool
  | .eps | .fail | .notP _ => true
  | .segment _ => false
  | .seq a b | .alt a b => zeroWidth a && zeroWidth b
  | .star a => zeroWidth a

def check (arity : Nat) : Body → Bool
  | .eps | .fail => true
  | .segment i => decide (i<arity)
  | .seq a b | .alt a b => check arity a && check arity b
  | .notP a => check arity a
  | .star a => zeroWidth a && check arity a

def render (d : Char) : Body → MExp
  | .eps => .eps | .fail => MExp.failAlways
  | .segment i => DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d [i])
  | .seq a b => .seq (render d a) (render d b)
  | .alt a b => .alt (render d a) (render d b)
  | .notP a => .notP (render d a)
  | .star a => .star (render d a)

theorem render_firstOrder (d : Char) : ∀ e, (render d e).FirstOrder
  | .eps | .fail => True.intro
  | .segment _ => DelimiterTemplate.compile_firstOrder _ _
  | .seq a b | .alt a b => ⟨render_firstOrder d a,render_firstOrder d b⟩
  | .notP a | .star a => render_firstOrder d a

abbrev Result (α : Type) := Option (Option α)
def chain {α : Type} (r : Result α) (k : α → Result α) : Result α :=
  match r with | none => none | some none => some none | some (some s) => k s
def choice {α : Type} (r fallback : Result α) : Result α :=
  match r with | some none => fallback | other => other
def negative {α : Type} (s : α) : Result α → Result α
  | none => none | some none => some (some s) | some (some _) => some none
/-- The finite checker restricts this repetition to zero-width bodies. -/
def repeatZero {α : Type} (s : α) : Result α → Result α
  | none => none | some none => some (some s) | some (some _) => none

def eval {α : Type} (step : Nat → α → Option α) : Body → α → Result α
  | .eps,s => some (some s)
  | .fail,_ => some none
  | .segment i,s => some (step i s)
  | .seq a b,s => chain (eval step a s) (eval step b)
  | .alt a b,s => choice (eval step a s) (eval step b s)
  | .notP a,s => negative s (eval step a s)
  | .star a,s => repeatZero s (eval step a s)

inductive Related {α β : Type} (R : α → β → Prop) : Result α → Result β → Prop
  | undef : Related R none none
  | fail : Related R (some none) (some none)
  | ok (a : α) (b : β) : R a b → Related R (some (some a)) (some (some b))

theorem related_chain {α β : Type} {R : α → β → Prop} {a : Result α} {b : Result β}
    {ka : α → Result α} {kb : β → Result β} (h : Related R a b)
    (hk : ∀ a b, R a b → Related R (ka a) (kb b)) : Related R (chain a ka) (chain b kb) := by
  cases h with
  | undef => exact .undef
  | fail => exact .fail
  | ok a b hr => exact hk a b hr

theorem related_choice {α β : Type} {R : α → β → Prop} {a : Result α} {b : Result β}
    {fa : Result α} {fb : Result β} (h : Related R a b) (hf : Related R fa fb) :
    Related R (choice a fa) (choice b fb) := by
  cases h with
  | undef => exact .undef
  | fail => exact hf
  | ok a b hr => exact .ok a b hr

theorem related_negative {α β : Type} {R : α → β → Prop} {a : Result α} {b : Result β}
    {s : α} {t : β} (hst : R s t) (h : Related R a b) : Related R (negative s a) (negative t b) := by
  cases h with
  | undef => exact .undef
  | fail => exact .ok s t hst
  | ok _ _ _ => exact .fail

theorem related_repeatZero {α β : Type} {R : α → β → Prop} {a : Result α} {b : Result β}
    {s : α} {t : β} (hst : R s t) (h : Related R a b) : Related R (repeatZero s a) (repeatZero t b) := by
  cases h with
  | undef => exact .undef
  | fail => exact .ok s t hst
  | ok _ _ _ => exact .undef

theorem eval_related {α β : Type} (R : α → β → Prop) (aStep : Nat → α → Option α) (bStep : Nat → β → Option β)
    (hs : ∀ i a b, R a b → Related R (some (aStep i a)) (some (bStep i b))) :
    ∀ e a b, R a b → Related R (eval aStep e a) (eval bStep e b)
  | .eps,a,b,hab => .ok a b hab
  | .fail,_,_,_ => .fail
  | .segment i,a,b,hab => hs i a b hab
  | .seq a b,s,t,hst => related_chain (eval_related R aStep bStep hs a s t hst) (fun u v huv => eval_related R aStep bStep hs b u v huv)
  | .alt a b,s,t,hst => related_choice (eval_related R aStep bStep hs a s t hst) (eval_related R aStep bStep hs b s t hst)
  | .notP a,s,t,hst => related_negative hst (eval_related R aStep bStep hs a s t hst)
  | .star a,s,t,hst => related_repeatZero hst (eval_related R aStep bStep hs a s t hst)

theorem eval_zero {α : Type} (step : Nat → α → Option α) : ∀ e, zeroWidth e=true → ∀ s t,
    eval step e s=some (some t) → t=s
  | .eps,_,s,t,h => by cases h; rfl
  | .fail,_,_,_,h => by cases h
  | .segment _,h,_,_,_ => by cases h
  | .seq a b,h,s,t,he => by
    cases ha : eval step a s with
    | none => simp [eval,chain,ha] at he
    | some v => cases v with
      | none => simp [eval,chain,ha] at he
      | some u =>
        have hu := eval_zero step a (Bool.and_eq_true_iff.mp h).1 s u ha
        subst u
        exact eval_zero step b (Bool.and_eq_true_iff.mp h).2 s t (by simpa [eval,chain,ha] using he)
  | .alt a b,h,s,t,he => by
    cases ha : eval step a s with
    | none => simp [eval,choice,ha] at he
    | some v => cases v with
      | none => exact eval_zero step b (Bool.and_eq_true_iff.mp h).2 s t (by simpa [eval,choice,ha] using he)
      | some u =>
        have hu : u=t := by simpa [eval,choice,ha] using he
        subst u
        exact eval_zero step a (Bool.and_eq_true_iff.mp h).1 s t ha
  | .notP a,_,s,t,he => by
    cases ha : eval step a s with
    | none => simp [eval,negative,ha] at he
    | some v => cases v <;> simp_all [eval,negative]
  | .star a,_,s,t,he => by
    cases ha : eval step a s with
    | none => simp [eval,repeatZero,ha] at he
    | some v => cases v <;> simp_all [eval,repeatZero]

theorem eval_preserves {α : Type} (step : Nat → α → Option α) (P : α → Prop)
    (hstep : ∀ i s t, P s → step i s=some t → P t) :
    ∀ e s, P s → ∀ t, eval step e s=some (some t) → P t
  | .eps,s,hs,t,h => by cases h; exact hs
  | .fail,_,_,_,h => by cases h
  | .segment i,s,hs,t,h => hstep i s t hs (by simpa only [eval,Option.some.injEq] using h)
  | .seq a b,s,hs,t,h => by
    cases ha : eval step a s with
    | none => simp [eval,chain,ha] at h
    | some v => cases v with
      | none => simp [eval,chain,ha] at h
      | some u => exact eval_preserves step P hstep b u (eval_preserves step P hstep a s hs u ha) t (by simpa [eval,chain,ha] using h)
  | .alt a b,s,hs,t,h => by
    cases ha : eval step a s with
    | none => simp [eval,choice,ha] at h
    | some v => cases v with
      | none => exact eval_preserves step P hstep b s hs t (by simpa [eval,choice,ha] using h)
      | some u =>
        have hh : u=t := by simpa [eval,choice,ha] using h
        subst u; exact eval_preserves step P hstep a s hs t ha
  | .notP a,s,hs,t,h => by
    have ht := eval_zero step (.notP a) rfl s t h
    subst t; exact hs
  | .star a,s,hs,t,h => by
    cases ha : eval step a s with
    | none => simp [eval,repeatZero,ha] at h
    | some v => cases v with
      | none => have hh : s=t := by simpa [eval,repeatZero,ha] using h
                subst t; exact hs
      | some _ => simp [eval,repeatZero,ha] at h

inductive Plan where
  | fail | undef | done (history : List Nat)
  | branch (query : List Nat) (yes no : Plan)
  deriving Repr

def Plan.eval (query : List Nat → Bool) : Plan → Result (List Nat)
  | .fail => some none | .undef => none | .done h => some (some h)
  | .branch h yes no => if query h then yes.eval query else no.eval query

def compile : Body → List Nat → (List Nat → Plan) → Plan → Plan
  | .eps,h,k,_ => k h
  | .fail,_,_,f => f
  | .segment i,h,k,f => .branch (h++[i]) (k (h++[i])) f
  | .seq a b,h,k,f => compile a h (fun h' => compile b h' k f) f
  | .alt a b,h,k,f => compile a h k (compile b h k f)
  | .notP a,h,k,f => compile a h (fun _ => f) (k h)
  | .star a,h,k,_ => compile a h (fun _ => .undef) (k h)

def historyStep (query : List Nat → Bool) (i : Nat) (h : List Nat) : Option (List Nat) :=
  if query (h++[i]) then some (h++[i]) else none

theorem compile_eval (query : List Nat → Bool) : ∀ e h k f,
    (compile e h k f).eval query=
      match eval (historyStep query) e h with
      | none => none | some none => f.eval query | some (some h') => (k h').eval query
  | .eps,_,_,_ | .fail,_,_,_ => rfl
  | .segment i,h,k,f => by cases hq : query (h++[i]) <;> simp [compile,Plan.eval,eval,historyStep,hq]
  | .seq a b,h,k,f => by
    rw [compile,compile_eval query a]
    cases ha : eval (historyStep query) a h with
    | none => simp [eval,chain,ha]
    | some v => cases v with
      | none => simp [eval,chain,ha]
      | some h' => simpa only [eval,chain,ha] using compile_eval query b h' k f
  | .alt a b,h,k,f => by
    rw [compile,compile_eval query a]
    cases ha : eval (historyStep query) a h with
    | none => simp [eval,choice,ha]
    | some v => cases v with
      | none => simpa only [eval,choice,ha] using compile_eval query b h k f
      | some _ => simp [eval,choice,ha]
  | .notP a,h,k,f => by
    rw [compile,compile_eval query a]
    cases ha : eval (historyStep query) a h with
    | none => simp [eval,negative,ha]
    | some v => cases v <;> simp [eval,negative,ha]
  | .star a,h,k,f => by
    rw [compile,compile_eval query a]
    cases ha : eval (historyStep query) a h with
    | none => simp [eval,repeatZero,ha]
    | some v => cases v <;> simp [eval,repeatZero,ha,Plan.eval]

def normalized (e : Body) : Plan := compile e [] Plan.done .fail

theorem normalized_eval (query : List Nat → Bool) (e : Body) : (normalized e).eval query=eval (historyStep query) e [] := by
  rw [normalized,compile_eval]
  cases eval (historyStep query) e [] with
  | none => rfl
  | some v => cases v <;> rfl

def Plan.keys : Plan → List (List Nat)
  | .fail | .undef => [] | .done h => [h]
  | .branch h a b => h::(a.keys++b.keys)
def Plan.Scope (arity : Nat) (p : Plan) := ∀ h∈p.keys, ∀ i∈h, i<arity

theorem compile_scope (arity : Nat) : ∀ e, check arity e=true → ∀ h,
    (∀ i∈h, i<arity) → ∀ k, (∀ h, (∀ i∈h, i<arity) → (k h).Scope arity) → ∀ f,
    f.Scope arity → (compile e h k f).Scope arity
  | .eps,_,h,hh,k,hk,_,_ => hk h hh
  | .fail,_,_,_,_,_,f,hf => hf
  | .segment i,hc,h,hh,k,hk,f,hf => by
    have hi : i<arity := of_decide_eq_true hc
    have hs : ∀ j∈h++[i], j<arity := by intro j hj; simp at hj; rcases hj with hj|rfl; exact hh j hj; exact hi
    intro hist hm j hj
    rcases List.mem_cons.mp hm with rfl|hm
    · exact hs j hj
    · rcases List.mem_append.mp hm with hm|hm
      · exact hk (h++[i]) hs hist hm j hj
      · exact hf hist hm j hj
  | .seq a b,hc,h,hh,k,hk,f,hf =>
      compile_scope arity a (Bool.and_eq_true_iff.mp hc).1 h hh _ (fun h hh => compile_scope arity b (Bool.and_eq_true_iff.mp hc).2 h hh k hk f hf) f hf
  | .alt a b,hc,h,hh,k,hk,f,hf =>
      compile_scope arity a (Bool.and_eq_true_iff.mp hc).1 h hh k hk _ (compile_scope arity b (Bool.and_eq_true_iff.mp hc).2 h hh k hk f hf)
  | .notP a,hc,h,hh,k,hk,f,hf => compile_scope arity a hc h hh _ (fun _ _ => hf) _ (hk h hh)
  | .star a,hc,h,hh,k,hk,_,_ => compile_scope arity a (Bool.and_eq_true_iff.mp hc).2 h hh _ (fun _ _ => by intro h hm; cases hm) _ (hk h hh)

theorem normalized_scope (arity : Nat) (e : Body) (he : check arity e=true) : (normalized e).Scope arity := by
  apply compile_scope arity e he [] (by simp)
  · intro h hh hist hm i hi
    have he : hist=h := by simpa [Plan.keys] using hm
    subst hist; exact hh i hi
  · intro h hm; cases hm

end Shallot.MacroPeg.CBV.CopyBodyControl
