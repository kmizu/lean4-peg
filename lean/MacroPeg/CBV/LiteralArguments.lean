import MacroPeg.CBV.ReplayFusion

/-! Literal and forwarded-literal arguments have statically known values, but
Par still requires all their prefix matches to succeed at the caller position. -/
namespace Shallot.MacroPeg.CBV.LiteralArguments

def Arg (V : List (List Char)) : MExp → Prop
  | .lit w => w ∈ V
  | .param _ => True
  | _ => False

def Supported (V : List (List Char)) : MExp → Prop
  | .call _ args => ∀ a ∈ args, Arg V a
  | .seq a b | .alt a b => Supported V a ∧ Supported V b
  | .star a | .notP a => Supported V a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

def resolve (E : List (List Char)) : MExp → Option (List Char)
  | .lit w => some w
  | .param k => E[k]?
  | _ => none

def resolveArgs (E : List (List Char)) : List MExp → Option (List (List Char))
  | [] => some []
  | a :: args => do
    let w ← resolve E a
    let W ← resolveArgs E args
    pure (w::W)

def good (x : List Char) (p : Nat) (W : List (List Char)) : Bool :=
  W.all (fun w => (Shallot.stripPrefix? w (sfx x p)).isSome)

def guards : List (List Char) → MExp
  | [] => .eps
  | w :: W => .seq (.andP (.lit w)) (guards W)

theorem guards_firstOrder (W : List (List Char)) : (guards W).FirstOrder := by
  induction W <;> simp_all [guards,MExp.FirstOrder,MExp.andP]

theorem guards_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E W : List (List Char)) (p : Nat) :
    evV g x s T E (guards W) p = if good x p W then some (some p) else some none := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    cases hs : Shallot.stripPrefix? w (sfx x p) <;> simp [guards,MExp.andP,evV,good,hs,ih]

theorem arg_firstOrder {V : List (List Char)} {a : MExp} (h : Arg V a) : a.FirstOrder := by
  cases a <;> first | trivial | exact False.elim h

theorem args_firstOrder {V : List (List Char)} {args : List MExp} (h : ∀ a ∈ args, Arg V a) :
    MExp.FirstOrderArgs args := by
  induction args with
  | nil => trivial
  | cons a args ih => exact ⟨arg_firstOrder (h a (by simp)),ih (fun b hb => h b (by simp [hb]))⟩

theorem supported_firstOrder {V : List (List Char)} : ∀ e, Supported V e → e.FirstOrder
  | .call _ _, h => args_firstOrder h
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder a h.1,supported_firstOrder b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem resolveArgs_bounds {V E : List (List Char)} (hE : ∀ w ∈ E, w ∈ V) :
    ∀ args, (∀ a ∈ args, Arg V a) → ∀ W, resolveArgs E args = some W →
      W.length = args.length ∧ ∀ w ∈ W, w ∈ V
  | [], _, W, hw => by simp [resolveArgs] at hw; subst W; simp
  | a::args, ha, W, hw => by
    have htail : ∀ b ∈ args, Arg V b := fun b hb => ha b (by simp [hb])
    cases hr : resolve E a with
    | none => simp [resolveArgs,hr] at hw
    | some w =>
      cases ht : resolveArgs E args with
      | none => simp [resolveArgs,hr,ht] at hw
      | some ws =>
        have he : W = w::ws := by simpa [resolveArgs,hr,ht] using hw.symm
        subst W
        have hb := resolveArgs_bounds hE args htail ws ht
        have hv : w ∈ V := by
          have hh := ha a (by simp)
          cases a with
          | lit v =>
            have he : v=w := Option.some.inj hr
            subst v
            exact hh
          | param k => exact hE w (List.mem_of_getElem? hr)
          | _ => simp [resolve] at hr
        exact ⟨by simp [hb.1],by intro v hm; rcases List.mem_cons.mp hm with rfl | hm; exact hv; exact hb.2 v hm⟩

/-- Resolve the whole argument vector and check every literal at the same
original position. Matching the values remains mandatory even if the callee
never refers to them. -/
theorem arguments_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) {V : List (List Char)}
    (p : Nat) (hp : p ≤ x.length) :
    ∀ args, (∀ a ∈ args, Arg V a) →
      evParArgs g x s T E args p =
        match resolveArgs E args with
        | none => some none
        | some W => if good x p W then some (some W) else some none
  | [], _ => rfl
  | a::args, ha => by
    have ht := arguments_eval g x s T E p hp args (fun b hb => ha b (by simp [hb]))
    have hh := ha a (by simp)
    have step : ∀ w, resolve E a = some w →
        evV g x s T E a p = match Shallot.stripPrefix? w (sfx x p) with
          | some rest => some (some rest.length) | none => some none := by
      intro w hr
      cases a <;> first | rfl | (simp_all [resolve,evV] <;> rfl)
    cases hr : resolve E a with
    | none =>
      have hf : evV g x s T E a p = some none := by
        cases a <;> simp_all [Arg,resolve,evV]
      simp [evParArgs,hf,resolveArgs,hr]
    | some w =>
      rw [evParArgs,step w hr]
      cases hs : Shallot.stripPrefix? w (sfx x p) with
      | none => cases hv : resolveArgs E args <;> simp [resolveArgs,hr,hv,good,hs]
      | some rest =>
        have he : pre x p rest.length = w := by
          have hb := pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact w _ _).mp hs)
          simpa only [length_sfx x hp] using hb
        dsimp only
        rw [he,ht]
        cases hv : resolveArgs E args with
        | none => simp [resolveArgs,hr,hv]
        | some W =>
          simp only [resolveArgs,hr,hv]
          have hg : good x p (w::W) = good x p W := by simp [good,hs]
          change (match (if good x p W then some (some W) else some none) with
            | some (some Z) => some (some (w::Z)) | r => r) =
              if good x p (w::W) then some (some (w::W)) else some none
          rw [hg]
          cases good x p W <;> rfl

end Shallot.MacroPeg.CBV.LiteralArguments
