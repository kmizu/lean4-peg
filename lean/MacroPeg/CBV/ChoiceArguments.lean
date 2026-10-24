import MacroPeg.CBV.LiteralArguments
import MacroPeg.CBV.RootObservation

/-! Select a literal-valued argument through ordered choices. Continuation
failure does not change which argument alternative was selected. -/
namespace Shallot.MacroPeg.CBV.ChoiceArguments

def Arg (V : List (List Char)) : MExp → Prop
  | .lit w => w ∈ V
  | .param _ => True
  | .alt a b => Arg V a ∧ Arg V b
  | _ => False

def Supported (V : List (List Char)) : MExp → Prop
  | .call _ args => ∀ a ∈ args, Arg V a
  | .seq a b | .alt a b => Supported V a ∧ Supported V b
  | .star a | .notP a => Supported V a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

def erase (E : List (List Char)) : MExp → MExp
  | .lit w => .lit w
  | .param k => match E[k]? with | some w => .lit w | none => MExp.failAlways
  | .alt a b => .alt (erase E a) (erase E b)
  | _ => MExp.failAlways

def select (E : List (List Char)) (a : MExp) (K : List Char → MExp) : MExp := match a with
  | .lit w => .seq (.andP (.lit w)) (K w)
  | .param k => match E[k]? with
    | some w => .seq (.andP (.lit w)) (K w)
    | none => MExp.failAlways
  | .alt a b => RootObservation.branch (.andP (erase E a)) (select E a K) (select E b K)
  | _ => MExp.failAlways

def selectArgs (E : List (List Char)) : List MExp → (List (List Char) → MExp) → MExp
  | [], K => K []
  | a::args, K => select E a (fun w => selectArgs E args (fun W => K (w::W)))

theorem erase_firstOrder (E : List (List Char)) : ∀ a, (erase E a).FirstOrder
  | .lit _ => trivial
  | .param k => by simp only [erase]; split <;> trivial
  | .alt a b => ⟨erase_firstOrder E a,erase_firstOrder E b⟩
  | .eps | .any | .chr _ | .range _ _ | .call _ _ | .seq _ _ | .star _ | .notP _
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem select_firstOrder (E : List (List Char)) : ∀ a K, (∀ w, (K w).FirstOrder) → (select E a K).FirstOrder
  | .lit _, K, hK => ⟨trivial,hK _⟩
  | .param k, K, hK => by simp only [select]; split; exact ⟨trivial,hK _⟩; trivial
  | .alt a b, K, hK => by
    have ha := select_firstOrder E a K hK
    have hb := select_firstOrder E b K hK
    have hg := erase_firstOrder E a
    exact ⟨⟨hg,ha⟩,hg,hb⟩
  | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .call _ _, _, _
  | .seq _ _, _, _ | .star _, _, _ | .notP _, _, _ | .dbg _, _, _ | .lam _ _, _, _
  | .callParam _ _, _, _ | .invoke _ _ _, _, _ => trivial

theorem selectArgs_firstOrder (E : List (List Char)) :
    ∀ args K, (∀ W, (K W).FirstOrder) → (selectArgs E args K).FirstOrder
  | [], _, hK => hK []
  | a::args, _, hK => select_firstOrder E a _ (fun w => selectArgs_firstOrder E args _ (fun W => hK (w::W)))

theorem arg_firstOrder {V : List (List Char)} : ∀ a, Arg V a → a.FirstOrder
  | .lit _, _ | .param _, _ => trivial
  | .alt a b, h => ⟨arg_firstOrder a h.1,arg_firstOrder b h.2⟩
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .seq _ _, h
  | .star _, h | .notP _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem args_firstOrder {V : List (List Char)} {args : List MExp} (h : ∀ a ∈ args, Arg V a) :
    MExp.FirstOrderArgs args := by
  induction args with
  | nil => trivial
  | cons a args ih => exact ⟨arg_firstOrder a (h a (by simp)),ih (fun b hb => h b (by simp [hb]))⟩

theorem supported_firstOrder {V : List (List Char)} : ∀ e, Supported V e → e.FirstOrder
  | .call _ _, h => args_firstOrder h
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder a h.1,supported_firstOrder b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem erase_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) {V : List (List Char)} :
    ∀ a, Arg V a → ∀ p, evV g x s T E a p = evV h x t U [] (erase E a) p
  | .lit _, _, _ => rfl
  | .param k, _, p => by cases hh : E[k]? <;> simp [erase,evV,hh,MExp.failAlways]
  | .alt a b, ha, p => by
    simp only [erase,evV]
    rw [← erase_eval g h x s t T U E a ha.1 p,← erase_eval g h x s t T U E b ha.2 p]
  | .eps, ha, _ | .any, ha, _ | .chr _, ha, _ | .range _ _, ha, _ | .call _ _, ha, _
  | .seq _ _, ha, _ | .star _, ha, _ | .notP _, ha, _ | .dbg _, ha, _ | .lam _ _, ha, _
  | .callParam _ _, ha, _ | .invoke _ _ _, ha, _ => False.elim ha

/-- A successful argument commits the continuation even when that
continuation fails or has no finite result. -/
theorem branch_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a yes no : MExp) (p : Nat) :
    evV g x s T E (RootObservation.branch (.andP a) yes no) p =
      match evV g x s T E a p with
      | none => none | some none => evV g x s T E no p | some (some _) => evV g x s T E yes p := by
  cases ha : evV g x s T E a p with
  | none => simp [RootObservation.branch,MExp.andP,evV,ha]
  | some r =>
    cases r with
    | none => simp [RootObservation.branch,MExp.andP,evV,ha]
    | some q =>
      cases hy : evV g x s T E yes p with
      | none => simp [RootObservation.branch,MExp.andP,evV,ha,hy]
      | some r => cases r <;> simp [RootObservation.branch,MExp.andP,evV,ha,hy]

private theorem literal_select (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (w : List Char)
    (K : List Char → MExp) (p : Nat) (hp : p ≤ x.length) :
    evV h x t U [] (.seq (.andP (.lit w)) (K w)) p =
      match evV g x s T E (.lit w) p with
      | some (some q) => evV h x t U [] (K (pre x p q)) p | r => r := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [MExp.andP,evV,hs]
  | some rest =>
    have he : pre x p rest.length = w := by
      have hh := pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact w _ _).mp hs)
      simpa only [length_sfx x hp] using hh
    simp [MExp.andP,evV,hs,he]

theorem select_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) {V : List (List Char)}
    (p : Nat) (hp : p ≤ x.length) :
    ∀ a, Arg V a → ∀ K,
      evV h x t U [] (select E a K) p =
        match evV g x s T E a p with
        | some (some q) => evV h x t U [] (K (pre x p q)) p | r => r
  | .lit w, _, K => literal_select g h x s t T U E w K p hp
  | .param k, _, K => by
    cases hh : E[k]? with
    | none => simp [select,evV,hh,MExp.failAlways]
    | some w => simpa only [select,hh,evV] using literal_select g h x s t T U E w K p hp
  | .alt a b, ha, K => by
    rw [select,branch_eval,← erase_eval g h x s t T U E a ha.1 p]
    cases hv : evV g x s T E a p with
    | none => simp [evV,hv]
    | some r =>
      cases r with
      | none => simpa only [evV,hv] using select_eval g h x s t T U E p hp b ha.2 K
      | some q => simpa only [evV,hv] using select_eval g h x s t T U E p hp a ha.1 K
  | .eps, ha, _ | .any, ha, _ | .chr _, ha, _ | .range _ _, ha, _ | .call _ _, ha, _
  | .seq _ _, ha, _ | .star _, ha, _ | .notP _, ha, _ | .dbg _, ha, _ | .lam _ _, ha, _
  | .callParam _ _, ha, _ | .invoke _ _ _, ha, _ => False.elim ha

theorem selectArgs_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) {V : List (List Char)}
    (p : Nat) (hp : p ≤ x.length) :
    ∀ args, (∀ a ∈ args, Arg V a) → ∀ K,
      evV h x t U [] (selectArgs E args K) p =
        match evParArgs g x s T E args p with
        | some (some W) => evV h x t U [] (K W) p | none => none | some none => some none
  | [], _, _ => rfl
  | a::args, ha, K => by
    rw [selectArgs,select_eval g h x s t T U E p hp a (ha a (by simp))]
    simp only [evParArgs]
    cases hv : evV g x s T E a p with
    | none => rfl
    | some r =>
      cases r with
      | none => rfl
      | some q =>
        dsimp only
        rw [selectArgs_eval g h x s t T U E p hp args (fun b hb => ha b (by simp [hb]))]
        cases evParArgs g x s T E args p with
        | none => rfl
        | some r => cases r <;> rfl

private theorem literal_value (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (w : List Char)
    (p q : Nat) (hp : p ≤ x.length) (hv : evV g x s T E (.lit w) p = some (some q)) :
    pre x p q = w := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at hv
  | some rest =>
    have hq : rest.length=q := by simpa [evV,hs] using hv
    rw [← hq]
    have he := pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact w _ _).mp hs)
    simpa only [length_sfx x hp] using he

theorem success_value {V E : List (List Char)} (hE : ∀ w ∈ E, w ∈ V)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (p : Nat) (hp : p ≤ x.length) :
    ∀ a, Arg V a → ∀ q, evV g x s T E a p = some (some q) → pre x p q ∈ V
  | .lit w, hw, q, hv => by
    rw [literal_value g x s T E w p q hp hv]
    exact hw
  | .param k, _, q, hv => by
    cases hh : E[k]? with
    | none => simp [evV,hh] at hv
    | some w =>
      have hl : evV g x s T E (.lit w) p = some (some q) := by simpa only [evV,hh] using hv
      rw [literal_value g x s T E w p q hp hl]
      exact hE w (List.mem_of_getElem? hh)
  | .alt a b, ha, q, hv => by
    cases hh : evV g x s T E a p with
    | none => simp [evV,hh] at hv
    | some r =>
      cases r with
      | none => exact success_value hE g x s T p hp b ha.2 q (by simpa only [evV,hh] using hv)
      | some j =>
        have hq : j=q := by simpa only [evV,hh,Option.some.injEq] using hv
        exact success_value hE g x s T p hp a ha.1 q (by simpa only [hq] using hh)
  | .eps, ha, _, _ | .any, ha, _, _ | .chr _, ha, _, _ | .range _ _, ha, _, _ | .call _ _, ha, _, _
  | .seq _ _, ha, _, _ | .star _, ha, _, _ | .notP _, ha, _, _ | .dbg _, ha, _, _ | .lam _ _, ha, _, _
  | .callParam _ _, ha, _, _ | .invoke _ _ _, ha, _, _ => False.elim ha

theorem arguments_bounds {V E : List (List Char)} (hE : ∀ w ∈ E, w ∈ V)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (p : Nat) (hp : p ≤ x.length) :
    ∀ args, (∀ a ∈ args, Arg V a) → ∀ W, evParArgs g x s T E args p = some (some W) →
      W.length=args.length ∧ ∀ w ∈ W, w ∈ V
  | [], _, W, hw => by simp [evParArgs] at hw; subst W; simp
  | a::args, ha, W, hw => by
    cases hh : evV g x s T E a p with
    | none => simp [evParArgs,hh] at hw
    | some r =>
      cases r with
      | none => simp [evParArgs,hh] at hw
      | some q =>
        cases ht : evParArgs g x s T E args p with
        | none => simp [evParArgs,hh,ht] at hw
        | some r =>
          cases r with
          | none => simp [evParArgs,hh,ht] at hw
          | some ws =>
            have he : W=pre x p q::ws := by simpa [evParArgs,hh,ht] using hw.symm
            subst W
            have hb := arguments_bounds hE g x s T p hp args (fun b hb => ha b (by simp [hb])) ws ht
            have hv := success_value hE g x s T p hp a (ha a (by simp)) q hh
            exact ⟨by simp [hb.1],by intro w hm; rcases List.mem_cons.mp hm with rfl | hm; exact hv; exact hb.2 w hm⟩

/-- Plain distribution retries a different captured value after continuation
failure. On the same input, the committed selection fails but the naive
alternative accepts the whole word. -/
theorem plain_distribution_changes_result :
    let g : MGrammar := ⟨[]⟩
    let T : Nat → List (List Char) → Val := fun _ _ => []
    let a := MExp.lit ['a']
    let b := MExp.lit ['a','b']
    let K := fun w : List Char => if w=['a'] then MExp.failAlways else b
    evV g ['a','b'] .callByValueSeq T [] (select [] (.alt a b) K) 2 = some none ∧
      evV g ['a','b'] .callByValueSeq T [] (.alt (select [] a K) (select [] b K)) 2 = some (some 0) := by
  constructor <;> rfl

end Shallot.MacroPeg.CBV.ChoiceArguments
