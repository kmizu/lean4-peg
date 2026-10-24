import MacroPeg.CBV.LiteralArguments

/-! Finite auxiliary values are separated from one runtime captured word.
Parameter zero remains dynamic; positive parameters address the finite flags. -/
namespace Shallot.MacroPeg.CBV.HybridFlags

def Flag (V : List (List Char)) : MExp → Prop
  | .lit w => w ∈ V
  | .param (_+1) => True
  | _ => False

def lower : MExp → MExp
  | .lit w => .lit w
  | .param (k+1) => .param k
  | _ => MExp.failAlways

def lowerArgs (args : List MExp) : List MExp := args.map lower

def resolve (F : List (List Char)) (args : List MExp) : Option (List (List Char)) :=
  LiteralArguments.resolveArgs F (lowerArgs args)

def Head (H F : List (List Char)) : Prop := H.length ≤ 1 ∧ (H=[] → F=[])

theorem lower_supported {V : List (List Char)} {args : List MExp} (h : ∀ a ∈ args, Flag V a) :
    ∀ a ∈ lowerArgs args, LiteralArguments.Arg V a := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have hh := h b hb
  cases b with
  | lit w => exact hh
  | param k => cases k; exact False.elim hh; trivial
  | _ => exact False.elim hh

theorem flag_firstOrder {V : List (List Char)} {a : MExp} (h : Flag V a) : a.FirstOrder := by
  cases a <;> first | trivial | exact False.elim h

theorem args_firstOrder {V : List (List Char)} {args : List MExp} (h : ∀ a ∈ args, Flag V a) :
    MExp.FirstOrderArgs args := by
  induction args with
  | nil => trivial
  | cons a args ih => exact ⟨flag_firstOrder (h a (by simp)),ih (fun b hb => h b (by simp [hb]))⟩

theorem flag_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) {V H F : List (List Char)} (hH : Head H F) :
    ∀ a, Flag V a → ∀ p, evV g x s T (H++F) a p = evV g x s T F (lower a) p
  | .lit _, _, _ => rfl
  | .param (k+1), _, p => by
    cases H with
    | nil => have hf := hH.2 rfl; subst F; simp [lower,evV]
    | cons w H =>
      have he : H=[] := List.eq_nil_of_length_eq_zero (by have hb := hH.1; change H.length+1 ≤ 1 at hb; omega)
      subst H
      simp [lower,evV]
  | .eps, h, _ | .any, h, _ | .chr _, h, _ | .range _ _, h, _ | .param 0, h, _
  | .call _ _, h, _ | .seq _ _, h, _ | .alt _ _, h, _ | .star _, h, _ | .notP _, h, _
  | .dbg _, h, _ | .lam _ _, h, _ | .callParam _ _, h, _ | .invoke _ _ _, h, _ => False.elim h

theorem args_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) {V H F : List (List Char)} (hH : Head H F) :
    ∀ args, (∀ a ∈ args, Flag V a) → ∀ p,
      evParArgs g x s T (H++F) args p = evParArgs g x s T F (lowerArgs args) p
  | [], _, _ => rfl
  | a::args, ha, p => by
    simp only [lowerArgs,List.map_cons,evParArgs]
    rw [flag_eval g x s T hH a (ha a (by simp)) p,
      args_eval g x s T hH args (fun b hb => ha b (by simp [hb])) p]
    rfl

theorem resolve_bounds {V F : List (List Char)} (hF : ∀ w ∈ F, w ∈ V)
    {args : List MExp} (ha : ∀ a ∈ args, Flag V a) {W : List (List Char)} (hw : resolve F args=some W) :
    W.length=args.length ∧ ∀ w ∈ W, w ∈ V := by
  have hh := LiteralArguments.resolveArgs_bounds hF (lowerArgs args) (lower_supported ha) W hw
  simpa [lowerArgs] using hh

end Shallot.MacroPeg.CBV.HybridFlags
