import MacroPeg.CBV.ReplayControlFusion

/-! Word-valued arguments have the same value at every successful position.
Concatenation can grow captured values without any fixed finite palette. -/
namespace Shallot.MacroPeg.CBV.WordArguments

def Word : MExp → Prop
  | .lit _ | .param _ => True
  | .seq a b => Word a ∧ Word b
  | _ => False

def value (E : List (List Char)) : MExp → Option (List Char)
  | .lit w => some w
  | .param k => E[k]?
  | .seq a b => (value E a).bind (fun u => (value E b).map (fun v => u++v))
  | _ => none

def literal : Option (List Char) → MExp
  | some w => .lit w
  | none => MExp.failAlways

theorem word_firstOrder : ∀ a, Word a → a.FirstOrder
  | .lit _, _ | .param _, _ => trivial
  | .seq a b, h => ⟨word_firstOrder a h.1,word_firstOrder b h.2⟩
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .alt _ _, h | .star _, h | .notP _, h
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem word_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) :
    ∀ a, Word a → ∀ p, evV g x s T E a p = evV g x s T [] (literal (value E a)) p
  | .lit _, _, _ => rfl
  | .param k, _, p => by cases hv : E[k]? <;> simp [value,literal,evV,hv,MExp.failAlways]
  | .seq a b, h, p => by
    change (match evV g x s T E a p with
      | some (some q) => evV g x s T E b q | other => other) = _
    rw [word_eval g x s T E a h.1 p]
    cases ha : value E a with
    | none => simp [value,ha,literal,MExp.failAlways,evV]
    | some u =>
      have hb (q : Nat) := word_eval g x s T E b h.2 q
      cases hv : value E b with
      | none =>
        simp only [value,ha,hv,Option.bind_some,Option.map_none,literal]
        simp only [hv] at hb
        cases hs : Shallot.stripPrefix? u (sfx x p) <;>
          simp [literal,evV,hs,MExp.failAlways,hb]
      | some v =>
        simp only [value,ha,hv,Option.bind_some,Option.map_some,literal]
        simp only [hv,literal] at hb
        have he := CaptureViews.sequence_literals g x s T [] u v p
        change (match evV g x s T [] (.lit u) p with
          | some (some q) => evV g x s T E b q | other => other) = _
        cases hs : Shallot.stripPrefix? u (sfx x p) <;>
          simpa only [evV,hs,hb] using he
  | .eps, h, _ | .any, h, _ | .chr _, h, _ | .range _ _, h, _ | .call _ _, h, _ | .alt _ _, h, _
  | .star _, h, _ | .notP _, h, _ | .dbg _, h, _ | .lam _ _, h, _ | .callParam _ _, h, _ | .invoke _ _ _, h, _ => False.elim h

theorem value_of_success (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (ha : Word a)
    (p q : Nat) (hp : p ≤ x.length) (he : evV g x s T E a p = some (some q)) :
    value E a = some (pre x p q) := by
  rw [word_eval g x s T E a ha p] at he
  cases hv : value E a with
  | none => simp [literal,hv,MExp.failAlways,evV] at he
  | some w =>
    cases hs : Shallot.stripPrefix? w (sfx x p) with
    | none => simp [literal,hv,evV,hs] at he
    | some rest =>
      have hq : rest.length=q := by simpa [literal,hv,evV,hs] using he
      have hw := pre_eq (sfx_is_suffix x p) ((CBVtoCBN.stripPrefix_exact w _ _).mp hs)
      rw [length_sfx x hp,hq] at hw
      exact congrArg some hw.symm


theorem duplication (w : List Char) :
    Word (.seq (.param 0) (.param 0)) ∧ value [w] (.seq (.param 0) (.param 0)) = some (w++w) := by
  simp [Word,value]

end Shallot.MacroPeg.CBV.WordArguments
