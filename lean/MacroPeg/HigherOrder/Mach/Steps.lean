import MacroPeg.HigherOrder.Mach.ReadAll

/-!
# The reading machine stops within `4 n + 1` steps

A potential: four per remaining token, plus a weight per pending control frame (`ctlPot`, the two arguments of a
frame `9` counted with it). Every step either stops the machine (empties the control stack) or lowers the potential
(`pstep_pot`); so after `pot s + 1` steps the machine has stopped (`pruns_stops`), from the start within
`4 n + 1` steps (`pinit_stops`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.Flat

/-- The weight of a pending control frame: what is left to do beyond reading tokens. -/
def frameW : Nat → Nat
  | 2 => 2 | 3 => 1 | 4 => 2 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 2 | 10 => 2 | 11 => 1 | 12 => 2 | 13 => 1
  | 15 => 1 | 17 => 1 | 18 => 1
  | _ => 0

/-- The weight of a control stack; a frame `9` carries two numbers. -/
def ctlPot : List Nat → Nat
  | 9 :: _ :: _ :: K => 1 + ctlPot K
  | k :: K => frameW k + ctlPot K
  | [] => 0

/-- The potential of a state. -/
def pot (s : PSt) : Nat := 4 * s.tk.length + ctlPot s.ctl

theorem ctlPot_cons (k : Nat) (K : List Nat) (hk : k ≠ 9) : ctlPot (k :: K) = frameW k + ctlPot K := by
  match K with
  | [] => simp [ctlPot]
  | [a] => simp [ctlPot]
  | a :: b :: K' => simp [ctlPot, hk]

/-- What a step does: stop, or lower the potential. -/
def Lowers (s : PSt) : Prop := (pstep s).ctl = [] ∨ pot (pstep s) < pot s

theorem lowers_fail {s : PSt} (h : pstep s = s.fail) : Lowers s := .inl (by rw [h]; rfl)

/-- A step that consumed a token and pushed frames of weight at most `2` lowers the potential. -/
theorem lowers_arith {n m c d : Nat} (hm : m < n) (hd : d ≤ c + 2) : 4 * m + d < 4 * n + c := by omega

theorem readExpr_lowers (s : PSt) (K : List Nat) :
    (readExpr s K).ctl = [] ∨
      4 * (readExpr s K).tk.length + ctlPot (readExpr s K).ctl < 4 * s.tk.length + ctlPot K := by
  unfold readExpr
  split
  next r h => exact .inr (lowers_arith (by simp [PSt.leaf, h]) (by simp [PSt.leaf]))
  next r h => exact .inr (lowers_arith (by simp [PSt.leaf, h]) (by simp [PSt.leaf]))
  next r h =>
    split
    next c r₁ hc =>
      have := parseChar_shorter hc
      exact .inr (lowers_arith (by simp [PSt.leaf, h]; omega) (by simp [PSt.leaf]))
    next => exact .inl rfl
  next r h =>
    split
    next lo r₁ h₁ =>
      split
      next hi r₂ h₂ =>
        have := parseChar_shorter h₁; have := parseChar_shorter h₂
        exact .inr (lowers_arith (by simp [PSt.leaf, h]; omega) (by simp [PSt.leaf]))
      next => exact .inl rfl
    next => exact .inl rfl
  next r h =>
    split
    next str r₁ h₁ =>
      have := parseStr_shorter h₁
      exact .inr (lowers_arith (by simp [PSt.leaf, h]; omega) (by simp [PSt.leaf]))
    next => exact .inl rfl
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next r h =>
    split
    next i r₁ h₁ =>
      split
      next τ _ =>
        have := parseNat_shorter h₁
        exact .inr (lowers_arith (by simp [PSt.leaf, h]; omega) (by simp [PSt.leaf]))
      next => exact .inl rfl
    next => exact .inl rfl
  next r h =>
    split
    next i r₁ h₁ =>
      split
      next τ _ =>
        have := parseNat_shorter h₁
        exact .inr (lowers_arith (by simp [PSt.leaf, h]; omega) (by simp [PSt.leaf]))
      next => exact .inl rfl
    next => exact .inl rfl
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next => exact .inl rfl

theorem readType_lowers (s : PSt) (K : List Nat) :
    (readType s K).ctl = [] ∨
      4 * (readType s K).tk.length + ctlPot (readType s K).ctl < 4 * s.tk.length + ctlPot K := by
  unfold readType
  split
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp))
  next r h => exact .inr (lowers_arith (by simp [h]) (by simp [ctlPot_cons, frameW]; omega))
  next => exact .inl rfl

/-- A step that pops a frame of weight `w` and pushes frames of weight less than `w`, without reading. -/
theorem lowers_pop {s s' : PSt} {k : Nat} {K : List Nat} (hc : s.ctl = k :: K) (hk : k ≠ 9) (htk : s'.tk = s.tk)
    (hw : ctlPot s'.ctl < frameW k + ctlPot K) : pot s' < pot s := by
  simp only [pot, hc, ctlPot_cons k K hk, htk]; omega

theorem pstep_lowers (s : PSt) (h : s.ctl ≠ []) : Lowers s := by
  unfold Lowers
  unfold pstep
  split
  next hc => exact absurd hc h
  next K hc =>
    rcases readExpr_lowers s K with h' | h'
    · exact .inl h'
    · right; simp only [pot, hc, ctlPot_cons 0 K (by decide), frameW]; omega
  next K hc =>
    rcases readType_lowers s K with h' | h'
    · exact .inl h'
    · right; simp only [pot, hc, ctlPot_cons 1 K (by decide), frameW]; omega
  next K hc =>
    split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot_cons, frameW]))
    · exact .inl rfl
  next K hc =>
    unfold binDone; split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [frameW]))
    · exact .inl rfl
  next K hc =>
    split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot_cons, frameW]))
    · exact .inl rfl
  next K hc =>
    unfold binDone; split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [frameW]))
    · exact .inl rfl
  next K hc =>
    unfold unDone; split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [frameW]))
    · exact .inl rfl
  next K hc =>
    unfold unDone; split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [frameW]))
    · exact .inl rfl
  next K hc =>
    split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot, frameW]))
    · exact .inl rfl
  next a c K hc =>
    split
    · right; simp only [pot, hc, ctlPot]; omega
    · exact .inl rfl
  next K hc => exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot_cons, frameW]))
  next K hc =>
    repeat' split
    all_goals first
      | exact .inl rfl
      | exact .inr (lowers_pop hc (by decide) rfl (by simp [frameW]))
  next K hc => exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot_cons, frameW]))
  next K hc =>
    split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [frameW]))
    · exact .inl rfl
  next K hc =>
    split
    next r htk => right; simp only [pot, hc, htk, ctlPot_cons 14 K (by decide), ctlPot_cons 16 K (by decide),
      frameW, List.length_cons]; omega
    next r htk => right; simp only [pot, hc, htk, ctlPot_cons 14 K (by decide), ctlPot_cons 1 _ (by decide),
      ctlPot_cons 15 K (by decide), frameW, List.length_cons]; omega
    next => exact .inl rfl
  next K hc =>
    split
    · exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot_cons, frameW]))
    · exact .inl rfl
  next K hc =>
    split
    next r htk =>
      split
      · right; simp only [pot, hc, htk, ctlPot_cons 16 K (by decide), ctlPot_cons 0 _ (by decide),
          ctlPot_cons 18 K (by decide), frameW, List.length_cons]; omega
      · exact .inl rfl
    next r htk => right; simp only [pot, hc, htk, ctlPot_cons 16 K (by decide), ctlPot_cons 0 _ (by decide),
      ctlPot_cons 17 K (by decide), frameW, List.length_cons]; omega
    next => exact .inl rfl
  next K hc =>
    repeat' split
    all_goals first
      | exact .inl rfl
      | exact .inr (lowers_pop hc (by decide) rfl (by simp [ctlPot_cons, frameW]))
  next K hc =>
    repeat' split
    all_goals first
      | exact .inl rfl
      | (right; simp only [pot, hc, ctlPot_cons 18 K (by decide), frameW, List.length_cons]; omega)
  next => exact .inl rfl

/-- After `pot s + 1` steps the machine has stopped. -/
theorem pruns_stops : ∀ (n : Nat) (s : PSt), pot s + 1 ≤ n → (pruns s n).ctl = []
  | 0, _, h => absurd h (by omega)
  | n + 1, s, h => by
    rw [pruns_succ]
    by_cases hc : s.ctl = []
    · rw [pstep_halted hc, pruns_halted hc]; exact hc
    · rcases pstep_lowers s hc with h' | h'
      · rw [pruns_halted h']; exact h'
      · exact pruns_stops n (pstep s) (by omega)

/-- From the start, the machine stops within `4 n + 1` steps. -/
theorem pinit_stops (tk : List Nat) : (pruns (pinit tk) (4 * tk.length + 1)).ctl = [] :=
  pruns_stops _ _ (by simp [pot, pinit, ctlPot, frameW])

end Shallot.MacroPeg.Mach
