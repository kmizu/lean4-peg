import MacroPeg.CBV.SequenceArguments

/-! A finite syntactic capture domain for composite arguments. Concatenation
must remain inside the supplied input-independent palette. -/
namespace Shallot.MacroPeg.CBV.SequenceArgumentDomain
open SequenceArguments

def possible (V : List (List Char)) : MExp → List (List Char)
  | .lit w => [w]
  | .param _ => V
  | .alt a b => possible V a ++ possible V b
  | .seq a b => (possible V a).flatMap (fun u => (possible V b).map (fun v => u++v))
  | _ => []

def Closed (V : List (List Char)) (a : MExp) : Prop := Arg a ∧ ∀ w ∈ possible V a, w ∈ V

def Supported (V : List (List Char)) : MExp → Prop
  | .call _ args => ∀ a ∈ args, Closed V a
  | .seq a b | .alt a b => Supported V a ∧ Supported V b
  | .star a | .notP a => Supported V a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

theorem args_firstOrder {V : List (List Char)} {args : List MExp} (h : ∀ a ∈ args, Closed V a) :
    MExp.FirstOrderArgs args := by
  induction args with
  | nil => trivial
  | cons a args ih => exact ⟨arg_firstOrder a (h a (by simp)).1,ih (fun b hb => h b (by simp [hb]))⟩

theorem supported_firstOrder {V : List (List Char)} : ∀ e, Supported V e → e.FirstOrder
  | .call _ _, h => args_firstOrder h
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder a h.1,supported_firstOrder b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

private theorem literal_word (g : MGrammar) (x : List Char) (s : Strategy)
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

theorem success_possible {V E : List (List Char)} (hE : ∀ w ∈ E, w ∈ V)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) :
    ∀ a, Arg a → ∀ p q, p ≤ x.length → evV g x s T E a p = some (some q) → pre x p q ∈ possible V a
  | .lit w, _, p, q, hp, hv => by rw [literal_word g x s T E w p q hp hv]; simp [possible]
  | .param k, _, p, q, hp, hv => by
    cases hh : E[k]? with
    | none => simp [evV,hh] at hv
    | some w =>
      have hl : evV g x s T E (.lit w) p = some (some q) := by simpa only [evV,hh] using hv
      rw [literal_word g x s T E w p q hp hl]
      exact hE w (List.mem_of_getElem? hh)
  | .alt a b, ha, p, q, hp, hv => by
    cases hh : evV g x s T E a p with
    | none => simp [evV,hh] at hv
    | some r =>
      cases r with
      | none => exact List.mem_append_right _ (success_possible hE g x s T b ha.2 p q hp (by simpa only [evV,hh] using hv))
      | some j =>
        have hq : j=q := by simpa only [evV,hh,Option.some.injEq] using hv
        exact List.mem_append_left _ (success_possible hE g x s T a ha.1 p q hp (by simpa only [hq] using hh))
  | .seq a b, ha, p, q, hp, hv => by
    cases hh : evV g x s T E a p with
    | none => simp [evV,hh] at hv
    | some r =>
      cases r with
      | none => simp [evV,hh] at hv
      | some j =>
        have hb : evV g x s T E b j = some (some q) := by simpa only [evV,hh] using hv
        obtain ⟨hj,hpre⟩ := success_prefix g x s T E a ha.1 p j hp hh
        obtain ⟨hq,hpost⟩ := success_prefix g x s T E b ha.2 j q hj hb
        rw [pre_concat hp hq hpre hpost]
        exact List.mem_flatMap.mpr ⟨pre x p j,success_possible hE g x s T a ha.1 p j hp hh,
          List.mem_map.mpr ⟨pre x j q,success_possible hE g x s T b ha.2 j q hj hb,rfl⟩⟩
  | .eps, ha, _, _, _, _ | .any, ha, _, _, _, _ | .chr _, ha, _, _, _, _ | .range _ _, ha, _, _, _, _
  | .call _ _, ha, _, _, _, _ | .star _, ha, _, _, _, _ | .notP _, ha, _, _, _, _ | .dbg _, ha, _, _, _, _
  | .lam _ _, ha, _, _, _, _ | .callParam _ _, ha, _, _, _, _ | .invoke _ _ _, ha, _, _, _, _ => False.elim ha

theorem arguments_bounds {V E : List (List Char)} (hE : ∀ w ∈ E, w ∈ V)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (p : Nat) (hp : p ≤ x.length) :
    ∀ args, (∀ a ∈ args, Closed V a) → ∀ W, evParArgs g x s T E args p = some (some W) →
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
            have hc := ha a (by simp)
            have hv := hc.2 _ (success_possible hE g x s T a hc.1 p q hp hh)
            exact ⟨by simp [hb.1],by intro w hm; rcases List.mem_cons.mp hm with rfl | hm; exact hv; exact hb.2 w hm⟩

def argB : MExp → Bool
  | .lit _ | .param _ => true
  | .seq a b | .alt a b => argB a && argB b
  | _ => false

theorem argB_iff : ∀ a, argB a = true ↔ Arg a
  | .lit _ | .param _ => by simp [argB,Arg]
  | .seq a b | .alt a b => by simp [argB,Arg,argB_iff a,argB_iff b]
  | .eps | .any | .chr _ | .range _ _ | .call _ _ | .star _ | .notP _
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => by simp [argB,Arg]

def closedB (V : List (List Char)) (a : MExp) : Bool :=
  argB a && (possible V a).all (fun w => decide (w ∈ V))

theorem closedB_iff (V : List (List Char)) (a : MExp) : closedB V a = true ↔ Closed V a := by
  simp [closedB,Closed,argB_iff,List.all_eq_true]

def supportedB (V : List (List Char)) : MExp → Bool
  | .call _ args => args.all (closedB V)
  | .seq a b | .alt a b => supportedB V a && supportedB V b
  | .star a | .notP a => supportedB V a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => true
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => false

theorem supportedB_iff (V : List (List Char)) : ∀ e, supportedB V e = true ↔ Supported V e
  | .call _ args => by simp [supportedB,Supported,List.all_eq_true,closedB_iff]
  | .seq a b | .alt a b => by simp [supportedB,Supported,supportedB_iff V a,supportedB_iff V b]
  | .star a | .notP a => supportedB_iff V a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => by simp [supportedB,Supported]
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => by simp [supportedB,Supported]

private theorem length_le_sum {V : List (List Char)} {w : List Char} (hw : w ∈ V) :
    w.length ≤ (V.map List.length).sum := by
  induction V with
  | nil => cases hw
  | cons v V ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · simp <;> omega
    · have hh := ih hw
      simp; omega

/-- Finite palette closure is a real restriction: allowing every current
value to be duplicated cannot remain closed around a nonempty captured word.
This concerns the syntactic palette check, not a language-class separation. -/
theorem no_nonempty_palette_for_duplication {V : List (List Char)} {w : List Char}
    (hw : w ∈ V) (hne : w ≠ []) : ¬ Closed V (.seq (.param 0) (.param 0)) := by
  intro hc
  have hcat : ∀ u ∈ V, ∀ v ∈ V, u++v ∈ V := by
    intro u hu v hv
    exact hc.2 _ (List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩)
  have hCopies : ∀ n, (List.replicate (n+1) w).flatten ∈ V := by
    intro n
    induction n with
    | zero => simpa using hw
    | succ n ih => simpa [List.replicate_succ] using hcat w hw _ ih
  let B := (V.map List.length).sum
  have hh := length_le_sum (hCopies B)
  have hlen : (List.replicate (B+1) w).flatten.length = (B+1)*w.length := by simp
  rw [hlen] at hh
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hne
  have hm := Nat.le_mul_of_pos_right (B+1) hwpos
  omega

/-- A fixed concatenation can pass even though general duplication cannot. -/
theorem concrete_concatenation_checked :
    closedB [['a','b']] (.seq (.lit ['a']) (.lit ['b'])) = true := by rfl

end Shallot.MacroPeg.CBV.SequenceArgumentDomain
