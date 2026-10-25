import MacroPeg.CBV.FiniteSuffixObservedDeclarations

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedAtoms
open FiniteSuffixObservedSyntax
open RegularCaptureProduct (run filtered)
open ExactWordCaptureMachine (machine)
open ClockFreezing (Table)

def project (m : Mode) (x : List Char) (p : Nat) (v : Res) : Res := match m with
  | none => v
  | some (u,q,r) => filtered (machine u) x q r p v

theorem atom_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (m : Mode) (e : MExp) (w : List Char) (p : Nat)
    (hw : ∀ j, evV g x s T E e p=some (some j) → pre x p j=w) :
    evV g x s T E (atom m e w) p=project m x p (evV g x s T E e p) := by
  cases m with
  | none => rfl
  | some v =>
    rcases v with ⟨u,q,r⟩
    simpa only [atom,project,Option.some.injEq] using
      DependentCaptureFilter.atom_correct g x s T (machine u) E e q r p (some (run (machine u) q w))
        (by intro j hj; rw [hw j hj])

theorem pre_character (x : List Char) (p : Nat) (hp : p≤x.length) (c : Char) (rest : List Char)
    (hx : sfx x p=c::rest) : pre x p rest.length=[c] := by
  have hl := length_sfx x hp
  rw [hx,List.length_cons] at hl
  unfold pre
  rw [hx]
  simp [←hl]

theorem beq_char_iff (a b : Char) : Shallot.beqChar a b=true ↔ a=b := by
  simp [Shallot.beqChar,Char.toNat_inj]

theorem charFilter_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (u : List Char) (q r p : Nat) (hp : p≤x.length) :
    evV g x s T E (charFilter u q r) p=filtered (machine u) x q r p (evV g x s T E .any p) := by
  by_cases hq : q<u.length
  · rw [charFilter,if_pos hq,ChoiceArguments.branch_eval]
    have hg : u[q]?.getD '\x00'=u[q] := by simp [List.getElem?_eq_getElem hq]
    rw [hg]
    cases hx : sfx x p with
    | nil =>
        simp only [evV,hx,filtered]
        split <;> simp [evV,hx,MExp.failAlways]
    | cons c rest =>
      have hpref := pre_character x p hp c rest hx
      by_cases he : u[q]=c
      · have hbe : Shallot.beqChar u[q] c=true := (beq_char_iff _ _).mpr he
        have hs : ExactWordCaptureMachine.step u q c=q+1 := by simp [ExactWordCaptureMachine.step,hq,List.getElem?_eq_getElem hq,he]
        simp only [evV,hx,hbe,if_true]
        by_cases hh : q+1=r <;> simp [hh,evV,hx,filtered,hpref,run,machine,hs,MExp.failAlways]
      · have hbe : Shallot.beqChar u[q] c=false := Bool.eq_false_iff.mpr (fun h => he ((beq_char_iff _ _).mp h))
        have hs : ExactWordCaptureMachine.step u q c=u.length+1 := by simp [ExactWordCaptureMachine.step,hq,List.getElem?_eq_getElem hq,he]
        simp only [evV,hx,hbe,Bool.false_eq_true,if_false]
        by_cases hh : u.length+1=r <;> simp [hh,evV,hx,filtered,hpref,run,machine,hs,MExp.failAlways]
  · rw [charFilter,if_neg hq]
    have hs (c : Char) : ExactWordCaptureMachine.step u q c=u.length+1 := by simp [ExactWordCaptureMachine.step,hq]
    cases hx : sfx x p with
    | nil => split <;> simp [evV,hx,filtered,MExp.failAlways]
    | cons c rest =>
      have hpref := pre_character x p hp c rest hx
      by_cases hh : u.length+1=r <;> simp [hh,evV,hx,filtered,hpref,run,machine,hs,MExp.failAlways]

/-- A one-character source atom gates the DFA step, including characters
outside every candidate word. No alphabet restriction or Char enumeration. -/
theorem character_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (m : Mode) (e : MExp) (p : Nat) (hp : p≤x.length)
    (he : e=.any ∨ (∃ c, e=.chr c) ∨ (∃ a b, e=.range a b)) :
    evV g x s T E (character m e) p=project m x p (evV g x s T E e p) := by
  cases m with
  | none => rfl
  | some v =>
    rcases v with ⟨u,q,r⟩
    change (match evV g x s T E (.andP e) p with
      | some (some j) => evV g x s T E (charFilter u q r) j | other => other)=_
    rw [CallLookahead.evV_peek]
    have hAny : ∀ j, evV g x s T E e p=some (some j) → evV g x s T E .any p=some (some j) := by
      intro j hj
      rcases he with rfl | ⟨c,rfl⟩ | ⟨a,b,rfl⟩
      · exact hj
      · cases hx : sfx x p with
        | nil => simp [evV,hx] at hj
        | cons d rest =>
          simp only [evV,hx] at hj ⊢
          split at hj
          · exact hj
          · cases hj
      · cases hx : sfx x p with
        | nil => simp [evV,hx] at hj
        | cons d rest =>
          simp only [evV,hx] at hj ⊢
          split at hj
          · exact hj
          · cases hj
    cases hv : evV g x s T E e p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some j =>
        dsimp only [CallLookahead.peek]
        rw [charFilter_correct g x s T E u q r p hp,hAny j hv]
        rfl


theorem replay_word (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (R : List (List Char)) (V : View) (i p : Nat) (hp : p≤x.length) (j : Nat)
    (hv : evV g x s T [] (.seq (FiniteSuffixReplay.guard R) (FiniteSuffixReplay.literal V i)) p=some (some j)) :
    pre x p j=V[i]?.join.getD [] := by
  have hg := FiniteSuffixReplay.guard_eval g x s T [] R p hp
  by_cases hm : sfx x p∈R
  · rw [if_pos hm] at hg
    rw [evV_seq_ok hg] at hv
    cases hw : V[i]?.join with
    | none => simp [FiniteSuffixReplay.literal,hw,MExp.failAlways,evV] at hv
    | some w =>
      have hh : evV g x s T [] (.lit w) p=some (some j) := by simpa only [FiniteSuffixReplay.literal,hw] using hv
      have he := WordArguments.value_of_success g x s T [] (.lit w) True.intro p j hp hh
      simpa [WordArguments.value,hw] using (Option.some.inj he).symm
  · rw [if_neg hm] at hg
    rw [evV_seq_fail hg] at hv
    cases hv

theorem not_word (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (e : MExp) (p j : Nat) (hv : evV g x s T [] (.notP e) p=some (some j)) : pre x p j=[] := by
  cases hh : evV g x s T [] e p with
  | none => simp [evV,hh] at hv
  | some v => cases v with
    | none => have he : p=j := by simpa [evV,hh] using hv
              simp [pre,he]
    | some q => simp [evV,hh] at hv

end Shallot.MacroPeg.CBV.FiniteSuffixObservedAtoms
