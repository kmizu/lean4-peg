import MacroPeg.CBV.ChoiceArguments
import MacroPeg.CBV.CallLookahead

/-! Select a composite captured word while retaining the caller's position.
A known prefix is replayed only inside lookahead before inspecting the next part. -/
namespace Shallot.MacroPeg.CBV.SequenceArguments

def Arg : MExp → Prop
  | .lit _ | .param _ => True
  | .seq a b | .alt a b => Arg a ∧ Arg b
  | _ => False

def erase (E : List (List Char)) : MExp → MExp
  | .lit w => .lit w
  | .param k => match E[k]? with | some w => .lit w | none => MExp.failAlways
  | .seq a b => .seq (erase E a) (erase E b)
  | .alt a b => .alt (erase E a) (erase E b)
  | _ => MExp.failAlways

def selectAt (E : List (List Char)) (before : List Char) (a : MExp) (K : List Char → MExp) : MExp := match a with
  | .lit w => .seq (.andP (.seq (.lit before) (.lit w))) (K w)
  | .param k => match E[k]? with
    | some w => .seq (.andP (.seq (.lit before) (.lit w))) (K w)
    | none => MExp.failAlways
  | .alt a b => RootObservation.branch (.andP (.seq (.lit before) (erase E a)))
      (selectAt E before a K) (selectAt E before b K)
  | .seq a b => selectAt E before a (fun u => selectAt E (before++u) b (fun v => K (u++v)))
  | _ => MExp.failAlways

def select (E : List (List Char)) (a : MExp) (K : List Char → MExp) : MExp := selectAt E [] a K

def selectArgs (E : List (List Char)) : List MExp → (List (List Char) → MExp) → MExp
  | [], K => K []
  | a::args, K => select E a (fun w => selectArgs E args (fun W => K (w::W)))

theorem arg_firstOrder : ∀ a, Arg a → a.FirstOrder
  | .lit _, _ | .param _, _ => trivial
  | .seq a b, h | .alt a b, h => ⟨arg_firstOrder a h.1,arg_firstOrder b h.2⟩
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .star _, h | .notP _, h
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem erase_firstOrder (E : List (List Char)) : ∀ a, (erase E a).FirstOrder
  | .lit _ => trivial
  | .param k => by simp only [erase]; split <;> trivial
  | .seq a b | .alt a b => ⟨erase_firstOrder E a,erase_firstOrder E b⟩
  | .eps | .any | .chr _ | .range _ _ | .call _ _ | .star _ | .notP _
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem selectAt_firstOrder (E : List (List Char)) :
    ∀ a before K, (∀ w, (K w).FirstOrder) → (selectAt E before a K).FirstOrder
  | .lit _, _, K, hK => ⟨⟨trivial,trivial⟩,hK _⟩
  | .param k, _, K, hK => by simp only [selectAt]; split; exact ⟨⟨trivial,trivial⟩,hK _⟩; trivial
  | .alt a b, before, K, hK => by
    have ha := selectAt_firstOrder E a before K hK
    have hb := selectAt_firstOrder E b before K hK
    have hg : (MExp.seq (.lit before) (erase E a)).FirstOrder := ⟨trivial,erase_firstOrder E a⟩
    exact ⟨⟨hg,ha⟩,hg,hb⟩
  | .seq a b, before, K, hK =>
    selectAt_firstOrder E a before _ (fun u => selectAt_firstOrder E b (before++u) _ (fun v => hK (u++v)))
  | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .call _ _, _, _, _
  | .star _, _, _, _ | .notP _, _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => trivial

theorem selectArgs_firstOrder (E : List (List Char)) :
    ∀ args K, (∀ W, (K W).FirstOrder) → (selectArgs E args K).FirstOrder
  | [], _, hK => hK []
  | a::args, _, hK => selectAt_firstOrder E a [] _ (fun w => selectArgs_firstOrder E args _ (fun W => hK (w::W)))

theorem erase_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) :
    ∀ a, Arg a → ∀ p, evV g x s T E a p = evV h x t U [] (erase E a) p
  | .lit _, _, _ => rfl
  | .param k, _, p => by cases hh : E[k]? <;> simp [erase,evV,hh,MExp.failAlways]
  | .seq a b, ha, p => by
    simp only [erase,evV]
    rw [← erase_eval g h x s t T U E a ha.1 p]
    cases hv : evV g x s T E a p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some q => exact erase_eval g h x s t T U E b ha.2 q
  | .alt a b, ha, p => by
    simp only [erase,evV]
    rw [← erase_eval g h x s t T U E a ha.1 p,← erase_eval g h x s t T U E b ha.2 p]
  | .eps, ha, _ | .any, ha, _ | .chr _, ha, _ | .range _ _, ha, _ | .call _ _, ha, _
  | .star _, ha, _ | .notP _, ha, _ | .dbg _, ha, _ | .lam _ _, ha, _
  | .callParam _ _, ha, _ | .invoke _ _ _, ha, _ => False.elim ha

/-- The argument contains no calls, so its successful prefix property follows
from a sound empty grammar independently of the surrounding table. -/
theorem success_prefix (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (ha : Arg a)
    (p q : Nat) (hp : p ≤ x.length) (hv : evV g x s T E a p = some (some q)) :
    q ≤ x.length ∧ sfx x p = pre x p q ++ sfx x q := by
  let h : MGrammar := ⟨[]⟩
  let U : Nat → List (List Char) → Val := fun _ _ => []
  have hs : SoundTV h x .callByValuePar U := by
    intro i r W hr
    cases i <;> cases hr
  have he := (erase_eval g h x s .callByValuePar T U E a ha p).symm.trans hv
  exact ReplayFusion.success_prefix hs [] (erase E a) (erase_firstOrder E a) p q hp he

theorem probe_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (ha : Arg a)
    (before : List Char) (p q : Nat) (hq : q ≤ x.length)
    (hprefix : sfx x p = before++sfx x q) :
    evV h x t U [] (.seq (.lit before) (erase E a)) p = evV g x s T E a q := by
  have hl : evV h x t U [] (.lit before) p = some (some q) := by
    simp only [evV,(CBVtoCBN.stripPrefix_exact before _ _).mpr hprefix,length_sfx x hq]
  rw [evV_seq_ok hl]
  exact (erase_eval g h x s t T U E a ha q).symm

theorem pre_concat {x : List Char} {q j k : Nat} (hq : q ≤ x.length) (hk : k ≤ x.length)
    (ha : sfx x q = pre x q j++sfx x j) (hb : sfx x j = pre x j k++sfx x k) :
    pre x q k = pre x q j++pre x j k := by
  have hh : sfx x q = (pre x q j++pre x j k)++sfx x k := by rw [ha,hb,List.append_assoc]
  have he := pre_eq (sfx_is_suffix x q) hh
  simpa only [length_sfx x hq,length_sfx x hk] using he

private theorem literal_selectAt (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (w before : List Char)
    (K : List Char → MExp) (p q : Nat) (hq : q ≤ x.length)
    (hprefix : sfx x p = before++sfx x q) :
    evV h x t U [] (.seq (.andP (.seq (.lit before) (.lit w))) (K w)) p =
      match evV g x s T E (.lit w) q with
      | some (some j) => evV h x t U [] (K (pre x q j)) p | r => r := by
  have hp := probe_eval g h x s t T U E (.lit w) trivial before p q hq hprefix
  change evV h x t U [] (.seq (.andP (.seq (.lit before) (erase E (.lit w)))) (K w)) p = _
  cases hs : Shallot.stripPrefix? w (sfx x q) with
  | none =>
    have hg : evV h x t U [] (.andP (.seq (.lit before) (erase E (.lit w)))) p = some none := by
      rw [CallLookahead.evV_peek,hp]
      simp [evV,hs,CallLookahead.peek]
    rw [evV_seq_fail hg]
    simp [evV,hs]
  | some rest =>
    have he := pre_eq (sfx_is_suffix x q) ((CBVtoCBN.stripPrefix_exact w _ _).mp hs)
    have hw : pre x q rest.length=w := by simpa only [length_sfx x hq] using he
    have hg : evV h x t U [] (.andP (.seq (.lit before) (erase E (.lit w)))) p = some (some p) := by
      rw [CallLookahead.evV_peek,hp]
      simp [evV,hs,CallLookahead.peek]
    rw [evV_seq_ok hg]
    simp [evV,hs,hw]

theorem selectAt_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (p : Nat) :
    ∀ a, Arg a → ∀ before q, q ≤ x.length → sfx x p = before++sfx x q → ∀ K,
      evV h x t U [] (selectAt E before a K) p =
        match evV g x s T E a q with
        | some (some j) => evV h x t U [] (K (pre x q j)) p | r => r
  | .lit w, _, before, q, hq, hs, K => literal_selectAt g h x s t T U E w before K p q hq hs
  | .param k, _, before, q, hq, hs, K => by
    cases hh : E[k]? with
    | none => simp [selectAt,evV,hh,MExp.failAlways]
    | some w => simpa only [selectAt,hh,evV] using literal_selectAt g h x s t T U E w before K p q hq hs
  | .alt a b, ha, before, q, hq, hs, K => by
    rw [selectAt,ChoiceArguments.branch_eval,probe_eval g h x s t T U E a ha.1 before p q hq hs]
    cases hv : evV g x s T E a q with
    | none => simp [evV,hv]
    | some r =>
      cases r with
      | none => simpa only [evV,hv] using selectAt_eval g h x s t T U E p b ha.2 before q hq hs K
      | some j => simpa only [evV,hv] using selectAt_eval g h x s t T U E p a ha.1 before q hq hs K
  | .seq a b, ha, before, q, hq, hs, K => by
    rw [selectAt,selectAt_eval g h x s t T U E p a ha.1 before q hq hs]
    cases hv : evV g x s T E a q with
    | none => simp [evV,hv]
    | some r =>
      cases r with
      | none => simp [evV,hv]
      | some j =>
        obtain ⟨hj,hpre⟩ := success_prefix g x s T E a ha.1 q j hq hv
        have hs' : sfx x p = (before++pre x q j)++sfx x j := by rw [hs,hpre,List.append_assoc]
        dsimp only
        rw [selectAt_eval g h x s t T U E p b ha.2 _ j hj hs']
        simp only [evV_seq_ok hv]
        cases hb : evV g x s T E b j with
        | none => rfl
        | some r =>
          cases r with
          | none => rfl
          | some k =>
            obtain ⟨hk,hbpre⟩ := success_prefix g x s T E b ha.2 j k hj hb
            dsimp only
            rw [pre_concat hq hk hpre hbpre]
  | .eps, ha, _, _, _, _, _ | .any, ha, _, _, _, _, _ | .chr _, ha, _, _, _, _, _
  | .range _ _, ha, _, _, _, _, _ | .call _ _, ha, _, _, _, _, _ | .star _, ha, _, _, _, _, _
  | .notP _, ha, _, _, _, _, _ | .dbg _, ha, _, _, _, _, _ | .lam _ _, ha, _, _, _, _, _
  | .callParam _ _, ha, _, _, _, _, _ | .invoke _ _ _, ha, _, _, _, _, _ => False.elim ha

theorem select_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (p : Nat) (hp : p ≤ x.length)
    (a : MExp) (ha : Arg a) (K : List Char → MExp) :
    evV h x t U [] (select E a K) p = match evV g x s T E a p with
      | some (some j) => evV h x t U [] (K (pre x p j)) p | r => r :=
  selectAt_eval g h x s t T U E p a ha [] p hp (by simp) K

theorem selectArgs_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char))
    (p : Nat) (hp : p ≤ x.length) :
    ∀ args, (∀ a ∈ args, Arg a) → ∀ K,
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

end Shallot.MacroPeg.CBV.SequenceArguments
