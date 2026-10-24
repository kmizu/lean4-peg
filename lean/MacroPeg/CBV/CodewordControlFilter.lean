import MacroPeg.CBV.SelectedCodewordGrammar
import MacroPeg.CBV.ChoiceArguments
import MacroPeg.CBV.RootObservation

/-! Compare all consumed codewords with a retained runtime word while
preserving the original parser's choices and greedy stopping point. -/
namespace Shallot.MacroPeg.CBV.CodewordControlFilter
open ClockFreezing (Table)

inductive Expr where
  | token
  | eps
  | test (e : MExp)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | notP (a : Expr)
  | star (a : Expr)

def render (A : MExp) : Expr → MExp
  | .token => A
  | .eps => .eps
  | .test e => .andP e
  | .seq a b => .seq (render A a) (render A b)
  | .alt a b => .alt (render A a) (render A b)
  | .notP a => .notP (render A a)
  | .star a => .star (render A a)

def filter (A : MExp) (d : Expr) : MExp :=
  .seq (.andP (render A d)) (match d with
    | .token => .param 0
    | .eps => .eps
    | .test e => .andP e
    | .seq a b => .seq (filter A a) (filter A b)
    | .alt a b => RootObservation.branch (.andP (render A a)) (filter A a) (filter A b)
    | .notP a => .notP (render A a)
    | .star a => .seq (.star (filter A a)) (.notP (render A a)))

def Pure : Expr → Prop
  | .test e => ParserPrefixFusion.Pure e
  | .seq a b | .alt a b => Pure a ∧ Pure b
  | .notP a | .star a => Pure a
  | _ => True

theorem render_pure (A : MExp) (hA : ParserPrefixFusion.Pure A) :
    ∀ d, Pure d → ParserPrefixFusion.Pure (render A d)
  | .token, _ => hA
  | .eps, _ => True.intro
  | .test _, h => h
  | .seq a b, h | .alt a b, h => ⟨render_pure A hA a h.1,render_pure A hA b h.2⟩
  | .notP a, h | .star a, h => render_pure A hA a h

theorem filter_syntax (A : MExp) (hA : ParserPrefixFusion.Pure A) :
    ∀ d, Pure d → HelperArgument.Syntax 0 (filter A d)
  | .token, _ => ⟨LastCodewordGrammar.pure_syntax A hA,True.intro⟩
  | .eps, _ => ⟨True.intro,True.intro⟩
  | .test e, h => ⟨LastCodewordGrammar.pure_syntax e h,LastCodewordGrammar.pure_syntax e h⟩
  | .seq a b, h => ⟨LastCodewordGrammar.pure_syntax _ (render_pure A hA _ h),filter_syntax A hA a h.1,filter_syntax A hA b h.2⟩
  | .alt a b, h => ⟨LastCodewordGrammar.pure_syntax _ (render_pure A hA _ h),
      ⟨LastCodewordGrammar.pure_syntax _ (render_pure A hA a h.1),filter_syntax A hA a h.1⟩,
      LastCodewordGrammar.pure_syntax _ (render_pure A hA a h.1),filter_syntax A hA b h.2⟩
  | .notP a, h => ⟨LastCodewordGrammar.pure_syntax _ (render_pure A hA _ h),LastCodewordGrammar.pure_syntax _ (render_pure A hA a h)⟩
  | .star a, h => ⟨LastCodewordGrammar.pure_syntax _ (render_pure A hA _ h),filter_syntax A hA a h,LastCodewordGrammar.pure_syntax _ (render_pure A hA a h)⟩

theorem uniform_append (u : List Char) (as bs : List (List Char)) :
    as++bs=List.replicate (as++bs).length u ↔
      as=List.replicate as.length u ∧ bs=List.replicate bs.length u := by
  simp only [List.append_eq_replicate_iff,List.length_append,true_and]

theorem filter_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (A : MExp) (d : Expr) (p : Nat)
    (h : evV g x s T E (render A d) p=none) : evV g x s T E (filter A d) p=none := by
  rw [filter.eq_def]
  apply evV_seq_none
  rw [CallLookahead.evV_peek,h]
  rfl

theorem filter_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (A : MExp) (d : Expr) (p : Nat)
    (h : evV g x s T E (render A d) p=some none) : evV g x s T E (filter A d) p=some none := by
  rw [filter.eq_def]
  apply evV_seq_fail
  rw [CallLookahead.evV_peek,h]
  rfl

/-- With arbitrary retained context after the comparison word, filtering
keeps the original branch and stopping point. Header and tests may inspect
that context; only the actual header-success code certificate is required. -/
theorem success_environment (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u) (E : List (List Char))
    (hcode : ∀ p q, p≤x.length → evV g x s T (u::E) A p=some (some q) → C (pre x p q)) :
    ∀ d p q, p≤x.length → evV g x s T (u::E) (render A d) p=some (some q) →
      ∃ ws : List (List Char), (∀ w∈ws, C w) ∧ sfx x p=ws.flatten++sfx x q ∧
        evV g x s T (u::E) (filter A d) p=
          if ws=List.replicate ws.length u then some (some q) else some none := by
  intro d
  induction d with
  | token =>
    intro p q hp hv
    have hq : q≤x.length := evV_ok hOk A p hp q hv
    have hsf := (WordStarFilter.success_prefix hs hT (u::E) A hA p q hp hv).2
    refine ⟨[pre x p q],by simpa using hcode p q hp hv,by simpa using hsf,?_⟩
    rw [filter,evV_seq_ok (show evV g x s T (u::E) (.andP (render A .token)) p=some (some p) by
      rw [CallLookahead.evV_peek,hv]; rfl)]
    by_cases he : pre x p q=u
    · have hh := hsf
      rw [he] at hh
      simp only [List.length_singleton,List.replicate_one,List.cons.injEq,and_true,if_pos he]
      change evV g x s T [] (.lit u) p=_
      simpa only [length_sfx x hq] using LastCodewordCandidate.literal_at g x s T [] u (sfx x q) p hh
    · have hstrip : Shallot.stripPrefix? u (sfx x p)=none := by
        cases hh : Shallot.stripPrefix? u (sfx x p) with
        | none => rfl
        | some rest => exact False.elim (he (PrefixCodeCapture.prefix_identifies hc hu (hcode p q hp hv)
            ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm.trans hsf⟩).symm)
      simp [evV,hstrip,he]
  | eps =>
    intro p q hp hv
    have he : p=q := by simpa [render,evV] using hv
    subst q
    exact ⟨[],by simp,by simp,by simp [filter,render,evV,MExp.andP]⟩
  | test e =>
    intro p q hp hv
    have he : p=q := by rw [render,CallLookahead.evV_peek] at hv; cases hh : evV g x s T (u::E) e p with
      | none => simp [CallLookahead.peek,hh] at hv
      | some r => cases r with | none => simp [CallLookahead.peek,hh] at hv | some j => simpa [CallLookahead.peek,hh] using hv
    subst q
    refine ⟨[],by simp,by simp,?_⟩
    rw [filter,evV_seq_ok (show evV g x s T (u::E) (.andP (render A (.test e))) p=some (some p) by
      rw [CallLookahead.evV_peek,hv]; rfl)]
    exact hv
  | notP a ih =>
    intro p q hp hv
    have he : p=q := by
      change (match evV g x s T (u::E) (render A a) p with
        | some (some _) => some none | some none => some (some p) | none => none)=some (some q) at hv
      split at hv <;> simp_all
    subst q
    refine ⟨[],by simp,by simp,?_⟩
    rw [filter,evV_seq_ok (show evV g x s T (u::E) (.andP (render A (.notP a))) p=some (some p) by
      rw [CallLookahead.evV_peek,hv]; rfl)]
    exact hv
  | seq a b ia ib =>
    intro p q hp hv
    change (match evV g x s T (u::E) (render A a) p with
      | some (some j) => evV g x s T (u::E) (render A b) j | other => other)=_ at hv
    cases ha : evV g x s T (u::E) (render A a) p with
    | none => simp [ha] at hv
    | some result => cases result with
      | none => simp [ha] at hv
      | some j =>
        have hb : evV g x s T (u::E) (render A b) j=some (some q) := by simpa [ha] using hv
        have hj : j≤x.length := evV_ok hOk _ p hp j ha
        obtain ⟨as,hac,has,haf⟩ := ia p j hp ha
        obtain ⟨bs,hbc,hbs,hbf⟩ := ib j q hj hb
        refine ⟨as++bs,by intro w hw; exact (List.mem_append.mp hw).elim (hac w) (hbc w),
          by simpa [List.flatten_append,List.append_assoc,hbs] using has,?_⟩
        rw [filter,evV_seq_ok (show evV g x s T (u::E) (.andP (render A (.seq a b))) p=some (some p) by
          rw [CallLookahead.evV_peek]; change CallLookahead.peek p (evV g x s T (u::E) (.seq (render A a) (render A b)) p)=_
          rw [evV_seq_ok ha,hb]; rfl)]
        change (match evV g x s T (u::E) (filter A a) p with
          | some (some z) => evV g x s T (u::E) (filter A b) z | other => other)=_
        rw [haf]
        by_cases he : as=List.replicate as.length u
        · rw [if_pos he]
          dsimp only []
          rw [hbf]
          congr 1
          exact propext ⟨fun h => (uniform_append u as bs).mpr ⟨he,h⟩,fun h => ((uniform_append u as bs).mp h).2⟩
        · rw [if_neg he,if_neg (fun h => he ((uniform_append u as bs).mp h).1)]
  | alt a b ia ib =>
    intro p q hp hv
    have hpre : evV g x s T (u::E) (.andP (render A (.alt a b))) p=some (some p) := by
      rw [CallLookahead.evV_peek,hv]; rfl
    change (match evV g x s T (u::E) (render A a) p with
      | some none => evV g x s T (u::E) (render A b) p | other => other)=_ at hv
    cases ha : evV g x s T (u::E) (render A a) p with
    | none => simp [ha] at hv
    | some result => cases result with
      | none =>
        have hb : evV g x s T (u::E) (render A b) p=some (some q) := by simpa [ha] using hv
        obtain ⟨ws,hw,hsf,hf⟩ := ib p q hp hb
        refine ⟨ws,hw,hsf,?_⟩
        rw [filter,evV_seq_ok hpre,ChoiceArguments.branch_eval,ha]
        exact hf
      | some j =>
        have he : j=q := by simpa [ha] using hv
        subst j
        obtain ⟨ws,hw,hsf,hf⟩ := ia p q hp ha
        refine ⟨ws,hw,hsf,?_⟩
        rw [filter,evV_seq_ok hpre,ChoiceArguments.branch_eval,ha]
        exact hf
  | star a ia =>
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro q hp hv
      have hpre : evV g x s T (u::E) (.andP (render A (.star a))) p=some (some p) := by
        rw [CallLookahead.evV_peek,hv]; rfl
      change evStar (fun z => evV g x s T (u::E) (render A a) z) p=some (some q) at hv
      cases ha : evV g x s T (u::E) (render A a) p with
      | none => rw [evStar_none ha] at hv; cases hv
      | some result => cases result with
        | none =>
          rw [evStar_fail ha] at hv
          have he : p=q := by simpa using hv
          subst q
          refine ⟨[],by simp,by simp,?_⟩
          have hf := filter_fail g x s T (u::E) A a p ha
          rw [filter,evV_seq_ok hpre]
          rw [evV_seq_ok (show evV g x s T (u::E) (.star (filter A a)) p=some (some p) from evStar_fail hf),evV_not_fail ha]
          rfl
        | some j =>
          by_cases hjp : j<p
          · rw [evStar_ok ha hjp] at hv
            have hj : j≤x.length := by omega
            obtain ⟨as,hac,has,haf⟩ := ia p j hp ha
            obtain ⟨bs,hbc,hbs,hbf⟩ := ih j hjp q hj hv
            refine ⟨as++bs,by intro w hw; exact (List.mem_append.mp hw).elim (hac w) (hbc w),
              by simpa [List.flatten_append,List.append_assoc,hbs] using has,?_⟩
            rw [filter,evV_seq_ok hpre]
            have hfpre : evV g x s T (u::E) (.andP (render A (.star a))) j=some (some j) := by
              rw [CallLookahead.evV_peek]; change CallLookahead.peek j (evStar (fun z => evV g x s T (u::E) (render A a) z) j)=_
              rw [hv]; rfl
            rw [filter,evV_seq_ok hfpre] at hbf
            by_cases he : as=List.replicate as.length u
            · rw [if_pos he] at haf
              change (match evStar (fun z => evV g x s T (u::E) (filter A a) z) p with
                | some (some z) => evV g x s T (u::E) (.notP (render A a)) z | other => other)=_
              rw [evStar_ok haf hjp]
              change evV g x s T (u::E) (.seq (.star (filter A a)) (.notP (render A a))) j=_
              rw [hbf]
              congr 1
              exact propext ⟨fun h => (uniform_append u as bs).mpr ⟨he,h⟩,fun h => ((uniform_append u as bs).mp h).2⟩
            · rw [if_neg he] at haf
              rw [evV_seq_ok (show evV g x s T (u::E) (.star (filter A a)) p=some (some p) from evStar_fail haf),evV_not_ok ha]
              rw [if_neg (fun h => he ((uniform_append u as bs).mp h).1)]
          · rw [evStar_stuck ha hjp] at hv; cases hv

theorem success (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u)
    (hcode : ∀ p q, p≤x.length → evV g x s T [u] A p=some (some q) → C (pre x p q)) :
    ∀ d p q, p≤x.length → evV g x s T [u] (render A d) p=some (some q) →
      ∃ ws : List (List Char), (∀ w∈ws, C w) ∧ sfx x p=ws.flatten++sfx x q ∧
        evV g x s T [u] (filter A d) p=
          if ws=List.replicate ws.length u then some (some q) else some none := by
  exact success_environment g x s hs T hT hOk A hA hc u hu [] hcode

/-- Reconstruct the whole source argument from two consecutive captures. -/
def wholeView (b : MExp) : MExp := MExp.subst [CaptureViews.prefixExpr 2] b

theorem wholeView_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u v : List Char) (b : MExp) (hb : b.FirstOrder) (p : Nat) :
    evV g x s T [u,v] (wholeView b) p=evV g x s T [u++v] b p := by
  exact CaptureViews.body_view g x s T [u,v] [u++v] [2]
    (by simp) (by simp) b hb p

theorem wholeView_firstOrder (b : MExp) (hb : b.FirstOrder) : (wholeView b).FirstOrder :=
  firstOrder_subst (args := [CaptureViews.prefixExpr 2])
    ⟨CaptureViews.prefixExpr_firstOrder 2,True.intro⟩ b hb

theorem wholeView_syntax : ∀ b, HelperArgument.Syntax 0 b → HelperArgument.Syntax 0 (wholeView b)
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => True.intro
  | .param 0, _ => ⟨⟨True.intro,True.intro⟩,True.intro⟩
  | .param (_+1), _ => True.intro
  | .seq a b, h | .alt a b, h => ⟨wholeView_syntax a h.1,wholeView_syntax b h.2⟩
  | .notP a, h | .star a, h => wholeView_syntax a h
  | .call i [], h => False.elim (Nat.not_lt_zero i h)
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

/-- A raw trace determines the source replay exactly. A mismatch rejects
the committed trace; the target cannot select a different branch or count. -/
theorem replay_trace (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u) (ws : List (List Char)) (hw : ∀ w∈ws, C w)
    (p q : Nat) (hq : q≤x.length) (htrace : sfx x p=ws.flatten++sfx x q)
    (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [u++ws.flatten] (.seq (.param 0) b) p=
      if ws=List.replicate ws.length u then
        evV g x s T [u,ws.flatten] (.seq (.param 0) (wholeView b)) q
      else some none := by
  by_cases he : ws=List.replicate ws.length u
  · rw [if_pos he]
    have hcomm : u++ws.flatten=ws.flatten++u := by
      calc
        u++ws.flatten=CodewordReplay.power u (ws.length+1) := by
          exact (congrArg (fun ls : List (List Char) => u++ls.flatten) he).trans
            (by simp only [CodewordReplay.power,List.replicate_succ,List.flatten_cons])
        _=ws.flatten++u := by
          rw [LastCodewordCandidate.power_succ_right]
          congr 1
          exact congrArg List.flatten he.symm
    have hfirst : evV g x s T [ws.flatten++u] (.lit ws.flatten) p=some (some q) := by
      simpa only [length_sfx x hq] using
        LastCodewordCandidate.literal_at g x s T [ws.flatten++u] ws.flatten (sfx x q) p htrace
    have hr : evV g x s T [u++ws.flatten] (.param 0) p=
        evV g x s T [u,ws.flatten] (.param 0) q := by
      change evV g x s T [u++ws.flatten] (.lit (u++ws.flatten)) p=_
      rw [hcomm,← CaptureViews.sequence_literals,evV_seq_ok hfirst]
      rfl
    change (match evV g x s T [u++ws.flatten] (.param 0) p with
      | some (some j) => evV g x s T [u++ws.flatten] b j | other => other)=_
    rw [hr]
    change _=(match evV g x s T [u,ws.flatten] (.param 0) q with
      | some (some j) => evV g x s T [u,ws.flatten] (wholeView b) j | other => other)
    cases evV g x s T [u,ws.flatten] (.param 0) q with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some j => exact (wholeView_eval g x s T u ws.flatten b hb j).symm
  · rw [if_neg he]
    have hfail : Shallot.stripPrefix? (u++ws.flatten) (ws.flatten++sfx x q)=none := by
      cases h : Shallot.stripPrefix? (u++ws.flatten) (ws.flatten++sfx x q) with
      | none => rfl
      | some r => exact False.elim (he (CodewordReplay.source_prefix_forces hc u ws (sfx x q) hu hw
          ⟨r,((CBVtoCBN.stripPrefix_exact _ _ _).mp h).symm⟩))
    apply evV_seq_fail
    simp [evV,htrace,hfail]

/-- Exact partial replay equivalence after the original control selects
its endpoint. The input after that endpoint need not start with a header. -/
theorem replay_success_environment (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u) (E : List (List Char))
    (hcode : ∀ p q, p≤x.length → evV g x s T (u::E) A p=some (some q) → C (pre x p q))
    (d : Expr) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T (u::E) (render A d) p=some (some q))
    (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [u++pre x p q] (.seq (.param 0) b) p=
      match evV g x s T (u::E) (filter A d) p with
      | some (some _) => evV g x s T [u,pre x p q] (.seq (.param 0) (wholeView b)) q
      | other => other := by
  obtain ⟨ws,hw,htrace,hf⟩ := success_environment g x s hs T hT hOk A hA hc u hu E hcode d p q hp hv
  have hq := evV_ok hOk (render A d) p hp q hv
  have hpre : pre x p q=ws.flatten := by
    simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) htrace
  rw [hpre,hf]
  have hr := replay_trace g x s T hc u hu ws hw p q hq htrace b hb
  by_cases he : ws=List.replicate ws.length u
  · rw [if_pos he] at hr ⊢
    exact hr
  · rw [if_neg he] at hr ⊢
    exact hr

theorem replay_success (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u)
    (hcode : ∀ p q, p≤x.length → evV g x s T [u] A p=some (some q) → C (pre x p q))
    (d : Expr) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T [u] (render A d) p=some (some q))
    (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [u++pre x p q] (.seq (.param 0) b) p=
      match evV g x s T [u] (filter A d) p with
      | some (some _) => evV g x s T [u,pre x p q] (.seq (.param 0) (wholeView b)) q
      | other => other := by
  exact replay_success_environment g x s hs T hT hOk A hA hc u hu [] hcode d p q hp hv b hb

end Shallot.MacroPeg.CBV.CodewordControlFilter
