import MacroPeg.CBV.SelectedControlFusion

/-! Predicate-bearing arguments select empty words at their exact positions.
Predicate translation may execute arbitrary recursive first-order queries. -/
namespace Shallot.MacroPeg.CBV.GuardedWordSelection
open WordArguments (Word value word_eval value_of_success)

def Shape : MExp → Prop
  | .lit _ | .param _ | .notP _ => True
  | .seq a b | .alt a b => Shape a ∧ Shape b
  | _ => False

def shapeB : MExp → Bool
  | .lit _ | .param _ | .notP _ => true
  | .seq a b | .alt a b => shapeB a && shapeB b
  | _ => false

theorem shapeB_iff : ∀ a, shapeB a = true ↔ Shape a
  | .lit _ | .param _ | .notP _ => by simp [shapeB,Shape]
  | .seq a b | .alt a b => by simp [shapeB,Shape,shapeB_iff a,shapeB_iff b]
  | .eps | .any | .chr _ | .range _ _ | .call _ _ | .star _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => by simp [shapeB,Shape]

def Checks (P : MExp → Prop) : MExp → Prop
  | .notP e => P e
  | .seq a b | .alt a b => Checks P a ∧ Checks P b
  | _ => True

def argRender (R : MExp → MExp) : MExp → MExp
  | .lit w => .lit w
  | .param k => .param k
  | .seq a b => .seq (argRender R a) (argRender R b)
  | .alt a b => .alt (argRender R a) (argRender R b)
  | .notP e => .notP (R e)
  | _ => MExp.failAlways

def selectAt (R : MExp → MExp) (before : MExp) : MExp → (MExp → MExp) → MExp
  | .lit w, K => .seq (.andP (.seq before (.lit w))) (K (.lit w))
  | .param k, K => .seq (.andP (.seq before (.param k))) (K (.param k))
  | .notP e, K => .seq (.andP (.seq before (.notP (R e)))) (K (.lit []))
  | .alt a b, K => RootObservation.branch (.andP (.seq before (argRender R a)))
      (selectAt R before a K) (selectAt R before b K)
  | .seq a b, K => selectAt R before a (fun u => selectAt R (.seq before u) b (fun v => K (.seq u v)))
  | _, _ => MExp.failAlways

def select (R : MExp → MExp) (a : MExp) (K : MExp → MExp) : MExp := selectAt R (.lit []) a K

theorem checks_imp {P Q : MExp → Prop} (h : ∀ e, P e → Q e) : ∀ a, Checks P a → Checks Q a
  | .notP e, he => h e he
  | .seq a b, he | .alt a b, he => ⟨checks_imp h a he.1,checks_imp h b he.2⟩
  | .lit _, _ | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .call _ _, _ | .star _, _
  | .dbg _, _ | .lam _ _, _ | .callParam _ _, _ | .invoke _ _ _, _ => trivial

theorem arg_firstOrder : ∀ a, Shape a → Checks MExp.FirstOrder a → a.FirstOrder
  | .lit _, _, _ | .param _, _, _ => trivial
  | .notP _, _, he => he
  | .seq a b, ha, he | .alt a b, ha, he => ⟨arg_firstOrder a ha.1 he.1,arg_firstOrder b ha.2 he.2⟩
  | .eps, ha, _ | .any, ha, _ | .chr _, ha, _ | .range _ _, ha, _ | .call _ _, ha, _ | .star _, ha, _
  | .dbg _, ha, _ | .lam _ _, ha, _ | .callParam _ _, ha, _ | .invoke _ _ _, ha, _ => False.elim ha

def Agrees (g h : MGrammar) (x : List Char) (T U : Nat → List (List Char) → Val)
    (E : List (List Char)) (R : MExp → MExp) (e : MExp) : Prop :=
  e.FirstOrder ∧ ∀ p, p ≤ x.length → evV g x .callByValuePar T E e p = evV h x .callByValueSeq U E (R e) p

theorem arg_eval (g h : MGrammar) (x : List Char) (T U : Nat → List (List Char) → Val)
    (E : List (List Char)) (R : MExp → MExp) (hOk : OkTV x.length T) :
    ∀ a, Shape a → Checks (Agrees g h x T U E R) a → ∀ p, p ≤ x.length →
      evV g x .callByValuePar T E a p = evV h x .callByValueSeq U E (argRender R a) p
  | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .notP e, _, he, p, hp => by simp only [argRender,evV]; rw [he.2 p hp]
  | .seq a b, ha, he, p, hp => by
    have hh := arg_eval g h x T U E R hOk a ha.1 he.1 p hp
    cases hv : evV g x .callByValuePar T E a p with
    | none => simp only [argRender,evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some r => cases r with
      | none => simp only [argRender,evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        simp only [argRender,evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact arg_eval g h x T U E R hOk b ha.2 he.2 q (evV_ok hOk a p hp q hv)
  | .alt a b, ha, he, p, hp => by
    have hh := arg_eval g h x T U E R hOk a ha.1 he.1 p hp
    cases hv : evV g x .callByValuePar T E a p with
    | none => simp only [argRender,evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some r => cases r with
      | none =>
        simp only [argRender,evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
        exact arg_eval g h x T U E R hOk b ha.2 he.2 p hp
      | some q => simp only [argRender,evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .eps, ha, _, _, _ | .any, ha, _, _, _ | .chr _, ha, _, _, _ | .range _ _, ha, _, _, _
  | .call _ _, ha, _, _, _ | .star _, ha, _, _, _ | .dbg _, ha, _, _, _ | .lam _ _, ha, _, _, _
  | .callParam _ _, ha, _, _, _ | .invoke _ _ _, ha, _, _, _ => False.elim ha

theorem probe_eval (g h : MGrammar) (x : List Char) (T U : Nat → List (List Char) → Val)
    (E : List (List Char)) (R : MExp → MExp) (hOk : OkTV x.length T)
    (before : MExp) (hb : Word before) (u : List Char) (hu : value E before = some u)
    (a : MExp) (ha : Shape a) (he : Checks (Agrees g h x T U E R) a)
    (p q : Nat) (hq : q ≤ x.length) (hs : sfx x p = u++sfx x q) :
    evV h x .callByValueSeq U E (.seq before (argRender R a)) p = evV g x .callByValuePar T E a q := by
  have hv : evV h x .callByValueSeq U E before p = some (some q) := by
    rw [word_eval _ _ _ _ E before hb p,hu]
    simp only [WordArguments.literal,evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hs,length_sfx x hq]
  rw [evV_seq_ok hv]
  exact (arg_eval g h x T U E R hOk a ha he q hq).symm

abbrev Respects := SymbolicWordSelection.Respects

theorem selectAt_eval (g h : MGrammar) (x : List Char) (T U : Nat → List (List Char) → Val) (E : List (List Char))
    (R : MExp → MExp) (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T) (p : Nat) :
    ∀ a, Shape a → Checks (Agrees g h x T U E R) a → ∀ before, Word before → ∀ u, value E before = some u →
      ∀ q, q ≤ x.length → sfx x p = u++sfx x q → ∀ K f, Respects h x .callByValueSeq U E p q K f →
      evV h x .callByValueSeq U E (selectAt R before a K) p =
        match evV g x .callByValuePar T E a q with | some (some j) => f (pre x q j) | other => other
  | .lit w, _, he, before, hb, u, hu, q, hq, hs, K, f, hK =>
    SymbolicWordSelection.selectAt_eval g h x .callByValuePar .callByValueSeq T U E p (.lit w) True.intro before hb u hu q hq hs K f hK
  | .param k, _, he, before, hb, u, hu, q, hq, hs, K, f, hK =>
    SymbolicWordSelection.selectAt_eval g h x .callByValuePar .callByValueSeq T U E p (.param k) True.intro before hb u hu q hq hs K f hK
  | .alt a b, ha, he, before, hb, u, hu, q, hq, hs, K, f, hK => by
    rw [selectAt,ChoiceArguments.branch_eval,probe_eval g h x T U E R hOk before hb u hu a ha.1 he.1 p q hq hs]
    cases hv : evV g x .callByValuePar T E a q with
    | none => simp [evV,hv]
    | some r => cases r with
      | none => simpa only [evV,hv] using selectAt_eval g h x T U E R hT hOk p b ha.2 he.2 before hb u hu q hq hs K f hK
      | some j => simpa only [evV,hv] using selectAt_eval g h x T U E R hT hOk p a ha.1 he.1 before hb u hu q hq hs K f hK
  | .seq a b, ha, he, before, hb, u, hu, q, hq, hs, K, f, hK => by
    rw [selectAt]
    have hcont : Respects h x .callByValueSeq U E p q
        (fun v => selectAt R (.seq before v) b (fun w => K (.seq v w)))
        (fun v => match evV g x .callByValuePar T E b (q-v.length) with
          | some (some j) => f (v++pre x (q-v.length) j) | other => other) := by
      intro v hv word hword hprefix
      obtain ⟨rest,hrest⟩ := hprefix
      have hlen := congrArg List.length hrest
      simp only [length_sfx x hq,List.length_append] at hlen
      have hpos : q-word.length = rest.length := by omega
      have hrem : sfx x (q-word.length) = rest := by
        rw [hpos]
        exact sfx_suffix (suffix_trans (sfx_is_suffix x q) ⟨word,hrest⟩).choose_spec
      have hs' : sfx x p = (u++word)++sfx x (q-word.length) := by
        rw [hs,hrest,hrem,List.append_assoc]
      refine selectAt_eval g h x T U E R hT hOk p b ha.2 he.2 (.seq before v) ⟨hb,hv⟩ (u++word)
        (by simp [value,hu,hword]) (q-word.length) (by omega) hs'
        (fun z => K (.seq v z)) (fun word' => f (word++word')) ?_
      intro z hz word' hword' hprefix'
      apply hK (.seq v z) ⟨hv,hz⟩ (word++word') (by simp [value,hword,hword'])
      obtain ⟨rem,hrem'⟩ := hprefix'
      refine ⟨rem,?_⟩
      rw [hrest,← hrem,hrem',List.append_assoc]
    rw [selectAt_eval g h x T U E R hT hOk p a ha.1 he.1 before hb u hu q hq hs _ _ hcont]
    cases hv : evV g x .callByValuePar T E a q with
    | none => simp [evV,hv]
    | some r => cases r with
      | none => simp [evV,hv]
      | some j =>
        obtain ⟨hj,hpre⟩ := ReplayFusion.success_prefix hT E a (arg_firstOrder a ha.1 (checks_imp (fun _ h => h.1) a he.1)) q j hq hv
        have hlen := congrArg List.length hpre
        simp only [length_sfx x hq,length_sfx x hj,List.length_append] at hlen
        have hpos : q-(pre x q j).length = j := by omega
        dsimp only []
        rw [hpos]
        simp only [evV_seq_ok hv]
        cases hvb : evV g x .callByValuePar T E b j with
        | none => rfl
        | some rb => cases rb with
          | none => rfl
          | some k =>
            obtain ⟨hk,hbpre⟩ := ReplayFusion.success_prefix hT E b (arg_firstOrder b ha.2 (checks_imp (fun _ h => h.1) b he.2)) j k hj hvb
            dsimp only []
            rw [SequenceArguments.pre_concat hq hk hpre hbpre]
  | .notP e, _, he, before, hb, u, hu, q, hq, hs, K, f, hK => by
    have hg : evV h x .callByValueSeq U E (.andP (.seq before (.notP (R e)))) p =
        CallLookahead.peek p (evV g x .callByValuePar T E (.notP e) q) := by
      rw [CallLookahead.evV_peek]
      exact congrArg (CallLookahead.peek p) (probe_eval g h x T U E R hOk before hb u hu (.notP e) True.intro he p q hq hs)
    rw [selectAt]
    cases hv : evV g x .callByValuePar T E e q with
    | none =>
      rw [evV_not_none hv]
      rw [evV_seq_none (hg.trans (by rw [evV_not_none hv]; rfl))]
    | some r => cases r with
      | none =>
        rw [evV_not_fail hv]
        rw [evV_seq_ok (hg.trans (by rw [evV_not_fail hv]; rfl))]
        have hh := hK (.lit []) True.intro [] rfl ⟨sfx x q,by simp⟩
        simpa only [pre,Nat.sub_self,List.take_zero] using hh
      | some j =>
        rw [evV_not_ok hv]
        rw [evV_seq_fail (hg.trans (by rw [evV_not_ok hv]; rfl))]
  | .eps, ha, _, _, _, _, _, _, _, _, _, _, _ | .any, ha, _, _, _, _, _, _, _, _, _, _, _
  | .chr _, ha, _, _, _, _, _, _, _, _, _, _, _ | .range _ _, ha, _, _, _, _, _, _, _, _, _, _, _
  | .call _ _, ha, _, _, _, _, _, _, _, _, _, _, _ | .star _, ha, _, _, _, _, _, _, _, _, _, _, _
  | .dbg _, ha, _, _, _, _, _, _, _, _, _, _, _ | .lam _ _, ha, _, _, _, _, _, _, _, _, _, _, _
  | .callParam _ _, ha, _, _, _, _, _, _, _, _, _, _, _ | .invoke _ _ _, ha, _, _, _, _, _, _, _, _, _, _, _ => False.elim ha


theorem select_eval (g h : MGrammar) (x : List Char) (T U : Nat → List (List Char) → Val)
    (E : List (List Char)) (R : MExp → MExp) (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T)
    (p : Nat) (hp : p ≤ x.length) (a : MExp) (ha : Shape a) (he : Checks (Agrees g h x T U E R) a)
    (K : MExp → MExp) (f : List Char → Res) (hK : Respects h x .callByValueSeq U E p p K f) :
    evV h x .callByValueSeq U E (select R a K) p =
      match evV g x .callByValuePar T E a p with | some (some j) => f (pre x p j) | other => other :=
  selectAt_eval g h x T U E R hT hOk p a ha he (.lit []) True.intro [] rfl p hp (by simp) K f hK


theorem argRender_firstOrder (R : MExp → MExp) : ∀ a, Shape a → Checks (fun e => (R e).FirstOrder) a → (argRender R a).FirstOrder
  | .lit _, _, _ | .param _, _, _ => trivial
  | .notP _, _, he => he
  | .seq a b, ha, he | .alt a b, ha, he => ⟨argRender_firstOrder R a ha.1 he.1,argRender_firstOrder R b ha.2 he.2⟩
  | .eps, ha, _ | .any, ha, _ | .chr _, ha, _ | .range _ _, ha, _ | .call _ _, ha, _ | .star _, ha, _
  | .dbg _, ha, _ | .lam _ _, ha, _ | .callParam _ _, ha, _ | .invoke _ _ _, ha, _ => False.elim ha

theorem selectAt_firstOrder (R : MExp → MExp) : ∀ a, Shape a → Checks (fun e => (R e).FirstOrder) a →
    ∀ before, Word before → ∀ K, (∀ w, Word w → (K w).FirstOrder) → (selectAt R before a K).FirstOrder
  | .lit w, _, _, before, hb, K, hK => ⟨⟨WordArguments.word_firstOrder before hb,True.intro⟩,hK _ True.intro⟩
  | .param k, _, _, before, hb, K, hK => ⟨⟨WordArguments.word_firstOrder before hb,True.intro⟩,hK _ True.intro⟩
  | .notP e, _, he, before, hb, K, hK => ⟨⟨WordArguments.word_firstOrder before hb,he⟩,hK _ True.intro⟩
  | .alt a b, ha, he, before, hb, K, hK => by
    have hg : (MExp.seq before (argRender R a)).FirstOrder := ⟨WordArguments.word_firstOrder before hb,argRender_firstOrder R a ha.1 he.1⟩
    exact ⟨⟨hg,selectAt_firstOrder R a ha.1 he.1 before hb K hK⟩,
      ⟨hg,selectAt_firstOrder R b ha.2 he.2 before hb K hK⟩⟩
  | .seq a b, ha, he, before, hb, K, hK =>
    selectAt_firstOrder R a ha.1 he.1 before hb _ (fun u hu =>
      selectAt_firstOrder R b ha.2 he.2 (.seq before u) ⟨hb,hu⟩ _ (fun v hv => hK (.seq u v) ⟨hu,hv⟩))
  | .eps, ha, _, _, _, _, _ | .any, ha, _, _, _, _, _ | .chr _, ha, _, _, _, _, _ | .range _ _, ha, _, _, _, _, _
  | .call _ _, ha, _, _, _, _, _ | .star _, ha, _, _, _, _, _ | .dbg _, ha, _, _, _, _, _ | .lam _ _, ha, _, _, _, _, _
  | .callParam _ _, ha, _, _, _, _, _ | .invoke _ _ _, ha, _, _, _, _, _ => False.elim ha

end Shallot.MacroPeg.CBV.GuardedWordSelection
