import MacroPeg.CBV.MixedControlFusion
import MacroPeg.CBV.SequenceArgumentDomain

/-! Select word expressions from finite argument syntax, not from a palette
of runtime strings. All guards restore the original caller position. -/
namespace Shallot.MacroPeg.CBV.SymbolicWordSelection
open SequenceArguments (Arg)
open WordArguments (Word value word_eval value_of_success)

def selectAt (before : MExp) : MExp → (MExp → MExp) → MExp
  | .lit w, K => .seq (.andP (.seq before (.lit w))) (K (.lit w))
  | .param k, K => .seq (.andP (.seq before (.param k))) (K (.param k))
  | .alt a b, K => RootObservation.branch (.andP (.seq before a)) (selectAt before a K) (selectAt before b K)
  | .seq a b, K => selectAt before a (fun u => selectAt (.seq before u) b (fun v => K (.seq u v)))
  | _, _ => MExp.failAlways

def select (a : MExp) (K : MExp → MExp) : MExp := selectAt (.lit []) a K

theorem arg_equiv (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (a : MExp) (ha : Arg a) (p : Nat) :
    evV g x s T E a p = evV h x t U E a p := by
  exact (SequenceArguments.erase_eval g h x s t T U E a ha p).trans
    (SequenceArguments.erase_eval h h x t t U U E a ha p).symm

theorem probe_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char))
    (before : MExp) (hbefore : Word before) (u : List Char) (hu : value E before = some u)
    (a : MExp) (ha : Arg a) (p q : Nat) (hq : q ≤ x.length)
    (hs : sfx x p = u++sfx x q) :
    evV h x t U E (.seq before a) p = evV g x s T E a q := by
  have hb : evV h x t U E before p = some (some q) := by
    rw [word_eval h x t U E before hbefore p,hu]
    simp only [WordArguments.literal,evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hs,length_sfx x hq]
  rw [evV_seq_ok hb]
  exact (arg_equiv g h x s t T U E a ha q).symm

theorem word_arg : ∀ a, Word a → Arg a
  | .lit _, _ | .param _, _ => trivial
  | .seq a b, h => ⟨word_arg a h.1,word_arg b h.2⟩
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .alt _ _, h | .star _, h | .notP _, h
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

/-- A continuation depends on the selected word value, not its syntax. -/
def Respects (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (E : List (List Char)) (p q : Nat) (K : MExp → MExp) (f : List Char → Res) : Prop :=
  ∀ a, Word a → ∀ w, value E a = some w → (∃ rest, sfx x q = w++rest) → evV g x s T E (K a) p = f w

private theorem word_select_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char))
    (before : MExp) (hbefore : Word before) (u : List Char) (hu : value E before = some u)
    (a : MExp) (ha : Word a) (p q : Nat) (hq : q ≤ x.length) (hs : sfx x p = u++sfx x q)
    (K : MExp → MExp) (f : List Char → Res) (hK : Respects h x t U E p q K f) :
    evV h x t U E (.seq (.andP (.seq before a)) (K a)) p =
      match evV g x s T E a q with | some (some j) => f (pre x q j) | other => other := by
  have hg : evV h x t U E (.andP (.seq before a)) p = CallLookahead.peek p (evV g x s T E a q) := by
    rw [CallLookahead.evV_peek,probe_eval g h x s t T U E before hbefore u hu a (word_arg a ha) p q hq hs]
  cases hv : evV g x s T E a q with
  | none => rw [evV_seq_none (hg.trans (by rw [hv]; rfl))]
  | some r => cases r with
    | none => rw [evV_seq_fail (hg.trans (by rw [hv]; rfl))]
    | some j =>
      rw [evV_seq_ok (hg.trans (by rw [hv]; rfl))]
      obtain ⟨hj,hpre⟩ := SequenceArguments.success_prefix g x s T E a (word_arg a ha) q j hq hv
      exact hK a ha _ (value_of_success g x s T E a ha q j hq hv) ⟨sfx x j,hpre⟩

theorem selectAt_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (p : Nat) :
    ∀ a, Arg a → ∀ before, Word before → ∀ u, value E before = some u →
      ∀ q, q ≤ x.length → sfx x p = u++sfx x q → ∀ K f, Respects h x t U E p q K f →
      evV h x t U E (selectAt before a K) p =
        match evV g x s T E a q with | some (some j) => f (pre x q j) | other => other
  | .lit w, _, before, hb, u, hu, q, hq, hs, K, f, hK =>
    word_select_eval g h x s t T U E before hb u hu (.lit w) trivial p q hq hs K f hK
  | .param k, _, before, hb, u, hu, q, hq, hs, K, f, hK =>
    word_select_eval g h x s t T U E before hb u hu (.param k) trivial p q hq hs K f hK
  | .alt a b, ha, before, hb, u, hu, q, hq, hs, K, f, hK => by
    rw [selectAt,ChoiceArguments.branch_eval,probe_eval g h x s t T U E before hb u hu a ha.1 p q hq hs]
    cases hv : evV g x s T E a q with
    | none => simp [evV,hv]
    | some r => cases r with
      | none => simpa only [evV,hv] using selectAt_eval g h x s t T U E p b ha.2 before hb u hu q hq hs K f hK
      | some j => simpa only [evV,hv] using selectAt_eval g h x s t T U E p a ha.1 before hb u hu q hq hs K f hK
  | .seq a b, ha, before, hb, u, hu, q, hq, hs, K, f, hK => by
    rw [selectAt]
    have hcont : Respects h x t U E p q
        (fun v => selectAt (.seq before v) b (fun w => K (.seq v w)))
        (fun v => match evV g x s T E b (q-v.length) with
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
      refine selectAt_eval g h x s t T U E p b ha.2 (.seq before v) ⟨hb,hv⟩ (u++word)
        (by simp [value,hu,hword]) (q-word.length) (by omega) hs'
        (fun z => K (.seq v z)) (fun word' => f (word++word')) ?_
      intro z hz word' hword' hprefix'
      apply hK (.seq v z) ⟨hv,hz⟩ (word++word') (by simp [value,hword,hword'])
      obtain ⟨rem,hrem'⟩ := hprefix'
      refine ⟨rem,?_⟩
      rw [hrest,← hrem,hrem',List.append_assoc]
    rw [selectAt_eval g h x s t T U E p a ha.1 before hb u hu q hq hs _ _ hcont]
    cases hv : evV g x s T E a q with
    | none => simp [evV,hv]
    | some r => cases r with
      | none => simp [evV,hv]
      | some j =>
        obtain ⟨hj,hpre⟩ := SequenceArguments.success_prefix g x s T E a ha.1 q j hq hv
        have hlen := congrArg List.length hpre
        simp only [length_sfx x hq,length_sfx x hj,List.length_append] at hlen
        have hpos : q-(pre x q j).length = j := by omega
        dsimp only []
        rw [hpos]
        simp only [evV_seq_ok hv]
        cases hvb : evV g x s T E b j with
        | none => rfl
        | some rb => cases rb with
          | none => rfl
          | some k =>
            obtain ⟨hk,hbpre⟩ := SequenceArguments.success_prefix g x s T E b ha.2 j k hj hvb
            dsimp only []
            rw [SequenceArguments.pre_concat hq hk hpre hbpre]
  | .eps, ha, _, _, _, _, _, _, _, _, _, _ | .any, ha, _, _, _, _, _, _, _, _, _, _
  | .chr _, ha, _, _, _, _, _, _, _, _, _, _ | .range _ _, ha, _, _, _, _, _, _, _, _, _, _
  | .call _ _, ha, _, _, _, _, _, _, _, _, _, _ | .star _, ha, _, _, _, _, _, _, _, _, _, _
  | .notP _, ha, _, _, _, _, _, _, _, _, _, _ | .dbg _, ha, _, _, _, _, _, _, _, _, _, _
  | .lam _ _, ha, _, _, _, _, _, _, _, _, _, _ | .callParam _ _, ha, _, _, _, _, _, _, _, _, _, _
  | .invoke _ _ _, ha, _, _, _, _, _, _, _, _, _, _ => False.elim ha


theorem select_eval (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (p : Nat) (hp : p ≤ x.length)
    (a : MExp) (ha : Arg a) (K : MExp → MExp) (f : List Char → Res)
    (hK : Respects h x t U E p p K f) :
    evV h x t U E (select a K) p =
      match evV g x s T E a p with | some (some j) => f (pre x p j) | other => other :=
  selectAt_eval g h x s t T U E p a ha (.lit []) trivial [] rfl p hp (by simp) K f hK


theorem selectAt_firstOrder : ∀ a, Arg a → ∀ before, Word before → ∀ K,
    (∀ w, Word w → (K w).FirstOrder) → (selectAt before a K).FirstOrder
  | .lit w, _, before, hb, K, hK => ⟨⟨WordArguments.word_firstOrder before hb,True.intro⟩,hK _ True.intro⟩
  | .param k, _, before, hb, K, hK => ⟨⟨WordArguments.word_firstOrder before hb,True.intro⟩,hK _ True.intro⟩
  | .alt a b, ha, before, hb, K, hK => by
    have hg : (MExp.seq before a).FirstOrder := ⟨WordArguments.word_firstOrder before hb,SequenceArguments.arg_firstOrder a ha.1⟩
    exact ⟨⟨hg,selectAt_firstOrder a ha.1 before hb K hK⟩,
      ⟨hg,selectAt_firstOrder b ha.2 before hb K hK⟩⟩
  | .seq a b, ha, before, hb, K, hK =>
    selectAt_firstOrder a ha.1 before hb _ (fun u hu =>
      selectAt_firstOrder b ha.2 (.seq before u) ⟨hb,hu⟩ _ (fun v hv => hK (.seq u v) ⟨hu,hv⟩))
  | .eps, ha, _, _, _, _ | .any, ha, _, _, _, _ | .chr _, ha, _, _, _, _ | .range _ _, ha, _, _, _, _
  | .call _ _, ha, _, _, _, _ | .star _, ha, _, _, _, _ | .notP _, ha, _, _, _, _ | .dbg _, ha, _, _, _, _
  | .lam _ _, ha, _, _, _, _ | .callParam _ _, ha, _, _, _, _ | .invoke _ _ _, ha, _, _, _, _ => False.elim ha

theorem select_firstOrder (a : MExp) (ha : Arg a) (K : MExp → MExp)
    (hK : ∀ w, Word w → (K w).FirstOrder) : (select a K).FirstOrder :=
  selectAt_firstOrder a ha (.lit []) True.intro K hK

end Shallot.MacroPeg.CBV.SymbolicWordSelection
