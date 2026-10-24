import MacroPeg.CBV.CodewordControlFilter

/-! Compare adjacent runtime codewords without moving the caller's retained
context into the comparison rule. -/
namespace Shallot.MacroPeg.CBV.AdjacentCodewordControl
open ClockFreezing (Table)

/-- Each word must match the input immediately following that word. -/
def Linked : List (List Char) → List Char → Prop
  | [], _ => True
  | w::ws, rest => w.IsPrefix (ws.flatten++rest) ∧ Linked ws rest

instance linkedDecidable : ∀ (ws : List (List Char)) (rest : List Char), Decidable (Linked ws rest)
  | [], _ => isTrue True.intro
  | w::ws, rest => by
    letI : Decidable (Linked ws rest) := linkedDecidable ws rest
    exact inferInstanceAs (Decidable (w.IsPrefix (ws.flatten++rest) ∧ Linked ws rest))

theorem linked_append (as bs : List (List Char)) (rest : List Char) :
    Linked (as++bs) rest ↔ Linked as (bs.flatten++rest) ∧ Linked bs rest := by
  induction as with
  | nil => simp [Linked]
  | cons a as ih => simp only [List.cons_append,Linked,List.flatten_append,List.append_assoc,ih,and_assoc]

theorem linked_uniform {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u) (ws : List (List Char)) (hw : ∀ w∈ws, C w)
    (rest : List Char) :
    Linked (u::ws) rest ↔ ws=List.replicate ws.length u ∧ u.IsPrefix rest := by
  induction ws generalizing u with
  | nil => simp [Linked]
  | cons v vs ih =>
    have hv : C v := hw v (by simp)
    have hvs : ∀ w∈vs, C w := fun w h => hw w (by simp [h])
    constructor
    · intro h
      have he : u=v := PrefixCodeCapture.prefix_identifies hc hu hv
        (by simpa only [List.flatten_cons,List.append_assoc] using h.1)
      subst v
      obtain ⟨hs,hr⟩ := (ih u hu hvs).mp h.2
      exact ⟨by change u::vs=u::List.replicate vs.length u; exact congrArg (List.cons u) hs,hr⟩
    · rintro ⟨h,hr⟩
      have he : v=u ∧ vs=List.replicate vs.length u := by
        simpa only [List.length_cons,List.replicate_succ,List.cons.injEq] using h
      rcases he with ⟨he,hs⟩
      subst v
      exact ⟨⟨vs.flatten++rest,by simp [List.flatten_cons,List.append_assoc]⟩,
        (ih u hu hvs).mpr ⟨hs,hr⟩⟩

theorem uniform_rotate (u : List Char) (ws : List (List Char))
    (h : ws=List.replicate ws.length u) : u++ws.flatten=ws.flatten++u := by
  calc
    u++ws.flatten=CodewordReplay.power u (ws.length+1) := by
      exact (congrArg (fun ls : List (List Char) => u++ls.flatten) h).trans
        (by simp only [CodewordReplay.power,List.replicate_succ,List.flatten_cons])
    _=ws.flatten++u := by
      rw [LastCodewordCandidate.power_succ_right]
      congr 1
      exact congrArg List.flatten h.symm

/-- The entire shifted replay is exactly the collection of adjacent
comparisons, including the final word's comparison with the remaining input. -/
theorem linked_replay {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (u : List Char) (hu : C u) (ws : List (List Char)) (hw : ∀ w∈ws, C w)
    (rest : List Char) :
    Linked (u::ws) rest ↔ (u++ws.flatten).IsPrefix (ws.flatten++rest) := by
  rw [linked_uniform hc u hu ws hw rest]
  constructor
  · rintro ⟨he,hr⟩
    rw [uniform_rotate u ws he]
    exact (List.prefix_append_right_inj ws.flatten).mpr hr
  · intro h
    have he := CodewordReplay.source_prefix_forces hc u ws rest hu hw h
    refine ⟨he,?_⟩
    rw [uniform_rotate u ws he] at h
    exact (List.prefix_append_right_inj ws.flatten).mp h

/-- Keep tests in the caller environment. The comparison expression must
only compare the current header with the immediately following bytes. -/
def filter (A compare : MExp) (d : CodewordControlFilter.Expr) : MExp :=
  .seq (.andP (CodewordControlFilter.render A d)) (match d with
    | .token => .seq (.andP compare) A
    | .eps => .eps
    | .test e => .andP e
    | .seq a b => .seq (filter A compare a) (filter A compare b)
    | .alt a b => RootObservation.branch (.andP (CodewordControlFilter.render A a))
        (filter A compare a) (filter A compare b)
    | .notP a => .notP (CodewordControlFilter.render A a)
    | .star a => .seq (.star (filter A compare a)) (.notP (CodewordControlFilter.render A a)))

theorem filter_firstOrder (A compare : MExp) (hA : A.FirstOrder) (hcompare : compare.FirstOrder) :
    ∀ d, (CodewordControlFilter.render A d).FirstOrder → (filter A compare d).FirstOrder
  | .token, h => ⟨h,hcompare,hA⟩
  | .eps, h => ⟨h,True.intro⟩
  | .test _, h => ⟨h,h⟩
  | .seq a b, h => ⟨h,filter_firstOrder A compare hA hcompare a h.1,
      filter_firstOrder A compare hA hcompare b h.2⟩
  | .alt a b, h => ⟨h,
      ⟨h.1,filter_firstOrder A compare hA hcompare a h.1⟩,
      h.1,filter_firstOrder A compare hA hcompare b h.2⟩
  | .notP _, h => ⟨h,h⟩
  | .star a, h => ⟨h,filter_firstOrder A compare hA hcompare a h,h⟩

theorem filter_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (A compare : MExp) (d : CodewordControlFilter.Expr) (p : Nat)
    (h : evV g x s T E (CodewordControlFilter.render A d) p=none) :
    evV g x s T E (filter A compare d) p=none := by
  rw [filter.eq_def]
  apply evV_seq_none
  rw [CallLookahead.evV_peek,h]
  rfl


theorem filter_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (A compare : MExp) (d : CodewordControlFilter.Expr) (p : Nat)
    (h : evV g x s T E (CodewordControlFilter.render A d) p=some none) :
    evV g x s T E (filter A compare d) p=some none := by
  rw [filter.eq_def]
  apply evV_seq_fail
  rw [CallLookahead.evV_peek,h]
  rfl

theorem success (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (E : List (List Char)) (compare : MExp)
    (hcompare : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) →
      evV g x s T E (.andP compare) p=
        if (pre x p q).IsPrefix (sfx x q) then some (some p) else some none)
    (hcode : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) → C (pre x p q)) :
    ∀ (d : CodewordControlFilter.Expr) p q, p≤x.length → evV g x s T E (CodewordControlFilter.render A d) p=some (some q) →
      ∃ ws : List (List Char), (∀ w∈ws, C w) ∧ sfx x p=ws.flatten++sfx x q ∧
        evV g x s T E (filter A compare d) p=
          if Linked ws (sfx x q) then some (some q) else some none := by
  intro d
  induction d with
  | token =>
    intro p q hp hv
    have hq : q≤x.length := evV_ok hOk A p hp q hv
    have hsf := (WordStarFilter.success_prefix hs hT E A hA p q hp hv).2
    refine ⟨[pre x p q],by simpa using hcode p q hp hv,by simpa using hsf,?_⟩
    rw [filter,evV_seq_ok (show evV g x s T E (.andP (CodewordControlFilter.render A .token)) p=some (some p) by
      rw [CallLookahead.evV_peek,hv]; rfl)]
    change (match evV g x s T E (.andP compare) p with
      | some (some j) => evV g x s T E A j | other => other)=_
    rw [hcompare p q hp hv]
    simp only [Linked,List.flatten_nil,List.nil_append,and_true]
    by_cases he : (pre x p q).IsPrefix (sfx x q)
    · rw [if_pos he,if_pos he]
      exact hv
    · rw [if_neg he,if_neg he]
  | eps =>
    intro p q hp hv
    have he : p=q := by simpa [CodewordControlFilter.render,evV] using hv
    subst q
    exact ⟨[],by simp,by simp,by simp [filter,CodewordControlFilter.render,Linked,evV,MExp.andP]⟩
  | test e =>
    intro p q hp hv
    have he : p=q := by rw [CodewordControlFilter.render,CallLookahead.evV_peek] at hv; cases hh : evV g x s T E e p with
      | none => simp [CallLookahead.peek,hh] at hv
      | some r => cases r with | none => simp [CallLookahead.peek,hh] at hv | some j => simpa [CallLookahead.peek,hh] using hv
    subst q
    refine ⟨[],by simp,by simp,?_⟩
    rw [filter,evV_seq_ok (show evV g x s T E (.andP (CodewordControlFilter.render A (.test e))) p=some (some p) by
      rw [CallLookahead.evV_peek,hv]; rfl)]
    exact hv
  | notP a ih =>
    intro p q hp hv
    have he : p=q := by
      change (match evV g x s T E (CodewordControlFilter.render A a) p with
        | some (some _) => some none | some none => some (some p) | none => none)=some (some q) at hv
      split at hv <;> simp_all
    subst q
    refine ⟨[],by simp,by simp,?_⟩
    rw [filter,evV_seq_ok (show evV g x s T E (.andP (CodewordControlFilter.render A (.notP a))) p=some (some p) by
      rw [CallLookahead.evV_peek,hv]; rfl)]
    exact hv
  | seq a b ia ib =>
    intro p q hp hv
    change (match evV g x s T E (CodewordControlFilter.render A a) p with
      | some (some j) => evV g x s T E (CodewordControlFilter.render A b) j | other => other)=_ at hv
    cases ha : evV g x s T E (CodewordControlFilter.render A a) p with
    | none => simp [ha] at hv
    | some result => cases result with
      | none => simp [ha] at hv
      | some j =>
        have hb : evV g x s T E (CodewordControlFilter.render A b) j=some (some q) := by simpa [ha] using hv
        have hj : j≤x.length := evV_ok hOk _ p hp j ha
        obtain ⟨as,hac,has,haf⟩ := ia p j hp ha
        obtain ⟨bs,hbc,hbs,hbf⟩ := ib j q hj hb
        refine ⟨as++bs,by intro w hw; exact (List.mem_append.mp hw).elim (hac w) (hbc w),
          by simpa [List.flatten_append,List.append_assoc,hbs] using has,?_⟩
        rw [filter,evV_seq_ok (show evV g x s T E (.andP (CodewordControlFilter.render A (.seq a b))) p=some (some p) by
          rw [CallLookahead.evV_peek]; change CallLookahead.peek p (evV g x s T E (.seq (CodewordControlFilter.render A a) (CodewordControlFilter.render A b)) p)=_
          rw [evV_seq_ok ha,hb]; rfl)]
        change (match evV g x s T E (filter A compare a) p with
          | some (some z) => evV g x s T E (filter A compare b) z | other => other)=_
        rw [haf]
        have hlink : Linked (as++bs) (sfx x q) ↔ Linked as (sfx x j) ∧ Linked bs (sfx x q) := by
          rw [linked_append,←hbs]
        by_cases he : Linked as (sfx x j)
        · rw [if_pos he]
          dsimp only []
          rw [hbf]
          congr 1
          exact propext ⟨fun h => hlink.mpr ⟨he,h⟩,fun h => (hlink.mp h).2⟩
        · rw [if_neg he,if_neg (fun h => he (hlink.mp h).1)]
  | alt a b ia ib =>
    intro p q hp hv
    have hpre : evV g x s T E (.andP (CodewordControlFilter.render A (.alt a b))) p=some (some p) := by
      rw [CallLookahead.evV_peek,hv]; rfl
    change (match evV g x s T E (CodewordControlFilter.render A a) p with
      | some none => evV g x s T E (CodewordControlFilter.render A b) p | other => other)=_ at hv
    cases ha : evV g x s T E (CodewordControlFilter.render A a) p with
    | none => simp [ha] at hv
    | some result => cases result with
      | none =>
        have hb : evV g x s T E (CodewordControlFilter.render A b) p=some (some q) := by simpa [ha] using hv
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
      have hpre : evV g x s T E (.andP (CodewordControlFilter.render A (.star a))) p=some (some p) := by
        rw [CallLookahead.evV_peek,hv]; rfl
      change evStar (fun z => evV g x s T E (CodewordControlFilter.render A a) z) p=some (some q) at hv
      cases ha : evV g x s T E (CodewordControlFilter.render A a) p with
      | none => rw [evStar_none ha] at hv; cases hv
      | some result => cases result with
        | none =>
          rw [evStar_fail ha] at hv
          have he : p=q := by simpa using hv
          subst q
          refine ⟨[],by simp,by simp,?_⟩
          have hf := filter_fail g x s T E A compare a p ha
          rw [filter,evV_seq_ok hpre]
          rw [evV_seq_ok (show evV g x s T E (.star (filter A compare a)) p=some (some p) from evStar_fail hf),evV_not_fail ha]
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
            have hfpre : evV g x s T E (.andP (CodewordControlFilter.render A (.star a))) j=some (some j) := by
              rw [CallLookahead.evV_peek]; change CallLookahead.peek j (evStar (fun z => evV g x s T E (CodewordControlFilter.render A a) z) j)=_
              rw [hv]; rfl
            rw [filter,evV_seq_ok hfpre] at hbf
            have hlink : Linked (as++bs) (sfx x q) ↔ Linked as (sfx x j) ∧ Linked bs (sfx x q) := by
              rw [linked_append,←hbs]
            by_cases he : Linked as (sfx x j)
            · rw [if_pos he] at haf
              change (match evStar (fun z => evV g x s T E (filter A compare a) z) p with
                | some (some z) => evV g x s T E (.notP (CodewordControlFilter.render A a)) z | other => other)=_
              rw [evStar_ok haf hjp]
              change evV g x s T E (.seq (.star (filter A compare a)) (.notP (CodewordControlFilter.render A a))) j=_
              rw [hbf]
              congr 1
              exact propext ⟨fun h => hlink.mpr ⟨he,h⟩,fun h => (hlink.mp h).2⟩
            · rw [if_neg he] at haf
              rw [evV_seq_ok (show evV g x s T E (.star (filter A compare a)) p=some (some p) from evStar_fail haf),evV_not_ok ha]
              rw [if_neg (fun h => he (hlink.mp h).1)]
          · rw [evStar_stuck ha hjp] at hv; cases hv

/-- The adjacent comparator is an ordinary unary Seq rule. Its body only
replays its own new capture; it never receives the caller's parameters. -/
theorem physical_compare (g : MGrammar) (x : List Char) (i k : Nat)
    (hr : ruleAtM g.rules i=some ⟨1,.param 0⟩) (E : List (List Char))
    (A : MExp) (p q : Nat) (hp : p≤x.length)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1)) E A p=some (some q)) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1)) E (.andP (.call i [A])) p=
      if (pre x p q).IsPrefix (sfx x q) then some (some p) else some none := by
  have hq := evV_ok (tblV_ok g x .callByValueSeq (k+1)) A p hp q ha
  rw [CallLookahead.evV_peek,evV_call_seq hr rfl]
  simp only [evSeqArgs,ha]
  rw [valAt_tblV_succ hr _ hq]
  simp only [evV,List.getElem?_cons_zero]
  cases hh : Shallot.stripPrefix? (pre x p q) (sfx x q) with
  | none =>
    have hn : ¬(pre x p q).IsPrefix (sfx x q) := by
      rintro ⟨rest,he⟩
      have hv : Shallot.stripPrefix? (pre x p q) (sfx x q)=some rest :=
        (CBVtoCBN.stripPrefix_exact _ _ _).mpr he.symm
      rw [hh] at hv
      cases hv
    rw [if_neg hn]
    rfl
  | some rest =>
    have hy : (pre x p q).IsPrefix (sfx x q) :=
      ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩
    rw [if_pos hy]
    rfl

/-- On a successful original argument, adjacent filtering selects the
same endpoint and checks the shifted replay of the entire capture. -/
theorem argument_checks (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (E : List (List Char)) (compare : MExp)
    (hcompare : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) →
      evV g x s T E (.andP compare) p=
        if (pre x p q).IsPrefix (sfx x q) then some (some p) else some none)
    (hcode : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) → C (pre x p q))
    (d : CodewordControlFilter.Expr) (p j q : Nat) (hp : p≤x.length)
    (ha : evV g x s T E A p=some (some j))
    (hd : evV g x s T E (CodewordControlFilter.render A d) j=some (some q)) :
    evV g x s T E (filter A compare (.seq .token d)) p=
      if (pre x p j++pre x j q).IsPrefix (sfx x j) then some (some q) else some none := by
  have hj := evV_ok hOk A p hp j ha
  have hq := evV_ok hOk _ j hj q hd
  obtain ⟨ws,hw,htrace,hf⟩ := success g x s hs T hT hOk A hA hc E compare hcompare hcode d j q hj hd
  have hpw : pre x j q=ws.flatten := by
    simpa only [length_sfx x hj,length_sfx x hq] using pre_eq (sfx_is_suffix x j) htrace
  have hb : evV g x s T E (CodewordControlFilter.render A (.seq .token d)) p=some (some q) :=
    evV_seq_ok ha |>.trans hd
  rw [filter,evV_seq_ok (show evV g x s T E
    (.andP (CodewordControlFilter.render A (.seq .token d))) p=some (some p) by
      rw [CallLookahead.evV_peek,hb]; rfl)]
  have ht : evV g x s T E (filter A compare .token) p=
      if (pre x p j).IsPrefix (sfx x j) then some (some j) else some none := by
    rw [filter,evV_seq_ok (show evV g x s T E
      (.andP (CodewordControlFilter.render A .token)) p=some (some p) by
        rw [CallLookahead.evV_peek,CodewordControlFilter.render,ha]; rfl)]
    change (match evV g x s T E (.andP compare) p with
      | some (some z) => evV g x s T E A z | other => other)=_
    rw [hcompare p j hp ha]
    by_cases he : (pre x p j).IsPrefix (sfx x j) <;> simp [he,ha]
  change (match evV g x s T E (filter A compare .token) p with
    | some (some z) => evV g x s T E (filter A compare d) z | other => other)=_
  rw [ht]
  have he : Linked (pre x p j::ws) (sfx x q) ↔
      (pre x p j++pre x j q).IsPrefix (sfx x j) := by
    rw [linked_replay hc _ (hcode p j hp ha) ws hw,hpw,htrace]
  simp only [←he]
  by_cases hh : (pre x p j).IsPrefix (sfx x j)
  · rw [if_pos hh]
    dsimp only []
    rw [hf]
    have hz : Linked (pre x p j::ws) (sfx x q) ↔ Linked ws (sfx x q) := by
      simp only [Linked,←htrace,hh,true_and]
    simp only [hz]
  · rw [if_neg hh]
    have hn : ¬Linked (pre x p j::ws) (sfx x q) := by
      intro h
      exact hh (by simpa only [←htrace] using h.1)
    rw [if_neg hn]

/-- Comparison runs in the original caller environment E. The continuation
retains the same whole source capture through its two consecutive parts. -/
theorem entry (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : Table) (hT : SoundTV g x s T) (hOk : OkTV x.length T)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (E : List (List Char)) (compare : MExp)
    (hcompare : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) →
      evV g x s T E (.andP compare) p=
        if (pre x p q).IsPrefix (sfx x q) then some (some p) else some none)
    (hcode : ∀ p q, p≤x.length → evV g x s T E A p=some (some q) → C (pre x p q))
    (d : CodewordControlFilter.Expr) (p j q : Nat) (hp : p≤x.length)
    (ha : evV g x s T E A p=some (some j))
    (hd : evV g x s T E (CodewordControlFilter.render A d) j=some (some q))
    (b : MExp) (hb : b.FirstOrder) :
    evV g x s T [pre x p j++pre x j q] (.seq (.param 0) b) j=
      match evV g x s T E (filter A compare (.seq .token d)) p with
      | some (some _) => evV g x s T [pre x p j,pre x j q]
          (.seq (.param 0) (CodewordControlFilter.wholeView b)) q
      | other => other := by
  rw [argument_checks g x s hs T hT hOk A hA hc E compare hcompare hcode d p j q hp ha hd]
  have hj := evV_ok hOk A p hp j ha
  have hq := evV_ok hOk _ j hj q hd
  obtain ⟨ws,hw,htrace,_⟩ := success g x s hs T hT hOk A hA hc E compare hcompare hcode d j q hj hd
  have hpw : pre x j q=ws.flatten := by
    simpa only [length_sfx x hj,length_sfx x hq] using pre_eq (sfx_is_suffix x j) htrace
  by_cases he : (pre x p j++pre x j q).IsPrefix (sfx x j)
  · rw [if_pos he]
    have hew : (pre x p j++ws.flatten).IsPrefix (ws.flatten++sfx x q) := by
      simpa only [hpw,htrace] using he
    have hu := hcode p j hp ha
    have huniform := CodewordReplay.source_prefix_forces hc (pre x p j) ws (sfx x q) hu hw hew
    have hr := CodewordControlFilter.replay_trace g x s T hc (pre x p j) hu ws hw j q hq htrace b hb
    rw [if_pos huniform] at hr
    simpa only [hpw] using hr
  · rw [if_neg he]
    have hn : Shallot.stripPrefix? (pre x p j++pre x j q) (sfx x j)=none := by
      cases hh : Shallot.stripPrefix? (pre x p j++pre x j q) (sfx x j) with
      | none => rfl
      | some rest => exact False.elim (he ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩)
    apply evV_seq_fail
    simp only [evV,List.getElem?_cons_zero,hn]

/-- Actual ordinary Seq tables discharge the comparator premise, for every
retained caller environment and every positive stage. -/
theorem physical_entry (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (i k : Nat)
    (hr : ruleAtM g.rules i=some ⟨1,.param 0⟩)
    (A : MExp) (hA : A.FirstOrder) {C : List Char → Prop} (hc : PrefixCodeCapture.PrefixFree C)
    (E : List (List Char))
    (hcode : ∀ p q, p≤x.length →
      evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1)) E A p=some (some q) → C (pre x p q))
    (d : CodewordControlFilter.Expr) (p j q : Nat) (hp : p≤x.length)
    (ha : evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1)) E A p=some (some j))
    (hd : evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1)) E
      (CodewordControlFilter.render A d) j=some (some q))
    (b : MExp) (hb : b.FirstOrder) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1))
      [pre x p j++pre x j q] (.seq (.param 0) b) j=
      match evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1)) E
        (filter A (.call i [A]) (.seq .token d)) p with
      | some (some _) => evV g x .callByValueSeq (tblV g x .callByValueSeq (k+1))
          [pre x p j,pre x j q] (.seq (.param 0) (CodewordControlFilter.wholeView b)) q
      | other => other :=
  entry g x .callByValueSeq (by decide) _ (tblV_sound hg (by decide) _) (tblV_ok _ _ _ _)
    A hA hc E (.call i [A]) (physical_compare g x i k hr E A) hcode d p j q hp ha hd b hb

end Shallot.MacroPeg.CBV.AdjacentCodewordControl
