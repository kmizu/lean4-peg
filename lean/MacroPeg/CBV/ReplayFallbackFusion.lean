import MacroPeg.CBV.ScannerPairFusion

/-! Keep the capture-independent fallback at the caller's original position.
A source rule has body `(x B) / C`; its target has an advanced arity-one B
rule and an arity-zero C rule called after restoring the original position.
This removes unconditional leading replay from this recursive source family. -/
namespace Shallot.MacroPeg.CBV.ReplayFallbackFusion

mutual
  def Closed : MExp → Prop
    | .call _ args => ClosedArgs args
    | .seq a b | .alt a b => Closed a ∧ Closed b
    | .star a | .notP a => Closed a
    | .eps | .any | .chr _ | .range _ _ | .lit _ => True
    | _ => False
  def ClosedArgs : List MExp → Prop
    | [] => True
    | a::args => Closed a ∧ ClosedArgs args
end

mutual
  theorem closed_firstOrder : ∀ e, Closed e → e.FirstOrder
    | .call _ args, h => closedArgs_firstOrder args h
    | .seq a b, h | .alt a b, h => ⟨closed_firstOrder a h.1,closed_firstOrder b h.2⟩
    | .star a, h | .notP a, h => closed_firstOrder a h
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
    | .param _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h
  theorem closedArgs_firstOrder : ∀ args, ClosedArgs args → MExp.FirstOrderArgs args
    | [], _ => trivial
    | a::args, h => ⟨closed_firstOrder a h.1,closedArgs_firstOrder args h.2⟩
end

mutual
  theorem subst_closed (P : List MExp) : ∀ e, Closed e → MExp.subst P e = e
    | .call i args, h => by simp only [MExp.subst,substArgs_closed P args h]
    | .seq a b, h | .alt a b, h => by simp only [MExp.subst,subst_closed P a h.1,subst_closed P b h.2]
    | .star a, h | .notP a, h => by simp only [MExp.subst,subst_closed P a h]
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
    | .param _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h
  theorem substArgs_closed (P : List MExp) : ∀ args, ClosedArgs args → MExp.substArgs P args = args
    | [], _ => rfl
    | a::args, h => by simp only [MExp.substArgs,subst_closed P a h.1,substArgs_closed P args h.2]
end

theorem closed_env (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (e : MExp) (he : Closed e) (E : List (List Char)) (p : Nat) :
    evV g x s T E e p = evV g x s T [] e p := by
  have h := evV_subst (g := g) (x := x) (s := s) (T := T) (E := []) E e (closed_firstOrder e he) p
  rw [subst_closed _ e he] at h
  exact h.symm

structure Spec where
  tail : MExp
  fallback : MExp

def Valid (r : Spec) : Prop := r.tail.FirstOrder ∧ Closed r.fallback

def parGrammar (specs : List Spec) : MGrammar :=
  ⟨specs.map (fun r => ⟨1,.alt (.seq (.param 0) r.tail) r.fallback⟩)⟩

def render (specs : List Spec) : MExp → MExp
  | .call i [a] => match specs[i]? with
    | none => MExp.failAlways
    | some _ => .seq (.andP (render specs a))
        (.alt (.call (2*i) [render specs a]) (.call (2*i+1) []))
  | .call _ _ => MExp.failAlways
  | .param k => .param k
  | .seq a b => .seq (render specs a) (render specs b)
  | .alt a b => .alt (render specs a) (render specs b)
  | .star a => .star (render specs a)
  | .notP a => .notP (render specs a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder (specs : List Spec) : ∀ e, (render specs e).FirstOrder
  | .call i [a] => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some r => exact ⟨render_firstOrder specs a,⟨⟨render_firstOrder specs a,True.intro⟩,True.intro⟩⟩
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder specs a,render_firstOrder specs b⟩
  | .star a | .notP a => render_firstOrder specs a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem render_closed (specs : List Spec) : ∀ e, Closed e → Closed (render specs e)
  | .call i [a], h => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some r => exact ⟨render_closed specs a h.1,⟨⟨render_closed specs a h.1,True.intro⟩,True.intro⟩⟩
  | .call _ [], _ | .call _ (_::_::_), _ => trivial
  | .seq a b, h | .alt a b, h => ⟨render_closed specs a h.1,render_closed specs b h.2⟩
  | .star a, h | .notP a, h => render_closed specs a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

def targetRule (specs : List Spec) (main : Bool) (r : Spec) : MRule :=
  if main then ⟨1,render specs r.tail⟩ else ⟨0,render specs r.fallback⟩

def seqGrammar (specs : List Spec) : MGrammar :=
  ⟨specs.flatMap (fun r => [targetRule specs true r,targetRule specs false r])⟩

theorem par_rule (specs : List Spec) (i : Nat) :
    ruleAtM (parGrammar specs).rules i =
      (specs[i]?).map (fun r => ⟨1,.alt (.seq (.param 0) r.tail) r.fallback⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

private theorem pair_lookup (entries all : List Spec) (main : Bool) (i : Nat) :
    (entries.flatMap (fun r => [targetRule all true r,targetRule all false r]))[2*i + (if main then 0 else 1)]? =
      (entries[i]?).map (targetRule all main) := by
  induction entries generalizing i with
  | nil => simp
  | cons r entries ih =>
    cases i with
    | zero => cases main <;> rfl
    | succ i =>
      have hn : 2*(i+1)+(if main then 0 else 1) = (2*i+(if main then 0 else 1))+2 := by omega
      rw [hn]
      simpa only [List.flatMap_cons,List.cons_append,List.nil_append,
        List.getElem?_cons_succ,List.getElem?_cons_zero,Nat.add_succ,Nat.add_zero] using ih i

theorem seq_rule (specs : List Spec) (main : Bool) (i : Nat) :
    ruleAtM (seqGrammar specs).rules (2*i+(if main then 0 else 1)) =
      (specs[i]?).map (targetRule specs main) := by
  simpa only [seqGrammar,ruleAtM_eq_getElem?] using pair_lookup specs specs main i

theorem par_firstOrder {specs : List Spec} (hf : ∀ r ∈ specs, Valid r) : (parGrammar specs).FirstOrder := by
  intro r hr
  change r ∈ specs.map (fun r => ⟨1,.alt (.seq (.param 0) r.tail) r.fallback⟩) at hr
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨True.intro,(hf src hsrc).1⟩,closed_firstOrder _ (hf src hsrc).2⟩

theorem seq_firstOrder (specs : List Spec) : (seqGrammar specs).FirstOrder := by
  intro r hr
  obtain ⟨r,_,hmem⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl <;> exact render_firstOrder _ _

/-- Ordered choice of partial results: undefined does not select fallback. -/
def orElse (a b : Res) : Res := match a with
  | some none => b
  | other => other

def Shifted (specs : List Spec) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i r, specs[i]? = some r → ∀ w p q, p ≤ x.length → q ≤ x.length →
    sfx x p = w ++ sfx x q →
    valAt (T i [w]) p = orElse (valAt (U (2*i) [w]) q) (valAt (U (2*i+1) []) p)


/-- The caller retains its original position for the capture-free fallback. -/
theorem evaluator_of_shift {specs : List Spec} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hT : SoundTV (parGrammar specs) x .callByValuePar T)
    (hOk : OkTV x.length T) (hshift : Shifted specs x T U) :
    ∀ e, e.FirstOrder → ∀ E p, p ≤ x.length →
      evV (parGrammar specs) x .callByValuePar T E e p =
        evV (seqGrammar specs) x .callByValueSeq U E (render specs e) p
  | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
  | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _ | .callParam _ _, hf, _, _, _
  | .invoke _ _ _, hf, _, _, _ => False.elim hf
  | .call i [], hf, E, p, hp | .call i (_::_::_), hf, E, p, hp => by
    cases hr : specs[i]? <;> simp [render,evV,par_rule,hr,MExp.failAlways]
  | .call i [a], hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
    cases hr : specs[i]? with
    | none => simp [render,evV,par_rule,hr,MExp.failAlways]
    | some r =>
      have hpar : ruleAtM (parGrammar specs).rules i = some ⟨1,.alt (.seq (.param 0) r.tail) r.fallback⟩ := by
        rw [par_rule,hr]; rfl
      have hmain : ruleAtM (seqGrammar specs).rules (2*i) = some ⟨1,render specs r.tail⟩ := by
        simpa only [if_true,Nat.add_zero,hr,Option.map_some,targetRule] using seq_rule specs true i
      have hfall : ruleAtM (seqGrammar specs).rules (2*i+1) = some ⟨0,render specs r.fallback⟩ := by
        simpa only [Bool.false_eq_true,if_false,hr,Option.map_some,targetRule] using seq_rule specs false i
      simp only [render,hr]
      rw [evV_call_par hpar rfl (by decide)]
      have hguard : evV (seqGrammar specs) x .callByValueSeq U E (.andP (render specs a)) p =
          CallLookahead.peek p (evV (parGrammar specs) x .callByValuePar T E a p) := by
        rw [CallLookahead.evV_peek,← heq]
      cases hv : evV (parGrammar specs) x .callByValuePar T E a p with
      | none =>
        rw [evPar_cons_none hv,evV_seq_none (hguard.trans (by rw [hv]; rfl))]
      | some result => cases result with
        | none =>
          rw [evPar_cons_fail hv,evV_seq_fail (hguard.trans (by rw [hv]; rfl))]
        | some q =>
          rw [evPar_cons_ok hv,evV_seq_ok (hguard.trans (by rw [hv]; rfl))]
          have hargs : evSeqArgs (seqGrammar specs) x .callByValueSeq U E [render specs a] p =
              some (some ([pre x p q],q)) := by
            rw [evSeq_cons_ok (heq.symm.trans hv)]
            rfl
          change valAt (T i [pre x p q]) p = _
          change _ = match evV (seqGrammar specs) x .callByValueSeq U E (.call (2*i) [render specs a]) p with
            | some none => evV (seqGrammar specs) x .callByValueSeq U E (.call (2*i+1) []) p
            | other => other
          rw [evV_call_seq hmain rfl,hargs,evV_call_seq hfall rfl]
          obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix hT E a hf.1 p q hp hv
          exact hshift i r hr (pre x p q) p q hp hq hs
  | .seq a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
    cases hv : evV (parGrammar specs) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv]; exact (evV_seq_none (heq.symm.trans hv)).symm
    | some result => cases result with
      | none => rw [evV_seq_fail hv]; exact (evV_seq_fail (heq.symm.trans hv)).symm
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b hf.2 E q (evV_ok hOk a p hp q hv)
  | .alt a b, hf, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
    cases hv : evV (parGrammar specs) x .callByValuePar T E a p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b hf.2 E p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, hf, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift hT hOk hshift a hf E p hp]
  | .star a, hf, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hshift a hf E q (by omega))


/-- User-table correspondence, including the caller-position fallback, is
proved for every recursion depth rather than assumed as a call interface. -/
theorem tables_shifted {specs : List Spec} (hf : ∀ r ∈ specs, Valid r)
    (x : List Char) (k : Nat) :
    Shifted specs x (tblV (parGrammar specs) x .callByValuePar k)
      (tblV (seqGrammar specs) x .callByValueSeq k) := by
  induction k with
  | zero => intro i r hr w p q hp hq hs; simp [tblV,valAt_nil,orElse]
  | succ k ih =>
    intro i r hr w p q hp hq hs
    have hv := hf r (List.mem_of_getElem? hr)
    have hpar : ruleAtM (parGrammar specs).rules i = some ⟨1,.alt (.seq (.param 0) r.tail) r.fallback⟩ := by
      rw [par_rule,hr]; rfl
    have hmain : ruleAtM (seqGrammar specs).rules (2*i) = some ⟨1,render specs r.tail⟩ := by
      simpa only [if_true,Nat.add_zero,hr,Option.map_some,targetRule] using seq_rule specs true i
    have hfall : ruleAtM (seqGrammar specs).rules (2*i+1) = some ⟨0,render specs r.fallback⟩ := by
      simpa only [Bool.false_eq_true,if_false,hr,Option.map_some,targetRule] using seq_rule specs false i
    rw [valAt_tblV_succ hpar [w] hp,valAt_tblV_succ hmain [w] hq,valAt_tblV_succ hfall [] hp]
    have hmainEq := evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) k)
      (tblV_ok _ _ _ k) ih r.tail hv.1 [w] q hq
    have hfallEq := evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) k)
      (tblV_ok _ _ _ k) ih r.fallback (closed_firstOrder _ hv.2) [w] p hp
    rw [closed_env _ _ _ _ _ (render_closed specs r.fallback hv.2) [w] p] at hfallEq
    have hstrip := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr hs
    have hpre : evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k)
        [w] (.seq (.param 0) r.tail) p =
      evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k) [w] r.tail q := by
      simp only [evV,List.getElem?_cons_zero,hstrip,length_sfx x hq]
    change (match evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k)
      [w] (.seq (.param 0) r.tail) p with
      | some none => evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k) [w] r.fallback p
      | other => other) = _
    rw [hpre,hmainEq,hfallEq]
    rfl

theorem evaluator_eq {specs : List Spec} (hf : ∀ r ∈ specs, Valid r)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar specs) x .callByValuePar (tblV (parGrammar specs) x .callByValuePar k) E e p =
      evV (seqGrammar specs) x .callByValueSeq (tblV (seqGrammar specs) x .callByValueSeq k) E (render specs e) p :=
  evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) k) (tblV_ok _ _ _ k)
    (tables_shifted hf x k) e he E p hp

theorem decide_eq {specs : List Spec} (hf : ∀ r ∈ specs, Valid r)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (parGrammar specs) x e =
      decideObsV .callByValueSeq (seqGrammar specs) x (render specs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (parGrammar specs) (seqGrammar specs) x .callByValuePar .callByValueSeq
    e (render specs e) (fun k => evaluator_eq hf x k [] e he x.length (Nat.le_refl _))]

/-- A fixed Seq grammar preserves every original-string observation, even
when the successful fallback returns before the original capture endpoint. -/
theorem observations_iff {specs : List Spec} (hf : ∀ r ∈ specs, Valid r)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar specs) .callByValuePar e x r ↔
      SObs (seqGrammar specs) .callByValueSeq (render specs e) x r := by
  rw [← decideObsV_iff (par_firstOrder hf) (by decide) he,
    ← decideObsV_iff (seq_firstOrder specs) (by decide) (render_firstOrder specs e),decide_eq hf e he x]

theorem language_translation {specs : List Spec} (hf : ∀ r ∈ specs, Valid r)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar specs) .callByValuePar e x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar specs,render specs e,seq_firstOrder specs,render_firstOrder specs e,
    fun x => observations_iff hf e he x (some [])⟩


/-- The argument captures all of `ab`, but the fallback returns with `b`
remaining. Both sides do so after one actual user-table round. -/
theorem fallback_returns_before_capture :
    let specs : List Spec := [⟨MExp.failAlways,.chr 'a'⟩]
    let e : MExp := .call 0 [.lit ['a','b']]
    evV (parGrammar specs) ['a','b'] .callByValuePar
      (tblV (parGrammar specs) ['a','b'] .callByValuePar 1) [] e 2 = some (some 1) ∧
    evV (seqGrammar specs) ['a','b'] .callByValueSeq
      (tblV (seqGrammar specs) ['a','b'] .callByValueSeq 1) [] (render specs e) 2 = some (some 1) := by
  decide

end Shallot.MacroPeg.CBV.ReplayFallbackFusion
