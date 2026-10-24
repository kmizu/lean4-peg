import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.RootObservation

/-! Move rule-body lookahead to Seq call sites while retaining argument
consumption. A successful call probe is followed by re-evaluation of its
arguments. This is a whole-grammar Seq transformation, not a Par-to-Seq
translation or a finite restriction on captured runtime strings. -/
namespace Shallot.MacroPeg.CBV.SequentialCallLookahead
open CallLookahead (tested tested_rule tested_firstOrder peek evV_peek Peeked)

def sequenceArgs : List MExp → MExp
  | [] => .eps
  | a :: args => .seq a (sequenceArgs args)

def consumed : Option (Option (List (List Char) × Nat)) → Res
  | some (some (_,q)) => some (some q)
  | some none => some none
  | none => none

theorem sequenceArgs_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (args : List MExp) (p : Nat) :
    evV g x s T E (sequenceArgs args) p = consumed (evSeqArgs g x s T E args p) := by
  induction args generalizing p with
  | nil => rfl
  | cons a args ih =>
    simp only [sequenceArgs,evV,evSeqArgs]
    cases hv : evV g x s T E a p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some q =>
        simp only []
        rw [ih]
        cases ht : evSeqArgs g x s T E args q with
        | none => rfl
        | some r => cases r with
          | none => rfl
          | some Wq => cases Wq; rfl

theorem sequenceArgs_firstOrder : ∀ args, MExp.FirstOrderArgs args → (sequenceArgs args).FirstOrder
  | [], _ => trivial
  | _::args, h => ⟨h.1,sequenceArgs_firstOrder args h.2⟩

mutual
  def render : MExp → MExp
    | .call i args => .seq (.andP (.call i (renderArgs args))) (sequenceArgs (renderArgs args))
    | .seq a b => .seq (render a) (render b)
    | .alt a b => .alt (render a) (render b)
    | .star a => .star (render a)
    | .notP a => .notP (render a)
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range lo hi => .range lo hi
    | .lit w => .lit w
    | .param k => .param k
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways
  def renderArgs : List MExp → List MExp
    | [] => []
    | a::args => render a :: renderArgs args
end

mutual
  theorem render_firstOrder : ∀ e, (render e).FirstOrder
    | .call _ args => ⟨renderArgs_firstOrder args,sequenceArgs_firstOrder _ (renderArgs_firstOrder args)⟩
    | .seq a b | .alt a b => ⟨render_firstOrder a,render_firstOrder b⟩
    | .star a | .notP a => render_firstOrder a
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
  theorem renderArgs_firstOrder : ∀ args, MExp.FirstOrderArgs (renderArgs args)
    | [] => trivial
    | a::args => ⟨render_firstOrder a,renderArgs_firstOrder args⟩
end

theorem renderArgs_length (args : List MExp) : (renderArgs args).length = args.length := by
  induction args <;> simp_all [renderArgs]

def wrapped (g : MGrammar) : MGrammar := ⟨g.rules.map (fun r => ⟨r.arity,render r.body⟩)⟩

theorem wrapped_rule (g : MGrammar) (i : Nat) :
    ruleAtM (wrapped g).rules i = (ruleAtM g.rules i).map (fun r => ⟨r.arity,render r.body⟩) := by
  simp [wrapped,ruleAtM_eq_getElem?]

theorem wrapped_firstOrder (g : MGrammar) : (wrapped g).FirstOrder := by
  intro r hr
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder src.body

mutual
  theorem evaluator_of_peek {g : MGrammar} {x : List Char} {T U : Nat → List (List Char) → Val}
      (hOk : OkTV x.length T) (hpeek : Peeked g x T U) :
      ∀ e : MExp, e.FirstOrder → ∀ E p, p ≤ x.length →
        evV (tested g) x .callByValueSeq T E e p =
          evV (wrapped g) x .callByValueSeq U E (render e) p
    | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
    | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
    | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _
    | .callParam _ _, hf, _, _, _ | .invoke _ _ _, hf, _, _, _ => False.elim hf
    | .call i args, hf, E, p, hp => by
      have hargs := arguments_of_peek hOk hpeek args hf E p hp
      have hseq := sequenceArgs_eval (wrapped g) x .callByValueSeq U E (renderArgs args) p
      rw [← hargs] at hseq
      cases hr : ruleAtM g.rules i with
      | none => simp [render,evV,tested_rule,wrapped_rule,hr,MExp.andP]
      | some r =>
        by_cases ha : r.arity = args.length
        · have ht : ruleAtM (tested g).rules i = some ⟨r.arity,.andP r.body⟩ := by rw [tested_rule,hr]; rfl
          have hw : ruleAtM (wrapped g).rules i = some ⟨r.arity,render r.body⟩ := by rw [wrapped_rule,hr]; rfl
          have ha' : r.arity = (renderArgs args).length := by rw [renderArgs_length]; exact ha
          rw [evV_call_seq ht ha]
          change _ = match evV (wrapped g) x .callByValueSeq U E (.andP (.call i (renderArgs args))) p with
            | some (some q) => evV (wrapped g) x .callByValueSeq U E (sequenceArgs (renderArgs args)) q
            | r => r
          rw [evV_peek,evV_call_seq hw ha',← hargs]
          cases hv : evSeqArgs (tested g) x .callByValueSeq T E args p with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W,q⟩ := Wq
              have hq := (evSeq_mem hOk args p W q hp hv).2
              have he := hpeek i r hr W q hq
              simp only []
              rw [he]
              cases hu : valAt (U i W) q with
              | none => rfl
              | some v => cases v with
                | none => rfl
                | some j =>
                  change some (some q) = evV (wrapped g) x .callByValueSeq U E (sequenceArgs (renderArgs args)) p
                  rw [hseq,hv]; rfl
        · simp [render,evV,tested_rule,wrapped_rule,hr,renderArgs_length,ha,MExp.andP]
    | .seq a b, hf, E, p, hp => by
      simp only [render]
      have heq := evaluator_of_peek hOk hpeek a hf.1 E p hp
      cases hv : evV (tested g) x .callByValueSeq T E a p with
      | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
      | some v => cases v with
        | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
          exact evaluator_of_peek hOk hpeek b hf.2 E q (evV_ok hOk a p hp q hv)
    | .alt a b, hf, E, p, hp => by
      simp only [render]
      have heq := evaluator_of_peek hOk hpeek a hf.1 E p hp
      cases hv : evV (tested g) x .callByValueSeq T E a p with
      | none => rw [evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
      | some v => cases v with
        | none =>
          rw [evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
          exact evaluator_of_peek hOk hpeek b hf.2 E p hp
        | some q => rw [evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
    | .notP a, hf, E, p, hp => by simp only [render,evV]; rw [evaluator_of_peek hOk hpeek a hf E p hp]
    | .star a, hf, E, p, hp => by
      rw [render,evV_star,evV_star]
      exact evStar_congr p (fun q hq => evaluator_of_peek hOk hpeek a hf E q (by omega))

  theorem arguments_of_peek {g : MGrammar} {x : List Char} {T U : Nat → List (List Char) → Val}
      (hOk : OkTV x.length T) (hpeek : Peeked g x T U) :
      ∀ args : List MExp, MExp.FirstOrderArgs args → ∀ E p, p ≤ x.length →
        evSeqArgs (tested g) x .callByValueSeq T E args p =
          evSeqArgs (wrapped g) x .callByValueSeq U E (renderArgs args) p
    | [], _, _, _, _ => rfl
    | a::args, hf, E, p, hp => by
      simp only [renderArgs,evSeqArgs]
      rw [← evaluator_of_peek hOk hpeek a hf.1 E p hp]
      cases hv : evV (tested g) x .callByValueSeq T E a p with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some q =>
          simp only []
          rw [arguments_of_peek hOk hpeek args hf.2 E q (evV_ok hOk a p hp q hv)]
end

theorem tables_peeked {g : MGrammar} (hg : g.FirstOrder) (x : List Char) (m : Nat) :
    Peeked g x (tblV (tested g) x .callByValueSeq m) (tblV (wrapped g) x .callByValueSeq m) := by
  induction m with
  | zero => intro i r hr E p hp; rfl
  | succ m ih =>
    intro i r hr E p hp
    have ht : ruleAtM (tested g).rules i = some ⟨r.arity,.andP r.body⟩ := by rw [tested_rule,hr]; rfl
    have hw : ruleAtM (wrapped g).rules i = some ⟨r.arity,render r.body⟩ := by rw [wrapped_rule,hr]; rfl
    rw [valAt_tblV_succ ht E hp,valAt_tblV_succ hw E hp,evV_peek]
    rw [evaluator_of_peek (tblV_ok _ _ _ m) ih r.body (hg r (ruleAtM_mem hr)) E p hp]

theorem evaluator_eq {g : MGrammar} (hg : g.FirstOrder) (x : List Char) (m : Nat)
    (e : MExp) (he : e.FirstOrder) (E : List (List Char)) (p : Nat) (hp : p ≤ x.length) :
    evV (tested g) x .callByValueSeq (tblV (tested g) x .callByValueSeq m) E e p =
      evV (wrapped g) x .callByValueSeq (tblV (wrapped g) x .callByValueSeq m) E (render e) p :=
  evaluator_of_peek (tblV_ok _ _ _ m) (tables_peeked hg x m) e he E p hp

theorem iterBound_eq (g : MGrammar) (x : List Char) : iterBoundV (tested g) x = iterBoundV (wrapped g) x := by
  unfold iterBoundV
  have hn : (tested g).rules.length = (wrapped g).rules.length := by simp [tested,wrapped]
  rw [hn]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [tested_rule,wrapped_rule]
  cases ruleAtM g.rules i <;> rfl

theorem decide_eq {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValueSeq (tested g) x e = decideObsV .callByValueSeq (wrapped g) x (render e) := by
  unfold decideObsV
  rw [evaluator_eq hg x _ e he [] x.length (Nat.le_refl _),iterBound_eq]

/-- The fixed Seq grammar transformation preserves all original character
inputs, success remainders, finite failures, and absence of finite results. -/
theorem observations_iff {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    SObs (tested g) .callByValueSeq e x r ↔ SObs (wrapped g) .callByValueSeq (render e) x r := by
  rw [← decideObsV_iff (tested_firstOrder hg) (by decide) he,
    ← decideObsV_iff (wrapped_firstOrder g) (by decide) (render_firstOrder e),decide_eq hg e he x]

theorem language_translation {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) :
    ∃ (out : MGrammar) (entry : MExp), out.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (tested g) .callByValueSeq e x (some []) ↔
        SObs out .callByValueSeq entry x (some []) :=
  ⟨wrapped g,render e,wrapped_firstOrder g,render_firstOrder e,
    fun x => observations_iff hg e he x (some [])⟩

/-- A plain call peek loses Seq argument consumption even for an empty body.
The source accepts the whole one-character input; the naive wrapper does not. -/
theorem plain_peek_changes_result :
    let g : MGrammar := ⟨[⟨1,.eps⟩]⟩
    let e : MExp := .call 0 [.lit ['a']]
    SObs (tested g) .callByValueSeq e ['a'] (some []) ∧
      SObs (wrapped g) .callByValueSeq (.andP e) ['a'] (some ['a']) ∧
      ¬ SObs (wrapped g) .callByValueSeq (.andP e) ['a'] (some []) := by
  intro g e
  have ha : ∀ G : MGrammar, DerivesArgsSeq G .callByValueSeq ['a'] [.lit ['a']] [.lit ['a']] [] := by
    intro G
    exact .cons _ _ _ ['a'] [] [] _ _ (.litOk _ _ _ rfl) rfl (.nil _)
  have hsource : SObs (tested g) .callByValueSeq e ['a'] (some []) := by
    refine ⟨_,.callSeqOk 0 _ ⟨1,.andP .eps⟩ _ [] [] _ .notT rfl rfl rfl (ha _) ?_,rfl⟩
    exact .notFail _ _ (.notOk _ _ _ _ (.eps _))
  have hcall : SObs (wrapped g) .callByValueSeq e ['a'] (some []) := by
    exact ⟨_,.callSeqOk 0 _ ⟨1,.eps⟩ _ [] [] _ _ rfl rfl rfl (ha _) (.eps _),rfl⟩
  have hpeek := RootObservation.peek_success hcall
  refine ⟨hsource,hpeek,?_⟩
  intro h
  have he := sObs_unique h hpeek
  cases he

end Shallot.MacroPeg.CBV.SequentialCallLookahead
