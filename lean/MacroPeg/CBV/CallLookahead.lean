import MacroPeg.CBV.ReplayFusion

/-! For Par, a lookahead around every rule body can be moved to every call.
This preserves recursive finite observations, including failure and undefinedness. -/
namespace Shallot.MacroPeg.CBV.CallLookahead

mutual
  def render : MExp → MExp
    | .call i args => .andP (.call i (renderArgs args))
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
    | a :: args => render a :: renderArgs args
end

mutual
  theorem render_firstOrder : ∀ e, (render e).FirstOrder
    | .call _ args => renderArgs_firstOrder args
    | .seq a b | .alt a b => ⟨render_firstOrder a,render_firstOrder b⟩
    | .star a | .notP a => render_firstOrder a
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
  theorem renderArgs_firstOrder : ∀ args, MExp.FirstOrderArgs (renderArgs args)
    | [] => trivial
    | a :: args => ⟨render_firstOrder a,renderArgs_firstOrder args⟩
end

theorem renderArgs_length (args : List MExp) : (renderArgs args).length = args.length := by
  induction args <;> simp_all [renderArgs]

def tested (g : MGrammar) : MGrammar := ⟨g.rules.map (fun r => ⟨r.arity,.andP r.body⟩)⟩
def wrapped (g : MGrammar) : MGrammar := ⟨g.rules.map (fun r => ⟨r.arity,render r.body⟩)⟩

theorem tested_rule (g : MGrammar) (i : Nat) :
    ruleAtM (tested g).rules i = (ruleAtM g.rules i).map (fun r => ⟨r.arity,.andP r.body⟩) := by
  simp [tested,ruleAtM_eq_getElem?]
theorem wrapped_rule (g : MGrammar) (i : Nat) :
    ruleAtM (wrapped g).rules i = (ruleAtM g.rules i).map (fun r => ⟨r.arity,render r.body⟩) := by
  simp [wrapped,ruleAtM_eq_getElem?]

theorem tested_firstOrder {g : MGrammar} (hg : g.FirstOrder) : (tested g).FirstOrder := by
  intro r hr
  change r ∈ g.rules.map (fun r => ⟨r.arity,.andP r.body⟩) at hr
  obtain ⟨src,hsrc,he⟩ := List.mem_map.mp hr
  subst r
  exact hg src hsrc

theorem wrapped_firstOrder (g : MGrammar) : (wrapped g).FirstOrder := by
  intro r hr
  change r ∈ g.rules.map (fun r => ⟨r.arity,render r.body⟩) at hr
  obtain ⟨src,hsrc,he⟩ := List.mem_map.mp hr
  subst r
  exact render_firstOrder src.body

def peek (p : Nat) (r : Res) : Res := match r with
  | some (some _) => some (some p)
  | r => r

theorem evV_peek (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV g x s T E (.andP e) p = peek p (evV g x s T E e p) := by
  simp only [MExp.andP,evV]
  cases evV g x s T E e p with
  | none => rfl
  | some r => cases r <;> rfl

def Peeked (g : MGrammar) (x : List Char) (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i r, ruleAtM g.rules i = some r → ∀ E p, p ≤ x.length →
    valAt (T i E) p = peek p (valAt (U i E) p)

mutual
  theorem evaluator_of_peek {g : MGrammar} {x : List Char} {T U : Nat → List (List Char) → Val}
      (hOk : OkTV x.length T) (hpeek : Peeked g x T U) :
      ∀ e : MExp, e.FirstOrder → ∀ E p, p ≤ x.length →
        evV (tested g) x .callByValuePar T E e p =
          evV (wrapped g) x .callByValuePar U E (render e) p
    | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
    | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
    | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _
    | .callParam _ _, hf, _, _, _ | .invoke _ _ _, hf, _, _, _ => False.elim hf
    | .call i args, hf, E, p, hp => by
      have hargs := arguments_of_peek hOk hpeek args hf E p hp
      rw [render,evV_peek]
      cases hr : ruleAtM g.rules i with
      | none => simp [evV,tested_rule,wrapped_rule,hr,peek]
      | some r =>
        by_cases ha : r.arity = args.length
        · simp only [evV,tested_rule,wrapped_rule,hr,Option.map,renderArgs_length,if_pos ha]
          rw [← hargs]
          cases hv : evParArgs (tested g) x .callByValuePar T E args p with
          | none => rfl
          | some v =>
            cases v with
            | none => rfl
            | some W => exact hpeek i r hr W p hp
        · simp [evV,tested_rule,wrapped_rule,hr,renderArgs_length,ha,peek]
    | .seq a b, hf, E, p, hp => by
      simp only [render]
      have heq := evaluator_of_peek hOk hpeek a hf.1 E p hp
      cases hv : evV (tested g) x .callByValuePar T E a p with
      | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
      | some v =>
        cases v with
        | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
          exact evaluator_of_peek hOk hpeek b hf.2 E q (evV_ok hOk a p hp q hv)
    | .alt a b, hf, E, p, hp => by
      simp only [render]
      have heq := evaluator_of_peek hOk hpeek a hf.1 E p hp
      cases hv : evV (tested g) x .callByValuePar T E a p with
      | none => rw [evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
      | some v =>
        cases v with
        | none =>
          rw [evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
          exact evaluator_of_peek hOk hpeek b hf.2 E p hp
        | some q => rw [evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
    | .notP a, hf, E, p, hp => by
      simp only [render,evV]
      rw [evaluator_of_peek hOk hpeek a hf E p hp]
    | .star a, hf, E, p, hp => by
      simp only [render]
      rw [evV_star,evV_star]
      exact evStar_congr p (fun q hq => evaluator_of_peek hOk hpeek a hf E q (by omega))

  theorem arguments_of_peek {g : MGrammar} {x : List Char} {T U : Nat → List (List Char) → Val}
      (hOk : OkTV x.length T) (hpeek : Peeked g x T U) :
      ∀ args : List MExp, MExp.FirstOrderArgs args → ∀ E p, p ≤ x.length →
        evParArgs (tested g) x .callByValuePar T E args p =
          evParArgs (wrapped g) x .callByValuePar U E (renderArgs args) p
    | [], _, _, _, _ => rfl
    | a :: args, hf, E, p, hp => by
      simp only [renderArgs,evParArgs]
      rw [← evaluator_of_peek hOk hpeek a hf.1 E p hp,← arguments_of_peek hOk hpeek args hf.2 E p hp]
end

theorem tables_peeked {g : MGrammar} (hg : g.FirstOrder) (x : List Char) (m : Nat) :
    Peeked g x (tblV (tested g) x .callByValuePar m) (tblV (wrapped g) x .callByValuePar m) := by
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
    evV (tested g) x .callByValuePar (tblV (tested g) x .callByValuePar m) E e p =
      evV (wrapped g) x .callByValuePar (tblV (wrapped g) x .callByValuePar m) E (render e) p :=
  evaluator_of_peek (tblV_ok _ _ _ m) (tables_peeked hg x m) e he E p hp

theorem iterBound_eq (g : MGrammar) (x : List Char) :
    iterBoundV (tested g) x = iterBoundV (wrapped g) x := by
  unfold iterBoundV
  have hn : (tested g).rules.length = (wrapped g).rules.length := by simp [tested,wrapped]
  rw [hn]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [tested_rule,wrapped_rule]
  cases ruleAtM g.rules i <;> rfl

theorem decide_eq {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (tested g) x e = decideObsV .callByValuePar (wrapped g) x (render e) := by
  unfold decideObsV
  rw [evaluator_eq hg x _ e he [] x.length (Nat.le_refl _),iterBound_eq]

theorem observations_iff {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    SObs (tested g) .callByValuePar e x r ↔ SObs (wrapped g) .callByValuePar (render e) x r := by
  rw [← decideObsV_iff (tested_firstOrder hg) (by decide) he,
    ← decideObsV_iff (wrapped_firstOrder g) (by decide) (render_firstOrder e),decide_eq hg e he x]

end Shallot.MacroPeg.CBV.CallLookahead
