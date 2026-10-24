import MacroPeg.CBV.ReplayFusion

namespace Shallot.MacroPeg.CBV.PrefixPairFusion

/-! Two common-origin prefixes can be represented by disjoint chunks.
Template calls `F(A,B)` mean `F(A,A B)` in Par and `F(A,B)` in Seq.
The source rule replays its second parameter before its template tail;
the target tail reconstructs that parameter as the two chunks in sequence.
This is a prefix-factored fragment, not an arbitrary-Par normalization. -/

def render (parallel : Bool) : MExp → MExp
  | .param k => if parallel || k != 1 then .param k else .seq (.param 0) (.param 1)
  | .call i [a, b] =>
    if parallel then .call i [render parallel a, .seq (render parallel a) (render parallel b)]
    else .call i [render parallel a, render parallel b]
  | .call _ _ => MExp.failAlways
  | .seq a b => .seq (render parallel a) (render parallel b)
  | .alt a b => .alt (render parallel a) (render parallel b)
  | .star a => .star (render parallel a)
  | .notP a => .notP (render parallel a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder (parallel : Bool) : ∀ e, (render parallel e).FirstOrder
  | .param k => by
    by_cases hk : k = 1 <;> cases parallel <;> simp [render, hk, MExp.FirstOrder]
  | .call i [] | .call i [_] | .call i (_ :: _ :: _ :: _) => by
    simp [render, MExp.failAlways, MExp.FirstOrder]
  | .call i [a, b] => by
    cases parallel <;> simp [render, MExp.FirstOrder, MExp.FirstOrderArgs,
      render_firstOrder _ a, render_firstOrder _ b]
  | .seq a b | .alt a b => by
    exact ⟨render_firstOrder parallel a, render_firstOrder parallel b⟩
  | .star a | .notP a => render_firstOrder parallel a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def parGrammar (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun body => ⟨2, .seq (.param 1) (render true body)⟩)⟩

def seqGrammar (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun body => ⟨2, render false body⟩)⟩

theorem par_rule (tails : List MExp) (i : Nat) :
    ruleAtM (parGrammar tails).rules i =
      (tails[i]?).map (fun body => ⟨2, .seq (.param 1) (render true body)⟩) := by
  simp [parGrammar, ruleAtM_eq_getElem?]

theorem seq_rule (tails : List MExp) (i : Nat) :
    ruleAtM (seqGrammar tails).rules i = (tails[i]?).map (fun body => ⟨2, render false body⟩) := by
  simp [seqGrammar, ruleAtM_eq_getElem?]

theorem par_firstOrder (tails : List MExp) : (parGrammar tails).FirstOrder := by
  intro r hr
  obtain ⟨body, hb, rfl⟩ := List.mem_map.mp hr
  exact ⟨trivial, render_firstOrder true body⟩

theorem seq_firstOrder (tails : List MExp) : (seqGrammar tails).FirstOrder := by
  intro r hr
  obtain ⟨body, hb, rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder false body

def mergeEnv : List (List Char) → List (List Char)
  | u :: v :: rest => u :: (u ++ v) :: rest
  | E => E

private theorem strip_concat (u v input : List Char) :
    Shallot.stripPrefix? (u ++ v) input =
      (Shallot.stripPrefix? u input).bind (Shallot.stripPrefix? v) := by
  induction u generalizing input with
  | nil => rfl
  | cons c u ih =>
    cases input with
    | nil => rfl
    | cons d input =>
      simp only [List.cons_append, Shallot.stripPrefix?]
      split <;> simp_all

private theorem pair_parameter (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (u v : List Char) (rest : List (List Char)) (p : Nat) :
    evV g x s T (u :: v :: rest) (.seq (.param 0) (.param 1)) p =
      evV g x s T [u ++ v] (.param 0) p := by
  simp only [evV, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [strip_concat]
  cases hs : Shallot.stripPrefix? u (sfx x p) with
  | none => rfl
  | some rem =>
    have hsplit := (CBVtoCBN.stripPrefix_exact u (sfx x p) rem).mp hs
    have hroot := suffix_trans (sfx_is_suffix x p) ⟨u, hsplit⟩
    have hrestore := sfx_suffix hroot.choose_spec
    simp only [Option.bind_some, hrestore]

theorem parameters_eq (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (k p : Nat) :
    evV g x s T (mergeEnv E) (render true (.param k)) p =
      evV h x t U E (render false (.param k)) p := by
  cases k with
  | zero => cases E <;> simp [render, mergeEnv, evV]; rename_i u E; cases E <;> rfl
  | succ k =>
    cases k with
    | zero =>
      cases E with
      | nil => simp [render, mergeEnv, evV]
      | cons u E =>
        cases E with
        | nil =>
          cases hs : Shallot.stripPrefix? u (sfx x p) <;> simp [render, mergeEnv, evV, hs]
        | cons v rest =>
          have hv := pair_parameter h x t U u v rest p
          simpa [render, mergeEnv, evV] using hv.symm
    | succ k =>
      cases E with
      | nil => simp [render, mergeEnv, evV]
      | cons u E =>
        cases E <;> simp [render, mergeEnv, evV, Nat.succ_ne_self]

def Shifted (tails : List MExp) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i body, tails[i]? = some body → ∀ u v p q, p ≤ x.length → q ≤ x.length →
    sfx x p = (u ++ v) ++ sfx x q →
      valAt (T i [u, u ++ v]) p = valAt (U i [u, v]) q

theorem evaluator_of_shift {tails : List MExp} {x : List Char}
    {T U : Nat → List (List Char) → Val}
    (hT : SoundTV (parGrammar tails) x .callByValuePar T)
    (hOk : OkTV x.length T) (hshift : Shifted tails x T U) :
    ∀ e E p, p ≤ x.length →
      evV (parGrammar tails) x .callByValuePar T (mergeEnv E) (render true e) p =
        evV (seqGrammar tails) x .callByValueSeq U E (render false e) p
  | .param k, E, p, _ => parameters_eq _ _ _ _ _ _ _ E k p
  | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .dbg _, _, _, _ | .lam _ _, _, _, _ | .callParam _ _, _, _, _
  | .invoke _ _ _, _, _, _ | .call _ [], _, _, _ | .call _ [_], _, _, _
  | .call _ (_ :: _ :: _ :: _), _, _, _ => rfl
  | .call i [a, b], E, p, hp => by
    change evV _ _ _ _ _ (.call i [render true a, .seq (render true a) (render true b)]) p =
      evV _ _ _ _ _ (.call i [render false a, render false b]) p
    cases hr : tails[i]? with
    | none => simp [evV, par_rule, seq_rule, hr]
    | some body =>
      have hrp : ruleAtM (parGrammar tails).rules i =
          some ⟨2, .seq (.param 1) (render true body)⟩ := by rw [par_rule, hr]; rfl
      have hrs : ruleAtM (seqGrammar tails).rules i = some ⟨2, render false body⟩ := by
        rw [seq_rule, hr]; rfl
      rw [evV_call_par hrp rfl (by decide), evV_call_seq hrs rfl]
      have ha := evaluator_of_shift hT hOk hshift a E p hp
      cases hv : evV (parGrammar tails) x .callByValuePar T (mergeEnv E) (render true a) p with
      | none => simp [evParArgs, evSeqArgs, hv, ha.symm.trans hv]
      | some result =>
        cases result with
        | none => simp [evParArgs, evSeqArgs, hv, ha.symm.trans hv]
        | some q =>
          obtain ⟨hq, hpq⟩ := ReplayFusion.success_prefix hT (mergeEnv E) (render true a)
            (render_firstOrder true a) p q hp hv
          have hb := evaluator_of_shift hT hOk hshift b E q hq
          simp only [evParArgs, evSeqArgs, hv, ha.symm.trans hv, evV_seq_ok hv]
          rw [← hb]
          cases hw : evV (parGrammar tails) x .callByValuePar T (mergeEnv E) (render true b) q with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some r =>
              obtain ⟨hrange, hqr⟩ := ReplayFusion.success_prefix hT (mergeEnv E) (render true b)
                (render_firstOrder true b) q r hq hw
              have hpr : sfx x p = (pre x p q ++ pre x q r) ++ sfx x r := by
                rw [hpq, hqr, List.append_assoc]
              have he := pre_split (x := x) hp ⟨_, hpr⟩
              rw [length_sfx x hrange] at he
              have hpre : pre x p r = pre x p q ++ pre x q r :=
                List.append_cancel_right (he.symm.trans hpr)
              simpa only [hpre] using hshift i body hr (pre x p q) (pre x q r) p r hp hrange hpr
  | .seq a b, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a E p hp
    cases hv : evV (parGrammar tails) x .callByValuePar T (mergeEnv E) (render true a) p with
    | none => simp only [render, evV_seq_none hv, evV_seq_none (heq.symm.trans hv)]
    | some result =>
      cases result with
      | none => simp only [render, evV_seq_fail hv, evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        simp only [render, evV_seq_ok hv, evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b E q (evV_ok hOk (render true a) p hp q hv)
  | .alt a b, E, p, hp => by
    have heq := evaluator_of_shift hT hOk hshift a E p hp
    cases hv : evV (parGrammar tails) x .callByValuePar T (mergeEnv E) (render true a) p with
    | none => simp only [render, evV_alt_none hv, evV_alt_none (heq.symm.trans hv)]
    | some result =>
      cases result with
      | none =>
        simp only [render, evV_alt_fail hv, evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b E p hp
      | some q => simp only [render, evV_alt_ok hv, evV_alt_ok (heq.symm.trans hv)]
  | .notP a, E, p, hp => by
    simp only [render, evV]
    rw [evaluator_of_shift hT hOk hshift a E p hp]
  | .star a, E, p, hp => by
    simp only [render, evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hshift a E q (by omega))

theorem tables_shifted (tails : List MExp) (x : List Char) (m : Nat) :
    Shifted tails x (tblV (parGrammar tails) x .callByValuePar m)
      (tblV (seqGrammar tails) x .callByValueSeq m) := by
  induction m with
  | zero => intro i body hr u v p q hp hq hs; simp [tblV, valAt_nil]
  | succ m ih =>
    intro i body hr u v p q hp hq hs
    have hrp : ruleAtM (parGrammar tails).rules i =
        some ⟨2, .seq (.param 1) (render true body)⟩ := by rw [par_rule, hr]; rfl
    have hrs : ruleAtM (seqGrammar tails).rules i = some ⟨2, render false body⟩ := by
      rw [seq_rule, hr]; rfl
    rw [valAt_tblV_succ hrp [u, u ++ v] hp, valAt_tblV_succ hrs [u, v] hq]
    have hstrip := (CBVtoCBN.stripPrefix_exact (u ++ v) (sfx x p) (sfx x q)).mpr hs
    simp only [evV, List.getElem?_cons_zero, List.getElem?_cons_succ, hstrip, length_sfx x hq]
    exact evaluator_of_shift (tblV_sound (par_firstOrder tails) (by decide) m)
      (tblV_ok _ _ _ m) ih body [u, v] q hq

/-- All partial results agree at every clock with the two representations
of the same captured values, including during recursive calls. -/
theorem evaluator_eq (tails : List MExp) (x : List Char) (m : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar tails) x .callByValuePar (tblV (parGrammar tails) x .callByValuePar m)
      (mergeEnv E) (render true e) p =
    evV (seqGrammar tails) x .callByValueSeq (tblV (seqGrammar tails) x .callByValueSeq m)
      E (render false e) p :=
  evaluator_of_shift (tblV_sound (par_firstOrder tails) (by decide) m) (tblV_ok _ _ _ m)
    (tables_shifted tails x m) e E p hp

theorem iterBound_eq (tails : List MExp) (x : List Char) :
    iterBoundV (parGrammar tails) x = iterBoundV (seqGrammar tails) x := by
  have hlen : (parGrammar tails).rules.length = (seqGrammar tails).rules.length := by
    simp [parGrammar, seqGrammar]
  unfold iterBoundV
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [par_rule, seq_rule]
  cases tails[i]? <;> rfl

theorem decide_eq (tails : List MExp) (e : MExp) (x : List Char) :
    decideObsV .callByValuePar (parGrammar tails) x (render true e) =
      decideObsV .callByValueSeq (seqGrammar tails) x (render false e) := by
  unfold decideObsV
  rw [show ([] : List (List Char)) = mergeEnv [] from rfl,
    evaluator_eq tails x _ [] e x.length (Nat.le_refl _), iterBound_eq]
  rfl

/-- The two-prefix transformation preserves every observation on the same
original input, including finite failure. No totality premise is used. -/
theorem observations_iff (tails : List MExp) (e : MExp) (x : List Char)
    (r : Option (List Char)) :
    SObs (parGrammar tails) .callByValuePar (render true e) x r ↔
      SObs (seqGrammar tails) .callByValueSeq (render false e) x r := by
  rw [← decideObsV_iff (par_firstOrder tails) (by decide) (render_firstOrder true e),
    ← decideObsV_iff (seq_firstOrder tails) (by decide) (render_firstOrder false e),
    decide_eq tails e x]

theorem recognizes_iff (tails : List MExp) (e : MExp) (x : List Char) :
    SObs (parGrammar tails) .callByValuePar (render true e) x (some []) ↔
      SObs (seqGrammar tails) .callByValueSeq (render false e) x (some []) :=
  observations_iff tails e x (some [])

end Shallot.MacroPeg.CBV.PrefixPairFusion
