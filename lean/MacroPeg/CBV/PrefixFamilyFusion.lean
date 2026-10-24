import MacroPeg.CBV.ReplayFusion
import MacroPeg.CBV.CaptureViews

/-! Reverse compilation for prefix-factored calls of arbitrary arity.
Par captures cumulative prefixes and replays the longest one; Seq captures
consecutive chunks. This is not a normal form for arbitrary Par grammars. -/
namespace Shallot.MacroPeg.CBV.PrefixFamilyFusion

def words : List (List Char) → List (List Char)
  | [] => []
  | w :: W => w :: (words W).map (w ++ ·)

def parsers : List MExp → List MExp
  | [] => []
  | a :: args => a :: (parsers args).map (.seq a)

theorem words_length (W : List (List Char)) : (words W).length = W.length := by
  induction W <;> simp_all [words]
theorem parsers_length (args : List MExp) : (parsers args).length = args.length := by
  induction args <;> simp_all [parsers]

theorem words_get (W : List (List Char)) (k : Nat) (hk : k < W.length) :
    (words W)[k]? = some (W.take (k+1)).flatten := by
  induction W generalizing k with
  | nil => simp at hk
  | cons w W ih =>
    cases k with
    | zero => simp [words]
    | succ k =>
      have hh : k < W.length := by simpa using hk
      simp [words,ih k hh,List.take_succ_cons]

theorem parsers_firstOrder (args : List MExp) (h : MExp.FirstOrderArgs args) :
    MExp.FirstOrderArgs (parsers args) := by
  induction args with
  | nil => trivial
  | cons a args ih =>
    have hm : ∀ bs, MExp.FirstOrderArgs bs → MExp.FirstOrderArgs (bs.map (.seq a)) := by
      intro bs hb
      induction bs with
      | nil => trivial
      | cons b bs ih => exact ⟨⟨h.1,hb.1⟩,ih hb.2⟩
    exact ⟨h.1,hm _ (ih h.2)⟩

mutual
  def render (parallel : Bool) (scope : Nat) : MExp → MExp
    | .param k => if k < scope then
        (if parallel then .param k else CaptureViews.prefixExpr (k+1)) else MExp.failAlways
    | .call i args => .call i (if parallel then parsers (renderArgs parallel scope args)
        else renderArgs parallel scope args)
    | .seq a b => .seq (render parallel scope a) (render parallel scope b)
    | .alt a b => .alt (render parallel scope a) (render parallel scope b)
    | .star a => .star (render parallel scope a)
    | .notP a => .notP (render parallel scope a)
    | .eps => .eps
    | .any => .any
    | .chr c => .chr c
    | .range lo hi => .range lo hi
    | .lit w => .lit w
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways
  def renderArgs (parallel : Bool) (scope : Nat) : List MExp → List MExp
    | [] => []
    | a :: args => render parallel scope a :: renderArgs parallel scope args
end

mutual
  theorem render_firstOrder (parallel : Bool) (scope : Nat) : ∀ e, (render parallel scope e).FirstOrder
    | .param k => by
      by_cases hk : k < scope <;> cases parallel <;>
        simp [render,hk,MExp.failAlways,MExp.FirstOrder,CaptureViews.prefixExpr_firstOrder]
    | .call i args => by
      cases parallel
      · exact renderArgs_firstOrder false scope args
      · exact parsers_firstOrder _ (renderArgs_firstOrder true scope args)
    | .seq a b | .alt a b => ⟨render_firstOrder parallel scope a,render_firstOrder parallel scope b⟩
    | .star a | .notP a => render_firstOrder parallel scope a
    | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
  theorem renderArgs_firstOrder (parallel : Bool) (scope : Nat) :
      ∀ args, MExp.FirstOrderArgs (renderArgs parallel scope args)
    | [] => trivial
    | a :: args => ⟨render_firstOrder parallel scope a,renderArgs_firstOrder parallel scope args⟩
end

theorem renderArgs_length (parallel : Bool) (scope : Nat) (args : List MExp) :
    (renderArgs parallel scope args).length = args.length := by
  induction args <;> simp_all [renderArgs]

def replay : Nat → MExp
  | 0 => .eps
  | n+1 => .param n

def parGrammar (rules : List MRule) : MGrammar :=
  ⟨rules.map (fun r => ⟨r.arity,.seq (replay r.arity) (render true r.arity r.body)⟩)⟩
def seqGrammar (rules : List MRule) : MGrammar :=
  ⟨rules.map (fun r => ⟨r.arity,render false r.arity r.body⟩)⟩

theorem par_rule (rules : List MRule) (i : Nat) :
    ruleAtM (parGrammar rules).rules i =
      (rules[i]?).map (fun r => ⟨r.arity,.seq (replay r.arity) (render true r.arity r.body)⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]
theorem seq_rule (rules : List MRule) (i : Nat) :
    ruleAtM (seqGrammar rules).rules i =
      (rules[i]?).map (fun r => ⟨r.arity,render false r.arity r.body⟩) := by
  simp [seqGrammar,ruleAtM_eq_getElem?]

theorem replay_firstOrder (n : Nat) : (replay n).FirstOrder := by cases n <;> trivial
theorem par_firstOrder (rules : List MRule) : (parGrammar rules).FirstOrder := by
  intro r hr
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
  exact ⟨replay_firstOrder _,render_firstOrder _ _ _⟩
theorem seq_firstOrder (rules : List MRule) : (seqGrammar rules).FirstOrder := by
  intro r hr
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder _ _ _

theorem parameters_eq (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Nat → List (List Char) → Val) (E : List (List Char)) (k p : Nat) :
    evV g x s T (words E) (render true E.length (.param k)) p =
      evV h x t U E (render false E.length (.param k)) p := by
  by_cases hk : k < E.length
  · simp only [render,if_pos hk]
    change evV g x s T (words E) (.param k) p =
      evV h x t U E (CaptureViews.prefixExpr (k+1)) p
    rw [CaptureViews.prefixExpr_eval _ _ _ _ _ _ (by omega)]
    simp only [evV,words_get E k hk]
  · simp [render,hk,evV,MExp.failAlways]

private theorem pre_concat {g : MGrammar} {x : List Char}
    {T : Nat → List (List Char) → Val} (hT : SoundTV g x .callByValuePar T)
    (E : List (List Char)) (a b : MExp) (ha : a.FirstOrder) (hb : b.FirstOrder)
    (p q r : Nat) (hp : p ≤ x.length)
    (hqa : evV g x .callByValuePar T E a p = some (some q))
    (hrb : evV g x .callByValuePar T E b q = some (some r)) :
    pre x p r = pre x p q ++ pre x q r := by
  obtain ⟨hq,hpq⟩ := ReplayFusion.success_prefix hT E a ha p q hp hqa
  obtain ⟨hr,hqr⟩ := ReplayFusion.success_prefix hT E b hb q r hq hrb
  have hpr : sfx x p = (pre x p q ++ pre x q r) ++ sfx x r := by
    rw [hpq,hqr,List.append_assoc]
  have he := pre_split (x := x) hp ⟨_,hpr⟩
  rw [length_sfx x hr] at he
  exact List.append_cancel_right (he.symm.trans hpr)

theorem par_prepend {g : MGrammar} {x : List Char}
    {T : Nat → List (List Char) → Val} (hT : SoundTV g x .callByValuePar T)
    (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (p q : Nat) (hp : p ≤ x.length)
    (hv : evV g x .callByValuePar T E a p = some (some q)) :
    ∀ bs, MExp.FirstOrderArgs bs →
      evParArgs g x .callByValuePar T E (bs.map (.seq a)) p =
        (evParArgs g x .callByValuePar T E bs q).map
          (Option.map (List.map (pre x p q ++ ·))) := by
  intro bs hb
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,evParArgs,evV_seq_ok hv]
    cases hr : evV g x .callByValuePar T E b q with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some r =>
        rw [ih hb.2]
        dsimp only []
        rw [pre_concat hT E a b ha hb.1 p q r hp hv hr]
        cases evParArgs g x .callByValuePar T E bs q with
        | none => rfl
        | some result => cases result <;> rfl

theorem arguments_factor {g : MGrammar} {x : List Char}
    {T : Nat → List (List Char) → Val} (hT : SoundTV g x .callByValuePar T)
    (hOk : OkTV x.length T) (E : List (List Char)) :
    ∀ args, MExp.FirstOrderArgs args → ∀ p, p ≤ x.length →
      evParArgs g x .callByValuePar T E (parsers args) p =
        (evSeqArgs g x .callByValuePar T E args p).map (Option.map (fun Wq => words Wq.1)) := by
  intro args ha
  induction args with
  | nil => intro p hp; rfl
  | cons a args ih =>
    intro p hp
    simp only [parsers,evParArgs,evSeqArgs]
    cases hv : evV g x .callByValuePar T E a p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some q =>
        rw [par_prepend hT E a ha.1 p q hp hv _ (parsers_firstOrder args ha.2),
          ih ha.2 q (evV_ok hOk a p hp q hv)]
        dsimp only []
        cases evSeqArgs g x .callByValuePar T E args q with
        | none => rfl
        | some result => cases result <;> rfl


/-- The actual consecutive argument run covers exactly the concatenation
of its captured chunks. -/
theorem arguments_prefix {g : MGrammar} {x : List Char}
    {T : Nat → List (List Char) → Val} (hT : SoundTV g x .callByValuePar T)
    (E : List (List Char)) : ∀ args, MExp.FirstOrderArgs args → ∀ p W q,
      p ≤ x.length → evSeqArgs g x .callByValuePar T E args p = some (some (W,q)) →
      sfx x p = W.flatten ++ sfx x q := by
  intro args ha
  induction args with
  | nil => intro p W q hp h; cases h; rfl
  | cons a args ih =>
    intro p W q hp h
    cases hv : evV g x .callByValuePar T E a p with
    | none => simp [evSeqArgs,hv] at h
    | some result => cases result with
      | none => simp [evSeqArgs,hv] at h
      | some r =>
        obtain ⟨hr,hpr⟩ := ReplayFusion.success_prefix hT E a ha.1 p r hp hv
        simp only [evSeqArgs,hv] at h
        cases ht : evSeqArgs g x .callByValuePar T E args r with
        | none => rw [ht] at h; cases h
        | some result => cases result with
          | none => rw [ht] at h; cases h
          | some Wq =>
            obtain ⟨V,j⟩ := Wq
            rw [ht] at h
            cases h
            rw [hpr,ih ha.2 r V q hr ht,List.flatten_cons,List.append_assoc]

theorem replay_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (W : List (List Char)) (p q : Nat)
    (hp : p ≤ x.length) (hq : q ≤ x.length)
    (hs : sfx x p = W.flatten ++ sfx x q) :
    evV g x s T (words W) (replay W.length) p = some (some q) := by
  cases W with
  | nil =>
    have hl := congrArg List.length hs
    simp only [List.flatten_nil,List.nil_append,length_sfx x hp,length_sfx x hq] at hl
    have he : p=q := by omega
    subst q
    rfl
  | cons w W =>
    have hw := words_get (w::W) W.length (by simp)
    have htake : (w::W).take (W.length+1) = w::W := by
      simpa only [List.length_cons] using (List.take_length (l := w::W))
    rw [htake] at hw
    have ht := (CBVtoCBN.stripPrefix_exact (w::W).flatten (sfx x p) (sfx x q)).mpr hs
    simp only [List.length_cons,replay,evV,hw,ht,length_sfx x hq]

def Shifted (rules : List MRule) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i rule, rules[i]? = some rule → ∀ W p q, W.length = rule.arity →
    p ≤ x.length → q ≤ x.length → sfx x p = W.flatten ++ sfx x q →
      valAt (T i (words W)) p = valAt (U i W) q

mutual
  theorem evaluator_of_shift {rules : List MRule} {x : List Char}
      {T U : Nat → List (List Char) → Val}
      (hT : SoundTV (parGrammar rules) x .callByValuePar T)
      (hOk : OkTV x.length T) (hshift : Shifted rules x T U) :
      ∀ e E p, p ≤ x.length →
        evV (parGrammar rules) x .callByValuePar T (words E) (render true E.length e) p =
          evV (seqGrammar rules) x .callByValueSeq U E (render false E.length e) p
    | .param k, E, p, _ => parameters_eq _ _ _ _ _ _ _ E k p
    | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
    | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
    | .dbg _, _, _, _ | .lam _ _, _, _, _ | .callParam _ _, _, _, _
    | .invoke _ _ _, _, _, _ => rfl
    | .call i args, E, p, hp => by
      change evV _ _ _ _ _ (.call i (parsers (renderArgs true E.length args))) p =
        evV _ _ _ _ _ (.call i (renderArgs false E.length args)) p
      cases hr : rules[i]? with
      | none => simp [evV,par_rule,seq_rule,hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · have hrp : ruleAtM (parGrammar rules).rules i =
              some ⟨rule.arity,.seq (replay rule.arity) (render true rule.arity rule.body)⟩ := by
            rw [par_rule,hr]; rfl
          have hrs : ruleAtM (seqGrammar rules).rules i =
              some ⟨rule.arity,render false rule.arity rule.body⟩ := by rw [seq_rule,hr]; rfl
          rw [evV_call_par hrp (by simpa [parsers_length,renderArgs_length] using ha) (by decide),
            evV_call_seq hrs (by simpa [renderArgs_length] using ha),
            arguments_factor hT hOk (words E) _ (renderArgs_firstOrder true E.length args) p hp]
          have heq := arguments_of_shift hT hOk hshift args E p hp
          rw [heq]
          cases hv : evSeqArgs (seqGrammar rules) x .callByValueSeq U E
              (renderArgs false E.length args) p with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W,q⟩ := Wq
              have hs := heq.trans hv
              have hlen : W.length = rule.arity := by
                have hh := evSeq_length _ _ W q hs
                simpa [renderArgs_length,ha] using hh
              exact hshift i rule hr W p q hlen hp (evSeq_mem hOk _ _ _ _ hp hs).2
                (arguments_prefix hT (words E) _ (renderArgs_firstOrder true E.length args) p W q hp hs)
        · simp [evV,par_rule,seq_rule,hr,parsers_length,renderArgs_length,ha]
    | .seq a b, E, p, hp => by
      have heq := evaluator_of_shift hT hOk hshift a E p hp
      cases hv : evV (parGrammar rules) x .callByValuePar T (words E) (render true E.length a) p with
      | none => simp only [render,evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
      | some result => cases result with
        | none => simp only [render,evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          simp only [render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
          exact evaluator_of_shift hT hOk hshift b E q (evV_ok hOk _ p hp q hv)
    | .alt a b, E, p, hp => by
      have heq := evaluator_of_shift hT hOk hshift a E p hp
      cases hv : evV (parGrammar rules) x .callByValuePar T (words E) (render true E.length a) p with
      | none => simp only [render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
      | some result => cases result with
        | none =>
          simp only [render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
          exact evaluator_of_shift hT hOk hshift b E p hp
        | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
    | .notP a, E, p, hp => by
      simp only [render,evV]
      rw [evaluator_of_shift hT hOk hshift a E p hp]
    | .star a, E, p, hp => by
      simp only [render,evV_star]
      exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hshift a E q (by omega))

  theorem arguments_of_shift {rules : List MRule} {x : List Char}
      {T U : Nat → List (List Char) → Val}
      (hT : SoundTV (parGrammar rules) x .callByValuePar T)
      (hOk : OkTV x.length T) (hshift : Shifted rules x T U) :
      ∀ args E p, p ≤ x.length →
        evSeqArgs (parGrammar rules) x .callByValuePar T (words E) (renderArgs true E.length args) p =
          evSeqArgs (seqGrammar rules) x .callByValueSeq U E (renderArgs false E.length args) p
    | [], _, _, _ => rfl
    | a::args, E, p, hp => by
      have heq := evaluator_of_shift hT hOk hshift a E p hp
      simp only [renderArgs,evSeqArgs]
      rw [← heq]
      cases hv : evV (parGrammar rules) x .callByValuePar T (words E) (render true E.length a) p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          dsimp only []
          rw [arguments_of_shift hT hOk hshift args E q (evV_ok hOk _ p hp q hv)]
end


theorem tables_shifted (rules : List MRule) (x : List Char) (m : Nat) :
    Shifted rules x (tblV (parGrammar rules) x .callByValuePar m)
      (tblV (seqGrammar rules) x .callByValueSeq m) := by
  induction m with
  | zero => intro i rule hr W p q hlen hp hq hs; simp [tblV,valAt_nil]
  | succ m ih =>
    intro i rule hr W p q hlen hp hq hs
    have hrp : ruleAtM (parGrammar rules).rules i =
        some ⟨rule.arity,.seq (replay rule.arity) (render true rule.arity rule.body)⟩ := by
      rw [par_rule,hr]; rfl
    have hrs : ruleAtM (seqGrammar rules).rules i =
        some ⟨rule.arity,render false rule.arity rule.body⟩ := by rw [seq_rule,hr]; rfl
    rw [valAt_tblV_succ hrp (words W) hp,valAt_tblV_succ hrs W hq,← hlen,
      evV_seq_ok (replay_eval _ _ _ _ W p q hp hq hs)]
    exact evaluator_of_shift (tblV_sound (par_firstOrder rules) (by decide) m)
      (tblV_ok _ _ _ m) ih rule.body W q hq

/-- Arbitrary recursive calls retain all cumulative source values as views
of consecutive, unbounded runtime chunks. -/
theorem evaluator_eq (rules : List MRule) (x : List Char) (m : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar rules) x .callByValuePar (tblV (parGrammar rules) x .callByValuePar m)
      (words E) (render true E.length e) p =
    evV (seqGrammar rules) x .callByValueSeq (tblV (seqGrammar rules) x .callByValueSeq m)
      E (render false E.length e) p :=
  evaluator_of_shift (tblV_sound (par_firstOrder rules) (by decide) m) (tblV_ok _ _ _ m)
    (tables_shifted rules x m) e E p hp

theorem iterBound_eq (rules : List MRule) (x : List Char) :
    iterBoundV (parGrammar rules) x = iterBoundV (seqGrammar rules) x := by
  have hlen : (parGrammar rules).rules.length = (seqGrammar rules).rules.length := by
    simp [parGrammar,seqGrammar]
  unfold iterBoundV
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [par_rule,seq_rule]
  cases rules[i]? <;> rfl

theorem decide_eq (rules : List MRule) (e : MExp) (x : List Char) :
    decideObsV .callByValuePar (parGrammar rules) x (render true 0 e) =
      decideObsV .callByValueSeq (seqGrammar rules) x (render false 0 e) := by
  unfold decideObsV
  have he := evaluator_eq rules x (iterBoundV (parGrammar rules) x) [] e x.length (Nat.le_refl _)
  simp only [words,List.length_nil] at he
  rw [he,iterBound_eq]

/-- All finite observations on unchanged original strings agree. The source
must have cumulative arguments and a leading longest-prefix replay. -/
theorem observations_iff (rules : List MRule) (e : MExp) (x : List Char)
    (r : Option (List Char)) :
    SObs (parGrammar rules) .callByValuePar (render true 0 e) x r ↔
      SObs (seqGrammar rules) .callByValueSeq (render false 0 e) x r := by
  rw [← decideObsV_iff (par_firstOrder rules) (by decide) (render_firstOrder true 0 e),
    ← decideObsV_iff (seq_firstOrder rules) (by decide) (render_firstOrder false 0 e),
    decide_eq rules e x]

theorem language_translation (rules : List MRule) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar rules) .callByValuePar (render true 0 e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar rules,render false 0 e,seq_firstOrder rules,render_firstOrder false 0 e,
    fun x => observations_iff rules e x (some [])⟩

end Shallot.MacroPeg.CBV.PrefixFamilyFusion
