import MacroPeg.CBV.FragmentStuckRecursive
import MacroPeg.CBV.NullableStarControl

/-! Normalize nullable body loops before recursive fragment capture transfer. -/
namespace Shallot.MacroPeg.CBV.FragmentNullableControl
open ReplayControlFusion (Plan)
open FragmentStuckRecursive (stuck leaf render)

inductive Body where
  | leaf : Nat → Body
  | alt : Body → Body → Body
  | guard : Body → Body → Body
  | notP : Body → Body
  | starNot : Body → Body
  | doubleStar : Body → Body

def Body.syntax (L : Nat → MExp) : Body → MExp
  | .leaf i => L i
  | .alt a b => .alt (a.syntax L) (b.syntax L)
  | .guard a b => .seq (.andP (a.syntax L)) (b.syntax L)
  | .notP a => .notP (a.syntax L)
  | .starNot a => .star (.notP (a.syntax L))
  | .doubleStar a => .star (.star (a.syntax L))

def negativeStar (n : Nat) (P : Plan) : Plan :=
  .alt (.guard (.notP P) (.leaf n)) (.notP (.notP P))
def normalize (n : Nat) : Body → Plan
  | .leaf i => .leaf i
  | .alt a b => .alt (normalize n a) (normalize n b)
  | .guard a b => .guard (normalize n a) (normalize n b)
  | .notP a => .notP (normalize n a)
  | .starNot a => negativeStar n (normalize n a)
  | .doubleStar _ => .leaf n

def Body.Valid (n : Nat) : Body → Prop
  | .leaf i => i≤n
  | .alt a b | .guard a b => a.Valid n ∧ b.Valid n
  | .notP a | .starNot a | .doubleStar a => a.Valid n

theorem normalize_bounded (n : Nat) : ∀ e, e.Valid n → (normalize n e).All (fun i => i≤n)
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => ⟨normalize_bounded n a h.1,normalize_bounded n b h.2⟩
  | .notP a, h => normalize_bounded n a h
  | .starNot a, h => ⟨⟨normalize_bounded n a h,Nat.le_refl n⟩,normalize_bounded n a h⟩
  | .doubleStar _, _ => Nat.le_refl n

theorem negative_star_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (L : Nat → MExp)
    (n : Nat) (hd : ∀ p, evV g x s T E (L n) p=none) (P : Plan) (p : Nat) :
    evV g x s T E ((negativeStar n P).exp L) p=
      evV g x s T E (.star (.notP (P.exp L))) p := by
  simp only [negativeStar,Plan.exp,MExp.andP,evV]
  cases he : evV g x s T E (P.exp L) p with
  | none => rw [evStar_none (by simp only [he])]
  | some v => cases v with
    | none =>
      rw [evStar_stuck (by simp only [he]) (Nat.lt_irrefl p)]
      simp only [hd]
    | some q => rw [evStar_fail (by simp only [he])]

/-- No consumer, sound-table, purity, or totality premise. -/
theorem evaluator_eq (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (L : Nat → MExp)
    (n : Nat) (hd : ∀ p, evV g x s T E (L n) p=none) : ∀ e p,
    evV g x s T E ((normalize n e).exp L) p=evV g x s T E (e.syntax L) p
  | .leaf _, _ => rfl
  | .alt a b, p => by
    simp only [normalize,Plan.exp,Body.syntax,evV,evaluator_eq g x s T E L n hd a p,
      evaluator_eq g x s T E L n hd b p]
  | .guard a b, p => by
    simp only [normalize,Plan.exp,Body.syntax,MExp.andP,evV,evaluator_eq g x s T E L n hd a p]
    cases he : evV g x s T E (a.syntax L) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some _ => exact evaluator_eq g x s T E L n hd b p
  | .notP a, p => by
    simp only [normalize,Plan.exp,Body.syntax,evV,evaluator_eq g x s T E L n hd a p]
  | .starNot a, p => by
    rw [normalize,negative_star_eval g x s T E L n hd]
    simp only [Body.syntax,evV_star]
    apply evStar_congr p
    intro q _
    simp only [evV,evaluator_eq g x s T E L n hd a q]
  | .doubleStar a, p => by
    change evV g x s T E (L n) p=evStar (evStar (fun q => evV g x s T E (a.syntax L) q)) p
    rw [hd,NullableStarControl.nested_star_none]

theorem leaf_stuck (plans : List Plan) (tails : List MExp) : leaf plans tails tails.length=stuck := by
  simp [leaf]

def plans (tails : List MExp) (users : List Body) : List Plan := users.map (normalize tails.length)
def source (tails : List MExp) (users : List Body) : MGrammar :=
  ⟨users.map (fun u => ⟨1,u.syntax (leaf (plans tails users) tails)⟩)++
    ((FragmentStuckRecursive.source (plans tails users) tails).rules.drop users.length)⟩
abbrev core (tails : List MExp) (users : List Body) := FragmentStuckRecursive.source (plans tails users) tails
abbrev target (tails : List MExp) (users : List Body) := FragmentStuckRecursive.target (plans tails users) tails
abbrev sourceRender (tails : List MExp) (users : List Body) := render tails.length (plans tails users) true false
abbrev targetRender (tails : List MExp) (users : List Body) := render tails.length (plans tails users) false false

theorem valid (tails : List MExp) (users : List Body) (hu : ∀ u∈users, u.Valid tails.length) :
    FragmentStuckRecursive.Valid (plans tails users) tails := by
  intro P hp
  obtain ⟨u,hm,rfl⟩ := List.mem_map.mp hp
  exact normalize_bounded tails.length u (hu u hm)

private theorem rules (tails : List MExp) (users : List Body) :
    (core tails users).rules=
      (plans tails users).map (fun P => ⟨1,P.exp (leaf (plans tails users) tails)⟩)++
      (core tails users).rules.drop users.length := by
  have hl : (plans tails users).length=users.length := by simp [plans]
  simp only [core,FragmentStuckRecursive.source]
  rw [←hl]
  simp only [List.drop_append,List.length_map,←List.map_drop,List.drop_length,Nat.sub_self,Nat.zero_sub,List.drop_zero,List.nil_append,List.map_nil]

theorem headers (tails : List MExp) (users : List Body) (i : Nat) :
    (ruleAtM (source tails users).rules i).map MRule.arity=
      (ruleAtM (core tails users).rules i).map MRule.arity := by
  have h : (source tails users).rules.map MRule.arity=(core tails users).rules.map MRule.arity := by
    rw [source]
    conv => rhs; rw [rules]
    simp only [plans,List.map_append,List.map_map,Function.comp_def,core]
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using congrArg (fun l => l[i]?) h

theorem body_results (tails : List MExp) (users : List Body) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    (source tails users).rules.map (fun r => evV g x s T E r.body p)=
      (core tails users).rules.map (fun r => evV g x s T E r.body p) := by
  rw [source]
  conv => rhs; rw [rules]
  simp only [List.map_append,List.map_map,plans,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro u _
  exact (evaluator_eq g x s T E (leaf (plans tails users) tails) tails.length
    (fun q => by rw [leaf_stuck]; exact MixedOriginControl.stuck_eval _ _ _ _ _ q) u p).symm


theorem tables_eq (tails : List MExp) (users : List Body) (x : List Char) (s : Strategy) : ∀ k,
    tblV (source tails users) x s k=tblV (core tails users) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hh := headers tails users i
    simp only [tblV]
    cases hs : ruleAtM (source tails users).rules i with
    | none =>
      cases ht : ruleAtM (core tails users).rules i with
      | none => rfl
      | some r => simp [hs,ht] at hh
    | some r =>
      cases ht : ruleAtM (core tails users).rules i with
      | none => simp [hs,ht] at hh
      | some t =>
        apply List.map_congr_left
        intro p _
        rw [ih]
        have hb := congrArg (fun l => l[i]?)
          (body_results tails users (core tails users) x s (tblV (core tails users) x s k) E p)
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hs,ht,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (source tails users) (core tails users)
          (headers tails users) x s _ E r.body p).trans hb

theorem grammar_evaluator_eq (tails : List MExp) (users : List Body) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source tails users) x s (tblV (source tails users) x s k) E e p=
      evV (core tails users) x s (tblV (core tails users) x s k) E e p := by
  rw [tables_eq tails users x s k]
  exact ContinuationGrammar.eval_headers (source tails users) (core tails users) (headers tails users) x s _ E e p

theorem body_firstOrder (L : Nat → MExp) (hL : ∀ i, (L i).FirstOrder) :
    ∀ (u : Body), (u.syntax L).FirstOrder
  | .leaf i => hL i
  | .alt a b | .guard a b => ⟨body_firstOrder L hL a,body_firstOrder L hL b⟩
  | .notP a | .starNot a | .doubleStar a => body_firstOrder L hL a

theorem source_firstOrder (tails : List MExp) (users : List Body) : (source tails users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    exact body_firstOrder _ (FragmentStuckRecursive.leaf_firstOrder _ _) u
  · exact FragmentStuckRecursive.source_firstOrder _ _ r (List.mem_of_mem_drop hr)

/-- Actual nullable stars stay in the source grammar. Its complete ordinary
clock tables agree with the normalized core, then transfer to fixed Seq. -/
theorem observations_iff (tails : List MExp) (users : List Body)
    (hu : ∀ u∈users, u.Valid tails.length) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source tails users) .callByValuePar (sourceRender tails users e) x r ↔
      SObs (target tails users) .callByValueSeq (targetRender tails users e) x r := by
  have hnorm : SObs (source tails users) .callByValuePar (sourceRender tails users e) x r ↔
      SObs (core tails users) .callByValuePar (sourceRender tails users e) x r := by
    rw [←decideObsV_iff (source_firstOrder tails users) (by decide)
        (FragmentStuckRecursive.render_firstOrder _ _ true false e),
      ←decideObsV_iff (FragmentStuckRecursive.source_firstOrder _ _) (by decide)
        (FragmentStuckRecursive.render_firstOrder _ _ true false e)]
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (source tails users) (core tails users) x .callByValuePar .callByValuePar
      (sourceRender tails users e) (sourceRender tails users e)
      (fun k => grammar_evaluator_eq tails users x .callByValuePar k [] _ x.length)]
  exact hnorm.trans (FragmentStuckRecursive.observations_iff _ _ (valid tails users hu) e x r)

theorem language_translation (tails : List MExp) (users : List Body)
    (hu : ∀ u∈users, u.Valid tails.length) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source tails users) .callByValuePar (sourceRender tails users e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target tails users,targetRender tails users e,FragmentStuckRecursive.target_firstOrder _ _,
    FragmentStuckRecursive.render_firstOrder _ _ false false e,fun x => observations_iff tails users hu e x (some [])⟩

end Shallot.MacroPeg.CBV.FragmentNullableControl
