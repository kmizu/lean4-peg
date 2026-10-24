import MacroPeg.CBV.GeneralStarFilter

/-! Inline state filters for parameter-dependent finite parser control.
Fresh recursive helper captures can be mixed with retained parameters. -/
namespace Shallot.MacroPeg.CBV.DependentCaptureFilter
open RegularCaptureProduct
open CaptureTransitionProfile (profile)
open ClockFreezing (Table)

inductive Expr where
  | lit (w : List Char)
  | param (k : Nat)
  | helper (i : Nat)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | notP (a : Expr)
  | star (a : Expr)

def render : Expr → MExp
  | .lit w => .lit w
  | .param k => .param k
  | .helper i => .call i []
  | .seq a b => .seq (render a) (render b)
  | .alt a b => .alt (render a) (render b)
  | .notP a => .notP (render a)
  | .star a => .star (render a)

def Valid (nodes : List Node) : Expr → Prop
  | .helper i => i<nodes.length
  | .seq a b | .alt a b => Valid nodes a ∧ Valid nodes b
  | .notP a => Valid nodes a
  | .star a => Valid nodes a
  | _ => True

def Accurate (D : Machine) (S : List (List Nat)) (E : List (List Char)) : Prop :=
  ∀ (k : Nat) (w : List Char), E[k]?=some w → S[k]?=some (profile D w)

def nextState (S : List (List Nat)) (k q : Nat) : Option Nat := S[k]?.bind (fun P => P[q]?)

def filter (nodes : List Node) (D : Machine) (S : List (List Nat)) : Expr → Nat → Nat → MExp
  | .lit w, q, r => .seq (.lit w) (if some (run D q w)=some r then .eps else MExp.failAlways)
  | .param k, q, r => .seq (.param k) (if nextState S k q=some r then .eps else MExp.failAlways)
  | .helper i, q, r => call nodes D i q r
  | .seq a b, q, r => choice ((List.range D.width).map (fun t =>
      .seq (filter nodes D S a q t) (filter nodes D S b t r)))
  | .alt a b, q, r => RootObservation.branch (.andP (render a)) (filter nodes D S a q r) (filter nodes D S b q r)
  | .star a, q, r => GeneralStarFilter.filter D.width (render a) (fun q r => filter nodes D S a q r) q r
  | .notP a, q, r => .seq (.notP (render a)) (if some q=some r then .eps else MExp.failAlways)

theorem render_firstOrder : ∀ a, (render a).FirstOrder
  | .lit _ | .param _ | .helper _ => True.intro
  | .seq a b | .alt a b => ⟨render_firstOrder a,render_firstOrder b⟩
  | .notP a | .star a => render_firstOrder a

theorem filter_firstOrder (nodes : List Node) (D : Machine) (S : List (List Nat)) :
    ∀ a q r, (filter nodes D S a q r).FirstOrder
  | .lit _, _, _ | .param _, _, _ => by simp only [filter]; split <;> trivial
  | .helper _, _, _ => True.intro
  | .star a, q, r => GeneralStarFilter.filter_firstOrder D.width (render a) (render_firstOrder a)
      _ (fun q r => filter_firstOrder nodes D S a q r) q r
  | .seq a b, q, r => by
    apply choice_firstOrder
    intro e he
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
    exact ⟨filter_firstOrder nodes D S a q t,filter_firstOrder nodes D S b t r⟩
  | .alt a b, q, r => ⟨⟨render_firstOrder a,filter_firstOrder nodes D S a q r⟩,
      render_firstOrder a,filter_firstOrder nodes D S b q r⟩
  | .notP a, q, r => by
    simp only [filter]
    split <;> exact ⟨render_firstOrder a,True.intro⟩

/-- Sound evaluation supplies consumed prefixes with retained parameters,
for either CBV strategy. -/
theorem success_prefix {g : MGrammar} {x : List Char} {s : Strategy} {T : Table}
    (hs : s≠.callByName) (hT : SoundTV g x s T) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (p j : Nat) (hp : p≤x.length)
    (hv : evV g x s T E e p=some (some j)) :
    j≤x.length ∧ sfx x p=pre x p j++sfx x j := by
  have hf : (MExp.subst (E.map MExp.lit) e).FirstOrder := firstOrder_subst (firstOrderArgs_lits E) e he
  have hv' : evV g x s T [] (MExp.subst (E.map MExp.lit) e) p=some (some j) := by
    rw [evV_subst E e he]; exact hv
  obtain ⟨o,hd,ho⟩ := evV_sound hs hT _ hf p hp _ hv'
  obtain ⟨t,rest,rfl,hj⟩ := obsR_ok ho
  have hpre := mderives_suffix hd _ _ rfl
  have hr := rest_eq_sfx' hd
  rw [hj] at hr
  have hlen : j≤x.length := by
    obtain ⟨w,hw⟩ := hpre
    have hl := congrArg List.length hw
    rw [List.length_append,length_sfx x hp,hj] at hl
    omega
  refine ⟨hlen,?_⟩
  rw [hr]
  simpa [hj] using pre_split hp hpre

theorem atom_correct (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (D : Machine) (E : List (List Char)) (e : MExp) (q r p : Nat) (state : Option Nat)
    (hstate : ∀ j, evV g x s T E e p=some (some j) → state=some (run D q (pre x p j))) :
    evV g x s T E (.seq e (if state=some r then .eps else MExp.failAlways)) p =
      filtered D x q r p (evV g x s T E e p) := by
  cases hv : evV g x s T E e p with
  | none => rw [evV_seq_none hv]; rfl
  | some result => cases result with
    | none => rw [evV_seq_fail hv]; rfl
    | some j =>
      rw [evV_seq_ok hv,hstate j hv]
      simp only [Option.some.injEq,filtered]
      split <;> rfl

abbrev table (nodes : List Node) (D : Machine) (x : List Char) : Table :=
  tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)

/-- Correct profiles suffice for filtering parameter-dependent control.
The profiles themselves are finite, while the retained strings and fresh
recursive helper captures have no length bound. -/
theorem correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (S : List (List Nat)) (E : List (List Char))
    (hS : Accurate D S E) :
    ∀ a, Valid nodes a → ∀ p, p≤x.length → ∀ q r, q<D.width → r<D.width →
      evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (filter nodes D S a q r) p =
        filtered D x q r p (evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p)
  | .star a, ha, p, hp, q, r, hq, _ =>
    GeneralStarFilter.correct D hD (grammar nodes D) x .callByValueSeq (by decide) (table nodes D x)
      (tblV_sound (grammar_firstOrder nodes D) (by decide) _) E (render a) (render_firstOrder a) _
      (fun q r p hq hr hp => correct nodes hNodes D hD x S E hS a ha p hp q r hq hr) q r p hq hp
  | .lit w, _, p, hp, q, r, _, _ => by
    apply atom_correct (state := some (run D q w))
    intro j hv
    have hw := WordArguments.value_of_success (grammar nodes D) x .callByValueSeq (table nodes D x)
      E (.lit w) True.intro p j hp hv
    have he : w=pre x p j := by simpa only [WordArguments.value,Option.some.injEq] using hw
    rw [he]
  | .param k, _, p, hp, q, r, hq, _ => by
    apply atom_correct
    intro j hv
    cases hw : E[k]? with
    | none => simp [evV,hw] at hv
    | some w =>
      have he := WordArguments.value_of_success (grammar nodes D) x .callByValueSeq (table nodes D x)
        E (.param k) True.intro p j hp hv
      have he' : w=pre x p j := by simpa only [WordArguments.value,hw,Option.some.injEq] using he
      rw [nextState,hS k w hw,Option.bind_some,CaptureTransitionProfile.profile_get D w q hq,he']
  | .helper i, hi, p, hp, q, r, hq, hr => by
    simp only [filter,render]
    rw [product_call_eval nodes D hD.1 x .callByValueSeq _ E i q r hi hq hr p,
      original_call_eval nodes D x .callByValueSeq _ E i nodes[i] (List.getElem?_eq_getElem hi) p]
    exact product_at_fixed nodes hNodes D hD x _ (bound_fixed _ _ _) i q r p hi hq hr hp
  | .seq a b, ha, p, hp, q, r, hq, hr => by
    simp only [filter,render]
    cases hv : evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p with
    | none =>
      rw [evV_seq_none hv]
      apply RecursiveFilteredOverlap.choice_none
      · intro hn
        have hl := congrArg List.length hn
        simp only [List.length_range,List.length_nil] at hl
        omega
      · intro t ht
        have he := correct nodes hNodes D hD x S E hS a ha.1 p hp q t hq (List.mem_range.mp ht)
        rw [hv] at he
        exact evV_seq_none he
    | some result => cases result with
      | none =>
        rw [evV_seq_fail hv]
        apply CaptureTransitionProfile.choice_failed
        intro t ht
        have he := correct nodes hNodes D hD x S E hS a ha.1 p hp q t hq (List.mem_range.mp ht)
        rw [hv] at he
        exact evV_seq_fail he
      | some z =>
        have hSound := tblV_sound (x := x) (s := .callByValueSeq) (grammar_firstOrder nodes D) (by decide) (iterBoundV (grammar nodes D) x)
        have hz := success_prefix (by decide) hSound E (render a) (render_firstOrder a) p z hp hv
        have ht := run_bound hD q hq (pre x p z)
        rw [CaptureTransitionProfile.choice_unique (chosen := run D q (pre x p z))
          (v := filtered D x (run D q (pre x p z)) r z
            (evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render b) z))]
        · rw [if_pos (List.mem_range.mpr ht),evV_seq_ok hv]
          cases hb : evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render b) z with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some j =>
              have hj := success_prefix (by decide) hSound E (render b) (render_firstOrder b) z j hz.1 hb
              have he := SequenceArguments.pre_concat hp hj.1 hz.2 hj.2
              simp only [filtered,he,run_append]
        · intro t hmem
          have he := correct nodes hNodes D hD x S E hS a ha.1 p hp q t hq (List.mem_range.mp hmem)
          rw [hv] at he
          simp only [filtered] at he
          by_cases ht' : t=run D q (pre x p z)
          · subst t
            rw [if_pos rfl] at he
            rw [evV_seq_ok he,if_pos rfl]
            exact correct nodes hNodes D hD x S E hS b ha.2 z hz.1 _ r ht hr
          · rw [if_neg (Ne.symm ht')] at he
            rw [evV_seq_fail he,if_neg ht']
  | .alt a b, ha, p, hp, q, r, hq, hr => by
    simp only [filter,render]
    rw [ChoiceArguments.branch_eval]
    cases hv : evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p with
    | none => rw [evV_alt_none hv]; rfl
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv]
        exact correct nodes hNodes D hD x S E hS b ha.2 p hp q r hq hr
      | some j =>
        rw [evV_alt_ok hv]
        simpa only [hv] using correct nodes hNodes D hD x S E hS a ha.1 p hp q r hq hr
  | .notP a, _, p, hp, q, r, hq, hr => by
    apply atom_correct (state := some q)
    intro j hv
    change evV _ _ _ _ E (.notP (render a)) p=some (some j) at hv
    cases he : evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p with
    | none => simp [evV,he] at hv
    | some result => cases result with
      | some z => simp [evV,he] at hv
      | none =>
        have hj : p=j := by simpa only [evV,he,Option.some.injEq] using hv
        subst j
        simp [pre,run]

theorem environment_accurate (D : Machine) (E : List (List Char)) :
    Accurate D (E.map (profile D)) E := by
  intro k w hw
  simp [List.getElem?_map,hw]

/-- Source argument queries use only retained values and independent helper
calls, so Par and Seq agree before the state constraint is imposed. -/
theorem render_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (x : List Char) (E : List (List Char)) :
    ∀ a, Valid nodes a → ∀ p, p≤x.length →
      evV (grammar nodes D) x .callByValuePar
        (tblV (grammar nodes D) x .callByValuePar (iterBoundV (grammar nodes D) x)) E (render a) p =
      evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p
  | .star a, ha, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun z hz => render_eq nodes hNodes D x E a ha z (by omega))
  | .lit _, _, _, _ | .param _, _, _, _ => rfl
  | .helper i, hi, p, hp => by
    simp only [render]
    rw [original_call_eval nodes D x .callByValuePar _ E i nodes[i] (List.getElem?_eq_getElem hi) p,
      original_call_eval nodes D x .callByValueSeq _ E i nodes[i] (List.getElem?_eq_getElem hi) p]
    exact canonical_helpers_eq (helper_valid hNodes) (original_installed nodes D) (original_installed nodes D)
      x .callByValuePar .callByValueSeq i p (by simpa [Valid] using hi) hp
  | .seq a b, ha, p, hp => by
    have he := render_eq nodes hNodes D x E a ha.1 p hp
    simp only [render]
    cases hv : evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (he.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (he.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (he.trans hv)]
        exact render_eq nodes hNodes D x E b ha.2 z (evV_ok (tblV_ok _ _ _ _) _ p hp z hv)
  | .alt a b, ha, p, hp => by
    have he := render_eq nodes hNodes D x E a ha.1 p hp
    simp only [render]
    cases hv : evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (render a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (he.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (he.trans hv)]
        exact render_eq nodes hNodes D x E b ha.2 p hp
      | some z => rw [evV_alt_ok hv,evV_alt_ok (he.trans hv)]
  | .notP a, ha, p, hp => by
    have he := render_eq nodes hNodes D x E a ha p hp
    change (match evV _ _ _ _ E (render a) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [he]
    rfl

theorem correct_par (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (S : List (List Nat)) (E : List (List Char))
    (hS : Accurate D S E) (a : Expr) (ha : Valid nodes a) (p : Nat) (hp : p≤x.length)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (filter nodes D S a q r) p =
      filtered D x q r p (evV (grammar nodes D) x .callByValuePar
        (tblV (grammar nodes D) x .callByValuePar (iterBoundV (grammar nodes D) x)) E (render a) p) := by
  rw [correct nodes hNodes D hD x S E hS a ha p hp q r hq hr,
    render_eq nodes hNodes D x E a ha p hp]

/-- Correct incoming metadata follows from an actual generated profile
guard on the original capture, rather than from a semantic advice premise. -/
theorem guard_accurate (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (i p j : Nat) (hi : i<nodes.length)
    (hp : p≤x.length) (P : List Nat) (hP : P∈CaptureTransitionProfile.profiles D)
    (hv : evV (grammar nodes D) x .callByValueSeq (table nodes D x) [] (.call i []) p=some (some j))
    (hg : evV (grammar nodes D) x .callByValueSeq (table nodes D x) []
      (CaptureTransitionProfile.guard nodes D i P) p=some (some p)) :
    Accurate D [P] [pre x p j] := by
  have he := CaptureTransitionProfile.guard_correct nodes hNodes D hD x i p hi hp P hP
  dsimp only [] at he
  rw [hv] at he
  dsimp only [] at he
  have heq : P=profile D (pre x p j) := by
    by_cases h : P=profile D (pre x p j)
    · exact h
    · rw [if_neg h,hg] at he
      cases he
  rw [heq]
  exact environment_accurate D [pre x p j]

/-- A real origin guard and retained captured string justify filtering the
next parameter-dependent argument after the original capture has consumed
input. The original Par argument and the generated Seq filter share the
successful endpoint; a wrong state is finite failure. -/
theorem guarded_argument_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (x : List Char) (i p j : Nat) (hi : i<nodes.length)
    (hp : p≤x.length) (hj : j≤x.length) (P : List Nat) (hP : P∈CaptureTransitionProfile.profiles D)
    (hv : evV (grammar nodes D) x .callByValueSeq (table nodes D x) [] (.call i []) p=some (some j))
    (hg : evV (grammar nodes D) x .callByValueSeq (table nodes D x) []
      (CaptureTransitionProfile.guard nodes D i P) p=some (some p))
    (a : Expr) (ha : Valid nodes a) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (grammar nodes D) x .callByValueSeq (table nodes D x) [pre x p j]
        (filter nodes D [P] a q r) j =
      filtered D x q r j (evV (grammar nodes D) x .callByValuePar
        (tblV (grammar nodes D) x .callByValuePar (iterBoundV (grammar nodes D) x)) [pre x p j] (render a) j) :=
  correct_par nodes hNodes D hD x [P] [pre x p j]
    (guard_accurate nodes hNodes D hD x i p j hi hp P hP hv hg) a ha j hj q r hq hr

def exampleMachine : Machine := ⟨2,fun q c => if c='a' then 0 else if c='c' then 1 else q⟩

def exampleNodes : List Node := [.alt 1 2,.lit ['a'],.lit ['b'],.star 4,.lit ['b']]

def exampleArgument : Expr := .seq (.lit ['c']) (.seq (.param 0) (.helper 3))

def exampleGrammar : MGrammar :=
  let base := grammar exampleNodes exampleMachine
  ⟨base.rules++(CaptureTransitionProfile.profiles exampleMachine).map (fun P =>
    ⟨1,.seq (.lit ['#']) (.seq (filter exampleNodes exampleMachine [P] exampleArgument 0 0)
      (.seq (.lit ['#']) (.notP .any)))⟩)⟩

def exampleStart : MExp :=
  CaptureTransitionProfile.select exampleNodes exampleMachine 0 (fun P =>
    .call ((grammar exampleNodes exampleMachine).rules.length+
      (CaptureTransitionProfile.profiles exampleMachine).idxOf P) [.call 0 []])

/-- An actual Seq caller selects finite metadata, retains a/b, and filters
c + retained value + a fresh greedy b* capture. Both old words have ending
state zero from zero, but the full profiles distinguish their later use.
Supplying the a profile for a retained b would incorrectly pass the filter. -/
theorem dependent_argument_execution :
    let good := "a#cabb#".toList
    let bad := "b#cbbb#".toList
    let g := exampleGrammar
    let base := grammar exampleNodes exampleMachine
    (evV g good .callByValueSeq (tblV g good .callByValueSeq 16) [] exampleStart good.length=some (some 0)) ∧
    (evV g bad .callByValueSeq (tblV g bad .callByValueSeq 16) [] exampleStart bad.length=some none) ∧
    (run exampleMachine 0 ['a']=run exampleMachine 0 ['b']) ∧
    (let x := "cbbb#".toList
     let T := tblV base x .callByValueSeq 16
     evV base x .callByValueSeq T [['b']]
       (filter exampleNodes exampleMachine [profile exampleMachine ['b']] exampleArgument 0 0) x.length=some none ∧
     evV base x .callByValueSeq T [['b']]
       (filter exampleNodes exampleMachine [profile exampleMachine ['a']] exampleArgument 0 0) x.length=some (some 1)) := by
  decide +kernel

end Shallot.MacroPeg.CBV.DependentCaptureFilter
