import MacroPeg.CBV.SequentialCaptureObserver
import MacroPeg.CBV.ControlFilter

namespace Shallot.MacroPeg.CBV.SequentialRecursiveObserver
open RegularCaptureProduct (Machine filtered run choice)
open CaptureTransitionProfile (profile profiles)
open ClockFreezing (Table)

/-- Structurally nested actual unary arguments and ordinary PEG control.
The rule bodies may be mutually recursive. -/
inductive Expr where
  | lit (w : List Char)
  | param (k : Nat)
  | user (i : Nat) (a : Expr)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | star (a : Expr)
  | notP (a : Expr)

def render : Expr → MExp
  | .lit w => .lit w
  | .param k => .param k
  | .user i a => .call i [render a]
  | .seq a b => .seq (render a) (render b)
  | .alt a b => .alt (render a) (render b)
  | .star a => .star (render a)
  | .notP a => .notP (render a)

def Valid (bodies : List Expr) : Expr → Prop
  | .user i a => i<bodies.length ∧ Valid bodies a
  | .seq a b | .alt a b => Valid bodies a ∧ Valid bodies b
  | .star a | .notP a => Valid bodies a
  | _ => True

def check (size : Nat) : Expr → Bool
  | .user i a => decide (i<size) && check size a
  | .seq a b | .alt a b => check size a && check size b
  | .star a | .notP a => check size a
  | _ => true

theorem check_sound (bodies : List Expr) : ∀ e, check bodies.length e=true → Valid bodies e
  | .user _i a, h => ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      check_sound bodies a (Bool.and_eq_true_iff.mp h).2⟩
  | .seq a b, h | .alt a b, h =>
      ⟨check_sound bodies a (Bool.and_eq_true_iff.mp h).1,check_sound bodies b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a, h | .notP a, h => check_sound bodies a h
  | .lit _, _ | .param _, _ => True.intro

def keys (D : Machine) (bodies : List Expr) : List (Nat × List Nat × Nat × Nat) :=
  (List.range bodies.length).flatMap (fun i => (profiles D).flatMap (fun P =>
    (List.range D.width).flatMap (fun q => (List.range D.width).map (fun r => (i,P,q,r)))))

def address (D : Machine) (bodies : List Expr) (i : Nat) (P : List Nat) (q r : Nat) : Nat :=
  bodies.length+(keys D bodies).idxOf (i,P,q,r)

def filter (D : Machine) (bodies : List Expr) (S : List (List Nat)) : Expr → Nat → Nat → MExp
  | .lit w, q, r => .seq (.lit w) (if some (run D q w)=some r then .eps else MExp.failAlways)
  | .param k, q, r => .seq (.param k) (if DependentCaptureFilter.nextState S k q=some r then .eps else MExp.failAlways)
  | .user i a, q, r => ProfileControl.select D (render a) (fun q r => filter D bodies S a q r)
      (fun P => .call (address D bodies i P (P[q]?.getD 0) r) [render a])
  | .seq a b, q, r => choice ((List.range D.width).map (fun t =>
      .seq (filter D bodies S a q t) (filter D bodies S b t r)))
  | .alt a b, q, r => RootObservation.branch (.andP (render a)) (filter D bodies S a q r) (filter D bodies S b q r)
  | .star a, q, r => GeneralStarFilter.filter D.width (render a) (fun q r => filter D bodies S a q r) q r
  | .notP a, q, r => .seq (.notP (render a)) (if some q=some r then .eps else MExp.failAlways)

def original (bodies : List Expr) : List MRule := bodies.map (fun b => ⟨1,render b⟩)
def products (D : Machine) (bodies : List Expr) : List MRule :=
  (keys D bodies).map (fun (i,P,q,r) => ⟨1,match bodies[i]? with
    | none => MExp.failAlways | some b => filter D bodies [P] b q r⟩)
def grammar (D : Machine) (bodies : List Expr) : MGrammar := ⟨original bodies++products D bodies⟩

theorem render_firstOrder : ∀ e, (render e).FirstOrder
  | .lit _ | .param _ => True.intro
  | .user _ a => ⟨render_firstOrder a,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder a,render_firstOrder b⟩
  | .star a | .notP a => render_firstOrder a

theorem filter_firstOrder (D : Machine) (bodies : List Expr) (S : List (List Nat)) :
    ∀ e q r, (filter D bodies S e q r).FirstOrder
  | .lit _, _, _ | .param _, _, _ => by simp only [filter]; split <;> trivial
  | .user i a, q, r => ProfileControl.select_firstOrder D _ _ (render_firstOrder a)
      (fun q r => filter_firstOrder D bodies S a q r) _ (fun _ _ => ⟨render_firstOrder a,True.intro⟩)
  | .seq a b, q, r => by
      apply RegularCaptureProduct.choice_firstOrder
      intro e he
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
      exact ⟨filter_firstOrder D bodies S a q t,filter_firstOrder D bodies S b t r⟩
  | .alt a b, q, r => ⟨⟨render_firstOrder a,filter_firstOrder D bodies S a q r⟩,
      render_firstOrder a,filter_firstOrder D bodies S b q r⟩
  | .star a, q, r => GeneralStarFilter.filter_firstOrder D.width _ (render_firstOrder a) _
      (fun q r => filter_firstOrder D bodies S a q r) q r
  | .notP a, q, r => by simp only [filter]; split <;> exact ⟨render_firstOrder a,True.intro⟩

theorem firstOrder (D : Machine) (bodies : List Expr) : (grammar D bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact render_firstOrder b
  · obtain ⟨⟨i,P,q,r⟩,_,rfl⟩ := List.mem_map.mp hr
    dsimp only []
    cases bodies[i]? with
    | none => trivial
    | some b => exact filter_firstOrder D bodies [P] b q r

theorem original_rule (D : Machine) (bodies : List Expr) (i : Nat) (b : Expr) (hi : bodies[i]?=some b) :
    ruleAtM (grammar D bodies).rules i=some ⟨1,render b⟩ := by
  simp only [grammar,original,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.mp hi).1)]
  simp only [List.getElem?_map,hi,Option.map_some]

theorem key_mem (D : Machine) (bodies : List Expr) (i : Nat) (hi : i<bodies.length)
    (P : List Nat) (hP : P∈profiles D) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    (i,P,q,r)∈keys D bodies :=
  List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_flatMap.mpr ⟨P,hP,
    List.mem_flatMap.mpr ⟨q,List.mem_range.mpr hq,List.mem_map.mpr ⟨r,List.mem_range.mpr hr,rfl⟩⟩⟩⟩

theorem product_rule (D : Machine) (bodies : List Expr) (i : Nat) (b : Expr) (hi : bodies[i]?=some b)
    (P : List Nat) (hP : P∈profiles D) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    ruleAtM (grammar D bodies).rules (address D bodies i P q r)=some ⟨1,filter D bodies [P] b q r⟩ := by
  have hk := DependentProfileCall.index_correct (i,P,q,r) (keys D bodies)
    (key_mem D bodies i (List.getElem?_eq_some_iff.mp hi).1 P hP q r hq hr)
  simp only [grammar,address,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp [original])]
  simp only [original,List.length_map,Nat.add_sub_cancel_left,products,List.getElem?_map,hk,Option.map_some,hi]

/-- The actual original and product rows can be installed in a larger
first-order grammar, alongside scanners and other closed components. -/
structure Installed (D : Machine) (bodies : List Expr) (g : MGrammar) : Prop where
  original : ∀ i b, bodies[i]?=some b → ruleAtM g.rules i=some ⟨1,render b⟩
  product : ∀ i b, bodies[i]?=some b → ∀ P, P∈profiles D → ∀ q r, q<D.width → r<D.width →
    ruleAtM g.rules (address D bodies i P q r)=some ⟨1,filter D bodies [P] b q r⟩

theorem installed (D : Machine) (bodies : List Expr) : Installed D bodies (grammar D bodies) :=
  ⟨original_rule D bodies,product_rule D bodies⟩

theorem rule_append (before extra : List MRule) (i : Nat) (r : MRule)
    (h : ruleAtM before i=some r) : ruleAtM (before++extra) i=some r := by
  rw [ruleAtM_eq_getElem?] at *
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1,h]

theorem installed_append (D : Machine) (bodies : List Expr) (extra : List MRule) :
    Installed D bodies ⟨(grammar D bodies).rules++extra⟩ := by
  constructor
  · intro i b hi
    exact rule_append _ extra i _ (original_rule D bodies i b hi)
  · intro i b hi P hP q r hq hr
    exact rule_append _ extra _ _ (product_rule D bodies i b hi P hP q r hq hr)

def Rows (D : Machine) (bodies : List Expr) (x : List Char) (T : Table) : Prop :=
  ∀ i b, bodies[i]?=some b → ∀ w p q r, p≤x.length → q<D.width → r<D.width →
    valAt (T (address D bodies i (profile D w) q r) [w]) p=
      filtered D x q r p (valAt (T i [w]) p)

/-- A recursive argument is evaluated at the same physical stage. Once
its whole profile is selected, a previous-stage callee row takes over. -/
theorem call_correct (D : Machine) (hD : D.Valid) (bodies : List Expr) (g : MGrammar) (hg : Installed D bodies g) (x : List Char)
    (T : Table) (hT : SoundTV g x .callByValueSeq T) (hRows : Rows D bodies x T)
    (i : Nat) (b : Expr) (hi : bodies[i]?=some b) (a : Expr) (S : List (List Nat))
    (E : List (List Char)) (p : Nat) (hp : p≤x.length)
    (hF : ∀ q r, q<D.width → r<D.width →
      evV g x .callByValueSeq T E (filter D bodies S a q r) p=
        filtered D x q r p (evV g x .callByValueSeq T E (render a) p))
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV g x .callByValueSeq T E (filter D bodies S (.user i a) q r) p=
      filtered D x q r p (evV g x .callByValueSeq T E (render (.user i a)) p) := by
  rw [filter,ProfileControl.select_correct D hD _ x .callByValueSeq T E (render a) _ p hF]
  rw [render,evV_call_seq (hg.original i b hi) rfl]
  simp only [evSeqArgs]
  cases hv : evV g x .callByValueSeq T E (render a) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := DependentCaptureFilter.success_prefix (by decide) hT E (render a) (render_firstOrder a) p j hp hv
      have ht := RegularCaptureProduct.run_bound hD q hq (pre x p j)
      dsimp only []
      rw [CaptureTransitionProfile.profile_get D (pre x p j) q hq,Option.getD_some,
        evV_call_seq (hg.product i b hi _ (CaptureTransitionProfile.profile_mem D hD _) _ r ht hr) rfl]
      simp only [evSeqArgs,hv]
      rw [hRows i b hi _ j _ r hj.1 ht hr]
      exact (CapturePrefixRows.filter_prefix D x (pre x p j) p j q r hp hj.1 hj.2
        (valAt (T i [pre x p j]) j)
        (fun z hz => CapturePrefixRows.row_success_prefix _ x .callByValueSeq T hT i _
          (hg.original i b hi) [pre x p j] rfl j z hj.1 hz)).symm

/-- Structural argument nesting is separate from the row-clock induction.
Ordinary choices retain the original successful branch, and stars retain
the original stopping point and nullable divergence. -/
theorem evaluator_of_rows (D : Machine) (hD : D.Valid) (bodies : List Expr) (g : MGrammar) (hg : Installed D bodies g) (x : List Char)
    (T : Table) (hT : SoundTV g x .callByValueSeq T) (hRows : Rows D bodies x T) :
    ∀ e, Valid bodies e → ∀ S E, DependentCaptureFilter.Accurate D S E →
      ∀ p, p≤x.length → ∀ q r, q<D.width → r<D.width →
    evV g x .callByValueSeq T E (filter D bodies S e q r) p=
      filtered D x q r p (evV g x .callByValueSeq T E (render e) p)
  | .lit w, _, S, E, _, p, hp, q, r, _, _ => by
    apply DependentCaptureFilter.atom_correct (state := some (run D q w))
    intro j hv
    have hw := WordArguments.value_of_success g x .callByValueSeq T
      E (.lit w) True.intro p j hp hv
    have he : w=pre x p j := by simpa only [WordArguments.value,Option.some.injEq] using hw
    rw [he]
  | .param k, _, S, E, hS, p, hp, q, r, hq, _ => by
    apply DependentCaptureFilter.atom_correct
    intro j hv
    cases hw : E[k]? with
    | none => simp [evV,hw] at hv
    | some w =>
      have he := WordArguments.value_of_success g x .callByValueSeq T
        E (.param k) True.intro p j hp hv
      have he' : w=pre x p j := by simpa only [WordArguments.value,hw,Option.some.injEq] using he
      rw [DependentCaptureFilter.nextState,hS k w hw,Option.bind_some,
        CaptureTransitionProfile.profile_get D w q hq,he']
  | .user i a, ha, S, E, hS, p, hp, q, r, hq, hr => by
    have hib : i<bodies.length := ha.1
    have hi : bodies[i]?=some bodies[i] := List.getElem?_eq_getElem hib
    exact call_correct D hD bodies g hg x T hT hRows i bodies[i] hi a S E p hp
      (fun q r hq hr => evaluator_of_rows D hD bodies g hg x T hT hRows a ha.2 S E hS p hp q r hq hr) q r hq hr
  | .seq a b, ha, S, E, hS, p, hp, q, r, hq, hr => by
    exact ControlFilter.seq_correct D hD _ x .callByValueSeq (by decide) T hT E
      (render a) (render b) (render_firstOrder a) (render_firstOrder b) _ _ p hp
      (fun q r hq hr => evaluator_of_rows D hD bodies g hg x T hT hRows a ha.1 S E hS p hp q r hq hr)
      (fun z hz q r hq hr => evaluator_of_rows D hD bodies g hg x T hT hRows b ha.2 S E hS z hz q r hq hr) q r hq hr
  | .alt a b, ha, S, E, hS, p, hp, q, r, hq, hr => by
    change evV _ _ _ _ E (RootObservation.branch (.andP (render a)) _ _) p=_
    rw [ChoiceArguments.branch_eval]
    cases hv : evV g x .callByValueSeq T E (render a) p with
    | none => rw [show render (.alt a b)=.alt (render a) (render b) from rfl,evV_alt_none hv]; rfl
    | some result => cases result with
      | none =>
        rw [show render (.alt a b)=.alt (render a) (render b) from rfl,evV_alt_fail hv]
        exact evaluator_of_rows D hD bodies g hg x T hT hRows b ha.2 S E hS p hp q r hq hr
      | some j =>
        rw [show render (.alt a b)=.alt (render a) (render b) from rfl,evV_alt_ok hv]
        simpa only [hv] using evaluator_of_rows D hD bodies g hg x T hT hRows a ha.1 S E hS p hp q r hq hr
  | .star a, ha, S, E, hS, p, hp, q, r, hq, hr => by
    exact GeneralStarFilter.correct D hD _ x .callByValueSeq (by decide) T hT E (render a)
      (render_firstOrder a) _
      (fun q r z hq hr hz => evaluator_of_rows D hD bodies g hg x T hT hRows a ha S E hS z hz q r hq hr) q r p hq hp
  | .notP a, _, S, E, _, p, _, q, r, _, _ => by
    apply DependentCaptureFilter.atom_correct (state := some q)
    intro j hv
    cases hz : evV g x .callByValueSeq T E (render a) p with
    | none => simp [evV,hz] at hv
    | some result => cases result with
      | some z => simp [evV,hz] at hv
      | none =>
        have hj : p=j := by simpa only [render,evV,hz,Option.some.injEq] using hv
        subst j
        simp [pre,run]

/-- Every recursive product row is derived from the actual installed
rules at the same physical clock, for all retained words and inputs. -/
theorem physical_rows (D : Machine) (hD : D.Valid) (bodies : List Expr) (g : MGrammar) (hg : Installed D bodies g) (hFO : g.FirstOrder)
    (hB : ∀ b∈bodies, Valid bodies b) (x : List Char) (k : Nat) :
    Rows D bodies x (tblV g x .callByValueSeq k) := by
  induction k with
  | zero => intro i b hi w p q r hp hq hr; rfl
  | succ k ih =>
    intro i b hi w p q r hp hq hr
    rw [valAt_tblV_succ (hg.product i b hi _ (CaptureTransitionProfile.profile_mem D hD w) q r hq hr) [w] hp,
      valAt_tblV_succ (hg.original i b hi) [w] hp]
    exact evaluator_of_rows D hD bodies g hg x _ (tblV_sound hFO (by decide) k) ih
      b (hB b (List.mem_of_getElem? hi)) [profile D w] [w]
      (DependentCaptureFilter.environment_accurate D [w]) p hp q r hq hr

/-- No recursive row premise remains. Captured prefixes and complete
partial results are observed by one fixed generated Seq grammar. -/
theorem filter_correct (D : Machine) (hD : D.Valid) (bodies : List Expr)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E
      (filter D bodies (E.map (profile D)) e q r) p=
      filtered D x q r p
        (evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E (render e) p) :=
  evaluator_of_rows D hD bodies (grammar D bodies) (installed D bodies) x _ (tblV_sound (firstOrder D bodies) (by decide) k)
    (physical_rows D hD bodies (grammar D bodies) (installed D bodies) (firstOrder D bodies) (fun b hb => check_sound bodies b ((List.all_eq_true.mp hB) b hb)) x k)
    e (check_sound bodies e he) (E.map (profile D)) E
    (DependentCaptureFilter.environment_accurate D E) p hp q r hq hr

/-- The complete capture of an arbitrarily nested recursive Seq expression
selects the continuation. Failure and undefinedness precede that choice. -/
theorem select_result (D : Machine) (hD : D.Valid) (bodies : List Expr)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (K : List Nat → MExp) :
    evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E
      (ProfileControl.select D (render e) (fun q r => filter D bodies (E.map (profile D)) e q r) K) p=
      match evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E (render e) p with
      | some (some j) => evV (grammar D bodies) x .callByValueSeq
          (tblV (grammar D bodies) x .callByValueSeq k) E (K (profile D (pre x p j))) p
      | other => other :=
  ProfileControl.select_correct D hD _ x .callByValueSeq _ E (render e) _ p
    (fun q r hq hr => filter_correct D hD bodies hB x k e he E p hp q r hq hr) K

abbrev source (bodies : List Expr) : MGrammar := ⟨original bodies⟩

theorem source_rule (bodies : List Expr) (i : Nat) (b : Expr) (hi : bodies[i]?=some b) :
    ruleAtM (source bodies).rules i=some ⟨1,render b⟩ := by
  simp only [original,ruleAtM_eq_getElem?,List.getElem?_map,hi,Option.map_some]

/-- Appending products leaves the actual original grammar intact. -/
theorem eval_congr (bodies : List Expr) (g h : MGrammar) (x : List Char) (T U : Table)
    (hT : OkTV x.length T)
    (hg : ∀ i b, bodies[i]?=some b → ruleAtM g.rules i=some ⟨1,render b⟩)
    (hh : ∀ i b, bodies[i]?=some b → ruleAtM h.rules i=some ⟨1,render b⟩)
    (hRows : ∀ i, i<bodies.length → ∀ W p, p≤x.length → valAt (T i W) p=valAt (U i W) p) :
    ∀ e, Valid bodies e → ∀ E p, p≤x.length →
      evV g x .callByValueSeq T E (render e) p=evV h x .callByValueSeq U E (render e) p
  | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .user i a, ha, E, p, hp => by
    have hib : i<bodies.length := ha.1
    have hi : bodies[i]?=some bodies[i] := List.getElem?_eq_getElem hib
    rw [render,evV_call_seq (hg i _ hi) rfl,evV_call_seq (hh i _ hi) rfl]
    simp only [evSeqArgs,eval_congr bodies g h x T U hT hg hh hRows a ha.2 E p hp]
    cases hv : evV h x .callByValueSeq U E (render a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        have hv' : evV g x .callByValueSeq T E (render a) p=some (some j) :=
          (eval_congr bodies g h x T U hT hg hh hRows a ha.2 E p hp).trans hv
        exact hRows i hib _ j (evV_ok hT _ p hp j hv')
  | .seq a b, ha, E, p, hp => by
    change (match evV g x .callByValueSeq T E (render a) p with
      | some (some j) => evV g x .callByValueSeq T E (render b) j | other => other)=
      (match evV h x .callByValueSeq U E (render a) p with
      | some (some j) => evV h x .callByValueSeq U E (render b) j | other => other)
    have he := eval_congr bodies g h x T U hT hg hh hRows a ha.1 E p hp
    rw [←he]
    cases hv : evV g x .callByValueSeq T E (render a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j => exact eval_congr bodies g h x T U hT hg hh hRows b ha.2 E j (evV_ok hT _ p hp j hv)
  | .alt a b, ha, E, p, hp => by
    simp only [render,evV,eval_congr bodies g h x T U hT hg hh hRows a ha.1 E p hp,
      eval_congr bodies g h x T U hT hg hh hRows b ha.2 E p hp]
  | .star a, ha, E, p, hp => evStar_congr p (fun j hj =>
      eval_congr bodies g h x T U hT hg hh hRows a ha E j (by omega))
  | .notP a, ha, E, p, hp => by
    simp only [render,evV,eval_congr bodies g h x T U hT hg hh hRows a ha E p hp]

theorem original_rows (D : Machine) (bodies : List Expr) (hB : ∀ b∈bodies, Valid bodies b)
    (x : List Char) (k : Nat) : ∀ i, i<bodies.length → ∀ W p, p≤x.length →
    valAt (tblV (source bodies) x .callByValueSeq k i W) p=
      valAt (tblV (grammar D bodies) x .callByValueSeq k i W) p := by
  induction k with
  | zero => intro i hi W p hp; rfl
  | succ k ih =>
    intro i hi W p hp
    have hb := List.getElem?_eq_getElem hi
    rw [valAt_tblV_succ (source_rule bodies i bodies[i] hb) W hp,
      valAt_tblV_succ (original_rule D bodies i bodies[i] hb) W hp]
    exact eval_congr bodies _ _ x _ _ (tblV_ok _ _ _ k)
      (source_rule bodies) (original_rule D bodies) ih bodies[i] (hB _ (List.mem_of_getElem? hb)) W p hp

theorem original_eval (D : Machine) (bodies : List Expr)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq k) E (render e) p=
      evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E (render e) p :=
  eval_congr bodies _ _ x _ _ (tblV_ok _ _ _ k) (source_rule bodies) (original_rule D bodies)
    (original_rows D bodies (fun b hb => check_sound bodies b ((List.all_eq_true.mp hB) b hb)) x k)
    e (check_sound bodies e he) E p hp

/-- The product is an observer for the separate original source grammar,
not for an assumed or modified plain-row oracle. All physical stages agree. -/
theorem source_filter_correct (D : Machine) (hD : D.Valid) (bodies : List Expr)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (grammar D bodies) x .callByValueSeq (tblV (grammar D bodies) x .callByValueSeq k) E
      (filter D bodies (E.map (profile D)) e q r) p=
      filtered D x q r p
        (evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq k) E (render e) p) := by
  rw [filter_correct D hD bodies hB x k e he E p hp q r hq hr,original_eval D bodies hB x k e he E p hp]

theorem ambient_original_rows (D : Machine) (bodies : List Expr) (g : MGrammar) (hg : Installed D bodies g)
    (hB : ∀ b∈bodies, Valid bodies b) (x : List Char) (k : Nat) :
    ∀ i, i<bodies.length → ∀ W p, p≤x.length →
      valAt (tblV (source bodies) x .callByValueSeq k i W) p=valAt (tblV g x .callByValueSeq k i W) p := by
  induction k with
  | zero => intro i hi W p hp; rfl
  | succ k ih =>
    intro i hi W p hp
    have hb := List.getElem?_eq_getElem hi
    rw [valAt_tblV_succ (source_rule bodies i bodies[i] hb) W hp,
      valAt_tblV_succ (hg.original i bodies[i] hb) W hp]
    exact eval_congr bodies _ _ x _ _ (tblV_ok _ _ _ k) (source_rule bodies) hg.original ih
      bodies[i] (hB _ (List.mem_of_getElem? hb)) W p hp

theorem ambient_original_eval (D : Machine) (bodies : List Expr) (g : MGrammar) (hg : Installed D bodies g)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source bodies) x .callByValueSeq (tblV (source bodies) x .callByValueSeq k) E (render e) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (render e) p :=
  eval_congr bodies _ _ x _ _ (tblV_ok _ _ _ k) (source_rule bodies) hg.original
    (ambient_original_rows D bodies g hg (fun b hb => check_sound bodies b ((List.all_eq_true.mp hB) b hb)) x k)
    e (check_sound bodies e he) E p hp

theorem ambient_filter_correct (D : Machine) (hD : D.Valid) (bodies : List Expr)
    (g : MGrammar) (hg : Installed D bodies g) (hFO : g.FirstOrder)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (filter D bodies (E.map (profile D)) e q r) p=
      filtered D x q r p (evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (render e) p) :=
  evaluator_of_rows D hD bodies g hg x _ (tblV_sound hFO (by decide) k)
    (physical_rows D hD bodies g hg hFO (fun b hb => check_sound bodies b ((List.all_eq_true.mp hB) b hb)) x k)
    e (check_sound bodies e he) (E.map (profile D)) E (DependentCaptureFilter.environment_accurate D E) p hp q r hq hr

theorem ambient_select_result (D : Machine) (hD : D.Valid) (bodies : List Expr)
    (g : MGrammar) (hg : Installed D bodies g) (hFO : g.FirstOrder)
    (hB : bodies.all (check bodies.length)=true) (x : List Char) (k : Nat)
    (e : Expr) (he : check bodies.length e=true) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (K : List Nat → MExp) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq k) E
      (ProfileControl.select D (render e) (fun q r => filter D bodies (E.map (profile D)) e q r) K) p=
      match evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (render e) p with
      | some (some j) => evV g x .callByValueSeq (tblV g x .callByValueSeq k) E (K (profile D (pre x p j))) p
      | other => other :=
  ProfileControl.select_correct D hD g x .callByValueSeq _ E (render e) _ p
    (fun q r hq hr => ambient_filter_correct D hD bodies g hg hFO hB x k e he E p hp q r hq hr) K

end Shallot.MacroPeg.CBV.SequentialRecursiveObserver
