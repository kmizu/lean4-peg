import MacroPeg.CBV.ClockFreezing
import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.ReplayFusion

/-! Empty-result observation for arbitrary nullary recursive PEGs. The full
lookahead gates preserve divergence on paths a zero-only traversal skips. -/
namespace Shallot.MacroPeg.CBV.EmptyResultObservation
open ClockFreezing (Table)

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | call (i : Nat)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

def render (f : Nat → Nat) : Expr → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .call i => .call (f i) []
  | .seq a b => .seq (render f a) (render f b)
  | .alt a b => .alt (render f a) (render f b)
  | .notP a => .notP (render f a)
  | .star a => .star (render f a)

abbrev plain := render id
abbrev normal := render (fun i => 2*i)
def gate (a b : MExp) := MExp.seq (.andP a) b

def empty : Expr → MExp
  | .eps => .eps
  | .any | .chr _ | .range _ _ => MExp.failAlways
  | .lit w => if w=[] then .eps else MExp.failAlways
  | .call i => .call (2*i+1) []
  | .seq a b => gate (normal (.seq a b)) (.seq (empty a) (empty b))
  | .alt a b => gate (normal (.alt a b)) (.alt (empty a) (.seq (.notP (normal a)) (empty b)))
  | .notP a => normal (.notP a)
  | .star a => gate (normal (.star a)) (.notP (normal a))

/-- Preserve failure and undefinedness, discarding only consuming success. -/
def project (p : Nat) : Res → Res
  | none => none
  | some none => some none
  | some (some q) => if q=p then some (some p) else some none

def source (bs : List Expr) : MGrammar := ⟨bs.map (fun b => ⟨0,plain b⟩)⟩
def target (bs : List Expr) : MGrammar := ⟨bs.flatMap (fun b => [⟨0,normal b⟩,⟨0,empty b⟩])⟩

theorem render_firstOrder (f : Nat → Nat) : ∀ e, (render f e).FirstOrder
  | .seq a b | .alt a b => ⟨render_firstOrder f a,render_firstOrder f b⟩
  | .notP a | .star a => render_firstOrder f a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .call _ => True.intro

theorem empty_firstOrder : ∀ e, (empty e).FirstOrder
  | .seq a b => ⟨render_firstOrder _ _,empty_firstOrder a,empty_firstOrder b⟩
  | .alt a b => ⟨render_firstOrder _ _,empty_firstOrder a,render_firstOrder _ _,empty_firstOrder b⟩
  | .notP a => render_firstOrder _ _
  | .star a => ⟨render_firstOrder _ _,render_firstOrder _ _⟩
  | .lit w => by simp only [empty]; split <;> trivial
  | .eps | .any | .chr _ | .range _ _ | .call _ => True.intro

theorem source_firstOrder (bs : List Expr) : (source bs).FirstOrder := by
  intro r hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder _ _

theorem target_firstOrder (bs : List Expr) : (target bs).FirstOrder := by
  intro r hr
  obtain ⟨b,_,hr⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact render_firstOrder _ _
  · exact empty_firstOrder _

theorem rule_count (bs : List Expr) : (target bs).rules.length=2*bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [target,List.flatMap_cons] at *; omega

theorem source_rule (bs : List Expr) (i : Nat) :
    ruleAtM (source bs).rules i=(bs[i]?).map (fun b => ⟨0,plain b⟩) := by
  simp [source,ruleAtM_eq_getElem?]

theorem target_rule (bs : List Expr) (i : Nat) (odd : Bool) :
    ruleAtM (target bs).rules (2*i+(if odd then 1 else 0))=
      (bs[i]?).map (fun b => ⟨0,if odd then empty b else normal b⟩) := by
  induction bs generalizing i with
  | nil => simp [target,ruleAtM_eq_getElem?]
  | cons b bs ih =>
    cases i with
    | zero => cases odd <;> rfl
    | succ i =>
      rw [show 2*(i+1)+(if odd then 1 else 0)=(2*i+(if odd then 1 else 0))+2 by omega]
      simpa only [target,ruleAtM_eq_getElem?,List.flatMap_cons,List.cons_append,List.nil_append,List.getElem?_cons_succ,
        Nat.add_succ,Nat.add_zero] using ih i

theorem call_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (i : Nat) (p : Nat)
    (hr : ∀ r, ruleAtM g.rules i=some r → r.arity=0) :
    evV g x s T [] (.call i []) p=
      match ruleAtM g.rules i with | none => some none | some _ => valAt (T i []) p := by
  cases hh : ruleAtM g.rules i with
  | none => simp [evV,hh]
  | some r =>
    have ha := hr r hh
    by_cases hs : s=.callByValueSeq
    · subst s; rw [evV_call_seq hh (by simpa using ha)]; rfl
    · rw [evV_call_par hh (by simpa using ha) hs]; rfl

def Rows (bs : List Expr) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, bs[i]?=some b → ∀ p, p≤x.length →
    valAt (U (2*i) []) p=valAt (T i []) p ∧
    valAt (U (2*i+1) []) p=project p (valAt (T i []) p)

theorem normal_eval (bs : List Expr) (x : List Char) (T U : Table)
    (rows : Rows bs x T U) (ht : OkTV x.length T) : ∀ e p, p≤x.length →
    evV (target bs) x .callByValueSeq U [] (normal e) p=
      evV (source bs) x .callByValuePar T [] (plain e) p
  | .call i,p,hp => by
    have hs := source_rule bs i
    have hh := target_rule bs i false
    simp only [Bool.false_eq_true,if_false,Nat.add_zero] at hh
    rw [show normal (.call i)=.call (2*i) [] from rfl,show plain (.call i)=.call i [] from rfl]
    rw [call_eval _ _ _ _ _ _ (by intro r h; rw [hh] at h; cases hb : bs[i]? <;> simp_all <;> cases h <;> rfl),
      call_eval _ _ _ _ _ _ (by intro r h; rw [hs] at h; cases hb : bs[i]? <;> simp_all <;> cases h <;> rfl)]
    rw [hs,hh]
    cases hb : bs[i]? with
    | none => rfl
    | some b => exact (rows i b hb p hp).1
  | .seq a b,p,hp => by
    have ha := normal_eval bs x T U rows ht a p hp
    cases he : evV (source bs) x .callByValuePar T [] (plain a) p with
    | none => simp only [render,evV_seq_none he,evV_seq_none (ha.trans he)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail he,evV_seq_fail (ha.trans he)]
      | some j =>
        simp only [render,evV_seq_ok he,evV_seq_ok (ha.trans he)]
        exact normal_eval bs x T U rows ht b j (evV_ok ht _ p hp j he)
  | .alt a b,p,hp => by
    have ha := normal_eval bs x T U rows ht a p hp
    cases he : evV (source bs) x .callByValuePar T [] (plain a) p with
    | none => simp only [render,evV_alt_none he,evV_alt_none (ha.trans he)]
    | some v => cases v with
      | none => simp only [render,evV_alt_fail he,evV_alt_fail (ha.trans he)]; exact normal_eval bs x T U rows ht b p hp
      | some j => simp only [render,evV_alt_ok he,evV_alt_ok (ha.trans he)]
  | .notP a,p,hp => by simp only [render,evV,normal_eval bs x T U rows ht a p hp]
  | .star a,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => normal_eval bs x T U rows ht a q (by omega))
  | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl


theorem gate_project (g h : MGrammar) (x : List Char) (T U : Table) (a b c : MExp) (p : Nat)
    (hn : evV h x .callByValueSeq U [] b p=evV g x .callByValuePar T [] a p)
    (hc : ∀ q, evV g x .callByValuePar T [] a p=some (some q) →
      evV h x .callByValueSeq U [] c p=project p (some (some q))) :
    evV h x .callByValueSeq U [] (gate b c) p=project p (evV g x .callByValuePar T [] a p) := by
  unfold gate
  change (match evV h x .callByValueSeq U [] (.andP b) p with
    | some (some j) => evV h x .callByValueSeq U [] c j | other => other)=_
  rw [CallLookahead.evV_peek,hn]
  cases ha : evV g x .callByValuePar T [] a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q => exact hc q ha

/-- A successful repetition is empty exactly when its first body fails. -/
theorem star_empty_test (f : Nat → Res) (p q : Nat) (h : evStar f p=some (some q)) :
    (match f p with | none => none | some none => some (some p) | some (some _) => some none)=project p (some (some q)) := by
  cases he : f p with
  | none => rw [evStar_none he] at h; cases h
  | some v => cases v with
    | none => rw [evStar_fail he] at h; cases h; simp [project]
    | some j =>
      by_cases hj : j<p
      · rw [evStar_ok he hj] at h
        have hq := evStar_le j q h
        simp [project,show q≠p by omega]
      · rw [evStar_stuck he hj] at h; cases h

/-- This premise concerns ordinary calls only; actual source tables supply it. -/
def Down (g : MGrammar) (x : List Char) (T : Table) : Prop :=
  ∀ e p q, p≤x.length → evV g x .callByValuePar T [] (plain e) p=some (some q) → q≤p

theorem empty_eval (bs : List Expr) (x : List Char) (T U : Table)
    (rows : Rows bs x T U) (ht : OkTV x.length T) (down : Down (source bs) x T) : ∀ e p, p≤x.length →
    evV (target bs) x .callByValueSeq U [] (empty e) p=
      project p (evV (source bs) x .callByValuePar T [] (plain e) p)
  | .call i,p,hp => by
    have hh := target_rule bs i true
    simp only [if_true] at hh
    rw [show empty (.call i)=.call (2*i+1) [] from rfl,
      call_eval _ _ _ _ _ _ (by intro r h; rw [hh] at h; cases hb : bs[i]? <;> simp_all <;> cases h <;> rfl)]
    have hs := source_rule bs i
    rw [show plain (.call i)=.call i [] from rfl,
      call_eval _ _ _ _ _ _ (by intro r h; rw [hs] at h; cases hb : bs[i]? <;> simp_all <;> cases h <;> rfl),hh,hs]
    cases hb : bs[i]? with
    | none => rfl
    | some b => exact (rows i b hb p hp).2
  | .seq a b,p,hp => by
    apply gate_project _ _ x T U _ _ _ p (normal_eval bs x T U rows ht (.seq a b) p hp)
    intro q hq
    cases ha : evV (source bs) x .callByValuePar T [] (plain a) p with
    | none => rw [show plain (.seq a b)=.seq (plain a) (plain b) from rfl,evV_seq_none ha] at hq; cases hq
    | some v => cases v with
      | none => rw [show plain (.seq a b)=.seq (plain a) (plain b) from rfl,evV_seq_fail ha] at hq; cases hq
      | some j =>
        rw [show plain (.seq a b)=.seq (plain a) (plain b) from rfl,evV_seq_ok ha] at hq
        have hj := evV_ok ht _ p hp j ha
        have hdown := down b j q hj hq
        have hza := (empty_eval bs x T U rows ht down a p hp).trans (congrArg (project p) ha)
        by_cases he : j=p
        · subst j
          simp only [project,if_true] at hza
          rw [evV_seq_ok hza,empty_eval bs x T U rows ht down b p hp,hq]
        · simp only [project,if_neg he] at hza
          rw [evV_seq_fail hza]
          simp [project,show q≠p from by have := down a p j hp ha; omega]
  | .alt a b,p,hp => by
    apply gate_project _ _ x T U _ _ _ p (normal_eval bs x T U rows ht (.alt a b) p hp)
    intro q hq
    have hza := empty_eval bs x T U rows ht down a p hp
    have hna := normal_eval bs x T U rows ht a p hp
    cases ha : evV (source bs) x .callByValuePar T [] (plain a) p with
    | none => rw [show plain (.alt a b)=.alt (plain a) (plain b) from rfl,evV_alt_none ha] at hq; cases hq
    | some v => cases v with
      | none =>
        rw [show plain (.alt a b)=.alt (plain a) (plain b) from rfl,evV_alt_fail ha] at hq
        rw [ha] at hza hna
        rw [evV_alt_fail hza,evV_seq_ok (evV_not_fail hna),empty_eval bs x T U rows ht down b p hp,hq]
      | some j =>
        rw [show plain (.alt a b)=.alt (plain a) (plain b) from rfl,evV_alt_ok ha] at hq
        have he : j=q := by simpa only [Option.some.injEq] using hq
        subst j
        rw [ha] at hza hna
        by_cases he : q=p
        · simp only [project,if_pos he] at hza
          rw [evV_alt_ok hza]; simp [project,he]
        · simp only [project,if_neg he] at hza
          rw [evV_alt_fail hza,evV_seq_fail (evV_not_ok hna)]
          simp [project,he]
  | .notP a,p,hp => by
    rw [show empty (.notP a)=normal (.notP a) from rfl,normal_eval bs x T U rows ht (.notP a) p hp]
    change evV _ _ _ _ _ (.notP (plain a)) p=project p (evV _ _ _ _ _ (.notP (plain a)) p)
    cases ha : evV (source bs) x .callByValuePar T [] (plain a) p with
    | none => rw [evV_not_none ha]; rfl
    | some v => cases v with
      | none => rw [evV_not_fail ha]; simp [project]
      | some j => rw [evV_not_ok ha]; rfl
  | .star a,p,hp => by
    apply gate_project _ _ x T U _ _ _ p (normal_eval bs x T U rows ht (.star a) p hp)
    intro q hq
    change evV _ _ _ _ _ (.notP (normal a)) p=_
    simp only [evV,normal_eval bs x T U rows ht a p hp]
    have hh := star_empty_test _ p q hq
    cases hv : evV (source bs) x .callByValuePar T [] (plain a) p with
    | none => simpa [hv] using hh
    | some v => cases v <;> simpa [hv] using hh
  | .eps,p,hp => by simp [empty,plain,render,evV,project]
  | .any,p,hp => by
    have hl := length_sfx x hp
    cases hx : sfx x p with
    | nil => simp [empty,plain,render,evV,hx,project,MExp.failAlways]
    | cons c rest =>
      rw [hx] at hl
      have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
      simp [empty,plain,render,evV,hx,project,hn,MExp.failAlways]
  | .chr c,p,hp => by
    have hl := length_sfx x hp
    cases hx : sfx x p with
    | nil => simp [empty,plain,render,evV,hx,project,MExp.failAlways]
    | cons d rest =>
      rw [hx] at hl
      have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
      cases hc : Shallot.beqChar c d <;> simp [empty,plain,render,evV,hx,hc,project,hn,MExp.failAlways]
  | .range a b,p,hp => by
    have hl := length_sfx x hp
    cases hx : sfx x p with
    | nil => simp [empty,plain,render,evV,hx,project,MExp.failAlways]
    | cons d rest =>
      rw [hx] at hl
      have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
      cases hc : (Shallot.leChar a d && Shallot.leChar d b) <;> simp [empty,plain,render,evV,hx,hc,project,hn,MExp.failAlways]
  | .lit w,p,hp => by
    by_cases hw : w=[]
    · subst w; simp [empty,plain,render,evV,Shallot.stripPrefix?,length_sfx x hp,project]
    · simp only [empty,if_neg hw,MExp.failAlways,plain,render,evV]
      cases hh : Shallot.stripPrefix? w (sfx x p) with
      | none => rfl
      | some rest =>
        have hs := (CBVtoCBN.stripPrefix_exact _ _ _).mp hh
        have hl := congrArg List.length hs
        rw [List.length_append,length_sfx x hp] at hl
        simp [project,show rest.length≠p from by have := List.length_pos_iff.mpr hw; omega]


theorem physical_down (bs : List Expr) (x : List Char) (k : Nat) :
    Down (source bs) x (tblV (source bs) x .callByValuePar k) := by
  intro e p q hp he
  have hh := ReplayFusion.success_prefix (tblV_sound (source_firstOrder bs) (by decide) k)
    [] (plain e) (render_firstOrder _ _) p q hp he
  have hl := congrArg List.length hh.2
  rw [List.length_append,length_sfx x hp,length_sfx x hh.1] at hl
  omega

/-- Both row channels agree at the same physical clock, including left and
mutual recursion and nullable stars. -/
theorem tables_related (bs : List Expr) (x : List Char) (k : Nat) :
    Rows bs x (tblV (source bs) x .callByValuePar k) (tblV (target bs) x .callByValueSeq k) := by
  induction k with
  | zero => intro i b hb p hp; exact ⟨rfl,rfl⟩
  | succ k ih =>
    intro i b hb p hp
    have hs : ruleAtM (source bs).rules i=some ⟨0,plain b⟩ := by rw [source_rule,hb]; rfl
    have hn : ruleAtM (target bs).rules (2*i)=some ⟨0,normal b⟩ := by simpa only [Bool.false_eq_true,if_false,Nat.add_zero,hb,Option.map_some] using target_rule bs i false
    have hz : ruleAtM (target bs).rules (2*i+1)=some ⟨0,empty b⟩ := by simpa only [if_true,hb,Option.map_some] using target_rule bs i true
    constructor
    · rw [valAt_tblV_succ hs [] hp,valAt_tblV_succ hn [] hp]
      exact normal_eval bs x _ _ ih (tblV_ok _ _ _ k) b p hp
    · rw [valAt_tblV_succ hs [] hp,valAt_tblV_succ hz [] hp]
      exact empty_eval bs x _ _ ih (tblV_ok _ _ _ k) (physical_down bs x k) b p hp

theorem physical (bs : List Expr) (x : List Char) (e : Expr) (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (normal e) p=
      evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p ∧
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (empty e) p=
      project p (evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p) :=
  ⟨normal_eval bs x _ _ (tables_related bs x k) (tblV_ok _ _ _ k) e p hp,
    empty_eval bs x _ _ (tables_related bs x k) (tblV_ok _ _ _ k) (physical_down bs x k) e p hp⟩

theorem empty_success_iff (bs : List Expr) (x : List Char) (e : Expr) (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (empty e) p=some (some p) ↔
      evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p=some (some p) := by
  rw [(physical bs x e p k hp).2]
  cases he : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p with
  | none => simp [project]
  | some v => cases v with
    | none => simp [project]
    | some q => by_cases hh : q=p <;> simp [project,hh]

theorem empty_undefined_iff (bs : List Expr) (x : List Char) (e : Expr) (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (empty e) p=none ↔
      evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p=none := by
  rw [(physical bs x e p k hp).2]
  cases he : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p with
  | none => simp [project]
  | some v => cases v with
    | none => simp [project]
    | some q => by_cases hh : q=p <;> simp [project,hh]

/-- This observes the actual captured substring, not a nullable approximation. -/
theorem actual_capture_empty_iff (bs : List Expr) (x : List Char) (e : Expr) (p q k : Nat) (hp : p≤x.length)
    (he : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p=some (some q)) :
    pre x p q=[] ↔ evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (empty e) p=some (some p) := by
  rw [empty_success_iff bs x e p k hp,he]
  have hq := physical_down bs x k e p q hp he
  have hl : (pre x p q).length=p-q := by simp [pre,List.length_take,length_sfx x hp,Nat.min_eq_left (Nat.sub_le _ _)]
  constructor
  · intro hh
    rw [hh] at hl
    simp only [List.length_nil] at hl
    have hh : q=p := by omega
    simp [hh]
  · intro hh
    have hh : q=p := by simpa only [Option.some.injEq] using hh
    simp [pre,hh]

/-- Finite failure versus an empty success may be selected by ordinary PEG
priority. The nonempty observer still propagates the producer's divergence. -/
def nonempty (e : Expr) := gate (normal e) (.notP (empty e))

theorem nonempty_physical (bs : List Expr) (x : List Char) (e : Expr) (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (nonempty e) p=
      match evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p with
      | none => none | some none => some none
      | some (some q) => if q=p then some none else some (some p) := by
  unfold nonempty gate
  change (match evV _ _ _ _ _ (.andP (normal e)) p with
    | some (some j) => evV _ _ _ _ _ (.notP (empty e)) j | other => other)=_
  rw [CallLookahead.evV_peek,(physical bs x e p k hp).1]
  cases he : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain e) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q =>
      simp only [CallLookahead.peek]
      have hz := (physical bs x e p k hp).2
      rw [he] at hz
      by_cases hh : q=p
      · simp only [project,if_pos hh] at hz
        rw [evV_not_ok hz]; simp [hh]
      · simp only [project,if_neg hh] at hz
        rw [evV_not_fail hz]; simp [hh]

end Shallot.MacroPeg.CBV.EmptyResultObservation
