import PalPeg.GalilScaffoldChainPeriod

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainCredits
open GalilScaffoldCounter

/-- Margin/lag projection before watch. An event records the enabled copy
and outer matched guards, in that order. It excludes shift/fallback and
the ready consume branch of matched after entering watch. -/
structure State where
  margin : Counter
  lag : Counter

def start (radius : Counter) : State := ⟨radius, radius⟩
def decFour (c : Counter) : Counter := dec (dec (dec (dec c)))
def step (s : State) (e : Bool × Bool) : State :=
  let margin := if e.1 then decFour s.margin else s.margin
  ⟨if e.2 then inc margin else margin, if e.2 then inc s.lag else s.lag⟩

def run : State → List (Bool × Bool) → State
  | s, [] => s
  | s, e :: es => run (step s e) es

theorem step_value (s : State) (copy matched : Bool) :
    value (step s (copy, matched)).margin = value s.margin -
      (if copy then 4 else 0) + (if matched then 1 else 0) ∧
    value (step s (copy, matched)).lag = value s.lag + (if matched then 1 else 0) := by
  cases copy <;> cases matched <;> simp [step, decFour, inc_value, dec_value] <;> omega

theorem run_value (s : State) (es : List (Bool × Bool)) :
    value (run s es).margin = value s.margin - 4 * ((es.map Prod.fst).count true : ℤ) +
      ((es.map Prod.snd).count true : ℤ) ∧
    value (run s es).lag = value s.lag + ((es.map Prod.snd).count true : ℤ) := by
  induction es generalizing s with
  | nil => simp [run]
  | cons e es ih =>
    have hv := step_value s e.1 e.2
    have hr := ih (step s e)
    rcases e with ⟨a,b⟩
    cases a <;> cases b <;> simp_all [run] <;> omega

theorem step_canonical (s : State) (e : Bool × Bool)
    (hm : Canonical s.margin) (hl : Canonical s.lag) :
    Canonical (step s e).margin ∧ Canonical (step s e).lag := by
  have hd := dec_canonical _ (dec_canonical _ (dec_canonical _ (dec_canonical _ hm)))
  rcases e with ⟨a,b⟩
  cases a <;> cases b <;> simp only [step, Bool.false_eq_true, if_false, if_true]
  all_goals try dsimp only [decFour]
  all_goals aesop (add safe inc_canonical)

theorem run_canonical (s : State) (es : List (Bool × Bool))
    (hm : Canonical s.margin) (hl : Canonical s.lag) :
    Canonical (run s es).margin ∧ Canonical (run s es).lag := by
  induction es generalizing s with
  | nil => exact ⟨hm,hl⟩
  | cons e es ih =>
    have hc := step_canonical s e hm hl
    exact ih (step s e) hc.1 hc.2

/-- If radius is positive, all pre-watch matching events keep lag nonzero;
the first outer matched dispatch after back cannot take ready consume. -/
theorem lag_not_zero (radius : Counter) (es : List (Bool × Bool))
    (hc : Canonical radius) (hp : 0 < value radius) :
    zero (run (start radius) es).lag = false := by
  have hv := (run_value (start radius) es).2
  have hk := (run_canonical (start radius) es hc hc).2
  have hpos : 0 < value (run (start radius) es).lag := by
    change value (run (start radius) es).lag = value radius + _ at hv
    omega
  cases he : zero (run (start radius) es).lag
  · rfl
  · have hz := (zero_iff _ hk).mp he
    omega

structure CopyState where
  answer : GalilScaffoldTape.Tape
  h : Counter
  walker : GalilScaffoldPlace.Place
  period : GalilScaffoldChainPeriod.Tape
  credits : State

def copyStep (s : CopyState) (a : Fin 3) (matched : Bool) : CopyState :=
  ⟨GalilScaffoldTape.moveLeft s.answer, inc s.h, GalilScaffoldPlace.left s.walker,
    GalilScaffoldChainPeriod.put s.period a, step s.credits (true, matched)⟩

/-- One enabled copy per event, followed by its outer matched update.
Fallback/shift and pauses are not included in this uninterrupted relation. -/
inductive PacedCopy : CopyState → List Bool → CopyState → Prop
  | stop (s) : PacedCopy s [] s
  | next {s bs u} (a : Fin 3) (matched : Bool)
      (one : s.answer.focus = 8) (legal : s.answer.left ≠ [])
      (present : GalilScaffoldPlace.read (GalilScaffoldPlace.left s.walker) = some a)
      (rest : PacedCopy (copyStep s a matched) bs u) :
      PacedCopy s (matched :: bs) u

theorem pace_copy {t c p v n u d q z}
    (hr : GalilScaffoldChainPeriod.Copy t c p v n u d q z)
    (bs : List Bool) (hlen : bs.length = n) (credits : State) :
    PacedCopy ⟨t,c,p,v,credits⟩ bs
      ⟨u,d,q,z,run credits (bs.map (fun b => (true,b)))⟩ := by
  induction hr generalizing bs credits with
  | stop t c p v =>
    have he : bs = [] := List.length_eq_zero_iff.mp hlen
    subst bs
    exact PacedCopy.stop _
  | next a one legal present rest ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      apply PacedCopy.next a b one legal present
      exact ih bs (by simpa using hlen) (step credits (true,b))

/-- The credit ledger refers to precisely the matched events used by the
same copy execution, rather than an unrelated event list. -/
theorem pace_copy_balance {t c p v n u d q z}
    (hr : GalilScaffoldChainPeriod.Copy t c p v n u d q z)
    (bs : List Bool) (hlen : bs.length = n) (credits : State)
    (hm : Canonical credits.margin) (hl : Canonical credits.lag) :
    ∃ final, PacedCopy ⟨t,c,p,v,credits⟩ bs ⟨u,d,q,z,final⟩ ∧
      Canonical final.margin ∧ Canonical final.lag ∧
      value final.margin = value credits.margin - 4*(n : ℤ) + (bs.count true : ℤ) ∧
      value final.lag = value credits.lag + (bs.count true : ℤ) := by
  let es := bs.map (fun b => (true,b))
  refine ⟨run credits es, pace_copy hr bs hlen credits, ?_⟩
  have hc := run_canonical credits es hm hl
  have hv := run_value credits es
  have hfirst : (es.map Prod.fst).count true = n := by
    dsimp [es]
    simpa using hlen
  have hsecond : (es.map Prod.snd).count true = bs.count true := by simp [es]
  rw [hfirst,hsecond] at hv
  exact ⟨hc.1,hc.2,hv.1,hv.2⟩

/-- Back plus the outer matched update. On its final tick the new mode
is watch: a nonzero lag justifies using the lag-inc branch, not consume. -/
inductive PacedBack : GalilScaffoldChainPeriod.Tape → State → List Bool →
    GalilScaffoldChainPeriod.Tape → State → Prop
  | done (t s b) (hf : GalilScaffoldChainPeriod.isFirst t.focus = true)
      (hl : b = true → zero s.lag = false) :
      PacedBack t s [b] (GalilScaffoldChainPeriod.moveRight t) (step s (false,b))
  | next (t s b) (hf : GalilScaffoldChainPeriod.isFirst t.focus = false)
      (hl : t.left ≠ []) {bs u d}
      (hr : PacedBack (GalilScaffoldChainPeriod.moveLeft t) (step s (false,b)) bs u d) :
      PacedBack t s (b :: bs) u d

theorem pace_back {t n u} (hr : GalilScaffoldChainPeriod.Back t n u)
    (bs : List Bool) (hlen : bs.length = n) (s : State)
    (hc : Canonical s.lag) (hp : 0 < value s.lag) :
    PacedBack t s bs u (run s (bs.map (fun b => (false,b)))) := by
  induction hr generalizing bs s with
  | done t hf =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have he : bs = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst bs
      apply PacedBack.done t s b hf
      intro _
      cases hz : zero s.lag
      · rfl
      · have hv := (zero_iff _ hc).mp hz
        omega
  | next t hf hl hr ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      apply PacedBack.next t s b hf hl
      apply ih bs (by simpa using hlen) (step s (false,b))
      · cases b <;> simp only [step, if_false, if_true]
        · exact hc
        · exact inc_canonical _ hc
      · have hv := (step_value s false b).2
        cases b <;> simp_all <;> omega

/-- With no outer match during back, even zero initial lag leaves period
untouched. Positive radius is not necessary for this execution branch. -/
theorem pace_back_quiet {t n u} (hr : GalilScaffoldChainPeriod.Back t n u) (s : State) :
    PacedBack t s (List.replicate n false) u s := by
  induction hr with
  | done t hf =>
    simpa [step] using PacedBack.done t s false hf (by simp)
  | next t hf hl hr ih =>
    rw [List.replicate_succ]
    apply PacedBack.next t s false hf hl
    simpa [step] using ih

theorem run_append (s : State) (xs ys : List (Bool × Bool)) :
    run s (xs ++ ys) = run (run s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih => exact ih (step s e)

def prepEvents (startMatch doneMatch : Bool) (copyMatches backMatches : List Bool) :
    List (Bool × Bool) :=
  (false,startMatch) :: (copyMatches.map (fun b => (true,b)) ++
    (false,doneMatch) :: backMatches.map (fun b => (false,b)))

/-- Start and LAST-marking dispatches each have their own outer matched
event. Copy and back share the exact intermediate credit states. -/
theorem prepare_paced {t c p v n u d q z watch}
    (hcopy : GalilScaffoldChainPeriod.Copy t c p v n u d q z)
    (b : Fin 3) (hback : GalilScaffoldChainPeriod.Back
      (GalilScaffoldChainPeriod.write z (.last b)) (n+1) watch)
    (radius : Counter) (hc : Canonical radius) (hp : 0 < value radius)
    (sm dm : Bool) (bs cs : List Bool) (hb : bs.length = n) (hcs : cs.length = n+1) :
    ∃ copied final,
      PacedCopy ⟨t,c,p,v,step (start radius) (false,sm)⟩ bs ⟨u,d,q,z,copied⟩ ∧
      PacedBack (GalilScaffoldChainPeriod.write z (.last b))
        (step copied (false,dm)) cs watch final ∧
      final = run (start radius) (prepEvents sm dm bs cs) ∧
      Canonical final.margin ∧ Canonical final.lag ∧ zero final.lag = false := by
  let initial := step (start radius) (false,sm)
  let copied := run initial (bs.map (fun b => (true,b)))
  let beforeBack := step copied (false,dm)
  let final := run beforeBack (cs.map (fun b => (false,b)))
  have hpre : beforeBack = run (start radius)
      ([(false,sm)] ++ bs.map (fun b => (true,b)) ++ [(false,dm)]) := by
    simp [run_append, run, beforeBack, copied, initial]
  have hk := run_canonical (start radius)
    ([(false,sm)] ++ bs.map (fun b => (true,b)) ++ [(false,dm)]) hc hc
  rw [← hpre] at hk
  have hpos : 0 < value beforeBack.lag := by
    have hv := (run_value (start radius)
      ([(false,sm)] ++ bs.map (fun b => (true,b)) ++ [(false,dm)])).2
    rw [← hpre] at hv
    change value beforeBack.lag = value radius + _ at hv
    omega
  have heq : final = run (start radius) (prepEvents sm dm bs cs) := by
    simp [prepEvents, run_append, run, final, beforeBack, copied, initial]
  refine ⟨copied, final, pace_copy hcopy bs hb initial,
    pace_back hback cs hcs beforeBack hk.2 hpos, heq, ?_⟩
  rw [heq]
  have hf := run_canonical (start radius) (prepEvents sm dm bs cs) hc hc
  exact ⟨hf.1,hf.2,lag_not_zero radius _ hc hp⟩

theorem prep_value (radius : Counter) (sm dm : Bool) (bs cs : List Bool) :
    let final := run (start radius) (prepEvents sm dm bs cs)
    let matchedCount := (sm :: (bs ++ dm :: cs)).count true
    value final.margin = value radius - 4*(bs.length : ℤ) + (matchedCount : ℤ) ∧
    value final.lag = value radius + (matchedCount : ℤ) := by
  have hv := run_value (start radius) (prepEvents sm dm bs cs)
  simpa [prepEvents, start, List.map_append, List.count_append, List.count_replicate] using hv

#print axioms prepare_paced
#print axioms pace_back_quiet
#print axioms prep_value
#print axioms pace_back
#print axioms pace_copy_balance
#print axioms run_value
#print axioms lag_not_zero
end PalPeg.GalilScaffoldChainCredits
