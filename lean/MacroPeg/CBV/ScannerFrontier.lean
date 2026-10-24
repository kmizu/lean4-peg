import MacroPeg.CBV.NestedScannerArguments
import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.RootObservation

/-! Runtime endpoint ordering for two independent greedy scanners, with no
inclusion or preselected ordering assumption on their character classes. -/
namespace Shallot.MacroPeg.CBV.ScannerFrontier
open NestedScannerArguments

def intersection (A B : List Char) : List Char := A.filter (accepts B)

theorem accepts_intersection (A B : List Char) (c : Char) :
    accepts (intersection A B) c = (accepts A c && accepts B c) := by
  have hh : accepts (intersection A B) c = true ↔ (accepts A c && accepts B c) = true := by
    simp only [accepts_iff_mem,intersection,List.mem_filter,Bool.and_eq_true]
  exact Bool.eq_iff_iff.mpr hh

theorem intersection_left (A B : List Char) : Included (intersection A B) A := by
  intro c hc
  rw [accepts_intersection] at hc
  exact (Bool.and_eq_true_iff.mp hc).1

theorem intersection_right (A B : List Char) : Included (intersection A B) B := by
  intro c hc
  rw [accepts_intersection] at hc
  exact (Bool.and_eq_true_iff.mp hc).2

def remainder (A : List Char) (x : List Char) : List Char := x.dropWhile (accepts A)

/-- A tie uses the first branch. At the first character outside the common
prefix, at least one of the two scanners must stop. -/
def firstStops (A B : List Char) (x : List Char) : Bool :=
  match remainder (intersection A B) x with
  | [] => true
  | c::_ => !(accepts A c)

def guard (A B : List Char) : MExp :=
  .andP (.seq (scan (intersection A B)) (.notP (choice A)))

theorem guard_firstOrder (A B : List Char) : (guard A B).FirstOrder :=
  ⟨scan_firstOrder _,choice_firstOrder _⟩

theorem remainder_suffix (A : List Char) (x : List Char) : ∃ w, x = w ++ remainder A x :=
  ⟨_,(List.takeWhile_append_dropWhile (p := accepts A) (l := x)).symm⟩

theorem remainder_length (A : List Char) (x : List Char) : (remainder A x).length ≤ x.length := by
  obtain ⟨w,hw⟩ := remainder_suffix A x
  have hl := congrArg List.length hw
  simp only [List.length_append] at hl
  omega

theorem remainder_stops (A : List Char) (x : List Char) (c : Char) (rest : List Char)
    (h : remainder A x = c::rest) : accepts A c = false := by
  induction x with
  | nil => cases h
  | cons d x ih =>
    by_cases hd : accepts A d = true
    · simp only [remainder,List.dropWhile_cons_of_pos hd] at h
      exact ih h
    · simp only [remainder,List.dropWhile_cons_of_neg hd] at h
      cases h
      exact Bool.eq_false_iff.mpr hd

theorem first_remainder (A B : List Char) (x : List Char) :
    if firstStops A B x then remainder A x = remainder (intersection A B) x
    else remainder B x = remainder (intersection A B) x := by
  have ha := dropWhile_absorb (intersection A B) A (intersection_left A B) x
  have hb := dropWhile_absorb (intersection A B) B (intersection_right A B) x
  change remainder A (remainder (intersection A B) x) = remainder A x at ha
  change remainder B (remainder (intersection A B) x) = remainder B x at hb
  cases hz : remainder (intersection A B) x with
  | nil =>
    rw [hz] at ha
    have hfirst : firstStops A B x = true := by simp only [firstStops,hz]
    simp only [hfirst,if_true]
    simpa only [remainder,List.dropWhile_nil] using ha.symm
  | cons c rest =>
    have hc := remainder_stops _ _ c rest hz
    rw [accepts_intersection] at hc
    rw [hz] at ha hb
    by_cases hA : accepts A c = true
    · have hB : accepts B c = false := by cases hB : accepts B c <;> simp_all
      have he : remainder B x = c::rest := by simpa [remainder,hB] using hb.symm
      have hfirst : firstStops A B x = false := by simp only [firstStops,hz,hA,Bool.not_true]
      simpa only [hfirst,Bool.false_eq_true,if_false] using he
    · have he : remainder A x = c::rest := by simpa [remainder,hA] using ha.symm
      simpa only [firstStops,hz,Bool.eq_false_iff.mpr hA,Bool.not_false,if_true] using he

/-- The actual input test discovers the stopping order and restores p. -/
theorem guard_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A B : List Char)
    (p : Nat) (hp : p ≤ x.length) :
    evV g x s T E (guard A B) p =
      if firstStops A B (sfx x p) then some (some p) else some none := by
  have hs : sfx x (remainder (intersection A B) (sfx x p)).length =
      remainder (intersection A B) (sfx x p) := by
    exact sfx_suffix (suffix_trans (sfx_is_suffix x p) (remainder_suffix _ _)).choose_spec
  rw [guard,CallLookahead.evV_peek,evV_seq_ok (scan_eval _ _ _ _ _ _ p hp)]
  change CallLookahead.peek p (match evV g x s T E (choice A)
      (remainder (intersection A B) (sfx x p)).length with
    | some (some _) => some none
    | some none => some (some (remainder (intersection A B) (sfx x p)).length)
    | none => none) = _
  rw [choice_eval,hs]
  cases hz : remainder (intersection A B) (sfx x p) with
  | nil => simp [firstStops,hz,CallLookahead.peek]
  | cons c rest =>
    cases ha : accepts A c <;> simp [firstStops,hz,ha,CallLookahead.peek]

def commonPos (A B : List Char) (x : List Char) (p : Nat) : Nat :=
  (remainder (intersection A B) (sfx x p)).length

def lastClass (A B : List Char) (x : List Char) (p : Nat) : List Char :=
  if firstStops A B (sfx x p) then B else A

def finalPos (A B : List Char) (x : List Char) (p : Nat) : Nat :=
  (remainder (lastClass A B x p) (sfx x p)).length

def chunks (A B : List Char) (x : List Char) (p : Nat) : List (List Char) :=
  [pre x p (commonPos A B x p),pre x (commonPos A B x p) (finalPos A B x p)]

def restore (first : Bool) (u v : List Char) : List (List Char) :=
  if first then [u,u++v] else [u++v,u]

theorem commonPos_le (A B : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    commonPos A B x p ≤ p := by
  simpa only [commonPos,length_sfx x hp] using remainder_length (intersection A B) (sfx x p)

theorem common_suffix (A B : List Char) (x : List Char) (p : Nat) :
    sfx x (commonPos A B x p) = remainder (intersection A B) (sfx x p) :=
  sfx_suffix (suffix_trans (sfx_is_suffix x p) (remainder_suffix _ _)).choose_spec

theorem final_resume (A B : List Char) (x : List Char) (p : Nat) :
    (remainder (lastClass A B x p) (sfx x (commonPos A B x p))).length = finalPos A B x p := by
  rw [common_suffix]
  by_cases hf : firstStops A B (sfx x p) = true
  · simp only [lastClass,finalPos,if_pos hf]
    exact congrArg List.length (dropWhile_absorb _ B (intersection_right A B) (sfx x p))
  · simp only [lastClass,finalPos,if_neg hf]
    exact congrArg List.length (dropWhile_absorb _ A (intersection_left A B) (sfx x p))

theorem finalPos_le (A B : List Char) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    finalPos A B x p ≤ commonPos A B x p := by
  rw [← final_resume]
  have hc : commonPos A B x p ≤ x.length := Nat.le_trans (commonPos_le A B x p hp) hp
  simpa only [length_sfx x hc] using remainder_length (lastClass A B x p) (sfx x (commonPos A B x p))

theorem pre_concat (x : List Char) (p c q : Nat) (hp : p ≤ x.length) (hc : c ≤ p) (hq : q ≤ c) :
    pre x p q = pre x p c ++ pre x c q := by
  have hsplit (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ p) :
      sfx x p = pre x p q ++ sfx x q := by
    have hh : sfx x q = (sfx x p).drop (p-q) := by
      simp only [sfx,List.drop_drop]
      congr 1
      omega
    rw [hh]
    exact (List.take_append_drop (p-q) (sfx x p)).symm
  have hc' := Nat.le_trans hc hp
  have he : sfx x p = (pre x p c ++ pre x c q) ++ sfx x q := by
    rw [hsplit p c hp hc,hsplit c q hc' hq,List.append_assoc]
  exact List.append_cancel_right ((hsplit p q hp (Nat.le_trans hq hc)).symm.trans he)

/-- The target's ordinary Seq argument parsers discover the two disjoint
chunks at runtime in either stopping order, including coincident endpoints. -/
theorem sequential_arguments (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A B : List Char)
    (p : Nat) (hp : p ≤ x.length) :
    evSeqArgs g x s T E [scan (intersection A B),scan (lastClass A B x p)] p =
      some (some (chunks A B x p,finalPos A B x p)) := by
  have hc : commonPos A B x p ≤ x.length := Nat.le_trans (commonPos_le A B x p hp) hp
  have hscan : evV g x s T E (scan (intersection A B)) p = some (some (commonPos A B x p)) :=
    scan_eval _ _ _ _ _ _ p hp
  rw [evSeq_cons_ok hscan,
    evSeq_cons_ok (scan_eval g x s T E (lastClass A B x p) (commonPos A B x p) hc)]
  simp only [evSeq_nil]
  change some (some ([pre x p (commonPos A B x p),
    pre x (commonPos A B x p) (remainder (lastClass A B x p)
      (sfx x (commonPos A B x p))).length],
      (remainder (lastClass A B x p) (sfx x (commonPos A B x p))).length)) = _
  rw [final_resume]
  rfl

/-- The original independent captures are reconstructed in their original
parameter order; only one bit of control selects the reconstruction. -/
theorem parallel_arguments (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A B : List Char)
    (p : Nat) (hp : p ≤ x.length) :
    evParArgs g x s T E [scan A,scan B] p = some (some
      (restore (firstStops A B (sfx x p)) (pre x p (commonPos A B x p))
        (pre x (commonPos A B x p) (finalPos A B x p)))) := by
  have he := first_remainder A B (sfx x p)
  have hc := commonPos_le A B x p hp
  have hq := finalPos_le A B x p hp
  have hpre := pre_concat x p (commonPos A B x p) (finalPos A B x p) hp hc hq
  rw [evPar_cons_ok (scan_eval _ _ _ _ _ A p hp),evPar_cons_ok (scan_eval _ _ _ _ _ B p hp)]
  simp only [evPar_nil]
  change some (some [pre x p (remainder A (sfx x p)).length,
    pre x p (remainder B (sfx x p)).length]) = _
  cases hf : firstStops A B (sfx x p) with
  | true =>
    simp only [hf,if_true] at he
    have hh := congrArg List.length he
    change (remainder A (sfx x p)).length = commonPos A B x p at hh
    have hlast : finalPos A B x p = (remainder B (sfx x p)).length := by
      simp [finalPos,lastClass,hf]
    simp only [restore,if_true]
    rw [hh,← hlast,hpre]
  | false =>
    simp only [hf] at he
    have hh := congrArg List.length he
    change (remainder B (sfx x p)).length = commonPos A B x p at hh
    have hlast : finalPos A B x p = (remainder A (sfx x p)).length := by
      simp [finalPos,lastClass,hf]
    simp only [restore,Bool.false_eq_true,if_false]
    rw [hh,← hlast,hpre]


/-- Fixed syntax chooses the target rule before capturing either value.
The guard is repeated on failure, so failure of the chosen call cannot
fall through into the other calling convention. -/
def dispatch (A B : List Char) (left right : Nat) : MExp :=
  RootObservation.branch (guard A B)
    (.call left [scan (intersection A B),scan B])
    (.call right [scan (intersection A B),scan A])

theorem dispatch_firstOrder (A B : List Char) (left right : Nat) :
    (dispatch A B left right).FirstOrder := by
  exact ⟨⟨guard_firstOrder _ _,⟨scan_firstOrder _,scan_firstOrder _,trivial⟩⟩,
    ⟨guard_firstOrder _ _,⟨scan_firstOrder _,scan_firstOrder _,trivial⟩⟩⟩

theorem branch_eval {g : MGrammar} {x : List Char} {s : Strategy}
    {T : Nat → List (List Char) → Val} {E : List (List Char)}
    (test yes no : MExp) (p : Nat) (b : Bool)
    (h : evV g x s T E test p = if b then some (some p) else some none) :
    evV g x s T E (RootObservation.branch test yes no) p =
      if b then evV g x s T E yes p else evV g x s T E no p := by
  cases b with
  | false => simp only [Bool.false_eq_true,if_false] at h ⊢
             simp only [RootObservation.branch,evV,h]
  | true =>
    simp only [if_true] at h ⊢
    simp only [RootObservation.branch,evV,h]
    cases evV g x s T E yes p with
    | none => rfl
    | some result => cases result <;> rfl

/-- The actual Seq expression selects one of two fixed rule slots using the
runtime guard, captures its chunks, and enters the selected body at the
maximum source endpoint. The result may be success, failure, or undefined. -/
theorem dispatch_eval {g : MGrammar} {x : List Char}
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A B : List Char)
    (left right : Nat) (lrule rrule : MRule)
    (hl : ruleAtM g.rules left = some lrule) (hr : ruleAtM g.rules right = some rrule)
    (hla : lrule.arity = 2) (hra : rrule.arity = 2) (p : Nat) (hp : p ≤ x.length) :
    evV g x .callByValueSeq T E (dispatch A B left right) p =
      if firstStops A B (sfx x p) then valAt (T left (chunks A B x p)) (finalPos A B x p)
      else valAt (T right (chunks A B x p)) (finalPos A B x p) := by
  rw [dispatch,branch_eval _ _ _ p _ (guard_eval g x .callByValueSeq T E A B p hp)]
  have ha := sequential_arguments g x .callByValueSeq T E A B p hp
  cases hf : firstStops A B (sfx x p) with
  | true =>
    simp only [lastClass,hf,if_true] at ha
    simp only [if_true]
    rw [evV_call_seq (args := [scan (intersection A B),scan B]) hl hla,ha]
  | false =>
    simp only [lastClass,hf,Bool.false_eq_true,if_false] at ha
    simp only [Bool.false_eq_true,if_false]
    rw [evV_call_seq (args := [scan (intersection A B),scan A]) hr hra,ha]

/-- A common-origin Par call is represented by an actual sorted Seq call,
provided the two selected bodies implement the specified entry-position
relation. This explicit relation is not a whole-grammar compiler theorem. -/
theorem call_of_body_relation {g h : MGrammar} {x : List Char}
    (T U : Nat → List (List Char) → Val) (E F : List (List Char)) (A B : List Char)
    (src left right : Nat) (sr lr rr : MRule)
    (hs : ruleAtM g.rules src = some sr) (hl : ruleAtM h.rules left = some lr)
    (hr : ruleAtM h.rules right = some rr) (hsa : sr.arity = 2)
    (hla : lr.arity = 2) (hra : rr.arity = 2) (p : Nat) (hp : p ≤ x.length)
    (hbody : valAt (T src (restore (firstStops A B (sfx x p))
          (pre x p (commonPos A B x p))
          (pre x (commonPos A B x p) (finalPos A B x p)))) p =
      if firstStops A B (sfx x p) then valAt (U left (chunks A B x p)) (finalPos A B x p)
      else valAt (U right (chunks A B x p)) (finalPos A B x p)) :
    evV g x .callByValuePar T E (.call src [scan A,scan B]) p =
      evV h x .callByValueSeq U F (dispatch A B left right) p := by
  rw [evV_call_par (args := [scan A,scan B]) hs hsa (by decide),parallel_arguments g x .callByValuePar T E A B p hp]
  dsimp only []
  rw [dispatch_eval U F A B left right lr rr hl hr hla hra p hp]
  exact hbody


/-- Two fixed body variants reconstruct the original parameter order. Their
syntax depends only on the stopping-order bit, never on captured strings. -/
def body (first : Bool) (e : MExp) : MExp :=
  MExp.subst ((if first then [1,2] else [2,1]).map CaptureViews.prefixExpr) e

theorem body_firstOrder (first : Bool) (e : MExp) (he : e.FirstOrder) :
    (body first e).FirstOrder := by
  cases first <;> apply firstOrder_subst _ e he
  · exact ⟨CaptureViews.prefixExpr_firstOrder _,CaptureViews.prefixExpr_firstOrder _,trivial⟩
  · exact ⟨CaptureViews.prefixExpr_firstOrder _,CaptureViews.prefixExpr_firstOrder _,trivial⟩

/-- All first-order body expressions can reuse both reconstructed captures
at the common advanced position. Recursive calls still use the same table. -/
theorem body_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (first : Bool) (u v : List Char)
    (e : MExp) (he : e.FirstOrder) (p : Nat) :
    evV g x s T [u,v] (body first e) p = evV g x s T (restore first u v) e p := by
  apply CaptureViews.body_view
  · cases first <;> simp only [if_false,if_true,Bool.false_eq_true,List.mem_cons,List.not_mem_nil,
      or_false,List.length_cons,List.length_nil] <;> intro k hk <;> omega
  · cases first <;> simp [restore,List.take_succ_cons]
  · exact he

/-- With these two actual target-rule bodies installed, the fixed dispatch
expression performs sorting, capture, query entry, and arbitrary body use.
This is a one-query semantic theorem, not a recursive grammar translation. -/
theorem dispatch_body_eval {g : MGrammar} {x : List Char}
    (E : List (List Char)) (A B : List Char) (left right : Nat) (e : MExp) (he : e.FirstOrder)
    (hl : ruleAtM g.rules left = some ⟨2,body true e⟩)
    (hr : ruleAtM g.rules right = some ⟨2,body false e⟩)
    (m p : Nat) (hp : p ≤ x.length) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (dispatch A B left right) p =
      evV g x .callByValueSeq (tblV g x .callByValueSeq m)
        (restore (firstStops A B (sfx x p)) (pre x p (commonPos A B x p))
          (pre x (commonPos A B x p) (finalPos A B x p))) e (finalPos A B x p) := by
  rw [dispatch_eval _ E A B left right _ _ hl hr rfl rfl p hp]
  have hq : finalPos A B x p ≤ x.length :=
    Nat.le_trans (finalPos_le A B x p hp) (Nat.le_trans (commonPos_le A B x p hp) hp)
  cases hf : firstStops A B (sfx x p) with
  | true =>
    simp only [if_true]
    rw [valAt_tblV_succ hl _ hq]
    exact body_eval g x .callByValueSeq _ true _ _ e he _
  | false =>
    simp only [Bool.false_eq_true,if_false]
    rw [valAt_tblV_succ hr _ hq]
    exact body_eval g x .callByValueSeq _ false _ _ e he _


/-- One fixed non-nested pair has both stopping orders after arbitrarily
long shared captures; the control bit cannot be chosen from syntax alone. -/
theorem stopping_order_switches (n : Nat) :
    firstStops ['a','b'] ['a','c'] (List.replicate n 'a' ++ ['b']) = false ∧
    firstStops ['a','b'] ['a','c'] (List.replicate n 'a' ++ ['c']) = true := by
  have hi : intersection ['a','b'] ['a','c'] = ['a'] := by decide
  have hh : ∀ (n : Nat) (tail : List Char),
      remainder ['a'] (List.replicate n 'a' ++ tail) = remainder ['a'] tail := by
    intro n tail
    induction n with
    | zero => rfl
    | succ n ih => simp_all [remainder,List.replicate_succ,accepts,Shallot.beqChar]
  simp only [firstStops,hi,hh]
  decide

end Shallot.MacroPeg.CBV.ScannerFrontier
