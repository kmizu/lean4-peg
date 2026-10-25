import MacroPeg.CBV.GuardedPairSimulation

namespace Shallot.MacroPeg.CBV.ScannerFrontierValues
open NestedScannerArguments ScannerFrontier
open GuardedPairSimulation (values)
open MixedScannerPairFusion (Entry)
open ClockFreezing (Table)

def starts (A : List Char) : List Char → Bool
  | [] => false
  | c::_ => accepts A c

def word (A x : List Char) := x.takeWhile (accepts A)

theorem word_empty_iff (A x : List Char) : word A x=[] ↔ starts A x=false := by
  cases x with
  | nil => simp [word,starts]
  | cons c x => cases ha : accepts A c <;> simp [word,starts,List.takeWhile_cons,ha]

theorem pre_word (x A : List Char) (p : Nat) (hp : p≤x.length) :
    pre x p (remainder A (sfx x p)).length=word A (sfx x p) := by
  have hh := pre_eq (sfx_is_suffix x p)
    ((List.takeWhile_append_dropWhile (p := accepts A) (l := sfx x p)).symm)
  simpa only [length_sfx x hp,word,remainder] using hh

theorem values_words (g : MGrammar) (x : List Char) (T : Table) (r : Entry) (A B : List Char)
    (hr : r.pairing=some (A,B)) (p : Nat) (hp : p≤x.length) : values r x p=[word A (sfx x p),word B (sfx x p)] := by
  have hh := parallel_arguments g x .callByValuePar T [] A B p hp
  rw [evPar_cons_ok (scan_eval g x .callByValuePar T [] A p hp),
    evPar_cons_ok (scan_eval g x .callByValuePar T [] B p hp),evPar_nil] at hh
  simp only [Option.some.injEq] at hh
  change [pre x p (remainder A (sfx x p)).length,pre x p (remainder B (sfx x p)).length]=_ at hh
  rw [pre_word x A p hp,pre_word x B p hp] at hh
  simpa only [values,hr] using hh.symm

theorem empty_remainder (A x : List Char) (h : starts A x=false) : remainder A x=x := by
  cases x with
  | nil => rfl
  | cons c x =>
    change accepts A c=false at h
    simp [remainder,List.dropWhile_cons,h]

theorem probe_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (A : List Char) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.andP (choice A)) p=if starts A (sfx x p) then some (some p) else some none := by
  rw [CallLookahead.evV_peek,choice_eval]
  cases hx : sfx x p with
  | nil => rfl
  | cons c rest => cases hc : accepts A c <;> simp [starts,hc,CallLookahead.peek]

/-- The second retained prefix need not itself come from a scanner.
This concerns the current stateless frontier, not all later suffixes. -/
theorem strip_origin_prefix (A w rest : List Char) (h : starts A (w++rest)=true) :
    Shallot.stripPrefix? w (remainder A (w++rest))=if w=[] then some (remainder A (w++rest)) else none := by
  cases w with
  | nil => rfl
  | cons c w =>
    have ha : accepts A c=true := h
    cases hz : remainder A ((c::w)++rest) with
    | nil => rfl
    | cons d xs =>
      have hd := remainder_stops A ((c::w)++rest) d xs hz
      have hne : Shallot.beqChar c d=false := by
        by_cases he : Shallot.beqChar c d=true
        · have hh : c=d := Char.toNat_inj.mp (by simpa only [Shallot.beqChar,beq_iff_eq] using he)
          subst d; rw [ha] at hd; cases hd
        · exact Bool.eq_false_iff.mpr he
      simp [Shallot.stripPrefix?,hne]

/-- After a nonempty maximal A run, every nonempty capture from the same
origin has a first character that the current frontier cannot match. -/
theorem strip_at_frontier (A B x : List Char) (h : starts A x=true) :
    Shallot.stripPrefix? (word B x) (remainder A x)=if starts B x then none else some (remainder A x) := by
  cases x with
  | nil => cases h
  | cons c x =>
    have ha : accepts A c=true := h
    cases hb : accepts B c with
    | false => simp [word,starts,List.takeWhile_cons,hb,Shallot.stripPrefix?]
    | true =>
      cases hz : remainder A (c::x) with
      | nil => simp [word,starts,List.takeWhile_cons,hb,hz,Shallot.stripPrefix?]
      | cons d rest =>
        have hd := remainder_stops A (c::x) d rest hz
        have hne : Shallot.beqChar c d=false := by
          by_cases he : Shallot.beqChar c d=true
          · have hh : c=d := Char.toNat_inj.mp (by simpa only [Shallot.beqChar,beq_iff_eq] using he)
            subst d
            rw [ha] at hd
            cases hd
          · exact Bool.eq_false_iff.mpr he
        simp [word,starts,List.takeWhile_cons,hb,hz,Shallot.stripPrefix?,hne]

theorem frontier_parameter (g : MGrammar) (x : List Char) (T : Table) (r : Entry) (A B : List Char)
    (hr : r.pairing=some (A,B)) (selected second : Bool) (p : Nat) (hp : p≤x.length)
    (hpos : starts (if selected then B else A) (sfx x p)=true) :
    evV g x .callByValuePar T (values r x p) (.param (if second then 1 else 0))
        (remainder (if selected then B else A) (sfx x p)).length=
      if starts (if second then B else A) (sfx x p) then some none
      else some (some (remainder (if selected then B else A) (sfx x p)).length) := by
  have hsf : sfx x (remainder (if selected then B else A) (sfx x p)).length=
      remainder (if selected then B else A) (sfx x p) :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) (remainder_suffix _ _)).choose_spec
  have hget : (values r x p)[if second then 1 else 0]?=some (word (if second then B else A) (sfx x p)) := by
    rw [values_words g x T r A B hr p hp]
    cases second <;> rfl
  simp only [evV,hget,hsf,strip_at_frontier _ _ _ hpos]
  cases starts (if second then B else A) (sfx x p) <;> rfl

/-- A maximal scanner followed by its explicit frontier test always
succeeds at exactly the scanner endpoint. -/
theorem scanner_argument (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (A : List Char) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (scan A) (.notP (choice A))) p=some (some (remainder A (sfx x p)).length) := by
  have hs : sfx x (remainder A (sfx x p)).length=remainder A (sfx x p) :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) (remainder_suffix A (sfx x p))).choose_spec
  have hf : evV g x s T E (choice A) (remainder A (sfx x p)).length=some none := by
    rw [choice_eval,hs]
    cases hr : remainder A (sfx x p) with
    | nil => rfl
    | cons c rest => simp [remainder_stops A (sfx x p) c rest hr]
  rw [evV_seq_ok (scan_eval g x s T E A p hp)]
  exact evV_not_fail hf

end Shallot.MacroPeg.CBV.ScannerFrontierValues
