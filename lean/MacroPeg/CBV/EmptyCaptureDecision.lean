import MacroPeg.CBV.EmptyResultObservation
import MacroPeg.CBV.ScannerFrontier

namespace Shallot.MacroPeg.CBV.EmptyCaptureDecision
open EmptyResultObservation
abbrev Parser := EmptyResultObservation.Expr

/-- Evaluate every original argument, left to right, at the common origin.
The generated arguments themselves are zero width. -/
def preflight : List Parser → MExp
  | [] => .eps
  | a::args => .seq (.andP (normal a)) (preflight args)

def decision : List Parser → (List Bool → MExp) → MExp
  | [],f => f []
  | a::args,f => RootObservation.branch (empty a)
      (decision args (fun bits => f (true::bits)))
      (decision args (fun bits => f (false::bits)))

def compile (args : List Parser) (f : List Bool → MExp) : MExp := .seq (preflight args) (decision args f)

def gateArgs (p : Nat) : Option (Option (List (List Char))) → Res
  | none => none
  | some none => some none
  | some (some _) => some (some p)

theorem preflight_physical (bs : List Parser) (x : List Char) (args : List Parser) (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (preflight args) p=
      gateArgs p (evParArgs (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (args.map plain) p) := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    change (match evV _ _ _ _ _ (.andP (normal a)) p with
      | some (some j) => evV _ _ _ _ _ (preflight args) j | other => other)=_
    rw [CallLookahead.evV_peek,(physical bs x a p k hp).1]
    simp only [List.map_cons,evParArgs]
    cases ha : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        simp only [CallLookahead.peek,ih]
        cases ht : evParArgs (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (args.map plain) p with
        | none => rfl
        | some v => cases v <;> rfl

theorem empty_word_probe (bs : List Parser) (x : List Char) (a : Parser) (p q k : Nat) (hp : p≤x.length)
    (ha : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain a) p=some (some q)) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (empty a) p=
      if (pre x p q).isEmpty then some (some p) else some none := by
  rw [(physical bs x a p k hp).2,ha]
  by_cases hh : (pre x p q).isEmpty=true
  · have hw := List.isEmpty_iff.mp hh
    have hz := (actual_capture_empty_iff bs x a p q k hp ha).mp hw
    rw [(physical bs x a p k hp).2,ha] at hz
    simpa only [hh,if_true] using hz
  · have hn : (pre x p q).isEmpty=false := Bool.eq_false_iff.mpr hh
    rw [hn]
    simp only [Bool.false_eq_true,if_false]
    by_cases hq : q=p
    · subst q
      simp [pre] at hn
    · simp [project,hq]

/-- The bits describe the actual arbitrary-length captured words. No bound
on capture length, prefix-scanner discipline, or helper termination is used. -/
theorem decision_physical (bs : List Parser) (x : List Char) (args : List Parser) (W : List (List Char))
    (p k : Nat) (hp : p≤x.length)
    (hargs : evParArgs (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (args.map plain) p=some (some W))
    (f : List Bool → MExp) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (decision args f) p=
      evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (f (W.map List.isEmpty)) p := by
  induction args generalizing W f with
  | nil => simp only [List.map_nil,evParArgs,Option.some.injEq] at hargs; subst W; rfl
  | cons a args ih =>
    simp only [List.map_cons] at hargs
    cases ha : evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (plain a) p with
    | none => simp [evParArgs,ha] at hargs
    | some v => cases v with
      | none => simp [evParArgs,ha] at hargs
      | some q =>
        cases ht : evParArgs (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (args.map plain) p with
        | none => simp [evParArgs,ha,ht] at hargs
        | some v => cases v with
          | none => simp [evParArgs,ha,ht] at hargs
          | some words =>
            simp only [evParArgs,ha,ht,Option.some.injEq] at hargs
            subst W
            rw [decision,ScannerFrontier.branch_eval _ _ _ p _ (empty_word_probe bs x a p q k hp ha)]
            cases hw : (pre x p q).isEmpty <;> simp only [List.map_cons,hw,if_true,Bool.false_eq_true,if_false]
            · exact ih words ht (fun bits => f (false::bits))
            · exact ih words ht (fun bits => f (true::bits))

/-- One concrete Seq expression computes the empty/nonempty view of the
original Par tuple before entering the selected, possibly consuming leaf.
Preflight is essential: empty-result failure alone conflates producer
failure and producer success with a nonempty word. -/
theorem physical (bs : List Parser) (x : List Char) (args : List Parser) (f : List Bool → MExp)
    (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (compile args f) p=
      match evParArgs (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (args.map plain) p with
      | none => none | some none => some none
      | some (some W) => evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (f (W.map List.isEmpty)) p := by
  have hh := preflight_physical bs x args p k hp
  cases ha : evParArgs (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (args.map plain) p with
  | none => rw [ha] at hh; exact evV_seq_none hh
  | some v => cases v with
    | none => rw [ha] at hh; exact evV_seq_fail hh
    | some W =>
      rw [ha] at hh
      rw [compile,evV_seq_ok hh]
      exact decision_physical bs x args W p k hp ha f


theorem preflight_firstOrder : ∀ args, (preflight args).FirstOrder
  | [] => True.intro
  | a::args => ⟨render_firstOrder _ _,preflight_firstOrder args⟩

theorem decision_firstOrder : ∀ args f, (∀ bits, bits.length=args.length → (f bits).FirstOrder) →
    (decision args f).FirstOrder
  | [],f,h => h [] rfl
  | a::args,f,h => by
    have ht := decision_firstOrder args (fun bits => f (true::bits)) (by intro bits hb; apply h; simp [hb])
    have hf := decision_firstOrder args (fun bits => f (false::bits)) (by intro bits hb; apply h; simp [hb])
    exact ⟨⟨empty_firstOrder a,ht⟩,⟨empty_firstOrder a,hf⟩⟩

theorem compile_firstOrder (args : List Parser) (f : List Bool → MExp)
    (h : ∀ bits, bits.length=args.length → (f bits).FirstOrder) : (compile args f).FirstOrder :=
  ⟨preflight_firstOrder args,decision_firstOrder args f h⟩

end Shallot.MacroPeg.CBV.EmptyCaptureDecision
