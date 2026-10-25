import MacroPeg.CBV.ScannerAbsorption
import MacroPeg.CBV.BoundedBodyRewrite
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBV.FrontierArgumentNormalization
open NestedScannerArguments (accepts choice scan scan_eval)
open ClockFreezing (Table)

/-- A successful recursive argument must end at the scanner frontier.
Its original evaluation remains in the ordered preflight. -/
structure Argument where
  alphabet : List Char
  helpers : List MExp
  parser : MExp

def argument (a : Argument) := MExp.seq a.parser (.notP (choice a.alphabet))

def safeCheck (size : Nat) (A : List Char) : MExp → Bool
  | .eps | .notP _ => true
  | .chr c => accepts A c
  | .lit w => w.all (accepts A)
  | .seq a b | .alt a b => safeCheck size A a && safeCheck size A b
  | .star a => safeCheck size A a
  | .call i [] => decide (i<size)
  | _ => false

theorem safe_checked (size : Nat) (A : List Char) : ∀ e, safeCheck size A e=true → ScannerAbsorption.Safe size A e
  | .eps,_ | .notP _,_ => True.intro
  | .chr _,h | .lit _,h => h
  | .seq a b,h | .alt a b,h => ⟨safe_checked size A a (Bool.and_eq_true_iff.mp h).1,
      safe_checked size A b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a,h => safe_checked size A a h
  | .call i [],h => (of_decide_eq_true h : i<size)
  | .call _ (_::_),h | .any,h | .range _ _,h | .param _,h | .dbg _,h
  | .lam _ _,h | .invoke _ _ _,h | .callParam _ _,h => by cases h

def check (g : MGrammar) (a : Argument) : Bool :=
  (a.helpers.zipIdx.all (fun (b,i) => match ruleAtM g.rules i with
    | some r => decide (r.arity=0) && MExp.beqE r.body b
    | none => false) && a.helpers.all (safeCheck a.helpers.length a.alphabet)) &&
    safeCheck a.helpers.length a.alphabet a.parser

theorem checked (g : MGrammar) (a : Argument) (hc : check g a=true) :
    RecursiveParserStability.Installed a.helpers g ∧
      (∀ b∈a.helpers, ScannerAbsorption.Safe a.helpers.length a.alphabet b) ∧
      ScannerAbsorption.Safe a.helpers.length a.alphabet a.parser := by
  obtain ⟨hh,hp⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hi,hb⟩ := Bool.and_eq_true_iff.mp hh
  refine ⟨?_,fun b hm => safe_checked _ _ b (List.all_eq_true.mp hb b hm),safe_checked _ _ _ hp⟩
  intro i b hget
  have hm : (b,i)∈a.helpers.zipIdx := List.mem_of_getElem?
    (show a.helpers.zipIdx[i]?=some (b,i) from by simp [List.getElem?_zipIdx,hget])
  have hh := List.all_eq_true.mp hi (b,i) hm
  cases hr : ruleAtM g.rules i with
  | none => simp [hr] at hh
  | some r =>
    simp only [hr] at hh
    have har := of_decide_eq_true (Bool.and_eq_true_iff.mp hh).1
    have hbody := (MExp.beqE_iff _ _).mp (Bool.and_eq_true_iff.mp hh).2
    cases r
    simp_all

/-- Actual finite tables and a checked consuming path supply the endpoint;
no language-equivalence premise is accepted. -/
theorem success_endpoint (g : MGrammar) (a : Argument) (hc : check g a=true)
    (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char))
    (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s (tblV g x s k) E (argument a) p=some (some q)) :
    evV g x s (tblV g x s k) E (scan a.alphabet) p=some (some q) := by
  have hh := checked g a hc
  cases he : evV g x s (tblV g x s k) E a.parser p with
  | none => rw [argument,evV_seq_none he] at hv; cases hv
  | some v => cases v with
    | none => rw [argument,evV_seq_fail he] at hv; cases hv
    | some j =>
      rw [argument,evV_seq_ok he] at hv
      have hscan := ScannerAbsorption.scan_after_success hh.1 a.alphabet hh.2.1 x s k E a.parser hh.2.2 p j hp he
      cases ht : evV g x s (tblV g x s k) E (choice a.alphabet) j with
      | none => simp [evV,ht] at hv
      | some v => cases v with
        | some z => simp [evV,ht] at hv
        | none =>
          have hj : j=q := by simpa only [evV,ht,Option.some.injEq] using hv
          subst q
          rw [hscan,scan,evV_star,evStar_fail ht]

def arguments (ds : List Argument) : List MExp := ds.map argument
def scans (ds : List Argument) : List MExp := ds.map (fun a => scan a.alphabet)
def preflight : List Argument → MExp
  | [] => .eps
  | a::ds => .seq (.andP (argument a)) (preflight ds)

def gate (p : Nat) : Option (Option (List (List Char))) → Option (Option Nat)
  | none => none
  | some none => some none
  | some (some _) => some (some p)

theorem preflight_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (ds : List Argument) (p : Nat) :
    evV g x s T E (preflight ds) p=gate p (evParArgs g x s T E (arguments ds) p) := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [preflight,arguments,List.map_cons,evParArgs]
    change (match evV g x s T E (.andP (argument a)) p with
      | some (some j) => evV g x s T E (preflight ds) j
      | r => r)=_
    rw [CallLookahead.evV_peek]
    cases hv : evV g x s T E (argument a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some j =>
        simp only [CallLookahead.peek,ih,arguments]
        cases evParArgs g x s T E (ds.map argument) p with
        | none => rfl
        | some v => cases v <;> rfl

theorem successful_arguments (g : MGrammar) (ds : List Argument)
    (hc : ds.all (check g)=true) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) (W : List (List Char))
    (hv : evParArgs g x s (tblV g x s k) E (arguments ds) p=some (some W)) :
    evParArgs g x s (tblV g x s k) E (scans ds) p=some (some W) := by
  induction ds generalizing W with
  | nil => exact hv
  | cons a ds ih =>
    obtain ⟨ha,hds⟩ := Bool.and_eq_true_iff.mp hc
    cases he : evV g x s (tblV g x s k) E (argument a) p with
    | none => rw [arguments,List.map_cons,evPar_cons_none he] at hv; cases hv
    | some v => cases v with
      | none => rw [arguments,List.map_cons,evPar_cons_fail he] at hv; cases hv
      | some j =>
        rw [arguments,List.map_cons,evPar_cons_ok he] at hv
        rw [scans,List.map_cons,evPar_cons_ok (success_endpoint g a ha x s k E p j hp he)]
        cases ht : evParArgs g x s (tblV g x s k) E (ds.map argument) p with
        | none => simp [ht] at hv
        | some v => cases v with
          | none => simp [ht] at hv
          | some V =>
            have hh := ih hds V ht
            simp only [scans] at hh
            rw [hh]
            simpa only [ht] using hv

def guarded (i : Nat) (ds : List Argument) := MExp.seq (preflight ds) (.call i (scans ds))

/-- All original arguments execute first, from left to right at the origin.
Failure and undefinedness survive although the scanners always succeed. -/
theorem call_eq (g : MGrammar) (ds : List Argument) (hc : ds.all (check g)=true)
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) (ha : r.arity=ds.length)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call i (arguments ds)) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (guarded i ds) p := by
  have har : r.arity=(arguments ds).length := by simpa [arguments] using ha
  have has : r.arity=(scans ds).length := by simpa [scans] using ha
  rw [evV_call_par hr har (by decide)]
  change _=(match evV g x .callByValuePar (tblV g x .callByValuePar k) E (preflight ds) p with
    | some (some j) => evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call i (scans ds)) j
    | r => r)
  rw [preflight_eval]
  cases hv : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E (arguments ds) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      simp only [gate]
      rw [evV_call_par hr has (by decide),successful_arguments g ds hc x .callByValuePar k E p hp W hv]

end Shallot.MacroPeg.CBV.FrontierArgumentNormalization
