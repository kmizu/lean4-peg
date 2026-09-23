import PalPeg.ScaWorkerCoroutine
import PalPeg.ScaGsCertData

/-!
# The GS certificates are functional

`ScaWorkerCoroutine.certified_certWorker` needs `certFunctional vs = true`: two entries with the
same configuration and event carry the same row. Checked as written it compares every pair
(`874²` and `1175²` configuration comparisons, and the kernel runs out of memory well before the
end).

This file checks a sufficient condition in `n log n`: every entry gets a number `entryKey`
computed from its configuration and event alone; the keys are sorted by a merge sort with fuel
(`sortKeys`), and the sorted list is checked to be strictly increasing on adjacent pairs
(`strictlySorted`). The sort is a permutation of its input whatever the fuel (running out of fuel
leaves the list unsorted, which the check then rejects), so the keys of the certificate are
pairwise distinct; two entries with the same configuration and event have the same key, hence are
the same entry.

`entryKey` need not be injective for the argument: a collision on the data only makes the check
fail.
-/

set_option autoImplicit false

namespace PalPeg.ScaGsCertFunctional

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaGsCert PalPeg.ScaGsCertData
  PalPeg.ScaWorkerCoroutine

/-! ## Keys -/

/-- A string as digits: its length, then its characters. -/
def stringDigits (s : String) : List Nat := s.length :: s.toList.map Char.toNat

def boolDigit : Bool → Nat
  | false => 0
  | true => 1

def optionBoolDigit : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

def optionNatDigits : Option Nat → List Nat
  | none => [0]
  | some n => [1, n]

def intDigit : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def frameDigits : Frame → List Nat
  | .initialize k site => [0, k, site]
  | .resetShift k search phase nonempty site =>
    [1, k, boolDigit search, phase, optionBoolDigit nonempty, site]
  | .periodShift k search site => [2, k, boolDigit search, site]
  | .first k bounded site => [3, k, boolDigit bounded, site]
  | .second k site => [4, k, site]
  | .decompose k site => [5, k, site]
  | .report flags site => [6, boolDigit flags, site]
  | .finishFlags site => [7, site]
  | .borderController k flags tailOrigin firstStage periodExists site =>
    [8, k, boolDigit flags] ++ stringDigits tailOrigin ++
      [boolDigit firstStage, optionBoolDigit periodExists, site]
  | .matcherController k periodExists prefixOk phase site =>
    [9, k, optionBoolDigit periodExists, optionBoolDigit prefixOk] ++ optionNatDigits phase ++
      [site]
  | .flagController name k tailOrigin site =>
    [10] ++ stringDigits name ++ [k] ++ stringDigits tailOrigin ++ [site]

def configDigits (c : Config) : List Nat :=
  c.length :: (c.map frameDigits).flatten

def movementDigits (m : Movement) : List Nat :=
  stringDigits m.head ++ [intDigit m.delta]

def eventDigits : Event → List Nat
  | .move moves => 0 :: moves.length :: (moves.map movementDigits).flatten
  | .copy target source => 1 :: stringDigits target ++ stringDigits source
  | .equal left right => 2 :: stringDigits left ++ stringDigits right
  | .less left right => 3 :: stringDigits left ++ stringDigits right
  | .symbols left right => 4 :: stringDigits left ++ stringDigits right
  | .border head => 5 :: stringDigits head
  | .flag value => [6, boolDigit value]
  | .available head => 7 :: stringDigits head
  | .assertEqual left right => 8 :: stringDigits left ++ stringDigits right
  | .«match» head => 9 :: stringDigits head
  | .halt => [10]

/-- Digits read in base `2^32` (shifted by one, so no digit is zero). -/
def pack (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * 4294967296 + (d + 1)) 0

/-- The key of an entry: a function of its configuration and event only. -/
def entryKey (v : Entry) : Nat :=
  pack (eventDigits v.event ++ configDigits v.config)

/-! ## A merge sort with fuel -/

/-- Merge; out of fuel, concatenate. -/
def mergeKeys : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if Nat.ble x y then x :: mergeKeys n xs (y :: ys) else y :: mergeKeys n (x :: xs) ys

/-- Merge sort with recursion-depth fuel; out of fuel, the list is returned as is. -/
def sortKeys : Nat → List Nat → List Nat
  | 0, xs => xs
  | n + 1, xs =>
    if xs.length ≤ 1 then xs
    else
      mergeKeys xs.length (sortKeys n (xs.take (xs.length / 2)))
        (sortKeys n (xs.drop (xs.length / 2)))

/-- Adjacent pairs are strictly increasing. -/
def strictlySorted : List Nat → Bool
  | x :: y :: rest => Nat.blt x y && strictlySorted (y :: rest)
  | _ => true

theorem mergeKeys_perm (n : Nat) (xs ys : List Nat) : (mergeKeys n xs ys).Perm (xs ++ ys) := by
  induction n generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    match xs, ys with
    | [], ys => exact List.Perm.refl _
    | x :: xs, [] => simp [mergeKeys]
    | x :: xs, y :: ys =>
      unfold mergeKeys
      split
      · exact (ih xs (y :: ys)).cons x
      · exact ((ih (x :: xs) ys).cons y).trans List.perm_middle.symm

theorem sortKeys_perm (n : Nat) (xs : List Nat) : (sortKeys n xs).Perm xs := by
  induction n generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    unfold sortKeys
    split
    · exact List.Perm.refl _
    · refine (mergeKeys_perm _ _ _).trans ?_
      refine ((ih _).append (ih _)).trans ?_
      rw [List.take_append_drop]

theorem strictlySorted_pairwise : ∀ l : List Nat, strictlySorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: rest, h => by
    simp only [strictlySorted, Bool.and_eq_true, Nat.blt_eq] at h
    have hrest := strictlySorted_pairwise (y :: rest) h.2
    refine List.Pairwise.cons (fun z hz => ?_) hrest
    rcases List.mem_cons.mp hz with rfl | hz
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons hrest hz)

/-! ## The sufficient condition -/

/-- The keys of the certificate, sorted, are strictly increasing. -/
def keysSorted (vs : List Entry) : Bool :=
  strictlySorted (sortKeys 64 (vs.map entryKey))

theorem certFunctional_of_keysSorted {vs : List Entry} (h : keysSorted vs = true) :
    certFunctional vs = true := by
  have hnodup : (vs.map entryKey).Nodup :=
    (sortKeys_perm 64 _).nodup_iff.mp
      ((strictlySorted_pairwise _ h).imp fun hlt => Nat.ne_of_lt hlt)
  simp only [certFunctional, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq, beq_iff_eq]
  intro v hv v' hv'
  by_cases hsame : v.config = v'.config ∧ v.event = v'.event
  · right
    have hkey : entryKey v = entryKey v' := by
      unfold entryKey; rw [hsame.1, hsame.2]
    rw [List.inj_on_of_nodup_map hnodup hv hv' hkey]
  · left
    by_cases hconfig : v.config = v'.config
    · exact Or.inr fun hevent => hsame ⟨hconfig, hevent⟩
    · exact Or.inl hconfig

/-! ## The GS certificates -/

/-- Checked by the kernel. -/
theorem matcher_keysSorted : keysSorted matcherCert = true := by
  decide +kernel

/-- Checked by the kernel. -/
theorem flags_keysSorted : keysSorted flagsCert = true := by
  decide +kernel

theorem matcher_certFunctional : certFunctional matcherCert = true :=
  certFunctional_of_keysSorted matcher_keysSorted

theorem flags_certFunctional : certFunctional flagsCert = true :=
  certFunctional_of_keysSorted flags_keysSorted

/-- The matcher coroutine worker read off its certificate runs the matcher table. -/
theorem matcher_certified :
    Certified ScaGsTables.matcherWorker
      (certWorker ScaGsTables.matcherWorker matchTests matcherInitial matcherCert) matcherCert :=
  certified_certWorker matcher_certOk matcher_certFunctional matchTests_areTableTests
    (sinkRowHasNoTargets_of matcherWorker_sinkRow)

/-- The dual-flags coroutine worker read off its certificate runs the flags table. -/
theorem flags_certified :
    Certified ScaGsTables.flagsWorker
      (certWorker ScaGsTables.flagsWorker tests flagsInitial flagsCert) flagsCert :=
  certified_certWorker flags_certOk flags_certFunctional tests_areTableTests
    (sinkRowHasNoTargets_of flagsWorker_sinkRow)

#print axioms matcher_certFunctional
#print axioms flags_certFunctional
#print axioms matcher_certified
#print axioms flags_certified

end PalPeg.ScaGsCertFunctional
