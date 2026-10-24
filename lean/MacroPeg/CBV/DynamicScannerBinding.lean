import MacroPeg.CBV.DynamicScannerCapture
import MacroPeg.CBV.DependentProfileCall

namespace Shallot.MacroPeg.CBV.DynamicScannerBinding
open ClockFreezing (Table)
open RegularCaptureProduct (Node grammar)
open CaptureTransitionProfile (profile profiles)
open DependentCaptureFilter (render)
open DynamicScannerCapture (observer)
abbrev Arg := DependentCaptureFilter.Expr

/-- A finite profile stores the partial resumption state without storing a
bounded approximation of the captured string. -/
def resume {n : Nat} (P : List Nat) (q : Fin n) : Option (Fin n) :=
  let r := P[q.val]?.getD n
  if h : r<n then some ⟨r,h⟩ else none

theorem resume_actual {n : Nat} (M : StatefulScanner.Machine n)
    (w : List Char) (q : Fin n) :
    resume (profile (observer M) w) q=StatefulScanner.advance M q w := by
  unfold resume
  rw [CaptureTransitionProfile.profile_get _ _ _ (by exact Nat.lt_succ_of_lt q.isLt)]
  have hr := DynamicScannerCapture.observer_run M w (some q)
  change RegularCaptureProduct.run (observer M) q.val w=
    DynamicScannerCapture.encode (StatefulScanner.advance M q w) at hr
  rw [Option.getD_some,hr]
  cases ht : StatefulScanner.advance M q w with
  | none => simp [DynamicScannerCapture.encode]
  | some r => simp [DynamicScannerCapture.encode,r.isLt]

def scanner {n : Nat} (base : Nat) (q : Option (Fin n)) : MExp :=
  match q with | some r => .call (base+r.val) [] | none => MExp.failAlways

def scanBase {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n) : Nat :=
  (grammar nodes (observer M)).rules.length+(profiles (observer M)).length

def body {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (P : List Nat) : MExp :=
  .seq (scanner (scanBase nodes M) (resume P q)) (B P)

def extra {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) : List MRule :=
  DependentProfileCall.rules (observer M) (body nodes M q B) ++
    StatefulScanner.block M (fun _ => true) (scanBase nodes M)

abbrev target {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) :=
  FilteredOverlapCaller.extend nodes (observer M) (extra nodes M q B)

abbrev rounds {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (x : List Char) (k : Nat) :=
  DependentProfileCall.rounds nodes (observer M) (extra nodes M q B) x k

def entry {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (S : List (List Nat)) (a : Arg) : MExp :=
  DependentProfileCall.entry nodes (observer M) S a

theorem user_rule {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (P : List Nat) (hP : P∈profiles (observer M)) :
    ruleAtM (target nodes M q B).rules (DependentProfileCall.address nodes (observer M) P)=
      some ⟨1,body nodes M q B P⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp
    (by simpa only [ruleAtM_eq_getElem?] using
      DependentProfileCall.specialized_rule nodes (observer M) (body nodes M q B) P hP)).1
  change ruleAtM ((grammar nodes (observer M)).rules ++
    (DependentProfileCall.rules (observer M) (body nodes M q B) ++
      StatefulScanner.block M (fun _ => true) (scanBase nodes M))) _ = _
  rw [←List.append_assoc]
  change ruleAtM (((grammar nodes (observer M)).rules ++
    DependentProfileCall.rules (observer M) (body nodes M q B)) ++
    StatefulScanner.block M (fun _ => true) (scanBase nodes M)) _ = _
  change DependentProfileCall.address nodes (observer M) P <
    ((grammar nodes (observer M)).rules ++ DependentProfileCall.rules (observer M) (body nodes M q B)).length at hi
  rw [ruleAtM_eq_getElem?,List.getElem?_append_left hi]
  simpa only [DependentProfileCall.specialized,DependentProfileCall.caller,
    FilteredOverlapCaller.extend,ruleAtM_eq_getElem?] using
    DependentProfileCall.specialized_rule nodes (observer M) (body nodes M q B) P hP

theorem scanner_rule {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (r : Fin n) :
    ruleAtM (target nodes M q B).rules (scanBase nodes M+r.val)=
      some ⟨0,StatefulScanner.branches (scanBase nodes M)
        (StatefulScanner.terminal true) (M.arcs r)⟩ := by
  have hlen : ((grammar nodes (observer M)).rules ++
      DependentProfileCall.rules (observer M) (body nodes M q B)).length=scanBase nodes M := by
    simp [scanBase,DependentProfileCall.rules]
  change ruleAtM ((grammar nodes (observer M)).rules ++
    (DependentProfileCall.rules (observer M) (body nodes M q B) ++
      StatefulScanner.block M (fun _ => true) (scanBase nodes M))) _ = _
  rw [←List.append_assoc]
  change ruleAtM (((grammar nodes (observer M)).rules ++
    DependentProfileCall.rules (observer M) (body nodes M q B)) ++
    StatefulScanner.block M (fun _ => true) (scanBase nodes M)) _ = _
  rw [ruleAtM_eq_getElem?,List.getElem?_append_right (by omega),hlen,Nat.add_sub_cancel_left]
  simpa only [ruleAtM_eq_getElem?] using StatefulScanner.block_rule M (fun _ => true) (scanBase nodes M) r

/-- Actual finite profile selection binds the original whole capture in an
installed unary Seq row. Source and target user stages may differ. -/
theorem entry_result {n : Nat} (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (M : StatefulScanner.Machine n) (q : Fin n) (B : List Nat → MExp) (left : List MRule)
    (x : List Char) (k l : Nat) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length) :
    evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x l) E (entry nodes M S a) p =
    match evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
      (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
        (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) E (render a) p with
    | some (some j) => valAt (rounds nodes M q B x l
        (DependentProfileCall.address nodes (observer M) (profile (observer M) (pre x p j))) [pre x p j]) j
    | other => other := by
  have he : evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x l) E (render a) p =
      evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
        (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
          (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) E (render a) p := by
    rw [ParametricHelperControl.rounds_base nodes hNodes (observer M)
        (DynamicScannerCapture.observer_valid M).1 (extra nodes M q B) x .callByValueSeq l E _
        (ParametricHelperControl.render_safe nodes (observer M) a ha) p hp,
      ParametricHelperControl.rounds_base nodes hNodes (observer M)
        (DynamicScannerCapture.observer_valid M).1 left x .callByValuePar k E _
        (ParametricHelperControl.render_safe nodes (observer M) a ha) p hp]
  unfold entry DependentProfileCall.entry
  rw [DependentProfileCall.select_correct nodes hNodes (observer M) (DynamicScannerCapture.observer_valid M)
    (extra nodes M q B) x l S E hS a ha p hp,he]
  cases hv : evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
    (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
      (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) E (render a) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j =>
      dsimp only []
      rw [evV_call_seq (user_rule nodes M q B _
        (CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) _)) rfl]
      simp only [evSeqArgs,he,hv]

theorem firstOrder {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (hB : ∀ P∈profiles (observer M), (B P).FirstOrder) :
    (target nodes M q B).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact RegularCaptureProduct.grammar_firstOrder nodes (observer M) r hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hr
      refine ⟨?_,hB P hP⟩
      unfold scanner
      split <;> trivial
    · exact StatefulScanner.block_firstOrder M (fun _ => true) (scanBase nodes M) r hr

/-- The selected prefix is an installed scanner call. At its ordinary
physical bound it executes the actual residual state, retaining the full
captured word as the surrounding environment. -/
theorem scanner_physical {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (x w : List Char) (p clock : Nat)
    (hp : p≤x.length) (hc : p+1≤clock) :
    evV (target nodes M q B) x .callByValueSeq
      (tblV (target nodes M q B) x .callByValueSeq clock) [w]
      (scanner (scanBase nodes M) (resume (profile (observer M) w) q)) p =
    match StatefulScanner.advance M q w with
    | none => some none
    | some r => some (some (StatefulScanner.run M r (sfx x p)).2.length) := by
  rw [resume_actual]
  cases ht : StatefulScanner.advance M q w with
  | none => rfl
  | some r =>
    change evV _ _ _ _ _ (.call (scanBase nodes M+r.val) []) p=_
    rw [evV_call_seq (scanner_rule nodes M q B r) rfl]
    simp only [evSeqArgs]
    exact StatefulScanner.query_eval M (fun _ => true) (target nodes M q B)
      (scanBase nodes M) (scanner_rule nodes M q B) x .callByValueSeq p hp clock hc r

theorem scanner_prefix_eq {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (x w : List Char) (p j clock : Nat)
    (hj : j≤x.length) (hc : j+1≤clock) (hcap : sfx x p=w++sfx x j)
    (hfrontier : StatefulScanner.advance M q w≠none) :
    evV (target nodes M q B) x .callByValueSeq
      (tblV (target nodes M q B) x .callByValueSeq clock) [w]
      (scanner (scanBase nodes M) (resume (profile (observer M) w) q)) j =
      some (some (StatefulScanner.run M q (sfx x p)).2.length) := by
  rw [scanner_physical nodes M q B x w j clock hj hc]
  cases ht : StatefulScanner.advance M q w with
  | none => exact False.elim (hfrontier ht)
  | some r =>
    rw [hcap,StatefulScanner.run_after_prefix M w (sfx x j) q r ht]

/-- At the next real user stage, the whole captured word is the callee's
actual singleton environment. Its resumption state comes from that capture,
not a fixed type annotation or an assumed successful scanner run. -/
theorem entry_step {n : Nat} (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (M : StatefulScanner.Machine n) (q : Fin n) (B : List Nat → MExp) (left : List MRule)
    (x : List Char) (k l : Nat) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length) :
    evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x (l+1)) E (entry nodes M S a) p =
    match evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
      (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
        (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) E (render a) p with
    | some (some j) => evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x l) [pre x p j]
        (.seq (scanner (scanBase nodes M) (StatefulScanner.advance M q (pre x p j)))
          (B (profile (observer M) (pre x p j)))) j
    | other => other := by
  rw [entry_result nodes hNodes M q B left x k (l+1) S E hS a ha p hp]
  cases hv : evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
    (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
      (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) E (render a) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j =>
      have hj := evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp j hv
      have hr := user_rule nodes M q B _
        (CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) (pre x p j))
      have hi : RecursiveParserStability.pick (RegularCaptureProduct.component nodes (observer M))
          (DependentProfileCall.address nodes (observer M) (profile (observer M) (pre x p j)))=false := by
        simp [RecursiveParserStability.pick,RegularCaptureProduct.component,DependentProfileCall.address]
      dsimp only []
      rw [SeededClock.user_step _ x .callByValueSeq _ _ _ l _ hi _ hr _ j hj]
      simp only [body,resume_actual]

theorem physical {n : Nat} (nodes : List Node) (M : StatefulScanner.Machine n)
    (q : Fin n) (B : List Nat → MExp) (x : List Char) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) (v : Option Nat)
    (hv : evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x k) E e p=some v) :
    evV (target nodes M q B) x .callByValueSeq
      (tblV (target nodes M q B) x .callByValueSeq
        (RecursiveParserStability.floor (RegularCaptureProduct.component nodes (observer M)) x+(k+1)))
      E e p=some v :=
  (evV_mono (SeededClock.rounds_bound _ _ _ _ k) e p).eq_of_some hv

/-- A profile-specialized parent supplies the correct metadata for the next
actual capture. No new accuracy hypothesis is required at the child call. -/
theorem recapture_step {n : Nat} (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (M : StatefulScanner.Machine n) (q : Fin n) (B : List Nat → MExp) (left : List MRule)
    (x parent : List Char) (k l : Nat) (a : Arg) (ha : DependentCaptureFilter.Valid nodes a)
    (p : Nat) (hp : p≤x.length) :
    evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x (l+1)) [parent]
      (entry nodes M [profile (observer M) parent] a) p =
    match evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
      (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
        (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) [parent] (render a) p with
    | some (some j) => evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x l) [pre x p j]
        (.seq (scanner (scanBase nodes M) (StatefulScanner.advance M q (pre x p j)))
          (B (profile (observer M) (pre x p j)))) j
    | other => other :=
  entry_step nodes hNodes M q B left x k l _ [parent]
    (DependentCaptureFilter.environment_accurate (observer M) [parent]) a ha p hp

/-- These installed rows and actual capture-binding calls have exactly the
ordinary grammar's finite observations; seeded stages add no extra result. -/
theorem observations_iff {n : Nat} (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (M : StatefulScanner.Machine n) (q : Fin n) (B : List Nat → MExp)
    (hB : ∀ P∈profiles (observer M), (B P).FirstOrder)
    (x : List Char) (a : Arg) (rest : Option (List Char)) :
    SObs (target nodes M q B) .callByValueSeq (entry nodes M [] a) x rest ↔
      ∃ k v, evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x k)
        [] (entry nodes M [] a) x.length=some v ∧ v.map (sfx x)=rest := by
  exact SeededClock.observations_iff
    (RegularCaptureProduct.component_valid nodes hNodes (observer M) (DynamicScannerCapture.observer_valid M).1)
    (RegularCaptureProduct.component_installed nodes (observer M) (extra nodes M q B))
    (firstOrder nodes M q B hB) x .callByValueSeq (by decide)
    (entry nodes M [] a) (DependentProfileCall.entry_firstOrder nodes (observer M) [] a) rest

/-- An undefined independent argument stays undefined at every ordinary
physical clock, even if a specialized callee could immediately reject. -/
theorem entry_undefined {n : Nat} (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (M : StatefulScanner.Machine n) (q : Fin n) (B : List Nat → MExp) (left : List MRule)
    (x : List Char) (k : Nat) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length)
    (hnone : evV (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar
      (SeededClock.rounds (RegularCaptureProduct.component nodes (observer M))
        (DependentProfileCall.caller nodes (observer M) left) x .callByValuePar k) E (render a) p=none)
    (clock : Nat) :
    evV (target nodes M q B) x .callByValueSeq
      (tblV (target nodes M q B) x .callByValueSeq clock) E (entry nodes M S a) p=none := by
  cases hv : evV (target nodes M q B) x .callByValueSeq
      (tblV (target nodes M q B) x .callByValueSeq clock) E (entry nodes M S a) p with
  | none => rfl
  | some v =>
    obtain ⟨l,hl⟩ := (SeededClock.rounds_defined_iff
      (RegularCaptureProduct.component_valid nodes hNodes (observer M) (DynamicScannerCapture.observer_valid M).1)
      (RegularCaptureProduct.component_installed nodes (observer M) (extra nodes M q B))
      x .callByValueSeq E (entry nodes M S a) p v).mpr ⟨clock,hv⟩
    change evV (target nodes M q B) x .callByValueSeq (rounds nodes M q B x l) E (entry nodes M S a) p=some v at hl
    rw [entry_result nodes hNodes M q B left x k l S E hS a ha p hp,hnone] at hl
    cases hl

end Shallot.MacroPeg.CBV.DynamicScannerBinding
