import MacroPeg.CBV.ProfileCheckedScannerCorrespondence

/-! Automatic conservative summaries for unrestricted unary argument syntax.
Only the source entry family remains restricted. No user-supplied output or
input profile sets are required. -/
namespace Shallot.MacroPeg.CBV.UniversalCaptureProfiles
open RecursiveScannerProductCompiler
open RecursiveCaptureProfiles
open CaptureTransitionProfile (profiles profile compose profile_mem)
open DynamicScannerCapture (observer)
open StatefulScanner (Machine)

abbrev AllIn (D : RegularCaptureProduct.Machine) (S : List (List Nat)) :=
  ∀ P∈S, P∈profiles D

theorem compose_mem (D : RegularCaptureProduct.Machine) (P Q : List Nat)
    (hP : P∈profiles D) (hQ : Q∈profiles D) : compose P Q∈profiles D := by
  apply (mem_words _ _ _).mpr
  refine ⟨by simp [compose,CaptureTransitionProfile.member_length D P hP],?_⟩
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  have hq' := ((mem_words _ _ _).mp hP).2 q hq
  exact List.mem_range.mpr (CaptureTransitionProfile.member_bound D Q hQ q (List.mem_range.mp hq'))

theorem product_all (D : RegularCaptureProduct.Machine) (A B : List (List Nat))
    (hA : AllIn D A) (hB : AllIn D B) : AllIn D (product A B) := by
  intro R hR
  obtain ⟨P,hP,hR⟩ := List.mem_flatMap.mp hR
  obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hR
  exact compose_mem D P Q (hA P hP) (hB Q hQ)

theorem rounds_all (D : RegularCaptureProduct.Machine) (A : List (List Nat))
    (hA : AllIn D A) : ∀ k C, AllIn D C → AllIn D (rounds A k C)
  | 0,_,hC => hC
  | k+1,C,hC => by
    have hR := rounds_all D A hA k C hC
    intro P hP
    have hp := List.mem_eraseDups.mp hP
    rcases List.mem_append.mp hp with hp | hp
    · exact hR P hp
    · exact product_all D A _ hA hR P hp

theorem closure_all (D : RegularCaptureProduct.Machine) (hD : D.Valid)
    (A : List (List Nat)) (hA : AllIn D A) : AllIn D (closure D A) := by
  dsimp only [closure]
  split
  · apply rounds_all D A hA
    intro P hP
    have hp : P=profile D [] := by simpa using hP
    subst P
    exact profile_mem D hD []
  · exact fun _ h => h

abbrev summary {n : Nat} (M : Machine n) : Summary := fun _ _ => profiles (observer M)
abbrev scannerSummary {n : Nat} (M : Machine n) : ScannerSummary n := fun _ => profiles (observer M)
abbrev inputs {n : Nat} (M : Machine n) : ProfileCheckedScannerCorrespondence.Inputs := fun _ => profiles (observer M)

theorem effects_all {n : Nat} (M : Machine n) (S : List (List Nat)) (hS : AllIn (observer M) S) :
    ∀ e, AllIn (observer M) (effects M (summary M) S e)
  | .lit w => by
    intro P hP
    have hp : P=profile (observer M) w := by simpa [effects] using hP
    subst P
    exact profile_mem _ (valid M) w
  | .param i => by
    simp only [effects]
    cases hp : S[i]? with
    | none => simp [AllIn]
    | some P =>
      intro Q hQ
      have hQP : Q=P := by simpa using hQ
      subst Q
      exact hS P (List.mem_of_getElem? hp)
  | .user i a => by
    intro P hP
    obtain ⟨Q,_,hQ⟩ := List.mem_flatMap.mp hP
    exact hQ
  | .seq a b => product_all _ _ _ (effects_all M S hS a) (effects_all M S hS b)
  | .alt a b => by
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact effects_all M S hS a P hP
    · exact effects_all M S hS b P hP
  | .notP _ => by
    intro P hP
    have hp : P=profile (observer M) [] := by simpa [effects] using hP
    subst P
    exact profile_mem _ (valid M) []
  | .star a => closure_all _ (valid M) _ (effects_all M S hS a)

/-- Every shift component must have a complete rotating residual machine.
Replay components and finite choice/guard composition need no annotation. -/
def entryCheck {n : Nat} (M : Machine n) : Entry n → Bool
  | .replay | .safeReplay => true
  | .shift q R | .iterate q R => ScannerReplayResidual.entryCheck M R q && ScannerReplayResidual.completeCheck M R
  | .alt a b | .guard _ a b => entryCheck M a && entryCheck M b
  | .aligned c => GuardedReplayControl.check M c && GuardedReplayControl.universalCheck c
  | .scan _ => false

theorem entry_sound {n : Nat} (M : Machine n) : ∀ e, entryCheck M e=true →
    headerCheck M e=true ∧ ∀ P, RecursiveScannerProductHeader.entryCheck M e P=true
  | .replay,_ | .safeReplay,_ => ⟨rfl,fun _ => rfl⟩
  | .shift q R,h => by
    obtain ⟨hs,hc⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨hs,fun P => by simp [RecursiveScannerProductHeader.entryCheck,hc]⟩
  | .iterate q R,h => ⟨h,fun _ => rfl⟩
  | .aligned c,h => by
    obtain ⟨hc,hu⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨hc,fun P => GuardedReplayControl.capture_universal P c hu⟩
  | .alt a b,h | .guard _ a b,h => by
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ha,ha'⟩ := entry_sound M a ha
    obtain ⟨hb,hb'⟩ := entry_sound M b hb
    exact ⟨Bool.and_eq_true_iff.mpr ⟨ha,hb⟩,fun P => Bool.and_eq_true_iff.mpr ⟨ha' P,hb' P⟩⟩
  | .scan _,h => by cases h

/-- The only remaining checks inspect actual source rule syntax and entry
machines. Arbitrary argument seq/alt/star/notP and user recursion are allowed. -/
def check {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) : Bool :=
  bodies.zipIdx.all (fun (b,i) => entryCheck M (entries i) && scopeCheck bodies b)

theorem scanner_checked {n : Nat} (M : Machine n) : scannerCheck M (scannerSummary M)=true := by
  apply List.all_eq_true.mpr
  intro q _
  refine Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (profile_mem _ (valid M) []),?_⟩
  apply List.all_eq_true.mpr
  intro cr _
  apply List.all_eq_true.mpr
  intro P hP
  exact List.contains_iff_mem.mpr (compose_mem _ _ _ (profile_mem _ (valid M) [cr.1]) hP)

theorem header_all {n : Nat} (M : Machine n) (P : List Nat) (hP : P∈profiles (observer M)) :
    ∀ e, AllIn (observer M) (headerEffects M (scannerSummary M) e P)
  | .replay | .safeReplay => by
    intro Q hQ
    have hQP : Q=P := by simpa [headerEffects] using hQ
    subst Q
    exact hP
  | .scan _ => fun _ h => h
  | .iterate q R => by
    apply product_all
    · rw [effects_noUser M (fun _ _ => []) (summary M) [P] _ (rawControlArg_scoped _)]
      exact effects_all M [P] (by simpa [AllIn] using hP) _
    · simpa [AllIn] using hP
  | .aligned c => by
    apply product_all
    · rw [effects_noUser M (fun _ _ => []) (summary M) [P] _ (rawControlArg_scoped _)]
      exact effects_all M [P] (by simpa [AllIn] using hP) _
    · simpa [AllIn] using hP
  | .shift q R => product_all _ _ _ (by simpa [AllIn] using profile_mem (observer M) (valid M) ((R q).getD [])) (by simpa [AllIn] using hP)
  | .alt a b => by
    intro Q hQ
    rcases List.mem_append.mp hQ with hQ | hQ
    · exact header_all M P hP a Q hQ
    · exact header_all M P hP b Q hQ
  | .guard _ _ b => header_all M P hP b

theorem checked {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (i : Nat) (b : Arg) (hi : bodies[i]?=some b) :
    entryCheck M (entries i)=true ∧ scopeCheck bodies b=true := by
  exact Bool.and_eq_true_iff.mp ((List.all_eq_true.mp h) (b,i)
    (List.mem_of_getElem? (show bodies.zipIdx[i]?=some (b,i) from by simp [List.getElem?_zipIdx,hi])))

theorem grammar_checked {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) :
    grammarCheck M entries bodies (scannerSummary M) (summary M)=true := by
  apply List.all_eq_true.mpr
  intro bi hbi
  have hrow := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp h) bi hbi)
  refine Bool.and_eq_true_iff.mpr ⟨hrow.2,?_⟩
  apply List.all_eq_true.mpr
  intro P hP
  apply List.all_eq_true.mpr
  intro Q hQ
  apply List.contains_iff_mem.mpr
  exact product_all _ _ _ (header_all M P hP (entries bi.2))
    (effects_all M [P] (by simpa [AllIn] using hP) bi.1) Q hQ

theorem expression_checked {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (S : List (List Nat)) (hS : AllIn (observer M) S) :
    ∀ e, scopeCheck bodies e=true →
      ProfileCheckedScannerCorrespondence.check M entries bodies (summary M) (inputs M) S e=true
  | .lit _,_ | .param _,_ => rfl
  | .seq a b,he | .alt a b,he =>
    Bool.and_eq_true_iff.mpr ⟨expression_checked M entries bodies h S hS a (Bool.and_eq_true_iff.mp he).1,
      expression_checked M entries bodies h S hS b (Bool.and_eq_true_iff.mp he).2⟩
  | .notP a,he | .star a,he => expression_checked M entries bodies h S hS a he
  | .user i a,he => by
    obtain ⟨hi,ha⟩ := Bool.and_eq_true_iff.mp he
    have hib : i<bodies.length := of_decide_eq_true hi
    have hr := checked M entries bodies h i bodies[i] (List.getElem?_eq_getElem hib)
    refine Bool.and_eq_true_iff.mpr ⟨hi,Bool.and_eq_true_iff.mpr ⟨?_,expression_checked M entries bodies h S hS a ha⟩⟩
    apply List.all_eq_true.mpr
    intro P hP
    exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (effects_all M S hS a P hP),
      (entry_sound M (entries i) hr.1).2 P⟩

theorem bodies_checked {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) :
    ProfileCheckedScannerCorrespondence.bodiesCheck M entries bodies (summary M) (inputs M)=true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_,?_⟩
  · apply List.all_eq_true.mpr
    intro bi hbi
    exact (entry_sound M (entries bi.2) (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp h) bi hbi)).1).1
  · apply List.all_eq_true.mpr
    intro bi hbi
    have hb := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp h) bi hbi)).2
    apply List.all_eq_true.mpr
    intro P hP
    have he := expression_checked M entries bodies h [P] (by simpa [AllIn] using hP) bi.1 hb
    simp [he]

/-- Arbitrary argument concatenation, prioritized choice, negation,
repetition, and recursive recapture require no successful annotation guess.
The finite source entry check is the sole header restriction. -/
theorem language_translation {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (e : Arg) (he : scopeCheck bodies e=true) :
    ∃ (g : MGrammar) (root : MExp), g.FirstOrder ∧ root.FirstOrder ∧ ∀ x,
      SObs (source M entries bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq root x (some []) :=
  ProfileCheckedScannerCorrespondence.language_translation M entries bodies (scannerSummary M) (summary M) (inputs M)
    (scanner_checked M) (grammar_checked M entries bodies h) (bodies_checked M entries bodies h) e
    (expression_checked M entries bodies h [] (by simp [AllIn]) e he)

/-- Full partial equality at the shared user clock after the existing
closed-helper stabilization. This does not identify raw physical clocks. -/
theorem evaluator_eq {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (target M entries bodies) x .callByValueSeq (targetTable M entries bodies x k) []
      (plain M bodies [] e) p=
    evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) []
      (sourceExpr M e) p :=
  ProfileCheckedScannerCorrespondence.evaluator_eq M entries bodies (scannerSummary M) (summary M) (inputs M)
    (scanner_checked M) (grammar_checked M entries bodies h) (bodies_checked M entries bodies h) x k e [] []
    (expression_checked M entries bodies h [] (by simp [AllIn]) e he)
    (DependentCaptureFilter.environment_accurate (observer M) []) p hp

theorem observations_iff {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source M entries bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (target M entries bodies) .callByValueSeq (plain M bodies [] e) x rest :=
  ProfileCheckedScannerCorrespondence.observations_iff M entries bodies (scannerSummary M) (summary M) (inputs M)
    (scanner_checked M) (grammar_checked M entries bodies h) (bodies_checked M entries bodies h) e
    (expression_checked M entries bodies h [] (by simp [AllIn]) e he) x rest

theorem defined_iff {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (e : Arg) (he : scopeCheck bodies e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k)
      [] (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k)
      [] (plain M bodies [] e) x.length=some v) :=
  ProfileCheckedScannerCorrespondence.defined_iff M entries bodies (scannerSummary M) (summary M) (inputs M)
    (scanner_checked M) (grammar_checked M entries bodies h) (bodies_checked M entries bodies h) e
    (expression_checked M entries bodies h [] (by simp [AllIn]) e he) x v

theorem undefined_iff {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg)
    (h : check M entries bodies=true) (e : Arg) (he : scopeCheck bodies e=true) (x : List Char) :
    (∀ k, evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k)
      [] (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k)
      [] (plain M bodies [] e) x.length=none) :=
  ProfileCheckedScannerCorrespondence.undefined_iff M entries bodies (scannerSummary M) (summary M) (inputs M)
    (scanner_checked M) (grammar_checked M entries bodies h) (bodies_checked M entries bodies h) e
    (expression_checked M entries bodies h [] (by simp [AllIn]) e he) x

end Shallot.MacroPeg.CBV.UniversalCaptureProfiles
