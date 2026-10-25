import MacroPeg.CBV.LiteralPrefixObservation
import MacroPeg.CBV.FiniteProfileClosure

namespace Shallot.MacroPeg.CBV.AlphabetCaptureProfiles
open CaptureTransitionProfile (profile profiles compose)
open RecursiveCaptureProfiles
open RecursiveScannerProductCompiler
open DynamicScannerCapture (observer)

abbrev Word (alphabet w : List Char) := ∀ c∈w, c∈alphabet

def generators (D : RegularCaptureProduct.Machine) (alphabet : List Char) : List (List Nat) :=
  alphabet.map (fun c => profile D [c])
def domain (D : RegularCaptureProduct.Machine) (alphabet : List Char) : List (List Nat) :=
  closure D (generators D alphabet)

theorem generators_valid (D : RegularCaptureProduct.Machine) (hD : D.Valid) (alphabet : List Char) :
    UniversalCaptureProfiles.AllIn D (generators D alphabet) := by
  intro P hP
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hP
  exact CaptureTransitionProfile.profile_mem D hD [c]

theorem nil_mem (D : RegularCaptureProduct.Machine) (hD : D.Valid) (alphabet : List Char) :
    profile D []∈domain D alphabet := closure_nil D hD _

theorem word_mem (D : RegularCaptureProduct.Machine) (hD : D.Valid) (alphabet : List Char) :
    ∀ w, Word alphabet w → profile D w∈domain D alphabet
  | [],_ => nil_mem D hD alphabet
  | c::w,hw => closure_append D hD (generators D alphabet) [c] w
      (List.mem_map.mpr ⟨c,hw c (by simp),rfl⟩) (word_mem D hD alphabet w (fun a ha => hw a (by simp [ha])))

/-- No arbitrary profile guess is introduced: every domain member is
realized by an actual word over the finite source alphabet. -/
theorem generated (D : RegularCaptureProduct.Machine) (hD : D.Valid) (alphabet : List Char)
    (P : List Nat) (hP : P∈domain D alphabet) : ∃ w, Word alphabet w ∧ P=profile D w := by
  have hgen : ∀ k, ∀ P∈rounds (generators D alphabet) k [profile D []],
      ∃ w, Word alphabet w ∧ P=profile D w := by
    intro k
    induction k with
    | zero =>
      intro P hP
      have he : P=profile D [] := by simpa [rounds] using hP
      refine ⟨[], ?_, he⟩
      intro c hc
      cases hc
    | succ k ih =>
      intro P hP
      rcases List.mem_append.mp (List.mem_eraseDups.mp hP) with hP | hP
      · exact ih P hP
      · obtain ⟨Q,hQ,hP⟩ := List.mem_flatMap.mp hP
        obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hP
        obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hQ
        obtain ⟨w,hw,rfl⟩ := ih R hR
        exact ⟨c::w,(by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact hc; exact hw a ha),
          CaptureTransitionProfile.compose_correct D hD [c] w⟩
  rw [domain,FiniteProfileClosure.closure_eq_rounds D hD _ (generators_valid D hD alphabet)] at hP
  exact hgen _ P hP

theorem valid (D : RegularCaptureProduct.Machine) (hD : D.Valid) (alphabet : List Char) :
    UniversalCaptureProfiles.AllIn D (domain D alphabet) :=
  UniversalCaptureProfiles.closure_all D hD _ (generators_valid D hD alphabet)

theorem multiply (D : RegularCaptureProduct.Machine) (hD : D.Valid) (alphabet : List Char)
    (P Q : List Nat) (hP : P∈domain D alphabet) (hQ : Q∈domain D alphabet) :
    compose P Q∈domain D alphabet := by
  obtain ⟨u,hu,rfl⟩ := generated D hD alphabet P hP
  obtain ⟨v,hv,rfl⟩ := generated D hD alphabet Q hQ
  rw [CaptureTransitionProfile.compose_correct D hD]
  apply word_mem D hD alphabet
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hu c hc
  · exact hv c hc

def literalCheck (alphabet : List Char) : Arg → Bool
  | .lit w => w.all (fun c => alphabet.contains c)
  | .param _ => true
  | .user _ a | .star a | .notP a => literalCheck alphabet a
  | .seq a b | .alt a b => literalCheck alphabet a && literalCheck alphabet b

abbrev summary {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char) : Summary :=
  fun _ P => if P∈domain (observer M) alphabet then domain (observer M) alphabet else profiles (observer M)

theorem effects_domain {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char)
    (S : List (List Nat)) (hS : S⊆domain (observer M) alphabet) :
    ∀ e, literalCheck alphabet e=true → effects M (summary M alphabet) S e⊆domain (observer M) alphabet
  | .lit w,h => by
    intro P hP
    have he : P=profile (observer M) w := by simpa [effects] using hP
    subst P
    exact word_mem _ (DynamicScannerCapture.observer_valid M) alphabet w
      (by intro c hc; exact List.contains_iff_mem.mp ((List.all_eq_true.mp h) c hc))
  | .param i,_ => by
    cases hs : S[i]? with
    | none => simp [effects,hs]
    | some P =>
      intro Q hQ
      have he : Q=P := by simpa [effects,hs] using hQ
      subst Q
      exact hS (List.mem_of_getElem? hs)
  | .user i a,h => by
    intro P hP
    obtain ⟨Q,hQ,hP⟩ := List.mem_flatMap.mp hP
    have hQ := effects_domain M alphabet S hS a h hQ
    simpa only [summary,if_pos hQ] using hP
  | .seq a b,h => by
    intro P hP
    obtain ⟨Q,hQ,hP⟩ := List.mem_flatMap.mp hP
    obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hP
    exact multiply _ (DynamicScannerCapture.observer_valid M) alphabet Q R
      (effects_domain M alphabet S hS a (Bool.and_eq_true_iff.mp h).1 hQ)
      (effects_domain M alphabet S hS b (Bool.and_eq_true_iff.mp h).2 hR)
  | .alt a b,h => by
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact effects_domain M alphabet S hS a (Bool.and_eq_true_iff.mp h).1 hP
    · exact effects_domain M alphabet S hS b (Bool.and_eq_true_iff.mp h).2 hP
  | .notP _,_ => by
    intro P hP
    have he : P=profile (observer M) [] := by simpa [effects] using hP
    subst P
    exact nil_mem _ (DynamicScannerCapture.observer_valid M) alphabet
  | .star a,h => by
    have ha := effects_domain M alphabet S hS a h
    apply FiniteProfileClosure.closure_subset _ (DynamicScannerCapture.observer_valid M) _ _
      (fun P hP => valid _ (DynamicScannerCapture.observer_valid M) alphabet P (ha hP))
      (nil_mem _ (DynamicScannerCapture.observer_valid M) alphabet) ha
    exact fun P hP Q hQ => multiply _ (DynamicScannerCapture.observer_valid M) alphabet P Q hP hQ

theorem effects_valid {n : Nat} (M : StatefulScanner.Machine n) (C : Summary)
    (hC : ∀ i P, UniversalCaptureProfiles.AllIn (observer M) (C i P))
    (S : List (List Nat)) (hS : UniversalCaptureProfiles.AllIn (observer M) S) :
    ∀ e, UniversalCaptureProfiles.AllIn (observer M) (effects M C S e)
  | .lit w => by
    intro P hP
    have he : P=profile (observer M) w := by simpa [effects] using hP
    subst P
    exact CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) w
  | .param i => by
    cases hs : S[i]? with
    | none => simp [effects,hs,UniversalCaptureProfiles.AllIn]
    | some P =>
      intro Q hQ
      have he : Q=P := by simpa [effects,hs] using hQ
      subst Q
      exact hS P (List.mem_of_getElem? hs)
  | .user i _ => by
    intro P hP
    obtain ⟨Q,_,hP⟩ := List.mem_flatMap.mp hP
    exact hC i Q P hP
  | .seq a b => UniversalCaptureProfiles.product_all _ _ _ (effects_valid M C hC S hS a) (effects_valid M C hC S hS b)
  | .alt a b => by
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact effects_valid M C hC S hS a P hP
    · exact effects_valid M C hC S hS b P hP
  | .notP _ => by
    intro P hP
    have he : P=profile (observer M) [] := by simpa [effects] using hP
    subst P
    exact CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) []
  | .star a => UniversalCaptureProfiles.closure_all _ (DynamicScannerCapture.observer_valid M) _ (effects_valid M C hC S hS a)

theorem summary_valid {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char)
    (i : Nat) (P : List Nat) : UniversalCaptureProfiles.AllIn (observer M) (summary M alphabet i P) := by
  simp only [summary]
  split
  · exact valid _ (DynamicScannerCapture.observer_valid M) alphabet
  · exact fun _ h => h

def machineCheck {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char) : Bool :=
  (List.finRange n).all (fun q => (M.arcs q).all (fun cr => alphabet.contains cr.1))

def headerLiteralCheck {n : Nat} (alphabet : List Char) : Entry n → Bool
  | .replay | .safeReplay | .scan _ | .scannerIterate _ => true
  | .shift q R => ((R q).getD []).all (fun c => alphabet.contains c)
  | .iterate q R => literalCheck alphabet (rawControlArg (.star (.shift q R)))
  | .aligned c => literalCheck alphabet (rawControlArg c)
  | .alt a b | .guard _ a b => headerLiteralCheck alphabet a && headerLiteralCheck alphabet b

abbrev scannerSummary {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char) : ScannerSummary n :=
  fun _ => domain (observer M) alphabet
abbrev inputs {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char) : ProfileCheckedScannerCorrespondence.Inputs :=
  fun _ => domain (observer M) alphabet

def check {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) : Bool :=
  machineCheck M alphabet && bodies.zipIdx.all (fun (b,i) =>
    (scopeCheck bodies b && literalCheck alphabet b) &&
    ((headerCheck M (entries i) && headerLiteralCheck alphabet (entries i)) &&
      (domain (observer M) alphabet).all (RecursiveScannerProductHeader.entryCheck M (entries i))))

theorem scanner_checked {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char)
    (h : machineCheck M alphabet=true) : scannerCheck M (scannerSummary M alphabet)=true := by
  apply List.all_eq_true.mpr
  intro q _
  refine Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr (nil_mem _ (DynamicScannerCapture.observer_valid M) alphabet),?_⟩
  apply List.all_eq_true.mpr
  intro cr hcr
  apply List.all_eq_true.mpr
  intro P hP
  apply List.contains_iff_mem.mpr
  apply multiply _ (DynamicScannerCapture.observer_valid M) alphabet _ P
  · apply word_mem _ (DynamicScannerCapture.observer_valid M) alphabet
    intro c hc
    have he : c=cr.1 := by simpa using hc
    subst c
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp h) q (List.mem_finRange q))) cr hcr)
  · exact hP

theorem header_domain {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char)
    (P : List Nat) (hP : P∈domain (observer M) alphabet) : ∀ e,
    headerLiteralCheck alphabet e=true → headerEffects M (scannerSummary M alphabet) e P⊆domain (observer M) alphabet
  | .replay,_ | .safeReplay,_ => by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP
  | .scan _,_ => fun _ h => h
  | .scannerIterate q,_ => by
    intro Q hQ
    obtain ⟨A,hA,hQ⟩ := List.mem_flatMap.mp hQ
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hQ
    have hBP : B=P := List.mem_singleton.mp hB
    subst B
    apply multiply _ (DynamicScannerCapture.observer_valid M) alphabet A P _ hP
    exact FiniteProfileClosure.closure_subset _ (DynamicScannerCapture.observer_valid M)
      _ _ (valid _ (DynamicScannerCapture.observer_valid M) alphabet)
      (nil_mem _ (DynamicScannerCapture.observer_valid M) alphabet) (fun _ h => h)
      (fun P hP Q hQ => multiply _ (DynamicScannerCapture.observer_valid M) alphabet P Q hP hQ) hA
  | .shift q R,h => by
    intro Q hQ
    obtain ⟨A,hA,hQ⟩ := List.mem_flatMap.mp hQ
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hQ
    have ha : A=profile (observer M) ((R q).getD []) := by simpa using hA
    have hb : B=P := by simpa using hB
    subst A; subst B
    apply multiply _ (DynamicScannerCapture.observer_valid M) alphabet _ P _ hP
    apply word_mem _ (DynamicScannerCapture.observer_valid M) alphabet
    intro c hc
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp h) c hc)
  | .iterate q R,h | .aligned _,h => by
    intro Q hQ
    obtain ⟨A,hA,hQ⟩ := List.mem_flatMap.mp hQ
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hQ
    have hb : B=P := by simpa using hB
    subst B
    apply multiply _ (DynamicScannerCapture.observer_valid M) alphabet A P _ hP
    rw [effects_noUser M (fun _ _ => []) (summary M alphabet) [P] _ (rawControlArg_scoped _)] at hA
    exact effects_domain M alphabet [P] (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP) _ h hA
  | .alt a b,h => by
    intro Q hQ
    rcases List.mem_append.mp hQ with hQ | hQ
    · exact header_domain M alphabet P hP a (Bool.and_eq_true_iff.mp h).1 hQ
    · exact header_domain M alphabet P hP b (Bool.and_eq_true_iff.mp h).2 hQ
  | .guard _ _ b,h => header_domain M alphabet P hP b (Bool.and_eq_true_iff.mp h).2

theorem header_valid {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char)
    (P : List Nat) (hP : P∈profiles (observer M)) : ∀ e,
    UniversalCaptureProfiles.AllIn (observer M) (headerEffects M (scannerSummary M alphabet) e P)
  | .replay | .safeReplay => by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP
  | .scan _ => valid _ (DynamicScannerCapture.observer_valid M) alphabet
  | .scannerIterate q => UniversalCaptureProfiles.product_all _ _ _
      (UniversalCaptureProfiles.closure_all _ (DynamicScannerCapture.observer_valid M) _
        (valid _ (DynamicScannerCapture.observer_valid M) alphabet))
      (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP)
  | .shift q R => UniversalCaptureProfiles.product_all _ _ _
      (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact CaptureTransitionProfile.profile_mem _ (DynamicScannerCapture.observer_valid M) _)
      (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP)
  | .iterate q R | .aligned _ => by
    apply UniversalCaptureProfiles.product_all
    · exact effects_valid M (fun _ _ => []) (by intro i P Q hQ; cases hQ) [P]
        (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP) _
    · intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP
  | .alt a b => by
    intro Q hQ
    rcases List.mem_append.mp hQ with hQ | hQ
    · exact header_valid M alphabet P hP a Q hQ
    · exact header_valid M alphabet P hP b Q hQ
  | .guard _ _ b => header_valid M alphabet P hP b

theorem checked {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true)
    (i : Nat) (b : Arg) (hi : bodies[i]?=some b) :
    scopeCheck bodies b=true ∧ literalCheck alphabet b=true ∧ headerCheck M (entries i)=true ∧
      headerLiteralCheck alphabet (entries i)=true ∧
      ∀ P∈domain (observer M) alphabet, RecursiveScannerProductHeader.entryCheck M (entries i) P=true := by
  have hm : (b,i)∈bodies.zipIdx := List.mem_of_getElem? (show bodies.zipIdx[i]?=some (b,i) from by simp [List.getElem?_zipIdx,hi])
  have hb := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) (b,i) hm)
  have hs := Bool.and_eq_true_iff.mp hb.1
  have he := Bool.and_eq_true_iff.mp hb.2
  have hl := Bool.and_eq_true_iff.mp he.1
  exact ⟨hs.1,hs.2,hl.1,hl.2,List.all_eq_true.mp he.2⟩

theorem grammar_checked {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true) :
    grammarCheck M entries bodies (scannerSummary M alphabet) (summary M alphabet)=true := by
  apply List.all_eq_true.mpr
  intro bi hbi
  obtain ⟨b,i⟩ := bi
  have hb := (Bool.and_eq_true_iff.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) (b,i) hbi))
  have hs := Bool.and_eq_true_iff.mp hb.1
  have he := Bool.and_eq_true_iff.mp hb.2
  have hl := Bool.and_eq_true_iff.mp he.1
  refine Bool.and_eq_true_iff.mpr ⟨hs.1,?_⟩
  apply List.all_eq_true.mpr
  intro P hP
  apply List.all_eq_true.mpr
  intro Q hQ
  apply List.contains_iff_mem.mpr
  by_cases hin : P∈domain (observer M) alphabet
  · simp only [summary,if_pos hin]
    obtain ⟨A,hA,hQ⟩ := List.mem_flatMap.mp hQ
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hQ
    exact multiply _ (DynamicScannerCapture.observer_valid M) alphabet A B
      (header_domain M alphabet P hin (entries i) hl.2 hA)
      (effects_domain M alphabet [P] (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hin) b hs.2 hB)
  · simp only [summary,if_neg hin]
    exact UniversalCaptureProfiles.product_all _ _ _ (header_valid M alphabet P hP (entries i))
      (effects_valid M (summary M alphabet) (summary_valid M alphabet) [P]
        (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hP) b) Q hQ

theorem expression_checked {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true)
    (S : List (List Nat)) (hS : S⊆domain (observer M) alphabet) : ∀ e,
    scopeCheck bodies e=true → literalCheck alphabet e=true →
    ProfileCheckedScannerCorrespondence.check M entries bodies (summary M alphabet) (inputs M alphabet) S e=true
  | .lit _,_,_ | .param _,_,_ => rfl
  | .seq a b,he,ha | .alt a b,he,ha =>
    Bool.and_eq_true_iff.mpr ⟨expression_checked M entries bodies alphabet h S hS a (Bool.and_eq_true_iff.mp he).1 (Bool.and_eq_true_iff.mp ha).1,
      expression_checked M entries bodies alphabet h S hS b (Bool.and_eq_true_iff.mp he).2 (Bool.and_eq_true_iff.mp ha).2⟩
  | .notP a,he,ha | .star a,he,ha => expression_checked M entries bodies alphabet h S hS a he ha
  | .user i a,he,ha => by
    obtain ⟨hi,he⟩ := Bool.and_eq_true_iff.mp he
    have hib : i<bodies.length := of_decide_eq_true hi
    have hr := checked M entries bodies alphabet h i bodies[i] (List.getElem?_eq_getElem hib)
    refine Bool.and_eq_true_iff.mpr ⟨hi,Bool.and_eq_true_iff.mpr ⟨?_,expression_checked M entries bodies alphabet h S hS a he ha⟩⟩
    apply List.all_eq_true.mpr
    intro P hP
    have hd := effects_domain M alphabet S hS a ha hP
    exact Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr hd,hr.2.2.2.2 P hd⟩

theorem bodies_checked {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true) :
    ProfileCheckedScannerCorrespondence.bodiesCheck M entries bodies (summary M alphabet) (inputs M alphabet)=true := by
  refine Bool.and_eq_true_iff.mpr ⟨?_,?_⟩
  · apply List.all_eq_true.mpr
    intro bi hbi
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) bi hbi)).2).1 |> Bool.and_eq_true_iff.mp |> And.left
  · apply List.all_eq_true.mpr
    intro bi hbi
    have hs := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) bi hbi)).1
    apply List.all_eq_true.mpr
    intro P _
    by_cases hin : P∈domain (observer M) alphabet
    · have he := expression_checked M entries bodies alphabet h [P]
        (by intro Q hQ; obtain rfl := List.mem_singleton.mp hQ; exact hin) bi.1 hs.1 hs.2
      simp [he]
    · simp [ProfileCheckedScannerCorrespondence.inputCheck,inputs,hin]

/-- Alphabet support and entry-state checks derive all actual recursive
profile certificates; no successful-capture annotation is supplied. -/
theorem language_translation {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : literalCheck alphabet e=true) :
    ∃ (g : MGrammar) (root : MExp), g.FirstOrder ∧ root.FirstOrder ∧ ∀ x,
      SObs (source M entries bodies) .callByValuePar (sourceExpr M e) x (some []) ↔
        SObs g .callByValueSeq root x (some []) :=
  ProfileCheckedScannerCorrespondence.language_translation M entries bodies
    (scannerSummary M alphabet) (summary M alphabet) (inputs M alphabet)
    (scanner_checked M alphabet (Bool.and_eq_true_iff.mp h).1)
    (grammar_checked M entries bodies alphabet h) (bodies_checked M entries bodies alphabet h) e
    (expression_checked M entries bodies alphabet h [] (by intro P hp; cases hp) e he ha)

theorem observations_iff {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : literalCheck alphabet e=true)
    (x : List Char) (rest : Option (List Char)) :
    SObs (source M entries bodies) .callByValuePar (sourceExpr M e) x rest ↔
      SObs (target M entries bodies) .callByValueSeq (plain M bodies [] e) x rest :=
  ProfileCheckedScannerCorrespondence.observations_iff M entries bodies
    (scannerSummary M alphabet) (summary M alphabet) (inputs M alphabet)
    (scanner_checked M alphabet (Bool.and_eq_true_iff.mp h).1)
    (grammar_checked M entries bodies alphabet h) (bodies_checked M entries bodies alphabet h) e
    (expression_checked M entries bodies alphabet h [] (by intro P hp; cases hp) e he ha) x rest

theorem defined_iff {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : literalCheck alphabet e=true)
    (x : List Char) (v : Option Nat) :
    (∃ k, evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k) []
      (sourceExpr M e) x.length=some v) ↔
    (∃ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) []
      (plain M bodies [] e) x.length=some v) :=
  ProfileCheckedScannerCorrespondence.defined_iff M entries bodies
    (scannerSummary M alphabet) (summary M alphabet) (inputs M alphabet)
    (scanner_checked M alphabet (Bool.and_eq_true_iff.mp h).1)
    (grammar_checked M entries bodies alphabet h) (bodies_checked M entries bodies alphabet h) e
    (expression_checked M entries bodies alphabet h [] (by intro P hp; cases hp) e he ha) x v

theorem undefined_iff {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : literalCheck alphabet e=true) (x : List Char) :
    (∀ k, evV (source M entries bodies) x .callByValuePar (tblV (source M entries bodies) x .callByValuePar k) []
      (sourceExpr M e) x.length=none) ↔
    (∀ k, evV (target M entries bodies) x .callByValueSeq (tblV (target M entries bodies) x .callByValueSeq k) []
      (plain M bodies [] e) x.length=none) :=
  ProfileCheckedScannerCorrespondence.undefined_iff M entries bodies
    (scannerSummary M alphabet) (summary M alphabet) (inputs M alphabet)
    (scanner_checked M alphabet (Bool.and_eq_true_iff.mp h).1)
    (grammar_checked M entries bodies alphabet h) (bodies_checked M entries bodies alphabet h) e
    (expression_checked M entries bodies alphabet h [] (by intro P hp; cases hp) e he ha) x

/-- The finite source checks place an actual recursive argument result
inside the generated domain, without a guessed shape for its value. -/
theorem argument_domain {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E) (hDom : S⊆domain (observer M) alphabet)
    (e : Arg) (he : scopeCheck bodies e=true) (ha : literalCheck alphabet e=true)
    (p q : Nat) (hp : p≤x.length)
    (hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E
      (sourceExpr M e) p=some (some q)) :
    profile (observer M) (pre x p q)∈domain (observer M) alphabet := by
  have hc := capture M entries bodies (scannerSummary M alphabet) (summary M alphabet)
    (scanner_checked M alphabet (Bool.and_eq_true_iff.mp h).1) (grammar_checked M entries bodies alphabet h)
    x k S E hS e he p q hp hv
  exact effects_domain M alphabet S hDom e ha hc.1

theorem word_of_domain {n : Nat} (M : StatefulScanner.Machine n) (alphabet : List Char) (a : Fin n)
    (ha : LiteralPrefixObservation.alphabetCheck M alphabet a=true) (w : List Char)
    (hw : profile (observer M) w∈domain (observer M) alphabet) : Word alphabet w := by
  obtain ⟨v,hv,he⟩ := generated _ (DynamicScannerCapture.observer_valid M) alphabet _ hw
  have hv' := LiteralPrefixObservation.alphabet_advance M alphabet a ha v hv
  have hp := congrArg (fun P => DynamicScannerBinding.resume P a) he
  rw [DynamicScannerBinding.resume_actual,DynamicScannerBinding.resume_actual,hv'] at hp
  exact LiteralPrefixObservation.alphabet_of_readable M alphabet a ha w (by rw [hp]; simp)

/-- Literal-prefix lookahead can be moved past a capture, even when the
literal matched wholly inside that unbounded actual capture. -/
theorem actual_literal_probe {n : Nat} (M : StatefulScanner.Machine n) (entries : Entries n) (bodies : List Arg)
    (alphabet : List Char) (h : check M entries bodies alphabet=true) (a : Fin n)
    (ha : LiteralPrefixObservation.alphabetCheck M alphabet a=true)
    (L : LiteralPrefixObservation.Labels n) (hL : LiteralPrefixObservation.check M alphabet L=true)
    (start : Fin n) (u : List Char) (hu : L start=some u)
    (x : List Char) (k : Nat) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E) (hDom : S⊆domain (observer M) alphabet)
    (e : Arg) (he : scopeCheck bodies e=true) (hLit : literalCheck alphabet e=true)
    (p q : Nat) (hp : p≤x.length)
    (hv : evV (source M entries bodies) x .callByValuePar (sourceTable M entries bodies x k) E
      (sourceExpr M e) p=some (some q)) (T U : ClockFreezing.Table) :
    let w := pre x p q
    GuardedReplayControl.Results (GuardedReplayControl.Aligned x w)
      (evV (source M entries bodies) x .callByValuePar T [w] (.andP (.lit u)) p)
      (evV (target M entries bodies) x .callByValueSeq U [w]
        (LiteralPrefixObservation.query (profile (observer M) w) start L) q) := by
  have hd := argument_domain M entries bodies alphabet h x k S E hS hDom e he hLit p q hp hv
  have hc := capture M entries bodies (scannerSummary M alphabet) (summary M alphabet)
    (scanner_checked M alphabet (Bool.and_eq_true_iff.mp h).1) (grammar_checked M entries bodies alphabet h)
    x k S E hS e he p q hp hv
  have hq := (DependentCaptureFilter.success_prefix (by decide)
    (ClockFreezing.frozen_sound (source_firstOrder M entries bodies) x .callByValuePar (by decide) _ _ k)
    E _ (sourceExpr_firstOrder M e) p q hp hv).1
  exact LiteralPrefixObservation.peek_transfer M alphabet L hL start u hu _ _ x _ _ _ T U p q
    (word_of_domain M alphabet a ha _ hd) ⟨hp,hq,hc.2⟩

end Shallot.MacroPeg.CBV.AlphabetCaptureProfiles
