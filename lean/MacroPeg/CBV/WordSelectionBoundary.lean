import MacroPeg.CBV.GuardedControlFusion

/-! The finite syntax of a Word selector cannot discover every new capture.
This is a boundary of that compiler interface, not of Seq language recognition. -/
namespace Shallot.MacroPeg.CBV.WordSelectionBoundary
open WordArguments (Word value)
open GuardedWordSelection (Shape Checks)

/-- All Word expressions offered to a continuation by the guarded selector.
Predicate bodies may recurse, but their successful capture is empty. -/
def candidates : MExp → List MExp
  | .lit w => [.lit w]
  | .param k => [.param k]
  | .notP _ => [.lit []]
  | .alt a b => candidates a ++ candidates b
  | .seq a b => (candidates a).flatMap (fun u => (candidates b).map (MExp.seq u))
  | _ => []

theorem candidates_word : ∀ a w, w ∈ candidates a → Word w
  | .lit _, w, hw | .param _, w, hw | .notP _, w, hw => by
    simp only [candidates,List.mem_singleton] at hw
    subst w
    trivial
  | .alt a b, w, hw => by
    rcases List.mem_append.mp hw with ha | hb
    · exact candidates_word a w ha
    · exact candidates_word b w hb
  | .seq a b, w, hw => by
    obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp hw
    obtain ⟨v,hvb,rfl⟩ := List.mem_map.mp hv
    exact ⟨candidates_word a u hu,candidates_word b v hvb⟩
  | .eps, _, hw | .any, _, hw | .chr _, _, hw | .range _ _, _, hw
  | .call _ _, _, hw | .star _, _, hw | .dbg _, _, hw | .lam _ _, _, hw
  | .callParam _ _, _, hw | .invoke _ _ _, _, hw => by cases hw

/-- Any two continuations agreeing on the finite candidate list produce
identical target syntax, even with arbitrary recursive predicate translation. -/
theorem selectAt_congr (R : MExp → MExp) : ∀ a before K L,
    (∀ w ∈ candidates a, K w = L w) →
    GuardedWordSelection.selectAt R before a K = GuardedWordSelection.selectAt R before a L
  | .lit w, before, K, L, he => by simp only [GuardedWordSelection.selectAt,he (.lit w) (by simp [candidates])]
  | .param k, before, K, L, he => by simp only [GuardedWordSelection.selectAt,he (.param k) (by simp [candidates])]
  | .notP e, before, K, L, he => by simp only [GuardedWordSelection.selectAt,he (.lit []) (by simp [candidates])]
  | .alt a b, before, K, L, he => by
    simp only [GuardedWordSelection.selectAt]
    rw [selectAt_congr R a before K L (fun w hw => he w (List.mem_append_left _ hw)),
      selectAt_congr R b before K L (fun w hw => he w (List.mem_append_right _ hw))]
  | .seq a b, before, K, L, he => by
    simp only [GuardedWordSelection.selectAt]
    apply selectAt_congr R a
    intro u hu
    apply selectAt_congr R b
    intro v hv
    exact he (.seq u v) (List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩)
  | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _ | .range _ _, _, _, _, _
  | .call _ _, _, _, _, _ | .star _, _, _, _, _ | .dbg _, _, _, _, _ | .lam _ _, _, _, _, _
  | .callParam _ _, _, _, _, _ | .invoke _ _ _, _, _, _, _ => rfl

/-- Every successful source capture in the supported shape has one of these
Word values. The environment is fixed; the input and predicate queries vary. -/
theorem success_candidate (g : MGrammar) (x : List Char)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T) :
    ∀ a, Shape a → Checks MExp.FirstOrder a → ∀ p q, p ≤ x.length →
      evV g x .callByValuePar T E a p = some (some q) →
      ∃ w ∈ candidates a, value E w = some (pre x p q)
  | .lit w, _, _, p, q, hp, hv =>
    ⟨.lit w,by simp [candidates],WordArguments.value_of_success g x _ T E (.lit w) True.intro p q hp hv⟩
  | .param k, _, _, p, q, hp, hv =>
    ⟨.param k,by simp [candidates],WordArguments.value_of_success g x _ T E (.param k) True.intro p q hp hv⟩
  | .notP e, _, _, p, q, _, hv => by
    cases hh : evV g x .callByValuePar T E e p with
    | none => simp [evV,hh] at hv
    | some r => cases r with
      | some j => simp [evV,hh] at hv
      | none =>
        have hq : p=q := by simpa only [evV,hh,Option.some.injEq] using hv
        subst q
        exact ⟨.lit [],by simp [candidates],by simp [value,pre]⟩
  | .alt a b, ha, he, p, q, hp, hv => by
    cases hh : evV g x .callByValuePar T E a p with
    | none => rw [evV_alt_none hh] at hv; contradiction
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hh] at hv
        obtain ⟨w,hw,hv⟩ := success_candidate g x T E hT hOk b ha.2 he.2 p q hp hv
        exact ⟨w,List.mem_append_right _ hw,hv⟩
      | some j =>
        rw [evV_alt_ok hh] at hv
        have hj : j=q := by simpa using hv
        subst j
        obtain ⟨w,hw,hv⟩ := success_candidate g x T E hT hOk a ha.1 he.1 p q hp hh
        exact ⟨w,List.mem_append_left _ hw,hv⟩
  | .seq a b, ha, he, p, q, hp, hv => by
    cases hh : evV g x .callByValuePar T E a p with
    | none => rw [evV_seq_none hh] at hv; contradiction
    | some r => cases r with
      | none => rw [evV_seq_fail hh] at hv; simp at hv
      | some j =>
        rw [evV_seq_ok hh] at hv
        obtain ⟨hj,hpre⟩ := ReplayFusion.success_prefix hT E a (GuardedWordSelection.arg_firstOrder a ha.1 he.1) p j hp hh
        obtain ⟨hq,hpre'⟩ := ReplayFusion.success_prefix hT E b (GuardedWordSelection.arg_firstOrder b ha.2 he.2) j q hj hv
        obtain ⟨u,hu,hvu⟩ := success_candidate g x T E hT hOk a ha.1 he.1 p j hp hh
        obtain ⟨v,hv',hvv⟩ := success_candidate g x T E hT hOk b ha.2 he.2 j q hj hv
        refine ⟨.seq u v,List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv',rfl⟩⟩,?_⟩
        simp only [value,hvu,hvv,Option.bind_some,Option.map_some]
        rw [SequenceArguments.pre_concat hp hq hpre hpre']
  | .eps, ha, _, _, _, _, _ | .any, ha, _, _, _, _, _ | .chr _, ha, _, _, _, _, _
  | .range _ _, ha, _, _, _, _, _ | .call _ _, ha, _, _, _, _, _ | .star _, ha, _, _, _, _, _
  | .dbg _, ha, _, _, _, _, _ | .lam _ _, ha, _, _, _, _, _
  | .callParam _ _, ha, _, _, _, _, _ | .invoke _ _ _, ha, _, _, _, _, _ => False.elim ha

/-- A deliberately loose but uniform bound on all values of a finite list
of Word expressions, for one fixed current environment. -/
def budget (E : List (List Char)) : List MExp → Nat
  | [] => 0
  | a::as => ((value E a).getD []).length + budget E as

theorem value_le_budget (E : List (List Char)) : ∀ C a,
    a ∈ C → ∀ w, value E a = some w → w.length ≤ budget E C
  | b::bs, a, ha, w, hw => by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [budget,hw]
    · have hh := value_le_budget E bs a ha w hw
      simp only [budget]
      omega

theorem capture_le_budget (g : MGrammar) (x : List Char)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T)
    (a : MExp) (ha : Shape a) (he : Checks MExp.FirstOrder a)
    (p q : Nat) (hp : p ≤ x.length) (hv : evV g x .callByValuePar T E a p = some (some q)) :
    (pre x p q).length ≤ budget E (candidates a) := by
  obtain ⟨w,hw,hv⟩ := success_candidate g x T E hT hOk a ha he p q hp hv
  exact value_le_budget E _ w hw _ hv

theorem scanner_replicate (g : MGrammar) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (c : Char) (n : Nat) :
    evV g (List.replicate n c) s T E (NestedScannerArguments.scan [c]) n = some (some 0) := by
  rw [NestedScannerArguments.scan_eval _ _ _ _ _ _ _ (by simp)]
  simp [sfx,NestedScannerArguments.accepts,Shallot.beqChar]

/-- No finite family, even with arbitrarily long current parameters and
arbitrary runtime choice between its members, captures every fresh scan. -/
theorem no_finite_word_family (E : List (List Char)) (C : List MExp) (c : Char) :
    ∃ n, ∀ a ∈ C, value E a ≠ some (List.replicate n c) := by
  refine ⟨budget E C + 1,?_⟩
  intro a ha hv
  have hh := value_le_budget E C a ha _ hv
  simp only [List.length_replicate] at hh
  omega

/-- The obstruction uses a genuine successful source repetition, rather
than values chosen independently of the source evaluation. -/
theorem scanner_exceeds_family (g : MGrammar) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (C : List MExp) (c : Char) :
    ∃ x, evV g x s T E (NestedScannerArguments.scan [c]) x.length = some (some 0) ∧
      ∀ a ∈ C, value E a ≠ some (pre x x.length 0) := by
  obtain ⟨n,hn⟩ := no_finite_word_family E C c
  refine ⟨List.replicate n c,?_,?_⟩
  · simpa using scanner_replicate g s T E c n
  · simpa [pre,sfx] using hn

/-- Recursive predicates cannot repair this limitation: even their actual
grammar tables leave the finite outer Word candidates unchanged. -/
theorem no_shape_scanner_equivalent (g : MGrammar) (hg : g.FirstOrder)
    (E : List (List Char)) (c : Char) (a : MExp) (ha : Shape a)
    (he : Checks MExp.FirstOrder a) (k : Nat) :
    ¬ (∀ x, evV g x .callByValuePar (tblV g x .callByValuePar k) E a x.length =
      evV g x .callByValuePar (tblV g x .callByValuePar k) E (NestedScannerArguments.scan [c]) x.length) := by
  intro h
  have hscan' := scanner_replicate g .callByValuePar
    (tblV g (List.replicate (budget E (candidates a)+1) c) .callByValuePar k) E c
    (budget E (candidates a)+1)
  let y := List.replicate (budget E (candidates a)+1) c
  have hv : evV g y .callByValuePar (tblV g y .callByValuePar k) E a y.length = some (some 0) := by
    rw [h y]
    simpa only [y,List.length_replicate] using hscan'
  have hb := capture_le_budget g y (tblV g y .callByValuePar k) E
    (tblV_sound hg (by decide) k) (tblV_ok g y .callByValuePar k)
    a ha he y.length 0 (Nat.le_refl _) hv
  simp [y,pre,sfx] at hb
  omega

/-- The same unbounded scanner has identical original-string observations
under Par and Seq. Thus the finite-selector obstruction is not a language
class separation, even for its own concrete witness. -/
theorem scanner_observations (g : MGrammar) (hg : g.FirstOrder) (c : Char)
    (x : List Char) (r : Option (List Char)) :
    SObs g .callByValuePar (NestedScannerArguments.scan [c]) x r ↔
      SObs g .callByValueSeq (NestedScannerArguments.scan [c]) x r := by
  have hfo := NestedScannerArguments.scan_firstOrder [c]
  rw [← decideObsV_iff hg (by decide) hfo,← decideObsV_iff hg (by decide) hfo]
  have heq : decideObsV .callByValuePar g x (NestedScannerArguments.scan [c]) =
      decideObsV .callByValueSeq g x (NestedScannerArguments.scan [c]) := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq g g x .callByValuePar .callByValueSeq
      (NestedScannerArguments.scan [c]) (NestedScannerArguments.scan [c]) (fun k => by
        rw [NestedScannerArguments.scan_eval _ _ _ _ _ _ _ (Nat.le_refl _),
          NestedScannerArguments.scan_eval _ _ _ _ _ _ _ (Nat.le_refl _)])]
  rw [heq]

end Shallot.MacroPeg.CBV.WordSelectionBoundary
