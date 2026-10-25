import MacroPeg.CBV.CaptureAlphabetEffects
import MacroPeg.CBV.TupleFieldTransfer
import MacroPeg.CBV.ScannerPairFusion

/-! A positive, parameterized recursive producer becomes an outer actual.
Its result contains its own '#' separators and is subsequently retained
and replayed using '@'. The fixed source and target use the original input.
-/
namespace Shallot.MacroPeg.CBV.NestedFieldProducer
open TupleFieldTransfer DelimitedCopyProjection

def doubled : MExp := .seq (.param 0) (.param 0)
def leaf : MExp := .seq (.lit ['!']) (.param 0)
def producerBody : MExp := .alt leaf (.seq (.call 0 [doubled]) (.param 0))
def emittedProducerBody : MExp := .alt leaf
  (.seq (head 0 1 '#' [0] [doubled]) (.param 0))
def source : MGrammar := ⟨[
  ⟨1,sourceBody '#' [0] producerBody⟩,
  ⟨1,sourceBody '@' [0] (.param 0)⟩]⟩
def target : MGrammar := ⟨rules 1 '#' [0] emittedProducerBody++rules 1 '@' [0] (.param 0)⟩
def actual : MExp := .star (.lit ['a'])
def producer : MExp := .call 0 [actual]
def emittedProducer : MExp := head 0 1 '#' [0] [actual]
def root : MExp := .seq (.call 1 [producer]) (.notP .any)
def generatedRoot : MExp := .seq (head 2 1 '@' [0] [emittedProducer]) (.notP .any)
def signatures : List CaptureAlphabetEffects.Signature := [⟨[['a']],['a','#','!']⟩,⟨[['a','#','!']],['a','#','!','@']⟩]

theorem effects_checked : CaptureAlphabetEffects.grammarCheck source signatures=true := by decide +kernel
theorem actual_checked : CaptureAlphabetEffects.check signatures [] ['a'] actual=true := by decide +kernel
theorem producer_checked : CaptureAlphabetEffects.check signatures [] ['a','#','!'] producer=true := by decide +kernel
theorem positive_producer_was_rejected : DelimitedValueSafety.check '@' producer=false := by decide +kernel

theorem source_firstOrder : source.FirstOrder := by
  intro r hr
  simp only [source,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨DelimiterTemplate.compile_firstOrder _ _,by repeat constructor⟩
  · exact ⟨DelimiterTemplate.compile_firstOrder _ _,True.intro⟩

theorem target_firstOrder : target.FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact rules_firstOrder _ _ _ _ (by
      exact ⟨⟨True.intro,True.intro⟩,head_firstOrder _ _ _ _ _ (by repeat constructor),True.intro⟩) r hr
  · exact rules_firstOrder 1 '@' [0] (.param 0) True.intro r hr

private theorem producer_installed : Installed target 0 1 '#' [0] emittedProducerBody := by
  constructor
  · intro i hi
    have hi : i=0 := by omega
    subst i; rfl
  · rfl
private theorem outer_installed : Installed target 2 1 '@' [0] (.param 0) := by
  constructor
  · intro i hi
    have hi : i=0 := by omega
    subst i; rfl
  · rfl

/-- The producer proof is uniform in the actual expression and the
caller's retained environment. The recursive body assumption is discharged
against real tables, including fresh doubled captures and parent return. -/
theorem producer_call (x : List Char) (k : Nat) : ∀ (E : List (List Char)) (a b : MExp)
    (ha : a.FirstOrder) (p : Nat), p≤x.length →
    evV source x .callByValuePar (tblV source x .callByValuePar k) E a p=
      evV target x .callByValueSeq (tblV target x .callByValueSeq k) E b p →
    (∀ q, evV source x .callByValuePar (tblV source x .callByValuePar k) E a p=some (some q) →
      Free '#' (pre x p q)) →
    evV source x .callByValuePar (tblV source x .callByValuePar k) E (.call 0 [a]) p=
      evV target x .callByValueSeq (tblV target x .callByValueSeq k) E (head 0 1 '#' [0] [b]) p := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro E a b ha p hp hab hfree
    apply physical_using source target 0 0 '#' 0 [] producerBody emittedProducerBody
      [a] [b] rfl (by simp) (by intro i hi; simp only [List.mem_singleton] at hi; subst i; simp)
      (UsedFieldCapture.of_cover 1 [0] _ (by
        exact ⟨⟨True.intro,True.intro⟩,head_firstOrder _ _ _ _ _ (by repeat constructor),True.intro⟩)
        (by intro i hi; simpa only [List.mem_singleton] using Nat.lt_one_iff.mp hi))
      rfl producer_installed source_firstOrder ⟨ha,True.intro⟩ x E k p hp
    · intro m hm W hlen hW q hq
      have hEnv : DelimitedValueSafety.Environment '#' W := by
        intro w hw
        obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hw
        rw [←he]; exact hW i hi
      have hcall := ih m hm W doubled doubled (by repeat constructor) q hq rfl
        (fun j hj => DelimitedValueSafety.captured_free '#' source x .callByValuePar
          (tblV source x .callByValuePar m) W hEnv doubled (by rfl) q j hq hj)
      have hseq : evV source x .callByValuePar (tblV source x .callByValuePar m) W
          (.seq (.call 0 [doubled]) (.param 0)) q=
        evV target x .callByValueSeq (tblV target x .callByValueSeq m) W
          (.seq (head 0 1 '#' [0] [doubled]) (.param 0)) q := by
        change (match evV source x .callByValuePar _ W (.call 0 [doubled]) q with
          | some (some j) => evV source x .callByValuePar _ W (.param 0) j | other => other)=_
        rw [hcall]
        rfl
      change (match evV source x .callByValuePar (tblV source x .callByValuePar m) W leaf q with
        | some none => evV source x .callByValuePar _ W (.seq (.call 0 [doubled]) (.param 0)) q | other => other)=
        (match evV source x .callByValuePar (tblV source x .callByValuePar m) W leaf q with
        | some none => evV target x .callByValueSeq _ W (.seq (head 0 1 '#' [0] [doubled]) (.param 0)) q | other => other)
      rw [hseq]
    · intro i hi
      have : i=0 := by simp only [List.length_singleton] at hi; omega
      subst i; exact hab
    · intro i hi j hj
      have : i=0 := by simp only [List.length_singleton] at hi; omega
      subst i; exact hfree j hj

theorem producer_physical (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV source x .callByValuePar (tblV source x .callByValuePar k) [] producer p=
      evV target x .callByValueSeq (tblV target x .callByValueSeq k) [] emittedProducer p :=
  producer_call x k [] actual actual (by repeat constructor) p hp rfl
    (fun q hq => CaptureAlphabetEffects.captured_free source signatures effects_checked x k [] [] .nil
      actual ['a'] actual_checked '#' (by decide) p q hp hq)

theorem outer_physical (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV source x .callByValuePar (tblV source x .callByValuePar k) [] (.call 1 [producer]) p=
      evV target x .callByValueSeq (tblV target x .callByValueSeq k) []
        (head 2 1 '@' [0] [emittedProducer]) p := by
  apply physical_using source target 1 2 '@' 0 [] (.param 0) (.param 0)
    [producer] [emittedProducer] rfl (by simp) (by intro i hi; simp only [List.mem_singleton] at hi; subst i; simp)
    (UsedFieldCapture.of_cover 1 [0] _ True.intro (by intro i hi; simpa only [List.mem_singleton] using Nat.lt_one_iff.mp hi))
    rfl outer_installed source_firstOrder (by repeat constructor) x [] k p hp
  · intro m hm W hl hW q hq; rfl
  · intro i hi
    have : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i; exact producer_physical x k p hp
  · intro i hi q hq
    have : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    exact CaptureAlphabetEffects.captured_free source signatures effects_checked x k [] [] .nil producer
      ['a','#','!'] producer_checked '@' (by decide) p q hp hq

/-- All original inputs and all physical clocks, not only the example
family. This includes producer failure and undefined computations. -/
theorem physical (x : List Char) (k : Nat) :
    evV source x .callByValuePar (tblV source x .callByValuePar k) [] root x.length=
      evV target x .callByValueSeq (tblV target x .callByValueSeq k) [] generatedRoot x.length := by
  change (match evV source x .callByValuePar _ [] (.call 1 [producer]) x.length with
    | some (some q) => evV source x .callByValuePar _ [] (.notP .any) q | other => other)=_
  rw [outer_physical x k x.length (Nat.le_refl _)]
  rfl

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs source .callByValuePar root x rest ↔ SObs target .callByValueSeq generatedRoot x rest := by
  have hr : root.FirstOrder := by repeat constructor
  have ht : generatedRoot.FirstOrder :=
    ⟨head_firstOrder _ _ _ _ _ ⟨head_firstOrder _ _ _ _ _ (by repeat constructor),True.intro⟩,True.intro⟩
  rw [←decideObsV_iff source_firstOrder (by decide) hr,
    ←decideObsV_iff target_firstOrder (by decide) ht]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical x k)]

theorem language_translation :
    (fun x => SObs source .callByValuePar root x (some []))=
      (fun x => SObs target .callByValueSeq generatedRoot x (some [])) := by
  funext x
  exact propext (observations x (some []))

theorem undefined_iff (x : List Char) :
    (∀ k, evV source x .callByValuePar (tblV source x .callByValuePar k) [] root x.length=none) ↔
      (∀ k, evV target x .callByValueSeq (tblV target x .callByValueSeq k) [] generatedRoot x.length=none) := by
  constructor
  · intro h k; rw [←physical x k]; exact h k
  · intro h k; rw [physical x k]; exact h k

end Shallot.MacroPeg.CBV.NestedFieldProducer
