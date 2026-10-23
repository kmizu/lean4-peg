import MacroPeg.CBV.ParSimulation.CompilerCorrect
import MacroPeg.CBVtoCBN.Recognition

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (unicodeAlphabet clockDigits sourceArityBound sourceArityBound_spec fullClock_eval_iff
  finiteSource_accepts compilerStart_available emptyInputP)

attribute [local irreducible] unicodeAlphabet

theorem star_any_derives (g : MGrammar) (s : Strategy) : ∀ x : List Char,
    ∃ t, MDerives g s (.star .any) x (.ok t [])
  | [] => ⟨_, .starNil _ _ .anyFail⟩
  | a :: x => by
    obtain ⟨t, ht⟩ := star_any_derives g s x
    exact ⟨_, .starCons _ _ _ _ _ _ (.anyOk a x) ht⟩

theorem Predicate.consume_iff {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char} {P : Prop}
    (h : Predicate g s e x P) : SObs g s (.seq e (.star .any)) x (some []) ↔ P := by
  classical
  by_cases hp : P
  · constructor
    · intro _; exact hp
    · intro _
      obtain ⟨t, ht⟩ := star_any_derives g s x
      exact seq_ok (h.1 hp) ⟨_, ht, rfl⟩
  · constructor
    · intro hs
      have hf : SObs g s (.seq e (.star .any)) x none := seq_fail (h.2 hp)
      have he := sObs_unique hf hs
      cases he
    · exact fun h => False.elim (hp h)

theorem emptyInputP_obs (target source : MGrammar) (e : MExp) (x : List Char) :
    SObs target .callByValuePar (emptyInputP source .callByValueSeq e) x
      (if x = [] ∧ decideObsV .callByValueSeq source [] e = some (some []) then some x else none) := by
  unfold emptyInputP
  by_cases he : decideObsV .callByValueSeq source [] e = some (some [])
  · rw [if_pos he]
    cases x with
    | nil => exact ⟨_, .notFail _ _ .anyFail, by simp [he, MOutcome.restOf]⟩
    | cons a xs => exact ⟨_, .notOk _ _ _ _ (.anyOk a xs), by simp [MOutcome.restOf]⟩
  · rw [if_neg he]
    exact ⟨_, .notOk _ _ _ _ (.eps x), by simp [he, MOutcome.restOf]⟩

theorem emptyInputP_predicate (target : MGrammar) {source : MGrammar} {e : MExp}
    (hg : source.FirstOrder) (he : e.FirstOrder) (x : List Char) :
    Predicate target .callByValuePar (emptyInputP source .callByValueSeq e) x
      (x = [] ∧ SObs source .callByValueSeq e [] (some [])) := by
  apply (Predicate.of_obs (emptyInputP_obs target source e x)).congr
  exact and_congr_right (fun _ => decideObsV_iff hg (by decide) he [] (some []))

theorem compilerBootstrap_iff (c : CompilerConfig) (x : List Char) (r : Option (List Char)) :
    SObs c.target .callByValuePar (.call 4 [.star .any]) x r ↔
      SObs c.target .callByValuePar
        (c.exprCall 0 c.start false (stateValues x (List.replicate c.digits x.length) [] x.length 0)) x r := by
  have hi : ruleAtM c.target.rules 4 = some ⟨1,
      .call (c.address (.expr 0 c.start)) (.lit [] :: .param 0 :: .param 0 :: List.replicate c.digits (.param 0))⟩ := rfl
  obtain ⟨t, ht⟩ := star_any_derives c.target .callByValuePar x
  have hArgs : DerivesArgsPar c.target .callByValuePar x [.star .any] [.lit x] :=
    .cons _ _ _ _ _ _ _ ht (by simp) (.nil x)
  rw [par_call_iff hi rfl hArgs]
  simp [MExp.subst, MExp.substArgs, argAt, substArgs_replicate, CompilerConfig.exprCall,
    primarySlot, stateValues, statePositions, envPositions, prefixValues, prefixValues_replicate,
    prefixValues_append]

def translationConfig (source : MGrammar) (e : MExp) : CompilerConfig :=
  ⟨source, e, unicodeAlphabet, clockDigits source (sourceArityBound source)⟩

/-- One input-independent first-order Par grammar for the source Seq grammar. -/
def translate (source : MGrammar) (e : MExp) : MGrammar := (translationConfig source e).target

theorem translate_firstOrder (source : MGrammar) (e : MExp) : (translate source e).FirstOrder :=
  compileCandidate_firstOrder _ _ _ _

theorem candidateStart_firstOrder : candidateStart.FirstOrder := trivial

/-- First-order sequential CBV recognition is preserved on every original
character string, with no padding, re-encoding, or source termination assumption. -/
theorem translate_recognizes {source : MGrammar} {e : MExp}
    (hg : source.FirstOrder) (he : e.FirstOrder) (x : List Char) :
    SObs (translate source e) .callByValuePar candidateStart x (some []) ↔
      SObs source .callByValueSeq e x (some []) := by
  classical
  let c := translationConfig source e
  have hTop : ruleAtM c.target.rules 3 = some ⟨0,
      .alt (emptyInputP source .callByValueSeq e)
        (.seq (.andP .any) (.seq (.call 4 [.star .any]) (.star .any)))⟩ := rfl
  change SObs c.target .callByValuePar (.call 3 []) x (some []) ↔ _
  rw [par_call_iff hTop rfl (.nil x)]
  have hClosed : MExp.subst [] (emptyInputP source .callByValueSeq e) =
      emptyInputP source .callByValueSeq e := by unfold emptyInputP; split <;> rfl
  simp only [MExp.subst, MExp.substArgs, MExp.andP, hClosed]
  change SObs c.target .callByValuePar
    (.alt (emptyInputP source .callByValueSeq e)
      (.seq (.andP .any) (.seq (.call 4 [.star .any]) (.star .any)))) x (some []) ↔ _
  by_cases hx : x = []
  · subst x
    have hFail : SObs c.target .callByValuePar
        (.seq (.andP .any) (.seq (.call 4 [.star .any]) (.star .any))) [] none :=
      seq_fail (peek_failure ⟨_, .anyFail, rfl⟩)
    rw [alt_fail_right_iff hFail]
    have ht := (emptyInputP_predicate c.target hg he []).obs
    have hEq := unique_iff ht (some [])
    by_cases hAccept : SObs source .callByValueSeq e [] (some []) <;> simp [hEq, hAccept]
  · have hNonempty : 0 < x.length := by cases x <;> simp_all
    have hEmpty : SObs c.target .callByValuePar (emptyInputP source .callByValueSeq e) x none := by
      simpa only [hx, false_and, if_false] using emptyInputP_obs c.target source e x
    have hGuard : SObs c.target .callByValuePar (.andP .any) x (some x) := by
      cases x with
      | nil => exact False.elim (hx rfl)
      | cons a xs => exact peek_success ⟨_, .anyOk a xs, rfl⟩
    rw [alt_fail_left_iff hEmpty, seq_zero_iff hGuard]
    let ds := List.replicate c.digits x.length
    have hd : ds.length = c.digits := List.length_replicate
    have hv : ∀ k ∈ ds, k ≤ x.length := by intro k hk; have h := List.mem_replicate.mp hk; omega
    have hRoot := compiledEvaluator_correct c rfl hg x ds hd hv []
      (by intro span hm; cases hm) e he (compilerStart_available source e) x.length (by omega) 0 (by omega)
    have hBoot : Predicate c.target .callByValuePar (.call 4 [.star .any]) x
        (sourceResult c x ds [] e x.length = some (some 0)) :=
      ⟨fun hp => (compilerBootstrap_iff c x (some x)).2 (hRoot.1.1 hp),
        fun hp => (compilerBootstrap_iff c x none).2 (hRoot.1.2 hp)⟩
    rw [Predicate.consume_iff hBoot]
    have hFull := fullClock_eval_iff source x .callByValueSeq (sourceArityBound source)
      (sourceArityBound_spec source) hNonempty e x.length (Nat.le_refl _) (some 0)
    exact hFull.trans (finiteSource_accepts hg (by decide) he x)

end Shallot.MacroPeg.CBV.ParSimulation
