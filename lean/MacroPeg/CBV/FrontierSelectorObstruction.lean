import MacroPeg.CBV.FrontierStatusSelector

namespace Shallot.MacroPeg.CBV.FrontierSelectorObstruction
open FrontierStatusSelector
open RepeatedFrontierExamples

def probes (i : Fin 2) : MExp :=
  .call (1+i.val) [DelimitedPatternEvaluation.argument args i.val]

def atClock (tree : Tree) (x : List Char) (k : Nat) : Res :=
  evV projected x .callByValueSeq (tblV projected x .callByValueSeq k) []
    (FrontierStatusSelector.render probes tree) x.length

def output (tree : Tree) (x : List Char) : Res := atClock tree x 1

theorem small_probes_succeed (i : Fin 2) :
    ∃ q, evV projected earlySmall .callByValueSeq (tblV projected earlySmall .callByValueSeq 1) []
      (probes i) earlySmall.length=some (some q) := by
  obtain ⟨i,hi⟩ := i
  cases i with
  | zero => exact ⟨5,small_stops_first.2.1⟩
  | succ i =>
    have hz : i=0 := by omega
    subst i
    exact ⟨0,small_stops_first.2.2⟩

theorem large_probes_succeed (i : Fin 2) :
    ∃ q, evV projected earlyLarge .callByValueSeq (tblV projected earlyLarge .callByValueSeq 1) []
      (probes i) earlyLarge.length=some (some q) := by
  obtain ⟨i,hi⟩ := i
  cases i with
  | zero => exact ⟨0,large_stops_first.2.1⟩
  | succ i =>
    have hz : i=0 := by omega
    subst i
    exact ⟨4,large_stops_first.2.2⟩

theorem small_output (tree : Tree) : output tree earlySmall=
    outcomeValue (fun i => viewValue i.val earlySmall) (selected tree) :=
  render_physical projected earlySmall .callByValueSeq _ [] probes _ small_probes_succeed tree

theorem large_output (tree : Tree) : output tree earlyLarge=
    outcomeValue (fun i => viewValue i.val earlyLarge) (selected tree) :=
  render_physical projected earlyLarge .callByValueSeq _ [] probes _ large_probes_succeed tree

/-- Every finite selector of the specified form fails on one of these two
fixed original inputs. There is no bound on its Boolean-control depth,
repeated queries, negations or zero-width repetitions. -/
theorem no_status_selector (tree : Tree) :
    ∃ x∈[earlySmall,earlyLarge], output tree x≠sourceValue x := by
  cases hs : selected tree with
  | fail =>
    refine ⟨earlySmall,by simp,?_⟩
    rw [small_output tree,hs]
    decide +kernel
  | undef =>
    refine ⟨earlySmall,by simp,?_⟩
    rw [small_output tree,hs]
    decide +kernel
  | choose i =>
    obtain ⟨i,hi⟩ := i
    cases i with
    | zero =>
      refine ⟨earlyLarge,by simp,?_⟩
      rw [large_output tree,hs]
      change viewValue 0 earlyLarge≠sourceValue earlyLarge
      decide +kernel
    | succ i =>
      have hz : i=0 := by omega
      subst i
      refine ⟨earlySmall,by simp,?_⟩
      rw [small_output tree,hs]
      change viewValue 1 earlySmall≠sourceValue earlySmall
      decide +kernel

theorem probes_firstOrder (i : Fin 2) : (probes i).FirstOrder := by
  obtain ⟨i,hi⟩ := i
  cases i with
  | zero =>
    change (MExp.call 1 [.lit ['a']]).FirstOrder
    exact ⟨True.intro,True.intro⟩
  | succ i =>
    have hz : i=0 := by omega
    subst i
    change (MExp.call 2 [.lit ['a','b']]).FirstOrder
    exact ⟨True.intro,True.intro⟩

theorem selectors_firstOrder (tree : Tree) :
    (FrontierStatusSelector.render probes tree).FirstOrder := render_firstOrder probes probes_firstOrder tree

theorem projected_firstOrder : projected.FirstOrder := by
  intro r hr
  simp only [projected,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · trivial
  · exact RepeatedFrontierTransfer.afterLoop_firstOrder _ _ _
  · exact RepeatedFrontierTransfer.afterLoop_firstOrder _ _ _

theorem sample_probes_succeed (x : List Char) (hx : x∈[earlySmall,earlyLarge]) :
    ∀ i, ∃ q, evV projected x .callByValueSeq (tblV projected x .callByValueSeq 1) []
      (probes i) x.length=some (some q) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl
  · exact small_probes_succeed
  · exact large_probes_succeed

/-- This obstruction does not depend on testing at one chosen clock.
All successful probe results persist, so every positive clock selects the
same frontier (or the same finite failure/undefined result). -/
theorem positive_clock (tree : Tree) (x : List Char) (hx : x∈[earlySmall,earlyLarge]) (k : Nat) :
    atClock tree x (k+1)=output tree x := by
  have h1 := sample_probes_succeed x hx
  have hp : ∀ i, ∃ q, evV projected x .callByValueSeq (tblV projected x .callByValueSeq (k+1)) []
      (probes i) x.length=some (some q) := by
    intro i
    obtain ⟨q,hq⟩ := h1 i
    exact ⟨q,evV_lift (show 1≤k+1 by omega) hq⟩
  have he (i : Fin 2) :
      evV projected x .callByValueSeq (tblV projected x .callByValueSeq (k+1)) [] (probes i) x.length=
        evV projected x .callByValueSeq (tblV projected x .callByValueSeq 1) [] (probes i) x.length := by
    obtain ⟨q,hq⟩ := h1 i
    exact (evV_lift (show 1≤k+1 by omega) hq).trans hq.symm
  unfold atClock output
  rw [render_physical projected x .callByValueSeq _ [] probes _ hp tree]
  change _=evV projected x .callByValueSeq (tblV projected x .callByValueSeq 1) []
    (FrontierStatusSelector.render probes tree) x.length
  rw [render_physical projected x .callByValueSeq _ [] probes _ h1 tree]
  cases selected tree <;> simp only [outcomeValue,he]

theorem sample_source_success (x : List Char) (hx : x∈[earlySmall,earlyLarge]) :
    ∃ q, sourceValue x=some (some q) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl
  · exact ⟨5,small_stops_first.1⟩
  · exact ⟨4,large_stops_first.1⟩

/-- For every compiled selector, a fixed original input witnesses failure
at every evaluation clock, including all possible finite-run witnesses. -/
theorem no_status_selector_any_clock (tree : Tree) :
    ∃ x∈[earlySmall,earlyLarge], ∀ k, atClock tree x k≠sourceValue x := by
  obtain ⟨x,hx,hbad⟩ := no_status_selector tree
  refine ⟨x,hx,?_⟩
  intro k hk
  cases k with
  | zero =>
    obtain ⟨q,hq⟩ := sample_source_success x hx
    have hv : evV projected x .callByValueSeq (tblV projected x .callByValueSeq 0) []
        (FrontierStatusSelector.render probes tree) x.length=some (some q) := hk.trans hq
    have hpos := evV_lift (show 0≤1 from Nat.zero_le _) hv
    exact hbad (hpos.trans hq.symm)
  | succ k => exact hbad ((positive_clock tree x hx k).symm.trans hk)

/-- The missing residual observation is not recovered by choosing a
different finite derivation. This remains a result about this selector
compiler and its fixed projection grammar. -/
theorem no_status_selector_observation (tree : Tree) :
    ∃ x∈[earlySmall,earlyLarge], ∃ q,
      sourceValue x=some (some q) ∧
      ¬SObs projected .callByValueSeq (FrontierStatusSelector.render probes tree) x (some (sfx x q)) := by
  obtain ⟨x,hx,hbad⟩ := no_status_selector_any_clock tree
  obtain ⟨q,hq⟩ := sample_source_success x hx
  refine ⟨x,hx,q,hq,?_⟩
  intro ho
  have hv := (decideObsV_iff projected_firstOrder (by decide) (selectors_firstOrder tree) x (some (sfx x q))).mpr ho
  unfold decideObsV at hv
  cases he : atClock tree x (iterBoundV projected x) with
  | none => simp only [atClock] at he; rw [he] at hv; cases hv
  | some r => cases r with
    | none => simp only [atClock] at he; rw [he] at hv; cases hv
    | some j =>
      have hval : evV projected x .callByValueSeq (tblV projected x .callByValueSeq (iterBoundV projected x)) []
          (FrontierStatusSelector.render probes tree) x.length=some (some j) := he
      rw [hval] at hv
      have hs : sfx x j=sfx x q := by simpa using hv
      have hjbound := evV_ok (tblV_ok projected x .callByValueSeq (iterBoundV projected x)) _ x.length (Nat.le_refl _) j hval
      have hqbound := evV_ok (tblV_ok original x .callByValuePar 1) _ x.length (Nat.le_refl _) q hq
      have hl := congrArg List.length hs
      rw [length_sfx x hjbound,length_sfx x hqbound] at hl
      subst j
      exact hbad _ (he.trans hq.symm)

end Shallot.MacroPeg.CBV.FrontierSelectorObstruction
