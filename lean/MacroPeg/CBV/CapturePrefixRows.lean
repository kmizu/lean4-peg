import MacroPeg.CBV.HeterogeneousProfiledRecursion

/-! Row correspondence depends on the physical captured prefix, independently
of the parser and approximation stage that produced it. -/
namespace Shallot.MacroPeg.CBV.CapturePrefixRows
open RegularCaptureProduct
open CaptureTransitionProfile (profile profiles)
open HeterogeneousProfiledRecursion

/-- A physical suffix decomposition uniquely identifies the captured word. -/
theorem captured_word (x w : List Char) (p j : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) : pre x p j=w := by
  have he := pre_eq (sfx_is_suffix x p) hcap
  simpa only [length_sfx x hp,length_sfx x hj] using he

/-- No argument parser or sound caller table is needed for prefix rotation. -/
theorem prefix_eq (g h : MGrammar) (x : List Char) (T U : ClockFreezing.Table)
    (users : List User) (i : Nat) (r : User) (hr : users[i]?=some r) (hu : r.shift≠[])
    (w : List Char) (p j : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) :
    evV g x .callByValuePar T [w] (.seq (.lit r.shift) (.param 0)) p =
      evV h x .callByValueSeq U [w] (tailPrefix users i r (profile (machine users) w)) j := by
  let empty : MGrammar := ⟨[]⟩
  let V : ClockFreezing.Table := fun _ _ => []
  have hs : SoundTV empty x .callByValuePar V := by
    intro n rule W hn
    cases n <;> cases hn
  have hv : evV empty x .callByValuePar V [] (.lit w) p=some (some j) := by
    simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hcap,length_sfx x hj]
  have he := HeterogeneousProfiledRecursion.prefix_eq empty h x V V U hs [] (.lit w)
    True.intro users i r hr hu p j hp hv
  rw [captured_word x w p j hp hj hcap] at he
  exact (SeededClock.word_eval_eq g empty x .callByValuePar .callByValuePar T V [w]
    (.seq (.lit r.shift) (.param 0)) ⟨True.intro,True.intro⟩ p).trans he

/-- Rows correspond for every actual prefix, even when no current-stage
argument evaluation produces that prefix. -/
def Rows (nodes : List Node) (users : List User) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, users[i]?=some r → ∀ w p j, p≤x.length → j≤x.length → sfx x p=w++sfx x j →
    valAt (parTable nodes users x k ((grammar nodes (machine users)).rules.length+i) [w]) p =
      valAt (seqTable nodes users x k (address nodes users i (profile (machine users) w)) [w]) j

/-- The old same-stage condition follows from physical-prefix rows. -/
theorem shifted_of_rows (nodes : List Node) (users : List User) (x : List Char) (k : Nat)
    (hRows : Rows nodes users x k) : Shifted nodes users x k := by
  intro i r hr E p j hp hj hv
  have hcap := WordStarFilter.success_prefix (by decide)
    (SeededClock.rounds_sound (par_firstOrder nodes users) (helpers nodes users) x .callByValuePar (by decide) k)
    E (DependentCaptureFilter.render r.arg) (DependentCaptureFilter.render_firstOrder r.arg) p j hp hv
  exact hRows i r hr _ p j hp hj hcap.2

theorem rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : HeterogeneousProfiledRecursion.Valid nodes users) (x : List Char) :
    ∀ k, Rows nodes users x k := by
  have hD := CaptureMachineFamily.valid (shifts users)
  have huser (i : Nat) : RecursiveParserStability.pick (helpers nodes users) ((grammar nodes (machine users)).rules.length+i)=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  have htuser (i : Nat) (P : List Nat) : RecursiveParserStability.pick (helpers nodes users) (address nodes users i P)=false := by
    simp [RecursiveParserStability.pick,helpers,component,address]
  intro k
  induction k with
  | zero =>
    intro i r hr w p j hp hj hcap
    have hpar := source_rule nodes users i r hr
    have hseq := target_rule nodes users i r hr (profile (machine users) w) (CaptureTransitionProfile.profile_mem (machine users) hD w)
    have hrot := prefix_eq (parGrammar nodes users) (seqGrammar nodes users) x
      (ClockFreezing.frozen (parGrammar nodes users) x .callByValuePar (RecursiveParserStability.pick (helpers nodes users)) (RecursiveParserStability.floor (helpers nodes users) x) 0)
      (ClockFreezing.frozen (seqGrammar nodes users) x .callByValueSeq (RecursiveParserStability.pick (helpers nodes users)) (RecursiveParserStability.floor (helpers nodes users) x) 0)
      users i r hr (hUsers r (List.mem_of_getElem? hr)).2 w p j hp hj hcap
    change valAt (SeededClock.prefixSeed _ x .callByValuePar _ _ _ [w]) p =
      valAt (SeededClock.prefixSeed _ x .callByValueSeq _ _ _ [w]) j
    rw [SeededClock.prefixSeed_query _ x .callByValuePar _ _ _ (huser i) 1 _ _ hpar _ p hp,
      SeededClock.prefixSeed_query _ x .callByValueSeq _ _ _ (htuser i _) 1 _ _ hseq _ j hj,hrot]
  | succ k ih =>
    intro i r hr w p j hp hj hcap
    have hpar := source_rule nodes users i r hr
    have hseq := target_rule nodes users i r hr (profile (machine users) w) (CaptureTransitionProfile.profile_mem (machine users) hD w)
    have hrot := prefix_eq (parGrammar nodes users) (seqGrammar nodes users) x
      (parTable nodes users x k) (seqTable nodes users x k)
      users i r hr (hUsers r (List.mem_of_getElem? hr)).2 w p j hp hj hcap
    rw [SeededClock.user_step _ x .callByValuePar _ _ _ k _ (huser i) _ hpar _ p hp,
      SeededClock.user_step _ x .callByValueSeq _ _ _ k _ (htuser i _) _ hseq _ j hj]
    change (match evV _ _ _ _ [w] (.seq (.lit r.shift) (.param 0)) p with
      | some (some z) => evV _ _ _ _ [w] (parRender nodes users r.body) z
      | other => other)=_
    rw [hrot]
    dsimp only [targetBody]
    cases hz : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k)
        [w] (tailPrefix users i r (profile (machine users) w)) j with
    | none => rw [evV_seq_none hz]
    | some result => cases result with
      | none => rw [evV_seq_fail hz]
      | some z =>
        dsimp only []
        rw [evV_seq_ok hz]
        exact evaluator_of_rows nodes hNodes users hUsers x k (shifted_of_rows nodes users x k ih) r.body [profile (machine users) w] [w]
          (DependentCaptureFilter.environment_accurate (machine users) [w]) z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ j hj z hz)

/-- Filtering a source row factors through the already captured prefix.
This is a result identity, not yet a construction of product user rules. -/
theorem filter_prefix (D : Machine) (x w : List Char) (p j q r : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (R : Res) (hR : ∀ z, R=some (some z) → z≤x.length ∧ sfx x j=pre x j z++sfx x z) :
    filtered D x q r p R=filtered D x (run D q w) r j R := by
  cases R with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some z =>
      obtain ⟨hz,hzcap⟩ := hR z rfl
      have hword := captured_word x w p j hp hj hcap
      have hc := SequenceArguments.pre_concat hp hz (hword.symm ▸ hcap) hzcap
      rw [hword] at hc
      simp only [filtered,hc,run_append]

/-- A successful table query has the same physical suffix property as
an evaluated first-order expression, including seeded approximation tables. -/
theorem row_success_prefix (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (i : Nat) (rule : MRule) (hr : ruleAtM g.rules i=some rule)
    (W : List (List Char)) (hW : rule.arity=W.length) (p z : Nat) (hp : p≤x.length)
    (hv : valAt (T i W) p=some (some z)) :
    z≤x.length ∧ sfx x p=pre x p z++sfx x z := by
  obtain ⟨o,hd,ho⟩ := hT i rule W hr hW p hp (some z) hv
  obtain ⟨t,rest,rfl,hz⟩ := obsR_ok ho
  have hpre := mderives_suffix hd _ _ rfl
  have hsuf := rest_eq_sfx' hd
  rw [hz] at hsuf
  have hbound : z≤x.length := by
    obtain ⟨w,hw⟩ := hpre
    have hl := congrArg List.length hw
    rw [List.length_append,length_sfx x hp,hz] at hl
    omega
  refine ⟨hbound,?_⟩
  rw [hsuf]
  simpa [hz] using pre_split hp hpre

/-- An arbitrary finite observer can start the target tail after processing
the captured word. All three partial-result cases are preserved. -/
theorem filtered_rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : HeterogeneousProfiledRecursion.Valid nodes users) (x : List Char)
    (k i : Nat) (r : User) (hr : users[i]?=some r) (w : List Char) (p j : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (D : Machine) (q t : Nat) :
    filtered D x q t p (valAt (parTable nodes users x k ((grammar nodes (machine users)).rules.length+i) [w]) p) =
      filtered D x (run D q w) t j
        (valAt (seqTable nodes users x k (address nodes users i (profile (machine users) w)) [w]) j) := by
  rw [rows nodes hNodes users hUsers x k i r hr w p j hp hj hcap]
  apply filter_prefix D x w p j q t hp hj hcap
  intro z hz
  exact row_success_prefix (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k)
    (SeededClock.rounds_sound (seq_firstOrder nodes users) (helpers nodes users) x .callByValueSeq (by decide) k)
    _ _ (target_rule nodes users i r hr _ (CaptureTransitionProfile.profile_mem (machine users)
      (CaptureMachineFamily.valid (shifts users)) w)) [w] rfl j z hj hz

/-- The observer handoff uses finite profile metadata at a bounded
starting state, as required by a static specialization of target rows. -/
theorem filtered_rows_profile (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : HeterogeneousProfiledRecursion.Valid nodes users) (x : List Char)
    (k i : Nat) (r : User) (hr : users[i]?=some r) (w : List Char) (p j : Nat)
    (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (D : Machine) (q t : Nat) (hq : q<D.width) :
    filtered D x q t p (valAt (parTable nodes users x k ((grammar nodes (machine users)).rules.length+i) [w]) p) =
      filtered D x ((profile D w)[q]?.getD 0) t j
        (valAt (seqTable nodes users x k (address nodes users i (profile (machine users) w)) [w]) j) := by
  rw [CaptureTransitionProfile.profile_get D w q hq]
  exact filtered_rows nodes hNodes users hUsers x k i r hr w p j hp hj hcap D q t

/-- Capture may come from a different grammar, strategy, table, or stage.
Only its physical prefix is required by the installed recursive rows. -/
theorem rows_of_capture (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : HeterogeneousProfiledRecursion.Valid nodes users) (x : List Char)
    (k i : Nat) (r : User) (hr : users[i]?=some r)
    (g : MGrammar) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (p j : Nat) (hp : p≤x.length) (hv : evV g x s T E a p=some (some j)) :
    valAt (parTable nodes users x k ((grammar nodes (machine users)).rules.length+i) [pre x p j]) p =
      valAt (seqTable nodes users x k (address nodes users i (profile (machine users) (pre x p j))) [pre x p j]) j := by
  obtain ⟨hj,hcap⟩ := WordStarFilter.success_prefix hs hT E a ha p j hp hv
  exact rows nodes hNodes users hUsers x k i r hr _ p j hp hj hcap

namespace Examples

def users : List User := [⟨.lit ['Z'],"ab".toList,.seq (.lit ['#']) (.param 0)⟩]
def input : List Char := "ababa#aba".toList
def word : List Char := "aba".toList
def observer : Machine := ⟨2,fun q c => if c='b' then 1-q else q⟩

theorem users_valid : HeterogeneousProfiledRecursion.Valid [] users := by
  simp [HeterogeneousProfiledRecursion.Valid,users,DependentCaptureFilter.Valid]

theorem source_execution :
    evV (parGrammar [] users) input .callByValuePar (parTable [] users input 1) []
      (DependentCaptureFilter.render (.lit ['Z'])) input.length=some none ∧
    valAt (parTable [] users input 1 0 [word]) input.length=some (some 0) := by
  decide +kernel

set_option maxRecDepth 4000 in
/-- The installed target row accepts a physical prefix which its fixed
source argument cannot produce. No target grammar is boundedly evaluated. -/
theorem target_execution :
    valAt (seqTable [] users input 1 (address [] users 0 (profile (machine users) word)) [word]) 6=some (some 0) := by
  have he := rows [] (by simp [RegularCaptureProduct.Valid]) users users_valid input 1 0
    ⟨.lit ['Z'],"ab".toList,.seq (.lit ['#']) (.param 0)⟩ (by rfl) word input.length 6
    (by decide) (by decide) (by decide)
  exact he.symm.trans source_execution.2

/-- Starting the tail observer before processing the captured word gives
the wrong answer: three total b's become two tail b's. -/
theorem observer_handoff :
    filtered observer input 0 1 input.length (some (some 0))=some (some 0) ∧
    filtered observer input (run observer 0 word) 1 6 (some (some 0))=some (some 0) ∧
    filtered observer input 0 1 6 (some (some 0))=some none := by
  decide +kernel

end Examples

end Shallot.MacroPeg.CBV.CapturePrefixRows
