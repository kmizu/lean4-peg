import MacroPeg.CBV.CaptureActionSafety
import MacroPeg.CBV.DependentCaptureFilter

namespace Shallot.MacroPeg.CBV.DynamicScannerCapture
open ClockFreezing (Table)

/-- A missing scanner transition is an absorbing state in the capture
observer. It does not stop observation of the remaining captured word. -/
def encode {n : Nat} : Option (Fin n) → Nat
  | none => n
  | some q => q.val

def observer {n : Nat} (M : StatefulScanner.Machine n) : RegularCaptureProduct.Machine :=
  ⟨n+1, fun q c => if h : q<n then encode (StatefulScanner.next (M.arcs ⟨q,h⟩) c) else n⟩

theorem encode_bound {n : Nat} (q : Option (Fin n)) : encode q<n+1 := by
  cases q with
  | none => exact Nat.lt_succ_self n
  | some q => exact Nat.lt_succ_of_lt q.isLt

theorem observer_valid {n : Nat} (M : StatefulScanner.Machine n) : (observer M).Valid := by
  refine ⟨by simp [observer], fun q _ c => ?_⟩
  dsimp [observer]
  split
  · exact encode_bound _
  · omega

theorem observer_step {n : Nat} (M : StatefulScanner.Machine n)
    (q : Option (Fin n)) (c : Char) :
    (observer M).step (encode q) c =
      encode (q.bind (fun t => StatefulScanner.next (M.arcs t) c)) := by
  cases q with
  | none => simp [observer,encode]
  | some q => simp [observer,encode,q.isLt]

theorem observer_run {n : Nat} (M : StatefulScanner.Machine n)
    (w : List Char) (q : Option (Fin n)) :
    RegularCaptureProduct.run (observer M) (encode q) w =
      encode (q.bind (fun t => StatefulScanner.advance M t w)) := by
  induction w generalizing q with
  | nil => cases q <;> rfl
  | cons c w ih =>
    change RegularCaptureProduct.run (observer M) ((observer M).step (encode q) c) w = _
    rw [observer_step,ih]
    cases q with
    | none => rfl
    | some q => simp [StatefulScanner.advance]

theorem encode_injective {n : Nat} (a b : Option (Fin n))
    (h : encode a=encode b) : a=b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => have hb := b.isLt; simp [encode] at h; omega
  | some a => cases b with
    | none => have ha := a.isLt; simp [encode] at h; omega
    | some b => exact congrArg some (Fin.ext h)

/-- Exact observation of a partial scanner transition, including failure,
using the existing total finite-state capture filters. -/
theorem observer_result {n : Nat} (M : StatefulScanner.Machine n)
    (w : List Char) (q : Fin n) (r : Option (Fin n)) :
    RegularCaptureProduct.run (observer M) q.val w=encode r ↔
      StatefulScanner.advance M q w=r := by
  change RegularCaptureProduct.run (observer M) (encode (some q)) w=encode r ↔ _
  rw [observer_run]
  exact ⟨encode_injective _ _, congrArg encode⟩

/-- One observer profile determines the partial transition from every
scanner state, so it remains sufficient when a retained value is reused. -/
theorem profile_determines_action {n : Nat} (M : StatefulScanner.Machine n)
    (u v : List Char)
    (h : CaptureTransitionProfile.profile (observer M) u=
      CaptureTransitionProfile.profile (observer M) v) :
    CaptureActionSafety.action M u=CaptureActionSafety.action M v := by
  funext q
  apply encode_injective
  change encode ((some q).bind (fun t => StatefulScanner.advance M t u)) =
    encode ((some q).bind (fun t => StatefulScanner.advance M t v))
  rw [←observer_run,←observer_run]
  have hr := congrArg (fun P : List Nat => P[q.val]?) h
  rw [CaptureTransitionProfile.profile_get _ _ _ (by exact Nat.lt_succ_of_lt q.isLt),
    CaptureTransitionProfile.profile_get _ _ _ (by exact Nat.lt_succ_of_lt q.isLt)] at hr
  exact Option.some.inj hr

theorem finite_action_cover {n : Nat} (M : StatefulScanner.Machine n) (w : List Char) :
    ∃ P∈CaptureTransitionProfile.profiles (observer M),
      ∀ v, CaptureTransitionProfile.profile (observer M) v=P →
        CaptureActionSafety.action M v=CaptureActionSafety.action M w := by
  exact ⟨_,CaptureTransitionProfile.profile_mem _ (observer_valid M) w,
    fun _ hv => profile_determines_action M _ _ hv⟩

open RegularCaptureProduct (Node grammar choice)
open DependentCaptureFilter (render filter table)

/-- The filter follows the actual prioritized argument, including arbitrary
stars and recursive nullary helpers, rather than guessing a capture action. -/
theorem filter_result {n : Nat} (M : StatefulScanner.Machine n)
    (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (x : List Char) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p : Nat) (hp : p≤x.length) (q : Fin n) (r : Option (Fin n)) :
    evV (grammar nodes (observer M)) x .callByValueSeq (table nodes (observer M) x)
      E (filter nodes (observer M) S a q.val (encode r)) p =
    match evV (grammar nodes (observer M)) x .callByValuePar
        (tblV (grammar nodes (observer M)) x .callByValuePar
          (iterBoundV (grammar nodes (observer M)) x)) E (render a) p with
    | some (some j) => if StatefulScanner.advance M q (pre x p j)=r then some (some j) else some none
    | other => other := by
  rw [DependentCaptureFilter.correct_par nodes hNodes (observer M) (observer_valid M)
    x S E hS a ha p hp q.val (encode r) (by exact Nat.lt_succ_of_lt q.isLt) (encode_bound r)]
  cases evV (grammar nodes (observer M)) x .callByValuePar
    (tblV (grammar nodes (observer M)) x .callByValuePar
      (iterBoundV (grammar nodes (observer M)) x)) E (render a) p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some j => simp only [RegularCaptureProduct.filtered,observer_result]

theorem filter_success {n : Nat} (M : StatefulScanner.Machine n)
    (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (x : List Char) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p j : Nat) (hp : p≤x.length) (q : Fin n) (r : Option (Fin n))
    (hf : evV (grammar nodes (observer M)) x .callByValueSeq (table nodes (observer M) x)
      E (filter nodes (observer M) S a q.val (encode r)) p=some (some j)) :
    evV (grammar nodes (observer M)) x .callByValuePar
        (tblV (grammar nodes (observer M)) x .callByValuePar
          (iterBoundV (grammar nodes (observer M)) x)) E (render a) p=some (some j) ∧
    StatefulScanner.advance M q (pre x p j)=r := by
  rw [filter_result M nodes hNodes x S E hS a ha p hp q r] at hf
  cases hv : evV (grammar nodes (observer M)) x .callByValuePar
    (tblV (grammar nodes (observer M)) x .callByValuePar
      (iterBoundV (grammar nodes (observer M)) x)) E (render a) p with
  | none => simp only [hv] at hf; cases hf
  | some v => cases v with
    | none => simp only [hv] at hf; cases hf
    | some k =>
      simp only [hv] at hf
      split at hf
      · rename_i he
        have hk : k=j := Option.some.inj (Option.some.inj hf)
        subst k
        exact ⟨rfl,he⟩
      · cases hf

/-- A successful generated filter derives the exact residual scan from the
actual Par capture. The whole captured prefix remains pre x p j. -/
theorem filter_resumption {n : Nat} (M : StatefulScanner.Machine n)
    (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (x : List Char) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (observer M) S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p j : Nat) (hp : p≤x.length) (q r : Fin n)
    (hf : evV (grammar nodes (observer M)) x .callByValueSeq (table nodes (observer M) x)
      E (filter nodes (observer M) S a q.val r.val) p=some (some j)) :
    sfx x p=pre x p j++sfx x j ∧
    StatefulScanner.run M q (sfx x p)=StatefulScanner.run M r (sfx x j) := by
  obtain ⟨hv,ht⟩ := filter_success M nodes hNodes x S E hS a ha p j hp q (some r) hf
  have hs := DependentCaptureFilter.success_prefix (by decide : Strategy.callByValuePar≠.callByName)
    (tblV_sound (RegularCaptureProduct.grammar_firstOrder nodes (observer M)) (by decide) _)
    E (render a) (DependentCaptureFilter.render_firstOrder a) p j hp hv
  refine ⟨hs.2,?_⟩
  rw [hs.2]
  exact StatefulScanner.run_after_prefix M _ _ q r ht

/-- State-indexed continuations can reject or diverge; enumeration must not
then retry a different successful parse of the original argument. -/
def dispatch (nodes : List Node) (D : RegularCaptureProduct.Machine)
    (S : List (List Nat)) (a : DependentCaptureFilter.Expr) (q : Nat) (K : Nat → MExp) : MExp :=
  choice ((List.range D.width).map (fun r => .seq (filter nodes D S a q r) (K r)))

theorem dispatch_firstOrder (nodes : List Node) (D : RegularCaptureProduct.Machine)
    (S : List (List Nat)) (a : DependentCaptureFilter.Expr) (q : Nat) (K : Nat → MExp)
    (hK : ∀ r, (K r).FirstOrder) : (dispatch nodes D S a q K).FirstOrder := by
  apply RegularCaptureProduct.choice_firstOrder
  intro e he
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp he
  exact ⟨DependentCaptureFilter.filter_firstOrder nodes D S a q r,hK r⟩

theorem dispatch_success (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : RegularCaptureProduct.Machine) (hD : D.Valid) (x : List Char)
    (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate D S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p j q : Nat) (hp : p≤x.length) (hq : q<D.width) (K : Nat → MExp)
    (hv : evV (grammar nodes D) x .callByValuePar
      (tblV (grammar nodes D) x .callByValuePar (iterBoundV (grammar nodes D) x))
      E (render a) p=some (some j)) :
    evV (grammar nodes D) x .callByValueSeq (table nodes D x) E
      (dispatch nodes D S a q K) p =
    evV (grammar nodes D) x .callByValueSeq (table nodes D x) E
      (K (RegularCaptureProduct.run D q (pre x p j))) j := by
  let reached := RegularCaptureProduct.run D q (pre x p j)
  have hr : reached∈List.range D.width := List.mem_range.mpr (RegularCaptureProduct.run_bound hD q hq _)
  unfold dispatch
  rw [RegularCaptureProduct.choice_eval_unique (grammar nodes D) x .callByValueSeq
    (table nodes D x) E p (chosen:=reached)
    (v:=evV (grammar nodes D) x .callByValueSeq (table nodes D x) E (K reached) j)
    (R:=fun r => .seq (filter nodes D S a q r) (K r)) _ (fun r hm => ?_)]
  · simp only [hr,ite_true]; rfl
  · have hf := DependentCaptureFilter.correct_par nodes hNodes D hD x S E hS a ha p hp q r hq
      (List.mem_range.mp hm)
    rw [hv] at hf
    simp only [RegularCaptureProduct.filtered] at hf
    by_cases he : r=reached
    · subst r
      simp only [show RegularCaptureProduct.run D q (pre x p j)=reached from rfl,ite_true] at hf
      simp only [ite_true]
      exact evV_seq_ok hf
    · have hn : reached≠r := Ne.symm he
      simp only [show RegularCaptureProduct.run D q (pre x p j)=reached from rfl,hn,ite_false] at hf
      rw [evV_seq_fail hf]
      simp only [he,ite_false]

private theorem choice_failure (g : MGrammar) (x : List Char) (T : Table)
    (E : List (List Char)) (p : Nat) (R : Nat → MExp) : ∀ states : List Nat,
    (∀ r∈states, evV g x .callByValueSeq T E (R r) p=some none) →
    evV g x .callByValueSeq T E (choice (states.map R)) p=some none
  | [], _ => rfl
  | r::rs, h => by
    simp only [List.map_cons,choice]
    rw [evV_alt_fail (h r (by simp))]
    exact choice_failure g x T E p R rs (fun t ht => h t (by simp [ht]))

/-- Complete partial-result dispatch: argument failure and undefinedness
precede every continuation; a chosen continuation never reselects a state. -/
theorem dispatch_result (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : RegularCaptureProduct.Machine) (hD : D.Valid) (x : List Char)
    (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate D S E)
    (a : DependentCaptureFilter.Expr) (ha : DependentCaptureFilter.Valid nodes a)
    (p q : Nat) (hp : p≤x.length) (hq : q<D.width) (K : Nat → MExp) :
    evV (grammar nodes D) x .callByValueSeq (table nodes D x) E
      (dispatch nodes D S a q K) p =
    match evV (grammar nodes D) x .callByValuePar
      (tblV (grammar nodes D) x .callByValuePar (iterBoundV (grammar nodes D) x)) E (render a) p with
    | some (some j) => evV (grammar nodes D) x .callByValueSeq (table nodes D x) E
        (K (RegularCaptureProduct.run D q (pre x p j))) j
    | other => other := by
  cases hv : evV (grammar nodes D) x .callByValuePar
    (tblV (grammar nodes D) x .callByValuePar (iterBoundV (grammar nodes D) x)) E (render a) p with
  | some v => cases v with
    | some j => exact dispatch_success nodes hNodes D hD x S E hS a ha p j q hp hq K hv
    | none =>
      apply choice_failure
      intro r hr
      have hf := DependentCaptureFilter.correct_par nodes hNodes D hD x S E hS a ha p hp q r hq
        (List.mem_range.mp hr)
      rw [hv] at hf
      exact evV_seq_fail hf
  | none =>
    have hne : List.range D.width≠[] := by
      intro hz
      have hl := congrArg List.length hz
      simp only [List.length_range,List.length_nil] at hl
      have := hD.1
      omega
    cases hs : List.range D.width with
    | nil => exact False.elim (hne hs)
    | cons r rs =>
      have hr : r<D.width := List.mem_range.mp (by rw [hs]; simp)
      have hf := DependentCaptureFilter.correct_par nodes hNodes D hD x S E hS a ha p hp q r hq hr
      rw [hv] at hf
      change evV _ _ _ _ _ (choice ((List.range D.width).map _)) _ = _
      rw [hs]
      simp only [List.map_cons,choice]
      exact evV_alt_none (evV_seq_none hf)

end Shallot.MacroPeg.CBV.DynamicScannerCapture
