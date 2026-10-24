import MacroPeg.CBV.SequentialCallLookahead

/-! A capture-dependent forward search. Query identifiers have unbounded unary
length; record markers separate declarations from reference fields. -/
namespace Shallot.MacroPeg.CBV.ForwardQueryScan
open RootObservation

def identifier (n : Nat) : List Char := List.replicate n 'a' ++ ['b']
def header (n : Nat) : List Char := '[' :: identifier n ++ [']']

def key : MExp := SequentialCallLookahead.sequenceArgs [.lit ['['],.param 0,.lit [']']]
def closedKey (n : Nat) : MExp := MExp.subst [.lit (identifier n)] key
def seek (test : MExp) : MExp := .seq (.star (.seq (.notP test) .any)) test

private theorem strip_concat (u v input : List Char) :
    Shallot.stripPrefix? (u ++ v) input =
      (Shallot.stripPrefix? u input).bind (Shallot.stripPrefix? v) := by
  induction u generalizing input with
  | nil => rfl
  | cons c u ih =>
    cases input with
    | nil => rfl
    | cons d input =>
      simp only [List.cons_append,Shallot.stripPrefix?]
      split <;> simp_all

theorem literal_obs (g : MGrammar) (s : Strategy) (w x : List Char) :
    SObs g s (.lit w) x (Shallot.stripPrefix? w x) := by
  cases h : Shallot.stripPrefix? w x with
  | none => exact ⟨_,.litFail w x h,rfl⟩
  | some r => exact ⟨_,.litOk w x r h,rfl⟩

theorem literal_sequence (g : MGrammar) (s : Strategy) (words : List (List Char)) (x : List Char) :
    SObs g s (SequentialCallLookahead.sequenceArgs (words.map MExp.lit)) x
      (Shallot.stripPrefix? words.flatten x) := by
  induction words generalizing x with
  | nil => exact ⟨_,.eps x,rfl⟩
  | cons w ws ih =>
    simp only [List.map_cons,SequentialCallLookahead.sequenceArgs,List.flatten_cons,strip_concat]
    cases h : Shallot.stripPrefix? w x with
    | none => exact seq_fail ⟨_,.litFail w x h,rfl⟩
    | some rest => exact seq_ok ⟨_,.litOk w x rest h,rfl⟩ (ih rest)

theorem closedKey_obs (g : MGrammar) (s : Strategy) (n : Nat) (x : List Char) :
    SObs g s (closedKey n) x (Shallot.stripPrefix? (header n) x) := by
  simpa only [List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    List.cons_append,List.nil_append,header,closedKey,key,SequentialCallLookahead.sequenceArgs,MExp.subst,argAt]
    using literal_sequence g s [['['],identifier n,[']']] x

theorem strip_identifier (n m : Nat) (rest : List Char) :
    Shallot.stripPrefix? (identifier n) (identifier m ++ rest) = if n=m then some rest else none := by
  induction n generalizing m with
  | zero => cases m <;> simp [identifier,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]
  | succ n ih =>
    cases m with
    | zero => simp [identifier,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar]
    | succ m => simpa [identifier,List.replicate_succ,Shallot.stripPrefix?,Shallot.beqChar] using ih m

theorem strip_header (n m : Nat) (rest : List Char) :
    Shallot.stripPrefix? (header n) (header m ++ rest) = if n=m then some rest else none := by
  simp only [header,List.cons_append,Shallot.stripPrefix?,Shallot.beqChar,beq_self_eq_true,↓reduceIte]
  rw [List.append_assoc,strip_concat,strip_identifier]
  by_cases h : n=m <;> simp [h,Shallot.stripPrefix?,Shallot.beqChar]

private theorem fail_derivation {g : MGrammar} {s : Strategy} {e : MExp} {x : List Char}
    (h : SObs g s e x none) : MDerives g s e x .fail := by
  obtain ⟨o,hd,ho⟩ := h
  cases o with
  | fail => exact hd
  | ok _ _ => cases ho

theorem seek_here {g : MGrammar} {s : Strategy} {test : MExp} {x rest : List Char}
    (h : SObs g s test x (some rest)) : SObs g s (seek test) x (some rest) := by
  obtain ⟨o,hd,ho⟩ := h
  cases o with
  | fail => cases ho
  | ok t r =>
    cases ho
    exact ⟨_,.seqOk _ _ _ _ _ _ _
      (.starNil _ _ (.seqFail₁ _ _ _ (.notOk _ _ _ _ hd))) hd,rfl⟩

theorem seek_step {g : MGrammar} {s : Strategy} {test : MExp} {c : Char} {x : List Char}
    {result : Option (List Char)} (hfail : SObs g s test (c::x) none)
    (h : SObs g s (seek test) x result) : SObs g s (seek test) (c::x) result := by
  have hg : MDerives g s (.seq (.notP test) .any) (c::x) (.ok (.seq .notT (.leaf [c])) x) :=
    .seqOk _ _ _ _ _ _ _ (.notFail _ _ (fail_derivation hfail)) (.anyOk c x)
  obtain ⟨o,hd,ho⟩ := h
  cases hd with
  | seqOk _ _ _ mid final ts tk hs hk =>
    exact ⟨_,.seqOk _ _ _ _ _ _ _ (.starCons _ _ _ _ _ _ hg hs) hk,ho⟩
  | seqFail₁ _ _ _ hs => cases hs
  | seqFail₂ _ _ _ mid ts hs hk =>
    exact ⟨_,.seqFail₂ _ _ _ _ _ (.starCons _ _ _ _ _ _ hg hs) hk,ho⟩

theorem seek_empty (g : MGrammar) (s : Strategy) (n : Nat) :
    SObs g s (seek (closedKey n)) [] none := by
  have hk : SObs g s (closedKey n) [] none := closedKey_obs g s n []
  exact ⟨_,.seqFail₂ _ _ _ _ _
    (.starNil _ _ (.seqFail₂ _ _ _ _ _ (.notFail _ _ (fail_derivation hk)) (.anyFail)))
    (fail_derivation hk),rfl⟩

theorem key_fail_head (g : MGrammar) (s : Strategy) (n : Nat) (c : Char) (rest : List Char)
    (hc : c ≠ '[') : SObs g s (closedKey n) (c::rest) none := by
  have h := closedKey_obs g s n (c::rest)
  have hn : 91 ≠ c.toNat := fun he => hc (Char.toNat_inj.mp he.symm)
  simpa [header,Shallot.stripPrefix?,Shallot.beqChar,hn] using h

theorem seek_before {g : MGrammar} {s : Strategy} {n : Nat} {before rest : List Char}
    {result : Option (List Char)} (hc : '[' ∉ before)
    (h : SObs g s (seek (closedKey n)) rest result) :
    SObs g s (seek (closedKey n)) (before++rest) result := by
  induction before with
  | nil => exact h
  | cons c before ih =>
    have hn : c ≠ '[' := by intro he; subst c; exact hc (by simp)
    exact seek_step (key_fail_head g s n c (before++rest) hn) (ih (fun hm => hc (by simp [hm])))

theorem seek_header_here (g : MGrammar) (s : Strategy) (n : Nat) (rest : List Char) :
    SObs g s (seek (closedKey n)) (header n ++ rest) (some rest) :=
  seek_here (by simpa only [strip_header,ite_true] using closedKey_obs g s n (header n++rest))

theorem seek_header_skip {g : MGrammar} {s : Strategy} {n m : Nat} {payload rest : List Char}
    {result : Option (List Char)} (hn : n ≠ m) (hc : '[' ∉ payload)
    (h : SObs g s (seek (closedKey n)) rest result) :
    SObs g s (seek (closedKey n)) (header m ++ payload ++ rest) result := by
  have hk : SObs g s (closedKey n) (header m ++ payload ++ rest) none := by
    simpa only [List.append_assoc,strip_header,if_neg hn] using
      closedKey_obs g s n (header m ++ (payload++rest))
  apply seek_step hk
  apply seek_before (before := identifier m ++ [']'] ++ payload) _ h
  simp [identifier,hc]

end Shallot.MacroPeg.CBV.ForwardQueryScan
