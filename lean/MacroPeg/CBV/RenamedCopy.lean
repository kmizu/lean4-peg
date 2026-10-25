import MacroPeg.CBV.PrefixSpans
import MacroPeg.CBV.ParSimulation.Recognition
import MacroPeg.CBV.FiniteCaptureInterface

namespace Shallot.MacroPeg.CBV.RenamedCopy

open RootObservation PrefixCounters

def lower (b : Bool) : Char := if b then 'b' else 'a'
def upper (b : Bool) : Char := if b then 'B' else 'A'
def Language (x : List Char) : Prop :=
  ∃ w : List Bool, x = w.map lower ++ '#' :: w.map upper

def headIs : List Char → Char → Bool
  | [], _ => false
  | d :: _, c => Shallot.beqChar c d

def compatible (a b : List Char) : Bool :=
  (headIs a 'a' && headIs b 'A') || (headIs a 'b' && headIs b 'B')

def compare : List Char → List Char → Bool
  | [], _ => false
  | c :: cs, right => if c = '#' then right.isEmpty else
      match right with
      | [] => false
      | d :: ds => compatible (c :: cs) (d :: ds) && compare cs ds

def seek (x : List Char) : List Char → Bool
  | [] => false
  | c :: cs => if c = '#' then compare x cs else seek x cs

def pairTest (a b : MExp) : MExp :=
  .alt (.seq (atPosition a (.chr 'a')) (atPosition b (.chr 'A')))
    (.seq (atPosition a (.chr 'b')) (atPosition b (.chr 'B')))

def compareBody : MExp :=
  branch (atPosition (.param 0) (.chr '#')) (atEnd (.param 1))
    (.seq (pairTest (.param 0) (.param 1))
      (.call 0 [.seq (.param 0) .any, .seq (.param 1) .any]))

def seekBody : MExp :=
  branch (atPosition (.param 0) (.chr '#'))
    (.call 0 [.eps, .seq (.param 0) .any])
    (.call 1 [.seq (.param 0) .any])

def grammar : MGrammar := ⟨[⟨2, compareBody⟩, ⟨1, seekBody⟩]⟩
def start : MExp := .seq (.call 1 [.lit []]) (.star .any)

theorem grammar_firstOrder : grammar.FirstOrder := by
  intro r hr
  simp only [grammar, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;>
    simp [compareBody, seekBody, branch, pairTest, atPosition, atEnd,
      MExp.andP, MExp.FirstOrder, MExp.FirstOrderArgs]

theorem start_firstOrder : start.FirstOrder := by trivial

private theorem literal_prefix (g : MGrammar) (u rest : List Char) :
    MDerives g .callByValuePar (.lit u) (u ++ rest) (.ok (.leaf u) rest) :=
  .litOk _ _ _ ((CBVtoCBN.stripPrefix_exact _ _ _).mpr rfl)

private theorem literal_args (g : MGrammar) (x u v left right : List Char)
    (hu : x = u ++ left) (hv : x = v ++ right) :
    DerivesArgsPar g .callByValuePar x [.lit u, .lit v] [.lit u, .lit v] := by
  exact .cons _ _ _ _ _ _ _ (by rw [hu]; exact literal_prefix g u left) hu
    (.cons _ _ _ _ _ _ _ (by rw [hv]; exact literal_prefix g v right) hv (.nil x))

private theorem query_char (g : MGrammar) (u rest : List Char) (c : Char) :
    Test g .callByValuePar (atPosition (.lit u) (.chr c)) (u ++ rest) (headIs rest c) := by
  have hl : SObs g .callByValuePar (.lit u) (u ++ rest) (some rest) :=
    ⟨_, literal_prefix g u rest, rfl⟩
  cases rest with
  | nil => exact peek_failure (seq_ok hl ⟨_, .chrEmpty c, rfl⟩)
  | cons d ds =>
    cases he : Shallot.beqChar c d with
    | true => simpa only [headIs, he, atPosition] using peek_success (seq_ok hl ⟨_, .chrOk c d ds he, rfl⟩)
    | false => simpa only [headIs, he, atPosition] using peek_failure (seq_ok hl ⟨_, .chrFail c d ds he, rfl⟩)

private theorem query_end (g : MGrammar) (u rest : List Char) :
    Test g .callByValuePar (atEnd (.lit u)) (u ++ rest) rest.isEmpty := by
  have hl : SObs g .callByValuePar (.lit u) (u ++ rest) (some rest) :=
    ⟨_, literal_prefix g u rest, rfl⟩
  cases rest with
  | nil => exact peek_success (seq_ok hl (not_fail ⟨_, .anyFail, rfl⟩))
  | cons d ds => exact peek_failure (seq_ok hl (not_ok ⟨_, .anyOk d ds, rfl⟩))

private theorem query_pair (g : MGrammar) (x u v left right : List Char)
    (hu : x = u ++ left) (hv : x = v ++ right) :
    Test g .callByValuePar (pairTest (.lit u) (.lit v)) x (compatible left right) := by
  have qa := query_char g u left 'a'
  have qb := query_char g u left 'b'
  have qA := query_char g v right 'A'
  have qB := query_char g v right 'B'
  rw [← hu] at qa qb
  rw [← hv] at qA qB
  exact test_alt (test_seq qa qA) (test_seq qb qB)

private theorem grow (g : MGrammar) (u : List Char) (c : Char) (rest : List Char) :
    ∃ t, MDerives g .callByValuePar (.seq (.lit u) .any)
      (u ++ c :: rest) (.ok t rest) :=
  ⟨_, .seqOk _ _ _ _ _ _ _ (literal_prefix g u (c :: rest)) (.anyOk c rest)⟩

/-- Both actual prefix values grow while every recursive Par call stays at
the original input position. No value is recoded or inspected as a string. -/
theorem compare_test (x : List Char) : ∀ left right u v,
    x = u ++ left → x = v ++ right →
    Test grammar .callByValuePar (.call 0 [.lit u, .lit v]) x (compare left right) := by
  intro left
  induction left with
  | nil =>
    intro right u v hu hv
    apply par_call (by rfl) rfl (literal_args grammar x u v [] right hu hv)
    change SObs grammar .callByValuePar
      (branch (atPosition (.lit u) (.chr '#')) (atEnd (.lit v))
        (.seq (pairTest (.lit u) (.lit v))
          (.call 0 [.seq (.lit u) .any, .seq (.lit v) .any]))) x none
    have hq := query_char grammar u [] '#'
    rw [← hu] at hq
    apply branch_false hq
    have hp := query_pair grammar x u v [] right hu hv
    exact seq_fail hp
  | cons c cs ih =>
    intro right u v hu hv
    apply par_call (by rfl) rfl (literal_args grammar x u v (c :: cs) right hu hv)
    change SObs grammar .callByValuePar
      (branch (atPosition (.lit u) (.chr '#')) (atEnd (.lit v))
        (.seq (pairTest (.lit u) (.lit v))
          (.call 0 [.seq (.lit u) .any, .seq (.lit v) .any]))) x _
    have hq := query_char grammar u (c :: cs) '#'
    rw [← hu] at hq
    by_cases hc : c = '#'
    · subst c
      have hq' : Test grammar .callByValuePar (atPosition (.lit u) (.chr '#')) x true :=
        by simpa [headIs, Shallot.beqChar] using hq
      have he := query_end grammar v right
      rw [← hv] at he
      simpa only [compare, if_true] using branch_true hq' he
    · have hq' : Test grammar .callByValuePar (atPosition (.lit u) (.chr '#')) x false :=
        by
          have hne : '#'.toNat ≠ c.toNat := fun he => hc (Char.toNat_inj.mp he).symm
          simpa only [headIs, Shallot.beqChar, beq_eq_false_iff_ne.mpr hne] using hq
      apply branch_false hq'
      have hp := query_pair grammar x u v (c :: cs) right hu hv
      cases right with
      | nil =>
        have hp' : SObs grammar .callByValuePar (pairTest (.lit u) (.lit v)) x none :=
          by simpa [Test, compatible, headIs] using hp
        simpa [compare, hc] using seq_fail
          (b := .call 0 [.seq (.lit u) .any, .seq (.lit v) .any]) hp'
      | cons d ds =>
        cases he : compatible (c :: cs) (d :: ds) with
        | false =>
          rw [he] at hp
          simpa [compare, hc, he] using seq_fail
            (b := .call 0 [.seq (.lit u) .any, .seq (.lit v) .any]) hp
        | true =>
          rw [he] at hp
          obtain ⟨tu, hgu⟩ := grow grammar u c cs
          obtain ⟨tv, hgv⟩ := grow grammar v d ds
          rw [← hu] at hgu
          rw [← hv] at hgv
          have hu' : x = (u ++ [c]) ++ cs := by simpa [List.append_assoc] using hu
          have hv' : x = (v ++ [d]) ++ ds := by simpa [List.append_assoc] using hv
          have args : DerivesArgsPar grammar .callByValuePar x
              [.seq (.lit u) .any, .seq (.lit v) .any]
              [.lit (u ++ [c]), .lit (v ++ [d])] :=
            .cons _ _ _ _ _ _ _ hgu hu'
              (.cons _ _ _ _ _ _ _ hgv hv' (.nil x))
          have hn := ih ds (u ++ [c]) (v ++ [d]) hu' hv'
          have hb := (par_call_iff (i := 0) (by rfl) rfl
            (literal_args grammar x (u ++ [c]) (v ++ [d]) cs ds hu' hv') _).mp hn
          have hn' := par_call (i := 0) (by rfl) rfl args hb
          simpa [compare, hc, he] using seq_ok hp hn'

theorem seek_test (x : List Char) : ∀ rest v, x = v ++ rest →
    Test grammar .callByValuePar (.call 1 [.lit v]) x (seek x rest) := by
  intro rest
  induction rest with
  | nil =>
    intro v hv
    have args : DerivesArgsPar grammar .callByValuePar x [.lit v] [.lit v] :=
      .cons _ _ _ _ _ _ _ (by rw [hv]; exact literal_prefix grammar v []) hv (.nil x)
    apply par_call (i := 1) (by rfl) rfl args
    change SObs grammar .callByValuePar
      (branch (atPosition (.lit v) (.chr '#'))
        (.call 0 [.eps, .seq (.lit v) .any]) (.call 1 [.seq (.lit v) .any])) x none
    have hq := query_char grammar v [] '#'
    rw [← hv] at hq
    apply branch_false hq
    exact ⟨_, .callParArgFail 1 [] _ [] _ x [] rfl rfl rfl (.nil x)
      (.seqFail₂ _ _ _ [] _ (by rw [hv]; exact literal_prefix grammar v []) .anyFail), rfl⟩
  | cons c cs ih =>
    intro v hv
    have args : DerivesArgsPar grammar .callByValuePar x [.lit v] [.lit v] :=
      .cons _ _ _ _ _ _ _ (by rw [hv]; exact literal_prefix grammar v (c :: cs)) hv (.nil x)
    apply par_call (i := 1) (by rfl) rfl args
    change SObs grammar .callByValuePar
      (branch (atPosition (.lit v) (.chr '#'))
        (.call 0 [.eps, .seq (.lit v) .any]) (.call 1 [.seq (.lit v) .any])) x _
    have hq := query_char grammar v (c :: cs) '#'
    rw [← hv] at hq
    obtain ⟨t, hgv⟩ := grow grammar v c cs
    rw [← hv] at hgv
    have hv' : x = (v ++ [c]) ++ cs := by simpa [List.append_assoc] using hv
    by_cases hc : c = '#'
    · subst c
      have hq' : Test grammar .callByValuePar (atPosition (.lit v) (.chr '#')) x true :=
        by simpa [headIs, Shallot.beqChar] using hq
      have captured : DerivesArgsPar grammar .callByValuePar x
          [.eps, .seq (.lit v) .any] [.lit [], .lit (v ++ ['#'])] :=
        .cons _ _ _ [] x _ _ (.eps x) rfl
          (.cons _ _ _ _ _ _ _ hgv hv' (.nil x))
      have hn := compare_test x x cs [] (v ++ ['#']) (by simp) hv'
      have hb := (par_call_iff (i := 0) (by rfl) rfl
        (literal_args grammar x [] (v ++ ['#']) x cs (by simp) hv') _).mp hn
      have hn' := par_call (i := 0) (by rfl) rfl captured hb
      simpa [seek] using branch_true hq' hn'
    · have hq' : Test grammar .callByValuePar (atPosition (.lit v) (.chr '#')) x false := by
        have hne : '#'.toNat ≠ c.toNat := fun he => hc (Char.toNat_inj.mp he).symm
        simpa only [headIs, Shallot.beqChar, beq_eq_false_iff_ne.mpr hne] using hq
      have captured : DerivesArgsPar grammar .callByValuePar x
          [.seq (.lit v) .any] [.lit (v ++ [c])] :=
        .cons _ _ _ _ _ _ _ hgv hv' (.nil x)
      have literals : DerivesArgsPar grammar .callByValuePar x
          [.lit (v ++ [c])] [.lit (v ++ [c])] :=
        .cons _ _ _ _ _ _ _ (by rw [hv']; exact literal_prefix grammar (v ++ [c]) cs)
          hv' (.nil x)
      have hn := ih (v ++ [c]) hv'
      have hb := (par_call_iff (i := 1) (by rfl) rfl literals _).mp hn
      have hn' := par_call (i := 1) (by rfl) rfl captured hb
      simpa [seek, hc] using branch_false hq' hn'

/-- The complete root has a finite success or failure on every original
character list, including malformed inputs and a missing separator. -/
theorem start_observation (x : List Char) :
    SObs grammar .callByValuePar start x (if seek x x then some [] else none) := by
  have h := seek_test x x [] (by simp)
  cases he : seek x x with
  | false => rw [he] at h; exact seq_fail h
  | true =>
    rw [he] at h
    obtain ⟨t, ht⟩ := ParSimulation.star_any_derives grammar .callByValuePar x
    exact seq_ok h ⟨_, ht, rfl⟩

theorem start_accepts_iff (x : List Char) :
    SObs grammar .callByValuePar start x (some []) ↔ seek x x = true := by
  rw [unique_iff (start_observation x)]
  cases seek x x <;> simp

private theorem char_beq (a b : Char) : Shallot.beqChar a b = (b == a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Shallot.beqChar, beq_iff_eq, Char.toNat_inj]
  exact eq_comm

theorem compare_encoded (w : List Bool) (tail right : List Char) :
    compare (w.map lower ++ '#' :: tail) right = (right == w.map upper) := by
  induction w generalizing right with
  | nil => cases right <;> simp [compare]
  | cons b w ih =>
    cases right with
    | nil => cases b <;> simp [lower, upper, compare]
    | cons c right =>
      cases b <;>
        simp [lower, upper, compare, compatible, headIs, char_beq, ih,
          List.cons_beq_cons]

theorem seek_encoded (x : List Char) (w : List Bool) (tail : List Char) :
    seek x (w.map lower ++ '#' :: tail) = compare x tail := by
  induction w with
  | nil => simp [seek]
  | cons b w ih => cases b <;> simpa [lower, seek] using ih

private theorem compatible_cases (c d : Char) (cs ds : List Char)
    (h : compatible (c :: cs) (d :: ds) = true) :
    (c = 'a' ∧ d = 'A') ∨ (c = 'b' ∧ d = 'B') := by
  have h' : (Shallot.beqChar 'a' c = true ∧ Shallot.beqChar 'A' d = true) ∨
      (Shallot.beqChar 'b' c = true ∧ Shallot.beqChar 'B' d = true) := by
    simpa only [compatible, headIs, Bool.or_eq_true, Bool.and_eq_true] using h
  have charEq {a b : Char} (h : Shallot.beqChar a b = true) : b = a := by
    exact (Char.toNat_inj.mp (beq_iff_eq.mp h)).symm
  exact h'.imp (fun h => ⟨charEq h.1, charEq h.2⟩) (fun h => ⟨charEq h.1, charEq h.2⟩)

theorem compare_shape : ∀ left right, compare left right = true →
    ∃ w : List Bool, ∃ tail, left = w.map lower ++ '#' :: tail := by
  intro left
  induction left with
  | nil => intro right h; simp [compare] at h
  | cons c cs ih =>
    intro right h
    by_cases hc : c = '#'
    · exact ⟨[], cs, by simp [hc]⟩
    · cases right with
      | nil => simp [compare, hc] at h
      | cons d ds =>
        have hh := Bool.and_eq_true_iff.mp (by simpa [compare, hc] using h)
        obtain ⟨w, tail, hw⟩ := ih ds hh.2
        rcases compatible_cases c d cs ds hh.1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact ⟨false :: w, tail, by simp [lower, hw]⟩
        · exact ⟨true :: w, tail, by simp [lower, hw]⟩

private theorem seek_compare (x : List Char) : ∀ rest, seek x rest = true →
    ∃ right, compare x right = true := by
  intro rest
  induction rest with
  | nil => intro h; simp [seek] at h
  | cons c cs ih =>
    intro h
    by_cases hc : c = '#'
    · exact ⟨cs, by simpa [seek, hc] using h⟩
    · exact ih (by simpa [seek, hc] using h)

theorem seek_iff_language (x : List Char) : seek x x = true ↔ Language x := by
  constructor
  · intro h
    obtain ⟨right, hr⟩ := seek_compare x x h
    obtain ⟨w, tail, hx⟩ := compare_shape x right hr
    have he : tail = w.map upper := by
      have hh := h
      conv at hh => lhs; arg 2; rw [hx]
      rw [seek_encoded, hx, compare_encoded, beq_iff_eq] at hh
      exact hh
    exact ⟨w, by simpa [he] using hx⟩
  · rintro ⟨w, rfl⟩
    rw [seek_encoded, compare_encoded]
    simp

theorem recognizes (x : List Char) :
    SObs grammar .callByValuePar start x (some []) ↔ Language x :=
  (start_accepts_iff x).trans (seek_iff_language x)

/-- Every length and every left word, against arbitrary right-hand input. -/
theorem recognizes_slice (w : List Bool) (right : List Char) :
    SObs grammar .callByValuePar start (w.map lower ++ '#' :: right) (some []) ↔
      right = w.map upper := by
  rw [start_accepts_iff, seek_encoded, compare_encoded, beq_iff_eq]

theorem unary_slice (n m : Nat) :
    SObs grammar .callByValuePar start
      (List.replicate n 'a' ++ '#' :: List.replicate m 'A') (some []) ↔ n = m := by
  have hh := recognizes_slice (List.replicate n false) (List.replicate m 'A')
  simp only [List.map_replicate, lower, upper, Bool.false_eq_true, if_false] at hh
  rw [hh]
  constructor
  · intro h
    have hl := congrArg List.length h
    simpa only [List.length_replicate] using hl.symm
  · intro h; rw [h]

/-- Values made only of the consumed left field and its separator cannot
replay anywhere in the right field, even when values are split or copied. -/
theorem old_values_dead (E : List (List Char))
    (h : ∀ w ∈ E, ∀ c ∈ w, c = 'a' ∨ c = 'b' ∨ c = '#')
    (m : Nat) (w : List Char) (hw : w ∈ E) (hne : w ≠ []) :
    CaptureObservability.Unreplayable (List.replicate m 'A') w := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons c cs =>
    apply CaptureObservability.absent_head
    rcases h _ hw c (by simp) with rfl | rfl | rfl <;> simp

/-- This excludes a flattened boundary interface for this actual candidate;
it does not exclude an arbitrary Seq grammar with pending caller frames. -/
theorem no_flat_interface (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (K R : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (state : List Bool → Fin K) (capture : List Bool → List (List Char))
    (hlen : ∀ w, (capture w).length ≤ R)
    (halphabet : ∀ w u, u ∈ capture w → ∀ c ∈ u, c = 'a' ∨ c = 'b' ∨ c = '#') :
    ¬ ∀ w right,
      SObs grammar .callByValuePar start (w.map lower ++ '#' :: right) (some []) ↔
      SObs g s (MExp.subst ((capture w).map MExp.lit) (body (state w))) right (some []) := by
  intro hspec
  apply FiniteCaptureInterface.no_bounded_dead_equality g hg s hs K R body hbody
    (fun m => List.replicate m 'A')
    (fun n => state (List.replicate n false)) (fun n => capture (List.replicate n false))
    (fun n => hlen _)
    (fun n m => old_values_dead _ (halphabet _) m)
  intro n m
  have hh := hspec (List.replicate n false) (List.replicate m 'A')
  simp only [List.map_replicate, lower, Bool.false_eq_true, if_false] at hh
  exact hh.symm.trans (unary_slice n m)

end Shallot.MacroPeg.CBV.RenamedCopy
