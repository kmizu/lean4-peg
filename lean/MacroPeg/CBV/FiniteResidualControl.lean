import MacroPeg.CBV.CaptureObservability
import MacroPeg.CBV.RootObservation

namespace Shallot.MacroPeg.CBV.FiniteResidualControl

open CaptureObservability

def capturedPrefix (n : Nat) : List Char := List.replicate n 'a' ++ ['b']
def suffix (m : Nat) : List Char := List.replicate m 'c'

theorem prefix_dead (n m : Nat) : Unreplayable (suffix m) (capturedPrefix n) := by
  cases n with
  | zero => exact absent_head (by simp [suffix])
  | succ n =>
    apply absent_head
    simp [suffix]

private theorem no_embedding : ∀ K, ∀ f : Nat → Fin K,
    (∀ a b, f a = f b → a = b) → False
  | 0, f, _ => Fin.elim0 (f 0)
  | K + 1, f, hf => by
    have hne : ∀ n, (f (n + 1)).val ≠ (f 0).val := by
      intro n he
      have := hf (n + 1) 0 (Fin.ext he)
      omega
    let reduced : Nat → Fin K := fun n =>
      ⟨if (f (n + 1)).val < (f 0).val then (f (n + 1)).val else (f (n + 1)).val - 1, by
        have hb := (f (n + 1)).isLt
        have hzero := (f 0).isLt
        have hn := hne n
        split <;> omega⟩
    apply no_embedding K reduced
    intro a b he
    have hval := congrArg Fin.val he
    change (if (f (a + 1)).val < (f 0).val then (f (a + 1)).val else (f (a + 1)).val - 1) =
      (if (f (b + 1)).val < (f 0).val then (f (b + 1)).val else (f (b + 1)).val - 1) at hval
    have ha := hne a
    have hb := hne b
    have horig : f (a + 1) = f (b + 1) := by
      apply Fin.ext
      split at hval <;> split at hval <;> omega
    have := hf (a + 1) (b + 1) horig
    omega

/-- Even arbitrary finite control cannot repair the interface that enters
the suffix with only the original opaque captured prefix. The state may be
any function of that prefix; the theorem imposes no computability condition. -/
theorem no_finite_summary (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (K : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder) (state : Nat → Fin K) :
    ¬ ∀ n m, SObs g s (MExp.subst [MExp.lit (capturedPrefix n)] (body (state n)))
      (suffix m) (some []) ↔ n = m := by
  intro hspec
  apply no_embedding K state
  intro n k hstate
  have hstart := (hspec n n).mpr rfl
  have henv := dead_singletons_agree (prefix_dead n n) (prefix_dead k n)
  have hnext := (observations_iff hg hs henv (body (state n)) (hbody _) (some [])).mp hstart
  have haccept : SObs g s (MExp.subst [MExp.lit (capturedPrefix k)] (body (state k)))
      (suffix n) (some []) := by simpa only [hstate, List.map_cons, List.map_nil] using hnext
  exact ((hspec k n).mp haccept).symm

def balancedBody : MExp :=
  .alt (.seq (.chr 'a') (.seq (.call 0 []) (.chr 'c'))) (.chr 'b')

def balancedGrammar : MGrammar := ⟨[⟨0, balancedBody⟩]⟩

def balancedStart : MExp := .call 0 []

def consumePrefix : MExp := .seq (.star (.chr 'a')) (.chr 'b')

private theorem a_star (g : MGrammar) (s : Strategy) (m : Nat) : ∀ n,
    ∃ t, MDerives g s (.star (.chr 'a')) (capturedPrefix n ++ suffix m)
      (.ok t ('b' :: suffix m))
  | 0 => ⟨_, .starNil _ _ (.chrFail 'a' 'b' (suffix m) (by decide))⟩
  | n + 1 => by
    obtain ⟨t, ht⟩ := a_star g s m n
    exact ⟨_, .starCons _ _ _ _ _ _ (.chrOk 'a' 'a' _ (by decide)) ht⟩

theorem consume_prefix (g : MGrammar) (s : Strategy) (n m : Nat) :
    SObs g s consumePrefix (capturedPrefix n ++ suffix m) (some (suffix m)) := by
  obtain ⟨t, ht⟩ := a_star g s m n
  exact ⟨_, .seqOk _ _ _ _ _ _ _ ht (.chrOk 'b' 'b' _ (by decide)), rfl⟩

theorem balanced_firstOrder : balancedGrammar.FirstOrder := by
  intro r hr
  simp only [balancedGrammar, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst r
  trivial

private theorem wrap (s : Strategy) {input : List Char} {r : Option (List Char)}
    (h : SObs balancedGrammar s balancedBody input r) :
    SObs balancedGrammar s balancedStart input r := by
  obtain ⟨o, hd, ho⟩ := h
  have hb : MDerives balancedGrammar s (MExp.subst [] balancedBody) input o := by
    simpa [balancedBody, MExp.subst, MExp.substArgs] using hd
  have hc := call0_obs (g := balancedGrammar) (s := s) (i := 0) (r := ⟨0, balancedBody⟩)
    rfl rfl hb
  simpa only [ho, balancedStart] using hc

/-- The macro-free rule `B ← 'a' B 'c' / 'b'` has these exact observations
under every strategy. -/
theorem balanced_observation (s : Strategy) : ∀ n m,
    SObs balancedGrammar s balancedStart (capturedPrefix n ++ suffix m)
      (if n ≤ m then some (suffix (m - n)) else none)
  | 0, m => by
    apply wrap s
    apply RootObservation.alt_right
    · exact RootObservation.seq_fail ⟨_, .chrFail 'a' 'b' (suffix m) (by decide), rfl⟩
    · exact ⟨_, .chrOk 'b' 'b' (suffix m) (by decide), rfl⟩
  | n + 1, m => by
    have ha : SObs balancedGrammar s (.chr 'a') (capturedPrefix (n + 1) ++ suffix m)
        (some (capturedPrefix n ++ suffix m)) := by
      exact ⟨_, .chrOk 'a' 'a' _ (by decide), rfl⟩
    have hb : SObs balancedGrammar s (.chr 'b') (capturedPrefix (n + 1) ++ suffix m) none := by
      exact ⟨_, .chrFail 'b' 'a' _ (by decide), rfl⟩
    have hmid : SObs balancedGrammar s (.seq balancedStart (.chr 'c'))
        (capturedPrefix n ++ suffix m)
        (if n + 1 ≤ m then some (suffix (m - (n + 1))) else none) := by
      by_cases hle : n + 1 ≤ m
      · have hr : SObs balancedGrammar s balancedStart (capturedPrefix n ++ suffix m)
            (some (suffix (m - n))) := by
          simpa only [if_pos (show n ≤ m by omega)] using balanced_observation s n m
        have hc : SObs balancedGrammar s (.chr 'c') (suffix (m - n))
            (some (suffix (m - (n + 1)))) := by
          have he : m - n = (m - (n + 1)) + 1 := by omega
          rw [he]
          exact ⟨_, .chrOk 'c' 'c' _ (by decide), rfl⟩
        simpa only [if_pos hle] using RootObservation.seq_ok hr hc
      · by_cases hnm : n ≤ m
        · have he : m = n := by omega
          subst m
          have hr : SObs balancedGrammar s balancedStart (capturedPrefix n ++ suffix n) (some []) := by
            simpa [suffix] using balanced_observation s n n
          simpa only [if_neg hle] using RootObservation.seq_ok hr
            (show SObs balancedGrammar s (.chr 'c') [] none from ⟨_, .chrEmpty 'c', rfl⟩)
        · have hr : SObs balancedGrammar s balancedStart (capturedPrefix n ++ suffix m) none := by
            simpa only [if_neg hnm] using balanced_observation s n m
          simpa only [if_neg hle] using RootObservation.seq_fail (b := .chr 'c') hr
    have hlead := RootObservation.seq_ok ha hmid
    apply wrap s
    by_cases hle : n + 1 ≤ m
    · simp only [if_pos hle]
      apply RootObservation.alt_left
      simpa only [if_pos hle, balancedStart] using hlead
    · simp only [if_neg hle]
      apply RootObservation.alt_right
      · simpa only [if_neg hle, balancedStart] using hlead
      · exact hb

theorem balanced_recognizes (s : Strategy) (n m : Nat) :
    SObs balancedGrammar s balancedStart (capturedPrefix n ++ suffix m) (some []) ↔ n = m := by
  constructor
  · intro h
    have he := sObs_unique h (balanced_observation s n m)
    by_cases hle : n ≤ m
    · simp only [if_pos hle, Option.some.injEq] at he
      have hl := congrArg List.length he
      simp only [List.length_nil, suffix, List.length_replicate] at hl
      omega
    · simp only [if_neg hle] at he
      cases he
  · intro h
    subst m
    simpa [suffix] using balanced_observation s n n

/-- The obstruction already concerns whole-input acceptance, not only
preservation of the exact residual. The proposed front end must enter the
suffix with just a prefix-selected finite state and the captured literal;
an unbounded pending caller stack or suffix-dependent selection is excluded
by this interface, not by a claim about all Seq grammars. -/
theorem no_balanced_factorization (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (K : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder) (state : Nat → Fin K) :
    ¬ ∀ n m,
      SObs balancedGrammar .callByValuePar balancedStart (capturedPrefix n ++ suffix m) (some []) ↔
      SObs g s (MExp.subst [MExp.lit (capturedPrefix n)] (body (state n)))
        (suffix m) (some []) := by
  intro hspec
  apply no_finite_summary g hg s hs K body hbody state
  intro n m
  exact (hspec n m).symm.trans (balanced_recognizes .callByValuePar n m)

end Shallot.MacroPeg.CBV.FiniteResidualControl
