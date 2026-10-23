import MacroPeg.CBV.PrefixSpans

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation
open CBVtoCBN (spanSlice spanSlice_length spanSlice_cons)

def intervalExpr (self equal : Nat) (alphabet : List Char) (p q t u : MExp) : MExp :=
  branch (.call equal [p, q]) (.call equal [t, u])
    (branch (.call equal [t, u]) MExp.failAlways
      (.seq (sameCharacter alphabet p t) (.call self [.seq p .any, q, .seq t .any, u])))

def intervalBody (self equal : Nat) (alphabet : List Char) : MExp :=
  intervalExpr self equal alphabet (.param 0) (.param 1) (.param 2) (.param 3)

theorem intervalBody_firstOrder (self equal : Nat) (alphabet : List Char) :
    (intervalBody self equal alphabet).FirstOrder := by
  have hc : (sameCharacter alphabet (.param 0) (.param 2)).FirstOrder := by
    apply alternatives_firstOrder
    intro e he
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
    exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  exact ⟨⟨⟨trivial, trivial, trivial⟩, trivial, trivial, trivial⟩,
    ⟨⟨trivial, trivial, trivial⟩,
      ⟨⟨⟨trivial, trivial, trivial⟩, trivial⟩,
        ⟨⟨trivial, trivial, trivial⟩, hc,
          ⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial⟩⟩⟩⟩

theorem sameCharacter_subst (args : List MExp) (alphabet : List Char) (a b : MExp) :
    MExp.subst args (sameCharacter alphabet a b) =
      sameCharacter alphabet (MExp.subst args a) (MExp.subst args b) := by
  simp [sameCharacter, alternatives_subst, List.map_map, atPosition,
    MExp.andP, MExp.subst, Function.comp_def]

theorem intervalBody_subst (self equal : Nat) (alphabet : List Char) (p q t u : MExp) :
    MExp.subst [p, q, t, u] (intervalBody self equal alphabet) =
      intervalExpr self equal alphabet p q t u := by
  simp [intervalBody, intervalExpr, branch, MExp.subst, MExp.substArgs,
    sameCharacter_subst, argAt, MExp.failAlways]

/-- The Par interval test compares arbitrary original-input substrings,
using only root prefixes as stored values. Every bounded case terminates. -/
theorem interval_body_obs {g : MGrammar} {self equal : Nat} {alphabet : List Char}
    (hr : ruleAtM g.rules self = some ⟨4, intervalBody self equal alphabet⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (hcover : ∀ c ∈ x, c ∈ alphabet) :
    ∀ p q t u, p ≤ q → q ≤ x.length → t ≤ u → u ≤ x.length →
      SObs g .callByValuePar
        (MExp.subst [.lit (x.take p), .lit (x.take q), .lit (x.take t), .lit (x.take u)]
          (intervalBody self equal alphabet)) x
        (if spanSlice x p q = spanSlice x t u then some x else none) := by
  have aux : ∀ d p q t u, q - p = d → p ≤ q → q ≤ x.length → t ≤ u → u ≤ x.length →
      SObs g .callByValuePar
        (MExp.subst [.lit (x.take p), .lit (x.take q), .lit (x.take t), .lit (x.take u)]
          (intervalBody self equal alphabet)) x
        (if spanSlice x p q = spanSlice x t u then some x else none) := by
    intro d
    induction d with
    | zero =>
      intro p q t u hd hp hq ht hu
      have hpq : p = q := by omega
      rw [intervalBody_subst]
      unfold intervalExpr
      have hEq := equal_obs he x p q (by omega) hq
      simp only [if_pos hpq] at hEq
      apply (branch_true_iff hEq _).2
      have hTarget := equal_obs he x t u (by omega) hu
      have hSlices : spanSlice x p q = spanSlice x t u ↔ t = u := by
        rw [hpq]
        have hl := spanSlice_length x t u ht hu
        simp only [spanSlice, Nat.sub_self, List.take_zero] at *
        constructor
        · intro heq
          rw [← heq] at hl
          simp only [List.length_nil] at hl
          omega
        · intro heq
          simp [heq]
      simpa only [equalCall, hSlices] using hTarget
    | succ d ih =>
      intro p q t u hd hp hq ht hu
      have hpq : p ≠ q := by omega
      rw [intervalBody_subst]
      unfold intervalExpr
      have hEq := equal_obs he x p q (by omega) hq
      simp only [if_neg hpq] at hEq
      apply (branch_false_iff hEq _).2
      have hTarget := equal_obs he x t u (by omega) hu
      by_cases htu : t = u
      · simp only [if_pos htu] at hTarget
        apply (branch_true_iff hTarget _).2
        have hNe : spanSlice x p q ≠ spanSlice x t u := by
          intro hs
          have hl := spanSlice_length x p q hp hq
          rw [hs] at hl
          simp [spanSlice, htu] at hl
          omega
        simp only [if_neg hNe]
        exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩
      · simp only [if_neg htu] at hTarget
        apply (branch_false_iff hTarget _).2
        have hpn : p < x.length := by omega
        have htn : t < x.length := by omega
        cases hP : x.drop p with
        | nil => have h := congrArg List.length hP; simp at h; omega
        | cons c cs =>
          cases hT : x.drop t with
          | nil => have h := congrArg List.length hT; simp at h; omega
          | cons e es =>
            have hChars : sameCharacterAt alphabet x p t = true ↔ c = e := by
              rw [sameCharacterAt_iff alphabet x p t hcover]
              simp [← List.head?_drop, hP, hT, eq_comm]
            have hCharTest := sameCharacter_test g alphabet x p t
            by_cases hce : c = e
            · have hYes := hChars.2 hce
              rw [hYes] at hCharTest
              have hGrowP := grow_obs g x p hpn
              have hGrowT := grow_obs g x t htn
              obtain ⟨tp, hp'⟩ := hGrowP
              obtain ⟨tt, ht'⟩ := hGrowT
              have hv : DerivesArgsPar g .callByValuePar x
                  [.seq (.lit (x.take p)) .any, .lit (x.take q),
                    .seq (.lit (x.take t)) .any, .lit (x.take u)]
                  [.lit (x.take (p + 1)), .lit (x.take q),
                    .lit (x.take (t + 1)), .lit (x.take u)] :=
                .cons _ _ _ _ _ _ _ hp' (prefix_eq x (p + 1))
                  (.cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x q) (prefix_eq x q)
                    (.cons _ _ _ _ _ _ _ ht' (prefix_eq x (t + 1))
                      (.cons _ _ _ _ _ _ _ (literal_take g .callByValuePar x u) (prefix_eq x u) (.nil x))))
              have hi := ih (p + 1) q (t + 1) u (by omega) (by omega) hq (by omega) hu
              have hc := par_call hr rfl hv hi
              have hsP := spanSlice_cons (q := q) (by omega) hP
              have hsT := spanSlice_cons (q := u) (by omega) hT
              have hSeq := seq_ok hCharTest hc
              simpa only [hsP, hsT, hce, List.cons.injEq, true_and] using hSeq
            · have hNo : sameCharacterAt alphabet x p t = false := by
                cases hh : sameCharacterAt alphabet x p t with
                | false => rfl
                | true => exact False.elim (hce (hChars.1 hh))
              rw [hNo] at hCharTest
              have hNe : spanSlice x p q ≠ spanSlice x t u := by
                rw [spanSlice_cons (q := q) (by omega) hP,
                  spanSlice_cons (q := u) (by omega) hT]
                intro hh
                exact hce (List.cons.inj hh).1
              simp only [if_neg hNe]
              exact seq_fail hCharTest
  intro p q t u hp hq ht hu
  exact aux (q - p) p q t u rfl hp hq ht hu

theorem interval_obs {g : MGrammar} {self equal : Nat} {alphabet : List Char}
    (hr : ruleAtM g.rules self = some ⟨4, intervalBody self equal alphabet⟩)
    (he : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (hcover : ∀ c ∈ x, c ∈ alphabet)
    (p q t u : Nat) (hp : p ≤ q) (hq : q ≤ x.length) (ht : t ≤ u) (hu : u ≤ x.length) :
    SObs g .callByValuePar
      (.call self [.lit (x.take p), .lit (x.take q), .lit (x.take t), .lit (x.take u)]) x
      (if spanSlice x p q = spanSlice x t u then some x else none) := by
  apply par_call hr rfl _ (interval_body_obs hr he x hcover p q t u hp hq ht hu)
  exact prefixValues_args g x [p, q, t, u]

/-- A fixed two-rule grammar compares counters and intervals over every
Lean character. Neither the rules nor the alphabet depend on the input. -/
def counterGrammar : MGrammar :=
  ⟨[⟨2, equalBody 0⟩, ⟨4, intervalBody 1 0 CBVtoCBN.unicodeAlphabet⟩]⟩

theorem counterGrammar_firstOrder : counterGrammar.FirstOrder := by
  intro rule hr
  simp only [counterGrammar, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact equalBody_firstOrder 0
  · exact intervalBody_firstOrder 1 0 CBVtoCBN.unicodeAlphabet

theorem counterGrammar_interval (x : List Char) (p q t u : Nat)
    (hp : p ≤ q) (hq : q ≤ x.length) (ht : t ≤ u) (hu : u ≤ x.length)
    (r : Option (List Char)) :
    SObs counterGrammar .callByValuePar
      (.call 1 [.lit (x.take p), .lit (x.take q), .lit (x.take t), .lit (x.take u)]) x r ↔
      r = if spanSlice x p q = spanSlice x t u then some x else none := by
  have h := interval_obs (g := counterGrammar) (self := 1) (equal := 0)
    (by rfl) (by rfl) x (fun c _ => CBVtoCBN.unicodeAlphabet_mem c) p q t u hp hq ht hu
  exact RootObservation.unique_iff h r

end Shallot.MacroPeg.CBV.PrefixCounters
