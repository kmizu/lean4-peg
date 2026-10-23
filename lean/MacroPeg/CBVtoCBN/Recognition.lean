import MacroPeg.CBVtoCBN.CompilerCorrect

namespace Shallot.MacroPeg.CBVtoCBN

-- Elaboration need not expand the fixed list of every character.
attribute [local irreducible] unicodeAlphabet

theorem finiteSource_accepts {source : MGrammar} {s : Strategy} {e : MExp}
    (hg : source.FirstOrder) (hs : s ≠ .callByName) (he : e.FirstOrder) (x : List Char) :
    (∃ m, evV source x s (tblV source x s m) [] e x.length = some (some 0)) ↔ SObs source s e x (some []) := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨o, hd, ho⟩ := evV_derives hg hs he m (Nat.le_refl _) hm
    rw [sfx_self] at hd
    obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok ho
    have hr : rest = [] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_, hd, rfl⟩
  · rintro ⟨o, hd, ho⟩
    obtain ⟨t, rfl⟩ := restOf_eq_some ho
    obtain ⟨m, hm⟩ := derivesV_ev (x := x) hg hs hd he ⟨[], rfl⟩
    exact ⟨m, hm⟩

theorem obs_star_any (g : MGrammar) : ∀ x : List Char, MacroObs g (.star .any) x (some [])
  | [] => obs_star_none obs_any_nil
  | a :: x => obs_star_some (obs_any_some a x) (obs_star_any g x)

theorem RootTest.consume_iff {g : MGrammar} {e : MExp} {x : List Char} {P : Prop}
    (h : RootTest g e x P) : MacroObs g (.seq e (.star .any)) x (some []) ↔ P := by
  classical
  by_cases hp : P
  · exact ⟨fun _ => hp, fun _ => obs_seq (h.1 hp) (obs_star_any g x)⟩
  · constructor
    · intro hs
      have hf : MacroObs g (.seq e (.star .any)) x none := obs_seq_none (h.2 hp)
      have he := macroObs_unique hf hs
      cases he
    · exact fun h => False.elim (hp h)

/-- The fixed length-discovery prefix supplies the correct full clock and original-input positions. -/
theorem compilerBootstrap_iff (c : CompilerConfig) (x : List Char) (r : Option (List Char)) :
    MacroObs c.target (.call 2 [.eps]) x r ↔
      MacroObs c.target (c.exprCall 0 c.start false (evalArgs x (List.replicate c.digits x.length) [] x.length 0)) x r := by
  have hf : ruleAtM c.target.rules 2 = some ⟨1, findLengthBody 2 3⟩ := rfl
  have hi : ruleAtM c.target.rules 3 = some ⟨1, .call (c.address (.expr 0 c.start))
      (.param 0 :: .eps :: .eps :: .param 0 :: .param 0 :: repeatPair (.param 0) .eps c.digits)⟩ := rfl
  have h := findLength_iff hf x 0 (by omega) r
  apply h.trans
  rw [obs_call_iff hi rfl]
  simp [MExp.subst, MExp.substArgs, subst_repeatPair, argAt, CompilerConfig.exprCall,
    evalArgs, evalRest, clockArgs_replicate, envArgs, skipN]

/-- A fixed arity bound, depending only on the source grammar. -/
def sourceArityBound (source : MGrammar) : Nat := (source.rules.map MRule.arity).sum

theorem sourceArityBound_spec (source : MGrammar) : ∀ rule ∈ source.rules, rule.arity ≤ sourceArityBound source := by
  have bound : ∀ xs : List Nat, ∀ a ∈ xs, a ≤ xs.sum := by
    intro xs
    induction xs with
    | nil => intro a ha; cases ha
    | cons b bs ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · have h := ih a ha; simp only [List.sum_cons]; omega
  intro rule hr
  exact bound _ _ (List.mem_map.mpr ⟨rule, hr, rfl⟩)

def translationConfig (source : MGrammar) (s : Strategy) (e : MExp) : CompilerConfig :=
  ⟨source, s, e, unicodeAlphabet, clockDigits source (sourceArityBound source)⟩

/-- The translator produces one fixed first-order CBN grammar from the source syntax. -/
def translate (source : MGrammar) (s : Strategy) (e : MExp) : MGrammar := (translationConfig source s e).target

theorem translate_firstOrder (source : MGrammar) (s : Strategy) (e : MExp) : (translate source s e).FirstOrder :=
  (translationConfig source s e).firstOrder

theorem candidateStart_firstOrder : candidateStart.FirstOrder := trivial

/-- Whole-input recognition is preserved on every original character string, for both CBV strategies. -/
theorem translate_recognizes {source : MGrammar} {s : Strategy} {e : MExp}
    (hg : source.FirstOrder) (hs : s ≠ .callByName) (he : e.FirstOrder) (x : List Char) :
    MacroObs (translate source s e) candidateStart x (some []) ↔ SObs source s e x (some []) := by
  let c := translationConfig source s e
  have htop : ruleAtM c.target.rules 1 = some ⟨0,
      .alt (emptyInputP source s e) (.seq (andP .any) (.seq (.call 2 [.eps]) (.star .any)))⟩ := rfl
  change MacroObs c.target (.call 1 []) x (some []) ↔ _
  rw [obs_call_iff htop rfl]
  have hclosed : MExp.subst [] (emptyInputP source s e) = emptyInputP source s e := by
    unfold emptyInputP
    split <;> rfl
  simp only [MExp.subst, MExp.substArgs, hclosed]
  change MacroObs c.target (.alt (emptyInputP source s e)
    (.seq (andP .any) (.seq (.call 2 [.eps]) (.star .any)))) x (some []) ↔ _
  by_cases hx : x = []
  · subst x
    have hf : MacroObs c.target (.seq (andP .any) (.seq (.call 2 [.eps]) (.star .any))) [] none :=
      obs_seq_none (obs_and_none obs_any_nil)
    rw [alt_fail_right_iff hf]
    simpa only [true_and] using emptyInputP_correct c.target hg hs he []
  · have hnonempty : 0 < x.length := by cases x <;> simp_all
    have hempty : MacroObs c.target (emptyInputP source s e) x none := by
      simpa only [hx, false_and, if_false] using emptyInputP_obs c.target source s e x
    have hguard : MacroObs c.target (andP .any) x (some x) := by
      cases x with
      | nil => exact False.elim (hx rfl)
      | cons a xs => exact obs_and_some (obs_any_some a xs)
    rw [alt_fail_left_iff hempty, seq_zero_iff hguard]
    let ds := List.replicate c.digits x.length
    have hd : ds.length = c.digits := List.length_replicate
    have hv : ∀ k ∈ ds, k ≤ x.length := by intro k hk; have hk' := List.mem_replicate.mp hk; omega
    have hroot := compiledEvaluator_correct c rfl hg hs x ds hd hv []
      (by intro span hm; cases hm) e he (compilerStart_available source e) x.length (Nat.le_refl _) 0 (by omega)
    have hboot := RootTest.of_equiv (compilerBootstrap_iff c x) hroot.1
    rw [hboot.consume_iff]
    have hc := fullClock_eval_iff source x s (sourceArityBound source) (sourceArityBound_spec source) hnonempty
      e x.length (Nat.le_refl _) (some 0)
    exact hc.trans (finiteSource_accepts hg hs he x)

end Shallot.MacroPeg.CBVtoCBN
