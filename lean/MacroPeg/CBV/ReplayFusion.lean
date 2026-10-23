import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBV.ReplayFusion

/-! A Par rule `F(x) ← x B` can become the Seq rule `F(x) ← B`.
The capture remains available in B, including in recursive calls. This is a
fixed grammar transformation for this rule shape, not a normal-form theorem
for arbitrary Par grammars. -/

def parGrammar (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun body => ⟨1, .seq (.param 0) body⟩)⟩

def seqGrammar (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun body => ⟨1, body⟩)⟩

theorem par_rule (tails : List MExp) (i : Nat) :
    ruleAtM (parGrammar tails).rules i =
      (tails[i]?).map (fun body => ⟨1, .seq (.param 0) body⟩) := by
  simp [parGrammar, ruleAtM_eq_getElem?]

theorem seq_rule (tails : List MExp) (i : Nat) :
    ruleAtM (seqGrammar tails).rules i = (tails[i]?).map (fun body => ⟨1, body⟩) := by
  simp [seqGrammar, ruleAtM_eq_getElem?]

theorem par_firstOrder {tails : List MExp} (h : ∀ body ∈ tails, body.FirstOrder) :
    (parGrammar tails).FirstOrder := by
  intro r hr
  obtain ⟨body, hb, rfl⟩ := List.mem_map.mp hr
  exact ⟨trivial, h body hb⟩

theorem seq_firstOrder {tails : List MExp} (h : ∀ body ∈ tails, body.FirstOrder) :
    (seqGrammar tails).FirstOrder := by
  intro r hr
  obtain ⟨body, hb, rfl⟩ := List.mem_map.mp hr
  exact h body hb

theorem success_prefix {g : MGrammar} {x : List Char}
    {T : Nat → List (List Char) → Val} (hT : SoundTV g x .callByValuePar T)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p j : Nat) (hp : p ≤ x.length)
    (hv : evV g x .callByValuePar T E e p = some (some j)) :
    j ≤ x.length ∧ sfx x p = pre x p j ++ sfx x j := by
  have hs : (MExp.subst (E.map MExp.lit) e).FirstOrder :=
    firstOrder_subst (firstOrderArgs_lits E) e he
  have hv' : evV g x .callByValuePar T [] (MExp.subst (E.map MExp.lit) e) p =
      some (some j) := by
    rw [evV_subst E e he]
    exact hv
  obtain ⟨o, hd, ho⟩ := evV_sound (by decide) hT _ hs p hp _ hv'
  obtain ⟨t, rest, rfl, hj⟩ := obsR_ok ho
  have hf := mderives_suffix hd _ _ rfl
  have hr := rest_eq_sfx' hd
  rw [hj] at hr
  have hlen : j ≤ x.length := by
    obtain ⟨w, hw⟩ := hf
    have hl := congrArg List.length hw
    rw [List.length_append, length_sfx x hp, hj] at hl
    omega
  refine ⟨hlen, ?_⟩
  rw [hr]
  simpa [hj] using pre_split hp hf

def Shifted (tails : List MExp) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i body, tails[i]? = some body → ∀ w p q, p ≤ x.length → q ≤ x.length →
    sfx x p = w ++ sfx x q → valAt (T i [w]) p = valAt (U i [w]) q

mutual
  theorem evaluator_of_shift {tails : List MExp} {x : List Char}
      {T U : Nat → List (List Char) → Val}
      (hT : SoundTV (parGrammar tails) x .callByValuePar T)
      (hOk : OkTV x.length T) (hshift : Shifted tails x T U) :
      ∀ e : MExp, e.FirstOrder → ∀ E p, p ≤ x.length →
        evV (parGrammar tails) x .callByValuePar T E e p =
          evV (seqGrammar tails) x .callByValueSeq U E e p
    | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
    | .range _ _, _, _, _, _ | .lit _, _, _, _, _ | .param _, _, _, _, _ => by
      simp only [evV]
    | .dbg _, hf, _, _, _ | .lam _ _, hf, _, _, _
    | .callParam _ _, hf, _, _, _ | .invoke _ _ _, hf, _, _, _ => False.elim hf
    | .call i args, hf, E, p, hp => by
      have hargs := arguments_of_shift hT hOk hshift args hf E p hp
      cases hr : tails[i]? with
      | none => simp [evV, par_rule, seq_rule, hr]
      | some body =>
        by_cases ha : 1 = args.length
        · cases args with
          | nil => simp at ha
          | cons a args =>
            cases args with
            | cons b args => simp at ha
            | nil =>
              have heq := hargs a (by simp)
              simp only [evV, par_rule, seq_rule, hr, Option.map, if_pos ha,
                evParArgs, evSeqArgs]
              rw [← heq]
              cases hv : evV (parGrammar tails) x .callByValuePar T E a p with
              | none => rfl
              | some result =>
                cases result with
                | none => rfl
                | some q =>
                  obtain ⟨hq, hpre⟩ := success_prefix hT E a hf.1 p q hp hv
                  exact hshift i body hr (pre x p q) p q hp hq hpre
        · simp [evV, par_rule, seq_rule, hr, ha]
    | .seq a b, hf, E, p, hp => by
      have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
      cases hv : evV (parGrammar tails) x .callByValuePar T E a p with
      | none => rw [evV_seq_none hv, evV_seq_none (heq.symm.trans hv)]
      | some result =>
        cases result with
        | none => rw [evV_seq_fail hv, evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv, evV_seq_ok (heq.symm.trans hv)]
          exact evaluator_of_shift hT hOk hshift b hf.2 E q (evV_ok hOk a p hp q hv)
    | .alt a b, hf, E, p, hp => by
      have heq := evaluator_of_shift hT hOk hshift a hf.1 E p hp
      cases hv : evV (parGrammar tails) x .callByValuePar T E a p with
      | none => rw [evV_alt_none hv, evV_alt_none (heq.symm.trans hv)]
      | some result =>
        cases result with
        | none =>
          rw [evV_alt_fail hv, evV_alt_fail (heq.symm.trans hv)]
          exact evaluator_of_shift hT hOk hshift b hf.2 E p hp
        | some q => rw [evV_alt_ok hv, evV_alt_ok (heq.symm.trans hv)]
    | .notP a, hf, E, p, hp => by
      simp only [evV]
      rw [evaluator_of_shift hT hOk hshift a hf E p hp]
    | .star a, hf, E, p, hp => by
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hshift a hf E q (by omega))

  theorem arguments_of_shift {tails : List MExp} {x : List Char}
      {T U : Nat → List (List Char) → Val}
      (hT : SoundTV (parGrammar tails) x .callByValuePar T)
      (hOk : OkTV x.length T) (hshift : Shifted tails x T U) :
      ∀ args : List MExp, MExp.FirstOrderArgs args → ∀ E p, p ≤ x.length →
        ∀ a ∈ args, evV (parGrammar tails) x .callByValuePar T E a p =
          evV (seqGrammar tails) x .callByValueSeq U E a p
    | [], _, _, _, _, _, hm => by cases hm
    | a :: args, hf, E, p, hp, b, hm => by
      rcases List.mem_cons.mp hm with he | hm
      · subst b; exact evaluator_of_shift hT hOk hshift a hf.1 E p hp
      · exact arguments_of_shift hT hOk hshift args hf.2 E p hp b hm
end

theorem tables_shifted {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (x : List Char) (m : Nat) :
    Shifted tails x (tblV (parGrammar tails) x .callByValuePar m)
      (tblV (seqGrammar tails) x .callByValueSeq m) := by
  induction m with
  | zero => intro i body hr w p q hp hq hs; simp [tblV, valAt_nil]
  | succ m ih =>
    intro i body hr w p q hp hq hs
    have hrp : ruleAtM (parGrammar tails).rules i = some ⟨1, .seq (.param 0) body⟩ := by
      rw [par_rule, hr]; rfl
    have hrs : ruleAtM (seqGrammar tails).rules i = some ⟨1, body⟩ := by
      rw [seq_rule, hr]; rfl
    rw [valAt_tblV_succ hrp [w] hp, valAt_tblV_succ hrs [w] hq]
    have hstrip := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr hs
    simp only [evV, List.getElem?_cons_zero, hstrip, length_sfx x hq]
    exact evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) m)
      (tblV_ok _ _ _ m) ih body (hf body (List.mem_of_getElem? hr)) [w] q hq

/-- The transformed grammar has the same partial result at every table clock.
This includes explicit failure and absence of a finite result. -/
theorem evaluator_eq {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (x : List Char) (m : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (p : Nat) (hp : p ≤ x.length) :
    evV (parGrammar tails) x .callByValuePar (tblV (parGrammar tails) x .callByValuePar m) E e p =
      evV (seqGrammar tails) x .callByValueSeq (tblV (seqGrammar tails) x .callByValueSeq m) E e p :=
  evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) m) (tblV_ok _ _ _ m)
    (tables_shifted hf x m) e he E p hp

theorem iterBound_eq (tails : List MExp) (x : List Char) :
    iterBoundV (parGrammar tails) x = iterBoundV (seqGrammar tails) x := by
  have hlen : (parGrammar tails).rules.length = (seqGrammar tails).rules.length := by
    simp [parGrammar, seqGrammar]
  unfold iterBoundV
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [par_rule, seq_rule]
  cases tails[i]? <;> rfl

theorem decide_eq {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decideObsV .callByValuePar (parGrammar tails) x e =
      decideObsV .callByValueSeq (seqGrammar tails) x e := by
  unfold decideObsV
  rw [evaluator_eq hf x _ [] e he x.length (Nat.le_refl _), iterBound_eq]

/-- One fixed Seq grammar preserves every finite observation on the original
strings, for arbitrary recursive first-order tails. No totality is assumed. -/
theorem observations_iff {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar tails) .callByValuePar e x r ↔
      SObs (seqGrammar tails) .callByValueSeq e x r := by
  rw [← decideObsV_iff (par_firstOrder hf) (by decide) he,
    ← decideObsV_iff (seq_firstOrder hf) (by decide) he, decide_eq hf e he x]

theorem recognizes_iff {tails : List MExp} (hf : ∀ body ∈ tails, body.FirstOrder)
    (e : MExp) (he : e.FirstOrder) (x : List Char) :
    SObs (parGrammar tails) .callByValuePar e x (some []) ↔
      SObs (seqGrammar tails) .callByValueSeq e x (some []) :=
  observations_iff hf e he x (some [])

end Shallot.MacroPeg.CBV.ReplayFusion
