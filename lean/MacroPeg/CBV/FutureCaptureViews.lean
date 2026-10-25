import MacroPeg.CBV.CaptureViews
import MacroPeg.CBV.DependentCaptureFilter

/-! Parameter views need only agree at positions still reachable from the
current continuation. This concerns arbitrary first-order continuations and
physical tables; it imposes no covering-anchor shape on the grammar. -/
namespace Shallot.MacroPeg.CBV.FutureCaptureViews

theorem success_le {g : MGrammar} {x : List Char} {s : Strategy}
    {T : Nat → List (List Char) → Val} (hs : s≠.callByName) (hT : SoundTV g x s T)
    (W : List (List Char)) (e : MExp) (he : e.FirstOrder) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T W e p=some (some q)) : q≤p := by
  have h := DependentCaptureFilter.success_prefix hs hT W e he p q hp hv
  have hh := congrArg List.length h.2
  simp only [length_sfx x hp,length_sfx x h.1,List.length_append] at hh
  omega

mutual
  theorem evV_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} {bound : Nat} (hs : s≠.callByName)
      (hT : SoundTV g x s T) (hb : bound≤x.length) (P : List MExp) (W : List (List Char))
      (hparam : ∀ k p, p≤bound → evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (b : MExp), b.FirstOrder → ∀ p, p≤bound → evV g x s T E (MExp.subst P b) p = evV g x s T W b p
    | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => by simp only [MExp.subst, evV]
    | .param k, _, p, hp => hparam k p hp
    | .call j ms, he, p, hp => by
      simp only [MExp.subst]
      cases hr : ruleAtM g.rules j with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = ms.length
        · have ha' : r.arity = (MExp.substArgs P ms).length := by rw [length_substArgs]; exact ha
          by_cases hseq : s = .callByValueSeq
          · subst hseq
            rw [evV_call_seq hr ha', evV_call_seq hr ha, evSeqArgs_rebind hs hT hb P W hparam ms he p hp]
          · rw [evV_call_par hr ha' hseq, evV_call_par hr ha hseq, evParArgs_rebind hs hT hb P W hparam ms he p hp]
        · have ha' : ¬ r.arity = (MExp.substArgs P ms).length := by rw [length_substArgs]; exact ha
          simp only [evV, hr, if_neg ha, if_neg ha']
    | .seq a c, he, p, hp => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) hs hT hb P W hparam a he.1 p hp
      cases h : evV g x s T W a p with
      | none => rw [evV_seq_none (ha.trans h), evV_seq_none h]
      | some r =>
        cases r with
        | none => rw [evV_seq_fail (ha.trans h), evV_seq_fail h]
        | some j => rw [evV_seq_ok (ha.trans h), evV_seq_ok h]; exact evV_rebind hs hT hb P W hparam c he.2 j (Nat.le_trans (success_le hs hT W a he.1 p j (Nat.le_trans hp hb) h) hp)
    | .alt a c, he, p, hp => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) hs hT hb P W hparam a he.1 p hp
      cases h : evV g x s T W a p with
      | none => rw [evV_alt_none (ha.trans h), evV_alt_none h]
      | some r =>
        cases r with
        | none => rw [evV_alt_fail (ha.trans h), evV_alt_fail h]; exact evV_rebind hs hT hb P W hparam c he.2 p hp
        | some j => rw [evV_alt_ok (ha.trans h), evV_alt_ok h]
    | .notP a, he, p, hp => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) hs hT hb P W hparam a he p hp
      cases h : evV g x s T W a p with
      | none => rw [evV_not_none (ha.trans h), evV_not_none h]
      | some r =>
        cases r with
        | none => rw [evV_not_fail (ha.trans h), evV_not_fail h]
        | some j => rw [evV_not_ok (ha.trans h), evV_not_ok h]
    | .star a, he, p, hp => by
      simp only [MExp.subst]
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q hq => evV_rebind hs hT hb P W hparam a he q (by omega))
    | .dbg _, he, _, _ | .lam _ _, he, _, _ | .callParam _ _, he, _, _ | .invoke _ _ _, he, _, _ => absurd he id

  theorem evParArgs_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} {bound : Nat} (hs : s≠.callByName)
      (hT : SoundTV g x s T) (hb : bound≤x.length) (P : List MExp) (W : List (List Char))
      (hparam : ∀ k p, p≤bound → evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → ∀ p, p≤bound →
        evParArgs g x s T E (MExp.substArgs P ms) p = evParArgs g x s T W ms p
    | [], _, p, _ => by simp only [MExp.substArgs, evPar_nil]
    | m :: ms, hm, p, hp => by
      simp only [MExp.substArgs]
      have hh := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) hs hT hb P W hparam m hm.1 p hp
      cases h : evV g x s T W m p with
      | none => rw [evPar_cons_none (hh.trans h), evPar_cons_none h]
      | some r =>
        cases r with
        | none => rw [evPar_cons_fail (hh.trans h), evPar_cons_fail h]
        | some j => rw [evPar_cons_ok (hh.trans h), evPar_cons_ok h, evParArgs_rebind hs hT hb P W hparam ms hm.2 p hp]

  theorem evSeqArgs_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} {bound : Nat} (hs : s≠.callByName)
      (hT : SoundTV g x s T) (hb : bound≤x.length) (P : List MExp) (W : List (List Char))
      (hparam : ∀ k p, p≤bound → evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → ∀ p, p≤bound →
        evSeqArgs g x s T E (MExp.substArgs P ms) p = evSeqArgs g x s T W ms p
    | [], _, p, _ => by simp only [MExp.substArgs, evSeq_nil]
    | m :: ms, hm, p, hp => by
      simp only [MExp.substArgs]
      have hh := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) hs hT hb P W hparam m hm.1 p hp
      cases h : evV g x s T W m p with
      | none => rw [evSeq_cons_none (hh.trans h), evSeq_cons_none h]
      | some r =>
        cases r with
        | none => rw [evSeq_cons_fail (hh.trans h), evSeq_cons_fail h]
        | some j => rw [evSeq_cons_ok (hh.trans h), evSeq_cons_ok h, evSeqArgs_rebind hs hT hb P W hparam ms hm.2 j (Nat.le_trans (success_le hs hT W m hm.1 p j (Nat.le_trans hp hb) h) hp)]
end

end Shallot.MacroPeg.CBV.FutureCaptureViews
