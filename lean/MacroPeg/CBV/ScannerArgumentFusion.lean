import MacroPeg.CBV.ScannerCapturedArguments
import MacroPeg.CBV.ScannerPairFusion

/-! Unary scanner-prefix rules with varying capture-dependent arguments.
The same fixed grammar recognizes the same strings under Par and Seq. -/
namespace Shallot.MacroPeg.CBV.ScannerArgumentFusion
open NestedScannerArguments (accepts scan scan_eval)
open ScannerCapturedArguments (Environment Safe)
open ClockFreezing (Table)

def Supported (A : List Char) : MExp → Prop
  | .call _ [a] => Supported A a ∧ Safe A a
  | .seq a b | .alt a b => Supported A a ∧ Supported A b
  | .star a | .notP a => Supported A a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

def grammar (A : List Char) (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun e => ⟨1,.seq (scan A) e⟩)⟩
def Valid (A : List Char) (tails : List MExp) : Prop := ∀ e∈tails, Supported A e

theorem supported_firstOrder (A : List Char) : ∀ e, Supported A e → e.FirstOrder
  | .call _ [a], h => ⟨supported_firstOrder A a h.1,True.intro⟩
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder A a h.1,supported_firstOrder A b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder A a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .call _ (_::_::_), h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem firstOrder (A : List Char) (tails : List MExp) (hv : Valid A tails) : (grammar A tails).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  exact ⟨NestedScannerArguments.scan_firstOrder A,supported_firstOrder A e (hv e he)⟩

theorem rule (A : List Char) (tails : List MExp) (i : Nat) :
    ruleAtM (grammar A tails).rules i=(tails[i]?).map (fun e => ⟨1,.seq (scan A) e⟩) := by
  simp [grammar,ruleAtM_eq_getElem?]

def Shifted (A : List Char) (tails : List MExp) (x : List Char) (T U : Table) : Prop :=
  ∀ i e, tails[i]?=some e → ∀ w p q, p≤x.length → q≤x.length → w.all (accepts A)=true →
    sfx x p=w++sfx x q → valAt (T i [w]) p=valAt (U i [w]) q

theorem evaluator_of_shift (A : List Char) (tails : List MExp) (x : List Char) (T U : Table)
    (hT : SoundTV (grammar A tails) x .callByValuePar T) (hOk : OkTV x.length T)
    (hShift : Shifted A tails x T U) :
    ∀ e, Supported A e → ∀ E, Environment A E → ∀ p, p≤x.length →
    evV (grammar A tails) x .callByValuePar T E e p=
    evV (grammar A tails) x .callByValueSeq U E e p
  | .call i [a], he, E, hE, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [evV,rule,hr,Option.map_none]
    | some body =>
      have hg : ruleAtM (grammar A tails).rules i=some ⟨1,.seq (scan A) body⟩ := by rw [rule,hr]; rfl
      rw [evV_call_par hg rfl (by decide),evV_call_seq hg rfl]
      have ha := evaluator_of_shift A tails x T U hT hOk hShift a he.1 E hE p hp
      simp only [evParArgs,evSeqArgs]
      rw [←ha]
      cases ha' : evV (grammar A tails) x .callByValuePar T E a p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          dsimp only []
          have hq := evV_ok hOk a p hp q ha'
          have hw := ScannerCapturedArguments.capture_safe (grammar A tails) x A T hT hOk E hE a
            (supported_firstOrder A a he.1) he.2 p q hp ha'
          have hpref := (ReplayFusion.success_prefix hT E a (supported_firstOrder A a he.1) p q hp ha').2
          exact hShift i body hr (pre x p q) p q hp hq hw hpref
  | .seq a b, he, E, hE, p, hp => by
    have ha := evaluator_of_shift A tails x T U hT hOk hShift a he.1 E hE p hp
    cases hv : evV (grammar A tails) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact evaluator_of_shift A tails x T U hT hOk hShift b he.2 E hE q (evV_ok hOk a p hp q hv)
  | .alt a b, he, E, hE, p, hp => by
    have ha := evaluator_of_shift A tails x T U hT hOk hShift a he.1 E hE p hp
    cases hv : evV (grammar A tails) x .callByValuePar T E a p with
    | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact evaluator_of_shift A tails x T U hT hOk hShift b he.2 E hE p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .star a, he, E, hE, p, hp => by
    exact evStar_congr p (fun q hq => evaluator_of_shift A tails x T U hT hOk hShift a he E hE q (by omega))
  | .notP a, he, E, hE, p, hp => by
    simp only [evV]
    rw [evaluator_of_shift A tails x T U hT hOk hShift a he E hE p hp]
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _ | .range _ _, _, _, _, _, _
  | .lit _, _, _, _, _, _ | .param _, _, _, _, _, _ => rfl
  | .call _ [], h, _, _, _, _ | .call _ (_::_::_), h, _, _, _, _ | .dbg _, h, _, _, _, _
  | .lam _ _, h, _, _, _, _ | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem tables_shifted (A : List Char) (tails : List MExp) (hv : Valid A tails) (x : List Char) :
    ∀ k, Shifted A tails x (tblV (grammar A tails) x .callByValuePar k) (tblV (grammar A tails) x .callByValueSeq k)
  | 0 => by intro i e hi w p q hp hq hw hs; simp only [tblV,valAt_nil]
  | k+1 => by
    intro i e hi w p q hp hq hw hs
    rw [valAt_tblV_succ (rule A tails i |>.trans (by rw [hi]; rfl)) [w] hp,
      valAt_tblV_succ (rule A tails i |>.trans (by rw [hi]; rfl)) [w] hq]
    have habs : (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A) := by
      rw [hs,ScannerAbsorption.dropWhile_append A w hw]
    rw [evV_seq_ok (scan_eval _ _ _ _ _ A p hp),evV_seq_ok (scan_eval _ _ _ _ _ A q hq),habs]
    have hz : ((sfx x q).dropWhile (accepts A)).length≤x.length := by
      have hl := congrArg List.length (List.takeWhile_append_dropWhile (p:=accepts A) (l:=sfx x q))
      have hx : (sfx x q).length≤x.length := by simp [sfx]
      simp only [List.length_append] at hl
      omega
    exact evaluator_of_shift A tails x _ _ (tblV_sound (firstOrder A tails hv) (by decide) k)
      (tblV_ok _ _ _ k) (tables_shifted A tails hv x k) e (hv e (List.mem_of_getElem? hi))
      [w] (by intro v h; simp only [List.mem_singleton] at h; subst v; exact hw) _ hz

theorem evaluator_eq (A : List Char) (tails : List MExp) (hv : Valid A tails) (e : MExp)
    (he : Supported A e) (x : List Char) (k : Nat) :
    evV (grammar A tails) x .callByValuePar (tblV (grammar A tails) x .callByValuePar k) [] e x.length=
    evV (grammar A tails) x .callByValueSeq (tblV (grammar A tails) x .callByValueSeq k) [] e x.length :=
  evaluator_of_shift A tails x _ _ (tblV_sound (firstOrder A tails hv) (by decide) k) (tblV_ok _ _ _ k)
    (tables_shifted A tails hv x k) e he [] (by simp [Environment]) x.length (Nat.le_refl _)

theorem observations_iff (A : List Char) (tails : List MExp) (hv : Valid A tails) (e : MExp)
    (he : Supported A e) (x : List Char) (rest : Option (List Char)) :
    SObs (grammar A tails) .callByValuePar e x rest ↔ SObs (grammar A tails) .callByValueSeq e x rest := by
  have hd : decideObsV .callByValuePar (grammar A tails) x e=decideObsV .callByValueSeq (grammar A tails) x e := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (grammar A tails) (grammar A tails) x .callByValuePar .callByValueSeq
      e e (evaluator_eq A tails hv e he x)]
  rw [←decideObsV_iff (firstOrder A tails hv) (by decide) (supported_firstOrder A e he),
    ←decideObsV_iff (firstOrder A tails hv) (by decide) (supported_firstOrder A e he),hd]

theorem language_translation (A : List Char) (tails : List MExp) (hv : Valid A tails) (e : MExp)
    (he : Supported A e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (grammar A tails) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨grammar A tails,e,firstOrder A tails hv,supported_firstOrder A e he,fun x => observations_iff A tails hv e he x (some [])⟩

end Shallot.MacroPeg.CBV.ScannerArgumentFusion
