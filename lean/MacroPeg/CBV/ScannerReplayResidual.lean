import MacroPeg.CBV.DynamicScannerBinding
import MacroPeg.CBV.BlockCapture

namespace Shallot.MacroPeg.CBV.ScannerReplayResidual
open StatefulScanner (Machine next advance)
abbrev Labels (n : Nat) := Fin n → Option (List Char)

/-- A labeled scanner state carries the remaining fixed replay shift.
Each actual transition removes its leading character and rotates it back.
Unlabeled states may implement unrelated scanners in the same machine. -/
def check {n : Nat} (M : Machine n) (R : Labels n) : Bool :=
  (List.finRange n).all (fun q => match R q with
    | none => true
    | some [] => false
    | some (c::w) => (M.arcs q).all (fun (d,r) => decide (c=d ∧ R r=some (w++[c]))))

def entryCheck {n : Nat} (M : Machine n) (R : Labels n) (q : Fin n) : Bool :=
  check M R && (R q).isSome

/-- A labeled state has its required head transition. Unlabeled states
may still implement unrelated scanners. Soundness of every arc is checked
separately by `check`. -/
def completeCheck {n : Nat} (M : Machine n) (R : Labels n) : Bool :=
  (List.finRange n).all (fun q => match R q with
    | none => true
    | some [] => false
    | some (c::_) => (next (M.arcs q) c).isSome)

private theorem next_mem {Q : Type} (arcs : List (Char × Q)) (c : Char) (q : Q)
    (h : next arcs c=some q) : (c,q)∈arcs := by
  induction arcs with
  | nil => simp [next] at h
  | cons a arcs ih =>
    obtain ⟨d,r⟩ := a
    by_cases hc : Shallot.beqChar d c=true
    · have hd : d=c := Char.toNat_inj.mp (by simpa [Shallot.beqChar] using hc)
      have hr : r=q := by simpa [next,hc] using h
      simp [hd,hr]
    · exact List.mem_cons_of_mem _ (ih (by simpa [next,hc] using h))

/-- A defined capture path computes its unique actual rotated residual.
No periodic shape or successful replay is assumed. -/
theorem rotation {n : Nat} (M : Machine n) (R : Labels n) (hc : check M R=true)
    (w : List Char) (q r : Fin n) (u : List Char) (hq : R q=some u)
    (hw : advance M q w=some r) : ∃ v, R r=some v ∧ u++w=w++v := by
  induction w generalizing q u with
  | nil =>
    have hr : q=r := by simpa [advance] using hw
    subst r; exact ⟨u,hq,by simp⟩
  | cons c w ih =>
    have hrow := (List.all_eq_true.mp hc) q (List.mem_finRange q)
    cases u with
    | nil => simp [hq] at hrow
    | cons d u =>
      cases hs : next (M.arcs q) c with
      | none => simp [advance,hs] at hw
      | some t =>
        have ht := of_decide_eq_true ((List.all_eq_true.mp (show (M.arcs q).all
          (fun (e,t) => decide (d=e ∧ R t=some (u++[d])))=true from by simpa [hq] using hrow))
          (c,t) (next_mem (M.arcs q) c t hs))
        obtain ⟨hd,hlabel⟩ := ht
        subst d
        obtain ⟨v,hv,he⟩ := ih t (u++[c]) hlabel (by simpa [advance,hs] using hw)
        exact ⟨v,hv,by simpa [List.append_assoc] using congrArg (List.cons c) he⟩

/-- If an actual captured prefix can overlap a successful shifted copy,
a complete residual machine must read the entire capture. -/
theorem readable_of_overlap {n : Nat} (M : Machine n) (R : Labels n)
    (hSound : check M R=true) (hComplete : completeCheck M R=true)
    (w : List Char) : ∀ (q : Fin n) (u tail rest : List Char), R q=some u →
      w++tail=u++w++rest → StatefulScanner.advance M q w≠none := by
  induction w with
  | nil => intro q u tail rest hq he; simp [advance]
  | cons c w ih =>
    intro q u tail rest hq he
    have hc := (List.all_eq_true.mp hComplete) q (List.mem_finRange q)
    cases u with
    | nil => simp [hq] at hc
    | cons d u =>
      have hd : c=d := (List.cons.inj he).1
      subst d
      cases hs : next (M.arcs q) c with
      | none => simp [hq,hs] at hc
      | some t =>
        have hl := (List.all_eq_true.mp hSound) q (List.mem_finRange q)
        have ht := of_decide_eq_true ((List.all_eq_true.mp (show (M.arcs q).all
          (fun (e,t) => decide (c=e ∧ R t=some (u++[c])))=true from by simpa [hq] using hl))
          (c,t) (next_mem (M.arcs q) c t hs))
        have he' : w++tail=(u++[c])++w++rest := by
          simpa [List.append_assoc] using (List.cons.inj he).2
        simpa [advance,hs] using ih t (u++[c]) tail rest ht.2 he'

/-- An unreadable captured value forces finite source-header failure.
The original capture is a prefix of the actual input, not a shape oracle. -/
theorem replay_unreadable {n : Nat} (M : Machine n) (R : Labels n) (q : Fin n)
    (hEntry : entryCheck M R q=true) (hComplete : completeCheck M R=true)
    (w : List Char) (hw : advance M q w=none) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : ClockFreezing.Table) (p j : Nat)
    (hcap : sfx x p=w++sfx x j) :
    evV g x s T [w] (.seq (.lit ((R q).getD [])) (.param 0)) p=some none := by
  have he := WordArguments.word_eval g x s T [w]
    (.seq (.lit ((R q).getD [])) (.param 0)) ⟨True.intro,True.intro⟩ p
  simp only [WordArguments.value,WordArguments.literal,List.getElem?_cons_zero,
    Option.bind_some,Option.map_some] at he
  rw [he]
  cases hs : Shallot.stripPrefix? ((R q).getD []++w) (sfx x p) with
  | none => simp [evV,hs]
  | some rest =>
    have hx := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
    have hq : (R q).isSome=true := (Bool.and_eq_true_iff.mp hEntry).2
    cases hl : R q with
    | none => simp [hl] at hq
    | some u =>
      have hOverlap : w++sfx x j=u++w++rest := by
        simpa [hl] using hcap.symm.trans hx
      exact False.elim (readable_of_overlap M R (Bool.and_eq_true_iff.mp hEntry).1
        hComplete w q u (sfx x j) rest hl hOverlap hw)

theorem actual_rotation {n : Nat} (M : Machine n) (R : Labels n) (q : Fin n)
    (hc : entryCheck M R q=true) (w : List Char) (r : Fin n)
    (hw : advance M q w=some r) :
    (R q).getD []++w=w++(R r).getD [] := by
  have hh := Bool.and_eq_true_iff.mp hc
  cases hq : R q with
  | none => simp [hq] at hh
  | some u =>
    obtain ⟨v,hv,he⟩ := rotation M R hh.1 w q r u hq hw
    simpa [hq,hv] using he

/-- Rotating the header preserves its complete partial result, including
finite failure, in arbitrary grammars and at arbitrary clocks. -/
theorem replay_eq {n : Nat} (M : Machine n) (R : Labels n) (q : Fin n)
    (hc : entryCheck M R q=true) (w : List Char) (r : Fin n)
    (hw : advance M q w=some r) (g h : MGrammar) (x : List Char)
    (T U : ClockFreezing.Table) (p j : Nat) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) :
    evV g x .callByValuePar T [w] (.seq (.lit ((R q).getD [])) (.param 0)) p=
      evV h x .callByValueSeq U [w] (.lit ((R r).getD [])) j := by
  have hp : evV g x .callByValuePar T [w] (.param 0) p=some (some j) := by
    simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hcap,length_sfx x hj]
  rw [BlockCapture.prefix_rotate g x .callByValuePar T w _ _ (actual_rotation M R q hc w r hw) p,
    evV_seq_ok hp]
  rfl

end Shallot.MacroPeg.CBV.ScannerReplayResidual
