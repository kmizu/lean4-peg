import MacroPeg.CBV.RecursiveCopySyntax
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.RecursiveCopyCorrespondence
open RecursiveCopySyntax
abbrev Term := RecursiveCopySyntax.Expr

/-- Client rows may contain copy callbacks and need not remain syntactically
unchanged. All rows are related at the actual current physical clock. -/
def Rows (clients : List Term) (d : Char) (x : List Char) (k : Nat) : Prop :=
  ∀ (i : Nat) (e : Term), clients[i]?=some e → ∀ p, p≤x.length →
    valAt (tblV (source clients d) x .callByValuePar k i []) p=
      valAt (tblV (target clients d) x .callByValueSeq k i []) p

theorem expression_physical (clients : List Term) (alphabet : List Char) (d : Char) (hd : d∉alphabet)
    (x : List Char) (k : Nat) (rows : Rows clients d x k) :
    ∀ e, termCheck clients alphabet d e=true → ∀ p, p≤x.length →
    evV (source clients d) x .callByValuePar (tblV (source clients d) x .callByValuePar k) [] (render clients.length true e) p=
      evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false e) p
  | .user i,hc,p,hp => by
    have hi : i<clients.length := of_decide_eq_true (show decide (i<clients.length)=true from hc)
    have he := List.getElem?_eq_getElem hi
    rw [render,evV_call_par (source_user clients d i clients[i] he) rfl (by decide),
      render,evV_call_seq (target_user clients d i clients[i] he) rfl]
    exact rows i clients[i] he p hp
  | .copy a b,hc,p,hp => by
    obtain ⟨h,hb⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hab,ha⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hca,hcb⟩ := Bool.and_eq_true_iff.mp hab
    obtain ⟨hv,hsa⟩ := MaskedScannerAbsorption.checked (sourceBodies clients) alphabet (render clients.length true a) ha
    obtain ⟨_,hsb⟩ := MaskedScannerAbsorption.checked (sourceBodies clients) alphabet (render clients.length true b) hb
    exact DelimitedCopyCallTransfer.physical (source clients d) (target clients d) clients.length d
      (sourceBodies clients) _ alphabet (source_installed clients d) (source_firstOrder clients d) hv hd
      (render clients.length true a) (render clients.length true b) (render clients.length false a) (render clients.length false b)
      hsa hsb (render_firstOrder _ _ _) (render_firstOrder _ _ _) (source_copy clients d) (target_short clients d) (target_long clients d)
      x k p hp (expression_physical clients alphabet d hd x k rows a hca p hp) (expression_physical clients alphabet d hd x k rows b hcb p hp)
  | .seq a b,hc,p,hp => by
    have ha := expression_physical clients alphabet d hd x k rows a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV (source clients d) x .callByValuePar (tblV (source clients d) x .callByValuePar k) [] (render clients.length true a) p with
    | none => simp only [render,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        simp only [render,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact expression_physical clients alphabet d hd x k rows b (Bool.and_eq_true_iff.mp hc).2 q (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
  | .alt a b,hc,p,hp => by
    have ha := expression_physical clients alphabet d hd x k rows a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV (source clients d) x .callByValuePar (tblV (source clients d) x .callByValuePar k) [] (render clients.length true a) p with
    | none => simp only [render,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact expression_physical clients alphabet d hd x k rows b (Bool.and_eq_true_iff.mp hc).2 p hp
      | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .notP a,hc,p,hp => by simp only [render,evV,expression_physical clients alphabet d hd x k rows a hc p hp]
  | .star a,hc,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => expression_physical clients alphabet d hd x k rows a hc q (by omega))
  | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ => rfl

/-- One simultaneous induction closes the real mutually recursive clients,
copy headers, and copy-dependent actual queries without stabilizing a library. -/
theorem tables_related (clients : List Term) (alphabet : List Char) (d : Char) (hd : d∉alphabet)
    (hc : ∀ (i : Nat) (e : Term), clients[i]?=some e → termCheck clients alphabet d e=true)
    (x : List Char) (k : Nat) : Rows clients d x k := by
  induction k with
  | zero => intro i e hi p hp; rfl
  | succ k ih =>
    intro i e hi p hp
    rw [valAt_tblV_succ (source_user clients d i e hi) [] hp,valAt_tblV_succ (target_user clients d i e hi) [] hp]
    exact expression_physical clients alphabet d hd x k ih e (hc i e hi) p hp

theorem physical (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check clients alphabet d root=true) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source clients d) x .callByValuePar (tblV (source clients d) x .callByValuePar k) [] (render clients.length true root) p=
      evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false root) p := by
  obtain ⟨hd,hb,he⟩ := checked clients alphabet d root hc
  exact expression_physical clients alphabet d hd x k (tables_related clients alphabet d hd hb x k) root he p hp

theorem observations_iff (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check clients alphabet d root=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source clients d) .callByValuePar (render clients.length true root) x rest ↔
      SObs (target clients d) .callByValueSeq (render clients.length false root) x rest := by
  rw [←decideObsV_iff (source_firstOrder clients d) (by decide) (render_firstOrder _ _ _),
    ←decideObsV_iff (target_firstOrder clients d) (by decide) (render_firstOrder _ _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical clients alphabet d root hc x k _ (Nat.le_refl _))]

theorem language_translation (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check clients alphabet d root=true) :
    (fun x => SObs (source clients d) .callByValuePar (render clients.length true root) x (some []))=
      (fun x => SObs (target clients d) .callByValueSeq (render clients.length false root) x (some [])) := by
  funext x
  exact propext (observations_iff clients alphabet d root hc x (some []))

theorem defined_iff (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check clients alphabet d root=true) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source clients d) x .callByValuePar (tblV (source clients d) x .callByValuePar k) [] (render clients.length true root) x.length=some v) ↔
      ∃ k, evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false root) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical clients alphabet d root hc x k _ (Nat.le_refl _)).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical clients alphabet d root hc x k _ (Nat.le_refl _)).trans hk⟩

theorem undefined_iff (clients : List Term) (alphabet : List Char) (d : Char) (root : Term)
    (hc : check clients alphabet d root=true) (x : List Char) :
    (∀ k, evV (source clients d) x .callByValuePar (tblV (source clients d) x .callByValuePar k) [] (render clients.length true root) x.length=none) ↔
      ∀ k, evV (target clients d) x .callByValueSeq (tblV (target clients d) x .callByValueSeq k) [] (render clients.length false root) x.length=none := by
  constructor
  · intro h k; rw [←physical clients alphabet d root hc x k _ (Nat.le_refl _)]; exact h k
  · intro h k; rw [physical clients alphabet d root hc x k _ (Nat.le_refl _)]; exact h k

end Shallot.MacroPeg.CBV.RecursiveCopyCorrespondence
