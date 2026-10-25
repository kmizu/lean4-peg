import MacroPeg.CBV.GuardedReplayControl

namespace Shallot.MacroPeg.CBV.LiteralPrefixObservation
open StatefulScanner (Machine next advance)
open ClockFreezing (Table)
abbrev Labels (n : Nat) := Fin n → Option (List Char)
abbrev Word (alphabet w : List Char) := ∀ c∈w, c∈alphabet

/-- Empty labels remember that the literal has already matched, even
while the remainder of a long capture is read. -/
def check {n : Nat} (M : Machine n) (alphabet : List Char) (L : Labels n) : Bool :=
  (List.finRange n).all (fun q => match L q with
    | none => true
    | some [] => (M.arcs q).all (fun cr => decide (L cr.2=some [])) &&
        alphabet.all (fun c => (next (M.arcs q) c).isSome)
    | some (c::u) => (M.arcs q).all (fun cr => decide (cr.1=c ∧ L cr.2=some u)) &&
        (next (M.arcs q) c).isSome)

def alphabetCheck {n : Nat} (M : Machine n) (alphabet : List Char) (a : Fin n) : Bool :=
  (M.arcs a).all (fun cr => decide (cr.1∈alphabet ∧ cr.2=a)) &&
    alphabet.all (fun c => decide (next (M.arcs a) c=some a))

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

theorem alphabet_advance {n : Nat} (M : Machine n) (alphabet : List Char) (a : Fin n)
    (hc : alphabetCheck M alphabet a=true) : ∀ w, Word alphabet w → advance M a w=some a
  | [],_ => rfl
  | c::w,hw => by
    have hs := of_decide_eq_true ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2) c (hw c (by simp)))
    simp only [advance,hs,Option.bind_some]
    exact alphabet_advance M alphabet a hc w (fun d hd => hw d (by simp [hd]))

theorem alphabet_of_readable {n : Nat} (M : Machine n) (alphabet : List Char) (a : Fin n)
    (hc : alphabetCheck M alphabet a=true) : ∀ w, advance M a w≠none → Word alphabet w
  | [],_ => by intro c hc; cases hc
  | c::w,hw => by
    cases hs : next (M.arcs a) c with
    | none => simp [advance,hs] at hw
    | some r =>
      have hr := of_decide_eq_true ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).1) (c,r) (next_mem _ _ _ hs))
      obtain ⟨hca,hr⟩ := hr
      change r=a at hr
      subst r
      have ht : advance M a w≠none := by simpa [advance,hs] using hw
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hca
      · exact alphabet_of_readable M alphabet a hc w ht d hd

theorem empty_path {n : Nat} (M : Machine n) (alphabet : List Char) (L : Labels n)
    (hc : check M alphabet L=true) : ∀ w q r, L q=some [] → advance M q w=some r → L r=some []
  | [],q,r,hq,hw => by
    have hr : q=r := by simpa [advance] using hw
    subst r
    exact hq
  | c::w,q,r,hq,hw => by
    have hrow := (List.all_eq_true.mp hc) q (List.mem_finRange q)
    have hrow := (Bool.and_eq_true_iff.mp (show ((M.arcs q).all (fun cr => decide (L cr.2=some [])) &&
      alphabet.all (fun c => (next (M.arcs q) c).isSome))=true from by simpa [hq] using hrow)).1
    cases hs : next (M.arcs q) c with
    | none => simp [advance,hs] at hw
    | some t =>
      exact empty_path M alphabet L hc w t r
        (of_decide_eq_true ((List.all_eq_true.mp hrow) (c,t) (next_mem _ _ _ hs)))
        (by simpa [advance,hs] using hw)

theorem empty_readable {n : Nat} (M : Machine n) (alphabet : List Char) (L : Labels n)
    (hc : check M alphabet L=true) : ∀ w, Word alphabet w → ∀ q, L q=some [] → advance M q w≠none
  | [],_,q,_ => by simp [advance]
  | c::w,hw,q,hq => by
    have hr := (List.all_eq_true.mp hc) q (List.mem_finRange q)
    have hr : ((M.arcs q).all (fun cr => decide (L cr.2=some [])) &&
        alphabet.all (fun c => (next (M.arcs q) c).isSome))=true := by simpa [hq] using hr
    cases hs : next (M.arcs q) c with
    | none => have hh := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hr).2) c (hw c (by simp)); simp [hs] at hh
    | some t =>
      have ht := of_decide_eq_true ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hr).1) (c,t) (next_mem _ _ _ hs))
      simpa [advance,hs] using empty_readable M alphabet L hc w (fun d hd => hw d (by simp [hd])) t ht

/-- A partial path either finished the literal inside the capture, or
leaves precisely the unconsumed literal suffix. -/
theorem derivative {n : Nat} (M : Machine n) (alphabet : List Char) (L : Labels n)
    (hc : check M alphabet L=true) : ∀ w q r u, L q=some u → advance M q w=some r →
    ∃ v, L r=some v ∧ ((u.IsPrefix w ∧ v=[]) ∨ u=w++v)
  | [],q,r,u,hq,hw => by
    have hr : q=r := by simpa [advance] using hw
    subst r
    exact ⟨u,hq,Or.inr (by simp)⟩
  | c::w,q,r,[],hq,hw =>
    ⟨[],empty_path M alphabet L hc (c::w) q r hq hw,Or.inl ⟨by simp,rfl⟩⟩
  | c::w,q,r,d::u,hq,hw => by
    have hr := (List.all_eq_true.mp hc) q (List.mem_finRange q)
    have hr : ((M.arcs q).all (fun cr => decide (cr.1=d ∧ L cr.2=some u)) &&
        (next (M.arcs q) d).isSome)=true := by simpa [hq] using hr
    cases hs : next (M.arcs q) c with
    | none => simp [advance,hs] at hw
    | some t =>
      obtain ⟨rfl,ht⟩ := of_decide_eq_true ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hr).1) (c,t) (next_mem _ _ _ hs))
      obtain ⟨v,hv,hv'⟩ := derivative M alphabet L hc w t r u ht (by simpa [advance,hs] using hw)
      refine ⟨v,hv,?_⟩
      rcases hv' with ⟨hp,rfl⟩ | he
      · obtain ⟨tail,he⟩ := hp
        exact Or.inl ⟨⟨tail,congrArg (List.cons c) he⟩,rfl⟩
      · exact Or.inr (congrArg (List.cons c) he)

theorem readable_of_prefix {n : Nat} (M : Machine n) (alphabet : List Char) (L : Labels n)
    (hc : check M alphabet L=true) : ∀ w, Word alphabet w → ∀ q u suffix,
    L q=some u → u.IsPrefix (w++suffix) → advance M q w≠none
  | [],_,q,u,suffix,hq,hp => by simp [advance]
  | c::w,hw,q,[],suffix,hq,_ => empty_readable M alphabet L hc (c::w) hw q hq
  | c::w,hw,q,d::u,suffix,hq,hp => by
    obtain ⟨rest,he⟩ := hp
    have hd : d=c := (List.cons.inj he).1
    subst d
    have hr := (List.all_eq_true.mp hc) q (List.mem_finRange q)
    have hr : ((M.arcs q).all (fun cr => decide (cr.1=c ∧ L cr.2=some u)) &&
        (next (M.arcs q) c).isSome)=true := by simpa [hq] using hr
    cases hs : next (M.arcs q) c with
    | none => simp [hs] at hr
    | some t =>
      have ht := (of_decide_eq_true ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp hr).1) (c,t) (next_mem _ _ _ hs))).2
      simpa [advance,hs] using readable_of_prefix M alphabet L hc w (fun d hd => hw d (by simp [hd])) t u suffix ht ⟨rest,(List.cons.inj he).2⟩

def query {n : Nat} (P : List Nat) (q : Fin n) (L : Labels n) : MExp :=
  match DynamicScannerBinding.resume P q with
  | none => MExp.failAlways
  | some r => .andP (.lit ((L r).getD []))

theorem query_firstOrder {n : Nat} (P : List Nat) (q : Fin n) (L : Labels n) : (query P q L).FirstOrder := by
  simp only [query]
  split <;> trivial

theorem literal_test (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (u : List Char) (p : Nat) :
    evV g x s T E (.andP (.lit u)) p=
      if u.IsPrefix (sfx x p) then some (some p) else some none := by
  rw [CallLookahead.evV_peek]
  by_cases hp : u.IsPrefix (sfx x p)
  · obtain ⟨rest,he⟩ := hp
    rw [if_pos ⟨rest,he⟩]
    simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr he.symm,CallLookahead.peek]
  · cases hs : Shallot.stripPrefix? u (sfx x p) with
    | none => simp [evV,hs,CallLookahead.peek,hp]
    | some rest => exact False.elim (hp ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hs).symm⟩)

theorem peek_transfer {n : Nat} (M : Machine n) (alphabet : List Char) (L : Labels n)
    (hc : check M alphabet L=true) (q : Fin n) (u : List Char) (hq : L q=some u)
    (g h : MGrammar) (x w : List Char) (s t : Strategy) (T U : Table) (p j : Nat)
    (hw : Word alphabet w) (hpj : GuardedReplayControl.Aligned x w p j) :
    GuardedReplayControl.Results (GuardedReplayControl.Aligned x w)
      (evV g x s T [w] (.andP (.lit u)) p)
      (evV h x t U [w] (query (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) q L) j) := by
  cases hs : advance M q w with
  | none =>
    have hn : ¬u.IsPrefix (sfx x p) := by
      intro hu
      exact readable_of_prefix M alphabet L hc w hw q u (sfx x j) hq (hpj.2.2 ▸ hu) hs
    simp [query,DynamicScannerBinding.resume_actual,hs,literal_test,hn,MExp.failAlways,evV,GuardedReplayControl.Results]
  | some r =>
    obtain ⟨v,hv,hv'⟩ := derivative M alphabet L hc w q r u hq hs
    simp only [query,DynamicScannerBinding.resume_actual,hs,hv,Option.getD_some,literal_test]
    rcases hv' with ⟨hu,rfl⟩ | rfl
    · have hsrc : u.IsPrefix (sfx x p) := by
        obtain ⟨tail,he⟩ := hu
        refine ⟨tail++sfx x j,?_⟩
        rw [←List.append_assoc,he,←hpj.2.2]
      simpa [hsrc,GuardedReplayControl.Results] using hpj
    · have he : (w++v).IsPrefix (sfx x p) ↔ v.IsPrefix (sfx x j) := by
        rw [hpj.2.2]
        constructor
        · rintro ⟨tail,he⟩
          exact ⟨tail,List.append_cancel_left (as := w) (by simpa only [List.append_assoc] using he)⟩
        · rintro ⟨tail,he⟩
          exact ⟨tail,by simpa [List.append_assoc] using congrArg (w++·) he⟩
      by_cases ht : v.IsPrefix (sfx x j)
      · simpa [he,ht,GuardedReplayControl.Results] using hpj
      · simp [he,ht,GuardedReplayControl.Results]

end Shallot.MacroPeg.CBV.LiteralPrefixObservation
