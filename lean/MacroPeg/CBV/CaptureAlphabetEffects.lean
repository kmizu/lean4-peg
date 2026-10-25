import MacroPeg.CBV.DelimitedValueSafety

/-! Alphabet effects for actual Par captures. Each parameter has its own
alphabet and each rule has its own result alphabet. Calls on consuming
paths may be mutually recursive. A predicate has empty output regardless
of the expressions it executes; it need not terminate.

This checks source captures, not a Par-to-Seq translation. In particular,
Par call results exclude the text consumed while evaluating their actuals.
-/
namespace Shallot.MacroPeg.CBV.CaptureAlphabetEffects
open ClockFreezing (Table)

abbrev Alphabet := List Char
def Within (A : Alphabet) (w : List Char) : Prop := ∀ c∈w, c∈A
def subset (A B : Alphabet) : Bool := A.all (fun c => decide (c∈B))
inductive Environment : List Alphabet → List (List Char) → Prop where
  | nil : Environment [] []
  | cons {A : Alphabet} {w : List Char} {As : List Alphabet} {ws : List (List Char)}
      (head : Within A w) (tail : Environment As ws) : Environment (A::As) (w::ws)

structure Signature where
  parameters : List Alphabet
  result : Alphabet
  deriving DecidableEq

mutual
  def check (signatures : List Signature) (Γ : List Alphabet) (A : Alphabet) : MExp → Bool
    | .eps | .notP _ => true
    | .lit w => subset w A
    | .chr c => decide (c∈A)
    | .param i => match Γ[i]? with | none => true | some B => subset B A
    | .seq a b | .alt a b => check signatures Γ A a && check signatures Γ A b
    | .star a => check signatures Γ A a
    | .call i args => match signatures[i]? with
      | none => false
      | some σ => subset σ.result A && checkArgs signatures Γ σ.parameters args
    | _ => false
  def checkArgs (signatures : List Signature) (Γ : List Alphabet) : List Alphabet → List MExp → Bool
    | [],[] => true
    | A::As,a::args => check signatures Γ A a && checkArgs signatures Γ As args
    | _,_ => false
end

theorem subset_sound (A B : Alphabet) (h : subset A B=true) : ∀ c∈A, c∈B := by
  intro c hc
  exact of_decide_eq_true (List.all_eq_true.mp h c hc)

theorem within_mono {A B : Alphabet} {w : List Char}
    (h : ∀ c∈A, c∈B) (hw : Within A w) : Within B w :=
  fun c hc => h c (hw c hc)

theorem within_append {A : Alphabet} {u v : List Char}
    (hu : Within A u) (hv : Within A v) : Within A (u++v) := by
  intro c hc
  exact (List.mem_append.mp hc).elim (hu c) (hv c)

theorem environment_lookup {Γ : List Alphabet} {E : List (List Char)}
    (h : Environment Γ E) (i : Nat) :
    (Γ[i]?=none ∧ E[i]?=none) ∨ ∃ A w, Γ[i]?=some A ∧ E[i]?=some w ∧ Within A w := by
  induction h generalizing i with
  | nil => exact Or.inl ⟨rfl,rfl⟩
  | @cons A w As ws hw ht ih =>
    cases i with
    | zero => exact Or.inr ⟨A,w,rfl,rfl,hw⟩
    | succ i => simpa only [List.getElem?_cons_succ] using ih i

def Shape (A : Alphabet) (x : List Char) (p q : Nat) : Prop :=
  q≤p ∧ ∃ w, Within A w ∧ sfx x p=w++sfx x q

theorem captured_of_shape (A : Alphabet) (x : List Char) (p q : Nat)
    (hp : p≤x.length) (h : Shape A x p q) : Within A (pre x p q) := by
  obtain ⟨hqp,w,hw,hs⟩ := h
  have he : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
      pre_eq (sfx_is_suffix x p) hs
  exact he.symm ▸ hw

theorem shape_mono {A B : Alphabet} {x : List Char} {p q : Nat}
    (h : ∀ c∈A, c∈B) (hs : Shape A x p q) : Shape B x p q := by
  obtain ⟨hq,w,hw,hx⟩ := hs
  exact ⟨hq,w,within_mono h hw,hx⟩

private theorem literal_shape (g : MGrammar) (x : List Char) (T : Table)
    (E : List (List Char)) (w : List Char) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x .callByValuePar T E (.lit w) p=some (some q)) :
    q≤p ∧ sfx x p=w++sfx x q := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at hv
  | some rest =>
    have hq : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using hv
    have hh := (CBVtoCBN.stripPrefix_exact w (sfx x p) rest).mp hs
    have hr : sfx x rest.length=rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨w,hh⟩).choose_spec
    have hl := congrArg List.length hh
    rw [length_sfx x hp,List.length_append] at hl
    exact ⟨by omega,by rw [←hq,hr]; exact hh⟩

def Rows (signatures : List Signature) (x : List Char) (T : Table) : Prop :=
  ∀ i σ, signatures[i]?=some σ → ∀ E, Environment σ.parameters E → ∀ p q, p≤x.length →
    valAt (T i E) p=some (some q) → Shape σ.result x p q

mutual
  theorem expression (g : MGrammar) (x : List Char) (T : Table) (signatures : List Signature)
      (hRows : Rows signatures x T) (Γ : List Alphabet) (E : List (List Char)) (hE : Environment Γ E) :
      ∀ e A, check signatures Γ A e=true → ∀ p q, p≤x.length →
        evV g x .callByValuePar T E e p=some (some q) → Shape A x p q
    | .eps, A, _, p, q, hp, h => by
      have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
      subst q; exact ⟨Nat.le_refl _,[],(by intro c hc; cases hc),rfl⟩
    | .lit w, A, he, p, q, hp, h => by
      obtain ⟨hq,hs⟩ := literal_shape g x T E w p q hp h
      exact ⟨hq,w,subset_sound w A he,hs⟩
    | .chr c, A, he, p, q, hp, h => by
      have hc : c∈A := of_decide_eq_true he
      have hl : evV g x .callByValuePar T E (.lit [c]) p=some (some q) := by
        cases hs : sfx x p with
        | nil => simp [evV,hs] at h
        | cons d rest =>
          cases hb : Shallot.beqChar c d <;> simpa [evV,hs,Shallot.stripPrefix?,hb] using h
      obtain ⟨hq,hs⟩ := literal_shape g x T E [c] p q hp hl
      exact ⟨hq,[c],(by intro d hd; simpa using (List.mem_singleton.mp hd ▸ hc)),hs⟩
    | .param i, A, he, p, q, hp, h => by
      rcases environment_lookup hE i with ⟨hΓ,hw⟩ | ⟨B,w,hΓ,hw,hB⟩
      · simp [evV,hw] at h
      · have hh : subset B A=true := by simpa only [check,hΓ] using he
        have hl : evV g x .callByValuePar T E (.lit w) p=some (some q) := by simpa only [evV,hw] using h
        obtain ⟨hq,hs⟩ := literal_shape g x T E w p q hp hl
        exact ⟨hq,w,within_mono (subset_sound B A hh) hB,hs⟩
    | .notP a, A, _, p, q, hp, h => by
      cases ha : evV g x .callByValuePar T E a p with
      | none => simp [evV,ha] at h
      | some v => cases v with
        | some j => simp [evV,ha] at h
        | none =>
          have hq : p=q := by simpa only [evV,ha,Option.some.injEq] using h
          subst q; exact ⟨Nat.le_refl _,[],(by intro c hc; cases hc),rfl⟩
    | .seq a b, A, he, p, q, hp, h => by
      have hh := Bool.and_eq_true_iff.mp he
      cases ha : evV g x .callByValuePar T E a p with
      | none => rw [evV_seq_none ha] at h; cases h
      | some v => cases v with
        | none => rw [evV_seq_fail ha] at h; cases h
        | some j =>
          rw [evV_seq_ok ha] at h
          obtain ⟨hj,u,hu,hs⟩ := expression g x T signatures hRows Γ E hE a A hh.1 p j hp ha
          obtain ⟨hq,v,hv,ht⟩ := expression g x T signatures hRows Γ E hE b A hh.2 j q (Nat.le_trans hj hp) h
          exact ⟨Nat.le_trans hq hj,u++v,within_append hu hv,by rw [hs,ht,List.append_assoc]⟩
    | .alt a b, A, he, p, q, hp, h => by
      have hh := Bool.and_eq_true_iff.mp he
      cases ha : evV g x .callByValuePar T E a p with
      | none => simp [evV,ha] at h
      | some v => cases v with
        | none => exact expression g x T signatures hRows Γ E hE b A hh.2 p q hp (by simpa only [evV,ha] using h)
        | some j =>
          have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
          subst q; exact expression g x T signatures hRows Γ E hE a A hh.1 p j hp ha
    | .star a, A, he, p, q, hp, h => by
      have hh : ∀ p q, p≤x.length → evStar (fun z => evV g x .callByValuePar T E a z) p=some (some q) → Shape A x p q := by
        intro p
        induction p using Nat.strongRecOn with
        | ind p ih =>
          intro q hp h
          cases ha : evV g x .callByValuePar T E a p with
          | none => rw [evStar_none ha] at h; cases h
          | some v => cases v with
            | none =>
              rw [evStar_fail ha] at h
              have hq : p=q := by simpa using h
              subst q; exact ⟨Nat.le_refl _,[],(by intro c hc; cases hc),rfl⟩
            | some j =>
              by_cases hj : j<p
              · rw [evStar_ok ha hj] at h
                obtain ⟨hjp,u,hu,hs⟩ := expression g x T signatures hRows Γ E hE a A he p j hp ha
                obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
                exact ⟨Nat.le_trans hqj hjp,u++v,within_append hu hv,by rw [hs,ht,List.append_assoc]⟩
              · rw [evStar_stuck ha hj] at h; cases h
      exact hh p q hp h
    | .call i args, A, he, p, q, hp, h => by
      cases hσ : signatures[i]? with
      | none => simp [check,hσ] at he
      | some σ =>
        have hh : subset σ.result A=true ∧ checkArgs signatures Γ σ.parameters args=true := by
          simpa only [check,hσ,Bool.and_eq_true] using he
        cases hr : ruleAtM g.rules i with
        | none => simp [evV,hr] at h
        | some r =>
          by_cases hn : r.arity=args.length
          · rw [evV_call_par hr hn (by decide)] at h
            cases hv : evParArgs g x .callByValuePar T E args p with
            | none => simp [hv] at h
            | some v => cases v with
              | none => simp [hv] at h
              | some W =>
                simp only [hv] at h
                exact shape_mono (subset_sound σ.result A hh.1)
                  (hRows i σ hσ W (arguments g x T signatures hRows Γ E hE σ.parameters args hh.2 p hp W hv) p q hp h)
          · simp [evV,hr,hn] at h
    | .any,_,h,_,_,_,_ | .range _ _,_,h,_,_,_,_ | .dbg _,_,h,_,_,_,_
    | .lam _ _,_,h,_,_,_,_ | .callParam _ _,_,h,_,_,_,_ | .invoke _ _ _,_,h,_,_,_,_ => by cases h

  theorem arguments (g : MGrammar) (x : List Char) (T : Table) (signatures : List Signature)
      (hRows : Rows signatures x T) (Γ : List Alphabet) (E : List (List Char)) (hE : Environment Γ E) :
      ∀ As args, checkArgs signatures Γ As args=true → ∀ p, p≤x.length → ∀ W,
        evParArgs g x .callByValuePar T E args p=some (some W) → Environment As W
    | [],[],_,p,hp,W,h => by
      have hw : W=[] := by simpa only [evPar_nil,Option.some.injEq] using h.symm
      subst W; exact .nil
    | A::As,a::args,he,p,hp,W,h => by
      have hh := Bool.and_eq_true_iff.mp he
      cases ha : evV g x .callByValuePar T E a p with
      | none => simp [evParArgs,ha] at h
      | some v => cases v with
        | none => simp [evParArgs,ha] at h
        | some q =>
          cases ht : evParArgs g x .callByValuePar T E args p with
          | none => simp [evParArgs,ha,ht] at h
          | some v => cases v with
            | none => simp [evParArgs,ha,ht] at h
            | some V =>
              have hw : pre x p q::V=W := by simpa only [evParArgs,ha,ht,Option.some.injEq] using h
              subst W
              exact .cons (captured_of_shape A x p q hp (expression g x T signatures hRows Γ E hE a A hh.1 p q hp ha))
                (arguments g x T signatures hRows Γ E hE As args hh.2 p hp V ht)
    | [],_::_,h,_,_,_,_ | _::_,[],h,_,_,_,_ => by cases h
end

def grammarCheck (g : MGrammar) (signatures : List Signature) : Bool :=
  decide (signatures.length=g.rules.length) && g.rules.zipIdx.all (fun (r,i) =>
    match signatures[i]? with
    | none => false
    | some σ => decide (r.arity=σ.parameters.length) && check signatures σ.parameters σ.result r.body)

theorem grammar_checked (g : MGrammar) (signatures : List Signature) (hc : grammarCheck g signatures=true)
    (i : Nat) (σ : Signature) (hσ : signatures[i]?=some σ) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    r.arity=σ.parameters.length ∧ check signatures σ.parameters σ.result r.body=true := by
  rw [ruleAtM_eq_getElem?] at hr
  have hm : (r,i)∈g.rules.zipIdx := List.mem_of_getElem? (show g.rules.zipIdx[i]?=some (r,i) from by
    simp [List.getElem?_zipIdx,hr])
  have hh := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 (r,i) hm
  simpa only [hσ,Bool.and_eq_true,decide_eq_true_eq] using hh

/-- Every row premise is discharged by induction on the actual physical
clock, simultaneously for all declared parameter and result alphabets. -/
theorem physical_rows (g : MGrammar) (signatures : List Signature) (hg : grammarCheck g signatures=true)
    (x : List Char) (k : Nat) : Rows signatures x (tblV g x .callByValuePar k) := by
  induction k with
  | zero => intro i σ hσ E hE p q hp h; simp [tblV,valAt_nil] at h
  | succ k ih =>
    intro i σ hσ E hE p q hp h
    cases hr : ruleAtM g.rules i with
    | none => simp [tblV,hr,valAt_nil] at h
    | some r =>
      rw [valAt_tblV_succ hr E hp] at h
      exact expression g x _ signatures ih σ.parameters E hE r.body σ.result
        (grammar_checked g signatures hg i σ hσ r hr).2 p q hp h

theorem capture (g : MGrammar) (signatures : List Signature) (hg : grammarCheck g signatures=true)
    (x : List Char) (k : Nat) (Γ : List Alphabet) (E : List (List Char)) (hE : Environment Γ E)
    (e : MExp) (A : Alphabet) (he : check signatures Γ A e=true) (p q : Nat) (hp : p≤x.length)
    (h : evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=some (some q)) :
    Within A (pre x p q) :=
  captured_of_shape A x p q hp (expression g x _ signatures (physical_rows g signatures hg x k) Γ E hE e A he p q hp h)

theorem captured_free (g : MGrammar) (signatures : List Signature) (hg : grammarCheck g signatures=true)
    (x : List Char) (k : Nat) (Γ : List Alphabet) (E : List (List Char)) (hE : Environment Γ E)
    (e : MExp) (A : Alphabet) (he : check signatures Γ A e=true) (d : Char) (hd : d∉A)
    (p q : Nat) (hp : p≤x.length)
    (h : evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=some (some q)) :
    DelimitedCopyProjection.Free d (pre x p q) := by
  intro hm
  exact hd (capture g signatures hg x k Γ E hE e A he p q hp h d hm)

end Shallot.MacroPeg.CBV.CaptureAlphabetEffects
