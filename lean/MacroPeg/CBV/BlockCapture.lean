import MacroPeg.CBV.CaptureCommutation

/-! Syntactic recursive block capture and a phase-sensitive rotation law. -/
namespace Shallot.MacroPeg.CBV.BlockCapture
open RecursiveParserStability (Installed)
open ClockFreezing (Table)

def copies (u : List Char) : Nat → List Char
  | 0 => []
  | n+1 => u ++ copies u n

theorem copies_add (u : List Char) (n m : Nat) : copies u (n+m) = copies u n ++ copies u m := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simpa only [Nat.succ_add,copies,List.append_assoc] using congrArg (u ++ ·) ih

theorem copies_commute (u : List Char) (n : Nat) : u ++ copies u n = copies u n ++ u := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simpa only [copies,List.append_assoc] using congrArg (u ++ ·) ih

theorem rotate (left right : List Char) (n : Nat) :
    (left++right) ++ (copies (left++right) n ++ left) =
      (copies (left++right) n ++ left) ++ (right++left) := by
  rw [← List.append_assoc,copies_commute]
  simp only [List.append_assoc]

def Safe (n : Nat) (u : List Char) : MExp → Prop
  | .eps | .notP _ => True
  | .lit w => ∃ k, w = copies u k
  | .seq a b | .alt a b => Safe n u a ∧ Safe n u b
  | .star a => Safe n u a
  | .call i [] => i<n
  | _ => False

def Related (u x : List Char) (p q : Nat) : Prop :=
  ∃ n, sfx x p = copies u n ++ sfx x q

def RowsSafe (n : Nat) (u x : List Char) (T : Table) : Prop :=
  ∀ i, i<n → ∀ p q, p ≤ x.length → valAt (T i []) p = some (some q) → Related u x p q

theorem related_refl (u x : List Char) (p : Nat) : Related u x p p := ⟨0,by simp [copies]⟩

theorem related_trans {u x : List Char} {p q r : Nat}
    (h : Related u x p q) (k : Related u x q r) : Related u x p r := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := k
  exact ⟨n+m,by rw [copies_add,hn,hm,List.append_assoc]⟩

theorem evaluator_safe {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (u x : List Char) (s : Strategy) (T : Table)
    (hRows : RowsSafe bodies.length u x T) (hOk : OkTV x.length T) (E : List (List Char)) :
    ∀ e, Safe bodies.length u e → ∀ p q, p ≤ x.length → evV g x s T E e p = some (some q) → Related u x p q
  | .eps, _, p, q, hp, hv => by cases hv; exact related_refl u x _
  | .lit w, hw, p, q, hp, hv => by
    obtain ⟨n,rfl⟩ := hw
    cases hs : Shallot.stripPrefix? (copies u n) (sfx x p) with
    | none => simp only [evV,hs] at hv; cases hv
    | some rest =>
      simp only [evV,hs,Option.some.injEq] at hv
      subst q
      have hh := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
      have hr : sfx x rest.length = rest :=
        sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨_,hh⟩).choose_spec
      exact ⟨n,by rw [hr]; exact hh⟩
  | .call i [], hi, p, q, hp, hv => by
    have hr := hg i bodies[i] (List.getElem?_eq_getElem hi)
    cases s <;> apply hRows i hi p q hp <;>
      simpa only [evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true] using hv
  | .seq a b, he, p, q, hp, hv => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at hv; cases hv
    | some r => cases r with
      | none => rw [evV_seq_fail ha] at hv; cases hv
      | some j =>
        rw [evV_seq_ok ha] at hv
        exact related_trans (evaluator_safe hg u x s T hRows hOk E a he.1 p j hp ha)
          (evaluator_safe hg u x s T hRows hOk E b he.2 j q (evV_ok hOk a p hp j ha) hv)
  | .alt a b, he, p, q, hp, hv => by
    cases ha : evV g x s T E a p with
    | none => rw [evV_alt_none ha] at hv; cases hv
    | some r => cases r with
      | none => rw [evV_alt_fail ha] at hv
                exact evaluator_safe hg u x s T hRows hOk E b he.2 p q hp hv
      | some j => rw [evV_alt_ok ha] at hv
                  cases hv
                  exact evaluator_safe hg u x s T hRows hOk E a he.1 p q hp ha
  | .notP e, _, p, q, hp, hv => by
    cases he : evV g x s T E e p with
    | none => simp only [evV,he] at hv; cases hv
    | some r => cases r with
      | none => simp only [evV,he,Option.some.injEq] at hv; subst q; exact related_refl u x p
      | some j => simp only [evV,he] at hv; cases hv
  | .star e, he, p, q, hp, hv => by
    have hh : ∀ p, p ≤ x.length → evStar (fun z => evV g x s T E e z) p = some (some q) → Related u x p q := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro hp hv
        cases ha : evV g x s T E e p with
        | none => rw [evStar_none ha] at hv; cases hv
        | some r => cases r with
          | none => rw [evStar_fail ha] at hv; cases hv; exact related_refl u x _
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at hv
              exact related_trans (evaluator_safe hg u x s T hRows hOk E e he p j hp ha) (ih j hj (by omega) hv)
            · rw [evStar_stuck ha hj] at hv; cases hv
    exact hh p hp hv
  | .chr _, h, _, _, _, _ | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _
  | .param _, h, _, _, _, _ | .call _ (_::_), h, _, _, _, _ | .dbg _, h, _, _, _, _
  | .lam _ _, h, _, _, _, _ | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem physical_rows_safe {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (u : List Char) (hf : ∀ e ∈ bodies, Safe bodies.length u e)
    (x : List Char) (s : Strategy) (k : Nat) : RowsSafe bodies.length u x (tblV g x s k) := by
  induction k with
  | zero => intro i hi p q hp hv; cases hv
  | succ k ih =>
    intro i hi p q hp hv
    rw [valAt_tblV_succ (hg i bodies[i] (List.getElem?_eq_getElem hi)) [] hp] at hv
    exact evaluator_safe hg u x s _ ih (tblV_ok _ _ _ k) [] bodies[i] (hf _ (List.getElem_mem hi)) p q hp hv

theorem frozen_rows_safe {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (u : List Char) (hf : ∀ e ∈ bodies, Safe bodies.length u e)
    (x : List Char) (s : Strategy) (k : Nat) :
    RowsSafe bodies.length u x (RecursiveParserStability.frozen bodies g x s k) := by
  intro i hi p q hp hv
  rw [RecursiveParserStability.frozen,ClockFreezing.frozen_rows _ _ _ _ _ _ i (by simp [RecursiveParserStability.pick,hi])] at hv
  exact physical_rows_safe hg u hf x s (RecursiveParserStability.floor bodies x) i hi p q hp hv

/-- The phase suffix is captured with the recursive block prefix. -/
theorem head_capture {bodies : List MExp} {g : MGrammar}
    (hg : Installed bodies g) (u r x : List Char) (T : Table)
    (hRows : RowsSafe bodies.length u x T) (hOk : OkTV x.length T)
    (hT : SoundTV g x .callByValuePar T) (e : MExp) (he : e.FirstOrder) (hs : Safe bodies.length u e)
    (p q : Nat) (hp : p ≤ x.length)
    (hv : evV g x .callByValuePar T [] (.seq e (.lit r)) p = some (some q)) :
    ∃ n, pre x p q = copies u n ++ r := by
  have hfull := (ReplayFusion.success_prefix hT [] (.seq e (.lit r)) ⟨he,True.intro⟩ p q hp hv).2
  cases ha : evV g x .callByValuePar T [] e p with
  | none => rw [evV_seq_none ha] at hv; cases hv
  | some result => cases result with
    | none => rw [evV_seq_fail ha] at hv; cases hv
    | some j =>
      rw [evV_seq_ok ha] at hv
      obtain ⟨n,hn⟩ := evaluator_safe hg u x .callByValuePar T hRows hOk [] e hs p j hp ha
      cases hr : Shallot.stripPrefix? r (sfx x j) with
      | none => simp only [evV,hr] at hv; cases hv
      | some rest =>
        simp only [evV,hr,Option.some.injEq] at hv
        subst q
        have hh := (CBVtoCBN.stripPrefix_exact _ _ _).mp hr
        have hrest : sfx x rest.length = rest :=
          sfx_suffix (suffix_trans (sfx_is_suffix x j) ⟨r,hh⟩).choose_spec
        refine ⟨n,(List.append_left_inj (sfx x rest.length)).mp ?_⟩
        rw [← hfull,hn,hh,hrest,List.append_assoc]

/-- A rotated residual replaces the source prefix, including on failure. -/
theorem prefix_rotate (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w u v : List Char) (h : u++w=w++v) (p : Nat) :
    evV g x s T [w] (.seq (.lit u) (.param 0)) p =
      evV g x s T [w] (.seq (.param 0) (.lit v)) p := by
  rw [WordArguments.word_eval g x s T [w] (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩,
    WordArguments.word_eval g x s T [w] (.seq (.param 0) (.lit v)) ⟨True.intro,True.intro⟩]
  simp only [WordArguments.value,List.getElem?_cons_zero,Option.bind_some,Option.map_some,h]

/-- Every phase-shifted ab capture here is genuinely noncommuting. -/
theorem ab_noncommuting (n : Nat) :
    ['a','b'] ++ (copies ['a','b'] n ++ ['a']) ≠
      (copies ['a','b'] n ++ ['a']) ++ ['a','b'] := by
  intro h
  rw [← List.append_assoc,copies_commute] at h
  have hh := (List.append_right_inj (copies ['a','b'] n)).mp
    (show copies ['a','b'] n ++ ['a','b','a'] = copies ['a','b'] n ++ ['a','a','b'] from by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using h)
  have hn : ['a','b','a'] ≠ ['a','a','b'] := by decide
  exact hn hh

end Shallot.MacroPeg.CBV.BlockCapture
