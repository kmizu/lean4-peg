import MacroPeg.CBV.ControlledFragmentPreflight

/-! Consuming fragment control with arbitrary caller-side tests. -/
namespace Shallot.MacroPeg.CBV.FragmentConsumingSyntax
open ClockFreezing (Table)
open PartialCodewordCapture (look)
open RuntimeShiftFilter (scanner)
open ControlledFragmentReplay (argument preflight tailBody)

/-- Only consuming leaves are restricted. Tests can call recursive users,
read retained parameters, and contain arbitrary first-order control. -/
inductive Syntax : MExp → Prop where
  | eps : Syntax .eps
  | char : Syntax (.chr 'a')
  | test (e : MExp) (he : e.FirstOrder) : Syntax (look e)
  | reject (e : MExp) (he : e.FirstOrder) : Syntax (.notP e)
  | seq {a b} : Syntax a → Syntax b → Syntax (.seq a b)
  | alt {a b} : Syntax a → Syntax b → Syntax (.alt a b)
  | star {a} : Syntax a → Syntax (.star a)

theorem firstOrder {e : MExp} (he : Syntax e) : e.FirstOrder := by
  induction he with
  | eps => trivial
  | char => trivial
  | test e he => exact he
  | reject e he => exact he
  | seq _ _ ia ib => exact ⟨ia,ib⟩
  | alt _ _ ia ib => exact ⟨ia,ib⟩
  | star _ ia => exact ia

private theorem suffix_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) {e : MExp} (he : Syntax e) :
    ∀ p q, p≤x.length → evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ l, sfx x p=List.replicate l 'a'++sfx x q := by
  induction he with
  | eps =>
    intro p q hp h
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,0,rfl⟩
  | char =>
    intro p q hp h
    cases hx : sfx x p with
    | nil => simp [evV,hx] at h
    | cons c rest =>
      simp only [evV,hx] at h
      cases hb : Shallot.beqChar 'a' c with
      | false => simp [hb] at h
      | true =>
        have hc : c='a' := (Char.toNat_inj.mp (by
          simpa only [Shallot.beqChar,beq_iff_eq] using hb)).symm
        have hq : rest.length=q := by simpa [hb] using h
        have hl := congrArg List.length hx
        rw [length_sfx x hp] at hl
        have hr : sfx x q=rest := by
          rw [←hq]
          exact sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨[c],hx⟩).choose_spec
        refine ⟨by simp only [List.length_cons] at hl; omega,1,?_⟩
        simpa [hc,hr] using hx
  | test e he =>
    intro p q hp h
    change evV g x s T E (.andP e) p=_ at h
    rw [CallLookahead.evV_peek] at h
    cases hv : evV g x s T E e p with
    | none => simp [hv,CallLookahead.peek] at h
    | some v => cases v with
      | none => simp [hv,CallLookahead.peek] at h
      | some z =>
        have hq : p=q := by simpa [hv,CallLookahead.peek] using h
        subst q; exact ⟨Nat.le_refl _,0,rfl⟩
  | reject e he =>
    intro p q hp h
    cases hv : evV g x s T E e p with
    | none => simp [evV,hv] at h
    | some v => cases v with
      | none =>
        have hq : p=q := by simpa [evV,hv] using h
        subst q; exact ⟨Nat.le_refl _,0,rfl⟩
      | some z => simp [evV,hv] at h
  | @seq a b _ _ ia ib =>
    intro p q hp h
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,l,hl⟩ := ia p j hp ha
        obtain ⟨hqj,k,hk⟩ := ib j q (Nat.le_trans hjp hp) h
        refine ⟨Nat.le_trans hqj hjp,l+k,?_⟩
        rw [hl,hk,←List.append_assoc,List.replicate_append_replicate]
  | @alt a b _ _ ia ib =>
    intro p q hp h
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact ib p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact ia p j hp ha
  | @star a _ ia =>
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro q hp h
      change evStar (fun z => evV g x s T E a z) p=_ at h
      cases ha : evV g x s T E a p with
      | none => rw [evStar_none ha] at h; cases h
      | some v => cases v with
        | none =>
          rw [evStar_fail ha] at h
          have hq : p=q := by simpa using h
          subst q; exact ⟨Nat.le_refl _,0,rfl⟩
        | some j =>
          by_cases hj : j<p
          · rw [evStar_ok ha hj] at h
            obtain ⟨hjp,l,hl⟩ := ia p j hp ha
            obtain ⟨hqj,k,hk⟩ := ih j hj q (Nat.le_trans hjp hp) h
            refine ⟨Nat.le_trans hqj hjp,l+k,?_⟩
            rw [hl,hk,←List.append_assoc,List.replicate_append_replicate]
          · rw [evStar_stuck ha hj] at h; cases h

/-- Real execution derives the capture value. No totality or successful
iteration premise is required, even for nested nullable repetition. -/
theorem shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) {e : MExp} (he : Syntax e)
    (p q : Nat) (hp : p≤x.length) (h : evV g x s T E e p=some (some q)) :
    ∃ l, pre x p q=List.replicate l 'a' ∧
      sfx x p=List.replicate l 'a'++sfx x q := by
  obtain ⟨hqp,l,hl⟩ := suffix_shape g x s T E he p q hp h
  refine ⟨l,?_,hl⟩
  simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
    pre_eq (sfx_is_suffix x p) hl

/-- The physical Seq checker preserves every partial outcome for this
consuming syntax. Original failure/None precedes all comparisons. -/
theorem physical_result (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (m p : Nat) (E : List (List Char)) (G H : MExp) (hH : Syntax H)
    (hp : p≤x.length) (r0 : ruleAtM g.rules 0=some ⟨1,.param 0⟩)
    (r1 : ruleAtM g.rules 1=some ⟨1,tailBody⟩) :
    evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (preflight G H) p=
    match evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1)) E (argument G H) p with
    | none => none
    | some none => some none
    | some (some q) =>
      match evV g x .callByValueSeq (tblV g x .callByValueSeq (m+1))
          [pre x p q] (.seq scanner (.param 0)) p with
      | some (some _) => some (some q) | other => other := by
  exact ControlledFragmentPreflight.physical_result_of_shape g hg x m p E G H
    (firstOrder hH) (shape g x .callByValueSeq _ E hH) hp r0 r1

end Shallot.MacroPeg.CBV.FragmentConsumingSyntax
