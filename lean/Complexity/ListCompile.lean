import Complexity.Macros

/-!
# Compiling list programs to tape programs

`compile_exec`: a list-program run in which every visited state has lists shorter than `B - 1` is matched by a run of
the compiled tape program within `TFits B`, costing at most `8 * B + 20` tape steps per list step, ending in a tape
state that represents the final lists.
-/

namespace Complexity

variable {k : Nat}

/-- The tape outcome represents the list outcome. -/
def ORep : LOutcome k → Outcome k → Prop
  | .cont L, .cont τ => Rep L τ
  | .stop b L, .stop b' τ => b = b' ∧ Rep L τ
  | _, _ => False

/-- After the inner loop of a compiled `loop`: continuing outcomes have the head of tape `i` on the last element. -/
def ORepAt (i : Fin k) : LOutcome k → Outcome k → Prop
  | .cont L, .cont τ' => ∃ τ, Rep L τ ∧ τ' = τ.setPos i (L i).length
  | .stop b L, .stop b' τ => b = b' ∧ Rep L τ
  | _, _ => False

theorem LExec.q_start {Q : Lists k → Prop} {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k}
    (h : LExec Q p L t o) : Q L := by
  induction h <;> assumption

theorem LExec.q_end {Q : Lists k → Prop} {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k}
    (h : LExec Q p L t o) : ∀ L', (o = .cont L' ∨ ∃ b, o = .stop b L') → Q L' := by
  induction h with
  | push _ h₂ => rintro L' (h | ⟨b, h⟩) <;> cases h; exact h₂
  | pop _ h₂ => rintro L' (h | ⟨b, h⟩) <;> cases h; exact h₂
  | copy _ _ h₂ => rintro L' (h | ⟨b, h⟩) <;> cases h; exact h₂
  | halt h₁ => rintro L' (h | ⟨b, h⟩) <;> cases h; exact h₁
  | seqC _ _ _ ih₂ => exact ih₂
  | seqS _ ih => exact ih
  | iteT _ _ _ ih => exact ih
  | iteF _ _ _ ih => exact ih
  | loopF h₁ => rintro L' (h | ⟨b, h⟩) <;> cases h; exact h₁
  | loopC _ _ _ _ _ ih₂ => exact ih₂
  | loopS _ _ _ ih => exact ih

theorem lc_tfits {L : Lists k} {τ : Tapes k} {B : Nat} (hR : Rep L τ) (hB : LenOK B L) (i : Fin k) {p : Nat}
    (hp : p ≤ (L i).length + 1) : TFits B (τ.setPos i p) := by
  intro j
  refine ⟨?_, fun x hx => (hR j).2.2.2 x (by have := hB j; omega)⟩
  show (if j = i then p else τ.pos j) < B
  split
  · subst j; have := hB i; omega
  · rw [(hR j).1]; have := hB j; omega

theorem setPos_zero_of_rep {L : Lists k} {τ : Tapes k} (hR : Rep L τ) (i : Fin k) : τ.setPos i 0 = τ := by
  cases τ with
  | mk pos cells =>
    simp only [Tapes.setPos, Tapes.mk.injEq, and_true]
    funext j
    split
    · subst j; exact ((hR i).1).symm
    · rfl

theorem lc_tfits0 {L : Lists k} {τ : Tapes k} {B : Nat} (hR : Rep L τ) (hB : LenOK B L) : TFits B τ := by
  cases k with
  | zero => intro j; exact j.elim0
  | succ k =>
    have := lc_tfits hR hB 0 (Nat.zero_le _)
    rwa [setPos_zero_of_rep hR] at this

/-- The cost factor per list step. -/
def lcost (B : Nat) : Nat := 8 * B + 20

/-- The body of the compiled loop. -/
def loopBody (i : Fin k) (p : LProg k) : Prog k := .seq (goHome i) (.seq p.compile (goLast i))

theorem compile_exec {Q : Lists k → Prop} {B : Nat} (hQ : ∀ L, Q L → LenOK B L) :
    ∀ {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k}, LExec Q p L t o →
      (∀ τ, Rep L τ → ∃ t' o', t' ≤ t * lcost B ∧ Exec (TFits B) p.compile τ t' o' ∧ ORep o o') ∧
      (∀ i c body, p = .loop i c body → ∀ τ, Rep L τ → ∃ t' o', t' + 4 * B + 6 ≤ t * lcost B ∧
        Exec (TFits B) (.loop (fun r => c (r i)) (loopBody i body)) (τ.setPos i (L i).length) t' o' ∧
        ORepAt i o o') := by
  intro p L t o h
  induction h with
  | @push i e L hq hq' =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    obtain ⟨t', τ', ht', hex, hR'⟩ := pushP_spec i e hR (hQ _ hq')
    exact ⟨t', _, by simp only [lcost]; omega, hex, hR'⟩
  | @pop i L hq hq' =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    obtain ⟨t', τ', ht', hex, hR'⟩ := popP_spec i hR (hQ _ hq)
    exact ⟨t', _, by simp only [lcost]; omega, hex, hR'⟩
  | @copy i j L hij hq hq' =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    obtain ⟨t', τ', ht', hex, hR'⟩ := copyP_spec i j hij hR (hQ _ hq')
    exact ⟨t', _, by simp only [lcost]; omega, hex, hR'⟩
  | @halt b L hq =>
    refine ⟨fun τ hR => ⟨1, _, by simp only [lcost]; omega, Exec.halt (lc_tfits0 hR (hQ _ hq)), rfl, hR⟩,
      fun _ _ _ he => by cases he⟩
  | @seqC p q L L₁ t₁ t₂ o _ _ ih₁ ih₂ =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    obtain ⟨t₁', o₁, ht₁, hex₁, hr₁⟩ := ih₁.1 τ hR
    cases o₁ with
    | stop _ _ => exact hr₁.elim
    | cont τ₁ =>
      obtain ⟨t₂', o₂, ht₂, hex₂, hr₂⟩ := ih₂.1 τ₁ hr₁
      exact ⟨t₁' + t₂', o₂, by rw [Nat.add_mul]; omega, Exec.seqC hex₁ hex₂, hr₂⟩
  | @seqS p q L L₁ t₁ b _ ih =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    obtain ⟨t₁', o₁, ht₁, hex₁, hr₁⟩ := ih.1 τ hR
    cases o₁ with
    | cont _ => exact hr₁.elim
    | stop b' τ₁ =>
      obtain ⟨rfl, hr⟩ := hr₁
      exact ⟨t₁', _, ht₁, Exec.seqS hex₁, rfl, hr⟩
  | @iteT i c p q L t o hq hc _ ih =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    have hB := hQ _ hq
    obtain ⟨t', o', ht', hex, hr⟩ := ih.1 τ hR
    have hgl := goLast_spec i hR hB
    have hgh := goHome_spec i hR hB (p := (L i).length) (Nat.le_succ _)
    refine ⟨(2 * (L i).length + 4) + ((2 * (L i).length + 1 + t') + 1), o', ?_,
      Exec.seqC hgl (Exec.iteT (lc_tfits hR hB i (Nat.le_succ _)) (by rw [read_last i hR]; exact hc)
        (Exec.seqC hgh hex)), hr⟩
    have := hB i
    simp only [lcost, Nat.add_mul, Nat.one_mul] at ht' ⊢; omega
  | @iteF i c p q L t o hq hc _ ih =>
    refine ⟨fun τ hR => ?_, fun _ _ _ he => by cases he⟩
    have hB := hQ _ hq
    obtain ⟨t', o', ht', hex, hr⟩ := ih.1 τ hR
    have hgl := goLast_spec i hR hB
    have hgh := goHome_spec i hR hB (p := (L i).length) (Nat.le_succ _)
    refine ⟨(2 * (L i).length + 4) + ((2 * (L i).length + 1 + t') + 1), o', ?_,
      Exec.seqC hgl (Exec.iteF (lc_tfits hR hB i (Nat.le_succ _)) (by rw [read_last i hR]; exact hc)
        (Exec.seqC hgh hex)), hr⟩
    have := hB i
    simp only [lcost, Nat.add_mul, Nat.one_mul] at ht' ⊢; omega
  | @loopF i c p L hq hc =>
    have hB := hQ _ hq
    have inner : ∀ τ, Rep L τ → ∃ t' o', t' + 4 * B + 6 ≤ 1 * lcost B ∧
        Exec (TFits B) (.loop (fun r => c (r i)) (loopBody i p)) (τ.setPos i (L i).length) t' o' ∧
        ORepAt i (.cont L) o' := fun τ hR =>
      ⟨1, _, by simp only [lcost]; omega,
        Exec.loopF (lc_tfits hR hB i (Nat.le_succ _)) (by rw [read_last i hR]; exact hc), τ, hR, rfl⟩
    refine ⟨fun τ hR => ?_, fun i' c' body he τ hR => ?_⟩
    · obtain ⟨t', o', ht', hex, hr⟩ := inner τ hR
      cases o' with
      | stop _ _ => exact hr.elim
      | cont τ₁ =>
        obtain ⟨τ₂, hR₂, rfl⟩ := hr
        have hL : (fun j => L j) = L := rfl
        refine ⟨(2 * (L i).length + 4) + (t' + (2 * (L i).length + 1)), _, ?_,
          Exec.seqC (goLast_spec i hR hB) (Exec.seqC hex (goHome_spec i hR₂ hB (Nat.le_succ _))), hR₂⟩
        have := hB i
        simp only [lcost] at ht' ⊢; omega
    · cases he; exact inner τ hR
  | @loopC i c p L L₁ t₁ t₂ o hq hc hbody hrest ihb ihr =>
    have hB := hQ _ hq
    have hq₁ : Q L₁ := hrest.q_start
    have hB₁ := hQ _ hq₁
    have inner : ∀ τ, Rep L τ → ∃ t' o', t' + 4 * B + 6 ≤ (t₁ + 1 + t₂) * lcost B ∧
        Exec (TFits B) (.loop (fun r => c (r i)) (loopBody i p)) (τ.setPos i (L i).length) t' o' ∧
        ORepAt i o o' := by
      intro τ hR
      obtain ⟨tb, ob, htb, hexb, hrb⟩ := ihb.1 τ hR
      cases ob with
      | stop _ _ => exact hrb.elim
      | cont τ₁ =>
        obtain ⟨tr, o', htr, hexr, hr⟩ := ihr.2 i c p rfl τ₁ hrb
        refine ⟨((2 * (L i).length + 1) + (tb + (2 * (L₁ i).length + 4))) + 1 + tr, o', ?_,
          Exec.loopC (lc_tfits hR hB i (Nat.le_succ _)) (by rw [read_last i hR]; exact hc)
            (Exec.seqC (goHome_spec i hR hB (Nat.le_succ _)) (Exec.seqC hexb (goLast_spec i hrb hB₁))) hexr, hr⟩
        have := hB i; have := hB₁ i
        simp only [lcost, Nat.add_mul, Nat.one_mul] at htb htr ⊢; omega
    refine ⟨fun τ hR => ?_, fun i' c' body he τ hR => ?_⟩
    · obtain ⟨t', o', ht', hex, hr⟩ := inner τ hR
      cases o with
      | cont L' =>
        cases o' with
        | stop _ _ => exact hr.elim
        | cont τ₁ =>
          obtain ⟨τ₂, hR₂, rfl⟩ := hr
          have hB' := hQ _ (hrest.q_end L' (Or.inl rfl))
          refine ⟨(2 * (L i).length + 4) + (t' + (2 * (L' i).length + 1)), _, ?_,
            Exec.seqC (goLast_spec i hR hB) (Exec.seqC hex (goHome_spec i hR₂ hB' (Nat.le_succ _))), hR₂⟩
          have := hB i; have := hB' i
          simp only [lcost] at ht' ⊢; omega
      | stop b L' =>
        cases o' with
        | cont _ => exact hr.elim
        | stop b' τ₁ =>
          obtain ⟨rfl, hR₂⟩ := hr
          refine ⟨(2 * (L i).length + 4) + t', _, ?_,
            Exec.seqC (goLast_spec i hR hB) (Exec.seqS hex), rfl, hR₂⟩
          have := hB i
          simp only [lcost] at ht' ⊢; omega
    · cases he; exact inner τ hR
  | @loopS i c p L L₁ t₁ b hq hc hbody ihb =>
    have hB := hQ _ hq
    have inner : ∀ τ, Rep L τ → ∃ t' o', t' + 4 * B + 6 ≤ (t₁ + 1) * lcost B ∧
        Exec (TFits B) (.loop (fun r => c (r i)) (loopBody i p)) (τ.setPos i (L i).length) t' o' ∧
        ORepAt i (.stop b L₁) o' := by
      intro τ hR
      obtain ⟨tb, ob, htb, hexb, hrb⟩ := ihb.1 τ hR
      cases ob with
      | cont _ => exact hrb.elim
      | stop b' τ₁ =>
        obtain ⟨rfl, hR₁⟩ := hrb
        refine ⟨((2 * (L i).length + 1) + tb) + 1, _, ?_,
          Exec.loopS (lc_tfits hR hB i (Nat.le_succ _)) (by rw [read_last i hR]; exact hc)
            (Exec.seqC (goHome_spec i hR hB (Nat.le_succ _)) (Exec.seqS hexb)), rfl, hR₁⟩
        have := hB i
        simp only [lcost, Nat.add_mul, Nat.one_mul] at htb ⊢; omega
    refine ⟨fun τ hR => ?_, fun i' c' body he τ hR => ?_⟩
    · obtain ⟨t', o', ht', hex, hr⟩ := inner τ hR
      cases o' with
      | cont _ => exact hr.elim
      | stop b' τ₁ =>
        obtain ⟨rfl, hR₂⟩ := hr
        refine ⟨(2 * (L i).length + 4) + t', _, ?_,
          Exec.seqC (goLast_spec i hR hB) (Exec.seqS hex), rfl, hR₂⟩
        have := hB i
        simp only [lcost] at ht' ⊢; omega
    · cases he; exact inner τ hR

end Complexity
