import Shallot.Peg.Packrat.Machine.Sweep

/-!
# Transfer next rows into old rows

Clear an old row, move the next row through an empty scratch stack, and
move it back in position order. Both the next row and scratch are empty
at the end, so the same storage can be reused in the following round.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Replace a destination stack with a source stack, preserving order. -/
def replaceRow (src dst tmp : Fin K) (hst : src ≠ tmp) (htd : tmp ≠ dst) : NProg K :=
  .seq (nclr dst) (.seq (nmvAll src tmp hst) (nmvAll tmp dst htd))

theorem nruns_replaceRow (src dst tmp : Fin K) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hsd : src ≠ dst) (S : Lists K) (hT : S tmp = []) :
    NRuns (replaceRow src dst tmp hst htd) S ((S.set dst (S src)).set src [])
      (2 * (S dst).length + 6 * (S src).length + 3) := by
  have cl := nruns_clr dst S
  let S₁ := S.set dst []
  have mv₁ := nruns_mvAll src tmp hst S₁
  have hs₁ : S₁ src = S src := Lists.set_ne _ _ hsd
  have ht₁ : S₁ tmp = [] := by simp only [S₁, Lists.set_ne _ _ htd]; exact hT
  simp only [hs₁, ht₁, List.nil_append] at mv₁
  let S₂ := (S₁.set tmp (S src).reverse).set src []
  have mv₂ := nruns_mvAll tmp dst htd S₂
  have ht₂ : S₂ tmp = (S src).reverse := by simp only [S₂]; lists_at
  have hd₂ : S₂ dst = [] := by simp only [S₂, S₁]; lists_at
  simp only [ht₂, hd₂, List.nil_append, List.reverse_reverse, List.length_reverse] at mv₂
  have he : (S₂.set dst (S src)).set tmp [] = (S.set dst (S src)).set src [] := by
    simp only [S₂, S₁]; lists_eq
  rw [he] at mv₂
  exact (cl.seq (mv₁.seq mv₂)).mono (by omega)

@[simp] theorem oldR_inj (g : Grammar) (a b : Node g) : oldR g a = oldR g b ↔ a = b := by
  constructor
  · intro h; apply Fin.ext; have hh := congrArg Fin.val h; simp only [oldR] at hh; omega
  · intro h; cases h; rfl

theorem old_next_ne (g : Grammar) (a b : Node g) : oldR g a ≠ nextR g b := by
  intro h
  have hh := congrArg Fin.val h
  simp only [oldR, nextR] at hh
  have := a.isLt
  omega

def transferRows (g : Grammar) : List (Node g) → NProg (NK g)
  | [] => nskip (tmpR g)
  | j :: js => .seq (replaceRow (nextR g j) (oldR g j) (tmpR g) (by packrat_regs) (by packrat_regs))
      (transferRows g js)

/-- Transfer a list of distinct rows, preserving every other register. -/
theorem nruns_transferRows (g : Grammar) (js : List (Node g)) (hn : js.Nodup)
    (N : Nat) (R : Node g → List Nat) (S : Lists (NK g)) (hT : S (tmpR g) = [])
    (hOld : ∀ j ∈ js, (S (oldR g j)).length ≤ N + 1)
    (hNext : ∀ j ∈ js, S (nextR g j) = R j) (hLen : ∀ j ∈ js, (R j).length = N + 1) :
    ∃ S', NRuns (transferRows g js) S S' (js.length * (8 * N + 11) + 2) ∧
      (∀ j ∈ js, S' (oldR g j) = R j ∧ S' (nextR g j) = []) ∧
      (∀ r, (∀ j ∈ js, r ≠ oldR g j ∧ r ≠ nextR g j) → S' r = S r) := by
  induction js generalizing S with
  | nil =>
    refine ⟨S, ?_, by simp, by simp⟩
    simpa only [transferRows, List.length_nil, Nat.zero_mul, Nat.zero_add] using nruns_skip (tmpR g) S
  | cons j js ih =>
    obtain ⟨hj, hjs⟩ := List.nodup_cons.mp hn
    have rx := nruns_replaceRow (nextR g j) (oldR g j) (tmpR g)
      (by packrat_regs) (by packrat_regs) (Ne.symm (old_next_ne g j j)) S hT
    let S₁ := (S.set (oldR g j) (R j)).set (nextR g j) []
    rw [hNext j List.mem_cons_self] at rx
    have hS₁ : ∀ r, r ≠ oldR g j → r ≠ nextR g j → S₁ r = S r := by
      intro r hro hrn; simp only [S₁, Lists.set_ne _ _ hrn, Lists.set_ne _ _ hro]
    have haway : ∀ k ∈ js, oldR g k ≠ oldR g j ∧ nextR g k ≠ nextR g j := by
      intro k hk
      have hkne : k ≠ j := by intro he; exact hj (he ▸ hk)
      exact ⟨fun he => hkne ((oldR_inj g k j).mp he), fun he => hkne ((nextR_inj g k j).mp he)⟩
    obtain ⟨S', tx, ht, hf⟩ := ih hjs S₁
      (by rw [hS₁ (tmpR g) (by packrat_regs) (by packrat_regs)]; exact hT)
      (fun k hk => by rw [hS₁ _ (haway k hk).1 (by packrat_regs)]; exact hOld k (List.mem_cons_of_mem _ hk))
      (fun k hk => by rw [hS₁ _ (by packrat_regs) (haway k hk).2]; exact hNext k (List.mem_cons_of_mem _ hk))
      (fun k hk => hLen k (List.mem_cons_of_mem _ hk))
    refine ⟨S', (rx.seq tx).mono ?_, ?_, ?_⟩
    · have ho := hOld j List.mem_cons_self
      have hl := hLen j List.mem_cons_self
      simp only [List.length_cons, Nat.succ_mul]
      omega
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · constructor
        · rw [hf _ (fun a ha => ⟨Ne.symm (haway a ha).1, by packrat_regs⟩)]
          simp [S₁, Lists.set_ne _ _ (old_next_ne g k k)]
        · rw [hf _ (fun a ha => ⟨by packrat_regs, Ne.symm (haway a ha).2⟩)]
          simp [S₁]
      · exact ht k hk
    · intro r hr
      rw [hf r (fun k hk => hr k (List.mem_cons_of_mem _ hk)), hS₁ r (hr j List.mem_cons_self).1
        (hr j List.mem_cons_self).2]

/-- Transfer every next row. -/
def transfer (g : Grammar) : NProg (NK g) := transferRows g (List.finRange (dom g).length)

end Shallot.Packrat.Machine
