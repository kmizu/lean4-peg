import PalPeg.GalilScaffoldChainSweep

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainVerifyRun
open GalilScaffoldChainVerifier GalilScaffoldInputHead

/-- A supplied word is witnessed by the same successive legal right moves,
not by a separate oracle of characters. Queue contents remain decoded. -/
inductive Reads : PlaceHead → List (Fin 3) → PlaceHead → Prop
  | stop (p) : Reads p [] p
  | next (p a) {xs q} (hp : canRight p) (ha : read (right p) = some a)
      (hr : Reads (right p) xs q) : Reads p (a :: xs) q

/-- Enabled consume calls with the actual verifier. Outer clock/lag guards
must separately justify when these calls are scheduled. -/
inductive Run : State → ℕ → State → Prop
  | stop (s) : Run s 0 s
  | next (s) {n t} (hp : canRight s.verifier) (hr : Run (consume s) n t) : Run s (n+1) t

theorem realize {p xs q} (hr : Reads p xs q) (control : GalilScaffoldChainConsume.State) :
    Run ⟨p,control⟩ xs.length ⟨q,GalilScaffoldChainSweep.run control xs⟩ := by
  induction hr generalizing control with
  | stop p => exact Run.stop _
  | next p a hp ha hr ih =>
    apply Run.next _ hp
    simpa [consume, ha, GalilScaffoldChainSweep.run] using
      ih (GalilScaffoldChainConsume.consume control (some a))

theorem reads_append {p xs q ys r} (h1 : Reads p xs q) (h2 : Reads q ys r) :
    Reads p (xs ++ ys) r := by
  induction h1 with
  | stop p => exact h2
  | next p a hp ha hr ih => exact Reads.next p a hp ha (ih h2)

/-- Two successful bounces now describe the final controller of the same
verifier execution, including every input-head right assertion. -/
theorem four_boundaries (center b : Fin 3) (xs : List (Fin 3))
    (p q : PlaceHead)
    (hr : Reads p (GalilScaffoldChainSweep.bounce center b xs ++
      GalilScaffoldChainSweep.bounce center b xs) q) :
    ∃ t, Run ⟨p,GalilScaffoldChainConsume.ready center xs b⟩ (4*(xs.length+1)) t ∧
      t.verifier = q ∧
      t.control.period = (GalilScaffoldChainConsume.ready center xs b).period ∧
      GalilScaffoldCounter.value t.control.distance = 4*(xs.length+1) ∧
      GalilScaffoldCounter.value t.control.boundary = 4*(xs.length+1) ∧
      GalilScaffoldCounter.value t.control.last = 3*(xs.length+1) ∧
      t.control.phase = 4 ∧ t.control.forward = true ∧ t.control.broken = false := by
  have he := realize hr (GalilScaffoldChainConsume.ready center xs b)
  have hl : (GalilScaffoldChainSweep.bounce center b xs ++
      GalilScaffoldChainSweep.bounce center b xs).length = 4*(xs.length+1) := by
    simp [GalilScaffoldChainSweep.bounce]; omega
  rw [hl] at he
  exact ⟨_,he,rfl,GalilScaffoldChainSweep.four_boundaries center b xs⟩

def pairs : List (Fin 2) → List (Fin 3)
  | [] => []
  | a :: xs => 2 :: GalilScaffoldPlace.letter a :: pairs xs

/-- Concrete right-stack contents supply the interleaved gap/letter word;
no read-equality hypotheses are needed for its individual steps. -/
theorem stack_supply (xs : List (Fin 2)) (a : Fin 2)
    (ls rs : List (Option (Fin 2))) (qs : List (Fin 2)) :
    ∃ q, Reads ⟨⟨some a,ls,xs.map some ++ rs,qs⟩,false⟩ (pairs xs) q ∧
      q.head.right = rs ∧ q.head.incoming = qs ∧ q.gap = false := by
  induction xs generalizing a ls with
  | nil => exact ⟨_,Reads.stop _,rfl,rfl,rfl⟩
  | cons b xs ih =>
    obtain ⟨q,hr,hrs,hqs,hgap⟩ := ih b (some a :: ls)
    refine ⟨q,?_,hrs,hqs,hgap⟩
    apply Reads.next _ 2 (Or.inl rfl) rfl
    apply Reads.next _ (GalilScaffoldPlace.letter b)
    · right; left; simp [right]
    · rfl
    · exact hr

/-- With an empty right stack, the same word is supplied by the FIFO,
and the unused queue suffix is preserved. -/
theorem queue_supply (xs : List (Fin 2)) (a : Fin 2)
    (ls : List (Option (Fin 2))) (qs : List (Fin 2)) :
    ∃ q, Reads ⟨⟨some a,ls,[],xs ++ qs⟩,false⟩ (pairs xs) q ∧
      q.head.right = [] ∧ q.head.incoming = qs ∧ q.gap = false := by
  induction xs generalizing a ls with
  | nil => exact ⟨_,Reads.stop _,rfl,rfl,rfl⟩
  | cons b xs ih =>
    obtain ⟨q,hr,hrs,hqs,hgap⟩ := ih b (some a :: ls)
    refine ⟨q,?_,hrs,hqs,hgap⟩
    apply Reads.next _ 2 (Or.inl rfl) rfl
    apply Reads.next _ (GalilScaffoldPlace.letter b)
    · right; right; simp [right]
    · rfl
    · exact hr

#print axioms stack_supply
#print axioms queue_supply
#print axioms four_boundaries
#print axioms realize
end PalPeg.GalilScaffoldChainVerifyRun
