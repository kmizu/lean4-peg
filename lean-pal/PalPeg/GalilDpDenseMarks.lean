import PalPeg.GalilDpCost
import PalPeg.GalilFppFrontier

/-! The two MARKS heads may pass their blank frontier while the kernel walks
the longer prepared word. Their writes still stay inside the dense prefix:
the existing completed preparation supplies the final sentinel and blank
suffix, and the output phase only overwrites MARKS cells with 8. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpDenseMarks
open GalilFppWide GalilDpFrames

theorem steps_compare {x y z : Config 12} {qs rs : List ℕ}
    (hy : Steps GalilDpCode.code x qs y) (hz : Steps GalilDpCode.code x rs z) :
    (∃ us, Steps GalilDpCode.code y us z) ∨ (∃ us, Steps GalilDpCode.code z us y) := by
  induction hy generalizing rs z with
  | nil => exact Or.inl ⟨_,hz⟩
  | step x y z i qs hi he hs ih =>
    cases hz with
    | nil => exact Or.inr ⟨_, .step _ _ _ _ _ hi he hs⟩
    | step _ y' z' i' rs hi' he' hs' =>
      have hei : i = i' := Option.some.inj (hi.symm.trans hi')
      subst i'
      have hey := GalilDpCost.execute_unique (GalilScaffoldNextPc.dp_wellFormed i
        (List.mem_of_getElem? hi)) he he'
      subst y'
      exact ih hs'

/-- Every actual prefix still in the kernel extends to the already proved
preparation result. Search cannot return to such a prefix. -/
theorem future_prepared (w : List (Fin 3)) (lower : ℕ) {x : Config 12} {qs : List ℕ}
    (hx : Steps GalilDpCode.code (GalilDpPrepared.initial w lower) qs x) (hp : x.pc < 346) :
    ∃ y rs, Steps GalilDpCode.code x rs y ∧ y.pc = 372 ∧
      y.tape 8 = GalilFppMarkedLayout.marks w ∧ y.tape 9 = GalilFppMarkedLayout.marks w := by
  obtain ⟨y, rs, hy, hpc, _, _, _, _, h8, h9, _⟩ := GalilDpPrepared.prepared w lower
  rcases steps_compare hx hy with ⟨us,hu⟩ | ⟨us,hu⟩
  · exact ⟨y,us,hu,hpc,h8,h9⟩
  · have hbad := (before_search hu hp).1
    omega

def outputRegion (q : ℕ) : Bool := decide (q ≤ 36 ∨ q = 228 ∨ q = 321 ∨ q = 322 ∨ 346 ≤ q)

def outputGuard (q : ℕ) (i : Instruction 12) : Bool :=
  !outputRegion q || ((successors i).all outputRegion && match i with
    | .write t s _ => decide ((t = 8 ∨ t = 9) → s = 8)
    | _ => true)

set_option maxHeartbeats 2000000 in
theorem output_rows : ∀ q : Fin 373,
    (GalilDpCode.code[q.val]?).map (outputGuard q.val) = some true := by decide

theorem output_lookup {q : ℕ} {i : Instruction 12}
    (hi : GalilDpCode.code[q]? = some i) : outputGuard q i = true := by
  have hb : q < 373 := (List.getElem?_eq_some_iff.mp hi).1
  have h := output_rows ⟨q,hb⟩
  simpa only [hi, Option.map_some, Option.some.injEq] using h

theorem output_step {x y : Config 12} {i : Instruction 12}
    (hi : GalilDpCode.code[x.pc]? = some i) (he : Execute i x y)
    (hr : outputRegion x.pc = true) : outputRegion y.pc = true ∧
      ∀ t : Fin 12, t = 8 ∨ t = 9 → ∀ k, y.tape t k = x.tape t k ∨ y.tape t k = 8 := by
  have hg := output_lookup hi
  simp only [outputGuard, hr, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hg
  refine ⟨List.all_eq_true.mp hg.1 _ (execute_successor he), ?_⟩
  intro t ht k
  cases he with
  | right => exact Or.inl rfl
  | left => exact Or.inl rfl
  | read => exact Or.inl rfl
  | write x j s q =>
    have hs : (j = 8 ∨ j = 9) → s = 8 := of_decide_eq_true hg.2
    by_cases hj : t = j
    · subst j
      by_cases hk : k = x.pos t
      · right; simp [hk, hs ht]
      · left; simp [hk]
    · left; simp [hj]

theorem output_cells {x y : Config 12} {qs : List ℕ}
    (hr : Steps GalilDpCode.code x qs y) (hp : outputRegion x.pc = true) :
    ∀ t : Fin 12, t = 8 ∨ t = 9 → ∀ k, y.tape t k = x.tape t k ∨ y.tape t k = 8 := by
  induction hr with
  | nil => exact fun _ _ _ => Or.inl rfl
  | step x y z i qs hi he hr ih =>
    obtain ⟨hy,hcell⟩ := output_step hi he hp
    intro t ht k
    rcases ih hy t ht k with h | h
    · rw [h]
      exact hcell t ht k
    · exact Or.inr h

/-- At either duplicated emit write, the current dense prefix already
contains the final END marker. The write itself cannot leave that prefix. -/
theorem emit_inside (w : List (Fin 3)) (lower : ℕ) {x : Config 12} {qs : List ℕ}
    (hx : Steps GalilDpCode.code (GalilDpPrepared.initial w lower) qs x)
    (t : Fin 12) (q : ℕ) (hi : GalilDpCode.code[x.pc]? = some (.write t 8 q))
    (hp : x.pc = 36 ∨ x.pc = 321) (n : ℕ) (hn : GalilFppFrontier.Shape (x.tape t) n) :
    x.pos t < n := by
  have ht : t = 8 ∨ t = 9 := by
    rcases hp with h | h
    · simp only [h] at hi
      have hrow : GalilDpCode.code[36]? = some (.write 8 8 321) := rfl
      rw [hrow] at hi
      cases hi
      exact Or.inl rfl
    · simp only [h] at hi
      have hrow : GalilDpCode.code[321]? = some (.write 9 8 28) := rfl
      rw [hrow] at hi
      cases hi
      exact Or.inr rfl
  have hr : outputRegion x.pc = true := by rcases hp with h | h <;> simp [outputRegion,h]
  obtain ⟨y,rs,hxy,hyPC,h8,h9⟩ := future_prepared w lower hx (by rcases hp with h | h <;> omega)
  have hyt : y.tape t = GalilFppMarkedLayout.marks w := by rcases ht with rfl | rfl <;> assumption
  have hend : x.tape t (w.length+1) = 5 := by
    have hh := output_cells hxy hr t ht (w.length+1)
    rw [hyt] at hh
    have he : GalilFppMarkedLayout.marks w (w.length+1) = 5 := by simp [GalilFppMarkedLayout.marks]
    rw [he] at hh
    rcases hh with hh | hh
    · exact hh.symm
    · contradiction
  have hlen : w.length+1 < n := by
    by_contra h
    have hz := hn.2 (w.length+1) (by omega)
    rw [hend] at hz
    contradiction
  cases hxy with
  | nil =>
    rcases hp with h | h <;> omega
  | step _ z _ j rs hj he hz =>
    have hji : j = .write t 8 q := Option.some.inj (hj.symm.trans hi)
    subst j
    cases he
    have hc := output_cells hz (output_step hi (.write _ _ _ _) hr).1 t ht (x.pos t)
    have hval : y.tape t (x.pos t) = 8 := by simpa using hc
    have hb : x.pos t ≤ w.length := by
      rw [hyt] at hval
      by_contra hh
      simp [GalilFppMarkedLayout.marks, show x.pos t ≠ 0 by omega,
        show ¬ x.pos t ≤ w.length by omega] at hval
      split_ifs at hval <;> contradiction
    omega

/-- info: 'PalPeg.GalilDpDenseMarks.future_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms future_prepared

/-- info: 'PalPeg.GalilDpDenseMarks.emit_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emit_inside

end PalPeg.GalilDpDenseMarks
