import PalPeg.GalilDpDensity
import PalPeg.PhysicalProgramErase
import PalPeg.GalilScaffoldPreload

/-! Supply the finite eraser's density and size premises from actual scheduled
DP runs, including pauses, early cancellation and calls after halt. -/
set_option autoImplicit false
namespace PalPeg.PhysicalDpDensity
open GalilFppWide GalilFppFrontier
open PhysicalEncoding PhysicalProgramErase
open PalPeg.Program (STape)

theorem list_of_shape (xs : List (Fin 9)) (n : ℕ) (hs : Shape (GalilScaffoldTape.read xs) n) :
    ∃ body r, body.length = n ∧ (6 : Fin 9) ∉ body ∧ xs = body ++ List.replicate r 6 := by
  induction xs generalizing n with
  | nil =>
    have hz : n = 0 := by
      by_contra h
      exact hs.1 0 (by omega) rfl
    exact ⟨[],0,by simpa using hz.symm,by simp,rfl⟩
  | cons a xs ih =>
    cases n with
    | zero =>
      have ha : a = 6 := hs.2 0 (by omega)
      have ht : Shape (GalilScaffoldTape.read xs) 0 := ⟨by omega,fun k _ => hs.2 (k+1) (by omega)⟩
      obtain ⟨body,r,hb,_,he⟩ := ih 0 ht
      have hn : body = [] := List.length_eq_zero_iff.mp hb
      subst body
      exact ⟨[],r+1,rfl,by simp,by simp [ha,he,List.replicate_succ]⟩
    | succ n =>
      have ha : a ≠ 6 := hs.1 0 (by omega)
      have ht : Shape (GalilScaffoldTape.read xs) n :=
        ⟨fun k hk => hs.1 (k+1) (by omega),fun k hk => hs.2 (k+1) (by omega)⟩
      obtain ⟨body,r,hb,hd,he⟩ := ih n ht
      exact ⟨a::body,r,by simp [hb],by simp [Ne.symm ha,hd],by simp [he]⟩

theorem dense_of_shape (t : GalilScaffoldTape.Tape) (n : ℕ)
    (hs : Shape (GalilScaffoldTape.denote t) n) : Dense (encTape t) := by
  obtain ⟨body,r,_,hd,he⟩ := list_of_shape (t.left.reverse ++ t.focus :: t.right) n hs
  exact ⟨body,r,hd,he⟩

theorem run_steps {n : ℕ} {code : List (Instruction n)}
    {x y : GalilScaffoldControl.Machine n} {bs : List Bool}
    (hr : GalilScaffoldControl.Run code x bs y) :
    ∃ qs, Steps code (GalilScaffoldProgram.denote x.config) qs
      (GalilScaffoldProgram.denote y.config) := by
  induction hr with
  | nil => exact ⟨[],.nil _⟩
  | cons x y z b bs ht hr ih =>
    obtain ⟨qs,hqs⟩ := ih
    cases ht with
    | idle => exact ⟨qs,hqs⟩
    | halt => exact ⟨qs,hqs⟩
    | execute x y i hi he =>
      exact ⟨_,.step _ _ _ _ _ hi (GalilScaffoldProgram.execute_sound he) hqs⟩

theorem dense_onRun (w : List (Fin 3)) (lower : ℕ)
    {x : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : GalilScaffoldControl.Run GalilDpCode.code
      ⟨GalilScaffoldPreload.initial w lower,false⟩ bs x) :
    ∀ t, Dense (encTape (x.config.tapes t)) := by
  obtain ⟨qs,hqs⟩ := run_steps hr
  rw [GalilScaffoldPreload.initial_denote] at hqs
  intro t
  obtain ⟨n,hn⟩ := GalilDpDensity.onRun w lower hqs t
  exact dense_of_shape (x.config.tapes t) n hn

theorem dense_fpp_onRun (w : List (Fin 3))
    {x : GalilScaffoldControl.Machine 9} {bs : List Bool}
    (hr : GalilScaffoldControl.Run GalilFppMarkedCode.code
      ⟨GalilScaffoldChainInputSupply.fppInitial w,false⟩ bs x) :
    ∀ t, Dense (encTape (x.config.tapes t)) := by
  obtain ⟨qs,hqs⟩ := run_steps hr
  rw [GalilScaffoldChainInputSupply.fppInitial_denote] at hqs
  intro t
  obtain ⟨n,hn⟩ := GalilDpDensity.fpp_onRun w hqs t
  exact dense_of_shape (x.config.tapes t) n hn

def size (t : GalilScaffoldTape.Tape) : ℕ := t.left.length+t.right.length

theorem size_right (t : GalilScaffoldTape.Tape) : size (GalilScaffoldTape.moveRight t) ≤ size t+1 := by
  cases t with
  | mk l a r => cases r <;> simp [size,GalilScaffoldTape.moveRight]; omega

theorem size_left (t : GalilScaffoldTape.Tape) : size (GalilScaffoldTape.moveLeft t) ≤ size t+1 := by
  cases t with
  | mk l a r => cases l <;> simp [size,GalilScaffoldTape.moveLeft]; omega

theorem execute_size {n : ℕ} {i : Instruction n} {x y : GalilScaffoldProgram.Config n}
    (he : GalilScaffoldProgram.Execute i x y) (t : Fin n) : size (y.tapes t) ≤ size (x.tapes t)+1 := by
  cases he with
  | right x j q =>
    by_cases ht : t = j
    · subst t; simpa [GalilScaffoldProgram.changed] using size_right (x.tapes j)
    · simp [GalilScaffoldProgram.changed,ht]
  | left x j q hp =>
    by_cases ht : t = j
    · subst t; simpa [GalilScaffoldProgram.changed] using size_left (x.tapes j)
    · simp [GalilScaffoldProgram.changed,ht]
  | write x j s q =>
    by_cases ht : t = j <;> simp [GalilScaffoldProgram.changed,ht,size,GalilScaffoldTape.write]
  | read => simp

theorem tick_size {n : ℕ} {code : List (Instruction n)}
    {x y : GalilScaffoldControl.Machine n} {b : Bool}
    (hr : GalilScaffoldControl.Tick code b x y) (t : Fin n) :
    size (y.config.tapes t) ≤ size (x.config.tapes t)+(if b then 1 else 0) := by
  cases hr with
  | idle => split <;> omega
  | halt => simp
  | execute x y i hi he => exact execute_size he t

theorem run_size {n : ℕ} {code : List (Instruction n)}
    {x y : GalilScaffoldControl.Machine n} {bs : List Bool}
    (hr : GalilScaffoldControl.Run code x bs y) (t : Fin n) :
    size (y.config.tapes t) ≤ size (x.config.tapes t)+bs.count true := by
  induction hr with
  | nil => simp
  | cons x y z b bs ht hr ih =>
    have hh := tick_size ht t
    cases b <;> simp at * <;> omega

theorem initial_size (w : List (Fin 3)) (lower : ℕ) (t : Fin 12) :
    size ((GalilScaffoldPreload.initial w lower).tapes t) ≤ max (w.length+1) (lower+1) := by
  by_cases h7 : t = 7
  · simp [GalilScaffoldPreload.initial,h7,size,GalilScaffoldPreload.bounded]
  · by_cases h10 : t = 10
    · simp [GalilScaffoldPreload.initial,h10,size,GalilScaffoldPreload.bounded]
    · simp [GalilScaffoldPreload.initial,h7,h10,size,GalilScaffoldTape.reset]

/-- The deadline is now expressed using the original preload and the actual
enabled-call count. Its availability before reuse remains a scheduling duty. -/
theorem bank_reset_onRun (w : List (Fin 3)) (lower n steps : ℕ)
    {x : GalilScaffoldControl.Machine 12} {bs : List Bool}
    (hr : GalilScaffoldControl.Run GalilDpCode.code
      ⟨GalilScaffoldPreload.initial w lower,false⟩ bs x)
    {fb db : ℕ} (p : Control fb db × (Fin tapeCountM → STape Γm))
    (he : Stored n (fun i => (.rewind, encTape (x.config.tapes i))) p)
    (htime : 3*(max (w.length+1) (lower+1)+bs.count true)+5 ≤ steps) :
    let result := sweepRun steps p
    (∀ i, result.1.2 i = .done) ∧ ∀ i,
      CloseoutCoreEnc12.TEqG blankM (padLeft n (mapTape encProg (STape.blankTape 6)))
        (result.2 (slotIndex (dpSlotOf (!result.1.1.dpLive) i))) := by
  apply bank_real_reset n steps (fun i => encTape (x.config.tapes i)) p he (dense_onRun w lower hr)
  intro i
  have hs := run_size hr i
  have hi := initial_size w lower i
  change size (x.config.tapes i) ≤ size ((GalilScaffoldPreload.initial w lower).tapes i)+bs.count true at hs
  change 3*(size (x.config.tapes i))+5 ≤ steps
  omega

/-- info: 'PalPeg.PhysicalDpDensity.dense_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dense_onRun

/-- info: 'PalPeg.PhysicalDpDensity.dense_fpp_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dense_fpp_onRun

/-- info: 'PalPeg.PhysicalDpDensity.bank_reset_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bank_reset_onRun

end PalPeg.PhysicalDpDensity
