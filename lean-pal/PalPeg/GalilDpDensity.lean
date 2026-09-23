import PalPeg.GalilDpDenseMarks
import PalPeg.GalilDpDensityTable

/-! Density at every successful prefix of the actual twelve-tape DP code.
The finite table is only a checked control-flow certificate. Its soundness
below uses the actual tape semantics and, at emit, the proved MARKS bound. -/
set_option autoImplicit false
namespace PalPeg.GalilDpDensity
open GalilFppWide GalilFppFrontier GalilDpDensityTable

def Holds (b : Band) (n p : ℕ) : Prop := match b.val with
  | 0 => n < p | 1 => n = p | 2 => n = p+1 | _ => p+2 ≤ n

theorem read_sound {tape : ℕ → Fin 9} {n p : ℕ} (hs : Shape tape n)
    (b : Band) (hb : Holds b n p) : readBand (tape p) b = true := by
  have hh : tape p = 6 ↔ n ≤ p := by
    constructor
    · intro h
      by_contra hlt
      exact hs.1 p (by omega) h
    · exact hs.2 p
  unfold readBand
  apply decide_eq_true
  rw [hh]
  fin_cases b <;> simp [Holds] at hb ⊢ <;> omega

theorem move_sound (b : Band) (n p : ℕ) (right : Bool) (hb : Holds b n p)
    (hp : right = false → 0 < p) :
    ∃ c ∈ moveBands right b, Holds c n (if right then p+1 else p-1) := by
  cases right
  · have hp' := hp rfl
    fin_cases b
    · by_cases he : p = n+1
      · exact ⟨1, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
      · exact ⟨0, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨2, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨3, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨3, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
  · fin_cases b
    · exact ⟨0, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨0, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨1, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
    · by_cases he : n = p+2
      · exact ⟨2, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩
      · exact ⟨3, by simp [moveBands], by simp [Holds] at hb ⊢; omega⟩

theorem erase_shape (tape : ℕ → Fin 9) (n p : ℕ) (hs : Shape tape n) (hp : n ≤ p+1) :
    Shape (Function.update tape p 6) (min n p) := by
  constructor
  · intro k hk
    rw [Function.update_of_ne (show k ≠ p by omega)]
    exact hs.1 k (by omega)
  · intro k hk
    by_cases he : k = p
    · simp [he]
    · rw [Function.update_of_ne he]
      exact hs.2 k (by omega)

def WriteSafe (s : Fin 9) (n p : ℕ) : Prop :=
  (s = 6 → n ≤ p+1) ∧ (s ≠ 6 → p ≤ n)

theorem write_sound (tape : ℕ → Fin 9) (n p : ℕ) (s : Fin 9) (b : Band)
    (hs : Shape tape n) (hb : Holds b n p) (hw : WriteSafe s n p) :
    ∃ m c, c ∈ writeBands s b ∧ Shape (Function.update tape p s) m ∧ Holds c m p := by
  by_cases hz : s = 6
  · subst s
    have hshape := erase_shape tape n p hs (hw.1 rfl)
    have hp := hw.1 rfl
    fin_cases b
    · exact ⟨min n p,0,by simp [writeBands],hshape,by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨min n p,1,by simp [writeBands],hshape,by simp [Holds] at hb ⊢; omega⟩
    · exact ⟨min n p,1,by simp [writeBands],hshape,by simp [Holds] at hb ⊢; omega⟩
    · simp [Holds] at hb; omega
  · have hp := hw.2 hz
    have hshape := write_shape tape n p s hs hp hz
    fin_cases b
    · simp [Holds] at hb; omega
    · refine ⟨n+1,2,by simp [writeBands,hz],?_,?_⟩
      · simpa [show p = n by simpa [Holds] using hb.symm] using hshape
      · simp [Holds] at hb ⊢; omega
    · refine ⟨n,2,by simp [writeBands,hz],?_,hb⟩
      simpa [show p ≠ n by simp [Holds] at hb; omega] using hshape
    · refine ⟨n,3,by simp [writeBands,hz],?_,hb⟩
      simpa [show p ≠ n by simp [Holds] at hb; omega] using hshape

theorem legal_write (w : List (Fin 3)) (lower : ℕ) {x : Config 12} {qs : List ℕ}
    (hx : Steps GalilDpCode.code (GalilDpPrepared.initial w lower) qs x)
    (t : Fin 12) (s : Fin 9) (q n : ℕ) (b : Band)
    (hi : GalilDpCode.code[x.pc]? = some (.write t s q))
    (hs : Shape (x.tape t) n) (hb : Holds b n (x.pos t))
    (ha : allowed x.pc t b = true) : WriteSafe s n (x.pos t) := by
  by_cases hp : x.pc = 36 ∨ x.pc = 321
  · have he : s = 8 := by
      rcases hp with h | h
      · rw [h] at hi
        have hr : GalilDpCode.code[36]? = some (.write 8 8 321) := rfl
        rw [hr] at hi; cases hi; rfl
      · rw [h] at hi
        have hr : GalilDpCode.code[321]? = some (.write 9 8 28) := rfl
        rw [hr] at hi; cases hi; rfl
    subst s
    have hin := GalilDpDenseMarks.emit_inside w lower hx t q hi hp n hs
    exact ⟨by intro h; contradiction, fun _ => Nat.le_of_lt hin⟩
  · have h := (lookup hi t b ha).1
    have hsafe : (s = 6 ∧ b.val ≠ 3) ∨ (s ≠ 6 ∧ b.val ≠ 0) := by
      have h36 : x.pc ≠ 36 := fun h => hp (Or.inl h)
      have h321 : x.pc ≠ 321 := fun h => hp (Or.inr h)
      simpa [safe,h36,h321] using h
    constructor
    · intro hz
      have hne : b.val ≠ 3 := (hsafe.resolve_right (by simp [hz])).2
      fin_cases b <;> simp [Holds] at hb <;> simp_all; omega
    · intro hz
      have hne : b.val ≠ 0 := (hsafe.resolve_left (by simp [hz])).2
      fin_cases b <;> simp [Holds] at hb <;> simp_all; omega

def Inv (x : Config 12) : Prop := ∀ t, ∃ n b,
  Shape (x.tape t) n ∧ Holds b n (x.pos t) ∧ allowed x.pc t b = true

theorem step (w : List (Fin 3)) (lower : ℕ) {x y : Config 12} {qs : List ℕ}
    (hx : Steps GalilDpCode.code (GalilDpPrepared.initial w lower) qs x)
    {i : Instruction 12} (hi : GalilDpCode.code[x.pc]? = some i)
    (he : Execute i x y) (hinv : Inv x) : Inv y := by
  intro t
  obtain ⟨n,b,hs,hb,ha⟩ := hinv t
  have hg := (lookup hi t b ha).2
  cases he with
  | right x j q =>
    by_cases ht : j = t
    · subst j
      obtain ⟨c,hc,hcb⟩ := move_sound b n (x.pos t) true hb (by simp)
      refine ⟨n,c,hs,by simpa using hcb,?_⟩
      exact hg (q,c) (by simpa [transfers] using hc)
    · refine ⟨n,b,hs,by simpa [Ne.symm ht] using hb,?_⟩
      exact hg (q,b) (by simp [transfers,ht])
  | left x j q hp =>
    by_cases ht : j = t
    · subst j
      obtain ⟨c,hc,hcb⟩ := move_sound b n (x.pos t) false hb (fun _ => hp)
      refine ⟨n,c,hs,by simpa using hcb,?_⟩
      exact hg (q,c) (by simpa [transfers] using hc)
    · refine ⟨n,b,hs,by simpa [Ne.symm ht] using hb,?_⟩
      exact hg (q,b) (by simp [transfers,ht])
  | write x j s q =>
    by_cases ht : j = t
    · subst j
      obtain ⟨m,c,hc,hshape,hcb⟩ := write_sound (x.tape t) n (x.pos t) s b hs hb
        (legal_write w lower hx t s q n b hi hs hb ha)
      refine ⟨m,c,by simpa using hshape,hcb,?_⟩
      exact hg (q,c) (by simpa [transfers] using hc)
    · refine ⟨n,b,by simpa [Ne.symm ht] using hs,hb,?_⟩
      exact hg (q,b) (by simp [transfers,ht])
  | read x j cs q hq =>
    refine ⟨n,b,hs,hb,?_⟩
    apply hg (q,b)
    apply List.mem_map.mpr
    refine ⟨(x.tape j (x.pos j),q),List.mem_filter.mpr ⟨hq,?_⟩,rfl⟩
    by_cases ht : j = t
    · subst j
      simp [read_sound hs b hb]
    · simp [ht]

theorem input_shape (w : List (Fin 4)) :
    Shape (GalilFppInputWord.inputTape w) (w.length+2) := by
  constructor
  · intro k hk
    by_cases hz : k = 0
    · simp [hz, GalilFppInputWord.inputTape]
    · by_cases he : k = w.length+1
      · simp [he, GalilFppInputWord.input_end]
      · have hlt : k-1 < w.length := by omega
        have hread := GalilFppInputWord.input_next w (k-1) hlt
        rw [show k-1+1 = k by omega] at hread
        rw [hread]
        exact (by decide : ∀ a : Fin 4, GalilFppRetry.letter a ≠ 6) _
  · intro k hk
    simp [GalilFppInputWord.inputTape, show k ≠ 0 by omega,
      List.getElem?_eq_none_iff.mpr (show w.length ≤ k-1 by omega), show k ≠ w.length+1 by omega]

theorem lower_shape (lower : ℕ) : Shape (GalilDpPrepared.lowerTape lower) (lower+2) := by
  constructor
  · intro k hk
    unfold GalilDpPrepared.lowerTape
    split_ifs <;> (try decide); omega
  · intro k hk
    simp [GalilDpPrepared.lowerTape, show k ≠ 0 by omega,
      show ¬ k ≤ lower by omega, show k ≠ lower+1 by omega]

theorem initial_allowed : ∀ t : Fin 12,
    allowed 320 t (if t = 7 ∨ t = 10 then 3 else 1) = true := by decide

theorem initial (w : List (Fin 3)) (lower : ℕ) : Inv (GalilDpPrepared.initial w lower) := by
  intro t
  have ha := initial_allowed t
  by_cases h7 : t = 7
  · subst t
    refine ⟨w.length+2,3,?_,by simp [Holds,GalilDpPrepared.initial],by simpa [GalilDpPrepared.initial] using ha⟩
    simpa [GalilDpPrepared.initial, GalilFppPrepareCopy.source] using
      input_shape (w.map GalilFppPrepareCopy.embed)
  · by_cases h10 : t = 10
    · subst t
      refine ⟨lower+2,3,?_,by simp [Holds,GalilDpPrepared.initial],by simpa [GalilDpPrepared.initial] using ha⟩
      simpa [GalilDpPrepared.initial] using lower_shape lower
    · refine ⟨0,1,?_,rfl,?_⟩
      · simp only [GalilDpPrepared.initial,h7,h10,if_false,Shape]
        exact ⟨by omega,fun _ _ => trivial⟩
      · simpa [GalilDpPrepared.initial,h7,h10] using ha

theorem run (w : List (Fin 3)) (lower : ℕ) {x y : Config 12} {qs rs : List ℕ}
    (hx : Steps GalilDpCode.code (GalilDpPrepared.initial w lower) qs x)
    (hinv : Inv x) (hr : Steps GalilDpCode.code x rs y) : Inv y := by
  induction hr generalizing qs with
  | nil => exact hinv
  | step x y z i rs hi he hr ih =>
    exact ih (steps_append hx (.step _ _ _ _ [] hi he (.nil _))) (step w lower hx hi he hinv)

/-- All twelve tapes, at every successful prefix, with no density premise. -/
theorem onRun (w : List (Fin 3)) (lower : ℕ) {x : Config 12} {qs : List ℕ}
    (hx : Steps GalilDpCode.code (GalilDpPrepared.initial w lower) qs x) :
    ∀ t, ∃ n, Shape (x.tape t) n := by
  have h := run w lower (.nil _) (initial w lower) hx
  intro t
  obtain ⟨n,b,hs,_⟩ := h t
  exact ⟨n,hs⟩

/-- The existing FPP-to-DP simulation transports the same invariant back
to all nine FPP tapes, with no second instruction-table certificate. -/
theorem fpp_onRun (w : List (Fin 3)) {x : Config 9} {qs : List ℕ}
    (hx : Steps GalilFppMarkedCode.code (GalilFppPrepareInit.initial w) qs x) :
    ∀ t, ∃ n, Shape (x.tape t) n := by
  obtain ⟨y,rs,hr,_,hrep⟩ := GalilDpSimulation.steps hx (GalilDpPrepared.initial w 0)
    (GalilDpPrepared.initial_related w 0)
  intro t
  obtain ⟨n,hn⟩ := onRun w 0 hr (GalilDpTransform.tapeIndex t)
  rw [hrep.tape t] at hn
  exact ⟨n,hn⟩

/-- info: 'PalPeg.GalilDpDensity.onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms onRun

/-- info: 'PalPeg.GalilDpDensity.fpp_onRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fpp_onRun

end PalPeg.GalilDpDensity
