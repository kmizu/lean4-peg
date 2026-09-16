import Mathlib

set_option autoImplicit false
namespace PalPeg.GalilScaffoldPrepareClock

/-- Decoded preparation modes with remaining work/head distance. The copy
length m is the actual number copied, not automatically the requested span. -/
inductive Phase
  | grow (remaining : ℕ)
  | lower (remaining : ℕ)
  | lowerHome (distance : ℕ)
  | copy (remaining : ℕ)
  | home (distance : ℕ)
  | run
  deriving DecidableEq

def tick (r m : ℕ) : Phase → Phase
  | .grow (k+1) => .grow k
  | .grow 0 => .lower r
  | .lower (k+1) => .lower k
  | .lower 0 => .lowerHome (r+1)
  | .lowerHome (k+1) => .lowerHome k
  | .lowerHome 0 => .copy m
  | .copy (k+1) => .copy k
  | .copy 0 => .home (m+1)
  | .home (k+1) => .home k
  | .home 0 => .run
  | .run => .run

def remaining (r m : ℕ) : Phase → ℕ
  | .grow k => k+2*r+2*m+7
  | .lower k => k+r+2*m+6
  | .lowerHome k => k+2*m+4
  | .copy k => k+m+3
  | .home k => k+1
  | .run => 0

theorem tick_decreases (r m : ℕ) (p : Phase) (hp : p ≠ .run) :
    remaining r m (tick r m p)+1 = remaining r m p := by
  cases p with
  | run => contradiction
  | grow k | lower k | lowerHome k | copy k | home k =>
    cases k <;> simp [tick,remaining] <;> omega

def advance (r m : ℕ) : ℕ → Phase → Phase
  | 0,p => p
  | n+1,p => advance r m n (tick r m p)

theorem reaches_run (r m : ℕ) (p : Phase) :
    advance r m (remaining r m p) p = .run := by
  suffices ∀ n p, remaining r m p = n → advance r m n p = .run by
    exact this _ p rfl
  intro n
  induction n with
  | zero => intro p hp; cases p <;> simp_all [remaining,advance]
  | succ n ih =>
    intro p hp
    have hn : p ≠ .run := by intro he; subst p; simp [remaining] at hp
    have hd := tick_decreases r m p hn
    exact ih (tick r m p) (by omega)

theorem preparation_ticks (r m g : ℕ) :
    advance r m (g+2*r+2*m+7) (.grow g) = .run := reaches_run r m (.grow g)

#print axioms preparation_ticks
end PalPeg.GalilScaffoldPrepareClock
