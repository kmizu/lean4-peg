import MacroPeg.HigherOrder.Mach.StepDispatch
import MacroPeg.HigherOrder.Mach.StepExpr
import MacroPeg.HigherOrder.Mach.StepLits

/-!
# Reading an expression on stacks: frame `0`

The token programs `tok0P` … `tok12P`, dispatched on the token (`exprP`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The token programs, in order. -/
def tokPs : List (NProg NK) :=
  [tok0P, tok1P, tok2P, tok3P, tok4P, tok5P, tok6P, tok7P, tok8P, tok9P, tok10P, tok11P, tok12P]

/-- Read an expression. -/
def frame0P : NProg NK := exprP tokPs

theorem frame0_frame (s : PSt) (K : List Nat) (hc : s.ctl = 0 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame0P s K (frameCost N + 30) := by
  refine exprP_frame tokPs rfl s K hc (fun k hk r htk => ?_)
  match k, hk with
  | 0, _ => exact tok0_ok s K r htk hs hi hN
  | 1, _ => exact tok1_ok s K r htk hs hi hN
  | 2, _ => exact tok2_ok s K r htk hs hi hN
  | 3, _ => exact tok3_ok s K r htk hs hi hN
  | 4, _ => exact tok4_ok s K r htk hs hi hN
  | 5, _ => exact tok5_ok s K r htk hs hi hN
  | 6, _ => exact tok6_ok s K r htk hs hi hN
  | 7, _ => exact tok7_ok s K r htk hs hi hN
  | 8, _ => exact tok8_ok s K r htk hs hi hN
  | 9, _ => exact tok9_ok s K r htk hs hi hN
  | 10, _ => exact tok10_ok s K r htk hs hi hN
  | 11, _ => exact tok11_ok s K r htk hs hi hN
  | 12, _ => exact tok12_ok s K r htk hs hi hN
  | k + 13, hk => exact absurd hk (by simp [tokPs])

end Shallot.MacroPeg.Mach
