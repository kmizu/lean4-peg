import Complexity.TqbfEval

/-!
# Evaluating the quantifiers with a stack of frames

`qEvalV` is recursive; the list machine walks the tree of assignments with an explicit stack. A *context* is the list
of bound levels, newest first, each with its kind and frame (`fresh`: exploring the `true` branch; `second a`:
exploring the `false` branch after the `true` branch gave `a`).

* `fin ctx ks v`: the final answer when the subtree below the context (remaining kinds `ks`) has value `v`.
* `res ctx ks := fin ctx ks (qEvalV mv ks (bitsOf ctx))`: the final answer when starting to descend.
* `fin_descend`: descending (pushing `fresh` frames for all remaining kinds) does not change `res`.
* `res` is invariant under the moves of the machine and starts as `qEvalV mv kinds []`.
* `cnt`: the number of leaves still to visit; each round (descend, evaluate a leaf, return) lowers it by one.

`evalQP` is the list program; its tapes: `ks` (remaining kinds, outermost on top), `ku` (used kinds, newest on top),
`fr` (frames, newest on top), `vs` (values), and the tapes of `evalLeafP`.
-/

namespace Complexity

variable {k : Nat}

section Functional

variable (mv : List VTok)

def bitsOf (ctx : List (Bool × Frame)) : List Bool := ctx.map (fun p => p.2.bit)

def fin : List (Bool × Frame) → List Bool → Bool → Bool
  | [], _, v => v
  | (κ, .fresh) :: ctx, ks, v => fin ctx (κ :: ks) (comb κ v (qEvalV mv ks (false :: bitsOf ctx)))
  | (κ, .second a) :: ctx, ks, v => fin ctx (κ :: ks) (comb κ a v)

def res (ctx : List (Bool × Frame)) (ks : List Bool) : Bool := fin mv ctx ks (qEvalV mv ks (bitsOf ctx))

/-- The context after descending through `ks`. -/
def descendCtx (ks : List Bool) (ctx : List (Bool × Frame)) : List (Bool × Frame) :=
  (ks.map (fun κ => (κ, Frame.fresh))).reverse ++ ctx

theorem fin_descend : ∀ (ks : List Bool) (ctx : List (Bool × Frame)),
    res mv ctx ks = fin mv (descendCtx ks ctx) [] (qEvalV mv [] (bitsOf (descendCtx ks ctx)))
  | [], ctx => by simp [res, descendCtx]
  | κ :: ks, ctx => by
    have ih := fin_descend ks ((κ, .fresh) :: ctx)
    have e : descendCtx (κ :: ks) ctx = descendCtx ks ((κ, .fresh) :: ctx) := by simp [descendCtx]
    rw [e, ← ih]
    simp [res, fin, qEvalV, bitsOf, Frame.bit]

theorem res_refresh (ctx : List (Bool × Frame)) (κ : Bool) (ks : List Bool) (v : Bool) :
    fin mv ((κ, .fresh) :: ctx) ks v = res mv ((κ, .second v) :: ctx) ks := by
  simp [res, fin, bitsOf, Frame.bit]

/-- Leaves still to visit (excluding the subtree below the context). -/
def extra : List (Bool × Frame) → Nat → Nat
  | [], _ => 0
  | (_, .fresh) :: ctx, h => 2 ^ h + extra ctx (h + 1)
  | (_, .second _) :: ctx, h => extra ctx (h + 1)

def cnt (ctx : List (Bool × Frame)) (h : Nat) : Nat := 2 ^ h + extra ctx h

theorem extra_descend : ∀ (ks : List Bool) (ctx : List (Bool × Frame)),
    extra (descendCtx ks ctx) 0 + 1 = cnt ctx ks.length
  | [], ctx => by simp [descendCtx, cnt]; omega
  | κ :: ks, ctx => by
    have e : descendCtx (κ :: ks) ctx = descendCtx ks ((κ, .fresh) :: ctx) := by simp [descendCtx]
    rw [e, extra_descend ks ((κ, .fresh) :: ctx)]
    simp only [cnt, extra, List.length_cons, Nat.pow_succ]
    omega

end Functional

/-! ## The list program -/

def kindElem (κ : Bool) : Nat := if κ then 1 else 0

def bitElem' (b : Bool) : Nat := if b then 1 else 0

section
variable (ks ku fr ft vs mr mr2 : Fin k)

def descendP : LProg k := .loop ks nonEmpty (.seq (moveTop ks ku) (.push fr 20))

def clearP (i : Fin k) : LProg k := .loop i nonEmpty (.pop i)

/-- Leave exactly the top value (or `false`) on `vs`. -/
def normalizeP : LProg k :=
  .ite vs nonEmpty
    (.ite vs (symIs 1) (.seq (clearP vs) (.push vs 1)) (.seq (clearP vs) (.push vs 0)))
    (.push vs 0)

def isSecond : Nat → Bool := fun s => s == 21 + 4 || s == 22 + 4

/-- Combine the value on `vs` with a `second a` frame of kind on top of `ku`, pop the frame, return the kind. -/
def combineP : LProg k :=
  .seq
    (.ite fr (symIs 22)
      -- a = true
      (.ite ku (symIs 1) (skipP vs) (.seq (.pop vs) (.push vs 1)))
      -- a = false
      (.ite ku (symIs 1) (.seq (.pop vs) (.push vs 0)) (skipP vs)))
    (.seq (.pop fr) (moveTop ku ks))

def returnP : LProg k := .loop fr isSecond (combineP ks ku fr vs)

/-- The top frame is `fresh`: turn it into `second v`, clear the value. -/
def refreshP : LProg k :=
  .seq (.pop fr) (.seq (.ite vs (symIs 1) (.push fr 22) (.push fr 21)) (.pop vs))

def answerP : LProg k := .ite vs (symIs 1) (.halt true) (.halt false)

def roundP : LProg k :=
  .seq (descendP ks ku fr)
  (.seq (evalLeafP mr mr2 fr ft vs)
  (.seq (normalizeP vs)
  (.seq (returnP ks ku fr vs)
  (.ite fr nonEmpty (refreshP fr vs) (answerP vs)))))

def evalQP : LProg k := .loop ks (fun _ => true) (roundP ks ku fr ft vs mr mr2)

end

/-! ## A loop rule over abstract states -/

theorem halts_loop_abs {Q : Lists k → Prop} {i : Fin k} {c : Nat → Bool} {p : LProg k} {α : Type}
    (inv : α → Lists k → Prop) (μ : α → Nat) (R : Bool → Lists k → Prop)
    (hQ : ∀ a L, inv a L → Q L)
    (hexit : ∀ a L, inv a L → c (lastSym (L i)) = false → False)
    (hbody : ∀ a L, inv a L → c (lastSym (L i)) = true →
      (∃ a' L' T, Runs Q p L L' T ∧ inv a' L' ∧ μ a' < μ a) ∨ (∃ b L' T, Halts Q p L b L' T ∧ R b L')) :
    ∀ a L, inv a L → ∃ b L' T, Halts Q (.loop i c p) L b L' T ∧ R b L' := by
  intro a
  induction hm : μ a using Nat.strongRecOn generalizing a with
  | _ m ih =>
    intro L hI
    cases hc : c (lastSym (L i)) with
    | false => exact (hexit a L hI hc).elim
    | true =>
      rcases hbody a L hI hc with ⟨a', L₁, T₁, ⟨t₁, _, hx₁⟩, hI₁, hμ⟩ | ⟨b, L', T₁, ⟨t₁, _, hx₁⟩, hR⟩
      · obtain ⟨b, L', T₂, ⟨t₂, _, hx₂⟩, hR⟩ := ih (μ a') (hm ▸ hμ) a' rfl L₁ hI₁
        exact ⟨b, L', t₁ + 1 + t₂, ⟨_, Nat.le_refl _, .loopC (hQ a L hI) hc hx₁ hx₂⟩, hR⟩
      · exact ⟨b, L', t₁ + 1, ⟨_, Nat.le_refl _, .loopS (hQ a L hI) hc hx₁⟩, hR⟩

end Complexity
