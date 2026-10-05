import MacroPeg.HigherOrder.ExpSpace.Machine
import MacroPeg.HigherOrder.Hardness
import MacroPeg.HigherOrder.Adequacy

/-!
# Tools for running higher-order grammars on concrete inputs

* `runObs_peg`: on a plain PEG expression (no calls, no parameters), the first-order run and the higher-order run of
  its embedding are the same step by step — so the observations about sites proved for first-order grammars
  (`codeE_ok`, `siteE_ok`, `codeP_match`, … in `AtmHard.lean` / `QbfHard.lean`) carry over (`hobs_of_peg`).
* `hobs_call`: a call of a rule `λx₁ … λxₖ. B` with closed arguments observes what `B` with the arguments put in
  observes.
* Lookahead and guards.
-/

namespace Shallot.MacroPeg.HO

open Shallot.MacroPeg (MExp MGrammar MacroObs runObs runObs_eps runObs_seq runObs_alt runObs_star runObs_notP
  macroObs_iff_obs)

/-! ## Plain PEG expressions -/

/-- Built from PEG operators only. -/
def PegOnly : MExp → Prop
  | .eps | .any | .chr _ | .range _ _ | .lit _ => True
  | .seq a b | .alt a b => PegOnly a ∧ PegOnly b
  | .star a | .notP a => PegOnly a
  | _ => False

/-- A plain PEG expression runs the same in both calculi, at every fuel. -/
theorem runObs_peg {G : MGrammar} {g : HGrammar} : ∀ (n : Nat) (e : MExp) (x : List Char), PegOnly e →
    runObs (Shallot.MacroPeg.mpegRun G .callByName n e x) = hrun g n (emb 0 e) x
  | 0, _, _, _ => by rw [Shallot.MacroPeg.mpegRun.eq_def, hrun.eq_def]; rfl
  | n + 1, e, x, he => by
    cases e with
    | eps => rw [runObs_eps, hrun.eq_def]; rfl
    | any => exact runObs_leaf (.inl rfl)
    | chr c => exact runObs_leaf (.inr (.inl ⟨c, rfl⟩))
    | range lo hi => exact runObs_leaf (.inr (.inr (.inl ⟨lo, hi, rfl⟩)))
    | lit s => exact runObs_leaf (.inr (.inr (.inr ⟨s, rfl⟩)))
    | seq a b =>
      simp only [emb]; rw [runObs_seq, hrun_seq, runObs_peg n a x he.1]
      cases hrun g n (emb 0 a) x with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some y => exact runObs_peg n b y he.2
    | alt a b =>
      simp only [emb]; rw [runObs_alt, hrun_alt, runObs_peg n a x he.1]
      cases hrun g n (emb 0 a) x with
      | none => rfl
      | some r => cases r with
        | none => exact runObs_peg n b x he.2
        | some y => rfl
    | star a =>
      simp only [emb]; rw [runObs_star, hrun_star, runObs_peg n a x he]
      cases hrun g n (emb 0 a) x with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some y => exact runObs_peg n (.star a) y he
    | notP a =>
      simp only [emb]; rw [runObs_notP, hrun_notP, runObs_peg n a x he]
      cases hrun g n (emb 0 a) x with
      | none => rfl
      | some r => cases r <;> rfl
    | param _ | call _ _ | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ => exact absurd he id

/-- First-order observations of a plain PEG expression are higher-order observations of its embedding. -/
theorem hobs_of_peg {G : MGrammar} {g : HGrammar} {e : MExp} (he : PegOnly e) {x : List Char}
    {r : Option (List Char)} (h : MacroObs G e x r) : HObs g (emb 0 e) x r := by
  obtain ⟨n, hn⟩ := (macroObs_iff_obs G e x r).1 h
  exact ⟨n, (runObs_peg n e x he).symm.trans hn⟩

/-! ## Lookahead and guards -/

section Guards

variable {g : HGrammar} {x : List Char}

def HExp.andP (e : HExp) : HExp := .notP (.notP e)

theorem hobs_and_some {A : HExp} {y : List Char} (h : HObs g A x (some y)) : HObs g (HExp.andP A) x (some x) :=
  hobs_not_fail (hobs_not_ok h)

theorem hobs_and_none {A : HExp} (h : HObs g A x none) : HObs g (HExp.andP A) x none :=
  hobs_not_ok (hobs_not_fail h)

theorem hobs_eps : HObs g .eps x (some x) := ⟨1, by rw [hrun.eq_def]⟩

theorem hobs_fail : HObs g HExp.failAlways x none := ⟨2, hrun_failAlways⟩

/-- `&C X / !C Y` with `C` succeeding runs `X`. -/
theorem guard_pos {C X Y : HExp} {y : List Char} {r : Option (List Char)} (hC : HObs g C x (some y))
    (hX : HObs g X x r) : HObs g (.alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)) x r := by
  cases r with
  | none => exact hobs_alt_fail (hobs_seq_ok (hobs_and_some hC) hX) (hobs_seq_fail (hobs_not_ok hC))
  | some z => exact hobs_alt_ok (hobs_seq_ok (hobs_and_some hC) hX)

/-- `&C X / !C Y` with `C` failing runs `Y`. -/
theorem guard_neg {C X Y : HExp} {r : Option (List Char)} (hC : HObs g C x none) (hY : HObs g Y x r) :
    HObs g (.alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)) x r :=
  hobs_alt_fail (hobs_seq_fail (hobs_and_none hC)) (hobs_seq_ok (hobs_not_fail hC) hY)

end Guards

/-! ## Calling a rule -/

/-- `λ:τ₁. … λ:τₖ. b`. -/
def lamsT : List Ty → HExp → HExp
  | [], b => b
  | τ :: τs, b => .lam τ (lamsT τs b)

theorem inst_lamsT (a : HExp) : ∀ (τs : List Ty) (k : Nat) (b : HExp),
    HExp.inst a k (lamsT τs b) = lamsT τs (HExp.inst a (k + τs.length) b)
  | [], _, _ => rfl
  | τ :: τs, k, b => by
    simp only [lamsT, HExp.inst, inst_lamsT a τs (k + 1) b, List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm 1 τs.length]

/-- `k` β-steps on `(λ. … λ. B) a₁ … aₖ`. -/
theorem hrun_spineT {g : HGrammar} {x : List Char} (B : HExp) : ∀ (τs : List Ty) (as : List HExp),
    τs.length = as.length → ∀ m, hrun g (m + as.length) (HExp.apps (lamsT τs B) as) x = hrun g m (instArgs as B) x
  | [], [], _, m => rfl
  | τ :: τs, a :: as, hl, m => by
    have hl' : τs.length = as.length := by simpa using hl
    have hstep : step g (HExp.apps (lamsT (τ :: τs) B) (a :: as)) =
        some (HExp.apps (lamsT τs (HExp.inst a as.length B)) as) := by
      have := step_apps (g := g) (f := .app (.lam τ (lamsT τs B)) a) rfl (fun _ _ h => by cases h) as
      rw [inst_lamsT, Nat.zero_add, hl'] at this
      exact this
    rw [List.length_cons, ← Nat.add_assoc, hrun_head (isHead_apps_cons a _ as), hstep]
    exact hrun_spineT (HExp.inst a as.length B) τs as hl' m
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- The β-steps of a call put the closed arguments in for the variables. -/
theorem instArgs_substC : ∀ (as σ : List HExp), AllClosed as → AllClosed σ → ∀ b : HExp,
    instArgs as (HExp.substC σ as.length b) = HExp.substC (as.reverse ++ σ) 0 b
  | [], σ, _, _, b => rfl
  | a :: as, σ, has, hσ, b => by
    have ha : HExp.Cl 0 a := has a List.mem_cons_self
    have has' : AllClosed as := fun c hc => has c (List.mem_cons_of_mem _ hc)
    have hσ' : AllClosed (a :: σ) := fun c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ha
      · exact hσ c hc
    simp only [instArgs, List.length_cons]
    rw [inst_substC ha hσ as.length b, instArgs_substC as (a :: σ) has' hσ' b]
    simp

/-- **Calling a rule**: if the body with the closed arguments put in observes `r`, the call observes `r`. -/
theorem hobs_call {g : HGrammar} {i : Nat} {τ : Ty} {τs : List Ty} {B : HExp} {as : List HExp}
    (hr : g.rules[i]? = some ⟨τ, lamsT τs B⟩) (hl : τs.length = as.length) (has : AllClosed as)
    {x : List Char} {r : Option (List Char)} (h : HObs g (HExp.substC as.reverse 0 B) x r) :
    HObs g (HExp.apps (.rule i) as) x r := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + as.length + 1, ?_⟩
  have hhead : (HExp.apps (.rule i) as).isHead = true := by
    cases as with
    | nil => rfl
    | cons a as => exact isHead_apps_cons a _ as
  have hstep : step g (HExp.apps (.rule i) as) = some (HExp.apps (lamsT τs B) as) :=
    step_apps (by simp [step, hr]) (fun _ _ h => by cases h) as
  rw [hrun_head hhead, hstep]
  dsimp only
  rw [hrun_spineT B τs as hl n, ← substC_nil as.length B, instArgs_substC as [] has (by simp [AllClosed]) B]
  simpa using hn

end Shallot.MacroPeg.HO
