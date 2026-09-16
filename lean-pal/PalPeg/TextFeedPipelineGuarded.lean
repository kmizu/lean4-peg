import PalPeg.TextFeedPipelineControl
import PalPeg.ProgLangGuarded

/-! Every residual of the guarded verifier source is safe under arbitrary
new observations. In particular, an arrival between calls cannot bypass
the text-cell check that precedes a right move. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineGuarded
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangGuarded
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl

variable {k : ℕ}

def KeepText (a : GSVProg.Act10) : Prop :=
  (a.1 = GSVProg.e8 GSTapes.tT → a.2.1 = true) ∧ (a.1 = GSVProg.tX → a.2.1 = true)

def GSGood : GSVProg.Act10 ⊕ Bool → Prop
  | .inl a => KeepText a
  | .inr _ => True

def Good (ev : TaskCond k → Bool) : TaskAct k → Prop
  | .inr (.inr (.inl a)) => KeepText a ∧
      (a.1 = GSVProg.e8 GSTapes.tT → a.2.2 = .right → ev (.inr (.inl .blankText)) = false) ∧
      (a.1 = GSVProg.tX → a.2.2 = .right → ev (.inr (.inr (.inr .blankX))) = false)
  | _ => True

theorem feedHead_certified : Certified (Good (k := k)) feedHead :=
  (Certified.act (fun _ => trivial)).ite Certified.skip

theorem feedHead2_certified : Certified (Good (k := k)) feedHead2 :=
  Certified.act (fun _ => by simp [Good, KeepText])

theorem afterVerify_certified (a : GSVProg.Act10 ⊕ Bool) :
    Certified (Good (k := k)) (afterVerify a) := by
  cases a with
  | inr _ => exact Certified.skip
  | inl a =>
    change Certified (Good (k := k))
      (if a.1 = GSVProg.e8 GSTapes.tT ∧ a.2.2 = .right then feedHead else .skip)
    split
    · exact feedHead_certified
    · exact Certified.skip

theorem beforeCond_certified (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) :
    Certified (Good (k := k)) (beforeCond c) := by
  cases c with
  | inr c => cases c <;> exact Certified.skip
  | inl c =>
    cases c with
    | notMark _ => exact Certified.skip
    | notStart => exact Certified.skip
    | notStartU => exact Certified.skip
    | matchOk => exact Certified.loop (fun _ => trivial) Certified.skip
    | compOk => exact Certified.loop (fun _ => by simp [Good, KeepText]) Certified.skip

/-- Certification is for the complete wait/action/after-feed command,
not for a hypothetical standalone text-right instruction. -/
theorem verifyAct_certified (a : GSVProg.Act10 ⊕ Bool) (ha : GSGood a) :
    Certified (Good (k := k)) (verifyAct a) := by
  cases a with
  | inr up =>
    exact Certified.skip.seq ((Certified.act (fun _ => trivial)).seq (afterVerify_certified (.inr up)))
  | inl a =>
    have hafter := afterVerify_certified (k := k) (.inl a)
    by_cases hr : a.2.2 = .right
    · by_cases ht : a.1 = GSVProg.e8 GSTapes.tT
      · have he : beforeVerify (k := k) (.inl a) = waitText1 := by
          simp only [beforeVerify, if_pos hr, if_pos ht]
        rw [verifyAct, he]
        apply Certified.guarded_then (fun _ => trivial) _ hafter
        intro ev hc
        refine ⟨ha, fun _ _ => hc, ?_⟩
        intro hx _
        exact False.elim (GSVProg.e8_ne_tX GSTapes.tT (ht.symm.trans hx))
      · by_cases hx : a.1 = GSVProg.tX
        · have he : beforeVerify (k := k) (.inl a) = waitText2 := by
            simp only [beforeVerify, if_pos hr, if_neg ht, if_pos hx]
          rw [verifyAct, he]
          apply Certified.guarded_then (fun _ => by simp [Good, KeepText]) _ hafter
          intro ev hc
          exact ⟨ha, fun h _ => False.elim (ht h), fun _ _ => hc⟩
        · have he : beforeVerify (k := k) (.inl a) = .skip := by
            simp only [beforeVerify, if_pos hr, if_neg ht, if_neg hx]
          rw [verifyAct, he]
          exact Certified.skip.seq ((Certified.act (fun _ =>
            ⟨ha, fun h _ => False.elim (ht h), fun h _ => False.elim (hx h)⟩)).seq hafter)
    · have he : beforeVerify (k := k) (.inl a) = .skip := by
        simp only [beforeVerify, if_neg hr]
      rw [verifyAct, he]
      exact Certified.skip.seq ((Certified.act (fun _ =>
        ⟨ha, fun _ h => False.elim (hr h), fun _ h => False.elim (hr h)⟩)).seq hafter)

theorem liftVerify_certified (p : GSVProgZLoop.DProg) (hp : AllActs GSGood p) :
    Certified (Good (k := k)) (liftVerify p) := by
  induction p with
  | skip => exact Certified.skip
  | act a => exact verifyAct_certified a hp
  | seq p q ihp ihq => exact (ihp hp.1).seq (ihq hp.2)
  | ite c p q ihp ihq => exact (beforeCond_certified c).seq ((ihp hp.1).ite (ihq hp.2))
  | loop c a b ihb =>
    exact (beforeCond_certified c).seq (Certified.loop (fun _ => trivial)
      ((verifyAct_certified a hp.1).seq ((ihb hp.2).seq (beforeCond_certified c))))

theorem liftPrep_certified (p : Prog (PrepInstance.PrepAct k) (PrepInstance.PrepCond k)) :
    Certified (Good (k := k)) (liftPrep p) := by
  apply Certified.of_all
  rw [liftPrep, all_map]
  exact all_of (fun _ _ => trivial) p

theorem liftPrefix_certified (p : Prog TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond) :
    Certified (Good (k := k)) (liftPrefix p) := by
  apply Certified.of_all
  rw [liftPrefix, all_map]
  exact all_of (fun _ _ => trivial) p

theorem task_certified (e : Env k) (leftSym : Fin k) (rate : ℕ)
    (hstep : AllActs GSGood (GSVProgZLoop.stepProg rate)) :
    Certified (Good (k := k)) (task e leftSym rate) := by
  have hbody : Certified (Good (k := k)) (verifyBody rate) :=
    feedHead_certified.seq (feedHead2_certified.seq (liftVerify_certified _ hstep))
  have hloop : Certified (Good (k := k)) (verifyLoop rate) := Certified.loop (fun _ => trivial) hbody
  exact (liftPrep_certified _).seq ((liftPrefix_certified _).seq
    ((Certified.act (fun _ => trivial)).seq hloop))

/-- info: 'PalPeg.TextFeedPipelineGuarded.liftVerify_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms liftVerify_certified

/-- info: 'PalPeg.TextFeedPipelineGuarded.task_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms task_certified

end PalPeg.TextFeedPipelineGuarded
