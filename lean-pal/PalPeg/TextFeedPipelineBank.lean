import PalPeg.TextFeedPrefixVerifier
import PalPeg.TextFeedPrepHandoff
import PalPeg.VerifierFeedPrimitive
import PalPeg.GSVerifierProgZLoop

/-! A shared 39-tape instruction bank for the whole preparation/prefix/
zigzag pipeline. No phase owns a private copy of the scanner tapes. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank
open PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed

variable {k : ℕ} {Terminal : Type}

def prepSlot : Fin 15 ↪ Fin 39 := (Fin.natAddEmb 11).trans (Fin.castAddEmb 13)

/-- Q2 is 27..37; the verifier/scanner view remains at 11..20. -/
def verifySlot : Fin 21 ↪ Fin 39 where
  toFun j := if h : j.val < 11 then ⟨j.val + 27, by omega⟩ else ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    have hi := i.isLt
    have hj := j.isLt
    dsimp only at hh
    split_ifs at hh <;> dsimp at hh <;> omega

def dirSlot : Fin 1 ↪ Fin 39 := Fin.natAddEmb 38

abbrev Act (k : ℕ) := TextFeedPrefixBank.Act k ⊕ (PrepAct k ⊕ (VerifierFeedShared.Act k ⊕ Bool))
abbrev Cond (k : ℕ) := TextFeedPrefixBank.Cond k ⊕ (PrepCond k ⊕ (VerifierFeedShared.Cond k ⊕ GSVProgZLoop.DCond))

noncomputable def interp (e : Env k) : Interp Terminal (Act k) (Cond k) (Fin k) 39 where
  actOf
    | .inl a => (TextFeedPrefixBank.interp e).actOf a
    | .inr (.inl a) => ((prepInterp e.blank e.endSym e.mark).transport prepSlot).actOf a
    | .inr (.inr (.inl a)) => ((VerifierFeedShared.shared e).transport verifySlot).actOf a
    | .inr (.inr (.inr up)) => ((GSVProgZLoop.dirInterp e.blank e.mark).transport dirSlot).actOf up
  condOf
    | .inl c => (TextFeedPrefixBank.interp (Terminal := Terminal) e).condOf c
    | .inr (.inl c) => ((prepInterp (Terminal := Terminal) e.blank e.endSym e.mark).transport prepSlot).condOf c
    | .inr (.inr (.inl c)) => ((VerifierFeedShared.shared (Terminal := Terminal) e).transport verifySlot).condOf c
    | .inr (.inr (.inr c)) => ((GSVProgZLoop.dirInterp (Terminal := Terminal) e.blank e.mark).transport dirSlot).condOf c

inductive Label (k : ℕ) where
  | enqueue (first : Bool)
  | prefix (a : TextFeedPrefixAtomic.Act)
  | prep (a : PrepAct k)
  | verify (a : GSVProg.Act10)
  | dir (up : Bool)
  deriving DecidableEq, Fintype

noncomputable def low (e : Env k) : Label k → Prog (Act k) (Cond k)
  | .enqueue first => (TextFeedPrefixBank.low e (.enqueue first)).map Sum.inl Sum.inl
  | .prefix a => (TextFeedPrefixBank.low e (.work a)).map Sum.inl Sum.inl
  | .prep a => .act (.inr (.inl a))
  | .verify a => (VerifierFeedPrimitive.low e a).map (Sum.inr ∘ Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr ∘ Sum.inl)
  | .dir up => .act (.inr (.inr (.inr up)))

theorem exec_prefix {e : Env k} {p : Prog (TextFeedPrefixBank.Act k) (TextFeedPrefixBank.Cond k)}
    {T : Fin 39 → STape (Fin k)} {tr : List (Fin 39 → Fin k × Move)}
    (h : Exec (TextFeedPrefixBank.interp (Terminal := Terminal) e) e.blank p T tr) :
    Exec (interp (Terminal := Terminal) e) e.blank (p.map Sum.inl Sum.inl) T tr :=
  exec_map (I₂ := interp e) (fa := Sum.inl) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) h

theorem exec_prep {e : Env k} {p : Prog (PrepAct k) (PrepCond k)}
    {T : Fin 15 → STape (Fin k)} {tr : List (Fin 15 → Fin k × Move)}
    (h : Exec (prepInterp (Terminal := Terminal) e.blank e.endSym e.mark) e.blank p T tr)
    (rest : Fin 39 → STape (Fin k)) :
    Exec (interp (Terminal := Terminal) e) e.blank (p.map (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (extend prepSlot T rest) (tr.map (extendVec prepSlot rest)) :=
  exec_map (I₂ := interp e) (fa := Sum.inr ∘ Sum.inl) (fc := Sum.inr ∘ Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h prepSlot rest)

theorem exec_verify {e : Env k} {p : Prog (VerifierFeedShared.Act k) (VerifierFeedShared.Cond k)}
    {T : Fin 21 → STape (Fin k)} {tr : List (Fin 21 → Fin k × Move)}
    (h : Exec (VerifierFeedShared.shared (Terminal := Terminal) e) e.blank p T tr)
    (rest : Fin 39 → STape (Fin k)) :
    Exec (interp (Terminal := Terminal) e) e.blank
      (p.map (Sum.inr ∘ Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr ∘ Sum.inl))
      (extend verifySlot T rest) (tr.map (extendVec verifySlot rest)) :=
  exec_map (I₂ := interp e) (fa := Sum.inr ∘ Sum.inr ∘ Sum.inl) (fc := Sum.inr ∘ Sum.inr ∘ Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h verifySlot rest)

def prepView (T : Fin 39 → STape (Fin k)) : Fin 15 → STape (Fin k) := fun j => T (prepSlot j)

theorem exec_enqueue {e : Env k} {first : Bool} {T : Fin 23 → STape (Fin k)}
    {tr : List (Fin 23 → Fin k × Move)}
    (h : Exec (DualQueueInput.interp (Terminal := Terminal) e) e.blank (DualQueueInput.worker e first) T tr)
    (rest : Fin 39 → STape (Fin k)) :
    Exec (interp (Terminal := Terminal) e) e.blank (low e (.enqueue first))
      (extend DualQueueShared.pairSlot T rest) (tr.map (extendVec DualQueueShared.pairSlot rest)) := by
  have hh := exec_map (I₂ := TextFeedPrefixBank.interp e) (fa := Sum.inl) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h DualQueueShared.pairSlot rest)
  exact exec_prefix hh

/-- Bootstrap both FIFOs from actual blank tapes in the same bank.
Its 92 actions fit the 93-clock bank window with one return clock. -/
theorem first_exec {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (a : Fin k) (ha : a ≠ e.mark) (rest : Fin 39 → STape (Fin k)) :
    ∃ tr qt₁ m₁ qt₂ m₂, Exec (interp (Terminal := Terminal) e) e.blank (low e (.enqueue true))
      (extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.blankPair e.blank) a) rest) tr ∧
      tr.length ≤ 92 ∧
      applyTrace e.blank (extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.blankPair e.blank) a) rest) tr =
        extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) a) rest ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty a) ∧ Ready e.blank e.mark qt₂ m₂ (snoc empty a) := by
  obtain ⟨tr, qt₁, m₁, qt₂, m₂, he, hn, ht, h₁, h₂⟩ := DualQueue.first_both (Terminal := Terminal) hc hmb a ha
  obtain ⟨tr', he', hn', ht'⟩ := DualQueueInput.read_exec he ht
  refine ⟨_, qt₁, m₁, qt₂, m₂, exec_enqueue he' rest, ?_, ?_, h₁, h₂⟩
  · simp only [List.length_map]
    omega
  · rw [applyTrace_extend, ht']

theorem prep_exec (e : Env k) (a : PrepAct k) (T : Fin 39 → STape (Fin k)) :
    ∃ tr, Exec (interp (Terminal := Terminal) e) e.blank (low e (.prep a)) T tr ∧
      tr.length = 1 ∧ applyTrace e.blank T tr =
        extend prepSlot (applyTrace e.blank (prepView T)
          [actVec (prepInterp (Terminal := Terminal) e.blank e.endSym e.mark) a (prepView T)]) T := by
  have he := exec_act (blank := e.blank)
    (prepInterp_inputFree (Terminal := Terminal) e.blank e.endSym e.mark) a (prepView T)
  have hh := exec_prep he T
  have hi : extend prepSlot (prepView T) T = T := TextFeedStartupSafety.extend_restrict prepSlot T
  rw [hi] at hh
  refine ⟨_, hh, rfl, ?_⟩
  have ht := applyTrace_extend prepSlot e.blank T
    [actVec (prepInterp (Terminal := Terminal) e.blank e.endSym e.mark) a (prepView T)] (prepView T)
  rwa [hi] at ht

theorem verify_exec {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt : QT k} {m : Mode} {M : VerifierFeed.VMachine' k}
    (h : Ready e.blank e.mark qt m M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2)
    (a : GSVProg.Act10) (rest : Fin 39 → STape (Fin k)) :
    ∃ tr qt' m', Exec (interp (Terminal := Terminal) e) e.blank (low e (.verify a))
      (extend verifySlot (VerifierFeedShared.bundle e qt m M) rest) tr ∧ tr.length ≤ 48 ∧
      applyTrace e.blank (extend verifySlot (VerifierFeedShared.bundle e qt m M) rest) tr =
        extend verifySlot (VerifierFeedShared.bundle e qt' m' (VerifierFeedPrimitive.effect e a M)) rest ∧
      Ready e.blank e.mark qt' m' (VerifierFeedPrimitive.effect e a M).Q2 ∧
      Encodes e.blank e.mark (VerifierFeedPrimitive.effect e a M).R2.qt (VerifierFeedPrimitive.effect e a M).Q2 := by
  obtain ⟨tr, qt', m', he, hn, ht, hr, hb'⟩ := VerifierFeedPrimitive.low_matches (Terminal := Terminal) hc hmb h hb a
  refine ⟨_, qt', m', exec_verify he rest, by simpa only [List.length_map] using hn, ?_, hr, hb'⟩
  rw [applyTrace_extend, ht]

def writeDir (e : Env k) (up : Bool) (T : Fin 39 → STape (Fin k)) : Fin 39 → STape (Fin k) :=
  Function.update T 38 ((T 38).applyAction e.blank (GSVProgZLoop.dirSymbol e.blank e.mark up, .stay))

theorem dir_exec (e : Env k) (up : Bool) (T : Fin 39 → STape (Fin k)) :
    ∃ tr, Exec (interp (Terminal := Terminal) e) e.blank (low e (.dir up)) T tr ∧
      tr.length = 1 ∧ applyTrace e.blank T tr = writeDir e up T := by
  let P : Fin 1 → STape (Fin k) := fun j => T (dirSlot j)
  have he := exec_act (I := GSVProgZLoop.dirInterp (Terminal := Terminal) e.blank e.mark)
    (blank := e.blank) (fun _ _ _ => rfl) up P
  have hh := exec_map (I₂ := interp e) (fa := Sum.inr ∘ Sum.inr ∘ Sum.inr)
    (fc := Sum.inr ∘ Sum.inr ∘ Sum.inr) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (exec_transport he dirSlot T)
  have hi : extend dirSlot P T = T := TextFeedStartupSafety.extend_restrict dirSlot T
  rw [hi] at hh
  refine ⟨_, hh, rfl, ?_⟩
  have ht := applyTrace_extend dirSlot e.blank T
    [actVec (GSVProgZLoop.dirInterp (Terminal := Terminal) e.blank e.mark) up P] P
  rw [hi] at ht
  rw [ht]
  funext j
  by_cases hj : j = 38
  · subst j
    change extend dirSlot _ T (dirSlot 0) = _
    rw [extend_ι]
    rfl
  · have ho : proj dirSlot j = none := by
      apply proj_eq_none
      intro i hi
      have hz : i = 0 := Subsingleton.elim _ _
      subst i
      exact hj hi.symm
    rw [extend_of_proj_none ho]
    exact (Function.update_of_ne hj _ _).symm

/-- info: 'PalPeg.TextFeedPipelineBank.prep_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prep_exec

/-- info: 'PalPeg.TextFeedPipelineBank.first_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_exec

/-- info: 'PalPeg.TextFeedPipelineBank.dir_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dir_exec

/-- info: 'PalPeg.TextFeedPipelineBank.verify_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verify_exec

end PalPeg.TextFeedPipelineBank
