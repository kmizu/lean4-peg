import PalPeg.TextFeedPipelinePrefixHit

/-! Prefix hitting times have witnesses in the real micro-input machine. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixPhysical
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixWindow
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPipelinePrefixHit PalPeg.TextFeedPrefixRank
open PalPeg.TextFeedPipelinePrepFinish (Config phase finishAt machine_partial)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def pack {e : Env k} {leftSym : Fin k} {R rate : ℕ} (x : Phys e leftSym R rate)
    (q : Fin ((R + 1) * 94 + 1)) : Config e leftSym R rate :=
  { state := ((x.1, 0), q), tape := x.2 }

theorem round_pack (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (a : Terminal) (x : Phys e leftSym R rate) :
    (machine e leftSym enc R rate).sRound (pack x 0) a = pack (frame e enc leftSym R rate a x) 0 :=
  machine_round e leftSym enc R rate x.1 x.2 a

theorem partial_pack (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate J : ℕ)
    (hJ : J ≤ R) (a : Terminal) (x : Phys e leftSym R rate) :
    finishAt e leftSym enc R rate [] a J (pack x 0) =
      pack ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J]
        (input e enc leftSym R rate a x)) (phase R J) :=
  machine_partial e leftSym enc R rate J hJ x.1 x.2 a

def Witness (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (d p r n : ℕ) (word : List Terminal) (x : Phys e leftSym R rate) : Prop :=
  (∃ before rest y z, word = before ++ rest ∧
    before.foldl (machine e leftSym enc R rate).sRound (pack x 0) = pack y 0 ∧
    Link e leftSym R rate z y ∧ Good e u v Text d p r (n + before.length) 0 (erase z)) ∨
  (∃ before a rest J y z, J ≤ R ∧ word = before ++ a :: rest ∧
    finishAt e leftSym enc R rate before a J (pack x 0) = pack y (phase R J) ∧
    Link e leftSym R rate z y ∧ Good e u v Text d p r (n + before.length + 1) 0 (erase z))

theorem hit_witness {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} {word : List Terminal} {x : Phys e leftSym R rate}
    (h : Hit e enc leftSym R rate u v Text d p r n word x) :
    Witness e enc leftSym R rate u v Text d p r n word x := by
  induction h with
  | @now n w x z hl hg => exact Or.inl ⟨[], w, x, z, rfl, rfl, hl, hg⟩
  | @within n a w x z J hJ hl hg =>
    exact Or.inr ⟨[], a, w, J, _, z, hJ, rfl, partial_pack e enc leftSym R rate J hJ a x, hl, hg⟩
  | @next n a w x h ih =>
    rcases ih with ⟨before, rest, y, z, hw, hp, hl, hg⟩ | ⟨before, b, rest, J, y, z, hJ, hw, hp, hl, hg⟩
    · left
      refine ⟨a :: before, rest, y, z, by simp only [List.cons_append, hw], ?_, hl, ?_⟩
      · simpa only [List.foldl_cons, round_pack] using hp
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg
    · right
      refine ⟨a :: before, b, rest, J, y, z, hJ, by simp only [List.cons_append, hw], ?_, hl, ?_⟩
      · simpa only [finishAt, List.foldl_cons, round_pack] using hp
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg

/-- info: 'PalPeg.TextFeedPipelinePrefixPhysical.hit_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hit_witness

end PalPeg.TextFeedPipelinePrefixPhysical
