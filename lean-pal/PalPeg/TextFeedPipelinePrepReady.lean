import PalPeg.TextFeedPipelinePrepSetup
import PalPeg.TextFeedBacklog

/-! Recover the prefix representation from the actual completed prep
view and both physical FIFOs, keeping the real accumulated arrival count. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrepReady
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelinePrepInput

variable {k : ℕ}

/-- The backlog passed to the prefix uses the real input count, including
all preparation-time arrivals and the final partial-frame arrival. -/
theorem arrivals_contents {Terminal : Type} (enc : Terminal → Fin k)
    {Text : List (Fin k)} {n : ℕ} {q : Queue (Fin k)} (hi : Inv q) (hl : toList q = Text.take n)
    (word : List Terminal) (a : Terminal)
    (hv : TextFeedPrefixDeadline.Valid Text n ((word ++ [a]).map enc)) :
    toList (snoc (word.foldl (fun q b => snoc q (enc b)) q) (enc a)) = Text.take (n + word.length + 1) := by
  have ht := toList_foldl_snoc ((word ++ [a]).map enc) q hi
  rw [List.foldl_map] at ht
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at ht
  rw [ht, hl, TextFeedPrefixVerifier.valid_take_append hv]
  simp only [List.length_map, List.length_append, List.length_singleton, Nat.add_assoc]

def preparedTapes (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (S : PatternTapes.Tapes k) (q₁ : Queue (Fin k)) (old : Fin k) (dir : STape (Fin k)) : Fin 39 → STape (Fin k) :=
  TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂
    (TextFeedPrefixFinish.data (TextFeedBacklog.model (toGS S) qt₁ m₁ q₁) (toVExt S).U)
    (toVExt S).Txt2 (fun j => TSg S (Fin.natAdd 10 j)) old dir

theorem prepared_view (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (S : PatternTapes.Tapes k) (q₁ : Queue (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    prepView (preparedTapes e qt₁ m₁ qt₂ m₂ S q₁ old dir) = TSg S := by
  funext j
  fin_cases j <;> rfl

theorem prepared_pair (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (S : PatternTapes.Tapes k) (q₁ : Queue (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    pairView (preparedTapes e qt₁ m₁ qt₂ m₂ S q₁ old dir) =
      DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old :=
  TextFeedPrefixBank.pair_view e qt₁ m₁ qt₂ m₂ _ _ _ old dir

/-- The two views and the untouched direction cover all 39 physical
tapes. No independently supplied scanner bundle is needed. -/
theorem tapes_eq {e : Env k} {T : Fin 39 → STape (Fin k)} {S : PatternTapes.Tapes k}
    {qt₁ qt₂ : QT k} {m₁ m₂ : Mode} {old : Fin k} (q₁ : Queue (Fin k))
    (hp : prepView T = TSg S)
    (hq : pairView T = DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old) :
    T = preparedTapes e qt₁ m₁ qt₂ m₂ S q₁ old (T 38) := by
  funext j
  have hcover : ∀ j : Fin 39, j = 38 ∨ (∃ i, prepSlot i = j) ∨ ∃ i, DualQueueShared.pairSlot i = j := by
    unfold prepSlot DualQueueShared.pairSlot
    decide
  rcases hcover j with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rfl
  · exact (congrFun hp i).trans (congrFun (prepared_view e qt₁ m₁ qt₂ m₂ S q₁ old (T 38)) i).symm
  · exact (congrFun hq i).trans (congrFun (prepared_pair e qt₁ m₁ qt₂ m₂ S q₁ old (T 38)) i).symm

/-- At the genuine prep endpoint, recover the prefix worker and its
rank representation at position zero, with the actual arrival count n. -/
theorem prepared_rep {e : Env k} {u v Text : List (Fin k)} {rate p r n : ℕ}
    {T : Fin 39 → STape (Fin k)} {S : PatternTapes.Tapes k} {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (hp : prepView T = TSg S) (hq : ReadyAt e T q₁ q₂ old) (hl : toList q₁ = Text.take n)
    (hv : GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark u v (TextFeed.padW e.blank Text 0)
      rate p r (toGS S, toVExt S) (⟨0, 0⟩, 0)) :
    ∃ (M : TextFeed.Machine' k) (U X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k))
        (dir : STape (Fin k)) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode),
      T = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ (TextFeedPrefixFinish.data M U) X aux old dir ∧
      M.Q = q₁ ∧ M.m = 0 ∧ Ready e.blank e.mark qt₁ m₁ M.Q ∧ Ready e.blank e.mark qt₂ m₂ q₂ ∧
      TextFeedPrefixRank.Rep e u v Text rate p r n M U 0 1 ∧
      Tape.SeqView e.blank X (TextFeed.padW e.blank Text 0) 0 := by
  obtain ⟨qt₁, m₁, qt₂, m₂, hview, h₁, h₂⟩ := hq
  refine ⟨TextFeedBacklog.model (toGS S) qt₁ m₁ q₁, (toVExt S).U, (toVExt S).Txt2,
    (fun j => TSg S (Fin.natAdd 10 j)), T 38, qt₁, m₁, qt₂, m₂, tapes_eq q₁ hp hview,
    rfl, rfl, h₁, h₂, ?_, ?_⟩
  · exact ⟨TextFeedBacklog.feedInv hv.scan h₁ hl, rfl, rfl, hv.pat⟩
  · simpa using hv.txt2

/-- info: 'PalPeg.TextFeedPipelinePrepReady.prepared_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_rep

end PalPeg.TextFeedPipelinePrepReady
