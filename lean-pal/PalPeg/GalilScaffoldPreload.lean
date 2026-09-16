import PalPeg.GalilScaffoldControl

set_option autoImplicit false
namespace PalPeg.GalilScaffoldPreload
open GalilScaffoldTape

def bounded (xs : List (Fin 9)) : Tape := ⟨[], 4, xs ++ [5]⟩

theorem read_end (xs : List (Fin 9)) (i : ℕ) :
    read (xs ++ [5]) i = match xs[i]? with
      | some s => s
      | none => if i = xs.length then 5 else 6 := by
  induction xs generalizing i with
  | nil => cases i <;> simp [GalilScaffoldTape.read]
  | cons a xs ih => cases i <;> simp [GalilScaffoldTape.read, ih]

theorem bounded_input (w : List (Fin 4)) :
    denote (bounded (w.map GalilFppRetry.letter)) = GalilFppInputWord.inputTape w := by
  funext i
  cases i with
  | zero => rfl
  | succ k =>
    cases he : w[k]? <;>
      simp [bounded, denote, GalilScaffoldTape.read, read_end,
        GalilFppInputWord.inputTape, List.getElem?_map, he]

theorem bounded_source (w : List (Fin 3)) :
    denote (bounded (w.map GalilFppPreparation.symbol)) = GalilFppPrepareCopy.source w := by
  have he : w.map GalilFppPreparation.symbol =
      (w.map GalilFppPrepareCopy.embed).map GalilFppRetry.letter := by
    rw [List.map_map]
    rfl
  rw [he]
  exact bounded_input (w.map GalilFppPrepareCopy.embed)

theorem bounded_lower (lower : ℕ) :
    denote (bounded (List.replicate lower 8)) = GalilDpPrepared.lowerTape lower := by
  funext i
  cases i with
  | zero => rfl
  | succ k =>
    by_cases hk : k < lower
    · have hn : k+1 ≤ lower := by omega
      simp [bounded, denote, GalilScaffoldTape.read, read_end, GalilDpPrepared.lowerTape, hk, hn]
    · have hn : ¬ k+1 ≤ lower := by omega
      simp [bounded, denote, GalilScaffoldTape.read, read_end, GalilDpPrepared.lowerTape, hk, hn]

/-- Concrete logical stack preload: bounded SOURCE and unary LOWER, all
other tapes empty with blank focus. No representation premise is required. -/
def initial (w : List (Fin 3)) (lower : ℕ) : GalilScaffoldProgram.Config 12 where
  pc := 320
  tapes := fun t => if t = 7 then bounded (w.map GalilFppPreparation.symbol)
    else if t = 10 then bounded (List.replicate lower 8) else reset

theorem initial_denote (w : List (Fin 3)) (lower : ℕ) :
    GalilScaffoldProgram.denote (initial w lower) = GalilDpPrepared.initial w lower := by
  apply GalilScaffoldProgram.wide_ext
  · rfl
  · funext t
    by_cases h7 : t = 7
    · subst t; simpa [GalilScaffoldProgram.denote, initial, GalilDpPrepared.initial] using bounded_source w
    · by_cases h10 : t = 10
      · subst t; simpa [GalilScaffoldProgram.denote, initial, GalilDpPrepared.initial] using bounded_lower lower
      · simp [GalilScaffoldProgram.denote, initial, GalilDpPrepared.initial, h7, h10, reset_blank]
  · funext t
    by_cases h7 : t = 7
    · subst t; rfl
    · by_cases h10 : t = 10
      · subst t; rfl
      · simp [GalilScaffoldProgram.denote, initial, GalilDpPrepared.initial, h7, h10, reset_head]

theorem scheduled_correct (w : List (Fin 3)) (lower : ℕ) :
    ∃ v qs, GalilScaffoldProgram.Completed GalilDpCode.code (initial w lower) qs v ∧
      GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      ∀ bs : List Bool, qs.length ≤ bs.count true →
        GalilScaffoldControl.Run GalilDpCode.code ⟨initial w lower,false⟩ bs ⟨v,true⟩ :=
  GalilScaffoldControl.dp_scheduled w lower (initial w lower) (initial_denote w lower)

#print axioms initial_denote
#print axioms scheduled_correct
end PalPeg.GalilScaffoldPreload
