import PalPeg.GalilDpPreparedCost
import PalPeg.GalilDpStart
import PalPeg.GalilDpCorrect
import PalPeg.GalilScaffoldNextPc

set_option autoImplicit false
namespace PalPeg.GalilDpCost
open GalilFppWide GalilDpAdvance GalilDpExhaustion GalilDpLoop GalilDpStart

/-- The complete exported DP program has a linear instruction bound,
including preparation and either halt, for every unary lower bound. -/
theorem initial_terminated_cost (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w lower) qs y ∧
      (y.pc = 346 ∨ y.pc = 347) ∧ qs.length ≤ 3186*w.length+1683 := by
  obtain ⟨x,qs,hr,hp,h8,h9,h7,ht7,hm,hs,h10,h11,hl,ht11,hcost⟩ :=
    GalilDpPreparedCost.prepared_cost w lower
  have hb := start_run x hp
    (by rw [hm,h8]; simp [GalilFppMarkedLayout.marks])
    (by rw [hs,h9]; simp [GalilFppMarkedLayout.marks])
  have hx := start_state w lower x hm hs hl h8 h9 h10
  by_cases hn : 5 ≤ w.length
  · obtain ⟨rs,hs',hrs⟩ := next_candidate w 0 (start x) rfl
      hx.marks hx.second hx.firstPos hx.secondPos hn
    obtain ⟨y,ts,ht,htl,hy⟩ := GalilDpLoop.terminates w lower 1
      {next (start x) with pc := 348} (next_state w lower 0 (start x) hx) rfl (by decide) hn
    refine ⟨y,_,steps_completed (steps_append hr (steps_append hb hs')) ht,hy,?_⟩
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  · obtain ⟨y,rs,hs',hrs,hy⟩ := short_next w (start x) (by omega) rfl
      hx.marks hx.second hx.firstPos hx.secondPos
    refine ⟨y,_,steps_completed (steps_append hr hb) hs',Or.inr hy,?_⟩
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem execute_unique {n : ℕ} {i : Instruction n} {x y z : Config n}
    (hw : GalilScaffoldNextPc.WellFormed i) (hy : Execute i x y) (hz : Execute i x z) :
    y = z := by
  cases hy with
  | right => cases hz; rfl
  | left => cases hz; rfl
  | write => cases hz; rfl
  | read x t cs p hm =>
    cases hz with
    | read _ _ _ q hq =>
      have hp := GalilScaffoldNextPc.lookup_mem _ p cs hw hm
      have hq' := GalilScaffoldNextPc.lookup_mem _ q cs hw hq
      have he : p = q := Option.some.inj (hp.symm.trans hq')
      subst q
      rfl

theorem completed_unique {n : ℕ} {code : List (Instruction n)}
    (hw : ∀ i ∈ code, GalilScaffoldNextPc.WellFormed i)
    {x y z : Config n} {qs rs : List ℕ}
    (hy : Completed code x qs y) (hz : Completed code x rs z) : y = z := by
  induction hy generalizing z rs with
  | halt x hi =>
    cases hz with
    | halt => rfl
    | step x v z i rs hj he hr =>
      have hh : i = .halt := Option.some.inj (hj.symm.trans hi)
      subst i
      cases he
  | step x v y i qs hi he hr ih =>
    cases hz with
    | halt x hj =>
      have hh : i = .halt := Option.some.inj (hi.symm.trans hj)
      subst i
      cases he
    | step x u z j rs hj hjstep hjrest =>
      have hh : i = j := Option.some.inj (hi.symm.trans hj)
      subst j
      have hmem : i ∈ code := List.mem_of_getElem? hi
      have hu := execute_unique (hw i hmem) he hjstep
      subst u
      exact ih hjrest

/-- Correctness and the global time bound hold for the very same execution. -/
theorem initial_correct_cost (w : List (Fin 3)) (lower : ℕ) :
    ∃ y qs, Completed GalilDpCode.code (GalilDpPrepared.initial w lower) qs y ∧
      GalilDpCorrect.Result w lower 0 y ∧ qs.length ≤ 3186*w.length+1683 := by
  obtain ⟨y,qs,hy,_,hcost⟩ := initial_terminated_cost w lower
  obtain ⟨z,rs,hz,hresult⟩ := GalilDpCorrect.initial_correct w lower
  have he := completed_unique GalilScaffoldNextPc.dp_wellFormed hy hz
  exact ⟨y,qs,hy,he.symm ▸ hresult,hcost⟩

#print axioms initial_correct_cost
#print axioms initial_terminated_cost
end PalPeg.GalilDpCost
