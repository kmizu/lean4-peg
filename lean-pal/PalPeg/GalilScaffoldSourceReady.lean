import PalPeg.GalilScaffoldLower
import PalPeg.GalilScaffoldPlace
import PalPeg.GalilScaffoldInputHead
import PalPeg.GalilScaffoldDpCost

set_option autoImplicit false
namespace PalPeg.GalilScaffoldSourceReady
open GalilScaffoldTape GalilScaffoldLoad

/-- Extract the exact copied payload from any copy execution, so the
walker execution and the preload theorem refer to the same final tape. -/
theorem copy_result {x y : GalilScaffoldCopy.Cursor} {n : ℕ} {final : Bool}
    (hr : GalilScaffoldCopy.Copy x n y final) :
    n = (x.rest.take x.work).length+1 ∧
      y.tape = write (fill ((x.rest.take x.work).map GalilFppPreparation.symbol) x.tape) 5 ∧
      final = (x.rest.drop x.work).isEmpty := by
  induction hr with
  | stop x h =>
    rcases h with h | h <;> simp [h,fill]
  | next a xs k n t y final hr ih =>
    obtain ⟨hn,ht,hf⟩ := ih
    refine ⟨?_,?_,?_⟩
    · simpa [hn,Nat.add_assoc]
    · simpa [fill] using ht
    · simpa using hf

theorem place_ready (p : GalilScaffoldPlace.Place) (span : ℕ) :
    ∃ y final, GalilScaffoldPlace.Copy
      ⟨p,span+1,moveRight (write reset 4)⟩
      (((GalilScaffoldPlace.stream p).take (span+1)).length+1) y final ∧
      GalilScaffoldLower.Rewind y.tape
        (((GalilScaffoldPlace.stream p).take (span+1)).length+2)
        (GalilScaffoldPreload.bounded
          (((GalilScaffoldPlace.stream p).take (span+1)).map GalilFppPreparation.symbol)) ∧
      (final = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1) := by
  obtain ⟨n,y,final,hr⟩ := GalilScaffoldPlace.runs p (span+1) (moveRight (write reset 4))
  obtain ⟨hn,ht,hf⟩ := copy_result (GalilScaffoldPlace.copy_sound hr)
  change n = ((GalilScaffoldPlace.stream p).take (span+1)).length+1 at hn
  refine ⟨y,final,hn ▸ hr,?_,?_⟩
  · change y.tape = _ at ht
    rw [ht]
    have hh := GalilScaffoldLower.rewind_home
      (GalilScaffoldCopy.copy_home (GalilScaffoldPlace.stream p) (span+1))
    simpa only [GalilScaffoldPlace.encode,reset,write,moveRight,Nat.add_assoc] using hh
  · change final = ((GalilScaffoldPlace.stream p).drop (span+1)).isEmpty at hf
    simp [hf]

theorem input_ready (p : GalilScaffoldPlace.Place) (span : ℕ)
    (rs : List (Option (Fin 2))) (q : List (Fin 2)) :
    ∃ y rs' final, GalilScaffoldInputHead.Copy
      (GalilScaffoldInputHead.encode ⟨p,span+1,moveRight (write reset 4)⟩ rs q)
      (((GalilScaffoldPlace.stream p).take (span+1)).length+1)
      (GalilScaffoldInputHead.encode y rs' q) final ∧
      GalilScaffoldLower.Rewind y.tape
        (((GalilScaffoldPlace.stream p).take (span+1)).length+2)
        (GalilScaffoldPreload.bounded
          (((GalilScaffoldPlace.stream p).take (span+1)).map GalilFppPreparation.symbol)) ∧
      (final = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1) := by
  obtain ⟨y,final,hr,hh,hf⟩ := place_ready p span
  obtain ⟨rs',hc⟩ := GalilScaffoldInputHead.realize_copy hr rs q
  exact ⟨y,rs',final,hc,hh,hf⟩

/-- Lift this same walker-copy/home execution into the full program state.
Only SOURCE changes; every other tape and the PC are framed by put. -/
theorem place_program_ops (p : GalilScaffoldPlace.Place) (span : ℕ)
    (x : GalilScaffoldProgram.Config 12)
    (hx : x.tapes 7 = moveRight (write reset 4)) :
    ∃ y final, GalilScaffoldPlace.Copy
      ⟨p,span+1,x.tapes 7⟩ (((GalilScaffoldPlace.stream p).take (span+1)).length+1) y final ∧
      GalilScaffoldLower.Rewind y.tape
        (((GalilScaffoldPlace.stream p).take (span+1)).length+2)
        (GalilScaffoldPreload.bounded
          (((GalilScaffoldPlace.stream p).take (span+1)).map GalilFppPreparation.symbol)) ∧
      GalilScaffoldLoading.Run x (3*((GalilScaffoldPlace.stream p).take (span+1)).length+2)
        (GalilScaffoldLoading.put x 7 (GalilScaffoldPreload.bounded
          (((GalilScaffoldPlace.stream p).take (span+1)).map GalilFppPreparation.symbol))) ∧
      (final = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1) := by
  obtain ⟨y,final,hr,hh,hf⟩ := place_ready p span
  have hc := GalilScaffoldPlace.copy_ops hr
  have hw := GalilScaffoldLower.rewind_ops hh
  have hall := GalilScaffoldLoad.run_append hc hw
  have hl := GalilScaffoldLoading.lift_run hall x 7 hx
  refine ⟨y,final,by simpa [hx] using hr,hh,?_,hf⟩
  convert hl using 1 <;> omega

/-- Reset, LOWER, SOURCE setup, and the witnessed walker copy/home end in
the exact full DP preload. The count is primitive tape operations only. -/
theorem prepare_program (p : GalilScaffoldPlace.Place) (span lower : ℕ)
    (old : GalilScaffoldControl.Machine 12) :
    let w := (GalilScaffoldPlace.stream p).take (span+1)
    ∃ y final, GalilScaffoldPlace.Copy ⟨p,span+1,moveRight (write reset 4)⟩
      (w.length+1) y final ∧
      GalilScaffoldLower.Rewind y.tape (w.length+2)
        (GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)) ∧
      GalilScaffoldLoading.Run (GalilScaffoldControl.reset 320 old).config
        (3*(lower+w.length)+8) (GalilScaffoldPreload.initial w lower) ∧
      (final = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1) := by
  dsimp
  let w := (GalilScaffoldPlace.stream p).take (span+1)
  let x := (GalilScaffoldControl.reset 320 old).config
  let a := GalilScaffoldLoading.put x 10
    (GalilScaffoldPreload.bounded (List.replicate lower 8))
  let b := GalilScaffoldLoading.put a 7 (moveRight (write reset 4))
  have hl : GalilScaffoldLoading.Run x (3*lower+4) a :=
    GalilScaffoldLoading.lift_run (load_lower lower) x 10 rfl
  have hsetup : GalilScaffoldLoad.Run reset 2 (moveRight (write reset 4)) :=
    .write _ _ _ _ (.right _ _ _ (.nil _))
  have hs : GalilScaffoldLoading.Run a 2 b := GalilScaffoldLoading.lift_run hsetup a 7
    (by simp [a,GalilScaffoldLoading.put,x,GalilScaffoldControl.reset])
  have hb : b.tapes 7 = moveRight (write reset 4) := by simp [b,GalilScaffoldLoading.put]
  obtain ⟨y,final,hcopy,hhome,hr,hfinal⟩ := place_program_ops p span b hb
  have he : GalilScaffoldLoading.put b 7
      (GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)) =
      GalilScaffoldPreload.initial w lower := by
    apply GalilScaffoldLoading.config_ext
    · rfl
    · funext t
      by_cases h7 : t = 7
      · subst t; simp [GalilScaffoldLoading.put,GalilScaffoldPreload.initial]
      · by_cases h10 : t = 10
        · subst t; simp [b,a,GalilScaffoldLoading.put,GalilScaffoldPreload.initial]
        · simp [b,a,x,GalilScaffoldLoading.put,GalilScaffoldControl.reset,
            GalilScaffoldPreload.initial,h7,h10]
  change GalilScaffoldLoading.Run b (3*w.length+2) _ at hr
  rw [he] at hr
  refine ⟨y,final,by simpa [hb] using hcopy,hhome,?_,hfinal⟩
  have hall := GalilScaffoldLoading.run_append hl (GalilScaffoldLoading.run_append hs hr)
  dsimp [w] at hall
  convert hall using 1 <;> omega

theorem prepare_then_dp (p : GalilScaffoldPlace.Place) (span lower : ℕ)
    (old : GalilScaffoldControl.Machine 12) :
    let w := (GalilScaffoldPlace.stream p).take (span+1)
    ∃ y final v, GalilScaffoldPlace.Copy ⟨p,span+1,moveRight (write reset 4)⟩
      (w.length+1) y final ∧
      GalilScaffoldLower.Rewind y.tape (w.length+2)
        (GalilScaffoldPreload.bounded (w.map GalilFppPreparation.symbol)) ∧
      GalilScaffoldLoading.Run (GalilScaffoldControl.reset 320 old).config
        (3*(lower+w.length)+8) (GalilScaffoldPreload.initial w lower) ∧
      (final = true ↔ (GalilScaffoldPlace.stream p).length ≤ span+1) ∧
      GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote v) ∧
      ∀ bs : List Bool, 3186*w.length+1683 ≤ bs.count true →
        GalilScaffoldControl.Run GalilDpCode.code
          (GalilScaffoldControl.start 320 ⟨GalilScaffoldPreload.initial w lower,true⟩) bs ⟨v,true⟩ := by
  obtain ⟨y,final,hc,hh,hr,hf⟩ := prepare_program p span lower old
  obtain ⟨v,hv,hbs⟩ := GalilScaffoldDpCost.scheduled_correct
    ((GalilScaffoldPlace.stream p).take (span+1)) lower
  exact ⟨y,final,v,hc,hh,hr,hf,hv,hbs⟩

#print axioms prepare_then_dp
#print axioms prepare_program
#print axioms place_program_ops
#print axioms input_ready
#print axioms place_ready
end PalPeg.GalilScaffoldSourceReady
