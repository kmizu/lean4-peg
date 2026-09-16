import PalPeg.GalilDpCode

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpFrames
open GalilFppWide

def successors : Instruction 12 → List ℕ
  | .halt => []
  | .move _ _ n | .write _ _ n => [n]
  | .read _ cs => cs.map Prod.snd

def spareSafe : Instruction 12 → Bool
  | .move t _ _ | .write t _ _ => decide (t.val < 10)
  | _ => true

/-- The FPP copy and its duplicated instructions never change LOWER or OUTPUT. -/
theorem preparation_rows : ∀ q : Fin 346,
    (GalilDpCode.code[q.val]?).map spareSafe = some true := by decide

/-- Once search starts it cannot return to FPP, including through either halt. -/
theorem search_rows : ∀ q : Fin 27,
    (GalilDpCode.code[q.val+346]?).map (fun i =>
      (successors i).all (fun n => decide (346 ≤ n))) = some true := by decide

theorem execute_successor {x y : Config 12} {i : Instruction 12} (he : Execute i x y) :
    y.pc ∈ successors i := by
  cases he with
  | read x t cs n hm => exact List.mem_map.mpr ⟨_, hm, rfl⟩
  | _ => simp [successors]

theorem search_closed {x y : Config 12} {i : Instruction 12}
    (hi : GalilDpCode.code[x.pc]? = some i) (he : Execute i x y) (hp : 346 ≤ x.pc) :
    346 ≤ y.pc := by
  obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hb' : x.pc < 373 := hb
  have hc := search_rows ⟨x.pc-346, by omega⟩
  have hq : x.pc-346+346 = x.pc := by omega
  simp only [hq, hi, Option.map_some, Option.some.injEq] at hc
  exact of_decide_eq_true (List.all_eq_true.mp hc _ (execute_successor he))

theorem spare_frame {x y : Config 12} {i : Instruction 12}
    (he : Execute i x y) (hs : spareSafe i = true) (t : Fin 12) (ht : 10 ≤ t.val) :
    y.pos t = x.pos t ∧ y.tape t = x.tape t := by
  cases he with
  | right x k n =>
    have hk : k.val < 10 := by simpa [spareSafe] using hs
    have hne : t ≠ k := by intro h; subst t; omega
    simp [hne]
  | left x k n hp =>
    have hk : k.val < 10 := by simpa [spareSafe] using hs
    have hne : t ≠ k := by intro h; subst t; omega
    simp [hne]
  | write x k s n =>
    have hk : k.val < 10 := by simpa [spareSafe] using hs
    have hne : t ≠ k := by intro h; subst t; omega
    simp [hne]
  | read => exact ⟨rfl, rfl⟩

/-- A prefix ending back in FPP never entered the closed search region.
Consequently it preserves the complete lower/output tapes and heads. -/
theorem before_search {x y : Config 12} {qs : List ℕ}
    (hs : Steps GalilDpCode.code x qs y) (hy : y.pc < 346) :
    x.pc < 346 ∧ ∀ t : Fin 12, 10 ≤ t.val →
      y.pos t = x.pos t ∧ y.tape t = x.tape t := by
  induction hs with
  | nil => exact ⟨hy, fun _ _ => ⟨rfl, rfl⟩⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨hyp, hframe⟩ := ih hy
    have hxp : x.pc < 346 := by
      by_contra hn
      have := search_closed hi he (by omega)
      omega
    have hc := preparation_rows ⟨x.pc, hxp⟩
    simp only [hi, Option.map_some, Option.some.injEq] at hc
    refine ⟨hxp, ?_⟩
    intro t ht
    obtain ⟨hpos, htape⟩ := spare_frame he hc t ht
    obtain ⟨hpos', htape'⟩ := hframe t ht
    exact ⟨hpos'.trans hpos, htape'.trans htape⟩

#print axioms before_search
end PalPeg.GalilDpFrames
