import PalPeg.GalilFppMarkedCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace PalPeg.GalilFppMarkedFrames
open GalilFppWide

def successors : Instruction 9 → List ℕ
  | .halt => []
  | .move _ _ n | .write _ _ n => [n]
  | .read _ cs => cs.map Prod.snd

def sourceSafe : Instruction 9 → Bool
  | .move t _ _ | .write t _ _ => t != 7
  | _ => true

/-- The transformed kernel, including its thirteen extra MARKS moves,
is a closed control region and never moves or writes SOURCE. -/
theorem kernel_rows : ∀ q : Fin 241,
    (GalilFppMarkedCode.code[q.val]?).map (fun i =>
      sourceSafe i && (successors i).all (fun n => decide (n ≤ 240))) = some true := by decide

theorem execute_successor {x y : Config 9} {i : Instruction 9} (he : Execute i x y) :
    y.pc ∈ successors i := by
  cases he with
  | read x t cs n hm => exact List.mem_map.mpr ⟨_, hm, rfl⟩
  | _ => simp [successors]

theorem source_frame {x y : Config 9} {i : Instruction 9}
    (he : Execute i x y) (hs : sourceSafe i = true) :
    y.pos 7 = x.pos 7 ∧ y.tape 7 = x.tape 7 := by
  cases he with
  | right x t n =>
    have ht : t ≠ 7 := by simpa [sourceSafe] using hs
    simp [Ne.symm ht]
  | left x t n hp =>
    have ht : t ≠ 7 := by simpa [sourceSafe] using hs
    simp [Ne.symm ht]
  | write x t s n =>
    have ht : t ≠ 7 := by simpa [sourceSafe] using hs
    simp [Ne.symm ht]
  | read => exact ⟨rfl, rfl⟩

theorem kernel_step {x y : Config 9} {i : Instruction 9}
    (hi : GalilFppMarkedCode.code[x.pc]? = some i) (he : Execute i x y) (hp : x.pc ≤ 240) :
    y.pc ≤ 240 ∧ y.pos 7 = x.pos 7 ∧ y.tape 7 = x.tape 7 := by
  have hc := kernel_rows ⟨x.pc, by omega⟩
  simp only [hi, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hc
  exact ⟨of_decide_eq_true (List.all_eq_true.mp hc.2 _ (execute_successor he)), source_frame he hc.1⟩

theorem completed_source {x y : Config 9} {qs : List ℕ}
    (hs : Completed GalilFppMarkedCode.code x qs y) (hp : x.pc ≤ 240) :
    y.pos 7 = x.pos 7 ∧ y.tape 7 = x.tape 7 := by
  induction hs with
  | halt => exact ⟨rfl, rfl⟩
  | step x y z i qs hi he hs ih =>
    obtain ⟨hypc, hyp, hyt⟩ := kernel_step hi he hp
    obtain ⟨hzp, hzt⟩ := ih hypc
    exact ⟨hzp.trans hyp, hzt.trans hyt⟩

#print axioms completed_source
end PalPeg.GalilFppMarkedFrames
