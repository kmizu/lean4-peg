import PalPeg.GalilScaffoldWriteGuards

set_option autoImplicit false
namespace PalPeg.GalilScaffoldRawTapes
open GalilFppWide (Instruction)
open GalilScaffoldHeap (Address)
open GalilScaffoldHeapProgram (Config moved written)

/-- Decoded write and move groups; the instruction is an entry snapshot. -/
def writeGroup {n slots : ℕ} (i : Instruction n) (active : Bool) (k : Fin n)
    (x : Config n slots) : Config n slots := match i with
  | .write t v _ => if active && decide (k = t) then written x k v x.pc else x
  | _ => x

def moveGroup {n slots : ℕ} (i : Instruction n) (active : Bool) (k : Fin n) (d : Bool)
    (a : Address slots) (x : Config n slots) : Config n slots := match i with
  | .move t e _ => if active && decide (k = t) && decide (d = e) then moved x k a d x.pc else x
  | _ => x

def body {n slots : ℕ} (i : Instruction n) (active : Bool) (a : Address slots)
    (k : Fin n) (x : Config n slots) : Config n slots :=
  moveGroup i active k true a (moveGroup i active k false a (writeGroup i active k x))

def loop {n slots : ℕ} (i : Instruction n) (active : Bool) (a : Address slots)
    (x : Config n slots) : Config n slots :=
  (List.finRange n).foldl (fun y k => body i active a k y) x

theorem body_write {n slots : ℕ} (t k : Fin n) (v : Fin 9) (pc : ℕ)
    (a : Address slots) (x : Config n slots) :
    body (.write t v pc) true a k x = if k = t then written x k v x.pc else x := by
  simp [body,moveGroup,writeGroup]

theorem body_move {n slots : ℕ} (t k : Fin n) (d : Bool) (pc : ℕ)
    (a : Address slots) (x : Config n slots) :
    body (.move t d pc) true a k x = if k = t then moved x k a d x.pc else x := by
  cases d <;> by_cases he : k = t <;> simp [body,moveGroup,writeGroup,he]

theorem loop_write {n slots : ℕ} (t : Fin n) (v : Fin 9) (pc : ℕ)
    (a : Address slots) (x : Config n slots) :
    loop (.write t v pc) true a x = written x t v x.pc := by
  simp only [loop,body_write]
  rw [GalilScaffoldWriteGuards.dispatch_fold]
  exact GalilScaffoldMoveGuards.dispatch_once t (fun k y => written y k v y.pc) _
    (List.nodup_finRange n) (List.mem_finRange t) x

theorem loop_move {n slots : ℕ} (t : Fin n) (d : Bool) (pc : ℕ)
    (a : Address slots) (x : Config n slots) :
    loop (.move t d pc) true a x = moved x t a d x.pc := by
  simp only [loop,body_move]
  rw [GalilScaffoldWriteGuards.dispatch_fold]
  exact GalilScaffoldMoveGuards.dispatch_once t (fun k y => moved y k a d y.pc) _
    (List.nodup_finRange n) (List.mem_finRange t) x

theorem loop_inactive {n slots : ℕ} (i : Instruction n) (a : Address slots) (x : Config n slots) :
    loop i false a x = x := by
  cases i <;> simp [loop,body,moveGroup,writeGroup]

theorem loop_read {n slots : ℕ} (t : Fin n) (cs : List (Fin 9 × ℕ)) (active : Bool)
    (a : Address slots) (x : Config n slots) : loop (.read t cs) active a x = x := by
  simp [loop,body,moveGroup,writeGroup]

theorem loop_halt {n slots : ℕ} (active : Bool) (a : Address slots) (x : Config n slots) :
    loop .halt active a x = x := by simp [loop,body,moveGroup,writeGroup]

/-- With the target PC supplied by the instruction semantics, the concrete
interleaved tape loop realizes the same heap step. Computing nextPc is separate. -/
theorem realize_loop {n slots : ℕ} {i : Instruction n}
    {u v : GalilScaffoldProgram.Config n} (he : GalilScaffoldProgram.Execute i u v)
    (x : Config n slots) (hr : GalilScaffoldHeapProgram.Represents x u)
    (a : Address slots) (hf : x.heap a = none) :
    GalilScaffoldHeapProgram.Represents {loop i true a x with pc := v.pc} v := by
  cases he with
  | right u t pc =>
    simpa [loop_move,moved,GalilScaffoldProgram.changed] using GalilScaffoldHeapProgram.moved_right hr t a hf pc
  | left u t pc legal =>
    simpa [loop_move,moved,GalilScaffoldProgram.changed] using (GalilScaffoldHeapProgram.moved_left hr t a hf pc legal).2
  | write u t s pc =>
    simpa [loop_write,written,GalilScaffoldProgram.changed] using GalilScaffoldHeapProgram.written_represents hr t s pc
  | read u t cs pc hm =>
    rw [loop_read]
    exact ⟨rfl,hr.2⟩

#print axioms realize_loop
#print axioms loop_write
#print axioms loop_move
#print axioms loop_inactive
end PalPeg.GalilScaffoldRawTapes
