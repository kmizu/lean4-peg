import PalPeg.GalilScaffoldRawTapes

set_option autoImplicit false
namespace PalPeg.GalilScaffoldNextPc
open GalilFppWide (Instruction)

def lookup (v : Fin 9) : List (Fin 9 × ℕ) → Option ℕ
  | [] => none
  | (w,q) :: cs => if v = w then some q else lookup v cs

theorem lookup_mem (v : Fin 9) (p : ℕ) (cs : List (Fin 9 × ℕ))
    (hn : (cs.map Prod.fst).Nodup) (hm : (v,p) ∈ cs) : lookup v cs = some p := by
  induction cs with
  | nil => simp at hm
  | cons c cs ih =>
    rcases c with ⟨w,q⟩
    obtain ⟨hw,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | he
    · cases he; simp [lookup]
    · by_cases hv : v = w
      · subst v
        exact False.elim (hw (List.mem_map.mpr ⟨(w,p),he,rfl⟩))
      · simpa [lookup,hv] using ih ht he

def WellFormed {n : ℕ} : Instruction n → Prop
  | .read _ cs => (cs.map Prod.fst).Nodup
  | _ => True

instance {n : ℕ} (i : Instruction n) : Decidable (WellFormed i) := by
  cases i <;> unfold WellFormed <;> infer_instance

def next {n : ℕ} (i : Instruction n) (focus : Fin n → Fin 9) : Option ℕ := match i with
  | .halt => none
  | .move _ _ pc => some pc
  | .write _ _ pc => some pc
  | .read t cs => lookup (focus t) cs

theorem next_execute {n : ℕ} {i : Instruction n} {u v : GalilScaffoldProgram.Config n}
    (he : GalilScaffoldProgram.Execute i u v) (hw : WellFormed i) :
    next i (fun t => (u.tapes t).focus) = some v.pc := by
  cases he with
  | right => rfl
  | left => rfl
  | write => rfl
  | read u t cs pc hm => exact lookup_mem _ _ cs hw hm

/-- The next PC is computed from the entry focus, rather than supplied as an
independent argument to the tape-loop refinement. -/
theorem realize_next {n slots : ℕ} {i : Instruction n}
    {u v : GalilScaffoldProgram.Config n} (he : GalilScaffoldProgram.Execute i u v)
    (hw : WellFormed i) (x : GalilScaffoldHeapProgram.Config n slots)
    (hr : GalilScaffoldHeapProgram.Represents x u) (a : GalilScaffoldHeap.Address slots)
    (hf : x.heap a = none) :
    ∃ pc, next i (fun t => (x.tapes t).focus) = some pc ∧
      GalilScaffoldHeapProgram.Represents {GalilScaffoldRawTapes.loop i true a x with pc := pc} v := by
  refine ⟨v.pc,?_,GalilScaffoldRawTapes.realize_loop he x hr a hf⟩
  have heq : (fun t => (x.tapes t).focus) = (fun t => (u.tapes t).focus) :=
    funext (fun t => (hr.2 t).2.1)
  rw [heq]
  exact next_execute he hw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem dp_wellFormed : ∀ i ∈ GalilDpCode.code, WellFormed i := by decide

theorem lookup_sound (v : Fin 9) (p : ℕ) (cs : List (Fin 9 × ℕ))
    (hh : lookup v cs = some p) : (v,p) ∈ cs := by
  induction cs with
  | nil => simp [lookup] at hh
  | cons c cs ih =>
    rcases c with ⟨w,q⟩
    by_cases he : v = w
    · subst w
      have hp : q = p := by simpa [lookup] using hh
      subst p
      exact List.mem_cons_self
    · have ht : lookup v cs = some p := by simpa [lookup,he] using hh
      exact List.mem_cons_of_mem _ (ih ht)

def Forward {n : ℕ} (i : Instruction n) (focus : Fin n → Fin 9) (target : ℕ) : Prop :=
  match i with
  | .halt => False
  | .move _ _ pc => target = pc
  | .write _ _ pc => target = pc
  | .read t cs => (focus t,target) ∈ cs

theorem forward_iff_next {n : ℕ} (i : Instruction n) (hw : WellFormed i)
    (focus : Fin n → Fin 9) (target : ℕ) :
    Forward i focus target ↔ next i focus = some target := by
  cases i with
  | halt => simp [Forward,next]
  | move => simp [Forward,next,eq_comm]
  | write => simp [Forward,next,eq_comm]
  | read t cs => exact ⟨lookup_mem _ _ cs hw,lookup_sound _ _ cs⟩

/-- The target-keyed disjunction built by Scala's forward(target,event).
Multiple matching read choices are allowed here; WellFormed establishes that
the lookup selects exactly the same target. -/
def TargetEvent {n : ℕ} (code : List (Instruction n)) (pc : ℕ) (active : Bool)
    (focus : Fin n → Fin 9) (target : ℕ) : Prop :=
  ∃ row i, active = true ∧ pc = row ∧ code[row]? = some i ∧ Forward i focus target

theorem targetEvent_iff {n : ℕ} {code : List (Instruction n)} {pc : ℕ} {i : Instruction n}
    (hi : code[pc]? = some i) (hw : WellFormed i) (active : Bool)
    (focus : Fin n → Fin 9) (target : ℕ) :
    TargetEvent code pc active focus target ↔ active = true ∧ next i focus = some target := by
  constructor
  · rintro ⟨row,j,ha,he,hj,hf⟩
    subst row
    rw [hi] at hj
    cases hj
    exact ⟨ha,(forward_iff_next i hw focus target).mp hf⟩
  · rintro ⟨ha,hn⟩
    exact ⟨pc,i,ha,rfl,hi,(forward_iff_next i hw focus target).mpr hn⟩

theorem target_unique {n : ℕ} {code : List (Instruction n)} {pc : ℕ} {i : Instruction n}
    (hi : code[pc]? = some i) (hw : WellFormed i) {active : Bool} {focus : Fin n → Fin 9}
    {p q : ℕ} (hp : TargetEvent code pc active focus p) (hq : TargetEvent code pc active focus q) :
    p = q := by
  have hp' := ((targetEvent_iff hi hw active focus p).mp hp).2
  have hq' := ((targetEvent_iff hi hw active focus q).mp hq).2
  exact Option.some.inj (hp'.symm.trans hq')

#print axioms targetEvent_iff
#print axioms target_unique
#print axioms realize_next
#print axioms dp_wellFormed
end PalPeg.GalilScaffoldNextPc
