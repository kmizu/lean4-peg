import PalPeg.GalilScaffoldRawTick

set_option autoImplicit false
namespace PalPeg.GalilScaffoldRawSchedule
open GalilFppWide (Instruction)
open GalilScaffoldHeap (Address)
open GalilScaffoldRawTick (Machine Represents tick)

theorem loop_other {n slots : ℕ} (i : Instruction n) (active : Bool) (a d : Address slots)
    (hne : d ≠ a) (x : GalilScaffoldHeapProgram.Config n slots) :
    (GalilScaffoldRawTapes.loop i active a x).heap d = x.heap d := by
  cases active with
  | false => simp [GalilScaffoldRawTapes.loop_inactive]
  | true =>
    cases i with
    | halt => simp [GalilScaffoldRawTapes.loop_halt]
    | read => simp [GalilScaffoldRawTapes.loop_read]
    | write => simp [GalilScaffoldRawTapes.loop_write,GalilScaffoldHeapProgram.written]
    | move t dir pc =>
      rw [GalilScaffoldRawTapes.loop_move]
      cases dir <;> simp [GalilScaffoldHeapProgram.moved,GalilScaffoldHeapTape.left,
        GalilScaffoldHeapTape.right,GalilScaffoldHeap.put,hne]

theorem tick_other {n slots : ℕ} {code : List (Instruction n)} {enabled : Bool}
    {a : Address slots} {x y : Machine n slots} (ht : tick code enabled a x = some y)
    (d : Address slots) (hne : d ≠ a) : y.config.heap d = x.config.heap d := by
  unfold tick at ht
  split at ht
  · cases Option.some.inj ht; rfl
  · cases hi : code[x.config.pc]? with
    | none => simp [hi] at ht
    | some i =>
      simp only [hi,Option.bind_some] at ht
      split at ht
      · cases Option.some.inj ht; rfl
      · cases hp : GalilScaffoldNextPc.next i (fun t => (x.config.tapes t).focus) with
        | none => simp [hp] at ht
        | some pc =>
          simp only [hp,Option.map_some] at ht
          cases Option.some.inj ht
          exact loop_other i true a d hne x.config

/-- Unlike the existential-allocation Run, this execution records the exact
preassigned address used at every tick (including idle ticks). -/
inductive Run {n slots : ℕ} (code : List (Instruction n)) :
    Machine n slots → List Bool → List (Address slots) → Machine n slots → Prop
  | nil (x : Machine n slots) : Run code x [] [] x
  | cons (x y z : Machine n slots) (b : Bool) (bs : List Bool)
      (a : Address slots) (as : List (Address slots))
      (ht : tick code b a x = some y) (hr : Run code y bs as z) :
      Run code x (b :: bs) (a :: as) z

theorem realize_run {n slots : ℕ} {code : List (Instruction n)}
    {u v : GalilScaffoldControl.Machine n} {bs : List Bool}
    (hu : GalilScaffoldControl.Run code u bs v)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (x : Machine n slots) (hr : Represents x u) (addresses : List (Address slots))
    (hlen : addresses.length = bs.length) (hn : addresses.Nodup)
    (hf : ∀ a ∈ addresses, x.config.heap a = none) :
    ∃ y, Run code x bs addresses y ∧ Represents y v := by
  induction hu generalizing x addresses with
  | nil u =>
    have he : addresses = [] := by simpa using hlen
    subst addresses
    exact ⟨x,.nil x,hr⟩
  | cons u v w b bs ht hu ih =>
    cases addresses with
    | nil => simp at hlen
    | cons a rest =>
      obtain ⟨ha,hnr⟩ := List.nodup_cons.mp hn
      obtain ⟨y,hy,hry⟩ := GalilScaffoldRawTick.realize_tick ht hw x hr a (hf a (by simp))
      have hfr : ∀ d ∈ rest, y.config.heap d = none := by
        intro d hd
        have hne : d ≠ a := by intro he; subst d; exact ha hd
        rw [tick_other hy d hne]
        exact hf d (List.mem_cons_of_mem _ hd)
      obtain ⟨z,hz,hrz⟩ := ih y hry rest (by simpa using hlen) hnr hfr
      exact ⟨z,.cons x y z b bs a rest hy hz,hrz⟩

/-- Instruction-prefix slots 0..quantum-1 on a fixed node; controller slots
may occupy the remaining suffix. -/
def block (node quantum slots : ℕ) (hq : quantum ≤ slots) : List (Address slots) :=
  (List.finRange quantum).map (fun k => (node,⟨k.val, Nat.lt_of_lt_of_le k.isLt hq⟩))

theorem block_length (node quantum slots : ℕ) (hq : quantum ≤ slots) :
    (block node quantum slots hq).length = quantum := by simp [block]

theorem block_nodup (node quantum slots : ℕ) (hq : quantum ≤ slots) :
    (block node quantum slots hq).Nodup := by
  apply (List.nodup_finRange quantum).map
  intro k j he
  apply Fin.ext
  exact congrArg (fun a : Address slots => a.2.val) he

theorem block_prefix {node quantum slots : ℕ} {hq : quantum ≤ slots} {a : Address slots}
    (ha : a ∈ block node quantum slots hq) : a.1 = node ∧ a.2.val < quantum := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
  exact ⟨rfl,k.isLt⟩

theorem run_other {n slots : ℕ} {code : List (Instruction n)}
    {x y : Machine n slots} {bs : List Bool} {addresses : List (Address slots)}
    (hr : Run code x bs addresses y) (d : Address slots) (hd : d ∉ addresses) :
    y.config.heap d = x.config.heap d := by
  induction hr with
  | nil => rfl
  | cons x y z b bs a rest ht hr ih =>
    have hne : d ≠ a := by intro he; subst d; exact hd (by simp)
    have hrest : d ∉ rest := by intro hm; exact hd (List.mem_cons_of_mem _ hm)
    exact (ih hrest).trans (tick_other ht d hne)

theorem block_suffix_frame {n slots : ℕ} {code : List (Instruction n)}
    {x y : Machine n slots} {bs : List Bool} {node quantum : ℕ} {hq : quantum ≤ slots}
    (hr : Run code x bs (block node quantum slots hq) y) (d : Address slots)
    (hd : quantum ≤ d.2.val) : y.config.heap d = x.config.heap d := by
  apply run_other hr d
  intro hm
  have hp := (block_prefix hm).2
  omega

theorem realize_block {n slots : ℕ} {code : List (Instruction n)}
    {u v : GalilScaffoldControl.Machine n} {bs : List Bool}
    (hu : GalilScaffoldControl.Run code u bs v)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (x : Machine n slots) (hr : Represents x u) (node : ℕ)
    (hq : bs.length ≤ slots)
    (hf : ∀ tag : Fin slots, tag.val < bs.length → x.config.heap (node,tag) = none) :
    ∃ y, Run code x bs (block node bs.length slots hq) y ∧ Represents y v ∧
      ∀ d : Address slots, bs.length ≤ d.2.val → y.config.heap d = x.config.heap d := by
  obtain ⟨y,hy,hry⟩ := realize_run hu hw x hr (block node bs.length slots hq)
    (block_length _ _ _ _) (block_nodup _ _ _ _) (by
      intro a ha
      obtain ⟨he,hp⟩ := block_prefix ha
      have hx := hf a.2 hp
      simpa [← he] using hx)
  exact ⟨y,hy,hry,fun d hd => block_suffix_frame hy d hd⟩

#print axioms realize_block
#print axioms block_suffix_frame
#print axioms block_nodup
#print axioms tick_other
#print axioms realize_run
end PalPeg.GalilScaffoldRawSchedule
