import PalPeg.GalilFppMarkedCode
import PalPeg.GalilFppCode

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilFppMarkTransform
open GalilFppWide

def tapeIndex (t : Fin 7) : Fin 9 := ⟨t.val, by omega⟩

/-- Check precisely the transformation performed by Scala: every A move
has an extra MARKS move, emit becomes a write, and other rows are lifted. -/
def translated (q : ℕ) (i : GalilFppInstruction.Instruction) : Bool :=
  match i with
  | .halt => GalilFppMarkedCode.code[q]? == some .halt
  | .emit n => GalilFppMarkedCode.code[q]? == some (.write 8 8 n)
  | .move t d n =>
    if t = 0 then
      match GalilFppMarkedCode.code[q]? with
      | some (.move t' d' extra) => t' == 0 && d' == d &&
          GalilFppMarkedCode.code[extra]? == some (.move 8 d n)
      | _ => false
    else GalilFppMarkedCode.code[q]? == some (.move (tapeIndex t) d n)
  | .write t s n => GalilFppMarkedCode.code[q]? == some (.write (tapeIndex t) s n)
  | .read t cs => GalilFppMarkedCode.code[q]? == some (.read (tapeIndex t) cs)

set_option maxHeartbeats 4000000 in
theorem all_kernel_rows : ∀ q : Fin 228,
    (GalilFppCode.code[q.val]?).map (translated q.val) = some true := by decide

theorem candidate_code (q : Fin 228) (d : Bool) (n : ℕ)
    (hi : GalilFppCode.code[q.val]? = some (.move 0 d n)) :
    ∃ extra, GalilFppMarkedCode.code[q.val]? = some (.move 0 d extra) ∧
      GalilFppMarkedCode.code[extra]? = some (.move 8 d n) := by
  have hc := all_kernel_rows q
  simp only [hi, Option.map_some, Option.some.injEq, translated] at hc
  cases hm : GalilFppMarkedCode.code[q.val]? with
  | none => simp [hm] at hc
  | some i =>
    cases i with
    | move t d' extra =>
      have hc' : (t == 0 && d' == d &&
          GalilFppMarkedCode.code[extra]? == some (.move 8 d n)) = true := by
        simpa [hm] using hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      obtain ⟨⟨ht, hd⟩, he⟩ := hc'
      subst t; subst d'
      exact ⟨extra, rfl, he⟩
    | halt => simp [hm] at hc
    | write => simp [hm] at hc
    | read => simp [hm] at hc

theorem emit_code (q : Fin 228) (n : ℕ)
    (hi : GalilFppCode.code[q.val]? = some (.emit n)) :
    GalilFppMarkedCode.code[q.val]? = some (.write 8 8 n) := by
  have hc := all_kernel_rows q
  simpa [hi, translated] using hc

/-- Two actual instructions keep MARKS aligned with A on a right move. -/
theorem move_right (q : Fin 228) (n : ℕ) (x : Config 9)
    (hi : GalilFppCode.code[q.val]? = some (.move 0 true n))
    (hp : x.pc = q.val) (ha : x.pos 8 = x.pos 0) :
    ∃ y qs, Steps GalilFppMarkedCode.code x qs y ∧ qs.length = 2 ∧ y.pc = n ∧
      y.pos 0 = x.pos 0+1 ∧ y.pos 8 = y.pos 0 ∧ y.tape = x.tape ∧
      (∀ t, t ≠ 0 → t ≠ 8 → y.pos t = x.pos t) := by
  obtain ⟨extra, hrow, hextra⟩ := candidate_code q true n hi
  let z : Config 9 := { x with pc := extra, pos := Function.update x.pos 0 (x.pos 0+1) }
  let y : Config 9 := { z with pc := n, pos := Function.update z.pos 8 (z.pos 8+1) }
  have hs : Steps GalilFppMarkedCode.code x [q.val,extra] y := by
    simpa only [hp] using
      (Steps.step x z y _ _ (by rw [hp]; exact hrow) (.right _ _ _)
        (.step z y y _ [] hextra (.right _ _ _) (.nil _)))
  exact ⟨y, _, hs, rfl, rfl, by simp [y, z], by simp [y, z, ha], rfl,
    by intro t h0 h8; simp [y, z, h0, h8]⟩

theorem move_left (q : Fin 228) (n : ℕ) (x : Config 9)
    (hi : GalilFppCode.code[q.val]? = some (.move 0 false n))
    (hp : x.pc = q.val) (ha : x.pos 8 = x.pos 0) (hpos : 0 < x.pos 0) :
    ∃ y qs, Steps GalilFppMarkedCode.code x qs y ∧ qs.length = 2 ∧ y.pc = n ∧
      y.pos 0 = x.pos 0-1 ∧ y.pos 8 = y.pos 0 ∧ y.tape = x.tape ∧
      (∀ t, t ≠ 0 → t ≠ 8 → y.pos t = x.pos t) := by
  obtain ⟨extra, hrow, hextra⟩ := candidate_code q false n hi
  let z : Config 9 := { x with pc := extra, pos := Function.update x.pos 0 (x.pos 0-1) }
  let y : Config 9 := { z with pc := n, pos := Function.update z.pos 8 (z.pos 8-1) }
  have hzpos : 0 < z.pos 8 := by simpa [z, ha] using hpos
  have hs : Steps GalilFppMarkedCode.code x [q.val,extra] y := by
    simpa only [hp] using
      (Steps.step x z y _ _ (by rw [hp]; exact hrow) (.left _ _ _ hpos)
        (.step z y y _ [] hextra (.left _ _ _ hzpos) (.nil _)))
  exact ⟨y, _, hs, rfl, rfl, by simp [y, z], by simp [y, z, ha], rfl,
    by intro t h0 h8; simp [y, z, h0, h8]⟩

/-- Proof-level interpretation of a mark tape; the runtime stores only
cells, never this list of emitted lengths. -/
def markTape (base : ℕ → Fin 9) (out : List ℕ) (i : ℕ) : Fin 9 :=
  if i ∈ out then 8 else base i

theorem markTape_append (base : ℕ → Fin 9) (out : List ℕ) (p : ℕ) :
    Function.update (markTape base out) p 8 = markTape base (out ++ [p]) := by
  funext i
  by_cases hi : i = p
  · subst i; simp [markTape]
  · simp [markTape, hi]

/-- The actual replacement of emit writes exactly the next mark while
preserving every head and every other tape. -/
theorem emit_write (q : Fin 228) (n : ℕ) (x : Config 9)
    (hi : GalilFppCode.code[q.val]? = some (.emit n)) (hp : x.pc = q.val)
    (ha : x.pos 8 = x.pos 0) (base : ℕ → Fin 9) (out : List ℕ)
    (hm : x.tape 8 = markTape base out) :
    ∃ y, Steps GalilFppMarkedCode.code x [q.val] y ∧ y.pc = n ∧ y.pos = x.pos ∧
      y.tape 8 = markTape base (out ++ [x.pos 0]) ∧
      (∀ t, t ≠ 8 → y.tape t = x.tape t) := by
  let y : Config 9 := { x with
    pc := n
    tape := Function.update x.tape 8 (Function.update (x.tape 8) (x.pos 8) 8) }
  have hs : Steps GalilFppMarkedCode.code x [q.val] y := by
    simpa only [hp] using
      (Steps.step x y y _ [] (by rw [hp]; exact emit_code q n hi) (.write _ _ _ _) (.nil _))
  refine ⟨y, hs, rfl, rfl, ?_, ?_⟩
  · simpa [y, ha, hm] using markTape_append base out (x.pos 0)
  · intro t ht
    simp [y, ht]

#print axioms emit_write
#print axioms all_kernel_rows
#print axioms move_right
#print axioms move_left
end PalPeg.GalilFppMarkTransform
