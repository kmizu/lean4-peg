import PalPeg.GalilDpCode
import PalPeg.GalilFppMarkedCode

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilDpTransform
open GalilFppWide

def tapeIndex (t : Fin 9) : Fin 12 := ⟨t.val, by omega⟩

/-- DpFinite duplicates every MARKS move/write on SECOND, lifts other
instructions, and replaces FPP halt with a SOURCE-left-marker dispatch. -/
def translated (q : ℕ) (i : Instruction 9) : Bool :=
  match i with
  | .halt => GalilDpCode.code[q]? == some (.read 7 [(4,372)])
  | .move t d n =>
    if t = 8 then
      match GalilDpCode.code[q]? with
      | some (.move t' d' extra) => t' == 8 && d' == d &&
          GalilDpCode.code[extra]? == some (.move 9 d n)
      | _ => false
    else GalilDpCode.code[q]? == some (.move (tapeIndex t) d n)
  | .write t s n =>
    if t = 8 then
      match GalilDpCode.code[q]? with
      | some (.write t' s' extra) => t' == 8 && s' == s &&
          GalilDpCode.code[extra]? == some (.write 9 s n)
      | _ => false
    else GalilDpCode.code[q]? == some (.write (tapeIndex t) s n)
  | .read t cs => GalilDpCode.code[q]? == some (.read (tapeIndex t) cs)

set_option maxHeartbeats 4000000 in
theorem all_marked_rows : ∀ q : Fin 321,
    (GalilFppMarkedCode.code[q.val]?).map (translated q.val) = some true := by decide

theorem write_code (q : Fin 321) (s : Fin 9) (n : ℕ)
    (hi : GalilFppMarkedCode.code[q.val]? = some (.write 8 s n)) :
    ∃ extra, GalilDpCode.code[q.val]? = some (.write 8 s extra) ∧
      GalilDpCode.code[extra]? = some (.write 9 s n) := by
  have hc := all_marked_rows q
  simp only [hi, Option.map_some, Option.some.injEq, translated] at hc
  cases hm : GalilDpCode.code[q.val]? with
  | none => simp [hm] at hc
  | some i =>
    cases i with
    | write t s' extra =>
      have hc' : (t == 8 && s' == s && GalilDpCode.code[extra]? == some (.write 9 s n)) = true := by
        simpa [hm] using hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      obtain ⟨⟨ht, hs⟩, he⟩ := hc'
      subst t; subst s'
      exact ⟨extra, rfl, he⟩
    | halt => simp [hm] at hc
    | move => simp [hm] at hc
    | read => simp [hm] at hc

theorem other_move_code (q : Fin 321) (t : Fin 9) (d : Bool) (n : ℕ)
    (ht : t ≠ 8)
    (hi : GalilFppMarkedCode.code[q.val]? = some (.move t d n)) :
    GalilDpCode.code[q.val]? = some (.move (tapeIndex t) d n) := by
  have hc := all_marked_rows q
  simpa [hi, translated, ht] using hc

theorem other_write_code (q : Fin 321) (t s : Fin 9) (n : ℕ)
    (ht : t ≠ 8)
    (hi : GalilFppMarkedCode.code[q.val]? = some (.write t s n)) :
    GalilDpCode.code[q.val]? = some (.write (tapeIndex t) s n) := by
  have hc := all_marked_rows q
  simpa [hi, translated, ht] using hc

theorem read_code (q : Fin 321) (t : Fin 9) (cs : List (Fin 9 × ℕ))
    (hi : GalilFppMarkedCode.code[q.val]? = some (.read t cs)) :
    GalilDpCode.code[q.val]? = some (.read (tapeIndex t) cs) := by
  have hc := all_marked_rows q
  simpa [hi, translated] using hc

theorem halt_code (q : Fin 321)
    (hi : GalilFppMarkedCode.code[q.val]? = some .halt) :
    GalilDpCode.code[q.val]? = some (.read 7 [(4,372)]) := by
  have hc := all_marked_rows q
  simpa [hi, translated] using hc

/-- Both physical mark copies remain identical after each transformed
write, including marker and zero writes during preparation. -/
theorem duplicate_write (q : Fin 321) (s : Fin 9) (n : ℕ) (x : Config 12)
    (hi : GalilFppMarkedCode.code[q.val]? = some (.write 8 s n)) (hp : x.pc = q.val)
    (hh : x.pos 8 = x.pos 9) (ht : x.tape 8 = x.tape 9) :
    ∃ y qs, Steps GalilDpCode.code x qs y ∧ qs.length = 2 ∧ y.pc = n ∧
      y.pos = x.pos ∧ y.tape 8 = y.tape 9 ∧
      y.tape 8 = Function.update (x.tape 8) (x.pos 8) s ∧
      ∀ t, t ≠ 8 → t ≠ 9 → y.tape t = x.tape t := by
  obtain ⟨extra, hrow, hextra⟩ := write_code q s n hi
  let z : Config 12 := { x with
    pc := extra
    tape := Function.update x.tape 8 (Function.update (x.tape 8) (x.pos 8) s) }
  let y : Config 12 := { z with
    pc := n
    tape := Function.update z.tape 9 (Function.update (z.tape 9) (z.pos 9) s) }
  have hs : Steps GalilDpCode.code x [q.val,extra] y := by
    simpa only [hp] using (Steps.step x z y _ _ (by rw [hp]; exact hrow) (.write _ _ _ _)
      (.step z y y _ [] hextra (.write _ _ _ _) (.nil _)))
  refine ⟨y, _, hs, rfl, rfl, rfl, by simp [y, z, hh, ht], by simp [y, z], ?_⟩
  intro t h8 h9
  simp [y, z, h8, h9]

theorem move_code (q : Fin 321) (d : Bool) (n : ℕ)
    (hi : GalilFppMarkedCode.code[q.val]? = some (.move 8 d n)) :
    ∃ extra, GalilDpCode.code[q.val]? = some (.move 8 d extra) ∧
      GalilDpCode.code[extra]? = some (.move 9 d n) := by
  have hc := all_marked_rows q
  simp only [hi, Option.map_some, Option.some.injEq, translated] at hc
  cases hm : GalilDpCode.code[q.val]? with
  | none => simp [hm] at hc
  | some i =>
    cases i with
    | move t d' extra =>
      have hc' : (t == 8 && d' == d && GalilDpCode.code[extra]? == some (.move 9 d n)) = true := by
        simpa [hm] using hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc'
      obtain ⟨⟨ht, hd⟩, he⟩ := hc'
      subst t; subst d'
      exact ⟨extra, rfl, he⟩
    | halt => simp [hm] at hc
    | write => simp [hm] at hc
    | read => simp [hm] at hc

/-- The duplicated moves keep both mark heads synchronized. Left movement
requires the same positive-head condition as the original machine. -/
theorem duplicate_move (q : Fin 321) (d : Bool) (n : ℕ) (x : Config 12)
    (hi : GalilFppMarkedCode.code[q.val]? = some (.move 8 d n)) (hp : x.pc = q.val)
    (hh : x.pos 8 = x.pos 9) (hl : d = false → 0 < x.pos 8) :
    ∃ y qs, Steps GalilDpCode.code x qs y ∧ qs.length = 2 ∧ y.pc = n ∧
      y.tape = x.tape ∧ y.pos 8 = y.pos 9 ∧
      y.pos 8 = (if d then x.pos 8 + 1 else x.pos 8 - 1) ∧
      ∀ t, t ≠ 8 → t ≠ 9 → y.pos t = x.pos t := by
  obtain ⟨extra, hrow, hextra⟩ := move_code q d n hi
  cases d with
  | false =>
    let z : Config 12 := { x with
      pc := extra
      pos := Function.update x.pos 8 (x.pos 8 - 1) }
    let y : Config 12 := { z with
      pc := n
      pos := Function.update z.pos 9 (z.pos 9 - 1) }
    have hz : 0 < z.pos 9 := by simpa [z, ← hh] using hl rfl
    have hs : Steps GalilDpCode.code x [q.val,extra] y := by
      simpa only [hp] using (Steps.step x z y _ _ (by rw [hp]; exact hrow)
        (.left _ _ _ (hl rfl))
        (.step z y y _ [] hextra (.left _ _ _ hz) (.nil _)))
    refine ⟨y, _, hs, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [y, z, hh]
    · simp [y, z]
    · intro t h8 h9; simp [y, z, h8, h9]
  | true =>
    let z : Config 12 := { x with
      pc := extra
      pos := Function.update x.pos 8 (x.pos 8 + 1) }
    let y : Config 12 := { z with
      pc := n
      pos := Function.update z.pos 9 (z.pos 9 + 1) }
    have hs : Steps GalilDpCode.code x [q.val,extra] y := by
      simpa only [hp] using (Steps.step x z y _ _ (by rw [hp]; exact hrow)
        (.right _ _ _) (.step z y y _ [] hextra (.right _ _ _) (.nil _)))
    refine ⟨y, _, hs, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · simp [y, z, hh]
    · simp [y, z]
    · intro t h8 h9; simp [y, z, h8, h9]

/-- FPP return is an actual SOURCE read, not a meta-level callback.
The search starts without changing any tape or head. -/
theorem dispatch (q : Fin 321) (x : Config 12)
    (hi : GalilFppMarkedCode.code[q.val]? = some .halt)
    (hp : x.pc = q.val) (hs : x.tape 7 (x.pos 7) = 4) :
    Steps GalilDpCode.code x [q.val] { x with pc := 372 } := by
  have hrow := halt_code q hi
  simpa only [hp] using
    (Steps.step x { x with pc := 372 } { x with pc := 372 }
      (.read 7 [(4,372)]) [] (by rw [hp]; exact hrow)
      (.read _ _ _ _ (by simp [hs])) (.nil _))

#print axioms all_marked_rows
#print axioms duplicate_write
#print axioms duplicate_move
#print axioms dispatch
end PalPeg.GalilDpTransform
