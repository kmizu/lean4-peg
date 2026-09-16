import PalPeg.GalilFppCode

set_option autoImplicit false
namespace PalPeg.GalilFppCopy
open GalilFppInstruction GalilFppCode

def Inside (qs : List ℕ) : Prop := qs.all (fun q => decide (28 ≤ q ∧ q ≤ 35)) = true

theorem steps_append {x y z : Config} {as bs : List ℕ}
    (h : Steps code x as y) (g : Steps code y bs z) : Steps code x (as ++ bs) z := by
  induction h with
  | nil => exact g
  | step x y z i qs hi hs rest ih => exact .step _ _ _ _ _ hi hs (ih g)

/-- One descent of Scala Builder.copySToT at its first generated entry. -/
def copyUnit (x : Config) : Config :=
  { x with
    pc := 28
    pos := Function.update (Function.update x.pos 4 (x.pos 4 + 1)) 3 (x.pos 3 - 1)
    tape := Function.update x.tape 4 (Function.update (x.tape 4) (x.pos 4 + 1) 8) }

theorem copy_unit (x : Config) (hpc : x.pc = 28) (hp : 0 < x.pos 3)
    (hs : x.tape 3 (x.pos 3) = 8) : Steps code x [28, 35, 34, 33] (copyUnit x) := by
  let x₁ : Config := { x with pc := 35 }
  let x₂ : Config := { x₁ with pc := 34, pos := Function.update x₁.pos 4 (x₁.pos 4 + 1) }
  let x₃ : Config := { x₂ with
    pc := 33
    tape := Function.update x₂.tape 4 (Function.update (x₂.tape 4) (x₂.pos 4) 8) }
  have hr : Execute (.read 3 [(4,32),(8,35)]) x x₁ := .read x 3 _ 35 (by simp [hs])
  have h₁ : Execute (.move 4 true 34) x₁ x₂ := .right _ _ _
  have h₂ : Execute (.write 4 8 33) x₂ x₃ := .write _ _ _ _
  have h₃ : Execute (.move 3 false 28) x₃ (copyUnit x) := by
    have hh := Execute.left x₃ 3 28 (by simpa [x₃, x₂, x₁] using hp)
    simpa [x₃, x₂, x₁, copyUnit] using hh
  have hlookup : code[x.pc]? = some (.read 3 [(4,32),(8,35)]) := by rw [hpc]; rfl
  have h := Steps.step x x₁ (copyUnit x) _ _ hlookup hr
    (.step x₁ x₂ _ _ _ rfl h₁ (.step x₂ x₃ _ _ _ rfl h₂
      (.step x₃ (copyUnit x) _ _ [] rfl h₃ (.nil _))))
  simpa only [hpc] using h

/-- Descend over n ones with exactly 4*n actual instructions. The source
tape is unchanged and T advances n cells. Restoration is a separate phase. -/
theorem copy_down (n : ℕ) (x : Config) (hpc : x.pc = 28) (hp : x.pos 3 = n)
    (hs : ∀ j, 1 ≤ j → j ≤ n → x.tape 3 j = 8) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 4 * n ∧ y.pc = 28 ∧ y.pos 3 = 0 ∧
      y.pos 4 = x.pos 4 + n ∧ y.tape 3 = x.tape 3 ∧
      (∀ j, j ≤ x.pos 4 → y.tape 4 j = x.tape 4 j) ∧
      (∀ j, x.pos 4 < j → j ≤ x.pos 4 + n → y.tape 4 j = 8) ∧ Inside qs := by
  induction n generalizing x with
  | zero => exact ⟨x, [], .nil _, rfl, hpc, hp, by omega, rfl, by intros; rfl, by intros; omega, rfl⟩
  | succ n ih =>
    have hu := copy_unit x hpc (by omega) (hs (x.pos 3) (by omega) (by omega))
    obtain ⟨y, qs, hr, hl, hy, hS, hT, htape, hbelow, hones, hinside⟩ := ih (copyUnit x) rfl
      (by simp [copyUnit, hp]) (by intro j hj hn; simpa [copyUnit] using hs j hj (by omega))
    refine ⟨y, [28,35,34,33] ++ qs, steps_append hu hr, ?_, hy, hS, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hl]
      omega
    · simpa [copyUnit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hT
    · simpa [copyUnit] using htape
    · intro j hj
      have hb := hbelow j (by simp [copyUnit]; omega)
      have hn : x.pos 4 + 1 ≠ j := by omega
      simpa [copyUnit, hn, Ne.symm hn] using hb
    · intro j hj hk
      by_cases he : j = x.pos 4 + 1
      · subst j
        have hb := hbelow (x.pos 4 + 1) (by simp [copyUnit])
        simpa [copyUnit] using hb
      · exact hones j (by simp [copyUnit]; omega) (by simp [copyUnit]; omega)
    · simpa [Inside, List.all_append] using hinside

def restoreUnit (x : Config) : Config :=
  { x with pc := 29, pos := Function.update x.pos 3 (x.pos 3 + 1) }

theorem restore_unit (x : Config) (hpc : x.pc = 29) (hs : x.tape 3 (x.pos 3) = 8) :
    Steps code x [29,31] (restoreUnit x) := by
  let y : Config := { x with pc := 31 }
  have hr : Execute (.read 3 [(6,30),(8,31)]) x y := .read x 3 _ 31 (by simp [hs])
  have hm : Execute (.move 3 true 29) y (restoreUnit x) := .right _ _ _
  have hi : code[x.pc]? = some (.read 3 [(6,30),(8,31)]) := by rw [hpc]; rfl
  have hh := Steps.step x y _ _ _ hi hr (.step y (restoreUnit x) _ _ [] rfl hm (.nil _))
  simpa only [hpc] using hh

theorem restore_scan (n : ℕ) (x : Config) (hpc : x.pc = 29) (hp : 1 ≤ x.pos 3)
    (hend : x.tape 3 (x.pos 3 + n) = 6)
    (hs : ∀ j, j < n → x.tape 3 (x.pos 3 + j) = 8) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 2 * n + 2 ∧ y.pc = 2 ∧
      y.pos 3 = x.pos 3 + n - 1 ∧ y.pos 4 = x.pos 4 ∧ y.tape = x.tape ∧ Inside qs := by
  induction n generalizing x with
  | zero =>
    let y : Config := { x with pc := 30 }
    let z : Config := { y with pc := 2, pos := Function.update y.pos 3 (y.pos 3 - 1) }
    have hr : Execute (.read 3 [(6,30),(8,31)]) x y := .read x 3 _ 30 (by simpa using hend)
    have hm : Execute (.move 3 false 2) y z := .left y 3 2 hp
    have hi : code[x.pc]? = some (.read 3 [(6,30),(8,31)]) := by rw [hpc]; rfl
    have hh := Steps.step x y z _ _ hi hr (.step y z z _ [] rfl hm (.nil _))
    refine ⟨z, [29,30], by simpa only [hpc] using hh, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · simp [z, y]
    · simp [z, y]
  | succ n ih =>
    have hu := restore_unit x hpc (by simpa using hs 0 (by omega))
    obtain ⟨y, qs, hr, hl, hy, hS, hT, ht, hinside⟩ := ih (restoreUnit x) rfl
      (by simp [restoreUnit]) (by simpa [restoreUnit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend)
      (by intro j hj; simpa [restoreUnit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs (j+1) (by omega))
    refine ⟨y, [29,31] ++ qs, steps_append hu hr, ?_, hy, ?_, ?_, ht, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hl]; omega
    · simpa [restoreUnit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hS
    · simpa [restoreUnit] using hT
    · simpa [Inside, List.all_append] using hinside

/-- Full first copySToT instance: exactly 6*n+4 instructions, S restored,
T advanced n cells, and control returned to the T-loop at PC 2. -/
theorem copy_restore (n : ℕ) (x : Config) (hpc : x.pc = 28) (hp : x.pos 3 = n)
    (hleft : x.tape 3 0 = 4) (hend : x.tape 3 (n + 1) = 6)
    (hs : ∀ j, 1 ≤ j → j ≤ n → x.tape 3 j = 8) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 6 * n + 4 ∧ y.pc = 2 ∧
      y.pos 3 = n ∧ y.pos 4 = x.pos 4 + n ∧ y.tape 3 = x.tape 3 ∧
      (∀ j, j ≤ x.pos 4 → y.tape 4 j = x.tape 4 j) ∧
      (∀ j, x.pos 4 < j → j ≤ x.pos 4 + n → y.tape 4 j = 8) ∧ Inside qs := by
  obtain ⟨d, ds, hd, hdl, hdpc, hdS, hdT, hdt, hbelow, hones, hdinside⟩ := copy_down n x hpc hp hs
  let r : Config := { d with pc := 32 }
  let s : Config := { r with pc := 29, pos := Function.update r.pos 3 (r.pos 3 + 1) }
  have hr : Execute (.read 3 [(4,32),(8,35)]) d r := .read d 3 _ 32 (by simp [hdS, hdt, hleft])
  have hm : Execute (.move 3 true 29) r s := .right _ _ _
  have hi : code[d.pc]? = some (.read 3 [(4,32),(8,35)]) := by rw [hdpc]; rfl
  have hturn := Steps.step d r s _ _ hi hr (.step r s s _ [] rfl hm (.nil _))
  have hturn' : Steps code d [28,32] s := by simpa only [hdpc] using hturn
  obtain ⟨y, qs, hy, hyl, hypc, hyS, hyT, hyt, hyinside⟩ := restore_scan n s rfl
    (by simp [s, r, hdS]) (by simpa [s, r, hdS, hdt, Nat.add_comm] using hend)
    (by intro j hj; simpa [s, r, hdS, hdt, Nat.add_comm] using hs (j+1) (by omega) (by omega))
  refine ⟨y, ds ++ ([28,32] ++ qs), steps_append hd (steps_append hturn' hy), ?_, hypc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, hdl, hyl]; omega
  · simpa [s, r, hdS] using hyS
  · simpa [s, r, hdT] using hyT
  · rw [hyt]; exact hdt
  · rw [hyt]; exact hbelow
  · rw [hyt]; exact hones
  · simpa [Inside, List.all_append] using And.intro hdinside hyinside

#print axioms copy_restore
#print axioms copy_down
end PalPeg.GalilFppCopy
