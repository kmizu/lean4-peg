import PalPeg.GalilFppCopy

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilFppCopyInstances
open GalilFppInstruction GalilFppCode GalilFppCopy

def renameInstruction (f : ℕ → ℕ) : Instruction → Instruction
  | .halt => .halt
  | .emit n => .emit (f n)
  | .move t d n => .move t d (f n)
  | .write t s n => .write t s (f n)
  | .read t cs => .read t (cs.map fun p => (p.1, f p.2))

def renameConfig (f : ℕ → ℕ) (x : Config) : Config := { x with pc := f x.pc }

theorem execute_rename (f : ℕ → ℕ) {i : Instruction} {x y : Config} (h : Execute i x y) :
    Execute (renameInstruction f i) (renameConfig f x) (renameConfig f y) := by
  cases h with
  | emit => exact .emit _ _
  | right => exact .right _ _ _
  | left x t n hp => exact .left _ _ _ hp
  | write => exact .write _ _ _ _
  | read x t cs n hc =>
    apply Execute.read
    exact List.mem_map.mpr ⟨_, hc, rfl⟩

theorem steps_rename (f : ℕ → ℕ) {x y : Config} {qs : List ℕ} (h : Steps code x qs y)
    (hc : ∀ q ∈ qs, code[f q]? = (code[q]?).map (renameInstruction f)) :
    Steps code (renameConfig f x) (qs.map f) (renameConfig f y) := by
  induction h with
  | nil => exact .nil _
  | step x y z i qs hi hs rest ih =>
    have ht := hc x.pc (by simp)
    rw [hi] at ht
    exact .step _ _ _ _ _ ht (execute_rename f hs) (ih (by intro q hq; exact hc q (by simp [hq])))

def entry : Fin 5 → ℕ := ![28, 97, 137, 177, 217]
def exitPC : Fin 5 → ℕ := ![2, 69, 109, 149, 189]
def renamePC (j : Fin 5) (q : ℕ) : ℕ :=
  if q = 2 then exitPC j else if 28 ≤ q ∧ q ≤ 35 then entry j + (q - 28) else q

/-- Check all eight instructions in each of the five Scala-generated copies. -/
theorem instances_match : ∀ (j : Fin 5) (q : Fin 8),
    code[renamePC j (q.val + 28)]? =
      (code[q.val + 28]?).map (renameInstruction (renamePC j)) := by decide

def untouched (t : Fin 7) : Instruction → Bool
  | .move u _ _ | .write u _ _ => u != t
  | _ => true

theorem copy_untouched : ∀ (q : Fin 8) (t : Fin 7), t ≠ 3 → t ≠ 4 →
    (code[q.val + 28]?).map (untouched t) = some true := by decide

theorem execute_frame {x y : Config} {i : Instruction} (he : Execute i x y)
    (t : Fin 7) (ht : untouched t i = true) : y.pos t = x.pos t ∧ y.tape t = x.tape t := by
  cases he with
  | right x u k =>
    have hn : u ≠ t := by simpa [untouched] using ht
    simp [Function.update_of_ne (Ne.symm hn)]
  | left x u k hp =>
    have hn : u ≠ t := by simpa [untouched] using ht
    simp [Function.update_of_ne (Ne.symm hn)]
  | write x u s k =>
    have hn : u ≠ t := by simpa [untouched] using ht
    simp [Function.update_of_ne (Ne.symm hn)]
  | _ => exact ⟨rfl, rfl⟩

theorem copy_frame {x y : Config} {qs : List ℕ} (hs : Steps code x qs y) (hin : Inside qs)
    (t : Fin 7) (ht₃ : t ≠ 3) (ht₄ : t ≠ 4) : y.pos t = x.pos t ∧ y.tape t = x.tape t := by
  induction hs with
  | nil => exact ⟨rfl, rfl⟩
  | step x y z i qs hi he hs ih =>
    have hb := of_decide_eq_true (List.all_eq_true.mp hin x.pc (by simp))
    have hc := copy_untouched ⟨x.pc-28, by omega⟩ t ht₃ ht₄
    have hn : x.pc - 28 + 28 = x.pc := by omega
    simp only [hn, hi, Option.map_some, Option.some.injEq] at hc
    obtain ⟨hp, ht⟩ := execute_frame he t hc
    have hin' : Inside qs := by
      exact List.all_eq_true.mpr (fun q hq => List.all_eq_true.mp hin q (by simp [hq]))
    obtain ⟨hp', ht'⟩ := ih hin'
    exact ⟨hp'.trans hp, ht'.trans ht⟩

/-- All generated copySToT calls obey the same execution and data contract;
there is no new assumed macro in the machine. -/
theorem copy_restore_all (j : Fin 5) (n : ℕ) (x : Config) (hpc : x.pc = entry j)
    (hp : x.pos 3 = n) (hleft : x.tape 3 0 = 4) (hend : x.tape 3 (n + 1) = 6)
    (hs : ∀ k, 1 ≤ k → k ≤ n → x.tape 3 k = 8) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 6 * n + 4 ∧ y.pc = exitPC j ∧
      y.pos 3 = n ∧ y.pos 4 = x.pos 4 + n ∧ y.tape 3 = x.tape 3 ∧
      (∀ k, k ≤ x.pos 4 → y.tape 4 k = x.tape 4 k) ∧
      (∀ k, x.pos 4 < k → k ≤ x.pos 4 + n → y.tape 4 k = 8) ∧
      (∀ t, t ≠ 3 → t ≠ 4 → y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  let x₀ : Config := { x with pc := 28 }
  obtain ⟨y, qs, hr, hl, hy, hS, hT, ht, hb, ho, hin⟩ := copy_restore n x₀ rfl hp hleft hend hs
  have hm : ∀ q ∈ qs, code[renamePC j q]? = (code[q]?).map (renameInstruction (renamePC j)) := by
    intro q hq
    have hbounds := of_decide_eq_true (List.all_eq_true.mp hin q hq)
    have hh := instances_match j ⟨q - 28, by omega⟩
    have he : q - 28 + 28 = q := by omega
    simpa only [he] using hh
  have hrun := steps_rename (renamePC j) hr hm
  have hinit : renameConfig (renamePC j) x₀ = x := by
    cases x
    simp_all [renameConfig, renamePC, x₀]
  rw [hinit] at hrun
  refine ⟨renameConfig (renamePC j) y, qs.map (renamePC j), hrun, by simpa using hl,
    ?_, hS, hT, ht, hb, ho, ?_⟩
  · simp [renameConfig, hy, renamePC]
  · intro t ht₃ ht₄
    exact copy_frame hr hin t ht₃ ht₄

#print axioms copy_restore_all
end PalPeg.GalilFppCopyInstances
