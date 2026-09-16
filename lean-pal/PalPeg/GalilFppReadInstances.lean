import PalPeg.GalilFppMaterialize
import PalPeg.GalilFppCopyInstances

set_option autoImplicit false
set_option maxRecDepth 100000
namespace PalPeg.GalilFppReadInstances
open GalilFppInstruction GalilFppCode GalilFppMaterialize
open GalilFppCopyInstances (renameInstruction renameConfig steps_rename untouched execute_frame)

def base : Fin 6 → ℕ := ![10,43,79,119,159,199]
def zeroPC : Fin 6 → ℕ := ![6,38,75,115,155,195]
def onePC : Fin 6 → ℕ := ![9,42,78,118,158,198]
def entry (j : Fin 6) : ℕ := base j + 16
def resultPC (j : Fin 6) (b : Fin 2) : ℕ := if b = 0 then zeroPC j else onePC j
def renamePC (j : Fin 6) (q : ℕ) : ℕ :=
  if q = 6 then zeroPC j else if q = 9 then onePC j else base j + (q-10)

/-- The entire refill/pop/write region matches in all six actual instances. -/
theorem instances_match : ∀ (j : Fin 6) (q : Fin 17),
    code[renamePC j (q.val+10)]? = (code[q.val+10]?).map (renameInstruction (renamePC j)) := by decide

theorem region_untouched : ∀ (q : Fin 17) (t : Fin 7), t ≠ 2 → t ≠ 5 → t ≠ 6 →
    (code[q.val+10]?).map (untouched t) = some true := by decide

theorem region_frame {x y : Config} {qs : List ℕ} (hs : Steps code x qs y) (hin : Region qs)
    (t : Fin 7) (ht₂ : t ≠ 2) (ht₅ : t ≠ 5) (ht₆ : t ≠ 6) :
    y.pos t = x.pos t ∧ y.tape t = x.tape t := by
  induction hs with
  | nil => exact ⟨rfl, rfl⟩
  | step x y z i qs hi he hs ih =>
    have hb := of_decide_eq_true (List.all_eq_true.mp hin x.pc (by simp))
    have hc := region_untouched ⟨x.pc-10, by omega⟩ t ht₂ ht₅ ht₆
    have hn : x.pc-10+10 = x.pc := by omega
    simp only [hn, hi, Option.map_some, Option.some.injEq] at hc
    obtain ⟨hp, ht⟩ := execute_frame he t hc
    have hin' : Region qs := List.all_eq_true.mpr (fun q hq => List.all_eq_true.mp hin q (by simp [hq]))
    obtain ⟨hp', ht'⟩ := ih hin'
    exact ⟨hp'.trans hp, ht'.trans ht⟩

/-- Actual lazy FIFO materialization for every deltaRead, including the
forward reader at PC59. A/B/S/T are preserved, C changes at only its head. -/
theorem dequeue_all (j : Fin 6) (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hp : x.pc = entry j) (hc : x.tape 2 (x.pos 2) = 6) (hq : QueueAt x (b :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = resultPC j b ∧ y.pos 2 = x.pos 2 ∧
      y.tape 2 (x.pos 2) = bitSymbol b ∧ QueueAt y rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧
      (∀ t, t ≠ 2 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  let x₀ : Config := { x with pc := 26 }
  obtain ⟨y, qs, hs, hpc, hpos, hcell, hyq, hframe, hin⟩ := dequeue b rest x₀ rfl hc hq
  have hm : ∀ q ∈ qs, code[renamePC j q]? = (code[q]?).map (renameInstruction (renamePC j)) := by
    intro q hq
    have hb := of_decide_eq_true (List.all_eq_true.mp hin q hq)
    have hh := instances_match j ⟨q-10, by omega⟩
    have he : q-10+10 = q := by omega
    simpa only [he] using hh
  have hr := steps_rename (renamePC j) hs hm
  have hx : renameConfig (renamePC j) x₀ = x := by
    cases x
    simp_all [renameConfig, renamePC, entry, x₀]
  rw [hx] at hr
  refine ⟨renameConfig (renamePC j) y, qs.map (renamePC j), hr, ?_, hpos, hcell, hyq, hframe, ?_⟩
  · change renamePC j y.pc = resultPC j b
    rw [hpc]
    fin_cases b <;> simp [destination, renamePC, resultPC]
  · intro t ht₂ ht₅ ht₆
    exact region_frame hs hin t ht₂ ht₅ ht₆

theorem cached_all (j : Fin 6) (b : Fin 2) (x : Config) (hp : x.pc = entry j)
    (hc : x.tape 2 (x.pos 2) = bitSymbol b) :
    Steps code x [entry j] { x with pc := resultPC j b } := by
  have hi : code[x.pc]? = some (.read 2 [(7,zeroPC j),(8,onePC j),(6,base j)]) := by
    rw [hp]; fin_cases j <;> rfl
  have he : Execute (.read 2 [(7,zeroPC j),(8,onePC j),(6,base j)]) x { x with pc := resultPC j b } :=
    .read _ _ _ _ (by rw [hc]; fin_cases b <;> simp [bitSymbol, resultPC])
  simpa only [hp] using Steps.step x _ _ _ [] hi he (.nil _)

/-- The forward scan's alias dispatch enters lazy materialization on blank
C and returns to the actual zero/one continuation, preserving A/B/S/T. -/
theorem forward_blank (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hp : x.pc = 39) (hc : x.tape 2 (x.pos 2) = 6) (hq : QueueAt x (b :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = (if b = 0 then 38 else 42) ∧ y.pos 2 = x.pos 2 ∧
      y.tape 2 (x.pos 2) = bitSymbol b ∧ QueueAt y rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧
      (∀ t, t ≠ 2 → t ≠ 5 → t ≠ 6 → y.pos t = x.pos t ∧ y.tape t = x.tape t) := by
  let u : Config := { x with pc := 59 }
  have hi : code[x.pc]? = some (.read 2 [(7,59),(8,59),(6,59)]) := by rw [hp]; rfl
  have he : Execute (.read 2 [(7,59),(8,59),(6,59)]) x u := .read _ _ _ _ (by simp [hc])
  obtain ⟨y, qs, hs, hpc, hpos, hcell, hyq, hframe, hother⟩ := dequeue_all 1 b rest u rfl hc hq
  refine ⟨y, 39 :: qs, ?_, hpc, hpos, hcell, hyq, hframe, hother⟩
  simpa only [hp] using Steps.step x u y _ qs hi he hs

#print axioms forward_blank
#print axioms dequeue_all
end PalPeg.GalilFppReadInstances
