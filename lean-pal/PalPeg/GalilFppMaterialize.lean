import PalPeg.GalilFppCopy

set_option autoImplicit false
namespace PalPeg.GalilFppMaterialize
open GalilFppInstruction GalilFppCode GalilFppCopy

def bitSymbol (b : Fin 2) : Fin 9 := if b = 0 then 7 else 8
def destination (b : Fin 2) : ℕ := 6 + 3 * b.val

def popFront (x : Config) : Config :=
  { x with
    pos := Function.update x.pos 6 (x.pos 6 - 1)
    tape := Function.update x.tape 6 (Function.update (x.tape 6) (x.pos 6) 6) }

def materialized (b : Fin 2) (x : Config) : Config :=
  { popFront x with
    pc := destination b
    tape := Function.update (popFront x).tape 2
      (Function.update (x.tape 2) (x.pos 2) (bitSymbol b)) }

/-- A cached delta bit needs one read and does not touch any tape or head. -/
theorem cached (b : Fin 2) (x : Config) (hpc : x.pc = 26)
    (hbit : x.tape 2 (x.pos 2) = bitSymbol b) :
    Steps code x [26] { x with pc := destination b } := by
  have hr : Execute (.read 2 [(7,6),(8,9),(6,10)]) x { x with pc := destination b } :=
    .read x 2 _ _ (by rw [hbit]; fin_cases b <;> simp [bitSymbol, destination])
  have hi : code[x.pc]? = some (.read 2 [(7,6),(8,9),(6,10)]) := by rw [hpc]; rfl
  have hh := Steps.step _ _ _ _ [] hi hr (.nil _)
  simpa only [hpc] using hh

/-- On a blank C cell and a nonempty FRONT, the actual first deltaRead
instance consumes exactly one bit and materializes it in five instructions. -/
theorem pop_front (b : Fin 2) (x : Config) (hpc : x.pc = 10)
    (hfront : x.tape 6 (x.pos 6) = bitSymbol b)
    (hpos : 0 < x.pos 6) :
    Steps code x [10,14 + 3*b.val,13 + 3*b.val,12 + 3*b.val] (materialized b x) := by
  let x₁ : Config := x
  let x₂ : Config := { x₁ with pc := 14 + 3*b.val }
  let x₃ : Config := { x₂ with
    pc := 13 + 3*b.val
    tape := Function.update x₂.tape 6 (Function.update (x₂.tape 6) (x₂.pos 6) 6) }
  let x₄ : Config := { x₃ with pc := 12 + 3*b.val, pos := Function.update x₃.pos 6 (x₃.pos 6 - 1) }
  have h₁ : Execute (.read 6 [(4,11),(7,14),(8,17)]) x₁ x₂ := by
    apply Execute.read
    change (x.tape 6 (x.pos 6), 14 + 3*b.val) ∈ _
    rw [hfront]
    fin_cases b <;> simp [bitSymbol]
  have h₂ : Execute (.write 6 6 (13 + 3*b.val)) x₂ x₃ := .write _ _ _ _
  have h₃ : Execute (.move 6 false (12 + 3*b.val)) x₃ x₄ := .left _ _ _ hpos
  have h₄ : Execute (.write 2 (bitSymbol b) (destination b)) x₄ (materialized b x) := by
    have hh := Execute.write x₄ 2 (bitSymbol b) (destination b)
    simpa [x₄, x₃, x₂, x₁, materialized, popFront] using hh
  have hi₁ : code[x₁.pc]? = some (.read 6 [(4,11),(7,14),(8,17)]) := by change code[x.pc]? = _; rw [hpc]; rfl
  have hi₂ : code[x₂.pc]? = some (.write 6 6 (13 + 3*b.val)) := by fin_cases b <;> rfl
  have hi₃ : code[x₃.pc]? = some (.move 6 false (12 + 3*b.val)) := by fin_cases b <;> rfl
  have hi₄ : code[x₄.pc]? = some (.write 2 (bitSymbol b) (destination b)) := by fin_cases b <;> rfl
  have hh := Steps.step x₁ x₂ _ _ _ hi₁ h₁
    (.step x₂ x₃ _ _ _ hi₂ h₂ (.step x₃ x₄ _ _ _ hi₃ h₃
      (.step x₄ (materialized b x) _ _ [] hi₄ h₄ (.nil _))))
  simpa only [x₁, hpc] using hh

theorem from_front (b : Fin 2) (x : Config) (hpc : x.pc = 26)
    (hblank : x.tape 2 (x.pos 2) = 6) (hfront : x.tape 6 (x.pos 6) = bitSymbol b)
    (hpos : 0 < x.pos 6) :
    Steps code x [26,10,14 + 3*b.val,13 + 3*b.val,12 + 3*b.val] (materialized b x) := by
  have hi : code[x.pc]? = some (.read 2 [(7,6),(8,9),(6,10)]) := by rw [hpc]; rfl
  have he : Execute (.read 2 [(7,6),(8,9),(6,10)]) x { x with pc := 10 } :=
    .read x 2 _ 10 (by simp [hblank])
  have ht := pop_front b { x with pc := 10 } rfl hfront hpos
  simpa [hpc, materialized, popFront] using Steps.step x _ _ _ _ hi he ht

theorem materialized_cell (b : Fin 2) (x : Config) :
    (materialized b x).pos 2 = x.pos 2 ∧
    (materialized b x).tape 2 (x.pos 2) = bitSymbol b ∧
    (materialized b x).pos 6 = x.pos 6 - 1 ∧
    (materialized b x).tape 6 (x.pos 6) = 6 := by
  simp [materialized, popFront]

def transferBit (b : Fin 2) (x : Config) : Config :=
  { x with
    pc := 11
    pos := Function.update (Function.update x.pos 5 (x.pos 5 - 1)) 6 (x.pos 6 + 1)
    tape := Function.update
      (Function.update x.tape 5 (Function.update (x.tape 5) (x.pos 5) 6))
      6 (Function.update (x.tape 6) (x.pos 6 + 1) (bitSymbol b)) }

/-- The refill loop erases one BACK cell and pushes its bit onto FRONT. -/
theorem transfer_bit (b : Fin 2) (x : Config) (hpc : x.pc = 11)
    (hbit : x.tape 5 (x.pos 5) = bitSymbol b) (hpos : 0 < x.pos 5) :
    Steps code x [11,21 + 4*b.val,20 + 4*b.val,19 + 4*b.val,18 + 4*b.val]
      (transferBit b x) := by
  let x₁ : Config := { x with pc := 21 + 4*b.val }
  let x₂ : Config := { x₁ with
    pc := 20 + 4*b.val
    tape := Function.update x₁.tape 5 (Function.update (x₁.tape 5) (x₁.pos 5) 6) }
  let x₃ : Config := { x₂ with
    pc := 19 + 4*b.val
    pos := Function.update x₂.pos 5 (x₂.pos 5 - 1) }
  let x₄ : Config := { x₃ with
    pc := 18 + 4*b.val
    pos := Function.update x₃.pos 6 (x₃.pos 6 + 1) }
  have h₀ : Execute (.read 5 [(4,10),(7,21),(8,25)]) x x₁ := by
    apply Execute.read
    rw [hbit]
    fin_cases b <;> simp [bitSymbol]
  have h₁ : Execute (.write 5 6 (20 + 4*b.val)) x₁ x₂ := .write _ _ _ _
  have h₂ : Execute (.move 5 false (19 + 4*b.val)) x₂ x₃ := .left _ _ _ hpos
  have h₃ : Execute (.move 6 true (18 + 4*b.val)) x₃ x₄ := .right _ _ _
  have h₄ : Execute (.write 6 (bitSymbol b) 11) x₄ (transferBit b x) := by
    have hh := Execute.write x₄ 6 (bitSymbol b) 11
    simpa [x₄, x₃, x₂, x₁, transferBit] using hh
  have hi₀ : code[x.pc]? = some (.read 5 [(4,10),(7,21),(8,25)]) := by rw [hpc]; rfl
  have hi₁ : code[x₁.pc]? = some (.write 5 6 (20 + 4*b.val)) := by fin_cases b <;> rfl
  have hi₂ : code[x₂.pc]? = some (.move 5 false (19 + 4*b.val)) := by fin_cases b <;> rfl
  have hi₃ : code[x₃.pc]? = some (.move 6 true (18 + 4*b.val)) := by fin_cases b <;> rfl
  have hi₄ : code[x₄.pc]? = some (.write 6 (bitSymbol b) 11) := by fin_cases b <;> rfl
  have hh := Steps.step x x₁ _ _ _ hi₀ h₀ (.step x₁ x₂ _ _ _ hi₁ h₁
    (.step x₂ x₃ _ _ _ hi₂ h₂ (.step x₃ x₄ _ _ _ hi₃ h₃
      (.step x₄ (transferBit b x) _ _ [] hi₄ h₄ (.nil _)))))
  simpa only [hpc] using hh

/- Lists describe stacks from their top towards the left-end marker. -/
def StackAt (t : ℕ → Fin 9) : ℕ → List (Fin 2) → Prop
  | h, [] => h = 0 ∧ t 0 = 4
  | h, b :: bs => 0 < h ∧ t h = bitSymbol b ∧ StackAt t (h - 1) bs

theorem stack_congr {t u : ℕ → Fin 9} {h : ℕ} {bs : List (Fin 2)}
    (hs : StackAt t h bs) (he : ∀ j, j ≤ h → t j = u j) : StackAt u h bs := by
  induction bs generalizing h with
  | nil => exact ⟨hs.1, (he 0 (by omega)).symm.trans hs.2⟩
  | cons b bs ih =>
    exact ⟨hs.1, (he h (by omega)).symm.trans hs.2.1,
      ih hs.2.2 (fun j hj => he j (by omega))⟩

theorem transfer_stacks (b : Fin 2) (bs fs : List (Fin 2)) (x : Config)
    (hb : StackAt (x.tape 5) (x.pos 5) (b :: bs))
    (hf : StackAt (x.tape 6) (x.pos 6) fs) :
    StackAt ((transferBit b x).tape 5) ((transferBit b x).pos 5) bs ∧
    StackAt ((transferBit b x).tape 6) ((transferBit b x).pos 6) (b :: fs) := by
  simp only [transferBit, Function.update_self, Function.update_of_ne (by decide : (5 : Fin 7) ≠ 6)]
  constructor
  · apply stack_congr hb.2.2
    intro j hj
    have hn : j ≠ x.pos 5 := by have := hb.1; omega
    simp [Function.update_of_ne hn]
  · refine ⟨by omega, by simp, ?_⟩
    simp only [Nat.add_sub_cancel]
    apply stack_congr hf
    intro j hj
    have hn : j ≠ x.pos 6 + 1 := by omega
    simp [Function.update_of_ne hn]

def Region (qs : List ℕ) : Prop := qs.all (fun q => decide (10 ≤ q ∧ q ≤ 26)) = true

/-- Arbitrarily many actual refill iterations reverse BACK onto FRONT. -/
theorem transfer_all (bs fs : List (Fin 2)) (x : Config) (hpc : x.pc = 11)
    (hb : StackAt (x.tape 5) (x.pos 5) bs)
    (hf : StackAt (x.tape 6) (x.pos 6) fs) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5 * bs.length ∧ y.pc = 11 ∧
      StackAt (y.tape 5) (y.pos 5) [] ∧
      StackAt (y.tape 6) (y.pos 6) (bs.reverse ++ fs) ∧
      y.pos 2 = x.pos 2 ∧ y.tape 2 = x.tape 2 ∧ Region qs := by
  induction bs generalizing fs x with
  | nil => exact ⟨x, [], .nil _, by simp, hpc, hb, by simpa using hf, rfl, rfl, rfl⟩
  | cons b bs ih =>
    have ht := transfer_bit b x hpc hb.2.1 hb.1
    obtain ⟨hb', hf'⟩ := transfer_stacks b bs fs x hb hf
    obtain ⟨y, qs, hs, hl, hp, hyb, hyf, hcp, hct, hin⟩ := ih (b :: fs) (transferBit b x) rfl hb' hf'
    refine ⟨y, [11,21 + 4*b.val,20 + 4*b.val,19 + 4*b.val,18 + 4*b.val] ++ qs,
      steps_append ht hs, ?_, hp, hyb, ?_, ?_, ?_, ?_⟩
    · simp [hl, Nat.mul_add, Nat.add_comm]; omega
    · simpa [List.reverse_cons, List.append_assoc] using hyf
    · simpa [transferBit] using hcp
    · simpa [transferBit] using hct
    · fin_cases b <;> simpa [Region, List.all_append] using hin

/-- Refill exits at the FRONT reader after exactly 5n+1 instructions.
With an initially empty FRONT, its top is the oldest BACK bit. -/
theorem refill (bs fs : List (Fin 2)) (x : Config) (hpc : x.pc = 11)
    (hb : StackAt (x.tape 5) (x.pos 5) bs)
    (hf : StackAt (x.tape 6) (x.pos 6) fs) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5 * bs.length + 1 ∧ y.pc = 10 ∧
      StackAt (y.tape 5) (y.pos 5) [] ∧
      StackAt (y.tape 6) (y.pos 6) (bs.reverse ++ fs) ∧
      y.pos 2 = x.pos 2 ∧ y.tape 2 = x.tape 2 ∧ Region qs := by
  obtain ⟨y, qs, hs, hl, hp, hyb, hyf, hcp, hct, hin⟩ := transfer_all bs fs x hpc hb hf
  have hmarker : y.tape 5 (y.pos 5) = 4 := by rw [hyb.1]; exact hyb.2
  have hi : code[y.pc]? = some (.read 5 [(4,10),(7,21),(8,25)]) := by rw [hp]; rfl
  have he : Execute (.read 5 [(4,10),(7,21),(8,25)]) y { y with pc := 10 } :=
    .read y 5 _ 10 (by simp [hmarker])
  have ht : Steps code y [11] { y with pc := 10 } := by
    simpa only [hp] using Steps.step y { y with pc := 10 } _ _ [] hi he (.nil _)
  exact ⟨{ y with pc := 10 }, qs ++ [11], steps_append hs ht,
    by simp [hl], rfl, hyb, hyf, hcp, hct, by simpa [Region, List.all_append] using hin⟩

theorem pop_stacks (b : Fin 2) (bs fs : List (Fin 2)) (x : Config)
    (hb : StackAt (x.tape 5) (x.pos 5) bs)
    (hf : StackAt (x.tape 6) (x.pos 6) (b :: fs)) :
    StackAt ((materialized b x).tape 5) ((materialized b x).pos 5) bs ∧
    StackAt ((materialized b x).tape 6) ((materialized b x).pos 6) fs := by
  constructor
  · simpa [materialized, popFront] using hb
  · simp only [materialized, popFront, Function.update_self,
      Function.update_of_ne (by decide : (6 : Fin 7) ≠ 2)]
    apply stack_congr hf.2.2
    intro j hj
    have hn : j ≠ x.pos 6 := by have := hf.1; omega
    simp [Function.update_of_ne hn]

/-- Empty FRONT is refilled and the oldest queued bit is materialized in C.
The remaining queue is exactly the tail, not merely the same multiset. -/
theorem from_back (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hpc : x.pc = 26) (hblank : x.tape 2 (x.pos 2) = 6)
    (hb : StackAt (x.tape 5) (x.pos 5) ((b :: rest).reverse))
    (hf : StackAt (x.tape 6) (x.pos 6) []) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5 * (b :: rest).length + 7 ∧
      y.pc = destination b ∧ y.pos 2 = x.pos 2 ∧
      y.tape 2 (x.pos 2) = bitSymbol b ∧
      StackAt (y.tape 5) (y.pos 5) [] ∧ StackAt (y.tape 6) (y.pos 6) rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧ Region qs := by
  let x₁ : Config := { x with pc := 10 }
  let x₂ : Config := { x with pc := 11 }
  have hi : code[x.pc]? = some (.read 2 [(7,6),(8,9),(6,10)]) := by rw [hpc]; rfl
  have he : Execute (.read 2 [(7,6),(8,9),(6,10)]) x x₁ :=
    .read x 2 _ 10 (by simp [hblank])
  have hm : x.tape 6 (x.pos 6) = 4 := by rw [hf.1]; exact hf.2
  have he' : Execute (.read 6 [(4,11),(7,14),(8,17)]) x₁ x₂ :=
    .read x₁ 6 _ 11 (by simp [x₁, hm])
  have enter : Steps code x [26,10] x₂ := by
    simpa only [hpc] using Steps.step x x₁ _ _ _ hi he
      (.step x₁ x₂ _ _ [] rfl he' (.nil _))
  obtain ⟨z, qs, hs, hl, hp, hzb, hzf, hcp, hct, hin⟩ :=
    refill ((b :: rest).reverse) [] x₂ rfl hb hf
  have hzfront : StackAt (z.tape 6) (z.pos 6) (b :: rest) := by simpa using hzf
  have ht := pop_front b z hp hzfront.2.1 hzfront.1
  obtain ⟨hfinalb, hfinalf⟩ := pop_stacks b [] rest z hzb hzfront
  refine ⟨materialized b z, [26,10] ++ qs ++ [10,14+3*b.val,13+3*b.val,12+3*b.val],
    steps_append (steps_append enter hs) ht, ?_, rfl, ?_, ?_, hfinalb, hfinalf, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse] at hl ⊢
    omega
  · simpa [materialized, popFront, x₂] using hcp
  · have hp' : x.pos 2 = z.pos 2 := hcp.symm
    rw [hp']
    exact (materialized_cell b z).2.1
  · simp [materialized, popFront, hcp, hct, x₂]
  · fin_cases b <;> simpa [Region, List.all_append] using hin

/-- The queue abstraction uses FRONT followed by reversed BACK. -/
def QueueAt (x : Config) (q : List (Fin 2)) : Prop :=
  ∃ bs fs, StackAt (x.tape 5) (x.pos 5) bs ∧
    StackAt (x.tape 6) (x.pos 6) fs ∧ q = fs ++ bs.reverse

theorem stack_height {t : ℕ → Fin 9} {h : ℕ} {bs : List (Fin 2)}
    (hs : StackAt t h bs) : h = bs.length := by
  induction bs generalizing h with
  | nil => exact hs.1
  | cons b bs ih =>
    have hh := ih hs.2.2
    have hp := hs.1
    simp only [List.length_cons]
    omega

/-- BACK's potential pays for a complete refill; every dequeue costs at
most seven instructions plus released potential. -/
theorem dequeue_cost (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hpc : x.pc = 26) (hblank : x.tape 2 (x.pos 2) = 6)
    (hq : QueueAt x (b :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = destination b ∧
      y.pos 2 = x.pos 2 ∧ y.tape 2 (x.pos 2) = bitSymbol b ∧ QueueAt y rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧ Region qs ∧
      qs.length + 5*y.pos 5 ≤ 7 + 5*x.pos 5 := by
  obtain ⟨bs, fs, hb, hf, hq⟩ := hq
  cases fs with
  | nil =>
    have hbs : bs = (b :: rest).reverse := by
      have hh := congrArg List.reverse hq
      simpa using hh.symm
    rw [hbs] at hb
    obtain ⟨y, qs, hs, hcost, hp, hpos, hcell, hyb, hyf, hframe, hin⟩ := from_back b rest x hpc hblank hb hf
    have hxB := stack_height hb
    have hyB := stack_height hyb
    refine ⟨y, qs, hs, hp, hpos, hcell, ⟨[], rest, hyb, hyf, by simp⟩, hframe, hin,?_⟩
    simp only [List.length_reverse] at hxB
    simp only [List.length_nil] at hyB
    omega
  | cons a fs =>
    have hh : b = a ∧ rest = fs ++ bs.reverse := by simpa using hq
    have ha := hh.1
    subst a
    have ht := from_front b x hpc hblank hf.2.1 hf.1
    obtain ⟨hyb, hyf⟩ := pop_stacks b bs fs x hb hf
    obtain ⟨hpos, hcell, _⟩ := materialized_cell b x
    exact ⟨materialized b x, _, ht, rfl, hpos, hcell, ⟨bs, fs, hyb, hyf, hh.2⟩,
      by simp [materialized, popFront], by fin_cases b <;> rfl, by simp [materialized, popFront]⟩

/-- Compatibility contract; cost-aware callers should use dequeue_cost. -/
theorem dequeue (b : Fin 2) (rest : List (Fin 2)) (x : Config)
    (hpc : x.pc = 26) (hblank : x.tape 2 (x.pos 2) = 6)
    (hq : QueueAt x (b :: rest)) :
    ∃ y qs, Steps code x qs y ∧ y.pc = destination b ∧
      y.pos 2 = x.pos 2 ∧ y.tape 2 (x.pos 2) = bitSymbol b ∧ QueueAt y rest ∧
      y.tape 2 = Function.update (x.tape 2) (x.pos 2) (bitSymbol b) ∧ Region qs := by
  obtain ⟨y,qs,hr,hp,hpos,hcell,hq,hframe,hin,_⟩ := dequeue_cost b rest x hpc hblank hq
  exact ⟨y,qs,hr,hp,hpos,hcell,hq,hframe,hin⟩

#print axioms dequeue_cost
#print axioms dequeue
#print axioms from_back
#print axioms refill
#print axioms transfer_all
#print axioms transfer_bit
#print axioms from_front
end PalPeg.GalilFppMaterialize
