import MacroPeg.HigherOrder.Mach.Order

/-!
# The tables the machine builds for evaluation

The machine tabulates the rows only of the *small* types: order below `j` and size below a cap (`sizeNum` is the
size, capped). The lengths of values (`valT`), the numbers of environments (`envT`) and the variable numbers
(`varVecT`) are computed from these tables. On the types an evaluation needs they agree with `valNum`, `envNum`,
`varVecNum` (`valT_eq`, `envT_eq`, `varVecT_eq`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

variable (j cap N : Nat) (tt ct : List (Nat × Nat))

/-- The size of type number `k`, capped at `cap`. -/
def sizeNum : Nat → Nat
  | 0 => 1
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if a ≤ k ∧ b ≤ k then min cap (sizeNum a + sizeNum b + 1) else cap
    | none => cap
termination_by k => k
decreasing_by all_goals omega

/-- A type whose rows are tabulated. -/
def small (k : Nat) : Prop := ordNum tt k < j ∧ sizeNum cap tt k < cap

instance (k : Nat) : Decidable (small j cap tt k) := inferInstanceAs (Decidable (_ ∧ _))

/-- The tabulated rows. -/
def rowsT (k : Nat) : List (List Nat) := if small j cap tt k then rowsNum N tt k else []

/-- The length of written-out values, from the tables. -/
def valT : Nat → Nat
  | 0 => N + 1
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if a ≤ k ∧ b ≤ k then (rowsT j cap N tt a).length * valT b else 0
    | none => 0
termination_by k => k
decreasing_by omega

/-- The number of environments, from the tables. -/
def envT : Nat → Nat
  | 0 => 1
  | k + 1 =>
    match ct[k]? with
    | some (par, t) => if par ≤ k then envT par * (rowsT j cap N tt t).length else 0
    | none => 0
termination_by k => k
decreasing_by omega

/-- The variable numbers over the environments, from the tables. -/
def varVecT : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i =>
    match ct[k]? with
    | some (par, t) =>
      if par ≤ k then
        match i with
        | 0 => (List.replicate (envT j cap N tt ct par) (List.range (rowsT j cap N tt t).length)).flatten
        | i + 1 => (varVecT par i).flatMap (fun v => List.replicate (rowsT j cap N tt t).length v)
      else []
    | none => []
termination_by k => k
decreasing_by omega

/-- Every binder type of context `c` is small. -/
def ctxSmall : Nat → Prop
  | 0 => True
  | k + 1 =>
    match ct[k]? with
    | some (par, t) => if par ≤ k then small j cap tt t ∧ ctxSmall par else False
    | none => True
termination_by k => k
decreasing_by omega

/-- A type an evaluation may need: order at most `j`, size below the cap. -/
def need (k : Nat) : Prop := ordNum tt k ≤ j ∧ sizeNum cap tt k < cap

/-! ## The tables agree on the types needed -/

variable {j cap N tt ct}

theorem need_arrow {k a b : Nat} (hk : tt[k]? = some (a, b)) (hab : a ≤ k ∧ b ≤ k) (h : need j cap tt (k + 1)) :
    small j cap tt a ∧ need j cap tt b := by
  unfold need at h
  rw [ordNum, sizeNum] at h
  simp only [hk, if_pos hab] at h
  obtain ⟨h₁, h₂⟩ := h
  have h₃ : sizeNum cap tt a + sizeNum cap tt b + 1 < cap := by
    rcases Nat.le_total cap (sizeNum cap tt a + sizeNum cap tt b + 1) with hc | hc
    · rw [Nat.min_eq_left hc] at h₂; omega
    · rw [Nat.min_eq_right hc] at h₂; exact h₂
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

theorem valT_eq : ∀ k, need j cap tt k → valT j cap N tt k = valNum N tt k
  | 0, _ => by rw [valT, valNum]
  | k + 1, h => by
    rw [valT, valNum]
    rcases hk : tt[k]? with _ | ⟨a, b⟩
    · rfl
    · simp only []
      split
      · rename_i hab
        obtain ⟨ha, hb⟩ := need_arrow hk hab h
        rw [rowsT, if_pos ha, valT_eq b hb]
      · rfl

theorem envT_eq : ∀ c, ctxSmall j cap tt ct c → envT j cap N tt ct c = envNum N tt ct c
  | 0, _ => by rw [envT, envNum]
  | k + 1, h => by
    rw [ctxSmall] at h
    rw [envT, envNum]
    rcases hk : ct[k]? with _ | ⟨par, t⟩
    · rfl
    · rw [hk] at h
      simp only [] at h ⊢
      split
      · rename_i hp
        rw [if_pos hp] at h
        rw [rowsT, if_pos h.1, envT_eq par h.2]
      · rfl

theorem varVecT_eq : ∀ c, ctxSmall j cap tt ct c → ∀ i, varVecT j cap N tt ct c i = varVecNum N tt ct c i
  | 0, _, i => by rw [varVecT, varVecNum]
  | k + 1, h, i => by
    rw [ctxSmall] at h
    rw [varVecT, varVecNum]
    rcases hk : ct[k]? with _ | ⟨par, t⟩
    · rfl
    · rw [hk] at h
      simp only [] at h ⊢
      split
      · rename_i hp
        rw [if_pos hp] at h
        cases i with
        | zero => dsimp only; rw [rowsT, if_pos h.1, envT_eq par h.2]
        | succ i => dsimp only; rw [rowsT, if_pos h.1, varVecT_eq par h.2 i]
      · rfl

/-! ## Evaluating with the tables -/

section StepT

variable (j cap : Nat) (x : List Char) (tt ct : List (Nat × Nat)) (lt : List (List Nat)) (Tf : List (List Nat))

/-- One numbered item, with the tables. -/
def stepT (it : MItem) (st : List (List Nat)) : List (List Nat) :=
  let n := envT j cap x.length tt ct it.ctx
  match it.tag, st with
  | 5, vb :: va :: st =>
    (List.zipWith (seqCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten :: st
  | 6, vb :: va :: st =>
    (List.zipWith (altCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten :: st
  | 7, va :: st => ((chunksN (x.length + 1) n va).map (starCodes x)).flatten :: st
  | 8, va :: st => ((chunksN (x.length + 1) n va).map (notCodes x)).flatten :: st
  | 9, st =>
    ((varVecT j cap x.length tt ct it.ctx it.a).map
      (fun k => (rowsT j cap x.length tt ((varTy ct it.ctx it.a).getD 0)).getD k [])).flatten :: st
  | 10, st => (List.replicate n (Tf.getD it.a [])).flatten :: st
  | 11, st => st
  | 12, vy :: vf :: st =>
    (List.zipWith
      (fun fv yv => block (valT j cap x.length tt it.b) (indexIn yv (rowsT j cap x.length tt it.a)) fv)
      (chunksN ((rowsT j cap x.length tt it.a).length * valT j cap x.length tt it.b) n vf)
      (chunksN (valT j cap x.length tt it.a) n vy)).flatten :: st
  | _, st =>
    match opOf tt lt it with
    | some (.leaf e) => (List.replicate n (leafCodes x e)).flatten :: st
    | _ => st

/-- What an item needs of the tables. -/
def ItemOK (it : MItem) : Prop :=
  ctxSmall j cap tt ct it.ctx ∧ (it.tag = 9 → small j cap tt ((varTy ct it.ctx it.a).getD 0)) ∧
    (it.tag = 12 → small j cap tt it.a ∧ need j cap tt it.b)

variable {j cap x tt ct lt Tf}

theorem small_need {k : Nat} (h : small j cap tt k) : need j cap tt k := ⟨by have := h.1; omega, h.2⟩

/-- **With the tables, an item evaluates as without.** -/
theorem stepT_eq {it : MItem} (h : ItemOK j cap tt ct it) (st : List (List Nat)) :
    stepT j cap x tt ct lt Tf it st = stepM x tt ct lt Tf it st := by
  obtain ⟨hc, hv, ha⟩ := h
  unfold stepT stepM
  rw [envT_eq _ hc]
  by_cases h9 : it.tag = 9
  · have hs := hv h9
    simp only [h9]
    rw [varVecT_eq _ hc, rowsT, if_pos hs]
  by_cases h12 : it.tag = 12
  · obtain ⟨ha', hb'⟩ := ha h12
    rw [h12]
    rcases st with _ | ⟨vy, _ | ⟨vf, st⟩⟩
    · rfl
    · rfl
    · simp only []
      rw [rowsT, if_pos ha', valT_eq _ hb', valT_eq _ (small_need ha')]
  split <;> first
    | rfl
    | (simp_all; done)
    | (simp_all; rcases opOf tt lt it with _ | op
       · rfl
       · cases op <;> rfl)

end StepT

/-! ## Rounds and the answer, with the tables -/

section RoundsT

variable (j cap : Nat) (x : List Char) (tt ct : List (Nat × Nat)) (lt : List (List Nat))

def runT (Tf : List (List Nat)) (l : List MItem) (st : List (List Nat)) : List (List Nat) :=
  l.foldl (fun st it => stepT j cap x tt ct lt Tf it st) st

def roundT (bodies : List (List MItem)) (Tf : List (List Nat)) : List (List Nat) :=
  bodies.map (fun l => (runT j cap x tt ct lt Tf l []).headD [])

def fixT (bodies : List (List MItem)) : Nat → List (List Nat) → List (List Nat)
  | 0, Tf => Tf
  | fuel + 1, Tf =>
    if roundT j cap x tt ct lt bodies Tf = Tf then Tf else fixT bodies fuel (roundT j cap x tt ct lt bodies Tf)

/-- The answer, with the tables. -/
def startCodeT (rt : List Nat) (bodies : List (List MItem)) (start : List MItem) : Nat :=
  ((runT j cap x tt ct lt (fixT j cap x tt ct lt bodies ((rt.map (valT j cap x.length tt)).sum + 1)
      (rt.map (fun t => List.replicate (valT j cap x.length tt t) 0))) start []).headD []).getD x.length 0

variable {j cap x tt ct lt}

theorem runT_eq (Tf : List (List Nat)) :
    ∀ (l : List MItem), (∀ it ∈ l, ItemOK j cap tt ct it) → ∀ st,
      runT j cap x tt ct lt Tf l st = runM x tt ct lt Tf l st
  | [], _, _ => rfl
  | it :: l, h, st => by
    simp only [runT, runM, List.foldl_cons]
    rw [stepT_eq (h it List.mem_cons_self)]
    exact runT_eq Tf l (fun i hi => h i (List.mem_cons_of_mem _ hi)) _

theorem roundT_eq {bodies : List (List MItem)} (h : ∀ it ∈ bodies.flatten, ItemOK j cap tt ct it)
    (Tf : List (List Nat)) : roundT j cap x tt ct lt bodies Tf = roundM x tt ct lt bodies Tf := by
  unfold roundT roundM
  refine List.map_congr_left (fun l hl => ?_)
  rw [runT_eq Tf l (fun it hit => h it (List.mem_flatten.2 ⟨l, hl, hit⟩))]

theorem fixT_eq {bodies : List (List MItem)} (h : ∀ it ∈ bodies.flatten, ItemOK j cap tt ct it) :
    ∀ fuel Tf, fixT j cap x tt ct lt bodies fuel Tf = fixM x tt ct lt bodies fuel Tf
  | 0, _ => rfl
  | fuel + 1, Tf => by
    simp only [fixT, fixM, roundT_eq h]
    split
    · rfl
    · exact fixT_eq h fuel _

/-- **The answer with the tables** is the answer, when the items need only tabulated types. -/
theorem startCodeT_eq {rt : List Nat} {bodies : List (List MItem)} {start : List MItem}
    (hrt : ∀ t ∈ rt, need j cap tt t) (h : ∀ it ∈ bodies.flatten ++ start, ItemOK j cap tt ct it) :
    startCodeT j cap x tt ct lt rt bodies start = startCodeM x tt ct lt rt bodies start := by
  have hb : ∀ it ∈ bodies.flatten, ItemOK j cap tt ct it := fun it hi => h it (List.mem_append_left _ hi)
  have hs : ∀ it ∈ start, ItemOK j cap tt ct it := fun it hi => h it (List.mem_append_right _ hi)
  have hv : rt.map (valT j cap x.length tt) = rt.map (valNum x.length tt) :=
    List.map_congr_left (fun t ht => valT_eq t (hrt t ht))
  have hz : rt.map (fun t => List.replicate (valT j cap x.length tt t) 0) =
      rt.map (fun t => List.replicate (valNum x.length tt t) 0) :=
    List.map_congr_left (fun t ht => by rw [valT_eq t (hrt t ht)])
  unfold startCodeT startCodeM
  rw [hv, hz, fixT_eq hb, runT_eq _ start hs]

end RoundsT

end Shallot.MacroPeg.Mach
