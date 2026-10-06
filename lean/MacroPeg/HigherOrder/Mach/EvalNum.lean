import MacroPeg.HigherOrder.Mach.Rows
import MacroPeg.HigherOrder.Mach.ReadAll
import MacroPeg.HigherOrder.Flat.Packed

/-!
# The packed evaluator on numbered items

The evaluator `stepF` needs, for an item, numbers that depend on types: the number of environments of its context
(`envNum`), the length of written-out values (`valNum`), the variable numbers over the environments (`varVecNum`)
and the rows of a type (`rowsNum`). Here they are computed from the arrow and context tables, and `stepM` is `stepF`
on numbered items (`MItem`): `stepM_eq`.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

variable (N : Nat) (tt ct : List (Nat × Nat))

/-- The length of the written-out values of type number `k`. -/
def valNum : Nat → Nat
  | 0 => N + 1
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if a ≤ k ∧ b ≤ k then (rowsNum N tt a).length * valNum b else 0
    | none => 0
termination_by k => k
decreasing_by omega

/-- The number of environments of context number `c`. -/
def envNum : Nat → Nat
  | 0 => 1
  | k + 1 =>
    match ct[k]? with
    | some (par, t) => if par ≤ k then envNum par * (rowsNum N tt t).length else 0
    | none => 0
termination_by k => k
decreasing_by omega

/-- The numbers of variable `i` over the environments of context number `c`. -/
def varVecNum : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i =>
    match ct[k]? with
    | some (par, t) =>
      if par ≤ k then
        match i with
        | 0 => (List.replicate (envNum N tt ct par) (List.range (rowsNum N tt t).length)).flatten
        | i + 1 => (varVecNum par i).flatMap (fun v => List.replicate (rowsNum N tt t).length v)
      else []
    | none => []
termination_by k => k
decreasing_by omega

/-! ## They agree with the types -/

variable {N tt ct}

theorem rowsNum_length {k : Nat} {τ : HO.Ty} (h : tyOf tt k = some τ) : (rowsNum N tt k).length = (elems N τ).length := by
  rw [rowsNum_eq N k h, eRows, List.length_map]

theorem valNum_eq : ∀ (k : Nat) {τ : HO.Ty}, tyOf tt k = some τ → valNum N tt k = valSize N τ
  | 0, τ, h => by rw [tyOf] at h; cases h; rw [valNum, valSize]
  | k + 1, τ, h => by
    rw [tyOf] at h
    split at h
    · rename_i a b hk
      split at h
      · rename_i hab
        split at h
        · rename_i σ ρ hσ hρ
          cases h
          rw [valNum]; simp only [hk]
          rw [if_pos hab, rowsNum_length hσ, valNum_eq b hρ, valSize]
        · cases h
      · cases h
    · cases h

theorem envNum_eq : ∀ (c : Nat) {Γ : List HO.Ty}, ctxOf tt ct c = some Γ → envNum N tt ct c = envSize N Γ
  | 0, Γ, h => by rw [ctxOf] at h; cases h; rw [envNum, envSize]
  | k + 1, Γ, h => by
    rw [ctxOf] at h
    split at h
    · rename_i par t hk
      split at h
      · rename_i hp
        split at h
        · rename_i τ Γ' hτ hΓ
          cases h
          rw [envNum]; simp only [hk]
          rw [if_pos hp, envNum_eq par hΓ, rowsNum_length hτ, envSize]
        · cases h
      · cases h
    · cases h

theorem varVecNum_eq : ∀ (c : Nat) {Γ : List HO.Ty}, ctxOf tt ct c = some Γ → ∀ i,
    varVecNum N tt ct c i = varVec N Γ i
  | 0, Γ, h, i => by rw [ctxOf] at h; cases h; rw [varVecNum]; cases i <;> rfl
  | k + 1, Γ, h, i => by
    rw [ctxOf] at h
    split at h
    · rename_i par t hk
      split at h
      · rename_i hp
        split at h
        · rename_i τ Γ' hτ hΓ
          cases h
          rw [varVecNum]; simp only [hk]
          rw [if_pos hp]
          cases i with
          | zero => dsimp only; rw [envNum_eq par hΓ, rowsNum_length hτ, varVec]
          | succ i => dsimp only; rw [varVecNum_eq par hΓ i, rowsNum_length hτ, varVec]
        · cases h
      · cases h
    · cases h

/-! ## One numbered item -/

section Step

variable (x : List Char) (tt ct : List (Nat × Nat)) (lt : List (List Nat)) (Tf : List (List Nat))

/-- One numbered item, on a stack of packed vectors. -/
def stepM (it : MItem) (st : List (List Nat)) : List (List Nat) :=
  let n := envNum x.length tt ct it.ctx
  match it.tag, st with
  | 5, vb :: va :: st =>
    (List.zipWith (seqCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten :: st
  | 6, vb :: va :: st =>
    (List.zipWith (altCodes x) (chunksN (x.length + 1) n va) (chunksN (x.length + 1) n vb)).flatten :: st
  | 7, va :: st => ((chunksN (x.length + 1) n va).map (starCodes x)).flatten :: st
  | 8, va :: st => ((chunksN (x.length + 1) n va).map (notCodes x)).flatten :: st
  | 9, st =>
    ((varVecNum x.length tt ct it.ctx it.a).map
      (fun k => (rowsNum x.length tt ((varTy ct it.ctx it.a).getD 0)).getD k [])).flatten :: st
  | 10, st => (List.replicate n (Tf.getD it.a [])).flatten :: st
  | 11, st => st
  | 12, vy :: vf :: st =>
    (List.zipWith (fun fv yv => block (valNum x.length tt it.b) (indexIn yv (rowsNum x.length tt it.a)) fv)
      (chunksN ((rowsNum x.length tt it.a).length * valNum x.length tt it.b) n vf)
      (chunksN (valNum x.length tt it.a) n vy)).flatten :: st
  | _, st =>
    match opOf tt lt it with
    | some (.leaf e) => (List.replicate n (leafCodes x e)).flatten :: st
    | _ => st

end Step

/-! ## `stepM` is `stepF` -/

section StepEq

variable {x : List Char} {tt ct : List (Nat × Nat)} {lt : List (List Nat)} {Tf : List (List Nat)}

theorem varRows_eq (hw : TTWF tt) {c : Nat} {Γ : List HO.Ty} (hΓ : ctxOf tt ct c = some Γ) (i : Nat) :
    rowsNum x.length tt ((varTy ct c i).getD 0) = eRows x.length (Γ.getD i .p) := by
  obtain ⟨hb, hle⟩ := varTy_ctx c hΓ i
  rcases hv : varTy ct c i with _ | t
  · rw [hv] at hb
    have : Γ[i]? = none := by simpa using hb.symm
    rw [Option.getD_none, List.getD_eq_getElem?_getD, this, Option.getD_none]
    exact rowsNum_eq x.length 0 (by rw [tyOf])
  · rw [hv] at hb
    obtain ⟨τ, hτ⟩ := tyOf_some hw t (hle t hv)
    rw [Option.bind_some, hτ] at hb
    rw [Option.getD_some, List.getD_eq_getElem?_getD, ← hb, Option.getD_some]
    exact rowsNum_eq x.length t hτ

/-- **The numbered evaluator agrees with the packed one.** -/
theorem stepM_eq (hw : TTWF tt) {it : MItem} {item : Item} (h : itemOf tt ct lt it = some item)
    (st : List (List Nat)) : stepM x tt ct lt Tf it st = stepF x Tf item st := by
  unfold itemOf at h
  split at h
  · rename_i op Γ hop hΓ
    cases h
    have hn : envNum x.length tt ct it.ctx = envSize x.length Γ := envNum_eq it.ctx hΓ
    have hop' := hop
    unfold opOf at hop
    unfold stepM
    simp only [hn]
    split at hop
    -- leaves
    all_goals first
      | (rename_i htag; cases hop; rw [htag]; simp only [hop', stepF]; done)
      | (rename_i htag; cases hop; rw [htag]; rcases st with _ | ⟨vb, _ | ⟨va, st⟩⟩ <;> simp [hop', stepF]; done)
      | (rename_i htag; cases hop; rw [htag]; simp only [stepF]; rw [varRows_eq hw hΓ, varVecNum_eq _ hΓ])
      | (rename_i htag; rw [htag]
         rcases hl : litOf lt it.a with _ | str
         · rw [hl] at hop; cases hop
         · rw [hl] at hop; cases hop; simp only [hop', stepF])
      | (rename_i htag; rw [htag]
         split at hop
         · rename_i a σ ha hσ
           cases hop
           rcases st with _ | ⟨vb, st⟩ <;> rfl
         · cases hop)
      | (rename_i htag; rw [htag]
         split at hop
         · rename_i a b ha hb
           cases hop
           rcases st with _ | ⟨vy, _ | ⟨vf, st⟩⟩
           · simp [hop', stepF]
           · simp [hop', stepF]
           · simp only [stepF]
             rw [rowsNum_eq x.length _ ha, valNum_eq _ hb, valNum_eq _ ha, eRows, List.length_map, valSize]
         · cases hop)
      | (cases hop)
      | skip
    all_goals done
  · cases h

end StepEq

/-! ## Bodies, rounds and the answer, on numbered items -/

theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {r : List β}
    (h : (a :: l).mapM f = some r) : ∃ b bs, f a = some b ∧ l.mapM f = some bs ∧ r = b :: bs := by
  cases hf : f a with
  | none => simp [List.mapM_cons, hf] at h
  | some b =>
    cases hl : l.mapM f with
    | none => simp [List.mapM_cons, hf, hl] at h
    | some bs => simp [List.mapM_cons, hf, hl] at h; exact ⟨b, bs, rfl, rfl, h.symm⟩

section Rounds

variable (x : List Char) (tt ct : List (Nat × Nat)) (lt : List (List Nat))

def runM (Tf : List (List Nat)) (l : List MItem) (st : List (List Nat)) : List (List Nat) :=
  l.foldl (fun st it => stepM x tt ct lt Tf it st) st

def roundM (bodies : List (List MItem)) (Tf : List (List Nat)) : List (List Nat) :=
  bodies.map (fun l => (runM x tt ct lt Tf l []).headD [])

def fixM (bodies : List (List MItem)) : Nat → List (List Nat) → List (List Nat)
  | 0, Tf => Tf
  | fuel + 1, Tf => if roundM x tt ct lt bodies Tf = Tf then Tf else fixM bodies fuel (roundM x tt ct lt bodies Tf)

/-- The answer from the tables of a finished reading: rule types `rt`, bodies, start. -/
def startCodeM (rt : List Nat) (bodies : List (List MItem)) (start : List MItem) : Nat :=
  ((runM x tt ct lt (fixM x tt ct lt bodies ((rt.map (valNum x.length tt)).sum + 1)
      (rt.map (fun t => List.replicate (valNum x.length tt t) 0))) start []).headD []).getD x.length 0

variable {x tt ct lt}

theorem runM_eq (hw : TTWF tt) (Tf : List (List Nat)) :
    ∀ {l : List MItem} {is : List Item}, itemsOf tt ct lt l = some is → ∀ st,
      runM x tt ct lt Tf l st = runF x Tf is st
  | [], is, h, st => by simp [itemsOf] at h; subst h; rfl
  | it :: l, is, h, st => by
    obtain ⟨item, is', hit, hl, rfl⟩ := mapM_cons_some h
    simp only [runM, List.foldl_cons]
    rw [stepM_eq hw hit]
    exact runM_eq hw Tf hl _

theorem roundM_eq (hw : TTWF tt) {bodies : List (List MItem)} {bis : List (List Item)}
    (h : bodies.mapM (itemsOf tt ct lt) = some bis) (Tf : List (List Nat)) :
    roundM x tt ct lt bodies Tf = roundP x bis Tf := by
  induction bodies generalizing bis with
  | nil => simp at h; subst h; rfl
  | cons l bodies ih =>
    obtain ⟨is, bis', hl, hb, rfl⟩ := mapM_cons_some h
    simp only [roundM, roundP, List.map_cons]
    rw [runM_eq hw Tf hl]
    have := ih hb
    simp only [roundM, roundP] at this
    rw [this]

theorem fixM_eq (hw : TTWF tt) {bodies : List (List MItem)} {bis : List (List Item)}
    (h : bodies.mapM (itemsOf tt ct lt) = some bis) : ∀ fuel Tf,
    fixM x tt ct lt bodies fuel Tf = fixP x bis fuel Tf
  | 0, _ => rfl
  | fuel + 1, Tf => by
    simp only [fixM, fixP, roundM_eq hw h]
    split
    · rfl
    · exact fixM_eq hw h fuel _

theorem valNum_sum (hw : TTWF tt) : ∀ {rt : List Nat} {R : List HO.Ty}, rt.mapM (tyOf tt) = some R →
    (rt.map (valNum x.length tt)).sum = maxEnv x.length R ∧
      rt.map (fun t => List.replicate (valNum x.length tt t) 0) = R.map (fun τ => List.replicate (valSize x.length τ) 0)
  | [], R, h => by simp at h; subst h; simp [maxEnv]
  | t :: rt, R, h => by
    obtain ⟨τ, R', hτ, hR, rfl⟩ := mapM_cons_some h
    obtain ⟨h₁, h₂⟩ := valNum_sum hw hR
    simp [maxEnv, h₁, h₂, valNum_eq t hτ, maxCount_eq_valSize]
where
  maxCount_eq_valSize (N : Nat) : ∀ τ : HO.Ty, valSize N τ = maxCount N τ
    | .p => rfl
    | .arr a b => by rw [valSize, maxCount, maxCount_eq_valSize N b]

end Rounds

/-- **The answer from a finished reading** is the answer of the packed procedure. -/
theorem startCodeM_eq {st : PSt} {g : HGrammar} {bis : List (List Item)} {is : List Item} {x : List Char}
    (hr : ReadOK st g.types bis is x) :
    startCodeM x st.tt st.ct st.lt st.rt st.bodies st.start = startCodeP x g bis is := by
  obtain ⟨hsum, hzero⟩ := valNum_sum (x := x) hr.tt hr.rt
  unfold startCodeM startCodeP
  rw [hsum, hzero, fixM_eq hr.tt hr.bodies, runM_eq hr.tt _ hr.start]
  congr 4
  simp [zeroRules, HGrammar.types, List.map_map, Function.comp_def]

end Shallot.MacroPeg.Mach
