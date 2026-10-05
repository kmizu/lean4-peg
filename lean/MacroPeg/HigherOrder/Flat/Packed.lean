import MacroPeg.HigherOrder.Flat.Decider

/-!
# The evaluator on packed vectors

A vector of the evaluator (one written-out value per environment) is kept as one list: the values one after another
(`List.flatten`). Since the environments vary the innermost variable fastest, a lambda leaves the packed vector of
its body as it is. `stepF` is `step` on packed vectors (`stepF_packed`), and `runF` computes the packed values of a
term (`runF_items`).
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

section Packed

variable (x : List Char) (Tf : List (List Nat))

/-- One item, on a stack of packed vectors. -/
def stepF : Item → List (List Nat) → List (List Nat)
  | ⟨.leaf e, Γ⟩, st => (List.replicate (envSize x.length Γ) (leafCodes x e)).flatten :: st
  | ⟨.seq, Γ⟩, vb :: va :: st =>
      (List.zipWith (seqCodes x) (chunksN (x.length + 1) (envSize x.length Γ) va)
        (chunksN (x.length + 1) (envSize x.length Γ) vb)).flatten :: st
  | ⟨.alt, Γ⟩, vb :: va :: st =>
      (List.zipWith (altCodes x) (chunksN (x.length + 1) (envSize x.length Γ) va)
        (chunksN (x.length + 1) (envSize x.length Γ) vb)).flatten :: st
  | ⟨.star, Γ⟩, va :: st => ((chunksN (x.length + 1) (envSize x.length Γ) va).map (starCodes x)).flatten :: st
  | ⟨.notP, Γ⟩, va :: st => ((chunksN (x.length + 1) (envSize x.length Γ) va).map (notCodes x)).flatten :: st
  | ⟨.var i, Γ⟩, st => ((varVec x.length Γ i).map (fun k => (eRows x.length (Γ.getD i .p)).getD k [])).flatten :: st
  | ⟨.rule i, Γ⟩, st => (List.replicate (envSize x.length Γ) (Tf.getD i [])).flatten :: st
  | ⟨.lam _ _, _⟩, vb :: st => vb :: st
  | ⟨.app a b, Γ⟩, vy :: vf :: st =>
      (List.zipWith (fun fv yv => block (valSize x.length b) (indexIn yv (eRows x.length a)) fv)
        (chunksN (valSize x.length (a ⇒ b)) (envSize x.length Γ) vf)
        (chunksN (valSize x.length a) (envSize x.length Γ) vy)).flatten :: st
  | _, st => st

def runF (is : List Item) (st : List (List Nat)) : List (List Nat) :=
  is.foldl (fun st it => stepF x Tf it st) st

theorem runF_append (is js : List Item) (st : List (List Nat)) :
    runF x Tf (is ++ js) st = runF x Tf js (runF x Tf is st) := by
  simp [runF, List.foldl_append]

theorem runF_single (it : Item) (st : List (List Nat)) : runF x Tf [it] st = stepF x Tf it st := rfl

end Packed

/-! ## Shapes -/

/-- `n` values of length `m` each. -/
def Shaped (n m : Nat) (v : List (List Nat)) : Prop := v.length = n ∧ ∀ c ∈ v, c.length = m

theorem Shaped.chunks {n m : Nat} {v : List (List Nat)} (h : Shaped n m v) : chunksN m n v.flatten = v := by
  rw [← h.1]; exact chunksN_flatten m v h.2

theorem chunksN_flatten_self {α : Type} (k : Nat) : ∀ (n : Nat) (l : List α), l.length = n * k →
    (chunksN k n l).flatten = l
  | 0, l, h => by simp at h; simp [chunksN, h]
  | n + 1, l, h => by
    simp only [chunksN, List.flatten_cons]
    rw [chunksN_flatten_self k n (l.drop k) (by simp [h, Nat.succ_mul]), List.take_append_drop]

theorem flatten_map_flatten' {α : Type} : ∀ L : List (List (List α)), (L.map List.flatten).flatten = L.flatten.flatten
  | [] => rfl
  | l :: L => by simp [flatten_map_flatten' L]

section Items

variable {x : List Char} {R : List HO.Ty} {T : HO.Env R}

theorem vec_shaped (hT : Env.Mem x.length T) {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) :
    Shaped (envSize x.length Γ) (valSize x.length τ) (vec x T t) := by
  refine ⟨by simp [vec, envs_length], fun c hc => ?_⟩
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hc
  exact length_flatVal τ (den_mem hT t hρ)

/-- The step on the last item of a term, from the vectors of its parts. -/
theorem vec_of_run (hT : Env.Mem x.length T) {Tf : List (List Nat)}
    (hTf : ∀ (i : Nat) {τ : HO.Ty} (h : R[i]? = some τ), Tf.getD i [] = flatVal x.length τ (Env.get T i h))
    {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) : run x Tf (items t) [] = [vec x T t] :=
  run_items hT hTf t []

/-- **The packed evaluator computes the packed values of a term.** -/
theorem runF_items (hT : Env.Mem x.length T) {Tf : List (List Nat)}
    (hTf : ∀ (i : Nat) {τ : HO.Ty} (h : R[i]? = some τ), Tf.getD i [] = flatVal x.length τ (Env.get T i h)) :
    ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ) (st : List (List Nat)),
      runF x Tf (items t) st = (vec x T t).flatten :: st := by
  intro Γ τ t
  have hv := vec_of_run hT hTf t
  induction t with
  | eps | any | chr | range | lit =>
    intro st
    simp only [items, run_single, step, List.cons.injEq, and_true] at hv
    simp only [items, runF_single, stepF, ← hv]
  | seq a b iha ihb | alt a b iha ihb =>
    intro st
    have ha := vec_of_run hT hTf a
    have hb := vec_of_run hT hTf b
    simp only [items, run_append, ha, run_single] at hv
    rw [run_items hT hTf b] at hv
    simp only [step, List.cons.injEq, and_true] at hv
    have ca : chunksN (x.length + 1) _ (vec x T a).flatten = vec x T a := (vec_shaped hT a).chunks
    have cb : chunksN (x.length + 1) _ (vec x T b).flatten = vec x T b := (vec_shaped hT b).chunks
    simp only [items, runF_append, iha ha, ihb hb, runF_single, stepF, ca, cb, ← hv]
  | star a ih | notP a ih =>
    intro st
    have ha := vec_of_run hT hTf a
    simp only [items, run_append, ha, run_single, step, List.cons.injEq, and_true] at hv
    have ca : chunksN (x.length + 1) _ (vec x T a).flatten = vec x T a := (vec_shaped hT a).chunks
    simp only [items, runF_append, ih ha, runF_single, stepF, ca, ← hv]
  | var i h =>
    intro st
    simp only [items, run_single, step, List.cons.injEq, and_true] at hv
    simp only [items, runF_single, stepF, ← hv]
  | rule i h =>
    intro st
    simp only [items, run_single, step, List.cons.injEq, and_true] at hv
    simp only [items, runF_single, stepF, ← hv]
  | lam body ih =>
    rename_i Γ' a σ
    intro st
    have hb := vec_of_run hT hTf body
    simp only [items, run_append, hb, run_single, step, List.cons.injEq, and_true] at hv
    simp only [items, runF_append, ih hb, runF_single, stepF, List.cons.injEq, and_true]
    rw [← hv, flatten_map_flatten', chunksN_flatten_self]
    have := (vec_shaped hT body).1
    simp only [envSize] at this
    exact this
  | app f y ihf ihy =>
    intro st
    have hf := vec_of_run hT hTf f
    have hy := vec_of_run hT hTf y
    simp only [items, run_append, hf, run_single] at hv
    rw [run_items hT hTf y] at hv
    simp only [step, List.cons.injEq, and_true] at hv
    simp only [items, runF_append, ihf hf, ihy hy, runF_single, stepF, (vec_shaped hT f).chunks,
      (vec_shaped hT y).chunks, ← hv]

end Items

/-! ## Rounds and the answer, on packed vectors -/

section Rounds

variable (x : List Char)

/-- One round: every body evaluated with the current rule values. -/
def roundP (bis : List (List Item)) (Tf : List (List Nat)) : List (List Nat) :=
  bis.map (fun is => (runF x Tf is []).headD [])

/-- Repeat rounds until nothing changes, at most `fuel` times. -/
def fixP (bis : List (List Item)) : Nat → List (List Nat) → List (List Nat)
  | 0, Tf => Tf
  | fuel + 1, Tf => if roundP x bis Tf = Tf then Tf else fixP bis fuel (roundP x bis Tf)

/-- The code at the full input of the start, after the rounds. -/
def startCodeP (g : HGrammar) (bis : List (List Item)) (is : List Item) : Nat :=
  ((runF x (fixP x bis (maxEnv x.length g.types + 1) (zeroRules x.length g)) is []).headD []).getD x.length 0

variable {x} {R : List HO.Ty}

theorem runF_closed {T : HO.Env R} (hT : Env.Mem x.length T) {τ : HO.Ty} (t : Tm R [] τ) :
    (runF x (envFlat x.length T) (items t) []).headD [] = flatVal x.length τ (den x t T ()) := by
  rw [runF_items hT (envFlat_getD x.length T) t, vec_closed]; simp

theorem run_closed {T : HO.Env R} (hT : Env.Mem x.length T) {τ : HO.Ty} (t : Tm R [] τ) :
    ((run x (envFlat x.length T) (items t) []).headD []).headD [] = flatVal x.length τ (den x t T ()) := by
  rw [run_items hT (envFlat_getD x.length T) t, vec_closed]; simp

theorem roundP_eq {T : HO.Env R} (hT : Env.Mem x.length T) :
    ∀ {S : List HO.Ty} (ts : TBodies R S),
      roundP x (bodyItems ts) (envFlat x.length T) = roundFlat x (bodyItems ts) (envFlat x.length T)
  | [], _ => rfl
  | _ :: _, (t, ts) => by
    simp only [bodyItems, roundP, roundFlat, List.map_cons]
    rw [runF_closed hT t, run_closed hT t]
    have := roundP_eq hT ts
    simp only [roundP, roundFlat] at this
    rw [this]

variable (G : TGrammar R)

theorem fixP_iter : ∀ (fuel m : Nat),
    fixP x (bodyItems G.bodies) fuel (envFlat x.length (iter x G m)) =
      fixFlat x (bodyItems G.bodies) fuel (envFlat x.length (iter x G m))
  | 0, _ => rfl
  | fuel + 1, m => by
    simp only [fixP, fixFlat]
    rw [roundP_eq (iter_mem x G m) G.bodies, round_iter]
    split
    · rfl
    · exact fixP_iter fuel (m + 1)

theorem startCodeP_eq {g : HGrammar} (hG : G.erase = g) (t : Tm R [] .p) (hR : R = g.types) :
    startCodeP x g (bodyItems G.bodies) (items t) = startCode g x (bodyItems G.bodies) (items t) := by
  subst hR
  have hz : zeroRules x.length g = envFlat x.length (iter x G 0) := by
    rw [show iter x G 0 = Env.bot x.length g.types from rfl, envFlat_bot]; simp [zeroRules, HGrammar.types]
  unfold startCodeP startCode
  rw [hz, fixP_iter, fixFlat_iter x G _ 0 (by omega), runF_closed (iter_mem x G _) t,
    run_closed (iter_mem x G _) t]

end Rounds

/-- The flat decision procedure, on packed vectors. -/
def flatDecideP (j : Nat) (bits : List Bool) : Bool :=
  match deser (Complexity.ofBits bits) with
  | none => false
  | some (g, s, x) =>
    match checkRules g, inferE g.types [] s with
    | some bis, some (.p, is) => decide (KExp.GOrd j g s) && (startCodeP x g bis is == 2)
    | _, _ => false

theorem flatDecideP_eq (j : Nat) (bits : List Bool) : flatDecideP j bits = flatDecide j bits := by
  unfold flatDecideP flatDecide
  rcases deser (Complexity.ofBits bits) with _ | ⟨g, s, x⟩
  · rfl
  · dsimp only
    rcases hcr : checkRules g with _ | bis
    · rfl
    · rcases hinf : inferE g.types [] s with _ | ⟨_ | ⟨a, b⟩, is⟩
      · rfl
      · obtain ⟨G, hG, hbis⟩ := checkRules_sound hcr
        obtain ⟨t, _, hit⟩ := inferE_sound s hinf
        dsimp only
        rw [← hbis, ← hit, startCodeP_eq G hG t rfl]
      · rfl

/-- **The packed procedure decides the uniform problem.** -/
theorem flatDecideP_iff (j : Nat) (bits : List Bool) : flatDecideP j bits = true ↔ KExp.UMPEG j bits := by
  rw [flatDecideP_eq]; exact flatDecide_iff j bits

end Shallot.MacroPeg.Flat
