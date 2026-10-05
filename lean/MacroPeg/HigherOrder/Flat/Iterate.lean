import MacroPeg.HigherOrder.Flat.Eval

/-!
# The iteration with numbers, and the answer

The rule values are kept as numbers (`envNums`). One round evaluates every rule body (`roundNums`); it is one step of
`iter` (`roundNums_envNums`). The rounds are repeated until nothing changes (`fixNums`), which happens within
`maxEnv + 1` rounds and gives the stopped iterate (`fixNums_eq`). The grammar consumes the whole input iff the start
term's parser value has code `2` (success, nothing left) at the full input (`accept_iff`).
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

variable (x : List Char) {R : List HO.Ty}

/-! ## Rule values as numbers -/

/-- The numbers of the rule values. -/
def envNums (N : Nat) : {S : List HO.Ty} → HO.Env S → List Nat
  | [], _ => []
  | τ :: _, (d, T) => vIdx N τ d :: envNums N T

theorem envNums_getD (N : Nat) : ∀ {S : List HO.Ty} (T : HO.Env S) (i : Nat) {τ : HO.Ty} (h : S[i]? = some τ),
    (envNums N T).getD i 0 = vIdx N τ (Env.get T i h)
  | [], _, _, _, h => by simp at h
  | σ :: S, (d, T), 0, τ, h => by
    obtain rfl : σ = τ := by simpa using h
    rfl
  | _ :: _, (_, T), i + 1, _, h => envNums_getD N T i h

theorem envNums_inj (N : Nat) : ∀ {S : List HO.Ty} {T T' : HO.Env S}, Env.Mem N T → Env.Mem N T' →
    envNums N T = envNums N T' → T = T'
  | [], (), (), _, _, _ => rfl
  | τ :: _, (d, T), (d', T'), ⟨hd, hT⟩, ⟨hd', hT'⟩, h => by
    simp only [envNums, List.cons.injEq] at h
    rw [indexIn_inj hd hd' h.1, envNums_inj N hT hT' h.2]

/-- The items of every rule body. -/
def bodyItems : {S : List HO.Ty} → TBodies R S → List (List Item)
  | [], _ => []
  | _ :: _, (t, ts) => items t :: bodyItems ts

/-- One round: every body evaluated with the current rule values. -/
def roundNums (bis : List (List Item)) (Tn : List Nat) : List Nat :=
  bis.map (fun is => ((run x Tn is []).headD []).headD 0)

theorem vec_closed (T : HO.Env R) {τ : HO.Ty} (t : Tm R [] τ) : vec x T t = [vIdx x.length τ (den x t T ())] := rfl

theorem roundNums_envNums {T : HO.Env R} (hT : Env.Mem x.length T) :
    ∀ {S : List HO.Ty} (ts : TBodies R S),
      roundNums x (bodyItems ts) (envNums x.length T) = envNums x.length (ts.den x T)
  | [], _ => rfl
  | _ :: _, (t, ts) => by
    simp only [bodyItems, roundNums, List.map_cons]
    rw [run_items hT (envNums_getD x.length T) t, vec_closed]
    simp only [List.headD_cons, TBodies.den, envNums, List.cons.injEq, true_and]
    exact roundNums_envNums hT ts

/-! ## Repeating rounds -/

/-- Repeat rounds until nothing changes, at most `fuel` times. -/
def fixNums (bis : List (List Item)) : Nat → List Nat → List Nat
  | 0, Tn => Tn
  | fuel + 1, Tn => if roundNums x bis Tn = Tn then Tn else fixNums bis fuel (roundNums x bis Tn)

variable (G : TGrammar R)

theorem round_iter (m : Nat) :
    roundNums x (bodyItems G.bodies) (envNums x.length (iter x G m)) = envNums x.length (iter x G (m + 1)) :=
  roundNums_envNums x (iter_mem x G m) G.bodies

/-- From iterate `m`, the rounds reach the stopped iterate when `m + fuel` exceeds `maxEnv`. -/
theorem fixNums_iter : ∀ fuel m, maxEnv x.length R < m + fuel + 1 →
    fixNums x (bodyItems G.bodies) fuel (envNums x.length (iter x G m)) =
      envNums x.length (iter x G (maxEnv x.length R))
  | 0, m, h => by
    simp only [fixNums]
    rw [iter_stable x G m (by omega)]
  | fuel + 1, m, h => by
    simp only [fixNums, round_iter]
    split
    · rename_i heq
      have hm := envNums_inj x.length (iter_mem x G _) (iter_mem x G _) heq
      by_cases hle : m ≤ maxEnv x.length R
      · rw [← iter_const x G hm.symm _ hle]
      · rw [iter_stable x G m (by omega)]
    · rw [fixNums_iter fuel (m + 1) (by omega)]

/-- **The rounds from the empty rule values reach the stopped iterate.** -/
theorem fixNums_eq (fuel : Nat) (h : maxEnv x.length R < fuel + 1) :
    fixNums x (bodyItems G.bodies) fuel (envNums x.length (Env.bot x.length R)) =
      envNums x.length (iter x G (maxEnv x.length R)) := by
  have := fixNums_iter x G fuel 0 (by omega)
  simpa [iter] using this

/-! ## The answer -/

/-- The code at position `N` of the parser value with number `i`. -/
def answerCode (i : Nat) : Nat := ((rows x.length .p).getD i []).getD x.length 0

theorem sfx_eq_nil {j : Nat} (hj : j ≤ x.length) : sfx x j = [] ↔ j = 0 := by
  simp only [sfx, List.drop_eq_nil_iff]; omega

/-- **The grammar consumes the whole input iff the code at the full input is `2`.** -/
theorem accept_iff (t : Tm R [] .p) :
    HObs G.erase t.erase x (some []) ↔
      answerCode x (vIdx x.length .p (den x t (iter x G (maxEnv x.length R)) ())) = 2 := by
  have hd := den_mem (x := x) (iter_mem x G (maxEnv x.length R)) t (ρ := ()) (by simp [envs])
  have hcode : answerCode x (vIdx x.length .p (den x t (iter x G (maxEnv x.length R)) ())) =
      resCode (decideHO G t x) := by
    simp only [answerCode, decideHO, atq]
    rw [List.getD_eq_getElem?_getD (l := rows _ _), rows_getElem? hd, Option.getD_some]
    have hl := ((mem_allVecs _ _ _).1 hd).1
    simp only [row]
    rw [getD_map_lt resCode none 0 _ (by rw [hl]; omega)]
  rw [hcode, decideHO_iff]
  have hmem : decideHO G t x ∈ resElems x.length := by
    simp only [decideHO]; exact atq_mem hd _
  constructor
  · rintro ⟨r', h, hr⟩
    rw [h]
    cases r' with
    | none => simp at hr
    | some j =>
      simp only [Option.map_some, Option.some.injEq] at hr
      rw [h] at hmem
      have hj : j ≤ x.length := by
        rcases mem_resElems.1 hmem with e | e | ⟨k, hk, e⟩
        · cases e
        · cases e
        · simp only [Option.some.injEq] at e; omega
      rw [(sfx_eq_nil x hj).1 hr]; rfl
  · intro h
    refine ⟨some 0, ?_, by simp [HO.sfx]⟩
    revert h
    cases decideHO G t x with
    | none => intro h; cases h
    | some r =>
      cases r with
      | none => intro h; cases h
      | some j =>
        intro h
        simp only [resCode] at h
        rw [show j = 0 by omega]

end Shallot.MacroPeg.Flat
