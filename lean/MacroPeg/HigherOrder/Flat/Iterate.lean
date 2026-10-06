import MacroPeg.HigherOrder.Flat.Eval

/-!
# The iteration with numbers, and the answer

The rule values are kept written out (`envFlat`). One round evaluates every rule body (`roundFlat`); it is one step
of `iter` (`roundFlat_envFlat`). The rounds are repeated until nothing changes (`fixFlat`), which happens within
`maxEnv + 1` rounds and gives the stopped iterate (`fixFlat_eq`). The grammar consumes the whole input iff the start
term's parser value has code `2` (success, nothing left) at the full input (`accept_iff`).
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO

variable (x : List Char) {R : List HO.Ty}

/-! ## Rule values written out -/

def envFlat (N : Nat) : {S : List HO.Ty} → HO.Env S → List (List Nat)
  | [], _ => []
  | τ :: _, (d, T) => flatVal N τ d :: envFlat N T

theorem envFlat_getD (N : Nat) : ∀ {S : List HO.Ty} (T : HO.Env S) (i : Nat) {τ : HO.Ty} (h : S[i]? = some τ),
    (envFlat N T).getD i [] = flatVal N τ (Env.get T i h)
  | [], _, _, _, h => by simp at h
  | σ :: S, (d, T), 0, τ, h => by
    obtain rfl : σ = τ := by simpa using h
    rfl
  | _ :: _, (_, T), i + 1, _, h => envFlat_getD N T i h

theorem envFlat_inj (N : Nat) : ∀ {S : List HO.Ty} {T T' : HO.Env S}, Env.Mem N T → Env.Mem N T' →
    envFlat N T = envFlat N T' → T = T'
  | [], (), (), _, _, _ => rfl
  | τ :: _, (d, T), (d', T'), ⟨hd, hT⟩, ⟨hd', hT'⟩, h => by
    simp only [envFlat, List.cons.injEq] at h
    rw [flatVal_inj τ hd hd' h.1, envFlat_inj N hT hT' h.2]

/-- The items of every rule body. -/
def bodyItems : {S : List HO.Ty} → TBodies R S → List (List Item)
  | [], _ => []
  | _ :: _, (t, ts) => items t :: bodyItems ts

/-- One round: every body evaluated with the current rule values. -/
def roundFlat (bis : List (List Item)) (Tf : List (List Nat)) : List (List Nat) :=
  bis.map (fun is => ((run x Tf is []).headD []).headD [])

theorem vec_closed (T : HO.Env R) {τ : HO.Ty} (t : Tm R [] τ) : vec x T t = [flatVal x.length τ (den x t T ())] := rfl

theorem roundFlat_envFlat {T : HO.Env R} (hT : Env.Mem x.length T) :
    ∀ {S : List HO.Ty} (ts : TBodies R S),
      roundFlat x (bodyItems ts) (envFlat x.length T) = envFlat x.length (ts.den x T)
  | [], _ => rfl
  | _ :: _, (t, ts) => by
    simp only [bodyItems, roundFlat, List.map_cons]
    rw [run_items hT (envFlat_getD x.length T) t, vec_closed]
    simp only [List.headD_cons, TBodies.den, envFlat, List.cons.injEq, true_and]
    exact roundFlat_envFlat hT ts

/-! ## Repeating rounds -/

/-- Repeat rounds until nothing changes, at most `fuel` times. -/
def fixFlat (bis : List (List Item)) : Nat → List (List Nat) → List (List Nat)
  | 0, Tf => Tf
  | fuel + 1, Tf => if roundFlat x bis Tf = Tf then Tf else fixFlat bis fuel (roundFlat x bis Tf)

variable (G : TGrammar R)

theorem round_iter (m : Nat) :
    roundFlat x (bodyItems G.bodies) (envFlat x.length (iter x G m)) = envFlat x.length (iter x G (m + 1)) :=
  roundFlat_envFlat x (iter_mem x G m) G.bodies

theorem fixFlat_iter : ∀ fuel m, maxEnv x.length R < m + fuel + 1 →
    fixFlat x (bodyItems G.bodies) fuel (envFlat x.length (iter x G m)) =
      envFlat x.length (iter x G (maxEnv x.length R))
  | 0, m, h => by
    simp only [fixFlat]
    rw [iter_stable x G m (by omega)]
  | fuel + 1, m, h => by
    simp only [fixFlat, round_iter]
    split
    · rename_i heq
      have hm := envFlat_inj x.length (iter_mem x G _) (iter_mem x G _) heq
      by_cases hle : m ≤ maxEnv x.length R
      · rw [← iter_const x G hm.symm _ hle]
      · rw [iter_stable x G m (by omega)]
    · rw [fixFlat_iter fuel (m + 1) (by omega)]

/-- **The rounds from the least rule values reach the stopped iterate.** -/
theorem fixFlat_eq (fuel : Nat) (h : maxEnv x.length R < fuel + 1) :
    fixFlat x (bodyItems G.bodies) fuel (envFlat x.length (Env.bot x.length R)) =
      envFlat x.length (iter x G (maxEnv x.length R)) := by
  have := fixFlat_iter x G fuel 0 (by omega)
  simpa [iter] using this

/-! ## The answer -/

theorem sfx_eq_nil {j : Nat} (hj : j ≤ x.length) : HO.sfx x j = [] ↔ j = 0 := by
  simp only [HO.sfx, List.drop_eq_nil_iff]; omega

/-- **The grammar consumes the whole input iff the code at the full input is `2`.** -/
theorem accept_iff (t : Tm R [] .p) :
    HObs G.erase t.erase x (some []) ↔
      (flatVal x.length .p (den x t (iter x G (maxEnv x.length R)) ())).getD x.length 0 = 2 := by
  have hd := den_mem (x := x) (iter_mem x G (maxEnv x.length R)) t (ρ := ()) (by simp [envs])
  have hcode : (flatVal x.length .p (den x t (iter x G (maxEnv x.length R)) ())).getD x.length 0 =
      resCode (decideHO G t x) := by
    simp only [decideHO, atq, flatVal]
    have hl := ((mem_allVecs _ _ _).1 hd).1
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
