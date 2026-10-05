import MacroPeg.HigherOrder.Embed
import MacroPeg.Properties.AtmHard

/-!
# Higher-order Macro PEG is EXPTIME-hard already at order 1

The grammar `atmG M` that simulates a linear-space alternating Turing machine (`AtmHard.lean`) is first-order and
arity-correct (`atmG_arityOk`), so its embedding into the higher-order calculus recognizes the same inputs
(`atm_reduction_HO`). With the upper bound of `HigherOrder/Decide.lean`, order-1 recognition is EXPTIME-complete in
the higher-order calculus too (APSPACE = EXPTIME is the external fact, as in `AtmHard.lean`). Whether order `k` is
`k`-EXPTIME-hard is open here.
-/

namespace Shallot.MacroPeg

section ArityOk

variable (M : ATM)

local notation "G" => atmG M

theorem ao_seq {a b : MExp} (ha : MExp.arityOk G a = true) (hb : MExp.arityOk G b = true) :
    MExp.arityOk G (.seq a b) = true := by simp only [MExp.arityOk, ha, hb, Bool.and_self]
theorem ao_alt {a b : MExp} (ha : MExp.arityOk G a = true) (hb : MExp.arityOk G b = true) :
    MExp.arityOk G (.alt a b) = true := by simp only [MExp.arityOk, ha, hb, Bool.and_self]
theorem ao_not {a : MExp} (ha : MExp.arityOk G a = true) : MExp.arityOk G (.notP a) = true := ha
theorem ao_and {a : MExp} (ha : MExp.arityOk G a = true) : MExp.arityOk G (andP a) = true := ha

/-- Expressions without calls are arity-correct in every grammar. -/
theorem arityOk_codeP (k : Nat) : MExp.arityOk G (codeP k) = true := by
  induction k with
  | zero => rfl
  | succ k ih => simp_all [codeP, cNum, MExp.arityOk, one, zero]

theorem arityOk_factE {K : MExp} (hK : MExp.arityOk G K = true) (b : Bool) : MExp.arityOk G (factE K b) = true := by
  cases b <;> simp [factE, MExp.arityOk, hK, zero, optY]

theorem arityOk_ftCall {a b : MExp} (ha : MExp.arityOk G a = true) (hb : MExp.arityOk G b = true) :
    MExp.arityOk G (ftCall M.states a b) = true := by
  simp [ftCall, MExp.arityOk, MExp.arityOkArgs, atmG_ft, ha, hb]

theorem arityOk_state {q : Nat} (hq : q < M.states) {h a p k : MExp} (hh : MExp.arityOk G h = true)
    (ha : MExp.arityOk G a = true) (hp : MExp.arityOk G p = true) (hk : MExp.arityOk G k = true) :
    MExp.arityOk G (.call q [h, a, p, k]) = true := by
  simp [MExp.arityOk, MExp.arityOkArgs, atmG_scan M hq, hh, ha, hp, hk]

theorem arityOk_allChain : ∀ es : List MExp, (∀ e ∈ es, MExp.arityOk G e = true) → MExp.arityOk G (allChain es) = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [allChain, andP, MExp.arityOk, Bool.and_eq_true]
    exact ⟨h e List.mem_cons_self, arityOk_allChain es (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem arityOk_anyChain : ∀ es : List MExp, (∀ e ∈ es, MExp.arityOk G e = true) → MExp.arityOk G (anyChain es) = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [anyChain, MExp.arityOk, Bool.and_eq_true]
    exact ⟨h e List.mem_cons_self, arityOk_anyChain es (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

variable {M}

theorem arityOk_brC (hM : M.WF) {q : Nat} {b : Bool} {A P K : MExp} (hA : MExp.arityOk G A = true)
    (hP : MExp.arityOk G P = true) (hK : MExp.arityOk G K = true) {tr : Nat × Bool × Dir}
    (htr : tr ∈ M.delta q b) : MExp.arityOk G (brC M A P K tr) = true := by
  have hq := hM.2 q b tr htr
  obtain ⟨q', b', d⟩ := tr
  have hfa : MExp.arityOk G (.alt (factE K b') A) = true := ao_alt M (arityOk_factE M hK b') hA
  have hK1 : MExp.arityOk G (.seq K one) = true := ao_seq M hK rfl
  have hft := arityOk_ftCall M hK1 (b := .eps) rfl
  cases d with
  | left => exact arityOk_state M hq hP hfa (arityOk_codeP M 0) rfl
  | right =>
    exact ao_alt M (ao_seq M (ao_and M hft) (arityOk_state M hq (ao_seq M hK1 rfl) hfa (arityOk_codeP M 0) rfl))
      (ao_seq M (ao_not M hft) (arityOk_state M hq (ao_seq M hK rfl) hfa (arityOk_codeP M 0) rfl))

theorem arityOk_transC (hM : M.WF) (q : Nat) (b : Bool) {A P K : MExp} (hA : MExp.arityOk G A = true)
    (hP : MExp.arityOk G P = true) (hK : MExp.arityOk G K = true) : MExp.arityOk G (transC M q b A P K) = true := by
  unfold transC
  split
  · rfl
  · rfl
  · exact arityOk_allChain M _ (fun e he => by
      obtain ⟨tr, htr, rfl⟩ := List.mem_map.1 he; exact arityOk_brC hM hA hP hK htr)
  · exact arityOk_anyChain M _ (fun e he => by
      obtain ⟨tr, htr, rfl⟩ := List.mem_map.1 he; exact arityOk_brC hM hA hP hK htr)

/-- **The simulating grammar is arity-correct.** -/
theorem atmG_arityOk (hM : M.WF) : (atmG M).arityOk = true := by
  simp only [MGrammar.arityOk, List.all_eq_true]
  intro r hr
  simp only [atmG, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with ⟨q, hq, rfl⟩ | rfl
  · have hp : ∀ i, MExp.arityOk G (.param i) = true := fun _ => rfl
    have hsemi : MExp.arityOk G (.seq (.param 1) semi) = true := ao_seq M rfl rfl
    have hst := arityOk_ftCall M (hp 3) hsemi
    have hs₁ := arityOk_transC hM q true (hp 1) (hp 2) (hp 3)
    have hs₂ := arityOk_transC hM q false (hp 1) (hp 2) (hp 3)
    have hK1 : MExp.arityOk G (.seq (.param 3) one) = true := ao_seq M rfl rfl
    have hK0 : MExp.arityOk G (.seq (.param 3) zero) = true := ao_seq M rfl rfl
    have hH := arityOk_ftCall M (hp 3) (hp 0)
    exact ao_alt M (ao_seq M (ao_and M hH) (ao_alt M (ao_seq M (ao_and M hst) hs₁) (ao_seq M (ao_not M hst) hs₂)))
      (ao_seq M (ao_not M hH) (ao_seq M (ao_and M (arityOk_ftCall M hK1 rfl))
        (arityOk_state M hq (hp 0) (hp 1) hK0 hK1)))
  · simp [ftBody, andP, MExp.arityOk, MExp.arityOkArgs, atmG_ft, zero, siteE, codeE, optY, one]

theorem atmStart_arityOk (hM : M.WF) : MExp.arityOk G (atmStart M) = true := by
  have htape : MExp.arityOk G tape0 = true := rfl
  exact ao_seq M (arityOk_state M hM.1 (arityOk_codeP M 0) htape (arityOk_codeP M 0) rfl) rfl

end ArityOk

/-- **EXPTIME-hardness of higher-order Macro PEG at order 1**: the embedded simulating grammar consumes the whole
encoding of `w` iff the machine accepts `w`. -/
theorem atm_reduction_HO {M : ATM} {w : List Bool} (hM : M.WF) (hw : w ≠ []) (hh : M.Halts (M.init w)) :
    HO.HObs (HO.embGrammar (atmG M)) (HO.emb 0 (atmStart M)) (sitesStr w 0) (some []) ↔ M.Accepts w :=
  (HO.emb_obs (atmG_firstOrder M) (atmG_arityOk hM) (atmStart_firstOrder M) (atmStart_arityOk hM) _ _).symm.trans
    (atm_reduction M w hM hw hh)

end Shallot.MacroPeg
