import MacroPeg.CBV.EvalSpec

namespace Shallot.MacroPeg.CBV

/-- A round reads one finite numeric row and writes the next, with no functional table argument. -/
def numericRound (s : Strategy) (g : MGrammar) (x : List Char) (row : List Nat) : List Nat :=
  (keys g x).map (fun k => match ruleAtM g.rules k.1 with
    | none => 0
    | some r => resultCode (eval g x s row k.2.1 r.body k.2.2))

theorem numericRound_pack (s : Strategy) (g : MGrammar) (x : List Char) (m : Nat) :
    numericRound s g x (pack g x (tblV g x s m)) = pack g x (tblV g x s (m + 1)) := by
  rw [← round_pack s g x m]
  unfold numericRound round
  apply List.map_congr_left
  intro k hk
  cases hr : ruleAtM g.rules k.1 with
  | none => rfl
  | some r =>
    have hp := (key_valid hk).choose_spec.2.2
    simp only
    congr 1
    exact (eval_correct (g := g) (s := s) (E := k.2.1) (tblV_ok g x s m) r.body k.2.2 hp).trans
      (evV_agree (unpack_pack g x (tblV g x s m)).symm (tblV_ok g x s m) r.body k.2.2 hp)

def numericIterate (s : Strategy) (g : MGrammar) (x : List Char) : Nat → List Nat
  | 0 => List.replicate (keys g x).length 0
  | m + 1 => numericRound s g x (numericIterate s g x m)

theorem numericIterate_pack (s : Strategy) (g : MGrammar) (x : List Char) (m : Nat) :
    numericIterate s g x m = pack g x (tblV g x s m) := by
  induction m with
  | zero => simp [numericIterate, pack, tblV, valAt, resultCode, List.map_const']
  | succ m ih => rw [numericIterate, ih, numericRound_pack]

/-- Execute enough finite-row iterations and evaluate the closed entry. -/
def numericDecide (s : Strategy) (g : MGrammar) (x : List Char) (e : MExp) : Res :=
  eval g x s (numericIterate s g x (iterBoundV g x)) [] e x.length

theorem numericDecide_eq (s : Strategy) (g : MGrammar) (x : List Char) (e : MExp) :
    numericDecide s g x e = evV g x s (tblV g x s (iterBoundV g x)) [] e x.length := by
  unfold numericDecide
  rw [numericIterate_pack]
  exact eval_correct (E := []) (tblV_ok g x s _) e x.length (Nat.le_refl _)

def numericObservation (s : Strategy) (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match numericDecide s g x e with
  | none => none
  | some none => some none
  | some (some p) => some (some (sfx x p))

theorem numericObservation_eq (s : Strategy) (g : MGrammar) (x : List Char) (e : MExp) :
    numericObservation s g x e = decideObsV s g x e := by
  simp only [numericObservation, numericDecide_eq, decideObsV]
  rfl

theorem numericObservation_iff {s : Strategy} {g : MGrammar} {e : MExp}
    (hg : g.FirstOrder) (hs : s ≠ .callByName) (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) :
    numericObservation s g x e = some r ↔ SObs g s e x r := by
  rw [numericObservation_eq]
  exact decideObsV_iff hg hs he x r

/-- Full-input acceptance is exactly the numeric success with zero remaining characters. -/
theorem numericAccept_iff {s : Strategy} {g : MGrammar} {e : MExp}
    (hg : g.FirstOrder) (hs : s ≠ .callByName) (he : e.FirstOrder) (x : List Char) :
    numericDecide s g x e = some (some 0) ↔ SObs g s e x (some []) := by
  rw [← numericObservation_iff hg hs he]
  unfold numericObservation
  have hok : OkR x.length (numericDecide s g x e) := by
    rw [numericDecide_eq]
    exact evV_ok (tblV_ok g x s _) e x.length (Nat.le_refl _)
  cases h : numericDecide s g x e with
  | none => simp
  | some r => cases r with
    | none => simp
    | some p =>
      have hp := hok p h
      have hsfx : sfx x p = [] ↔ p = 0 := by
        simp only [sfx, List.drop_eq_nil_iff]
        omega
      simpa only [Option.some.injEq] using hsfx.symm

/-- The fully numeric iterations retain the polynomial storage bound of the semantic table. -/
theorem numericIterate_size (s : Strategy) (g : MGrammar) (x : List Char) (m : Nat) {K : Nat}
    (hK : ∀ r ∈ g.rules, r.arity ≤ K) :
    (numericIterate s g x m).length ≤ g.rules.length * (((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1)) ∧
    RowBound x.length (numericIterate s g x m) := by
  rw [numericIterate_pack]
  exact ⟨by rw [pack_length]; exact iterBoundV_le g x hK, pack_bound (tblV_ok g x s m)⟩

end Shallot.MacroPeg.CBV
