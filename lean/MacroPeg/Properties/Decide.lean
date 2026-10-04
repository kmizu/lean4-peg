import MacroPeg.Properties.ArgEquiv

/-!
# First-order call-by-name Macro PEG is decidable in exponential time

Fix a grammar `g` and an input `x` of length `n`. A position is the length `p ≤ n` of the remaining input
(`sfx x p`). The meaning of a call-by-name actual argument is its result at every position: a *value* is a list
`v : List R` with `R = Option (Option Nat)` (`none` = no finite derivation, `some none` = failure, `some (some j)` =
success leaving `j` symbols). `ev T env e p` evaluates `e` at `p` given a rule table `T` (rule, argument values ↦ value)
and parameter values `env`. The tables `tbl m` are the Kleene iterates (`tbl 0 = ⊥`, `tbl (m+1) i W = ev (tbl m) W
body_i`).

* `derives_ev` (derivation ⇒ some iterate gives its result) and `ev_derives` (a result of any iterate is backed by a
  derivation) — so finite derivations are exactly the defined results of the iterates;
* `tbl_stable` — the iterates stop changing on all relevant entries after `iterBound g x` rounds, by counting the
  defined entries (a finite set: argument values are lists of length `n + 1` over `n + 3` symbols);
* `decideObs` — the resulting decision procedure, with `decideObs_iff : decideObs g x e = some r ↔ MacroObs g e x r`
  and `decideObs_none_iff` (no finite derivation at all);
* `iterBound_eq` — `iterBound g x = Σ_i (n+3)^((n+1)·arity_i) · (n+1)`: exponential in `n` for a fixed grammar.

Each round computes every table entry once, so the running time is `iterBound` rounds times the table size times the
grammar size — exponential in `n`; this last multiplication is counted in the report, not formalized as a cost model.
-/

namespace Shallot.MacroPeg

open Shallot (beqChar leChar stripPrefix?)

abbrev Res := Option (Option Nat)
abbrev Val := List Res

def valAt (v : Val) (p : Nat) : Res := v.getD p none

def sfx (x : List Char) (p : Nat) : List Char := x.drop (x.length - p)

/-- `star` at position `p`, given the results `f` of its body: a non-consuming success has no finite derivation. -/
def evStar (f : Nat → Res) (p : Nat) : Res :=
  match f p with
  | some none => some (some p)
  | some (some j) => if j < p then evStar f j else none
  | none => none
termination_by p
decreasing_by omega

section Eval

variable (g : MGrammar) (x : List Char)

mutual
  def ev (T : Nat → List Val → Val) (env : List Val) : MExp → Nat → Res
    | .eps, p => some (some p)
    | .any, p =>
      match sfx x p with
      | _ :: r => some (some r.length)
      | [] => some none
    | .chr c, p =>
      match sfx x p with
      | d :: r => if beqChar c d then some (some r.length) else some none
      | [] => some none
    | .range lo hi, p =>
      match sfx x p with
      | d :: r => if (leChar lo d && leChar d hi) then some (some r.length) else some none
      | [] => some none
    | .lit s, p =>
      match stripPrefix? s (sfx x p) with
      | some r => some (some r.length)
      | none => some none
    | .param k, p =>
      match env[k]? with
      | some v => valAt v p
      | none => some none
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some r => if r.arity = args.length then valAt (T i (evArgs T env args)) p else some none
      | none => some none
    | .seq a b, p =>
      match ev T env a p with
      | some (some j) => ev T env b j
      | r => r
    | .alt a b, p =>
      match ev T env a p with
      | some none => ev T env b p
      | r => r
    | .star a, p => evStar (fun q => ev T env a q) p
    | .notP a, p =>
      match ev T env a p with
      | some (some _) => some none
      | some none => some (some p)
      | none => none
    | .dbg _, p => some (some p)
    | .lam _ _, p => some (some p)
    | .callParam _ _, _ => some none
    | .invoke _ _ _, _ => none

  def evArgs (T : Nat → List Val → Val) (env : List Val) : List MExp → List Val
    | [] => []
    | a :: as => (List.range (x.length + 1)).map (fun q => ev T env a q) :: evArgs T env as
end

/-- The Kleene iterates of the rule table. -/
def tbl : Nat → Nat → List Val → Val
  | 0 => fun _ _ => []
  | m + 1 => fun i W =>
    match ruleAtM g.rules i with
    | some r => (List.range (x.length + 1)).map (fun p => ev g x (tbl m) W r.body p)
    | none => []

end Eval

/-! ## Unfolding lemmas -/

section Unfold

variable {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val}

theorem ev_seq_ok {a b : MExp} {p j : Nat} (h : ev g x T E a p = some (some j)) :
    ev g x T E (.seq a b) p = ev g x T E b j := by simp only [ev, h]
theorem ev_seq_fail {a b : MExp} {p : Nat} (h : ev g x T E a p = some none) :
    ev g x T E (.seq a b) p = some none := by simp only [ev, h]
theorem ev_seq_none {a b : MExp} {p : Nat} (h : ev g x T E a p = none) : ev g x T E (.seq a b) p = none := by
  simp only [ev, h]
theorem ev_alt_ok {a b : MExp} {p j : Nat} (h : ev g x T E a p = some (some j)) :
    ev g x T E (.alt a b) p = some (some j) := by simp only [ev, h]
theorem ev_alt_fail {a b : MExp} {p : Nat} (h : ev g x T E a p = some none) :
    ev g x T E (.alt a b) p = ev g x T E b p := by simp only [ev, h]
theorem ev_alt_none {a b : MExp} {p : Nat} (h : ev g x T E a p = none) : ev g x T E (.alt a b) p = none := by
  simp only [ev, h]
theorem ev_not_ok {a : MExp} {p j : Nat} (h : ev g x T E a p = some (some j)) :
    ev g x T E (.notP a) p = some none := by simp only [ev, h]
theorem ev_not_fail {a : MExp} {p : Nat} (h : ev g x T E a p = some none) :
    ev g x T E (.notP a) p = some (some p) := by simp only [ev, h]
theorem ev_not_none {a : MExp} {p : Nat} (h : ev g x T E a p = none) : ev g x T E (.notP a) p = none := by
  simp only [ev, h]
theorem ev_star (a : MExp) (p : Nat) : ev g x T E (.star a) p = evStar (fun q => ev g x T E a q) p := by
  simp only [ev]

end Unfold

theorem evStar_fail {f : Nat → Res} {p : Nat} (h : f p = some none) : evStar f p = some (some p) := by
  rw [evStar, h]
theorem evStar_ok {f : Nat → Res} {p j : Nat} (h : f p = some (some j)) (hj : j < p) : evStar f p = evStar f j := by
  rw [evStar, h]; simp [hj]
theorem evStar_stuck {f : Nat → Res} {p j : Nat} (h : f p = some (some j)) (hj : ¬ j < p) : evStar f p = none := by
  rw [evStar, h]; simp [hj]
theorem evStar_none {f : Nat → Res} {p : Nat} (h : f p = none) : evStar f p = none := by
  rw [evStar, h]

theorem valAt_nil (p : Nat) : valAt [] p = none := rfl

theorem valAt_rangeMap (n : Nat) (f : Nat → Res) (p : Nat) :
    valAt ((List.range (n + 1)).map f) p = if p ≤ n then f p else none := by
  unfold valAt
  rw [List.getD_eq_getElem?_getD]
  by_cases hp : p ≤ n
  · rw [if_pos hp, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  · rw [if_neg hp, List.getElem?_eq_none (by simp; omega)]; rfl

/-! ## Information order and monotonicity -/

/-- `r ⊑ r'`: `r` is undefined or equal to `r'`. -/
def RLe (r r' : Res) : Prop := r = none ∨ r = r'
def VLe (v v' : Val) : Prop := ∀ p, RLe (valAt v p) (valAt v' p)
def ArgsLe (W W' : List Val) : Prop := W.length = W'.length ∧ ∀ (k : Nat) w w', W[k]? = some w → W'[k]? = some w' → VLe w w'
def TLe (T T' : Nat → List Val → Val) : Prop := ∀ i W, VLe (T i W) (T' i W)
def MonoT (T : Nat → List Val → Val) : Prop := ∀ i W W', ArgsLe W W' → VLe (T i W) (T i W')

theorem RLe.refl (r : Res) : RLe r r := Or.inr rfl
theorem RLe.trans {a b c : Res} (h₁ : RLe a b) (h₂ : RLe b c) : RLe a c := by
  rcases h₁ with h | rfl
  · exact Or.inl h
  · exact h₂
theorem RLe.eq_of_some {r r' : Res} {v : Option Nat} (h : RLe r r') (hr : r = some v) : r' = some v := by
  rcases h with h | h
  · rw [hr] at h; cases h
  · rw [← h, hr]

theorem ArgsLe.refl (W : List Val) : ArgsLe W W :=
  ⟨rfl, fun _ w w' h h' => by rw [h] at h'; cases h'; exact fun _ => RLe.refl _⟩
theorem ArgsLe.nil : ArgsLe [] [] := ArgsLe.refl []
theorem ArgsLe.cons {w w' : Val} {W W' : List Val} (h : VLe w w') (hs : ArgsLe W W') :
    ArgsLe (w :: W) (w' :: W') := by
  refine ⟨by simp [hs.1], ?_⟩
  intro k a a' ha ha'
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ha'
    subst ha; subst ha'; exact h
  | succ k => exact hs.2 k a a' (by simpa using ha) (by simpa using ha')

theorem evStar_mono {f f' : Nat → Res} : ∀ p, (∀ q, q ≤ p → RLe (f q) (f' q)) → RLe (evStar f p) (evStar f' p) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro h
    rcases h p (Nat.le_refl _) with hp | hp
    · rw [evStar_none hp]; exact Or.inl rfl
    · cases hf : f p with
      | none => rw [evStar_none hf]; exact Or.inl rfl
      | some r =>
        rw [hf] at hp
        cases r with
        | none => rw [evStar_fail hf, evStar_fail hp.symm]; exact RLe.refl _
        | some j =>
          by_cases hj : j < p
          · rw [evStar_ok hf hj, evStar_ok hp.symm hj]
            exact ih j hj (fun q hq => h q (by omega))
          · rw [evStar_stuck hf hj]; exact Or.inl rfl

theorem getElem?_none_iff_len {α β : Type} {l : List α} {l' : List β} (hl : l.length = l'.length) (k : Nat) :
    l[k]? = none ↔ l'[k]? = none := by
  simp only [List.getElem?_eq_none_iff]; omega

mutual
  theorem ev_mono {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} {E E' : List Val}
      (hT : TLe T T') (hM : MonoT T') (hE : ArgsLe E E') :
      ∀ (e : MExp) (p : Nat), RLe (ev g x T E e p) (ev g x T' E' e p)
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .dbg _, _ | .lam _ _, _ | .callParam _ _, _
    | .invoke _ _ _, _ => by simp only [ev]; exact RLe.refl _
    | .param k, p => by
      simp only [ev]
      cases h : E[k]? with
      | none =>
        rw [(getElem?_none_iff_len hE.1 k).1 h]; exact RLe.refl _
      | some v =>
        cases h' : E'[k]? with
        | none => exact absurd ((getElem?_none_iff_len hE.1 k).2 h') (by rw [h]; simp)
        | some v' => exact hE.2 k v v' h h' p
    | .call i args, p => by
      simp only [ev]
      cases hr : ruleAtM g.rules i with
      | none => exact RLe.refl _
      | some r =>
        simp only
        split
        · exact RLe.trans (hT i _ p) (hM i _ _ (evArgs_mono hT hM hE args) p)
        · exact RLe.refl _
    | .seq a b, p => by
      rcases ev_mono hT hM hE a p with h | h
      · rw [ev_seq_none h]; exact Or.inl rfl
      · cases ha : ev g x T E a p with
        | none => rw [ev_seq_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [ev_seq_fail ha, ev_seq_fail h.symm]; exact RLe.refl _
          | some j => rw [ev_seq_ok ha, ev_seq_ok h.symm]; exact ev_mono hT hM hE b j
    | .alt a b, p => by
      rcases ev_mono hT hM hE a p with h | h
      · rw [ev_alt_none h]; exact Or.inl rfl
      · cases ha : ev g x T E a p with
        | none => rw [ev_alt_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [ev_alt_fail ha, ev_alt_fail h.symm]; exact ev_mono hT hM hE b p
          | some j => rw [ev_alt_ok ha, ev_alt_ok h.symm]; exact RLe.refl _
    | .notP a, p => by
      rcases ev_mono hT hM hE a p with h | h
      · rw [ev_not_none h]; exact Or.inl rfl
      · cases ha : ev g x T E a p with
        | none => rw [ev_not_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [ev_not_fail ha, ev_not_fail h.symm]; exact RLe.refl _
          | some j => rw [ev_not_ok ha, ev_not_ok h.symm]; exact RLe.refl _
    | .star a, p => by
      rw [ev_star, ev_star]
      exact evStar_mono p (fun q _ => ev_mono hT hM hE a q)

  theorem evArgs_mono {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} {E E' : List Val}
      (hT : TLe T T') (hM : MonoT T') (hE : ArgsLe E E') :
      ∀ (as : List MExp), ArgsLe (evArgs g x T E as) (evArgs g x T' E' as)
    | [] => ArgsLe.nil
    | a :: as => by
      simp only [evArgs]
      refine ArgsLe.cons ?_ (evArgs_mono hT hM hE as)
      intro q
      rw [valAt_rangeMap, valAt_rangeMap]
      split
      · exact ev_mono hT hM hE a q
      · exact RLe.refl _
end

theorem TLe.refl (T : Nat → List Val → Val) : TLe T T := fun _ _ _ => RLe.refl _
theorem TLe.trans {T₁ T₂ T₃ : Nat → List Val → Val} (h₁ : TLe T₁ T₂) (h₂ : TLe T₂ T₃) : TLe T₁ T₃ :=
  fun i W p => RLe.trans (h₁ i W p) (h₂ i W p)

theorem tbl_mono (g : MGrammar) (x : List Char) : ∀ m, MonoT (tbl g x m)
  | 0 => fun _ _ _ _ p => by simp only [tbl, valAt_nil]; exact RLe.refl _
  | m + 1 => by
    intro i W W' hW p
    simp only [tbl]
    cases ruleAtM g.rules i with
    | none => exact RLe.refl _
    | some r =>
      simp only
      rw [valAt_rangeMap, valAt_rangeMap]
      split
      · exact ev_mono (TLe.refl _) (tbl_mono g x m) hW r.body p
      · exact RLe.refl _

theorem tbl_step (g : MGrammar) (x : List Char) : ∀ m, TLe (tbl g x m) (tbl g x (m + 1))
  | 0 => fun _ _ p => by simp only [tbl, valAt_nil]; exact Or.inl rfl
  | m + 1 => by
    intro i W p
    simp only [tbl]
    cases ruleAtM g.rules i with
    | none => exact RLe.refl _
    | some r =>
      simp only
      rw [valAt_rangeMap, valAt_rangeMap]
      split
      · exact ev_mono (tbl_step g x m) (tbl_mono g x (m + 1)) (ArgsLe.refl W) r.body p
      · exact RLe.refl _

theorem tbl_le (g : MGrammar) (x : List Char) {m m' : Nat} (h : m ≤ m') : TLe (tbl g x m) (tbl g x m') := by
  induction h with
  | refl => exact TLe.refl _
  | step _ ih => exact TLe.trans ih (tbl_step g x _)

/-- Results only get defined along the iterates. -/
theorem ev_tbl_le (g : MGrammar) (x : List Char) {m m' : Nat} (h : m ≤ m') (e : MExp) (p : Nat) :
    RLe (ev g x (tbl g x m) [] e p) (ev g x (tbl g x m') [] e p) :=
  ev_mono (tbl_le g x h) (tbl_mono g x m') ArgsLe.nil e p

/-! ## Positions and the range invariant -/

theorem length_sfx_le (x : List Char) (p : Nat) : (sfx x p).length ≤ x.length := by
  simp [sfx]

theorem length_sfx (x : List Char) {p : Nat} (hp : p ≤ x.length) : (sfx x p).length = p := by
  simp [sfx]; omega

theorem sfx_suffix {x y pre : List Char} (h : x = pre ++ y) : sfx x y.length = y := by
  subst h
  simp [sfx]

theorem stripPrefix_length : ∀ (s y r : List Char), stripPrefix? s y = some r → r.length ≤ y.length
  | [], y, r, h => by simp [stripPrefix?] at h; subst h; exact Nat.le_refl _
  | _ :: _, [], r, h => by simp [stripPrefix?] at h
  | c :: s, d :: y, r, h => by
    simp only [stripPrefix?] at h
    split at h
    · have := stripPrefix_length s y r h; simp; omega
    · cases h

def OkR (n : Nat) (r : Res) : Prop := ∀ j, r = some (some j) → j ≤ n
def OkV (n : Nat) (v : Val) : Prop := ∀ p, OkR n (valAt v p)
def OkT (n : Nat) (T : Nat → List Val → Val) : Prop := ∀ i W, (∀ w ∈ W, OkV n w) → OkV n (T i W)

theorem okR_none (n : Nat) : OkR n none := fun _ h => by cases h
theorem okR_fail (n : Nat) : OkR n (some none) := fun _ h => by cases h
theorem okR_ok {n j : Nat} (h : j ≤ n) : OkR n (some (some j)) := fun _ h' => by cases h'; exact h

theorem evStar_le {f : Nat → Res} : ∀ p j, evStar f p = some (some j) → j ≤ p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro j h
    cases hf : f p with
    | none => rw [evStar_none hf] at h; cases h
    | some r =>
      cases r with
      | none => rw [evStar_fail hf] at h; cases h; exact Nat.le_refl _
      | some k =>
        by_cases hk : k < p
        · rw [evStar_ok hf hk] at h; have := ih k hk j h; omega
        · rw [evStar_stuck hf hk] at h; cases h

theorem okV_rangeMap {n : Nat} {f : Nat → Res} (h : ∀ q, q ≤ n → OkR n (f q)) : OkV n ((List.range (n + 1)).map f) := by
  intro q
  rw [valAt_rangeMap]
  split
  · exact h q (by assumption)
  · exact okR_none n

mutual
  theorem ev_ok {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} (hT : OkT x.length T)
      (hE : ∀ w ∈ E, OkV x.length w) : ∀ (e : MExp) (p : Nat), p ≤ x.length → OkR x.length (ev g x T E e p)
    | .eps, p, hp | .dbg _, p, hp | .lam _ _, p, hp => by simp only [ev]; exact okR_ok hp
    | .callParam _ _, _, _ => by simp only [ev]; exact okR_fail _
    | .invoke _ _ _, _, _ => by simp only [ev]; exact okR_none _
    | .any, p, _ => by
      simp only [ev]
      have := length_sfx_le x p
      split
      · rename_i r h; rw [h] at this; exact okR_ok (by simp at this; omega)
      · exact okR_fail _
    | .chr c, p, _ => by
      simp only [ev]
      have := length_sfx_le x p
      split
      · rename_i d r h
        rw [h] at this
        split
        · exact okR_ok (by simp at this; omega)
        · exact okR_fail _
      · exact okR_fail _
    | .range lo hi, p, _ => by
      simp only [ev]
      have := length_sfx_le x p
      split
      · rename_i d r h
        rw [h] at this
        split
        · exact okR_ok (by simp at this; omega)
        · exact okR_fail _
      · exact okR_fail _
    | .lit s, p, _ => by
      simp only [ev]
      split
      · rename_i r h; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ h) (length_sfx_le x p))
      · exact okR_fail _
    | .param k, p, _ => by
      simp only [ev]
      split
      · rename_i v h; exact hE v (List.mem_of_getElem? h) p
      · exact okR_fail _
    | .call i args, p, _ => by
      simp only [ev]
      split
      · split
        · exact hT i _ (evArgs_ok hT hE args) p
        · exact okR_fail _
      · exact okR_fail _
    | .seq a b, p, hp => by
      have ha := ev_ok (g := g) hT hE a p hp
      cases h : ev g x T E a p with
      | none => rw [ev_seq_none h]; exact okR_none _
      | some r =>
        cases r with
        | none => rw [ev_seq_fail h]; exact okR_fail _
        | some j => rw [ev_seq_ok h]; exact ev_ok hT hE b j (ha j h)
    | .alt a b, p, hp => by
      have ha := ev_ok (g := g) hT hE a p hp
      cases h : ev g x T E a p with
      | none => rw [ev_alt_none h]; exact okR_none _
      | some r =>
        cases r with
        | none => rw [ev_alt_fail h]; exact ev_ok hT hE b p hp
        | some j => rw [ev_alt_ok h]; exact okR_ok (ha j h)
    | .notP a, p, hp => by
      cases h : ev g x T E a p with
      | none => rw [ev_not_none h]; exact okR_none _
      | some r =>
        cases r with
        | none => rw [ev_not_fail h]; exact okR_ok hp
        | some j => rw [ev_not_ok h]; exact okR_fail _
    | .star a, p, hp => by
      rw [ev_star]
      intro j h
      have := evStar_le p j h; omega

  theorem evArgs_ok {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} (hT : OkT x.length T)
      (hE : ∀ w ∈ E, OkV x.length w) : ∀ (as : List MExp), ∀ w ∈ evArgs g x T E as, OkV x.length w
    | [], w, h => by simp [evArgs] at h
    | a :: as, w, h => by
      simp only [evArgs, List.mem_cons] at h
      rcases h with rfl | h
      · exact okV_rangeMap (fun q hq => ev_ok hT hE a q hq)
      · exact evArgs_ok hT hE as w h
end

theorem tbl_ok (g : MGrammar) (x : List Char) : ∀ m, OkT x.length (tbl g x m)
  | 0 => fun _ _ _ p => by simp only [tbl, valAt_nil]; exact okR_none _
  | m + 1 => by
    intro i W hW
    simp only [tbl]
    split
    · exact okV_rangeMap (fun q hq => ev_ok (tbl_ok g x m) hW _ q hq)
    · intro p; simp only [valAt_nil]; exact okR_none _

/-! ## First-order expressions are closed under substitution -/

theorem argAt_firstOrder : ∀ {args : List MExp} {k : Nat} {a : MExp}, MExp.FirstOrderArgs args → argAt args k = some a →
    a.FirstOrder
  | _ :: _, 0, _, h, ha => by cases ha; exact h.1
  | _ :: as, k + 1, _, h, ha => argAt_firstOrder (args := as) (k := k) h.2 ha

mutual
  theorem firstOrder_subst {args : List MExp} (hargs : MExp.FirstOrderArgs args) :
      ∀ (b : MExp), b.FirstOrder → (MExp.subst args b).FirstOrder
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
    | .param k, _ => by
      simp only [MExp.subst]
      split
      · rename_i a h; exact argAt_firstOrder hargs h
      · exact trivial
    | .call _ ms, hb => firstOrderArgs_subst hargs ms hb
    | .seq a b, hb => ⟨firstOrder_subst hargs a hb.1, firstOrder_subst hargs b hb.2⟩
    | .alt a b, hb => ⟨firstOrder_subst hargs a hb.1, firstOrder_subst hargs b hb.2⟩
    | .star a, hb => firstOrder_subst hargs a hb
    | .notP a, hb => firstOrder_subst hargs a hb
    | .dbg _, hb | .lam _ _, hb | .callParam _ _, hb | .invoke _ _ _, hb => absurd hb id

  theorem firstOrderArgs_subst {args : List MExp} (hargs : MExp.FirstOrderArgs args) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → MExp.FirstOrderArgs (MExp.substArgs args ms)
    | [], _ => trivial
    | m :: ms, h => ⟨firstOrder_subst hargs m h.1, firstOrderArgs_subst hargs ms h.2⟩
end

/-! ## The substitution lemma -/

theorem evStar_congr {f f' : Nat → Res} : ∀ p, (∀ q, q ≤ p → f q = f' q) → evStar f p = evStar f' p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro h
    rw [evStar, evStar, h p (Nat.le_refl _)]
    split
    · rfl
    · rename_i j _
      split
      · rename_i hj; exact ih j hj (fun q hq => h q (by omega))
      · rfl
    · rfl

theorem evArgs_getElem? (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) (E : List Val) :
    ∀ (args : List MExp) (k : Nat),
      (evArgs g x T E args)[k]? = (argAt args k).map (fun a => (List.range (x.length + 1)).map (fun q => ev g x T E a q))
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, k + 1 => by simp only [evArgs, List.getElem?_cons_succ, argAt]; exact evArgs_getElem? g x T E as k

theorem length_evArgs (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) (E : List Val) :
    ∀ (args : List MExp), (evArgs g x T E args).length = args.length
  | [] => rfl
  | _ :: as => by simp [evArgs, length_evArgs g x T E as]

theorem ev_failAlways (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) (E : List Val) (p : Nat) :
    ev g x T E MExp.failAlways p = some none := by
  simp [MExp.failAlways, ev]

mutual
  /-- Call-by-name substitution is evaluation in the environment of the arguments' values. -/
  theorem ev_subst {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} (hT : OkT x.length T)
      (hE : ∀ w ∈ E, OkV x.length w) (args : List MExp) :
      ∀ (b : MExp), b.FirstOrder → ∀ p, p ≤ x.length →
        ev g x T E (MExp.subst args b) p = ev g x T (evArgs g x T E args) b p
    | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => by
      simp only [MExp.subst, ev]
    | .param k, _, p, hp => by
      simp only [MExp.subst]
      conv => rhs; simp only [ev]
      rw [evArgs_getElem?]
      cases h : argAt args k with
      | none => simp only [Option.map_none]; exact ev_failAlways g x T E p
      | some a => simp only [Option.map_some]; rw [valAt_rangeMap, if_pos hp]
    | .call j ms, hb, p, _ => by
      simp only [MExp.subst, ev, length_substArgs, evArgs_subst hT hE args ms hb]
    | .seq a c, hb, p, hp => by
      simp only [MExp.subst]
      have ha := ev_subst (g := g) hT hE args a hb.1 p hp
      have hok := ev_ok (g := g) (E := evArgs g x T E args) hT (evArgs_ok (g := g) hT hE args) a p hp
      cases h : ev g x T (evArgs g x T E args) a p with
      | none => rw [ev_seq_none (ha.trans h), ev_seq_none h]
      | some r =>
        cases r with
        | none => rw [ev_seq_fail (ha.trans h), ev_seq_fail h]
        | some j => rw [ev_seq_ok (ha.trans h), ev_seq_ok h]; exact ev_subst hT hE args c hb.2 j (hok j h)
    | .alt a c, hb, p, hp => by
      simp only [MExp.subst]
      have ha := ev_subst (g := g) hT hE args a hb.1 p hp
      cases h : ev g x T (evArgs g x T E args) a p with
      | none => rw [ev_alt_none (ha.trans h), ev_alt_none h]
      | some r =>
        cases r with
        | none => rw [ev_alt_fail (ha.trans h), ev_alt_fail h]; exact ev_subst hT hE args c hb.2 p hp
        | some j => rw [ev_alt_ok (ha.trans h), ev_alt_ok h]
    | .notP a, hb, p, hp => by
      simp only [MExp.subst]
      have ha := ev_subst (g := g) hT hE args a hb p hp
      cases h : ev g x T (evArgs g x T E args) a p with
      | none => rw [ev_not_none (ha.trans h), ev_not_none h]
      | some r =>
        cases r with
        | none => rw [ev_not_fail (ha.trans h), ev_not_fail h]
        | some j => rw [ev_not_ok (ha.trans h), ev_not_ok h]
    | .star a, hb, p, hp => by
      simp only [MExp.subst]
      rw [ev_star, ev_star]
      exact evStar_congr p (fun q hq => ev_subst hT hE args a hb q (by omega))
    | .dbg _, hb, _, _ | .lam _ _, hb, _, _ | .callParam _ _, hb, _, _ | .invoke _ _ _, hb, _, _ => absurd hb id

  theorem evArgs_subst {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} (hT : OkT x.length T)
      (hE : ∀ w ∈ E, OkV x.length w) (args : List MExp) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms →
        evArgs g x T E (MExp.substArgs args ms) = evArgs g x T (evArgs g x T E args) ms
    | [], _ => rfl
    | m :: ms, hm => by
      simp only [MExp.substArgs, evArgs]
      rw [evArgs_subst hT hE args ms hm.2]
      congr 1
      apply List.map_congr_left
      intro q hq
      exact ev_subst hT hE args m hm.1 q (by simp at hq; omega)
end

/-! ## Derivations give defined results -/

/-- The result a derivation's outcome stands for. -/
def obsR : MOutcome → Res
  | .fail => some none
  | .ok _ r => some (some r.length)

theorem ev_lift {g : MGrammar} {x : List Char} {m m' : Nat} (h : m ≤ m') {e : MExp} {p : Nat} {v : Option Nat}
    (hv : ev g x (tbl g x m) [] e p = some v) : ev g x (tbl g x m') [] e p = some v :=
  (ev_tbl_le g x h e p).eq_of_some hv

theorem nil_ok (n : Nat) : ∀ w ∈ ([] : List Val), OkV n w := fun _ h => by cases h

/-- The table entry of the next iterate is the body evaluated in the current one. -/
theorem valAt_tbl_succ {g : MGrammar} {x : List Char} {m i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r)
    (W : List Val) {p : Nat} (hp : p ≤ x.length) : valAt (tbl g x (m + 1) i W) p = ev g x (tbl g x m) W r.body p := by
  simp only [tbl, hr, valAt_rangeMap, if_pos hp]

theorem ev_call_eq {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} {i : Nat}
    {args : List MExp} {r : MRule} (hr : ruleAtM g.rules i = some r) (ha : r.arity = args.length) (p : Nat) :
    ev g x T E (.call i args) p = valAt (T i (evArgs g x T E args)) p := by
  simp only [ev, hr, if_pos ha]

/-- The call step: a result of the substituted body at iterate `m` is the call's result at iterate `m + 1`. -/
theorem ev_call_step {g : MGrammar} {x : List Char} (hg : g.FirstOrder) {m i : Nat} {args : List MExp} {r : MRule}
    (hr : ruleAtM g.rules i = some r) (ha : r.arity = args.length) (hargs : MExp.FirstOrderArgs args) {p : Nat}
    (hp : p ≤ x.length) {v : Option Nat}
    (hm : ev g x (tbl g x m) [] (MExp.subst args r.body) p = some v) :
    ev g x (tbl g x (m + 1)) [] (.call i args) p = some v := by
  rw [ev_subst (tbl_ok g x m) (nil_ok _) args r.body (hg r (ruleAtM_mem hr)) p hp,
    ← valAt_tbl_succ hr _ hp] at hm
  rw [ev_call_eq hr ha]
  exact (tbl_mono g x (m + 1) i _ _ (evArgs_mono (tbl_step g x m) (tbl_mono g x (m + 1)) ArgsLe.nil args) p).eq_of_some hm

theorem suffix_trans {x y z : List Char} (h₁ : ∃ pre, x = pre ++ y) (h₂ : ∃ p, y = p ++ z) : ∃ pre, x = pre ++ z := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂; exact ⟨a ++ b, by simp⟩

theorem suffix_len {x y : List Char} (h : ∃ pre, x = pre ++ y) : y.length ≤ x.length := by
  obtain ⟨pre, rfl⟩ := h; simp

/-- **Derivation ⇒ result.** A finite call-by-name derivation on a suffix of `x` is reproduced by some iterate. -/
theorem derives_ev {g : MGrammar} {x : List Char} (hg : g.FirstOrder) {e : MExp} {y : List Char} {o : MOutcome}
    (h : MDerives g .callByName e y o) :
    e.FirstOrder → (∃ pre, x = pre ++ y) → ∃ m, ev g x (tbl g x m) [] e y.length = obsR o := by
  induction h using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input => intro _ _; exact ⟨0, rfl⟩
  case anyOk c rest =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; rfl
  case anyFail =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; rfl
  case chrOk c d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case chrFail c d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case chrEmpty c =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; rfl
  case rangeOk lo hi d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case rangeFail lo hi d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case rangeEmpty lo hi =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre]; rfl
  case litOk str input rest hs =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre, hs]; rfl
  case litFail str input hs =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [ev]; rw [sfx_suffix hpre, hs]; rfl
  case paramFail k input => intro _ _; exact ⟨0, rfl⟩
  case callNameOk i args r input rest t _ hr ha _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih (firstOrder_subst hfo r.body (hg r (ruleAtM_mem hr))) hsuf
    exact ⟨m + 1, ev_call_step hg hr ha hfo (suffix_len hsuf) hm⟩
  case callNameFail i args r input _ hr ha _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih (firstOrder_subst hfo r.body (hg r (ruleAtM_mem hr))) hsuf
    exact ⟨m + 1, ev_call_step hg hr ha hfo (suffix_len hsuf) hm⟩
  case callMissing i args input hr => intro _ _; exact ⟨0, by simp [ev, hr, obsR]⟩
  case callArity i args r input hr ha => intro _ _; exact ⟨0, by simp [ev, hr, ha, obsR]⟩
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 (suffix_trans hsuf (mderives_suffix h₁ _ _ rfl))
    refine ⟨m₁ + m₂, ?_⟩
    rw [ev_seq_ok (ev_lift (by omega) hm₁)]
    exact ev_lift (by omega) hm₂
  case seqFail₁ e₁ e₂ input _ ih₁ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    exact ⟨m₁, ev_seq_fail hm₁⟩
  case seqFail₂ e₁ e₂ input rest₁ t₁ h₁ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 (suffix_trans hsuf (mderives_suffix h₁ _ _ rfl))
    refine ⟨m₁ + m₂, ?_⟩
    rw [ev_seq_ok (ev_lift (by omega) hm₁)]
    exact ev_lift (by omega) hm₂
  case altL e₁ e₂ input rest t _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo.1 hsuf
    exact ⟨m, ev_alt_ok hm⟩
  case altR e₁ e₂ input rest t _ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 hsuf
    refine ⟨m₁ + m₂, ?_⟩
    rw [ev_alt_fail (ev_lift (by omega) hm₁)]
    exact ev_lift (by omega) hm₂
  case altFail e₁ e₂ input _ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 hsuf
    refine ⟨m₁ + m₂, ?_⟩
    rw [ev_alt_fail (ev_lift (by omega) hm₁)]
    exact ev_lift (by omega) hm₂
  case starNil e input _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo hsuf
    exact ⟨m, by rw [ev_star]; exact evStar_fail hm⟩
  case starCons e input rest rest' t ts h₁ _ ih₁ ih₂ =>
    intro hfo hsuf
    have hsuf' := suffix_trans hsuf (mderives_suffix h₁ _ _ rfl)
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo hsuf'
    have h₁' := ev_lift (m' := m₁ + m₂) (by omega) hm₁
    have h₂' := ev_lift (m' := m₁ + m₂) (by omega) hm₂
    have hle : rest.length ≤ input.length := by
      obtain ⟨q, hq⟩ := mderives_suffix h₁ _ _ rfl; rw [hq]; simp
    by_cases hlt : rest.length < input.length
    · refine ⟨m₁ + m₂, ?_⟩
      rw [ev_star, evStar_ok h₁' hlt, ← ev_star]
      exact h₂'
    · have heq : rest.length = input.length := by omega
      rw [ev_star, heq, evStar_stuck (heq ▸ h₁') (by omega)] at h₂'
      cases h₂'
  case notOk e input rest t _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo hsuf
    exact ⟨m, ev_not_ok hm⟩
  case notFail e input _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo hsuf
    exact ⟨m, ev_not_fail hm⟩
  all_goals first
    | trivial
    | (intro hfo; exact absurd hfo id)
    | (intro _ _; contradiction)

/-! ## Defined results are backed by derivations -/

def SoundV (g : MGrammar) (x : List Char) (v : Val) (a : MExp) : Prop :=
  ∀ q, q ≤ x.length → ∀ r, valAt v q = some r → ∃ o, MDerives g .callByName a (sfx x q) o ∧ obsR o = some r

def SoundArgs (g : MGrammar) (x : List Char) (W : List Val) (args : List MExp) : Prop :=
  W.length = args.length ∧ ∀ (k : Nat) w a, W[k]? = some w → args[k]? = some a → SoundV g x w a

/-- Every defined entry is backed by a derivation of the call, for actual arguments its argument values are sound for. -/
def SoundT (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) : Prop :=
  ∀ i r W args, ruleAtM g.rules i = some r → r.arity = args.length → (∀ w ∈ W, OkV x.length w) →
    SoundArgs g x W args → SoundV g x (T i W) (.call i args)

theorem argAt_eq_get : ∀ (l : List MExp) (k : Nat), argAt l k = l[k]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, k + 1 => by simp [argAt, argAt_eq_get as k]

theorem sfx_is_suffix (x : List Char) (p : Nat) : ∃ pre, x = pre ++ sfx x p := ⟨x.take (x.length - p), by simp [sfx]⟩

theorem obsR_ok {o : MOutcome} {j : Nat} (h : obsR o = some (some j)) : ∃ t rest, o = .ok t rest ∧ rest.length = j := by
  cases o with
  | fail => cases h
  | ok t rest => simp [obsR] at h; exact ⟨t, rest, rfl, h⟩

theorem obsR_fail {o : MOutcome} (h : obsR o = some none) : o = .fail := by
  cases o with
  | fail => rfl
  | ok t rest => cases h

/-- The remaining input after a successful derivation on `sfx x p` with `j` symbols left is `sfx x j`. -/
theorem rest_eq_sfx {g : MGrammar} {x : List Char} {a : MExp} {p : Nat} {t : MTree} {rest : List Char}
    (h : MDerives g .callByName a (sfx x p) (.ok t rest)) : sfx x rest.length = rest :=
  sfx_suffix' (suffix_trans (sfx_is_suffix x p) (mderives_suffix h _ _ rfl))
where
  sfx_suffix' {x rest : List Char} (h : ∃ pre, x = pre ++ rest) : sfx x rest.length = rest := by
    obtain ⟨pre, hpre⟩ := h; exact sfx_suffix hpre

theorem evStar_ne_fail {f : Nat → Res} : ∀ p, evStar f p ≠ some none := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro h
    cases hf : f p with
    | none => rw [evStar_none hf] at h; cases h
    | some r =>
      cases r with
      | none => rw [evStar_fail hf] at h; cases h
      | some j =>
        by_cases hj : j < p
        · rw [evStar_ok hf hj] at h; exact ih j hj h
        · rw [evStar_stuck hf hj] at h; cases h

mutual
  theorem ev_sound {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} {args : List MExp}
      (hT : SoundT g x T) (hTok : OkT x.length T) (hE : SoundArgs g x E args) (hEok : ∀ w ∈ E, OkV x.length w) :
      ∀ (b : MExp), b.FirstOrder → ∀ p, p ≤ x.length → ∀ r, ev g x T E b p = some r →
        ∃ o, MDerives g .callByName (MExp.subst args b) (sfx x p) o ∧ obsR o = some r
    | .eps, _, p, hp, r, hev => by
      simp only [ev, Option.some.injEq] at hev; subst hev
      exact ⟨_, .eps _, by simp [obsR, length_sfx x hp]⟩
    | .any, _, p, _, r, hev => by
      simp only [ev] at hev
      simp only [MExp.subst]
      cases hs : sfx x p with
      | nil => rw [hs] at hev; cases hev; exact ⟨_, .anyFail, rfl⟩
      | cons d rr => rw [hs] at hev; cases hev; exact ⟨_, .anyOk d rr, rfl⟩
    | .chr c, _, p, _, r, hev => by
      simp only [ev] at hev
      simp only [MExp.subst]
      cases hs : sfx x p with
      | nil => rw [hs] at hev; cases hev; exact ⟨_, .chrEmpty c, rfl⟩
      | cons d rr =>
        rw [hs] at hev
        cases hb : beqChar c d
        · simp [hb] at hev; subst hev; exact ⟨_, .chrFail c d rr hb, rfl⟩
        · simp [hb] at hev; subst hev; exact ⟨_, .chrOk c d rr hb, rfl⟩
    | .range lo hi, _, p, _, r, hev => by
      simp only [ev] at hev
      simp only [MExp.subst]
      cases hs : sfx x p with
      | nil => rw [hs] at hev; cases hev; exact ⟨_, .rangeEmpty lo hi, rfl⟩
      | cons d rr =>
        rw [hs] at hev
        cases hb : (leChar lo d && leChar d hi)
        · simp [hb] at hev; subst hev; exact ⟨_, .rangeFail lo hi d rr hb, rfl⟩
        · simp [hb] at hev; subst hev; exact ⟨_, .rangeOk lo hi d rr hb, rfl⟩
    | .lit str, _, p, _, r, hev => by
      simp only [ev] at hev
      simp only [MExp.subst]
      cases hs : stripPrefix? str (sfx x p) with
      | none => rw [hs] at hev; cases hev; exact ⟨_, .litFail _ _ hs, rfl⟩
      | some rr => rw [hs] at hev; cases hev; exact ⟨_, .litOk _ _ rr hs, rfl⟩
    | .param k, _, p, hp, r, hev => by
      simp only [ev] at hev
      simp only [MExp.subst, argAt_eq_get]
      cases hk : E[k]? with
      | none =>
        rw [hk] at hev; cases hev
        rw [(getElem?_none_iff_len hE.1 k).1 hk]
        exact ⟨_, .notOk _ _ _ _ (.eps _), rfl⟩
      | some w =>
        rw [hk] at hev
        cases ha : args[k]? with
        | none => exact absurd ((getElem?_none_iff_len hE.1 k).2 ha) (by rw [hk]; simp)
        | some a => exact hE.2 k w a hk ha p hp r hev
    | .call j ms, hb, p, hp, r, hev => by
      simp only [ev] at hev
      simp only [MExp.subst]
      cases hr : ruleAtM g.rules j with
      | none => rw [hr] at hev; cases hev; exact ⟨_, .callMissing _ _ _ hr, rfl⟩
      | some rr =>
        rw [hr] at hev
        simp only at hev
        by_cases ha : rr.arity = ms.length
        · rw [if_pos ha] at hev
          exact hT j rr _ _ hr (by rw [length_substArgs]; exact ha) (evArgs_ok hTok hEok ms)
            (evArgs_sound hT hTok hE hEok ms hb) p hp r hev
        · rw [if_neg ha] at hev; cases hev
          exact ⟨_, .callArity _ _ rr _ hr (by rw [length_substArgs]; exact ha), rfl⟩
    | .seq a c, hb, p, hp, r, hev => by
      simp only [MExp.subst]
      cases ha : ev g x T E a p with
      | none => rw [ev_seq_none ha] at hev; cases hev
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := ev_sound hT hTok hE hEok a hb.1 p hp ra ha
        cases ra with
        | none =>
          rw [ev_seq_fail ha] at hev; cases hev
          rw [obsR_fail hoa] at da
          exact ⟨_, .seqFail₁ _ _ _ da, rfl⟩
        | some j =>
          rw [ev_seq_ok ha] at hev
          obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
          have hj : j ≤ x.length := ev_ok hTok hEok a p hp j ha
          obtain ⟨oc, dc, hoc⟩ := ev_sound hT hTok hE hEok c hb.2 j hj r hev
          rw [← hlen, rest_eq_sfx da] at dc
          cases oc with
          | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ da dc, hoc⟩
          | ok t' rest' => exact ⟨_, .seqOk _ _ _ _ _ _ _ da dc, hoc⟩
    | .alt a c, hb, p, hp, r, hev => by
      simp only [MExp.subst]
      cases ha : ev g x T E a p with
      | none => rw [ev_alt_none ha] at hev; cases hev
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := ev_sound hT hTok hE hEok a hb.1 p hp ra ha
        cases ra with
        | none =>
          rw [ev_alt_fail ha] at hev
          rw [obsR_fail hoa] at da
          obtain ⟨oc, dc, hoc⟩ := ev_sound hT hTok hE hEok c hb.2 p hp r hev
          cases oc with
          | fail => exact ⟨_, .altFail _ _ _ da dc, hoc⟩
          | ok t' rest' => exact ⟨_, .altR _ _ _ _ _ da dc, hoc⟩
        | some j =>
          rw [ev_alt_ok ha] at hev; cases hev
          obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
          exact ⟨_, .altL _ _ _ _ _ da, by simp [obsR, hlen]⟩
    | .notP a, hb, p, hp, r, hev => by
      simp only [MExp.subst]
      cases ha : ev g x T E a p with
      | none => rw [ev_not_none ha] at hev; cases hev
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := ev_sound hT hTok hE hEok a hb p hp ra ha
        cases ra with
        | none =>
          rw [ev_not_fail ha] at hev; cases hev
          rw [obsR_fail hoa] at da
          exact ⟨_, .notFail _ _ da, by simp [obsR, length_sfx x hp]⟩
        | some j =>
          rw [ev_not_ok ha] at hev; cases hev
          obtain ⟨t, rest, rfl, _⟩ := obsR_ok hoa
          exact ⟨_, .notOk _ _ _ _ da, rfl⟩
    | .star a, hb, p, hp, r, hev => by
      simp only [MExp.subst]
      rw [ev_star] at hev
      induction p using Nat.strongRecOn generalizing r with
      | ind p ih =>
        cases hf : ev g x T E a p with
        | none => rw [evStar_none hf] at hev; cases hev
        | some ra =>
          obtain ⟨oa, da, hoa⟩ := ev_sound hT hTok hE hEok a hb p hp ra hf
          cases ra with
          | none =>
            rw [evStar_fail hf] at hev; cases hev
            rw [obsR_fail hoa] at da
            exact ⟨_, .starNil _ _ da, by simp [obsR, length_sfx x hp]⟩
          | some j =>
            obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
            by_cases hj : j < p
            · rw [evStar_ok hf hj] at hev
              obtain ⟨os, ds, hos⟩ := ih j hj (by omega) r hev
              rw [← hlen, rest_eq_sfx da] at ds
              cases os with
              | fail => cases r with
                | none => exact absurd hev (evStar_ne_fail j)
                | some _ => cases hos
              | ok ts rest' => exact ⟨_, .starCons _ _ _ _ _ _ da ds, hos⟩
            · rw [evStar_stuck hf hj] at hev; cases hev
    | .dbg _, hb, _, _, _, _ | .lam _ _, hb, _, _, _, _ | .callParam _ _, hb, _, _, _, _
    | .invoke _ _ _, hb, _, _, _, _ => absurd hb id

  theorem evArgs_sound {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val} {args : List MExp}
      (hT : SoundT g x T) (hTok : OkT x.length T) (hE : SoundArgs g x E args) (hEok : ∀ w ∈ E, OkV x.length w) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → SoundArgs g x (evArgs g x T E ms) (MExp.substArgs args ms)
    | [], _ => ⟨rfl, fun _ _ _ h => by simp [evArgs] at h⟩
    | m :: ms, hm => by
      have ih := evArgs_sound hT hTok hE hEok ms hm.2
      refine ⟨by simp [evArgs, MExp.substArgs, ih.1], ?_⟩
      intro k w a hw ha
      cases k with
      | zero =>
        simp only [evArgs, MExp.substArgs, List.getElem?_cons_zero, Option.some.injEq] at hw ha
        subst hw; subst ha
        intro q hq r hv
        rw [valAt_rangeMap, if_pos hq] at hv
        exact ev_sound hT hTok hE hEok m hm.1 q hq r hv
      | succ k => exact ih.2 k w a (by simpa [evArgs] using hw) (by simpa [MExp.substArgs] using ha)
end

theorem tbl_sound {g : MGrammar} {x : List Char} (hg : g.FirstOrder) : ∀ m, SoundT g x (tbl g x m)
  | 0 => fun _ _ _ _ _ _ _ _ q _ r hv => by simp [tbl, valAt_nil] at hv
  | m + 1 => by
    intro i r W args hr ha hWok hW q hq res hv
    rw [valAt_tbl_succ hr W hq] at hv
    obtain ⟨o, d, ho⟩ := ev_sound (tbl_sound hg m) (tbl_ok g x m) hW hWok r.body (hg r (ruleAtM_mem hr)) q hq res hv
    cases o with
    | fail => exact ⟨_, .callNameFail i args r _ rfl hr ha d, ho⟩
    | ok t rest => exact ⟨_, .callNameOk i args r _ rest t rfl hr ha d, ho⟩

/-- **Result ⇒ derivation.** A defined result of any iterate on a closed first-order expression is backed by a finite
call-by-name derivation with that outcome. -/
theorem ev_derives {g : MGrammar} {x : List Char} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (he0 : MExp.subst [] e = e) (m : Nat) {p : Nat} (hp : p ≤ x.length) {r : Option Nat}
    (hev : ev g x (tbl g x m) [] e p = some r) :
    ∃ o, MDerives g .callByName e (sfx x p) o ∧ obsR o = some r := by
  have := ev_sound (args := []) (tbl_sound hg m) (tbl_ok g x m) ⟨rfl, fun _ _ _ h => by simp at h⟩ (nil_ok _) e he p hp
    r hev
  rwa [he0] at this

/-! ## The value space is finite -/

/-- The `n + 3` possible results at a position. -/
def rSyms (n : Nat) : List Res := none :: some none :: (List.range (n + 1)).map (fun j => some (some j))

/-- All lists of length `k` over `syms`. -/
def words {α : Type} (syms : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => syms.flatMap (fun s => (words syms k).map (s :: ·))

theorem length_words {α : Type} (syms : List α) : ∀ k, (words syms k).length = syms.length ^ k
  | 0 => rfl
  | k + 1 => by
    simp only [words, List.length_flatMap, List.length_map, length_words syms k]
    rw [List.map_const', sum_replicate_nat, Nat.pow_succ, Nat.mul_comm]

theorem mem_words {α : Type} (syms : List α) : ∀ (k : Nat) (w : List α),
    w ∈ words syms k ↔ w.length = k ∧ ∀ a ∈ w, a ∈ syms
  | 0, w => by cases w <;> simp [words]
  | k + 1, w => by
    cases w with
    | nil => simp [words]
    | cons a w =>
      simp only [words, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons, List.mem_cons,
        forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨s, hs, w', hw', rfl, rfl⟩
        exact ⟨((mem_words syms k w').1 hw').1, hs, ((mem_words syms k w').1 hw').2⟩
      · rintro ⟨hl, ha, hw⟩
        exact ⟨a, ha, w, (mem_words syms k w).2 ⟨hl, hw⟩, rfl, rfl⟩

/-- All values: lists of length `n + 1` over the `n + 3` results. -/
def allVals (n : Nat) : List Val := words (rSyms n) (n + 1)

theorem length_rSyms (n : Nat) : (rSyms n).length = n + 3 := by simp [rSyms]

theorem mem_rSyms {n : Nat} {r : Res} (h : OkR n r) : r ∈ rSyms n := by
  simp only [rSyms, List.mem_cons, List.mem_map, List.mem_range]
  rcases r with _ | _ | j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨j, by have := h j rfl; omega, rfl⟩)

theorem okR_of_mem {n : Nat} {r : Res} (h : r ∈ rSyms n) : OkR n r := by
  simp only [rSyms, List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with rfl | rfl | ⟨j, hj, rfl⟩
  · exact okR_none n
  · exact okR_fail n
  · exact okR_ok (by omega)

theorem rangeMap_mem_allVals {n : Nat} {f : Nat → Res} (h : ∀ q, q ≤ n → OkR n (f q)) :
    (List.range (n + 1)).map f ∈ allVals n := by
  refine (mem_words _ _ _).2 ⟨by simp, ?_⟩
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
  exact mem_rSyms (h q (by simp at hq; omega))

theorem okV_of_mem_allVals {n : Nat} {v : Val} (h : v ∈ allVals n) : OkV n v := by
  intro p
  unfold valAt
  rw [List.getD_eq_getElem?_getD]
  cases hp : v[p]? with
  | none => exact okR_none n
  | some r => exact okR_of_mem (((mem_words _ _ _).1 h).2 r (List.mem_of_getElem? hp))

theorem evArgs_mem {g : MGrammar} {x : List Char} {T : Nat → List Val → Val} {E : List Val}
    (hT : OkT x.length T) (hE : ∀ w ∈ E, OkV x.length w) (as : List MExp) :
    evArgs g x T E as ∈ words (allVals x.length) as.length := by
  refine (mem_words _ _ _).2 ⟨length_evArgs g x T E as, ?_⟩
  induction as with
  | nil => intro a ha; simp [evArgs] at ha
  | cons a as ih =>
    intro w hw
    simp only [evArgs, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact rangeMap_mem_allVals (fun q hq => ev_ok hT hE a q hq)
    · exact ih w hw

/-! ## Agreement on the relevant entries -/

/-- Two tables agree on every entry an evaluation can query: an existing rule, argument values from `allVals`, a
position `≤ n`. -/
def Agree (g : MGrammar) (x : List Char) (T T' : Nat → List Val → Val) : Prop :=
  ∀ i r W, ruleAtM g.rules i = some r → W ∈ words (allVals x.length) r.arity → ∀ p, p ≤ x.length →
    valAt (T i W) p = valAt (T' i W) p

theorem Agree.refl (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) : Agree g x T T :=
  fun _ _ _ _ _ _ _ => rfl
theorem Agree.symm {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} (h : Agree g x T T') : Agree g x T' T :=
  fun i r W hr hW p hp => (h i r W hr hW p hp).symm
theorem Agree.trans {g : MGrammar} {x : List Char} {T₁ T₂ T₃ : Nat → List Val → Val} (h₁ : Agree g x T₁ T₂)
    (h₂ : Agree g x T₂ T₃) : Agree g x T₁ T₃ :=
  fun i r W hr hW p hp => (h₁ i r W hr hW p hp).trans (h₂ i r W hr hW p hp)

mutual
  theorem ev_agree {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} {E : List Val} (h : Agree g x T T')
      (hT : OkT x.length T) (hT' : OkT x.length T') (hE : ∀ w ∈ E, OkV x.length w) :
      ∀ (e : MExp) (p : Nat), p ≤ x.length → ev g x T E e p = ev g x T' E e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ | .dbg _, _, _ | .lam _ _, _, _
    | .callParam _ _, _, _ | .invoke _ _ _, _, _ | .param _, _, _ => by simp only [ev]
    | .call i args, p, hp => by
      simp only [ev]
      cases hr : ruleAtM g.rules i with
      | none => rfl
      | some r =>
        simp only
        split
        · rename_i ha
          rw [evArgs_agree h hT hT' hE args]
          exact h i r _ hr (ha ▸ evArgs_mem hT' hE args) p hp
        · rfl
    | .seq a b, p, hp => by
      have ha := ev_agree (g := g) h hT hT' hE a p hp
      cases hv : ev g x T E a p with
      | none => rw [ev_seq_none hv, ev_seq_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [ev_seq_fail hv, ev_seq_fail (ha.symm.trans hv)]
        | some j =>
          rw [ev_seq_ok hv, ev_seq_ok (ha.symm.trans hv)]
          exact ev_agree h hT hT' hE b j (ev_ok hT hE a p hp j hv)
    | .alt a b, p, hp => by
      have ha := ev_agree (g := g) h hT hT' hE a p hp
      cases hv : ev g x T E a p with
      | none => rw [ev_alt_none hv, ev_alt_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [ev_alt_fail hv, ev_alt_fail (ha.symm.trans hv)]; exact ev_agree h hT hT' hE b p hp
        | some j => rw [ev_alt_ok hv, ev_alt_ok (ha.symm.trans hv)]
    | .notP a, p, hp => by
      have ha := ev_agree (g := g) h hT hT' hE a p hp
      cases hv : ev g x T E a p with
      | none => rw [ev_not_none hv, ev_not_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [ev_not_fail hv, ev_not_fail (ha.symm.trans hv)]
        | some j => rw [ev_not_ok hv, ev_not_ok (ha.symm.trans hv)]
    | .star a, p, hp => by
      rw [ev_star, ev_star]
      exact evStar_congr p (fun q hq => ev_agree h hT hT' hE a q (by omega))

  theorem evArgs_agree {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} {E : List Val}
      (h : Agree g x T T') (hT : OkT x.length T) (hT' : OkT x.length T') (hE : ∀ w ∈ E, OkV x.length w) :
      ∀ (as : List MExp), evArgs g x T E as = evArgs g x T' E as
    | [] => rfl
    | a :: as => by
      simp only [evArgs]
      rw [evArgs_agree h hT hT' hE as]
      congr 1
      apply List.map_congr_left
      intro q hq
      exact ev_agree h hT hT' hE a q (by simp at hq; omega)
end

theorem agree_succ {g : MGrammar} {x : List Char} {m : Nat} (h : Agree g x (tbl g x m) (tbl g x (m + 1))) :
    Agree g x (tbl g x (m + 1)) (tbl g x (m + 2)) := by
  intro i r W hr hW p hp
  rw [valAt_tbl_succ hr W hp, valAt_tbl_succ hr W hp]
  exact ev_agree h (tbl_ok g x m) (tbl_ok g x (m + 1))
    (fun w hw => okV_of_mem_allVals (((mem_words _ _ _).1 hW).2 w hw)) r.body p hp

theorem agree_from {g : MGrammar} {x : List Char} {m : Nat} (h : Agree g x (tbl g x m) (tbl g x (m + 1))) :
    ∀ k, Agree g x (tbl g x m) (tbl g x (m + k)) := by
  have step : ∀ k, Agree g x (tbl g x (m + k)) (tbl g x (m + k + 1)) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih => exact agree_succ ih
  intro k
  induction k with
  | zero => exact Agree.refl _ _ _
  | succ k ih => exact ih.trans (step k)

/-! ## Counting defined entries -/

theorem sum_le_sum_of_le {α : Type} (f h : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ h a) → (l.map f).sum ≤ (l.map h).sum
  | [], _ => Nat.le_refl _
  | a :: l, hl => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_sum_of_le f h l (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    have := hl a List.mem_cons_self
    omega

theorem eq_of_sum_eq {α : Type} (f h : α → Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ h a) → (l.map f).sum = (l.map h).sum → ∀ a ∈ l, f a = h a
  | [], _, _, a, ha => by cases ha
  | b :: l, hl, he, a, ha => by
    simp only [List.map_cons, List.sum_cons] at he
    have h₁ := sum_le_sum_of_le f h l (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    have h₂ := hl b List.mem_cons_self
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · exact eq_of_sum_eq f h l (fun c hc => hl c (List.mem_cons_of_mem _ hc)) (by omega) a ha

theorem sum_le_length_mul {α : Type} (f : α → Nat) (c : Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ c) → (l.map f).sum ≤ l.length * c
  | [], _ => by simp
  | a :: l, hl => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := sum_le_length_mul f c l (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    have := hl a List.mem_cons_self
    omega

def defined (r : Res) : Nat := if r.isSome then 1 else 0

def entryCount (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) (i : Nat) : Nat :=
  match ruleAtM g.rules i with
  | some r =>
    ((words (allVals x.length) r.arity).map
      (fun W => ((List.range (x.length + 1)).map (fun p => defined (valAt (T i W) p))).sum)).sum
  | none => 0

/-- The number of defined relevant entries of a table. -/
def defCount (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) : Nat :=
  ((List.range g.rules.length).map (entryCount g x T)).sum

/-- The number of relevant entries: `Σ_i |allVals|^arity_i · (n + 1)`. -/
def iterBound (g : MGrammar) (x : List Char) : Nat :=
  ((List.range g.rules.length).map (fun i =>
    match ruleAtM g.rules i with
    | some r => (words (allVals x.length) r.arity).length * (x.length + 1)
    | none => 0)).sum

theorem defined_le {r r' : Res} (h : RLe r r') : defined r ≤ defined r' := by
  rcases h with rfl | rfl
  · simp [defined]
  · exact Nat.le_refl _

theorem defined_le_one (r : Res) : defined r ≤ 1 := by unfold defined; split <;> omega

theorem defCount_le {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} (h : TLe T T') :
    defCount g x T ≤ defCount g x T' := by
  refine sum_le_sum_of_le _ _ _ (fun i _ => ?_)
  unfold entryCount
  split
  · exact sum_le_sum_of_le _ _ _ (fun W _ => sum_le_sum_of_le _ _ _ (fun p _ => defined_le (h i W p)))
  · exact Nat.le_refl _

theorem defCount_le_bound (g : MGrammar) (x : List Char) (T : Nat → List Val → Val) :
    defCount g x T ≤ iterBound g x := by
  refine sum_le_sum_of_le _ _ _ (fun i _ => ?_)
  unfold entryCount
  split
  · refine sum_le_length_mul _ _ _ (fun W _ => ?_)
    have := sum_le_length_mul (fun p => defined (valAt (T i W) p)) 1 (List.range (x.length + 1))
      (fun p _ => defined_le_one _)
    simpa using this
  · exact Nat.le_refl _

theorem ruleAtM_lt {rs : List MRule} {i : Nat} {r : MRule} (h : ruleAtM rs i = some r) : i < rs.length := by
  rw [ruleAtM_eq_getElem?] at h; exact (List.getElem?_eq_some_iff.1 h).1

theorem agree_of_count_eq {g : MGrammar} {x : List Char} {T T' : Nat → List Val → Val} (h : TLe T T')
    (he : defCount g x T = defCount g x T') : Agree g x T T' := by
  intro i r W hr hW p hp
  have hi := eq_of_sum_eq _ _ _ (fun i _ => by
      unfold entryCount
      split
      · exact sum_le_sum_of_le _ _ _ (fun W _ => sum_le_sum_of_le _ _ _ (fun p _ => defined_le (h i W p)))
      · exact Nat.le_refl _) he i (List.mem_range.2 (ruleAtM_lt hr))
  simp only [entryCount, hr] at hi
  have hW' := eq_of_sum_eq _ _ _ (fun W _ => sum_le_sum_of_le _ _ _ (fun p _ => defined_le (h i W p))) hi W hW
  have hp' := eq_of_sum_eq _ _ _ (fun p _ => defined_le (h i W p)) hW' p (List.mem_range.2 (by omega))
  rcases h i W p with h₀ | h₀
  · rw [h₀] at hp' ⊢
    cases hv : valAt (T' i W) p with
    | none => rfl
    | some v => rw [hv] at hp'; simp [defined] at hp'
  · exact h₀

/-- Pigeonhole: within `iterBound` rounds some round changes no relevant entry. -/
theorem tbl_fix_exists (g : MGrammar) (x : List Char) :
    ∃ m, m ≤ iterBound g x ∧ Agree g x (tbl g x m) (tbl g x (m + 1)) := by
  refine Classical.byContradiction fun hne => ?_
  have hlt : ∀ m, m ≤ iterBound g x → defCount g x (tbl g x m) < defCount g x (tbl g x (m + 1)) := by
    intro m hm
    refine Nat.lt_of_le_of_ne (defCount_le (tbl_step g x m)) (fun heq => hne ⟨m, hm, ?_⟩)
    exact agree_of_count_eq (tbl_step g x m) heq
  have hgrow : ∀ m, m ≤ iterBound g x + 1 → m ≤ defCount g x (tbl g x m) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih => intro hm; have := hlt m (by omega); have := ih (by omega); omega
  have := hgrow _ (Nat.le_refl _)
  have := defCount_le_bound g x (tbl g x (iterBound g x + 1))
  omega

/-- After `iterBound` rounds the iterates no longer change any result on a closed expression. -/
theorem tbl_stable (g : MGrammar) (x : List Char) {e : MExp} {p : Nat} (hp : p ≤ x.length) {v : Option Nat} :
    (∃ m, ev g x (tbl g x m) [] e p = some v) ↔ ev g x (tbl g x (iterBound g x)) [] e p = some v := by
  obtain ⟨m₀, hm₀, hfix⟩ := tbl_fix_exists g x
  have hag := agree_from hfix
  have hB : ev g x (tbl g x (iterBound g x)) [] e p = ev g x (tbl g x m₀) [] e p := by
    have := hag (iterBound g x - m₀)
    rw [Nat.add_sub_cancel' hm₀] at this
    exact (ev_agree this (tbl_ok g x _) (tbl_ok g x _) (nil_ok _) e p hp).symm
  constructor
  · rintro ⟨m, hm⟩
    by_cases hle : m ≤ iterBound g x
    · exact ev_lift hle hm
    · have := hag (m - m₀)
      rw [Nat.add_sub_cancel' (by omega)] at this
      rw [hB, ev_agree this (tbl_ok g x _) (tbl_ok g x _) (nil_ok _) e p hp]
      exact hm
  · intro h; exact ⟨_, h⟩

/-! ## The decision procedure -/

def decideRes (g : MGrammar) (x : List Char) (e : MExp) : Res := ev g x (tbl g x (iterBound g x)) [] e x.length

/-- `none`: no finite derivation; `some none`: failure; `some (some rest)`: success leaving `rest`. -/
def decideObs (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match decideRes g x e with
  | none => none
  | some none => some none
  | some (some j) => some (some (sfx x j))

theorem sfx_self (x : List Char) : sfx x x.length = x := by simp [sfx]

/-- **Decidability.** For a first-order grammar and a closed first-order expression, `decideObs` returns exactly the
observation of the (unique) finite call-by-name derivation on `x`. -/
theorem decideObs_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder) (he0 : MExp.subst [] e = e)
    (x : List Char) (r : Option (List Char)) : decideObs g x e = some r ↔ MacroObs g e x r := by
  constructor
  · intro h
    unfold decideObs at h
    cases hd : decideRes g x e with
    | none => rw [hd] at h; cases h
    | some v =>
      obtain ⟨o, d, ho⟩ := ev_derives hg he he0 (iterBound g x) (Nat.le_refl _) hd
      rw [sfx_self] at d
      cases v with
      | none =>
        rw [hd] at h; cases h
        rw [obsR_fail ho] at d
        exact ⟨_, d, rfl⟩
      | some j =>
        rw [hd] at h; cases h
        obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok ho
        refine ⟨_, d, ?_⟩
        rw [← hlen, sfx_suffix (mderives_suffix d _ _ rfl).choose_spec]
        rfl
  · rintro ⟨o, d, rfl⟩
    obtain ⟨m, hm⟩ := derives_ev hg d he ⟨[], rfl⟩
    cases o with
    | fail =>
      have := (tbl_stable g x (Nat.le_refl _)).1 ⟨m, hm⟩
      simp [decideObs, decideRes, this, obsR, MOutcome.restOf]
    | ok t rest =>
      have := (tbl_stable g x (Nat.le_refl _)).1 ⟨m, hm⟩
      simp only [decideObs, decideRes, this, MOutcome.restOf]
      rw [sfx_suffix (mderives_suffix d _ _ rfl).choose_spec]

theorem decideObs_none_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (he0 : MExp.subst [] e = e) (x : List Char) : decideObs g x e = none ↔ ∀ r, ¬ MacroObs g e x r := by
  constructor
  · intro h r hr
    rw [(decideObs_iff hg he he0 x r).2 hr] at h; cases h
  · intro h
    cases hd : decideObs g x e with
    | none => rfl
    | some r => exact absurd ((decideObs_iff hg he he0 x r).1 hd) (h r)

/-- Recognition (whole consumption) is decidable. -/
theorem recognizesAll_decide {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (he0 : MExp.subst [] e = e) (x : List Char) : MRecognizesAll g e x ↔ decideObs g x e = some (some []) :=
  (decideObs_iff hg he he0 x (some [])).symm

/-! ## The bound -/

/-- **The number of rounds**: `Σ_i (n+3)^((n+1)·arity_i) · (n+1)` for the rules `i` of `g`, `n = |x|`. -/
theorem iterBound_eq (g : MGrammar) (x : List Char) :
    iterBound g x = ((List.range g.rules.length).map (fun i =>
      match ruleAtM g.rules i with
      | some r => (x.length + 3) ^ ((x.length + 1) * r.arity) * (x.length + 1)
      | none => 0)).sum := by
  unfold iterBound
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · rw [length_words, allVals, length_words, length_rSyms, ← Nat.pow_mul]
  · rfl

/-- With every arity at most `K`: at most `|rules| · (n+3)^((n+1)·K) · (n+1)` rounds — exponential in `n`. -/
theorem iterBound_le (g : MGrammar) (x : List Char) {K : Nat} (hK : ∀ r ∈ g.rules, r.arity ≤ K) :
    iterBound g x ≤ g.rules.length * ((x.length + 3) ^ ((x.length + 1) * K) * (x.length + 1)) := by
  rw [iterBound_eq]
  have := sum_le_length_mul (fun i => match ruleAtM g.rules i with
      | some r => (x.length + 3) ^ ((x.length + 1) * r.arity) * (x.length + 1)
      | none => 0) ((x.length + 3) ^ ((x.length + 1) * K) * (x.length + 1)) (List.range g.rules.length) (by
    intro i _
    split
    · rename_i r hr
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left _ (hK r (ruleAtM_mem hr))))
    · exact Nat.zero_le _)
  simpa using this

/-! ## Examples (computed by the decision procedure) -/

/-- `S ← "a" S / ε` consumes `aa`; `L ← L` has no finite derivation (non-termination is decided, not timed out). -/
def exDecG : MGrammar := ⟨[⟨0, .alt (.seq (.lit ['a']) (.call 0 [])) .eps⟩, ⟨0, .call 1 []⟩]⟩

example : decideObs exDecG ['a', 'a'] (.call 0 []) = some (some []) := by decide
example : decideObs exDecG ['a', 'b'] (.call 0 []) = some (some ['b']) := by decide
example : decideObs exDecG ['a'] (.call 1 []) = none := by decide

/-- Hence `L ← L` has no observation at all on `a`, proved through the decision procedure. -/
example : ∀ r, ¬ MacroObs exDecG (.call 1 []) ['a'] r := by
  have hg : exDecG.FirstOrder := by
    intro r hr
    simp only [exDecG, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [MExp.FirstOrder, MExp.FirstOrderArgs]
  exact (decideObs_none_iff hg (e := .call 1 []) (by simp [MExp.FirstOrder, MExp.FirstOrderArgs]) rfl ['a']).1
    (by decide)

end Shallot.MacroPeg
