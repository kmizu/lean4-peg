import MacroPeg.Properties.Decide
import MacroPeg.Properties.Strategy

/-!
# First-order call-by-value Macro PEG is decidable in polynomial time

Under the call-by-value strategies (`callByValuePar`, `callByValueSeq`) an actual argument is evaluated first and the
callee receives the consumed prefix as a literal (`.lit p`). That prefix is a substring of the input, so an argument value
is one of at most `(n+1)(n+2)/2` strings — unlike call-by-name, where it is a whole function from positions to results
(`Decide.lean`). The same Kleene iteration of rule tables therefore runs a polynomial number of rounds:

* `derivesV_ev` / `evV_derives`: finite derivations under Par/Seq are exactly the defined results of the iterates;
* `decideObsV_iff` / `decideObsV_none_iff`: the decision procedure;
* `iterBoundV_le`: at most `|rules| · ((n+1)(n+2))^K · (n+1)` rounds (`K` the largest arity) — polynomial in `n` for a
  fixed grammar.

With the PSPACE-hardness of first-order call-by-name (`QbfHard.lean`), this separates the strategies unless P = PSPACE.
-/

namespace Shallot.MacroPeg

open Shallot (beqChar leChar stripPrefix?)

/-- The prefix consumed from position `p` to position `j`. -/
def pre (x : List Char) (p j : Nat) : List Char := (sfx x p).take (p - j)

section EvalV

variable (g : MGrammar) (x : List Char)

mutual
  def evV (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) : MExp → Nat → Res
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
    | .lit w, p =>
      match stripPrefix? w (sfx x p) with
      | some r => some (some r.length)
      | none => some none
    | .param k, p =>
      match E[k]? with
      | some w =>
        match stripPrefix? w (sfx x p) with
        | some r => some (some r.length)
        | none => some none
      | none => some none
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some r =>
        if r.arity = args.length then
          match s with
          | .callByValueSeq =>
            match evSeqArgs s T E args p with
            | some (some (W, q)) => valAt (T i W) q
            | some none => some none
            | none => none
          | _ =>
            match evParArgs s T E args p with
            | some (some W) => valAt (T i W) p
            | some none => some none
            | none => none
        else some none
      | none => some none
    | .seq a b, p =>
      match evV s T E a p with
      | some (some j) => evV s T E b j
      | r => r
    | .alt a b, p =>
      match evV s T E a p with
      | some none => evV s T E b p
      | r => r
    | .star a, p => evStar (fun q => evV s T E a q) p
    | .notP a, p =>
      match evV s T E a p with
      | some (some _) => some none
      | some none => some (some p)
      | none => none
    | .dbg _, p => some (some p)
    | .lam _ _, p => some (some p)
    | .callParam _ _, _ => some none
    | .invoke _ _ _, _ => none

  /-- Par: every argument at the same position, left to right, stopping at the first failure. -/
  def evParArgs (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) :
      List MExp → Nat → Option (Option (List (List Char)))
    | [], _ => some (some [])
    | a :: as, p =>
      match evV s T E a p with
      | some (some j) =>
        match evParArgs s T E as p with
        | some (some W) => some (some (pre x p j :: W))
        | r => r
      | some none => some none
      | none => none

  /-- Seq: arguments threaded through the input; returns the values and the final position. -/
  def evSeqArgs (s : Strategy) (T : Nat → List (List Char) → Val) (E : List (List Char)) :
      List MExp → Nat → Option (Option (List (List Char) × Nat))
    | [], p => some (some ([], p))
    | a :: as, p =>
      match evV s T E a p with
      | some (some j) =>
        match evSeqArgs s T E as j with
        | some (some (W, q)) => some (some (pre x p j :: W, q))
        | r => r
      | some none => some none
      | none => none
end

def tblV (s : Strategy) : Nat → Nat → List (List Char) → Val
  | 0 => fun _ _ => []
  | m + 1 => fun i W =>
    match ruleAtM g.rules i with
    | some r => (List.range (x.length + 1)).map (fun p => evV g x s (tblV s m) W r.body p)
    | none => []

end EvalV

/-! ## Unfolding lemmas -/

section UnfoldV

variable {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val} {E : List (List Char)}

theorem evV_seq_ok {a b : MExp} {p j : Nat} (h : evV g x s T E a p = some (some j)) :
    evV g x s T E (.seq a b) p = evV g x s T E b j := by simp only [evV, h]
theorem evV_seq_fail {a b : MExp} {p : Nat} (h : evV g x s T E a p = some none) :
    evV g x s T E (.seq a b) p = some none := by simp only [evV, h]
theorem evV_seq_none {a b : MExp} {p : Nat} (h : evV g x s T E a p = none) : evV g x s T E (.seq a b) p = none := by
  simp only [evV, h]
theorem evV_alt_ok {a b : MExp} {p j : Nat} (h : evV g x s T E a p = some (some j)) :
    evV g x s T E (.alt a b) p = some (some j) := by simp only [evV, h]
theorem evV_alt_fail {a b : MExp} {p : Nat} (h : evV g x s T E a p = some none) :
    evV g x s T E (.alt a b) p = evV g x s T E b p := by simp only [evV, h]
theorem evV_alt_none {a b : MExp} {p : Nat} (h : evV g x s T E a p = none) : evV g x s T E (.alt a b) p = none := by
  simp only [evV, h]
theorem evV_not_ok {a : MExp} {p j : Nat} (h : evV g x s T E a p = some (some j)) :
    evV g x s T E (.notP a) p = some none := by simp only [evV, h]
theorem evV_not_fail {a : MExp} {p : Nat} (h : evV g x s T E a p = some none) :
    evV g x s T E (.notP a) p = some (some p) := by simp only [evV, h]
theorem evV_not_none {a : MExp} {p : Nat} (h : evV g x s T E a p = none) : evV g x s T E (.notP a) p = none := by
  simp only [evV, h]
theorem evV_star (a : MExp) (p : Nat) : evV g x s T E (.star a) p = evStar (fun q => evV g x s T E a q) p := by
  simp only [evV]

theorem evPar_nil (p : Nat) : evParArgs g x s T E [] p = some (some []) := by simp only [evParArgs]
theorem evPar_cons_ok {a : MExp} {as : List MExp} {p j : Nat} (h : evV g x s T E a p = some (some j)) :
    evParArgs g x s T E (a :: as) p =
      match evParArgs g x s T E as p with
      | some (some W) => some (some (pre x p j :: W))
      | r => r := by
  simp only [evParArgs, h]
theorem evPar_cons_fail {a : MExp} {as : List MExp} {p : Nat} (h : evV g x s T E a p = some none) :
    evParArgs g x s T E (a :: as) p = some none := by simp only [evParArgs, h]
theorem evPar_cons_none {a : MExp} {as : List MExp} {p : Nat} (h : evV g x s T E a p = none) :
    evParArgs g x s T E (a :: as) p = none := by simp only [evParArgs, h]

theorem evSeq_nil (p : Nat) : evSeqArgs g x s T E [] p = some (some ([], p)) := by simp only [evSeqArgs]
theorem evSeq_cons_ok {a : MExp} {as : List MExp} {p j : Nat} (h : evV g x s T E a p = some (some j)) :
    evSeqArgs g x s T E (a :: as) p =
      match evSeqArgs g x s T E as j with
      | some (some (W, q)) => some (some (pre x p j :: W, q))
      | r => r := by
  simp only [evSeqArgs, h]
theorem evSeq_cons_fail {a : MExp} {as : List MExp} {p : Nat} (h : evV g x s T E a p = some none) :
    evSeqArgs g x s T E (a :: as) p = some none := by simp only [evSeqArgs, h]
theorem evSeq_cons_none {a : MExp} {as : List MExp} {p : Nat} (h : evV g x s T E a p = none) :
    evSeqArgs g x s T E (a :: as) p = none := by simp only [evSeqArgs, h]

theorem evV_call_par {i : Nat} {args : List MExp} {r : MRule} (hr : ruleAtM g.rules i = some r)
    (ha : r.arity = args.length) (hs : s ≠ .callByValueSeq) (p : Nat) :
    evV g x s T E (.call i args) p =
      match evParArgs g x s T E args p with
      | some (some W) => valAt (T i W) p
      | some none => some none
      | none => none := by
  cases s
  · simp only [evV, hr, if_pos ha]
  · simp only [evV, hr, if_pos ha]
  · exact absurd rfl hs

theorem evV_call_seq {i : Nat} {args : List MExp} {r : MRule} (hr : ruleAtM g.rules i = some r)
    (ha : r.arity = args.length) (p : Nat) :
    evV g x .callByValueSeq T E (.call i args) p =
      match evSeqArgs g x .callByValueSeq T E args p with
      | some (some (W, q)) => valAt (T i W) q
      | some none => some none
      | none => none := by
  simp only [evV, hr, if_pos ha]

end UnfoldV

/-! ## Monotonicity in the table -/

def OLe {α : Type} (o o' : Option α) : Prop := o = none ∨ o = o'

theorem OLe.refl {α : Type} (o : Option α) : OLe o o := Or.inr rfl
theorem OLe.eq_of_some {α : Type} {o o' : Option α} {v : α} (h : OLe o o') (ho : o = some v) : o' = some v := by
  rcases h with h | h
  · rw [ho] at h; cases h
  · rw [← h, ho]

def TLeV (T T' : Nat → List (List Char) → Val) : Prop := ∀ i W, VLe (T i W) (T' i W)

theorem TLeV.refl (T : Nat → List (List Char) → Val) : TLeV T T := fun _ _ _ => RLe.refl _
theorem TLeV.trans {T₁ T₂ T₃ : Nat → List (List Char) → Val} (h₁ : TLeV T₁ T₂) (h₂ : TLeV T₂ T₃) : TLeV T₁ T₃ :=
  fun i W p => RLe.trans (h₁ i W p) (h₂ i W p)

mutual
  theorem evV_mono {g : MGrammar} {x : List Char} {s : Strategy} {T T' : Nat → List (List Char) → Val}
      {E : List (List Char)} (hT : TLeV T T') : ∀ (e : MExp) (p : Nat), RLe (evV g x s T E e p) (evV g x s T' E e p)
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .dbg _, _ | .lam _ _, _ | .callParam _ _, _
    | .invoke _ _ _, _ | .param _, _ => by simp only [evV]; exact RLe.refl _
    | .call i args, p => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr]; exact RLe.refl _
      | some r =>
        by_cases ha : r.arity = args.length
        · by_cases hs : s = .callByValueSeq
          · subst hs
            rw [evV_call_seq hr ha, evV_call_seq hr ha]
            rcases evSeqArgs_mono (g := g) (x := x) (s := .callByValueSeq) (E := E) hT args p with h | h
            · rw [h]; exact Or.inl rfl
            · rw [← h]
              split
              · exact hT i _ _
              · exact RLe.refl _
              · exact RLe.refl _
          · rw [evV_call_par hr ha hs, evV_call_par hr ha hs]
            rcases evParArgs_mono (g := g) (x := x) (s := s) (E := E) hT args p with h | h
            · rw [h]; exact Or.inl rfl
            · rw [← h]
              split
              · exact hT i _ _
              · exact RLe.refl _
              · exact RLe.refl _
        · simp only [evV, hr, if_neg ha]; exact RLe.refl _
    | .seq a b, p => by
      rcases evV_mono (g := g) (x := x) (s := s) (E := E) hT a p with h | h
      · rw [evV_seq_none h]; exact Or.inl rfl
      · cases ha : evV g x s T E a p with
        | none => rw [evV_seq_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [evV_seq_fail ha, evV_seq_fail h.symm]; exact RLe.refl _
          | some j => rw [evV_seq_ok ha, evV_seq_ok h.symm]; exact evV_mono hT b j
    | .alt a b, p => by
      rcases evV_mono (g := g) (x := x) (s := s) (E := E) hT a p with h | h
      · rw [evV_alt_none h]; exact Or.inl rfl
      · cases ha : evV g x s T E a p with
        | none => rw [evV_alt_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [evV_alt_fail ha, evV_alt_fail h.symm]; exact evV_mono hT b p
          | some j => rw [evV_alt_ok ha, evV_alt_ok h.symm]; exact RLe.refl _
    | .notP a, p => by
      rcases evV_mono (g := g) (x := x) (s := s) (E := E) hT a p with h | h
      · rw [evV_not_none h]; exact Or.inl rfl
      · cases ha : evV g x s T E a p with
        | none => rw [evV_not_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [evV_not_fail ha, evV_not_fail h.symm]; exact RLe.refl _
          | some j => rw [evV_not_ok ha, evV_not_ok h.symm]; exact RLe.refl _
    | .star a, p => by
      rw [evV_star, evV_star]
      exact evStar_mono p (fun q _ => evV_mono hT a q)

  theorem evParArgs_mono {g : MGrammar} {x : List Char} {s : Strategy} {T T' : Nat → List (List Char) → Val}
      {E : List (List Char)} (hT : TLeV T T') :
      ∀ (as : List MExp) (p : Nat), OLe (evParArgs g x s T E as p) (evParArgs g x s T' E as p)
    | [], p => by rw [evPar_nil, evPar_nil]; exact OLe.refl _
    | a :: as, p => by
      rcases evV_mono (g := g) (x := x) (s := s) (E := E) hT a p with h | h
      · rw [evPar_cons_none h]; exact Or.inl rfl
      · cases ha : evV g x s T E a p with
        | none => rw [evPar_cons_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [evPar_cons_fail ha, evPar_cons_fail h.symm]; exact OLe.refl _
          | some j =>
            rw [evPar_cons_ok ha, evPar_cons_ok h.symm]
            rcases evParArgs_mono hT as p with h' | h'
            · rw [h']; exact Or.inl rfl
            · rw [h']; exact OLe.refl _

  theorem evSeqArgs_mono {g : MGrammar} {x : List Char} {s : Strategy} {T T' : Nat → List (List Char) → Val}
      {E : List (List Char)} (hT : TLeV T T') :
      ∀ (as : List MExp) (p : Nat), OLe (evSeqArgs g x s T E as p) (evSeqArgs g x s T' E as p)
    | [], p => by rw [evSeq_nil, evSeq_nil]; exact OLe.refl _
    | a :: as, p => by
      rcases evV_mono (g := g) (x := x) (s := s) (E := E) hT a p with h | h
      · rw [evSeq_cons_none h]; exact Or.inl rfl
      · cases ha : evV g x s T E a p with
        | none => rw [evSeq_cons_none ha]; exact Or.inl rfl
        | some r =>
          rw [ha] at h
          cases r with
          | none => rw [evSeq_cons_fail ha, evSeq_cons_fail h.symm]; exact OLe.refl _
          | some j =>
            rw [evSeq_cons_ok ha, evSeq_cons_ok h.symm]
            rcases evSeqArgs_mono hT as j with h' | h'
            · rw [h']; exact Or.inl rfl
            · rw [h']; exact OLe.refl _
end

theorem tblV_step (g : MGrammar) (x : List Char) (s : Strategy) : ∀ m, TLeV (tblV g x s m) (tblV g x s (m + 1))
  | 0 => fun _ _ p => by simp only [tblV, valAt_nil]; exact Or.inl rfl
  | m + 1 => by
    intro i W p
    simp only [tblV]
    cases ruleAtM g.rules i with
    | none => exact RLe.refl _
    | some r =>
      simp only
      rw [valAt_rangeMap, valAt_rangeMap]
      split
      · exact evV_mono (tblV_step g x s m) r.body p
      · exact RLe.refl _

theorem tblV_le (g : MGrammar) (x : List Char) (s : Strategy) {m m' : Nat} (h : m ≤ m') :
    TLeV (tblV g x s m) (tblV g x s m') := by
  induction h with
  | refl => exact TLeV.refl _
  | step _ ih => exact TLeV.trans ih (tblV_step g x s _)

theorem evV_lift {g : MGrammar} {x : List Char} {s : Strategy} {m m' : Nat} (h : m ≤ m') {E : List (List Char)}
    {e : MExp} {p : Nat} {v : Option Nat} (hv : evV g x s (tblV g x s m) E e p = some v) :
    evV g x s (tblV g x s m') E e p = some v :=
  (evV_mono (tblV_le g x s h) e p).eq_of_some hv

theorem evPar_lift {g : MGrammar} {x : List Char} {s : Strategy} {m m' : Nat} (h : m ≤ m') {E : List (List Char)}
    {as : List MExp} {p : Nat} {v : Option (List (List Char))}
    (hv : evParArgs g x s (tblV g x s m) E as p = some v) : evParArgs g x s (tblV g x s m') E as p = some v :=
  (evParArgs_mono (tblV_le g x s h) as p).eq_of_some hv

theorem evSeq_lift {g : MGrammar} {x : List Char} {s : Strategy} {m m' : Nat} (h : m ≤ m') {E : List (List Char)}
    {as : List MExp} {p : Nat} {v : Option (List (List Char) × Nat)}
    (hv : evSeqArgs g x s (tblV g x s m) E as p = some v) : evSeqArgs g x s (tblV g x s m') E as p = some v :=
  (evSeqArgs_mono (tblV_le g x s h) as p).eq_of_some hv

/-! ## The substitution lemma (call-by-value: literals) -/

theorem argAt_map_lit : ∀ (W : List (List Char)) (k : Nat), argAt (W.map MExp.lit) k = (W[k]?).map MExp.lit
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: W, k + 1 => by simp only [List.map_cons, argAt, List.getElem?_cons_succ]; exact argAt_map_lit W k

mutual
  theorem evV_subst {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (W : List (List Char)) :
      ∀ (b : MExp), b.FirstOrder → ∀ p, evV g x s T E (MExp.subst (W.map MExp.lit) b) p = evV g x s T W b p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => by simp only [MExp.subst, evV]
    | .param k, _, p => by
      simp only [MExp.subst, argAt_map_lit]
      conv => rhs; simp only [evV]
      cases h : W[k]? with
      | none => simp [MExp.failAlways, evV]
      | some w => simp only [Option.map_some, evV]
    | .call j ms, hb, p => by
      simp only [MExp.subst]
      cases hr : ruleAtM g.rules j with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = ms.length
        · have ha' : r.arity = (MExp.substArgs (W.map MExp.lit) ms).length := by rw [length_substArgs]; exact ha
          by_cases hs : s = .callByValueSeq
          · subst hs
            rw [evV_call_seq hr ha', evV_call_seq hr ha, evSeqArgs_subst W ms hb]
          · rw [evV_call_par hr ha' hs, evV_call_par hr ha hs, evParArgs_subst W ms hb]
        · have ha' : ¬ r.arity = (MExp.substArgs (W.map MExp.lit) ms).length := by rw [length_substArgs]; exact ha
          simp only [evV, hr, if_neg ha, if_neg ha']
    | .seq a c, hb, p => by
      simp only [MExp.subst]
      have ha := evV_subst (g := g) (x := x) (s := s) (T := T) (E := E) W a hb.1 p
      cases h : evV g x s T W a p with
      | none => rw [evV_seq_none (ha.trans h), evV_seq_none h]
      | some r =>
        cases r with
        | none => rw [evV_seq_fail (ha.trans h), evV_seq_fail h]
        | some j => rw [evV_seq_ok (ha.trans h), evV_seq_ok h]; exact evV_subst W c hb.2 j
    | .alt a c, hb, p => by
      simp only [MExp.subst]
      have ha := evV_subst (g := g) (x := x) (s := s) (T := T) (E := E) W a hb.1 p
      cases h : evV g x s T W a p with
      | none => rw [evV_alt_none (ha.trans h), evV_alt_none h]
      | some r =>
        cases r with
        | none => rw [evV_alt_fail (ha.trans h), evV_alt_fail h]; exact evV_subst W c hb.2 p
        | some j => rw [evV_alt_ok (ha.trans h), evV_alt_ok h]
    | .notP a, hb, p => by
      simp only [MExp.subst]
      have ha := evV_subst (g := g) (x := x) (s := s) (T := T) (E := E) W a hb p
      cases h : evV g x s T W a p with
      | none => rw [evV_not_none (ha.trans h), evV_not_none h]
      | some r =>
        cases r with
        | none => rw [evV_not_fail (ha.trans h), evV_not_fail h]
        | some j => rw [evV_not_ok (ha.trans h), evV_not_ok h]
    | .star a, hb, p => by
      simp only [MExp.subst]
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q _ => evV_subst W a hb q)
    | .dbg _, hb, _ | .lam _ _, hb, _ | .callParam _ _, hb, _ | .invoke _ _ _, hb, _ => absurd hb id

  theorem evParArgs_subst {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (W : List (List Char)) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → ∀ p,
        evParArgs g x s T E (MExp.substArgs (W.map MExp.lit) ms) p = evParArgs g x s T W ms p
    | [], _, p => by simp only [MExp.substArgs, evPar_nil]
    | m :: ms, hm, p => by
      simp only [MExp.substArgs]
      have hh := evV_subst (g := g) (x := x) (s := s) (T := T) (E := E) W m hm.1 p
      cases h : evV g x s T W m p with
      | none => rw [evPar_cons_none (hh.trans h), evPar_cons_none h]
      | some r =>
        cases r with
        | none => rw [evPar_cons_fail (hh.trans h), evPar_cons_fail h]
        | some j => rw [evPar_cons_ok (hh.trans h), evPar_cons_ok h, evParArgs_subst W ms hm.2 p]

  theorem evSeqArgs_subst {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (W : List (List Char)) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → ∀ p,
        evSeqArgs g x s T E (MExp.substArgs (W.map MExp.lit) ms) p = evSeqArgs g x s T W ms p
    | [], _, p => by simp only [MExp.substArgs, evSeq_nil]
    | m :: ms, hm, p => by
      simp only [MExp.substArgs]
      have hh := evV_subst (g := g) (x := x) (s := s) (T := T) (E := E) W m hm.1 p
      cases h : evV g x s T W m p with
      | none => rw [evSeq_cons_none (hh.trans h), evSeq_cons_none h]
      | some r =>
        cases r with
        | none => rw [evSeq_cons_fail (hh.trans h), evSeq_cons_fail h]
        | some j => rw [evSeq_cons_ok (hh.trans h), evSeq_cons_ok h, evSeqArgs_subst W ms hm.2 j]
end

/-! ## Derivations give defined results -/

theorem firstOrderArgs_lits : ∀ W : List (List Char), MExp.FirstOrderArgs (W.map MExp.lit)
  | [] => trivial
  | _ :: W => ⟨trivial, firstOrderArgs_lits W⟩

theorem valAt_tblV_succ {g : MGrammar} {x : List Char} {s : Strategy} {m i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) (W : List (List Char)) {p : Nat} (hp : p ≤ x.length) :
    valAt (tblV g x s (m + 1) i W) p = evV g x s (tblV g x s m) W r.body p := by
  simp only [tblV, hr, valAt_rangeMap, if_pos hp]

theorem pre_eq {x input p rest : List Char} (hx : ∃ pre, x = pre ++ input) (hp : input = p ++ rest) :
    pre x input.length rest.length = p := by
  obtain ⟨pre0, h0⟩ := hx
  unfold pre
  rw [sfx_suffix h0, hp]
  simp

theorem evPar_append_fail {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} {bad : MExp} {post : List MExp} {p : Nat} (hbad : evV g x s T E bad p = some none) :
    ∀ (pre' : List MExp) (W : List (List Char)), evParArgs g x s T E pre' p = some (some W) →
      evParArgs g x s T E (pre' ++ bad :: post) p = some none
  | [], _, _ => by simp only [List.nil_append]; exact evPar_cons_fail hbad
  | a :: as, W, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evPar_cons_none ha] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [evPar_cons_fail ha] at h; cases h
      | some j =>
        rw [evPar_cons_ok ha] at h
        cases hr : evParArgs g x s T E as p with
        | none => rw [hr] at h; cases h
        | some v =>
          cases v with
          | none => rw [hr] at h; cases h
          | some W' =>
            simp only [List.cons_append]
            rw [evPar_cons_ok ha, evPar_append_fail hbad as W' hr]

theorem evSeq_append_fail {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} {bad : MExp} {post : List MExp} :
    ∀ (pre' : List MExp) (p : Nat) (W : List (List Char)) (q : Nat), evSeqArgs g x s T E pre' p = some (some (W, q)) →
      evV g x s T E bad q = some none → evSeqArgs g x s T E (pre' ++ bad :: post) p = some none
  | [], p, _, q, h, hbad => by
    rw [evSeq_nil] at h; cases h
    simp only [List.nil_append]; exact evSeq_cons_fail hbad
  | a :: as, p, W, q, h, hbad => by
    cases ha : evV g x s T E a p with
    | none => rw [evSeq_cons_none ha] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [evSeq_cons_fail ha] at h; cases h
      | some j =>
        rw [evSeq_cons_ok ha] at h
        cases hr : evSeqArgs g x s T E as j with
        | none => rw [hr] at h; cases h
        | some v =>
          cases v with
          | none => rw [hr] at h; cases h
          | some Wq =>
            obtain ⟨W', q'⟩ := Wq
            rw [hr] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            simp only [List.cons_append]
            rw [evSeq_cons_ok ha, evSeq_append_fail as j W' q' hr hbad]

theorem foArgs_split {bad : MExp} {post : List MExp} :
    ∀ {pre' : List MExp}, MExp.FirstOrderArgs (pre' ++ bad :: post) → MExp.FirstOrderArgs pre' ∧ bad.FirstOrder
  | [], h => ⟨trivial, h.1⟩
  | _ :: _, h => ⟨⟨h.1, (foArgs_split h.2).1⟩, (foArgs_split h.2).2⟩

/-- **Derivation ⇒ result** (call-by-value). -/
theorem derivesV_ev {g : MGrammar} {x : List Char} {s : Strategy} (hg : g.FirstOrder) (hs : s ≠ .callByName)
    {e : MExp} {y : List Char} {o : MOutcome} (h : MDerives g s e y o) :
    e.FirstOrder → (∃ pre, x = pre ++ y) → ∃ m, evV g x s (tblV g x s m) [] e y.length = obsR o := by
  induction h using MDerives.rec
    (motive_2 := fun input args vals _ => MExp.FirstOrderArgs args → (∃ pre, x = pre ++ input) →
      ∃ m W, evParArgs g x s (tblV g x s m) [] args input.length = some (some W) ∧ vals = W.map MExp.lit)
    (motive_3 := fun input args vals final _ => MExp.FirstOrderArgs args → (∃ pre, x = pre ++ input) →
      ∃ m W, evSeqArgs g x s (tblV g x s m) [] args input.length = some (some (W, final.length)) ∧
        vals = W.map MExp.lit ∧ ∃ pre, x = pre ++ final)
  case eps input => intro _ _; exact ⟨0, rfl⟩
  case anyOk c rest =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; rfl
  case anyFail =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; rfl
  case chrOk c d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case chrFail c d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case chrEmpty c =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; rfl
  case rangeOk lo hi d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case rangeFail lo hi d rest hb =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; simp [hb, obsR]
  case rangeEmpty lo hi =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre]; rfl
  case litOk str input rest hl =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre, hl]; rfl
  case litFail str input hl =>
    intro _ ⟨pre, hpre⟩; refine ⟨0, ?_⟩; simp only [evV]; rw [sfx_suffix hpre, hl]; rfl
  case paramFail k input => intro _ _; exact ⟨0, rfl⟩
  case callNameOk hs' _ _ _ _ => exact absurd hs' hs
  case callNameFail hs' _ _ _ _ => exact absurd hs' hs
  case callParOk i args r input rest vals t hs' hr ha _ _ ih_args ih_d =>
    intro hfo hsuf
    subst hs'
    obtain ⟨m₁, W, hW, rfl⟩ := ih_args hfo hsuf
    obtain ⟨m₂, hm₂⟩ := ih_d (firstOrder_subst (firstOrderArgs_lits W) r.body (hg r (ruleAtM_mem hr))) hsuf
    rw [evV_subst W r.body (hg r (ruleAtM_mem hr))] at hm₂
    refine ⟨m₁ + m₂ + 1, ?_⟩
    rw [evV_call_par hr ha (by decide), evPar_lift (by omega) hW]
    simp only
    rw [valAt_tblV_succ hr W (suffix_len hsuf)]
    exact evV_lift (by omega) hm₂
  case callParFail i args r input vals hs' hr ha _ _ ih_args ih_d =>
    intro hfo hsuf
    subst hs'
    obtain ⟨m₁, W, hW, rfl⟩ := ih_args hfo hsuf
    obtain ⟨m₂, hm₂⟩ := ih_d (firstOrder_subst (firstOrderArgs_lits W) r.body (hg r (ruleAtM_mem hr))) hsuf
    rw [evV_subst W r.body (hg r (ruleAtM_mem hr))] at hm₂
    refine ⟨m₁ + m₂ + 1, ?_⟩
    rw [evV_call_par hr ha (by decide), evPar_lift (by omega) hW]
    simp only
    rw [valAt_tblV_succ hr W (suffix_len hsuf)]
    exact evV_lift (by omega) hm₂
  case callParArgFail i pre' bad post r input preVals hs' hr ha _ _ ih_pre ih_bad =>
    intro hfo hsuf
    subst hs'
    have hsplit : MExp.FirstOrderArgs pre' ∧ bad.FirstOrder := foArgs_split hfo
    obtain ⟨m₁, W, hW, _⟩ := ih_pre hsplit.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih_bad hsplit.2 hsuf
    refine ⟨m₁ + m₂, ?_⟩
    rw [evV_call_par hr ha (by decide),
      evPar_append_fail (evV_lift (by omega) hm₂) pre' W (evPar_lift (by omega) hW)]
    rfl
  case callSeqOk i args r input mid rest vals t hs' hr ha _ _ ih_args ih_d =>
    intro hfo hsuf
    subst hs'
    obtain ⟨m₁, W, hW, rfl, hmid⟩ := ih_args hfo hsuf
    obtain ⟨m₂, hm₂⟩ := ih_d (firstOrder_subst (firstOrderArgs_lits W) r.body (hg r (ruleAtM_mem hr))) hmid
    rw [evV_subst W r.body (hg r (ruleAtM_mem hr))] at hm₂
    refine ⟨m₁ + m₂ + 1, ?_⟩
    rw [evV_call_seq hr ha, evSeq_lift (by omega) hW]
    simp only
    rw [valAt_tblV_succ hr W (suffix_len hmid)]
    exact evV_lift (by omega) hm₂
  case callSeqFail i args r input mid vals hs' hr ha _ _ ih_args ih_d =>
    intro hfo hsuf
    subst hs'
    obtain ⟨m₁, W, hW, rfl, hmid⟩ := ih_args hfo hsuf
    obtain ⟨m₂, hm₂⟩ := ih_d (firstOrder_subst (firstOrderArgs_lits W) r.body (hg r (ruleAtM_mem hr))) hmid
    rw [evV_subst W r.body (hg r (ruleAtM_mem hr))] at hm₂
    refine ⟨m₁ + m₂ + 1, ?_⟩
    rw [evV_call_seq hr ha, evSeq_lift (by omega) hW]
    simp only
    rw [valAt_tblV_succ hr W (suffix_len hmid)]
    exact evV_lift (by omega) hm₂
  case callSeqArgFail i pre' bad post r input mid preVals hs' hr ha _ _ ih_pre ih_bad =>
    intro hfo hsuf
    subst hs'
    have hsplit : MExp.FirstOrderArgs pre' ∧ bad.FirstOrder := foArgs_split hfo
    obtain ⟨m₁, W, hW, _, hmid⟩ := ih_pre hsplit.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih_bad hsplit.2 hmid
    refine ⟨m₁ + m₂, ?_⟩
    rw [evV_call_seq hr ha,
      evSeq_append_fail pre' _ W _ (evSeq_lift (by omega) hW) (evV_lift (by omega) hm₂)]
    rfl
  case callMissing i args input hr => intro _ _; exact ⟨0, by simp [evV, hr, obsR]⟩
  case callArity i args r input hr ha => intro _ _; exact ⟨0, by simp [evV, hr, ha, obsR]⟩
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 (suffix_trans hsuf (mderives_suffix h₁ _ _ rfl))
    refine ⟨m₁ + m₂, ?_⟩
    rw [evV_seq_ok (evV_lift (by omega) hm₁)]
    exact evV_lift (by omega) hm₂
  case seqFail₁ e₁ e₂ input _ ih₁ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    exact ⟨m₁, evV_seq_fail hm₁⟩
  case seqFail₂ e₁ e₂ input rest₁ t₁ h₁ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 (suffix_trans hsuf (mderives_suffix h₁ _ _ rfl))
    refine ⟨m₁ + m₂, ?_⟩
    rw [evV_seq_ok (evV_lift (by omega) hm₁)]
    exact evV_lift (by omega) hm₂
  case altL e₁ e₂ input rest t _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo.1 hsuf
    exact ⟨m, evV_alt_ok hm⟩
  case altR e₁ e₂ input rest t _ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 hsuf
    refine ⟨m₁ + m₂, ?_⟩
    rw [evV_alt_fail (evV_lift (by omega) hm₁)]
    exact evV_lift (by omega) hm₂
  case altFail e₁ e₂ input _ _ ih₁ ih₂ =>
    intro hfo hsuf
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo.2 hsuf
    refine ⟨m₁ + m₂, ?_⟩
    rw [evV_alt_fail (evV_lift (by omega) hm₁)]
    exact evV_lift (by omega) hm₂
  case starNil e input _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo hsuf
    exact ⟨m, by rw [evV_star]; exact evStar_fail hm⟩
  case starCons e input rest rest' t ts h₁ _ ih₁ ih₂ =>
    intro hfo hsuf
    have hsuf' := suffix_trans hsuf (mderives_suffix h₁ _ _ rfl)
    obtain ⟨m₁, hm₁⟩ := ih₁ hfo hsuf
    obtain ⟨m₂, hm₂⟩ := ih₂ hfo hsuf'
    have h₁' := evV_lift (m' := m₁ + m₂) (by omega) hm₁
    have h₂' := evV_lift (m' := m₁ + m₂) (by omega) hm₂
    have hle : rest.length ≤ input.length := by
      obtain ⟨q, hq⟩ := mderives_suffix h₁ _ _ rfl; rw [hq]; simp
    by_cases hlt : rest.length < input.length
    · refine ⟨m₁ + m₂, ?_⟩
      rw [evV_star, evStar_ok h₁' hlt, ← evV_star]
      exact h₂'
    · have heq : rest.length = input.length := by omega
      rw [evV_star, heq, evStar_stuck (heq ▸ h₁') (by omega)] at h₂'
      cases h₂'
  case notOk e input rest t _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo hsuf
    exact ⟨m, evV_not_ok hm⟩
  case notFail e input _ ih =>
    intro hfo hsuf
    obtain ⟨m, hm⟩ := ih hfo hsuf
    exact ⟨m, evV_not_fail hm⟩
  all_goals first
    | (intro hfo; exact absurd hfo id)
    | (rename_i input _ hsuf; exact ⟨0, [], evPar_nil _, rfl⟩)
    | (rename_i input _ hsuf; exact ⟨0, [], evSeq_nil _, rfl, hsuf⟩)
    | (rename_i a as input p rest t vs h₁ hp _ ih₁ ih₂ hfo hsuf
       obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
       obtain ⟨m₂, W, hW, rfl⟩ := ih₂ hfo.2 hsuf
       refine ⟨m₁ + m₂, pre x input.length rest.length :: W, ?_, ?_⟩
       · rw [evPar_cons_ok (evV_lift (by omega) hm₁), evPar_lift (by omega) hW]
       · rw [pre_eq hsuf hp]; rfl)
    | (rename_i a as input p rest final t vs h₁ hp _ ih₁ ih₂ hfo
       intro hsuf
       obtain ⟨m₁, hm₁⟩ := ih₁ hfo.1 hsuf
       have hsufr := suffix_trans hsuf ⟨p, hp⟩
       obtain ⟨m₂, W, hW, rfl, hfin⟩ := ih₂ hfo.2 hsufr
       refine ⟨m₁ + m₂, pre x input.length rest.length :: W, ?_, ?_, hfin⟩
       · rw [evSeq_cons_ok (evV_lift (by omega) hm₁), evSeq_lift (by omega) hW]
       · rw [pre_eq hsuf hp]; rfl)

/-! ## Defined results are backed by derivations -/

theorem rest_eq_sfx' {g : MGrammar} {x : List Char} {s : Strategy} {a : MExp} {p : Nat} {t : MTree}
    {rest : List Char} (h : MDerives g s a (sfx x p) (.ok t rest)) : sfx x rest.length = rest := by
  obtain ⟨pre0, h0⟩ := suffix_trans (sfx_is_suffix x p) (mderives_suffix h _ _ rfl)
  exact sfx_suffix h0

/-- Every defined entry is backed by a derivation of the body with the argument literals substituted. -/
def SoundTV (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) : Prop :=
  ∀ i r W, ruleAtM g.rules i = some r → r.arity = W.length → ∀ q, q ≤ x.length → ∀ res, valAt (T i W) q = some res →
    ∃ o, MDerives g s (MExp.subst (W.map MExp.lit) r.body) (sfx x q) o ∧ obsR o = some res

theorem pre_split {x y : List Char} {p : Nat} (hp : p ≤ x.length) (h : ∃ q, sfx x p = q ++ y) :
    sfx x p = pre x p y.length ++ y := by
  obtain ⟨q, hq⟩ := h
  have hl : (sfx x p).length = p := length_sfx x hp
  unfold pre
  rw [hq] at hl ⊢
  simp only [List.length_append] at hl
  rw [show p - y.length = q.length by omega]
  simp

theorem evPar_length {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} {p : Nat} : ∀ (as : List MExp) (W : List (List Char)),
      evParArgs g x s T E as p = some (some W) → W.length = as.length
  | [], W, h => by rw [evPar_nil] at h; cases h; rfl
  | a :: as, W, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evPar_cons_none ha] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [evPar_cons_fail ha] at h; cases h
      | some j =>
        rw [evPar_cons_ok ha] at h
        cases hr : evParArgs g x s T E as p with
        | none => rw [hr] at h; cases h
        | some v =>
          cases v with
          | none => rw [hr] at h; cases h
          | some W' => rw [hr] at h; cases h; simp [evPar_length as W' hr]

theorem evSeq_length {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} : ∀ (as : List MExp) (p : Nat) (W : List (List Char)) (q : Nat),
      evSeqArgs g x s T E as p = some (some (W, q)) → W.length = as.length
  | [], p, W, q, h => by rw [evSeq_nil] at h; cases h; rfl
  | a :: as, p, W, q, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evSeq_cons_none ha] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [evSeq_cons_fail ha] at h; cases h
      | some j =>
        rw [evSeq_cons_ok ha] at h
        cases hr : evSeqArgs g x s T E as j with
        | none => rw [hr] at h; cases h
        | some v =>
          cases v with
          | none => rw [hr] at h; cases h
          | some Wq =>
            obtain ⟨W', q'⟩ := Wq
            rw [hr] at h; cases h; simp only [List.length_cons]; rw [evSeq_length as j W' _ hr]

theorem strategy_par_of {s : Strategy} (h₁ : s ≠ .callByName) (h₂ : s ≠ .callByValueSeq) : s = .callByValuePar := by
  cases s <;> simp_all

mutual
  theorem evV_sound {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      (hs : s ≠ .callByName) (hT : SoundTV g x s T) :
      ∀ (e : MExp), e.FirstOrder → ∀ p, p ≤ x.length → ∀ res, evV g x s T [] e p = some res →
        ∃ o, MDerives g s e (sfx x p) o ∧ obsR o = some res
    | .eps, _, p, hp, r, hev => by
      simp only [evV, Option.some.injEq] at hev; subst hev
      exact ⟨_, .eps _, by simp [obsR, length_sfx x hp]⟩
    | .any, _, p, _, r, hev => by
      simp only [evV] at hev
      cases hs' : sfx x p with
      | nil => rw [hs'] at hev; cases hev; exact ⟨_, .anyFail, rfl⟩
      | cons d rr => rw [hs'] at hev; cases hev; exact ⟨_, .anyOk d rr, rfl⟩
    | .chr c, _, p, _, r, hev => by
      simp only [evV] at hev
      cases hs' : sfx x p with
      | nil => rw [hs'] at hev; cases hev; exact ⟨_, .chrEmpty c, rfl⟩
      | cons d rr =>
        rw [hs'] at hev
        cases hb : beqChar c d
        · simp [hb] at hev; subst hev; exact ⟨_, .chrFail c d rr hb, rfl⟩
        · simp [hb] at hev; subst hev; exact ⟨_, .chrOk c d rr hb, rfl⟩
    | .range lo hi, _, p, _, r, hev => by
      simp only [evV] at hev
      cases hs' : sfx x p with
      | nil => rw [hs'] at hev; cases hev; exact ⟨_, .rangeEmpty lo hi, rfl⟩
      | cons d rr =>
        rw [hs'] at hev
        cases hb : (leChar lo d && leChar d hi)
        · simp [hb] at hev; subst hev; exact ⟨_, .rangeFail lo hi d rr hb, rfl⟩
        · simp [hb] at hev; subst hev; exact ⟨_, .rangeOk lo hi d rr hb, rfl⟩
    | .lit w, _, p, _, r, hev => by
      simp only [evV] at hev
      cases hl : stripPrefix? w (sfx x p) with
      | none => rw [hl] at hev; cases hev; exact ⟨_, .litFail _ _ hl, rfl⟩
      | some rr => rw [hl] at hev; cases hev; exact ⟨_, .litOk _ _ rr hl, rfl⟩
    | .param k, _, p, _, r, hev => by
      simp only [evV, List.getElem?_nil] at hev; cases hev
      exact ⟨_, .paramFail k _, rfl⟩
    | .call i args, hb, p, hp, res, hev => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr] at hev; cases hev; exact ⟨_, .callMissing _ _ _ hr, rfl⟩
      | some r =>
        by_cases ha : r.arity = args.length
        · by_cases hsq : s = .callByValueSeq
          · subst hsq
            rw [evV_call_seq hr ha] at hev
            have ⟨hok, hfail⟩ := evSeqArgs_sound hs hT args hb p hp
            cases hargs : evSeqArgs g x .callByValueSeq T [] args p with
            | none => rw [hargs] at hev; cases hev
            | some v =>
              cases v with
              | none =>
                rw [hargs] at hev; cases hev
                obtain ⟨pre', bad, post, preVals, q', _, rfl, hpre, hbad⟩ := hfail hargs
                exact ⟨_, .callSeqArgFail _ pre' bad post r _ _ preVals rfl hr ha hpre hbad, rfl⟩
              | some Wq =>
                obtain ⟨W, q⟩ := Wq
                rw [hargs] at hev
                obtain ⟨hq, hd⟩ := hok W q hargs
                obtain ⟨o, d, ho⟩ := hT i r W hr (by rw [evSeq_length args p W q hargs]; exact ha) q hq res hev
                cases o with
                | fail => exact ⟨_, .callSeqFail _ _ r _ _ _ rfl hr ha hd d, ho⟩
                | ok t rest => exact ⟨_, .callSeqOk _ _ r _ _ rest _ t rfl hr ha hd d, ho⟩
          · rw [evV_call_par hr ha hsq] at hev
            have hpar := strategy_par_of hs hsq
            have ⟨hok, hfail⟩ := evParArgs_sound hs hT args hb p hp
            cases hargs : evParArgs g x s T [] args p with
            | none => rw [hargs] at hev; cases hev
            | some v =>
              cases v with
              | none =>
                rw [hargs] at hev; cases hev
                obtain ⟨pre', bad, post, preVals, rfl, hpre, hbad⟩ := hfail hargs
                exact ⟨_, .callParArgFail _ pre' bad post r _ preVals hpar hr ha hpre hbad, rfl⟩
              | some W =>
                rw [hargs] at hev
                have hd := hok W hargs
                obtain ⟨o, d, ho⟩ := hT i r W hr (by rw [evPar_length args W hargs]; exact ha) p hp res hev
                cases o with
                | fail => exact ⟨_, .callParFail _ _ r _ _ hpar hr ha hd d, ho⟩
                | ok t rest => exact ⟨_, .callParOk _ _ r _ rest _ t hpar hr ha hd d, ho⟩
        · simp only [evV, hr, if_neg ha] at hev; cases hev
          exact ⟨_, .callArity _ _ r _ hr ha, rfl⟩
    | .seq a c, hb, p, hp, r, hev => by
      cases ha : evV g x s T [] a p with
      | none => rw [evV_seq_none ha] at hev; cases hev
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := evV_sound hs hT a hb.1 p hp ra ha
        cases ra with
        | none =>
          rw [evV_seq_fail ha] at hev; cases hev
          rw [obsR_fail hoa] at da
          exact ⟨_, .seqFail₁ _ _ _ da, rfl⟩
        | some j =>
          rw [evV_seq_ok ha] at hev
          obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
          have hj : j ≤ x.length := by
            rw [← hlen, ← rest_eq_sfx' da]; exact length_sfx_le x _
          obtain ⟨oc, dc, hoc⟩ := evV_sound hs hT c hb.2 j hj r hev
          rw [← hlen, rest_eq_sfx' da] at dc
          cases oc with
          | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ da dc, hoc⟩
          | ok t' rest' => exact ⟨_, .seqOk _ _ _ _ _ _ _ da dc, hoc⟩
    | .alt a c, hb, p, hp, r, hev => by
      cases ha : evV g x s T [] a p with
      | none => rw [evV_alt_none ha] at hev; cases hev
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := evV_sound hs hT a hb.1 p hp ra ha
        cases ra with
        | none =>
          rw [evV_alt_fail ha] at hev
          rw [obsR_fail hoa] at da
          obtain ⟨oc, dc, hoc⟩ := evV_sound hs hT c hb.2 p hp r hev
          cases oc with
          | fail => exact ⟨_, .altFail _ _ _ da dc, hoc⟩
          | ok t' rest' => exact ⟨_, .altR _ _ _ _ _ da dc, hoc⟩
        | some j =>
          rw [evV_alt_ok ha] at hev; cases hev
          obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
          exact ⟨_, .altL _ _ _ _ _ da, by simp [obsR, hlen]⟩
    | .notP a, hb, p, hp, r, hev => by
      cases ha : evV g x s T [] a p with
      | none => rw [evV_not_none ha] at hev; cases hev
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := evV_sound hs hT a hb p hp ra ha
        cases ra with
        | none =>
          rw [evV_not_fail ha] at hev; cases hev
          rw [obsR_fail hoa] at da
          exact ⟨_, .notFail _ _ da, by simp [obsR, length_sfx x hp]⟩
        | some j =>
          rw [evV_not_ok ha] at hev; cases hev
          obtain ⟨t, rest, rfl, _⟩ := obsR_ok hoa
          exact ⟨_, .notOk _ _ _ _ da, rfl⟩
    | .star a, hb, p, hp, r, hev => by
      rw [evV_star] at hev
      induction p using Nat.strongRecOn generalizing r with
      | ind p ih =>
        cases hf : evV g x s T [] a p with
        | none => rw [evStar_none hf] at hev; cases hev
        | some ra =>
          obtain ⟨oa, da, hoa⟩ := evV_sound hs hT a hb p hp ra hf
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
              rw [← hlen, rest_eq_sfx' da] at ds
              cases os with
              | fail => cases r with
                | none => exact absurd hev (evStar_ne_fail j)
                | some _ => cases hos
              | ok ts rest' => exact ⟨_, .starCons _ _ _ _ _ _ da ds, hos⟩
            · rw [evStar_stuck hf hj] at hev; cases hev
    | .dbg _, hb, _, _, _, _ | .lam _ _, hb, _, _, _, _ | .callParam _ _, hb, _, _, _, _
    | .invoke _ _ _, hb, _, _, _, _ => absurd hb id

  theorem evParArgs_sound {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      (hs : s ≠ .callByName) (hT : SoundTV g x s T) :
      ∀ (as : List MExp), MExp.FirstOrderArgs as → ∀ p, p ≤ x.length →
        (∀ W, evParArgs g x s T [] as p = some (some W) → DerivesArgsPar g s (sfx x p) as (W.map MExp.lit)) ∧
        (evParArgs g x s T [] as p = some none → ∃ pre' bad post preVals, as = pre' ++ bad :: post ∧
          DerivesArgsPar g s (sfx x p) pre' preVals ∧ MDerives g s bad (sfx x p) .fail)
    | [], _, p, _ => by
      refine ⟨fun W h => ?_, fun h => ?_⟩
      · rw [evPar_nil] at h; cases h; exact .nil _
      · rw [evPar_nil] at h; cases h
    | a :: as, hb, p, hp => by
      have ih := evParArgs_sound hs hT as hb.2 p hp
      cases ha : evV g x s T [] a p with
      | none =>
        exact ⟨fun W h => (by rw [evPar_cons_none ha] at h; cases h),
          fun h => (by rw [evPar_cons_none ha] at h; cases h)⟩
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := evV_sound hs hT a hb.1 p hp ra ha
        cases ra with
        | none =>
          refine ⟨fun W h => (by rw [evPar_cons_fail ha] at h; cases h), fun _ => ?_⟩
          rw [obsR_fail hoa] at da
          exact ⟨[], a, as, [], rfl, .nil _, da⟩
        | some j =>
          obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
          have hj : j ≤ x.length := by
            rw [← hlen]; exact suffix_len (suffix_trans (sfx_is_suffix x p) (mderives_suffix da _ _ rfl))
          have hrest : sfx x j = rest := by rw [← hlen]; exact rest_eq_sfx' da
          rw [← hrest] at da
          have hsplit : sfx x p = pre x p j ++ sfx x j := by
            have := pre_split hp (mderives_suffix da _ _ rfl); rwa [length_sfx x hj] at this
          refine ⟨fun W h => ?_, fun h => ?_⟩
          · rw [evPar_cons_ok ha] at h
            cases hr : evParArgs g x s T [] as p with
            | none => rw [hr] at h; cases h
            | some v =>
              cases v with
              | none => rw [hr] at h; cases h
              | some W' =>
                rw [hr] at h; cases h
                exact .cons a as _ (pre x p j) (sfx x j) t _ da hsplit (ih.1 W' hr)
          · rw [evPar_cons_ok ha] at h
            cases hr : evParArgs g x s T [] as p with
            | none => rw [hr] at h; cases h
            | some v =>
              cases v with
              | some _ => rw [hr] at h; cases h
              | none =>
                obtain ⟨pre', bad, post, preVals, hsp, hpre, hbad⟩ := ih.2 hr
                refine ⟨a :: pre', bad, post, MExp.lit (pre x p j) :: preVals, by rw [hsp]; rfl, ?_, hbad⟩
                exact .cons a pre' _ (pre x p j) (sfx x j) t _ da hsplit hpre

  theorem evSeqArgs_sound {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      (hs : s ≠ .callByName) (hT : SoundTV g x s T) :
      ∀ (as : List MExp), MExp.FirstOrderArgs as → ∀ p, p ≤ x.length →
        (∀ W q, evSeqArgs g x s T [] as p = some (some (W, q)) →
          q ≤ x.length ∧ DerivesArgsSeq g s (sfx x p) as (W.map MExp.lit) (sfx x q)) ∧
        (evSeqArgs g x s T [] as p = some none → ∃ pre' bad post preVals q', q' ≤ x.length ∧
          as = pre' ++ bad :: post ∧ DerivesArgsSeq g s (sfx x p) pre' preVals (sfx x q') ∧
          MDerives g s bad (sfx x q') .fail)
    | [], _, p, hp => by
      refine ⟨fun W q h => ?_, fun h => ?_⟩
      · rw [evSeq_nil] at h; cases h; exact ⟨hp, .nil _⟩
      · rw [evSeq_nil] at h; cases h
    | a :: as, hb, p, hp => by
      cases ha : evV g x s T [] a p with
      | none =>
        exact ⟨fun W q h => (by rw [evSeq_cons_none ha] at h; cases h),
          fun h => (by rw [evSeq_cons_none ha] at h; cases h)⟩
      | some ra =>
        obtain ⟨oa, da, hoa⟩ := evV_sound hs hT a hb.1 p hp ra ha
        cases ra with
        | none =>
          refine ⟨fun W q h => (by rw [evSeq_cons_fail ha] at h; cases h), fun _ => ?_⟩
          rw [obsR_fail hoa] at da
          exact ⟨[], a, as, [], p, hp, rfl, .nil _, da⟩
        | some j =>
          obtain ⟨t, rest, rfl, hlen⟩ := obsR_ok hoa
          have hj : j ≤ x.length := by
            rw [← hlen]; exact suffix_len (suffix_trans (sfx_is_suffix x p) (mderives_suffix da _ _ rfl))
          have hrest : sfx x j = rest := by rw [← hlen]; exact rest_eq_sfx' da
          rw [← hrest] at da
          have hsplit : sfx x p = pre x p j ++ sfx x j := by
            have := pre_split hp (mderives_suffix da _ _ rfl); rwa [length_sfx x hj] at this
          have ih := evSeqArgs_sound hs hT as hb.2 j hj
          refine ⟨fun W q h => ?_, fun h => ?_⟩
          · rw [evSeq_cons_ok ha] at h
            cases hr : evSeqArgs g x s T [] as j with
            | none => rw [hr] at h; cases h
            | some v =>
              cases v with
              | none => rw [hr] at h; cases h
              | some Wq =>
                obtain ⟨W', q'⟩ := Wq
                rw [hr] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hq, hd⟩ := ih.1 W' q' hr
                exact ⟨hq, .cons a as _ (pre x p j) (sfx x j) (sfx x q') t _ da hsplit hd⟩
          · rw [evSeq_cons_ok ha] at h
            cases hr : evSeqArgs g x s T [] as j with
            | none => rw [hr] at h; cases h
            | some v =>
              cases v with
              | some _ => rw [hr] at h; cases h
              | none =>
                obtain ⟨pre', bad, post, preVals, q', hq', hsp, hpre, hbad⟩ := ih.2 hr
                refine ⟨a :: pre', bad, post, MExp.lit (pre x p j) :: preVals, q', hq', by rw [hsp]; rfl, ?_, hbad⟩
                exact .cons a pre' _ (pre x p j) (sfx x j) (sfx x q') t _ da hsplit hpre
end

theorem tblV_sound {g : MGrammar} {x : List Char} {s : Strategy} (hg : g.FirstOrder) (hs : s ≠ .callByName) :
    ∀ m, SoundTV g x s (tblV g x s m)
  | 0 => fun _ _ _ _ _ _ _ res hv => by simp [tblV, valAt_nil] at hv
  | m + 1 => by
    intro i r W hr ha q hq res hv
    rw [valAt_tblV_succ hr W hq, ← evV_subst (E := []) W r.body (hg r (ruleAtM_mem hr))] at hv
    exact evV_sound hs (tblV_sound hg hs m) _ (firstOrder_subst (firstOrderArgs_lits W) r.body (hg r (ruleAtM_mem hr)))
      q hq res hv

/-- **Result ⇒ derivation** (call-by-value). -/
theorem evV_derives {g : MGrammar} {x : List Char} {s : Strategy} (hg : g.FirstOrder) (hs : s ≠ .callByName)
    {e : MExp} (he : e.FirstOrder) (m : Nat) {p : Nat} (hp : p ≤ x.length) {r : Option Nat}
    (hev : evV g x s (tblV g x s m) [] e p = some r) :
    ∃ o, MDerives g s e (sfx x p) o ∧ obsR o = some r :=
  evV_sound hs (tblV_sound hg hs m) e he p hp r hev

/-! ## The range invariant -/

def OkTV (n : Nat) (T : Nat → List (List Char) → Val) : Prop := ∀ i W, OkV n (T i W)

theorem evV_ok {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} (hT : OkTV x.length T) :
    ∀ (e : MExp) (p : Nat), p ≤ x.length → OkR x.length (evV g x s T E e p)
  | .eps, p, hp | .dbg _, p, hp | .lam _ _, p, hp => by simp only [evV]; exact okR_ok hp
  | .callParam _ _, _, _ => by simp only [evV]; exact okR_fail _
  | .invoke _ _ _, _, _ => by simp only [evV]; exact okR_none _
  | .any, p, _ => by
    simp only [evV]
    have := length_sfx_le x p
    split
    · rename_i r h; rw [h] at this; exact okR_ok (by simp at this; omega)
    · exact okR_fail _
  | .chr c, p, _ => by
    simp only [evV]
    have := length_sfx_le x p
    split
    · rename_i d r h
      rw [h] at this
      split
      · exact okR_ok (by simp at this; omega)
      · exact okR_fail _
    · exact okR_fail _
  | .range lo hi, p, _ => by
    simp only [evV]
    have := length_sfx_le x p
    split
    · rename_i d r h
      rw [h] at this
      split
      · exact okR_ok (by simp at this; omega)
      · exact okR_fail _
    · exact okR_fail _
  | .lit w, p, _ => by
    simp only [evV]
    split
    · rename_i r h; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ h) (length_sfx_le x p))
    · exact okR_fail _
  | .param k, p, _ => by
    simp only [evV]
    split
    · split
      · rename_i r h; exact okR_ok (Nat.le_trans (stripPrefix_length _ _ _ h) (length_sfx_le x p))
      · exact okR_fail _
    · exact okR_fail _
  | .call i args, p, _ => by
    simp only [evV]
    split
    · split
      · split
        · split
          · exact hT i _ _
          · exact okR_fail _
          · exact okR_none _
        · split
          · exact hT i _ _
          · exact okR_fail _
          · exact okR_none _
      · exact okR_fail _
    · exact okR_fail _
  | .seq a b, p, hp => by
    have ha := evV_ok (g := g) (s := s) (E := E) hT a p hp
    cases h : evV g x s T E a p with
    | none => rw [evV_seq_none h]; exact okR_none _
    | some r =>
      cases r with
      | none => rw [evV_seq_fail h]; exact okR_fail _
      | some j => rw [evV_seq_ok h]; exact evV_ok hT b j (ha j h)
  | .alt a b, p, hp => by
    have ha := evV_ok (g := g) (s := s) (E := E) hT a p hp
    cases h : evV g x s T E a p with
    | none => rw [evV_alt_none h]; exact okR_none _
    | some r =>
      cases r with
      | none => rw [evV_alt_fail h]; exact evV_ok hT b p hp
      | some j => rw [evV_alt_ok h]; exact okR_ok (ha j h)
  | .notP a, p, hp => by
    cases h : evV g x s T E a p with
    | none => rw [evV_not_none h]; exact okR_none _
    | some r =>
      cases r with
      | none => rw [evV_not_fail h]; exact okR_ok hp
      | some j => rw [evV_not_ok h]; exact okR_fail _
  | .star a, p, hp => by
    rw [evV_star]
    intro j h
    have := evStar_le p j h; omega

theorem tblV_ok (g : MGrammar) (x : List Char) (s : Strategy) : ∀ m, OkTV x.length (tblV g x s m)
  | 0 => fun _ _ p => by simp only [tblV, valAt_nil]; exact okR_none _
  | m + 1 => by
    intro i W
    simp only [tblV]
    split
    · exact okV_rangeMap (fun q hq => evV_ok (tblV_ok g x s m) _ q hq)
    · intro p; simp only [valAt_nil]; exact okR_none _

/-! ## The argument values are substrings -/

/-- All substrings of the input that a call-by-value argument can denote. -/
def subStrs (x : List Char) : List (List Char) :=
  (List.range (x.length + 1)).flatMap (fun p => (List.range (p + 1)).map (fun j => pre x p j))

theorem pre_mem {x : List Char} {p : Nat} (hp : p ≤ x.length) (j : Nat) : pre x p j ∈ subStrs x := by
  simp only [subStrs, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨p, by omega, min j p, by omega, ?_⟩
  unfold pre
  congr 1
  omega

theorem length_subStrs_le (x : List Char) : (subStrs x).length ≤ (x.length + 1) * (x.length + 1) := by
  unfold subStrs
  rw [List.length_flatMap]
  have := sum_le_length_mul (fun p => ((List.range (p + 1)).map (fun j => pre x p j)).length) (x.length + 1)
    (List.range (x.length + 1)) (by intro p hp; simp at hp ⊢; omega)
  simpa using this

theorem evPar_mem {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} {p : Nat} (hp : p ≤ x.length) : ∀ (as : List MExp) (W : List (List Char)),
      evParArgs g x s T E as p = some (some W) → ∀ w ∈ W, w ∈ subStrs x
  | [], W, h => by rw [evPar_nil] at h; cases h; intro w hw; cases hw
  | a :: as, W, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evPar_cons_none ha] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [evPar_cons_fail ha] at h; cases h
      | some j =>
        rw [evPar_cons_ok ha] at h
        cases hr : evParArgs g x s T E as p with
        | none => rw [hr] at h; cases h
        | some v =>
          cases v with
          | none => rw [hr] at h; cases h
          | some W' =>
            rw [hr] at h; cases h
            intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact pre_mem hp j
            · exact evPar_mem hp as W' hr w hw

theorem evSeq_mem {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
    {E : List (List Char)} (hT : OkTV x.length T) : ∀ (as : List MExp) (p : Nat) (W : List (List Char)) (q : Nat),
      p ≤ x.length → evSeqArgs g x s T E as p = some (some (W, q)) → (∀ w ∈ W, w ∈ subStrs x) ∧ q ≤ x.length
  | [], p, W, q, hp, h => by rw [evSeq_nil] at h; cases h; exact ⟨fun w hw => (by cases hw), hp⟩
  | a :: as, p, W, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => rw [evSeq_cons_none ha] at h; cases h
    | some ra =>
      cases ra with
      | none => rw [evSeq_cons_fail ha] at h; cases h
      | some j =>
        have hj : j ≤ x.length := evV_ok hT a p hp j ha
        rw [evSeq_cons_ok ha] at h
        cases hr : evSeqArgs g x s T E as j with
        | none => rw [hr] at h; cases h
        | some v =>
          cases v with
          | none => rw [hr] at h; cases h
          | some Wq =>
            obtain ⟨W', q'⟩ := Wq
            rw [hr] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hW', hq'⟩ := evSeq_mem hT as j W' q' hj hr
            refine ⟨fun w hw => ?_, hq'⟩
            rcases List.mem_cons.1 hw with rfl | hw
            · exact pre_mem hp j
            · exact hW' w hw

/-! ## Agreement, counting, and the fixpoint -/

def AgreeV (g : MGrammar) (x : List Char) (T T' : Nat → List (List Char) → Val) : Prop :=
  ∀ i r W, ruleAtM g.rules i = some r → W ∈ words (subStrs x) r.arity → ∀ p, p ≤ x.length →
    valAt (T i W) p = valAt (T' i W) p

theorem AgreeV.refl (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) : AgreeV g x T T :=
  fun _ _ _ _ _ _ _ => rfl
theorem AgreeV.symm {g : MGrammar} {x : List Char} {T T' : Nat → List (List Char) → Val} (h : AgreeV g x T T') :
    AgreeV g x T' T := fun i r W hr hW p hp => (h i r W hr hW p hp).symm
theorem AgreeV.trans {g : MGrammar} {x : List Char} {T₁ T₂ T₃ : Nat → List (List Char) → Val} (h₁ : AgreeV g x T₁ T₂)
    (h₂ : AgreeV g x T₂ T₃) : AgreeV g x T₁ T₃ :=
  fun i r W hr hW p hp => (h₁ i r W hr hW p hp).trans (h₂ i r W hr hW p hp)

mutual
  theorem evV_agree {g : MGrammar} {x : List Char} {s : Strategy} {T T' : Nat → List (List Char) → Val}
      {E : List (List Char)} (h : AgreeV g x T T') (hT : OkTV x.length T) :
      ∀ (e : MExp) (p : Nat), p ≤ x.length → evV g x s T E e p = evV g x s T' E e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ | .dbg _, _, _ | .lam _ _, _, _
    | .callParam _ _, _, _ | .invoke _ _ _, _, _ | .param _, _, _ => by simp only [evV]
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = args.length
        · by_cases hsq : s = .callByValueSeq
          · subst hsq
            rw [evV_call_seq hr ha, evV_call_seq hr ha, ← evSeqArgs_agree h hT args p hp]
            cases hv : evSeqArgs g x .callByValueSeq T E args p with
            | none => rfl
            | some v =>
              cases v with
              | none => rfl
              | some Wq =>
                obtain ⟨W, q⟩ := Wq
                obtain ⟨hW, hq⟩ := evSeq_mem hT args p W q hp hv
                exact h i r W hr ((mem_words _ _ _).2 ⟨by rw [evSeq_length args p W q hv]; exact ha.symm, hW⟩) q hq
          · rw [evV_call_par hr ha hsq, evV_call_par hr ha hsq, ← evParArgs_agree h hT args p hp]
            cases hv : evParArgs g x s T E args p with
            | none => rfl
            | some v =>
              cases v with
              | none => rfl
              | some W =>
                exact h i r W hr ((mem_words _ _ _).2 ⟨by rw [evPar_length args W hv]; exact ha.symm,
                  evPar_mem hp args W hv⟩) p hp
        · simp only [evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      have ha := evV_agree (g := g) (s := s) (E := E) h hT a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evV_seq_none hv, evV_seq_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [evV_seq_fail hv, evV_seq_fail (ha.symm.trans hv)]
        | some j =>
          rw [evV_seq_ok hv, evV_seq_ok (ha.symm.trans hv)]
          exact evV_agree h hT b j (evV_ok hT a p hp j hv)
    | .alt a b, p, hp => by
      have ha := evV_agree (g := g) (s := s) (E := E) h hT a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evV_alt_none hv, evV_alt_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [evV_alt_fail hv, evV_alt_fail (ha.symm.trans hv)]; exact evV_agree h hT b p hp
        | some j => rw [evV_alt_ok hv, evV_alt_ok (ha.symm.trans hv)]
    | .notP a, p, hp => by
      have ha := evV_agree (g := g) (s := s) (E := E) h hT a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evV_not_none hv, evV_not_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [evV_not_fail hv, evV_not_fail (ha.symm.trans hv)]
        | some j => rw [evV_not_ok hv, evV_not_ok (ha.symm.trans hv)]
    | .star a, p, hp => by
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q hq => evV_agree h hT a q (by omega))

  theorem evParArgs_agree {g : MGrammar} {x : List Char} {s : Strategy} {T T' : Nat → List (List Char) → Val}
      {E : List (List Char)} (h : AgreeV g x T T') (hT : OkTV x.length T) :
      ∀ (as : List MExp) (p : Nat), p ≤ x.length → evParArgs g x s T E as p = evParArgs g x s T' E as p
    | [], p, _ => by rw [evPar_nil, evPar_nil]
    | a :: as, p, hp => by
      have ha := evV_agree (g := g) (s := s) (E := E) h hT a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evPar_cons_none hv, evPar_cons_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [evPar_cons_fail hv, evPar_cons_fail (ha.symm.trans hv)]
        | some j => rw [evPar_cons_ok hv, evPar_cons_ok (ha.symm.trans hv), evParArgs_agree h hT as p hp]

  theorem evSeqArgs_agree {g : MGrammar} {x : List Char} {s : Strategy} {T T' : Nat → List (List Char) → Val}
      {E : List (List Char)} (h : AgreeV g x T T') (hT : OkTV x.length T) :
      ∀ (as : List MExp) (p : Nat), p ≤ x.length → evSeqArgs g x s T E as p = evSeqArgs g x s T' E as p
    | [], p, _ => by rw [evSeq_nil, evSeq_nil]
    | a :: as, p, hp => by
      have ha := evV_agree (g := g) (s := s) (E := E) h hT a p hp
      cases hv : evV g x s T E a p with
      | none => rw [evSeq_cons_none hv, evSeq_cons_none (ha.symm.trans hv)]
      | some r =>
        cases r with
        | none => rw [evSeq_cons_fail hv, evSeq_cons_fail (ha.symm.trans hv)]
        | some j =>
          rw [evSeq_cons_ok hv, evSeq_cons_ok (ha.symm.trans hv), evSeqArgs_agree h hT as j (evV_ok hT a p hp j hv)]
end

theorem agreeV_succ {g : MGrammar} {x : List Char} {s : Strategy} {m : Nat}
    (h : AgreeV g x (tblV g x s m) (tblV g x s (m + 1))) : AgreeV g x (tblV g x s (m + 1)) (tblV g x s (m + 2)) := by
  intro i r W hr _ p hp
  rw [valAt_tblV_succ hr W hp, valAt_tblV_succ hr W hp]
  exact evV_agree h (tblV_ok g x s m) r.body p hp

theorem agreeV_from {g : MGrammar} {x : List Char} {s : Strategy} {m : Nat}
    (h : AgreeV g x (tblV g x s m) (tblV g x s (m + 1))) : ∀ k, AgreeV g x (tblV g x s m) (tblV g x s (m + k)) := by
  have step : ∀ k, AgreeV g x (tblV g x s (m + k)) (tblV g x s (m + k + 1)) := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih => exact agreeV_succ ih
  intro k
  induction k with
  | zero => exact AgreeV.refl _ _ _
  | succ k ih => exact ih.trans (step k)

def entryCountV (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) (i : Nat) : Nat :=
  match ruleAtM g.rules i with
  | some r =>
    ((words (subStrs x) r.arity).map
      (fun W => ((List.range (x.length + 1)).map (fun p => defined (valAt (T i W) p))).sum)).sum
  | none => 0

def defCountV (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) : Nat :=
  ((List.range g.rules.length).map (entryCountV g x T)).sum

/-- The number of relevant entries: `Σ_i |subStrs|^arity_i · (n + 1)`. -/
def iterBoundV (g : MGrammar) (x : List Char) : Nat :=
  ((List.range g.rules.length).map (fun i =>
    match ruleAtM g.rules i with
    | some r => (words (subStrs x) r.arity).length * (x.length + 1)
    | none => 0)).sum

theorem defCountV_le {g : MGrammar} {x : List Char} {T T' : Nat → List (List Char) → Val} (h : TLeV T T') :
    defCountV g x T ≤ defCountV g x T' := by
  refine sum_le_sum_of_le _ _ _ (fun i _ => ?_)
  unfold entryCountV
  split
  · exact sum_le_sum_of_le _ _ _ (fun W _ => sum_le_sum_of_le _ _ _ (fun p _ => defined_le (h i W p)))
  · exact Nat.le_refl _

theorem defCountV_le_bound (g : MGrammar) (x : List Char) (T : Nat → List (List Char) → Val) :
    defCountV g x T ≤ iterBoundV g x := by
  refine sum_le_sum_of_le _ _ _ (fun i _ => ?_)
  unfold entryCountV
  split
  · refine sum_le_length_mul _ _ _ (fun W _ => ?_)
    have := sum_le_length_mul (fun p => defined (valAt (T i W) p)) 1 (List.range (x.length + 1))
      (fun p _ => defined_le_one _)
    simpa using this
  · exact Nat.le_refl _

theorem agreeV_of_count_eq {g : MGrammar} {x : List Char} {T T' : Nat → List (List Char) → Val} (h : TLeV T T')
    (he : defCountV g x T = defCountV g x T') : AgreeV g x T T' := by
  intro i r W hr hW p hp
  have hi := eq_of_sum_eq _ _ _ (fun i _ => by
      unfold entryCountV
      split
      · exact sum_le_sum_of_le _ _ _ (fun W _ => sum_le_sum_of_le _ _ _ (fun p _ => defined_le (h i W p)))
      · exact Nat.le_refl _) he i (List.mem_range.2 (ruleAtM_lt hr))
  simp only [entryCountV, hr] at hi
  have hW' := eq_of_sum_eq _ _ _ (fun W _ => sum_le_sum_of_le _ _ _ (fun p _ => defined_le (h i W p))) hi W hW
  have hp' := eq_of_sum_eq _ _ _ (fun p _ => defined_le (h i W p)) hW' p (List.mem_range.2 (by omega))
  rcases h i W p with h₀ | h₀
  · rw [h₀] at hp' ⊢
    cases hv : valAt (T' i W) p with
    | none => rfl
    | some v => rw [hv] at hp'; simp [defined] at hp'
  · exact h₀

theorem tblV_fix_exists (g : MGrammar) (x : List Char) (s : Strategy) :
    ∃ m, m ≤ iterBoundV g x ∧ AgreeV g x (tblV g x s m) (tblV g x s (m + 1)) := by
  refine Classical.byContradiction fun hne => ?_
  have hlt : ∀ m, m ≤ iterBoundV g x → defCountV g x (tblV g x s m) < defCountV g x (tblV g x s (m + 1)) := by
    intro m hm
    refine Nat.lt_of_le_of_ne (defCountV_le (tblV_step g x s m)) (fun heq => hne ⟨m, hm, ?_⟩)
    exact agreeV_of_count_eq (tblV_step g x s m) heq
  have hgrow : ∀ m, m ≤ iterBoundV g x + 1 → m ≤ defCountV g x (tblV g x s m) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih => intro hm; have := hlt m (by omega); have := ih (by omega); omega
  have := hgrow _ (Nat.le_refl _)
  have := defCountV_le_bound g x (tblV g x s (iterBoundV g x + 1))
  omega

theorem tblV_stable (g : MGrammar) (x : List Char) (s : Strategy) {e : MExp} {p : Nat} (hp : p ≤ x.length)
    {v : Option Nat} :
    (∃ m, evV g x s (tblV g x s m) [] e p = some v) ↔ evV g x s (tblV g x s (iterBoundV g x)) [] e p = some v := by
  obtain ⟨m₀, hm₀, hfix⟩ := tblV_fix_exists g x s
  have hag := agreeV_from hfix
  have hB : evV g x s (tblV g x s (iterBoundV g x)) [] e p = evV g x s (tblV g x s m₀) [] e p := by
    have := hag (iterBoundV g x - m₀)
    rw [Nat.add_sub_cancel' hm₀] at this
    exact (evV_agree this (tblV_ok g x s _) e p hp).symm
  constructor
  · rintro ⟨m, hm⟩
    by_cases hle : m ≤ iterBoundV g x
    · exact evV_lift hle hm
    · have := hag (m - m₀)
      rw [Nat.add_sub_cancel' (by omega)] at this
      rw [hB, evV_agree this (tblV_ok g x s _) e p hp]
      exact hm
  · intro h; exact ⟨_, h⟩

/-! ## The decision procedure and the polynomial bound -/

def decideObsV (s : Strategy) (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match evV g x s (tblV g x s (iterBoundV g x)) [] e x.length with
  | none => none
  | some none => some none
  | some (some j) => some (some (sfx x j))

/-- **Decidability (call-by-value).** For a first-order grammar and a first-order expression, `decideObsV` returns
exactly the observation of the finite Par/Seq derivation on `x`. -/
theorem decideObsV_iff {g : MGrammar} {s : Strategy} (hg : g.FirstOrder) (hs : s ≠ .callByName) {e : MExp}
    (he : e.FirstOrder) (x : List Char) (r : Option (List Char)) : decideObsV s g x e = some r ↔ SObs g s e x r := by
  constructor
  · intro h
    unfold decideObsV at h
    cases hd : evV g x s (tblV g x s (iterBoundV g x)) [] e x.length with
    | none => rw [hd] at h; cases h
    | some v =>
      obtain ⟨o, d, ho⟩ := evV_derives hg hs he (iterBoundV g x) (Nat.le_refl _) hd
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
    obtain ⟨m, hm⟩ := derivesV_ev (x := x) hg hs d he ⟨[], rfl⟩
    cases o with
    | fail =>
      have := (tblV_stable g x s (Nat.le_refl _)).1 ⟨m, hm⟩
      simp [decideObsV, this, obsR, MOutcome.restOf]
    | ok t rest =>
      have := (tblV_stable g x s (Nat.le_refl _)).1 ⟨m, hm⟩
      simp only [decideObsV, this, MOutcome.restOf]
      rw [sfx_suffix (mderives_suffix d _ _ rfl).choose_spec]

theorem decideObsV_none_iff {g : MGrammar} {s : Strategy} (hg : g.FirstOrder) (hs : s ≠ .callByName) {e : MExp}
    (he : e.FirstOrder) (x : List Char) : decideObsV s g x e = none ↔ ∀ r, ¬ SObs g s e x r := by
  constructor
  · intro h r hr
    rw [(decideObsV_iff hg hs he x r).2 hr] at h; cases h
  · intro h
    cases hd : decideObsV s g x e with
    | none => rfl
    | some r => exact absurd ((decideObsV_iff hg hs he x r).1 hd) (h r)

/-- **Polynomially many rounds**: with every arity at most `K`, at most `|rules| · ((n+1)²)^K · (n+1)`. -/
theorem iterBoundV_le (g : MGrammar) (x : List Char) {K : Nat} (hK : ∀ r ∈ g.rules, r.arity ≤ K) :
    iterBoundV g x ≤ g.rules.length * (((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1)) := by
  unfold iterBoundV
  have := sum_le_length_mul (fun i => match ruleAtM g.rules i with
      | some r => (words (subStrs x) r.arity).length * (x.length + 1)
      | none => 0) (((x.length + 1) * (x.length + 1)) ^ K * (x.length + 1)) (List.range g.rules.length) (by
    intro i _
    split
    · rename_i r hr
      rw [length_words]
      refine Nat.mul_le_mul_right _ (Nat.le_trans (Nat.pow_le_pow_left (length_subStrs_le x) _) ?_)
      exact Nat.pow_le_pow_right (by have := Nat.succ_pos x.length; exact Nat.mul_pos this this)
        (hK r (ruleAtM_mem hr))
    · exact Nat.zero_le _)
  simpa using this

/-! ## Examples: the strategy table, computed -/

example : decideObsV .callByValuePar row2G ['a'] (.call 1 []) = some (some []) := by decide
example : decideObsV .callByValueSeq row2G ['a'] (.call 1 []) = some none := by decide
example : decideObsV .callByValuePar row4G ['a', 'b'] (.call 1 []) = some none := by decide
example : decideObsV .callByValueSeq row4G ['a', 'b'] (.call 1 []) = some (some []) := by decide

end Shallot.MacroPeg
