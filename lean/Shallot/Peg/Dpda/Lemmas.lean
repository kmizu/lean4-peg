import Shallot.Peg.Dpda.Grammar
import Shallot.Peg.Determinism

/-!
# Small lemmas for the DPDA grammar

Ordered choices over lists, the always-failing rule, end of input, character comparison, rule lookup and index
arithmetic.
-/

namespace Shallot.Dpda

theorem beqChar_iff {c d : Char} : beqChar c d = true ↔ c = d := by
  simp only [beqChar, beq_iff_eq]; exact Char.toNat_inj

theorem beqChar_false {c d : Char} (h : c ≠ d) : beqChar c d = false := by
  cases hb : beqChar c d with
  | false => rfl
  | true => exact absurd (beqChar_iff.mp hb) h

theorem derives_failE (g : Grammar) (x : List Char) : Derives g failE x .fail := by
  cases x with
  | nil => exact Derives.rangeEmpty _ _
  | cons d rest =>
    refine Derives.rangeFail _ _ d rest ?_
    have : ∀ n : Nat, (Nat.ble 1 n && Nat.ble n 0) = false := by
      intro n
      cases n with
      | zero => rfl
      | succ k => have h : Nat.ble (k + 1) 0 = false := rfl; simp [h]
    exact this d.toNat

theorem derives_eofE_nil (g : Grammar) : Derives g eofE [] (.ok .notT []) :=
  Derives.notFail _ _ Derives.anyFail

theorem derives_eofE_cons (g : Grammar) (c : Char) (rest : List Char) : Derives g eofE (c :: rest) .fail :=
  Derives.notOk _ _ rest _ (Derives.anyOk c rest)

theorem altList_fail {g : Grammar} {x : List Char} :
    ∀ {l : List PExp}, (∀ e ∈ l, Derives g e x .fail) → Derives g (altList l) x .fail
  | [], _ => derives_failE g x
  | e :: _, h =>
    Derives.altFail _ _ _ (h e List.mem_cons_self)
      (altList_fail fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- If every alternative fails or succeeds with the same rest, and one succeeds, the choice succeeds with it. -/
theorem altList_ok {g : Grammar} {x r₀ : List Char} :
    ∀ {l : List PExp}, (∀ e ∈ l, Derives g e x .fail ∨ ∃ t, Derives g e x (.ok t r₀)) →
      (∃ e ∈ l, ∃ t, Derives g e x (.ok t r₀)) → ∃ t, Derives g (altList l) x (.ok t r₀)
  | [], _, ⟨e, he, _⟩ => by cases he
  | e :: es, hall, ⟨e', he', t', ht'⟩ => by
    rcases hall e List.mem_cons_self with hf | ⟨t, ht⟩
    · have hex : ∃ e'' ∈ es, ∃ t, Derives g e'' x (.ok t r₀) := by
        rcases List.mem_cons.mp he' with rfl | hes
        · exact absurd (derives_det hf ht') (by intro h; cases h)
        · exact ⟨e', hes, t', ht'⟩
      obtain ⟨t'', h''⟩ := altList_ok (fun e'' he'' => hall e'' (List.mem_cons_of_mem _ he'')) hex
      exact ⟨_, Derives.altR _ _ _ _ _ hf h''⟩
    · exact ⟨_, Derives.altL _ _ _ _ _ ht⟩

theorem ruleAt_eq_getElem? : ∀ (l : List PExp) (i : Nat), ruleAt l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rs, i + 1 => ruleAt_eq_getElem? rs i

theorem divmod {n a r : Nat} (hr : r < n) : (n * a + r) / n = a ∧ (n * a + r) % n = r := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

namespace DPDA

variable (M : DPDA)

theorem ruleAt_grammar {i : Nat} (hi : i < M.nQ * M.nG * M.nQ + M.nQ * M.nG) :
    ruleAt M.grammar.rules i = some (M.ruleOf i) := by
  show ruleAt ((List.range _).map M.ruleOf) i = _
  rw [ruleAt_eq_getElem?]; simp [hi]

theorem pidx_lt {q Z r : Nat} (hq : q < M.nQ) (hZ : Z < M.nG) (hr : r < M.nQ) :
    M.pidx q Z r < M.nQ * M.nG * M.nQ := by
  have h1 : (q + 1) * M.nG ≤ M.nQ * M.nG := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, Nat.one_mul] at h1
  have h2 : M.nQ * (q * M.nG + Z + 1) ≤ M.nQ * (M.nQ * M.nG) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at h2
  have h3 := Nat.mul_comm (M.nQ * M.nG) M.nQ
  unfold pidx
  omega

theorem ruleOf_pidx {q Z r : Nat} (hq : q < M.nQ) (hZ : Z < M.nG) (hr : r < M.nQ) :
    M.ruleOf (M.pidx q Z r) = M.popRule q Z r := by
  unfold ruleOf
  rw [if_pos (M.pidx_lt hq hZ hr)]
  have h1 := divmod (n := M.nQ) (a := q * M.nG + Z) hr
  have h2 := divmod (n := M.nG) (a := q) hZ
  rw [Nat.mul_comm M.nG q] at h2
  unfold pidx
  rw [h1.1, h1.2, h2.1, h2.2]

theorem aidx_lt {q Z : Nat} (hq : q < M.nQ) (hZ : Z < M.nG) :
    M.aidx q Z < M.nQ * M.nG * M.nQ + M.nQ * M.nG := by
  have h1 : (q + 1) * M.nG ≤ M.nQ * M.nG := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, Nat.one_mul] at h1
  unfold aidx
  omega

theorem ruleOf_aidx {q Z : Nat} (hq : q < M.nQ) (hZ : Z < M.nG) :
    M.ruleOf (M.aidx q Z) = M.accRule q Z := by
  unfold ruleOf aidx
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  have h2 := divmod (n := M.nG) (a := q) hZ
  rw [Nat.mul_comm M.nG q] at h2
  rw [h2.1, h2.2]

/-- Looking up a pop nonterminal. -/
theorem ruleAt_pop {q Z r : Nat} (hq : q < M.nQ) (hZ : Z < M.nG) (hr : r < M.nQ) :
    ruleAt M.grammar.rules (M.pidx q Z r) = some (M.popRule q Z r) := by
  have := M.ruleAt_grammar (i := M.pidx q Z r) (by have := M.pidx_lt hq hZ hr; omega)
  rw [this, M.ruleOf_pidx hq hZ hr]

/-- Looking up an accept nonterminal. -/
theorem ruleAt_acc {q Z : Nat} (hq : q < M.nQ) (hZ : Z < M.nG) :
    ruleAt M.grammar.rules (M.aidx q Z) = some (M.accRule q Z) := by
  rw [M.ruleAt_grammar (M.aidx_lt hq hZ), M.ruleOf_aidx hq hZ]

end DPDA

end Shallot.Dpda
