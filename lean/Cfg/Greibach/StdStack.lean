import Cfg.Greibach.Defs

/-!
# The stack machine behind the Dyck words (for `greibach_std`)

Following Nipkow's `bal_stk`: a stack machine over the bracket characters. An opening bracket is pushed; a closing
bracket pops the matching opening bracket. `Dyck v` holds iff the machine run on `v` from the empty stack ends with the
empty stack (`dyck_iff_stkRun`).

The nonterminal `i` is pushed as `( [^i (` (`pushcode`) and popped as `) ]^i )` (`popcode`); on the stack it occupies
the fragment `frag i`, which as a list equals `pushcode i`.
-/

namespace Shallot.Cfg
namespace GStd

/-- Pop the opening bracket `o` from the top of the stack, if it is there. -/
def popIf (o : Char) : List Char → Option (List Char)
  | y :: t => if y = o then some t else none
  | [] => none

/-- One step of the stack machine. -/
def stkStep (s : List Char) (x : Char) : Option (List Char) :=
  if x = '(' then some ('(' :: s)
  else if x = '[' then some ('[' :: s)
  else if x = ')' then popIf '(' s
  else if x = ']' then popIf '[' s
  else none

/-- Run the stack machine on a word. -/
def stkRun : List Char → List Char → Option (List Char)
  | s, [] => some s
  | s, x :: xs => (stkStep s x).bind (fun t => stkRun t xs)

/-- Popping the expected opener. -/
theorem popIf_self (o : Char) (t : List Char) : popIf o (o :: t) = some t := by simp [popIf]

/-- Step on `(`. -/
theorem step_lp (s : List Char) : stkStep s '(' = some ('(' :: s) := rfl
/-- Step on `[`. -/
theorem step_lb (s : List Char) : stkStep s '[' = some ('[' :: s) := rfl
/-- Step on `)`. -/
theorem step_rp (s : List Char) : stkStep s ')' = popIf '(' s := rfl
/-- Step on `]`. -/
theorem step_rb (s : List Char) : stkStep s ']' = popIf '[' s := rfl
/-- Step on a non-bracket. -/
theorem step_other {x : Char} (h1 : x ≠ '(') (h2 : x ≠ '[') (h3 : x ≠ ')') (h4 : x ≠ ']') (s : List Char) :
    stkStep s x = none := by simp [stkStep, h1, h2, h3, h4]

/-- Running on a cons. -/
theorem stkRun_cons (s : List Char) (x : Char) (xs : List Char) :
    stkRun s (x :: xs) = (stkStep s x).bind (fun t => stkRun t xs) := rfl

/-- Running on a concatenation is running on the parts in turn. -/
theorem stkRun_append (s u v : List Char) :
    stkRun s (u ++ v) = (stkRun s u).bind (fun t => stkRun t v) := by
  induction u generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, stkRun]
    cases stkStep s x with
    | none => rfl
    | some t => simp only [Option.bind_some]; exact ih t

/-- Splitting a successful run on a concatenation. -/
theorem stkRun_append_split {s u v t : List Char} (h : stkRun s (u ++ v) = some t) :
    ∃ s', stkRun s u = some s' ∧ stkRun s' v = some t := by
  rw [stkRun_append] at h
  cases hu : stkRun s u with
  | none => rw [hu] at h; cases h
  | some s' => rw [hu] at h; exact ⟨s', rfl, h⟩

/-- A Dyck word leaves every stack unchanged. -/
theorem stkRun_of_dyck {u : List Char} (hu : Dyck u) : ∀ s, stkRun s u = some s := by
  induction hu with
  | nil => intro s; rfl
  | append _ _ ih1 ih2 => intro s; rw [stkRun_append, ih1]; exact ih2 s
  | paren _ ih =>
    intro s
    rw [stkRun_cons, step_lp, Option.bind_some, stkRun_append, ih]; rfl
  | brack _ ih =>
    intro s
    rw [stkRun_cons, step_lb, Option.bind_some, stkRun_append, ih]; rfl

/-- Inserting a Dyck word between the halves of a split of an opened-and-closed word, the bracket case. -/
theorem dyck_insert_wrap {m u : List Char} (o cl : Char) (hm : Dyck m) (hu : Dyck u)
    (wrap : ∀ {v}, Dyck v → Dyck (o :: (v ++ [cl])))
    (ih : ∀ x y, u = x ++ y → Dyck (x ++ m ++ y)) :
    ∀ x y, o :: (u ++ [cl]) = x ++ y → Dyck (x ++ m ++ y) := by
  intro x y hxy
  cases x with
  | nil =>
    have := Dyck.append hm (wrap hu)
    simpa [hxy] using this
  | cons x0 x' =>
    simp only [List.cons_append, List.cons.injEq] at hxy
    obtain ⟨hx0, hxy⟩ := hxy
    subst hx0
    rcases List.append_eq_append_iff.mp hxy.symm with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · subst h1; subst h2
      have := wrap (ih x' a' rfl)
      simpa [List.append_assoc] using this
    · cases c' with
      | nil =>
        simp only [List.nil_append] at h2
        subst h2
        have := wrap (ih u [] (List.append_nil u).symm)
        simpa [List.append_assoc, h1] using this
      | cons c0 c'' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨h2a, h2b⟩ := h2
        have hc : c'' = [] := (List.append_eq_nil_iff.mp h2b.symm).1
        have hy : y = [] := (List.append_eq_nil_iff.mp h2b.symm).2
        subst hc; subst hy; subst h2a; subst h1
        have := Dyck.append (wrap hu) hm
        simpa [List.append_assoc] using this

/-- Inserting a Dyck word anywhere into a Dyck word gives a Dyck word. -/
theorem dyck_insert {m w : List Char} (hm : Dyck m) (hw : Dyck w) :
    ∀ x y, w = x ++ y → Dyck (x ++ m ++ y) := by
  induction hw with
  | nil =>
    intro x y hxy
    have hx : x = [] := (List.append_eq_nil_iff.mp hxy.symm).1
    have hy : y = [] := (List.append_eq_nil_iff.mp hxy.symm).2
    subst hx; subst hy; simpa using hm
  | @append u v hu hv ih1 ih2 =>
    intro x y hxy
    rcases List.append_eq_append_iff.mp hxy.symm with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · subst h1; subst h2
      have := Dyck.append (ih1 x a' rfl) hv
      simpa [List.append_assoc] using this
    · subst h1; subst h2
      have := Dyck.append hu (ih2 c' y rfl)
      simpa [List.append_assoc] using this
  | paren hu ih => exact dyck_insert_wrap '(' ')' hm hu Dyck.paren ih
  | brack hu ih => exact dyck_insert_wrap '[' ']' hm hu Dyck.brack ih

/-- `()` is a Dyck word. -/
theorem dyck_pp : Dyck ['(', ')'] := by simpa using Dyck.paren Dyck.nil

/-- `[]` is a Dyck word. -/
theorem dyck_bb : Dyck ['[', ']'] := by simpa using Dyck.brack Dyck.nil

/-- Popping after a step: a close bracket `cl` whose opener `o` is on top. -/
theorem dyck_of_pop {o cl : Char} {v s : List Char} (hp : Dyck [o, cl])
    (ih : ∀ t, stkRun t v = some [] → Dyck (t.reverse ++ v))
    (h : (popIf o s).bind (fun t => stkRun t v) = some []) : Dyck (s.reverse ++ cl :: v) := by
  cases s with
  | nil => simp [popIf] at h
  | cons y t =>
    by_cases hy : y = o
    · subst hy
      rw [popIf_self, Option.bind_some] at h
      have := dyck_insert hp (ih t h) t.reverse v rfl
      simpa [List.append_assoc] using this
    · simp [popIf, hy] at h

/-- A successful run ending empty: the reversed stack followed by the word is a Dyck word. -/
theorem dyck_of_stkRun_gen : ∀ (v s : List Char), stkRun s v = some [] → Dyck (s.reverse ++ v)
  | [], s, h => by
    simp only [stkRun, Option.some.injEq] at h
    subst h; exact Dyck.nil
  | x :: v, s, h => by
    rw [stkRun_cons] at h
    by_cases h1 : x = '('
    · subst h1
      rw [step_lp, Option.bind_some] at h
      have := dyck_of_stkRun_gen v ('(' :: s) h
      simpa using this
    · by_cases h2 : x = '['
      · subst h2
        rw [step_lb, Option.bind_some] at h
        have := dyck_of_stkRun_gen v ('[' :: s) h
        simpa using this
      · by_cases h3 : x = ')'
        · subst h3
          rw [step_rp] at h
          exact dyck_of_pop dyck_pp (fun t ht => dyck_of_stkRun_gen v t ht) h
        · by_cases h4 : x = ']'
          · subst h4
            rw [step_rb] at h
            exact dyck_of_pop dyck_bb (fun t ht => dyck_of_stkRun_gen v t ht) h
          · rw [step_other h1 h2 h3 h4] at h; cases h

/-- **Dyck words are exactly the words the stack machine accepts from the empty stack.** -/
theorem dyck_iff_stkRun (v : List Char) : Dyck v ↔ stkRun [] v = some [] :=
  ⟨fun h => stkRun_of_dyck h [], fun h => by simpa using dyck_of_stkRun_gen v [] h⟩

/-- A Dyck word consists of brackets. -/
theorem dyck_bracket {v : List Char} (hv : Dyck v) : ∀ c ∈ v, isBracket c = true := by
  induction hv with
  | nil => intro c hc; cases hc
  | append _ _ ih1 ih2 =>
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact ih1 c h
    · exact ih2 c h
  | paren _ ih =>
    intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with h | h | h
    · subst h; rfl
    · exact ih c h
    · simp at h; subst h; rfl
  | brack _ ih =>
    intro c hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with h | h | h
    · subst h; rfl
    · exact ih c h
    · simp at h; subst h; rfl

/-! ## Push and pop codes -/

/-- The push code of nonterminal `i`: `( [^i (`. -/
def pushcode (i : Nat) : List Char := '(' :: (List.replicate i '[' ++ ['('])

/-- The pop code of nonterminal `i`: `) ]^i )`. -/
def popcode (i : Nat) : List Char := ')' :: (List.replicate i ']' ++ [')'])

/-- The stack fragment of nonterminal `i` (top first); it equals `pushcode i`. -/
def frag (i : Nat) : List Char := '(' :: (List.replicate i '[' ++ ['('])

/-- The stack encoding of a nonterminal stack (top first). -/
def stkenc (α : List Nat) : List Char := (α.map frag).flatten

/-- Pushing `[` repeatedly. -/
theorem stkRun_rep_open (i : Nat) : ∀ s, stkRun s (List.replicate i '[') = some (List.replicate i '[' ++ s) := by
  induction i with
  | zero => intro s; rfl
  | succ i ih =>
    intro s
    rw [List.replicate_succ, stkRun_cons, step_lb, Option.bind_some, ih]
    simp only [Option.some.injEq]
    rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ]

/-- Popping `[` repeatedly. -/
theorem stkRun_rep_close (i : Nat) : ∀ t, stkRun (List.replicate i '[' ++ t) (List.replicate i ']') = some t := by
  induction i with
  | zero => intro t; rfl
  | succ i ih =>
    intro t
    rw [List.replicate_succ, List.replicate_succ, List.cons_append, stkRun_cons, step_rb]
    simpa [popIf] using ih t

/-- Inverting repeated `]` pops. -/
theorem stkRun_rep_close_inv (i : Nat) :
    ∀ t r s, stkRun t (List.replicate i ']' ++ r) = some s →
      ∃ t', t = List.replicate i '[' ++ t' ∧ stkRun t' r = some s := by
  induction i with
  | zero => intro t r s h; exact ⟨t, rfl, h⟩
  | succ i ih =>
    intro t r s h
    rw [List.replicate_succ, List.cons_append, stkRun_cons, step_rb] at h
    cases t with
    | nil => simp [popIf] at h
    | cons y t =>
      by_cases hy : y = '['
      · subst hy
        rw [popIf_self, Option.bind_some] at h
        obtain ⟨t', h1, h2⟩ := ih t r s h
        exact ⟨t', by simp [h1, List.replicate_succ], h2⟩
      · simp [popIf, hy] at h

/-- Reading `pushcode i` pushes `frag i`. -/
theorem stkRun_pushcode (i : Nat) (s : List Char) : stkRun s (pushcode i) = some (frag i ++ s) := by
  rw [pushcode, stkRun_cons, step_lp, Option.bind_some, stkRun_append, stkRun_rep_open, Option.bind_some,
    stkRun_cons, step_lp]
  simp [stkRun, frag]

/-- Reading `popcode i` pops `frag i`. -/
theorem stkRun_popcode (i : Nat) (s : List Char) : stkRun (frag i ++ s) (popcode i) = some s := by
  rw [frag, popcode, List.cons_append, stkRun_cons, step_rp]
  rw [popIf_self, Option.bind_some]
  rw [stkRun_append, List.append_assoc, stkRun_rep_close, Option.bind_some, stkRun_cons, step_rp]
  simp [stkRun, popIf]

/-- A successful pop of `popcode i` forces the stack to start with `frag i`. -/
theorem stkRun_popcode_inv {i : Nat} {t s : List Char} (h : stkRun t (popcode i) = some s) : t = frag i ++ s := by
  rw [popcode, stkRun_cons, step_rp] at h
  cases t with
  | nil => simp [popIf] at h
  | cons y t =>
    by_cases hy : y = '('
    · subst hy
      rw [popIf_self, Option.bind_some] at h
      obtain ⟨t', h1, h2⟩ := stkRun_rep_close_inv i t [')'] s h
      rw [stkRun_cons, step_rp] at h2
      cases t' with
      | nil => simp [popIf] at h2
      | cons z t'' =>
        by_cases hz : z = '('
        · subst hz
          rw [popIf_self, Option.bind_some] at h2
          simp only [stkRun, Option.some.injEq] at h2
          subst h2; subst h1
          simp [frag]
        · simp [popIf, hz] at h2
    · simp [popIf, hy] at h

/-- Reading concatenated push codes pushes the reversed stack. -/
theorem stkRun_pushes (is : List Nat) : ∀ s,
    stkRun s ((is.map pushcode).flatten) = some (stkenc is.reverse ++ s) := by
  induction is with
  | nil => intro s; rfl
  | cons i is ih =>
    intro s
    simp only [List.map_cons, List.flatten_cons]
    rw [stkRun_append, stkRun_pushcode, Option.bind_some, ih]
    simp [stkenc]

/-- `[^i (` determines `i` and the rest. -/
theorem rep_open_inj : ∀ (i j : Nat) (xs ys : List Char),
    List.replicate i '[' ++ '(' :: xs = List.replicate j '[' ++ '(' :: ys → i = j ∧ xs = ys
  | 0, 0, xs, ys, h => by simpa using h
  | 0, j + 1, xs, ys, h => by simp [List.replicate_succ] at h
  | i + 1, 0, xs, ys, h => by simp [List.replicate_succ] at h
  | i + 1, j + 1, xs, ys, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := rep_open_inj i j xs ys h
    exact ⟨by omega, this.2⟩

/-- The fragment determines the nonterminal and the rest as a prefix. -/
theorem frag_append_inj {i j : Nat} {xs ys : List Char} (h : frag i ++ xs = frag j ++ ys) : i = j ∧ xs = ys := by
  simp only [frag, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  exact rep_open_inj i j xs ys h

/-- An empty stack encoding is the encoding of the empty stack. -/
theorem stkenc_eq_nil {α : List Nat} (h : stkenc α = []) : α = [] := by
  cases α with
  | nil => rfl
  | cons a α => simp [stkenc, frag] at h

end GStd
end Shallot.Cfg
