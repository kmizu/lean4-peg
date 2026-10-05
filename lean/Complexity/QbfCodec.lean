import Complexity.Qbf

namespace Complexity

theorem bitsTok_tokBits (t : Nat) (h : t < 16) :
    bitsTok (t / 8 % 2 == 1) (t / 4 % 2 == 1) (t / 2 % 2 == 1) (t % 2 == 1) = t := by
  revert t; decide

theorem tokBits_lt_16_roundtrip (t : Nat) (h : t < 16) (rest : List Bool) :
    ofBits (tokBits t ++ rest) = t :: ofBits rest := by
  simp only [tokBits, List.cons_append, List.nil_append, ofBits]
  rw [bitsTok_tokBits t h]

theorem ofBits_toBits : ∀ ts : List Nat, (∀ t ∈ ts, t < 16) → ofBits (toBits ts) = ts := by
  intro ts
  induction ts with
  | nil => intro _; simp [toBits, ofBits]
  | cons t ts ih =>
    intro h
    have ht : t < 16 := h t (by simp)
    have := ih (fun s hs => h s (by simp [hs]))
    simp only [toBits, List.flatMap_cons] at *
    rw [tokBits_lt_16_roundtrip t ht, this]

theorem countOnes_replicate (n : Nat) (t : Nat) (ts : List Nat) (ht : t ≠ Tok.one) :
    countOnes (List.replicate n Tok.one ++ t :: ts) = (n, t :: ts) := by
  induction n with
  | zero => simp [countOnes, ht]
  | succ n ih => simp [List.replicate_succ, countOnes, ih]

theorem encName_cons (n : Nat) (x : Name) :
    encName (n :: x) = List.replicate n Tok.one ++ Tok.sep :: encName x := by
  simp [encName]

theorem length_lt_encName (x : Name) : x.length < (encName x).length := by
  induction x with
  | nil => simp [encName]
  | cons n x ih => rw [encName_cons]; simp; omega

theorem parseName_encName (x : Name) (rest : List Nat) (fuel : Nat) (hf : x.length < fuel) :
    parseName fuel (encName x ++ rest) = (x, rest) := by
  induction x generalizing fuel with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [encName, parseName, countOnes, Tok.fin, Tok.one, Tok.sep]
  | cons n x ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [encName_cons, List.append_assoc, List.cons_append, parseName,
      countOnes_replicate n Tok.sep _ (by decide)]
    simp only [Tok.sep, if_true]
    rw [ih f (by simp at hf; omega)]

theorem parseOp_enc (op : Op) (rest : List Nat) (fuel : Nat) (hf : op.enc.length ≤ fuel) :
    parseOp fuel (op.enc ++ rest) = some (op, rest) := by
  have a := length_lt_encName
  cases op with
  | var x =>
    have := a x
    simp [Op.enc] at hf
    simp [Op.enc, parseOp, Tok.var, parseName_encName x rest fuel (by omega)]
  | tt => simp [Op.enc, parseOp, Tok.tt, Tok.var]
  | ff => simp [Op.enc, parseOp, Tok.ff, Tok.tt, Tok.var]
  | not g =>
    have := a g
    simp [Op.enc] at hf
    simp [Op.enc, parseOp, Tok.neg, Tok.var, Tok.tt, Tok.ff, parseName_encName g rest fuel (by omega)]
  | and g h =>
    have := a g
    have := a h
    simp [Op.enc] at hf
    simp [Op.enc, parseOp, Tok.conj, Tok.var, Tok.tt, Tok.ff, Tok.neg,
      parseName_encName g _ fuel (by omega), parseName_encName h rest fuel (by omega)]
  | or g h =>
    have := a g
    have := a h
    simp [Op.enc] at hf
    simp [Op.enc, parseOp, Tok.disj, Tok.conj, Tok.var, Tok.tt, Tok.ff, Tok.neg,
      parseName_encName g _ fuel (by omega), parseName_encName h rest fuel (by omega)]

theorem decode_gates : ∀ (gs : List Gate) (fuel : Nat), (gs.flatMap Gate.enc).length < fuel →
    decodeToks fuel (gs.flatMap Gate.enc) = ⟨[], gs⟩ := by
  intro gs
  induction gs with
  | nil => intro fuel h; obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩; simp [decodeToks]
  | cons g gs ih =>
    intro fuel h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hn := length_lt_encName g.out
    have ho : g.op.enc.length ≤ (g.op.enc ++ gs.flatMap Gate.enc).length := by simp
    simp only [List.flatMap_cons, Gate.enc, List.length_append, List.length_cons] at h
    simp only [List.flatMap_cons, Gate.enc, List.cons_append, List.append_assoc, decodeToks]
    simp only [Tok.gate, Tok.all, Tok.ex]
    simp only [show ¬ (6 = 4 ∨ 6 = 5) by decide, if_false, if_true]
    rw [parseName_encName g.out _ _ (by simp; omega)]
    simp only []
    rw [parseOp_enc g.op _ _ (by simp)]
    simp only []
    rw [ih f (by omega)]

theorem decode_quants : ∀ (qs : List (Bool × Name)) (gs : List Gate) (fuel : Nat),
    (qs.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2)
      ++ gs.flatMap Gate.enc).length < fuel →
    decodeToks fuel (qs.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2)
      ++ gs.flatMap Gate.enc) = ⟨qs, gs⟩ := by
  intro qs gs
  induction qs with
  | nil => intro fuel h; simpa using decode_gates gs fuel (by simpa using h)
  | cons q qs ih =>
    intro fuel h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hn := length_lt_encName q.2
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc, List.length_append,
      List.length_cons] at h
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc, decodeToks]
    obtain ⟨b, x⟩ := q
    cases b <;>
    · simp only [Tok.all, Tok.ex, Bool.false_eq_true, if_true, if_false, true_or, or_true, ite_true] at *
      rw [parseName_encName x _ _ (by simp at *; omega)]
      simp only []
      rw [ih f (by simp at *; omega)]
      simp [Tok.all, Tok.ex]

theorem toks_lt_16 (φ : Qbf) : ∀ t ∈ φ.toks, t < 16 := by
  intro t ht
  have hn : ∀ x : Name, ∀ t ∈ encName x, t < 16 := by
    intro x t ht
    simp only [encName, List.mem_append, List.mem_flatMap, List.mem_replicate, List.mem_singleton] at ht
    rcases ht with ⟨n, _, h | h | h⟩ | h <;> simp [Tok.one, Tok.sep, Tok.fin] at * <;> omega
  have ho : ∀ o : Op, ∀ t ∈ o.enc, t < 16 := by
    intro o t ht
    cases o <;> simp [Op.enc] at ht <;>
      first
      | (rcases ht with h | h | h <;> first | (subst h; decide) | exact hn _ _ h)
      | (rcases ht with h | h <;> first | (subst h; decide) | exact hn _ _ h)
      | (subst ht; decide)
  simp only [Qbf.toks, List.mem_append, List.mem_flatMap] at ht
  rcases ht with ⟨p, _, h⟩ | ⟨g, _, h⟩
  · simp only [List.mem_cons] at h
    rcases h with h | h
    · subst h; split <;> decide
    · exact hn _ _ h
  · have h' : t ∈ Tok.gate :: (encName g.out ++ g.op.enc) := by simpa [Gate.enc] using h
    rcases List.mem_cons.mp h' with h | h
    · subst h; decide
    · rcases List.mem_append.mp h with h | h
      · exact hn _ _ h
      · exact ho g.op t h

theorem decode_encode (φ : Qbf) : Qbf.decode φ.encode = φ := by
  have h1 : ofBits φ.encode = φ.toks := ofBits_toBits _ (toks_lt_16 φ)
  unfold Qbf.decode
  rw [h1]
  obtain ⟨qs, gs⟩ := φ
  exact decode_quants qs gs _ (by simp [Qbf.toks])

end Complexity
