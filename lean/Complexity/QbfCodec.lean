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

theorem decode_matrix : ∀ (m : List RTok) (fuel : Nat), (m.flatMap RTok.enc).length < fuel →
    decodeToks fuel (m.flatMap RTok.enc) = ⟨[], m⟩ := by
  intro m
  induction m with
  | nil =>
    intro fuel h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at h; omega⟩
    simp [decodeToks]
  | cons r m ih =>
    intro fuel h
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    cases r with
    | var x =>
      have hn := length_lt_encName x
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.length_append,
        List.length_cons] at h
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, decodeToks]
      simp only [Tok.var, Tok.all, Tok.ex]
      simp only [show ¬ (6 = 4 ∨ 6 = 5) by decide, if_false, if_true]
      rw [parseName_encName x _ _ (by simp; omega)]
      simp only []
      rw [ih f (by omega)]
    | tt =>
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append,
        List.length_cons] at h
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append, decodeToks]
      rw [ih f (by omega)]
      simp [Tok.tt, Tok.var, Tok.all, Tok.ex]
    | ff =>
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append,
        List.length_cons] at h
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append, decodeToks]
      rw [ih f (by omega)]
      simp [Tok.tt, Tok.ff, Tok.var, Tok.all, Tok.ex]
    | neg =>
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append,
        List.length_cons] at h
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append, decodeToks]
      rw [ih f (by omega)]
      simp [Tok.tt, Tok.ff, Tok.neg, Tok.var, Tok.all, Tok.ex]
    | conj =>
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append,
        List.length_cons] at h
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append, decodeToks]
      rw [ih f (by omega)]
      simp [Tok.tt, Tok.ff, Tok.neg, Tok.conj, Tok.var, Tok.all, Tok.ex]
    | disj =>
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append,
        List.length_cons] at h
      simp only [List.flatMap_cons, RTok.enc, List.cons_append, List.nil_append, decodeToks]
      rw [ih f (by omega)]
      simp [Tok.tt, Tok.ff, Tok.neg, Tok.conj, Tok.disj, Tok.var, Tok.all, Tok.ex]

theorem decode_quants : ∀ (qs : List (Bool × Name)) (m : List RTok) (fuel : Nat),
    (qs.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2)
      ++ m.flatMap RTok.enc).length < fuel →
    decodeToks fuel (qs.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2)
      ++ m.flatMap RTok.enc) = ⟨qs, m⟩ := by
  intro qs m
  induction qs with
  | nil => intro fuel h; simpa using decode_matrix m fuel (by simpa using h)
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
  have ho : ∀ o : RTok, ∀ t ∈ o.enc, t < 16 := by
    intro o t ht
    cases o with
    | var x =>
      simp only [RTok.enc, List.mem_cons] at ht
      rcases ht with h | h
      · subst h; decide
      · exact hn _ _ h
    | tt => simp [RTok.enc] at ht; subst ht; decide
    | ff => simp [RTok.enc] at ht; subst ht; decide
    | neg => simp [RTok.enc] at ht; subst ht; decide
    | conj => simp [RTok.enc] at ht; subst ht; decide
    | disj => simp [RTok.enc] at ht; subst ht; decide
  simp only [Qbf.toks, List.mem_append, List.mem_flatMap] at ht
  rcases ht with ⟨p, _, h⟩ | ⟨g, _, h⟩
  · simp only [List.mem_cons] at h
    rcases h with h | h
    · subst h; split <;> decide
    · exact hn _ _ h
  · exact ho g t h

theorem decode_encode (φ : Qbf) : Qbf.decode φ.encode = φ := by
  have h1 : ofBits φ.encode = φ.toks := ofBits_toBits _ (toks_lt_16 φ)
  unfold Qbf.decode
  rw [h1]
  obtain ⟨qs, m⟩ := φ
  exact decode_quants qs m _ (by simp [Qbf.toks])

end Complexity
