import MacroPeg.CBV.SequentialStackCodecBound

namespace Shallot.MacroPeg.CBV.SequentialStackBinary

open SequentialStack SequentialStackCodec SequentialStackCodecBound CBVtoCBN

/-- Little-endian words with an explicit width, including leading zero bits. -/
def word : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, n => decide (n % 2 = 1) :: word w (n / 2)

def unword : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * unword bs

theorem word_length (w n : Nat) : (word w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [word, ih]

theorem unword_word {w n : Nat} (h : n < 2 ^ w) : unword (word w n) = n := by
  induction w generalizing n with
  | zero =>
    simp only [Nat.pow_zero] at h
    have hn : n = 0 := by omega
    subst n
    rfl
  | succ w ih =>
    have hd : n / 2 < 2 ^ w := by rw [Nat.pow_succ] at h; omega
    simp only [word, unword, ih hd]
    have hm := Nat.mod_lt n (by decide : 0 < 2)
    split <;> simp_all <;> omega

def pack (w : Nat) (ns : List Nat) : List Bool := ns.flatMap (word w)

theorem pack_length (w : Nat) (ns : List Nat) : (pack w ns).length = ns.length * w := by
  induction ns with
  | nil => simp [pack]
  | cons n ns ih =>
    change (word w n ++ pack w ns).length = (ns.length + 1) * w
    rw [List.length_append, word_length, ih, Nat.add_mul]
    omega

/-- The count is computed from the bit stream's length by `unpack`. -/
def readWords (w : Nat) : Nat → List Bool → Option (List Nat × List Bool)
  | 0, rest => some ([], rest)
  | k + 1, input => do
    if input.length < w then none else
      let (ns, rest) ← readWords w k (input.drop w)
      pure (unword (input.take w) :: ns, rest)

theorem readWords_pack (w : Nat) (ns : List Nat)
    (h : ∀ n ∈ ns, n < 2 ^ w) (tail : List Bool) :
    readWords w ns.length (pack w ns ++ tail) = some (ns, tail) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht : ∀ v ∈ ns, v < 2 ^ w := fun v hv => h v (by simp [hv])
    have hl : ¬ (word w n ++ (pack w ns ++ tail)).length < w := by
      simp only [List.length_append, word_length]; omega
    simp only [List.length_cons, pack, List.flatMap_cons, List.append_assoc, readWords]
    change (if (word w n ++ (pack w ns ++ tail)).length < w then none else _) = _
    rw [if_neg hl]
    have hd : (word w n ++ (pack w ns ++ tail)).drop w = pack w ns ++ tail := by
      simpa only [word_length] using (List.drop_left (l₁ := word w n) (l₂ := pack w ns ++ tail))
    have htake : (word w n ++ (pack w ns ++ tail)).take w = word w n := by
      simpa only [word_length] using (List.take_left (l₁ := word w n) (l₂ := pack w ns ++ tail))
    change (readWords w ns.length ((word w n ++ (pack w ns ++ tail)).drop w)).bind
      (fun pair => some (unword ((word w n ++ (pack w ns ++ tail)).take w) :: pair.1, pair.2)) = _
    rw [hd, htake, unword_word hn]
    change (readWords w ns.length (pack w ns ++ tail)).bind
      (fun pair => some (n :: pair.1, pair.2)) = some (n :: ns, tail)
    rw [ih ht]
    rfl

def unpack (w : Nat) (input : List Bool) : Option (List Nat) := do
  if w = 0 ∨ input.length % w ≠ 0 then none else
    let (ns, rest) ← readWords w (input.length / w) input
    if rest.isEmpty then some ns else none

theorem unpack_pack {w : Nat} (hw : 0 < w) (ns : List Nat)
    (h : ∀ n ∈ ns, n < 2 ^ w) : unpack w (pack w ns) = some ns := by
  have hr := readWords_pack w ns h []
  simp only [List.append_nil] at hr
  simp [unpack, pack_length, Nat.ne_of_gt hw, Nat.mul_div_cancel _ hw, hr]

def encodeBits (ns : List CompileNode) (w : Nat) (c : Config) : List Bool :=
  pack w (encode ns c)

def decodeBits (ns : List CompileNode) (w : Nat) (input : List Bool) : Option Config := do
  let code ← unpack w input
  decode ns code

/-- The width uses a proved bound, not an unencoded runtime state field. -/
noncomputable def width (g : MGrammar) (x : List Char) (e : MExp) : Nat :=
  (numberBound g x e).log2 + 1

theorem reachable_roundtrip (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    decodeBits (compilerNodes g e) (width g x e)
      (encodeBits (compilerNodes g e) (width g x e) c) = some c := by
  have hn := reachable_numbers g x e c h
  have hb : ∀ n ∈ encode (compilerNodes g e) c, n < 2 ^ width g x e := by
    intro n hm
    exact Nat.lt_of_le_of_lt (hn n hm) Nat.lt_log2_self
  simp only [decodeBits, encodeBits, unpack_pack (by unfold width; omega) _ hb]
  exact SequentialStackCodec.reachable_roundtrip g x e c h

theorem reachable_length (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encodeBits (compilerNodes g e) (width g x e) c).length ≤
      ((SequentialStackRank.initialCap g x e + 1) * (7 + 3 * SequentialStackPayload.arityBudget g)) *
        ((numberBound g x e).log2 + 1) := by
  rw [encodeBits, pack_length]
  exact Nat.mul_le_mul_right _ (SequentialStackCodecBound.reachable_length g x e c h)

/-- Constants depend on the fixed source program only. -/
noncomputable def cellCoefficient (g : MGrammar) (e : MExp) : Nat :=
  (((g.rules.length + 1) * SequentialStackRank.codeBudget g) + sizeOf e + 1) *
    (7 + 3 * SequentialStackPayload.arityBudget g)

noncomputable def numberCoefficient (g : MGrammar) (e : MExp) : Nat :=
  ((g.rules.length + 1) * SequentialStackRank.codeBudget g) + sizeOf e +
    (g.rules.length + 1) + 1 + SequentialStackPayload.arityBudget g +
    (SequentialStackPool.exprPool (compilerNodes g e)).length + g.rules.length + 8

theorem numberBound_linear (g : MGrammar) (x : List Char) (e : MExp) :
    numberBound g x e ≤ numberCoefficient g e * (x.length + 1) := by
  let C := (g.rules.length + 1) * SequentialStackRank.codeBudget g + (g.rules.length + 1) + 1
  let D := sizeOf e + SequentialStackPayload.arityBudget g +
    (SequentialStackPool.exprPool (compilerNodes g e)).length + g.rules.length + 8
  have hd : D ≤ D * (x.length + 1) := Nat.le_mul_of_pos_right D (by omega)
  have hf : numberBound g x e + 1 = C * (x.length + 1) + D := by
    dsimp [numberBound, SequentialStackRank.initialCap, SequentialClock.positionClock, C, D]
    rw [Nat.mul_right_comm (g.rules.length + 1) (x.length + 1) (SequentialStackRank.codeBudget g)]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hc : numberCoefficient g e = C + D := by dsimp [numberCoefficient, C, D]; omega
  rw [hc, Nat.add_mul]
  omega

theorem log2_linear {B K t : Nat} (ht : 0 < t) (h : B ≤ K * t) :
    B.log2 + 1 ≤ t.log2 + K.log2 + 2 := by
  by_cases hb : B = 0
  · simp only [hb, Nat.log2_zero]; omega
  have hp : K * t < (2 ^ (K.log2 + 1)) * (2 ^ (t.log2 + 1)) := by
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self ht)
      (Nat.mul_le_mul_left _ (Nat.le_of_lt Nat.lt_log2_self))
  have hp' : B < 2 ^ (t.log2 + K.log2 + 2) := by
    have he : K.log2 + 1 + (t.log2 + 1) = t.log2 + K.log2 + 2 := by omega
    rw [← Nat.pow_add, he] at hp
    exact Nat.lt_of_le_of_lt h hp
  have := (Nat.log2_lt hb).mpr hp'
  omega

/-- A concrete bit bound of the form C(n+1)(log₂(n+1)+D), including all
state fields and headers. This does not bound transition workspace. -/
theorem reachable_bit_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encodeBits (compilerNodes g e) (width g x e) c).length ≤
      (cellCoefficient g e * (x.length + 1)) *
        ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  have hs : (SequentialStackRank.initialCap g x e + 1) *
      (7 + 3 * SequentialStackPayload.arityBudget g) ≤ cellCoefficient g e * (x.length + 1) := by
    have he : sizeOf e + 1 ≤ (sizeOf e + 1) * (x.length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    unfold SequentialStackRank.initialCap SequentialClock.positionClock cellCoefficient
    rw [Nat.mul_right_comm (g.rules.length + 1) (x.length + 1) (SequentialStackRank.codeBudget g)]
    rw [Nat.mul_right_comm _ (7 + 3 * SequentialStackPayload.arityBudget g) (x.length + 1)]
    apply Nat.mul_le_mul_right
    simp only [Nat.add_mul, Nat.one_mul] at he ⊢
    omega
  exact Nat.le_trans (reachable_length g x e c h)
    (Nat.mul_le_mul hs (log2_linear (by omega) (numberBound_linear g x e)))

def stepBits (g : MGrammar) (x : List Char) (ns : List CompileNode) (w : Nat)
    (input : List Bool) : Option (List Bool) := do
  let c ← decodeBits ns w input
  let next ← step g x c
  pure (encodeBits ns w next)

theorem stepBits_correct (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    stepBits g x (compilerNodes g e) (width g x e)
      (encodeBits (compilerNodes g e) (width g x e) c) =
        (step g x c).map (encodeBits (compilerNodes g e) (width g x e)) := by
  simp only [stepBits, reachable_roundtrip g x e c h]
  change (step g x c).bind (fun next => some (encodeBits (compilerNodes g e) (width g x e) next)) = _
  cases step g x c <;> rfl

theorem stepBits_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) (output : List Bool)
    (hs : stepBits g x (compilerNodes g e) (width g x e)
      (encodeBits (compilerNodes g e) (width g x e) c) = some output) :
    output.length ≤ (cellCoefficient g e * (x.length + 1)) *
      ((x.length + 1).log2 + (numberCoefficient g e).log2 + 2) := by
  rw [stepBits_correct g x e c h] at hs
  cases ht : step g x c with
  | none => simp [ht] at hs
  | some next =>
    simp only [ht, Option.map_some, Option.some.injEq] at hs
    rw [← hs]
    exact reachable_bit_bound g x e next (h.trans (.single ht))

end Shallot.MacroPeg.CBV.SequentialStackBinary
