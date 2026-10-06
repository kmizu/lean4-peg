import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# Cutting the input bits into tokens on stacks

The input of the stack machine (`nInit`) is the bit list `w` on stack `0`, first bit on top. `tokenizeP` turns it into
the first state of the reading machine, `enc (pinit (ofBits w))` (`tokenizeP_runs`):

1. push the constants of `pinit` (`CTL = [14]`, `CUR`, `NB` and the four table counts `0`);
2. read the bits four at a time from the top of stack `0`, adding `8`, `4`, `2`, `1` for each `1` bit to a number on
   top of the scratch stack `18`; a group cut short by the end of the input is dropped (its partial number popped),
   so stack `18` ends up holding `ofBits w`, first token at the bottom;
3. move stack `18` onto `TK` (which reverses it, putting the first token on top).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-! ## The program -/

/-- The scratch stack where the tokens are collected. -/
abbrev tokz_ACC : Fin NK := 18

/-- Add `c + 1` to the top of `i`. -/
def tokz_incs (i : Fin NK) : Nat → NProg NK
  | 0 => .prim (.inc i)
  | c + 1 => .seq (.prim (.inc i)) (tokz_incs i c)

/-- Read one bit (popped from stack `0`); for a `1` add `c + 1` to the token on top of the scratch stack. -/
def tokz_bit (c : Nat) : NProg NK :=
  .ite 0 .zero (.prim (.pop 0)) (.seq (.prim (.pop 0)) (tokz_incs tokz_ACC c))

/-- Drop the partial token (the input ended inside a group). -/
def tokz_drop : NProg NK := .prim (.pop tokz_ACC)

/-- If a bit is left, read it (weight `c + 1`) and go on with `k`; otherwise drop the partial token. -/
def tokz_rd (c : Nat) (k : NProg NK) : NProg NK := .ite 0 .nonempty (.seq (tokz_bit c) k) tokz_drop

/-- One group of four bits: start a token at `0`, then the bits of weights `8`, `4`, `2`, `1`. -/
def tokz_group : NProg NK :=
  .seq (.prim (.pushZ tokz_ACC)) (tokz_rd 7 (tokz_rd 3 (tokz_rd 1 (.ite 0 .nonempty (tokz_bit 0) tokz_drop))))

/-- All groups. -/
def tokz_loop : NProg NK := .loop 0 .nonempty tokz_group

/-- The constants of the first reading state. -/
def tokz_consts : NProg NK :=
  .seq (npushC CTL 14) (.seq (npushC CUR 0) (.seq (npushC NB 0) (.seq (npushC NTT 0)
    (.seq (npushC NCT 0) (.seq (npushC NLT 0) (npushC NRT 0))))))

/-- Turn the input bits into the first state of the reading machine. -/
def tokenizeP : NProg NK := .seq tokz_consts (.seq tokz_loop (nmvAll tokz_ACC TK (by decide)))

/-! ## The states -/

/-- No stack holds anything. -/
def tokz_E : Lists NK := fun _ => []

/-- Only the constants of `pinit` are pushed. -/
def tokz_P : Lists NK :=
  ((((((tokz_E.set CTL [14]).set CUR [0]).set NB [0]).set NTT [0]).set NCT [0]).set NLT [0]).set NRT [0]

theorem tokz_P_eq : tokz_P = enc (pinit []) := by
  funext i; revert i; decide

/-- The constants, the bits left `a` on stack `0`, the tokens `acc` on stack `18`. -/
def tokz_St (a acc : List Nat) : Lists NK := (tokz_P.set 0 a).set tokz_ACC acc

theorem tokz_St_0 (a acc : List Nat) : tokz_St a acc 0 = a := by
  simp (config := { decide := true }) [tokz_St, Lists.set]

theorem tokz_St_18 (a acc : List Nat) : tokz_St a acc tokz_ACC = acc := by
  simp [tokz_St]

theorem tokz_St_set0 (a acc a' : List Nat) : (tokz_St a acc).set 0 a' = tokz_St a' acc := by
  simp only [tokz_St]
  rw [Lists.set_comm (by decide : tokz_ACC ≠ 0), Lists.set_set_u]

theorem tokz_St_set18 (a acc acc' : List Nat) : (tokz_St a acc).set tokz_ACC acc' = tokz_St a acc' := by
  simp only [tokz_St, Lists.set_set_u]

/-! ## Reading one bit -/

theorem tokz_incs_runs (i : Fin NK) (S : Lists NK) {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    ∀ c, NRuns (tokz_incs i c) S (S.set i (l ++ [v + c + 1])) (c + 1)
  | 0 => nruns_inc i S h
  | c + 1 => by
    have x₁ := nruns_inc i S h
    have x₂ := tokz_incs_runs i (S.set i (l ++ [v + 1])) (l := l) (v := v + 1) (by simp) c
    rw [Lists.set_set_u] at x₂
    rw [show v + (c + 1) + 1 = v + 1 + c + 1 by omega]
    exact (x₁.seq x₂).mono (by omega)

/-- The value a bit adds with weight `c + 1`. -/
def tokz_w (c : Nat) (b : Bool) : Nat := if b then c + 1 else 0

theorem tokz_bit_runs (c : Nat) (A acc : List Nat) (v : Nat) (b : Bool) :
    NRuns (tokz_bit c) (tokz_St (A ++ [bitElem b]) (acc ++ [v])) (tokz_St A (acc ++ [v + tokz_w c b])) (c + 3) := by
  cases b
  · have x₁ := nruns_pop 0 (tokz_St (A ++ [bitElem false]) (acc ++ [v])) (l := A) (v := 0)
      (by rw [tokz_St_0]; rfl)
    rw [tokz_St_set0] at x₁
    simp only [tokz_w]
    exact (x₁.iteT (by rw [tokz_St_0]; exact eval_zero_zero _)).mono (by omega)
  · have x₁ := nruns_pop 0 (tokz_St (A ++ [bitElem true]) (acc ++ [v])) (l := A) (v := 1)
      (by rw [tokz_St_0]; rfl)
    rw [tokz_St_set0] at x₁
    have x₂ := tokz_incs_runs tokz_ACC (tokz_St A (acc ++ [v])) (l := acc) (v := v) (tokz_St_18 _ _) c
    rw [tokz_St_set18] at x₂
    simp only [tokz_w, if_true]
    rw [show v + (c + 1) = v + c + 1 by omega]
    exact ((x₁.seq x₂).iteF (by rw [tokz_St_0]; exact eval_zero_succ _ 0)).mono (by omega)

theorem tokz_drop_runs (acc : List Nat) (v : Nat) :
    NRuns tokz_drop (tokz_St [] (acc ++ [v])) (tokz_St [] acc) 1 := by
  have x := nruns_pop tokz_ACC (tokz_St [] (acc ++ [v])) (l := acc) (v := v) (tokz_St_18 _ _)
  rwa [tokz_St_set18] at x

theorem tokz_ne_snoc (A acc : List Nat) (e : Nat) : NTest.nonempty.eval (tokz_St (A ++ [e]) acc 0) = true := by
  rw [tokz_St_0]; exact eval_nonempty_snoc _ _

theorem tokz_ne_nil (acc : List Nat) : NTest.nonempty.eval (tokz_St [] acc 0) = false := by
  rw [tokz_St_0]; rfl

theorem tokz_pushZ_runs (a acc : List Nat) :
    NRuns (.prim (.pushZ tokz_ACC)) (tokz_St a acc) (tokz_St a (acc ++ [0])) 1 := by
  have x := nruns_pushZ tokz_ACC (tokz_St a acc)
  rwa [tokz_St_18, tokz_St_set18] at x

/-! ## One group -/

/-- The bits as they lie on stack `0` (first bit on top). -/
def tokz_bits (bs : List Bool) : List Nat := (bs.map bitElem).reverse

theorem tokz_bits_cons (b : Bool) (bs : List Bool) : tokz_bits (b :: bs) = tokz_bits bs ++ [bitElem b] := by
  simp [tokz_bits]

theorem tokz_tok (b₃ b₂ b₁ b₀ : Bool) :
    0 + tokz_w 7 b₃ + tokz_w 3 b₂ + tokz_w 1 b₁ + tokz_w 0 b₀ = bitsTok b₃ b₂ b₁ b₀ := by
  cases b₃ <;> cases b₂ <;> cases b₁ <;> cases b₀ <;> rfl

theorem tokz_group_full (b₃ b₂ b₁ b₀ : Bool) (rest : List Bool) (acc : List Nat) :
    NRuns tokz_group (tokz_St (tokz_bits (b₃ :: b₂ :: b₁ :: b₀ :: rest)) acc)
      (tokz_St (tokz_bits rest) (acc ++ [bitsTok b₃ b₂ b₁ b₀])) 28 := by
  simp only [tokz_bits_cons]
  have x₀ := tokz_pushZ_runs (tokz_bits rest ++ [bitElem b₀] ++ [bitElem b₁] ++ [bitElem b₂] ++ [bitElem b₃]) acc
  have x₃ := tokz_bit_runs 7 (tokz_bits rest ++ [bitElem b₀] ++ [bitElem b₁] ++ [bitElem b₂]) acc 0 b₃
  have x₂ := tokz_bit_runs 3 (tokz_bits rest ++ [bitElem b₀] ++ [bitElem b₁]) acc (0 + tokz_w 7 b₃) b₂
  have x₁ := tokz_bit_runs 1 (tokz_bits rest ++ [bitElem b₀]) acc (0 + tokz_w 7 b₃ + tokz_w 3 b₂) b₁
  have x₄ := tokz_bit_runs 0 (tokz_bits rest) acc (0 + tokz_w 7 b₃ + tokz_w 3 b₂ + tokz_w 1 b₁) b₀
  rw [tokz_tok] at x₄
  have y₄ := x₄.iteT (q := tokz_drop) (by exact tokz_ne_snoc _ _ _)
  have y₁ := (x₁.seq y₄).iteT (q := tokz_drop) (by exact tokz_ne_snoc _ _ _)
  have y₂ := (x₂.seq y₁).iteT (q := tokz_drop) (by exact tokz_ne_snoc _ _ _)
  have y₃ := (x₃.seq y₂).iteT (q := tokz_drop) (by exact tokz_ne_snoc _ _ _)
  exact (x₀.seq y₃).mono (by omega)

theorem tokz_group_one (b : Bool) (acc : List Nat) :
    NRuns tokz_group (tokz_St (tokz_bits [b]) acc) (tokz_St [] acc) 28 := by
  have e : tokz_bits [b] = [] ++ [bitElem b] := rfl
  rw [e]
  have x₀ := tokz_pushZ_runs ([] ++ [bitElem b]) acc
  have x₁ := tokz_bit_runs 7 [] acc 0 b
  have d := tokz_drop_runs acc (0 + tokz_w 7 b)
  have y := (x₁.seq (d.iteF (p := .seq (tokz_bit 3) (tokz_rd 1 (.ite 0 .nonempty (tokz_bit 0) tokz_drop)))
    (tokz_ne_nil _))).iteT (q := tokz_drop) (tokz_ne_snoc _ _ _)
  exact (x₀.seq y).mono (by omega)

theorem tokz_group_two (b b' : Bool) (acc : List Nat) :
    NRuns tokz_group (tokz_St (tokz_bits [b, b']) acc) (tokz_St [] acc) 28 := by
  have e : tokz_bits [b, b'] = [] ++ [bitElem b'] ++ [bitElem b] := rfl
  rw [e]
  have x₀ := tokz_pushZ_runs ([] ++ [bitElem b'] ++ [bitElem b]) acc
  have x₁ := tokz_bit_runs 7 ([] ++ [bitElem b']) acc 0 b
  have x₂ := tokz_bit_runs 3 [] acc (0 + tokz_w 7 b) b'
  have d := tokz_drop_runs acc (0 + tokz_w 7 b + tokz_w 3 b')
  have y₂ := (x₂.seq (d.iteF (p := .seq (tokz_bit 1) (.ite 0 .nonempty (tokz_bit 0) tokz_drop))
    (tokz_ne_nil _))).iteT (q := tokz_drop) (tokz_ne_snoc _ _ _)
  have y₁ := (x₁.seq y₂).iteT (q := tokz_drop) (tokz_ne_snoc _ _ _)
  exact (x₀.seq y₁).mono (by omega)

theorem tokz_group_three (b b' b'' : Bool) (acc : List Nat) :
    NRuns tokz_group (tokz_St (tokz_bits [b, b', b'']) acc) (tokz_St [] acc) 28 := by
  have e : tokz_bits [b, b', b''] = [] ++ [bitElem b''] ++ [bitElem b'] ++ [bitElem b] := rfl
  rw [e]
  have x₀ := tokz_pushZ_runs ([] ++ [bitElem b''] ++ [bitElem b'] ++ [bitElem b]) acc
  have x₁ := tokz_bit_runs 7 ([] ++ [bitElem b''] ++ [bitElem b']) acc 0 b
  have x₂ := tokz_bit_runs 3 ([] ++ [bitElem b'']) acc (0 + tokz_w 7 b) b'
  have x₃ := tokz_bit_runs 1 [] acc (0 + tokz_w 7 b + tokz_w 3 b') b''
  have d := tokz_drop_runs acc (0 + tokz_w 7 b + tokz_w 3 b' + tokz_w 1 b'')
  have y₃ := (x₃.seq (d.iteF (p := tokz_bit 0) (tokz_ne_nil _))).iteT (q := tokz_drop) (tokz_ne_snoc _ _ _)
  have y₂ := (x₂.seq y₃).iteT (q := tokz_drop) (tokz_ne_snoc _ _ _)
  have y₁ := (x₁.seq y₂).iteT (q := tokz_drop) (tokz_ne_snoc _ _ _)
  exact (x₀.seq y₁).mono (by omega)

/-! ## All groups -/

/-- One more round of a loop. -/
theorem tokz_loop_step {i : Fin NK} {c : NTest} {p : NProg NK} {S S₁ S₂ : Lists NK} {T₁ T₂ : Nat}
    (hc : c.eval (S i) = true) (h₁ : NRuns p S S₁ T₁) (h₂ : NRuns (.loop i c p) S₁ S₂ T₂) :
    NRuns (.loop i c p) S S₂ (T₁ + 1 + T₂) :=
  let ⟨t₁, ht₁, x₁⟩ := h₁; let ⟨t₂, ht₂, x₂⟩ := h₂; ⟨t₁ + 1 + t₂, by omega, .loopC trivial hc x₁ x₂⟩

theorem tokz_loop_runs : ∀ (bs : List Bool) (acc : List Nat),
    NRuns tokz_loop (tokz_St (tokz_bits bs) acc) (tokz_St [] (acc ++ ofBits bs)) (8 * bs.length + 30) ∧
      (ofBits bs).length ≤ bs.length
  | b₃ :: b₂ :: b₁ :: b₀ :: rest, acc => by
    obtain ⟨ih, hl⟩ := tokz_loop_runs rest (acc ++ [bitsTok b₃ b₂ b₁ b₀])
    have hs : tokz_bits (b₃ :: b₂ :: b₁ :: b₀ :: rest) = (tokz_bits rest ++ [bitElem b₀, bitElem b₁, bitElem b₂]) ++
        [bitElem b₃] := by simp [tokz_bits]
    have x := tokz_loop_step (i := 0) (c := .nonempty) (by rw [hs]; exact tokz_ne_snoc _ _ _)
      (tokz_group_full b₃ b₂ b₁ b₀ rest acc) ih
    simp only [ofBits, List.length_cons]
    refine ⟨?_, by omega⟩
    rw [show acc ++ bitsTok b₃ b₂ b₁ b₀ :: ofBits rest = acc ++ [bitsTok b₃ b₂ b₁ b₀] ++ ofBits rest by simp]
    exact x.mono (by omega)
  | [], acc => by
    simp only [ofBits, List.append_nil, List.length_nil]
    exact ⟨(nruns_loop_exit (tokz_ne_nil acc)).mono (by omega), Nat.le_refl _⟩
  | [b], acc => by
    simp only [ofBits, List.append_nil, List.length_cons, List.length_nil]
    refine ⟨?_, by omega⟩
    exact (tokz_loop_step (i := 0) (c := .nonempty) (by exact tokz_ne_snoc [] acc _) (tokz_group_one b acc)
      (nruns_loop_exit (tokz_ne_nil acc))).mono (by omega)
  | [b, b'], acc => by
    simp only [ofBits, List.append_nil, List.length_cons, List.length_nil]
    refine ⟨?_, by omega⟩
    exact (tokz_loop_step (i := 0) (c := .nonempty) (by exact tokz_ne_snoc ([] ++ [bitElem b']) acc _)
      (tokz_group_two b b' acc) (nruns_loop_exit (tokz_ne_nil acc))).mono (by omega)
  | [b, b', b''], acc => by
    simp only [ofBits, List.append_nil, List.length_cons, List.length_nil]
    refine ⟨?_, by omega⟩
    exact (tokz_loop_step (i := 0) (c := .nonempty)
      (by exact tokz_ne_snoc ([] ++ [bitElem b''] ++ [bitElem b']) acc _)
      (tokz_group_three b b' b'' acc) (nruns_loop_exit (tokz_ne_nil acc))).mono (by omega)

/-! ## The constants and the end -/

theorem tokz_pushC_empty (i : Fin NK) (S : Lists NK) (h : S i = []) (c : Nat) :
    NRuns (npushC i c) S (S.set i [c]) (c + 1) := by
  have x := nruns_pushC i S c
  rwa [h, List.nil_append] at x

theorem tokz_consts_runs (a : List Nat) :
    NRuns tokz_consts (tokz_E.set 0 a) (tokz_P.set 0 a) 21 := by
  let S₀ := tokz_E.set 0 a
  have x₁ := tokz_pushC_empty CTL S₀ (by simp (config := { decide := true }) [S₀, Lists.set, tokz_E]) 14
  let S₁ := S₀.set CTL [14]
  have x₂ := tokz_pushC_empty CUR S₁ (by simp (config := { decide := true }) [S₁, S₀, Lists.set, tokz_E]) 0
  let S₂ := S₁.set CUR [0]
  have x₃ := tokz_pushC_empty NB S₂ (by simp (config := { decide := true }) [S₂, S₁, S₀, Lists.set, tokz_E]) 0
  let S₃ := S₂.set NB [0]
  have x₄ := tokz_pushC_empty NTT S₃ (by simp (config := { decide := true }) [S₃, S₂, S₁, S₀, Lists.set, tokz_E]) 0
  let S₄ := S₃.set NTT [0]
  have x₅ := tokz_pushC_empty NCT S₄ (by simp (config := { decide := true }) [S₄, S₃, S₂, S₁, S₀, Lists.set, tokz_E]) 0
  let S₅ := S₄.set NCT [0]
  have x₆ := tokz_pushC_empty NLT S₅ (by simp (config := { decide := true }) [S₅, S₄, S₃, S₂, S₁, S₀, Lists.set, tokz_E]) 0
  let S₆ := S₅.set NLT [0]
  have x₇ := tokz_pushC_empty NRT S₆ (by simp (config := { decide := true }) [S₆, S₅, S₄, S₃, S₂, S₁, S₀, Lists.set, tokz_E]) 0
  have e : (((((((tokz_E.set 0 a).set CTL [14]).set CUR [0]).set NB [0]).set NTT [0]).set NCT [0]).set NLT [0]).set
      NRT [0] = tokz_P.set 0 a := by
    funext x
    by_cases h0 : x = 0
    · subst h0; simp (config := { decide := true }) [Lists.set]
    · simp (config := { decide := true }) [Lists.set, tokz_P, h0]
  rw [e] at x₇
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq x₇)))))).mono (by omega)

theorem tokz_init (w : List Bool) : nInit NK w = tokz_E.set 0 (tokz_bits w) := by
  funext x
  simp only [nInit, Lists.set, tokz_E, tokz_bits]
  by_cases h : x = 0
  · subst h; simp
  · have : x.val ≠ 0 := fun e => h (Fin.ext e)
    simp [h, this]

theorem tokz_final (tk : List Nat) :
    (((tokz_St [] tk).set TK (tokz_St [] tk TK ++ (tokz_St [] tk tokz_ACC).reverse)).set tokz_ACC []) =
      enc (pinit tk) := by
  have e : enc (pinit tk) = (enc (pinit [])).set TK tk.reverse := enc_with_tk (pinit []) tk
  rw [e, ← tokz_P_eq, tokz_St_18]
  have h1 : tokz_St [] tk TK = [] := by simp (config := { decide := true }) [tokz_St, Lists.set, tokz_P, tokz_E]
  rw [h1, List.nil_append]
  funext x
  by_cases hA : x = tokz_ACC
  · subst hA; simp (config := { decide := true }) [Lists.set, tokz_P, tokz_E]
  · by_cases hT : x = TK
    · subst hT; simp (config := { decide := true }) [Lists.set]
    · by_cases h0 : x = 0
      · subst h0; simp (config := { decide := true }) [Lists.set, tokz_St, tokz_P, tokz_E]
      · simp (config := { decide := true }) [Lists.set, tokz_St, hA, hT, h0]

/-! ## The whole program -/

theorem tokenizeP_runs (w : List Bool) :
    NRuns tokenizeP (nInit NK w) (enc (pinit (ofBits w))) (100 * (w.length + 1)) := by
  have x₁ := tokz_consts_runs (tokz_bits w)
  have e₁ : tokz_P.set 0 (tokz_bits w) = tokz_St (tokz_bits w) [] := by
    simp only [tokz_St]
    have : (tokz_P.set 0 (tokz_bits w)) tokz_ACC = [] := by simp (config := { decide := true }) [Lists.set, tokz_P, tokz_E]
    rw [← this, Lists.set_get_self]
  rw [e₁, ← tokz_init] at x₁
  obtain ⟨x₂, hl⟩ := tokz_loop_runs w []
  rw [List.nil_append] at x₂
  have x₃ := nruns_mvAll tokz_ACC TK (by decide) (tokz_St [] (ofBits w))
  rw [tokz_final] at x₃
  have hc : 3 * (tokz_St [] (ofBits w) tokz_ACC).length + 1 ≤ 3 * w.length + 1 := by
    rw [tokz_St_18]; omega
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

end Shallot.MacroPeg.Mach
