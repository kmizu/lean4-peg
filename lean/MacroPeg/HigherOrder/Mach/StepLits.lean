import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# One step of the reading machine on stacks: the literal tokens

The tokens `2` (a character), `3` (a range of characters) and `4` (a string) of an expression emit a leaf item
`⟨tag, a, b, cur⟩` whose numbers are read from the tokens, and push the type `0` (a parser). The string of token `4`
is also added to the literal table.

The programs read the codes onto the scratch stacks `18` (`a`) and `24` (`b`), then emit the leaf (`leafOutP`).
The scratch stacks `19`–`23` are used by the character checks.
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.Flat

/-! ## Names of the scratch stacks -/

abbrev SA : Fin NK := 18
abbrev SB : Fin NK := 24
abbrev SC : Fin NK := 19
abbrev ST : Fin NK := 20
abbrev SU : Fin NK := 21
abbrev SG : Fin NK := 22
abbrev SF : Fin NK := 23

/-- Read a character code from the tokens onto `x`. -/
def charP (x : Fin NK) (hx : x ≠ ST) : NProg NK := parseCharP TK x SC ST SU SG SF hx (by decide)

/-! ## The cost bound -/

/-- The base of the cost bound, kept opaque so that `omega` never sees the large literal inside a product. -/
def tkM (N : Nat) : Nat := N + 1114113

theorem chB_eq (N : Nat) : chB N = tkM N * tkM N := rfl

theorem litFrameCost_eq (N : Nat) : frameCost N = 100 * (chB N * tkM N) := rfl

/-- Two character reads and one string read fit into `frameCost N`. -/
theorem tokCost_le {L N : Nat} (h : L ≤ N) :
    2 * (6 * L + 6 + charCost L) + strCost L + 100 ≤ frameCost N := by
  have hc : charCost L ≤ 10 * chB N + 10 := by rw [← charCost_eq]; exact charCost_mono h
  have hX : N + 1114113 = tkM N := rfl
  have hXB : tkM N ≤ chB N := by rw [chB_eq]; exact Nat.le_mul_of_pos_left _ (by unfold tkM; omega)
  have hBP : chB N ≤ chB N * tkM N := Nat.le_mul_of_pos_right _ (by unfold tkM; omega)
  have hs : strCost L ≤ tkM N * (16 * chB N) := by
    unfold strCost
    exact Nat.mul_le_mul (by omega) (by omega)
  have e : tkM N * (16 * chB N) = 16 * (chB N * tkM N) := by
    rw [Nat.mul_left_comm, Nat.mul_comm (tkM N)]
  rw [litFrameCost_eq]
  have := chB_big N
  omega

/-! ## Token programs and `readExpr` -/

theorem litTokOK_run {p : NProg NK} {s : PSt} {K r : List Nat} {T : Nat} {s' : PSt} (he : readExpr s K = s')
    (h : NRuns p (enc { s with ctl := K, tk := r }) (enc s') T) (hok : s'.ok = s.ok) (hs : s.ok = true) :
    TokOK p s K r T :=
  ⟨fun _ => he ▸ h, fun hf => by rw [he, hok, hs] at hf; cases hf⟩

theorem litTokOK_halt {p : NProg NK} {s : PSt} {K r : List Nat} {T : Nat} (he : readExpr s K = s.fail)
    (h : ∃ S', NHalts p (enc { s with ctl := K, tk := r }) false S' T) : TokOK p s K r T :=
  ⟨fun ht => absurd ht (by rw [he]; simp (config := { decide := true }) [PSt.fail]), fun _ => h⟩

/-! ## Emitting a leaf -/

/-- Emit the item `⟨tag, a, b, cur⟩` with `a` on `SA` and `b` on `SB`, and push the type `0`. -/
def leafOutP (tag : Nat) : NProg NK :=
  .seq (npushC OUT tag) (.seq (nmv SA OUT (by decide)) (.seq (nmv SB OUT (by decide))
    (.seq (.prim (.dup CUR OUT (by decide))) (.prim (.pushZ TY)))))

theorem leafOutP_runs (t : PSt) (tag a b : Nat) :
    NRuns (leafOutP tag) (((enc t).set SA [a]).set SB [b])
      (enc { t with ty := 0 :: t.ty, out := ⟨tag, a, b, t.cur⟩ :: t.out }) (tag + 7) := by
  have hA : enc t SA = [] := enc_scratch t SA (by decide)
  have hB : enc t SB = [] := enc_scratch t SB (by decide)
  let S₀ := ((enc t).set SA [a]).set SB [b]
  have x₁ := nruns_pushC OUT S₀ tag
  let S₁ := S₀.set OUT (S₀ OUT ++ [tag])
  have x₂ := nruns_mv SA OUT (by decide) S₁ (l := []) (v := a) (by simp (config := { decide := true }) [S₁, S₀, Lists.set])
  let S₂ := (S₁.set OUT (S₁ OUT ++ [a])).set SA []
  have x₃ := nruns_mv SB OUT (by decide) S₂ (l := []) (v := b) (by simp (config := { decide := true }) [S₂, S₁, S₀, Lists.set])
  let S₃ := (S₂.set OUT (S₂ OUT ++ [b])).set SB []
  have x₄ := nruns_dup CUR OUT (by decide) S₃ (l := []) (v := t.cur) (by simp (config := { decide := true }) [S₃, S₂, S₁, S₀, Lists.set]; rfl)
  let S₄ := S₃.set OUT (S₃ OUT ++ [t.cur])
  have x₅ := nruns_pushZ TY S₄
  have e : S₄.set TY (S₄ TY ++ [0]) = enc { t with ty := 0 :: t.ty, out := ⟨tag, a, b, t.cur⟩ :: t.out } := by
    rw [enc_with_out { t with ty := 0 :: t.ty } _, enc_with_ty t _]
    funext x
    by_cases h3 : x = TY
    · subst h3; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, S₀, Lists.set, enc_ty]
    by_cases h4 : x = OUT
    · subst h4; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, S₀, Lists.set, enc_out, encItems, encItem]
    by_cases h18 : x = SA
    · subst h18; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, S₀, Lists.set, hA]
    by_cases h24 : x = SB
    · subst h24; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, S₀, Lists.set, hB]
    simp (config := { decide := true }) [S₄, S₃, S₂, S₁, S₀, Lists.set, h3, h4, h18, h24]
  rw [e] at x₅
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (by omega)

/-! ## Reading a character onto the scratch stacks -/

/-- Read a character code from the tokens (on `TK` of `B`) onto the stack `x` of `S`, which is `B` but for `x`. -/
theorem charP_ok (x : Fin NK) (hx : x ≠ ST) (hd : [TK, x, SC, ST, SU, SG, SF].Nodup) (B S : Lists NK)
    (hS : S = B.set x (S x)) (hx1 : x ≠ TK) {r r₁ : List Nat} {c : Char} (hT : B TK = r.reverse)
    (hp : parseChar r = some (c, r₁)) :
    NRuns (charP x hx) S ((B.set TK r₁.reverse).set x (S x ++ [c.toNat])) (6 * r.length + 5 + charCost r.length) := by
  have hT' : S TK = r.reverse := by rw [hS, Lists.set_ne _ _ (Ne.symm hx1), hT]
  have x₁ := parseCharP_ok TK x SC ST SU SG SF hx (by decide) hd S hT' hp
  have e : (S.set TK r₁.reverse).set x (S x ++ [c.toNat]) = (B.set TK r₁.reverse).set x (S x ++ [c.toNat]) := by
    have hSy : ∀ y, y ≠ x → S y = B y := fun y hy => by rw [hS, Lists.set_ne _ _ hy]
    funext y
    by_cases hy : y = x
    · subst hy; simp only [Lists.set_same]
    · rw [Lists.set_ne _ _ hy, Lists.set_ne _ _ hy]
      simp only [Lists.set]
      split
      · rfl
      · exact hSy y hy
  rw [e] at x₁
  exact x₁

theorem charP_fail (x : Fin NK) (hx : x ≠ ST) (hd : [TK, x, SC, ST, SU, SG, SF].Nodup) (S : Lists NK)
    {r : List Nat} (hT : S TK = r.reverse) (hp : parseChar r = none) :
    ∃ S', NHalts (charP x hx) S false S' (6 * r.length + 6 + charCost r.length) :=
  parseCharP_fail TK x SC ST SU SG SF hx (by decide) hd S hT hp

/-! ## Token `2`: a character -/

def tok2P : NProg NK := .seq (charP SA (by decide)) (.seq (.prim (.pushZ SB)) (leafOutP 2))

theorem tok2_ok (s : PSt) (K r : List Nat) (htk : s.tk = 2 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok2P s K r (frameCost N) := by
  have hL : r.length ≤ N := by rw [htk] at hN; simp at hN; omega
  have hc := tokCost_le hL
  let t : PSt := { s with ctl := K, tk := r }
  have hA : enc t SA = [] := enc_scratch t SA (by decide)
  cases hp : parseChar r with
  | none =>
    have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp]
    obtain ⟨S', x₁⟩ := charP_fail SA (by decide) (by decide) (enc t) (r := r) rfl hp
    exact litTokOK_halt he ⟨S', x₁.seq.mono (by omega)⟩
  | some p =>
    obtain ⟨c, r₁⟩ := p
    have he : readExpr s K = s.leaf ⟨2, c.toNat, 0, s.cur⟩ 0 r₁ K := by simp only [readExpr, htk, hp]
    have x₁ := charP_ok SA (by decide) (by decide) (enc t) (enc t) (by rw [Lists.set_get_self]) (by decide)
      (r := r) rfl hp
    rw [hA, List.nil_append, ← enc_with_tk t r₁] at x₁
    have x₂ := nruns_pushZ SB ((enc { t with tk := r₁ }).set SA [c.toNat])
    rw [Lists.set_ne _ _ (by decide), enc_scratch _ SB (by decide), List.nil_append] at x₂
    have x₃ := leafOutP_runs { t with tk := r₁ } 2 c.toNat 0
    exact litTokOK_run he ((x₁.seq (x₂.seq x₃)).mono (by omega)) rfl hs

/-! ## Token `3`: a range of characters -/

def tok3P : NProg NK := .seq (charP SA (by decide)) (.seq (charP SB (by decide)) (leafOutP 3))

theorem tok3_ok (s : PSt) (K r : List Nat) (htk : s.tk = 3 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok3P s K r (frameCost N) := by
  have hL : r.length ≤ N := by rw [htk] at hN; simp at hN; omega
  have hc := tokCost_le hL
  let t : PSt := { s with ctl := K, tk := r }
  have hA : enc t SA = [] := enc_scratch t SA (by decide)
  cases hp : parseChar r with
  | none =>
    have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp]
    obtain ⟨S', x₁⟩ := charP_fail SA (by decide) (by decide) (enc t) (r := r) rfl hp
    exact litTokOK_halt he ⟨S', x₁.seq.mono (by omega)⟩
  | some p =>
    obtain ⟨lo, r₁⟩ := p
    have hlen₁ := parseChar_len hp
    have hm₁ := charCost_mono (show r₁.length ≤ r.length by omega)
    have x₁ := charP_ok SA (by decide) (by decide) (enc t) (enc t) (by rw [Lists.set_get_self]) (by decide)
      (r := r) rfl hp
    rw [hA, List.nil_append, ← enc_with_tk t r₁] at x₁
    let t₁ : PSt := { t with tk := r₁ }
    let B : Lists NK := (enc t₁).set SA [lo.toNat]
    have hBT : B TK = r₁.reverse := Lists.set_ne (enc t₁) [lo.toNat] (by decide : TK ≠ SA)
    have hBB : B SB = [] :=
      (Lists.set_ne (enc t₁) [lo.toNat] (by decide : SB ≠ SA)).trans (enc_scratch _ SB (by decide))
    cases hp₂ : parseChar r₁ with
    | none =>
      have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp, hp₂]
      obtain ⟨S', x₂⟩ := charP_fail SB (by decide) (by decide) B hBT hp₂
      exact litTokOK_halt he ⟨S', (x₁.seqH x₂.seq).mono (by omega)⟩
    | some p₂ =>
      obtain ⟨hi', r₂⟩ := p₂
      have he : readExpr s K = s.leaf ⟨3, lo.toNat, hi'.toNat, s.cur⟩ 0 r₂ K := by
        simp only [readExpr, htk, hp, hp₂]
      have x₂ := charP_ok SB (by decide) (by decide) B B (Lists.set_get_self B SB).symm (by decide) hBT hp₂
      have e : (B.set TK r₂.reverse).set SB (B SB ++ [hi'.toNat]) =
          ((enc { t₁ with tk := r₂ }).set SA [lo.toNat]).set SB [hi'.toNat] := by
        rw [hBB, List.nil_append, enc_with_tk t₁ r₂]
        congr 1
        exact Lists.set_comm (by decide : SA ≠ TK) _ _
      rw [e] at x₂
      have x₃ := leafOutP_runs { t₁ with tk := r₂ } 3 lo.toNat hi'.toNat
      exact litTokOK_run he ((x₁.seq (x₂.seq x₃)).mono (by omega)) rfl hs

/-! ## Token `4`: a string -/

/-- Read the string, adding its codes plus one to `LTs`; end the literal with `0`; the literal's number (`NLT`, then
incremented) is `a`. -/
def tok4P : NProg NK :=
  .seq (parseStrP TK SA SC ST SU SG SF (by decide) (by decide) (strSink SA LTs (by decide) true))
    (.seq (.prim (.pushZ LTs)) (.seq (.prim (.dup NLT SA (by decide))) (.seq (.prim (.inc NLT))
      (.seq (.prim (.pushZ SB)) (leafOutP 4)))))

theorem tok4_ok (s : PSt) (K r : List Nat) (htk : s.tk = 4 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok4P s K r (frameCost N) := by
  have hL : r.length ≤ N := by rw [htk] at hN; simp at hN; omega
  have hc := tokCost_le hL
  let t : PSt := { s with ctl := K, tk := r }
  cases hp : parseStr r.length r with
  | none =>
    have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp]
    obtain ⟨S', x₁⟩ := parseStrP_fail TK SA SC ST SU SG SF LTs (by decide) (by decide) (by decide) true
      (by decide) (enc t) (l := r) rfl (Nat.le_refl _) hp
    exact litTokOK_halt he ⟨S', x₁.seq.mono (by omega)⟩
  | some p =>
    obtain ⟨str, r₁⟩ := p
    have he : readExpr s K = { s.leaf ⟨4, s.lt.length, 0, s.cur⟩ 0 r₁ K with lt := s.lt ++ [str.map Char.toNat] } := by
      simp only [readExpr, htk, hp]
    have x₁ := parseStrP_ok TK SA SC ST SU SG SF LTs (by decide) (by decide) (by decide) true
      (by decide) (enc t) (l := r) rfl hp
    let S₁ : Lists NK := ((enc t).set TK r₁.reverse).set LTs
      (enc t LTs ++ str.map (fun ch => ch.toNat + cond true 1 0))
    have x₂ := nruns_pushZ LTs S₁
    let S₂ : Lists NK := S₁.set LTs (S₁ LTs ++ [0])
    have x₃ := nruns_dup NLT SA (by decide) S₂ (l := []) (v := t.lt.length)
      (by simp (config := { decide := true }) [S₂, S₁, Lists.set, enc_nlt])
    let S₃ : Lists NK := S₂.set SA (S₂ SA ++ [t.lt.length])
    have x₄ := nruns_inc NLT S₃ (l := []) (v := t.lt.length)
      (by simp (config := { decide := true }) [S₃, S₂, S₁, Lists.set, enc_nlt])
    let S₄ : Lists NK := S₃.set NLT ([] ++ [t.lt.length + 1])
    have x₅ := nruns_pushZ SB S₄
    let t₂ : PSt := { t with tk := r₁, lt := t.lt ++ [str.map Char.toNat] }
    have hA : enc t SA = [] := enc_scratch t SA (by decide)
    have hB : enc t SB = [] := enc_scratch t SB (by decide)
    have e : S₄.set SB (S₄ SB ++ [0]) = ((enc t₂).set SA [t.lt.length]).set SB [0] := by
      rw [enc_with_lt { t with tk := r₁ } _, enc_with_tk t r₁]
      funext x
      by_cases h1 : x = TK
      · subst h1; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, Lists.set]
      by_cases h8 : x = LTs
      · subst h8; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, Lists.set, enc_lt, encLits]
      by_cases h16 : x = NLT
      · subst h16; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, Lists.set]
      by_cases h18 : x = SA
      · subst h18; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, Lists.set, hA]
      by_cases h24 : x = SB
      · subst h24; simp (config := { decide := true }) [S₄, S₃, S₂, S₁, Lists.set, hB]
      simp (config := { decide := true }) [S₄, S₃, S₂, S₁, Lists.set, h1, h8, h16, h18, h24]
    rw [e] at x₅
    have x₆ := leafOutP_runs t₂ 4 t.lt.length 0
    exact litTokOK_run he ((x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆))))).mono (by omega)) rfl hs

end Shallot.MacroPeg.Mach
