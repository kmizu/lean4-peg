import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# One step of the reading machine on stacks: reading a type, and the simple tokens of an expression

* `frame1P`: the frame `1` (`readType`): token `0` pushes the base type, token `1` asks for an arrow.
* Token programs (`TokOK`): tokens `0`, `1` emit a constant leaf; tokens `5`–`8`, `11`, `12` push frames; token
  `9` reads a variable (`parseNatP`, `varTyP`); token `10` reads a rule (`parseNatP`, `cmpTop`, `peekAt`).

Scratch stacks: `18` holds the number read (`i`), `19`–`24` the scratch of the macros. All of them are empty again
at the end.
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.Flat
open Shallot.MacroPeg.KExp

/-! ## Costs -/

/-- The base of `frameCost`, kept folded. -/
def fB (N : Nat) : Nat := N + 1114113

theorem frameCost_fB (N : Nat) : frameCost N = 100 * (fB N * fB N * fB N) := rfl

theorem fB_big (N : Nat) : 1114113 ≤ fB N := by unfold fB; omega

theorem le_fB (N : Nat) : N + 1 ≤ fB N := by unfold fB; omega

/-- A product of two numbers of size `O(N)`, plus a linear term, is within `frameCost N`. -/
theorem cost_le {N x y : Nat} (hx : x ≤ 30 * fB N) (hy : y ≤ 30 * fB N) : x * y + 30 * fB N ≤ frameCost N := by
  rw [frameCost_fB]
  have hb := fB_big N
  generalize fB N = B at hx hy hb ⊢
  have h₁ : x * y ≤ 30 * B * (30 * B) := Nat.mul_le_mul hx hy
  have h₂ : 30 * B * (30 * B) = 900 * (B * B) := by
    rw [Nat.mul_mul_mul_comm]
  have h₃ : B ≤ B * B := Nat.le_mul_self B
  have h₄ : B * B * 10 ≤ B * B * B := Nat.mul_le_mul_left (B * B) (by omega)
  generalize B * B * B = C at h₄ ⊢
  generalize B * B = Q at h₂ h₃ h₄
  omega

/-- Small constants are within `frameCost N`. -/
theorem small_le (N c : Nat) (hc : c ≤ 30 * fB N) : c ≤ frameCost N := by
  have := cost_le (N := N) (x := 0) (y := 0) (by omega) (by omega)
  omega

/-! ## What a token program does -/

theorem tokOK_run {p : NProg NK} {s : PSt} {K r : List Nat} {T : Nat} {s' : PSt} (he : readExpr s K = s')
    (h : NRuns p (enc { s with ctl := K, tk := r }) (enc s') T) (hok : s'.ok = true) : TokOK p s K r T :=
  ⟨fun _ => he ▸ h, fun hf => by rw [he, hok] at hf; cases hf⟩

theorem tokOK_halt {p : NProg NK} {s : PSt} {K r : List Nat} {T : Nat} (he : readExpr s K = s.fail)
    (h : ∃ S', NHalts p (enc { s with ctl := K, tk := r }) false S' T) : TokOK p s K r T :=
  ⟨fun ht => absurd ht (by rw [he]; simp [PSt.fail]), fun _ => h⟩

/-! ## Reading a type (frame `1`) -/

/-- Frame `1`: token `0` is the base type (push `0` on `TY`); token `1` an arrow (push the frames `12`, `1`). -/
def frame1P : NProg NK :=
  .ite TK .nonempty (caseTop TK [.prim (.pushZ TY), push2 12 1] (.halt false)) (.halt false)

theorem enc_tk_K (s : PSt) (K : List Nat) : (enc { s with ctl := K }) TK = s.tk.reverse := rfl

/-- Popping the token `t` off `TK`. -/
theorem enc_pop_tk (s : PSt) (K r : List Nat) :
    (enc { s with ctl := K }).set TK r.reverse = enc { s with ctl := K, tk := r } :=
  (enc_with_tk { s with ctl := K } r).symm

/-- Pushing the base type. -/
theorem pushZ_ty_runs (t : PSt) : NRuns (.prim (.pushZ TY)) (enc t) (enc { t with ty := 0 :: t.ty }) 1 := by
  have x := nruns_pushZ TY (enc t)
  have e : (enc t).set TY ((enc t) TY ++ [0]) = enc { t with ty := 0 :: t.ty } := by
    rw [enc_with_ty t (0 :: t.ty), List.reverse_cons]; rfl
  rw [e] at x; exact x

set_option linter.unusedVariables false in
theorem frame1_frame (s : PSt) (K : List Nat) (hc : s.ctl = 1 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame1P s K (frameCost N) := by
  have hp : pstep s = readType s K := by simp only [pstep, hc]
  have h30 := small_le N 30 (by have := fB_big N; omega)
  rcases htk : s.tk with _ | ⟨_ | _ | v, r⟩
  · have he : pstep s = s.fail := by rw [hp]; simp only [readType, htk]
    exact frameOK_halt he ⟨_, ((nhalts_halt false _).iteF (by rw [enc_tk_K, htk]; rfl)).mono (by omega)⟩
  · have he : pstep s = { s with tk := r, ctl := K, ty := 0 :: s.ty } := by rw [hp]; simp only [readType, htk]
    have x := caseTop_runs TK [.prim (.pushZ TY), push2 12 1] (.halt false) 0 (by decide) (enc { s with ctl := K })
      r.reverse (by rw [enc_tk_K, htk]; simp) _ _ (by rw [enc_pop_tk]; exact pushZ_ty_runs { s with ctl := K, tk := r })
    exact frameOK_run he ((x.iteT (by rw [enc_tk_K, htk]; simp [NTest.eval])).mono (by omega)) rfl hs
  · have he : pstep s = { s with tk := r, ctl := 1 :: 12 :: K } := by rw [hp]; simp only [readType, htk]
    have x := caseTop_runs TK [.prim (.pushZ TY), push2 12 1] (.halt false) 1 (by decide) (enc { s with ctl := K })
      r.reverse (by rw [enc_tk_K, htk]; simp) _ _ (by rw [enc_pop_tk]; exact push2_runs { s with tk := r } K 12 1)
    exact frameOK_run he ((x.iteT (by rw [enc_tk_K, htk]; simp [NTest.eval])).mono (by omega)) rfl hs
  · have he : pstep s = s.fail := by rw [hp]; simp only [readType, htk]
    have x := caseTop_default TK [.prim (.pushZ TY), push2 12 1] (.halt false) v (enc { s with ctl := K })
      r.reverse (by rw [enc_tk_K, htk]; simp) false _ _ (nhalts_halt false _)
    exact frameOK_halt he ⟨_, (x.iteT (by rw [enc_tk_K, htk]; simp [NTest.eval])).mono (by simp; omega)⟩

/-! ## Tokens that push frames -/

theorem tokPush_ok (s : PSt) (K r : List Nat) (a b : Nat) (hs : s.ok = true)
    (he : readExpr s K = { s with tk := r, ctl := b :: a :: K }) {N : Nat} (hab : a + b + 2 ≤ frameCost N) :
    TokOK (push2 a b) s K r (frameCost N) :=
  tokOK_run he ((push2_runs { s with tk := r } K a b).mono hab) hs

def tok5P : NProg NK := push2 2 0
def tok6P : NProg NK := push2 4 0
def tok7P : NProg NK := push2 6 0
def tok8P : NProg NK := push2 7 0
def tok11P : NProg NK := push2 8 1
def tok12P : NProg NK := push2 10 0

set_option linter.unusedVariables false in
theorem tok5_ok (s : PSt) (K r : List Nat) (htk : s.tk = 5 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok5P s K r (frameCost N) :=
  tokPush_ok s K r 2 0 hs (by simp only [readExpr, htk]) (small_le N _ (by have := fB_big N; omega))

set_option linter.unusedVariables false in
theorem tok6_ok (s : PSt) (K r : List Nat) (htk : s.tk = 6 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok6P s K r (frameCost N) :=
  tokPush_ok s K r 4 0 hs (by simp only [readExpr, htk]) (small_le N _ (by have := fB_big N; omega))

set_option linter.unusedVariables false in
theorem tok7_ok (s : PSt) (K r : List Nat) (htk : s.tk = 7 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok7P s K r (frameCost N) :=
  tokPush_ok s K r 6 0 hs (by simp only [readExpr, htk]) (small_le N _ (by have := fB_big N; omega))

set_option linter.unusedVariables false in
theorem tok8_ok (s : PSt) (K r : List Nat) (htk : s.tk = 8 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok8P s K r (frameCost N) :=
  tokPush_ok s K r 7 0 hs (by simp only [readExpr, htk]) (small_le N _ (by have := fB_big N; omega))

set_option linter.unusedVariables false in
theorem tok11_ok (s : PSt) (K r : List Nat) (htk : s.tk = 11 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok11P s K r (frameCost N) :=
  tokPush_ok s K r 8 1 hs (by simp only [readExpr, htk]) (small_le N _ (by have := fB_big N; omega))

set_option linter.unusedVariables false in
theorem tok12_ok (s : PSt) (K r : List Nat) (htk : s.tk = 12 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok12P s K r (frameCost N) :=
  tokPush_ok s K r 10 0 hs (by simp only [readExpr, htk]) (small_le N _ (by have := fB_big N; omega))


/-! ## Constant leaves (tokens `0`, `1`) -/

/-- Push the base type and emit `⟨tag, 0, 0, cur⟩`. -/
def leafP (tag : Nat) : NProg NK := .seq (.prim (.pushZ TY)) (emitP tag)

theorem leafP_runs (t : PSt) (tag : Nat) :
    NRuns (leafP tag) (enc t) (enc { t with ty := 0 :: t.ty, out := ⟨tag, 0, 0, t.cur⟩ :: t.out }) (tag + 5) :=
  ((pushZ_ty_runs t).seq (emitP_runs { t with ty := 0 :: t.ty } tag)).mono (by omega)

def tok0P : NProg NK := leafP 0
def tok1P : NProg NK := leafP 1

set_option linter.unusedVariables false in
theorem tok0_ok (s : PSt) (K r : List Nat) (htk : s.tk = 0 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok0P s K r (frameCost N) :=
  tokOK_run (by simp only [readExpr, htk]; rfl)
    ((leafP_runs { s with ctl := K, tk := r } 0).mono (small_le N _ (by have := fB_big N; omega))) hs

set_option linter.unusedVariables false in
theorem tok1_ok (s : PSt) (K r : List Nat) (htk : s.tk = 1 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok1P s K r (frameCost N) :=
  tokOK_run (by simp only [readExpr, htk]; rfl)
    ((leafP_runs { s with ctl := K, tk := r } 1).mono (small_le N _ (by have := fB_big N; omega))) hs

/-! ## Emitting a leaf with a number -/

/-- The scratch stack holding the number read. -/
abbrev NUM : Fin NK := 18

/-- Emit `⟨tag, i, 0, cur⟩`, with `i` taken from `NUM`. -/
def emitV (tag : Nat) : NProg NK :=
  .seq (npushC OUT tag) (.seq (nmv NUM OUT (by decide)) (.seq (.prim (.pushZ OUT)) (.prim (.dup CUR OUT (by decide)))))

theorem emitV_runs (t : PSt) (tag i : Nat) :
    NRuns (emitV tag) ((enc t).set NUM [i]) (enc { t with out := ⟨tag, i, 0, t.cur⟩ :: t.out }) (tag + 5) := by
  have hNO : NUM ≠ OUT := by decide
  have hON : OUT ≠ NUM := by decide
  have hCO : CUR ≠ OUT := by decide
  have hCN : CUR ≠ NUM := by decide
  let S := (enc t).set NUM [i]
  have x₁ := nruns_pushC OUT S tag
  let S₁ := S.set OUT (S OUT ++ [tag])
  have x₂ := nruns_mv NUM OUT hNO S₁ (l := []) (v := i) (by simp [S₁, S, Lists.set_ne _ _ hNO])
  let S₂ := (S₁.set OUT (S₁ OUT ++ [i])).set NUM []
  have x₃ := nruns_pushZ OUT S₂
  let S₃ := S₂.set OUT (S₂ OUT ++ [0])
  have x₄ := nruns_dup CUR OUT hCO S₃ (l := []) (v := t.cur)
    (by simp only [S₃, S₂, S₁, S, Lists.set_ne _ _ hCO, Lists.set_ne _ _ hCN]; rfl)
  have e : S₃.set OUT (S₃ OUT ++ [t.cur]) = enc { t with out := ⟨tag, i, 0, t.cur⟩ :: t.out } := by
    rw [enc_with_out t (⟨tag, i, 0, t.cur⟩ :: t.out)]
    funext x
    by_cases hx : x = OUT
    · subst hx
      simp only [S₃, S₂, S₁, S, Lists.set_same, Lists.set_ne _ _ hON]
      simp [enc_out, encItems, encItem]
    · by_cases hy : x = NUM
      · subst hy
        simp only [S₃, S₂, S₁, S, Lists.set_same, Lists.set_ne _ _ hNO]
        exact (enc_scratch t NUM (by decide)).symm
      · simp only [S₃, S₂, S₁, S, Lists.set_ne _ _ hx, Lists.set_ne _ _ hy]
  rw [e] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by omega)

/-! ## Reading the number of a variable or a rule -/

/-- The copy of the number read, consumed by the lookups. -/
abbrev IDX : Fin NK := 19

theorem parseNum_runs (s : PSt) (K r r₁ : List Nat) (i : Nat) (hr : r = serNat i ++ r₁) :
    NRuns (parseNatP TK NUM) (enc { s with ctl := K, tk := r }) ((enc { s with ctl := K, tk := r₁ }).set NUM [i])
      (6 * i + 5) := by
  have x := parseNatP_ok TK NUM (by decide) (enc { s with ctl := K, tk := r }) (n := i) (r := r₁)
    (by show r.reverse = _; rw [hr, List.reverse_append])
  rw [← enc_with_tk { s with ctl := K, tk := r } r₁, enc_scratch _ NUM (by decide), List.nil_append] at x
  exact x

theorem parseNum_fail (s : PSt) (K r : List Nat) (hp : parseNat r = none) :
    ∃ S', NHalts (parseNatP TK NUM) (enc { s with ctl := K, tk := r }) false S' (6 * r.length + 6) :=
  parseNatP_fail TK NUM (by decide) _ (l := r) rfl hp

/-- Copy the number read to `IDX`. -/
theorem dupNum_runs (a : PSt) (i : Nat) :
    NRuns (.prim (.dup NUM IDX (by decide))) ((enc a).set NUM [i]) (((enc a).set NUM [i]).set IDX [i]) 1 := by
  have x := nruns_dup NUM IDX (by decide) ((enc a).set NUM [i]) (l := []) (v := i) (by simp)
  rw [Lists.set_ne _ _ (by decide), enc_scratch a IDX (by decide), List.nil_append] at x
  exact x

/-- After a lookup consumed `IDX` and pushed the type `τ`. -/
theorem ty_after (a : PSt) (i τ : Nat) :
    ((((enc a).set NUM [i]).set IDX [i]).set IDX []).set TY ((((enc a).set NUM [i]).set IDX [i]) TY ++ [τ]) =
      (enc { a with ty := τ :: a.ty }).set NUM [i] := by
  rw [enc_with_ty a (τ :: a.ty), Lists.set_set_u, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]
  funext x
  by_cases hx : x = TY
  · subst hx; simp +decide [Lists.set, enc_ty]
  · by_cases hy : x = IDX
    · subst hy; simp +decide [Lists.set, enc_scratch a IDX (by decide)]
    · simp [Lists.set, hx, hy]

/-! ## Variables (token `9`) -/

/-- Read `i`, push the type of variable `i` in the current context, emit `⟨9, i, 0, cur⟩`. Scratch `19`–`24`. -/
def tok9P : NProg NK :=
  .seq (parseNatP TK NUM) (.seq (.prim (.dup NUM IDX (by decide)))
    (.seq (varTyP CTs CUR IDX TY 20 21 22 23 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (emitV 9)))

theorem varStacks_tok9 : VarStacks CTs CUR IDX 20 21 22 23 24 TY := by decide

set_option linter.unusedVariables false in
theorem tok9_ok (s : PSt) (K r : List Nat) (htk : s.tk = 9 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok9P s K r (frameCost N) := by
  have hlen : s.tk.length = r.length + 1 := by rw [htk]; rfl
  have hct : s.ct.length ≤ N := by unfold tsize at hN; omega
  have hB := le_fB N
  rcases hp : parseNat r with _ | ⟨i, r₁⟩
  · have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp]
    obtain ⟨S', h⟩ := parseNum_fail s K r hp
    refine tokOK_halt he ⟨S', h.seq.mono ?_⟩
    exact small_le N _ (by omega)
  have hr := parseNat_sound hp
  have hil : i + 1 ≤ r.length := by rw [hr, List.length_append, length_serNat]; omega
  let a : PSt := { s with ctl := K, tk := r₁ }
  have x₁ := parseNum_runs s K r r₁ i hr
  have x₂ := dupNum_runs a i
  let S₂ := ((enc a).set NUM [i]).set IDX [i]
  have hP : S₂ CTs = encPairs s.ct := by simp +decide only [S₂, Lists.set]; rfl
  have hTe : S₂ 23 = [] := by simp +decide only [S₂, Lists.set]; exact enc_scratch a 23 (by decide)
  have hcs : S₂ CUR = [] ++ [s.cur] := by simp +decide only [S₂, Lists.set]; rfl
  have hci : S₂ IDX = [] ++ [i] := by simp [S₂]
  have hcost : 6 * i + 5 + (1 + (varTyCost s.ct.length i + (9 + 5))) ≤ frameCost N := by
    have := cost_le (N := N) (x := i + 1) (y := 23 * s.ct.length + 30) (by omega) (by omega)
    unfold varTyCost; omega
  rcases hv : varTy s.ct s.cur i with _ | τ
  · have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp, hv]
    obtain ⟨S', h⟩ := varTyP_fail CTs CUR IDX 20 21 22 23 24 TY (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) varStacks_tok9 S₂ hP hTe hi.ct hi.cur hcs hci hv
    exact tokOK_halt he ⟨S', (x₁.seqH (x₂.seqH h.seq)).mono (by omega)⟩
  · have he : readExpr s K = s.leaf ⟨9, i, 0, s.cur⟩ τ r₁ K := by simp only [readExpr, htk, hp, hv]
    have x₃ := varTyP_ok CTs CUR IDX 20 21 22 23 24 TY (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) varStacks_tok9 S₂ hP hTe hi.ct hi.cur hcs hci hv
    rw [ty_after a i τ] at x₃
    have x₄ := emitV_runs { a with ty := τ :: a.ty } 9 i
    exact tokOK_run he ((x₁.seq (x₂.seq (x₃.seq x₄))).mono hcost) hs

/-! ## Rules (token `10`) -/

/-- The result of comparing the number read with the number of rule types. -/
abbrev CMP : Fin NK := 23

/-- After the comparison: the number read is a rule; push its type, emit `⟨10, i, 0, cur⟩`. -/
def ruleP : NProg NK :=
  .seq (.prim (.dup NUM IDX (by decide))) (.seq (peekAt RTs 20 IDX TY (by decide) (by decide)) (emitV 10))

/-- Read `i`, check `i < rt.length` (`cmpTop`), push the rule type `rt[i]`, emit `⟨10, i, 0, cur⟩`. -/
def tok10P : NProg NK :=
  .seq (parseNatP TK NUM) (.seq (cmpTop NUM NRT 20 21 22 CMP (by decide) (by decide))
    (caseTop CMP [ruleP] (.halt false)))

theorem ruleP_runs (s : PSt) (a : PSt) (ha : a.rt = s.rt) (i τ : Nat) (hτ : s.rt[i]? = some τ) :
    NRuns ruleP ((enc a).set NUM [i]) (enc { { a with ty := τ :: a.ty } with out := ⟨10, i, 0, a.cur⟩ :: a.out })
      (6 * s.rt.length + 4 * i + 22) := by
  have x₁ := dupNum_runs a i
  let S₂ := ((enc a).set NUM [i]).set IDX [i]
  have hRT : S₂ RTs = s.rt := by simp +decide only [S₂, Lists.set]; exact ha
  have hτ' : (S₂ RTs)[i]? = some τ := by rw [hRT]; exact hτ
  have hk : i < (S₂ RTs).length := (List.getElem?_eq_some_iff.mp hτ').1
  have hval : (S₂ RTs)[i] = τ := (List.getElem?_eq_some_iff.mp hτ').2
  have x₂ := nruns_peekAt RTs 20 IDX TY (by decide) (by decide) (by decide) S₂
    (by simp +decide only [S₂, Lists.set]; exact enc_scratch a 20 (by decide)) (lc := []) (k := i) (by simp [S₂]) hk
  rw [hval] at x₂
  rw [hRT] at x₂
  rw [ty_after a i τ] at x₂
  have x₃ := emitV_runs { a with ty := τ :: a.ty } 10 i
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

theorem cmpRes_ge {a b : Nat} (h : ¬ a < b) : cmpRes a b = (cmpRes a b - 1) + 1 := by
  have := cmpRes_ne (show b ≤ a by omega); omega

set_option linter.unusedVariables false in
theorem tok10_ok (s : PSt) (K r : List Nat) (htk : s.tk = 10 :: r) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : TokOK tok10P s K r (frameCost N) := by
  have hlen : s.tk.length = r.length + 1 := by rw [htk]; rfl
  have hrt : s.rt.length ≤ N := by unfold tsize at hN; omega
  have hB := le_fB N
  rcases hp : parseNat r with _ | ⟨i, r₁⟩
  · have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp]
    obtain ⟨S', h⟩ := parseNum_fail s K r hp
    refine tokOK_halt he ⟨S', h.seq.mono ?_⟩
    exact small_le N _ (by omega)
  have hr := parseNat_sound hp
  have hil : i + 1 ≤ r.length := by rw [hr, List.length_append, length_serNat]; omega
  let a : PSt := { s with ctl := K, tk := r₁ }
  have x₁ := parseNum_runs s K r r₁ i hr
  have x₂ := nruns_cmpTop NUM NRT 20 21 22 CMP (by decide) (by decide) (by decide) ((enc a).set NUM [i])
    (li := []) (lj := []) (a := i) (b := s.rt.length) (by simp) (by simp +decide only [Lists.set]; rfl)
  have h23 : ((enc a).set NUM [i]) CMP = [] := by
    simp +decide only [Lists.set]; exact enc_scratch a CMP (by decide)
  rw [h23, List.nil_append] at x₂
  have hcost := cost_le (N := N) (x := i + s.rt.length + 1) (y := 2 * i + 6) (by omega) (by omega)
  rcases hτ : s.rt[i]? with _ | τ
  · have he : readExpr s K = s.fail := by simp only [readExpr, htk, hp, hτ]
    have hge : ¬ i < s.rt.length := by rw [List.getElem?_eq_none_iff] at hτ; omega
    have x₃ := caseTop_default CMP [ruleP] (.halt false) (cmpRes i s.rt.length - 1)
      (((enc a).set NUM [i]).set CMP [cmpRes i s.rt.length]) [] (by simp; exact cmpRes_ge hge) false _ _
      (nhalts_halt false _)
    exact tokOK_halt he ⟨_, (x₁.seqH (x₂.seqH x₃)).mono (by simp; omega)⟩
  · have he : readExpr s K = s.leaf ⟨10, i, 0, s.cur⟩ τ r₁ K := by simp only [readExpr, htk, hp, hτ]
    have hlt : i < s.rt.length := (List.getElem?_eq_some_iff.mp hτ).1
    rw [cmpRes_lt hlt] at x₂
    have hback : (((enc a).set NUM [i]).set CMP [0]).set CMP [] = (enc a).set NUM [i] := by
      rw [Lists.set_set_u]
      have := Lists.set_get_self ((enc a).set NUM [i]) CMP
      rw [h23] at this; exact this
    have x₃ := caseTop_runs CMP [ruleP] (.halt false) 0 (by decide) (((enc a).set NUM [i]).set CMP [0]) []
      (by simp) _ _ (by rw [hback]; exact ruleP_runs s a rfl i τ hτ)
    exact tokOK_run he ((x₁.seq (x₂.seq x₃)).mono (by omega)) hs

end Shallot.MacroPeg.Mach
