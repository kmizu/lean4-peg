import PalPeg.GSPreprocessProg

/-!
# 前処理段の有限制御プログラム化・第 2 部 (`GSPreprocessProg2`)

`PalPeg.GSPreprocessProg` で作った基盤（`A9` / `Cond9` / `I9` / `ExecA` /
`DLOOP` / `dLoop_exec`）の上に、

* `bottomProg` の番人駆動版（`V2` が右端番人 `endSym` を読むまで回る）、
* `subKLoop` の `k` 段 `seq` 版、
* `perUnit` / `rewindUnit` の**並べ替え版**（駆動 probe を先頭に置いたもの）、
* `repoProg` の部分ドレイン `pvLoop (P-1)` を回避する退避ガジェット、
* 状態依存の本体を許す**一般化駆動ループ** `dLoopS_exec`、
* それを使った**カウンタ比較ガジェット** `CMPLT`

を追加する。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM
open PalPeg.GSPre
open PalPeg.Program
open PalPeg.ProgLang

variable {sc : ℕ}

/-! ## 12. `bottomProg`：番人 `endSym` で止まるループ

`bottomProg blank n ts = sIncs blank (n - sOf ts)` は `n = |x|` を数として使うが、
有限制御は `|x|` を持てない。そこで「`V2` が右端番人を読むまで `V2` と `Cs` を
同時に 1 セルずつ右へ動かす」ループで実現する。`Cs` の増分は同じだが、
`V2` のヘッドが右端に移動する点だけが元の動作列と異なる
（`decompose2_on_tapes` の終状態の `V2` 位置は存在量化されているので影響しない）。 -/

section Bottom

/-- 1 単位：`V2` を右へ、`Cs` を 1 増やす。 -/
def v2csUnit (blank : Fin sc) : List (Act sc) :=
  [Act.V2 Move.right, Act.Cs blank Move.right]

def v2csLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => v2csUnit blank ++ v2csLoop blank n

@[simp] theorem v2csLoop_length (blank : Fin sc) (n : ℕ) :
    (v2csLoop blank n).length = 2 * n := by
  induction n with
  | zero => simp [v2csLoop]
  | succ n ih => simp only [v2csLoop, List.length_append, v2csUnit, ih]; simp; omega

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

theorem applyActs_v2csUnit (ts : Tapes sc) :
    applyActs blank (v2csUnit blank) ts =
      { ts with
        V2 := Tape.step blank ts.V2 ts.V2.focus .right
        Cs := Tape.step blank ts.Cs blank .right } := rfl

theorem v2csLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc), b + n ≤ x.length →
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a (b + n) ⟨D, Q, E, P, F, S + n, R⟩
        (applyActs blank (v2csLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts _ hE; simpa [v2csLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hb hE
      have hblt : b < x.length := by omega
      have hstep : Enc blank startSym endSym mark x a (b + 1) ⟨D, Q, E, P, F, S + 1, R⟩
          (applyActs blank (v2csUnit blank) ts) := by
        rw [applyActs_v2csUnit]
        exact ⟨hE.v1, pat_right hE.v2 hblt, hE.cd, hE.cq, hE.ce, hE.cp, hE.cf,
          Tape.counter'_inc hE.cs, hE.cr⟩
      have := ih a (b + 1) D Q E P F (S + 1) R _ (by omega) hstep
      simp only [v2csLoop, applyActs_append]
      have e1 : b + 1 + n = b + (n + 1) := by omega
      have e2 : S + 1 + n = S + (n + 1) := by omega
      rw [e1, e2] at this
      exact this

/-- 番人駆動の「底」プログラム。 -/
def BOTTOM : Prog A9 Cond9 :=
  Prog.loop Cond9.v2NotEnd (tV2, W9.keep, Move.right) (Prog.act (tCs, W9.blk, Move.right))

variable {Terminal : Type}

/-- **`BOTTOM` の実現**：`V2` が位置 `b` にあるとき、ちょうど `|x| - b` 回まわる。 -/
theorem BOTTOM_exec (hend : endSym ∉ x) : ∀ (m b : ℕ) (c : Ctr) (a : ℕ) (ts : Tapes sc),
    b + m = x.length → Enc blank startSym endSym mark x a b c ts →
      ExecA Terminal blank endSym mark BOTTOM ts (v2csLoop blank m) := by
  intro m
  induction m with
  | zero =>
      intro b c a ts hb hE
      refine execA_loop_stop ?_
      have hread : Tape.read ts.V2 = endSym :=
        (read_pat_end_iff hend hE.v2).2 (by omega)
      simp only [condOf9, decide_eq_false_iff_not, not_not]
      exact hread
  | succ m ih =>
      intro b c a ts hb hE
      have hne : Tape.read ts.V2 ≠ endSym := by
        intro hc
        have := (read_pat_end_iff hend hE.v2).1 hc
        omega
      have hcond : condOf9 endSym mark Cond9.v2NotEnd (fun j => (getT ts j).focus) = true := by
        simp only [condOf9, decide_eq_true_eq]
        exact hne
      have h1 : ExecA Terminal blank endSym mark (Prog.act (tCs, W9.blk, Move.right))
          (applyAct blank ts (Act.V2 Move.right)) [Act.Cs blank Move.right] :=
        execA_ct_put (ctCs : CT sc) Move.right _
      have hstate : applyActs blank [Act.Cs blank Move.right]
          (applyAct blank ts (Act.V2 Move.right)) = applyActs blank (v2csUnit blank) ts := rfl
      have hE1 : Enc blank startSym endSym mark x a (b + 1) ⟨c.d, c.q, c.e, c.p, c.f, c.s + 1, c.r⟩
          (applyActs blank (v2csUnit blank) ts) := by
        rw [applyActs_v2csUnit]
        exact ⟨hE.v1, pat_right hE.v2 (by omega), hE.cd, hE.cq, hE.ce, hE.cp, hE.cf,
          Tape.counter'_inc hE.cs, hE.cr⟩
      have h2 := ih (b + 1) ⟨c.d, c.q, c.e, c.p, c.f, c.s + 1, c.r⟩ a _ (by omega) hE1
      rw [← hstate] at h2
      have := execA_loop_cont (Terminal := Terminal) (c := Cond9.v2NotEnd)
        (a := Act.V2 (sc := sc) Move.right) (w := W9.keep) (j := tV2) (mv := Move.right)
        (b := Prog.act (tCs, W9.blk, Move.right)) (ts := ts) rfl rfl rfl hcond h1 h2
      refine execA_of_eq ?_ this
      simp [v2csLoop, v2csUnit]

end Bottom

/-! ## 13. `subKLoop` の `k` 段 `seq` -/

section SubK

/-- `subKLoop … n` の有限制御版（`n` 段の `seq`）。 -/
def SUBK : ℕ → Prog A9 Cond9
  | 0 => Prog.skip
  | n + 1 => Prog.seq (Prog.seq ecProg qpProg) (SUBK n)

/-- `SUBK n` が実行する動作列。 -/
def subKActs (blank mark : Fin sc) (p : ℕ) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 =>
      ((ecLoop blank p ++ dTest (ctCp : CT sc) blank mark) ++
        (qpLoop blank p ++ dTest (ctCq : CT sc) blank mark)) ++ subKActs blank mark p n

@[simp] theorem subKActs_length (blank mark : Fin sc) (p n : ℕ) :
    (subKActs blank mark p n).length = (subKLoop blank p n).length + 4 * n := by
  induction n with
  | zero => simp [subKActs, subKLoop]
  | succ n ih =>
      simp only [subKActs, subKLoop, List.length_append, ih, ecLoop_length, qpLoop_length,
        dTest_length]
      omega

variable {Terminal : Type} {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

theorem SUBK_exec (hmark : mark ≠ blank) (p : ℕ) :
    ∀ (n a b D E F S R : ℕ) (ts : Tapes sc),
      Enc blank startSym endSym mark x a b ⟨D, 0, E + n * p, p, F, S, R⟩ ts →
        ExecA Terminal blank endSym mark (SUBK n) ts (subKActs blank mark p n) := by
  intro n
  induction n with
  | zero => intro a b D E F S R ts _; exact execA_skip
  | succ n ih =>
      intro a b D E F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b
          ⟨D, 0, (E + n * p) + p, 0 + p, F, S, R⟩ ts := by
        have e1 : E + (n + 1) * p = (E + n * p) + p := by ring
        have e2 : (0 : ℕ) + p = p := by omega
        rw [← e1, e2]; exact hE
      -- `ecProg`：`Cp` を `Cq` へ（`Ce` も減る）
      have h1 := ecProg_exec (Terminal := Terminal) (endSym := endSym) hmark p ts
        (show PalPeg.Tape.CounterView' blank mark ts.Cp p by simpa using hE.cp)
      have e1 := ecLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) p a b D 0 (E + n * p) 0 F S R ts hE'
      have e1' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) e1
      rw [← applyActs_append] at e1'
      set ts1 := applyActs blank (ecLoop blank p ++ dTest (ctCp : CT sc) blank mark) ts
        with hts1
      -- `qpProg`：`Cq` を `Cp` へ戻す
      have h2 := qpProg_exec (Terminal := Terminal) (endSym := endSym) hmark p ts1
        (show PalPeg.Tape.CounterView' blank mark ts1.Cq p by simpa using e1'.cq)
      have e2 := qpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) p a b D 0 (E + n * p) 0 F S R ts1 (by simpa using e1')
      have e2' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) e2
      rw [← applyActs_append] at e2'
      set ts2 := applyActs blank (qpLoop blank p ++ dTest (ctCq : CT sc) blank mark) ts1
        with hts2
      have h3 := ih a b D E F S R ts2 (by simpa using e2')
      have hst2 : applyActs blank ((ecLoop blank p ++ dTest (ctCp : CT sc) blank mark) ++
          (qpLoop blank p ++ dTest (ctCq : CT sc) blank mark)) ts = ts2 := by
        rw [applyActs_append, hts2, hts1]
      rw [← hst2] at h3
      exact execA_seq' (execA_seq' h1 h2 rfl) h3 rfl

/-- `SUBK` 実行後の符号化（`subKLoop_enc` と同じ）。 -/
theorem SUBK_enc (p : ℕ) : ∀ (n a b D E F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, 0, E + n * p, p, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, 0, E, p, F, S, R⟩
        (applyActs blank (subKActs blank mark p n) ts) := by
  intro n
  induction n with
  | zero => intro a b D E F S R ts hE; simpa [subKActs] using hE
  | succ n ih =>
      intro a b D E F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b
          ⟨D, 0, (E + n * p) + p, 0 + p, F, S, R⟩ ts := by
        have e1 : E + (n + 1) * p = (E + n * p) + p := by ring
        have e2 : (0 : ℕ) + p = p := by omega
        rw [← e1, e2]; exact hE
      have e1 := ecLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) p a b D 0 (E + n * p) 0 F S R ts hE'
      have e1' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) e1
      rw [← applyActs_append] at e1'
      set ts1 := applyActs blank (ecLoop blank p ++ dTest (ctCp : CT sc) blank mark) ts
        with hts1
      have e2 := qpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) p a b D 0 (E + n * p) 0 F S R ts1 (by simpa using e1')
      have e2' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) e2
      rw [← applyActs_append] at e2'
      set ts2 := applyActs blank (qpLoop blank p ++ dTest (ctCq : CT sc) blank mark) ts1
        with hts2
      have h3 := ih a b D E F S R ts2 (by simpa using e2')
      have hst : applyActs blank (subKActs blank mark p (n + 1)) ts
          = applyActs blank (subKActs blank mark p n) ts2 := by
        rw [subKActs, applyActs_append, applyActs_append, hts2, hts1]
      rw [hst]
      exact h3

end SubK

/-! ## 14. `perUnit` / `rewindUnit` の並べ替え版

元の単位は駆動 probe の**前**に `V1`（と `V2`）の移動を置いているため
`DLOOP` の形（`[c blank .left, c blank .stay] ++ rest`）に合わない。
触れるテープが全部異なるので、動作を並べ替えても**テープの終状態は同一**であり、
`_enc` はそのまま移植できる。 -/

section Reorder

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

/-- `perUnit` の並べ替え版（駆動 `Cq` の probe を先頭に）。 -/
def perUnit' (blank : Fin sc) : List (Act sc) :=
  [Act.Cq blank Move.left, Act.Cq blank Move.stay, Act.V1 Move.left,
    Act.Cp blank Move.right, Act.Cf blank Move.left, Act.Cf blank Move.stay,
    Act.Ce blank Move.right]

def perLoop1' (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => perUnit' blank ++ perLoop1' blank n

@[simp] theorem perLoop1'_length (blank : Fin sc) (n : ℕ) :
    (perLoop1' blank n).length = 7 * n := by
  induction n with
  | zero => simp [perLoop1']
  | succ n ih => simp only [perLoop1', List.length_append, perUnit', ih]; simp; omega

/-- 並べ替えてもテープの終状態は `perUnit` と完全に一致する。 -/
theorem applyActs_perUnit' (ts : Tapes sc) :
    applyActs blank (perUnit' blank) ts = applyActs blank (perUnit blank) ts := rfl

theorem perLoop1'_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) b ⟨D, Q + n, E, P, F + n, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P + n, F, S, R⟩
        (applyActs blank (perLoop1' blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [perLoop1'] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) b
          ⟨D, (Q + n) + 1, E, P, (F + n) + 1, S, R⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : Q + (n + 1) = (Q + n) + 1 := by omega
        have e3 : F + (n + 1) = (F + n) + 1 := by omega
        rw [e1, e2, e3] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x (a + n) b
          ⟨D, Q + n, E + 1, P + 1, F + n, S, R⟩ (applyActs blank (perUnit' blank) ts) := by
        rw [applyActs_perUnit', applyActs_perUnit]
        refine ⟨pat_left hE'.v1, hE'.v2, hE'.cd, ?_, Tape.counter'_inc hE'.ce,
          Tape.counter'_inc hE'.cp, ?_, hE'.cs, hE'.cr⟩
        · exact by simpa using Tape.counter'_dec (n := Q + n) hE'.cq
        · exact by simpa using Tape.counter'_dec (n := F + n) hE'.cf
      have := ih a b D Q (E + 1) (P + 1) F S R _ hstep
      have e4 : E + 1 + n = E + (n + 1) := by omega
      have e5 : P + 1 + n = P + (n + 1) := by omega
      rw [e4, e5] at this
      simp only [perLoop1', applyActs_append]
      exact this

/-- `perLoop1'` の 1 単位の残り動作。 -/
def perRestL (blank : Fin sc) : List (Act sc) :=
  [Act.V1 Move.left, Act.Cp blank Move.right, Act.Cf blank Move.left,
    Act.Cf blank Move.stay, Act.Ce blank Move.right]

/-- `perLoop1'` の 1 単位の残り部分のプログラム。 -/
def perRest : Prog A9 Cond9 :=
  Prog.seq (Prog.act (tV1, W9.keep, Move.left))
    (Prog.seq (Prog.act (tCp, W9.blk, Move.right))
      (Prog.seq (Prog.act (tCf, W9.blk, Move.left))
        (Prog.seq (Prog.act (tCf, W9.blk, Move.stay))
          (Prog.seq (Prog.act (tCe, W9.blk, Move.right)) Prog.skip))))

/-- `perLoop1'` の有限制御プログラム。 -/
def PER1 : Prog A9 Cond9 := DLOOP tCq perRest

variable {Terminal : Type}

theorem perRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark perRest ts (perRestL blank) := by
  have h : ∀ a ∈ perRestL (sc := sc) blank, OkAct blank mark a := by
    intro a ha
    fin_cases ha
    all_goals (intro ts; rfl)
  exact execA_progOf (perRestL blank) h ts

theorem perRest_get (ts : Tapes sc) :
    (ctCq : CT sc).get (applyActs blank (perRestL blank) ts) = (ctCq : CT sc).get ts := rfl

theorem per_dPow (n : ℕ) :
    dPow (ctCq : CT sc) blank (perRestL blank) n = perLoop1' blank n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dPow, ih]; rfl

/-- **`perLoop1'` の実現**（`Cq` を使い切る場合）。 -/
theorem PER1_exec (hmark : mark ≠ blank) (n : ℕ) (ts : Tapes sc)
    (hcv : PalPeg.Tape.CounterView' blank mark ts.Cq n) :
    ExecA Terminal blank endSym mark PER1 ts
      (perLoop1' blank n ++ dTest (ctCq : CT sc) blank mark) := by
  have h := dLoop_exec (Terminal := Terminal) (endSym := endSym) (ctCq : CT sc) perRest
    (perRestL blank) hmark (fun ts => perRest_exec ts) (fun ts => perRest_get ts) n ts hcv
  rw [per_dPow] at h
  exact h

/-! ### `rewindUnit` の並べ替え版 -/

/-- `rewindUnit` の並べ替え版（駆動 `Cq` の probe を先頭に）。 -/
def rewindUnit' (blank : Fin sc) : List (Act sc) :=
  [Act.Cq blank Move.left, Act.Cq blank Move.stay, Act.V1 Move.left, Act.V2 Move.left,
    Act.Cd blank Move.right]

theorem applyActs_rewindUnit' (ts : Tapes sc) :
    applyActs blank (rewindUnit' blank) ts = applyActs blank (rewindUnit blank) ts := rfl

/-- 巻き戻しループ（並べ替え版）。位相 `c` が `0` の回だけ `Ce` を 1 上げる。 -/
def rewindLoop' (blank : Fin sc) (k : ℕ) : ℕ → ℕ → List (Act sc)
  | 0, _ => []
  | n + 1, 0 => (rewindUnit' blank ++ [Act.Ce blank Move.right]) ++ rewindLoop' blank k n (k - 1)
  | n + 1, c + 1 => rewindUnit' blank ++ rewindLoop' blank k n c

theorem rewindLoop'_length (blank : Fin sc) (k : ℕ) : ∀ n c,
    (rewindLoop' blank k n c).length = 5 * n + stays k n c := by
  intro n
  induction n with
  | zero => intro c; simp [rewindLoop', stays]
  | succ n ih =>
      intro c
      cases c with
      | zero =>
          have h := ih (k - 1)
          simp only [rewindLoop', stays, List.length_append, rewindUnit', List.length_cons,
            List.length_nil, h]
          omega
      | succ c =>
          have h := ih c
          simp only [rewindLoop', stays, List.length_append, rewindUnit', List.length_cons,
            List.length_nil, h]
          omega

theorem rewind_unit'_enc {a b D Q E P F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (a + 1) (b + 1) ⟨D, Q + 1, E, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D + 1, Q, E, P, F, S, R⟩
      (applyActs blank (rewindUnit' blank) ts) := by
  rw [applyActs_rewindUnit']
  exact rewind_unit_enc hE

theorem rewind'_enc (k : ℕ) : ∀ (n c a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) (b + n) ⟨D, Q + n, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D + n, Q, E + stays k n c, P, F, S, R⟩
        (applyActs blank (rewindLoop' blank k n c) ts) := by
  intro n
  induction n with
  | zero => intro c a b D Q E P F S R ts hE; simpa [rewindLoop', stays] using hE
  | succ n ih =>
      intro c a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) (b + n + 1)
          ⟨D, (Q + n) + 1, E, P, F, S, R⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : b + (n + 1) = b + n + 1 := by omega
        have e3 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1, e2, e3] at hE
        exact hE
      have hstep := rewind_unit'_enc hE'
      cases c with
      | zero =>
          have hce : Enc blank startSym endSym mark x (a + n) (b + n)
              ⟨D + 1, Q + n, E + 1, P, F, S, R⟩
              (applyActs blank (rewindUnit' blank ++ [Act.Ce blank Move.right]) ts) := by
            rw [applyActs_append]
            refine ⟨hstep.v1, hstep.v2, hstep.cd, hstep.cq, ?_, hstep.cp, hstep.cf, hstep.cs,
              hstep.cr⟩
            exact Tape.counter'_inc hstep.ce
          have := ih (k - 1) a b (D + 1) Q (E + 1) P F S R _ hce
          simp only [rewindLoop', stays, applyActs_append]
          have e4 : D + 1 + n = D + (n + 1) := by omega
          have e5 : E + 1 + stays k n (k - 1) = E + (stays k n (k - 1) + 1) := by omega
          rw [e4, e5] at this
          exact this
      | succ c =>
          have := ih c a b (D + 1) Q E P F S R _ hstep
          simp only [rewindLoop', stays, applyActs_append]
          have e4 : D + 1 + n = D + (n + 1) := by omega
          rw [e4] at this
          exact this

end Reorder

/-! ## 15. `repoProg`：部分ドレイン `pvLoop (P-1)` の退避ガジェット

`repoProg` の末尾は `Cp` を `P` から `1` までしか減らさないので、
ゼロまで回す `DLOOP` では実現できない。そこで **一度ゼロまで回してから
`Cp` を 1 だけ戻し、`V2` も 1 セル右へ戻す**。テープの終状態は
`pvLoop blank (P-1)` を実行した場合と完全に一致する（`P ≥ 1` のとき）。 -/

section Repo

variable {Terminal : Type} {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

/-- 「`Cp` をゼロまで落としてから 1 だけ戻す」プログラム。 -/
def PVM1 : Prog A9 Cond9 :=
  Prog.seq pvProg
    (Prog.seq (Prog.act (tCp, W9.blk, Move.right)) (Prog.act (tV2, W9.keep, Move.right)))

/-- `PVM1` が実行する動作列。 -/
def pvm1Acts (blank mark : Fin sc) (P : ℕ) : List (Act sc) :=
  (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ++
    [Act.Cp blank Move.right, Act.V2 Move.right]

theorem pvm1Acts_length (blank mark : Fin sc) {P : ℕ} (hP : 0 < P) :
    (pvm1Acts blank mark P).length = (pvLoop blank (P - 1)).length + 7 := by
  simp only [pvm1Acts, List.length_append, pvLoop_length, dTest_length, List.length_cons,
    List.length_nil]
  omega

theorem PVM1_exec (hmark : mark ≠ blank) {a b D Q E F S R P : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ ts) :
    ExecA Terminal blank endSym mark PVM1 ts (pvm1Acts blank mark P) := by
  have h1 := pvProg_exec (Terminal := Terminal) (endSym := endSym) hmark P ts hE.cp
  have h2 : ExecA Terminal blank endSym mark (Prog.act (tCp, W9.blk, Move.right))
      (applyActs blank (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts)
      [Act.Cp blank Move.right] := execA_ct_put (ctCp : CT sc) Move.right _
  have h3 : ExecA Terminal blank endSym mark (Prog.act (tV2, W9.keep, Move.right))
      (applyActs blank [Act.Cp blank Move.right]
        (applyActs blank (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts))
      [Act.V2 Move.right] := execA_v2 Move.right _
  exact execA_seq' h1 (execA_seq' h2 h3 rfl) rfl

/-- **退避ガジェットの符号化**：`pvLoop (P-1)` と同じ効果。 -/
theorem PVM1_enc {s D F S R P : ℕ} {ts : Tapes sc} (hP : 0 < P)
    (hE : Enc blank startSym endSym mark x s (s + P) ⟨D, 0, 0, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, F, S, R⟩
      (applyActs blank (pvm1Acts blank mark P) ts) := by
  have e1 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s D 0 0 0 F S R ts
    (by rw [show (0 : ℕ) + P = P from by omega]; exact hE)
  have e1' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  rw [← applyActs_append] at e1'
  set ts1 := applyActs blank (pvLoop blank P ++ dTest (ctCp : CT sc) blank mark) ts with hts1
  have hs : s < x.length := by
    have := pat_le e1'.v2
    have hPle : s + P ≤ x.length := pat_le hE.v2
    omega
  have e2 : Enc blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, F, S, R⟩
      (applyActs blank [Act.Cp blank Move.right, Act.V2 Move.right] ts1) := by
    show Enc blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, F, S, R⟩
      { ts1 with
        Cp := Tape.step blank ts1.Cp blank Move.right
        V2 := Tape.step blank ts1.V2 ts1.V2.focus Move.right }
    exact ⟨e1'.v1, pat_right e1'.v2 hs, e1'.cd, e1'.cq, e1'.ce,
      Tape.counter'_inc e1'.cp, e1'.cf, e1'.cs, e1'.cr⟩
  rw [pvm1Acts, applyActs_append, ← hts1]
  exact e2

end Repo

/-! ## 16. 一般化駆動ループ（本体が状態に依存してよい）

`DLOOP` の本体 `rest` が実行する動作列が**状態に依存**してよい版。
比較ガジェットのように本体に `ite` が入る場合に必要になる。 -/

section DrivenLoopS

/-- probe と消去の 2 動作を適用した状態。 -/
def dStep (c : CT sc) (blank : Fin sc) (ts : Tapes sc) : Tapes sc :=
  applyAct blank (applyAct blank ts (c.act blank Move.left)) (c.act blank Move.stay)

/-- 本体を `n` 回まわしたときの動作列（状態依存版）。 -/
def dPowS (c : CT sc) (blank : Fin sc) (restL : Tapes sc → List (Act sc)) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      (c.act blank Move.left :: c.act blank Move.stay :: restL (dStep c blank ts)) ++
        dPowS c blank restL n
          (applyActs blank (restL (dStep c blank ts)) (dStep c blank ts))

private def dInnerS (c : CT sc) (blank : Fin sc) (restL : Tapes sc → List (Act sc)) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      (c.act blank Move.stay :: (restL (dStep c blank ts) ++ [c.act blank Move.left])) ++
        dInnerS c blank restL n
          (applyActs blank (restL (dStep c blank ts)) (dStep c blank ts))

private theorem dInnerS_eq (c : CT sc) (blank mark : Fin sc)
    (restL : Tapes sc → List (Act sc)) :
    ∀ (n : ℕ) (ts : Tapes sc),
      c.act blank Move.left :: (dInnerS c blank restL n ts ++ [c.act mark Move.right])
        = dPowS c blank restL n ts ++ dTest c blank mark := by
  intro n
  induction n with
  | zero => intro ts; rfl
  | succ n ih =>
      intro ts
      have h1 : dInnerS c blank restL (n + 1) ts
          = c.act blank Move.stay ::
            (restL (dStep c blank ts) ++ ([c.act blank Move.left] ++
              dInnerS c blank restL n
                (applyActs blank (restL (dStep c blank ts)) (dStep c blank ts)))) := by
        simp [dInnerS, List.append_assoc]
      have h2 : dPowS c blank restL (n + 1) ts
          = c.act blank Move.left ::
            (c.act blank Move.stay ::
              (restL (dStep c blank ts) ++
                dPowS c blank restL n
                  (applyActs blank (restL (dStep c blank ts)) (dStep c blank ts)))) := by
        simp [dPowS]
      rw [h1, h2]
      simp only [List.cons_append, List.append_assoc]
      rw [← ih]
      simp

/-- 長さの一様上界。 -/
theorem dPowS_length_le (c : CT sc) (blank : Fin sc) (restL : Tapes sc → List (Act sc))
    (L : ℕ) (hL : ∀ ts : Tapes sc, (restL ts).length ≤ L) :
    ∀ (n : ℕ) (ts : Tapes sc), (dPowS c blank restL n ts).length ≤ n * (L + 2) := by
  intro n
  induction n with
  | zero => intro ts; simp [dPowS]
  | succ n ih =>
      intro ts
      have h := ih (applyActs blank (restL (dStep c blank ts)) (dStep c blank ts))
      have hl := hL (dStep c blank ts)
      simp only [dPowS, List.length_append, List.length_cons]
      have : n * (L + 2) + (L + 2) = (n + 1) * (L + 2) := by ring
      omega

variable {Terminal : Type} {blank endSym mark : Fin sc}

private theorem dLoopS_body_exec (c : CT sc) (rest : Prog A9 Cond9)
    (restL : Tapes sc → List (Act sc)) (hmark : mark ≠ blank)
    (hrest : ∀ ts : Tapes sc, ExecA Terminal blank endSym mark rest ts (restL ts))
    (hrestget : ∀ ts : Tapes sc, c.get (applyActs blank (restL ts) ts) = c.get ts) :
    ∀ (n : ℕ) (ts : Tapes sc), PalPeg.Tape.CounterView' blank mark (c.get ts) n →
      ExecA Terminal blank endSym mark
        (Prog.loop (Cond9.notMark c.idx) (c.idx, W9.blk, Move.stay)
          (Prog.seq rest (Prog.act (c.idx, W9.blk, Move.left))))
        (applyAct blank ts (c.act blank Move.left)) (dInnerS c blank restL n ts) := by
  intro n
  induction n with
  | zero =>
      intro ts hcv
      refine execA_loop_stop ?_
      have hread : (getT (applyAct blank ts (c.act blank Move.left)) c.idx).focus = mark := by
        rw [c.get_eq, c.step_eq]
        exact (PalPeg.Tape.counter'_read_after_probe hcv).trans (by rw [if_pos rfl])
      simp only [condOf9, decide_eq_false_iff_not, not_not]
      exact hread
  | succ n ih =>
      intro ts hcv
      set ts0 := applyAct blank ts (c.act blank Move.left) with hts0
      have hread : (getT ts0 c.idx).focus = blank := by
        rw [hts0, c.get_eq, c.step_eq]
        exact (PalPeg.Tape.counter'_read_after_probe hcv).trans
          (by rw [if_neg (Nat.succ_ne_zero n)])
      have hcond : condOf9 endSym mark (Cond9.notMark c.idx)
          (fun j => (getT ts0 j).focus) = true := by
        simp only [condOf9, decide_eq_true_eq]
        rw [hread]
        exact Ne.symm hmark
      have hts1 : applyAct blank ts0 (c.act blank Move.stay) = dStep c blank ts := rfl
      have hcv1 : PalPeg.Tape.CounterView' blank mark (c.get (dStep c blank ts)) n := by
        rw [dStep, c.step_eq, c.step_eq]
        exact PalPeg.Tape.counter'_dec hcv
      set u := dStep c blank ts with hu
      set v := applyActs blank (restL u) u with hv
      have hcv2 : PalPeg.Tape.CounterView' blank mark (c.get v) n := by
        rw [hv, hrestget]; exact hcv1
      have hbody : ExecA Terminal blank endSym mark
          (Prog.seq rest (Prog.act (c.idx, W9.blk, Move.left))) u
          (restL u ++ [c.act blank Move.left]) :=
        execA_seq (hrest u) (execA_ct_put c Move.left v)
      have htail := ih v hcv2
      have hstate : applyActs blank (restL u ++ [c.act blank Move.left]) u
          = applyAct blank v (c.act blank Move.left) := by
        rw [applyActs_append]; rfl
      rw [← hstate] at htail
      have hres := execA_loop_cont (Terminal := Terminal) (c := Cond9.notMark c.idx)
        (a := c.act blank Move.stay) (w := W9.blk)
        (b := Prog.seq rest (Prog.act (c.idx, W9.blk, Move.left)))
        (ts := ts0) (c.tape_eq blank Move.stay) (c.move_eq blank Move.stay)
        (by simpa using (c.write_eq ts0 blank Move.stay).symm) hcond
        (by rw [hts1]; exact hbody) (by rw [hts1]; exact htail)
      refine execA_of_eq ?_ hres
      simp [dInnerS, hu, hv]

/-- **一般化駆動ループの主補題**。 -/
theorem dLoopS_exec (c : CT sc) (rest : Prog A9 Cond9) (restL : Tapes sc → List (Act sc))
    (hmark : mark ≠ blank)
    (hrest : ∀ ts : Tapes sc, ExecA Terminal blank endSym mark rest ts (restL ts))
    (hrestget : ∀ ts : Tapes sc, c.get (applyActs blank (restL ts) ts) = c.get ts)
    (n : ℕ) (ts : Tapes sc) (hcv : PalPeg.Tape.CounterView' blank mark (c.get ts) n) :
    ExecA Terminal blank endSym mark (DLOOP c.idx rest) ts
      (dPowS c blank restL n ts ++ dTest c blank mark) := by
  have h1 : ExecA Terminal blank endSym mark (Prog.act (c.idx, W9.blk, Move.left)) ts
      [c.act blank Move.left] := execA_ct_put c Move.left ts
  have h2 := dLoopS_body_exec (Terminal := Terminal) c rest restL hmark hrest hrestget n ts hcv
  have h3 : ExecA Terminal blank endSym mark (Prog.act (c.idx, W9.mrk, Move.right))
      (applyActs blank (dInnerS c blank restL n ts)
        (applyAct blank ts (c.act blank Move.left))) [c.act mark Move.right] :=
    execA_ct_mark c Move.right _
  have hs : ExecA Terminal blank endSym mark (DLOOP c.idx rest) ts
      ([c.act blank Move.left] ++ (dInnerS c blank restL n ts ++ [c.act mark Move.right])) := by
    refine execA_seq h1 (execA_seq ?_ ?_)
    · show ExecA Terminal blank endSym mark _ (applyActs blank [c.act blank Move.left] ts) _
      exact h2
    · show ExecA Terminal blank endSym mark _
        (applyActs blank (dInnerS c blank restL n ts)
          (applyActs blank [c.act blank Move.left] ts)) _
      exact h3
  refine execA_of_eq ?_ hs
  exact dInnerS_eq c blank mark restL n ts

end DrivenLoopS

/-! ## 17. カウンタ比較ガジェット `CMPLT`（`Cp` と `Cf`、`orcCf` 用）

`orcCf ts = decide (pOf ts < fOf ts)` を有限制御で判定する。
`orcCf_spec` の時点の符号化は `⟨(k-1)p', 0, 0, p', F, S, R⟩` なので
**`Cq` と `Ce` が空いている**。この 2 本を鏡像に使う。

アルゴリズム（`A = Cp`(値 `p`), `B = Cf`(値 `F`), `Am = Cq`, `Bm = Ce`）：

```
A を 0 まで駆動（p 回）:
   B を probe
   B ≠ 0 なら  B--, Bm++
   B = 0 なら  B を復元（何もしない）
   Am++
-- ここで  Am = p,  Bm = min p F,  B = F - min p F
B を probe:  B ≠ 0  ⟺  p < F        ← これが判定
復元: Bm を B へ戻し（cfProg）、Am を A へ戻す（qpProg）
```

判定 1 回のコストは `≤ 12p + 8` 動作で、`F` には依存しない。 -/

section Compare

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

/-- 比較ループ 1 単位の「残り」動作列（状態依存）。 -/
def cmpRestL (blank mark : Fin sc) (t : Tapes sc) : List (Act sc) :=
  Act.Cf blank Move.left ::
    ((if probe blank t.Cf = mark then [Act.Cf mark Move.right]
      else [Act.Cf blank Move.stay, Act.Ce blank Move.right]) ++ [Act.Cq blank Move.right])

/-- 比較ループ 1 単位の「残り」プログラム。 -/
def cmpRest : Prog A9 Cond9 :=
  Prog.seq (Prog.act (tCf, W9.blk, Move.left))
    (Prog.seq
      (Prog.ite (Cond9.notMark tCf)
        (Prog.seq (Prog.act (tCf, W9.blk, Move.stay)) (Prog.act (tCe, W9.blk, Move.right)))
        (Prog.act (tCf, W9.mrk, Move.right)))
      (Prog.act (tCq, W9.blk, Move.right)))

theorem cmpRestL_length_le (blank mark : Fin sc) (t : Tapes sc) :
    (cmpRestL blank mark t).length ≤ 4 := by
  rw [cmpRestL]
  split <;> simp

theorem applyActs_cmpRestL_zero (t : Tapes sc) (h : probe blank t.Cf = mark) :
    applyActs blank (cmpRestL blank mark t) t =
      { t with
        Cf := Tape.step blank (Tape.step blank t.Cf blank Move.left) mark Move.right
        Cq := Tape.step blank t.Cq blank Move.right } := by
  rw [cmpRestL, if_pos h]; rfl

theorem applyActs_cmpRestL_pos (t : Tapes sc) (h : ¬ probe blank t.Cf = mark) :
    applyActs blank (cmpRestL blank mark t) t =
      { t with
        Cf := Tape.step blank (Tape.step blank t.Cf blank Move.left) blank Move.stay
        Ce := Tape.step blank t.Ce blank Move.right
        Cq := Tape.step blank t.Cq blank Move.right } := by
  rw [cmpRestL, if_neg h]; rfl

/-- `Cp` は比較ループの本体では触られない。 -/
theorem cmpRestL_get (t : Tapes sc) :
    (ctCp : CT sc).get (applyActs blank (cmpRestL blank mark t) t)
      = (ctCp : CT sc).get t := by
  by_cases h : probe blank t.Cf = mark
  · rw [applyActs_cmpRestL_zero t h]; rfl
  · rw [applyActs_cmpRestL_pos t h]; rfl

variable {Terminal : Type}

theorem cmpRest_exec (t : Tapes sc) :
    ExecA Terminal blank endSym mark cmpRest t (cmpRestL blank mark t) := by
  have h1 : ExecA Terminal blank endSym mark (Prog.act (tCf, W9.blk, Move.left)) t
      [Act.Cf blank Move.left] := execA_ct_put (ctCf : CT sc) Move.left t
  set t1 := applyActs blank [Act.Cf (sc := sc) blank Move.left] t with ht1
  have hfoc : (getT t1 tCf).focus = probe blank t.Cf := rfl
  have hmid : ExecA Terminal blank endSym mark
      (Prog.ite (Cond9.notMark tCf)
        (Prog.seq (Prog.act (tCf, W9.blk, Move.stay)) (Prog.act (tCe, W9.blk, Move.right)))
        (Prog.act (tCf, W9.mrk, Move.right))) t1
      (if probe blank t.Cf = mark then [Act.Cf mark Move.right]
        else [Act.Cf blank Move.stay, Act.Ce blank Move.right]) := by
    by_cases h : probe blank t.Cf = mark
    · rw [if_pos h]
      refine execA_ite_neg ?_ (execA_ct_mark (ctCf : CT sc) Move.right t1)
      simp only [condOf9, decide_eq_false_iff_not, not_not]
      rw [hfoc]; exact h
    · rw [if_neg h]
      refine execA_ite_pos ?_ ?_
      · simp only [condOf9, decide_eq_true_eq]
        rw [hfoc]; exact h
      · exact execA_seq (execA_ct_put (ctCf : CT sc) Move.stay t1)
          (execA_ct_put (ctCe : CT sc) Move.right _)
  have hlast : ExecA Terminal blank endSym mark (Prog.act (tCq, W9.blk, Move.right))
      (applyActs blank
        (if probe blank t.Cf = mark then [Act.Cf mark Move.right]
          else [Act.Cf blank Move.stay, Act.Ce blank Move.right]) t1)
      [Act.Cq blank Move.right] := execA_ct_put (ctCq : CT sc) Move.right _
  refine execA_seq' h1 (execA_seq' hmid hlast rfl) ?_
  rw [cmpRestL]
  rfl

/-- **比較ループの符号化**：`Cp = n` から回すと
`Cq = Q + n`, `Ce = E + min n F`, `Cf = F - min n F`, `Cp = 0` になる。 -/
theorem cmp_dPowS_enc (hmark : mark ≠ blank) :
    ∀ (n a b D Q E F S R : ℕ) (t : Tapes sc),
      Enc blank startSym endSym mark x a b ⟨D, Q, E, n, F, S, R⟩ t →
        Enc blank startSym endSym mark x a b
          ⟨D, Q + n, E + min n F, 0, F - min n F, S, R⟩
          (applyActs blank (dPowS (ctCp : CT sc) blank (cmpRestL blank mark) n t) t) := by
  intro n
  induction n with
  | zero => intro a b D Q E F S R t hE; simpa [dPowS] using hE
  | succ n ih =>
      intro a b D Q E F S R t hE
      rw [dPowS, applyActs_append]
      -- probe と消去で `Cp` が 1 減る
      set u := dStep (ctCp : CT sc) blank t with hu
      have hEu : Enc blank startSym endSym mark x a b ⟨D, Q, E, n, F, S, R⟩ u := by
        rw [hu]
        show Enc blank startSym endSym mark x a b ⟨D, Q, E, n, F, S, R⟩
          { t with Cp := Tape.step blank (Tape.step blank t.Cp blank Move.left) blank Move.stay }
        exact ⟨hE.v1, hE.v2, hE.cd, hE.cq, hE.ce,
          by simpa using Tape.counter'_dec (n := n) hE.cp, hE.cf, hE.cs, hE.cr⟩
      have hprobe : probe blank u.Cf = mark ↔ F = 0 := probe_iff hmark hEu.cf
      cases F with
      | zero =>
          have hz : probe blank u.Cf = mark := hprobe.2 rfl
          have hEv : Enc blank startSym endSym mark x a b ⟨D, Q + 1, E, n, 0, S, R⟩
              (applyActs blank (cmpRestL blank mark u) u) := by
            rw [applyActs_cmpRestL_zero u hz]
            exact ⟨hEu.v1, hEu.v2, hEu.cd, Tape.counter'_inc hEu.cq, hEu.ce, hEu.cp,
              Tape.counter'_dec_zero hEu.cf, hEu.cs, hEu.cr⟩
          have h := ih a b D (Q + 1) E 0 S R _ hEv
          have e1 : Q + (n + 1) = Q + 1 + n := by omega
          have e2 : min (n + 1) 0 = 0 := by omega
          have e3 : min n 0 = 0 := by omega
          rw [e3] at h
          rw [e1, e2]
          exact h
      | succ F' =>
          have hz : ¬ probe blank u.Cf = mark := fun hc => by simpa using hprobe.1 hc
          have hEv : Enc blank startSym endSym mark x a b ⟨D, Q + 1, E + 1, n, F', S, R⟩
              (applyActs blank (cmpRestL blank mark u) u) := by
            rw [applyActs_cmpRestL_pos u hz]
            exact ⟨hEu.v1, hEu.v2, hEu.cd, Tape.counter'_inc hEu.cq,
              Tape.counter'_inc hEu.ce, hEu.cp,
              by simpa using Tape.counter'_dec (n := F') hEu.cf, hEu.cs, hEu.cr⟩
          have h := ih a b D (Q + 1) (E + 1) F' S R _ hEv
          have e1 : Q + 1 + n = Q + (n + 1) := by omega
          have e2 : E + 1 + min n F' = E + min (n + 1) (F' + 1) := by omega
          have e3 : F' - min n F' = F' + 1 - min (n + 1) (F' + 1) := by omega
          rw [e1, e2, e3] at h
          exact h

/-! ### 判定と復元 -/

/-- 判定の 2 動作（probe と復元）。 -/
def cmpDecideL (blank : Fin sc) (t : Tapes sc) : List (Act sc) :=
  [Act.Cf blank Move.left, Act.Cf (probe blank t.Cf) Move.right]

/-- 鏡像から `Cf` と `Cp` を復元する動作列。 -/
def cmpRestoreActs (blank mark : Fin sc) (p F : ℕ) : List (Act sc) :=
  (cfLoop blank (min p F) ++ dTest (ctCe : CT sc) blank mark) ++
    (qpLoop blank p ++ dTest (ctCq : CT sc) blank mark)

/-- 比較ループ直後の状態。 -/
def cmpT1 (blank mark : Fin sc) (p : ℕ) (t : Tapes sc) : Tapes sc :=
  applyActs blank
    (dPowS (ctCp : CT sc) blank (cmpRestL blank mark) p t ++ dTest (ctCp : CT sc) blank mark) t

/-- 比較ガジェット全体が実行する動作列。 -/
def cmpActs (blank mark : Fin sc) (p F : ℕ) (t : Tapes sc) : List (Act sc) :=
  (dPowS (ctCp : CT sc) blank (cmpRestL blank mark) p t ++ dTest (ctCp : CT sc) blank mark) ++
    (cmpDecideL blank (cmpT1 blank mark p t) ++ cmpRestoreActs blank mark p F)

/-- **比較 1 回のコスト**：`≤ 12p + 8`（`F` には依存しない）。 -/
theorem cmpActs_length_le (blank mark : Fin sc) (p F : ℕ) (t : Tapes sc) :
    (cmpActs blank mark p F t).length ≤ 12 * p + 8 := by
  have hd := dPowS_length_le (ctCp : CT sc) blank (cmpRestL blank mark) 4
    (fun t => cmpRestL_length_le blank mark t) p t
  have hmin : min p F ≤ p := Nat.min_le_left _ _
  simp only [cmpActs, cmpRestoreActs, cmpDecideL, List.length_append, dTest_length,
    cfLoop_length, qpLoop_length, List.length_cons, List.length_nil]
  omega

/-- 復元プログラム。 -/
def CMPRESTORE : Prog A9 Cond9 := Prog.seq cfProg qpProg

/-- **比較ガジェット**：`pOf t < fOf t` なら `THEN`、そうでなければ `ELSE` を実行する。 -/
def CMPLT_PF (THEN ELSE : Prog A9 Cond9) : Prog A9 Cond9 :=
  Prog.seq (DLOOP tCp cmpRest)
    (Prog.seq (Prog.act (tCf, W9.blk, Move.left))
      (Prog.ite (Cond9.notMark tCf)
        (Prog.seq (Prog.act (tCf, W9.blk, Move.right)) (Prog.seq CMPRESTORE THEN))
        (Prog.seq (Prog.act (tCf, W9.mrk, Move.right)) (Prog.seq CMPRESTORE ELSE))))

section CmpSpec

variable {Terminal : Type}

/-- 比較ループ直後の符号化。 -/
theorem cmpT1_enc (hmark : mark ≠ blank) {a b D S R p F : ℕ} {t : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, 0, 0, p, F, S, R⟩ t) :
    Enc blank startSym endSym mark x a b
      ⟨D, p, min p F, 0, F - min p F, S, R⟩ (cmpT1 blank mark p t) := by
  have e1 := cmp_dPowS_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) hmark p a b D 0 0 F S R t (by simpa using hE)
  have e1' := dTest_enc_Cp (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (by simpa using e1)
  rw [← applyActs_append] at e1'
  simpa [cmpT1] using e1'

/-- 判定 2 動作は符号化を保つ。 -/
theorem cmpDecide_enc {a b : ℕ} {c : Ctr} {t : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c t) :
    Enc blank startSym endSym mark x a b c (applyActs blank (cmpDecideL blank t) t) := by
  show Enc blank startSym endSym mark x a b c
    { t with
      Cf := Tape.step blank (Tape.step blank t.Cf blank Move.left) (probe blank t.Cf)
        Move.right }
  exact ⟨hE.v1, hE.v2, hE.cd, hE.cq, hE.ce, hE.cp, counter'_test hE.cf, hE.cs, hE.cr⟩

/-- **比較ガジェットは非破壊**：終状態の符号化は入口と同じ。 -/
theorem cmpActs_enc (hmark : mark ≠ blank) {a b D S R p F : ℕ} {t : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, 0, 0, p, F, S, R⟩ t) :
    Enc blank startSym endSym mark x a b ⟨D, 0, 0, p, F, S, R⟩
      (applyActs blank (cmpActs blank mark p F t) t) := by
  have e1 := cmpT1_enc (startSym := startSym) hmark hE
  have e2 := cmpDecide_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  set t2 := applyActs blank (cmpDecideL blank (cmpT1 blank mark p t)) (cmpT1 blank mark p t)
    with ht2
  have e3 := cfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (min p F) a b D p 0 0 (F - min p F) S R t2 (by simpa using e2)
  have e3' := dTest_enc_Ce (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e3
  rw [← applyActs_append] at e3'
  set t3 := applyActs blank (cfLoop blank (min p F) ++ dTest (ctCe : CT sc) blank mark) t2
    with ht3
  have hF : F - min p F + min p F = F := by omega
  rw [hF] at e3'
  have e4 := qpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p a b D 0 0 0 F S R t3
    (by rw [show (0 : ℕ) + p = p from by omega]; exact e3')
  have e4' := dTest_enc_Cq (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e4
  rw [← applyActs_append] at e4'
  have hst : applyActs blank (cmpActs blank mark p F t) t
      = applyActs blank (qpLoop blank p ++ dTest (ctCq : CT sc) blank mark) t3 := by
    rw [cmpActs, ht3, ht2, cmpT1]
    simp only [cmpRestoreActs, applyActs_append]
  rw [hst]
  simpa using e4'

/-- 復元プログラムの実行。 -/
theorem CMPRESTORE_exec (hmark : mark ≠ blank) {a b D S R p F : ℕ} {t2 : Tapes sc}
    (hE2 : Enc blank startSym endSym mark x a b
      ⟨D, p, min p F, 0, F - min p F, S, R⟩ t2) :
    ExecA Terminal blank endSym mark CMPRESTORE t2 (cmpRestoreActs blank mark p F) := by
  have h4 := cfProg_exec (Terminal := Terminal) (endSym := endSym) hmark (min p F) t2 hE2.ce
  have e3 := cfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (min p F) a b D p 0 0 (F - min p F) S R t2 (by simpa using hE2)
  have e3' := dTest_enc_Ce (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e3
  rw [← applyActs_append] at e3'
  set t3 := applyActs blank (cfLoop blank (min p F) ++ dTest (ctCe : CT sc) blank mark) t2
    with ht3
  have h5 := qpProg_exec (Terminal := Terminal) (endSym := endSym) hmark p t3
    (show PalPeg.Tape.CounterView' blank mark t3.Cq p by simpa using e3'.cq)
  exact execA_seq' h4 h5 rfl

/-- **比較ガジェットの実行**。`p < F` なら `THEN`、そうでなければ `ELSE` に進む。
実行される動作列は `cmpActs`（`≤ 12p + 8` 動作）に続く枝の動作列。 -/
theorem CMPLT_PF_exec (hmark : mark ≠ blank) {THEN ELSE : Prog A9 Cond9}
    {a b D S R p F : ℕ} {t : Tapes sc} {LT LE : List (Act sc)}
    (hE : Enc blank startSym endSym mark x a b ⟨D, 0, 0, p, F, S, R⟩ t)
    (hthen : p < F → ExecA Terminal blank endSym mark THEN
      (applyActs blank (cmpActs blank mark p F t) t) LT)
    (helse : ¬ p < F → ExecA Terminal blank endSym mark ELSE
      (applyActs blank (cmpActs blank mark p F t) t) LE) :
    ExecA Terminal blank endSym mark (CMPLT_PF THEN ELSE) t
      (cmpActs blank mark p F t ++ (if p < F then LT else LE)) := by
  -- 比較ループ
  have h1 := dLoopS_exec (Terminal := Terminal) (endSym := endSym) (ctCp : CT sc) cmpRest
    (cmpRestL blank mark) hmark (fun t => cmpRest_exec t) (fun t => cmpRestL_get t) p t hE.cp
  have e1 := cmpT1_enc (startSym := startSym) hmark hE
  set t1 := cmpT1 blank mark p t with ht1
  have hst1 : applyActs blank
      (dPowS (ctCp : CT sc) blank (cmpRestL blank mark) p t ++ dTest (ctCp : CT sc) blank mark)
      t = t1 := by rw [ht1, cmpT1]
  -- 判定の probe
  have h2 : ExecA Terminal blank endSym mark (Prog.act (tCf, W9.blk, Move.left)) t1
      [Act.Cf blank Move.left] := execA_ct_put (ctCf : CT sc) Move.left t1
  set t1' := applyActs blank [Act.Cf (sc := sc) blank Move.left] t1 with ht1'
  have hfoc : (getT t1' tCf).focus = probe blank t1.Cf := rfl
  have hpe : probe blank t1.Cf = if F - min p F = 0 then mark else blank := probe_eq e1.cf
  -- 判定後の状態と復元
  have e2 := cmpDecide_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) e1
  set t2 := applyActs blank (cmpDecideL blank t1) t1 with ht2
  have hrest := CMPRESTORE_exec (Terminal := Terminal) (startSym := startSym) (x := x)
    hmark e2
  have hstate : applyActs blank (cmpRestoreActs blank mark p F) t2
      = applyActs blank (cmpActs blank mark p F t) t := by
    rw [cmpActs, applyActs_append, applyActs_append, hst1, ht2, ht1]
  by_cases hlt : p < F
  · -- `Cf` が残っている枝
    have hne : F - min p F ≠ 0 := by omega
    have hprobe : probe blank t1.Cf = blank := by rw [hpe, if_neg hne]
    have hdec : cmpDecideL blank t1
        = [Act.Cf blank Move.left] ++ [Act.Cf blank Move.right] := by
      rw [cmpDecideL, hprobe]; rfl
    have hbr : ExecA Terminal blank endSym mark (Prog.act (tCf, W9.blk, Move.right)) t1'
        [Act.Cf blank Move.right] := execA_ct_put (ctCf : CT sc) Move.right t1'
    have hst2 : applyActs blank [Act.Cf (sc := sc) blank Move.right] t1' = t2 := by
      rw [ht2, hdec, ht1', applyActs_append]
    have hite : ExecA Terminal blank endSym mark
        (Prog.ite (Cond9.notMark tCf)
          (Prog.seq (Prog.act (tCf, W9.blk, Move.right)) (Prog.seq CMPRESTORE THEN))
          (Prog.seq (Prog.act (tCf, W9.mrk, Move.right)) (Prog.seq CMPRESTORE ELSE))) t1'
        ([Act.Cf blank Move.right] ++ (cmpRestoreActs blank mark p F ++ LT)) := by
      refine execA_ite_pos ?_ ?_
      · simp only [condOf9, decide_eq_true_eq]
        rw [hfoc, hprobe]
        exact Ne.symm hmark
      · refine execA_seq hbr ?_
        rw [hst2]
        exact execA_seq hrest (by rw [hstate]; exact hthen hlt)
    have := execA_seq h1 (execA_seq (by rw [hst1]; exact h2) (by rw [hst1, ← ht1']; exact hite))
    refine execA_of_eq ?_ this
    rw [if_pos hlt, cmpActs, hdec]
    simp [List.append_assoc]
  · -- `Cf` を使い切った枝
    have hz : F - min p F = 0 := by omega
    have hprobe : probe blank t1.Cf = mark := by rw [hpe, if_pos hz]
    have hdec : cmpDecideL blank t1
        = [Act.Cf blank Move.left] ++ [Act.Cf mark Move.right] := by
      rw [cmpDecideL, hprobe]; rfl
    have hbr : ExecA Terminal blank endSym mark (Prog.act (tCf, W9.mrk, Move.right)) t1'
        [Act.Cf mark Move.right] := execA_ct_mark (ctCf : CT sc) Move.right t1'
    have hst2 : applyActs blank [Act.Cf (sc := sc) mark Move.right] t1' = t2 := by
      rw [ht2, hdec, ht1', applyActs_append]
    have hite : ExecA Terminal blank endSym mark
        (Prog.ite (Cond9.notMark tCf)
          (Prog.seq (Prog.act (tCf, W9.blk, Move.right)) (Prog.seq CMPRESTORE THEN))
          (Prog.seq (Prog.act (tCf, W9.mrk, Move.right)) (Prog.seq CMPRESTORE ELSE))) t1'
        ([Act.Cf mark Move.right] ++ (cmpRestoreActs blank mark p F ++ LE)) := by
      refine execA_ite_neg ?_ ?_
      · simp only [condOf9, decide_eq_false_iff_not, not_not]
        rw [hfoc, hprobe]
      · refine execA_seq hbr ?_
        rw [hst2]
        exact execA_seq hrest (by rw [hstate]; exact helse hlt)
    have := execA_seq h1 (execA_seq (by rw [hst1]; exact h2) (by rw [hst1, ← ht1']; exact hite))
    refine execA_of_eq ?_ this
    rw [if_neg hlt, cmpActs, hdec]
    simp [List.append_assoc]

/-- `CMPLT_PF` の分岐は `orcCf` と一致する。 -/
theorem orcCf_eq_lt {a b D S R p F : ℕ} {t : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, 0, 0, p, F, S, R⟩ t) :
    orcCf t = decide (p < F) := by
  simp [orcCf, pOf_eq hE, fOf_eq hE]

end CmpSpec



end Compare


/-! ## 18. まとめと残っている作業

本ファイルで新たに閉じたもの：

* `BOTTOM`（`bottomProg` の番人駆動版）。`|x|` を数として持たずに
  `Cs := |x|` を実現する。動作列は `v2csLoop blank (|x| - b)`（`2(|x|-b)` 動作）。
* `SUBK n`（`subKLoop … n` の `n` 段 `seq`）。`SUBK_exec` / `SUBK_enc`。
  追加コストは `4n` 動作（ゼロ判定 2 動作 × 2 × `n`）。
* `perUnit'` / `rewindUnit'`（並べ替え版）と `perLoop1'_enc` / `rewind'_enc`。
  並べ替えてもテープの終状態は完全に同一（`applyActs_perUnit'` / `applyActs_rewindUnit'`）。
  `perLoop1'` は `PER1 = DLOOP tCq perRest` として有限制御化済み（`Cq` を使い切る場合）。
* `PVM1`（`repoProg` の部分ドレイン `pvLoop (P-1)` の退避ガジェット）。
  `Cp` をゼロまで落としてから 1 だけ戻し、`V2` も 1 セル右へ戻す。
  `PVM1_enc` により終状態は `pvLoop (P-1)` と完全一致（`0 < P` のとき）。
  追加コストは 7 動作。
* `dLoopS_exec`：本体が**状態依存**でよい一般化駆動ループ。`ite` を含む本体
  （比較ガジェットなど）を有限制御ループに載せるための鍵。
* **比較ガジェット `CMPLT_PF`**：`Cp` と `Cf` を鏡像 `Cq` / `Ce` で
  ロックステップに減らして `pOf < fOf` を判定し、完全に復元する。
  - `CMPLT_PF_exec`：`p < F` なら `THEN`、そうでなければ `ELSE` に進む。
  - `cmpActs_enc`：**非破壊**（終状態の符号化は入口と同じ）。
  - `cmpActs_length_le`：**判定 1 回のコストは `≤ 12p + 8` 動作**（`F` に依存しない）。
  - `orcCf_eq_lt`：分岐条件が `orcCf` と一致する。

### まだ残っていること

1. **`orcR` / `orc2R` の比較ガジェットは作れていない。** 理由は資源不足である：
   `orcCf` の判定点では符号化が `⟨(k-1)p', 0, 0, p', F, S, R⟩` で `Cq` と `Ce` が
   確実に空なので鏡像 2 本が取れるが、`orcR_spec` / `orc2R_spec` の判定点の符号化は
   `⟨D', q', E', p', F', S', r⟩` で **`D'`, `E'`, `S'` がすべて自由変数**であり、
   空きテープが 1 本も保証されない。したがって
   (a) 周囲の仕様を強めて判定点で `E' = 0`（あるいは `D' = 0`）を示すか、
   (b) テープを 1〜2 本増やすか、
   のどちらかが先に必要である。`k` 倍の比較（`(k-1)·Cp` や `k·Cf`）自体は
   駆動 1 回につき `k` 段のロックステップを踏むだけなので、鏡像さえ確保できれば
   `CMPLT_PF` と同じ構成でできる（コストは `≤ c·k·(値)`）。
2. `rewindLoop'` の**有限制御版**（mod `k` 位相）。位相を空きカウンタ 1 本に持たせて
   `dLoopS_exec` で回せばよいが、`rewindLoop` の使用点でも空きテープの確保が要る。
3. `repoProg` / `advanceProg` 全体の `_exec`（部品はすべて揃った：`PVM1`, `SUBK`,
   および第 1 部の各 `*Prog_exec`）。
4. `mProg` / `rProg` / `sProg`、`oProg` / `fpProg` / `frProg` / `soProg` / `spProg` /
   `stepProg` / `stripProg2`、そして `decProgP` の組み立てと
   `decProgP_length_le` の係数の取り直し。これは 1 と 2 が片づいてからの作業になる。

### コスト計上について（判明していること）

`orcCf` の判定は `stripProg2` の 1 反復につき 1 回起き、そのコストは `≤ 12p + 8`
（`p = pOf ts`）。同じ反復の `fpProg` はすでに `firstOuterWork ≥ p` を払っているので、
この比較は既存の項に定数倍で吸収できる。`SUBK` の `+4k`、`PVM1` の `+7`、
各ループの `+2`（ゼロ判定）も同様に反復あたり定数である。
したがって最終的な係数 `A`, `B` は
`A' = A + O(1)`, `B' = B + O(k)` の形になる見込みだが、
`orcR` / `orc2R` が未解決なので確定した値はまだ出せない。
-/

section AxiomCheck2

#print axioms BOTTOM_exec
#print axioms v2csLoop_enc
#print axioms SUBK_exec
#print axioms SUBK_enc
#print axioms perLoop1'_enc
#print axioms PER1_exec
#print axioms rewind'_enc
#print axioms PVM1_exec
#print axioms PVM1_enc
#print axioms dLoopS_exec
#print axioms cmpRest_exec
#print axioms cmp_dPowS_enc
#print axioms cmpActs_length_le
#print axioms cmpActs_enc
#print axioms CMPRESTORE_exec
#print axioms CMPLT_PF_exec
#print axioms orcCf_eq_lt

end AxiomCheck2

end PalPeg.GSPreProg
