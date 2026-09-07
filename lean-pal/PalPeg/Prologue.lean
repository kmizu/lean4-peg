import PalPeg.TapeLib
import PalPeg.InputCopy

/-!
# `Prologue`：`minit_encodes` の前提を作る小さなテープ・プログラム

`MiddleTapes.minit_encodes` は各種テープが特定のビュー（入力コピーの最前線が
`[leftSym]`、フラグテープが長さ `≥ Lmax S + 1` の全 `zero` 語をヘッド `0` で持つ）に
あることを仮定する。ここでは、それらのビューを空白テープから作るための小さなプログラム
（1 テープぶんの `(記号, 移動)` 列）を用意し、使った動作数を明示する。

* `runProg`        — テープ 1 本に対する `(記号, 移動)` の列を順に適用する薄い実行器。
* `writeWord`      — 空スタックから語 `l` を書いて先頭（`index 0`）へ戻る：`2 * l.length` 動作。
* `writeZeros`     — `writeWord` の系：全 `zero` の語（フラグテープ用）。
* `writeSingleton` — 空スタックから `[leftSym]` を書いて空白セルに戻す：`1` 動作。
* `clearTape`      — スタック内容をすべて消して空スタックへ戻す：`2 * l.length ≤ 2 * n + 2` 動作。
* `spreadClear`    — 上記のプログラムを `c + 1` 動作以下のチャンクに分割できること。
-/

namespace PalPeg.GSTapes

open PalPeg.Tape PegSeparation.RealTimeTM

variable {k : ℕ}

/-- 1 本のテープに対する「書いて動く」動作の列。 -/
abbrev TapeProg (k : ℕ) := List (Fin k × Move)

/-- 動作列を順に適用する。 -/
def runProg (blank : Fin k) (tp : TapeConfiguration k) : TapeProg k → TapeConfiguration k
  | [] => tp
  | (a, m) :: rest => runProg blank (step blank tp a m) rest

@[simp] theorem runProg_nil (blank : Fin k) (tp : TapeConfiguration k) :
    runProg blank tp ([] : TapeProg k) = tp := rfl

@[simp] theorem runProg_cons (blank : Fin k) (tp : TapeConfiguration k)
    (a : Fin k) (m : Move) (rest : TapeProg k) :
    runProg blank tp ((a, m) :: rest) = runProg blank (step blank tp a m) rest := rfl

/-- 動作列の連結は、実行の合成に対応する。 -/
theorem runProg_append (blank : Fin k) (tp : TapeConfiguration k) (p₁ p₂ : TapeProg k) :
    runProg blank tp (p₁ ++ p₂) = runProg blank (runProg blank tp p₁) p₂ := by
  induction p₁ generalizing tp with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨a, m⟩ := hd
      simp only [List.cons_append, runProg_cons, ih]

/-- チャンクの列を `flatten` してから実行するのは、各チャンクを順に実行する（`foldl`）のと同じ。 -/
theorem runProg_join (blank : Fin k) (tp : TapeConfiguration k) (chunks : List (TapeProg k)) :
    runProg blank tp chunks.flatten = chunks.foldl (fun s q => runProg blank s q) tp := by
  induction chunks generalizing tp with
  | nil => simp
  | cons q qs ih => simp only [List.flatten_cons, runProg_append, ih, List.foldl_cons]

/-- `decN`（`GSScanTapes` で定義済みの「1 回の消去 = 2 動作」を `n` 回）を
実際の動作列として書き下したもの。 -/
def decProg (blank : Fin k) : ℕ → TapeProg k
  | 0 => []
  | n + 1 => (blank, Move.left) :: (blank, Move.stay) :: decProg blank n

@[simp] theorem decProg_length (blank : Fin k) (n : ℕ) : (decProg blank n).length = 2 * n := by
  induction n with
  | zero => simp [decProg]
  | succ n ih => simp only [decProg, List.length_cons, ih]; omega

theorem runProg_decProg (blank : Fin k) (tp : TapeConfiguration k) (n : ℕ) :
    runProg blank tp (decProg blank n) = decN blank tp n := by
  induction n generalizing tp with
  | zero => simp [decProg, decN]
  | succ n ih =>
      show runProg blank (step blank tp blank .left)
          ((blank, Move.stay) :: decProg blank n) = decN blank tp (n + 1)
      rw [runProg_cons]
      show runProg blank (step blank (step blank tp blank .left) blank .stay)
          (decProg blank n) = decN blank tp (n + 1)
      rw [ih, decN]

end PalPeg.GSTapes

namespace PalPeg.Prologue

open PegSeparation.RealTimeTM
open PalPeg.Tape PalPeg.GSTapes

variable {k : ℕ}

/-! ## 1. `writeWord`：空スタックから語を書いて先頭へ戻る -/

/-- `l` の各記号を左から右へ `push` する動作列。 -/
def pushProg (l : List (Fin k)) : TapeProg k := l.map (fun a => (a, Move.right))

@[simp] theorem pushProg_length (l : List (Fin k)) : (pushProg l).length = l.length := by
  simp [pushProg]

@[simp] theorem pushProg_nil : (pushProg ([] : List (Fin k))) = [] := rfl

@[simp] theorem pushProg_cons (a : Fin k) (rest : List (Fin k)) :
    pushProg (a :: rest) = (a, Move.right) :: pushProg rest := rfl

/-- `pushProg` の実行は、最前線ビューを `w` から `w ++ l` へ進める。 -/
theorem runProg_pushProg {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    (h : InputCopy.FrontierView blank tp w) (l : List (Fin k)) :
    InputCopy.FrontierView blank (runProg blank tp (pushProg l)) (w ++ l) := by
  induction l generalizing tp w with
  | nil => simpa using h
  | cons a rest ih =>
      have h' := InputCopy.append_spec h a
      have := ih h'
      simpa [pushProg, List.append_assoc] using this

/-- `w` を右端から左へ、`i` 個読み返しながら書き戻す動作列
（`SeqView blank tp w i` から `GSTapes.leftN blank tp i` に対応する）。 -/
def backProg (w : List (Fin k)) (i : ℕ) : TapeProg k :=
  (((w.take (i + 1)).drop 1).reverse).map (fun a => (a, Move.left))

@[simp] theorem backProg_zero (w : List (Fin k)) : backProg w 0 = [] := by
  simp [backProg]

theorem backProg_length (w : List (Fin k)) (i : ℕ) (hi : i < w.length) :
    (backProg w i).length = i := by
  have h1 : (w.take (i + 1)).length = i + 1 := by
    rw [List.length_take]; omega
  simp only [backProg, List.length_map, List.length_reverse, List.length_drop, h1]
  omega

/-- `leftN` の各ステップは、実際には `runProg` で `backProg` を流したものに一致する。 -/
theorem leftN_eq_runProg_backProg {blank : Fin k} {w : List (Fin k)} :
    ∀ (i : ℕ) (tp : TapeConfiguration k), SeqView blank tp w i →
      GSTapes.leftN blank tp i = runProg blank tp (backProg w i) := by
  intro i
  induction i with
  | zero => intro tp _; simp [GSTapes.leftN]
  | succ n ih =>
      intro tp h
      have hstep : SeqView blank (step blank tp tp.focus .left) w n := seq_move_left h
      have hlen1 : n + 1 < w.length := h.lt
      have htake : w.take (n + 1 + 1) = w.take (n + 1) ++ [w[n + 1]] := by
        simp [List.take_add_one, List.getElem?_eq_getElem hlen1]
      have hfocus : tp.focus = w[n + 1] := by
        have hopt := h.focus_eq
        rw [List.getElem?_eq_getElem hlen1] at hopt
        exact (Option.some_inj.1 hopt.symm)
      have hlen_take : 1 ≤ (w.take (n + 1)).length := by
        rw [List.length_take]; omega
      have hdrop : (w.take (n + 1 + 1)).drop 1
          = ((w.take (n + 1)).drop 1) ++ [w[n + 1]] := by
        rw [htake, List.drop_append_of_le_length hlen_take]
      show GSTapes.leftN blank (step blank tp tp.focus .left) n
          = runProg blank tp (backProg w (n + 1))
      rw [ih _ hstep]
      show runProg blank (step blank tp tp.focus .left) (backProg w n)
          = runProg blank tp (backProg w (n + 1))
      have hb : backProg w (n + 1) = (tp.focus, Move.left) :: backProg w n := by
        simp only [backProg, hdrop, hfocus, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.singleton_append, List.map_cons]
      rw [hb, runProg_cons]

/-- 空スタックから語 `l`（`l ≠ []`）を左から右へ書き、先頭（添字 `0`）へ戻る。
使う動作は `2 * l.length` 個ちょうど。 -/
theorem writeWord {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (l : List (Fin k)) (hl : l ≠ []) :
    ∃ prog : TapeProg k, SeqView blank (runProg blank tp prog) l 0 ∧
      prog.length = 2 * l.length := by
  have hf0 : InputCopy.FrontierView blank tp [] :=
    (InputCopy.frontierView_iff_stackView).2 (by simpa using h)
  have hfl : InputCopy.FrontierView blank (runProg blank tp (pushProg l)) ([] ++ l) :=
    runProg_pushProg hf0 l
  have hfl' : InputCopy.FrontierView blank (runProg blank tp (pushProg l)) l := by
    simpa using hfl
  have hw : 0 < l.length := by
    rcases l with _ | ⟨a, rest⟩
    · exact absurd rfl hl
    · simp
  have hseq0 : SeqView blank (step blank (runProg blank tp (pushProg l)) blank .left) l
      (l.length - 1) := InputCopy.toSeqView hfl' hw
  set n := l.length - 1 with hn
  have hlast : GSTapes.leftN blank
      (step blank (runProg blank tp (pushProg l)) blank .left) n
      = runProg blank (step blank (runProg blank tp (pushProg l)) blank .left)
        (backProg l n) := leftN_eq_runProg_backProg n _ hseq0
  have hfin : SeqView blank
      (GSTapes.leftN blank
        (step blank (runProg blank tp (pushProg l)) blank .left) n) l 0 :=
    GSTapes.seq_leftN n _ 0 (by simpa using hseq0)
  refine ⟨pushProg l ++ (blank, Move.left) :: backProg l n, ?_, ?_⟩
  · have heq : runProg blank tp (pushProg l ++ (blank, Move.left) :: backProg l n)
        = runProg blank
            (step blank (runProg blank tp (pushProg l)) blank .left) (backProg l n) := by
      rw [runProg_append, runProg_cons]
    rw [heq, ← hlast]
    exact hfin
  · have hbn : n < l.length := by omega
    have hb : (backProg l n).length = n := backProg_length l n hbn
    simp only [List.length_append, pushProg_length, List.length_cons, hb]
    omega

/-- `writeZeros`：フラグテープ用の系。長さ `L ≥ 1` の全 `zero` 語を書いて先頭へ戻す。
`L := Lmax S + 1` として `MiddleTapes.minit_encodes` の仮定を満たすのに使う。
動作数はちょうど `2 * L`。 -/
theorem writeZeros {blank zero : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (L : ℕ) (hL : 0 < L) :
    ∃ prog : TapeProg k, SeqView blank (runProg blank tp prog) (List.replicate L zero) 0 ∧
      prog.length = 2 * L := by
  have hl : (List.replicate L zero : List (Fin k)) ≠ [] := by
    simp only [ne_eq, List.replicate_eq_nil_iff]; omega
  obtain ⟨prog, hprog, hlen⟩ := writeWord h (List.replicate L zero) hl
  exact ⟨prog, hprog, by simpa using hlen⟩

/-! ## 2. `writeSingleton`：入力コピーの初期最前線 `[leftSym]` -/

/-- 空スタックから `[leftSym]` を書いて（空白セルに）戻る：`1` 動作。 -/
theorem writeSingleton {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) (leftSym : Fin k) :
    ∃ prog : TapeProg k,
      InputCopy.FrontierView blank (runProg blank tp prog) [leftSym] ∧ prog.length = 1 := by
  have hf0 : InputCopy.FrontierView blank tp [] :=
    (InputCopy.frontierView_iff_stackView).2 (by simpa using h)
  refine ⟨[(leftSym, Move.right)], ?_, rfl⟩
  have h1 := InputCopy.append_spec hf0 leftSym
  simpa using h1

/-! ## 3. `clearTape`：スタック内容を全消去して空スタックへ -/

/-- `StackView` の内容 `l` をすべて消して空スタックへ戻す（`GSTapes.decN` を再利用）。
動作数は正確に `2 * l.length`。 -/
theorem clearStack {blank : Fin k} :
    ∀ (l : List (Fin k)) (tp : TapeConfiguration k), StackView blank tp l →
      StackView blank (GSTapes.decN blank tp l.length) [] := by
  intro l
  induction l with
  | nil => intro tp h; simpa [GSTapes.decN] using h
  | cons a rest ih =>
      intro tp h
      have h1 := pop_spec h
      have h2 := pop_erase h1
      have h3 := ih _ h2
      simpa [GSTapes.decN, List.length_cons] using h3

/-- `clearTape`：スタックとして見て内容 `l`（`l.length ≤ n`）を持つテープを、
ちょうど `2 * l.length`（したがって `≤ 2 * n + 2`）動作で完全な空白（空スタック、
ヘッド添字 `0`）に戻す。 -/
theorem clearTape {blank : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)} {n : ℕ}
    (h : StackView blank tp l) (hn : l.length ≤ n) :
    ∃ prog : TapeProg k, StackView blank (runProg blank tp prog) [] ∧
      prog.length = 2 * l.length ∧ prog.length ≤ 2 * n + 2 := by
  refine ⟨GSTapes.decProg blank l.length, ?_, GSTapes.decProg_length blank l.length, ?_⟩
  · rw [GSTapes.runProg_decProg]
    exact clearStack l tp h
  · rw [GSTapes.decProg_length]; omega

/-! ## 4. `spreadClear`：消去プログラムを小さなチャンクへ分割する -/

/-- 動作列を「`c + 1` 個以下」のチャンクへ貪欲に分割する。 -/
def chunkList (c : ℕ) : TapeProg k → List (TapeProg k)
  | [] => []
  | (x :: xs) => (x :: xs).take (c + 1) :: chunkList c ((x :: xs).drop (c + 1))
termination_by p => p.length
decreasing_by
  simp only [List.length_cons, List.length_drop]
  omega

theorem chunkList_join (c : ℕ) : ∀ p : TapeProg k, (chunkList c p).flatten = p := by
  intro p
  induction p using chunkList.induct (c := c) with
  | case1 => simp [chunkList]
  | case2 x xs ih =>
      have hdef : chunkList c (x :: xs)
          = (x :: xs).take (c + 1) :: chunkList c ((x :: xs).drop (c + 1)) := by
        simp [chunkList]
      rw [hdef, List.flatten_cons, ih]
      simp

theorem chunkList_chunk_le (c : ℕ) : ∀ p : TapeProg k, ∀ q ∈ chunkList c p, q.length ≤ c + 1 := by
  intro p
  induction p using chunkList.induct (c := c) with
  | case1 => simp [chunkList]
  | case2 x xs ih =>
      intro q hq
      have hdef : chunkList c (x :: xs)
          = (x :: xs).take (c + 1) :: chunkList c ((x :: xs).drop (c + 1)) := by
        simp [chunkList]
      rw [hdef] at hq
      rcases List.mem_cons.1 hq with hq | hq
      · subst hq
        rw [List.length_take]
        omega
      · exact ih q hq

/-- `spreadClear`：`≤ n` 個の非空白セルを消去するプログラム（`2 * l.length` 動作）は、
それぞれ `≤ c + 1` 動作のチャンクに分割でき、それらを順に実行すれば元と同じ効果
（空スタックへ戻る）が得られる。 -/
theorem spreadClear {blank : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)} {n c : ℕ}
    (h : StackView blank tp l) (hn : l.length ≤ n) :
    ∃ chunks : List (TapeProg k),
      (∀ q ∈ chunks, q.length ≤ c + 1) ∧
      chunks.flatten = GSTapes.decProg blank l.length ∧
      StackView blank (chunks.foldl (fun s q => runProg blank s q) tp) [] := by
  refine ⟨chunkList c (GSTapes.decProg blank l.length), chunkList_chunk_le c _,
    chunkList_join c _, ?_⟩
  rw [← runProg_join, chunkList_join]
  rw [GSTapes.runProg_decProg]
  exact clearStack l tp h

end PalPeg.Prologue
