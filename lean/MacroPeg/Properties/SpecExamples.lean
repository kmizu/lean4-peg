import MacroPeg.Properties.Reachable
import Shallot.Peg.Determinism

/-!
# Examples for finite specialization (instructions.md §10)

The plain PEG side is evaluated with `decide` (`pegRun` reduces in the kernel); the Macro PEG facts are then obtained
through `finite_specialization_cbn`, so each example exercises the theorem rather than a separate computation. The
examples cover: a duplicated argument with a lookahead (`Twice`), recursion with reordered arguments (`Alt`), an unused
argument (`Fst`), a reference to the ordinary environment from a constant (`envG`), self-recursion that has no derivation
on either side (`Loop`), `|D| = 0`, arity `0`, empty input, and grammars rejected by `wfB` (missing rule, arity mismatch,
parameter / constant / env index out of range). A grammar that builds a new argument such as `F(x) ← F(x "a")` is not
expressible: `FArg` has only `fwd j` and `const k`.
-/

namespace Shallot.MacroPeg

open Shallot (PExp Grammar Derives pegRun)

theorem pegObs_of_run {g : Grammar} {e : PExp} {x : List Char} {r : Option (List Char)} (f : Nat)
    (h : (pegRun g f e x).map pegRestOf = some r) : PegObs g e x r := by
  cases hrun : pegRun g f e x with
  | none => rw [hrun] at h; cases h
  | some o =>
    rw [hrun] at h
    exact ⟨o, Shallot.pegRun_sound hrun, Option.some.inj h⟩

/-- A failure observation excludes every success observation (plain PEG is deterministic). -/
theorem pegObs_fail_not_accepts {g : Grammar} {e : PExp} {x : List Char} (h : PegObs g e x none) :
    ¬ PAccepts g e x := by
  rintro ⟨rest, o', hd', ho'⟩
  obtain ⟨o, hd, ho⟩ := h
  have := Shallot.derives_det hd hd'
  subst this
  rw [ho] at ho'; cases ho'

/-! ## `Twice(x) ← x x !.` with `D = ["a", "b"]` -/

def twiceF : FGrammar := ⟨[], [.lit ['a'], .lit ['b']], [⟨1, .seq (.param 0) (.seq (.param 0) (.notP .any))⟩]⟩

theorem twiceF_wf : twiceF.WF := twiceF.wfB_sound (by decide)
theorem twiceF_valid : twiceF.ValidVec 0 [1] := twiceF.validVecB_sound 0 [1] (by decide)

example : twiceF.specs = [(0, [0]), (0, [1])] := by decide
example : (twiceF.specialize 0 [1]).rules.length = 2 := by decide

/-- `Twice("b")` consumes all of `"bb"`. -/
example : MRecognizesAll twiceF.toMacro (twiceF.entry 0 [1]) ['b', 'b'] :=
  (finite_specialization_recognizesAll twiceF twiceF_wf twiceF_valid _).2 (pegObs_of_run 10 (by decide))

/-- `Twice("b")` fails on `"bbb"` (the lookahead `!.` sees a residue) and on the empty input. -/
example : MacroObs twiceF.toMacro (twiceF.entry 0 [1]) ['b', 'b', 'b'] none :=
  (finite_specialization_cbn twiceF twiceF_wf twiceF_valid _ _).2 (pegObs_of_run 10 (by decide))

example : MacroObs twiceF.toMacro (twiceF.entry 0 [1]) [] none :=
  (finite_specialization_cbn twiceF twiceF_wf twiceF_valid _ _).2 (pegObs_of_run 10 (by decide))

example : ¬ MAccepts twiceF.toMacro (twiceF.entry 0 [1]) ['b', 'a'] := by
  rw [finite_specialization_accepts twiceF twiceF_wf twiceF_valid]
  exact pegObs_fail_not_accepts (pegObs_of_run 10 (by decide))

/-! ## `Alt(x, y) ← x Alt(y, x) / !.` (recursion with swapped arguments), `Fst(x, y) ← x` (unused argument) -/

def altF : FGrammar :=
  ⟨[], [.lit ['a'], .lit ['b']],
    [⟨2, .alt (.seq (.param 0) (.call 0 [.fwd 1, .fwd 0])) (.notP .any)⟩, ⟨2, .param 0⟩]⟩

theorem altF_wf : altF.WF := altF.wfB_sound (by decide)
theorem altF_valid : altF.ValidVec 0 [0, 1] := altF.validVecB_sound 0 [0, 1] (by decide)
theorem altF_valid_fst : altF.ValidVec 1 [1, 0] := altF.validVecB_sound 1 [1, 0] (by decide)

/-- `|D| ^ arity` for each rule: `2 ^ 2 + 2 ^ 2 = 8` specialized rules, no more. -/
example : altF.specs.length = 8 := by decide

example : MRecognizesAll altF.toMacro (altF.entry 0 [0, 1]) ['a', 'b', 'a', 'b'] :=
  (finite_specialization_recognizesAll altF altF_wf altF_valid _).2 (pegObs_of_run 20 (by decide))

example : MacroObs altF.toMacro (altF.entry 0 [0, 1]) ['a', 'b', 'b', 'a'] none :=
  (finite_specialization_cbn altF altF_wf altF_valid _ _).2 (pegObs_of_run 20 (by decide))

/-- `Fst("b", "a")` on `"ba"` succeeds leaving `"a"` (the second argument is never used). -/
example : MacroObs altF.toMacro (altF.entry 1 [1, 0]) ['b', 'a'] (some ['a']) :=
  (finite_specialization_cbn altF altF_wf altF_valid_fst _ _).2 (pegObs_of_run 10 (by decide))

/-! ## A constant that refers to the ordinary environment: env `S ← "a"*`, `D = [S]`, `G(x) ← x "b"` -/

def envG : FGrammar := ⟨[.star (.chr 'a')], [.nt 0], [⟨1, .seq (.param 0) (.lit ['b'])⟩]⟩

theorem envG_wf : envG.WF := envG.wfB_sound (by decide)
theorem envG_valid : envG.ValidVec 0 [0] := envG.validVecB_sound 0 [0] (by decide)

example : MRecognizesAll envG.toMacro (envG.entry 0 [0]) ['a', 'a', 'b'] :=
  (finite_specialization_recognizesAll envG envG_wf envG_valid _).2 (pegObs_of_run 20 (by decide))

/-! ## `Loop ← Loop`: no derivation on either side, for every input and observation -/

def loopF : FGrammar := ⟨[], [], [⟨0, .call 0 []⟩]⟩

theorem loopF_wf : loopF.WF := loopF.wfB_sound (by decide)
theorem loopF_valid : loopF.ValidVec 0 [] := loopF.validVecB_sound 0 [] (by decide)

/-- Recursion stays recursion: the specialized grammar is the one-rule PEG `L ← L`, not an unrolling. -/
example : (loopF.specialize 0 []).rules = [.nt 0] := rfl

theorem no_derives_selfLoop {g : Grammar} {k : Nat} (hk : Shallot.ruleAt g.rules k = some (.nt k))
    {e : PExp} {x : List Char} {o : Shallot.Outcome} (h : Derives g e x o) : e = .nt k → False := by
  induction h with
  | ntOk i e' _ _ _ hr _ ih =>
    intro he; cases he; rw [hk] at hr; cases hr; exact ih rfl
  | ntFail i e' _ hr _ ih =>
    intro he; cases he; rw [hk] at hr; cases hr; exact ih rfl
  | ntMissing i _ hr => intro he; cases he; rw [hk] at hr; cases hr
  | _ => intro he; cases he

theorem loopF_no_obs (x : List Char) (r : Option (List Char)) : ¬ MacroObs loopF.toMacro (loopF.entry 0 []) x r := by
  rw [finite_specialization_cbn loopF loopF_wf loopF_valid]
  rintro ⟨o, hd, _⟩
  exact no_derives_selfLoop (k := 0) rfl hd rfl

/-! ## `|D| = 0` and arity `0` -/

/-- With no constants, a rule of arity 1 has no admissible vector (`0 ^ 1 = 0`), an arity-0 rule has one (`0 ^ 0 = 1`). -/
def zeroF : FGrammar := ⟨[], [], [⟨1, .param 0⟩, ⟨0, .lit ['c']⟩]⟩

example : zeroF.specs = [(1, [])] := by decide
example : (zeroF.specialize 1 []).rules.length = 1 := by decide
example : ¬ zeroF.ValidVec 0 [0] := by
  rintro ⟨r, _, _, hk⟩; exact absurd (hk 0 (by simp)) (by decide)

theorem zeroF_wf : zeroF.WF := zeroF.wfB_sound (by decide)

example : MRecognizesAll zeroF.toMacro (zeroF.entry 1 []) ['c'] :=
  (finite_specialization_recognizesAll zeroF zeroF_wf (zeroF.validVecB_sound 1 [] (by decide)) _).2
    (pegObs_of_run 10 (by decide))

/-! ## Grammars outside `WF` (rejected by the checker) -/

/-- Missing rule. -/
example : (FGrammar.mk [] [] [⟨0, .call 5 []⟩]).wfB = false := by decide
/-- Arity mismatch. -/
example : (FGrammar.mk [] [.eps] [⟨1, .call 0 []⟩]).wfB = false := by decide
/-- Parameter out of range. -/
example : (FGrammar.mk [] [.eps] [⟨1, .param 3⟩]).wfB = false := by decide
/-- Constant out of range. -/
example : (FGrammar.mk [] [.eps] [⟨1, .call 0 [.const 4]⟩]).wfB = false := by decide
/-- Env reference out of range (in a body and in a constant). -/
example : (FGrammar.mk [] [] [⟨0, .env 0⟩]).wfB = false := by decide
example : (FGrammar.mk [] [.nt 2] [⟨0, .eps⟩]).wfB = false := by decide

/-! ## Mutual recursion, an empty constant, a failing argument, a lookahead residue

`D = ["a", ε, !ε]`; `E(x) ← x O(x) / !.`, `O(x) ← x E(x)`, `Fst(x, y) ← x`, `Peek(x) ← !!x`. -/

def mutF : FGrammar :=
  ⟨[], [.lit ['a'], .eps, .notP .eps],
    [⟨1, .alt (.seq (.param 0) (.call 1 [.fwd 0])) (.notP .any)⟩, ⟨1, .seq (.param 0) (.call 0 [.fwd 0])⟩,
      ⟨2, .param 0⟩, ⟨1, .notP (.notP (.param 0))⟩]⟩

theorem mutF_wf : mutF.WF := mutF.wfB_sound (by decide)

/-- `E("a")` consumes all of `"aa"` (mutual recursion with the same vector) and fails on `"aaa"`. -/
example : MRecognizesAll mutF.toMacro (mutF.entry 0 [0]) ['a', 'a'] :=
  (finite_specialization_recognizesAll mutF mutF_wf (mutF.validVecB_sound 0 [0] (by decide)) _).2
    (pegObs_of_run 30 (by decide))

example : MacroObs mutF.toMacro (mutF.entry 0 [0]) ['a', 'a', 'a'] none :=
  (finite_specialization_cbn mutF mutF_wf (mutF.validVecB_sound 0 [0] (by decide)) _ _).2
    (pegObs_of_run 30 (by decide))

/-- `Fst(ε, "a")` on `"b"`: the empty constant succeeds and leaves everything. -/
example : MacroObs mutF.toMacro (mutF.entry 2 [1, 0]) ['b'] (some ['b']) :=
  (finite_specialization_cbn mutF mutF_wf (mutF.validVecB_sound 2 [1, 0] (by decide)) _ _).2
    (pegObs_of_run 10 (by decide))

/-- `Fst(!ε, "a")` on `"a"`: the argument fails, so the call fails. -/
example : MacroObs mutF.toMacro (mutF.entry 2 [2, 0]) ['a'] none :=
  (finite_specialization_cbn mutF mutF_wf (mutF.validVecB_sound 2 [2, 0] (by decide)) _ _).2
    (pegObs_of_run 10 (by decide))

/-- `Peek("a")` on `"ab"` succeeds and leaves `"ab"`: the lookahead consumes nothing and the residue is observed. -/
example : MacroObs mutF.toMacro (mutF.entry 3 [0]) ['a', 'b'] (some ['a', 'b']) :=
  (finite_specialization_cbn mutF mutF_wf (mutF.validVecB_sound 3 [0] (by decide)) _ _).2
    (pegObs_of_run 10 (by decide))

/-! ## Reachable specialization is smaller -/

example : twiceF.reach 0 [1] = [(0, [1])] := by decide
example : altF.reach 0 [0, 1] = [(0, [0, 1]), (0, [1, 0])] := by decide
/-- 2 reachable pairs instead of 8; `E("a")` reaches `E("a"), O("a")` out of `3 + 3 + 9 + 3 = 18`. -/
example : (altF.specializeOn (altF.reach 0 [0, 1]) 0 [0, 1]).rules.length = 2 := by decide
example : mutF.specs.length = 18 ∧ mutF.reach 0 [0] = [(0, [0]), (1, [0])] := by decide

example : MRecognizesAll altF.toMacro (altF.entry 0 [0, 1]) ['a', 'b', 'a', 'b'] :=
  (reachable_specialization altF altF_wf altF_valid _ _).2 (pegObs_of_run 20 (by decide))

end Shallot.MacroPeg
