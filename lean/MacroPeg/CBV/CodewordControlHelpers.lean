import MacroPeg.CBV.CodewordControlRecursive
import MacroPeg.CBV.LastCodewordHelpers

/-! Codeword control may inspect the same independent recursive helpers as
its runtime header. Comparisons retain the actual selected control trace. -/
namespace Shallot.MacroPeg.CBV.CodewordControlHelpers
open ClockFreezing (Table)
open RecursiveParserStability (Installed Lexical)
open RecursiveCodeGrammar (canonical)
open LastCodewordHelpers (lexical_environment lexical_syntax)
open CodewordControlFilter (Expr render filter wholeView)

def Control (n : Nat) : CodewordControlFilter.Expr → Prop
  | .test e => Lexical n e
  | .seq a b | .alt a b => Control n a ∧ Control n b
  | .notP a | .star a => Control n a
  | _ => True

theorem render_lexical (n : Nat) (A : MExp) (hA : Lexical n A) :
    ∀ d, Control n d → Lexical n (render A d)
  | .token, _ => hA
  | .eps, _ => True.intro
  | .test _, h => h
  | .seq a b, h | .alt a b, h => ⟨render_lexical n A hA a h.1,render_lexical n A hA b h.2⟩
  | .notP a, h | .star a, h => render_lexical n A hA a h

theorem filter_syntax (n : Nat) (A : MExp) (hA : Lexical n A) :
    ∀ d, Control n d → HelperArgument.Syntax n (filter A d)
  | .token, _ => ⟨lexical_syntax n A hA,True.intro⟩
  | .eps, _ => ⟨True.intro,True.intro⟩
  | .test e, h => ⟨lexical_syntax n e h,lexical_syntax n e h⟩
  | .seq a b, h => ⟨lexical_syntax n _ (render_lexical n A hA _ h),filter_syntax n A hA a h.1,filter_syntax n A hA b h.2⟩
  | .alt a b, h => ⟨lexical_syntax n _ (render_lexical n A hA _ h),
      ⟨lexical_syntax n _ (render_lexical n A hA a h.1),filter_syntax n A hA a h.1⟩,
      lexical_syntax n _ (render_lexical n A hA a h.1),filter_syntax n A hA b h.2⟩
  | .notP a, h => ⟨lexical_syntax n _ (render_lexical n A hA _ h),lexical_syntax n _ (render_lexical n A hA a h)⟩
  | .star a, h => ⟨lexical_syntax n _ (render_lexical n A hA _ h),filter_syntax n A hA a h,lexical_syntax n _ (render_lexical n A hA a h)⟩

structure Header extends RecursiveCodeGrammar.Header where
  control : CodewordControlFilter.Expr
  controlLexical : Control bodies.length control

abbrev lexical (H : Header) := RecursiveCodeGrammar.lexical H.toHeader
abbrev LexicalTable (H : Header) := RecursiveCodeGrammar.LexicalTable H.toHeader
abbrev pick (H : Header) := LastCodewordHelpers.pick H.toHeader
abbrev floor (H : Header) := LastCodewordHelpers.floor H.toHeader
abbrev syntax_eval (H : Header) := LastCodewordHelpers.syntax_eval H.toHeader
abbrev lexical_table (H : Header) := LastCodewordHelpers.lexical_table H.toHeader
abbrev physical_lexical (H : Header) := LastCodewordHelpers.physical_lexical H.toHeader
abbrev prefixAt (H : Header) := LastCodewordHelpers.prefixAt H.toHeader
abbrev prefix_eval (H : Header) := LastCodewordHelpers.prefix_eval H.toHeader

def rest (H : Header) : MExp := render H.head H.control
def argument (H : Header) : MExp := .seq H.head (rest H)
def verifier (H : Header) : MExp := filter H.head H.control

theorem rest_lexical (H : Header) : Lexical H.bodies.length (rest H) :=
  render_lexical _ H.head H.lexical H.control H.controlLexical
theorem argument_lexical (H : Header) : Lexical H.bodies.length (argument H) := ⟨H.lexical,rest_lexical H⟩
theorem verifier_allowed (H : Header) : HelperArgument.Syntax H.bodies.length (verifier H) :=
  filter_syntax _ H.head H.lexical H.control H.controlLexical

def argumentAt (H : Header) (x : List Char) (p : Nat) : Res := lexical H (argument H) x p
def check (H : Header) (x u : List Char) (p : Nat) : Res :=
  evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar (canonical H.bodies x)
    [u] (verifier H) p

theorem head_firstOrder (H : Header) : H.head.FirstOrder :=
  RecursiveParserStability.lexical_firstOrder _ _ H.lexical
theorem rest_firstOrder (H : Header) : (rest H).FirstOrder :=
  RecursiveParserStability.lexical_firstOrder _ _ (rest_lexical H)

theorem head_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E H.head p=lexical H H.head x p := hLex E _ H.lexical p hp

theorem rest_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (rest H) p=lexical H (rest H) x p := hLex E _ (rest_lexical H) p hp

theorem argument_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (argument H) p=argumentAt H x p := hLex E _ (argument_lexical H) p hp

theorem verifier_eval (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x s T) (u : List Char) (p : Nat) (hp : p≤x.length) :
    evV g x s T [u] (verifier H) p=check H x u p :=
  syntax_eval H g hg x s T hOk hLex [u] _ (verifier_allowed H) p hp

theorem stable (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (hr : ruleAtM g.rules H.bodies.length=some ⟨1,verifier H⟩)
    (x : List Char) (s : Strategy) : ClockFreezing.StableRows g x s (pick H) (floor H x) :=
  LastCodewordHelpers.stable_unary H.toHeader (verifier H) (verifier_allowed H) g hg hr x s

/-- Exact entry preserves the full control-selected capture even when the
header and tests call independent recursive helpers. -/
theorem entry (H : Header) (g : MGrammar) (hg : Installed H.bodies g) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x .callByValuePar T)
    (p j q : Nat) (hp : p≤x.length) (ha : lexical H H.head x p=some (some j))
    (hd : lexical H (rest H) x j=some (some q)) (b : MExp) (hb : b.FirstOrder) :
    evV g x .callByValuePar T [pre x p q] (.seq (.seq H.head (.param 0)) b) p=
      match check H x (pre x p j) j with
      | some (some _) => evV g x .callByValuePar T [pre x p j,pre x j q]
          (.seq (.param 0) (wholeView b)) q
      | other => other := by
  have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp ha).1
  have ha0 := (head_eval H g x .callByValuePar T hLex [] p hp).trans ha
  have hd0 := (rest_eval H g x .callByValuePar T hLex [] j hj).trans hd
  have hq := evV_ok hOk _ j hj q hd0
  have hc := SequenceArguments.pre_concat hp hq
    (WordStarFilter.success_prefix (by decide) hT [] H.head (head_firstOrder H) p j hp ha0).2
    (WordStarFilter.success_prefix (by decide) hT [] (rest H) (rest_firstOrder H) j q hj hd0).2
  rw [LeadingReplayStar.sequence_assoc,evV_seq_ok ((head_eval H g x .callByValuePar T hLex [pre x p q] p hp).trans ha),hc]
  have hh := CodewordControlFilter.replay_success g x .callByValuePar (by decide) T hT hOk
    H.head (head_firstOrder H) H.prefixFree (pre x p j) (H.captured x p j hp ha)
    (fun z k hz hk => H.captured x z k hz ((head_eval H g x .callByValuePar T hLex [pre x p j] z hz).symm.trans hk))
    H.control j q hj ((rest_eval H g x .callByValuePar T hLex [pre x p j] j hj).trans hd) b hb
  change _=(match evV g x .callByValuePar T [pre x p j] (verifier H) j with
    | some (some _) => evV g x .callByValuePar T [pre x p j,pre x j q]
        (.seq (.param 0) (wholeView b)) q
    | other => other) at hh
  rw [verifier_eval H g hg x .callByValuePar T hOk hLex _ j hj] at hh
  exact hh

/-- Canonical helper behavior is obtained from actual ordinary stages,
including the first stabilized stage; no lexical table is supplied as advice. -/
theorem physical_lexical_at (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (k : Nat) :
    LexicalTable H g x s (tblV g x s (RecursiveParserStability.floor H.bodies x+k)) := by
  apply lexical_table H g hg x s _ (tblV_ok g x s _) _
  intro i hi
  have hs := RecursiveParserStability.helpers_stable H.valid hg x s
  exact (hs k i (by simp [RecursiveParserStability.pick,hi]) []).trans
    (hs 1 i (by simp [RecursiveParserStability.pick,hi]) []).symm

/-- The original argument itself supplies its actual first header and
consecutive retained parts, rather than requiring a decomposition oracle. -/
theorem argument_success (H : Header) (x : List Char) (p q : Nat) (hp : p≤x.length)
    (hb : argumentAt H x p=some (some q)) :
    ∃ j, j≤x.length ∧ lexical H H.head x p=some (some j) ∧
      lexical H (rest H) x j=some (some q) ∧
      pre x p q=pre x p j++pre x j q ∧ H.code (pre x p j) := by
  let g := RecursiveParserStability.grammar H.bodies
  let T := canonical H.bodies x
  change evV g x .callByValuePar T [] (.seq H.head (rest H)) p=some (some q) at hb
  cases ha : evV g x .callByValuePar T [] H.head p with
  | none => rw [evV_seq_none ha] at hb; cases hb
  | some rr => cases rr with
    | none => rw [evV_seq_fail ha] at hb; cases hb
    | some j =>
      rw [evV_seq_ok ha] at hb
      have hj := RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp ha
      have hq := RecursiveCodeGrammar.lexical_success H.toHeader (rest H) (rest_lexical H) x j q hj.1 hb
      exact ⟨j,hj.1,ha,hb,SequenceArguments.pre_concat hp hq.1 hj.2 hq.2,H.captured x p j hp ha⟩

/-- The concrete source call's successful argument is enough to derive
full partial entry equivalence with two retained parts. -/
theorem argument_entry (H : Header) (g : MGrammar) (hg : Installed H.bodies g) (x : List Char)
    (T : Table) (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x .callByValuePar T) (E : List (List Char))
    (p q : Nat) (hp : p≤x.length) (hb : evV g x .callByValuePar T E (argument H) p=some (some q))
    (b : MExp) (hbody : b.FirstOrder) :
    ∃ j, j≤x.length ∧ H.code (pre x p j) ∧ pre x p q=pre x p j++pre x j q ∧
      evV g x .callByValuePar T [pre x p q] (.seq (.seq H.head (.param 0)) b) p=
        match check H x (pre x p j) j with
        | some (some _) => evV g x .callByValuePar T [pre x p j,pre x j q]
            (.seq (.param 0) (wholeView b)) q
        | other => other := by
  have harg : argumentAt H x p=some (some q) := (argument_eval H g x _ T hLex E p hp).symm.trans hb
  obtain ⟨j,hj,ha,hd,hparts,hcode⟩ := argument_success H x p q hp harg
  exact ⟨j,hj,hcode,hparts,entry H g hg x T hT hOk hLex p j q hp ha hd b hbody⟩

/-- A direct ordinary-table theorem removes the lexical-table premise.
The original source grammar and its actual successful argument determine
both retained values and the full three-valued continuation result. -/
theorem physical_argument_entry (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (hfo : g.FirstOrder) (x : List Char) (k : Nat) (E : List (List Char))
    (p q : Nat) (hp : p≤x.length)
    (hb : evV g x .callByValuePar (tblV g x .callByValuePar (RecursiveParserStability.floor H.bodies x+k))
      E (argument H) p=some (some q)) (b : MExp) (hbody : b.FirstOrder) :
    ∃ j, j≤x.length ∧ H.code (pre x p j) ∧ pre x p q=pre x p j++pre x j q ∧
      evV g x .callByValuePar (tblV g x .callByValuePar (RecursiveParserStability.floor H.bodies x+k))
        [pre x p q] (.seq (.seq H.head (.param 0)) b) p=
        match check H x (pre x p j) j with
        | some (some _) => evV g x .callByValuePar
            (tblV g x .callByValuePar (RecursiveParserStability.floor H.bodies x+k))
            [pre x p j,pre x j q] (.seq (.param 0) (wholeView b)) q
        | other => other :=
  argument_entry H g hg x _ (tblV_sound hfo (by decide) _) (tblV_ok g x _ _)
    (physical_lexical_at H g hg x .callByValuePar k) E p q hp hb b hbody

theorem wholeView_allowed (n : Nat) : ∀ b, HelperArgument.Syntax n b → HelperArgument.Syntax n (wholeView b)
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => True.intro
  | .param 0, _ => ⟨⟨True.intro,True.intro⟩,True.intro⟩
  | .param (_+1), _ => True.intro
  | .seq a b, h | .alt a b, h => ⟨wholeView_allowed n a h.1,wholeView_allowed n b h.2⟩
  | .notP a, h | .star a, h => wholeView_allowed n a h
  | .call _ [], h => h
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

/-- Cross the actual Par/Seq entry-position boundary with recursive helper
continuations and the full retained source value. -/
theorem entry_seq (H : Header) (g h : MGrammar) (hg : Installed H.bodies g) (hh : Installed H.bodies h)
    (x : List Char) (T U : Table) (hT : SoundTV g x .callByValuePar T)
    (hOk : OkTV x.length T) (hU : OkTV x.length U)
    (hLexT : LexicalTable H g x .callByValuePar T) (hLexU : LexicalTable H h x .callByValueSeq U)
    (p j q : Nat) (hp : p≤x.length) (ha : lexical H H.head x p=some (some j))
    (hd : lexical H (rest H) x j=some (some q))
    (b : MExp) (hb : HelperArgument.Syntax H.bodies.length b) :
    evV g x .callByValuePar T [pre x p q] (.seq (.seq H.head (.param 0)) b) p=
      match check H x (pre x p j) j with
      | some (some _) => evV h x .callByValueSeq U [pre x p j,pre x j q]
          (.seq (.param 0) (wholeView b)) q
      | other => other := by
  have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp ha).1
  have hq := (RecursiveCodeGrammar.lexical_success H.toHeader (rest H) (rest_lexical H) x j q hj hd).1
  rw [entry H g hg x T hT hOk hLexT p j q hp ha hd b (HelperArgument.firstOrder _ b hb)]
  cases check H x (pre x p j) j with
  | none => rfl
  | some rr => cases rr with
    | none => rfl
    | some z =>
      have hs : HelperArgument.Syntax H.bodies.length (.seq (.param 0) (wholeView b)) :=
        ⟨True.intro,wholeView_allowed _ b hb⟩
      exact (syntax_eval H g hg x .callByValuePar T hOk hLexT _ _ hs q hq).trans
        (syntax_eval H h hh x .callByValueSeq U hU hLexU _ _ hs q hq).symm

/-- Both tables are actual ordinary computations. This theorem handles
arbitrary extra ordinary rounds and derives the split from the actual
source argument, including recursive header and test calls. -/
theorem physical_argument_entry_seq (H : Header) (g h : MGrammar)
    (hg : Installed H.bodies g) (hh : Installed H.bodies h) (hfo : g.FirstOrder)
    (x : List Char) (k m : Nat) (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (hb : evV g x .callByValuePar (tblV g x .callByValuePar (RecursiveParserStability.floor H.bodies x+k))
      E (argument H) p=some (some q))
    (b : MExp) (hbody : HelperArgument.Syntax H.bodies.length b) :
    ∃ j, j≤x.length ∧ H.code (pre x p j) ∧ pre x p q=pre x p j++pre x j q ∧
      evV g x .callByValuePar (tblV g x .callByValuePar (RecursiveParserStability.floor H.bodies x+k))
        [pre x p q] (.seq (.seq H.head (.param 0)) b) p=
        match check H x (pre x p j) j with
        | some (some _) => evV h x .callByValueSeq
            (tblV h x .callByValueSeq (RecursiveParserStability.floor H.bodies x+m))
            [pre x p j,pre x j q] (.seq (.param 0) (wholeView b)) q
        | other => other := by
  have hlex := physical_lexical_at H g hg x .callByValuePar k
  obtain ⟨j,hj,ha,hd,hparts,hcode⟩ := argument_success H x p q hp
    ((argument_eval H g x _ _ hlex E p hp).symm.trans hb)
  exact ⟨j,hj,hcode,hparts,entry_seq H g h hg hh x _ _ (tblV_sound hfo (by decide) _)
    (tblV_ok g x _ _) (tblV_ok h x _ _) hlex (physical_lexical_at H h hh x .callByValueSeq m)
    p j q hp ha hd b hbody⟩

private theorem seq_eps (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (e : MExp) (p : Nat) :
    evV g x s T E (.seq e .eps) p=evV g x s T E e p := by
  change (match evV g x s T E e p with
    | some (some z) => some (some z) | other => other)=_
  cases evV g x s T E e p with
  | none => rfl
  | some r => cases r <;> rfl

/-- Exact prefix identity for the independent recursive component. -/
theorem prefix_identity (H : Header) (x : List Char) (p j q : Nat) (hp : p≤x.length)
    (ha : lexical H H.head x p=some (some j)) (hd : lexical H (rest H) x j=some (some q)) :
    prefixAt H x [pre x p q] p=
      match check H x (pre x p j) j with
      | some (some _) => CodewordControlRecursive.wordAt x (pre x p j) q | other => other := by
  let g := RecursiveParserStability.grammar H.bodies
  let T := canonical H.bodies x
  have hOk : OkTV x.length T := tblV_ok g x _ _
  have hLex : LexicalTable H g x .callByValuePar T := by
    intro E e he z hz
    exact lexical_environment g x .callByValuePar T E [] _ e he z
  have hg := RecursiveParserStability.installed H.bodies
  have he := entry H g hg x T (tblV_sound (RecursiveCodeGrammar.helpers_firstOrder H.toHeader) (by decide) _)
    hOk hLex p j q hp ha hd .eps True.intro
  simp only [wholeView,MExp.subst,seq_eps] at he
  rw [prefix_eval H g hg x .callByValuePar T hOk hLex _ p hp] at he
  simp only [CodewordControlRecursive.word_eval] at he
  exact he

/-- Actual finite prefix failures synchronize the two user clocks, even
when the recursive verifier rejects before querying the target user row. -/
theorem seed_entry (H : Header) (x : List Char) (p j q : Nat) (hp : p≤x.length)
    (ha : lexical H H.head x p=some (some j)) (hd : lexical H (rest H) x j=some (some q)) :
    (if prefixAt H x [pre x p q] p=some none then some none else none)=
      match check H x (pre x p j) j with
      | some (some _) => if CodewordControlRecursive.wordAt x (pre x p j) q=some none then some none else none
      | other => other := by
  rw [prefix_identity H x p j q hp ha hd]
  cases check H x (pre x p j) j with
  | none => rfl
  | some r => cases r <;> rfl

end Shallot.MacroPeg.CBV.CodewordControlHelpers
