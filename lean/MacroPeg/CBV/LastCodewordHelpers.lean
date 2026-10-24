import MacroPeg.CBV.LastCodewordRecursive
import MacroPeg.CBV.RecursiveCodeGrammar

/-! Freeze independent recursive helpers and their unary last-header
verifier at actual ordinary stages. No verifier row is supplied as advice. -/
namespace Shallot.MacroPeg.CBV.LastCodewordHelpers
open ClockFreezing (Table)
open RecursiveCodeGrammar (Header canonical lexical LexicalTable)
open RecursiveParserStability (Installed Lexical)

/-- Nullary lexical expressions ignore their caller's environment even
before helper stabilization, and at arbitrary physical query positions. -/
theorem lexical_environment (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E F : List (List Char)) (n : Nat) :
    ∀ e, Lexical n e → ∀ p, evV g x s T E e p=evV g x s T F e p
  | .call i [], _, p => by cases hr : ruleAtM g.rules i <;> cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  | .seq a b, he, p | .alt a b, he, p => by
    simp only [evV,lexical_environment g x s T E F n a he.1 p]
    split <;> first | rfl | exact lexical_environment g x s T E F n b he.2 _
  | .star a, he, p => by
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q _ => lexical_environment g x s T E F n a he q)
  | .notP a, he, p => by simp only [evV]; rw [lexical_environment g x s T E F n a he p]
  | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => rfl
  | .call _ (_::_), h, _ | .param _, h, _ | .dbg _, h, _ | .lam _ _, h, _
  | .callParam _ _, h, _ | .invoke _ _ _, h, _ => False.elim h

theorem lexical_syntax (n : Nat) : ∀ e, Lexical n e → HelperArgument.Syntax n e
  | .call _ [], h => h
  | .seq a b, h | .alt a b, h => ⟨lexical_syntax n a h.1,lexical_syntax n b h.2⟩
  | .star a, h | .notP a, h => lexical_syntax n a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .call _ (_::_), h | .param _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

def argument (H : Header) : MExp := LastCodewordRotation.argument H.head
theorem argument_lexical (H : Header) : Lexical H.bodies.length (argument H) := ⟨H.lexical,H.lexical⟩
def argumentAt (H : Header) (x : List Char) (p : Nat) : Res := lexical H (argument H) x p

def probe (H : Header) (x : List Char) (p : Nat) : Res :=
  LastCodewordVerification.probe (RecursiveParserStability.grammar H.bodies) x .callByValuePar
    (canonical H.bodies x) H.head p

def prefixAt (H : Header) (x : List Char) (W : List (List Char)) (p : Nat) : Res :=
  evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
    (canonical H.bodies x) W (.seq H.head (.param 0)) p

def pick (H : Header) (i : Nat) : Bool := decide (i≤H.bodies.length)
def floor (H : Header) (x : List Char) : Nat := RecursiveParserStability.floor H.bodies x+1

/-- Parameter-dependent expressions use the same actual stabilized helper
rows. Their old environment is retained, rather than erased or guessed. -/
theorem syntax_eval (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x s T) (E : List (List Char)) (e : MExp)
    (he : HelperArgument.Syntax H.bodies.length e) (p : Nat) (hp : p≤x.length) :
    evV g x s T E e p=evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
      (canonical H.bodies x) E e p := by
  apply HelperArgument.eval_eq hg (RecursiveParserStability.installed H.bodies)
    x s .callByValuePar T _ hOk _ E e he p hp
  intro i hi q hq
  have h := hLex [] (.call i []) hi q hq
  have hs := hg i H.bodies[i] (List.getElem?_eq_getElem hi)
  have ht := RecursiveParserStability.installed H.bodies i H.bodies[i] (List.getElem?_eq_getElem hi)
  cases s <;> simpa only [lexical,evV,hs,ht,evParArgs,evSeqArgs,List.length_nil,ite_true] using h

/-- The combined frozen floor initializes the verifier one ordinary round
after the independent nullary component has stabilized. -/
theorem stable_unary (H : Header) (body : MExp)
    (hbody : HelperArgument.Syntax H.bodies.length body) (g : MGrammar) (hg : Installed H.bodies g)
    (hr : ruleAtM g.rules H.bodies.length=some ⟨1,body⟩)
    (x : List Char) (s : Strategy) : ClockFreezing.StableRows g x s (pick H) (floor H x) := by
  have hs := RecursiveParserStability.helpers_stable H.valid hg x s
  intro k i hi W
  have hle : i≤H.bodies.length := by simpa [pick] using hi
  by_cases hlt : i<H.bodies.length
  · have hip : RecursiveParserStability.pick H.bodies i=true := by simp [RecursiveParserStability.pick,hlt]
    have h1 := hs (1+k) i hip W
    have h2 := hs 1 i hip W
    dsimp only [floor]
    simpa only [Nat.add_assoc] using h1.trans h2.symm
  · have he : i=H.bodies.length := by omega
    subst i
    have hn : floor H x+k=RecursiveParserStability.floor H.bodies x+k+1 := by unfold floor; omega
    rw [hn,show floor H x=RecursiveParserStability.floor H.bodies x+1 from rfl]
    simp only [tblV,hr]
    apply List.map_congr_left
    intro p hp
    apply HelperArgument.eval_eq hg hg x s s _ _ (tblV_ok g x s _) _ W
      (body)
      hbody p
      (by have := List.mem_range.mp hp; omega)
    intro j hj q hq
    exact congrArg (fun row => valAt row q) (hs k j (by simp [RecursiveParserStability.pick,hj]) [])

/-- Specialization to the original last-header verifier. -/
theorem stable (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (hr : ruleAtM g.rules H.bodies.length=some ⟨1,LastCodewordVerification.verifier H.head⟩)
    (x : List Char) (s : Strategy) : ClockFreezing.StableRows g x s (pick H) (floor H x) :=
  stable_unary H (LastCodewordVerification.verifier H.head)
    ⟨⟨lexical_syntax _ H.head H.lexical,True.intro⟩,lexical_syntax _ H.head H.lexical⟩ g hg hr x s

/-- Any table whose selected rows are the actual combined-floor rows
agrees with the standalone canonical helper parser on every valid suffix. -/
theorem lexical_table (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hRows : ∀ i, i<H.bodies.length → T i []=tblV g x s (floor H x) i []) :
    LexicalTable H g x s T := by
  intro E e he p hp
  apply RecursiveParserStability.lexical_eval hg (RecursiveParserStability.installed H.bodies)
    x s .callByValuePar T _ hOk _ E [] e he p hp
  intro i hi q hq
  rw [hRows i hi]
  have hstable := RecursiveParserStability.helpers_stable H.valid hg x s 1 i
    (by simp [RecursiveParserStability.pick,hi]) []
  rw [show floor H x=RecursiveParserStability.floor H.bodies x+1 from rfl,hstable]
  exact congrArg (fun row => valAt row q)
    (RecursiveParserStability.helper_rows_eq H.valid hg (RecursiveParserStability.installed H.bodies)
      x s .callByValuePar (RecursiveParserStability.floor H.bodies x) i hi [] [])

theorem physical_lexical (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) :
    LexicalTable H g x s (tblV g x s (RecursiveParserStability.floor H.bodies x)) := by
  intro E e he p hp
  apply RecursiveParserStability.lexical_eval hg (RecursiveParserStability.installed H.bodies)
    x s .callByValuePar _ _ (tblV_ok g x s _) _ E [] e he p hp
  intro i hi q hq
  exact congrArg (fun row => valAt row q)
    (RecursiveParserStability.helper_rows_eq H.valid hg (RecursiveParserStability.installed H.bodies)
      x s .callByValuePar (RecursiveParserStability.floor H.bodies x) i hi [] [])

theorem argument_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (argument H) p=argumentAt H x p :=
  hLex E _ (argument_lexical H) p hp

theorem prefix_eval (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x s T) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T W (.seq H.head (.param 0)) p=prefixAt H x W p :=
  syntax_eval H g hg x s T hOk hLex W (.seq H.head (.param 0)) ⟨lexical_syntax _ H.head H.lexical,True.intro⟩ p hp

theorem probe_eval (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x s T) (p : Nat) (hp : p≤x.length) :
    LastCodewordVerification.probe g x s T H.head p=probe H x p := by
  unfold probe LastCodewordVerification.probe
  rw [hLex [] H.head H.lexical p hp]
  change (match lexical H H.head x p with
    | some (some j) => evV g x s T [pre x p j] (LastCodewordVerification.verifier H.head) j | other => other)=
    (match lexical H H.head x p with
    | some (some j) => evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
        (canonical H.bodies x) [pre x p j] (LastCodewordVerification.verifier H.head) j | other => other)
  cases hv : lexical H H.head x p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := (RecursiveCodeGrammar.lexical_success H H.head H.lexical x p j hp hv).1
      exact syntax_eval H g hg x s T hOk hLex [pre x p j] (LastCodewordVerification.verifier H.head)
        ⟨⟨lexical_syntax _ H.head H.lexical,True.intro⟩,lexical_syntax _ H.head H.lexical⟩ j hj

end Shallot.MacroPeg.CBV.LastCodewordHelpers
