import MacroPeg.CBV.ParserPrefixFusion
import MacroPeg.CBV.ClockFreezing

/-! A closed mutually recursive PEG component stabilizes independently of
arbitrary user rules. Freeze actual rows, including undefined results. -/
namespace Shallot.MacroPeg.CBV.RecursiveParserStability
open ClockFreezing (Table)

def Lexical (n : Nat) : MExp → Prop
  | .call i [] => i<n
  | .seq a b | .alt a b => Lexical n a ∧ Lexical n b
  | .star a | .notP a => Lexical n a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => True
  | _ => False

def Valid (bodies : List MExp) : Prop := ∀ e ∈ bodies, Lexical bodies.length e

def Installed (bodies : List MExp) (g : MGrammar) : Prop :=
  ∀ i e, bodies[i]? = some e → ruleAtM g.rules i = some ⟨0,e⟩

def grammar (bodies : List MExp) : MGrammar := ⟨bodies.map (fun e => ⟨0,e⟩)⟩

theorem installed (bodies : List MExp) : Installed bodies (grammar bodies) := by
  intro i e hi
  simp [grammar,ruleAtM_eq_getElem?,hi]

theorem lexical_firstOrder (n : Nat) : ∀ e, Lexical n e → e.FirstOrder
  | .call _ [], _ => trivial
  | .seq a b, h | .alt a b, h => ⟨lexical_firstOrder n a h.1,lexical_firstOrder n b h.2⟩
  | .star a, h | .notP a, h => lexical_firstOrder n a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .call _ (_::_), h | .param _, h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem lexical_zero_iff_pure : ∀ e, Lexical 0 e ↔ ParserPrefixFusion.Pure e
  | .seq a b | .alt a b => by simp only [Lexical,ParserPrefixFusion.Pure,lexical_zero_iff_pure a,lexical_zero_iff_pure b]
  | .star a | .notP a => lexical_zero_iff_pure a
  | .call _ [] => by simp [Lexical,ParserPrefixFusion.Pure]
  | .call _ (_::_) | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _
  | .lam _ _ | .callParam _ _ | .invoke _ _ _ => Iff.rfl

theorem lexical_eval {bodies : List MExp} {g h : MGrammar}
    (hg : Installed bodies g) (hh : Installed bodies h) (x : List Char) (s t : Strategy)
    (T U : Table) (hOk : OkTV x.length T)
    (hRows : ∀ i, i<bodies.length → ∀ p, p ≤ x.length → valAt (T i []) p = valAt (U i []) p)
    (E F : List (List Char)) : ∀ e, Lexical bodies.length e → ∀ p, p ≤ x.length →
      evV g x s T E e p = evV h x t U F e p
  | .call i [], hi, p, hp => by
    have hr := List.getElem?_eq_getElem hi
    have hgr := hg i bodies[i] hr
    have hhr := hh i bodies[i] hr
    cases s <;> cases t <;> simpa only [evV,hgr,hhr,evParArgs,evSeqArgs,List.length_nil,ite_true] using hRows i hi p hp
  | .seq a b, he, p, hp => by
    have hh' := lexical_eval hg hh x s t T U hOk hRows E F a he.1 p hp
    cases hv : evV g x s T E a p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh'.symm.trans hv)]
    | some r => cases r with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh'.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh'.symm.trans hv)]
        exact lexical_eval hg hh x s t T U hOk hRows E F b he.2 q (evV_ok hOk a p hp q hv)
  | .alt a b, he, p, hp => by
    have hh' := lexical_eval hg hh x s t T U hOk hRows E F a he.1 p hp
    cases hv : evV g x s T E a p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh'.symm.trans hv)]
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (hh'.symm.trans hv)]
        exact lexical_eval hg hh x s t T U hOk hRows E F b he.2 p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh'.symm.trans hv)]
  | .star a, he, p, hp => by
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q hq => lexical_eval hg hh x s t T U hOk hRows E F a he q (by omega))
  | .notP a, he, p, hp => by simp only [evV]; rw [lexical_eval hg hh x s t T U hOk hRows E F a he p hp]
  | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_), he, _, _ | .param _, he, _, _ | .dbg _, he, _, _ | .lam _ _, he, _, _
  | .callParam _ _, he, _, _ | .invoke _ _ _, he, _, _ => False.elim he

/-- Complete helper rows agree in any two extensions, environments, and
strategies, at every physical round; users cannot affect this component. -/
theorem helper_rows_eq {bodies : List MExp} (hf : Valid bodies) {g h : MGrammar}
    (hg : Installed bodies g) (hh : Installed bodies h) (x : List Char) (s t : Strategy) (k : Nat) :
    ∀ i, i<bodies.length → ∀ E F, tblV g x s k i E = tblV h x t k i F := by
  induction k with
  | zero => intro i hi E F; rfl
  | succ k ih =>
    intro i hi E F
    have hr := List.getElem?_eq_getElem hi
    simp only [tblV,hg i bodies[i] hr,hh i bodies[i] hr]
    apply List.map_congr_left
    intro p hp
    apply lexical_eval hg hh x s t _ _ (tblV_ok g x s k)
      (fun j hj q _ => congrArg (fun row => valAt row q) (ih j hj [] [])) E F bodies[i]
      (hf _ (List.mem_of_getElem? hr)) p
    have := List.mem_range.mp hp
    omega

def floor (bodies : List MExp) (x : List Char) : Nat := iterBoundV (grammar bodies) x + 1
def pick (bodies : List MExp) (i : Nat) : Bool := decide (i<bodies.length)

theorem floor_agree (bodies : List MExp) (x : List Char) (s : Strategy) (k : Nat) :
    AgreeV (grammar bodies) x (tblV (grammar bodies) x s (floor bodies x))
      (tblV (grammar bodies) x s (floor bodies x+k)) := by
  obtain ⟨m,hm,hfix⟩ := tblV_fix_exists (grammar bodies) x s
  have hleft := agreeV_from hfix (floor bodies x-m)
  have hright := agreeV_from hfix (floor bodies x+k-m)
  have hm' : m ≤ floor bodies x := by dsimp [floor]; omega
  rw [Nat.add_sub_cancel' hm'] at hleft
  rw [Nat.add_sub_cancel' (by omega)] at hright
  exact hleft.symm.trans hright

theorem row_length {bodies : List MExp} {g : MGrammar} (hg : Installed bodies g)
    (x : List Char) (s : Strategy) (k i : Nat) (hi : i<bodies.length) (hk : 0<k)
    (E : List (List Char)) : (tblV g x s k i E).length = x.length+1 := by
  cases k with
  | zero => omega
  | succ k => simp [tblV,hg i bodies[i] (List.getElem?_eq_getElem hi)]

/-- Arbitrary mutually recursive lexical PEGs, including nonterminating
cycles, have stable actual helper rows at this input-dependent finite floor. -/
theorem helpers_stable {bodies : List MExp} (hf : Valid bodies) {g : MGrammar}
    (hg : Installed bodies g) (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows g x s (pick bodies) (floor bodies x) := by
  intro k i hi E
  have hi' : i<bodies.length := by simpa only [pick,decide_eq_true_eq] using hi
  rw [helper_rows_eq hf hg (installed bodies) x s s (floor bodies x+k) i hi' E [],
    helper_rows_eq hf hg (installed bodies) x s s (floor bodies x) i hi' E []]
  have hfloor : 0<floor bodies x := by simp [floor]
  apply List.ext_getElem
  · rw [row_length (installed bodies) x s _ i hi' (by omega),
      row_length (installed bodies) x s _ i hi' hfloor]
  · intro p hp hp'
    have hbound : p ≤ x.length := by
      rw [row_length (installed bodies) x s _ i hi' (by omega)] at hp
      omega
    have hrow := floor_agree bodies x s k i ⟨0,bodies[i]⟩ []
      (installed bodies i bodies[i] (List.getElem?_eq_getElem hi')) (by simp [words]) p hbound
    simpa only [valAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hp,
      List.getElem?_eq_getElem hp',Option.getD_some] using hrow.symm

abbrev frozen (bodies : List MExp) (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) : Table :=
  ClockFreezing.frozen g x s (pick bodies) (floor bodies x) k

/-- Once actual helpers are frozen, their expressions agree across all
user stages, environments, and either calling strategy, without an oracle. -/
theorem frozen_lexical_eval {bodies : List MExp} (hf : Valid bodies) {g h : MGrammar}
    (hg : Installed bodies g) (hh : Installed bodies h) (x : List Char) (s t : Strategy)
    (k l : Nat) (E F : List (List Char)) (e : MExp) (he : Lexical bodies.length e)
    (p : Nat) (hp : p ≤ x.length) :
    evV g x s (frozen bodies g x s k) E e p =
      evV h x t (frozen bodies h x t l) F e p := by
  apply lexical_eval hg hh x s t _ _ (ClockFreezing.frozen_ok _ _ _ _ _ _) _ E F e he p hp
  intro i hi q _
  have hb : pick bodies i = true := by simp [pick,hi]
  change valAt (ClockFreezing.frozen g x s (pick bodies) (floor bodies x) k i []) q =
    valAt (ClockFreezing.frozen h x t (pick bodies) (floor bodies x) l i []) q
  rw [ClockFreezing.frozen_rows g x s (pick bodies) (floor bodies x) k i hb [],
    ClockFreezing.frozen_rows h x t (pick bodies) (floor bodies x) l i hb []]
  exact congrArg (fun row => valAt row q) (helper_rows_eq hf hg hh x s t _ i hi [] [])

/-- Freezing a recursive parser does not manufacture a result for an
unproductive cycle, at any actual physical stage or calling strategy. -/
theorem cycle_undefined {g : MGrammar} (hr : ruleAtM g.rules 0 = some ⟨0,.call 0 []⟩)
    (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p ≤ x.length) :
    evV g x s (tblV g x s k) E (.call 0 []) p = none := by
  have hcall (T : Table) (F : List (List Char)) (q : Nat) :
      evV g x s T F (.call 0 []) q = valAt (T 0 []) q := by
    cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  have hrow : ∀ j q, q ≤ x.length → valAt (tblV g x s j 0 []) q = none := by
    intro j
    induction j with
    | zero => intro q hq; rfl
    | succ j ih =>
      intro q hq
      rw [valAt_tblV_succ hr [] hq,hcall]
      exact ih q hq
  rw [hcall]
  exact hrow k p hp

end Shallot.MacroPeg.CBV.RecursiveParserStability
