import MacroPeg.CBV.RepeatedFrontierExamples
import MacroPeg.CBV.ScannerFrontier

/-! A limit of choosing a frontier using only whole-projection success
tests. This concerns the explicitly compiled selector syntax below, not
arbitrary Seq grammars or language-class separation. -/
namespace Shallot.MacroPeg.CBV.FrontierStatusSelector
open CopyBodyControl (Body)
open ClockFreezing

def guardStatus : Body → Option Bool
  | .eps => some true | .fail => some false | .segment _ => some true
  | .seq a b => match guardStatus a with
    | none => none | some false => some false | some true => guardStatus b
  | .alt a b => match guardStatus a with
    | none => none | some false => guardStatus b | some true => some true
  | .notP a => (guardStatus a).map Bool.not
  | .star a => match guardStatus a with
    | some false => some true | _ => none

def guard (probes : Fin 2 → MExp) : Body → MExp
  | .eps => .eps | .fail => MExp.failAlways
  | .segment i => .andP (probes ⟨i%2,Nat.mod_lt _ (by decide)⟩)
  | .seq a b => .seq (guard probes a) (guard probes b)
  | .alt a b => .alt (guard probes a) (guard probes b)
  | .notP a => .notP (guard probes a)
  | .star a => .star (guard probes a)

def statusValue (p : Nat) : Option Bool → Res
  | none => none | some false => some none | some true => some (some p)

theorem guard_firstOrder (probes : Fin 2 → MExp) (hp : ∀ i, (probes i).FirstOrder) :
    ∀ b, (guard probes b).FirstOrder
  | .eps | .fail => True.intro
  | .segment _ => hp _
  | .seq a b | .alt a b => ⟨guard_firstOrder probes hp a,guard_firstOrder probes hp b⟩
  | .notP a | .star a => guard_firstOrder probes hp a

/-- All guard control stays at the original position, including nullable
repetition's undefined result. Probe endpoints are intentionally hidden. -/
theorem guard_physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (probes : Fin 2 → MExp) (p : Nat)
    (hp : ∀ i, ∃ q, evV g x s T E (probes i) p=some (some q)) :
    ∀ b, evV g x s T E (guard probes b) p=statusValue p (guardStatus b)
  | .eps => rfl
  | .fail => by simp [guard,guardStatus,statusValue,MExp.failAlways,evV]
  | .segment i => by
    obtain ⟨q,hq⟩ := hp ⟨i%2,Nat.mod_lt _ (by decide)⟩
    rw [guard,CallLookahead.evV_peek,hq]
    rfl
  | .seq a b => by
    have ha := guard_physical g x s T E probes p hp a
    have hb := guard_physical g x s T E probes p hp b
    cases hs : guardStatus a with
    | none => rw [guard,evV_seq_none (by simpa [hs,statusValue] using ha)]; simp [guardStatus,hs,statusValue]
    | some v => cases v with
      | false => rw [guard,evV_seq_fail (by simpa [hs,statusValue] using ha)]; simp [guardStatus,hs,statusValue]
      | true => rw [guard,evV_seq_ok (by simpa [hs,statusValue] using ha),hb]; simp [guardStatus,hs]
  | .alt a b => by
    have ha := guard_physical g x s T E probes p hp a
    have hb := guard_physical g x s T E probes p hp b
    cases hs : guardStatus a with
    | none => rw [guard,evV_alt_none (by simpa [hs,statusValue] using ha)]; simp [guardStatus,hs,statusValue]
    | some v => cases v with
      | false => rw [guard,evV_alt_fail (by simpa [hs,statusValue] using ha),hb]; simp [guardStatus,hs]
      | true =>
        have hh : evV g x s T E (guard probes a) p=some (some p) := by simpa [hs,statusValue] using ha
        rw [guard,evV_alt_ok hh]; simp [guardStatus,hs,statusValue]
  | .notP a => by
    rw [guard,evV,guard_physical g x s T E probes p hp a]
    cases hs : guardStatus a with
    | none => simp [guardStatus,hs,statusValue]
    | some v => cases v <;> simp [guardStatus,hs,statusValue]
  | .star a => by
    have ha := guard_physical g x s T E probes p hp a
    rw [guard,evV_star]
    cases hs : guardStatus a with
    | none => rw [evStar_none (by simpa [hs,statusValue] using ha)]; simp [guardStatus,hs,statusValue]
    | some v => cases v with
      | false => rw [evStar_fail (by simpa [hs,statusValue] using ha)]; simp [guardStatus,hs,statusValue]
      | true =>
        rw [evStar_stuck (by simpa [hs,statusValue] using ha) (Nat.lt_irrefl p)]
        simp [guardStatus,hs,statusValue]

inductive Tree where
  | choose (i : Fin 2) | fail | undef
  | branch (test : Body) (yes no : Tree)
  deriving Repr

inductive Outcome where
  | choose (i : Fin 2) | fail | undef
  deriving Repr

def selected : Tree → Outcome
  | .choose i => .choose i | .fail => .fail | .undef => .undef
  | .branch b yes no => match guardStatus b with
    | none => .undef | some true => selected yes | some false => selected no

def render (probes : Fin 2 → MExp) : Tree → MExp
  | .choose i => probes i | .fail => MExp.failAlways | .undef => .star .eps
  | .branch b yes no => RootObservation.branch (guard probes b) (render probes yes) (render probes no)

def outcomeValue (values : Fin 2 → Res) : Outcome → Res
  | .choose i => values i | .fail => some none | .undef => none

theorem render_firstOrder (probes : Fin 2 → MExp) (hp : ∀ i, (probes i).FirstOrder) :
    ∀ tree, (render probes tree).FirstOrder
  | .choose i => hp i
  | .fail | .undef => True.intro
  | .branch b yes no =>
    ⟨⟨guard_firstOrder probes hp b,render_firstOrder probes hp yes⟩,
      ⟨guard_firstOrder probes hp b,render_firstOrder probes hp no⟩⟩

theorem render_physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (probes : Fin 2 → MExp) (p : Nat)
    (hp : ∀ i, ∃ q, evV g x s T E (probes i) p=some (some q)) :
    ∀ tree, evV g x s T E (render probes tree) p=
      outcomeValue (fun i => evV g x s T E (probes i) p) (selected tree)
  | .choose _ => rfl
  | .fail => by simp [render,selected,outcomeValue,MExp.failAlways,evV]
  | .undef => by rw [render,evV_star,evStar_stuck rfl (Nat.lt_irrefl p)]; rfl
  | .branch b yes no => by
    have hg := guard_physical g x s T E probes p hp b
    cases hs : guardStatus b with
    | none =>
      have hn : evV g x s T E (guard probes b) p=none := by simpa [hs,statusValue] using hg
      rw [render,RootObservation.branch,evV_alt_none (evV_seq_none hn)]
      simp [selected,hs,outcomeValue]
    | some v => cases v with
      | false =>
        have hn : evV g x s T E (guard probes b) p=some none := by simpa [hs,statusValue] using hg
        rw [render,ScannerFrontier.branch_eval _ _ _ p false (by simpa using hn)]
        simpa only [selected,hs,ite_false,Bool.false_eq_true] using render_physical g x s T E probes p hp no
      | true =>
        have hn : evV g x s T E (guard probes b) p=some (some p) := by simpa [hs,statusValue] using hg
        rw [render,ScannerFrontier.branch_eval _ _ _ p true (by simpa using hn)]
        simpa only [selected,hs,ite_true] using render_physical g x s T E probes p hp yes

end Shallot.MacroPeg.CBV.FrontierStatusSelector
