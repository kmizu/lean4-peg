import MacroPeg.CBV.FiniteWordCaptureSelection

namespace Shallot.MacroPeg.CBV.FiniteSuffixBody
open ClockFreezing (Table)

inductive Body where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | helper (i : Nat) | replay (i : Nat)
  | seq (a b : Body) | alt (a b : Body) | notP (a : Body) | star (a : Body)
  deriving Repr

def render (n : Nat) (R : List (List Char)) (V : Option (List (Option (List Char)))) : Body → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .helper i => if i<n then .call i [] else MExp.failAlways
  | .replay i => .seq (FiniteSuffixReplay.guard R) (match V with
      | none => .param i | some V => FiniteSuffixReplay.literal V i)
  | .seq a b => .seq (render n R V a) (render n R V b)
  | .alt a b => .alt (render n R V a) (render n R V b)
  | .notP a => .notP (render n R V a)
  | .star a => .star (render n R V a)

theorem firstOrder (n : Nat) (R : List (List Char)) (V : Option (List (Option (List Char)))) :
    ∀ B, (render n R V B).FirstOrder
  | .seq a b | .alt a b => ⟨firstOrder n R V a,firstOrder n R V b⟩
  | .notP a | .star a => firstOrder n R V a
  | .helper i => by simp only [render]; split <;> trivial
  | .replay i => by
    cases V with
    | none => exact ⟨FiniteSuffixReplay.guard_firstOrder R,True.intro⟩
    | some V => exact ⟨FiniteSuffixReplay.guard_firstOrder R,FiniteSuffixReplay.literal_firstOrder V i⟩
  | .eps | .any | .chr _ | .range _ _ | .lit _ => True.intro

/-- A finite suffix dictionary supports exact content specialization at any
current position, including after arbitrary consuming helper control. -/
theorem aligned (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (n : Nat) (R : List (List Char)) (ht : OkTV x.length T)
    (helpers : ∀ i, i<n → ∀ p, p≤x.length →
      evV g x .callByValuePar T E (.call i []) p=evV h x .callByValueSeq U [] (.call i []) p) :
    ∀ B p, p≤x.length →
    evV g x .callByValuePar T E (render n R none B) p=
      evV h x .callByValueSeq U [] (render n R (some (FiniteSuffixReplay.views R E)) B) p
  | .helper i,p,hp => by
    by_cases hi : i<n
    · simp only [render,if_pos hi]; exact helpers i hi p hp
    · simp [render,hi,MExp.failAlways,evV]
  | .replay i,p,hp => FiniteSuffixReplay.replay_eval g h x _ _ T U E R i p hp
  | .seq a b,p,hp => by
    have ha := aligned g h x T U E n R ht helpers a p hp
    cases he : evV g x .callByValuePar T E (render n R none a) p with
    | none => simp only [render,evV_seq_none he,evV_seq_none (ha.symm.trans he)]
    | some v => cases v with
      | none => simp only [render,evV_seq_fail he,evV_seq_fail (ha.symm.trans he)]
      | some j =>
        simp only [render,evV_seq_ok he,evV_seq_ok (ha.symm.trans he)]
        exact aligned g h x T U E n R ht helpers b j (evV_ok ht _ p hp j he)
  | .alt a b,p,hp => by
    have ha := aligned g h x T U E n R ht helpers a p hp
    cases he : evV g x .callByValuePar T E (render n R none a) p with
    | none => simp only [render,evV_alt_none he,evV_alt_none (ha.symm.trans he)]
    | some v => cases v with
      | none =>
        simp only [render,evV_alt_fail he,evV_alt_fail (ha.symm.trans he)]
        exact aligned g h x T U E n R ht helpers b p hp
      | some j => simp only [render,evV_alt_ok he,evV_alt_ok (ha.symm.trans he)]
  | .notP a,p,hp => by simp only [render,evV,aligned g h x T U E n R ht helpers a p hp]
  | .star a,p,hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => aligned g h x T U E n R ht helpers a q (by omega))
  | .eps,_,_ | .any,_,_ | .chr _,_,_ | .range _ _,_,_ | .lit _,_,_ => rfl

end Shallot.MacroPeg.CBV.FiniteSuffixBody
