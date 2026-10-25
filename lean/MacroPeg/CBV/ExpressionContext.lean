import MacroPeg.CBV.BoundedBodyRewrite

namespace Shallot.MacroPeg.CBV.ExpressionContext
open ClockFreezing (Table)

inductive Context where
  | hole
  | atom (e : MExp)
  | seq (a b : Context)
  | alt (a b : Context)
  | notP (a : Context)
  | star (a : Context)

def plug (e : MExp) : Context → MExp
  | .hole => e
  | .atom a => a
  | .seq a b => .seq (plug e a) (plug e b)
  | .alt a b => .alt (plug e a) (plug e b)
  | .notP a => .notP (plug e a)
  | .star a => .star (plug e a)

theorem firstOrder (A B : MExp) (hB : B.FirstOrder) : ∀ C,
    (plug A C).FirstOrder → (plug B C).FirstOrder
  | .hole,_ => hB
  | .atom _,h => h
  | .seq a b,h | .alt a b,h => ⟨firstOrder A B hB a h.1,firstOrder A B hB b h.2⟩
  | .notP a,h | .star a,h => firstOrder A B hB a h

/-- Contextual refinement includes committed choice, negation, and partial
repetition. Only a defined result constrains the refining evaluator. -/
theorem refinement (g : MGrammar) (x : List Char) (s : Strategy) (T U : Table) (E : List (List Char))
    (hT : OkTV x.length T) (hTU : TLeV T U) (A B : MExp)
    (hAB : ∀ p, p≤x.length → RLe (evV g x s T E A p) (evV g x s U E B p)) :
    ∀ C p, p≤x.length → RLe (evV g x s T E (plug A C) p) (evV g x s U E (plug B C) p)
  | .hole,p,hp => hAB p hp
  | .atom a,p,_ => evV_mono hTU a p
  | .seq a b,p,hp => by
    have ha := refinement g x s T U E hT hTU A B hAB a p hp
    cases hv : evV g x s T E (plug A a) p with
    | none => simp only [plug]; rw [evV_seq_none hv]; exact Or.inl rfl
    | some v =>
      have hu := ha.eq_of_some hv
      cases v with
      | none => simp only [plug]; rw [evV_seq_fail hv,evV_seq_fail hu]; exact RLe.refl _
      | some j =>
        have hj := evV_ok (g := g) (s := s) (E := E) hT (plug A a) p hp
        rw [hv] at hj
        simp only [plug]; rw [evV_seq_ok hv,evV_seq_ok hu]
        exact refinement g x s T U E hT hTU A B hAB b j (hj j rfl)
  | .alt a b,p,hp => by
    have ha := refinement g x s T U E hT hTU A B hAB a p hp
    cases hv : evV g x s T E (plug A a) p with
    | none => simp only [plug]; rw [evV_alt_none hv]; exact Or.inl rfl
    | some v =>
      have hu := ha.eq_of_some hv
      cases v with
      | none =>
        simp only [plug]; rw [evV_alt_fail hv,evV_alt_fail hu]
        exact refinement g x s T U E hT hTU A B hAB b p hp
      | some j => simp only [plug]; rw [evV_alt_ok hv,evV_alt_ok hu]; exact RLe.refl _
  | .notP a,p,hp => by
    have ha := refinement g x s T U E hT hTU A B hAB a p hp
    cases hv : evV g x s T E (plug A a) p with
    | none => simp only [plug]; rw [evV_not_none hv]; exact Or.inl rfl
    | some v =>
      have hu := ha.eq_of_some hv
      cases v with
      | none => simp only [plug]; rw [evV_not_fail hv,evV_not_fail hu]; exact RLe.refl _
      | some j => simp only [plug]; rw [evV_not_ok hv,evV_not_ok hu]; exact RLe.refl _
  | .star a,p,hp => by
    simp only [plug]; rw [evV_star,evV_star]
    exact evStar_mono p (fun q hq => refinement g x s T U E hT hTU A B hAB a q (Nat.le_trans hq hp))

end Shallot.MacroPeg.CBV.ExpressionContext
