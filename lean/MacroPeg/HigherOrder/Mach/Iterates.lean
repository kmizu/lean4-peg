import MacroPeg.HigherOrder.Mach.DecideT
import MacroPeg.HigherOrder.Mach.CodesBound

/-!
# The rule values along the rounds

On an accepted reading, the rounds with the tables go through the iterates of the grammar written out:
`roundT` of `envFlat (iter m)` is `envFlat (iter (m + 1))` (`roundT_iter`). Their entries are the written-out
values of the rules: of the lengths of the rule types (`envFlat_lengths`), with codes at most `N + 2`
(`envFlat_small`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

theorem envFlat_small (N : Nat) : ∀ {S : List HO.Ty} {T : HO.Env S}, Env.Mem N T →
    ∀ f ∈ envFlat N T, Small (N + 2) f
  | [], _, _, f, hf => by simp [envFlat] at hf
  | τ :: S, (d, T), hT, f, hf => by
    simp only [envFlat, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact flatVal_small τ hT.1
    · exact envFlat_small N hT.2 f hf

theorem envFlat_lengths (N : Nat) : ∀ {S : List HO.Ty} {T : HO.Env S}, Env.Mem N T →
    (envFlat N T).map List.length = S.map (valSize N)
  | [], _, _ => rfl
  | τ :: S, (d, T), hT => by
    simp only [envFlat, List.map_cons, envFlat_lengths N hT.2, length_flatVal τ hT.1]

section Accepted

variable {j cap : Nat} {g : HGrammar} {bis : List (List Item)} {is : List Item} {x : List Char} {st : PSt}
  (G : TGrammar g.types)

/-- **The rounds with the tables go through the iterates.** -/
theorem roundT_iter (hr : ReadOK st g.types bis is x) (hbis : bodyItems G.bodies = bis)
    (hit : ∀ it ∈ st.bodies.flatten, ItemOK j cap st.tt st.ct it) (m : Nat) :
    roundT j cap x st.tt st.ct st.lt st.bodies (envFlat x.length (iter x G m)) =
      envFlat x.length (iter x G (m + 1)) := by
  rw [roundT_eq hit, roundM_eq hr.tt hr.bodies, ← hbis, roundP_eq (iter_mem x G m) G.bodies, round_iter]

/-- **The steps of the rounds**, when every round over an iterate costs at most `R`. -/
theorem fixCost_le (hr : ReadOK st g.types bis is (st.x.map Char.ofNat)) (hbis : bodyItems G.bodies = bis)
    (hit : ∀ it ∈ st.bodies.flatten, ItemOK j cap st.tt st.ct it) (R : Nat)
    (hR : ∀ m, roundCost j cap st (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m)) ≤ R) :
    ∀ fuel m, fixCost j cap st fuel (envFlat (st.x.map Char.ofNat).length (iter (st.x.map Char.ofNat) G m)) ≤
      (fuel + 1) * (R + 1)
  | 0, _ => by simp [fixCost]
  | fuel + 1, m => by
    rw [fixCost, roundT_iter G hr hbis hit m]
    have h₁ := hR m
    have ih := fixCost_le hr hbis hit R hR fuel (m + 1)
    split
    · rw [Nat.succ_mul]; omega
    · rw [Nat.succ_mul]; omega

end Accepted

end Shallot.MacroPeg.Mach
