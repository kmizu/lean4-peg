import Complexity.OneTape.Machine

/-!
# Sweeps of the simulator

`Leads P Q`: from every configuration in `P` the simulator reaches one in `Q`; it composes (`Leads.trans`).
`At x p T`: the simulator is in control state `x`, at cell `p`, with tape `T`.

* `at_step`: one step of a control state.
* `scanR` / `scanL`: a control state that just moves right (left) over the cells it passes, unchanged.
* `TapeRep T pos cells`: the tape `T` holds the columns of a `k`-tape configuration with heads `pos` and contents
  `cells`, the left bit exactly at cell `0`.
* `seek`: from cell `0`, a scan for the flag of tape `i` stops at that head; `home`: a scan left stops at cell `0`.
-/

namespace Complexity
namespace OneTape

variable {k : Nat} (M : TM k)

/-- From every configuration in `P`, the simulator reaches one in `Q`. -/
def Leads (P Q : Cfg 1 → Prop) : Prop := ∀ sc, P sc → ∃ n, Q ((sim M).run sc n)

theorem Leads.trans {P Q R : Cfg 1 → Prop} (h1 : Leads M P Q) (h2 : Leads M Q R) : Leads M P R := by
  intro sc hp
  obtain ⟨n, hq⟩ := h1 sc hp
  obtain ⟨m, hr⟩ := h2 _ hq
  exact ⟨n + m, by rw [TM.run_add]; exact hr⟩

theorem Leads.of_imp {P Q : Cfg 1 → Prop} (h : ∀ sc, P sc → Q sc) : Leads M P Q := fun sc hp => ⟨0, h sc hp⟩

theorem Leads.mono {P Q Q' : Cfg 1 → Prop} (h : Leads M P Q) (h' : ∀ sc, Q sc → Q' sc) : Leads M P Q' := by
  intro sc hp
  obtain ⟨n, hq⟩ := h sc hp
  exact ⟨n, h' _ hq⟩

/-- Updating a tape at one cell. -/
def upd (T : Nat → Nat) (p a : Nat) : Nat → Nat := fun j => if j = p then a else T j

theorem upd_eq (T : Nat → Nat) (p a : Nat) : upd T p a p = a := by simp [upd]

theorem upd_ne (T : Nat → Nat) {p j : Nat} (a : Nat) (h : j ≠ p) : upd T p a j = T j := by simp [upd, h]

/-- The simulator is in control state `x` at cell `p` with tape `T`. -/
def At (x : Ctl) (p : Nat) (T : Nat → Nat) (sc : Cfg 1) : Prop :=
  sc.state = enc M x ∧ sc.pos 0 = p ∧ sc.cells 0 = T

/-- **One step** in control state `x` with a result in range. -/
theorem at_step {x y : Ctl} {p a' : Nat} {T : Nat → Nat} {m : Move} (hx : WF M x) (hy : WF M y)
    (ha : a' < NA M) (hact : act M x (T p) = (enc M y, a', m)) :
    Leads M (At M x p T) (At M y (m.apply p) (upd T p a')) := by
  intro sc ⟨hs, hp, hT⟩
  refine ⟨1, ?_⟩
  have hr : sc.cells 0 (sc.pos 0) = T p := by rw [hp, hT]
  have h := step_ctl M hx hs (by rw [hr, hact]; exact enc_lt M hy) (by rw [hr, hact]; exact ha)
  rw [hr, hact] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · show ((sim M).step sc).pos 0 = _; rw [h2, hp]
  · show ((sim M).step sc).cells 0 = _; rw [h3, hp, hT]; rfl

/-- Writing back the symbol read leaves the tape. -/
theorem write_same (T : Nat → Nat) (p : Nat) : upd T p (T p) = T := by
  funext j; unfold upd; split
  · subst j; rfl
  · rfl

/-- **Scanning right**: a control state that moves right over the cells satisfying `P`. -/
theorem scanR {x : Ctl} (hx : WF M x) {P : Nat → Prop}
    (hmove : ∀ a, a < NA M → P a → act M x a = (enc M x, a, .R)) :
    ∀ n p (T : Nat → Nat), (∀ j, p ≤ j → j < p + n → T j < NA M ∧ P (T j)) →
      Leads M (At M x p T) (At M x (p + n) T)
  | 0, p, T, _ => Leads.of_imp M fun _ h => h
  | n + 1, p, T, hc => by
    have ih := scanR hx hmove n p T (fun j h1 h2 => hc j h1 (by omega))
    obtain ⟨hlt, hP⟩ := hc (p + n) (by omega) (by omega)
    have hs := at_step M hx hx hlt (hmove _ hlt hP)
    rw [write_same] at hs
    exact Leads.trans M ih hs

/-- **Scanning left**: a control state that moves left over the cells satisfying `P`. -/
theorem scanL {x : Ctl} (hx : WF M x) {P : Nat → Prop}
    (hmove : ∀ a, a < NA M → P a → act M x a = (enc M x, a, .L)) :
    ∀ n p (T : Nat → Nat), n ≤ p → (∀ j, p - n < j → j ≤ p → T j < NA M ∧ P (T j)) →
      Leads M (At M x p T) (At M x (p - n) T)
  | 0, p, T, _, _ => Leads.of_imp M fun _ h => h
  | n + 1, p, T, hn, hc => by
    have ih := scanL hx hmove n p T (by omega) (fun j h1 h2 => hc j (by omega) h2)
    obtain ⟨hlt, hP⟩ := hc (p - n) (by omega) (by omega)
    have hs := at_step M hx hx hlt (hmove _ hlt hP)
    rw [write_same] at hs
    have e : Move.apply .L (p - n) = p - (n + 1) := by show p - n - 1 = _; omega
    rw [e] at hs
    exact Leads.trans M ih hs

/-! ## Tapes holding the columns of a configuration -/

/-- The flag digit of tape `i` at cell `j`. -/
def flag {k : Nat} (pos : Fin k → Nat) (i : Fin k) (j : Nat) : Nat := if pos i = j then 1 else 0

/-- The tape `T` holds the columns of the tapes `cells` with heads `pos`. -/
def TapeRep (T : Nat → Nat) (pos : Fin k → Nat) (cells : Fin k → Nat → Nat) : Prop :=
  ∀ j, T j < NA M ∧ (clft (T j) = true ↔ j = 0) ∧ ∀ i : Fin k, cdig M (T j) i.val = 2 * cells i j + flag pos i j

/-- **Seeking a head**: from cell `0`, a scan for the flag of tape `i` stops at head `i`. -/
theorem seek {x : Ctl} (hx : WF M x) {T : Nat → Nat} {pos : Fin k → Nat} {cells : Fin k → Nat → Nat}
    (hT : TapeRep M T pos cells) (i : Fin k)
    (hmove : ∀ a, a < NA M → cdig M a i.val % 2 ≠ 1 → act M x a = (enc M x, a, .R)) :
    Leads M (At M x 0 T) (At M x (pos i) T) := by
  have h := scanR M hx hmove (pos i) 0 T (fun j _ hj => by
    obtain ⟨hlt, _, hd⟩ := hT j
    refine ⟨hlt, ?_⟩
    rw [hd i]
    have : flag pos i j = 0 := by unfold flag; rw [if_neg (by omega)]
    omega)
  rw [Nat.zero_add] at h
  exact h

/-- **Going home**: a scan left over cells without the left bit stops at cell `0`. -/
theorem home {x : Ctl} (hx : WF M x) {T : Nat → Nat} (hl : ∀ j, T j < NA M ∧ (clft (T j) = true ↔ j = 0))
    (hmove : ∀ a, a < NA M → clft a = false → act M x a = (enc M x, a, .L)) (p : Nat) :
    Leads M (At M x p T) (At M x 0 T) := by
  have h := scanL M hx hmove p p T (Nat.le_refl _) (fun j h1 _ => by
    obtain ⟨hlt, hj⟩ := hl j
    refine ⟨hlt, ?_⟩
    cases e : clft (T j)
    · rfl
    · exact absurd (hj.1 e) (by omega))
  rw [Nat.sub_self] at h
  exact h

end OneTape
end Complexity
