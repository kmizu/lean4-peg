import MacroPeg.HigherOrder.Mach.Steps

/-!
# The final state of the reading machine

After `4 n + 1` steps from the start the machine has stopped (`pinit_stops`), so its state then is the state at any
earlier stopping time: it is the state `read_ok` reaches (`final_of_reach`), and it rejects when the machine fails
(`final_of_fails`).
-/

namespace Shallot.MacroPeg.Mach

/-- Once stopped, later states are the same. -/
theorem pruns_after {s : PSt} {a : Nat} (h : (pruns s a).ctl = []) : ∀ b, a ≤ b → pruns s b = pruns s a := by
  intro b hb
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [pruns_add, pruns_halted h]

/-- The state after `4 n + 1` steps. -/
def finalSt (tk : List Nat) : PSt := pruns (pinit tk) (4 * tk.length + 1)

theorem final_of_reach {tk : List Nat} {st : PSt} {n : Nat} (h : Reach (pinit tk) st n) (hc : st.ctl = [])
    (hn : n ≤ 4 * tk.length + 1) : finalSt tk = st := by
  unfold finalSt Reach at *
  rw [pruns_after (h ▸ hc) _ hn, h]

theorem final_of_fails {tk : List Nat} (h : Fails (pinit tk)) : (finalSt tk).ok = false := by
  obtain ⟨m, hc, hok⟩ := h
  unfold finalSt
  by_cases hm : m ≤ 4 * tk.length + 1
  · rw [pruns_after hc _ hm]; exact hok
  · rw [← pruns_after (pinit_stops tk) m (by omega)]; exact hok

end Shallot.MacroPeg.Mach
