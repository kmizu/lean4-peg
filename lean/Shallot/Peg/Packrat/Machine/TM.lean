import Shallot.Peg.Packrat.Machine.Main
import Complexity.ListTime

/-!
# A uniform polynomial bound on actual Turing machines

Compile the complete stack recognizer with the existing verified stack,
list, and tape translations. Space follows from its cubic stack time.
The resulting time is bounded by a polynomial of degree fifteen for every
grammar; the coefficient may depend on the grammar and the two characters.
-/

namespace Shallot.Packrat.Machine

open Complexity

def stackTime (g : Grammar) (f : Bool → Char) (N : Nat) : Nat := programCoeff g f * (N + 1) ^ 3

def stackSpace (g : Grammar) (f : Bool → Char) (N : Nat) : Nat :=
  2 * N + stackTime g f N * (stackTime g f N + 2) + 2

def listSpace (g : Grammar) (f : Bool → Char) (N : Nat) : Nat := stackSpace g f N + (2 * N + 2)

def listTime (g : Grammar) (f : Bool → Char) (N : Nat) : Nat :=
  (N + 1) * 5 + stackTime g f N * ncost (listSpace g f N)

def tmTime (g : Grammar) (f : Bool → Char) : Nat → Nat := lmTime (listSpace g f) (listTime g f)

/-- The verified translations give a decider with an explicit machine-time budget. -/
theorem program_tm (g : Grammar) (f : Bool → Char) :
    ∃ M : TM (NK g + 1), M.Decides (bitLanguage g f) ∧
      ∀ w, (M.run (initCfg (NK g + 1) w) (tmTime g f w.length)).halted := by
  have hK : 1 < NK g := by unfold NK; omega
  have hruns : ∀ w, ∃ t b L', t ≤ listTime g f w.length ∧
      LExec (LenOK (listSpace g f w.length)) (.seq (importP hK) (program g f).compile)
        (initLists (NK g + 1) w) t (.stop b L') ∧ (b = true ↔ bitLanguage g f w) := by
    intro w
    obtain ⟨b, S', ⟨t, ht, hx⟩, hb⟩ := program_halts g f w
    have hT : t ≤ stackTime g f w.length := Nat.le_trans ht (programCost_le g f w.length)
    have hx₁ : NExec (NFits (stackSpace g f w.length)) (program g f) (nInit (NK g) w) t (.stop b S') :=
      (nexec_space hx 1 (2 * w.length) (bnd_nInit w)).2 _ (by
        have hg : grow 1 t ≤ stackTime g f w.length * (stackTime g f w.length + 2) :=
          Nat.mul_le_mul hT (by omega)
        unfold stackSpace
        omega)
    obtain ⟨t', ht', hx'⟩ := nprog_lexec hK (program g f) w (B := listSpace g f w.length)
      (by unfold listSpace stackSpace; omega)
      (hx₁.mono (fun _ hS => hS.mono (by unfold listSpace; omega)))
    refine ⟨t', b, _, ?_, hx', hb⟩
    have hm := Nat.mul_le_mul_right (ncost (listSpace g f w.length)) hT
    unfold listTime
    omega
  exact lm_time (by omega) (.seq (importP hK) (program g f).compile) 3 (by decide)
    (nprog_constOK hK (program g f)) (bitLanguage g f) (listSpace g f) (listTime g f) hruns

/-- A polynomial bound with the exponent fixed in the proposition. -/
private inductive Degree (d : Nat) (F : Nat → Nat) : Prop where
  | intro (c : Nat) (bound : ∀ N, F N ≤ c * (N + 1) ^ d) : Degree d F

private theorem degree_const (d c : Nat) : Degree d (fun _ => c) := by
  refine ⟨c, fun N => ?_⟩
  have hm := Nat.mul_le_mul_left c (Nat.one_le_pow d (N + 1) (by omega))
  simpa only [Nat.mul_one] using hm

private theorem degree_lift {d e : Nat} {F : Nat → Nat} (h : Degree d F) (hde : d ≤ e) : Degree e F := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun N => Nat.le_trans (hc N) (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega) hde))⟩

private theorem degree_add {d : Nat} {F G : Nat → Nat} (hf : Degree d F) (hg : Degree d G) :
    Degree d (fun N => F N + G N) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨c + b, fun N => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add (hc N) (hb N)

private theorem degree_mul {d e : Nat} {F G : Nat → Nat} (hf : Degree d F) (hg : Degree e G) :
    Degree (d + e) (fun N => F N * G N) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨c * b, fun N => ?_⟩
  have hm := Nat.mul_le_mul (hc N) (hb N)
  have he : (c * (N + 1) ^ d) * (b * (N + 1) ^ e) = (c * b) * (N + 1) ^ (d + e) := by
    rw [Nat.pow_add]
    simp only [Nat.mul_assoc, Nat.mul_left_comm]
  rwa [he] at hm

private theorem degree_scale {d : Nat} {F : Nat → Nat} (c : Nat) (hf : Degree d F) :
    Degree d (fun N => c * F N) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨c * b, fun N => ?_⟩
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (hb N)

private theorem degree_linear (a b : Nat) : Degree 1 (fun N => a * N + b) := by
  refine ⟨a + b, fun N => ?_⟩
  have ha := Nat.mul_le_mul_left a (show N ≤ N + 1 by omega)
  have hb := Nat.mul_le_mul_left b (show 1 ≤ N + 1 by omega)
  rw [Nat.mul_one] at hb
  rw [Nat.pow_one, Nat.add_mul]
  omega

/-- The compiled decider's time has the same degree bound for every grammar. -/
theorem tmTime_degree15 (g : Grammar) (f : Bool → Char) :
    ∃ c, ∀ N, tmTime g f N ≤ c * (N + 1) ^ 15 := by
  suffices h : Degree 15 (tmTime g f) from by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  have ht : Degree 3 (stackTime g f) := ⟨programCoeff g f, fun _ => Nat.le_refl _⟩
  have hs : Degree 6 (stackSpace g f) := by
    exact degree_add (degree_add (degree_lift (degree_linear 2 0) (by omega))
      (degree_mul ht (degree_add ht (degree_const 3 2)))) (degree_const 6 2)
  have hls : Degree 6 (listSpace g f) :=
    degree_add hs (degree_lift (degree_linear 2 2) (by omega))
  have hnc : Degree 6 (fun N => ncost (listSpace g f N)) :=
    degree_add (degree_scale 8 hls) (degree_const 6 16)
  have hlt : Degree 9 (listTime g f) := by
    have hfirst : Degree 9 (fun N => (N + 1) * 5) := by
      apply degree_lift (d := 1) (hde := by omega)
      simpa only [Nat.add_mul, Nat.one_mul, Nat.mul_comm] using degree_linear 5 5
    exact degree_add hfirst (degree_mul ht hnc)
  have hN2 : Degree 1 (fun N => N + 2) := by simpa only [Nat.one_mul] using degree_linear 1 2
  have hfac : Degree 6 (fun N => 8 * (listSpace g f N + (N + 2)) + 20) :=
    degree_add (degree_scale 8 (degree_add hls (degree_lift (d := 1) (e := 6) hN2 (by omega)))) (degree_const 6 20)
  exact degree_add (degree_lift (e := 15) (degree_linear 4 8) (by omega)) (degree_mul hlt hfac)

/-- Every fixed PEG on the two input characters has a concrete degree-15 TM decider. -/
theorem bitLanguage_time15 (g : Grammar) (f : Bool → Char) :
    ∃ (M : TM (NK g + 1)) (c : Nat), M.Decides (bitLanguage g f) ∧
      ∀ w, (M.run (initCfg (NK g + 1) w) (c * (w.length + 1) ^ 15)).halted := by
  obtain ⟨M, hdec, hh⟩ := program_tm g f
  obtain ⟨c, hc⟩ := tmTime_degree15 g f
  refine ⟨M, c, hdec, fun w => ?_⟩
  rw [TM.run_stays M _ (hc w.length) (hh w)]
  exact hh w

end Shallot.Packrat.Machine
