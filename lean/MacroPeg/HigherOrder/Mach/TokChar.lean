import MacroPeg.HigherOrder.Mach.Tok

/-!
# Reading characters and strings on stacks

* `parseCharP`: read a character code (`parseNatP`) and check that it names a character (`Nat.isValidChar`:
  below `55296`, or between `57343` and `1114112`), comparing with constants (`cmpTop`); stop rejecting otherwise —
  exactly as `parseChar`.
* `parseStrP`: read `1 c₁ 1 c₂ … 0`, giving each character code to a sink — exactly as `parseStr`.
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.Flat
open Shallot.MacroPeg.KExp

variable {K : Nat}

/-- Check the code on top of `a` (kept): stop rejecting unless it names a character. Scratch: `c t u g f`. -/
def checkCharP (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) : NProg K :=
  .seq (npushC c 55296) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
    (.ite f .zero (.prim (.pop f))
      (.seq (.prim (.pop f)) (.seq (npushC c 57343) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
        (caseTop f [.halt false, .halt false,
          .seq (npushC c 1114112) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
            (.ite f .zero (.prim (.pop f)) (.halt false))))] (.halt false)))))))))

/-- Read a character code onto `a`. -/
def parseCharP (tk a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) : NProg K :=
  .seq (parseNatP tk a) (checkCharP a c t u g f hat hcu)

/-- Read a string; `sink` takes each code from the top of `a`. -/
def parseStrP (tk a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (sink : NProg K) : NProg K :=
  .seq (.loop tk .pos (.seq (.prim (.dec tk))
      (.ite tk .zero (.seq (.prim (.pop tk)) (.seq (parseCharP tk a c t u g f hat hcu) sink)) (.halt false))))
    (.ite tk .zero (.prim (.pop tk)) (.halt false))

theorem toNat_ofNat_iff (n : Nat) : (Char.ofNat n).toNat = n ↔ n.isValidChar := by
  unfold Char.ofNat
  split
  · rename_i h; simp [Char.ofNatAux, Char.toNat, h]
  · rename_i h
    constructor
    · intro e
      have : n = 0 := by rw [← e]; rfl
      subst this; exact absurd (Or.inl (by decide)) h
    · intro h'; exact absurd h' h

/-! ## Checking a character code -/

/-- A bound on the cost of checking/reading a character code `n`. -/
def charCost (n : Nat) : Nat := 10 * (n + 1114113) * (n + 1114113) + 10

/-- Push a constant on `c`, compare with the top of `a`, pop `c`: the result is pushed on `f`. -/
theorem cmpC_core (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [a, c, t, u, g, f].Nodup)
    (S : Lists K) {la : List Nat} {n : Nat} (ha : S a = la ++ [n]) (k : Nat) :
    ∃ S₁ S₂, NRuns (npushC c k) S S₁ (k + 1) ∧ NRuns (cmpTop a c t u g f hat hcu) S₁ S₂ ((n + k + 1) * (2 * n + 6) + 20)
      ∧ NRuns (.prim (.pop c)) S₂ (S.set f (S f ++ [cmpRes n k])) 1 := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true] at hd'
  have hac : a ≠ c := hd'.1.1
  have hcf : c ≠ f := hd'.2.1.2.2.2
  have x₁ := nruns_pushC c S k
  have x₂ := nruns_cmpTop a c t u g f hat hcu hd (S.set c (S c ++ [k])) (li := la) (lj := S c) (a := n) (b := k)
    (by rw [Lists.set_ne _ _ hac]; exact ha) (by rw [Lists.set_same])
  have x₃ := nruns_pop c ((S.set c (S c ++ [k])).set f ((S.set c (S c ++ [k])) f ++ [cmpRes n k]))
    (l := S c) (v := k) (by rw [Lists.set_ne _ _ hcf, Lists.set_same])
  have e : ((S.set c (S c ++ [k])).set f ((S.set c (S c ++ [k])) f ++ [cmpRes n k])).set c (S c)
      = S.set f (S f ++ [cmpRes n k]) := by
    rw [Lists.set_ne _ _ (Ne.symm hcf)]
    funext x
    by_cases hx : x = c
    · subst hx; simp [Lists.set, hcf]
    · simp [Lists.set, hx]
  rw [e] at x₃
  exact ⟨_, _, x₁, x₂, x₃⟩

/-- The square that bounds the comparisons. -/
def chB (n : Nat) : Nat := (n + 1114113) * (n + 1114113)

/-- The cost of one comparison with a constant `k ≤ 1114112`. -/
theorem cmpC_cost (n k : Nat) (hk : k ≤ 1114112) : (n + k + 1) * (2 * n + 6) ≤ 2 * chB n := by
  have := Nat.mul_le_mul (show n + k + 1 ≤ n + 1114113 by omega) (show 2 * n + 6 ≤ 2 * (n + 1114113) by omega)
  rw [Nat.mul_left_comm] at this
  exact this

theorem charCost_eq (n : Nat) : charCost n = 10 * chB n + 10 := by
  simp only [charCost, chB, Nat.mul_assoc]

theorem chB_big (n : Nat) : 1114113 ≤ chB n :=
  Nat.le_trans (show 1114113 ≤ n + 1114113 by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem charCost_mono {m n : Nat} (h : m ≤ n) : charCost m ≤ charCost n := by
  rw [charCost_eq, charCost_eq]
  have := Nat.mul_le_mul (show m + 1114113 ≤ n + 1114113 by omega) (show m + 1114113 ≤ n + 1114113 by omega)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _

theorem cmpC_runs (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [a, c, t, u, g, f].Nodup)
    (S : Lists K) {la : List Nat} {n : Nat} (ha : S a = la ++ [n]) (k : Nat) (hk : k ≤ 1114112) (R : NProg K)
    {S' : Lists K} {T : Nat} (hR : NRuns R (S.set f (S f ++ [cmpRes n k])) S' T) :
    NRuns (.seq (npushC c k) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c)) R))) S S'
      (k + 1 + (2 * chB n + 20) + (1 + T)) := by
  obtain ⟨_, _, x₁, x₂, x₃⟩ := cmpC_core a c t u g f hat hcu hd S ha k
  have := cmpC_cost n k hk
  exact (x₁.seq (x₂.seq (x₃.seq hR))).mono (by omega)

theorem cmpC_halts (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [a, c, t, u, g, f].Nodup)
    (S : Lists K) {la : List Nat} {n : Nat} (ha : S a = la ++ [n]) (k : Nat) (hk : k ≤ 1114112) (R : NProg K)
    {b : Bool} {S' : Lists K} {T : Nat} (hR : NHalts R (S.set f (S f ++ [cmpRes n k])) b S' T) :
    NHalts (.seq (npushC c k) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c)) R))) S b S'
      (k + 1 + (2 * chB n + 20) + (1 + T)) := by
  obtain ⟨_, _, x₁, x₂, x₃⟩ := cmpC_core a c t u g f hat hcu hd S ha k
  have := cmpC_cost n k hk
  exact (x₁.seqH (x₂.seqH (x₃.seqH hR))).mono (by omega)

theorem cmpRes_lt {a b : Nat} (h : a < b) : cmpRes a b = 0 := by simp only [cmpRes, if_pos h]
theorem cmpRes_eq (a : Nat) : cmpRes a a = 1 := by simp [cmpRes]
theorem cmpRes_gt {a b : Nat} (h : b < a) : cmpRes a b = 2 := by
  simp only [cmpRes, if_neg (show ¬ a < b by omega), if_neg (show a ≠ b by omega)]
theorem cmpRes_ne {a b : Nat} (h : b ≤ a) : cmpRes a b ≠ 0 := by
  simp only [cmpRes, if_neg (show ¬ a < b by omega)]; split <;> simp

theorem eval_zero_ne (l : List Nat) {v : Nat} (h : v ≠ 0) : NTest.zero.eval (l ++ [v]) = false := by
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  exact eval_zero_succ l w

theorem nruns_popBack (f : Fin K) (S : Lists K) (v : Nat) :
    NRuns (.prim (.pop f)) (S.set f (S f ++ [v])) S 1 := by
  have := nruns_pop f (S.set f (S f ++ [v])) (l := S f) (v := v) (by rw [Lists.set_same])
  rwa [Lists.set_set_u, Lists.set_get_self] at this

theorem checkCharP_ok (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [a, c, t, u, g, f].Nodup)
    (S : Lists K) {la : List Nat} {n : Nat} (ha : S a = la ++ [n]) (hn : n.isValidChar) :
    NRuns (checkCharP a c t u g f hat hcu) S S (charCost n) := by
  have hb := chB_big n
  rw [charCost_eq]
  unfold Nat.isValidChar at hn
  unfold checkCharP
  by_cases h1 : n < 55296
  · have hr : cmpRes n 55296 = 0 := cmpRes_lt h1
    have x := cmpC_runs a c t u g f hat hcu hd S ha 55296 (by decide) _
      ((nruns_popBack f S (cmpRes n 55296)).iteT (i := f) (c := .zero) (q := .seq (.prim (.pop f)) (.seq (npushC c 57343)
        (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
        (caseTop f [.halt false, .halt false,
          .seq (npushC c 1114112) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
            (.ite f .zero (.prim (.pop f)) (.halt false))))] (.halt false))))))
        (by simp only [Lists.set_same, hr, eval_zero_zero]))
    exact x.mono (by omega)
  · have h2 : 57343 < n ∧ n < 1114112 := by omega
    have hr1 : cmpRes n 55296 = 2 := cmpRes_gt (by omega)
    have hr2 : cmpRes n 57343 = 2 := cmpRes_gt h2.1
    have hr3 : cmpRes n 1114112 = 0 := cmpRes_lt h2.2
    have xX := cmpC_runs a c t u g f hat hcu hd S ha 1114112 (Nat.le_refl _) _
      ((nruns_popBack f S (cmpRes n 1114112)).iteT (i := f) (c := .zero) (q := .halt false) (by simp only [Lists.set_same, hr3, eval_zero_zero]))
    have xC := caseTop_runs f [.halt false, .halt false,
          .seq (npushC c 1114112) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
            (.ite f .zero (.prim (.pop f)) (.halt false))))] (.halt false) 2 (by simp)
      (S.set f (S f ++ [cmpRes n 57343])) (S f) (by rw [Lists.set_same, hr2]) S _
      (by rw [Lists.set_set_u, Lists.set_get_self]; exact xX)
    have x2 := cmpC_runs a c t u g f hat hcu hd S ha 57343 (by decide) _ xC
    have x1 := cmpC_runs a c t u g f hat hcu hd S ha 55296 (by decide) _
      (((nruns_popBack f S (cmpRes n 55296)).seq x2).iteF (i := f) (c := .zero) (p := .prim (.pop f))
        (by rw [Lists.set_same, hr1]; simp))
    exact x1.mono (by omega)

theorem checkCharP_fail (a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [a, c, t, u, g, f].Nodup)
    (S : Lists K) {la : List Nat} {n : Nat} (ha : S a = la ++ [n]) (hn : ¬ n.isValidChar) :
    ∃ S', NHalts (checkCharP a c t u g f hat hcu) S false S' (charCost n) := by
  have hb := chB_big n
  rw [charCost_eq]
  unfold Nat.isValidChar at hn
  unfold checkCharP
  have hr1 : cmpRes n 55296 ≠ 0 := cmpRes_ne (by omega)
  let X : NProg K := .seq (npushC c 1114112) (.seq (cmpTop a c t u g f hat hcu) (.seq (.prim (.pop c))
    (.ite f .zero (.prim (.pop f)) (.halt false))))
  -- the second comparison, then the branch on its result
  have second : ∀ (S₂ : Lists K) (T : Nat),
      NHalts (caseTop f [.halt false, .halt false, X] (.halt false)) (S.set f (S f ++ [cmpRes n 57343])) false S₂ T →
      NHalts (checkCharP a c t u g f hat hcu) S false S₂
        (55296 + 1 + (2 * chB n + 20) + (1 + (1 + (57343 + 1 + (2 * chB n + 20) + (1 + T)) + 1))) := by
    intro S₂ T h
    have x2 := cmpC_halts a c t u g f hat hcu hd S ha 57343 (by decide) _ h
    exact cmpC_halts a c t u g f hat hcu hd S ha 55296 (by decide) _
      (((nruns_popBack f S (cmpRes n 55296)).seqH x2).iteF (i := f) (c := .zero) (p := .prim (.pop f))
        (by rw [Lists.set_same]; exact eval_zero_ne _ hr1))
  by_cases h1 : n < 57343
  · have hr2 : cmpRes n 57343 = 0 := cmpRes_lt h1
    have xC := caseTop_halts f [.halt false, .halt false, X] (.halt false) 0 (by simp)
      (S.set f (S f ++ [cmpRes n 57343])) (S f) (by rw [Lists.set_same, hr2]) false _ 1 (nhalts_halt false _)
    exact ⟨_, (second _ _ xC).mono (by omega)⟩
  by_cases h2 : n = 57343
  · have hr2 : cmpRes n 57343 = 1 := by rw [h2]; exact cmpRes_eq _
    have xC := caseTop_halts f [.halt false, .halt false, X] (.halt false) 1 (by simp)
      (S.set f (S f ++ [cmpRes n 57343])) (S f) (by rw [Lists.set_same, hr2]) false _ 1 (nhalts_halt false _)
    exact ⟨_, (second _ _ xC).mono (by omega)⟩
  · have hr2 : cmpRes n 57343 = 2 := cmpRes_gt (by omega)
    have hr3 : cmpRes n 1114112 ≠ 0 := cmpRes_ne (by omega)
    have xX := cmpC_halts a c t u g f hat hcu hd S ha 1114112 (Nat.le_refl _) _
      ((nhalts_halt false _).iteF (i := f) (c := .zero) (p := .prim (.pop f))
        (by rw [Lists.set_same]; exact eval_zero_ne _ hr3))
    have xC := caseTop_halts f [.halt false, .halt false, X] (.halt false) 2 (by simp)
      (S.set f (S f ++ [cmpRes n 57343])) (S f) (by rw [Lists.set_same, hr2]) false _ _
      (by rw [Lists.set_set_u, Lists.set_get_self]; exact xX)
    exact ⟨_, (second _ _ xC).mono (by omega)⟩

/-! ## Reading a character -/

theorem parseChar_some {l r : List Nat} {ch : Char} (hp : parseChar l = some (ch, r)) :
    ∃ n, parseNat l = some (n, r) ∧ n.isValidChar ∧ ch.toNat = n := by
  unfold parseChar at hp
  split at hp
  · rename_i n r' hn
    split at hp
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨n, hn, (toNat_ofNat_iff n).mp hc, hc⟩
    · cases hp
  · cases hp

theorem parseChar_none {l : List Nat} (hp : parseChar l = none) :
    parseNat l = none ∨ ∃ n r, parseNat l = some (n, r) ∧ ¬ n.isValidChar := by
  unfold parseChar at hp
  split at hp
  · rename_i n r' hn
    split at hp
    · cases hp
    · rename_i hc
      exact .inr ⟨n, r', hn, fun h => hc ((toNat_ofNat_iff n).mpr h)⟩
  · rename_i hn
    exact .inl hn

theorem parseCharP_ok (tk a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [tk, a, c, t, u, g, f].Nodup)
    (S : Lists K) {l r : List Nat} {ch : Char} (hS : S tk = l.reverse) (hp : parseChar l = some (ch, r)) :
    NRuns (parseCharP tk a c t u g f hat hcu) S ((S.set tk r.reverse).set a (S a ++ [ch.toNat]))
      (6 * l.length + 5 + charCost l.length) := by
  obtain ⟨n, hn, hv, hch⟩ := parseChar_some hp
  have hl := parseNat_sound hn
  have htk : tk ≠ a := by
    intro h; subst h; simp at hd
  have hd' : [a, c, t, u, g, f].Nodup := (List.nodup_cons.mp hd).2
  have x₁ := parseNatP_ok tk a htk S (n := n) (r := r) (by rw [hS, hl, List.reverse_append])
  have x₂ := checkCharP_ok a c t u g f hat hcu hd' ((S.set tk r.reverse).set a (S a ++ [n])) (la := S a) (n := n)
    (by rw [Lists.set_same]) hv
  rw [hch]
  have hlen : l.length = n + 1 + r.length := by rw [hl]; simp [length_serNat]
  have := charCost_mono (show n ≤ l.length by omega)
  exact (x₁.seq x₂).mono (by omega)

theorem parseCharP_fail (tk a c t u g f : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hd : [tk, a, c, t, u, g, f].Nodup)
    (S : Lists K) {l : List Nat} (hS : S tk = l.reverse) (hp : parseChar l = none) :
    ∃ S', NHalts (parseCharP tk a c t u g f hat hcu) S false S' (6 * l.length + 6 + charCost l.length) := by
  have htk : tk ≠ a := by
    intro h; subst h; simp at hd
  have hd' : [a, c, t, u, g, f].Nodup := (List.nodup_cons.mp hd).2
  rcases parseChar_none hp with hn | ⟨n, r, hn, hv⟩
  · obtain ⟨S', x⟩ := parseNatP_fail tk a htk S hS hn
    exact ⟨S', x.seq.mono (by omega)⟩
  · have hl := parseNat_sound hn
    have x₁ := parseNatP_ok tk a htk S (n := n) (r := r) (by rw [hS, hl, List.reverse_append])
    obtain ⟨S', x₂⟩ := checkCharP_fail a c t u g f hat hcu hd' ((S.set tk r.reverse).set a (S a ++ [n]))
      (la := S a) (n := n) (by rw [Lists.set_same]) hv
    have hlen : l.length = n + 1 + r.length := by rw [hl]; simp [length_serNat]
    have := charCost_mono (show n ≤ l.length by omega)
    exact ⟨S', (x₁.seqH x₂).mono (by omega)⟩

/-! ## Reading a string -/

/-- The sink of `parseStrP`: add `e` (0 or 1) to the code on `a` and move it to `o`. -/
def strSink (a o : Fin K) (hao : a ≠ o) (e : Bool) : NProg K :=
  .seq (cond e (.prim (.inc a)) (nskip a)) (nmv a o hao)

def strCost (L : Nat) : Nat := (L + 1) * (charCost L + 6 * L + 30)

theorem strSink_runs (a o : Fin K) (hao : a ≠ o) (e : Bool) (S : Lists K) {la : List Nat} {v : Nat}
    (ha : S a = la ++ [v]) :
    NRuns (strSink a o hao e) S ((S.set o (S o ++ [v + cond e 1 0])).set a la) 4 := by
  cases e with
  | false =>
    have x₁ := nruns_skip a S
    have x₂ := nruns_mv a o hao S ha
    exact (x₁.seq x₂).mono (by omega)
  | true =>
    have x₁ := nruns_inc a S ha
    have x₂ := nruns_mv a o hao (S.set a (la ++ [v + 1])) (l := la) (v := v + 1) (by rw [Lists.set_same])
    rw [Lists.set_ne _ _ (Ne.symm hao), Lists.set_comm (Ne.symm hao), Lists.set_set_u] at x₂
    rw [Lists.set_comm hao] at x₂
    exact (x₁.seq x₂).mono (by omega)

/-- One more round of a loop. -/
theorem NRuns.loopStep {i : Fin K} {c : NTest} {p : NProg K} {S S₁ S₂ : Lists K} {T₁ T₂ : Nat}
    (hc : c.eval (S i) = true) (h₁ : NRuns p S S₁ T₁) (h₂ : NRuns (.loop i c p) S₁ S₂ T₂) :
    NRuns (.loop i c p) S S₂ (T₁ + 1 + T₂) :=
  let ⟨t₁, ht₁, x₁⟩ := h₁; let ⟨t₂, ht₂, x₂⟩ := h₂; ⟨t₁ + 1 + t₂, by omega, .loopC trivial hc x₁ x₂⟩

/-- The loop stops inside its body. -/
theorem NHalts.loopIn {i : Fin K} {c : NTest} {p : NProg K} {S S₁ : Lists K} {b : Bool} {T : Nat}
    (hc : c.eval (S i) = true) (h : NHalts p S b S₁ T) : NHalts (.loop i c p) S b S₁ (T + 1) :=
  let ⟨t, ht, x⟩ := h; ⟨t + 1, by omega, .loopS trivial hc x⟩

/-- One more round of a loop followed by `q`, which stops. -/
theorem NHalts.loopStepSeq {i : Fin K} {c : NTest} {p q : NProg K} {S S₁ S₂ : Lists K} {b : Bool} {T₁ T₂ : Nat}
    (hc : c.eval (S i) = true) (h₁ : NRuns p S S₁ T₁) (h₂ : NHalts (.seq (.loop i c p) q) S₁ b S₂ T₂) :
    NHalts (.seq (.loop i c p) q) S b S₂ (T₁ + 1 + T₂) := by
  obtain ⟨t₁, ht₁, x₁⟩ := h₁
  obtain ⟨t₂, ht₂, x₂⟩ := h₂
  cases x₂ with
  | seqC y₁ y₂ => exact ⟨_, by omega, .seqC (.loopC trivial hc x₁ y₁) y₂⟩
  | seqS y₁ => exact ⟨_, by omega, .seqS (.loopC trivial hc x₁ y₁)⟩

theorem ne_of_nodup8 {tk a c t u g f o : Fin K} (hd : [tk, a, c, t, u, g, f, o].Nodup) :
    tk ≠ a ∧ tk ≠ o ∧ [tk, a, c, t, u, g, f].Nodup := by
  refine ⟨?_, ?_, hd.sublist (List.sublist_append_left [tk, a, c, t, u, g, f] [o])⟩
  · intro h; subst h; simp at hd
  · intro h; subst h; simp at hd

theorem parseChar_len {l r : List Nat} {ch : Char} (hp : parseChar l = some (ch, r)) :
    l.length = ch.toNat + 1 + r.length := by
  obtain ⟨n, hn, _, hch⟩ := parseChar_some hp
  rw [parseNat_sound hn, hch]; simp [length_serNat]

/-- The loop body on the token `1` followed by a character. -/
theorem strBody_char (tk a c t u g f o : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hao : a ≠ o) (e : Bool)
    (hd : [tk, a, c, t, u, g, f, o].Nodup) (S : Lists K) {r' r₁ : List Nat} {ch : Char}
    (hS : S tk = r'.reverse ++ [1]) (hp : parseChar r' = some (ch, r₁)) :
    NRuns (.seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk))
        (.seq (parseCharP tk a c t u g f hat hcu) (strSink a o hao e))) (.halt false))) S
      ((S.set tk r₁.reverse).set o (S o ++ [ch.toNat + cond e 1 0])) (6 * r'.length + 14 + charCost r'.length) := by
  obtain ⟨htka, htko, hd7⟩ := ne_of_nodup8 hd
  have x₁ := nruns_dec tk S hS
  have x₂ := nruns_pop tk (S.set tk (r'.reverse ++ [1 - 1])) (l := r'.reverse) (v := 1 - 1) (by rw [Lists.set_same])
  rw [Lists.set_set_u] at x₂
  have x₃ := parseCharP_ok tk a c t u g f hat hcu hd7 (S.set tk r'.reverse) (by rw [Lists.set_same]) hp
  rw [Lists.set_set_u, Lists.set_ne _ _ (Ne.symm htka)] at x₃
  have x₄ := strSink_runs a o hao e ((S.set tk r₁.reverse).set a (S a ++ [ch.toNat])) (la := S a) (v := ch.toNat)
    (by rw [Lists.set_same])
  have e₄ : ((((S.set tk r₁.reverse).set a (S a ++ [ch.toNat])).set o
      (((S.set tk r₁.reverse).set a (S a ++ [ch.toNat])) o ++ [ch.toNat + cond e 1 0])).set a (S a))
      = (S.set tk r₁.reverse).set o (S o ++ [ch.toNat + cond e 1 0]) := by
    funext x
    by_cases hx : x = a
    · subst hx; simp [Lists.set, hao, Ne.symm htka]
    by_cases hy : x = o
    · subst hy; simp [Lists.set, hx, Ne.symm htko]
    simp [Lists.set, hx, hy]
  rw [e₄] at x₄
  exact (x₁.seq ((x₂.seq (x₃.seq x₄)).iteT (by simp only [Lists.set_same, Nat.sub_self, eval_zero_zero]))).mono
    (by omega)

/-- The cost of the loop of `parseStrP`. -/
def strLoopCost (L : Nat) : Nat := (L + 1) * (charCost L + 6 * L + 20)

theorem strLoopCost_step {L' L₁ : Nat} (h : L₁ < L') :
    6 * L' + 14 + charCost L' + 1 + strLoopCost L₁ ≤ strLoopCost (L' + 1) := by
  have hm := charCost_mono (show L' ≤ L' + 1 by omega)
  have hm₁ := charCost_mono (show L₁ ≤ L' + 1 by omega)
  have hp := Nat.mul_le_mul (show L₁ + 1 ≤ L' by omega)
    (show charCost L₁ + 6 * L₁ + 20 ≤ charCost (L' + 1) + 6 * (L' + 1) + 20 by omega)
  unfold strLoopCost
  have e : (L' + 1 + 1) * (charCost (L' + 1) + 6 * (L' + 1) + 20) = L' * (charCost (L' + 1) + 6 * (L' + 1) + 20) +
      (charCost (L' + 1) + 6 * (L' + 1) + 20) + (charCost (L' + 1) + 6 * (L' + 1) + 20) := by
    simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem one_le_strLoopCost (L : Nat) : 1 ≤ strLoopCost L :=
  Nat.le_trans (show 1 ≤ charCost L + 6 * L + 20 by omega) (Nat.le_mul_of_pos_left _ (by omega))

theorem strLoopCost_le (L : Nat) : strLoopCost L + 2 ≤ strCost L := by
  unfold strLoopCost strCost
  have : (L + 1) * (charCost L + 6 * L + 30) = (L + 1) * (charCost L + 6 * L + 20) + (L + 1) * 10 := by
    rw [← Nat.mul_add]
  have h2 : 10 ≤ (L + 1) * 10 := Nat.le_mul_of_pos_left 10 (by omega)
  omega

theorem strLoop_ok (tk a c t u g f o : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hao : a ≠ o) (e : Bool)
    (hd : [tk, a, c, t, u, g, f, o].Nodup) :
    ∀ (fuel : Nat) (S : Lists K) {l r : List Nat} {cs : List Char}, S tk = l.reverse → parseStr fuel l = some (cs, r) →
    NRuns (.loop tk .pos (.seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk))
        (.seq (parseCharP tk a c t u g f hat hcu) (strSink a o hao e))) (.halt false)))) S
      ((S.set tk (r.reverse ++ [0])).set o (S o ++ cs.map (fun ch => ch.toNat + cond e 1 0)))
      (strLoopCost l.length) := by
  obtain ⟨htka, htko, hd7⟩ := ne_of_nodup8 hd
  intro fuel
  induction fuel with
  | zero =>
    intro S l r cs hS hp
    match l, hp with
    | 0 :: r', hp =>
      simp only [parseStr, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have x := nruns_loop_exit (i := tk) (c := .pos)
        (p := .seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk))
          (.seq (parseCharP tk a c t u g f hat hcu) (strSink a o hao e))) (.halt false))) (S := S)
        (by rw [hS]; simp)
      rw [List.map_nil, List.append_nil, ← List.reverse_cons, ← hS, Lists.set_get_self, Lists.set_get_self]
      exact x.mono (one_le_strLoopCost _)
    | 1 :: _, hp => simp [parseStr] at hp
    | [], hp => simp [parseStr] at hp
    | (_ + 2) :: _, hp => simp [parseStr] at hp
  | succ fu ih =>
    intro S l r cs hS hp
    match l, hp with
    | 0 :: r', hp =>
      simp only [parseStr, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have x := nruns_loop_exit (i := tk) (c := .pos)
        (p := .seq (.prim (.dec tk)) (.ite tk .zero (.seq (.prim (.pop tk))
          (.seq (parseCharP tk a c t u g f hat hcu) (strSink a o hao e))) (.halt false))) (S := S)
        (by rw [hS]; simp)
      rw [List.map_nil, List.append_nil, ← List.reverse_cons, ← hS, Lists.set_get_self, Lists.set_get_self]
      exact x.mono (one_le_strLoopCost _)
    | 1 :: r', hp =>
      simp only [parseStr] at hp
      split at hp
      · rename_i ch r₁ hc
        simp only [Option.map_eq_some_iff] at hp
        obtain ⟨⟨p, r₂⟩, hs, he⟩ := hp
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have hS' : S tk = r'.reverse ++ [1] := by rw [hS]; simp
        have x₁ := strBody_char tk a c t u g f o hat hcu hao e hd S hS' hc
        have x₂ := ih ((S.set tk r₁.reverse).set o (S o ++ [ch.toNat + cond e 1 0])) (l := r₁)
          (by rw [Lists.set_ne _ _ htko, Lists.set_same]) hs
        have e₂ : ((((S.set tk r₁.reverse).set o (S o ++ [ch.toNat + cond e 1 0])).set tk (r₂.reverse ++ [0])).set o
            (((S.set tk r₁.reverse).set o (S o ++ [ch.toNat + cond e 1 0])) o ++
              p.map (fun ch => ch.toNat + cond e 1 0)))
            = (S.set tk (r₂.reverse ++ [0])).set o (S o ++ (ch :: p).map (fun ch => ch.toNat + cond e 1 0)) := by
          funext x
          by_cases hx : x = o
          · subst hx; simp [Lists.set]
          by_cases hy : x = tk
          · subst hy; simp [Lists.set, hx]
          simp [Lists.set, hx, hy]
        rw [e₂] at x₂
        have hlen := parseChar_len hc
        have := strLoopCost_step (show r₁.length < r'.length by omega)
        exact (NRuns.loopStep (by rw [hS']; exact eval_pos_succ _ 0) x₁ x₂).mono (by simp; omega)
      · cases hp
    | [], hp => simp [parseStr] at hp
    | (_ + 2) :: _, hp => simp [parseStr] at hp

theorem parseStrP_ok (tk a c t u g f o : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hao : a ≠ o) (e : Bool)
    (hd : [tk, a, c, t, u, g, f, o].Nodup) (S : Lists K) {fuel : Nat} {l r : List Nat} {cs : List Char}
    (hS : S tk = l.reverse) (hp : parseStr fuel l = some (cs, r)) :
    NRuns (parseStrP tk a c t u g f hat hcu (strSink a o hao e)) S
      ((S.set tk r.reverse).set o (S o ++ cs.map (fun ch => ch.toNat + cond e 1 0))) (strCost l.length) := by
  obtain ⟨htka, htko, hd7⟩ := ne_of_nodup8 hd
  have x₁ := strLoop_ok tk a c t u g f o hat hcu hao e hd fuel S hS hp
  let Y := S o ++ cs.map (fun ch => ch.toNat + cond e 1 0)
  have hF : ((S.set tk (r.reverse ++ [0])).set o Y) tk = r.reverse ++ [0] := by
    rw [Lists.set_ne _ _ htko, Lists.set_same]
  have x₂ := nruns_pop tk ((S.set tk (r.reverse ++ [0])).set o Y) hF
  rw [Lists.set_comm (Ne.symm htko), Lists.set_set_u] at x₂
  have := strLoopCost_le l.length
  exact (x₁.seq (x₂.iteT (q := .halt false) (by rw [hF]; exact eval_zero_zero _))).mono (by omega)

theorem strLoopCost_ge (L : Nat) : charCost L + 6 * L + 20 ≤ strLoopCost L :=
  Nat.le_mul_of_pos_left _ (by omega)

theorem strP_fail (tk a c t u g f o : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hao : a ≠ o) (e : Bool)
    (hd : [tk, a, c, t, u, g, f, o].Nodup) :
    ∀ (fuel : Nat) (S : Lists K) {l : List Nat}, S tk = l.reverse → l.length ≤ fuel → parseStr fuel l = none →
    ∃ S', NHalts (parseStrP tk a c t u g f hat hcu (strSink a o hao e)) S false S' (strLoopCost l.length + 2) := by
  obtain ⟨htka, htko, hd7⟩ := ne_of_nodup8 hd
  intro fuel
  induction fuel with
  | zero =>
    intro S l hS hl hp
    match l, hp with
    | [], _ =>
      unfold parseStrP
      exact ⟨S, ((nruns_loop_exit (by rw [hS]; rfl)).seqH ((nhalts_halt false S).iteF (by rw [hS]; rfl))).mono
        (by simp only [List.length_nil]; have := one_le_strLoopCost 0; omega)⟩
    | _ :: _, _ => simp at hl
  | succ fu ih =>
    intro S l hS hl hp
    match l, hp with
    | [], _ =>
      unfold parseStrP
      exact ⟨S, ((nruns_loop_exit (by rw [hS]; rfl)).seqH ((nhalts_halt false S).iteF (by rw [hS]; rfl))).mono
        (by simp only [List.length_nil]; have := one_le_strLoopCost 0; omega)⟩
    | 0 :: _, hp => simp [parseStr] at hp
    | (k + 2) :: r, _ =>
      have hS' : S tk = r.reverse ++ [k + 2] := by rw [hS]; simp
      have x₁ := nruns_dec tk S hS'
      have body := x₁.seqH ((nhalts_halt false _).iteF (p := .seq (.prim (.pop tk))
        (.seq (parseCharP tk a c t u g f hat hcu) (strSink a o hao e)))
        (i := tk) (c := .zero) (by simp only [Lists.set_same]; exact eval_zero_ne _ (by omega)))
      have lp := NHalts.loopIn (i := tk) (c := .pos) (by rw [hS']; exact eval_pos_succ _ (k + 1)) body
      have := strLoopCost_ge ((k + 2) :: r).length
      unfold parseStrP
      refine ⟨_, lp.seq.mono ?_⟩
      omega
    | 1 :: r', hp =>
      have hS' : S tk = r'.reverse ++ [1] := by rw [hS]; simp
      have hlen' : r'.length ≤ fu := by simp at hl; omega
      simp only [parseStr] at hp
      split at hp
      · rename_i ch r₁ hc
        simp only [Option.map_eq_none_iff] at hp
        have hlen := parseChar_len hc
        have x₁ := strBody_char tk a c t u g f o hat hcu hao e hd S hS' hc
        obtain ⟨S', x₂⟩ := ih ((S.set tk r₁.reverse).set o (S o ++ [ch.toNat + cond e 1 0])) (l := r₁)
          (by rw [Lists.set_ne _ _ htko, Lists.set_same]) (by omega) hp
        have := strLoopCost_step (show r₁.length < r'.length by omega)
        unfold parseStrP at x₂ ⊢
        exact ⟨S', (NHalts.loopStepSeq (by rw [hS']; exact eval_pos_succ _ 0) x₁ x₂).mono (by simp; omega)⟩
      · rename_i hc
        have x₁ := nruns_dec tk S hS'
        have x₂ := nruns_pop tk (S.set tk (r'.reverse ++ [1 - 1])) (l := r'.reverse) (v := 1 - 1)
          (by rw [Lists.set_same])
        rw [Lists.set_set_u] at x₂
        obtain ⟨S', x₃⟩ := parseCharP_fail tk a c t u g f hat hcu hd7 (S.set tk r'.reverse) (by rw [Lists.set_same]) hc
        have body := x₁.seqH ((x₂.seqH (x₃.seq (q := strSink a o hao e))).iteT (q := .halt false)
          (i := tk) (c := .zero) (by simp only [Lists.set_same, Nat.sub_self, eval_zero_zero]))
        have lp := NHalts.loopIn (i := tk) (c := .pos) (by rw [hS']; exact eval_pos_succ _ 0) body
        have := strLoopCost_ge (1 :: r').length
        have := charCost_mono (show r'.length ≤ (1 :: r').length by simp)
        unfold parseStrP
        refine ⟨_, lp.seq.mono ?_⟩
        simp at *; omega

theorem parseStrP_fail (tk a c t u g f o : Fin K) (hat : a ≠ t) (hcu : c ≠ u) (hao : a ≠ o) (e : Bool)
    (hd : [tk, a, c, t, u, g, f, o].Nodup) (S : Lists K) {fuel : Nat} {l : List Nat}
    (hS : S tk = l.reverse) (hfuel : l.length ≤ fuel) (hp : parseStr fuel l = none) :
    ∃ S', NHalts (parseStrP tk a c t u g f hat hcu (strSink a o hao e)) S false S' (strCost l.length) := by
  obtain ⟨S', x⟩ := strP_fail tk a c t u g f o hat hcu hao e hd fuel S hS hfuel hp
  exact ⟨S', x.mono (strLoopCost_le _)⟩

end Shallot.MacroPeg.Mach
