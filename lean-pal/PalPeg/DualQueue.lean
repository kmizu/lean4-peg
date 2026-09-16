import PalPeg.TextFeedInit

/-! Two independent closed finite-mode FIFOs receive the same arrival.
The pair will feed the scanner and its prefix verifier, respectively. -/
set_option autoImplicit false

namespace PalPeg.DualQueue
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueControl PalPeg.RTQueueClosed PalPeg.TextFeedControl PalPeg.TextFeedInit

variable {k : ℕ} {Terminal : Type}

abbrev Act (k : ℕ) := (ActQ k ⊕ Mode) ⊕ (ActQ k ⊕ Mode)
abbrev Cond (k : ℕ) := (CondQ k ⊕ Mode) ⊕ (CondQ k ⊕ Mode)
abbrev PP (k : ℕ) := Prog (Act k) (Cond k)

noncomputable def interp (e : Env k) := Interp.sum (IC Terminal e.code) (IC Terminal e.code)

def tapes (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) : Fin 22 → STape (Fin k) :=
  Fin.append (RTQueueControl.tapes e.code qt₁ m₁) (RTQueueControl.tapes e.code qt₂ m₂)

def blankOne (blank : Fin k) : Fin 11 → STape (Fin k) :=
  Fin.append (blankBundle blank 10) (blankBundle blank 1)

def blankPair (blank : Fin k) : Fin 22 → STape (Fin k) := Fin.append (blankOne blank) (blankOne blank)

noncomputable def one (blank mark a : Fin k) (first : Bool) : CP k :=
  if first then .seq (queueBoot blank mark) (enqueue blank mark a) else enqueue blank mark a

noncomputable def both (blank mark a : Fin k) (first : Bool) : PP k :=
  .seq ((one blank mark a first).map Sum.inl Sum.inl) ((one blank mark a first).map Sum.inr Sum.inr)

theorem first_one {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (a : Fin k) (ha : a ≠ e.mark) :
    ∃ tr qt m, Exec (IC Terminal e.code) e.blank (one e.blank e.mark a true) (blankOne e.blank) tr ∧
      tr.length ≤ 46 ∧ applyTrace e.blank (blankOne e.blank) tr = RTQueueControl.tapes e.code qt m ∧
      Ready e.blank e.mark qt m (snoc empty a) := by
  obtain ⟨b, hb, hbn, hbt⟩ := queueBoot_exec (Terminal := Terminal) e
  obtain ⟨n, qt, m, hn, ⟨tr, he, hlen, ht⟩, hr⟩ := enqueue_ready (Terminal := Terminal)
    hc hmb (initial_ready e.blank e.mark) ha
  refine ⟨b ++ tr, qt, m, exec_seq hb (hbt ▸ he), ?_, ?_, hr⟩
  · simp only [List.length_append, hbn, hlen]
    omega
  · rw [applyTrace_append, blankOne, hbt, ht]

theorem pair_exec {e : Env k} {p₁ p₂ : CP k}
    {T₁ T₂ U₁ U₂ : Fin 11 → STape (Fin k)} {a b : List (Fin 11 → Fin k × Move)}
    (ha : Exec (IC Terminal e.code) e.blank p₁ T₁ a)
    (hb : Exec (IC Terminal e.code) e.blank p₂ T₂ b)
    (hta : applyTrace e.blank T₁ a = U₁) (htb : applyTrace e.blank T₂ b = U₂) :
    ∃ tr, Exec (interp (Terminal := Terminal) e) e.blank
      (.seq (p₁.map Sum.inl Sum.inl) (p₂.map Sum.inr Sum.inr)) (Fin.append T₁ T₂) tr ∧
      tr.length = a.length + b.length ∧ applyTrace e.blank (Fin.append T₁ T₂) tr = Fin.append U₁ U₂ := by
  have he := exec_sum_seq ha hb
  have hmid := applyTrace_extend (Fin.castAddEmb 11) e.blank (Fin.append T₁ T₂) a T₁
  simp only [extend_castAdd_append] at hmid
  have hlast := applyTrace_extend (Fin.natAddEmb 11) e.blank
    (Fin.append (applyTrace e.blank T₁ a) T₂) b T₂
  simp only [extend_natAdd_append] at hlast
  refine ⟨_, he, by simp only [List.length_append, List.length_map], ?_⟩
  rw [applyTrace_append, hmid, hlast, hta, htb]

theorem enqueue_both {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt₁ qt₂ : QT k} {m₁ m₂ : Mode} {q₁ q₂ : Queue (Fin k)}
    (h₁ : Ready e.blank e.mark qt₁ m₁ q₁) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂)
    (a : Fin k) (ha : a ≠ e.mark) :
    ∃ tr qt₁' m₁' qt₂' m₂', Exec (interp (Terminal := Terminal) e) e.blank
      (both e.blank e.mark a false) (tapes e qt₁ m₁ qt₂ m₂) tr ∧ tr.length ≤ 68 ∧
      applyTrace e.blank (tapes e qt₁ m₁ qt₂ m₂) tr = tapes e qt₁' m₁' qt₂' m₂' ∧
      Ready e.blank e.mark qt₁' m₁' (snoc q₁ a) ∧ Ready e.blank e.mark qt₂' m₂' (snoc q₂ a) := by
  obtain ⟨n₁, qt₁', m₁', hn₁, ⟨a₁, he₁, hl₁, ht₁⟩, hr₁⟩ := enqueue_ready (Terminal := Terminal) hc hmb h₁ ha
  obtain ⟨n₂, qt₂', m₂', hn₂, ⟨a₂, he₂, hl₂, ht₂⟩, hr₂⟩ := enqueue_ready (Terminal := Terminal) hc hmb h₂ ha
  obtain ⟨tr, he, hn, ht⟩ := pair_exec he₁ he₂ ht₁ ht₂
  exact ⟨tr, qt₁', m₁', qt₂', m₂', he, by omega, ht, hr₁, hr₂⟩

theorem first_both {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (a : Fin k) (ha : a ≠ e.mark) :
    ∃ tr qt₁ m₁ qt₂ m₂, Exec (interp (Terminal := Terminal) e) e.blank
      (both e.blank e.mark a true) (blankPair e.blank) tr ∧ tr.length ≤ 92 ∧
      applyTrace e.blank (blankPair e.blank) tr = tapes e qt₁ m₁ qt₂ m₂ ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty a) ∧ Ready e.blank e.mark qt₂ m₂ (snoc empty a) := by
  obtain ⟨a₁, qt₁, m₁, he₁, hl₁, ht₁, hr₁⟩ := first_one (Terminal := Terminal) hc hmb a ha
  obtain ⟨a₂, qt₂, m₂, he₂, hl₂, ht₂, hr₂⟩ := first_one (Terminal := Terminal) hc hmb a ha
  obtain ⟨tr, he, hn, ht⟩ := pair_exec he₁ he₂ ht₁ ht₂
  exact ⟨tr, qt₁, m₁, qt₂, m₂, he, by omega, ht, hr₁, hr₂⟩

/-- info: 'PalPeg.DualQueue.first_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_both

end PalPeg.DualQueue
