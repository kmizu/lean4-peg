import PalPeg.ProgLangPersist
import PalPeg.ProgLangSum

/-! Action safety under arbitrary observations between source steps.
The guarded-action rule certifies a wait followed by an action without
requiring an unsafe standalone action to be safe on every observation. -/
set_option autoImplicit false

namespace PalPeg.ProgLangGuarded
open PalPeg.ProgLang

variable {A C B D : Type}

def AllActs (P : A → Prop) : Prog A C → Prop
  | .skip => True
  | .act a => P a
  | .seq p q | .ite _ p q => AllActs P p ∧ AllActs P q
  | .loop _ a b => P a ∧ AllActs P b

theorem all_of {P : A → Prop} (h : ∀ a, P a) (p : Prog A C) : AllActs P p := by
  induction p with
  | skip => trivial
  | act a => exact h a
  | seq p q hp hq => exact ⟨hp, hq⟩
  | ite c p q hp hq => exact ⟨hp, hq⟩
  | loop c a b hb => exact ⟨h a, hb⟩

theorem all_mono {P Q : A → Prop} (h : ∀ a, P a → Q a) {p : Prog A C}
    (hp : AllActs P p) : AllActs Q p := by
  induction p with
  | skip => trivial
  | act a => exact h a hp
  | seq p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | ite c p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | loop c a b ihb => exact ⟨h a hp.1, ihb hp.2⟩

theorem all_map (P : B → Prop) (fa : A → B) (fc : C → D) (p : Prog A C) :
    AllActs P (p.map fa fc) ↔ AllActs (P ∘ fa) p := by
  induction p <;> simp_all [AllActs, Prog.map]

def Bounded (G : (C → Bool) → A → Prop) : ℕ → Stack A C → Prop
  | 0, _ => True
  | N + 1, s => ∀ ev, (∀ a, (stepStack ev s).2 = some a → G ev a) ∧
      Bounded G N (stepStack ev s).1

def Certified (G : (C → Bool) → A → Prop) (p : Prog A C) : Prop :=
  ∀ N s, Bounded G N s → Bounded G N (p :: s)

def Invariant (G : (C → Bool) → A → Prop) (s : Stack A C) : Prop := ∀ N, Bounded G N s

variable {G : (C → Bool) → A → Prop}

theorem bounded_down : ∀ N s, Bounded G (N + 1) s → Bounded G N s := by
  intro N
  induction N with
  | zero => intro s h; trivial
  | succ N ih =>
    intro s h ev
    exact ⟨(h ev).1, ih _ (h ev).2⟩

theorem bounded_nil : ∀ N, Bounded G N [] := by
  intro N
  induction N with
  | zero => trivial
  | succ N ih =>
    intro ev
    rw [stepStack_nil]
    refine ⟨?_, ih⟩
    intro a ha
    cases ha

theorem bounded_of_steps {s t : Stack A C} (he : ∀ ev, stepStack ev s = stepStack ev t)
    (N : ℕ) (h : Bounded G N t) : Bounded G N s := by
  cases N with
  | zero => trivial
  | succ N =>
    intro ev
    simpa only [he ev] using h ev

theorem Certified.skip : Certified G .skip := by
  intro N s hs
  exact bounded_of_steps (fun ev => stepStack_skip ev s) N hs

theorem Certified.act {a : A} (h : ∀ ev, G ev a) : Certified G (.act a) := by
  intro N s hs
  cases N with
  | zero => trivial
  | succ N =>
    intro ev
    rw [stepStack_act]
    refine ⟨?_, bounded_down N s hs⟩
    intro a' ha
    cases Option.some.inj ha
    exact h ev

theorem Certified.seq {p q : Prog A C} (hp : Certified G p) (hq : Certified G q) :
    Certified G (.seq p q) := by
  intro N s hs
  exact bounded_of_steps (fun ev => stepStack_seq ev p q s) N (hp N (q :: s) (hq N s hs))

theorem Certified.ite {c : C} {p q : Prog A C} (hp : Certified G p) (hq : Certified G q) :
    Certified G (.ite c p q) := by
  intro N s hs
  cases N with
  | zero => trivial
  | succ N =>
    intro ev
    by_cases he : ev c = true
    · simpa only [stepStack_ite, he, if_true] using hp (N + 1) s hs ev
    · simpa only [stepStack_ite, if_neg he] using hq (N + 1) s hs ev

theorem Certified.loop {c : C} {a : A} {b : Prog A C}
    (ha : ∀ ev, G ev a) (hb : Certified G b) : Certified G (.loop c a b) := by
  intro N
  induction N with
  | zero => intro s hs; trivial
  | succ N ih =>
    intro s hs ev
    by_cases he : ev c = true
    · simp only [stepStack_loop, he, if_true]
      refine ⟨?_, hb N (.loop c a b :: s) (ih s (bounded_down N s hs))⟩
      intro a' ha'
      cases Option.some.inj ha'
      exact ha ev
    · simpa only [stepStack_loop, if_neg he] using hs ev

/-- The action is selected in the same source step that observes the
wait condition to be false. Suspensions retain the wait in the continuation. -/
theorem Certified.guarded_then {c : C} {waitA a : A} {q : Prog A C}
    (hw : ∀ ev, G ev waitA) (ha : ∀ ev, ev c = false → G ev a)
    (hq : Certified G q) :
    Certified G (.seq (.loop c waitA .skip) (.seq (.act a) q)) := by
  intro N
  induction N with
  | zero => intro s hs; trivial
  | succ N ih =>
    intro s hs ev
    by_cases he : ev c = true
    · simp only [stepStack_seq, stepStack_loop, he, if_true]
      refine ⟨?_, ?_⟩
      · intro a' ha'
        cases Option.some.inj ha'
        exact hw ev
      · apply bounded_of_steps (t := .seq (.loop c waitA .skip) (.seq (.act a) q) :: s)
          (fun ev => by rw [stepStack_skip, stepStack_seq]) N
        exact ih s (bounded_down N s hs)
    · have hef : ev c = false := Bool.eq_false_iff.mpr he
      simp only [stepStack_seq, stepStack_loop, if_neg he, stepStack_act]
      refine ⟨?_, hq N s (bounded_down N s hs)⟩
      intro a' ha'
      cases Option.some.inj ha'
      exact ha ev hef

theorem Certified.of_all {p : Prog A C} (h : AllActs (fun a => ∀ ev, G ev a) p) :
    Certified G p := by
  induction p with
  | skip => exact Certified.skip
  | act a => exact Certified.act h
  | seq p q hp hq => exact (hp h.1).seq (hq h.2)
  | ite c p q hp hq => exact (hp h.1).ite (hq h.2)
  | loop c a b hb => exact Certified.loop h.1 (hb h.2)

theorem Invariant.of_certified {p : Prog A C} (h : Certified G p) : Invariant G [p] :=
  fun N => h N [] (bounded_nil N)

theorem Invariant.step {s : Stack A C} (h : Invariant G s) (ev : C → Bool) :
    Invariant G (stepStack ev s).1 := fun N => (h (N + 1) ev).2

theorem Invariant.selected {s : Stack A C} (h : Invariant G s) (ev : C → Bool)
    {a : A} (ha : (stepStack ev s).2 = some a) : G ev a := (h 1 ev).1 a ha

/-- info: 'PalPeg.ProgLangGuarded.Certified.guarded_then' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Certified.guarded_then

end PalPeg.ProgLangGuarded
