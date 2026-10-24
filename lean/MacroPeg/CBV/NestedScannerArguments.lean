import MacroPeg.CBV.PrefixFamilyFusion

/-! Operational factorization of independently evaluated greedy scanners.
The symbol sets are static; their captured words have no length bound. -/
namespace Shallot.MacroPeg.CBV.NestedScannerArguments
open Shallot (beqChar)

def accepts : List Char → Char → Bool
  | [], _ => false
  | a::A, c => beqChar a c || accepts A c

def choice : List Char → MExp
  | [] => MExp.failAlways
  | a::A => .alt (.chr a) (choice A)

def scan (A : List Char) : MExp := .star (choice A)

theorem choice_firstOrder (A : List Char) : (choice A).FirstOrder := by
  induction A <;> simp_all [choice,MExp.FirstOrder,MExp.failAlways]

theorem scan_firstOrder (A : List Char) : (scan A).FirstOrder := choice_firstOrder A

theorem choice_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A : List Char) (p : Nat) :
    evV g x s T E (choice A) p =
      match sfx x p with
      | [] => some none
      | c::rest => if accepts A c then some (some rest.length) else some none := by
  induction A with
  | nil => cases sfx x p <;> simp [choice,evV,MExp.failAlways,accepts]
  | cons a A ih =>
    simp only [choice,evV]
    cases hs : sfx x p with
    | nil => simpa only [hs] using ih
    | cons c rest =>
      rw [hs] at ih
      by_cases ha : beqChar a c = true <;> simp_all [accepts]

theorem scan_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (A : List Char) :
    ∀ p, p ≤ x.length → evV g x s T E (scan A) p =
      some (some ((sfx x p).dropWhile (accepts A)).length) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    rw [scan,evV_star]
    cases hs : sfx x p with
    | nil =>
      rw [evStar_fail (by rw [choice_eval,hs])]
      have hl := length_sfx x hp
      rw [hs] at hl
      simp only [List.length_nil] at hl
      simp [← hl]
    | cons c rest =>
      have hlen : rest.length + 1 = p := by
        simpa only [hs,List.length_cons] using (length_sfx x hp)
      have hrest : sfx x rest.length = rest := by
        have hh : ∃ pre, x = pre ++ rest :=
          suffix_trans (sfx_is_suffix x p) ⟨[c],hs⟩
        exact sfx_suffix hh.choose_spec
      by_cases ha : accepts A c = true
      · rw [evStar_ok (j := rest.length) (by rw [choice_eval,hs]; simp [ha]) (by omega)]
        have hi := ih rest.length (by omega) (by omega)
        change evStar (fun q => evV g x s T E (choice A) q) rest.length = _
        change evV g x s T E (scan A) rest.length = _
        rw [hi]
        simp [ha,hrest]
      · rw [evStar_fail (by rw [choice_eval,hs]; simp [ha])]
        simp [ha,hlen]

def Included (A B : List Char) : Prop := ∀ c, accepts A c = true → accepts B c = true

theorem accepts_append (A B : List Char) (c : Char) :
    accepts (A++B) c = (accepts A c || accepts B c) := by
  induction A <;> simp_all [accepts,Bool.or_assoc]

theorem included_prefix (A B : List Char) : Included A (A++B) := by
  intro c hc
  simp [accepts_append,hc]

theorem dropWhile_absorb (A B : List Char) (h : Included A B) (x : List Char) :
    (x.dropWhile (accepts A)).dropWhile (accepts B) = x.dropWhile (accepts B) := by
  induction x with
  | nil => rfl
  | cons c x ih =>
    by_cases ha : accepts A c = true
    · simp [ha,h c ha,ih]
    · simp [List.dropWhile_cons,ha]

/-- A wider scanner resumes at the actual end of the earlier scanner.
No captured value, endpoint, or finite-state advice is supplied to it. -/
theorem scan_absorb (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (A B : List Char) (h : Included A B) (p : Nat) (hp : p ≤ x.length) :
    evV g x s T E (.seq (scan A) (scan B)) p = evV g x s T E (scan B) p := by
  rw [evV_seq_ok (scan_eval g x s T E A p hp)]
  have hs : ∃ pre, x = pre ++ (sfx x p).dropWhile (accepts A) :=
    suffix_trans (sfx_is_suffix x p) ⟨_,(List.takeWhile_append_dropWhile (p := accepts A) (l := sfx x p)).symm⟩
  have hq : ((sfx x p).dropWhile (accepts A)).length ≤ x.length := by
    obtain ⟨pre,he⟩ := hs
    have hl := congrArg List.length he
    simp only [List.length_append] at hl
    omega
  rw [scan_eval _ _ _ _ _ B _ hq,scan_eval _ _ _ _ _ B p hp,
    sfx_suffix hs.choose_spec,dropWhile_absorb A B h]

def Equivalent (a b : MExp) : Prop :=
  ∀ g x s T E p, p ≤ x.length → evV g x s T E a p = evV g x s T E b p

inductive ArgsEquivalent : List MExp → List MExp → Prop where
  | nil : ArgsEquivalent [] []
  | cons {a b as bs} : Equivalent a b → ArgsEquivalent as bs → ArgsEquivalent (a::as) (b::bs)

theorem parsers_collapse (classes : List (List Char))
    (h : classes.Pairwise Included) :
    ArgsEquivalent (PrefixFamilyFusion.parsers (classes.map scan)) (classes.map scan) := by
  induction classes with
  | nil => exact .nil
  | cons A classes ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp h
    apply ArgsEquivalent.cons (by intro g x s T E p hp; rfl)
    have hgo : ∀ (es : List MExp) (ds : List (List Char)), ArgsEquivalent es (ds.map scan) →
        (∀ D ∈ ds, Included A D) →
        ArgsEquivalent (es.map (.seq (scan A))) (ds.map scan) := by
      intro es ds he
      induction ds generalizing es with
      | nil => cases he; intro hall; exact .nil
      | cons D ds ih =>
        cases he with
        | cons hd ht =>
          intro hall
          apply ArgsEquivalent.cons
          · intro g x s T E p hp
            have hh := scan_eval g x s T E A p hp
            rw [evV_seq_ok hh]
            have hs : ∃ pre, x = pre ++ (sfx x p).dropWhile (accepts A) :=
              suffix_trans (sfx_is_suffix x p) ⟨_,(List.takeWhile_append_dropWhile (p := accepts A) (l := sfx x p)).symm⟩
            have hq : ((sfx x p).dropWhile (accepts A)).length ≤ x.length := by
              obtain ⟨pre,he⟩ := hs
              have hl := congrArg List.length he
              simp only [List.length_append] at hl
              omega
            rw [hd g x s T E _ hq]
            rw [← evV_seq_ok hh]
            exact scan_absorb g x s T E A D (hall D (by simp)) p hp
          · exact ih _ ht (fun D hD => hall D (by simp [hD]))
    exact hgo _ classes (ih htail) hhead

theorem arguments_congr {g : MGrammar} {x : List Char} {s : Strategy}
    {T : Nat → List (List Char) → Val} (E : List (List Char)) (p : Nat) (hp : p ≤ x.length)
    {as bs : List MExp} (h : ArgsEquivalent as bs) :
    evParArgs g x s T E as p = evParArgs g x s T E bs p := by
  induction h with
  | nil => rfl
  | cons h ht ih => simp only [evParArgs,h g x s T E p hp,ih]

theorem independent_arguments (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char))
    (classes : List (List Char)) (h : classes.Pairwise Included) (p : Nat) (hp : p ≤ x.length) :
    evParArgs g x s T E (PrefixFamilyFusion.parsers (classes.map scan)) p =
      evParArgs g x s T E (classes.map scan) p :=
  arguments_congr E p hp (parsers_collapse classes h)


theorem accepts_iff_mem (A : List Char) (c : Char) : accepts A c = true ↔ c ∈ A := by
  have hb : ∀ a b, beqChar a b = true ↔ a = b := by
    intro a b
    simp only [Shallot.beqChar,beq_iff_eq]; exact Char.toNat_inj
  induction A with
  | nil => simp [accepts]
  | cons a A ih =>
    simp only [accepts,Bool.or_eq_true,hb,ih,List.mem_cons]
    exact or_congr eq_comm Iff.rfl

/-- The scanner-inclusion side condition is decidable on the static syntax,
without inspecting input strings or successful capture values. -/
def covers (A B : List Char) : Bool := A.all (accepts B)

theorem covers_iff (A B : List Char) : covers A B = true ↔ Included A B := by
  simp only [covers,List.all_eq_true]
  constructor
  · intro h c hc
    exact h c ((accepts_iff_mem A c).mp hc)
  · intro h c hc
    exact h c ((accepts_iff_mem A c).mpr hc)

theorem included_append_left {A B : List Char} (h : Included A B) (C : List Char) :
    Included (C++A) (C++B) := by
  intro c hc
  simp only [accepts_append,Bool.or_eq_true] at hc ⊢
  exact hc.elim Or.inl (fun ha => Or.inr (h c ha))

/-- Every finite list of static character sets generates a valid increasing
scanner family by cumulative union; all runtime captures remain unbounded. -/
theorem cumulative_nested (classes : List (List Char)) :
    (PrefixFamilyFusion.words classes).Pairwise Included := by
  induction classes with
  | nil => exact .nil
  | cons A classes ih =>
    rw [PrefixFamilyFusion.words,List.pairwise_cons]
    constructor
    · intro B hB
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hB
      exact included_prefix A B
    · exact ih.map (fun B => A++B) (fun {B C} h => included_append_left h A)

end Shallot.MacroPeg.CBV.NestedScannerArguments
