import MacroPeg.CBVtoCBN.LengthSearch

namespace Shallot.MacroPeg.CBVtoCBN

/-- Inspect one character at an encoded input position, restoring the original input. -/
def charAtP (pre : MExp) (c : Char) : MExp := andP (.seq pre (.chr c))

theorem charAt_obs {g : MGrammar} {pre : MExp} {p : Nat} (hp : LenRep g pre p)
    (x : List Char) (c : Char) :
    MacroObs g (charAtP pre c) x (if x[p]? = some c then some x else none) := by
  by_cases hn : p ≤ x.length
  · have hx : MacroObs g pre x (some (x.drop p)) := by simpa only [if_pos hn] using hp x
    have hget : x[p]? = (x.drop p).head? := List.head?_drop.symm
    cases hd : x.drop p with
    | nil =>
      have hb : MacroObs g (.chr c) (x.drop p) none := by rw [hd]; exact ⟨_, .chrEmpty c, rfl⟩
      simpa [charAtP, hget, hd] using obs_and_none (obs_seq hx hb)
    | cons d ds =>
      by_cases he : c = d
      · subst c
        have hb : MacroObs g (.chr d) (x.drop p) (some ds) := by
          rw [hd]
          exact ⟨_, .chrOk d d ds (by simp [Shallot.beqChar]), rfl⟩
        simpa [charAtP, hget, hd] using obs_and_some (obs_seq hx hb)
      · have hb : MacroObs g (.chr c) (x.drop p) none := by
          rw [hd]
          exact ⟨_, .chrFail c d ds (by simpa [Shallot.beqChar, Char.toNat_inj] using he), rfl⟩
        simpa [charAtP, hget, hd, Ne.symm he] using obs_and_none (obs_seq hx hb)
  · have hx : MacroObs g pre x none := by simpa only [if_neg hn] using hp x
    have hget : x[p]? = none := List.getElem?_eq_none (by omega)
    simpa [charAtP, hget] using obs_and_none (obs_seq_none (b := .chr c) hx)

def choices : List MExp → MExp
  | [] => MExp.failAlways
  | e :: es => .alt e (choices es)

theorem choices_none {g : MGrammar} (es : List MExp) (x : List Char)
    (h : ∀ e ∈ es, MacroObs g e x none) : MacroObs g (choices es) x none := by
  induction es with
  | nil => exact obs_not_some (obs_eps x)
  | cons e es ih =>
    exact obs_alt_none (h e List.mem_cons_self) (ih (fun a ha => h a (List.mem_cons_of_mem e ha)))

/-- A finite character case distinction preserves even an explicit failure of its selected branch. -/
theorem choices_character {g : MGrammar} (A : List Char) (branch : Char → MExp) (x : List Char)
    (c : Char) (r : Option (List Char)) (hc : c ∈ A)
    (h : ∀ d ∈ A, MacroObs g (branch d) x (if d = c then r else none)) :
    MacroObs g (choices (A.map branch)) x r := by
  cases r with
  | none =>
    apply choices_none
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    simpa using h d hd
  | some y =>
    induction A with
    | nil => simp at hc
    | cons d A ih =>
      by_cases he : d = c
      · subst d
        exact obs_alt_some (by simpa using h c List.mem_cons_self)
      · have hd : MacroObs g (branch d) x none := by simpa only [if_neg he] using h d List.mem_cons_self
        have hc' : c ∈ A := by simpa [Ne.symm he] using hc
        exact obs_alt_none hd (ih hc' (fun a ha => h a (List.mem_cons_of_mem d ha)))

def spanSlice (x : List Char) (p q : Nat) : List Char := (x.drop p).take (q - p)

theorem spanSlice_length (x : List Char) (p q : Nat) (hpq : p ≤ q) (hqn : q ≤ x.length) :
    (spanSlice x p q).length = q - p := by
  simp only [spanSlice, List.length_take, List.length_drop]
  omega

theorem spanSlice_cons {x : List Char} {p q : Nat} {c : Char} {cs : List Char}
    (hpq : p < q) (hd : x.drop p = c :: cs) :
    spanSlice x p q = c :: spanSlice x (p + 1) q := by
  have hn : q - p = (q - (p + 1)) + 1 := by omega
  have ht : x.drop (p + 1) = cs := by rw [List.drop_add_one_eq_tail_drop, hd]; rfl
  simp only [spanSlice, hd, hn, List.take_succ_cons, ht]

def spanEqExpr (self : Nat) (A : List Char) (src endSrc dst endDst : MExp) : MExp :=
  ifP (equalPositionP src endSrc) (equalPositionP dst endDst)
    (ifP (equalPositionP dst endDst) MExp.failAlways
      (choices (A.map (fun c => .seq (charAtP src c) (.seq (charAtP dst c)
        (.call self [.seq src .any, endSrc, .seq dst .any, endDst]))))))

def spanEqBody (self : Nat) (A : List Char) : MExp :=
  spanEqExpr self A (.param 0) (.param 1) (.param 2) (.param 3)

theorem subst_choices (args : List MExp) : ∀ es,
    MExp.subst args (choices es) = choices (es.map (MExp.subst args))
  | [] => rfl
  | e :: es => by simp [choices, MExp.subst, subst_choices args es]

theorem spanEqBody_subst (self : Nat) (A : List Char) (a b c d : MExp) :
    MExp.subst [a, b, c, d] (spanEqBody self A) = spanEqExpr self A a b c d := by
  simp [spanEqBody, spanEqExpr, ifP, equalPositionP, exactLengthP, andP, charAtP,
    MExp.subst, MExp.substArgs, MExp.failAlways, argAt, subst_choices, List.map_map, Function.comp_def]

theorem choices_firstOrder (es : List MExp) (h : ∀ e ∈ es, e.FirstOrder) : (choices es).FirstOrder := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem e ha))⟩

theorem spanEqBody_firstOrder (self : Nat) (A : List Char) : (spanEqBody self A).FirstOrder := by
  apply ifP_firstOrder
  · exact ⟨⟨trivial, trivial⟩, trivial⟩
  · exact ⟨⟨trivial, trivial⟩, trivial⟩
  · apply ifP_firstOrder
    · exact ⟨⟨trivial, trivial⟩, trivial⟩
    · trivial
    · apply choices_firstOrder
      intro e he
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
      exact ⟨⟨trivial, trivial⟩, ⟨⟨trivial, trivial⟩,
        ⟨⟨trivial, trivial⟩, trivial, ⟨trivial, trivial⟩, trivial, trivial⟩⟩⟩

/-- A single finite first-order CBN rule compares two arbitrary input intervals.
The alphabet need only cover the source input; all observations, including finite failure, are determined. -/
theorem spanEq_obs {g : MGrammar} {self : Nat} {A : List Char}
    (hr : ruleAtM g.rules self = some ⟨4, spanEqBody self A⟩)
    (x : List Char) (hA : ∀ c ∈ x, c ∈ A) :
    ∀ (p q t u : Nat), p ≤ q → q ≤ x.length → t ≤ u → u ≤ x.length →
      MacroObs g (.call self [skipN p, skipN (x.length - q), skipN t, skipN (x.length - u)]) x
        (if spanSlice x p q = spanSlice x t u then some x else none) := by
  have aux : ∀ d p q t u, q - p = d → p ≤ q → q ≤ x.length → t ≤ u → u ≤ x.length →
      MacroObs g (.call self [skipN p, skipN (x.length - q), skipN t, skipN (x.length - u)]) x
        (if spanSlice x p q = spanSlice x t u then some x else none) := by
    intro d
    induction d with
    | zero =>
      intro p q t u hd hpq hqn htu hun
      have hpq' : p = q := by omega
      have htest := equalPosition_obs (skipN_rep g p) (skipN_rep g (x.length - q)) x (by omega)
      have htest' : MacroObs g (equalPositionP (skipN p) (skipN (x.length - q))) x (some x) := by
        simpa only [show p = x.length - (x.length - q) by omega, if_true] using htest
      apply (obs_call_iff hr (by rfl) x _).mpr
      rw [spanEqBody_subst]
      apply (ifP_true_iff htest' _).mpr
      have ht := equalPosition_obs (skipN_rep g t) (skipN_rep g (x.length - u)) x (by omega)
      have he : spanSlice x p q = spanSlice x t u ↔ t = u := by
        have hl := spanSlice_length x t u htu hun
        simp only [spanSlice, show q - p = 0 by omega, List.take_zero]
        constructor
        · intro hh
          have := congrArg List.length hh
          simp only [List.length_nil] at this
          change 0 = (spanSlice x t u).length at this
          rw [hl] at this
          omega
        · intro hh; simp [hh]
      simpa only [he, show x.length - (x.length - u) = u by omega] using ht
    | succ d ih =>
      intro p q t u hd hpq hqn htu hun
      have hpq' : p < q := by omega
      have hsrc := equalPosition_obs (skipN_rep g p) (skipN_rep g (x.length - q)) x (by omega)
      have hsrc' : MacroObs g (equalPositionP (skipN p) (skipN (x.length - q))) x none := by
        have he : p ≠ x.length - (x.length - q) := by omega
        simpa only [if_neg he] using hsrc
      apply (obs_call_iff hr (by rfl) x _).mpr
      rw [spanEqBody_subst]
      apply (ifP_false_iff hsrc' _).mpr
      have hdst := equalPosition_obs (skipN_rep g t) (skipN_rep g (x.length - u)) x (by omega)
      by_cases htu' : t = u
      · have ht : MacroObs g (equalPositionP (skipN t) (skipN (x.length - u))) x (some x) := by
          simpa only [show t = x.length - (x.length - u) by omega, if_true] using hdst
        apply (ifP_true_iff ht _).mpr
        have he : spanSlice x p q ≠ spanSlice x t u := by
          have hl := spanSlice_length x p q hpq hqn
          intro he
          have hh := congrArg List.length he
          simp only [spanSlice, htu', Nat.sub_self, List.take_zero, List.length_nil] at hh
          change (spanSlice x p q).length = 0 at hh
          rw [hl] at hh
          omega
        simpa only [MExp.failAlways, if_neg he] using obs_not_some (obs_eps (g := g) x)
      · have htu'' : t < u := by omega
        have ht : MacroObs g (equalPositionP (skipN t) (skipN (x.length - u))) x none := by
          simpa only [show t ≠ x.length - (x.length - u) by omega, if_false] using hdst
        apply (ifP_false_iff ht _).mpr
        have hpLen : p < x.length := by omega
        have htLen : t < x.length := by omega
        cases hs : x.drop p with
        | nil => have hl := congrArg List.length hs; simp only [List.length_drop, List.length_nil] at hl; omega
        | cons c cs =>
          cases hz : x.drop t with
          | nil => have hl := congrArg List.length hz; simp only [List.length_drop, List.length_nil] at hl; omega
          | cons z zs =>
            have hc : c ∈ A := hA c (by
              have hm : c ∈ x.drop p := by rw [hs]; simp
              exact List.mem_of_mem_drop hm)
            have hgetp : x[p]? = some c := by rw [← List.head?_drop, hs]; rfl
            have hgett : x[t]? = some z := by rw [← List.head?_drop, hz]; rfl
            apply choices_character A _ x c _ hc
            intro a ha
            by_cases hac : a = c
            · subst a
              have hcAt : MacroObs g (charAtP (skipN p) c) x (some x) := by
                simpa only [hgetp, if_true] using charAt_obs (skipN_rep g p) x c
              apply obs_seq hcAt
              by_cases hcz : c = z
              · subst z
                have hzAt : MacroObs g (charAtP (skipN t) c) x (some x) := by
                  simpa only [hgett, if_true] using charAt_obs (skipN_rep g t) x c
                have hi := ih (p + 1) q (t + 1) u (by omega) (by omega) hqn (by omega) hun
                have he : spanSlice x p q = spanSlice x t u ↔ spanSlice x (p + 1) q = spanSlice x (t + 1) u := by
                  rw [spanSlice_cons hpq' hs, spanSlice_cons htu'' hz]
                  simp
                simpa only [if_true, he, skipN] using obs_seq hzAt hi
              · have hzAt : MacroObs g (charAtP (skipN t) c) x none := by
                  simpa [hgett, Ne.symm hcz] using charAt_obs (skipN_rep g t) x c
                have he : spanSlice x p q ≠ spanSlice x t u := by
                  rw [spanSlice_cons hpq' hs, spanSlice_cons htu'' hz]
                  intro h; exact hcz (List.cons.inj h).1
                simpa only [if_true, if_neg he] using obs_seq_none hzAt
            · have haAt : MacroObs g (charAtP (skipN p) a) x none := by
                simpa [hgetp, Ne.symm hac] using charAt_obs (skipN_rep g p) x a
              simpa only [if_neg hac] using obs_seq_none haAt
  intro p q t u hpq hqn htu hun
  exact aux (q - p) p q t u rfl hpq hqn htu hun

end Shallot.MacroPeg.CBVtoCBN
