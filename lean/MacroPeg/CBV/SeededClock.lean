import MacroPeg.CBV.FilteredOverlapCaller

/-! Finite failures known from a rule prefix can be seeded before user
iteration. Bracketing by two actual frozen rounds proves cofinality. -/
namespace Shallot.MacroPeg.CBV.SeededClock
open ClockFreezing (Table)

def table (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table) : Nat → Table
  | 0 => seed
  | k+1 => fun i W => if pick i then tblV g x s floor i W
      else ClockFreezing.step g x s (table g x s pick floor seed k) i W

theorem rows (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table)
    (hseed : ∀ i, pick i=true → ∀ W, seed i W=tblV g x s floor i W)
    (k i : Nat) (hi : pick i=true) (W : List (List Char)) :
    table g x s pick floor seed k i W=tblV g x s floor i W := by
  cases k with
  | zero => exact hseed i hi W
  | succ k => simp [table,hi]

theorem user_step (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table) (k i : Nat) (hi : pick i=false)
    (r : MRule) (hr : ruleAtM g.rules i=some r) (W : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    valAt (table g x s pick floor seed (k+1) i W) p=
      evV g x s (table g x s pick floor seed k) W r.body p := by
  simp [table,hi,ClockFreezing.step,hr,valAt_rangeMap,hp]

/-- Every seeded round contains the corresponding ordinary frozen round. -/
theorem frozen_le (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table)
    (hlo : TLeV (ClockFreezing.frozen g x s pick floor 0) seed) :
    ∀ k, TLeV (ClockFreezing.frozen g x s pick floor k) (table g x s pick floor seed k)
  | 0 => hlo
  | k+1 => by
    intro i W p
    by_cases hi : pick i=true
    · simp only [ClockFreezing.frozen,table,hi,ite_true]
      exact RLe.refl _
    · have hh := ClockFreezing.step_mono g x s (frozen_le g x s pick floor seed hlo k) i W p
      simpa only [ClockFreezing.frozen,table,hi,Bool.false_eq_true,ite_false] using hh

/-- No seeded round contains more information than one further ordinary
frozen round. The seed is therefore actual finite computation. -/
theorem le_frozen (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table)
    (hhi : TLeV seed (ClockFreezing.frozen g x s pick floor 1)) :
    ∀ k, TLeV (table g x s pick floor seed k) (ClockFreezing.frozen g x s pick floor (k+1))
  | 0 => hhi
  | k+1 => by
    intro i W p
    by_cases hi : pick i=true
    · simp only [ClockFreezing.frozen,table,hi,ite_true]
      exact RLe.refl _
    · have hh := ClockFreezing.step_mono g x s (le_frozen g x s pick floor seed hhi k) i W p
      simpa only [ClockFreezing.frozen,table,hi,Bool.false_eq_true,ite_false] using hh

theorem physical_bound (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table) (hhi : TLeV seed (ClockFreezing.frozen g x s pick floor 1))
    (k : Nat) : TLeV (table g x s pick floor seed k) (tblV g x s (floor+(k+1))) :=
  (le_frozen g x s pick floor seed hhi k).trans
    (ClockFreezing.frozen_le_physical g x s pick floor (k+1))

/-- Seeding finite prefix failures preserves all finite observations and
cannot turn genuine undefinedness into failure. -/
theorem defined_iff (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor : Nat) (seed : Table)
    (hlo : TLeV (ClockFreezing.frozen g x s pick floor 0) seed)
    (hhi : TLeV seed (ClockFreezing.frozen g x s pick floor 1))
    (hs : ClockFreezing.StableRows g x s pick floor)
    (E : List (List Char)) (e : MExp) (p : Nat) (v : Option Nat) :
    (∃ k, evV g x s (table g x s pick floor seed k) E e p=some v) ↔
      ∃ k, evV g x s (tblV g x s k) E e p=some v := by
  rw [←ClockFreezing.defined_iff g x s pick floor hs E e p v]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k+1,(evV_mono (le_frozen g x s pick floor seed hhi k) e p).eq_of_some hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(evV_mono (frozen_le g x s pick floor seed hlo k) e p).eq_of_some hk⟩

/-- Seed only a failed leading expression of an installed sequence body.
Every such result is justified by one actual frozen user round. -/
def prefixSeed (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor : Nat) : Table :=
  fun i W => if pick i then tblV g x s floor i W else
    match ruleAtM g.rules i with
    | some ⟨_,.seq a _⟩ => (List.range (x.length+1)).map (fun p =>
        if evV g x s (ClockFreezing.frozen g x s pick floor 0) W a p=some none then some none else none)
    | _ => []

theorem prefixSeed_rows (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor i : Nat) (hi : pick i=true) (W : List (List Char)) :
    prefixSeed g x s pick floor i W=tblV g x s floor i W := by simp [prefixSeed,hi]

theorem prefixSeed_lower (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor : Nat) :
    TLeV (ClockFreezing.frozen g x s pick floor 0) (prefixSeed g x s pick floor) := by
  intro i W p
  by_cases hi : pick i=true
  · rw [ClockFreezing.frozen_rows g x s pick floor 0 i hi W,prefixSeed_rows g x s pick floor i hi W]
    exact RLe.refl _
  · exact Or.inl (by simp [ClockFreezing.frozen,hi,valAt_nil])

theorem prefixSeed_upper (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool) (floor : Nat) :
    TLeV (prefixSeed g x s pick floor) (ClockFreezing.frozen g x s pick floor 1) := by
  intro i W p
  by_cases hi : pick i=true
  · rw [prefixSeed_rows g x s pick floor i hi W,ClockFreezing.frozen_rows g x s pick floor 1 i hi W]
    exact RLe.refl _
  · have hi' : pick i=false := by simpa using hi
    cases hr : ruleAtM g.rules i with
    | none => exact Or.inl (by simp [prefixSeed,hi,hr,valAt_nil])
    | some rule =>
      cases rule with
      | mk arity e =>
        cases e with
        | seq a b =>
          by_cases hp : p≤x.length
          · simp only [prefixSeed,hi',Bool.false_eq_true,ite_false,hr,valAt_rangeMap,if_pos hp]
            split
            · rename_i hfail
              exact Or.inr (by
                rw [ClockFreezing.frozen_user_step g x s pick floor 0 i hi' _ hr W p hp,
                  evV_seq_fail hfail])
            · exact Or.inl rfl
          · exact Or.inl (by simp [prefixSeed,hi,hr,valAt_rangeMap,hp])
        | eps | any | chr c | range lo upper | lit w | param j | call j args | alt a b | star a | notP a
        | dbg a | lam n a | callParam j args | invoke n a args =>
          exact Or.inl (by simp [prefixSeed,hi,hr,valAt_nil])

theorem prefixSeed_query (g : MGrammar) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor i : Nat) (hi : pick i=false) (arity : Nat) (a b : MExp)
    (hr : ruleAtM g.rules i=some ⟨arity,.seq a b⟩) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (prefixSeed g x s pick floor i W) p=
      if evV g x s (ClockFreezing.frozen g x s pick floor 0) W a p=some none then some none else none := by
  simp [prefixSeed,hi,hr,valAt_rangeMap,hp]

abbrev rounds (bodies : List MExp) (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) : Table :=
  table g x s (RecursiveParserStability.pick bodies) (RecursiveParserStability.floor bodies x)
    (prefixSeed g x s (RecursiveParserStability.pick bodies) (RecursiveParserStability.floor bodies x)) k

theorem rounds_bound (bodies : List MExp) (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) :
    TLeV (rounds bodies g x s k)
      (tblV g x s (RecursiveParserStability.floor bodies x+(k+1))) :=
  physical_bound g x s _ _ _ (prefixSeed_upper g x s _ _) k

theorem rounds_ok (bodies : List MExp) (g : MGrammar) (x : List Char) (s : Strategy) (k : Nat) :
    OkTV x.length (rounds bodies g x s k) := by
  intro i W p j hv
  exact tblV_ok g x s _ i W p j ((rounds_bound bodies g x s k i W p).eq_of_some hv)

theorem rounds_sound {g : MGrammar} (hg : g.FirstOrder) (bodies : List MExp) (x : List Char)
    (s : Strategy) (hs : s≠.callByName) (k : Nat) : SoundTV g x s (rounds bodies g x s k) := by
  intro i rule W hr ha p hp v hv
  exact tblV_sound hg hs _ i rule W hr ha p hp v ((rounds_bound bodies g x s k i W p).eq_of_some hv)

/-- The initial prefix probe uses the same independent helper computations
as the ordinary canonical evaluator. Seeding introduces no helper oracle. -/
theorem rounds_lexical {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g : MGrammar} (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy)
    (k : Nat) (E F : List (List Char)) (e : MExp) (he : RecursiveParserStability.Lexical bodies.length e)
    (p : Nat) (hp : p≤x.length) :
    evV g x s (rounds bodies g x s k) E e p=
      evV g x s (tblV g x s (iterBoundV g x)) F e p := by
  apply RecursiveParserStability.lexical_eval hg hg x s s _ _ (rounds_ok bodies g x s k) _ E F e he p hp
  intro i hi q hq
  have hchoose : RecursiveParserStability.pick bodies i=true := by simp [RecursiveParserStability.pick,hi]
  unfold rounds
  rw [rows g x s _ _ _ (prefixSeed_rows g x s _ _) k i hchoose []]
  have hn := List.getElem?_eq_getElem hi
  have hrow := RecursiveParserStability.helper_rows_eq hb hg (RecursiveParserStability.installed bodies)
    x s s (RecursiveParserStability.floor bodies x) i hi [] []
  rw [hrow]
  have hfixed := agreeV_from
    (RegularCaptureProduct.bound_fixed (RecursiveParserStability.grammar bodies) x s) 1
  have hc := hfixed i ⟨0,bodies[i]⟩ [] (RecursiveParserStability.installed bodies i bodies[i] hn)
    (by simp [words]) q hq
  rw [show RecursiveParserStability.floor bodies x=iterBoundV (RecursiveParserStability.grammar bodies) x+1 from rfl]
  rw [←hc]
  exact RegularCaptureProduct.canonical_helpers_eq hb (RecursiveParserStability.installed bodies) hg x s s i q hi hq

theorem rounds_defined_iff {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g : MGrammar} (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy)
    (E : List (List Char)) (e : MExp) (p : Nat) (v : Option Nat) :
    (∃ k, evV g x s (rounds bodies g x s k) E e p=some v) ↔
      ∃ k, evV g x s (tblV g x s k) E e p=some v :=
  defined_iff g x s _ _ _ (prefixSeed_lower g x s _ _) (prefixSeed_upper g x s _ _)
    (RecursiveParserStability.helpers_stable hb hg x s) E e p v

theorem word_eval_eq (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (E : List (List Char)) : ∀ a, WordArguments.Word a → ∀ p,
      evV g x s T E a p=evV h x t U E a p
  | .lit _, _, _ | .param _, _, _ => rfl
  | .seq a b, ha, p => by
    change (match evV g x s T E a p with | some (some z) => evV g x s T E b z | other => other)=_
    rw [word_eval_eq g h x s t T U E a ha.1 p]
    change (match evV h x t U E a p with | some (some z) => evV g x s T E b z | other => other)=
      (match evV h x t U E a p with | some (some z) => evV h x t U E b z | other => other)
    cases evV h x t U E a p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some z => exact word_eval_eq g h x s t T U E b ha.2 z
  | .eps, ha, _ | .any, ha, _ | .chr _, ha, _ | .range _ _, ha, _ | .call _ _, ha, _
  | .alt _ _, ha, _ | .star _, ha, _ | .notP _, ha, _ | .dbg _, ha, _
  | .lam _ _, ha, _ | .callParam _ _, ha, _ | .invoke _ _ _, ha, _ => False.elim ha

/-- A genuinely failed word prefix is already failed at seed stage zero
and remains failed at every later user stage, irrespective of its tail. -/
theorem rounds_failed_prefix (bodies : List MExp) (g : MGrammar) (x : List Char) (s : Strategy)
    (i arity : Nat) (hi : RecursiveParserStability.pick bodies i=false) (a b : MExp)
    (hr : ruleAtM g.rules i=some ⟨arity,.seq a b⟩) (ha : WordArguments.Word a)
    (W : List (List Char)) (T : Table) (p : Nat) (hp : p≤x.length)
    (hv : evV g x s T W a p=some none) (k : Nat) :
    valAt (rounds bodies g x s k i W) p=some none := by
  cases k with
  | zero =>
    rw [show rounds bodies g x s 0=prefixSeed g x s _ _ from rfl,
      prefixSeed_query g x s _ _ i hi arity a b hr W p hp,
      word_eval_eq g g x s s _ T W a ha p,if_pos hv]
  | succ k =>
    rw [user_step g x s _ _ _ k i hi _ hr W p hp]
    exact evV_seq_fail ((word_eval_eq g g x s s _ T W a ha p).trans hv)

theorem stable_defined_iff {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g : MGrammar} (hg : RecursiveParserStability.Installed bodies g) (x : List Char) (s : Strategy)
    (e : MExp) (p : Nat) (hp : p≤x.length) (v : Option Nat) :
    (∃ k, evV g x s (rounds bodies g x s k) [] e p=some v) ↔
      evV g x s (tblV g x s (iterBoundV g x)) [] e p=some v :=
  (rounds_defined_iff hb hg x s [] e p v).trans (tblV_stable g x s hp)

theorem observations_iff {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g : MGrammar} (hg : RecursiveParserStability.Installed bodies g) (hFO : g.FirstOrder)
    (x : List Char) (s : Strategy) (hs : s≠.callByName) (e : MExp) (he : e.FirstOrder)
    (rest : Option (List Char)) :
    SObs g s e x rest ↔ ∃ k v, evV g x s (rounds bodies g x s k) [] e x.length=some v ∧
      v.map (sfx x)=rest := by
  rw [←decideObsV_iff hFO hs he x rest]
  constructor
  · intro h
    unfold decideObsV at h
    cases hv : evV g x s (tblV g x s (iterBoundV g x)) [] e x.length with
    | none => rw [hv] at h; cases h
    | some v =>
      obtain ⟨k,hk⟩ := (stable_defined_iff hb hg x s e x.length (Nat.le_refl _) v).mpr hv
      refine ⟨k,v,hk,?_⟩
      rw [hv] at h
      cases v <;> simpa using h
  · rintro ⟨k,v,hk,hr⟩
    have hv := (stable_defined_iff hb hg x s e x.length (Nat.le_refl _) v).mp ⟨k,hk⟩
    unfold decideObsV
    rw [hv]
    cases v <;> simpa using congrArg some hr

end Shallot.MacroPeg.CBV.SeededClock
