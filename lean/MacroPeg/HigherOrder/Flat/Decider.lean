import MacroPeg.HigherOrder.Flat.Infer
import MacroPeg.HigherOrder.Flat.Deser

/-!
# The flat decision procedure for the uniform problem

`flatDecide j bits`: read the instance (`deser` of the 4-bit tokens), infer the type and the items of every rule body
and of the start (`checkRules`, `inferE`), check the order, run the rounds from the empty rule values until nothing
changes (`fixNums`), evaluate the start, and accept iff its code at the full input is `2`.

`flatDecide_iff`: it decides `UMPEG j`. Every step works on numbers and lists of numbers, so it is the specification
of the machine program.
-/

namespace Shallot.MacroPeg.Flat

open Complexity
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.KExp

/-! ## Checking the rules -/

/-- The items of a rule body, if it has the rule's type. -/
def checkRule (R : List HO.Ty) (r : HRule) : Option (List Item) :=
  match inferE R [] r.body with
  | some (τ, is) => if τ = r.ty then some is else none
  | none => none

def checkRules (g : HGrammar) : Option (List (List Item)) := g.rules.mapM (checkRule g.types)

theorem checkRule_sound {R : List HO.Ty} {r : HRule} {is : List Item} (h : checkRule R r = some is) :
    ∃ t : Tm R [] r.ty, t.erase = r.body ∧ items t = is := by
  unfold checkRule at h
  split at h
  · rename_i τ is' hi
    split at h
    · rename_i hτ
      subst hτ
      simp only [Option.some.injEq] at h
      subst h
      exact inferE_sound _ hi
    · cases h
  · cases h

theorem checkRule_complete {R : List HO.Ty} {r : HRule} (h : HasTy R [] r.body r.ty) : ∃ is, checkRule R r = some is := by
  obtain ⟨is, hi⟩ := inferE_complete h
  exact ⟨is, by simp [checkRule, hi]⟩

theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {bs : List β}
    (h : (a :: l).mapM f = some bs) : ∃ b bs', f a = some b ∧ l.mapM f = some bs' ∧ bs = b :: bs' := by
  rw [List.mapM_cons] at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨b, hb, bs', hbs', rfl⟩ := h
  exact ⟨b, bs', hb, hbs', rfl⟩

theorem checkRules_sound_aux {R : List HO.Ty} : ∀ (rs : List HRule) {bis : List (List Item)},
    rs.mapM (checkRule R) = some bis →
    ∃ ts : TBodies R (rs.map HRule.ty),
      List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) (rs.map HRule.ty) ts.erase = rs ∧ bodyItems ts = bis
  | [], bis, h => by
    rw [List.mapM_nil] at h
    simp only [pure, Option.some.injEq] at h
    exact ⟨(), rfl, h⟩
  | r :: rs, bis, h => by
    obtain ⟨is, bis', hr, hrs, rfl⟩ := mapM_cons_some h
    obtain ⟨t, ht, hit⟩ := checkRule_sound hr
    obtain ⟨ts, hts, hits⟩ := checkRules_sound_aux rs hrs
    refine ⟨(t, ts), ?_, ?_⟩
    · simp only [List.map_cons, TBodies.erase, List.zipWith_cons_cons, ht, hts]
    · show items t :: bodyItems ts = is :: bis'
      rw [hit, hits]

/-- **The checked rules are the bodies of a typed grammar**, with the computed items. -/
theorem checkRules_sound {g : HGrammar} {bis : List (List Item)} (h : checkRules g = some bis) :
    ∃ G : TGrammar g.types, G.erase = g ∧ bodyItems G.bodies = bis := by
  obtain ⟨ts, hts, hits⟩ := checkRules_sound_aux g.rules h
  exact ⟨⟨ts⟩, by cases g; simp only [TGrammar.erase, HGrammar.mk.injEq]; exact hts, hits⟩

theorem checkRules_complete {g : HGrammar} (hg : g.WellTyped) : ∃ bis, checkRules g = some bis := by
  unfold checkRules
  suffices ∀ rs : List HRule, (∀ r ∈ rs, HasTy g.types [] r.body r.ty) → ∃ bis, rs.mapM (checkRule g.types) = some bis
    from this g.rules hg
  intro rs
  induction rs with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons r rs ih =>
    intro h
    obtain ⟨is, hi⟩ := checkRule_complete (h r List.mem_cons_self)
    obtain ⟨bis, hb⟩ := ih (fun r' hr => h r' (List.mem_cons_of_mem _ hr))
    exact ⟨is :: bis, by simp [List.mapM_cons, hi, hb]⟩

theorem mapM_some_mem {α β : Type} {f : α → Option β} : ∀ {l : List α} {bs : List β}, l.mapM f = some bs →
    ∀ a ∈ l, ∃ b, f a = some b
  | [], _, _, a, ha => by simp at ha
  | c :: l, bs, h, a, ha => by
    obtain ⟨b, bs', hb, hbs, _⟩ := mapM_cons_some h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, hb⟩
    · exact mapM_some_mem hbs a ha

theorem checkRules_wellTyped {g : HGrammar} {bis : List (List Item)} (h : checkRules g = some bis) : g.WellTyped := by
  intro r hr
  obtain ⟨is, hi⟩ := mapM_some_mem h r hr
  obtain ⟨t, ht, _⟩ := checkRule_sound hi
  rw [← ht]
  exact t.hasTy

/-! ## The least values have number `0` -/

theorem allVecs_head {α : Type} (a : α) (xs : List α) : ∀ m, ∃ rest, allVecs (a :: xs) m = List.replicate m a :: rest
  | 0 => ⟨[], rfl⟩
  | m + 1 => by
    obtain ⟨rest, h⟩ := allVecs_head a xs m
    refine ⟨rest.map (a :: ·) ++ xs.flatMap (fun b => (allVecs (a :: xs) m).map (b :: ·)), ?_⟩
    rw [allVecs, List.flatMap_cons, h]
    simp [List.replicate_succ]

theorem elems_head (N : Nat) : ∀ τ : HO.Ty, ∃ rest, elems N τ = bot N τ :: rest
  | .p => by
    obtain ⟨rest, h⟩ := allVecs_head (none : Res) _ (N + 1)
    exact ⟨rest, by simp only [elems, resElems] at h ⊢; rw [h]; rfl⟩
  | .arr a b => by
    obtain ⟨rb, hb⟩ := elems_head N b
    obtain ⟨rest, h⟩ := allVecs_head (bot N b) rb (elems N a).length
    have hmono : tabMonoB (elems N a) (List.replicate (elems N a).length (bot N b)) = true := by
      have := bot_mem N (a ⇒ b)
      rw [mem_elems_arr] at this
      exact (tabMonoB_iff _ _).2 this.2
    refine ⟨rest.filter (tabMonoB (elems N a)), ?_⟩
    simp only [elems]
    rw [hb, h]
    simp only [List.filter, hmono]
    rfl

theorem vIdx_bot (N : Nat) (τ : HO.Ty) : vIdx N τ (bot N τ) = 0 := by
  obtain ⟨rest, h⟩ := elems_head N τ
  simp [vIdx, h, indexIn]

theorem envNums_bot (N : Nat) : ∀ R : List HO.Ty, envNums N (Env.bot N R) = List.replicate R.length 0
  | [] => rfl
  | τ :: R => by simp [envNums, Env.bot, vIdx_bot, envNums_bot N R, List.replicate_succ]

/-! ## The procedure -/

/-- The code at the full input of the start, after the rounds. -/
def startCode (g : HGrammar) (x : List Char) (bis : List (List Item)) (is : List Item) : Nat :=
  answerCode x (((run x (fixNums x bis (maxEnv x.length g.types + 1) (List.replicate g.rules.length 0)) is
    []).headD []).headD 0)

/-- **The flat decision procedure** for the uniform problem of order `j`. -/
def flatDecide (j : Nat) (bits : List Bool) : Bool :=
  match deser (ofBits bits) with
  | none => false
  | some (g, s, x) =>
    match checkRules g, inferE g.types [] s with
    | some bis, some (.p, is) => decide (g.order ≤ j) && (startCode g x bis is == 2)
    | _, _ => false

/-- The start code is `2` iff the grammar consumes the whole input. -/
theorem startCode_iff {g : HGrammar} {G : TGrammar g.types} (hG : G.erase = g) {x : List Char}
    {t : Tm g.types [] .p} : startCode g x (bodyItems G.bodies) (items t) = 2 ↔ HObs g t.erase x (some []) := by
  have hlen : g.rules.length = g.types.length := by simp [HGrammar.types]
  have hfix : fixNums x (bodyItems G.bodies) (maxEnv x.length g.types + 1) (List.replicate g.rules.length 0) =
      envNums x.length (iter x G (maxEnv x.length g.types)) := by
    rw [hlen, ← envNums_bot]
    exact fixNums_eq x G _ (by omega)
  have hrun := run_items (iter_mem x G (maxEnv x.length g.types)) (envNums_getD x.length _) t []
  unfold startCode
  rw [hfix, hrun, vec_closed]
  simp only [List.headD_cons]
  rw [← accept_iff x G t, hG]

/-- **The flat procedure decides the uniform problem.** -/
theorem flatDecide_iff (j : Nat) (bits : List Bool) : flatDecide j bits = true ↔ UMPEG j bits := by
  constructor
  · intro h
    unfold flatDecide at h
    split at h
    · cases h
    · rename_i g s x hdes
      split at h
      · rename_i bis is hcr hinf
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨G, hG, hbis⟩ := checkRules_sound hcr
        obtain ⟨t, ht, hit⟩ := inferE_sound s hinf
        refine ⟨g, s, x, deser_sound hdes, checkRules_wellTyped hcr, h.1, ht ▸ t.hasTy, ?_⟩
        rw [← ht, ← startCode_iff hG, hbis, hit]
        exact h.2
      · cases h
  · rintro ⟨g, s, x, hb, hwt, hord, hty, hobs⟩
    obtain ⟨bis, hcr⟩ := checkRules_complete hwt
    obtain ⟨is, hinf⟩ := inferE_complete hty
    obtain ⟨G, hG, hbis⟩ := checkRules_sound hcr
    obtain ⟨t, ht, hit⟩ := inferE_sound s hinf
    unfold flatDecide
    rw [hb, deser_serIn]
    simp only [hcr, hinf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨hord, ?_⟩
    rw [← hbis, ← hit, startCode_iff hG, ht]
    exact hobs

end Shallot.MacroPeg.Flat
