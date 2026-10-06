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

/-! ## The least values are written out as zeros -/

theorem flatMap_replicate_zeros {α : Type} (f : α → List Nat) (m : Nat) (x : α) (hx : f x = List.replicate m 0) :
    ∀ k, (List.replicate k x).flatMap f = List.replicate (k * m) 0
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, flatMap_replicate_zeros f m x hx k, hx, Nat.succ_mul,
      Nat.add_comm (k * m), List.replicate_append_replicate]

theorem flatVal_bot (N : Nat) : ∀ τ : HO.Ty, flatVal N τ (bot N τ) = List.replicate (valSize N τ) 0
  | .p => by simp [flatVal, bot, valSize, resCode]
  | .arr a b => by
    show (List.replicate (elems N a).length (bot N b)).flatMap (flatVal N b) = _
    rw [flatMap_replicate_zeros (flatVal N b) (valSize N b) (bot N b) (flatVal_bot N b)]
    rfl

theorem envFlat_bot (N : Nat) : ∀ R : List HO.Ty,
    envFlat N (Env.bot N R) = R.map (fun τ => List.replicate (valSize N τ) 0)
  | [] => rfl
  | τ :: R => by simp [envFlat, Env.bot, flatVal_bot, envFlat_bot N R]

/-! ## The procedure -/

instance (j : Nat) (g : HGrammar) (s : HExp) : Decidable (GOrd j g s) := by unfold GOrd; infer_instance

/-- The least rule values, written out. -/
def zeroRules (N : Nat) (g : HGrammar) : List (List Nat) := g.rules.map (fun r => List.replicate (valSize N r.ty) 0)

/-- The code at the full input of the start, after the rounds. -/
def startCode (g : HGrammar) (x : List Char) (bis : List (List Item)) (is : List Item) : Nat :=
  (((run x (fixFlat x bis (maxEnv x.length g.types + 1) (zeroRules x.length g)) is []).headD []).headD []).getD
    x.length 0

/-- **The flat decision procedure** for the uniform problem of order `j`. -/
def flatDecide (j : Nat) (bits : List Bool) : Bool :=
  match deser (ofBits bits) with
  | none => false
  | some (g, s, x) =>
    match checkRules g, inferE g.types [] s with
    | some bis, some (.p, is) => decide (GOrd j g s) && (startCode g x bis is == 2)
    | _, _ => false

/-- The start code is `2` iff the grammar consumes the whole input. -/
theorem startCode_iff {g : HGrammar} {G : TGrammar g.types} (hG : G.erase = g) {x : List Char}
    {t : Tm g.types [] .p} : startCode g x (bodyItems G.bodies) (items t) = 2 ↔ HObs g t.erase x (some []) := by
  have hfix : fixFlat x (bodyItems G.bodies) (maxEnv x.length g.types + 1) (zeroRules x.length g) =
      envFlat x.length (iter x G (maxEnv x.length g.types)) := by
    have : zeroRules x.length g = envFlat x.length (Env.bot x.length g.types) := by
      rw [envFlat_bot]; simp [zeroRules, HGrammar.types]
    rw [this]
    exact fixFlat_eq x G _ (by omega)
  have hrun := run_items (iter_mem x G (maxEnv x.length g.types)) (envFlat_getD x.length _) t []
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
