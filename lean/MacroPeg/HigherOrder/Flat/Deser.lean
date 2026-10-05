import MacroPeg.HigherOrder.KExp.Uniform

/-!
# Reading an instance back

`deser` parses the token codes of `serIn` (prefix codes, read with a fuel bound by the input length):

* `deser_serIn`: a serialized instance is read back;
* `deser_sound`: whatever is read back serializes to the input.
-/

namespace Shallot.MacroPeg.Flat

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.KExp

/-! ## The parsers -/

def parseNat : List Nat → Option (Nat × List Nat)
  | 0 :: r => some (0, r)
  | 1 :: r => (parseNat r).map (fun p => (p.1 + 1, p.2))
  | _ => none

def parseChar (l : List Nat) : Option (Char × List Nat) :=
  match parseNat l with
  | some (n, r) => if (Char.ofNat n).toNat = n then some (Char.ofNat n, r) else none
  | none => none

def parseStr : Nat → List Nat → Option (List Char × List Nat)
  | _, 0 :: r => some ([], r)
  | f + 1, 1 :: r =>
    match parseChar r with
    | some (c, r₁) => (parseStr f r₁).map (fun p => (c :: p.1, p.2))
    | none => none
  | _, _ => none

def parseTy : Nat → List Nat → Option (HO.Ty × List Nat)
  | _ + 1, 0 :: r => some (.p, r)
  | f + 1, 1 :: r =>
    match parseTy f r with
    | some (a, r₁) => (parseTy f r₁).map (fun p => (a ⇒ p.1, p.2))
    | none => none
  | _, _ => none

/-- Two subexpressions with the same fuel. -/
def parseE : Nat → List Nat → Option (HExp × List Nat)
  | _ + 1, 0 :: r => some (.eps, r)
  | _ + 1, 1 :: r => some (.any, r)
  | _ + 1, 2 :: r => (parseChar r).map (fun p => (.chr p.1, p.2))
  | _ + 1, 3 :: r =>
    match parseChar r with
    | some (lo, r₁) => (parseChar r₁).map (fun p => (.range lo p.1, p.2))
    | none => none
  | f + 1, 4 :: r => (parseStr f r).map (fun p => (.lit p.1, p.2))
  | f + 1, 5 :: r =>
    match parseE f r with
    | some (a, r₁) => (parseE f r₁).map (fun p => (.seq a p.1, p.2))
    | none => none
  | f + 1, 6 :: r =>
    match parseE f r with
    | some (a, r₁) => (parseE f r₁).map (fun p => (.alt a p.1, p.2))
    | none => none
  | f + 1, 7 :: r => (parseE f r).map (fun p => (.star p.1, p.2))
  | f + 1, 8 :: r => (parseE f r).map (fun p => (.notP p.1, p.2))
  | _ + 1, 9 :: r => (parseNat r).map (fun p => (.var p.1, p.2))
  | _ + 1, 10 :: r => (parseNat r).map (fun p => (.rule p.1, p.2))
  | f + 1, 11 :: r =>
    match parseTy f r with
    | some (τ, r₁) => (parseE f r₁).map (fun p => (.lam τ p.1, p.2))
    | none => none
  | f + 1, 12 :: r =>
    match parseE f r with
    | some (a, r₁) => (parseE f r₁).map (fun p => (.app a p.1, p.2))
    | none => none
  | _, _ => none

def parseRules : Nat → List Nat → Option (List HRule × List Nat)
  | _, 0 :: r => some ([], r)
  | f + 1, 1 :: r =>
    match parseTy f r with
    | some (τ, r₁) =>
      match parseE f r₁ with
      | some (e, r₂) => (parseRules f r₂).map (fun p => (⟨τ, e⟩ :: p.1, p.2))
      | none => none
    | none => none
  | _, _ => none

/-- Read an instance; the fuel is the input length. -/
def deser (l : List Nat) : Option (HGrammar × HExp × List Char) :=
  match parseRules l.length l with
  | some (rs, l₁) =>
    match parseE l.length l₁ with
    | some (s, l₂) =>
      match parseStr l.length l₂ with
      | some (x, []) => some (⟨rs⟩, s, x)
      | _ => none
    | none => none
  | none => none

/-! ## Serialized values are read back -/

theorem length_serNat : ∀ n : Nat, (serNat n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [serNat, length_serNat n]

theorem length_serStr_pos : ∀ s : List Char, 1 ≤ (serStr s).length
  | [] => by simp [serStr]
  | _ :: _ => by simp [serStr]

theorem length_serTy_pos (τ : HO.Ty) : 1 ≤ (serTy τ).length := by cases τ <;> simp [serTy]

theorem length_serE_pos (e : HExp) : 1 ≤ (serE e).length := by cases e <;> simp [serE]

theorem parseNat_ser : ∀ (n : Nat) (r : List Nat), parseNat (serNat n ++ r) = some (n, r)
  | 0, _ => rfl
  | n + 1, r => by simp [serNat, parseNat, parseNat_ser n r]

theorem parseChar_ser (c : Char) (r : List Nat) : parseChar (serChar c ++ r) = some (c, r) := by
  simp [parseChar, serChar, parseNat_ser, Char.ofNat_toNat]

theorem parseStr_ser : ∀ (s : List Char) (r : List Nat) (f : Nat), (serStr s).length ≤ f + 1 →
    parseStr f (serStr s ++ r) = some (s, r)
  | [], r, f, _ => by simp [serStr, parseStr]
  | c :: s, r, f, h => by
    have h₁ : (serChar c).length = c.toNat + 1 := length_serNat _
    simp only [serStr, List.length_cons, List.length_append] at h
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [serStr, List.cons_append, List.append_assoc, parseStr, parseChar_ser]
    rw [parseStr_ser s r f (by omega)]
    rfl

theorem parseTy_ser : ∀ (τ : HO.Ty) (r : List Nat) (f : Nat), (serTy τ).length ≤ f →
    parseTy f (serTy τ ++ r) = some (τ, r)
  | .p, r, f, h => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serTy] at h; omega⟩
    rfl
  | .arr a b, r, f, h => by
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serTy] at h; omega⟩
    simp only [serTy, List.length_cons, List.length_append] at h
    simp only [serTy, List.cons_append, List.append_assoc, parseTy]
    rw [parseTy_ser a _ f (by omega)]; simp only; rw [parseTy_ser b r f (by omega)]
    rfl

theorem parseE_ser : ∀ (e : HExp) (r : List Nat) (f : Nat), (serE e).length ≤ f →
    parseE f (serE e ++ r) = some (e, r) := by
  intro e
  induction e with
  | eps | any => intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩; rfl
  | chr c =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp [serE, parseE, parseChar_ser]
  | range lo hi =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp [serE, parseE, parseChar_ser]
  | lit s =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp only [serE, List.length_cons] at h
    simp only [serE, List.cons_append, parseE]
    rw [parseStr_ser s r f (by omega)]; rfl
  | seq a b iha ihb | alt a b iha ihb | app a b iha ihb =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp only [serE, List.length_cons, List.length_append] at h
    simp only [serE, List.cons_append, List.append_assoc, parseE]
    rw [iha _ f (by omega)]; simp only; rw [ihb r f (by omega)]; rfl
  | star a ih | notP a ih =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp only [serE, List.length_cons] at h
    simp only [serE, List.cons_append, parseE]
    rw [ih r f (by omega)]; rfl
  | var i | rule i =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp [serE, parseE, parseNat_ser]
  | lam τ b ih =>
    intro r f h; obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [serE] at h; omega⟩
    simp only [serE, List.length_cons, List.length_append] at h
    simp only [serE, List.cons_append, List.append_assoc, parseE]
    rw [parseTy_ser τ _ f (by omega)]; simp only; rw [ih r f (by omega)]; rfl

theorem parseRules_ser : ∀ (rs : List HRule) (r : List Nat) (f : Nat), (serRules rs).length ≤ f + 1 →
    parseRules f (serRules rs ++ r) = some (rs, r)
  | [], r, f, _ => by simp [serRules, parseRules]
  | ⟨τ, e⟩ :: rs, r, f, h => by
    have h₁ := length_serTy_pos τ
    have h₂ := length_serE_pos e
    simp only [serRules, List.length_cons, List.length_append] at h
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [serRules, List.cons_append, List.append_assoc, parseRules]
    rw [parseTy_ser τ _ f (by omega)]; simp only; rw [parseE_ser e _ f (by omega)]; simp only
    rw [parseRules_ser rs r f (by omega)]
    rfl

/-- **A serialized instance is read back.** -/
theorem deser_serIn (g : HGrammar) (s : HExp) (x : List Char) : deser (serIn g s x) = some (g, s, x) := by
  unfold deser
  rw [show serIn g s x = serRules g.rules ++ (serE s ++ serStr x) from rfl]
  generalize hF : (serRules g.rules ++ (serE s ++ serStr x)).length = F
  simp only [List.length_append] at hF
  have h₁ := length_serE_pos s
  have h₂ := length_serStr_pos x
  rw [parseRules_ser _ _ _ (by omega)]
  simp only
  rw [parseE_ser s _ _ (by omega)]
  simp only
  have h₃ := parseStr_ser x [] F (by omega)
  rw [List.append_nil] at h₃
  rw [h₃]

/-! ## What is read back serializes to the input -/

theorem parseNat_sound : ∀ {l : List Nat} {n : Nat} {r : List Nat}, parseNat l = some (n, r) → l = serNat n ++ r
  | 0 :: _, _, _, h => by simp only [parseNat, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | 1 :: l, n, r, h => by
    simp only [parseNat, Option.map_eq_some_iff] at h
    obtain ⟨⟨m, r'⟩, hm, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [parseNat_sound hm]; rfl
  | [], _, _, h | (_ + 2) :: _, _, _, h => by simp [parseNat] at h

theorem parseChar_sound {l : List Nat} {c : Char} {r : List Nat} (h : parseChar l = some (c, r)) :
    l = serChar c ++ r := by
  unfold parseChar at h
  split at h
  · rename_i n r' hn
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [parseNat_sound hn, serChar, hc]
    · cases h
  · cases h

theorem parseStr_sound : ∀ {f : Nat} {l : List Nat} {s : List Char} {r : List Nat},
    parseStr f l = some (s, r) → l = serStr s ++ r
  | _, 0 :: _, _, _, h => by
    simp only [parseStr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | f + 1, 1 :: l, s, r, h => by
    simp only [parseStr] at h
    split at h
    · rename_i c r₁ hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s', r'⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [parseChar_sound hc, parseStr_sound hs]
      simp [serStr]
    · cases h
  | 0, 1 :: _, _, _, h | _, [], _, _, h | _, (_ + 2) :: _, _, _, h => by simp [parseStr] at h

theorem parseTy_sound : ∀ {f : Nat} {l : List Nat} {τ : HO.Ty} {r : List Nat},
    parseTy f l = some (τ, r) → l = serTy τ ++ r
  | _ + 1, 0 :: _, _, _, h => by
    simp only [parseTy, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | f + 1, 1 :: l, τ, r, h => by
    simp only [parseTy] at h
    split at h
    · rename_i a r₁ ha
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨b, r'⟩, hb, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [parseTy_sound ha, parseTy_sound hb]
      simp [serTy]
    · cases h
  | 0, _, _, _, h | _ + 1, [], _, _, h | _ + 1, (_ + 2) :: _, _, _, h => by simp [parseTy] at h

theorem one_sound {α : Type} {p : List Nat → Option (α × List Nat)} {sa : α → List Nat}
    (hp : ∀ {l a r}, p l = some (a, r) → l = sa a ++ r) {l : List Nat} {c : α → HExp} {e : HExp} {r : List Nat}
    (h : (p l).map (fun x => (c x.1, x.2)) = some (e, r)) : ∃ a, e = c a ∧ l = sa a ++ r := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨a, r'⟩, ha, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨a, rfl, hp ha⟩

theorem parseE_sound : ∀ {f : Nat} {l : List Nat} {e : HExp} {r : List Nat},
    parseE f l = some (e, r) → l = serE e ++ r
  | 0, _, _, _, h => by simp [parseE] at h
  | _ + 1, [], _, _, h => by simp [parseE] at h
  | f + 1, t :: l, e, r, h => by
    match t, h with
    | 0, h | 1, h =>
      simp only [parseE, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
    | 2, h =>
      obtain ⟨a, rfl, rfl⟩ := one_sound (sa := serChar) parseChar_sound h; rfl
    | 3, h =>
      simp only [parseE] at h
      split at h
      · rename_i a r₁ ha
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [parseChar_sound ha, parseChar_sound hb]; simp [serE]
      · cases h
    | 4, h =>
      obtain ⟨a, rfl, rfl⟩ := one_sound (sa := serStr) parseStr_sound h; rfl
    | 5, h | 6, h | 12, h =>
      simp only [parseE] at h
      split at h
      · rename_i a r₁ ha
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [parseE_sound ha, parseE_sound hb]; simp [serE]
      · cases h
    | 7, h | 8, h =>
      obtain ⟨a, rfl, rfl⟩ := one_sound (sa := serE) parseE_sound h; rfl
    | 9, h | 10, h =>
      obtain ⟨a, rfl, rfl⟩ := one_sound (sa := serNat) parseNat_sound h; rfl
    | 11, h =>
      simp only [parseE] at h
      split at h
      · rename_i a r₁ ha
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [parseTy_sound ha, parseE_sound hb]; simp [serE]
      · cases h
    | _ + 13, h => simp [parseE] at h

theorem parseRules_sound : ∀ {f : Nat} {l : List Nat} {rs : List HRule} {r : List Nat},
    parseRules f l = some (rs, r) → l = serRules rs ++ r
  | _, 0 :: _, _, _, h => by
    simp only [parseRules, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | f + 1, 1 :: l, rs, r, h => by
    simp only [parseRules] at h
    split at h
    · rename_i τ r₁ hτ
      split at h
      · rename_i e r₂ he
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨rs', r'⟩, hrs, hh⟩ := h
        simp only [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        rw [parseTy_sound hτ, parseE_sound he, parseRules_sound hrs]
        simp [serRules]
      · cases h
    · cases h
  | 0, 1 :: _, _, _, h | _, [], _, _, h | _, (_ + 2) :: _, _, _, h => by simp [parseRules] at h

/-- **What is read back serializes to the input.** -/
theorem deser_sound {l : List Nat} {g : HGrammar} {s : HExp} {x : List Char} (h : deser l = some (g, s, x)) :
    l = serIn g s x := by
  unfold deser at h
  split at h
  · rename_i rs l₁ h₁
    split at h
    · rename_i s' l₂ h₂
      split at h
      · rename_i x' h₃
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [parseRules_sound h₁, parseE_sound h₂, parseStr_sound h₃]
        simp [serIn]
      · cases h
    · cases h
  · cases h

end Shallot.MacroPeg.Flat
