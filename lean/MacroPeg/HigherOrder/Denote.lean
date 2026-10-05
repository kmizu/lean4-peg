import MacroPeg.HigherOrder.Domain

/-!
# The meaning of typed terms in the finite model

Fix the input `x`; positions are the lengths `q ≤ |x|` of its suffixes `sfx x q`. Given values `T` for the rules and
`ρ` for the variables, `den x t T ρ` is the value of the typed term `t`:

* a PEG operator is computed position by position from the values of its operands (`seqRes`, `altRes`, `notRes`,
  `starRes`); a leaf (`ε`, `.`, a character, a range, a literal) is run directly;
* a lambda is the table of its body's values on all well-formed (monotone) arguments; an application looks it up.

Rule values are computed by iteration (`iter`): start with no results anywhere, then evaluate every rule body with the
current values. `den_mono` — the meaning is well formed and monotone in `T` and `ρ` — makes the iterates an increasing
chain (`iter_le_succ`). By counting defined entries the chain is constant from `maxEnv x.length R` on
(`iter_stable`): a fixpoint, computed in a number of rounds that is a tower of exponentials in `|x|` whose height is
the order of the grammar.
-/

namespace Shallot.MacroPeg.HO

/-! ## Environments -/

/-- One value per type of `Γ`. -/
def Env : List Ty → Type
  | [] => Unit
  | τ :: Γ => Dom τ × Env Γ

def Env.get : {Γ : List Ty} → Env Γ → (i : Nat) → {τ : Ty} → Γ[i]? = some τ → Dom τ
  | [], _, _, _, h => absurd h (by simp)
  | _ :: _, (d, _), 0, _, h => (Option.some.inj h) ▸ d
  | _ :: _, (_, ρ), i + 1, _, h => Env.get ρ i h

def Env.le : {Γ : List Ty} → Env Γ → Env Γ → Prop
  | [], _, _ => True
  | τ :: _, (d, ρ), (d', ρ') => Dom.le τ d d' ∧ Env.le ρ ρ'

/-- Every value is well formed. -/
def Env.Mem (N : Nat) : {Γ : List Ty} → Env Γ → Prop
  | [], _ => True
  | τ :: _, (d, ρ) => d ∈ elems N τ ∧ Env.Mem N ρ

def Env.bot (N : Nat) : (Γ : List Ty) → Env Γ
  | [] => ()
  | τ :: Γ => (HO.bot N τ, Env.bot N Γ)

def Env.count : {Γ : List Ty} → Env Γ → Nat
  | [], _ => 0
  | τ :: _, (d, ρ) => defCount τ d + Env.count ρ

def maxEnv (N : Nat) : List Ty → Nat
  | [] => 0
  | τ :: Γ => maxCount N τ + maxEnv N Γ

section EnvLemmas

variable {N : Nat}

theorem Env.get_mem : ∀ {Γ : List Ty} {ρ : Env Γ}, Env.Mem N ρ → ∀ (i : Nat) {τ : Ty} (h : Γ[i]? = some τ),
    Env.get ρ i h ∈ elems N τ
  | [], _, _, _, _, h => absurd h (by simp)
  | _ :: _, (_, _), hρ, 0, _, h => by cases Option.some.inj h; exact hρ.1
  | _ :: _, (_, _), hρ, i + 1, _, h => Env.get_mem hρ.2 i h

theorem Env.get_le : ∀ {Γ : List Ty} {ρ ρ' : Env Γ}, Env.le ρ ρ' → ∀ (i : Nat) {τ : Ty} (h : Γ[i]? = some τ),
    Dom.le τ (Env.get ρ i h) (Env.get ρ' i h)
  | [], _, _, _, _, _, h => absurd h (by simp)
  | _ :: _, (_, _), (_, _), hρ, 0, _, h => by cases Option.some.inj h; exact hρ.1
  | _ :: _, (_, _), (_, _), hρ, i + 1, _, h => Env.get_le hρ.2 i h

theorem Env.le_refl : ∀ {Γ : List Ty} (ρ : Env Γ), Env.le ρ ρ
  | [], _ => trivial
  | τ :: _, (d, ρ) => ⟨Dom.le_refl τ d, Env.le_refl ρ⟩

theorem Env.le_trans : ∀ {Γ : List Ty} {ρ₁ ρ₂ ρ₃ : Env Γ}, Env.le ρ₁ ρ₂ → Env.le ρ₂ ρ₃ → Env.le ρ₁ ρ₃
  | [], _, _, _, _, _ => trivial
  | τ :: _, (_, _), (_, _), (_, _), h₁, h₂ => ⟨Dom.le_trans τ _ _ _ h₁.1 h₂.1, Env.le_trans h₁.2 h₂.2⟩

theorem Env.bot_mem : ∀ Γ : List Ty, Env.Mem N (Env.bot N Γ)
  | [] => trivial
  | τ :: Γ => ⟨HO.bot_mem N τ, Env.bot_mem Γ⟩

theorem Env.bot_le : ∀ {Γ : List Ty} {ρ : Env Γ}, Env.Mem N ρ → Env.le (Env.bot N Γ) ρ
  | [], _, _ => trivial
  | τ :: _, (d, _), h => ⟨HO.bot_le N τ d h.1, Env.bot_le h.2⟩

theorem Env.count_le : ∀ {Γ : List Ty} {ρ : Env Γ}, Env.Mem N ρ → Env.count ρ ≤ maxEnv N Γ
  | [], _, _ => Nat.le_refl _
  | τ :: _, (d, _), h => by
    have := defCount_le_maxCount N τ d h.1
    have := Env.count_le h.2
    simp only [Env.count, maxEnv]; omega

theorem Env.count_mono : ∀ {Γ : List Ty} {ρ ρ' : Env Γ}, Env.le ρ ρ' → Env.count ρ ≤ Env.count ρ'
  | [], _, _, _ => Nat.le_refl _
  | τ :: _, (_, _), (_, _), h => by
    have := defCount_mono τ h.1
    have := Env.count_mono h.2
    simp only [Env.count]; omega

theorem Env.count_lt : ∀ {Γ : List Ty} {ρ ρ' : Env Γ}, Env.le ρ ρ' → ρ ≠ ρ' → Env.count ρ < Env.count ρ'
  | [], _, _, _, hne => absurd rfl hne
  | τ :: _, (d, ρ), (d', ρ'), h, hne => by
    simp only [Env.count]
    have h₁ := defCount_mono τ h.1
    have h₂ := Env.count_mono h.2
    by_cases hd : d = d'
    · subst hd
      have : ρ ≠ ρ' := fun e => hne (by rw [e])
      have := Env.count_lt h.2 this
      omega
    · have := defCount_lt τ h.1 hd
      omega

end EnvLemmas

/-! ## Parsers position by position -/

section Positions

variable (x : List Char)

/-- The suffix of `x` with `q` symbols. -/
def sfx (q : Nat) : List Char := x.drop (x.length - q)

/-- A parser value from its result at each position `0, …, |x|`. -/
def baseVec (f : Nat → Res) : Dom .p := (List.range (x.length + 1)).map f

/-- The result at position `q`. -/
def atq (d : Dom .p) (q : Nat) : Res := (d : List Res).getD q none

/-- A leaf (`ε`, `.`, a character, a range, a literal) run once at position `q`. -/
def leafRes (e : HExp) (q : Nat) : Res := (hrun ⟨[]⟩ 1 e (sfx x q)).map (Option.map List.length)

end Positions

def seqRes (da db : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some (some j) => atq db j
  | r => r

def altRes (da db : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some none => atq db q
  | r => r

def notRes (da : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some (some _) => some none
  | some none => some (some q)
  | none => none

/-- `a*` at position `q`: repeat while `a` succeeds and consumes; a zero-width success loops forever (no result). -/
def starRes (da : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some (some j) => if j < q then starRes da j else none
  | some none => some (some q)
  | none => none
termination_by q

/-! ## Well-formedness and monotonicity of position-wise operators -/

section Ops

variable {x : List Char}

/-- `r` carries no more information than `s`. -/
def ResLe (r s : Res) : Prop := r = none ∨ r = s

theorem mem_resElems {N : Nat} {r : Res} : r ∈ resElems N ↔ r = none ∨ r = some none ∨ ∃ j ≤ N, r = some (some j) := by
  simp only [resElems, List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro (h | h | ⟨j, hj, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨j, by omega, rfl⟩)
  · rintro (h | h | ⟨j, hj, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨j, by omega, rfl⟩)

theorem pw_map {α β : Type} {R : β → β → Prop} {f g : α → β} :
    ∀ l : List α, (∀ a ∈ l, R (f a) (g a)) → Pw R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (pw_map l (fun b hb => h b (by simp [hb])))

theorem baseVec_mem {f : Nat → Res} (h : ∀ q ≤ x.length, f q ∈ resElems x.length) :
    baseVec x f ∈ elems x.length .p := by
  refine (mem_allVecs _ _ _).2 ⟨by simp [baseVec], fun r hr => ?_⟩
  simp only [baseVec, List.mem_map, List.mem_range] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  exact h q (by omega)

theorem baseVec_le {f f' : Nat → Res} (h : ∀ q, ResLe (f q) (f' q)) : Dom.le .p (baseVec x f) (baseVec x f') :=
  pw_map _ (fun q _ => h q)

theorem atq_mem {N : Nat} {d : Dom .p} (hd : d ∈ elems N .p) (q : Nat) : atq d q ∈ resElems N :=
  getD_mem (P := (· ∈ resElems N)) (by simp [resElems]) _ _ ((mem_allVecs _ _ _).1 hd).2

theorem atq_le {d d' : Dom .p} (h : Dom.le .p d d') (q : Nat) : ResLe (atq d q) (atq d' q) :=
  pw_getD (R := ResLe) (.inl rfl) h q

theorem sfx_length_le (q : Nat) : (sfx x q).length ≤ x.length := by simp [sfx]

theorem leafRes_mem (e : HExp) {q : Nat} : leafRes x e q ∈ resElems x.length := by
  unfold leafRes
  cases h : hrun ⟨[]⟩ 1 e (sfx x q) with
  | none => simp [resElems]
  | some r =>
    cases r with
    | none => simp [resElems]
    | some rest =>
      obtain ⟨p, hp⟩ := hrun_suffix h
      have : rest.length ≤ (sfx x q).length := by rw [hp]; simp
      have := sfx_length_le (x := x) q
      exact mem_resElems.2 (.inr (.inr ⟨rest.length, by omega, rfl⟩))

theorem none_mem_resElems (N : Nat) : (none : Res) ∈ resElems N := by simp [resElems]
theorem fail_mem_resElems (N : Nat) : (some none : Res) ∈ resElems N := by simp [resElems]

theorem seqRes_mem {N : Nat} (da : Dom .p) {db : Dom .p} (hb : db ∈ elems N .p) (q : Nat) :
    seqRes da db q ∈ resElems N := by
  unfold seqRes
  cases hv : atq da q with
  | none => exact none_mem_resElems N
  | some r => cases r with
    | none => exact fail_mem_resElems N
    | some j => exact atq_mem hb j

theorem altRes_mem {N : Nat} {da db : Dom .p} (ha : da ∈ elems N .p) (hb : db ∈ elems N .p) (q : Nat) :
    altRes da db q ∈ resElems N := by
  unfold altRes
  have h := atq_mem ha q
  cases hv : atq da q with
  | none => exact none_mem_resElems N
  | some r => cases r with
    | none => exact atq_mem hb q
    | some j => rw [hv] at h; exact h

theorem notRes_mem {N : Nat} {da : Dom .p} {q : Nat} (hq : q ≤ N) : notRes da q ∈ resElems N := by
  unfold notRes
  cases atq da q with
  | none => exact none_mem_resElems N
  | some r => cases r with
    | none => exact mem_resElems.2 (.inr (.inr ⟨q, hq, rfl⟩))
    | some j => exact fail_mem_resElems N

theorem starRes_mem {N : Nat} (da : Dom .p) : ∀ q ≤ N, starRes da q ∈ resElems N := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro hq
    rw [starRes]
    split
    · split
      · exact ih _ (by assumption) (by omega)
      · simp [resElems]
    · exact mem_resElems.2 (.inr (.inr ⟨q, hq, rfl⟩))
    · simp [resElems]

theorem seqRes_le {da db da' db' : Dom .p} (ha : Dom.le .p da da') (hb : Dom.le .p db db') (q : Nat) :
    ResLe (seqRes da db q) (seqRes da' db' q) := by
  unfold seqRes
  rcases atq_le ha q with h | h
  · rw [h]; exact .inl rfl
  · rw [← h]; split
    · exact atq_le hb _
    · exact .inr rfl

theorem altRes_le {da db da' db' : Dom .p} (ha : Dom.le .p da da') (hb : Dom.le .p db db') (q : Nat) :
    ResLe (altRes da db q) (altRes da' db' q) := by
  unfold altRes
  rcases atq_le ha q with h | h
  · rw [h]; exact .inl rfl
  · rw [← h]; split
    · exact atq_le hb _
    · exact .inr rfl

theorem notRes_le {da da' : Dom .p} (ha : Dom.le .p da da') (q : Nat) : ResLe (notRes da q) (notRes da' q) := by
  unfold notRes
  rcases atq_le ha q with h | h
  · rw [h]; exact .inl rfl
  · rw [← h]; exact .inr rfl

theorem starRes_le {da da' : Dom .p} (ha : Dom.le .p da da') : ∀ q, ResLe (starRes da q) (starRes da' q) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    rw [starRes, starRes]
    rcases atq_le ha q with h | h
    · rw [h]; exact .inl rfl
    · rw [← h]; split
      · split
        · exact ih _ (by assumption)
        · exact .inr rfl
      · exact .inr rfl
      · exact .inr rfl

end Ops

/-! ## The meaning of a term -/

/-- The value of `t` given rule values `T` and variable values `ρ`, on the input `x`. -/
def den (x : List Char) {R : List Ty} : {Γ : List Ty} → {τ : Ty} → Tm R Γ τ → Env R → Env Γ → Dom τ
  | _, _, .eps, _, _ => baseVec x (leafRes x .eps)
  | _, _, .any, _, _ => baseVec x (leafRes x .any)
  | _, _, .chr c, _, _ => baseVec x (leafRes x (.chr c))
  | _, _, .range lo hi, _, _ => baseVec x (leafRes x (.range lo hi))
  | _, _, .lit s, _, _ => baseVec x (leafRes x (.lit s))
  | _, _, .seq a b, T, ρ => baseVec x (seqRes (den x a T ρ) (den x b T ρ))
  | _, _, .alt a b, T, ρ => baseVec x (altRes (den x a T ρ) (den x b T ρ))
  | _, _, .star a, T, ρ => baseVec x (starRes (den x a T ρ))
  | _, _, .notP a, T, ρ => baseVec x (notRes (den x a T ρ))
  | _, _, .var i h, _, ρ => Env.get ρ i h
  | _, _, .rule i h, T, _ => Env.get T i h
  | _, _, @Tm.lam _ _ a _ body, T, ρ => (elems x.length a).map (fun d => den x body T (d, ρ))
  | _, _, .app f y, T, ρ => Dom.app (N := x.length) (den x f T ρ) (den x y T ρ)

/-- The rule bodies evaluated with rule values `T`. -/
def TBodies.den (x : List Char) {R : List Ty} : {S : List Ty} → TBodies R S → Env R → Env S
  | [], _, _ => ()
  | _ :: _, (t, ts), T => (HO.den x t T (), TBodies.den x ts T)

/-- The iterates: no results anywhere, then the bodies evaluated with the previous iterate. -/
def iter (x : List Char) {R : List Ty} (G : TGrammar R) : Nat → Env R
  | 0 => Env.bot x.length R
  | m + 1 => G.bodies.den x (iter x G m)

/-! ## The meaning is well formed and monotone -/

theorem mem_zip_map {α β : Type} {g : α → β} : ∀ {l : List α} {p : α × β}, p ∈ l.zip (l.map g) → p.1 ∈ l ∧ p.2 = g p.1
  | [], _, h => by simp at h
  | a :: l, p, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨by simp, rfl⟩
    · obtain ⟨h₁, h₂⟩ := mem_zip_map h
      exact ⟨by simp [h₁], h₂⟩

/-- **Monotonicity**: with well-formed rule and variable values, the meaning of a term is well formed, and larger
rule and variable values give a larger meaning. -/
theorem den_mono (x : List Char) {R : List Ty} : ∀ {Γ : List Ty} {τ : Ty} (t : Tm R Γ τ) {T T' : Env R}
    {ρ ρ' : Env Γ}, Env.Mem x.length T → Env.Mem x.length T' → Env.le T T' →
    Env.Mem x.length ρ → Env.Mem x.length ρ' → Env.le ρ ρ' →
    den x t T ρ ∈ elems x.length τ ∧ Dom.le τ (den x t T ρ) (den x t T' ρ')
  | _, _, .eps, _, _, _, _, _, _, _, _, _, _
  | _, _, .any, _, _, _, _, _, _, _, _, _, _
  | _, _, .chr _, _, _, _, _, _, _, _, _, _, _
  | _, _, .range _ _, _, _, _, _, _, _, _, _, _, _
  | _, _, .lit _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨baseVec_mem (fun _ _ => leafRes_mem _), Dom.le_refl _ _⟩
  | _, _, .seq a b, _, _, _, _, hT, hT', hTT, hρ, hρ', hρρ => by
    have ha := den_mono x a hT hT' hTT hρ hρ' hρρ
    have hb := den_mono x b hT hT' hTT hρ hρ' hρρ
    exact ⟨baseVec_mem (fun q _ => seqRes_mem _ hb.1 q), baseVec_le (seqRes_le ha.2 hb.2)⟩
  | _, _, .alt a b, _, _, _, _, hT, hT', hTT, hρ, hρ', hρρ => by
    have ha := den_mono x a hT hT' hTT hρ hρ' hρρ
    have hb := den_mono x b hT hT' hTT hρ hρ' hρρ
    exact ⟨baseVec_mem (fun q _ => altRes_mem ha.1 hb.1 q), baseVec_le (altRes_le ha.2 hb.2)⟩
  | _, _, .star a, _, _, _, _, hT, hT', hTT, hρ, hρ', hρρ => by
    have ha := den_mono x a hT hT' hTT hρ hρ' hρρ
    exact ⟨baseVec_mem (fun q hq => starRes_mem _ q hq), baseVec_le (starRes_le ha.2)⟩
  | _, _, .notP a, _, _, _, _, hT, hT', hTT, hρ, hρ', hρρ => by
    have ha := den_mono x a hT hT' hTT hρ hρ' hρρ
    exact ⟨baseVec_mem (fun _ hq => notRes_mem hq), baseVec_le (notRes_le ha.2)⟩
  | _, _, .var i h, _, _, _, _, _, _, _, hρ, _, hρρ => ⟨Env.get_mem hρ i h, Env.get_le hρρ i h⟩
  | _, _, .rule i h, _, _, _, _, hT, _, hTT, _, _, _ => ⟨Env.get_mem hT i h, Env.get_le hTT i h⟩
  | _, _, @Tm.lam _ _ a b body, T, T', ρ, ρ', hT, hT', hTT, hρ, hρ', hρρ => by
    have hbody : ∀ {d d' : Dom a}, d ∈ elems x.length a → d' ∈ elems x.length a → Dom.le a d d' →
        den x body T (d, ρ) ∈ elems x.length b ∧ Dom.le b (den x body T (d, ρ)) (den x body T (d', ρ)) :=
      fun hd hd' hdd => den_mono x body hT hT (Env.le_refl T) ⟨hd, hρ⟩ ⟨hd', hρ⟩ ⟨hdd, Env.le_refl ρ⟩
    refine ⟨mem_elems_arr.2 ⟨(mem_allVecs _ _ _).2 ⟨by simp [den], fun v hv => ?_⟩, ?_⟩, ?_⟩
    · simp only [den, List.mem_map] at hv
      obtain ⟨d, hd, rfl⟩ := hv
      exact (hbody hd hd (Dom.le_refl a d)).1
    · intro p hp p' hp' hle
      obtain ⟨h₁, e₁⟩ := mem_zip_map hp
      obtain ⟨h₂, e₂⟩ := mem_zip_map hp'
      rw [e₁, e₂]
      exact (hbody h₁ h₂ hle).2
    · exact pw_map _ (fun d hd =>
        (den_mono x body hT hT' hTT ⟨hd, hρ⟩ ⟨hd, hρ'⟩ ⟨Dom.le_refl a d, hρρ⟩).2)
  | _, _, .app f y, T, T', ρ, ρ', hT, hT', hTT, hρ, hρ', hρρ => by
    have hf := den_mono x f hT hT' hTT hρ hρ' hρρ
    have hy := den_mono x y hT hT' hTT hρ hρ' hρρ
    have hy' := den_mono x y hT' hT' (Env.le_refl T') hρ' hρ' (Env.le_refl ρ')
    exact ⟨app_mem hf.1 _, Dom.le_trans _ _ _ _ (app_mono_arg hf.1 hy.1 hy'.1 hy.2) (app_le_fun hf.2 _)⟩

/-! ## The iterates form an increasing chain that stops -/

section Iterates

variable (x : List Char) {R : List Ty} (G : TGrammar R)

theorem TBodies.den_mono : ∀ {S : List Ty} (ts : TBodies R S) {T T' : Env R},
    Env.Mem x.length T → Env.Mem x.length T' → Env.le T T' →
    Env.Mem x.length (ts.den x T) ∧ Env.le (ts.den x T) (ts.den x T')
  | [], _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | _ :: _, (t, ts), _, _, hT, hT', hTT => by
    have h₁ := HO.den_mono x t hT hT' hTT (ρ := ()) (ρ' := ()) trivial trivial trivial
    have h₂ := TBodies.den_mono ts hT hT' hTT
    exact ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩

theorem iter_mem : ∀ m, Env.Mem x.length (iter x G m)
  | 0 => Env.bot_mem R
  | m + 1 => (TBodies.den_mono x G.bodies (iter_mem m) (iter_mem m) (Env.le_refl _)).1

theorem iter_le_succ : ∀ m, Env.le (iter x G m) (iter x G (m + 1))
  | 0 => Env.bot_le (iter_mem x G 1)
  | m + 1 => (TBodies.den_mono x G.bodies (iter_mem x G m) (iter_mem x G (m + 1)) (iter_le_succ m)).2

/-- Once two consecutive iterates agree, the iterates stay there. -/
theorem iter_const {m : Nat} (h : iter x G m = iter x G (m + 1)) : ∀ k, m ≤ k → iter x G k = iter x G m := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => rfl
  | succ d ih =>
    show G.bodies.den x (iter x G (m + d)) = _
    rw [ih (by omega)]; exact h.symm

/-- Some iterate up to `maxEnv` equals the next one: otherwise every step adds a defined entry. -/
theorem exists_iter_eq : ∃ m ≤ maxEnv x.length R, iter x G m = iter x G (m + 1) := by
  apply Classical.byContradiction
  intro hno
  have hgrow : ∀ m ≤ maxEnv x.length R + 1, m ≤ Env.count (iter x G m) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have hne : iter x G m ≠ iter x G (m + 1) := fun he => hno ⟨m, by omega, he⟩
      have := Env.count_lt (iter_le_succ x G m) hne
      have := ih (by omega)
      omega
  have h₁ := hgrow (maxEnv x.length R + 1) (Nat.le_refl _)
  have h₂ := Env.count_le (iter_mem x G (maxEnv x.length R + 1))
  omega

/-- **The iterates stop**: from `maxEnv |x| R` on they are all equal. -/
theorem iter_stable : ∀ k, maxEnv x.length R ≤ k → iter x G k = iter x G (maxEnv x.length R) := by
  obtain ⟨m, hm, he⟩ := exists_iter_eq x G
  intro k hk
  rw [iter_const x G he k (by omega), iter_const x G he _ hm]

/-- The stopped iterate is a fixpoint: evaluating the bodies with it gives it back. -/
theorem iter_fix : G.bodies.den x (iter x G (maxEnv x.length R)) = iter x G (maxEnv x.length R) :=
  iter_stable x G (maxEnv x.length R + 1) (by omega)

end Iterates

end Shallot.MacroPeg.HO
