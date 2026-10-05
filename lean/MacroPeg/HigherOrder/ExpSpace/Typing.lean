import MacroPeg.HigherOrder.ExpSpace.Sim

/-!
# The simulating grammar is a well-typed order-2 grammar

Every rule body of `g2 M` has its rule's type (`g2_wellTyped`, for a machine whose transitions stay among its states),
the start expression is a closed parser (`start2_hasTy`), and the largest order of a rule type is `2`
(`g2_order`). So `atm2_reduction` is about the grammars that `HigherOrder/Decide.lean` decides.
-/

namespace Shallot.MacroPeg.ExpSpace

open Shallot.MacroPeg (ATM Dir Kind codeE siteE optY)
open Shallot.MacroPeg.HO

/-- `τ₁ ⇒ … ⇒ τₖ ⇒ σ`. -/
def arrows : List HO.Ty → HO.Ty → HO.Ty
  | [], σ => σ
  | τ :: τs, σ => τ ⇒ arrows τs σ

section Typing

variable {R : List HO.Ty} {Γ : List HO.Ty}

theorem hasTy_peg : ∀ (e : MExp), PegOnly e → HasTy R Γ (emb 0 e) .p
  | .eps, _ => .eps Γ
  | .any, _ => .any Γ
  | .chr c, _ => .chr Γ c
  | .range lo hi, _ => .range Γ lo hi
  | .lit s, _ => .lit Γ s
  | .seq a b, h => .seq (hasTy_peg a h.1) (hasTy_peg b h.2)
  | .alt a b, h => .alt (hasTy_peg a h.1) (hasTy_peg b h.2)
  | .star a, h => .star (hasTy_peg a h)
  | .notP a, h => .notP (hasTy_peg a h)
  | .param _, h | .call _ _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => absurd h id

theorem hasTy_codeE : HasTy R Γ hcodeE .p := hasTy_peg _ peg_codeE
theorem hasTy_siteE : HasTy R Γ hsiteE .p := hasTy_peg _ peg_siteE
theorem hasTy_optY : HasTy R Γ hoptY .p := hasTy_peg _ peg_optY

theorem hasTy_andP {e : HExp} (h : HasTy R Γ e .p) : HasTy R Γ (HExp.andP e) .p := .notP (.notP h)

theorem hasTy_apps : ∀ {f : HExp} {τs : List HO.Ty} {σ : HO.Ty} {as : List HExp}, HasTy R Γ f (arrows τs σ) →
    τs.length = as.length →
    (∀ (i : Nat) (τ : HO.Ty) (a : HExp), τs[i]? = some τ → as[i]? = some a → HasTy R Γ a τ) →
    HasTy R Γ (HExp.apps f as) σ
  | _, [], _, [], hf, _, _ => hf
  | f, τ :: τs, σ, a :: as, hf, hl, ha =>
    hasTy_apps (f := .app f a) (τs := τs) (σ := σ) (as := as) (.app hf (ha 0 τ a rfl rfl)) (by simpa using hl)
      (fun i τ' a' h₁ h₂ => ha (i + 1) τ' a' h₁ h₂)
  | _, [], _, _ :: _, _, hl, _ | _, _ :: _, _, [], _, hl, _ => by simp at hl

theorem hasTy_rcall {i : Nat} {τs : List HO.Ty} {as : List HExp} (hr : R[i]? = some (arrows τs .p))
    (hl : τs.length = as.length)
    (ha : ∀ (i : Nat) (τ : HO.Ty) (a : HExp), τs[i]? = some τ → as[i]? = some a → HasTy R Γ a τ) :
    HasTy R Γ (rcall i as) .p :=
  hasTy_apps (.rule hr) hl ha

theorem hasTy_lamsT : ∀ (τs : List HO.Ty) {Γ : List HO.Ty} {B : HExp} {σ : HO.Ty},
    HasTy R (τs.reverse ++ Γ) B σ → HasTy R Γ (lamsT τs B) (arrows τs σ)
  | [], _, _, _, h => by simpa [lamsT, arrows] using h
  | τ :: τs, Γ, B, σ, h => .lam (hasTy_lamsT τs (Γ := τ :: Γ) (by simpa [List.reverse_cons, List.append_assoc] using h))

theorem hasTy_allChainH : ∀ es : List HExp, (∀ e ∈ es, HasTy R Γ e .p) → HasTy R Γ (allChainH es) .p
  | [], _ => .eps Γ
  | e :: es, h => .seq (hasTy_andP (h e List.mem_cons_self))
      (hasTy_allChainH es (fun e' he => h e' (List.mem_cons_of_mem _ he)))

theorem hasTy_anyChainH : ∀ es : List HExp, (∀ e ∈ es, HasTy R Γ e .p) → HasTy R Γ (anyChainH es) .p
  | [], _ => .notP (.eps Γ)
  | e :: es, h => .alt (h e List.mem_cons_self)
      (hasTy_anyChainH es (fun e' he => h e' (List.mem_cons_of_mem _ he)))

end Typing

section Grammar

variable (M : ATM)


theorem types_getElem? (i : Nat) : (g2 M).types[i]? = ((g2 M).rules[i]?).map HRule.ty := by
  simp [HGrammar.types, List.getElem?_map]

theorem ty_state {q : Nat} (hq : q < M.states) : (g2 M).types[q]? = some (arrows [.p, Ty.p ⇒ Ty.p] .p) := by
  rw [types_getElem?, g2_state M hq]; rfl
theorem ty_eq : (g2 M).types[rEQ M]? = some (arrows [.p, .p] .p) := by rw [types_getElem?, g2_eq M]; rfl
theorem ty_all1 : (g2 M).types[rALL1 M]? = some (arrows [.p] .p) := by rw [types_getElem?, g2_all1 M]; rfl
theorem ty_all0 : (g2 M).types[rALL0 M]? = some (arrows [.p] .p) := by rw [types_getElem?, g2_all0 M]; rfl
theorem ty_sc : (g2 M).types[rSC M]? = some (arrows [.p] .p) := by rw [types_getElem?, g2_sc M]; rfl

variable {M} {Γ : List HO.Ty}

theorem hasTy_rcall1 {i : Nat} (hr : (g2 M).types[i]? = some (arrows [.p] .p)) {a : HExp} (ha : HasTy (g2 M).types Γ a .p) :
    HasTy (g2 M).types Γ (rcall i [a]) .p :=
  hasTy_rcall hr rfl (fun j τ a' h₁ h₂ => by
    cases j with
    | zero => simp at h₁ h₂; rw [← h₁, ← h₂]; exact ha
    | succ j => simp at h₁)

theorem hasTy_rcall2 {i : Nat} {τ₁ τ₂ : HO.Ty} (hr : (g2 M).types[i]? = some (arrows [τ₁, τ₂] .p)) {a b : HExp}
    (ha : HasTy (g2 M).types Γ a τ₁) (hb : HasTy (g2 M).types Γ b τ₂) : HasTy (g2 M).types Γ (rcall i [a, b]) .p :=
  hasTy_rcall hr rfl (fun j τ a' h₁ h₂ => by
    match j with
    | 0 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact ha
    | 1 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact hb
    | _ + 2 => simp at h₁)

theorem hasTy_bit1 {a : HExp} (ha : HasTy (g2 M).types Γ a .p) : HasTy (g2 M).types Γ (bit1 a) .p := .seq ha (.lit Γ _)

theorem hasTy_newSite {B : HExp} (hB : HasTy (g2 M).types Γ B .p) : HasTy (g2 M).types Γ (newSite B) .p :=
  .alt (.seq (hasTy_andP hB) (.seq (.seq hasTy_codeE hasTy_optY) (.lit Γ _)))
    (.seq (.notP hB) (.seq hasTy_codeE hasTy_optY))

theorem hasTy_xorE {P Q : HExp} (hP : HasTy (g2 M).types Γ P .p) (hQ : HasTy (g2 M).types Γ Q .p) : HasTy (g2 M).types Γ (xorE P Q) .p :=
  .alt (.seq (hasTy_andP hP) (.notP hQ)) (.seq (.notP hP) (hasTy_andP hQ))

theorem hasTy_incE {h : HExp} (hh : HasTy (g2 M).types Γ h .p) : HasTy (g2 M).types Γ (incE M h) .p :=
  hasTy_newSite (hasTy_xorE (hasTy_bit1 hh) (.seq hasTy_siteE (hasTy_rcall1 (ty_all1 M) hh)))

theorem hasTy_decE {h : HExp} (hh : HasTy (g2 M).types Γ h .p) : HasTy (g2 M).types Γ (decE M h) .p :=
  hasTy_newSite (hasTy_xorE (hasTy_bit1 hh) (.seq hasTy_siteE (hasTy_rcall1 (ty_all0 M) hh)))

theorem hasTy_bitC (b : Bool) : HasTy (g2 M).types Γ (bitC b) .p := by cases b <;> exact by first | exact .eps Γ | exact .notP (.eps Γ)

/-- The written tape is a function from addresses to tests. -/
theorem hasTy_wrE {Hin Tin : HExp} (hH : HasTy (g2 M).types (.p :: Γ) Hin .p) (hT : HasTy (g2 M).types (.p :: Γ) Tin (Ty.p ⇒ Ty.p))
    (b : Bool) : HasTy (g2 M).types Γ (wrE M Hin Tin b) (Ty.p ⇒ Ty.p) := by
  have hv : HasTy (g2 M).types (.p :: Γ) (.var 0) .p := .var rfl
  have heq := hasTy_rcall2 (ty_eq M) hv hH
  exact .lam (.alt (.seq (hasTy_andP heq) (hasTy_bitC b)) (.seq (.notP heq) (.app hT hv)))

theorem hasTy_brE (hM : M.WF) {q : Nat} {b : Bool} {H Hin Tin : HExp} (hH : HasTy (g2 M).types Γ H .p)
    (hHin : HasTy (g2 M).types (.p :: Γ) Hin .p) (hTin : HasTy (g2 M).types (.p :: Γ) Tin (Ty.p ⇒ Ty.p)) {tr : Nat × Bool × Dir}
    (htr : tr ∈ M.delta q b) : HasTy (g2 M).types Γ (brE M H Hin Tin tr) .p := by
  have hq := hM.2 q b tr htr
  obtain ⟨q', b', d⟩ := tr
  have hw := hasTy_wrE hHin hTin b' (M := M)
  cases d with
  | left =>
    exact .alt (.seq (hasTy_andP (hasTy_rcall1 (ty_all0 M) hH)) (hasTy_rcall2 (ty_state M hq) hH hw))
      (.seq (.notP (hasTy_rcall1 (ty_all0 M) hH)) (hasTy_rcall2 (ty_state M hq) (hasTy_decE hH) hw))
  | right =>
    exact .alt (.seq (hasTy_andP (hasTy_rcall1 (ty_all1 M) hH)) (hasTy_rcall2 (ty_state M hq) hH hw))
      (.seq (.notP (hasTy_rcall1 (ty_all1 M) hH)) (hasTy_rcall2 (ty_state M hq) (hasTy_incE hH) hw))

theorem hasTy_transE (hM : M.WF) (q : Nat) (b : Bool) {H Hin Tin : HExp} (hH : HasTy (g2 M).types Γ H .p)
    (hHin : HasTy (g2 M).types (.p :: Γ) Hin .p) (hTin : HasTy (g2 M).types (.p :: Γ) Tin (Ty.p ⇒ Ty.p)) :
    HasTy (g2 M).types Γ (transE M q b H Hin Tin) .p := by
  unfold transE
  split
  · exact .eps Γ
  · exact .notP (.eps Γ)
  · exact hasTy_allChainH _ (fun e he => by
      obtain ⟨tr, htr, rfl⟩ := List.mem_map.1 he; exact hasTy_brE hM hH hHin hTin htr)
  · exact hasTy_anyChainH _ (fun e he => by
      obtain ⟨tr, htr, rfl⟩ := List.mem_map.1 he; exact hasTy_brE hM hH hHin hTin htr)

/-- **The rules are well typed.** -/
theorem g2_wellTyped (hM : M.WF) : (g2 M).WellTyped := by
  intro r hr
  simp only [g2, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hp : ∀ {Γ : List HO.Ty} {i : Nat}, Γ[i]? = some Ty.p → HasTy (g2 M).types Γ (.var i) .p := fun h => .var h
  rcases hr with ⟨q, hq, rfl⟩ | rfl | rfl | rfl | rfl
  · -- context `[p ⇒ p, p]`: `T = var 0`, `H = var 1`
    apply hasTy_lamsT [.p, Ty.p ⇒ Ty.p]
    have hH : HasTy (g2 M).types [Ty.p ⇒ Ty.p, .p] (.var 1) .p := .var rfl
    have hT : HasTy (g2 M).types [Ty.p ⇒ Ty.p, .p] (.var 0) (Ty.p ⇒ Ty.p) := .var rfl
    have hHin : HasTy (g2 M).types [.p, Ty.p ⇒ Ty.p, .p] (.var 2) .p := .var rfl
    have hTin : HasTy (g2 M).types [.p, Ty.p ⇒ Ty.p, .p] (.var 1) (Ty.p ⇒ Ty.p) := .var rfl
    exact .alt (.seq (hasTy_andP (.app hT hH)) (hasTy_transE hM q true hH hHin hTin))
      (.seq (.notP (.app hT hH)) (hasTy_transE hM q false hH hHin hTin))
  · apply hasTy_lamsT [.p, .p]
    have ha : HasTy (g2 M).types [.p, .p] (.var 1) .p := .var rfl
    have hh : HasTy (g2 M).types [.p, .p] (.var 0) .p := .var rfl
    exact .alt (hasTy_andP (.lit _ _))
      (.seq (.alt (.seq (hasTy_andP (hasTy_bit1 ha)) (hasTy_andP (hasTy_bit1 hh)))
        (.seq (.notP (hasTy_bit1 ha)) (.notP (hasTy_bit1 hh))))
        (.seq hasTy_siteE (hasTy_rcall2 (ty_eq M) ha hh)))
  · apply hasTy_lamsT [.p]
    have hh : HasTy (g2 M).types [.p] (.var 0) .p := .var rfl
    exact .alt (hasTy_andP (.lit _ _)) (.seq (hasTy_andP (hasTy_bit1 hh)) (.seq hasTy_siteE (hasTy_rcall1 (ty_all1 M) hh)))
  · apply hasTy_lamsT [.p]
    have hh : HasTy (g2 M).types [.p] (.var 0) .p := .var rfl
    exact .alt (hasTy_andP (.lit _ _)) (.seq (.notP (hasTy_bit1 hh)) (.seq hasTy_siteE (hasTy_rcall1 (ty_all0 M) hh)))
  · apply hasTy_lamsT [.p]
    have ha : HasTy (g2 M).types [.p] (.var 0) .p := .var rfl
    exact .alt (.seq (hasTy_andP (hasTy_bit1 ha)) (hasTy_andP (.seq hasTy_codeE (.lit _ _))))
      (.seq hasTy_siteE (hasTy_rcall1 (ty_sc M) ha))

/-- The start expression is a closed parser. -/
theorem start2_hasTy (hM : M.WF) : HasTy (g2 M).types [] (start2 M) .p := by
  have hT0 : HasTy (g2 M).types [] (T0 M) (Ty.p ⇒ Ty.p) := .lam (hasTy_andP (hasTy_rcall1 (ty_sc M) (.var rfl)))
  exact .seq (hasTy_rcall2 (ty_state M hM.1) (.seq hasTy_codeE hasTy_optY) hT0) (.star (.any _))

theorem le_foldr_max {a : Nat} : ∀ {l : List Nat}, a ∈ l → a ≤ l.foldr max 0
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

/-- **The grammar has order 2.** -/
theorem g2_order (hM : M.WF) : (g2 M).order = 2 := by
  apply Nat.le_antisymm
  · apply foldr_max_le
    intro a ha
    simp only [g2, List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_range,
      Function.comp, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ⟨q, _, rfl⟩ | rfl | rfl | rfl | rfl <;> decide
  · have hmem : stateTy.order ∈ (g2 M).rules.map (fun r => r.ty.order) := by
      simp only [g2, List.map_append, List.mem_append, List.mem_map, List.mem_range]
      exact .inl ⟨⟨stateTy, _⟩, ⟨M.start, hM.1, rfl⟩, rfl⟩
    exact le_foldr_max hmem

/-- **Order-2 Macro PEG is 2-EXPTIME-hard.** For every machine `M`, `g2 M` is a well-typed grammar of order 2 with a
closed start parser, and on every input on which all branches of `M` halt it consumes the (polynomially long,
`sitesStr_length`) encoding iff `M` accepts with its tape of `2^|w|` cells. With `AEXPSPACE = 2-EXPTIME` (external)
this makes recognition for fixed order-2 grammars 2-EXPTIME-hard. -/
theorem order2_hard (hM : M.WF) :
    (g2 M).WellTyped ∧ (g2 M).order = 2 ∧ HasTy (g2 M).types [] (start2 M) .p ∧
      ∀ w, Halts M (init M w) → (HObs (g2 M) (start2 M) (Shallot.MacroPeg.sitesStr w 0) (some []) ↔ Accepts M w) :=
  ⟨g2_wellTyped hM, g2_order hM, start2_hasTy hM, fun _ hh => atm2_reduction hM hh⟩

end Grammar

end Shallot.MacroPeg.ExpSpace
