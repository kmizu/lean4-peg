import MacroPeg.HigherOrder.KExp.Uniform

/-!
# The tableau grammar has no lambdas in its bodies

Every rule of `gT M K` is `lamsT τs B` with a lambda-free body `B` (`LF`), so its lambdas are its parameters and
`lamOrd` of the rule is at most the order of its type (`lamOrd_lamsT`), hence at most `K + 1` (`gT_lamOrd`). The start
has no lambda. So `gT M K` satisfies the order condition of the uniform problem (`gT_GOrd`).
-/

namespace Shallot.MacroPeg.KExp

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.Tableau
open Shallot.MacroPeg.ExpSpace (rcall allChainH anyChainH hcodeE hsiteE hoptY hsemi bitC bit1 xorE newSite
  peg_siteE peg_codeE peg_optY arrows)

/-- No lambda. -/
def LF (e : HExp) : Prop := lamOrd e = 0

theorem max_zero {a b : Nat} : max a b = 0 ↔ a = 0 ∧ b = 0 := by omega

theorem lf_seq {a b : HExp} (ha : LF a) (hb : LF b) : LF (.seq a b) := by simp_all [LF, lamOrd]
theorem lf_alt {a b : HExp} (ha : LF a) (hb : LF b) : LF (.alt a b) := by simp_all [LF, lamOrd]
theorem lf_app {a b : HExp} (ha : LF a) (hb : LF b) : LF (.app a b) := by simp_all [LF, lamOrd]
theorem lf_star {a : HExp} (ha : LF a) : LF (.star a) := by simp_all [LF, lamOrd]
theorem lf_notP {a : HExp} (ha : LF a) : LF (.notP a) := by simp_all [LF, lamOrd]
theorem lf_eps : LF .eps := rfl
theorem lf_any : LF .any := rfl
theorem lf_lit (s : List Char) : LF (.lit s) := rfl
theorem lf_var (i : Nat) : LF (.var i) := rfl
theorem lf_rule (i : Nat) : LF (.rule i) := rfl
theorem lf_andP {a : HExp} (ha : LF a) : LF (HExp.andP a) := lf_notP (lf_notP ha)
theorem lf_fail : LF HExp.failAlways := rfl

theorem lf_apps : ∀ {f : HExp} {as : List HExp}, LF f → (∀ a ∈ as, LF a) → LF (HExp.apps f as)
  | _, [], hf, _ => hf
  | f, a :: as, hf, h =>
    lf_apps (f := .app f a) (as := as) (lf_app hf (h a List.mem_cons_self))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem lf_rcall {i : Nat} {as : List HExp} (h : ∀ a ∈ as, LF a) : LF (rcall i as) := lf_apps (lf_rule i) h

theorem lf_rcall1 {i : Nat} {a : HExp} (h : LF a) : LF (rcall i [a]) := lf_rcall (by simpa using h)
theorem lf_rcall2 {i : Nat} {a b : HExp} (ha : LF a) (hb : LF b) : LF (rcall i [a, b]) :=
  lf_rcall (by simp [ha, hb])
theorem lf_rcall3 {i : Nat} {a b c : HExp} (ha : LF a) (hb : LF b) (hc : LF c) : LF (rcall i [a, b, c]) :=
  lf_rcall (by simp [ha, hb, hc])

theorem lf_emb_peg : ∀ e : Shallot.MacroPeg.MExp, PegOnly e → LF (emb 0 e)
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
  | .seq a b, h => lf_seq (lf_emb_peg a h.1) (lf_emb_peg b h.2)
  | .alt a b, h => lf_alt (lf_emb_peg a h.1) (lf_emb_peg b h.2)
  | .star a, h => lf_star (lf_emb_peg a h)
  | .notP a, h => lf_notP (lf_emb_peg a h)
  | .param _, h | .call _ _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => by
    simp [PegOnly] at h

theorem lf_codeE : LF hcodeE := lf_emb_peg _ peg_codeE
theorem lf_siteE : LF hsiteE := lf_emb_peg _ peg_siteE
theorem lf_optY : LF hoptY := lf_emb_peg _ peg_optY

theorem lf_bit1 {a : HExp} (ha : LF a) : LF (bit1 a) := lf_seq ha (lf_lit _)
theorem lf_bitC (b : Bool) : LF (bitC b) := by cases b <;> rfl
theorem lf_xorE {a b : HExp} (ha : LF a) (hb : LF b) : LF (xorE a b) :=
  lf_alt (lf_seq (lf_andP ha) (lf_notP hb)) (lf_seq (lf_notP ha) (lf_andP hb))
theorem lf_newSite {a : HExp} (ha : LF a) : LF (newSite a) :=
  lf_alt (lf_seq (lf_andP ha) (lf_seq (lf_seq lf_codeE lf_optY) (lf_lit _)))
    (lf_seq (lf_notP ha) (lf_seq lf_codeE lf_optY))
theorem lf_guardE {c x y : HExp} (hc : LF c) (hx : LF x) (hy : LF y) : LF (guardE c x y) :=
  lf_alt (lf_seq (lf_andP hc) hx) (lf_seq (lf_notP hc) hy)

theorem lf_allChainH : ∀ {es : List HExp}, (∀ e ∈ es, LF e) → LF (allChainH es)
  | [], _ => lf_eps
  | e :: _, h => lf_seq (lf_andP (h e List.mem_cons_self)) (lf_allChainH (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem lf_anyChainH : ∀ {es : List HExp}, (∀ e ∈ es, LF e) → LF (anyChainH es)
  | [], _ => lf_fail
  | e :: _, h => lf_alt (h e List.mem_cons_self) (lf_anyChainH (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-! ## The level operations -/

theorem lf_ops : ∀ i : Nat, LF (ops i).zero ∧ LF (ops i).max ∧
    (∀ e, LF e → LF ((ops i).inc e) ∧ LF ((ops i).dec e) ∧ LF ((ops i).isZero e) ∧ LF ((ops i).isMax e)) ∧
    ∀ a b, LF a → LF b → LF ((ops i).eq a b)
  | 0 => ⟨lf_seq lf_codeE lf_optY, lf_seq (lf_seq lf_codeE lf_optY) (lf_lit _),
      fun _ he => ⟨lf_newSite (lf_xorE (lf_bit1 he) (lf_seq lf_siteE (lf_rcall1 he))),
        lf_newSite (lf_xorE (lf_bit1 he) (lf_seq lf_siteE (lf_rcall1 he))), lf_rcall1 he, lf_rcall1 he⟩,
      fun _ _ ha hb => lf_rcall2 ha hb⟩
  | _ + 1 => ⟨lf_rule _, lf_rule _, fun _ he => ⟨lf_rcall1 he, lf_rcall1 he, lf_rcall1 he, lf_rcall1 he⟩,
      fun _ _ ha hb => lf_rcall2 ha hb⟩

/-! ## The bodies -/

theorem lf_level1 : ∀ r ∈ level1Rules, ∃ τs B, r.body = lamsT τs B ∧ LF B ∧ r.ty = arrows τs HO.Ty.p := by
  intro r hr
  simp only [level1Rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hv := lf_var
  rcases hr with rfl | rfl | rfl
  · exact ⟨[HO.Ty.p], _, rfl, lf_alt (lf_andP (lf_lit _)) (lf_seq (lf_andP (lf_bit1 (hv 0)))
      (lf_seq lf_siteE (lf_rcall1 (hv 0)))), rfl⟩
  · exact ⟨[HO.Ty.p], _, rfl, lf_alt (lf_andP (lf_lit _)) (lf_seq (lf_notP (lf_bit1 (hv 0)))
      (lf_seq lf_siteE (lf_rcall1 (hv 0)))), rfl⟩
  · exact ⟨[HO.Ty.p, HO.Ty.p], _, rfl, lf_alt (lf_andP (lf_lit _))
      (lf_seq (lf_alt (lf_seq (lf_andP (lf_bit1 (hv 1))) (lf_andP (lf_bit1 (hv 0))))
        (lf_seq (lf_notP (lf_bit1 (hv 1))) (lf_notP (lf_bit1 (hv 0)))))
        (lf_seq lf_siteE (lf_rcall2 (hv 1) (hv 0)))), rfl⟩

theorem lf_block (i : Nat) : ∀ r ∈ blockRules i, ∃ τs σ B, r.body = lamsT τs B ∧ LF B ∧ r.ty = arrows τs σ := by
  intro r hr
  have ho := lf_ops i
  have hv := lf_var
  simp only [blockRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, HO.Ty.p, _, rfl, lf_seq (lf_andP (lf_app (hv 1) (hv 0)))
      (lf_guardE (ho.2.2.1 _ (hv 0)).2.2.2 lf_eps (lf_rcall2 (hv 1) (ho.2.2.1 _ (hv 0)).1)), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_guardE (ho.2.2.1 _ (hv 0)).2.2.1 lf_eps
      (lf_seq (lf_andP (lf_app (hv 1) (ho.2.2.1 _ (hv 0)).2.1)) (lf_rcall2 (hv 1) (ho.2.2.1 _ (hv 0)).2.1)), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_guardE (ho.2.2.1 _ (hv 0)).2.2.1 lf_eps
      (lf_seq (lf_notP (lf_app (hv 1) (ho.2.2.1 _ (hv 0)).2.1)) (lf_rcall2 (hv 1) (ho.2.2.1 _ (hv 0)).2.1)), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_notP (lf_app (hv 1) (hv 0)), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_alt (lf_seq (lf_andP (lf_app (hv 2) (hv 0))) (lf_andP (lf_app (hv 1) (hv 0))))
      (lf_seq (lf_notP (lf_app (hv 2) (hv 0))) (lf_notP (lf_app (hv 1) (hv 0)))), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_fail, rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_eps, rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_xorE (lf_app (hv 1) (hv 0)) (lf_rcall2 (hv 1) (hv 0)), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_xorE (lf_app (hv 1) (hv 0)) (lf_rcall2 (hv 1) (hv 0)), rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_rcall2 (lf_rcall1 (hv 0)) ho.1, rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_rcall2 (hv 0) ho.1, rfl⟩
  · exact ⟨_, HO.Ty.p, _, rfl, lf_rcall2 (lf_rcall2 (hv 1) (hv 0)) ho.1, rfl⟩

section Tab

variable {kt : Nat} (M : Complexity.TM kt) (K : Nat)

theorem lf_ftE {Kc X : HExp} (hK : LF Kc) (hX : LF X) : LF (ftE K Kc X) :=
  lf_seq (lf_seq (lf_star lf_siteE) (lf_lit _)) (lf_rcall2 hK hX)

theorem lf_symE (s : Nat) : LF (symE s) := by
  unfold symE
  split
  · exact lf_seq lf_codeE (lf_lit _)
  · split
    · exact lf_seq lf_codeE (lf_lit _)
    · exact lf_fail

theorem lf_readsE (r : List Nat) {tp : HExp} (htp : LF tp) : LF (readsE M K r tp) :=
  lf_allChainH (fun e he => by
    obtain ⟨τ, _, rfl⟩ := List.mem_map.1 he
    exact lf_rcall2 htp (lf_ops K).1)

theorem lf_stateNext (q : Nat) {tp : HExp} (htp : LF tp) : LF (stateNext M K q tp) := by
  refine lf_anyChainH (fun e he => ?_)
  rcases List.mem_append.1 he with he | he
  · obtain ⟨q', _, rfl⟩ := List.mem_map.1 he
    exact lf_rcall1 htp
  · obtain ⟨q', _, he⟩ := List.mem_flatMap.1 he
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 he
    exact lf_seq (lf_andP (lf_rcall1 htp)) (lf_readsE M K r htp)

theorem lf_movedE (τ : Fin kt) (mv : Complexity.Move) {tp i : HExp} (htp : LF tp) (hi : LF i) :
    LF (movedE M K τ mv tp i) := by
  have ho := (lf_ops K).2.2.1 _ hi
  cases mv
  · exact lf_alt (lf_guardE ho.2.2.2 lf_fail (lf_rcall2 htp ho.1)) (lf_seq (lf_andP ho.2.2.1) (lf_rcall2 htp hi))
  · exact lf_rcall2 htp hi
  · exact lf_seq (lf_notP ho.2.2.1) (lf_rcall2 htp ho.2.1)

/-- The shape of `headNext` and `symNext`. -/
theorem lf_nextChain {tp : HExp} (htp : LF tp) (X : HExp) (Y : Nat → List Nat → HExp) (hX : LF X)
    (hY : ∀ q' r, LF (Y q' r)) :
    LF (anyChainH ((List.range 2).map (fun q' => .seq (HExp.andP (rcall (rST K q') [tp])) X) ++
      (runStates M).flatMap (fun q' => (readsList M.na kt).map (fun r =>
        .seq (HExp.andP (rcall (rST K q') [tp])) (.seq (HExp.andP (readsE M K r tp)) (Y q' r)))))) := by
  refine lf_anyChainH (fun e he => ?_)
  rcases List.mem_append.1 he with he | he
  · obtain ⟨q', _, rfl⟩ := List.mem_map.1 he
    exact lf_seq (lf_andP (lf_rcall1 htp)) hX
  · obtain ⟨q', _, he⟩ := List.mem_flatMap.1 he
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 he
    exact lf_seq (lf_andP (lf_rcall1 htp)) (lf_seq (lf_andP (lf_readsE M K r htp)) (hY q' r))

theorem lf_initE (τ : Fin kt) (s : Nat) {i : HExp} (hi : LF i) : LF (initE K τ s i) := by
  unfold initE
  split
  · split
    · exact lf_rcall3 hi (lf_ops K).1 lf_eps
    · exact lf_fail
  · exact lf_bitC _

theorem lf_tab : ∀ r ∈ tabRules M K, ∃ τs σ B, r.body = lamsT τs B ∧ LF B ∧ r.ty = arrows τs σ := by
  intro r hr
  have hv := lf_var
  have ho := lf_ops K
  simp only [tabRules, List.mem_append] at hr
  rcases hr with hr | hr | hr | hr | hr | hr
  · simp only [tabFT, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, HO.Ty.p, _, rfl, lf_alt (lf_seq (lf_andP (lf_seq (hv 1) (lf_lit _))) (lf_andP (hv 0)))
      (lf_seq (lf_seq lf_codeE (lf_alt (lf_lit _) (lf_lit _))) (lf_rcall2 (hv 1) (hv 0))), rfl⟩
  · obtain ⟨s, _, rfl⟩ := List.mem_map.1 hr
    exact ⟨_, HO.Ty.p, _, rfl, lf_guardE (lf_ftE K (hv 0) lf_eps)
      (lf_guardE (ho.2.2.2 _ _ (hv 2) (hv 1)) (lf_ftE K (hv 0) (lf_symE s))
        (lf_rcall3 (hv 2) (ho.2.2.1 _ (hv 1)).1 (lf_seq (hv 0) (lf_lit _)))) (lf_bitC _), rfl⟩
  · obtain ⟨q, _, rfl⟩ := List.mem_map.1 hr
    exact ⟨_, HO.Ty.p, _, rfl, lf_guardE (ho.2.2.1 _ (hv 0)).2.2.1 (lf_bitC _)
      (lf_stateNext M K q (ho.2.2.1 _ (hv 0)).2.1), rfl⟩
  · obtain ⟨τ, _, rfl⟩ := List.mem_map.1 hr
    have hd := (ho.2.2.1 _ (hv 1)).2.1
    exact ⟨_, HO.Ty.p, _, rfl, lf_guardE (ho.2.2.1 _ (hv 1)).2.2.1 (ho.2.2.1 _ (hv 0)).2.2.1
      (lf_nextChain M K hd _ _ (lf_rcall2 hd (hv 0)) (fun _ _ => lf_movedE M K τ _ hd (hv 0))), rfl⟩
  · obtain ⟨τ, _, he⟩ := List.mem_flatMap.1 hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
    have hd := (ho.2.2.1 _ (hv 1)).2.1
    exact ⟨_, HO.Ty.p, _, rfl, lf_guardE (ho.2.2.1 _ (hv 1)).2.2.1 (lf_initE K τ s (hv 0))
      (lf_nextChain M K hd _ _ (lf_rcall2 hd (hv 0))
        (fun _ _ => lf_guardE (lf_rcall2 hd (hv 0)) (lf_bitC _) (lf_rcall2 hd (hv 0)))), rfl⟩
  · obtain ⟨τ, _, he⟩ := List.mem_flatMap.1 hr
    obtain ⟨s, _, rfl⟩ := List.mem_map.1 he
    have hi := (ho.2.2.1 _ (hv 0))
    exact ⟨_, HO.Ty.p, _, rfl, lf_alt (lf_seq (lf_andP (lf_rcall2 (hv 1) (hv 0))) (lf_rcall2 (hv 1) (hv 0)))
      (lf_seq (lf_notP hi.2.2.2) (lf_rcall2 (hv 1) hi.1)), rfl⟩

end Tab

/-! ## The order condition -/

theorem lamOrd_lamsT {B : HExp} (hB : LF B) : ∀ (τs : List HO.Ty) (σ : HO.Ty),
    lamOrd (lamsT τs B) ≤ (arrows τs σ).order
  | [], _ => by simp only [lamsT]; rw [hB]; exact Nat.zero_le _
  | τ :: τs, σ => by
    simp only [lamsT, lamOrd, arrows, HO.Ty.order]
    have := lamOrd_lamsT hB τs σ
    omega

theorem gT_lamOrd {kt : Nat} (M : Complexity.TM kt) (K : Nat) : ∀ r ∈ (gT M K).rules, lamOrd r.body ≤ K + 1 := by
  intro r hr
  have hshape : ∃ τs σ B, r.body = lamsT τs B ∧ LF B ∧ r.ty = arrows τs σ := by
    have hr' := hr
    simp only [gT, List.mem_append] at hr'
    rcases hr' with (hr' | hr') | hr'
    · obtain ⟨τs, B, h₁, h₂, h₃⟩ := lf_level1 r hr'
      exact ⟨τs, _, B, h₁, h₂, h₃⟩
    · obtain ⟨i, _, hr'⟩ := List.mem_flatMap.1 hr'
      exact lf_block i r hr'
    · exact lf_tab M K r hr'
  obtain ⟨τs, σ, B, h₁, h₂, h₃⟩ := hshape
  rw [h₁]
  have := rule_order_le M K r hr
  rw [h₃] at this
  exact Nat.le_trans (lamOrd_lamsT h₂ τs σ) this

/-- **The tableau grammar satisfies the order condition** of the uniform problem for order `K + 1`. -/
theorem gT_GOrd {kt : Nat} (M : Complexity.TM kt) (K : Nat) : GOrd (K + 1) (gT M K) (startT K) := by
  refine ⟨by rw [gT_order]; exact Nat.le_refl _, gT_lamOrd M K, ?_⟩
  have : LF (startT K) := lf_seq (lf_andP (lf_rcall1 (lf_ops K).2.1)) (lf_star lf_any)
  rw [show lamOrd (startT K) = 0 from this]; exact Nat.zero_le _

end Shallot.MacroPeg.KExp
