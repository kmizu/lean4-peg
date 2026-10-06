import MacroPeg.HigherOrder.Mach.ReadExpr

/-!
# Reading a whole instance

The rule types (frames `14`/`15`), the bodies checked against them (frames `16`/`17`, `checkBodies`), the start
(frame `18`) and the string. `read_ok`/`read_fail`: from `pinit tokens` the machine stops accepting with the typed
items of the bodies and of the start exactly when `deser`, `checkRules` and `inferE` succeed (as in `flatDecide`),
and stops rejecting otherwise.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## The rule types -/

theorem parseTys_shorter {f : Nat} {l : List Nat} {ts : List HO.Ty} {r : List Nat} (h : parseTys f l = some (ts, r)) :
    r.length < l.length := by
  have := parseTys_sound h; have := length_serTys_pos ts; rw [‹l = _›]; simp; omega

/-- **Reading the rule types.** -/
theorem readTys_ok : ∀ (f : Nat) (l : List Nat) (ts : List HO.Ty) (rest : List Nat), parseTys f l = some (ts, rest) →
    ∀ (s : PSt) (K : List Nat), s.tk = l → s.ctl = 14 :: K → TTWF s.tt →
      ∃ n tt' ids, Reach s { s with tk := rest, ctl := 16 :: K, tt := tt', rt := s.rt ++ ids } n ∧ TTWF tt' ∧
        (∃ e, tt' = s.tt ++ e) ∧ ids.mapM (tyOf tt') = some ts ∧ n + 3 * rest.length ≤ 3 * l.length
  | _, 0 :: l, ts, rest, h, s, K, htk, hctl, hw => by
    simp only [parseTys, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨1, s.tt, [], ?_, hw, ⟨[], by simp⟩, rfl, by simp; omega⟩
    show pstep s = _
    simp [pstep, hctl, htk]
  | f + 1, 1 :: l, ts, rest, h, s, K, htk, hctl, hw => by
    simp only [parseTys] at h
    split at h
    · rename_i τ l₁ hτ
      obtain ⟨⟨ts', r'⟩, hts, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      let s₁ : PSt := { s with tk := l, ctl := 1 :: 15 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, htk, s₁]
      obtain ⟨n₁, tt₁, i₁, x₂, hw₁, he₁, hi₁, hτ₁, hn₁⟩ := readType_ok f l τ l₁ hτ s₁ (15 :: K) rfl rfl hw
      let s₂ : PSt := { s₁ with tk := l₁, ctl := 15 :: K, ty := i₁ :: s₁.ty, tt := tt₁ }
      let s₃ : PSt := { s₂ with ctl := 14 :: K, ty := s.ty, rt := s.rt ++ [i₁] }
      have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, s₂, s₃, s₁]
      obtain ⟨n₂, tt₂, ids, x₄, hw₂, he₂, hids, hn₂⟩ := readTys_ok f l₁ ts' r' hts s₃ K rfl rfl hw₁
      refine ⟨1 + n₁ + 1 + n₂, tt₂, i₁ :: ids, ?_, hw₂, ?_, ?_, ?_⟩
      · have := ((x₁.trans x₂).trans x₃).trans x₄
        simpa [s₃, s₂, s₁] using this
      · obtain ⟨e₁, h₁⟩ := he₁; obtain ⟨e₂, h₂⟩ := he₂
        exact ⟨e₁ ++ e₂, by rw [h₂, show s₃.tt = tt₁ from rfl, h₁, show s₁.tt = s.tt from rfl, List.append_assoc]⟩
      · rw [List.mapM_cons]
        simp only [tyOf_grow hw₁ he₂ hτ₁, hids, bind, Option.bind_some, pure]
      · simp only [List.length_cons] at hn₁ hn₂ ⊢; omega
    · cases h
  | 0, 1 :: _, _, _, h, _, _, _, _, _ | _, [], _, _, h, _, _, _, _, _
  | _, (_ + 2) :: _, _, _, h, _, _, _, _, _ => by simp [parseTys] at h

theorem readTys_fail : ∀ (f : Nat) (l : List Nat), l.length ≤ f → parseTys f l = none →
    ∀ (s : PSt) (K : List Nat), s.tk = l → s.ctl = 14 :: K → TTWF s.tt → Fails s
  | 0, [], _, _, s, K, htk, hctl, _ => Fails.of_step (by simp [pstep, hctl, htk]; exact Fails.fail _)
  | f + 1, [], _, _, s, K, htk, hctl, _ => Fails.of_step (by simp [pstep, hctl, htk]; exact Fails.fail _)
  | 0, _ :: _, hl, _, _, _, _, _, _ => by simp at hl
  | f + 1, t :: l, hl, h, s, K, htk, hctl, hw => by
    have hlf : l.length ≤ f := by simp at hl; omega
    match t, h with
    | 0, h => simp [parseTys] at h
    | 1, h =>
      let s₁ : PSt := { s with tk := l, ctl := 1 :: 15 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, htk, s₁]
      simp only [parseTys] at h
      split at h
      · rename_i τ l₁ hτ
        simp only [Option.map_eq_none_iff] at h
        obtain ⟨n₁, tt₁, i₁, x₂, hw₁, _, _, _, _⟩ := readType_ok f l τ l₁ hτ s₁ (15 :: K) rfl rfl hw
        let s₂ : PSt := { s₁ with tk := l₁, ctl := 15 :: K, ty := i₁ :: s₁.ty, tt := tt₁ }
        let s₃ : PSt := { s₂ with ctl := 14 :: K, ty := s.ty, rt := s.rt ++ [i₁] }
        have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, s₂, s₃, s₁]
        have := parseTy_shorter hτ
        exact Fails.of_reach ((x₁.trans x₂).trans x₃) (readTys_fail f l₁ (by omega) h s₃ K rfl rfl hw₁)
      · rename_i hτ
        exact Fails.of_reach x₁ (readType_fail f l hlf hτ s₁ (15 :: K) rfl rfl hw)
    | k + 2, _ => exact Fails.of_step (by simp [pstep, hctl, htk]; exact Fails.fail _)

/-! ## The bodies -/

/-- Type the bodies `es` against the rule types `ts`, one by one. -/
def checkBodies (R : List HO.Ty) : List HO.Ty → List HExp → Option (List (List Item))
  | [], [] => some []
  | τ :: ts, e :: es =>
    match inferE R [] e with
    | some (σ, is) => if σ = τ then (checkBodies R ts es).map (is :: ·) else none
    | none => none
  | _, _ => none

theorem checkBodies_rules (R : List HO.Ty) : ∀ (ts : List HO.Ty) (es : List HExp), ts.length = es.length →
    (List.zipWith (fun τ e => (⟨τ, e⟩ : HRule)) ts es).mapM (checkRule R) = checkBodies R ts es
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | τ :: ts, e :: es, h => by
    have hc : checkRule R ⟨τ, e⟩ = match inferE R [] e with
        | some (τ', is) => if τ' = τ then some is else none
        | none => none := rfl
    rw [List.zipWith_cons_cons, List.mapM_cons, checkBodies, hc]
    cases hi : inferE R [] e with
    | none => rfl
    | some p =>
      obtain ⟨σ, is⟩ := p
      simp only
      by_cases hσ : σ = τ
      · simp only [hσ, if_true, bind, Option.bind_some, pure]
        rw [checkBodies_rules R ts es (by simpa using h)]
        cases checkBodies R ts es <;> rfl
      · simp [hσ]

/-- What reading the bodies does. -/
def BodiesRes (s : PSt) (K rest : List Nat) (L : Nat) : Option (List (List Item)) → Prop
  | some bis => ∃ n s', Reach s s' n ∧ s'.tk = rest ∧ s'.ctl = 0 :: 18 :: K ∧ s'.cur = 0 ∧ s'.out = [] ∧
      s'.ty = s.ty ∧ s'.rt = s.rt ∧ s'.start = s.start ∧ s'.x = s.x ∧ s'.ok = s.ok ∧
      (∃ E, s'.bodies = s.bodies ++ E ∧ E.mapM (itemsOf s'.tt s'.ct s'.lt) = some bis) ∧
      Grows s.tt s.ct s.lt s'.tt s'.ct s'.lt ∧ TTWF s'.tt ∧ CTWF s'.tt s'.ct ∧ n + 3 * rest.length ≤ 3 * L
  | none => Fails s

theorem mapM_itemsOf_grow {tt ct tt' ct' : List (Nat × Nat)} {lt lt' : List (List Nat)} (hw : TTWF tt)
    (hc : CTWF tt ct) (hg : Grows tt ct lt tt' ct' lt') : ∀ {E : List (List MItem)} {bis : List (List Item)},
      E.mapM (itemsOf tt ct lt) = some bis → E.mapM (itemsOf tt' ct' lt') = some bis
  | [], _, h => h
  | b :: E, bis, h => by
    rw [List.mapM_cons] at h ⊢
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    simp [itemsOf_grow hw hc hg hx, mapM_itemsOf_grow hw hc hg hxs]

theorem mapM_length {α β : Type} {f : α → Option β} : ∀ {l : List α} {bs : List β}, l.mapM f = some bs →
    l.length = bs.length
  | [], bs, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, _, bs', hbs, rfl⟩ := h
    simp [mapM_length hbs]

theorem parseBodies_shorter {f : Nat} {l : List Nat} {es : List HExp} {r : List Nat}
    (h : parseBodies f l = some (es, r)) : r.length < l.length := by
  have := parseBodies_sound h; have := length_serBodies_pos es; rw [‹l = _›]; simp; omega

/-- **Reading the bodies**, each typed against its rule type. -/
theorem readBodies_spec : ∀ (f : Nat) (l : List Nat) (es : List HExp) (rest : List Nat),
    parseBodies f l = some (es, rest) →
    ∀ (s : PSt) (K : List Nat) (R : List HO.Ty), s.tk = l → s.ctl = 16 :: K → TTWF s.tt → CTWF s.tt s.ct →
      s.rt.mapM (tyOf s.tt) = some R → s.out = [] → s.bodies.length ≤ R.length →
      BodiesRes s K rest l.length (checkBodies R (R.drop s.bodies.length) es)
  | _, 0 :: l, es, rest, h, s, K, R, htk, hctl, hw, hc, hR, hout, hm => by
    simp only [parseBodies, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlen : s.rt.length = R.length := mapM_length hR
    by_cases he : s.bodies.length = R.length
    · rw [he, List.drop_length]
      refine ⟨1, { s with tk := l, ctl := 0 :: 18 :: K, cur := 0 }, ?_, rfl, rfl, rfl, hout, rfl, rfl, rfl, rfl, rfl,
        ⟨[], by simp, rfl⟩, Grows.refl _ _ _, hw, hc, by simp; omega⟩
      show pstep s = _
      simp [pstep, hctl, htk, he, hlen]
    · have hd : R.drop s.bodies.length ≠ [] := by simp; omega
      have : checkBodies R (R.drop s.bodies.length) [] = none := by
        cases hx : R.drop s.bodies.length with
        | nil => exact absurd hx hd
        | cons _ _ => rfl
      rw [this]
      exact Fails.of_step (by simp [pstep, hctl, htk, hlen, he]; exact Fails.fail _)
  | f + 1, 1 :: l, es, rest, h, s, K, R, htk, hctl, hw, hc, hR, hout, hm => by
    simp only [parseBodies] at h
    split at h
    · rename_i e l₁ he
      obtain ⟨⟨es', r'⟩, hes, hh⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 17 :: K, cur := 0 }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, htk, s₁]
      have hΓ₁ : ctxOf s₁.tt s₁.ct s₁.cur = some [] := by show ctxOf s.tt s.ct 0 = _; rw [ctxOf]
      have hA := readExpr_spec f l e l₁ he s₁ (17 :: K) R [] rfl rfl hw hc hR hΓ₁
      have hlen : s.rt.length = R.length := mapM_length hR
      -- the checks against the rule type
      cases hdrop : R.drop s.bodies.length with
      | nil =>
        have : checkBodies R [] (e :: es') = none := rfl
        rw [this]
        cases hia : inferE R [] e with
        | none => rw [hia] at hA; exact Fails.of_reach x₁ hA
        | some pa =>
          rw [hia] at hA
          obtain ⟨n₁, hd₁, _⟩ := hA
          obtain ⟨s₂, x₂, _, hctl₂, _, _, hrt₂, hbo₂, _, _, ⟨i₁, hty₂, _⟩, _, _, _, _⟩ := hd₁.parts
          have hnone : s.rt[s.bodies.length]? = none := by
            rw [List.getElem?_eq_none_iff]; have := List.drop_eq_nil_iff.1 hdrop; omega
          refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
          have hrt₂' : s₂.rt = s.rt := hrt₂
          have hbo₂' : s₂.bodies = s.bodies := hbo₂
          simp [pstep, hctl₂, hty₂, hrt₂', hbo₂', hnone]; exact Fails.fail _
      | cons τ ts' =>
        have hcb : checkBodies R (τ :: ts') (e :: es') = match inferE R [] e with
            | some (σ, is) => if σ = τ then (checkBodies R ts' es').map (is :: ·) else none
            | none => none := rfl
        rw [hcb]
        cases hia : inferE R [] e with
        | none => rw [hia] at hA; exact Fails.of_reach x₁ hA
        | some pa =>
          obtain ⟨σ, is⟩ := pa
          rw [hia] at hA
          obtain ⟨n₁, hd₁, hn₁⟩ := hA
          obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂, ⟨i₁, hty₂, hσ⟩, ⟨oE, hout₂, hoE⟩, hg₂,
            hw₂, hc₂⟩ := hd₁.parts
          have hrt₂' : s₂.rt = s.rt := hrt₂
          have hbo₂' : s₂.bodies = s.bodies := hbo₂
          -- the rule type of this body
          have hmlt : s.bodies.length < R.length := by
            have : (R.drop s.bodies.length).length = ts'.length + 1 := by rw [hdrop]; rfl
            simp at this; omega
          have hRm : R[s.bodies.length]? = some τ := by
            have := congrArg (·[0]?) hdrop
            simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using this
          obtain ⟨t, ht, htτ⟩ : ∃ t, s.rt[s.bodies.length]? = some t ∧ tyOf s.tt t = some τ := by
            have hv := mapM_getElem? hR s.bodies.length
            rw [hRm] at hv
            cases hx : s.rt[s.bodies.length]? with
            | none => rw [hx] at hv; cases hv
            | some t => rw [hx] at hv; exact ⟨t, rfl, hv⟩
          have htτ₂ : tyOf s₂.tt t = some τ := tyOf_grow hw hg₂.tt htτ
          by_cases hστ : σ = τ
          · subst hστ
            obtain rfl : t = i₁ := tyOf_eq_of_eq hw₂ htτ₂ hσ
            simp only [if_true]
            let s₃ : PSt :=
              { s₂ with
                ctl := 16 :: K
                ty := s.ty
                bodies := s.bodies ++ [s₂.out.reverse]
                out := [] }
            have x₃ : Reach s₂ s₃ 1 := by
              show pstep s₂ = s₃
              simp [pstep, hctl₂, hty₂, hrt₂', hbo₂', ht, s₃]; rfl
            have hR₃ : s₃.rt.mapM (tyOf s₃.tt) = some R := by
              show s₂.rt.mapM (tyOf s₂.tt) = _; rw [hrt₂']; exact mapM_tyOf_grow hw hg₂.tt hR
            have hm₃ : s₃.bodies.length ≤ R.length := by simp [s₃]; omega
            have hB := readBodies_spec f l₁ es' r' hes s₃ K R htk₂ rfl hw₂ hc₂ hR₃ rfl hm₃
            have hdrop' : R.drop s₃.bodies.length = ts' := by
              simp only [s₃, List.length_append, List.length_singleton]
              rw [← List.drop_drop, hdrop]; rfl
            rw [hdrop'] at hB
            cases hcb' : checkBodies R ts' es' with
            | none => rw [hcb'] at hB; exact Fails.of_reach ((x₁.trans x₂).trans x₃) hB
            | some bis =>
              rw [hcb'] at hB
              obtain ⟨n₂, s₄, x₄, htk₄, hctl₄, hcur₄, hout₄, hty₄, hrt₄, hst₄, hx₄, hok₄, ⟨E, hbo₄, hE⟩, hg₄, hw₄,
                hc₄, hn₂⟩ := hB
              refine ⟨1 + n₁ + 1 + n₂, s₄, ((x₁.trans x₂).trans x₃).trans x₄, htk₄, hctl₄, hcur₄, hout₄, hty₄,
                by rw [hrt₄]; exact hrt₂', by rw [hst₄]; exact hst₂, by rw [hx₄]; exact hx₂,
                by rw [hok₄]; exact hok₂, ⟨oE :: E, ?_, ?_⟩, hg₂.trans hg₄, hw₄, hc₄, ?_⟩
              · rw [hbo₄]
                show (s.bodies ++ [s₂.out.reverse]) ++ E = s.bodies ++ (oE :: E)
                rw [hout₂, show s₁.out = s.out from rfl, hout]; simp
              · rw [List.mapM_cons]
                simp [itemsOf_grow hw₂ hc₂ hg₄ hoE, hE]
              · simp only [List.length_cons] at hn₁ hn₂ ⊢; omega
          · simp only [hστ, if_false]
            have hne : t ≠ i₁ := fun e => hστ (by subst e; exact Option.some.inj (hσ.symm.trans htτ₂))
            refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
            simp [pstep, hctl₂, hty₂, hrt₂', hbo₂', ht, hne]; exact Fails.fail _
    · cases h
  | 0, 1 :: _, _, _, h, _, _, _, _, _, _, _, _, _, _ | _, [], _, _, h, _, _, _, _, _, _, _, _, _, _
  | _, (_ + 2) :: _, _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [parseBodies] at h

theorem readBodies_fail : ∀ (f : Nat) (l : List Nat), l.length ≤ f → parseBodies f l = none →
    ∀ (s : PSt) (K : List Nat) (R : List HO.Ty), s.tk = l → s.ctl = 16 :: K → TTWF s.tt → CTWF s.tt s.ct →
      s.rt.mapM (tyOf s.tt) = some R → Fails s
  | _, [], _, _, s, K, _, htk, hctl, _, _, _ => Fails.of_step (by simp [pstep, hctl, htk]; exact Fails.fail _)
  | 0, _ :: _, hl, _, _, _, _, _, _, _, _, _ => by simp at hl
  | f + 1, t :: l, hl, h, s, K, R, htk, hctl, hw, hc, hR => by
    have hlf : l.length ≤ f := by simp at hl; omega
    match t, h with
    | 0, h => simp [parseBodies] at h
    | 1, h =>
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 17 :: K, cur := 0 }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, htk, s₁]
      have hΓ₁ : ctxOf s₁.tt s₁.ct s₁.cur = some [] := by show ctxOf s.tt s.ct 0 = _; rw [ctxOf]
      simp only [parseBodies] at h
      split at h
      · rename_i e l₁ he
        simp only [Option.map_eq_none_iff] at h
        have hA := readExpr_spec f l e l₁ he s₁ (17 :: K) R [] rfl rfl hw hc hR hΓ₁
        cases hia : inferE R [] e with
        | none => rw [hia] at hA; exact Fails.of_reach x₁ hA
        | some pa =>
          rw [hia] at hA
          obtain ⟨n₁, hd₁, _⟩ := hA
          obtain ⟨s₂, x₂, htk₂, hctl₂, _, _, hrt₂, hbo₂, _, _, ⟨i₁, hty₂, _⟩, _, hg₂, hw₂, hc₂⟩ := hd₁.parts
          have hrt₂' : s₂.rt = s.rt := hrt₂
          have hbo₂' : s₂.bodies = s.bodies := hbo₂
          refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
          by_cases hm : s.rt[s.bodies.length]? = some i₁
          · let s₃ : PSt :=
              { s₂ with
                ctl := 16 :: K
                ty := s.ty
                bodies := s.bodies ++ [s₂.out.reverse]
                out := [] }
            have hs : pstep s₂ = s₃ := by simp [pstep, hctl₂, hty₂, hrt₂', hbo₂', hm, s₃]; rfl
            rw [hs]
            have := parseE_shorter he
            exact readBodies_fail f l₁ (by omega) h s₃ K R htk₂ rfl hw₂ hc₂
              (by show s₂.rt.mapM (tyOf s₂.tt) = _; rw [hrt₂']; exact mapM_tyOf_grow hw hg₂.tt hR)
          · simp [pstep, hctl₂, hty₂, hrt₂', hbo₂', hm]; exact Fails.fail _
      · rename_i he
        exact Fails.of_reach x₁ (readExpr_fail f l hlf he s₁ _ R [] rfl rfl hw hc hR hΓ₁)
    | k + 2, _ => exact Fails.of_step (by simp [pstep, hctl, htk]; exact Fails.fail _)

/-! ## The whole instance -/

theorem checkBodies_length {R : List HO.Ty} : ∀ {ts : List HO.Ty} {es : List HExp} {bis : List (List Item)},
    checkBodies R ts es = some bis → ts.length = es.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [checkBodies] at h
  | τ :: ts, e :: es, bis, h => by
    simp only [checkBodies] at h
    split at h
    · split at h
      · obtain ⟨_, hb, _⟩ := Option.map_eq_some_iff.1 h
        simp [checkBodies_length hb]
      · cases h
    · cases h

theorem parseStr_full' {L : Nat} {l : List Nat} (hl : l.length ≤ L) :
    parseStr l.length l = parseStr L l := by
  cases hs : parseStr L l with
  | none => exact parseStr_none hl hs
  | some p => obtain ⟨str, r⟩ := p; exact parseStr_full hs

/-- The machine stopped accepting, with the instance read and typed. -/
structure ReadOK (st : PSt) (R : List HO.Ty) (bis : List (List Item)) (is : List Item) (x : List Char) : Prop where
  ctl : st.ctl = []
  ok : st.ok = true
  rt : st.rt.mapM (tyOf st.tt) = some R
  bodies : st.bodies.mapM (itemsOf st.tt st.ct st.lt) = some bis
  start : itemsOf st.tt st.ct st.lt st.start = some is
  x : st.x = x.map Char.toNat
  tt : TTWF st.tt
  ct : CTWF st.tt st.ct

theorem TTWF.nil : TTWF [] := ⟨List.nodup_nil, fun k h => by simp at h⟩
theorem CTWF.nil (tt : List (Nat × Nat)) : CTWF tt [] := fun k h => by simp at h

/-- **Reading succeeds** when the instance reads back and types. -/
theorem read_ok {tk : List Nat} {g : HGrammar} {s₀ : HExp} {x : List Char} {bis : List (List Item)}
    {is : List Item} (hd : deser tk = some (g, s₀, x)) (hcr : checkRules g = some bis)
    (hinf : inferE g.types [] s₀ = some (.p, is)) :
    ∃ n st, Reach (pinit tk) st n ∧ ReadOK st g.types bis is x ∧ n ≤ 3 * tk.length + 1 := by
  unfold deser at hd
  split at hd
  · rename_i ts l₁ h₁
    split at hd
    · rename_i bs l₂ h₂
      split at hd
      · rename_i hlen
        split at hd
        · rename_i s' l₃ h₃
          split at hd
          · rename_i x' h₄
            simp only [Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl, rfl⟩ := hd
            have hty : (HGrammar.mk (List.zipWith (fun τ e => (⟨τ, e⟩ : HRule)) ts bs)).types = ts :=
              (map_zipWith_ty ts bs hlen).1
            rw [hty] at hinf ⊢
            have hcb : checkBodies ts ts bs = some bis := by
              rw [← checkBodies_rules ts ts bs hlen]
              have := hcr; unfold checkRules at this; rw [hty] at this; exact this
            -- the rule types
            obtain ⟨n₁, tt₁, ids, x₁, hw₁, _, hids, hn₁⟩ :=
              readTys_ok tk.length tk ts l₁ h₁ (pinit tk) [] rfl rfl TTWF.nil
            let s₁ : PSt := { pinit tk with tk := l₁, ctl := [16], tt := tt₁, rt := [] ++ ids }
            have hl₁ := parseTys_shorter h₁
            -- the bodies
            have hB := readBodies_spec tk.length l₁ bs l₂ h₂ s₁ [] ts rfl rfl hw₁ (CTWF.nil _) hids rfl (Nat.zero_le _)
            simp only [show s₁.bodies.length = 0 from rfl, List.drop_zero, hcb] at hB
            obtain ⟨n₂, s₂, x₂, htk₂, hctl₂, hcur₂, hout₂, hty₂, hrt₂, hst₂, hx₂, hok₂, ⟨E, hbo₂, hE⟩, hg₂, hw₂, hc₂,
              hn₂⟩ := hB
            -- the start
            have hΓ₂ : ctxOf s₂.tt s₂.ct s₂.cur = some [] := by rw [hcur₂, ctxOf]
            have hR₂ : s₂.rt.mapM (tyOf s₂.tt) = some ts := by
              rw [hrt₂]; exact mapM_tyOf_grow hw₁ hg₂.tt hids
            have hA := readExpr_spec tk.length l₂ s' l₃ h₃ s₂ [18] ts [] htk₂ hctl₂ hw₂ hc₂ hR₂ hΓ₂
            rw [hinf] at hA
            obtain ⟨n₃, hd₃, hn₃⟩ := hA
            obtain ⟨s₃, x₃, htk₃, hctl₃, hcur₃, hok₃, hrt₃, hbo₃, hst₃, hx₃, ⟨i₃, hty₃, hτ₃⟩, ⟨oS, hout₃, hoS⟩, hg₃,
              hw₃, hc₃⟩ := hd₃.parts
            obtain rfl : i₃ = 0 := tyOf_eq_p hτ₃
            -- the string
            have hl₂ := parseBodies_shorter h₂
            have hl₃ := parseE_shorter h₃
            have hstr : parseStr s₃.tk.length s₃.tk = some (x', []) := by
              rw [htk₃, parseStr_full' (L := tk.length) (by omega)]; exact h₄
            let st : PSt :=
              { s₃ with
                ctl := []
                ty := s₂.ty
                start := s₃.out.reverse
                out := []
                x := x'.map Char.toNat }
            have x₄ : Reach s₃ st 1 := by
              show pstep s₃ = st
              simp [pstep, hctl₃, hty₃, hstr, st]
            refine ⟨n₁ + n₂ + n₃ + 1, st, ((x₁.trans x₂).trans x₃).trans x₄, ⟨rfl, ?_, ?_, ?_, ?_, rfl, hw₃, hc₃⟩, ?_⟩
            · show s₃.ok = true; rw [hok₃, hok₂]; rfl
            · show s₃.rt.mapM (tyOf s₃.tt) = _; rw [hrt₃]; exact mapM_tyOf_grow hw₂ hg₃.tt hR₂
            · show s₃.bodies.mapM _ = _
              rw [hbo₃, hbo₂, show s₁.bodies = [] from rfl, List.nil_append]
              exact mapM_itemsOf_grow hw₂ hc₂ hg₃ hE
            · show itemsOf s₃.tt s₃.ct s₃.lt s₃.out.reverse = _
              rw [hout₃, hout₂]; simpa using hoS
            · omega
          · cases hd
        · cases hd
      · cases hd
    · cases hd
  · cases hd

/-- **Reading fails** when the instance does not read back or does not type. -/
theorem read_fail {tk : List Nat}
    (h : ∀ g s₀ x bis is, deser tk = some (g, s₀, x) → checkRules g = some bis →
      inferE g.types [] s₀ = some (.p, is) → False) : Fails (pinit tk) := by
  cases h₁ : parseTys tk.length tk with
  | none => exact readTys_fail tk.length tk (Nat.le_refl _) h₁ (pinit tk) [] rfl rfl TTWF.nil
  | some p₁ =>
    obtain ⟨ts, l₁⟩ := p₁
    obtain ⟨n₁, tt₁, ids, x₁, hw₁, _, hids, _⟩ := readTys_ok tk.length tk ts l₁ h₁ (pinit tk) [] rfl rfl TTWF.nil
    let s₁ : PSt := { pinit tk with tk := l₁, ctl := [16], tt := tt₁, rt := [] ++ ids }
    have hl₁ := parseTys_shorter h₁
    cases h₂ : parseBodies tk.length l₁ with
    | none =>
      exact Fails.of_reach x₁ (readBodies_fail tk.length l₁ (by omega) h₂ s₁ [] ts rfl rfl hw₁ (CTWF.nil _) hids)
    | some p₂ =>
      obtain ⟨bs, l₂⟩ := p₂
      have hl₂ := parseBodies_shorter h₂
      have hB := readBodies_spec tk.length l₁ bs l₂ h₂ s₁ [] ts rfl rfl hw₁ (CTWF.nil _) hids rfl (Nat.zero_le _)
      simp only [show s₁.bodies.length = 0 from rfl, List.drop_zero] at hB
      cases hcb : checkBodies ts ts bs with
      | none => rw [hcb] at hB; exact Fails.of_reach x₁ hB
      | some bis =>
        rw [hcb] at hB
        have hlen := checkBodies_length hcb
        obtain ⟨n₂, s₂, x₂, htk₂, hctl₂, hcur₂, _, _, hrt₂, _, _, _, _, hg₂, hw₂, hc₂, _⟩ := hB
        have hΓ₂ : ctxOf s₂.tt s₂.ct s₂.cur = some [] := by rw [hcur₂, ctxOf]
        have hR₂ : s₂.rt.mapM (tyOf s₂.tt) = some ts := by
          rw [hrt₂]; exact mapM_tyOf_grow hw₁ hg₂.tt hids
        cases h₃ : parseE tk.length l₂ with
        | none =>
          exact Fails.of_reach (x₁.trans x₂)
            (readExpr_fail tk.length l₂ (by omega) h₃ s₂ [18] ts [] htk₂ hctl₂ hw₂ hc₂ hR₂ hΓ₂)
        | some p₃ =>
          obtain ⟨s', l₃⟩ := p₃
          have hl₃ := parseE_shorter h₃
          have hA := readExpr_spec tk.length l₂ s' l₃ h₃ s₂ [18] ts [] htk₂ hctl₂ hw₂ hc₂ hR₂ hΓ₂
          cases hinf : inferE ts [] s' with
          | none => rw [hinf] at hA; exact Fails.of_reach (x₁.trans x₂) hA
          | some p₄ =>
            obtain ⟨σ, is⟩ := p₄
            rw [hinf] at hA
            obtain ⟨n₃, hd₃, _⟩ := hA
            obtain ⟨s₃, x₃, htk₃, hctl₃, _, _, _, _, _, _, ⟨i₃, hty₃, hτ₃⟩, _, _, _, _⟩ := hd₃.parts
            refine Fails.of_reach ((x₁.trans x₂).trans x₃) (Fails.of_step ?_)
            by_cases hσ : σ = .p
            · subst hσ
              obtain rfl : i₃ = 0 := tyOf_eq_p hτ₃
              have hstr : parseStr s₃.tk.length s₃.tk = parseStr tk.length l₃ := by
                rw [htk₃]; exact parseStr_full' (by omega)
              cases h₄ : parseStr tk.length l₃ with
              | none => simp [pstep, hctl₃, hty₃, hstr, h₄]; exact Fails.fail _
              | some p₅ =>
                obtain ⟨x', r⟩ := p₅
                cases r with
                | nil =>
                  exfalso
                  have hd : deser tk = some (⟨List.zipWith (fun τ e => ⟨τ, e⟩) ts bs⟩, s', x') := by
                    unfold deser; simp [h₁, h₂, hlen, h₃, h₄]
                  have hty : (HGrammar.mk (List.zipWith (fun τ e => (⟨τ, e⟩ : HRule)) ts bs)).types = ts :=
                    (map_zipWith_ty ts bs hlen).1
                  refine h _ _ _ bis is hd ?_ (by rw [hty]; exact hinf)
                  unfold checkRules; rw [hty, checkBodies_rules ts ts bs hlen]; exact hcb
                | cons c r => simp [pstep, hctl₃, hty₃, hstr, h₄]; exact Fails.fail _
            · have hi : i₃ ≠ 0 := fun e => hσ (by subst e; rw [tyOf] at hτ₃; exact (Option.some.inj hτ₃).symm)
              cases i₃ with
              | zero => exact absurd rfl hi
              | succ k => simp [pstep, hctl₃, hty₃]; exact Fails.fail _

end Shallot.MacroPeg.Mach
