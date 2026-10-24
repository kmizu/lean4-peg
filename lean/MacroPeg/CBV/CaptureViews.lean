import MacroPeg.CBV.CommonOriginCaptures

/-! Cumulative views of a disjoint runtime environment can replace overlapping
Par parameters throughout any first-order expression. The evaluation strategy
and recursive table are unchanged: this handles representation, not entry. -/
namespace Shallot.MacroPeg.CBV.CaptureViews

def prefixExpr : Nat → MExp
  | 0 => .lit []
  | k+1 => .seq (prefixExpr k) (.param k)

theorem prefixExpr_firstOrder (k : Nat) : (prefixExpr k).FirstOrder := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ih,trivial⟩

private theorem strip_concat (u v input : List Char) :
    Shallot.stripPrefix? (u ++ v) input =
      (Shallot.stripPrefix? u input).bind (Shallot.stripPrefix? v) := by
  induction u generalizing input with
  | nil => rfl
  | cons c u ih =>
    cases input with
    | nil => rfl
    | cons d input =>
      simp only [List.cons_append,Shallot.stripPrefix?]
      split <;> simp_all

theorem sequence_literals (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (u v : List Char) (p : Nat) :
    evV g x s T E (.seq (.lit u) (.lit v)) p = evV g x s T E (.lit (u++v)) p := by
  simp only [evV,strip_concat]
  cases hs : Shallot.stripPrefix? u (sfx x p) with
  | none => rfl
  | some rem =>
    have he := (CBVtoCBN.stripPrefix_exact u (sfx x p) rem).mp hs
    have hr := suffix_trans (sfx_is_suffix x p) ⟨u,he⟩
    simp only [Option.bind_some,sfx_suffix hr.choose_spec]

theorem prefixExpr_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (parts : List (List Char)) (k : Nat) (hk : k ≤ parts.length) (p : Nat) :
    evV g x s T parts (prefixExpr k) p = evV g x s T parts (.lit (parts.take k).flatten) p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    have hb : k < parts.length := by omega
    have hl := List.getElem?_eq_getElem hb
    have hseq : evV g x s T parts (prefixExpr (k+1)) p =
        evV g x s T parts (.seq (.lit (parts.take k).flatten) (.lit parts[k])) p := by
      change (match evV g x s T parts (prefixExpr k) p with
        | some (some q) => evV g x s T parts (.param k) q | r => r) = _
      rw [ih (by omega)]
      simp only [evV,hl]
      rfl
    rw [hseq,sequence_literals]
    have ht : parts.take (k+1) = parts.take k ++ [parts[k]] := by
      rw [List.take_add_one,hl]; rfl
    rw [ht,List.flatten_append]
    simp only [List.flatten_cons,List.flatten_nil,List.append_nil]

mutual
  /-- Rebinding parameters by observationally equal views preserves every
first-order expression, including either argument convention and recursion
through the same arbitrary table. -/
  theorem evV_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (P : List MExp) (W : List (List Char))
      (hparam : ∀ k p, evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (b : MExp), b.FirstOrder → ∀ p, evV g x s T E (MExp.subst P b) p = evV g x s T W b p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => by simp only [MExp.subst, evV]
    | .param k, _, p => hparam k p
    | .call j ms, hb, p => by
      simp only [MExp.subst]
      cases hr : ruleAtM g.rules j with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = ms.length
        · have ha' : r.arity = (MExp.substArgs P ms).length := by rw [length_substArgs]; exact ha
          by_cases hs : s = .callByValueSeq
          · subst hs
            rw [evV_call_seq hr ha', evV_call_seq hr ha, evSeqArgs_rebind P W hparam ms hb]
          · rw [evV_call_par hr ha' hs, evV_call_par hr ha hs, evParArgs_rebind P W hparam ms hb]
        · have ha' : ¬ r.arity = (MExp.substArgs P ms).length := by rw [length_substArgs]; exact ha
          simp only [evV, hr, if_neg ha, if_neg ha']
    | .seq a c, hb, p => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) P W hparam a hb.1 p
      cases h : evV g x s T W a p with
      | none => rw [evV_seq_none (ha.trans h), evV_seq_none h]
      | some r =>
        cases r with
        | none => rw [evV_seq_fail (ha.trans h), evV_seq_fail h]
        | some j => rw [evV_seq_ok (ha.trans h), evV_seq_ok h]; exact evV_rebind P W hparam c hb.2 j
    | .alt a c, hb, p => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) P W hparam a hb.1 p
      cases h : evV g x s T W a p with
      | none => rw [evV_alt_none (ha.trans h), evV_alt_none h]
      | some r =>
        cases r with
        | none => rw [evV_alt_fail (ha.trans h), evV_alt_fail h]; exact evV_rebind P W hparam c hb.2 p
        | some j => rw [evV_alt_ok (ha.trans h), evV_alt_ok h]
    | .notP a, hb, p => by
      simp only [MExp.subst]
      have ha := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) P W hparam a hb p
      cases h : evV g x s T W a p with
      | none => rw [evV_not_none (ha.trans h), evV_not_none h]
      | some r =>
        cases r with
        | none => rw [evV_not_fail (ha.trans h), evV_not_fail h]
        | some j => rw [evV_not_ok (ha.trans h), evV_not_ok h]
    | .star a, hb, p => by
      simp only [MExp.subst]
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q _ => evV_rebind P W hparam a hb q)
    | .dbg _, hb, _ | .lam _ _, hb, _ | .callParam _ _, hb, _ | .invoke _ _ _, hb, _ => absurd hb id

  theorem evParArgs_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (P : List MExp) (W : List (List Char))
      (hparam : ∀ k p, evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → ∀ p,
        evParArgs g x s T E (MExp.substArgs P ms) p = evParArgs g x s T W ms p
    | [], _, p => by simp only [MExp.substArgs, evPar_nil]
    | m :: ms, hm, p => by
      simp only [MExp.substArgs]
      have hh := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) P W hparam m hm.1 p
      cases h : evV g x s T W m p with
      | none => rw [evPar_cons_none (hh.trans h), evPar_cons_none h]
      | some r =>
        cases r with
        | none => rw [evPar_cons_fail (hh.trans h), evPar_cons_fail h]
        | some j => rw [evPar_cons_ok (hh.trans h), evPar_cons_ok h, evParArgs_rebind P W hparam ms hm.2 p]

  theorem evSeqArgs_rebind {g : MGrammar} {x : List Char} {s : Strategy} {T : Nat → List (List Char) → Val}
      {E : List (List Char)} (P : List MExp) (W : List (List Char))
      (hparam : ∀ k p, evV g x s T E (MExp.subst P (.param k)) p = evV g x s T W (.param k) p) :
      ∀ (ms : List MExp), MExp.FirstOrderArgs ms → ∀ p,
        evSeqArgs g x s T E (MExp.substArgs P ms) p = evSeqArgs g x s T W ms p
    | [], _, p => by simp only [MExp.substArgs, evSeq_nil]
    | m :: ms, hm, p => by
      simp only [MExp.substArgs]
      have hh := evV_rebind (g := g) (x := x) (s := s) (T := T) (E := E) P W hparam m hm.1 p
      cases h : evV g x s T W m p with
      | none => rw [evSeq_cons_none (hh.trans h), evSeq_cons_none h]
      | some r =>
        cases r with
        | none => rw [evSeq_cons_fail (hh.trans h), evSeq_cons_fail h]
        | some j => rw [evSeq_cons_ok (hh.trans h), evSeq_cons_ok h, evSeqArgs_rebind P W hparam ms hm.2 j]
end

private theorem argAt_prefix : ∀ (control : List Nat) (k : Nat),
    argAt (control.map prefixExpr) k = (control[k]?).map prefixExpr
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: control, k+1 => by
    simpa only [List.map_cons,argAt,List.getElem?_cons_succ] using argAt_prefix control k

/-- Reconstructing a source parameter uses only consecutive target parameters,
not a literal constant containing its captured word. -/
theorem parameter_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (parts words : List (List Char)) (control : List Nat)
    (hb : ∀ k ∈ control, k ≤ parts.length)
    (hd : control.map (fun k => (parts.take k).flatten) = words) (k p : Nat) :
    evV g x s T parts (MExp.subst (control.map prefixExpr) (.param k)) p =
      evV g x s T words (.param k) p := by
  have hw : words[k]? = (control[k]?).map (fun k => (parts.take k).flatten) := by
    rw [← hd,List.getElem?_map]
  cases hc : control[k]? with
  | none => simp [MExp.subst,argAt_prefix,hc,evV,hw,MExp.failAlways]
  | some r =>
    have hr := hb r (List.mem_of_getElem? hc)
    simpa only [MExp.subst,argAt_prefix,hc,Option.map_some,evV,hw] using
      prefixExpr_eval g x s T parts r hr p

/-- All first-order uses of a represented environment preserve the full
three-valued evaluator. Calls remain calls into the same grammar/table. -/
theorem body_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (parts words : List (List Char)) (control : List Nat)
    (hb : ∀ k ∈ control, k ≤ parts.length)
    (hd : control.map (fun k => (parts.take k).flatten) = words)
    (e : MExp) (he : e.FirstOrder) (p : Nat) :
    evV g x s T parts (MExp.subst (control.map prefixExpr) e) p = evV g x s T words e p :=
  evV_rebind _ words (parameter_view g x s T parts words control hb hd) e he p

/-- Arbitrary common-origin captures can be kept in disjoint runtime values;
their finite rank control suffices for every first-order body expression. -/
theorem common_origin_body {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (e : MExp) (he : e.FirstOrder) (p : Nat) :
    evV g x s T (CommonOriginCaptures.chunks words)
      (MExp.subst ((CommonOriginCaptures.ranks words).map prefixExpr) e) p =
        evV g x s T words e p :=
  body_view g x s T _ words _
    (by simpa only [CommonOriginCaptures.chunks_length] using CommonOriginCaptures.ranks_bounded hp)
    (CommonOriginCaptures.reconstruct hp) e he p

def variants (arity : Nat) (e : MExp) : List MExp :=
  (CommonOriginCaptures.controls arity arity).map (fun C => MExp.subst (C.map prefixExpr) e)

theorem variants_length (arity : Nat) (e : MExp) :
    (variants arity e).length = (arity+1)^arity := by
  simp only [variants,List.length_map,CommonOriginCaptures.controls_length]

private theorem prefixArgs_firstOrder : ∀ C : List Nat, MExp.FirstOrderArgs (C.map prefixExpr)
  | [] => trivial
  | k :: C => ⟨prefixExpr_firstOrder k,prefixArgs_firstOrder C⟩

/-- All possible body views can be compiled before the input is known.
Selecting the correct variant and constructing its runtime chunks remain
separate obligations of a complete grammar translation. -/
theorem finite_body_choice {input : List Char} {words : List (List Char)}
    (hp : ∀ w ∈ words, w <+: input) (e : MExp) (he : e.FirstOrder) :
    ∃ target ∈ variants words.length e, target.FirstOrder ∧
      ∀ (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val) (p : Nat),
        evV g x s T (CommonOriginCaptures.chunks words) target p = evV g x s T words e p := by
  refine ⟨MExp.subst ((CommonOriginCaptures.ranks words).map prefixExpr) e,?_,?_,?_⟩
  · exact List.mem_map.mpr ⟨_,CommonOriginCaptures.ranks_mem_controls hp,rfl⟩
  · exact firstOrder_subst (prefixArgs_firstOrder _) e he
  · intro g x s T p
    exact common_origin_body hp g x s T e he p

/-- The full value-level bridge for arbitrary successful Par arguments:
disjoint Seq values, finite static body variants, and exact local body
evaluation. No source grammar or argument syntax restriction is imposed. -/
theorem par_body_representation {g : MGrammar} {s : Strategy} {input : List Char}
    {args vals : List MExp} (h : DerivesArgsPar g s input args vals)
    (e : MExp) (he : e.FirstOrder) :
    ∃ (words parts : List (List Char)) (rest : List Char) (target : MExp),
      vals = words.map MExp.lit ∧ parts.length = args.length ∧
      target ∈ variants args.length e ∧ target.FirstOrder ∧
      input = parts.flatten ++ rest ∧
      DerivesArgsSeq g s input (parts.map MExp.lit) (parts.map MExp.lit) rest ∧
      ∀ (G : MGrammar) (x : List Char) (strategy : Strategy)
        (T : Nat → List (List Char) → Val) (p : Nat),
        evV G x strategy T parts target p = evV G x strategy T words e p := by
  obtain ⟨words,hv,hlen,hp⟩ := CommonOriginCaptures.par_prefixes h
  obtain ⟨target,hm,hfo,hbody⟩ := finite_body_choice hp e he
  obtain ⟨rest,hr⟩ := CommonOriginCaptures.chunks_prefix hp
  refine ⟨words,CommonOriginCaptures.chunks words,rest,target,hv,?_,?_,hfo,hr.symm,?_,hbody⟩
  · exact (CommonOriginCaptures.chunks_length words).trans hlen
  · simpa only [hlen] using hm
  · exact (SequentialCaptures.forward_iff _ _ _ _ _ _).mpr ⟨rfl,hr.symm⟩

end Shallot.MacroPeg.CBV.CaptureViews
