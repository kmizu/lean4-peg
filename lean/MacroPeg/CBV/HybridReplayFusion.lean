import MacroPeg.CBV.HybridFlags
import MacroPeg.CBV.LiteralSpecialization
import MacroPeg.CBV.CallLookahead

/-! Retain one unbounded runtime capture while specializing finitely many
auxiliary literal values. Source bodies replay the head capture before their tail. -/
namespace Shallot.MacroPeg.CBV.HybridReplayFusion
open HybridFlags
open LiteralSpecialization (vectors mem_vectors)

def Supported (d : Nat) (V : List (List Char)) : MExp → Prop
  | .call _ (a::args) => args.length=d ∧ Supported d V a ∧ ∀ b ∈ args, Flag V b
  | .call _ [] => False
  | .seq a b | .alt a b => Supported d V a ∧ Supported d V b
  | .star a | .notP a => Supported d V a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => False

theorem supported_firstOrder (d : Nat) (V : List (List Char)) : ∀ e, Supported d V e → e.FirstOrder
  | .call _ (a::_), h => ⟨supported_firstOrder d V a h.2.1,args_firstOrder h.2.2⟩
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder d V a h.1,supported_firstOrder d V b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder d V a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

def parGrammar (d : Nat) (tails : List MExp) : MGrammar :=
  ⟨tails.map (fun body => ⟨d+1,.seq (.param 0) body⟩)⟩

def specs (d : Nat) (V : List (List Char)) (tails : List MExp) : List (Nat × List (List Char)) :=
  (List.range tails.length).flatMap (fun i => (vectors V d).map (fun F => (i,F)))

def code (d : Nat) (V : List (List Char)) (tails : List MExp) (i : Nat) (F : List (List Char)) : Nat :=
  indexIn (i,F) (specs d V tails)

theorem mem_specs {d : Nat} {V F : List (List Char)} {tails : List MExp} {i : Nat} {body : MExp}
    (hr : tails[i]?=some body) (hn : F.length=d) (hF : ∀ w ∈ F, w ∈ V) : (i,F) ∈ specs d V tails := by
  exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr (List.getElem?_eq_some_iff.mp hr).1,
    List.mem_map.mpr ⟨F,(mem_vectors V d F).mpr ⟨hn,hF⟩,rfl⟩⟩

def compile (d : Nat) (V : List (List Char)) (tails : List MExp) (F : List (List Char)) : MExp → MExp
  | .param 0 => .param 0
  | .param (k+1) => match F[k]? with | some w => .lit w | none => MExp.failAlways
  | .call i (a::args) => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if args.length=d then .seq (.andP (compile d V tails F a))
      (match resolve F args with
      | none => MExp.failAlways
      | some W => .seq (LiteralArguments.guards W) (.call (code d V tails i W) [compile d V tails F a]))
      else MExp.failAlways
  | .seq a b => .seq (compile d V tails F a) (compile d V tails F b)
  | .alt a b => .alt (compile d V tails F a) (compile d V tails F b)
  | .star a => .star (compile d V tails F a)
  | .notP a => .notP (compile d V tails F a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .call _ [] | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem compile_firstOrder (d : Nat) (V : List (List Char)) (tails : List MExp) (F : List (List Char)) :
    ∀ e, (compile d V tails F e).FirstOrder
  | .param 0 => trivial
  | .param (k+1) => by simp only [compile]; split <;> trivial
  | .call i (a::args) => by
    have ha := compile_firstOrder d V tails F a
    simp only [compile]
    split
    · trivial
    · split
      · refine ⟨ha,?_⟩
        split
        · trivial
        · exact ⟨LiteralArguments.guards_firstOrder _,ha,trivial⟩
      · trivial
  | .seq a b | .alt a b => ⟨compile_firstOrder d V tails F a,compile_firstOrder d V tails F b⟩
  | .star a | .notP a => compile_firstOrder d V tails F a
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ [] | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

def seqGrammar (d : Nat) (V : List (List Char)) (tails : List MExp) : MGrammar :=
  ⟨(specs d V tails).map (fun q => ⟨1,match tails[q.1]? with
    | some body => compile d V tails q.2 body | none => MExp.failAlways⟩)⟩

theorem target_arity_one (d : Nat) (V : List (List Char)) (tails : List MExp) :
    ∀ r ∈ (seqGrammar d V tails).rules, r.arity=1 := by
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  rfl

theorem par_rule (d : Nat) (tails : List MExp) (i : Nat) : ruleAtM (parGrammar d tails).rules i =
    (tails[i]?).map (fun body => ⟨d+1,.seq (.param 0) body⟩) := by
  simp [parGrammar,ruleAtM_eq_getElem?]

theorem seq_rule {d : Nat} {V F : List (List Char)} {tails : List MExp} {i : Nat} {body : MExp}
    (hr : tails[i]?=some body) (hn : F.length=d) (hF : ∀ w ∈ F, w ∈ V) :
    ruleAtM (seqGrammar d V tails).rules (code d V tails i F) = some ⟨1,compile d V tails F body⟩ := by
  have hm := mem_specs hr hn hF
  simp [seqGrammar,code,ruleAtM_eq_getElem?,List.getElem?_map,getElem?_indexIn _ _ hm,hr]

theorem par_firstOrder {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) : (parGrammar d tails).FirstOrder := by
  intro r hr
  obtain ⟨body,hbody,rfl⟩ := List.mem_map.mp hr
  exact ⟨trivial,supported_firstOrder d V body (hf body hbody)⟩

theorem seq_firstOrder (d : Nat) (V : List (List Char)) (tails : List MExp) : (seqGrammar d V tails).FirstOrder := by
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  split
  · exact compile_firstOrder _ _ _ _ _
  · trivial

def Shifted (d : Nat) (V : List (List Char)) (tails : List MExp) (x : List Char)
    (T U : Nat → List (List Char) → Val) : Prop :=
  ∀ i body, tails[i]?=some body → ∀ F, F.length=d → (∀ w ∈ F, w ∈ V) →
    ∀ w p q, p ≤ x.length → q ≤ x.length → sfx x p=w++sfx x q →
      valAt (T i (w::F)) p = valAt (U (code d V tails i F) [w]) q

theorem evaluator_of_shift {d : Nat} {V : List (List Char)} {tails : List MExp} {x : List Char}
    {T U : Nat → List (List Char) → Val} (hT : SoundTV (parGrammar d tails) x .callByValuePar T)
    (hOk : OkTV x.length T) (hshift : Shifted d V tails x T U) :
    ∀ e, Supported d V e → ∀ H F, Head H F → (∀ w ∈ F, w ∈ V) → ∀ p, p ≤ x.length →
      evV (parGrammar d tails) x .callByValuePar T (H++F) e p =
        evV (seqGrammar d V tails) x .callByValueSeq U H (compile d V tails F e) p
  | .eps, _, _, _, _, _, _, _ | .any, _, _, _, _, _, _, _ | .chr _, _, _, _, _, _, _, _
  | .range _ _, _, _, _, _, _, _, _ | .lit _, _, _, _, _, _, _, _ => rfl
  | .param k, _, H, F, hH, _, p, _ => by
    cases H with
    | nil =>
      have hf := hH.2 rfl
      subst F
      cases k <;> simp [compile,evV,MExp.failAlways]
    | cons w H =>
      have he : H=[] := List.eq_nil_of_length_eq_zero (by have hb := hH.1; change H.length+1 ≤ 1 at hb; omega)
      subst H
      cases k with
      | zero => simp [compile,evV]
      | succ k => cases hh : F[k]? <;> simp [compile,evV,hh,MExp.failAlways]
  | .call _ [], hf, _, _, _, _, _, _ | .dbg _, hf, _, _, _, _, _, _ | .lam _ _, hf, _, _, _, _, _, _
  | .callParam _ _, hf, _, _, _, _, _, _ | .invoke _ _ _, hf, _, _, _, _, _, _ => False.elim hf
  | .call i (a::args), hf, H, F, hH, hF, p, hp => by
    cases hr : tails[i]? with
    | none => simp [compile,evV,par_rule,hr,MExp.failAlways]
    | some body =>
      have hpr : ruleAtM (parGrammar d tails).rules i=some ⟨d+1,.seq (.param 0) body⟩ := by rw [par_rule,hr]; rfl
      have ha : d+1=(a::args).length := by simp [hf.1]
      rw [evV_call_par hpr ha (by decide)]
      simp only [compile,hr,if_pos hf.1]
      have heq := evaluator_of_shift hT hOk hshift a hf.2.1 H F hH hF p hp
      have hg : evV (seqGrammar d V tails) x .callByValueSeq U H (.andP (compile d V tails F a)) p =
          CallLookahead.peek p (evV (parGrammar d tails) x .callByValuePar T (H++F) a p) := by
        rw [CallLookahead.evV_peek,← heq]
      rw [evParArgs]
      cases hv : evV (parGrammar d tails) x .callByValuePar T (H++F) a p with
      | none =>
        rw [hv] at hg
        change evV (seqGrammar d V tails) x .callByValueSeq U H (.andP (compile d V tails F a)) p = none at hg
        rw [evV_seq_none hg]
      | some result =>
        cases result with
        | none =>
          rw [hv] at hg
          change evV (seqGrammar d V tails) x .callByValueSeq U H (.andP (compile d V tails F a)) p = some none at hg
          rw [evV_seq_fail hg]
        | some q =>
          rw [hv] at hg
          change evV (seqGrammar d V tails) x .callByValueSeq U H (.andP (compile d V tails F a)) p = some (some p) at hg
          rw [evV_seq_ok hg]
          dsimp only
          rw [HybridFlags.args_eval (parGrammar d tails) x .callByValuePar T hH args hf.2.2 p]
          rw [LiteralArguments.arguments_eval (parGrammar d tails) x .callByValuePar T F p hp
            (lowerArgs args) (lower_supported hf.2.2)]
          simp only [HybridFlags.resolve]
          cases hc : LiteralArguments.resolveArgs F (lowerArgs args) with
          | none => simp [evV,MExp.failAlways]
          | some C =>
            have hb := resolve_bounds hF hf.2.2 hc
            have hlen : C.length=d := hb.1.trans hf.1
            have htr := seq_rule hr hlen hb.2
            simp only []
            cases hgood : LiteralArguments.good x p C with
            | false =>
              have hguard : evV (seqGrammar d V tails) x .callByValueSeq U H (LiteralArguments.guards C) p=some none := by
                rw [LiteralArguments.guards_eval]; simp [hgood]
              rw [evV_seq_fail hguard]
              rfl
            | true =>
              have hguard : evV (seqGrammar d V tails) x .callByValueSeq U H (LiteralArguments.guards C) p=some (some p) := by
                rw [LiteralArguments.guards_eval]; simp [hgood]
              rw [evV_seq_ok hguard,evV_call_seq htr (by rfl)]
              simp only [evSeqArgs,heq.symm.trans hv]
              obtain ⟨hq,hpre⟩ := ReplayFusion.success_prefix hT (H++F) a (supported_firstOrder d V a hf.2.1) p q hp hv
              exact hshift i body hr C hlen hb.2 (pre x p q) p q hp hq hpre
  | .seq a b, hf, H, F, hH, hF, p, hp => by
    simp only [compile]
    have heq := evaluator_of_shift hT hOk hshift a hf.1 H F hH hF p hp
    cases hv : evV (parGrammar d tails) x .callByValuePar T (H++F) a p with
    | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some v =>
      cases v with
      | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b hf.2 H F hH hF q (evV_ok hOk a p hp q hv)
  | .alt a b, hf, H, F, hH, hF, p, hp => by
    simp only [compile]
    have heq := evaluator_of_shift hT hOk hshift a hf.1 H F hH hF p hp
    cases hv : evV (parGrammar d tails) x .callByValuePar T (H++F) a p with
    | none => rw [evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some v =>
      cases v with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_shift hT hOk hshift b hf.2 H F hH hF p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .notP a, hf, H, F, hH, hF, p, hp => by
    simp only [compile,evV]
    rw [evaluator_of_shift hT hOk hshift a hf H F hH hF p hp]
  | .star a, hf, H, F, hH, hF, p, hp => by
    simp only [compile]
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift hT hOk hshift a hf H F hH hF q (by omega))

theorem tables_shifted {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) (x : List Char) (m : Nat) :
    Shifted d V tails x (tblV (parGrammar d tails) x .callByValuePar m)
      (tblV (seqGrammar d V tails) x .callByValueSeq m) := by
  induction m with
  | zero => intro i body hr F hn hF w p q hp hq hs; rfl
  | succ m ih =>
    intro i body hr F hn hF w p q hp hq hs
    have hrp : ruleAtM (parGrammar d tails).rules i=some ⟨d+1,.seq (.param 0) body⟩ := by rw [par_rule,hr]; rfl
    have hrs := seq_rule hr hn hF
    rw [valAt_tblV_succ hrp (w::F) hp,valAt_tblV_succ hrs [w] hq]
    have hstrip := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr hs
    simp only [evV,List.getElem?_cons_zero,hstrip,length_sfx x hq]
    exact evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) m)
      (tblV_ok _ _ _ m) ih body (hf body (List.mem_of_getElem? hr)) [w] F (by simp [Head]) hF q hq

theorem evaluator_eq {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) {e : MExp} (he : Supported d V e)
    (x : List Char) (m : Nat) :
    evV (parGrammar d tails) x .callByValuePar (tblV (parGrammar d tails) x .callByValuePar m) [] e x.length =
      evV (seqGrammar d V tails) x .callByValueSeq (tblV (seqGrammar d V tails) x .callByValueSeq m) []
        (compile d V tails [] e) x.length :=
  evaluator_of_shift (tblV_sound (par_firstOrder hf) (by decide) m) (tblV_ok _ _ _ m)
    (tables_shifted hf x m) e he [] [] (by simp [Head]) (by simp) _ (Nat.le_refl _)

theorem limit_eq {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) {e : MExp} (he : Supported d V e) (x : List Char) :
    evV (parGrammar d tails) x .callByValuePar
      (tblV (parGrammar d tails) x .callByValuePar (iterBoundV (parGrammar d tails) x)) [] e x.length =
    evV (seqGrammar d V tails) x .callByValueSeq
      (tblV (seqGrammar d V tails) x .callByValueSeq (iterBoundV (seqGrammar d V tails) x)) []
      (compile d V tails [] e) x.length := by
  cases hs : evV (parGrammar d tails) x .callByValuePar
      (tblV (parGrammar d tails) x .callByValuePar (iterBoundV (parGrammar d tails) x)) [] e x.length with
  | none =>
    cases ht : evV (seqGrammar d V tails) x .callByValueSeq
      (tblV (seqGrammar d V tails) x .callByValueSeq (iterBoundV (seqGrammar d V tails) x)) []
      (compile d V tails [] e) x.length with
    | none => rfl
    | some v =>
      have hh := (tblV_stable (parGrammar d tails) x .callByValuePar (Nat.le_refl _)).mp
        ⟨iterBoundV (seqGrammar d V tails) x,(evaluator_eq hf he x _).trans ht⟩
      rw [hs] at hh
      cases hh
  | some v =>
    have hh := (tblV_stable (seqGrammar d V tails) x .callByValueSeq (Nat.le_refl _)).mp
      ⟨iterBoundV (parGrammar d tails) x,(evaluator_eq hf he x _).symm.trans hs⟩
    exact hh.symm

theorem decide_eq {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) {e : MExp} (he : Supported d V e) (x : List Char) :
    decideObsV .callByValuePar (parGrammar d tails) x e =
      decideObsV .callByValueSeq (seqGrammar d V tails) x (compile d V tails [] e) := by
  unfold decideObsV
  rw [limit_eq hf he x]

/-- Finite flags are specialized, but the head word is kept as a runtime
capture of arbitrary length. All finite observations on original inputs agree. -/
theorem observations_iff {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) {e : MExp} (he : Supported d V e)
    (x : List Char) (r : Option (List Char)) :
    SObs (parGrammar d tails) .callByValuePar e x r ↔
      SObs (seqGrammar d V tails) .callByValueSeq (compile d V tails [] e) x r := by
  rw [← decideObsV_iff (par_firstOrder hf) (by decide) (supported_firstOrder d V e he),
    ← decideObsV_iff (seq_firstOrder d V tails) (by decide) (compile_firstOrder _ _ _ _ _),decide_eq hf he x]

theorem language_translation {d : Nat} {V : List (List Char)} {tails : List MExp}
    (hf : ∀ body ∈ tails, Supported d V body) {e : MExp} (he : Supported d V e) :
    ∃ (out : MGrammar) (start : MExp), out.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (parGrammar d tails) .callByValuePar e x (some []) ↔
        SObs out .callByValueSeq start x (some []) :=
  ⟨seqGrammar d V tails,compile d V tails [] e,seq_firstOrder _ _ _,compile_firstOrder _ _ _ _ _,
    fun x => observations_iff hf he x (some [])⟩

end Shallot.MacroPeg.CBV.HybridReplayFusion
