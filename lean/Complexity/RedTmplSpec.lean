import Complexity.RedTmpl

/-!
# Correctness of the reduction template

`redTmpl_denote`: the template `redTmpl M` describes, in the environment `⟨w, S, blockSize M S, ctr⟩`, the token list
of the QBF `redQbf M S w`.
-/

namespace Complexity

/-! ## Environment facts -/

section Env

@[simp] private theorem TEnv.set_S (e : TEnv) (i v : Nat) : (e.set i v).S = e.S := rfl
@[simp] private theorem TEnv.set_T (e : TEnv) (i v : Nat) : (e.set i v).T = e.T := rfl
@[simp] private theorem TEnv.set_w (e : TEnv) (i v : Nat) : (e.set i v).w = e.w := rfl
@[simp] private theorem TEnv.set_ctr_self (e : TEnv) (i v : Nat) : (e.set i v).ctr i = v := by simp [TEnv.set]
private theorem TEnv.set_ctr_ne (e : TEnv) {i j : Nat} (v : Nat) (h : j ≠ i) : (e.set i v).ctr j = e.ctr j := by
  simp [TEnv.set, h]

/-- A part depending on the counter `0` only. -/
private def Part.Z : Part → Prop
  | .const _ => True
  | .ctr i => i = 0
  | .rev i _ => i = 0

private theorem Part.val_set {p : Part} (h : p.Z) {n : Nat} (hn : n ≠ 0) (e : TEnv) (v : Nat) :
    p.val (e.set n v) = p.val e := by
  cases p with
  | const m => rfl
  | ctr i => simp only [Part.Z] at h; subst h; simp [Part.val, TEnv.set_ctr_ne e v hn.symm]
  | rev i c => simp only [Part.Z] at h; subst h; simp [Part.val, TEnv.set_ctr_ne e v hn.symm]

/-- A tag: a list of parts depending on the counter `0` only. -/
private def Free (b : List Part) : Prop := ∀ p ∈ b, p.Z

private theorem Free.map_set {b : List Part} (h : Free b) {n : Nat} (hn : n ≠ 0) (e : TEnv) (v : Nat) :
    b.map (Part.val (e.set n v)) = b.map (Part.val e) := by
  apply List.map_congr_left
  intro p hp
  exact Part.val_set (h p hp) hn e v

private theorem free_const (l : List Nat) : Free (l.map Part.const) := by
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨_, _, rfl⟩ := hp
  trivial

end Env

/-! ## List helpers -/

private theorem fm_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_congr_left h]

private theorem flatMap_ite_nil {α β : Type} (p : α → Bool) (A : α → List β) :
    ∀ l : List α, l.flatMap (fun v => if p v = true then A v else []) = (l.filter p).flatMap A
  | [] => rfl
  | x :: xs => by
    by_cases h : p x = true
    · simp [List.filter_cons, h, flatMap_ite_nil p A xs]
    · simp [List.filter_cons, h, flatMap_ite_nil p A xs]

private theorem flatMap_single_const {α β : Type} (t : β) : ∀ l : List α, l.flatMap (fun _ => [t]) = List.replicate l.length t
  | [] => rfl
  | x :: xs => by simp [flatMap_single_const t xs, List.replicate_succ]

private theorem replicate_length_flatMap {α β γ : Type} (t : γ) (g : α → List β) :
    ∀ l : List α, List.replicate (l.flatMap g).length t = l.flatMap (fun x => List.replicate (g x).length t)
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, ← List.replicate_append_replicate, replicate_length_flatMap t g xs,
      List.flatMap_cons]

private theorem pairsOf_map {α β : Type} (f : α → β) : ∀ l : List α,
    pairsOf (l.map f) = (pairsOf l).map (fun p => (f p.1, f p.2))
  | [] => rfl
  | x :: xs => by simp [pairsOf, pairsOf_map f xs, List.map_map, Function.comp_def]

private theorem pairsOf_range' {α : Type} (f : Nat → α) : ∀ (n s : Nat),
    pairsOf ((List.range' s n).map f) =
      (List.range' s n).flatMap (fun a => ((List.range' s n).filter (fun b => decide (a < b))).map (fun b => (f a, f b)))
  | 0, s => rfl
  | n + 1, s => by
    have ih := pairsOf_range' f n (s + 1)
    have e1 : List.range' s (n + 1) = s :: List.range' (s + 1) n := List.range'_succ
    have h1 : (s :: List.range' (s + 1) n).filter (fun b => decide (s < b)) = List.range' (s + 1) n := by
      rw [List.filter_cons]
      simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false]
      apply List.filter_eq_self.2
      intro b hb
      simp only [List.mem_range'_1] at hb
      simp; omega
    have h2 : ∀ a ∈ List.range' (s + 1) n, (s :: List.range' (s + 1) n).filter (fun b => decide (a < b)) =
        (List.range' (s + 1) n).filter (fun b => decide (a < b)) := by
      intro a ha
      simp only [List.mem_range'_1] at ha
      rw [List.filter_cons]
      have : ¬ (a < s) := by omega
      simp [this]
    rw [e1, List.map_cons, pairsOf, List.flatMap_cons, h1, ih]
    simp only [List.map_map, Function.comp_def]
    congr 1
    apply fm_congr
    intro a ha
    rw [h2 a ha]

private theorem pairsOf_range {α : Type} (f : Nat → α) (n : Nat) :
    pairsOf ((List.range n).map f) =
      (List.range n).flatMap (fun a => ((List.range n).filter (fun b => decide (a < b))).map (fun b => (f a, f b))) := by
  simpa [List.range_eq_range'] using pairsOf_range' f n 0

private theorem finRange_map_val {α : Type} (k : Nat) (g : Nat → α) :
    (List.finRange k).map (fun i => g i.val) = (List.range k).map g := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp


/-! ## Combinators -/

section Comb

variable (e : TEnv)

private theorem den_var (ps : List Part) : (T.var ps).denote e = rpnEnc (.var (ps.map (Part.val e))) := by
  simp [T.var, Tmpl.denote, rpnEnc_var]

private theorem den_not {a : Tmpl} {φ : Formula} (h : a.denote e = rpnEnc φ) : (T.not a).denote e = rpnEnc (.not φ) := by
  simp [T.not, Tmpl.denote, h, rpnEnc_not]

private theorem den_and {a b : Tmpl} {φ ψ : Formula} (ha : a.denote e = rpnEnc φ) (hb : b.denote e = rpnEnc ψ) :
    (T.and a b).denote e = rpnEnc (.and φ ψ) := by
  simp [T.and, Tmpl.denote_seqs, Tmpl.denote, ha, hb, rpnEnc_and]

private theorem den_or {a b : Tmpl} {φ ψ : Formula} (ha : a.denote e = rpnEnc φ) (hb : b.denote e = rpnEnc ψ) :
    (T.or a b).denote e = rpnEnc (.or φ ψ) := by
  simp [T.or, Tmpl.denote_seqs, Tmpl.denote, ha, hb, rpnEnc_or]

private theorem den_iff {a b : Tmpl} {φ ψ : Formula} (ha : a.denote e = rpnEnc φ) (hb : b.denote e = rpnEnc ψ) :
    (T.iff a b).denote e = rpnEnc (Formula.iff φ ψ) := by
  simp only [T.iff, Formula.iff]
  exact den_or e (den_and e ha hb) (den_and e (den_not e ha) (den_not e hb))

private theorem den_bigAndL {α : Type} (l : List α) (f : α → Tmpl) (g : α → Formula)
    (h : ∀ x ∈ l, (f x).denote e = rpnEnc (g x)) :
    (T.bigAndL (l.map f)).denote e = rpnEnc (bigAnd (l.map g)) := by
  rw [rpnEnc_bigAnd, T.bigAndL, Tmpl.denote_seqs]
  simp only [List.flatMap_append, List.flatMap_map, List.map_map, Function.comp_def, List.length_map]
  rw [fm_congr (g := fun x => rpnEnc (g x)) h]
  simp [Tmpl.denote, flatMap_single_const]

private theorem den_bigOrL {α : Type} (l : List α) (f : α → Tmpl) (g : α → Formula)
    (h : ∀ x ∈ l, (f x).denote e = rpnEnc (g x)) :
    (T.bigOrL (l.map f)).denote e = rpnEnc (bigOr (l.map g)) := by
  rw [rpnEnc_bigOr, T.bigOrL, Tmpl.denote_seqs]
  simp only [List.flatMap_append, List.flatMap_map, List.map_map, Function.comp_def, List.length_map]
  rw [fm_congr (g := fun x => rpnEnc (g x)) h]
  simp [Tmpl.denote, flatMap_single_const]

private theorem den_bigAndF (i : Nat) (b : Bound) (c : Cond) (body : Tmpl) (g : Nat → Formula)
    (h : ∀ v ∈ List.range (b.val e), c.eval (e.set i v) = true → body.denote (e.set i v) = rpnEnc (g v)) :
    (T.bigAndF i b c body).denote e =
      rpnEnc (bigAnd (((List.range (b.val e)).filter (fun v => c.eval (e.set i v))).map g)) := by
  rw [rpnEnc_bigAnd, T.bigAndF, Tmpl.denote_seqs]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Tmpl.denote, List.length_map]
  rw [flatMap_ite_nil (fun v => c.eval (e.set i v)), flatMap_ite_nil (fun v => c.eval (e.set i v)),
    flatMap_single_const, List.flatMap_map]
  have key : ((List.range (b.val e)).filter (fun v => c.eval (e.set i v))).flatMap (fun v => body.denote (e.set i v)) =
      ((List.range (b.val e)).filter (fun v => c.eval (e.set i v))).flatMap (fun a => rpnEnc (g a)) := by
    apply fm_congr
    intro v hv
    rw [List.mem_filter] at hv
    exact h v hv.1 hv.2
  rw [key, List.append_assoc]

private theorem den_bigOrF (i : Nat) (b : Bound) (c : Cond) (body : Tmpl) (g : Nat → Formula)
    (h : ∀ v ∈ List.range (b.val e), c.eval (e.set i v) = true → body.denote (e.set i v) = rpnEnc (g v)) :
    (T.bigOrF i b c body).denote e =
      rpnEnc (bigOr (((List.range (b.val e)).filter (fun v => c.eval (e.set i v))).map g)) := by
  rw [rpnEnc_bigOr, T.bigOrF, Tmpl.denote_seqs]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Tmpl.denote, List.length_map]
  rw [flatMap_ite_nil (fun v => c.eval (e.set i v)), flatMap_ite_nil (fun v => c.eval (e.set i v)),
    flatMap_single_const, List.flatMap_map]
  have key : ((List.range (b.val e)).filter (fun v => c.eval (e.set i v))).flatMap (fun v => body.denote (e.set i v)) =
      ((List.range (b.val e)).filter (fun v => c.eval (e.set i v))).flatMap (fun a => rpnEnc (g a)) := by
    apply fm_congr
    intro v hv
    rw [List.mem_filter] at hv
    exact h v hv.1 hv.2
  rw [key, List.append_assoc]

end Comb

section BlockDen

variable {k : Nat} (M : TM k) (S : Nat) (e : TEnv)

private theorem den_block (hS : e.S = S) (body : List Part → Tmpl) (G : List Nat → List Nat)
    (hs : ∀ q ∈ List.range M.nq, (body [.const 0, .const q]).denote e = G [0, q])
    (hh : ∀ i ∈ List.range k, ∀ j ∈ List.range S, (body [.const 1, .const i, .ctr 1]).denote (e.set 1 j) = G [1, i, j])
    (hc : ∀ i ∈ List.range k, ∀ j ∈ List.range S, ∀ s ∈ List.range M.na,
      (body [.const 2, .const i, .ctr 1, .const s]).denote (e.set 1 j) = G [2, i, j, s]) :
    (Tmpl.seqs (T.block M body)).denote e = (blockSuf M S).flatMap G := by
  rw [Tmpl.denote_seqs]
  simp only [T.block, blockSuf, sSuf, hSuf, cSuf, List.flatMap_append, List.flatMap_map, List.flatMap_assoc,
    Tmpl.denote, Tmpl.denote_seqs, Bound.val, hS, List.map_flatMap]
  congr 1
  · congr 1
    · exact fm_congr hs
    · apply fm_congr
      intro i hi
      exact fm_congr (hh i hi)
  · apply fm_congr
    intro i hi
    apply fm_congr
    intro j hj
    exact fm_congr (fun s hs => hc i hi j hj s hs)

private theorem den_bigAndBlock (hS : e.S = S) (body : List Part → Tmpl) (g : List Nat → Formula)
    (hs : ∀ q ∈ List.range M.nq, (body [.const 0, .const q]).denote e = rpnEnc (g [0, q]))
    (hh : ∀ i ∈ List.range k, ∀ j ∈ List.range S, (body [.const 1, .const i, .ctr 1]).denote (e.set 1 j) = rpnEnc (g [1, i, j]))
    (hc : ∀ i ∈ List.range k, ∀ j ∈ List.range S, ∀ s ∈ List.range M.na,
      (body [.const 2, .const i, .ctr 1, .const s]).denote (e.set 1 j) = rpnEnc (g [2, i, j, s])) :
    (T.bigAndBlock M body).denote e = rpnEnc (bigAnd ((blockSuf M S).map g)) := by
  have h1 := den_block M S e hS body (fun v => rpnEnc (g v)) hs hh hc
  have h2 := den_block M S e hS (fun _ => .tok Tok.conj) (fun _ => [Tok.conj])
    (by simp [Tmpl.denote]) (by simp [Tmpl.denote]) (by simp [Tmpl.denote])
  rw [Tmpl.denote_seqs] at h1 h2
  rw [rpnEnc_bigAnd, T.bigAndBlock, Tmpl.denote_seqs, List.flatMap_append, List.flatMap_append, h1, h2]
  simp [Tmpl.denote, flatMap_single_const, List.flatMap_map, Function.comp_def]

end BlockDen


/-! ## Pieces -/

section Pieces

variable {k : Nat} (M : TM k) (S : Nat) (e : TEnv)

private theorem den_var_val (b v : List Part) :
    (T.var (b ++ v)).denote e = rpnEnc (.var (b.map (Part.val e) ++ v.map (Part.val e))) := by
  rw [den_var]; simp

private theorem den_iffvar (b b' v : List Part) :
    (T.iff (T.var (b ++ v)) (T.var (b' ++ v))).denote e =
      rpnEnc (Formula.iff (.var (b.map (Part.val e) ++ v.map (Part.val e)))
        (.var (b'.map (Part.val e) ++ v.map (Part.val e)))) :=
  den_iff e (den_var_val e _ _) (den_var_val e _ _)

private theorem den_eqT (hS : e.S = S) {b b' : List Part} (hb : Free b) (hb' : Free b') :
    (eqT M b b').denote e = rpnEnc (eqF M S (b.map (Part.val e)) (b'.map (Part.val e))) := by
  rw [eqT, den_bigAndBlock M S e hS _
    (fun v => Formula.iff (.var (b.map (Part.val e) ++ v)) (.var (b'.map (Part.val e) ++ v)))]
  · rfl
  · intro q _
    rw [den_iffvar]; simp [Part.val]
  · intro i _ j _
    rw [den_iffvar, hb.map_set (by decide), hb'.map_set (by decide)]; simp [Part.val]
  · intro i _ j _ s _
    rw [den_iffvar, hb.map_set (by decide), hb'.map_set (by decide)]; simp [Part.val]

/-- The quantifier tokens of a block. -/
private def QB (kind : Nat) (tg : Name) : List Nat := (blockVars M S tg).flatMap (fun x => kind :: encName x)

private theorem den_quantBlock (hS : e.S = S) (kind : Nat) {tag : List Part} (ht : Free tag) :
    (quantBlockT M kind tag).denote e = QB M S kind (tag.map (Part.val e)) := by
  rw [quantBlockT]
  rw [den_block M S e hS _ (fun v => kind :: encName (tag.map (Part.val e) ++ v))]
  · simp [QB, blockVars, List.flatMap_map, Function.comp_def]
  · intro q _; simp [Tmpl.denote, Part.val]
  · intro i _ j _
    simp [Tmpl.denote, ht.map_set (show 1 ≠ 0 by decide), Part.val]
  · intro i _ j _ s _
    simp [Tmpl.denote, ht.map_set (show 1 ≠ 0 by decide), Part.val]


private theorem den_ite (c : Cond) (a b : Tmpl) : (Tmpl.ite c a b).denote e = if c.eval e then a.denote e else b.denote e := rfl

private theorem den_not_var (b v : List Part) :
    (T.not (T.var (b ++ v))).denote e = rpnEnc (.not (.var (b.map (Part.val e) ++ v.map (Part.val e)))) :=
  den_not e (den_var_val e _ _)

private def initBody (tag : List Part) : List Part → Tmpl
  | [.const 0, .const q] => if q = 2 then T.var (tag ++ [.const 0, .const q])
      else T.not (T.var (tag ++ [.const 0, .const q]))
  | [.const 1, .const i, .ctr 1] => .ite (.eqc 1 0) (T.var (tag ++ [.const 1, .const i, .ctr 1]))
      (T.not (T.var (tag ++ [.const 1, .const i, .ctr 1])))
  | [.const 2, .const i, .ctr 1, .const s] => .ite (initCellCond i s) (T.var (tag ++ [.const 2, .const i, .ctr 1, .const s]))
      (T.not (T.var (tag ++ [.const 2, .const i, .ctr 1, .const s])))
  | _ => .nil

private theorem initT_eq (tag : List Part) : initT M tag = T.bigAndBlock M (initBody tag) := by
  simp only [initT, T.bigAndBlock, T.block, List.append_assoc]
  rfl

private theorem initCond_eval (w : List Bool) (hw : e.w = w) (i s j : Nat) :
    (initCellCond i s).eval (e.set 1 j) =
      decide ((if i = 0 then (match w[j]? with | some b => bitSym b | none => 0) else 0) = s) := by
  unfold initCellCond
  by_cases hi : i = 0
  · subst hi
    rcases hwj : w[j]? with _ | b
    · by_cases h2 : s = 2
      · subst h2; simp [Cond.eval, TEnv.set, hw, hwj]
      · by_cases h1 : s = 1
        · subst h1; simp [Cond.eval, TEnv.set, hw, hwj]
        · by_cases h0 : s = 0
          · subst h0; simp [Cond.eval, TEnv.set, hw, hwj]
          · simp [Cond.eval, TEnv.set, hw, hwj, h2, h1, h0, Ne.symm h0, Ne.symm h1, Ne.symm h2]
    · cases b <;>
      · by_cases h2 : s = 2
        · subst h2; simp [Cond.eval, TEnv.set, hw, hwj, bitSym]
        · by_cases h1 : s = 1
          · subst h1; simp [Cond.eval, TEnv.set, hw, hwj, bitSym]
          · by_cases h0 : s = 0
            · subst h0; simp [Cond.eval, TEnv.set, hw, hwj, bitSym]
            · simp [Cond.eval, TEnv.set, hw, hwj, bitSym, h2, h1, h0, Ne.symm h0, Ne.symm h1, Ne.symm h2]
  · by_cases h0 : s = 0
    · subst h0; simp [hi, Cond.eval]
    · simp [hi, h0, Cond.eval, Ne.symm h0]

private theorem den_initT (hS : e.S = S) (w : List Bool) (hw : e.w = w) {tag : List Part} (ht : Free tag) :
    (initT M tag).denote e = rpnEnc (initF M S (tag.map (Part.val e)) (initCfg k w)) := by
  rw [initT_eq, initF]
  rw [den_bigAndBlock M S e hS _ (fun v => if bit (initCfg k w) v = true then
      Formula.var (tag.map (Part.val e) ++ v) else .not (.var (tag.map (Part.val e) ++ v)))]
  · intro q _
    by_cases hq : q = 2
    · subst hq; simp [initBody, bit, initCfg, den_var_val, Part.val]
    · simp [initBody, bit, initCfg, hq, den_not_var, Part.val, Ne.symm hq]
  · intro i hi j _
    have hik : i < k := List.mem_range.1 hi
    have hc : Cond.eval (e.set 1 j) (.eqc 1 0) = decide (j = 0) := by simp [Cond.eval]
    simp only [initBody, den_ite, hc]
    by_cases hj : j = 0
    · subst hj; simp [bit, initCfg, hik, den_var_val, Part.val, ht.map_set (show 1 ≠ 0 by decide)]
    · simp [bit, initCfg, hik, hj, den_not_var, Part.val, ht.map_set (show 1 ≠ 0 by decide), Ne.symm hj]
  · intro i hi j _ s _
    have hik : i < k := List.mem_range.1 hi
    have hc := initCond_eval e w hw i s j
    simp only [initBody, den_ite, hc]
    have hb : bit (initCfg k w) [2, i, j, s] =
        decide ((if i = 0 then (match w[j]? with | some b => bitSym b | none => 0) else 0) = s) := by
      simp only [bit, dif_pos hik]; rfl
    rw [hb]
    by_cases h : (if i = 0 then (match w[j]? with | some b => bitSym b | none => 0) else 0) = s
    · simp only [h, decide_true, if_true]
      simp [den_var_val, Part.val, ht.map_set (show 1 ≠ 0 by decide)]
    · simp only [h, decide_false, if_false, Bool.false_eq_true]
      simp [den_not_var, Part.val, ht.map_set (show 1 ≠ 0 by decide)]


private theorem den_exOneL (vs : List (List Part)) :
    (exOneL vs).denote e = rpnEnc (exOneF (vs.map (fun v => v.map (Part.val e)))) := by
  have h1 := den_bigOrL e vs T.var (fun v => Formula.var (v.map (Part.val e))) (fun v _ => den_var e v)
  have h2 := den_bigAndL e (pairsOf vs) (fun p => T.not (T.and (T.var p.1) (T.var p.2)))
    (fun p => Formula.not (.and (.var (p.1.map (Part.val e))) (.var (p.2.map (Part.val e)))))
    (fun p _ => den_not e (den_and e (den_var e _) (den_var e _)))
  have h3 := den_and e h1 h2
  unfold exOneL exOneF
  rw [h3, pairsOf_map]
  simp [List.map_map, Function.comp_def]

private theorem flat_rep_const {α β : Type} (t : β) (m : Nat) : ∀ l : List α,
    l.flatMap (fun _ => List.replicate m t) = List.replicate (l.length * m) t
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, flat_rep_const t m xs, List.length_cons, List.replicate_append_replicate]
    congr 1; rw [Nat.add_mul]; omega

private theorem rep_add_flat {β γ : Type} (k S a : Nat) (t : γ) (f : Nat → Nat → β) :
    List.replicate (a + ((List.range k).flatMap (fun i => (List.range S).map (f i))).length) t =
      List.replicate a t ++ List.replicate (k * S) t := by
  rw [← List.replicate_append_replicate, replicate_length_flatMap]
  simp [flat_rep_const]

private theorem rpnEnc_bigAnd_pairs (n : Nat) {α : Type} (f : Nat → α) (F : α × α → Formula) :
    rpnEnc (bigAnd ((pairsOf ((List.range n).map f)).map F)) =
      (List.range n).flatMap (fun a => ((List.range n).filter (fun b => decide (a < b))).flatMap
        (fun b => rpnEnc (F (f a, f b)))) ++ [Tok.tt] ++
      (List.range n).flatMap (fun a => ((List.range n).filter (fun b => decide (a < b))).flatMap
        (fun _ => [Tok.conj])) := by
  rw [pairsOf_range, rpnEnc_bigAnd]
  congr 1
  · congr 1
    rw [List.map_flatMap, List.flatMap_assoc]
    apply fm_congr; intro a _
    rw [List.map_map, List.flatMap_map]; rfl
  · rw [List.length_map, replicate_length_flatMap]
    apply fm_congr; intro a _
    rw [List.length_map, flatMap_single_const]


private theorem filter_tt {α : Type} (l : List α) : l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.filter, ih]

private theorem den_loop2 (c : Cond) (X : Tmpl) :
    (Tmpl.forR 1 .S (.forR 2 .S (.ite c X .nil))).denote e =
      (List.range e.S).flatMap (fun a => ((List.range e.S).filter (fun b => c.eval ((e.set 1 a).set 2 b))).flatMap
        (fun b => X.denote ((e.set 1 a).set 2 b))) := by
  simp only [Tmpl.denote, Bound.val, TEnv.set_S]
  apply fm_congr; intro a _
  exact flatMap_ite_nil (fun b => c.eval ((e.set 1 a).set 2 b)) (fun b => X.denote ((e.set 1 a).set 2 b)) _

private theorem den_exOneHead (hS : e.S = S) {b : List Part} (hb : Free b) (i : Nat) :
    (exOneHead b i).denote e =
      rpnEnc (exOneF ((List.range S).map (fun j => b.map (Part.val e) ++ [1, i, j]))) := by
  have h1 := den_bigOrF e 1 .S .tt (T.var (b ++ [.const 1, .const i, .ctr 1]))
    (fun j => Formula.var (b.map (Part.val e) ++ [1, i, j]))
    (by intro v _ _; rw [den_var_val, hb.map_set (show 1 ≠ 0 by decide)]; simp [Part.val])
  simp only [Bound.val, hS, Cond.eval, filter_tt] at h1
  have hc12 : ∀ a b : Nat, Cond.eval ((e.set 1 a).set 2 b) (.lt 1 2) = decide (a < b) := by
    intro a b; simp [Cond.eval, TEnv.set]
  have h2 : (Tmpl.seqs [.forR 1 .S (.forR 2 .S (.ite (.lt 1 2)
        (T.not (T.and (T.var (b ++ [.const 1, .const i, .ctr 1])) (T.var (b ++ [.const 1, .const i, .ctr 2]))))
        .nil)),
      .tok Tok.tt,
      .forR 1 .S (.forR 2 .S (.ite (.lt 1 2) (.tok Tok.conj) .nil))]).denote e =
      rpnEnc (bigAnd ((pairsOf ((List.range S).map (fun j => b.map (Part.val e) ++ [1, i, j]))).map
        (fun p => Formula.not (.and (.var p.1) (.var p.2))))) := by
    rw [rpnEnc_bigAnd_pairs, Tmpl.denote_seqs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, den_loop2, hS, hc12]
    have hv : ∀ a b', (T.not (T.and (T.var (b ++ [.const 1, .const i, .ctr 1]))
        (T.var (b ++ [.const 1, .const i, .ctr 2])))).denote ((e.set 1 a).set 2 b') =
        rpnEnc ((Formula.var (b.map (Part.val e) ++ [1, i, a])).and (.var (b.map (Part.val e) ++ [1, i, b']))).not := by
      intro a b'
      rw [den_not _ (den_and _ (den_var_val _ _ _) (den_var_val _ _ _))]
      simp only [hb.map_set (show 2 ≠ 0 by decide), hb.map_set (show 1 ≠ 0 by decide)]
      simp [Part.val, TEnv.set]
    simp only [hv, Tmpl.denote, List.append_assoc]
  unfold exOneHead exOneF
  rw [den_and e h1 h2]
  simp [List.map_map, Function.comp_def]


private theorem den_wfT (hS : e.S = S) {b : List Part} (hb : Free b) :
    (wfT M b).denote e = rpnEnc (wfF M S (b.map (Part.val e))) := by
  have hA : (exOneL ((List.range M.nq).map (fun q => b ++ [.const 0, .const q]))).denote e =
      rpnEnc (exOneF ((sSuf M.nq).map (b.map (Part.val e) ++ ·))) := by
    rw [den_exOneL]
    simp [sSuf, List.map_map, Function.comp_def, Part.val]
  have hB : ∀ i ∈ List.range k, (exOneHead b i).denote e =
      rpnEnc (exOneF ((List.range S).map (fun j => b.map (Part.val e) ++ [1, i, j]))) :=
    fun i _ => den_exOneHead S e hS hb i
  have hC : ∀ i ∈ List.range k, (Tmpl.forR 1 .S (exOneL ((List.range M.na).map (fun s =>
        b ++ [.const 2, .const i, .ctr 1, .const s])))).denote e =
      (List.range S).flatMap (fun j => rpnEnc (exOneF ((List.range M.na).map
        (fun s => b.map (Part.val e) ++ [2, i, j, s])))) := by
    intro i _
    simp only [Tmpl.denote, Bound.val, hS]
    apply fm_congr; intro j _
    rw [den_exOneL]
    simp [List.map_map, Function.comp_def, Part.val, hb.map_set (show 1 ≠ 0 by decide)]
  unfold wfF wfT
  rw [rpnEnc_bigAnd, Tmpl.denote_seqs]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map,
    Function.comp_def, List.length_cons, List.length_append, List.length_map, List.length_range]
  have eB : (List.range k).flatMap (fun a => Tmpl.denote e (exOneHead b a)) =
      (List.range k).flatMap (fun a => rpnEnc (exOneF ((List.range S).map (fun j => b.map (Part.val e) ++ [1, a, j])))) :=
    fm_congr hB
  have eC : (List.range k).flatMap (fun a => Tmpl.denote e (Tmpl.forR 1 Bound.S (exOneL ((List.range M.na).map
        (fun s => b ++ [Part.const 2, Part.const a, Part.ctr 1, Part.const s]))))) =
      (List.range k).flatMap (fun i => (List.range S).flatMap (fun j => rpnEnc (exOneF ((List.range M.na).map
        (fun s => b.map (Part.val e) ++ [2, i, j, s]))))) := fm_congr hC
  have eD : List.flatMap rpnEnc ((List.range k).flatMap (fun i => (List.range S).map (fun j =>
        exOneF ((List.range M.na).map (fun s => b.map (Part.val e) ++ [2, i, j, s]))))) =
      (List.range k).flatMap (fun i => (List.range S).flatMap (fun j => rpnEnc (exOneF ((List.range M.na).map
        (fun s => b.map (Part.val e) ++ [2, i, j, s]))))) := by
    rw [List.flatMap_assoc]
    apply fm_congr; intro i _
    rw [List.flatMap_map]
  have eE : (List.range k).flatMap (fun a => Tmpl.denote e (Tmpl.tok Tok.conj)) = List.replicate k Tok.conj := by
    have := flatMap_single_const (α := Nat) Tok.conj (List.range k)
    rw [List.length_range] at this
    exact this
  have eF : (List.range k).flatMap (fun a => Tmpl.denote e (Tmpl.forR 1 Bound.S (Tmpl.tok Tok.conj))) =
      List.replicate (k * S) Tok.conj := by
    have : ∀ a : Nat, Tmpl.denote e (Tmpl.forR 1 Bound.S (Tmpl.tok Tok.conj)) = List.replicate S Tok.conj := by
      intro a
      simp only [Tmpl.denote, Bound.val, hS]
      rw [flatMap_single_const, List.length_range]
    calc _ = (List.range k).flatMap (fun _ => List.replicate S Tok.conj) := fm_congr (fun a _ => this a)
      _ = _ := by rw [flat_rep_const, List.length_range]
  rw [hA, eB, eC, eD, eE, eF, rep_add_flat]
  simp only [Tmpl.denote, List.replicate_succ, List.append_assoc, List.cons_append, List.nil_append]


private theorem den_readT (hS : e.S = S) {b : List Part} (hb : Free b) (i : Fin k) (s : Nat) :
    (readT b i.val s).denote e = rpnEnc (readF S (b.map (Part.val e)) i s) := by
  have h := den_bigOrF e 3 .S .tt (T.and (T.var (b ++ [.const 1, .const i.val, .ctr 3]))
      (T.var (b ++ [.const 2, .const i.val, .ctr 3, .const s])))
    (fun j => Formula.and (.var (b.map (Part.val e) ++ [1, i.val, j])) (.var (b.map (Part.val e) ++ [2, i.val, j, s])))
    (by
      intro v _ _
      rw [den_and _ (den_var_val _ _ _) (den_var_val _ _ _), hb.map_set (show 3 ≠ 0 by decide)]
      simp [Part.val])
  simp only [Bound.val, hS, Cond.eval, filter_tt] at h
  exact h

private theorem den_combT (hS : e.S = S) {b : List Part} (hb : Free b) (q : Nat) (r : Fin k → Nat) :
    (combT b q r).denote e = rpnEnc (combF S (b.map (Part.val e)) q r) := by
  have h := den_bigAndL e (List.finRange k) (fun i => readT b i.val (r i))
    (fun i => readF S (b.map (Part.val e)) i (r i)) (fun i _ => den_readT S e hS hb i (r i))
  unfold combT combF
  rw [den_and e (den_var_val e _ _) h]
  simp [Part.val]

private theorem den_stateBitsT (hS : e.S = S) {b b' : List Part} (hb : Free b) (hb' : Free b') :
    (stateBitsT M b b').flatMap (fun t => t.denote e) =
      (stateBitsF M S (b.map (Part.val e)) (b'.map (Part.val e))).flatMap rpnEnc := by
  unfold stateBitsT stateBitsF
  rw [List.flatMap_map, List.flatMap_map]
  apply fm_congr; intro q' _
  have h := den_bigOrL e ((combos M).filter (fun p => nextState M p.1 p.2 = q'))
    (fun p => combT b p.1 p.2) (fun p => combF S (b.map (Part.val e)) p.1 p.2)
    (fun p _ => den_combT S e hS hb p.1 p.2)
  rw [den_iff e (den_var_val e _ _) h]
  simp [Part.val]

private theorem moveCond_eval (m : Move) (j v : Nat) (e : TEnv) :
    (moveCond m).eval ((e.set 1 j).set 2 v) = decide (m.apply v = j) := by
  cases m
  · simp [moveCond, Cond.eval, TEnv.set, Move.apply]
    by_cases h1 : v = j + 1 <;> by_cases h2 : v = 0 <;> by_cases h3 : j = 0 <;> simp [h1, h2, h3] <;> omega
  · simp [moveCond, Cond.eval, TEnv.set, Move.apply]
  · simp [moveCond, Cond.eval, TEnv.set, Move.apply]
    exact ⟨fun h => by omega, fun h => by omega⟩

private theorem den_headBitT (hS : e.S = S) {b b' : List Part} (hb : Free b) (hb' : Free b') (i : Fin k) (j : Nat) :
    (headBitT M b b' i).denote (e.set 1 j) =
      rpnEnc (headBitF M S (b.map (Part.val e)) (b'.map (Part.val e)) i j) := by
  have hS1 : (e.set 1 j).S = S := hS
  have hin : ∀ p : Nat × (Fin k → Nat), (T.and (combT b p.1 p.2)
      (T.bigOrF 2 .S (moveCond (moveOf M p.1 p.2 i)) (T.var (b ++ [.const 1, .const i.val, .ctr 2])))).denote (e.set 1 j) =
      rpnEnc (Formula.and (combF S (b.map (Part.val e)) p.1 p.2)
        (bigOr (((List.range S).filter (fun j' => decide ((moveOf M p.1 p.2 i).apply j' = j))).map
          (fun j' => .var (b.map (Part.val e) ++ [1, i.val, j']))))) := by
    intro p
    have h1 := den_combT S (e.set 1 j) hS1 hb p.1 p.2
    rw [hb.map_set (show 1 ≠ 0 by decide)] at h1
    have h2 := den_bigOrF (e.set 1 j) 2 .S (moveCond (moveOf M p.1 p.2 i))
      (T.var (b ++ [.const 1, .const i.val, .ctr 2]))
      (fun j' => Formula.var (b.map (Part.val e) ++ [1, i.val, j']))
      (by
        intro v _ _
        rw [den_var_val, hb.map_set (show 2 ≠ 0 by decide), hb.map_set (show 1 ≠ 0 by decide)]
        simp [Part.val, TEnv.set])
    simp only [Bound.val, hS1, moveCond_eval] at h2
    rw [den_and _ h1 h2]
  have h3 := den_bigOrL (e.set 1 j) (combos M) _ _ (fun p _ => hin p)
  unfold headBitT headBitF
  rw [den_iff _ (den_var_val _ _ _) h3, hb'.map_set (show 1 ≠ 0 by decide)]
  simp [Part.val, TEnv.set]

private theorem den_cellBitT (hS : e.S = S) {b b' : List Part} (hb : Free b) (hb' : Free b') (i : Fin k) (j s : Nat) :
    (cellBitT M b b' i s).denote (e.set 1 j) =
      rpnEnc (cellBitF M S (b.map (Part.val e)) (b'.map (Part.val e)) i j s) := by
  have hS1 : (e.set 1 j).S = S := hS
  have h1 : ∀ p : Nat × (Fin k → Nat), (combT b p.1 p.2).denote (e.set 1 j) =
      rpnEnc (combF S (b.map (Part.val e)) p.1 p.2) := by
    intro p
    have := den_combT S (e.set 1 j) hS1 hb p.1 p.2
    rwa [hb.map_set (show 1 ≠ 0 by decide)] at this
  have h2 := den_bigOrL (e.set 1 j) ((combos M).filter (fun p => writeSym M p.1 p.2 i = s))
    (fun p => combT b p.1 p.2) (fun p => combF S (b.map (Part.val e)) p.1 p.2) (fun p _ => h1 p)
  unfold cellBitT cellBitF
  rw [den_iff _ (den_var_val _ _ _)
    (den_or _ (den_and _ (den_not _ (den_var_val _ _ _)) (den_var_val _ _ _))
      (den_and _ (den_var_val _ _ _) h2)),
    hb.map_set (show 1 ≠ 0 by decide), hb'.map_set (show 1 ≠ 0 by decide)]
  simp [Part.val, TEnv.set]


private theorem rep_add_flat_l {α β γ : Type} (l : List α) (S a : Nat) (t : γ) (f : α → Nat → β) :
    List.replicate (a + (l.flatMap (fun i => (List.range S).map (f i))).length) t =
      List.replicate a t ++ List.replicate (l.length * S) t := by
  rw [← List.replicate_append_replicate, replicate_length_flatMap]
  simp [flat_rep_const]

private theorem rep_add_flat3 {α β γ : Type} (l : List α) (S na a : Nat) (t : γ) (f : α → Nat → Nat → β) :
    List.replicate (a + (l.flatMap (fun i => (List.range S).flatMap (fun j => (List.range na).map (f i j)))).length) t =
      List.replicate a t ++ List.replicate (l.length * (S * na)) t := by
  rw [← List.replicate_append_replicate, replicate_length_flatMap]
  simp only [replicate_length_flatMap, List.length_map, List.length_range]
  simp [flat_rep_const]

private theorem den_stepT (hS : e.S = S) {b b' : List Part} (hb : Free b) (hb' : Free b') :
    (stepT M b b').denote e = rpnEnc (stepF M S (b.map (Part.val e)) (b'.map (Part.val e))) := by
  unfold stepF stepT
  rw [rpnEnc_bigAnd, Tmpl.denote_seqs]
  simp only [List.flatMap_append, List.flatMap_map, List.length_append, List.length_map]
  rw [den_stateBitsT M S e hS hb hb']
  have hlen : (stateBitsF M S (b.map (Part.val e)) (b'.map (Part.val e))).length = M.nq := by
    simp [stateBitsF]
  have hH : (List.finRange k).flatMap (fun a => Tmpl.denote e (Tmpl.forR 1 Bound.S (headBitT M b b' a))) =
      List.flatMap rpnEnc ((List.finRange k).flatMap (fun i => (List.range S).map
        (fun j => headBitF M S (b.map (Part.val e)) (b'.map (Part.val e)) i j))) := by
    rw [List.flatMap_assoc]
    apply fm_congr; intro i _
    simp only [Tmpl.denote, Bound.val, hS]
    rw [List.flatMap_map]
    apply fm_congr; intro j _
    exact den_headBitT M S e hS hb hb' i j
  have hC : (List.finRange k).flatMap (fun a => Tmpl.denote e (Tmpl.forR 1 Bound.S
        (Tmpl.seqs (List.map (fun s => cellBitT M b b' a s) (List.range M.na))))) =
      List.flatMap rpnEnc ((List.finRange k).flatMap (fun i => (List.range S).flatMap (fun j =>
        (List.range M.na).map (fun s => cellBitF M S (b.map (Part.val e)) (b'.map (Part.val e)) i j s)))) := by
    rw [List.flatMap_assoc]
    apply fm_congr; intro i _
    simp only [Tmpl.denote, Bound.val, hS]
    rw [List.flatMap_assoc]
    apply fm_congr; intro j _
    rw [Tmpl.denote_seqs, List.flatMap_map, List.flatMap_map]
    apply fm_congr; intro s _
    exact den_cellBitT M S e hS hb hb' i j s
  have eN : (List.range M.nq).flatMap (fun a => Tmpl.denote e (Tmpl.tok Tok.conj)) = List.replicate M.nq Tok.conj := by
    have := flatMap_single_const (α := Nat) Tok.conj (List.range M.nq)
    rw [List.length_range] at this
    exact this
  have eM : ∀ a : Fin k, Tmpl.denote e (Tmpl.forR 1 Bound.S (Tmpl.seqs
        (List.map (fun x => Tmpl.tok Tok.conj) (List.range M.na)))) = List.replicate (S * M.na) Tok.conj := by
    intro a
    simp only [Tmpl.denote, Bound.val, hS, Tmpl.denote_seqs, List.flatMap_map]
    calc _ = (List.range S).flatMap (fun _ => List.replicate M.na Tok.conj) := by
          apply fm_congr; intro j _
          have := flatMap_single_const (α := Nat) Tok.conj (List.range M.na)
          rw [List.length_range] at this
          exact this
      _ = _ := by rw [flat_rep_const, List.length_range]
  have eK : ∀ a : Fin k, Tmpl.denote e (Tmpl.forR 1 Bound.S (Tmpl.tok Tok.conj)) = List.replicate S Tok.conj := by
    intro a
    simp only [Tmpl.denote, Bound.val, hS]
    rw [flatMap_single_const, List.length_range]
  have eK' : (List.finRange k).flatMap (fun a => Tmpl.denote e (Tmpl.forR 1 Bound.S (Tmpl.tok Tok.conj))) =
      List.replicate (k * S) Tok.conj := by
    calc _ = (List.finRange k).flatMap (fun _ => List.replicate S Tok.conj) := fm_congr (fun a _ => eK a)
      _ = _ := by rw [flat_rep_const, List.length_finRange]
  have eM' : (List.finRange k).flatMap (fun a => Tmpl.denote e (Tmpl.forR 1 Bound.S (Tmpl.seqs
        (List.map (fun x => Tmpl.tok Tok.conj) (List.range M.na))))) = List.replicate (k * (S * M.na)) Tok.conj := by
    calc _ = (List.finRange k).flatMap (fun _ => List.replicate (S * M.na) Tok.conj) := fm_congr (fun a _ => eM a)
      _ = _ := by rw [flat_rep_const, List.length_finRange]
  rw [rep_add_flat3, hlen, rep_add_flat_l, hH, hC, eN, eK', eM']
  simp only [Tmpl.denote, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_finRange,
    List.append_assoc]


private theorem free_tagX : Free tagX := by
  intro p hp; simp only [tagX, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> trivial
private theorem free_tagY : Free tagY := by
  intro p hp; simp only [tagY, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> trivial
private theorem free_tagL (i : Nat) : Free (tagL i) := by
  intro p hp; simp only [tagL, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> trivial
private theorem free_tagP (i : Nat) : Free (tagP i) := by
  intro p hp; simp only [tagP, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> trivial

private theorem den_guardT (hS : e.S = S) {X Y Mi A B : List Part} (hX : Free X) (hY : Free Y) (hMi : Free Mi)
    (hA : Free A) (hB : Free B) :
    (guardT M X Y Mi A B).denote e = rpnEnc (guardF M S (X.map (Part.val e)) (Y.map (Part.val e))
      (Mi.map (Part.val e)) (A.map (Part.val e)) (B.map (Part.val e))) := by
  unfold guardT guardF
  exact den_or e (den_and e (den_eqT M S e hS hA hX) (den_eqT M S e hS hB hMi))
    (den_and e (den_eqT M S e hS hA hMi) (den_eqT M S e hS hB hY))

/-- The level part of the matrix. -/
private def LV (ℓ : Nat) (X Y : Name) : List Nat :=
  rpnEnc (wfF M S [ℓ, 0]) ++ rpnEnc (guardF M S X Y [ℓ, 0] [ℓ, 1] [ℓ, 2]) ++ [Tok.neg]

private theorem den_levelT (hS : e.S = S) (c : Nat) :
    (levelT M).denote (e.set 0 c) =
      if c = 0 then LV M S e.T [0, 0] [0, 1] else LV M S (e.T - c) [e.T - c + 1, 1] [e.T - c + 1, 2] := by
  have hS1 : (e.set 0 c).S = S := hS
  have hw := den_wfT M S (e.set 0 c) hS1 (free_tagL 0)
  have hec : Cond.eval (e.set 0 c) (.eqc 0 0) = decide (c = 0) := by simp [Cond.eval]
  simp only [levelT, Tmpl.denote_seqs, List.flatMap_cons, List.flatMap_nil, List.append_nil, den_ite, hec,
    Tmpl.denote]
  rw [hw]
  by_cases hc : c = 0
  · subst hc
    rw [den_guardT M S _ hS1 free_tagX free_tagY (free_tagL 0) (free_tagL 1) (free_tagL 2)]
    simp [LV, tagX, tagY, tagL, Part.val, TEnv.set]
  · rw [den_guardT M S _ hS1 (free_tagP 1) (free_tagP 2) (free_tagL 0) (free_tagL 1) (free_tagL 2)]
    simp [LV, tagP, tagL, Part.val, TEnv.set, hc]


private theorem prenex1_exBlock : ∀ (xs : List Name) (φ : QF),
    (exBlock xs φ).prenex.1 = xs.map (fun x => (false, x)) ++ φ.prenex.1
  | [], _ => rfl
  | x :: xs, φ => by simp [exBlock, QF.prenex, prenex1_exBlock xs φ]
private theorem prenex1_allBlock : ∀ (xs : List Name) (φ : QF),
    (allBlock xs φ).prenex.1 = xs.map (fun x => (true, x)) ++ φ.prenex.1
  | [], _ => rfl
  | x :: xs, φ => by simp [allBlock, QF.prenex, prenex1_allBlock xs φ]
private theorem prenex2_exBlock : ∀ (xs : List Name) (φ : QF), (exBlock xs φ).prenex.2 = φ.prenex.2
  | [], _ => rfl
  | x :: xs, φ => by simp [exBlock, QF.prenex, prenex2_exBlock xs φ]
private theorem prenex2_allBlock : ∀ (xs : List Name) (φ : QF), (allBlock xs φ).prenex.2 = φ.prenex.2
  | [], _ => rfl
  | x :: xs, φ => by simp [allBlock, QF.prenex, prenex2_allBlock xs φ]

variable {k : Nat} (M : TM k) (S : Nat)

private theorem reach_matrix_succ (t : Nat) (X Y : Name) :
    rpnEnc (reach M S (t + 1) X Y).prenex.2 =
      LV M S (t + 1) X Y ++ rpnEnc (reach M S t [t + 1, 1] [t + 1, 2]).prenex.2 ++ [Tok.disj, Tok.conj] := by
  simp only [reach, prenex2_exBlock, QF.prenex, prenex2_allBlock, Formula.imp, rpnEnc_and, rpnEnc_or,
    rpnEnc_not, LV]
  simp

private theorem reach_matrix (t : Nat) : ∀ (X Y : Name),
    rpnEnc (reach M S (t + 1) X Y).prenex.2 =
      (List.range (t + 1)).flatMap (fun c =>
        if c = 0 then LV M S (t + 1) X Y else LV M S (t + 1 - c) [t + 1 - c + 1, 1] [t + 1 - c + 1, 2]) ++
      rpnEnc (Formula.or (eqF M S [1, 1] [1, 2]) (stepF M S [1, 1] [1, 2])) ++
      (List.range (t + 1)).flatMap (fun _ => [Tok.disj, Tok.conj]) := by
  induction t with
  | zero =>
    intro X Y
    rw [reach_matrix_succ]
    simp [reach, QF.prenex, LV]
  | succ t ih =>
    intro X Y
    rw [reach_matrix_succ, ih]
    have hconst : (List.range (t + 1 + 1)).flatMap (fun _ => [Tok.disj, Tok.conj]) =
        (List.range (t + 1)).flatMap (fun _ => [Tok.disj, Tok.conj]) ++ [Tok.disj, Tok.conj] := by
      rw [List.range_succ (n := t + 1)]; simp
    have hlev : (List.range (t + 1 + 1)).flatMap (fun c =>
        if c = 0 then LV M S (t + 1 + 1) X Y else LV M S (t + 1 + 1 - c) [t + 1 + 1 - c + 1, 1] [t + 1 + 1 - c + 1, 2]) =
        LV M S (t + 1 + 1) X Y ++ (List.range (t + 1)).flatMap (fun c =>
          if c = 0 then LV M S (t + 1) [t + 1 + 1, 1] [t + 1 + 1, 2]
          else LV M S (t + 1 - c) [t + 1 - c + 1, 1] [t + 1 - c + 1, 2]) := by
      rw [List.range_succ_eq_map (n := t + 1), List.flatMap_cons, List.flatMap_map]
      simp only [if_true]
      congr 1
      apply fm_congr; intro c _
      by_cases hc : c = 0
      · subst hc; simp
      · simp [hc, Nat.add_sub_add_right]
    rw [hconst, hlev]
    simp only [List.append_assoc]

private theorem reach_prefix (t : Nat) (X Y : Name) :
    ((reach M S t X Y).prenex.1).flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2) =
      (List.range t).flatMap (fun c =>
        QB M S Tok.ex [t - c, 0] ++ QB M S Tok.all [t - c, 1] ++ QB M S Tok.all [t - c, 2]) := by
  induction t generalizing X Y with
  | zero => simp [reach, QF.prenex]
  | succ t ih =>
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [reach, prenex1_exBlock, prenex1_allBlock, QF.prenex, List.flatMap_append, ih, QB, blockVars,
      List.flatMap_map, List.map_map, Function.comp_def, List.append_assoc]
    simp [Nat.add_sub_add_right]

end Pieces

theorem redTmpl_denote {k : Nat} (M : TM k) (S : Nat) (w : List Bool) (ctr : Nat → Nat) :
    (redTmpl M).denote ⟨w, S, blockSize M S, ctr⟩ = (redQbf M S w).toks := by
  obtain ⟨t, ht⟩ : ∃ t, blockSize M S = t + 1 := by
    have h1 := M.three_le_nq
    have h2 : M.nq ≤ blockSize M S := by simp [blockSize, blockSuf, sSuf]
    exact ⟨blockSize M S - 1, by omega⟩
  unfold redQbf redQF
  rw [ht]
  let e : TEnv := ⟨w, S, t + 1, ctr⟩
  have hS : e.S = S := rfl
  have hT : e.T = t + 1 := rfl
  show (redTmpl M).denote e = _
  simp only [redTmpl, prefixT, matrixT, Tmpl.denote, Tmpl.denote_seqs, QF.toQbf, Qbf.toks, topF, prenex1_exBlock,
    prenex2_exBlock, QF.prenex, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hBv : Bound.val e Bound.T = t + 1 := rfl
  have eP : (List.range (Bound.val e Bound.T)).flatMap (fun v =>
      Tmpl.denote (e.set 0 v) (quantBlockT M Tok.ex (tagL 0)) ++
        (Tmpl.denote (e.set 0 v) (quantBlockT M Tok.all (tagL 1)) ++
          Tmpl.denote (e.set 0 v) (quantBlockT M Tok.all (tagL 2)))) =
      (List.range (t + 1)).flatMap (fun c =>
        QB M S Tok.ex [t + 1 - c, 0] ++ QB M S Tok.all [t + 1 - c, 1] ++ QB M S Tok.all [t + 1 - c, 2]) := by
    rw [hBv]
    apply fm_congr; intro v _
    have hS' : (e.set 0 v).S = S := rfl
    rw [den_quantBlock M S _ hS' _ (free_tagL 0), den_quantBlock M S _ hS' _ (free_tagL 1),
      den_quantBlock M S _ hS' _ (free_tagL 2), List.append_assoc]
    simp [tagL, Part.val, TEnv.set, e]
  have eL : (List.range (Bound.val e Bound.T)).flatMap (fun v => Tmpl.denote (e.set 0 v) (levelT M)) =
      (List.range (t + 1)).flatMap (fun c =>
        if c = 0 then LV M S (t + 1) [0, 0] [0, 1]
        else LV M S (t + 1 - c) [t + 1 - c + 1, 1] [t + 1 - c + 1, 2]) := by
    rw [hBv]
    apply fm_congr; intro v _
    rw [den_levelT M S e hS v]
  have eD : (List.range (Bound.val e Bound.T)).flatMap (fun v => [Tok.disj] ++ [Tok.conj]) =
      (List.range (t + 1)).flatMap (fun _ => [Tok.disj, Tok.conj]) := by
    rw [hBv]; rfl
  have eS : Tmpl.denote e (sideT M) = rpnEnc (topSide M S (initCfg k w)) := by
    unfold sideT topSide accT accF
    rw [den_and e (den_initT M S e hS w rfl free_tagX)
      (den_and e (den_wfT M S e hS free_tagY) (den_var_val e _ _))]
    have h1 : tagX.map (Part.val e) = [0, 0] := rfl
    have h2 : tagY.map (Part.val e) = [0, 1] := rfl
    rw [h1, h2]
    rfl
  have eBase : Tmpl.denote e (baseT M) =
      rpnEnc (Formula.or (eqF M S [1, 1] [1, 2]) (stepF M S [1, 1] [1, 2])) := by
    have hf : ∀ n : Nat, Free [Part.const 1, Part.const n] := by
      intro n p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> trivial
    unfold baseT
    rw [den_or e (den_eqT M S e hS (hf 1) (hf 2)) (den_stepT M S e hS (hf 1) (hf 2))]
    rfl
  have eQ1 : Tmpl.denote e (quantBlockT M Tok.ex tagX) = QB M S Tok.ex [0, 0] :=
    den_quantBlock M S e hS _ free_tagX
  have eQ2 : Tmpl.denote e (quantBlockT M Tok.ex tagY) = QB M S Tok.ex [0, 1] :=
    den_quantBlock M S e hS _ free_tagY
  rw [eP, eL, eD, eS, eBase, eQ1, eQ2]
  have eR : ∀ φ : Formula, List.flatMap RTok.enc (toRPN φ) = rpnEnc φ := fun _ => rfl
  rw [eR, rpnEnc_and, reach_matrix M S t, List.flatMap_append, List.flatMap_map, List.flatMap_append,
    List.flatMap_map, reach_prefix]
  simp only [QB, blockVars, List.flatMap_map, List.append_assoc, Bool.false_eq_true, if_false]

end Complexity
