import MacroPeg.CBV.SequentialRecompute

namespace Shallot.MacroPeg.CBV.SequentialSpanRecompute

/-! Recompute individual Seq rule queries with numeric capture intervals.
Parameter matching traverses suffixes of the original input without making
captured strings. The correctness and per-environment bounds below do not
yet constitute a Turing-machine space analysis of the evaluation stack. -/

open Shallot (beqChar leChar stripPrefix?)

abbrev Env := List (Nat × Nat)
abbrev Query := Nat → Env → Nat → Res

def decodeEnv (x : List Char) (E : Env) : List (List Char) :=
  E.map (fun span => pre x span.1 span.2)

def ValidEnv (n : Nat) (E : Env) : Prop :=
  ∀ span ∈ E, span.2 ≤ span.1 ∧ span.1 ≤ n

theorem valid_capture {n p q : Nat} {E : Env} (hp : p ≤ n) (hE : ValidEnv n E) :
    ValidEnv n ((p, min q p) :: E) := by
  intro span hm
  rcases List.mem_cons.mp hm with he | hm
  · subst span; exact ⟨Nat.min_le_right _ _, hp⟩
  · exact hE span hm

theorem decode_capture (x : List Char) (p q : Nat) :
    pre x p (min q p) = pre x p q := by
  unfold pre
  congr 1
  omega

/-- Read two suffixes of the original input; do not construct the captured
substring. Only a counter and input cursors change during this traversal. -/
def matchCount : Nat → List Char → List Char → Option Nat
  | 0, _, target => some target.length
  | k + 1, c :: source, d :: target =>
    if beqChar c d then matchCount k source target else none
  | _ + 1, _, _ => none

theorem matchCount_eq : ∀ k source target, k ≤ source.length →
    matchCount k source target = (stripPrefix? (source.take k) target).map List.length
  | 0, _, _, _ => rfl
  | k + 1, [], _, hk => by simp at hk
  | k + 1, c :: source, [], _ => rfl
  | k + 1, c :: source, d :: target, hk => by
    simp only [matchCount, List.take_succ_cons, stripPrefix?]
    split
    · exact matchCount_eq k source target (by simp at hk; omega)
    · rfl

def matchSpan (x : List Char) (a b p : Nat) : Res :=
  some (matchCount (a - b) (sfx x a) (sfx x p))

theorem matchSpan_eq (x : List Char) (a b p : Nat) (ha : a ≤ x.length) :
    matchSpan x a b p = some ((stripPrefix? (pre x a b) (sfx x p)).map List.length) := by
  unfold matchSpan pre
  rw [matchCount_eq _ _ _ (by rw [length_sfx x ha]; omega)]

mutual
  def eval (g : MGrammar) (x : List Char) (Q : Query) (E : Env) : MExp → Nat → Res
    | .eps, p => some (some p)
    | .any, p =>
      match sfx x p with
      | _ :: rest => some (some rest.length)
      | [] => some none
    | .chr c, p =>
      match sfx x p with
      | d :: rest => if beqChar c d then some (some rest.length) else some none
      | [] => some none
    | .range lo hi, p =>
      match sfx x p with
      | d :: rest => if leChar lo d && leChar d hi then some (some rest.length) else some none
      | [] => some none
    | .lit w, p =>
      match stripPrefix? w (sfx x p) with
      | some rest => some (some rest.length)
      | none => some none
    | .param k, p =>
      match E[k]? with
      | some (a, b) => matchSpan x a b p
      | none => some none
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some rule =>
        if rule.arity = args.length then
          match evalArgs g x Q E args p with
          | some (some (W, q)) => Q i W q
          | some none => some none
          | none => none
        else some none
      | none => some none
    | .seq a b, p =>
      match eval g x Q E a p with
      | some (some q) => eval g x Q E b q
      | result => result
    | .alt a b, p =>
      match eval g x Q E a p with
      | some none => eval g x Q E b p
      | result => result
    | .star a, p => evStar (fun q => eval g x Q E a q) p
    | .notP a, p =>
      match eval g x Q E a p with
      | some (some _) => some none
      | some none => some (some p)
      | none => none
    | .dbg _, p | .lam _ _, p => some (some p)
    | .callParam _ _, _ => some none
    | .invoke _ _ _, _ => none

  def evalArgs (g : MGrammar) (x : List Char) (Q : Query) (E : Env) :
      List MExp → Nat → Option (Option (Env × Nat))
    | [], p => some (some ([], p))
    | a :: args, p =>
      match eval g x Q E a p with
      | some (some q) =>
        match evalArgs g x Q E args q with
        | some (some (W, r)) => some (some ((p, min q p) :: W, r))
        | result => result
      | some none => some none
      | none => none
end

def decodeArgs (x : List Char) (result : Option (Option (Env × Nat))) :
    Option (Option (List (List Char) × Nat)) :=
  result.map (fun v => v.map (fun pair => (decodeEnv x pair.1, pair.2)))

def ArgsSpec (x : List Char) (result : Option (Option (Env × Nat)))
    (source : Option (Option (List (List Char) × Nat))) : Prop :=
  decodeArgs x result = source ∧
    ∀ W q, result = some (some (W, q)) → ValidEnv x.length W ∧ q ≤ x.length

mutual
  theorem eval_eq {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : OkTV x.length T)
      (hQ : ∀ i W, ValidEnv x.length W → ∀ p, p ≤ x.length →
        Q i W p = valAt (T i (decodeEnv x W)) p) (E : Env) (hE : ValidEnv x.length E) :
      ∀ e p, p ≤ x.length → eval g x Q E e p = evV g x .callByValueSeq T (decodeEnv x E) e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl
    | .param k, p, _ => by
      cases hs : E[k]? with
      | none => simp [eval, evV, decodeEnv, hs]
      | some span =>
        obtain ⟨a, b⟩ := span
        have ha := (hE (a, b) (List.mem_of_getElem? hs)).2
        simp only [eval, evV, decodeEnv, List.getElem?_map, hs, Option.map_some]
        rw [matchSpan_eq x a b p ha]
        cases stripPrefix? (pre x a b) (sfx x p) <;> rfl
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [eval, evV, hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [eval, evV, hr, if_pos ha]
          have hargs := args_spec (g := g) hT hQ E hE args p hp
          rw [← hargs.1]
          cases hv : evalArgs g x Q E args p with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              obtain ⟨hW, hq⟩ := hargs.2 W q hv
              exact hQ i W hW q hq
        · simp only [eval, evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q => exact eval_eq hT hQ E hE b q (evV_ok hT a p hp q hv)
    | .alt a b, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none => rfl
      | some result =>
        cases result with
        | none => exact eval_eq hT hQ E hE b p hp
        | some q => rfl
    | .notP a, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      rfl
    | .star a, p, hp => by
      simp only [eval, evV_star]
      exact evStar_congr p (fun q hq => eval_eq hT hQ E hE a q (by omega))

  theorem args_spec {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : OkTV x.length T)
      (hQ : ∀ i W, ValidEnv x.length W → ∀ p, p ≤ x.length →
        Q i W p = valAt (T i (decodeEnv x W)) p) (E : Env) (hE : ValidEnv x.length E) :
      ∀ args p, p ≤ x.length → ArgsSpec x (evalArgs g x Q E args p)
        (evSeqArgs g x .callByValueSeq T (decodeEnv x E) args p)
    | [], p, hp => by
      refine ⟨rfl, ?_⟩
      intro W q h
      cases h
      refine ⟨?_, hp⟩
      intro span hm
      cases hm
    | a :: args, p, hp => by
      have ha := eval_eq (g := g) hT hQ E hE a p hp
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none =>
        refine ⟨by simp [decodeArgs, evalArgs, ha, hv, evSeqArgs], ?_⟩
        intro W q h; simp [evalArgs, ha, hv] at h
      | some result =>
        cases result with
        | none =>
          refine ⟨by simp [decodeArgs, evalArgs, ha, hv, evSeqArgs], ?_⟩
          intro W q h; simp [evalArgs, ha, hv] at h
        | some j =>
          have hj := evV_ok hT a p hp j hv
          have ht := args_spec (g := g) hT hQ E hE args j hj
          refine ⟨?_, ?_⟩
          · simp only [evalArgs, ha, hv, evSeqArgs]
            rw [← ht.1]
            cases hr : evalArgs g x Q E args j with
            | none => rfl
            | some result =>
              cases result with
              | none => rfl
              | some Wq =>
                obtain ⟨W, q⟩ := Wq
                simp [decodeArgs, decodeEnv, decode_capture]
          · intro W q h
            simp only [evalArgs, ha, hv] at h
            cases hr : evalArgs g x Q E args j with
            | none => rw [hr] at h; cases h
            | some result =>
              cases result with
              | none => rw [hr] at h; cases h
              | some Vr =>
                obtain ⟨V, r⟩ := Vr
                rw [hr] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hV, hq⟩ := ht.2 V r hr
                exact ⟨valid_capture hp hV, hq⟩
end

def query (g : MGrammar) (x : List Char) : Nat → Query
  | 0 => fun _ _ _ => none
  | m + 1 => fun i E p =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | some rule => eval g x (query g x m) E rule.body p
      | none => none
    else none

theorem query_eq (g : MGrammar) (x : List Char) : ∀ m i E, ValidEnv x.length E → ∀ p,
    query g x m i E p = valAt (tblV g x .callByValueSeq m i (decodeEnv x E)) p
  | 0, _, _, _, _ => by simp [query, tblV, valAt_nil]
  | m + 1, i, E, hE, p => by
    by_cases hp : p ≤ x.length
    · cases hr : ruleAtM g.rules i with
      | none => simp [query, hp, hr, tblV, valAt_nil]
      | some rule =>
        rw [valAt_tblV_succ hr (decodeEnv x E) hp]
        simp only [query, if_pos hp, hr]
        exact eval_eq (tblV_ok g x .callByValueSeq m)
          (fun i E hE p _ => query_eq g x m i E hE p) E hE rule.body p hp
    · cases hr : ruleAtM g.rules i with
      | none => simp [query, hp, tblV, hr, valAt_nil]
      | some rule => simp [query, hp, tblV, hr, valAt_rangeMap]

theorem eval_at_clock (g : MGrammar) (x : List Char) (m : Nat) (E : Env)
    (hE : ValidEnv x.length E) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    eval g x (query g x m) E e p =
      evV g x .callByValueSeq (tblV g x .callByValueSeq m) (decodeEnv x E) e p :=
  eval_eq (tblV_ok g x .callByValueSeq m)
    (fun i E hE p _ => query_eq g x m i E hE p) E hE e p hp

/-- Each successful argument stage retains exactly one bounded numeric span
per argument. It does not retain substring values or a substring dictionary. -/
theorem arguments_valid (g : MGrammar) (x : List Char) (m : Nat) (E : Env)
    (hE : ValidEnv x.length E) (args : List MExp) (p : Nat) (hp : p ≤ x.length)
    (W : Env) (q : Nat) (hv : evalArgs g x (query g x m) E args p = some (some (W, q))) :
    ValidEnv x.length W ∧ q ≤ x.length ∧ W.length = args.length := by
  have hargs := args_spec (g := g) (tblV_ok g x .callByValueSeq m)
    (fun i E hE p _ => query_eq g x m i E hE p) E hE args p hp
  obtain ⟨hW, hq⟩ := hargs.2 W q hv
  have hsource : evSeqArgs g x .callByValueSeq (tblV g x .callByValueSeq m)
      (decodeEnv x E) args p = some (some (decodeEnv x W, q)) := by
    rw [← hargs.1]
    simp [decodeArgs, hv]
  have hlen := evSeq_length args p (decodeEnv x W) q hsource
  exact ⟨hW, hq, by simpa [decodeEnv] using hlen⟩

def run (g : MGrammar) (x : List Char) (e : MExp) : Res :=
  eval g x (query g x (SequentialClock.positionClock g x.length)) [] e x.length

theorem run_eq (g : MGrammar) (x : List Char) (e : MExp) :
    run g x e = SequentialRecompute.run g x e := by
  unfold run SequentialRecompute.run
  rw [eval_at_clock g x _ [] (by intro span hm; cases hm) e x.length (Nat.le_refl _),
    SequentialRecompute.eval_at_clock g x _ [] e x.length (Nat.le_refl _)]
  rfl

def observation (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x e with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem observation_eq (g : MGrammar) (x : List Char) (e : MExp) :
    observation g x e = SequentialClock.decide g x e := by
  unfold observation
  rw [run_eq]
  exact SequentialRecompute.observation_eq g x e

theorem observation_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    observation g x e = some r ↔ SObs g .callByValueSeq e x r := by
  rw [observation_eq]
  exact SequentialClock.decide_iff hg he x r

theorem observation_none_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : observation g x e = none ↔ ∀ r, ¬ SObs g .callByValueSeq e x r := by
  rw [observation_eq]
  exact SequentialClock.decide_none_iff hg he x

theorem run_accepts_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : run g x e = some (some 0) ↔ SObs g .callByValueSeq e x (some []) := by
  rw [← observation_iff hg he x (some [])]
  unfold observation
  have hbound : OkR x.length (run g x e) := by
    unfold run
    rw [eval_at_clock g x _ [] (by intro span hm; cases hm) e x.length (Nat.le_refl _)]
    exact evV_ok (tblV_ok g x .callByValueSeq _) e x.length (Nat.le_refl _)
  cases hr : run g x e with
  | none => simp
  | some result =>
    cases result with
    | none => simp
    | some q =>
      have hq := hbound q hr
      have hs : sfx x q = [] ↔ q = 0 := by
        simp only [sfx, List.drop_eq_nil_iff]
        omega
      simpa only [Option.some.injEq] using hs.symm

end Shallot.MacroPeg.CBV.SequentialSpanRecompute
