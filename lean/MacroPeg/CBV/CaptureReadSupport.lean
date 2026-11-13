import MacroPeg.CBV.SequentialSpanRecompute

/-! A rule row depends only on the parameters read by its body. Reads in
actual arguments and predicates count even when the callee ignores the value.
This quotients the row after argument evaluation; it never erases an actual. -/
namespace Shallot.MacroPeg.CBV.CaptureReadSupport

mutual
  def reads : MExp → List Nat
    | .param k => [k]
    | .call _ args => argumentReads args
    | .seq a b | .alt a b => reads a ++ reads b
    | .star a | .notP a => reads a
    | _ => []
  def argumentReads : List MExp → List Nat
    | [] => []
    | a :: args => reads a ++ argumentReads args
end

mutual
  theorem expression (g : MGrammar) (x : List Char) (s : Strategy) (T : SequentialClock.Table) {E F : List (List Char)} : ∀ e,
      (∀ k ∈ reads e, E[k]? = F[k]?) → ∀ p, evV g x s T E e p = evV g x s T F e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl
    | .param k, h, p => by simp only [evV, h k (by simp [reads])]
    | .call i args, h, p => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = args.length
        · by_cases hs : s = .callByValueSeq
          · subst s
            rw [evV_call_seq hr ha, evV_call_seq hr ha, sequential g x _ T args h]
          · rw [evV_call_par hr ha hs, evV_call_par hr ha hs, parallel g x s T args h]
        · simp only [evV, hr, if_neg ha]
    | .seq a b, h, p => by
      have ha := expression g x s T a (fun k hk => h k (by simp [reads, hk])) p
      simp only [evV]
      rw [ha]
      cases evV g x s T F a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q => exact expression g x s T b (fun k hk => h k (by simp [reads, hk])) q
    | .alt a b, h, p => by
      have ha := expression g x s T a (fun k hk => h k (by simp [reads, hk])) p
      simp only [evV]
      rw [ha]
      cases evV g x s T F a p with
      | none => rfl
      | some result =>
        cases result with
        | none => exact expression g x s T b (fun k hk => h k (by simp [reads, hk])) p
        | some q => rfl
    | .notP a, h, p => by simp only [evV, expression g x s T a h p]
    | .star a, h, p => by
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q _ => expression g x s T a h q)

  theorem parallel (g : MGrammar) (x : List Char) (s : Strategy) (T : SequentialClock.Table) {E F : List (List Char)} : ∀ args,
      (∀ k ∈ argumentReads args, E[k]? = F[k]?) → ∀ p,
      evParArgs g x s T E args p = evParArgs g x s T F args p
    | [], _, _ => rfl
    | a :: args, h, p => by
      simp only [evParArgs]
      rw [expression g x s T a (fun k hk => h k (by simp [argumentReads, hk])) p]
      rw [parallel g x s T args (fun k hk => h k (by simp [argumentReads, hk])) p]

  theorem sequential (g : MGrammar) (x : List Char) (s : Strategy) (T : SequentialClock.Table) {E F : List (List Char)} : ∀ args,
      (∀ k ∈ argumentReads args, E[k]? = F[k]?) → ∀ p,
      evSeqArgs g x s T E args p = evSeqArgs g x s T F args p
    | [], _, _ => rfl
    | a :: args, h, p => by
      simp only [evSeqArgs]
      rw [expression g x s T a (fun k hk => h k (by simp [argumentReads, hk])) p]
      cases evV g x s T F a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q =>
          simp only []
          rw [sequential g x s T args (fun k hk => h k (by simp [argumentReads, hk])) q]
end

def canonical (e : MExp) (E : SequentialSpanRecompute.Env) : SequentialSpanRecompute.Env :=
  E.mapIdx (fun k span => if k ∈ reads e then span else (0,0))

theorem canonical_get (e : MExp) (E : SequentialSpanRecompute.Env) (k : Nat) :
    (canonical e E)[k]? = E[k]?.map (fun span => if k ∈ reads e then span else (0,0)) := by
  simp [canonical, List.getElem?_mapIdx]

theorem canonical_length (e : MExp) (E : SequentialSpanRecompute.Env) :
    (canonical e E).length = E.length := by simp [canonical]

theorem canonical_valid (e : MExp) {E : SequentialSpanRecompute.Env} {n : Nat}
    (hE : SequentialSpanRecompute.ValidEnv n E) : SequentialSpanRecompute.ValidEnv n (canonical e E) := by
  intro span hs
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hs
  rw [canonical_get] at hk
  cases he : E[k]? with
  | none => simp [he] at hk
  | some original =>
    simp only [he, Option.map_some, Option.some.injEq] at hk
    by_cases hr : k ∈ reads e
    · simp only [if_pos hr] at hk
      subst span
      exact hE original (List.mem_of_getElem? he)
    · simp only [if_neg hr] at hk
      subst span
      exact ⟨Nat.le_refl _, Nat.zero_le _⟩

theorem canonical_reads (e : MExp) (x : List Char) (E : SequentialSpanRecompute.Env)
    (k : Nat) (hk : k ∈ reads e) :
    (SequentialSpanRecompute.decodeEnv x (canonical e E))[k]? =
      (SequentialSpanRecompute.decodeEnv x E)[k]? := by
  simp only [SequentialSpanRecompute.decodeEnv, List.getElem?_map, canonical_get]
  cases E[k]? <;> simp [hk]

theorem canonical_body (g : MGrammar) (x : List Char) (s : Strategy) (T : SequentialClock.Table)
    (e : MExp) (E : SequentialSpanRecompute.Env) (p : Nat) :
    evV g x s T (SequentialSpanRecompute.decodeEnv x (canonical e E)) e p =
      evV g x s T (SequentialSpanRecompute.decodeEnv x E) e p :=
  expression g x s T e (fun k hk => canonical_reads e x E k hk) p

/-- Fixed-clock rows can be keyed by the canonical environment. This does
not identify rows from different physical clocks. -/
theorem row_canonical (g : MGrammar) (x : List Char) (s : Strategy) (m i : Nat)
    (r : MRule) (hr : ruleAtM g.rules i = some r) (E : SequentialSpanRecompute.Env) (p : Nat) :
    valAt (tblV g x s m i (SequentialSpanRecompute.decodeEnv x (canonical r.body E))) p =
      valAt (tblV g x s m i (SequentialSpanRecompute.decodeEnv x E)) p := by
  cases m with
  | zero => simp [tblV, valAt_nil]
  | succ m =>
    by_cases hp : p ≤ x.length
    · rw [valAt_tblV_succ hr _ hp, valAt_tblV_succ hr _ hp]
      exact canonical_body g x s _ r.body E p
    · simp [tblV, hr, valAt_rangeMap, hp]

theorem canonical_idempotent (e : MExp) (E : SequentialSpanRecompute.Env) :
    canonical e (canonical e E) = canonical e E := by
  apply List.ext_getElem?
  intro k
  simp only [canonical_get]
  cases E[k]? <;> by_cases hk : k ∈ reads e <;> simp [hk]

end Shallot.MacroPeg.CBV.CaptureReadSupport
