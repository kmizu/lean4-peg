import PalPeg.ScaHeadRep
import PalPeg.ScaProg

/-!
# Head programs as whole-machine stack programs

`ScaHeadRep` writes each head operation as a program over the head's own slots and control, and
compiles it to a local rule. The rest of the encoding writes one `ScaProg.Prog` per letter. This
file translates a head program into a `ScaProg.Prog` (slots through `ix`, control through the
lens) and proves that the translation evaluates exactly as the compiled rule runs, once the
machine's `peek` is at least the program's depth. Every correctness theorem of `ScaHeadRep`
therefore holds for the translated programs.
-/
set_option autoImplicit false
namespace PalPeg.ScaHeadBridge
open PalPeg.ScaLocal PalPeg.ScaHeadRep

variable {Γ C : Type} {K : ℕ} [Inhabited Γ]

/-- A head program at control `lc` and stacks `ix`, as a stack program. `moveTop` pushes the
top of the source, when there is one; the source is not popped. -/
def toProg (lc : Lens C HCtl) (ix : Slot → Fin K) : ScaHeadRep.Prog Γ → ScaProg.Prog Γ C K
  | .skip => .skip
  | .push x a => .push (ix a) fun _ _ => x
  | .pop a => .pop (ix a)
  | .moveTop b a =>
    .ite (fun _ v => (v (ix b)).isEmpty) .skip (.push (ix a) fun _ v => (v (ix b)).headD default)
  | .copy b a => .copy (ix b) (ix a)
  | .clear a => .clear (ix a)
  | .setPhase ph => .ctl fun c _ => lc.set c { lc.get c with phase := ph }
  | .setNeg b => .ctl fun c _ => lc.set c { lc.get c with balanceNeg := b }
  | .seq p q => .seq (toProg lc ix p) (toProg lc ix q)
  | .ite d cond p q =>
    .ite (fun c v => cond (lc.get c) (fun s => (v (ix s)).take d)) (toProg lc ix p)
      (toProg lc ix q)

/-- `f` performs `F` on the head at `lc`/`ix` and leaves every other stack unchanged (the shape
of `ScaHeadRep.Prog.Implements`, for any function). -/
def Performs (lc : Lens C HCtl) (ix : Slot → Fin K)
    (f : C → (Fin K → List Γ) → C × (Fin K → List Γ))
    (F : HCtl → (Slot → List Γ) → HCtl × (Slot → List Γ)) : Prop :=
  ∀ c st, (f c st).1 = lc.set c (F (lc.get c) (fun s => st (ix s))).1 ∧
    (fun s => (f c st).2 (ix s)) = (F (lc.get c) (fun s => st (ix s))).2 ∧
    ∀ k, (∀ s, ix s ≠ k) → (f c st).2 k = st k

omit [Inhabited Γ] in
/-- Two functions performing the same head meaning are equal. -/
theorem performs_unique {lc : Lens C HCtl} {ix : Slot → Fin K}
    {f g : C → (Fin K → List Γ) → C × (Fin K → List Γ)}
    {F : HCtl → (Slot → List Γ) → HCtl × (Slot → List Γ)}
    (hf : Performs lc ix f F) (hg : Performs lc ix g F) (c : C) (st : Fin K → List Γ) :
    f c st = g c st := by
  obtain ⟨hf1, hf2, hf3⟩ := hf c st
  obtain ⟨hg1, hg2, hg3⟩ := hg c st
  refine Prod.ext (hf1.trans hg1.symm) (funext fun k => ?_)
  by_cases hk : ∃ s, ix s = k
  · obtain ⟨s, rfl⟩ := hk
    exact (congrFun hf2 s).trans (congrFun hg2 s).symm
  · push Not at hk
    rw [hf3 k hk, hg3 k hk]

omit [Inhabited Γ] in
theorem take_take_of_le (l : List Γ) {d peek : ℕ} (h : d ≤ peek) :
    (l.take peek).take d = l.take d := by
  rw [List.take_take]
  congr 1
  omega

/-- **The translation performs the head program**, when `peek` covers its depth. -/
theorem performs_toProg (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix)
    (peek : ℕ) :
    ∀ p : ScaHeadRep.Prog Γ, p.depth ≤ peek →
      Performs lc ix (fun c st => (toProg lc ix p).eval peek c st) p.sem
  | .skip, _ => fun c st => ⟨(lc.set_get c).symm, rfl, fun _ _ => rfl⟩
  | .push x a, _ => fun c st => by
    refine ⟨(lc.set_get c).symm, ?_, fun k hk => ?_⟩
    · simp only [toProg, ScaProg.Prog.eval, Prog.sem]
      exact Prog.update_comp hix st a _
    · simp only [toProg, ScaProg.Prog.eval]
      exact Function.update_of_ne (Ne.symm (hk a)) _ _
  | .pop a, _ => fun c st => by
    refine ⟨(lc.set_get c).symm, ?_, fun k hk => ?_⟩
    · simp only [toProg, ScaProg.Prog.eval, Prog.sem]
      exact Prog.update_comp hix st a _
    · simp only [toProg, ScaProg.Prog.eval]
      exact Function.update_of_ne (Ne.symm (hk a)) _ _
  | .moveTop b a, hd => fun c st => by
    have hpeek : 1 ≤ peek := by simpa [Prog.depth] using hd
    cases hb : st (ix b) with
    | nil =>
      have hv : (view peek st (ix b)).isEmpty = true := by simp [view, hb]
      simp only [toProg, ScaProg.Prog.eval, hv, if_true, Prog.sem, hb, List.take_nil,
        List.nil_append]
      refine ⟨(lc.set_get c).symm, ?_, fun _ _ => trivial⟩
      exact (Function.update_eq_self a _).symm
    | cons y ys =>
      have hv : view peek st (ix b) = y :: ys.take (peek - 1) := by
        simp only [view, hb]
        obtain ⟨m, rfl⟩ : ∃ m, peek = m + 1 := ⟨peek - 1, by omega⟩
        simp
      simp only [toProg, ScaProg.Prog.eval, hv, List.isEmpty_cons, Bool.false_eq_true, if_false,
        List.headD_cons, Prog.sem, hb, List.take_succ_cons, List.take_zero, List.singleton_append]
      refine ⟨(lc.set_get c).symm, Prog.update_comp hix st a _, fun k hk => ?_⟩
      exact Function.update_of_ne (Ne.symm (hk a)) _ _
  | .copy b a, _ => fun c st => by
    refine ⟨(lc.set_get c).symm, ?_, fun k hk => ?_⟩
    · simp only [toProg, ScaProg.Prog.eval, Prog.sem]
      exact Prog.update_comp hix st a _
    · simp only [toProg, ScaProg.Prog.eval]
      exact Function.update_of_ne (Ne.symm (hk a)) _ _
  | .clear a, _ => fun c st => by
    refine ⟨(lc.set_get c).symm, ?_, fun k hk => ?_⟩
    · simp only [toProg, ScaProg.Prog.eval, Prog.sem]
      exact Prog.update_comp hix st a _
    · simp only [toProg, ScaProg.Prog.eval]
      exact Function.update_of_ne (Ne.symm (hk a)) _ _
  | .setPhase ph, _ => fun c st => ⟨rfl, rfl, fun _ _ => rfl⟩
  | .setNeg b, _ => fun c st => ⟨rfl, rfl, fun _ _ => rfl⟩
  | .seq p₁ p₂, hd => fun c st => by
    have hd' : p₁.depth + p₂.depth ≤ peek := by simpa [Prog.depth] using hd
    obtain ⟨h1c, h1s, h1f⟩ := performs_toProg lc hix peek p₁ (by omega) c st
    obtain ⟨h2c, h2s, h2f⟩ := performs_toProg lc hix peek p₂ (by omega)
      ((toProg lc ix p₁).eval peek c st).1 ((toProg lc ix p₁).eval peek c st).2
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · simp only [toProg, ScaProg.Prog.eval, Prog.sem]
      rw [h2c, h1c, lc.get_set, lc.set_set, h1s]
    · simp only [toProg, ScaProg.Prog.eval, Prog.sem]
      rw [h2s, h1c, lc.get_set, h1s]
    · simp only [toProg, ScaProg.Prog.eval]
      rw [h2f k hk, h1f k hk]
  | .ite d cond p₁ p₂, hd => fun c st => by
    have hd' : max d (max p₁.depth p₂.depth) ≤ peek := by simpa [Prog.depth] using hd
    have hv : (fun s => (view peek st (ix s)).take d) = hview d (fun s => st (ix s)) := by
      funext s
      exact take_take_of_le _ (le_of_max_le_left hd')
    simp only [toProg, ScaProg.Prog.eval, Prog.sem, hv]
    split
    · exact performs_toProg lc hix peek p₁ (by omega) c st
    · exact performs_toProg lc hix peek p₂ (by omega) c st

/-- **The translation evaluates as the compiled rule runs.** -/
theorem eval_toProg (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix)
    (p : ScaHeadRep.Prog Γ) {peek : ℕ} (hp : p.depth ≤ peek) (c : C) (st : Fin K → List Γ) :
    (toProg lc ix p).eval peek c st = (p.toRule lc ix).run c st :=
  performs_unique (performs_toProg lc hix peek p hp) (Prog.toRule_impl lc hix p) c st

/-! ## The head operations as stack programs -/

section Ops

variable (ι : Fin 2 → Γ) (tk : Γ) (lc : Lens C HCtl) (ix : Slot → Fin K)

def arriveProg (a : Fin 2) : ScaProg.Prog Γ C K := toProg lc ix (arriveP tk ι a)
def moveRightProg : ScaProg.Prog Γ C K := toProg lc ix (moveRightP tk)
def moveLeftProg : ScaProg.Prog Γ C K := toProg lc ix (moveLeftP (Γ := Γ))

variable {ι tk lc ix}

theorem arriveProg_eval (hix : Function.Injective ix) (a : Fin 2) {peek : ℕ} (hpeek : 14 ≤ peek)
    (c : C) (st : Fin K → List Γ) :
    (arriveProg ι tk lc ix a).eval peek c st = (arriveRule ι tk lc ix a).run c st :=
  eval_toProg lc hix _ (by rw [arriveP_depth]; exact hpeek) c st

theorem moveRightProg_eval (hix : Function.Injective ix) {peek : ℕ} (hpeek : 17 ≤ peek)
    (c : C) (st : Fin K → List Γ) :
    (moveRightProg tk lc ix).eval peek c st = (moveRightRule tk lc ix).run c st :=
  eval_toProg lc hix _ (by rw [moveRightP_depth]; exact hpeek) c st

theorem moveLeftProg_eval (hix : Function.Injective ix) {peek : ℕ} (hpeek : 2 ≤ peek)
    (c : C) (st : Fin K → List Γ) :
    (moveLeftProg (Γ := Γ) lc ix).eval peek c st = (moveLeftRule lc ix).run c st :=
  eval_toProg lc hix _ (by rw [moveLeftP_depth]; exact hpeek) c st

/-- **Arrival**, as a stack program: `t ↦ t ++ [a]`, same position. -/
theorem arriveProg_correct (hix : Function.Injective ix) (a : Fin 2) {peek : ℕ}
    (hpeek : 14 ≤ peek) {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ}
    (h : GHeadRep ι lc ix t p c st) :
    GHeadRep ι lc ix (t ++ [a]) p ((arriveProg ι tk lc ix a).eval peek c st).1
      ((arriveProg ι tk lc ix a).eval peek c st).2 := by
  rw [arriveProg_eval hix a hpeek]
  exact arrive_correct ι tk lc ix hix a h

/-- **Moving right**, as a stack program. -/
theorem moveRightProg_correct (hix : Function.Injective ix) {peek : ℕ} (hpeek : 17 ≤ peek)
    {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st)
    (hp : p < t.length) :
    GHeadRep ι lc ix t (p + 1) ((moveRightProg tk lc ix).eval peek c st).1
      ((moveRightProg tk lc ix).eval peek c st).2 := by
  rw [moveRightProg_eval hix hpeek]
  exact moveRight_correct ι tk lc ix hix h hp

/-- **Moving left**, as a stack program. -/
theorem moveLeftProg_correct (hix : Function.Injective ix) {peek : ℕ} (hpeek : 2 ≤ peek)
    {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st)
    (hp : 0 < p) :
    GHeadRep ι lc ix t (p - 1) ((moveLeftProg (Γ := Γ) lc ix).eval peek c st).1
      ((moveLeftProg (Γ := Γ) lc ix).eval peek c st).2 := by
  rw [moveLeftProg_eval hix hpeek]
  exact moveLeft_correct ι lc ix hix h hp

end Ops

/-! ## Reading through the machine's view -/

section Reads

variable {ι : Fin 2 → Γ} {lc : Lens C HCtl} {ix : Slot → Fin K}

/-- The head's depth-1 view, read out of the machine's view. -/
def headView (ix : Slot → Fin K) (v : Fin K → List Γ) : Slot → List Γ := fun s => (v (ix s)).take 1

omit [Inhabited Γ] in
theorem headView_view {peek : ℕ} (hpeek : 1 ≤ peek) (st : Fin K → List Γ) :
    headView ix (view peek st) = fun s => view 1 st (ix s) := by
  funext s
  exact take_take_of_le _ hpeek

omit [Inhabited Γ] in
theorem readFwd_view {peek : ℕ} (hpeek : 1 ≤ peek) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) :
    readFwd (headView ix (view peek st)) = t[p]?.map ι := by
  rw [headView_view hpeek]
  exact readFwd_correct ι lc ix h

omit [Inhabited Γ] in
theorem readRev_view {peek : ℕ} (hpeek : 1 ≤ peek) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) :
    readRev (headView ix (view peek st)) = (if p = 0 then none else t[p - 1]?).map ι := by
  rw [headView_view hpeek]
  exact readRev_correct ι lc ix h

omit [Inhabited Γ] in
theorem available_view {peek : ℕ} (hpeek : 1 ≤ peek) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) :
    available (headView ix (view peek st)) = decide (p < t.length) := by
  rw [headView_view hpeek]
  exact available_correct ι lc ix h

end Reads


/-! ## Moving by a fixed delta, and copying a head -/

section MoveCopy

/-- `n` copies of `p` in sequence. -/
def repeatProg (p : ScaProg.Prog Γ C K) : ℕ → ScaProg.Prog Γ C K
  | 0 => .skip
  | n + 1 => .seq p (repeatProg p n)

omit [Inhabited Γ] in
theorem eval_repeatProg (p : ScaProg.Prog Γ C K) (peek : ℕ) :
    ∀ (n : ℕ) (c : C) (st : Fin K → List Γ),
      (repeatProg p n).eval peek c st = (fun x => p.eval peek x.1 x.2)^[n] (c, st)
  | 0, _, _ => rfl
  | n + 1, c, st => by
    simp only [repeatProg, ScaProg.Prog.eval]
    rw [eval_repeatProg p peek n, Function.iterate_succ_apply]

variable (ι : Fin 2 → Γ) (tk : Γ) (lc : Lens C HCtl) (ix : Slot → Fin K)

/-- Move by the fixed integer `δ`: `|δ|` right or left moves. -/
def moveByProg (δ : ℤ) : ScaProg.Prog Γ C K :=
  if 0 ≤ δ then repeatProg (moveRightProg tk lc ix) δ.toNat
  else repeatProg (moveLeftProg (Γ := Γ) lc ix) (-δ).toNat

variable {ι tk lc ix}

theorem moveByProg_eval (hix : Function.Injective ix) (δ : ℤ) {peek : ℕ} (hpeek : 17 ≤ peek)
    (c : C) (st : Fin K → List Γ) :
    (moveByProg tk lc ix δ).eval peek c st = moveBy tk lc ix δ c st := by
  unfold moveByProg moveBy
  split_ifs with hδ
  · have hstep : (fun x : C × (Fin K → List Γ) => (moveRightProg tk lc ix).eval peek x.1 x.2)
        = stepOf (moveRightRule tk lc ix) :=
      funext fun x => moveRightProg_eval hix hpeek x.1 x.2
    rw [eval_repeatProg, hstep]
  · have hstep : (fun x : C × (Fin K → List Γ) => (moveLeftProg (Γ := Γ) lc ix).eval peek x.1 x.2)
        = stepOf (moveLeftRule lc ix) :=
      funext fun x => moveLeftProg_eval hix (by omega) x.1 x.2
    rw [eval_repeatProg, hstep]

/-- **Moving by `δ`**, as a stack program, when `0 ≤ p + δ ≤ t.length`. -/
theorem moveByProg_correct (hix : Function.Injective ix) {δ : ℤ} {peek : ℕ} (hpeek : 17 ≤ peek)
    {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st)
    (h0 : 0 ≤ (p : ℤ) + δ) (h1 : (p : ℤ) + δ ≤ t.length) :
    GHeadRep ι lc ix t ((p : ℤ) + δ).toNat ((moveByProg tk lc ix δ).eval peek c st).1
      ((moveByProg tk lc ix δ).eval peek c st).2 := by
  rw [moveByProg_eval hix δ hpeek]
  exact moveBy_correct ι tk lc ix hix h h0 h1

/-- Copy slot by slot, then run `tail`. -/
def copiesProg (ixA ixB : Slot → Fin K) (tail : ScaProg.Prog Γ C K) :
    List Slot → ScaProg.Prog Γ C K
  | [] => tail
  | s :: l => .seq (.copy (ixA s) (ixB s)) (copiesProg ixA ixB tail l)

/-- Head `B` becomes a copy of head `A`: every slot, then the control. -/
def copyFromProg (lA lB : Lens C HCtl) (ixA ixB : Slot → Fin K) : ScaProg.Prog Γ C K :=
  copiesProg ixA ixB (.ctl fun c _ => lB.set c (lA.get c)) allSlots

omit [Inhabited Γ] in
theorem eval_copiesProg {ixA ixB : Slot → Fin K} (hixB : Function.Injective ixB)
    (hdisj : ∀ s s', ixA s ≠ ixB s') (lA lB : Lens C HCtl) (peek : ℕ) :
    ∀ (l : List Slot) (c : C) (st : Fin K → List Γ),
      (copiesProg ixA ixB (.ctl fun c _ => lB.set c (lA.get c)) l).eval peek c st =
        (lB.set c (lA.get c), fun k =>
          match l.find? (fun s => decide (ixB s = k)) with
          | some s => st (ixA s)
          | none => st k)
  | [], _, _ => rfl
  | s :: l, c, st => by
    simp only [copiesProg, ScaProg.Prog.eval]
    rw [eval_copiesProg hixB hdisj lA lB peek l]
    refine Prod.ext rfl (funext fun k => ?_)
    simp only [List.find?_cons]
    by_cases hk : ixB s = k
    · subst hk
      simp only [decide_true]
      cases hf : l.find? (fun s' => decide (ixB s' = ixB s)) with
      | none => simp
      | some s' =>
        have hs' : s' = s :=
          hixB (of_decide_eq_true (List.find?_some (p := fun s' => decide (ixB s' = ixB s)) hf))
        subst hs'
        simp [Function.update_of_ne (hdisj s' s')]
    · simp only [hk, decide_false]
      cases hf : l.find? (fun s' => decide (ixB s' = k)) with
      | none => simp [Function.update_of_ne (Ne.symm hk)]
      | some s' => simp [Function.update_of_ne (hdisj s' s)]

omit [Inhabited Γ] in
theorem copyFromProg_eval {ixA ixB : Slot → Fin K} (hixB : Function.Injective ixB)
    (hdisj : ∀ s s', ixA s ≠ ixB s') (lA lB : Lens C HCtl) (peek : ℕ) (c : C)
    (st : Fin K → List Γ) :
    (copyFromProg lA lB ixA ixB).eval peek c st = (copyFromRule lA lB ixA ixB).run c st := by
  rw [copyFrom_run, copyFromProg, eval_copiesProg hixB hdisj lA lB peek]
  rfl

omit [Inhabited Γ] in
/-- **`copyFrom`**, as a stack program. -/
theorem copyFromProg_correct {lA lB : Lens C HCtl} {ixA ixB : Slot → Fin K}
    (hixB : Function.Injective ixB) (hdisj : ∀ s s', ixA s ≠ ixB s')
    (hindep : ∀ c h, lA.get (lB.set c h) = lA.get c) (peek : ℕ) {t : List (Fin 2)} {p : ℕ}
    {c : C} {st : Fin K → List Γ} (h : GHeadRep ι lA ixA t p c st) :
    GHeadRep ι lB ixB t p ((copyFromProg lA lB ixA ixB).eval peek c st).1
        ((copyFromProg lA lB ixA ixB).eval peek c st).2 ∧
      GHeadRep ι lA ixA t p ((copyFromProg lA lB ixA ixB).eval peek c st).1
        ((copyFromProg lA lB ixA ixB).eval peek c st).2 ∧
      ∀ k, (∀ s, ixB s ≠ k) → ((copyFromProg lA lB ixA ixB).eval peek c st).2 k = st k := by
  rw [copyFromProg_eval hixB hdisj lA lB peek]
  exact copyFrom_correct ι hixB hdisj hindep h

end MoveCopy

/-- info: 'PalPeg.ScaHeadBridge.eval_toProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_toProg

/-- info: 'PalPeg.ScaHeadBridge.moveByProg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms moveByProg_correct

/-- info: 'PalPeg.ScaHeadBridge.copyFromProg_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copyFromProg_correct

end PalPeg.ScaHeadBridge
