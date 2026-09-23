import PalPeg.ScaWindowPal
import PalPeg.ScaProgEmbed
import PalPeg.ScaEncode

/-!
# The window PAL controller as one stack program per letter

`ScaWindowPal.tick` (the Scala `WindowPAL.tick`) is written as a stack program
(`ScaProg.Prog`), parametric in stack-program encodings of the two worker kinds
(`WorkerEnc`). Every unbounded controller datum lives on a stack:

* the unit counters `history`, `power`, `nextBirth` and each stage's `half` / `clock` are
  represented by the stack **length** (the content is irrelevant);
* each stage's four result packets are stacks of the flag worker's flag symbols;
* each worker lives on its own block of stacks (`ScaProgEmbed.Embed`).

The finite fields of the controller and of the stages are in the finite control `Ctl`, together
with four scratch bits (`fr`, `bth`, `bnd`, `rel`) that no representation invariant constrains.

The program follows `tick` / `stageRound` statement by statement; each piece has its own
representation lemma and the pieces are chained. The result is `ScaEncode.LetterProgs`, hence
`PAL ∈ PEG` from the controller's correctness (`pal_in_peg`).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace PalPeg.ScaWindowEncode
open PalPeg.ScaLocal PalPeg.ScaProg PalPeg.ScaProgEmbed PalPeg.ScaWindowPal

/-! ## Worker encodings -/

/-- A worker kind encoded as stack programs on its own machine (`Kw` stacks of symbols `Γw`,
control `Cw`), at a fixed peek `D`. `Rep` relates an abstract worker to a configuration; every
worker operation has a program keeping `Rep` **as long as the operation does not fault** (after a
fault the answer is `false` anyway, and a real worker's heads may leave the text), and the
observations are read off the control. The output flag stack is stack `flagsIdx`, symbol by symbol
through `flagSym`. Faults are sticky: every operation keeps a set fault bit. -/
structure WorkerEnc (W : Type) (ops : WorkerOps W) (Γw Cw : Type) (Kw D : ℕ) where
  Rep : W → Cw → (Fin Kw → List Γw) → Prop
  arrive : Fin 2 → Prog Γw Cw Kw
  resetFlags : Bool → Prog Γw Cw Kw
  start : Bool → Prog Γw Cw Kw
  mark : Bool → Prog Γw Cw Kw
  service : Prog Γw Cw Kw
  output : Cw → Bool
  modeDone : Cw → Bool
  faulted : Cw → Bool
  flagsIdx : Fin Kw
  flagSym : Bool → Γw
  flagDecode : Γw → Bool
  flagDecode_sym : ∀ b, flagDecode (flagSym b) = b
  rep_arrive : ∀ a w c st, Rep w c st → ops.faulted (ops.arrive a w) = false →
    Rep (ops.arrive a w) ((arrive a).eval D c st).1 ((arrive a).eval D c st).2
  rep_resetFlags : ∀ b w c st, Rep w c st → ops.faulted (ops.resetFlags b w) = false →
    Rep (ops.resetFlags b w) ((resetFlags b).eval D c st).1 ((resetFlags b).eval D c st).2
  rep_start : ∀ b w c st, Rep w c st → ops.faulted (ops.start b w) = false →
    Rep (ops.start b w) ((start b).eval D c st).1 ((start b).eval D c st).2
  rep_mark : ∀ b w c st, Rep w c st → ops.faulted (ops.mark b w) = false →
    Rep (ops.mark b w) ((mark b).eval D c st).1 ((mark b).eval D c st).2
  rep_service : ∀ w c st, Rep w c st → ops.faulted (ops.service w) = false →
    Rep (ops.service w) (service.eval D c st).1 (service.eval D c st).2
  sticky_arrive : ∀ a w, ops.faulted w = true → ops.faulted (ops.arrive a w) = true
  sticky_resetFlags : ∀ b w, ops.faulted w = true → ops.faulted (ops.resetFlags b w) = true
  sticky_start : ∀ b w, ops.faulted w = true → ops.faulted (ops.start b w) = true
  sticky_mark : ∀ b w, ops.faulted w = true → ops.faulted (ops.mark b w) = true
  sticky_service : ∀ w, ops.faulted w = true → ops.faulted (ops.service w) = true
  rep_output : ∀ w c st, Rep w c st → ops.output w = output c
  rep_modeDone : ∀ w c st, Rep w c st → ops.modeDone w = modeDone c
  rep_faulted : ∀ w c st, Rep w c st → ops.faulted w = faulted c
  rep_flags : ∀ w c st, Rep w c st → st flagsIdx = (ops.flags w).map flagSym

/-! ## The finite control -/

/-- The finite fields of one `WindowStage` (`ScaWindowPal.StageState` minus `half`, `clock`,
`results`). -/
structure StageCtl where
  alive : Bool
  interval : Fin 7
  pending : Bool
  batch : Fin 4
  birth : Bool
  release : Bool
  middle : Bool
  deriving DecidableEq

/-- The finite control: the finite fields of `PalState` and of both stages, and scratch bits
(`fr` = first round, `bth` = birth, `bnd` = boundary, `rel` = new release). -/
structure Ctl where
  powerReady : Bool
  slot : Fin 2
  small : Fin 5
  first : Bool
  fault : Bool
  output : Bool
  stg : Fin 2 → StageCtl
  fr : Bool
  bth : Bool
  bnd : Bool
  rel : Bool

instance : Finite StageCtl :=
  Finite.of_injective
    (fun y : StageCtl => (y.alive, y.interval, y.pending, y.batch, y.birth, y.release, y.middle))
    (by intro a b h; cases a; cases b; simp only [Prod.mk.injEq] at h; simp [h])

instance : Finite Ctl :=
  Finite.of_injective
    (fun x : Ctl => (x.powerReady, x.slot, x.small, x.first, x.fault, x.output, x.stg, x.fr, x.bth,
      x.bnd, x.rel))
    (by intro a b h; cases a; cases b; simp only [Prod.mk.injEq] at h; simp [h])

def StageCtl.initial : StageCtl :=
  ⟨false, 0, false, 0, false, false, false⟩

def Ctl.initial : Ctl where
  powerReady := false
  slot := 0
  small := 0
  first := false
  fault := false
  output := true
  stg := fun _ => StageCtl.initial
  fr := false
  bth := false
  bnd := false
  rel := false

/-- `answering()` on the finite fields. -/
def StageCtl.answering (y : StageCtl) : Bool :=
  y.alive && (y.interval.val == 2 || y.interval.val == 3 ||
    y.interval.val == 4 || y.interval.val == 5)

/-- Replace stage `i`'s finite fields. -/
def Ctl.setStg (x : Ctl) (i : Fin 2) (y : StageCtl) : Ctl :=
  { x with stg := Function.update x.stg i y }

@[simp] theorem Ctl.setStg_stg_self (x : Ctl) (i : Fin 2) (y : StageCtl) :
    (x.setStg i y).stg i = y := by simp [Ctl.setStg]

theorem Ctl.setStg_stg_ne (x : Ctl) {i j : Fin 2} (y : StageCtl) (h : j ≠ i) :
    (x.setStg i y).stg j = x.stg j := by simp [Ctl.setStg, Function.update_of_ne h]

/-! ## The stacks -/

/-- The controller's own stacks. -/
inductive CStack where
  | history
  | power
  | nextBirth
  | half (i : Fin 2)
  | clock (i : Fin 2)
  | res (i : Fin 2) (r : Fin 4)
  deriving DecidableEq

/-- Number of stacks: 15 for the controller, then the two matchers, then the two flag workers. -/
abbrev KK (Km Kf : ℕ) : ℕ := 15 + 2 * Km + 2 * Kf

/-- Position of a controller stack (all below 15). -/
def CStack.pos : CStack → ℕ
  | .history => 0
  | .power => 1
  | .nextBirth => 2
  | .half i => 3 + i.val
  | .clock i => 5 + i.val
  | .res i r => 7 + 4 * i.val + r.val

theorem CStack.pos_lt (x : CStack) : x.pos < 15 := by
  cases x with
  | history => decide
  | power => decide
  | nextBirth => decide
  | half i => simp only [CStack.pos]; omega
  | clock i => simp only [CStack.pos]; omega
  | res i r => simp only [CStack.pos]; omega

theorem CStack.pos_inj {x y : CStack} (h : x.pos = y.pos) : x = y := by
  cases x with
  | history => cases y <;> simp only [CStack.pos] at h <;> first | rfl | omega
  | power => cases y <;> simp only [CStack.pos] at h <;> first | rfl | omega
  | nextBirth => cases y <;> simp only [CStack.pos] at h <;> first | rfl | omega
  | half i =>
    cases y <;> simp only [CStack.pos] at h <;> first | omega | (congr 1; exact Fin.ext (by omega))
  | clock i =>
    cases y <;> simp only [CStack.pos] at h <;> first | omega | (congr 1; exact Fin.ext (by omega))
  | res i r =>
    cases y with
    | res i' r' =>
      simp only [CStack.pos] at h
      have hi : i = i' := Fin.ext (by omega)
      have hr : r = r' := Fin.ext (by omega)
      rw [hi, hr]
    | _ => simp only [CStack.pos] at h; omega

section Layout
variable {Km Kf : ℕ}

/-- The stack index of a controller stack. -/
def cI (x : CStack) : Fin (KK Km Kf) := ⟨x.pos, by have := x.pos_lt; dsimp only [KK]; omega⟩

@[simp] theorem cI_val (x : CStack) : (cI x : Fin (KK Km Kf)).val = x.pos := rfl

@[simp] theorem cI_inj {x y : CStack} : (cI x : Fin (KK Km Kf)) = cI y ↔ x = y :=
  ⟨fun h => CStack.pos_inj (congrArg Fin.val h), fun h => h ▸ rfl⟩

theorem mul_le_of_fin2 (i : Fin 2) (n : ℕ) : i.val * n ≤ n := by
  have : i.val ≤ 1 := by omega
  calc i.val * n ≤ 1 * n := Nat.mul_le_mul_right _ this
    _ = n := one_mul n

/-- Stack `j` of matcher `i`. -/
def mI (i : Fin 2) (j : Fin Km) : Fin (KK Km Kf) :=
  ⟨15 + i.val * Km + j.val, by have := mul_le_of_fin2 i Km; have := j.isLt; dsimp only [KK]; omega⟩

/-- Stack `j` of flag worker `i`. -/
def fI (i : Fin 2) (j : Fin Kf) : Fin (KK Km Kf) :=
  ⟨15 + 2 * Km + i.val * Kf + j.val, by
    have := mul_le_of_fin2 i Kf; have := j.isLt; dsimp only [KK]; omega⟩

theorem mI_inj (i : Fin 2) : Function.Injective (mI (Km := Km) (Kf := Kf) i) := by
  intro j j' h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [mI] at this
  omega

theorem fI_inj (i : Fin 2) : Function.Injective (fI (Km := Km) (Kf := Kf) i) := by
  intro j j' h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [fI] at this
  omega

theorem mI_ne_mI {i i' : Fin 2} (h : i ≠ i') (j : Fin Km) (j' : Fin Km) :
    (mI i j : Fin (KK Km Kf)) ≠ mI i' j' := by
  intro heq
  have := congrArg Fin.val heq
  simp only [mI] at this
  have hj := j.isLt
  have hj' := j'.isLt
  fin_cases i <;> fin_cases i' <;> simp_all <;> omega

theorem fI_ne_fI {i i' : Fin 2} (h : i ≠ i') (j : Fin Kf) (j' : Fin Kf) :
    (fI i j : Fin (KK Km Kf)) ≠ fI i' j' := by
  intro heq
  have := congrArg Fin.val heq
  simp only [fI] at this
  have hj := j.isLt
  have hj' := j'.isLt
  fin_cases i <;> fin_cases i' <;> simp_all <;> omega

theorem mI_ne_fI (i i' : Fin 2) (j : Fin Km) (j' : Fin Kf) :
    (mI i j : Fin (KK Km Kf)) ≠ fI i' j' := by
  intro heq
  have := congrArg Fin.val heq
  simp only [mI, fI] at this
  have := mul_le_of_fin2 i Km
  have := j.isLt
  omega

theorem cI_ne_mI (x : CStack) (i : Fin 2) (j : Fin Km) :
    (cI x : Fin (KK Km Kf)) ≠ mI i j := by
  intro heq
  have := congrArg Fin.val heq
  have := x.pos_lt
  simp only [cI_val, mI] at *
  omega

theorem cI_ne_fI (x : CStack) (i : Fin 2) (j : Fin Kf) :
    (cI x : Fin (KK Km Kf)) ≠ fI i j := by
  intro heq
  have := congrArg Fin.val heq
  have := x.pos_lt
  simp only [cI_val, fI] at *
  omega

theorem mI_ge (i : Fin 2) (j : Fin Km) : 15 ≤ (mI i j : Fin (KK Km Kf)).val := by
  simp only [mI]; omega

theorem fI_ge (i : Fin 2) (j : Fin Kf) : 15 ≤ (fI i j : Fin (KK Km Kf)).val := by
  simp only [fI]; omega

end Layout

/-! ## Embedded components: purity and representation -/

section EmbedFacts
variable {Γ₁ C₁ Γ C : Type} {K₁ K : ℕ} (e : Embed Γ₁ C₁ Γ C K₁ K)

/-- The component's stacks hold only symbols of the component. -/
def Pure (st : Fin K → List Γ) : Prop := ∀ k, ∀ x ∈ st (e.idx k), e.sym (e.unsym x) = x

theorem pure_update {st : Fin K → List Γ} (hst : Pure e st) (k : Fin K₁) (l : List Γ)
    (hl : ∀ x ∈ l, e.sym (e.unsym x) = x) : Pure e (Function.update st (e.idx k) l) := by
  intro k' x hx
  by_cases h : k' = k
  · subst h; rw [Function.update_self] at hx; exact hl x hx
  · rw [Function.update_of_ne (fun h' => h (e.idx_inj h'))] at hx; exact hst k' x hx

/-- **An embedded program keeps its component pure.** -/
theorem pure_embed (peek : ℕ) :
    ∀ (p : Prog Γ₁ C₁ K₁) (c : C) (st : Fin K → List Γ), Pure e st →
      Pure e ((embed e p).eval peek c st).2
  | .skip, _, _, h => h
  | .ctl _, _, _, h => h
  | .push k x, c, st, h => by
    simp only [embed, Prog.eval]
    refine pure_update e h k _ fun y hy => ?_
    rcases List.mem_cons.mp hy with hy | hy
    · subst hy; rw [e.unsym_sym]
    · exact h k y hy
  | .pop k, c, st, h => by
    simp only [embed, Prog.eval]
    exact pure_update e h k _ fun y hy => h k y (List.mem_of_mem_tail hy)
  | .copy s d, c, st, h => by
    simp only [embed, Prog.eval]
    exact pure_update e h d _ fun y hy => h s y hy
  | .clear k, c, st, h => by
    simp only [embed, Prog.eval]
    exact pure_update e h k _ fun y hy => by simp at hy
  | .seq p q, c, st, h => by
    simp only [embed, Prog.eval]
    exact pure_embed peek q _ _ (pure_embed peek p c st h)
  | .ite b p q, c, st, h => by
    simp only [embed, Prog.eval]
    split
    · exact pure_embed peek p c st h
    · exact pure_embed peek q c st h

/-- A pure component's stacks are the component's stacks, symbol by symbol. -/
theorem pure_eq_map {st : Fin K → List Γ} (h : Pure e st) (k : Fin K₁) :
    st (e.idx k) = (proj e st k).map e.sym := by
  simp only [proj, List.map_map]
  symm
  calc List.map (e.sym ∘ e.unsym) (st (e.idx k)) = List.map id (st (e.idx k)) :=
        List.map_congr_left (fun x hx => h k x hx)
    _ = st (e.idx k) := List.map_id _

theorem pure_nil : Pure e (fun _ : Fin K => ([] : List Γ)) := fun _ _ hx => by simp at hx

theorem proj_nil : proj e (fun _ : Fin K => ([] : List Γ)) = fun _ => [] := by
  funext k; simp [proj]

/-- **An embedded program leaves alone any view of the control that `set` does not touch.** -/
theorem eval_embed_fix {α : Type} (f : C → α) (hf : ∀ c x, f (e.set c x) = f c) (peek : ℕ) :
    ∀ (p : Prog Γ₁ C₁ K₁) (c : C) (st : Fin K → List Γ), f ((embed e p).eval peek c st).1 = f c
  | .skip, _, _ => rfl
  | .ctl _, c, _ => hf c _
  | .push _ _, _, _ => rfl
  | .pop _, _, _ => rfl
  | .copy _ _, _, _ => rfl
  | .clear _, _, _ => rfl
  | .seq p q, c, st => by
    simp only [embed, Prog.eval]
    rw [eval_embed_fix f hf peek q, eval_embed_fix f hf peek p]
  | .ite b p q, c, st => by
    simp only [embed, Prog.eval]
    split
    · exact eval_embed_fix f hf peek p c st
    · exact eval_embed_fix f hf peek q c st

/-- A component's representation in the whole machine: the abstract component is represented by
the component's control and its (projected) stacks, which hold only component symbols. -/
def WRep {W : Type} (R : W → C₁ → (Fin K₁ → List Γ₁) → Prop) (w : W) (c : C)
    (st : Fin K → List Γ) : Prop :=
  R w (e.get c) (proj e st) ∧ Pure e st

theorem wrep_frame {W : Type} {R : W → C₁ → (Fin K₁ → List Γ₁) → Prop} {w : W} {c c' : C}
    {st st' : Fin K → List Γ} (h : WRep e R w c st) (hc : e.get c' = e.get c)
    (hst : ∀ k, st' (e.idx k) = st (e.idx k)) : WRep e R w c' st' := by
  have hp : proj e st' = proj e st := by funext k; simp [proj, hst]
  refine ⟨?_, ?_⟩
  · rw [hc, hp]; exact h.1
  · intro k x hx; rw [hst] at hx; exact h.2 k x hx

/-- **An embedded worker operation keeps the component's representation.** -/
theorem wrep_embed {W : Type} {R : W → C₁ → (Fin K₁ → List Γ₁) → Prop} (peek : ℕ) (f : W → W)
    (p : Prog Γ₁ C₁ K₁) {w : W}
    (hp : ∀ c st, R w c st → R (f w) (p.eval peek c st).1 (p.eval peek c st).2)
    {c : C} {st : Fin K → List Γ} (h : WRep e R w c st) :
    WRep e R (f w) ((embed e p).eval peek c st).1 ((embed e p).eval peek c st).2 := by
  obtain ⟨h1, h2⟩ := eval_embed e peek p c st
  refine ⟨?_, pure_embed e peek p c st h.2⟩
  rw [h1, h2]
  exact hp _ _ h.1

end EmbedFacts

/-! ## The whole machine -/

/-- Control of the whole machine: the controller's finite control, then the matchers' and the
flag workers' controls. -/
abbrev Ctrl (Cm Cf : Type) : Type := Ctl × (Fin 2 → Cm) × (Fin 2 → Cf)

section Machine
variable {Γm Γf Cm Cf : Type} {Km Kf : ℕ}

/-- Where matcher `i` lives. -/
def emM [Inhabited Γm] (i : Fin 2) : Embed Γm Cm (Γm ⊕ Γf) (Ctrl Cm Cf) Km (KK Km Kf) where
  idx := mI i
  idx_inj := mI_inj i
  sym := Sum.inl
  unsym := Sum.elim id fun _ => default
  unsym_sym _ := rfl
  get c := c.2.1 i
  set c x := (c.1, Function.update c.2.1 i x, c.2.2)
  get_set c x := by simp

/-- Where flag worker `i` lives. -/
def emF [Inhabited Γf] (i : Fin 2) : Embed Γf Cf (Γm ⊕ Γf) (Ctrl Cm Cf) Kf (KK Km Kf) where
  idx := fI i
  idx_inj := fI_inj i
  sym := Sum.inr
  unsym := Sum.elim (fun _ => default) id
  unsym_sym _ := rfl
  get c := c.2.2 i
  set c x := (c.1, c.2.1, Function.update c.2.2 i x)
  get_set c x := by simp

/-- Programs that touch only the controller's control and stacks (they may read everything). -/
def CtlOnly : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) → Prop
  | .skip => True
  | .ctl g => ∀ c v, (g c v).2 = c.2
  | .push k _ => k.val < 15
  | .pop k => k.val < 15
  | .copy _ d => d.val < 15
  | .clear k => k.val < 15
  | .seq p q => CtlOnly p ∧ CtlOnly q
  | .ite _ p q => CtlOnly p ∧ CtlOnly q

theorem ctlOnly_eval (peek : ℕ) :
    ∀ (p : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf)), CtlOnly p →
      ∀ c st, (p.eval peek c st).1.2 = c.2 ∧
        ∀ j : Fin (KK Km Kf), 15 ≤ j.val → (p.eval peek c st).2 j = st j
  | .skip, _, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | .ctl _, h, c, _ => ⟨h c _, fun _ _ => rfl⟩
  | .push k _, h, _, _ => ⟨rfl, fun j hj => by
      simp only [Prog.eval]
      rw [Function.update_of_ne (fun e => by subst e; simp only [CtlOnly] at h; omega)]⟩
  | .pop k, h, _, _ => ⟨rfl, fun j hj => by
      simp only [Prog.eval]
      rw [Function.update_of_ne (fun e => by subst e; simp only [CtlOnly] at h; omega)]⟩
  | .copy _ d, h, _, _ => ⟨rfl, fun j hj => by
      simp only [Prog.eval]
      rw [Function.update_of_ne (fun e => by subst e; simp only [CtlOnly] at h; omega)]⟩
  | .clear k, h, _, _ => ⟨rfl, fun j hj => by
      simp only [Prog.eval]
      rw [Function.update_of_ne (fun e => by subst e; simp only [CtlOnly] at h; omega)]⟩
  | .seq p q, h, c, st => by
    obtain ⟨hp1, hp2⟩ := ctlOnly_eval peek p h.1 c st
    obtain ⟨hq1, hq2⟩ := ctlOnly_eval peek q h.2 (p.eval peek c st).1 (p.eval peek c st).2
    simp only [Prog.eval]
    exact ⟨hq1.trans hp1, fun j hj => (hq2 j hj).trans (hp2 j hj)⟩
  | .ite b p q, h, c, st => by
    simp only [Prog.eval]
    split
    · exact ctlOnly_eval peek p h.1 c st
    · exact ctlOnly_eval peek q h.2 c st

/-- A controller step: new finite control, workers' controls kept. -/
def cctl (g : Ctrl Cm Cf → (Fin (KK Km Kf) → List (Γm ⊕ Γf)) → Ctl) :
    Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .ctl fun c v => (g c v, c.2)

theorem ctlOnly_pop (x : CStack) :
    CtlOnly (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) (Km := Km) (Kf := Kf) (.pop (cI x)) := by
  simp only [CtlOnly, cI_val]; exact x.pos_lt

theorem ctlOnly_push (x : CStack) (f : Ctrl Cm Cf → (Fin (KK Km Kf) → List (Γm ⊕ Γf)) → Γm ⊕ Γf) :
    CtlOnly (.push (cI x) f) := by
  simp only [CtlOnly, cI_val]; exact x.pos_lt

theorem ctlOnly_copy (y : Fin (KK Km Kf)) (x : CStack) :
    CtlOnly (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) (.copy y (cI x)) := by
  simp only [CtlOnly, cI_val]; exact x.pos_lt

theorem ctlOnly_clear (x : CStack) :
    CtlOnly (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) (Km := Km) (Kf := Kf) (.clear (cI x)) := by
  simp only [CtlOnly, cI_val]; exact x.pos_lt

theorem ctlOnly_cctl (g : Ctrl Cm Cf → (Fin (KK Km Kf) → List (Γm ⊕ Γf)) → Ctl) :
    CtlOnly (cctl g) := fun _ _ => rfl

@[simp] theorem eval_cctl (peek : ℕ) (g : Ctrl Cm Cf → (Fin (KK Km Kf) → List (Γm ⊕ Γf)) → Ctl)
    (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) :
    (cctl g).eval peek c st = ((g c (view peek st), c.2), st) := rfl

end Machine

/-! ## The representation of the controller -/

/-- Stage `t` is represented by its finite fields `y`, its `half` / `clock` stacks (by length)
and its four result stacks (symbol by symbol through `enc`). -/
structure SRep {Γ : Type} (enc : Bool → Γ) (t : StageState) (y : StageCtl) (h cl : List Γ)
    (res : Fin 4 → List Γ) : Prop where
  alive : y.alive = t.alive
  interval : y.interval = t.interval
  pending : y.pending = t.pending
  batch : y.batch = t.batch
  birth : y.birth = t.birth
  release : y.release = t.release
  middle : y.middle = t.middle
  half : h.length = t.half
  clock : cl.length = t.clock
  results : ∀ r, res r = (t.results r).map enc

theorem SRep.answering {Γ : Type} {enc : Bool → Γ} {t : StageState} {y : StageCtl}
    {h cl : List Γ} {res : Fin 4 → List Γ} (hS : SRep enc t y h cl res) :
    y.answering = ScaWindowPal.answering t := by
  simp [StageCtl.answering, ScaWindowPal.answering, hS.alive, hS.interval]

/-- The controller's part of the state is represented by the finite control and the controller
stacks. -/
structure CRep {Wm Wf Γ : Type} {Km Kf : ℕ} (enc : Bool → Γ) (s : PalState Wm Wf) (x : Ctl)
    (st : Fin (KK Km Kf) → List Γ) : Prop where
  powerReady : x.powerReady = s.powerReady
  slot : x.slot = s.slot
  small : x.small = s.small
  first : x.first = s.first
  fault : x.fault = s.fault
  output : x.output = s.output
  history : (st (cI .history)).length = s.history
  power : (st (cI .power)).length = s.power
  nextBirth : (st (cI .nextBirth)).length = s.nextBirth
  stage : ∀ i, SRep enc (s.stages i) (x.stg i) (st (cI (.half i))) (st (cI (.clock i)))
    (fun r => st (cI (.res i r)))

theorem CRep.congr {Wm Wf Γ : Type} {Km Kf : ℕ} {enc : Bool → Γ} {s : PalState Wm Wf} {x : Ctl}
    {st st' : Fin (KK Km Kf) → List Γ} (h : CRep enc s x st)
    (hst : ∀ y, st' (cI y) = st (cI y)) : CRep enc s x st' where
  powerReady := h.powerReady
  slot := h.slot
  small := h.small
  first := h.first
  fault := h.fault
  output := h.output
  history := by rw [hst]; exact h.history
  power := by rw [hst]; exact h.power
  nextBirth := by rw [hst]; exact h.nextBirth
  stage i := by simp only [hst]; exact h.stage i

/-- The controller's representation only looks at the controller's fields. -/
def SameCtl {Wm Wf : Type} (s s' : PalState Wm Wf) : Prop :=
  s'.history = s.history ∧ s'.power = s.power ∧ s'.nextBirth = s.nextBirth ∧
    s'.stages = s.stages ∧ s'.powerReady = s.powerReady ∧ s'.slot = s.slot ∧ s'.small = s.small ∧
    s'.first = s.first ∧ s'.fault = s.fault ∧ s'.output = s.output

theorem CRep.transfer {Wm Wf Γ : Type} {Km Kf : ℕ} {enc : Bool → Γ} {s s' : PalState Wm Wf}
    {x : Ctl} {st : Fin (KK Km Kf) → List Γ} (h : CRep enc s x st) (hs : SameCtl s s') :
    CRep enc s' x st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  exact ⟨h.powerReady.trans h5.symm, h.slot.trans h6.symm, h.small.trans h7.symm,
    h.first.trans h8.symm, h.fault.trans h9.symm, h.output.trans h10.symm,
    h.history.trans h1.symm, h.power.trans h2.symm, h.nextBirth.trans h3.symm,
    fun i => h4 ▸ h.stage i⟩

section Controller
variable {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf] {Km Kf D : ℕ}
  {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
  (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D)

/-- Result packets are stored as the flag worker's flag symbols. -/
def encR (b : Bool) : Γm ⊕ Γf := Sum.inr (fE.flagSym b)

/-- Decoding one result symbol. -/
def decR (x : Γm ⊕ Γf) : Bool := fE.flagDecode (Sum.elim (fun _ => default) id x)

omit [Inhabited Γm] in
theorem decR_encR (b : Bool) : decR (Γm := Γm) fE (encR (Γm := Γm) fE b) = b :=
  fE.flagDecode_sym b

/-- **The whole representation.** -/
structure Rep (s : PalState Wm Wf) (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) :
    Prop where
  ctl : CRep (encR (Γm := Γm) fE) s c.1 st
  mat : ∀ i, WRep (emM (Γf := Γf) (Kf := Kf) i) mE.Rep (s.matchers i) c st
  flg : ∀ i, WRep (emF (Γm := Γm) (Km := Km) i) fE.Rep (s.flags i) c st

/-- No worker of `s` has faulted. -/
def NoFault (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (s : PalState Wm Wf) : Prop :=
  ∀ i, mOps.faulted (s.matchers i) = false ∧ fOps.faulted (s.flags i) = false

/-- `g` keeps worker faults: if nothing has faulted after `g`, nothing had faulted before. -/
def Keeps (mOps : WorkerOps Wm) (fOps : WorkerOps Wf) (g : PalState Wm Wf → PalState Wm Wf) :
    Prop :=
  ∀ s, NoFault mOps fOps (g s) → NoFault mOps fOps s

theorem Keeps.comp {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
    {f g : PalState Wm Wf → PalState Wm Wf} (hf : Keeps mOps fOps f) (hg : Keeps mOps fOps g) :
    Keeps mOps fOps (fun s => g (f s)) := fun s h => hf s (hg (f s) h)

theorem Keeps.of_workers {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
    (g : PalState Wm Wf → PalState Wm Wf) (hmat : ∀ s, (g s).matchers = s.matchers)
    (hfl : ∀ s, (g s).flags = s.flags) : Keeps mOps fOps g := fun s h i => by
  have := h i
  rw [hmat, hfl] at this
  exact this

/-- `p` simulates the abstract update `f`, whenever `f`'s result has no faulted worker. -/
def Sim (f : PalState Wm Wf → PalState Wm Wf) (p : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf)) :
    Prop :=
  ∀ s c st, Rep mE fE s c st → NoFault mOps fOps (f s) →
    Rep mE fE (f s) (p.eval D c st).1 (p.eval D c st).2

theorem Sim.seq {f g : PalState Wm Wf → PalState Wm Wf}
    {p q : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf)} (hp : Sim mE fE f p) (hq : Sim mE fE g q)
    (hg : Keeps mOps fOps g) :
    Sim mE fE (fun s => g (f s)) (.seq p q) := fun s c st h hnf =>
  hq _ _ _ (hp s c st h (hg _ hnf)) hnf

/-! ### Worker steps -/

/-- Matcher `i` performs `p`. -/
def mOp (i : Fin 2) (p : Prog Γm Cm Km) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  embed (emM i) p

/-- Flag worker `i` performs `p`. -/
def fOp (i : Fin 2) (p : Prog Γf Cf Kf) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  embed (emF i) p

/-- Update matcher `i` of the abstract state. -/
def updM (i : Fin 2) (f : Wm → Wm) (s : PalState Wm Wf) : PalState Wm Wf :=
  { s with matchers := Function.update s.matchers i (f (s.matchers i)) }

/-- Update flag worker `i` of the abstract state. -/
def updF (i : Fin 2) (f : Wf → Wf) (s : PalState Wm Wf) : PalState Wm Wf :=
  { s with flags := Function.update s.flags i (f (s.flags i)) }

omit [Inhabited Γm] [Inhabited Γf] in
/-- A sticky matcher operation keeps faults. -/
theorem keeps_updM (i : Fin 2) (f : StageState → Wm → Wm)
    (hf : ∀ b w, mOps.faulted w = true → mOps.faulted (f b w) = true) :
    Keeps mOps fOps (fun s => updM i (f (s.stages i)) s) := fun s h j => by
  have hj := h j
  simp only [updM] at hj
  refine ⟨?_, hj.2⟩
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self] at hj
    cases hw : mOps.faulted (s.matchers j)
    · rfl
    · rw [hf _ _ hw] at hj; exact absurd hj.1 (by simp)
  · rw [Function.update_of_ne hji] at hj; exact hj.1

omit [Inhabited Γm] [Inhabited Γf] in
/-- A sticky flag-worker operation keeps faults. -/
theorem keeps_updF (i : Fin 2) (f : StageState → Wf → Wf)
    (hf : ∀ b w, fOps.faulted w = true → fOps.faulted (f b w) = true) :
    Keeps mOps fOps (fun s => updF i (f (s.stages i)) s) := fun s h j => by
  have hj := h j
  simp only [updF] at hj
  refine ⟨hj.1, ?_⟩
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self] at hj
    cases hw : fOps.faulted (s.flags j)
    · rfl
    · rw [hf _ _ hw] at hj; exact absurd hj.2 (by simp)
  · rw [Function.update_of_ne hji] at hj; exact hj.2

theorem sim_mOp (i : Fin 2) (p : Prog Γm Cm Km) (f : Wm → Wm)
    (hp : ∀ w c st, mE.Rep w c st → mOps.faulted (f w) = false →
      mE.Rep (f w) (p.eval D c st).1 (p.eval D c st).2) :
    Sim mE fE (updM i f) (mOp (Γf := Γf) (Cf := Cf) (Kf := Kf) i p) := by
  intro s c st h hnf
  have hfi : mOps.faulted (f (s.matchers i)) = false := by
    have := (hnf i).1
    simpa [updM] using this
  have hfst : ((mOp (Γf := Γf) (Cf := Cf) (Kf := Kf) i p).eval D c st).1.1 = c.1 :=
    eval_embed_fix (emM (Γf := Γf) (Cf := Cf) (Kf := Kf) i) Prod.fst (fun _ _ => rfl) D p c st
  have hother : ∀ j, (∀ k, (mI i k : Fin (KK Km Kf)) ≠ j) →
      ((mOp (Γf := Γf) (Cf := Cf) (Kf := Kf) i p).eval D c st).2 j = st j :=
    fun j hj => eval_embed_other _ D p c st j hj
  refine ⟨?_, ?_, ?_⟩
  · rw [hfst]
    exact (h.ctl.congr fun y => hother _ fun k => (cI_ne_mI y i k).symm).transfer
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i'
    by_cases hi : i' = i
    · subst hi
      simp only [updM, Function.update_self]
      exact wrep_embed _ D f p (fun c st hr => hp _ c st hr hfi) (h.mat i')
    · simp only [updM, Function.update_of_ne hi]
      refine wrep_frame _ (h.mat i') ?_ fun k => hother _ fun k' => mI_ne_mI (Ne.symm hi) k' k
      exact eval_embed_fix (emM (Γf := Γf) (Cf := Cf) (Kf := Kf) i) (fun c => c.2.1 i')
        (fun c x => by simp [emM, Function.update_of_ne hi]) D p c st
  · intro i'
    refine wrep_frame _ (h.flg i') ?_ fun k => hother _ fun k' => mI_ne_fI i i' k' k
    exact eval_embed_fix (emM (Γf := Γf) (Cf := Cf) (Kf := Kf) i) (fun c => c.2.2 i')
      (fun _ _ => rfl) D p c st

theorem sim_fOp (i : Fin 2) (p : Prog Γf Cf Kf) (f : Wf → Wf)
    (hp : ∀ w c st, fE.Rep w c st → fOps.faulted (f w) = false →
      fE.Rep (f w) (p.eval D c st).1 (p.eval D c st).2) :
    Sim mE fE (updF i f) (fOp (Γm := Γm) (Cm := Cm) (Km := Km) i p) := by
  intro s c st h hnf
  have hfi : fOps.faulted (f (s.flags i)) = false := by
    have := (hnf i).2
    simpa [updF] using this
  have hfst : ((fOp (Γm := Γm) (Cm := Cm) (Km := Km) i p).eval D c st).1.1 = c.1 :=
    eval_embed_fix (emF (Γm := Γm) (Cm := Cm) (Km := Km) i) Prod.fst (fun _ _ => rfl) D p c st
  have hother : ∀ j, (∀ k, (fI i k : Fin (KK Km Kf)) ≠ j) →
      ((fOp (Γm := Γm) (Cm := Cm) (Km := Km) i p).eval D c st).2 j = st j :=
    fun j hj => eval_embed_other _ D p c st j hj
  refine ⟨?_, ?_, ?_⟩
  · rw [hfst]
    exact (h.ctl.congr fun y => hother _ fun k => (cI_ne_fI y i k).symm).transfer
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i'
    refine wrep_frame _ (h.mat i') ?_ fun k => hother _ fun k' => (mI_ne_fI i' i k k').symm
    exact eval_embed_fix (emF (Γm := Γm) (Cm := Cm) (Km := Km) i) (fun c => c.2.1 i')
      (fun _ _ => rfl) D p c st
  · intro i'
    by_cases hi : i' = i
    · subst hi
      simp only [updF, Function.update_self]
      exact wrep_embed _ D f p (fun c st hr => hp _ c st hr hfi) (h.flg i')
    · simp only [updF, Function.update_of_ne hi]
      refine wrep_frame _ (h.flg i') ?_ fun k => hother _ fun k' => fI_ne_fI (Ne.symm hi) k' k
      exact eval_embed_fix (emF (Γm := Γm) (Cm := Cm) (Km := Km) i) (fun c => c.2.2 i')
        (fun c x => by simp [emF, Function.update_of_ne hi]) D p c st

/-- Matcher `i` performs `P b`, where `b` is read from stage `i`'s finite fields. -/
def mSel (i : Fin 2) (sel : StageCtl → Bool) (P : Bool → Prog Γm Cm Km) :
    Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .ite (fun c _ => sel (c.1.stg i)) (mOp i (P true)) (mOp i (P false))

/-- Flag worker `i` performs `P b`, where `b` is read from stage `i`'s finite fields. -/
def fSel (i : Fin 2) (sel : StageCtl → Bool) (P : Bool → Prog Γf Cf Kf) :
    Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .ite (fun c _ => sel (c.1.stg i)) (fOp i (P true)) (fOp i (P false))

theorem sim_mSel (i : Fin 2) (sel : StageCtl → Bool) (selA : StageState → Bool)
    (hsel : ∀ (t : StageState) (y : StageCtl) (h cl : List (Γm ⊕ Γf)) (res : Fin 4 → List (Γm ⊕ Γf)),
      SRep (encR (Γm := Γm) fE) t y h cl res → sel y = selA t)
    (P : Bool → Prog Γm Cm Km) (f : Bool → Wm → Wm)
    (hp : ∀ b w c st, mE.Rep w c st → mOps.faulted (f b w) = false →
      mE.Rep (f b w) ((P b).eval D c st).1 ((P b).eval D c st).2) :
    Sim mE fE (fun s => updM i (f (selA (s.stages i))) s)
      (mSel (Γf := Γf) (Cf := Cf) (Kf := Kf) i sel P) := by
  intro s c st h hnf
  simp only [mSel, Prog.eval]
  rw [hsel _ _ _ _ _ (h.ctl.stage i)]
  revert hnf
  beta_reduce
  cases selA (s.stages i)
  · exact sim_mOp mE fE i (P false) (f false) (hp false) s c st h
  · exact sim_mOp mE fE i (P true) (f true) (hp true) s c st h

theorem sim_fSel (i : Fin 2) (sel : StageCtl → Bool) (selA : StageState → Bool)
    (hsel : ∀ (t : StageState) (y : StageCtl) (h cl : List (Γm ⊕ Γf)) (res : Fin 4 → List (Γm ⊕ Γf)),
      SRep (encR (Γm := Γm) fE) t y h cl res → sel y = selA t)
    (P : Bool → Prog Γf Cf Kf) (f : Bool → Wf → Wf)
    (hp : ∀ b w c st, fE.Rep w c st → fOps.faulted (f b w) = false →
      fE.Rep (f b w) ((P b).eval D c st).1 ((P b).eval D c st).2) :
    Sim mE fE (fun s => updF i (f (selA (s.stages i))) s)
      (fSel (Γm := Γm) (Cm := Cm) (Km := Km) i sel P) := by
  intro s c st h hnf
  simp only [fSel, Prog.eval]
  rw [hsel _ _ _ _ _ (h.ctl.stage i)]
  revert hnf
  beta_reduce
  cases selA (s.stages i)
  · exact sim_fOp mE fE i (P false) (f false) (hp false) s c st h
  · exact sim_fOp mE fE i (P true) (f true) (hp true) s c st h

/-! ### Controller steps -/

/-- A controller-only program simulates `f` when it keeps the controller's representation and
`f` leaves the workers alone. -/
theorem sim_ctlOnly (p : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf)) (hp : CtlOnly p)
    (f : PalState Wm Wf → PalState Wm Wf) (hmat : ∀ s, (f s).matchers = s.matchers)
    (hfl : ∀ s, (f s).flags = s.flags)
    (hc : ∀ s c st, Rep mE fE s c st →
      CRep (encR (Γm := Γm) fE) (f s) (p.eval D c st).1.1 (p.eval D c st).2) :
    Sim mE fE f p := by
  intro s c st h _
  obtain ⟨h1, h2⟩ := ctlOnly_eval D p hp c st
  refine ⟨hc s c st h, fun i => ?_, fun i => ?_⟩
  · rw [hmat]
    exact wrep_frame _ (h.mat i) (by simp [emM, h1]) fun k => h2 _ (mI_ge i k)
  · rw [hfl]
    exact wrep_frame _ (h.flg i) (by simp [emF, h1]) fun k => h2 _ (fI_ge i k)

end Controller

/-! ## Stage updates of the controller representation -/

/-- The finite fields of an abstract stage. -/
def StageCtl.ofState (t : StageState) : StageCtl :=
  ⟨t.alive, t.interval, t.pending, t.batch, t.birth, t.release, t.middle⟩

theorem SRep.ctl_eq {Γ : Type} {enc : Bool → Γ} {t : StageState} {y : StageCtl}
    {h cl : List Γ} {res : Fin 4 → List Γ} (hS : SRep enc t y h cl res) :
    y = StageCtl.ofState t := by
  cases y
  simp only [StageCtl.ofState, StageCtl.mk.injEq]
  exact ⟨hS.alive, hS.interval, hS.pending, hS.batch, hS.birth, hS.release, hS.middle⟩

theorem SRep.of_ofState {Γ : Type} {enc : Bool → Γ} {t : StageState}
    {h cl : List Γ} {res : Fin 4 → List Γ} (hh : h.length = t.half) (hcl : cl.length = t.clock)
    (hres : ∀ r, res r = (t.results r).map enc) :
    SRep enc t (StageCtl.ofState t) h cl res :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hh, hcl, hres⟩

/-- The controller stacks owned by stage `i`. -/
def CStack.OfStage (i : Fin 2) : CStack → Prop
  | .half j => j = i
  | .clock j => j = i
  | .res j _ => j = i
  | _ => False

/-- **Updating one stage (and the fault bit).** -/
theorem CRep.stageUpd {Wm Wf Γ : Type} {Km Kf : ℕ} {enc : Bool → Γ} {s : PalState Wm Wf}
    {x x' : Ctl} {st st' : Fin (KK Km Kf) → List Γ} (h : CRep enc s x st) (i : Fin 2)
    (t' : StageState) (f' : Bool)
    (hx : x'.powerReady = x.powerReady ∧ x'.slot = x.slot ∧ x'.small = x.small ∧
      x'.first = x.first ∧ x'.output = x.output)
    (hfault : x'.fault = f') (hstg : ∀ j, j ≠ i → x'.stg j = x.stg j)
    (hst : ∀ y, ¬ y.OfStage i → st' (cI y) = st (cI y))
    (hS : SRep enc t' (x'.stg i) (st' (cI (.half i))) (st' (cI (.clock i)))
      (fun r => st' (cI (.res i r)))) :
    CRep enc { s with stages := Function.update s.stages i t', fault := f' } x' st' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨h1.trans h.powerReady, h2.trans h.slot, h3.trans h.small, h4.trans h.first, hfault,
    h5.trans h.output, ?_, ?_, ?_, fun j => ?_⟩
  · rw [hst _ (by simp [CStack.OfStage])]; exact h.history
  · rw [hst _ (by simp [CStack.OfStage])]; exact h.power
  · rw [hst _ (by simp [CStack.OfStage])]; exact h.nextBirth
  · by_cases hj : j = i
    · subst hj; simpa using hS
    · simp only [Function.update_of_ne hj]
      rw [hstg j hj, hst _ (by simp [CStack.OfStage, hj]), hst _ (by simp [CStack.OfStage, hj])]
      have hr : (fun r => st' (cI (.res j r))) = fun r => st (cI (.res j r)) := by
        funext r; exact hst _ (by simp [CStack.OfStage, hj])
      rw [hr]
      exact h.stage j

/-! ## `advance` -/

/-- The finite part of `advance`, given the boundary bit and the birth bit. -/
def advFin (y : StageCtl) (bnd nb : Bool) : StageCtl × Bool :=
  let iv1 := if bnd then incInterval y.interval else y.interval
  let rel := bnd && (iv1.val == 1 || iv1.val == 2 || iv1.val == 3 || iv1.val == 4)
  ({ alive := (y.alive && !(bnd && iv1.val == 6)) || nb
     interval := if nb then 0 else iv1
     pending := y.pending && !nb
     batch := if rel then batchOfInterval iv1 else y.batch
     birth := nb
     release := rel && !nb
     middle := y.middle }, rel && y.pending)

theorem advance_spec (t : StageState) (nb : Bool) (sh : ℕ) :
    StageCtl.ofState (advance t nb sh).1 =
        (advFin (StageCtl.ofState t)
          (t.alive && (if t.alive then t.clock.pred else t.clock) == 0) nb).1 ∧
      (advance t nb sh).2 =
        (advFin (StageCtl.ofState t)
          (t.alive && (if t.alive then t.clock.pred else t.clock) == 0) nb).2 ∧
      (advance t nb sh).1.half = (if nb then sh else t.half) ∧
      (advance t nb sh).1.clock = (if nb then sh else
        if t.alive && (if t.alive then t.clock.pred else t.clock) == 0 then t.half
        else if t.alive then t.clock.pred else t.clock) ∧
      (advance t nb sh).1.results = fun r => if nb then [] else t.results r :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

section Controller
variable {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf] {Km Kf D : ℕ}
  {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
  (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D)

/-- Stage `i`'s `advance` with `newBirth = birth ∧ slot = i` and `sourceHalf = power`. -/
def advS (i : Fin 2) (b : Bool) (s : PalState Wm Wf) : PalState Wm Wf :=
  { s with
    stages := Function.update s.stages i (advance (s.stages i) (b && s.slot == i) s.power).1
    fault := s.fault || (advance (s.stages i) (b && s.slot == i) s.power).2 }

/-- The finite-control step of `advance`: reads the boundary off the `clock` stack. -/
def advStep (i : Fin 2) (c : Ctrl Cm Cf) (v : Fin (KK Km Kf) → List (Γm ⊕ Γf)) : Ctl :=
  { c.1.setStg i (advFin (c.1.stg i) ((c.1.stg i).alive && decide (v (cI (.clock i)) = []))
        (c.1.bth && c.1.slot == i)).1 with
    fault := c.1.fault || (advFin (c.1.stg i)
      ((c.1.stg i).alive && decide (v (cI (.clock i)) = [])) (c.1.bth && c.1.slot == i)).2
    bnd := (c.1.stg i).alive && decide (v (cI (.clock i)) = []) }

/-- Clear stage `i`'s result stacks. -/
def clearRes (i : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (.clear (cI (.res i 0))) (.seq (.clear (cI (.res i 1)))
    (.seq (.clear (cI (.res i 2))) (.clear (cI (.res i 3)))))

/-- `advance()` of stage `i` (ScaffoldWindowPal.scala:27-44). -/
def advP (i : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (.ite (fun c _ => (c.1.stg i).alive) (.pop (cI (.clock i))) .skip)
    (.seq (cctl (advStep i))
      (.seq (.ite (fun c _ => c.1.bnd) (.copy (cI (.half i)) (cI (.clock i))) .skip)
        (.ite (fun c _ => c.1.bth && c.1.slot == i)
          (.seq (.copy (cI .power) (cI (.half i)))
            (.seq (.copy (cI .power) (cI (.clock i))) (clearRes i)))
          .skip)))

theorem ctlOnly_advP (i : Fin 2) : CtlOnly (advP (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf)
    (Km := Km) (Kf := Kf) i) := by
  exact ⟨⟨ctlOnly_pop _, trivial⟩, ctlOnly_cctl _, ⟨ctlOnly_copy _ _, trivial⟩,
    ⟨ctlOnly_copy _ _, ctlOnly_copy _ _, ctlOnly_clear _, ctlOnly_clear _, ctlOnly_clear _,
      ctlOnly_clear _⟩, trivial⟩

theorem view_nil_iff {Γ : Type} {K : ℕ} (hD : 1 ≤ D) (st : Fin K → List Γ) (k : Fin K) :
    view D st k = [] ↔ st k = [] := by
  simp only [view, List.take_eq_nil_iff]
  constructor
  · rintro (h | h)
    · omega
    · exact h
  · exact Or.inr

end Controller

section AdvProof
variable {Wm Wf Γm Γf Cm Cf : Type} {Km Kf D : ℕ}

theorem eval_seq {Γ C : Type} {K : ℕ} (p q : Prog Γ C K) (c : C) (st : Fin K → List Γ) :
    (Prog.seq p q).eval D c st = q.eval D (p.eval D c st).1 (p.eval D c st).2 := rfl

theorem eval_iteSkip {Γ C : Type} {K : ℕ} (b : C → (Fin K → List Γ) → Bool) (p : Prog Γ C K)
    (c : C) (st : Fin K → List Γ) :
    (Prog.ite b p .skip).eval D c st = if b c (view D st) then p.eval D c st else (c, st) := rfl

theorem advP_eval (i : Fin 2) (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) :
    let st1 := Function.update st (cI (.clock i))
      (if (c.1.stg i).alive then (st (cI (.clock i))).tail else st (cI (.clock i)))
    let x := advStep i c (view D st1)
    let st2 := Function.update st1 (cI (.clock i))
      (if x.bnd then st1 (cI (.half i)) else st1 (cI (.clock i)))
    (advP i).eval D c st =
      ((x, c.2), if c.1.bth && c.1.slot == i then
        Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update st2 (cI (.half i)) (st2 (cI .power)))
            (cI (.clock i)) (st2 (cI .power)))
          (cI (.res i 0)) []) (cI (.res i 1)) []) (cI (.res i 2)) []) (cI (.res i 3)) []
        else st2) := by
  intro st1 x st2
  have e1 : (Prog.ite (fun c _ => (c.1.stg i).alive) (.pop (cI (.clock i))) .skip).eval D c st =
      (c, st1) := by
    simp only [Prog.eval, st1]
    split <;> simp_all
  have e2 : (Prog.ite (fun (c : Ctrl Cm Cf) _ => c.1.bnd) (.copy (cI (.half i)) (cI (.clock i)))
      .skip).eval D ((x, c.2) : Ctrl Cm Cf) st1 = ((x, c.2), st2) := by
    simp only [Prog.eval, st2]
    split <;> simp_all
  simp only [advP, eval_seq, e1, eval_cctl]
  rw [e2, eval_iteSkip]
  have hx : x.bth = c.1.bth ∧ x.slot = c.1.slot := ⟨rfl, rfl⟩
  simp only [hx]
  split
  · simp only [Prog.eval, clearRes]
    rw [Function.update_of_ne (by simp)]
  · rfl

theorem CStack.not_ofStage {y : CStack} {i : Fin 2} (hy : ¬ y.OfStage i) :
    y ≠ .half i ∧ y ≠ .clock i ∧ ∀ r, y ≠ .res i r := by
  refine ⟨?_, ?_, fun r => ?_⟩ <;> rintro rfl <;> exact hy rfl

theorem crep_adv (hD : 1 ≤ D) (i : Fin 2) (b : Bool) {enc : Bool → Γm ⊕ Γf}
    (s : PalState Wm Wf) (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf))
    (h : CRep enc s c.1 st) (hb : c.1.bth = b) :
    CRep enc (advS i b s) ((advP i).eval D c st).1.1 ((advP i).eval D c st).2 := by
  have hS := h.stage i
  have hy := hS.ctl_eq
  have hnb : (c.1.bth && c.1.slot == i) = (b && s.slot == i) := by rw [hb, h.slot]
  rw [advP_eval]
  dsimp only
  set t := s.stages i with ht
  set st1 := Function.update st (cI (.clock i))
    (if (c.1.stg i).alive then (st (cI (.clock i))).tail else st (cI (.clock i))) with hst1
  have hc1 : (st1 (cI (.clock i))).length = if t.alive then t.clock.pred else t.clock := by
    rw [hst1, Function.update_self, hy]
    simp only [StageCtl.ofState]
    split
    · rw [List.length_tail, hS.clock, Nat.pred_eq_sub_one]
    · exact hS.clock
  have hbnd : ((c.1.stg i).alive && decide (view D st1 (cI (.clock i)) = [])) =
      (t.alive && (if t.alive then t.clock.pred else t.clock) == 0) := by
    rw [hy]
    simp only [StageCtl.ofState]
    congr 1
    rw [← hc1]
    simp only [view_nil_iff hD]
    generalize st1 (cI (.clock i)) = l
    cases l <;> rfl
  have hsp := advance_spec t (b && s.slot == i) s.power
  refine CRep.stageUpd h i _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ ?_
  · simp only [advStep, h.fault, hnb]
    rw [hbnd, hy, hsp.2.1]
  · intro j hj
    exact Ctl.setStg_stg_ne _ _ hj
  · intro y hy'
    obtain ⟨h1, h2, h3⟩ := CStack.not_ofStage hy'
    split <;> simp [h1, h2, h3, hst1]
  · have hxs : (advStep i c (view D st1)).stg i = StageCtl.ofState (advance t (b && s.slot == i) s.power).1 := by
      simp only [advStep, Ctl.setStg_stg_self, hnb]
      rw [hbnd, hy, hsp.1]
    rw [hxs]
    refine SRep.of_ofState ?_ ?_ ?_
    · rw [hsp.2.2.1]
      split <;> rename_i hn <;> simp only [hnb] at hn <;> simp [hn, hst1]
      · exact h.power
      · exact hS.half
    · rw [hsp.2.2.2.1]
      have hxb : (advStep i c (view D st1)).bnd =
          (t.alive && (if t.alive then t.clock.pred else t.clock) == 0) := hbnd
      split <;> rename_i hn <;> simp only [hnb] at hn
      · simp [hn, hst1]
        exact h.power
      · simp only [hn, Bool.false_eq_true, if_false, Function.update_self, hxb]
        by_cases hbd : (t.alive && (if t.alive then t.clock.pred else t.clock) == 0) = true
        · rw [if_pos hbd, if_pos hbd, hst1, Function.update_of_ne (by simp)]
          exact hS.half
        · rw [if_neg hbd, if_neg hbd]
          exact hc1
    · intro r
      rw [hsp.2.2.2.2]
      split <;> rename_i hn <;> simp only [hnb] at hn
      · fin_cases r <;> simp [hn, hst1]
      · simp [hn, hst1]
        exact hS.results r

theorem advP_ctl (i : Fin 2) (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) :
    ((advP i).eval D c st).1.1.bth = c.1.bth ∧ ((advP i).eval D c st).1.1.fr = c.1.fr := by
  rw [advP_eval]
  exact ⟨rfl, rfl⟩

/-! ## The per-letter prefix of `tick` (before the stage loop) -/

/-- `tick` up to the births: `first`, `small`, `history`, `nextBirth.drop(powerReady)`. -/
def pre1 (s : PalState Wm Wf) (a : Fin 2) : PalState Wm Wf :=
  { s with
    first := if s.small.val == 0 then a == 1 else s.first
    small := incSmall s.small
    history := s.history + 1
    nextBirth := if s.powerReady then s.nextBirth.pred else s.nextBirth }

/-- `birth = powerReady ∧ nextBirth.empty` after the drop. -/
def birthOf (s : PalState Wm Wf) : Bool :=
  s.powerReady && (if s.powerReady then s.nextBirth.pred else s.nextBirth) == 0

/-- `tick` after the stage advances: `power`, `nextBirth`, `slot`, `powerReady`. -/
def postS (fr b : Bool) (s : PalState Wm Wf) : PalState Wm Wf :=
  { s with
    power := if fr || b then s.history else s.power
    nextBirth := if fr || b then s.history else s.nextBirth
    slot := if b then s.slot + 1 else s.slot
    powerReady := true }

/-- The part of `tick` before the stage loop. -/
def preS (s : PalState Wm Wf) (a : Fin 2) : PalState Wm Wf :=
  postS (!s.powerReady) (birthOf s) (advS 1 (birthOf s) (advS 0 (birthOf s) (pre1 s a)))

/-- Finite part of the prefix: `firstRound`, `first`, `small`. -/
def preA (a : Fin 2) (c : Ctrl Cm Cf) (_ : Fin (KK Km Kf) → List (Γm ⊕ Γf)) : Ctl :=
  { c.1 with
    fr := !c.1.powerReady
    first := if c.1.small.val == 0 then a == 1 else c.1.first
    small := incSmall c.1.small }

/-- `birth := powerReady ∧ nextBirth.empty`. -/
def preD (c : Ctrl Cm Cf) (v : Fin (KK Km Kf) → List (Γm ⊕ Γf)) : Ctl :=
  { c.1 with bth := c.1.powerReady && decide (v (cI .nextBirth) = []) }

/-- The prefix program: `history.push`, `nextBirth.drop(powerReady)`, then `birth`. -/
def preP [Inhabited Γm] (a : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (cctl (preA a))
    (.seq (.push (cI .history) fun _ _ => Sum.inl default)
      (.seq (.ite (fun c _ => c.1.powerReady) (.pop (cI .nextBirth)) .skip) (cctl preD)))

/-- The postfix program: `power`/`nextBirth := history` when `firstRound ∨ birth`, `slot`,
`powerReady`. -/
def postP : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (.ite (fun c _ => c.1.fr || c.1.bth)
      (.seq (.copy (cI .history) (cI .power)) (.copy (cI .history) (cI .nextBirth))) .skip)
    (cctl fun c _ => { c.1 with
      slot := if c.1.bth then c.1.slot + 1 else c.1.slot
      powerReady := true })

theorem ctlOnly_preP [Inhabited Γm] (a : Fin 2) :
    CtlOnly (preP (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) (Km := Km) (Kf := Kf) a) :=
  ⟨ctlOnly_cctl _, ctlOnly_push _ _, ⟨ctlOnly_pop _, trivial⟩, ctlOnly_cctl _⟩

theorem ctlOnly_postP :
    CtlOnly (postP (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) (Km := Km) (Kf := Kf)) :=
  ⟨⟨⟨ctlOnly_copy _ _, ctlOnly_copy _ _⟩, trivial⟩, ctlOnly_cctl _⟩

theorem crep_pre1 [Inhabited Γm] (hD : 1 ≤ D) (a : Fin 2) {enc : Bool → Γm ⊕ Γf}
    (s : PalState Wm Wf) (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf))
    (h : CRep enc s c.1 st) :
    CRep enc (pre1 s a) ((preP a).eval D c st).1.1 ((preP a).eval D c st).2 ∧
      ((preP a).eval D c st).1.1.fr = !s.powerReady ∧
      ((preP a).eval D c st).1.1.bth = birthOf s := by
  set st1 := Function.update st (cI .history) (Sum.inl default :: st (cI .history)) with hst1
  set st2 := if c.1.powerReady then Function.update st1 (cI .nextBirth) (st1 (cI .nextBirth)).tail
    else st1 with hst2
  have heval : (preP a).eval D c st =
      ((preD (preA a c (view D st), c.2) (view D st2), c.2), st2) := by
    have hpr : (preA a c (view D st)).powerReady = c.1.powerReady := rfl
    simp only [preP, eval_seq, eval_cctl, Prog.eval, hpr, hst2]
    split <;> rfl
  have hnb : (st2 (cI .nextBirth)).length =
      if s.powerReady then s.nextBirth.pred else s.nextBirth := by
    simp only [hst2, h.powerReady]
    split
    · rw [Function.update_self, List.length_tail, hst1, Function.update_of_ne (by simp),
        h.nextBirth, Nat.pred_eq_sub_one]
    · rw [hst1, Function.update_of_ne (by simp)]
      exact h.nextBirth
  have hother : ∀ y, y ≠ .history → y ≠ .nextBirth → st2 (cI y) = st (cI y) := by
    intro y h1 h2
    simp only [hst2]
    split <;> simp [hst1, h1, h2]
  have hhist : (st2 (cI .history)).length = s.history + 1 := by
    simp only [hst2]
    split <;> simp [hst1, h.history]
  rw [heval]
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_⟩, ?_, ?_⟩
  · exact h.powerReady
  · exact h.slot
  · simp only [preD, preA, h.small]; rfl
  · simp only [preD, preA, h.small, h.first]; rfl
  · exact h.fault
  · exact h.output
  · exact hhist
  · rw [hother _ (by simp) (by simp)]; exact h.power
  · exact hnb
  · show SRep enc (s.stages i) (c.1.stg i) _ _ _
    rw [hother _ (by simp) (by simp), hother _ (by simp) (by simp)]
    have hr : (fun r => st2 (cI (.res i r))) = fun r => st (cI (.res i r)) := by
      funext r; exact hother _ (by simp) (by simp)
    rw [hr]
    exact h.stage i
  · simp only [preD, preA, h.powerReady]
  · simp only [preD, preA, h.powerReady, birthOf]
    congr 1
    rw [← hnb]
    simp only [view_nil_iff hD]
    generalize st2 (cI .nextBirth) = l
    cases l <;> rfl

theorem crep_post {enc : Bool → Γm ⊕ Γf} (fr b : Bool)
    (s : PalState Wm Wf) (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf))
    (h : CRep enc s c.1 st) (hfr : c.1.fr = fr) (hb : c.1.bth = b) :
    CRep enc (postS fr b s) (postP.eval D c st).1.1 (postP.eval D c st).2 := by
  subst hfr hb
  set st' := if c.1.fr || c.1.bth then Function.update (Function.update st (cI .power) (st (cI .history)))
    (cI .nextBirth) (st (cI .history)) else st with hst'
  have heval : postP.eval D c st = (({ c.1 with
      slot := if c.1.bth then c.1.slot + 1 else c.1.slot
      powerReady := true }, c.2), st') := by
    simp only [postP, eval_seq, eval_cctl, Prog.eval, hst']
    split
    · simp only [Function.update_of_ne (show cI (Km := Km) (Kf := Kf) .history ≠ cI .power by simp)]
    · rfl
  have hother : ∀ y, y ≠ .power → y ≠ .nextBirth → st' (cI y) = st (cI y) := by
    intro y h1 h2
    simp only [hst']
    split <;> simp [h1, h2]
  rw [heval]
  dsimp only
  refine ⟨rfl, ?_, h.small, h.first, h.fault, h.output, ?_, ?_, ?_, fun i => ?_⟩
  · simp only [h.slot]; rfl
  · rw [hother _ (by simp) (by simp)]; exact h.history
  · simp only [hst', postS]
    split <;> simp [h.history, h.power]
  · simp only [hst', postS]
    split <;> simp [h.history, h.nextBirth]
  · rw [hother _ (by simp) (by simp), hother _ (by simp) (by simp)]
    have hr : (fun r => st' (cI (.res i r))) = fun r => st (cI (.res i r)) := by
      funext r; exact hother _ (by simp) (by simp)
    rw [hr]
    exact h.stage i

end AdvProof

/-! ## `tick` factored into pieces -/

section Factor
variable {Wm Wf : Type} (mOps : WorkerOps Wm) (fOps : WorkerOps Wf)

/-- `tick`'s state after the stage advances, written exactly as in `tick`. -/
def preTick (s : PalState Wm Wf) (a : Fin 2) : PalState Wm Wf :=
  let current : Bool := a == 1
  let first := if s.small.val == 0 then current else s.first
  let small := incSmall s.small
  let history := s.history + 1
  let firstRound := !s.powerReady
  let nextBirth := if s.powerReady then s.nextBirth.pred else s.nextBirth
  let birth := s.powerReady && nextBirth == 0
  let (st0, v0) := advance (s.stages 0) (birth && s.slot == 0) s.power
  let (st1, v1) := advance (s.stages 1) (birth && s.slot == 1) s.power
  let power := if firstRound || birth then history else s.power
  let nextBirth := if firstRound || birth then history else nextBirth
  let slot := if birth then s.slot + 1 else s.slot
  { s with
    first := first, small := small, history := history, power := power,
    nextBirth := nextBirth, powerReady := true, slot := slot,
    stages := fun i => if i = 0 then st0 else st1,
    fault := s.fault || v0 || v1 }

/-- The end of `tick`: the stage-count check and the output. -/
def finishS (a : Fin 2) (s2 : PalState Wm Wf) : PalState Wm Wf :=
  let current : Bool := a == 1
  let active0 := answering (s2.stages 0)
  let active1 := answering (s2.stages 1)
  let violation := s2.small.val == 4 && !((active0 || active1) && !(active0 && active1))
  let ordinary :=
    (active0 && (s2.stages 0).middle && mOps.output (s2.matchers 0)) ||
    (active1 && (s2.stages 1).middle && mOps.output (s2.matchers 1))
  let short := s2.small.val == 1 ||
    ((s2.small.val == 2 || s2.small.val == 3) && (if current then s2.first else !s2.first))
  { s2 with
    fault := s2.fault || violation
    output := if s2.small.val == 4 then ordinary else short }

theorem tick_eq_preTick (s : PalState Wm Wf) (a : Fin 2) :
    tick mOps fOps s a =
      finishS mOps a (stageRound mOps fOps a 1 (stageRound mOps fOps a 0 (preTick s a))) := rfl

theorem preS_eq (s : PalState Wm Wf) (a : Fin 2) : preS s a = preTick s a := by
  simp only [preS, preTick, postS, advS, pre1, birthOf]
  congr 1
  funext i
  fin_cases i <;> simp

/-- `consume()` of stage `i`, with its violation. -/
def consS (i : Fin 2) (s : PalState Wm Wf) : PalState Wm Wf :=
  { s with
    stages := Function.update s.stages i (consume (s.stages i)).1
    fault := s.fault || (consume (s.stages i)).2 }

/-- `capture()` of stage `i` from flag worker `i`. -/
def capS (i : Fin 2) (s : PalState Wm Wf) : PalState Wm Wf :=
  { s with
    stages := Function.update s.stages i
      (capture (s.stages i) (fOps.modeDone (s.flags i)) (fOps.flags (s.flags i))) }

/-- `stageRound` as a chain of single steps. -/
def roundS (a : Fin 2) (i : Fin 2) (s : PalState Wm Wf) : PalState Wm Wf :=
  capS fOps i (updF i fOps.service (updM i mOps.service (consS i
    ((fun s => updF i (fOps.mark (s.stages i).release) s)
      ((fun s => updF i (fOps.start (s.stages i).release) s)
        ((fun s => updM i (mOps.start (s.stages i).birth) s)
          ((fun s => updF i (fOps.resetFlags (s.stages i).birth) s)
            (updF i (fOps.arrive a) (updM i (mOps.arrive a) s)))))))))

theorem stageRound_eq (a i : Fin 2) (s : PalState Wm Wf) :
    stageRound mOps fOps a i s = roundS mOps fOps a i s := by
  simp only [stageRound, roundS, capS, consS, updM, updF, Function.update_self,
    Function.update_idem]

/-! ## `consume` and `capture`, abstractly -/

theorem popFlag_false_snd (l : List Bool) : (popFlag false l).2.2 = false := by
  cases l <;> rfl

theorem consume_not (t : StageState) (h : answering t = false) :
    consume t = ({ t with middle := false }, false) := by
  unfold consume
  simp only [h]
  split <;> simp [popFlag_false_snd]

theorem consume_ans (t : StageState) (r : Fin 4) (hans : answering t = true)
    (hr : t.interval.val = r.val + 2) :
    consume t = ({ t with
      middle := (t.results r).headD false
      results := Function.update t.results r (t.results r).tail }, (t.results r).isEmpty) := by
  unfold consume
  simp only [hans]
  rw [dif_pos (by omega)]
  have hr' : (⟨t.interval.val - 2, by omega⟩ : Fin 4) = r := Fin.ext (by simp; omega)
  simp only [hr']
  rcases hl : t.results r with _ | ⟨b, rest⟩
  · simp only [popFlag, Bool.true_and, List.headD_nil, List.tail_nil, List.isEmpty_nil]
    refine Prod.ext ?_ rfl
    simp only [StageState.mk.injEq, true_and, and_true]
    funext r'
    by_cases hrr : r = r'
    · subst hrr; simp
    · simp [hrr, Function.update_of_ne (Ne.symm hrr)]
  · simp only [popFlag, Bool.true_and, List.headD_cons, List.tail_cons, List.isEmpty_cons]
    refine Prod.ext ?_ rfl
    simp only [StageState.mk.injEq, true_and, and_true]
    funext r'
    by_cases hrr : r = r'
    · subst hrr; simp
    · simp [hrr, Function.update_of_ne (Ne.symm hrr)]

end Factor

/-! ## `consume` as a program -/

section Consume
variable {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf] {Km Kf D : ℕ}
  {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
  (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D)

/-- The top bit of a result stack (`false` when empty), as `FlagStack.pop` returns it. -/
def headBit (l : List (Γm ⊕ Γf)) : Bool :=
  match l with
  | [] => false
  | x :: _ => decR fE x

theorem headBit_take (hD : 1 ≤ D) (l : List Bool) :
    headBit (Γm := Γm) fE ((l.map (encR fE)).take D) = l.headD false := by
  cases l with
  | nil => simp [headBit]
  | cons b rest =>
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    simp only [List.map_cons, List.take_succ_cons, headBit, List.headD_cons]
    exact decR_encR fE b

theorem isEmpty_take {α : Type} (hD : 1 ≤ D) (l : List Bool) (f : Bool → α) :
    ((l.map f).take D).isEmpty = l.isEmpty := by
  cases l with
  | nil => simp
  | cons b rest =>
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    rfl

/-- Pop result packet `r` of stage `i` into `middle` (the answering branch of `consume`). -/
def consBr (i : Fin 2) (r : Fin 4) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (cctl fun c v =>
      { c.1.setStg i { c.1.stg i with middle := headBit fE (v (cI (.res i r))) } with
        fault := c.1.fault || (v (cI (.res i r))).isEmpty })
    (.pop (cI (.res i r)))

/-- `consume()` of stage `i` (ScaffoldWindowPal.scala:46-58). -/
def consP (i : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .ite (fun c _ => (c.1.stg i).answering)
    (.ite (fun c _ => (c.1.stg i).interval.val == 2) (consBr fE i 0)
      (.ite (fun c _ => (c.1.stg i).interval.val == 3) (consBr fE i 1)
        (.ite (fun c _ => (c.1.stg i).interval.val == 4) (consBr fE i 2) (consBr fE i 3))))
    (cctl fun c _ => c.1.setStg i { c.1.stg i with middle := false })

theorem ctlOnly_consBr (i : Fin 2) (r : Fin 4) :
    CtlOnly (consBr (Γm := Γm) (Cm := Cm) (Km := Km) (Kf := Kf) fE i r) :=
  ⟨ctlOnly_cctl _, ctlOnly_pop _⟩

theorem ctlOnly_consP (i : Fin 2) :
    CtlOnly (consP (Γm := Γm) (Cm := Cm) (Km := Km) (Kf := Kf) fE i) :=
  ⟨⟨ctlOnly_consBr fE i 0, ctlOnly_consBr fE i 1, ctlOnly_consBr fE i 2, ctlOnly_consBr fE i 3⟩,
    ctlOnly_cctl _⟩

theorem consP_ans (i : Fin 2) (r : Fin 4) (c : Ctrl Cm Cf)
    (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) (hans : (c.1.stg i).answering = true)
    (hr : (c.1.stg i).interval.val = r.val + 2) :
    (consP fE i).eval D c st = (consBr fE i r).eval D c st := by
  simp only [consP, Prog.eval, hans, if_true, hr]
  fin_cases r <;> simp

theorem crep_consS (hD : 1 ≤ D) (i : Fin 2) (s : PalState Wm Wf) (c : Ctrl Cm Cf)
    (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) (h : CRep (encR fE) s c.1 st) :
    CRep (encR fE) (consS i s) ((consP fE i).eval D c st).1.1 ((consP fE i).eval D c st).2 := by
  have hS := h.stage i
  have hy := hS.ctl_eq
  have hans := hS.answering
  cases hA : ScaWindowPal.answering (s.stages i)
  · -- not answering: only `middle := false`
    have hc := consume_not (s.stages i) hA
    have heval : (consP fE i).eval D c st =
        ((c.1.setStg i { c.1.stg i with middle := false }, c.2), st) := by
      simp only [consP, Prog.eval, hans, hA, Bool.false_eq_true, if_false]
      rfl
    rw [heval]
    refine CRep.stageUpd h i _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ (fun _ _ => rfl) ?_
    · simp [Ctl.setStg, hc, h.fault]
    · intro j hj; exact Ctl.setStg_stg_ne _ _ hj
    · rw [Ctl.setStg_stg_self, hy, hc]
      exact SRep.of_ofState hS.half hS.clock hS.results
  · -- answering: pop the packet selected by `interval - 2`
    have hiv : 2 ≤ (s.stages i).interval.val ∧ (s.stages i).interval.val ≤ 5 := by
      simp only [ScaWindowPal.answering, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hA
      omega
    set r : Fin 4 := ⟨(s.stages i).interval.val - 2, by omega⟩ with hr
    have hrv : (s.stages i).interval.val = r.val + 2 := by simp only [hr]; omega
    have hc := consume_ans (s.stages i) r hA hrv
    rw [consP_ans fE i r c st (hans.trans hA) (by rw [hS.interval]; exact hrv)]
    have hres := hS.results r
    have heval : (consBr fE i r).eval D c st =
        (({ c.1.setStg i { c.1.stg i with middle := headBit fE (view D st (cI (.res i r))) } with
            fault := c.1.fault || (view D st (cI (.res i r))).isEmpty }, c.2),
          Function.update st (cI (.res i r)) (st (cI (.res i r))).tail) := rfl
    rw [heval]
    dsimp only
    refine CRep.stageUpd h i _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ ?_ ?_ ?_ ?_
    · simp only [hc, h.fault, view, hres, isEmpty_take hD]
    · intro j hj; exact Ctl.setStg_stg_ne _ _ hj
    · intro y hy'
      obtain ⟨_, _, h3⟩ := CStack.not_ofStage hy'
      simp [h3 r]
    · rw [Ctl.setStg_stg_self, hy, hc]
      simp only [view, hres, headBit_take fE hD]
      refine SRep.of_ofState ?_ ?_ fun r' => ?_
      · rw [Function.update_of_ne (by simp)]; exact hS.half
      · rw [Function.update_of_ne (by simp)]; exact hS.clock
      · by_cases hrr : r' = r
        · subst hrr
          simp [List.map_tail]
        · rw [Function.update_of_ne (by simpa using hrr)]
          show _ = List.map (encR fE) (Function.update (s.stages i).results r _ r')
          rw [Function.update_of_ne hrr]
          exact hS.results r'

end Consume

/-! ## `capture` and the end of `tick` as programs -/

section Capture
variable {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf] {Km Kf D : ℕ}
  {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
  (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D)

/-- Run `P r` for the stage-`i` batch `r` held in the control. -/
def onBatch (i : Fin 2) (P : Fin 4 → Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf)) :
    Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .ite (fun c _ => (c.1.stg i).batch.val == 0) (P 0)
    (.ite (fun c _ => (c.1.stg i).batch.val == 1) (P 1)
      (.ite (fun c _ => (c.1.stg i).batch.val == 2) (P 2) (P 3)))

omit [Inhabited Γm] [Inhabited Γf] in
theorem onBatch_eval (i : Fin 2) (P : Fin 4 → Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf))
    (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) :
    (onBatch i P).eval D c st = (P (c.1.stg i).batch).eval D c st := by
  simp only [onBatch, Prog.eval]
  have hr : ∀ r : Fin 4, (c.1.stg i).batch = r → ((if ((c.1.stg i).batch.val == 0) = true then
      (P 0).eval D c st else if ((c.1.stg i).batch.val == 1) = true then (P 1).eval D c st
      else if ((c.1.stg i).batch.val == 2) = true then (P 2).eval D c st else (P 3).eval D c st) =
      (P (c.1.stg i).batch).eval D c st) := by
    intro r hr
    rw [hr]
    fin_cases r <;> rfl
  exact hr _ rfl

/-- The finite part of `capture()` of stage `i`; the scratch bit `rel` records `done`. -/
def capCtl (i : Fin 2) (c : Ctrl Cm Cf) (_ : Fin (KK Km Kf) → List (Γm ⊕ Γf)) : Ctl :=
  { c.1.setStg i { c.1.stg i with
      pending := ((c.1.stg i).pending || (c.1.stg i).release) &&
        !(((c.1.stg i).pending || (c.1.stg i).release) && fE.modeDone (c.2.2 i)) } with
    rel := ((c.1.stg i).pending || (c.1.stg i).release) && fE.modeDone (c.2.2 i) }

/-- `capture()` of stage `i` (ScaffoldWindowPal.scala:60-67): when done, the result packet of
the current batch becomes a copy of flag worker `i`'s output flag stack. -/
def capP (i : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (cctl (capCtl fE i))
    (.ite (fun c _ => c.1.rel)
      (onBatch i fun r => .copy (fI i fE.flagsIdx) (cI (.res i r))) .skip)

theorem ctlOnly_capP (i : Fin 2) :
    CtlOnly (capP (Γm := Γm) (Cm := Cm) (Km := Km) (Kf := Kf) fE i) :=
  ⟨ctlOnly_cctl _, ⟨ctlOnly_copy _ _, ctlOnly_copy _ _, ctlOnly_copy _ _, ctlOnly_copy _ _⟩,
    trivial⟩

/-- Flag worker `i`'s output stack, read in the whole machine. -/
theorem flags_stack {s : PalState Wm Wf} {c : Ctrl Cm Cf} {st : Fin (KK Km Kf) → List (Γm ⊕ Γf)}
    (h : Rep mE fE s c st) (i : Fin 2) :
    st (fI i fE.flagsIdx) = (fOps.flags (s.flags i)).map (encR (Γm := Γm) fE) := by
  have h1 := pure_eq_map (emF (Γm := Γm) (Cm := Cm) (Km := Km) i) (h.flg i).2 fE.flagsIdx
  have h2 := fE.rep_flags _ _ _ (h.flg i).1
  change st (fI i fE.flagsIdx) = _ at h1
  rw [h1, h2, List.map_map]
  rfl

theorem crep_capS (i : Fin 2) (s : PalState Wm Wf) (c : Ctrl Cm Cf)
    (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) (h : Rep mE fE s c st) :
    CRep (encR fE) (capS fOps i s) ((capP fE i).eval D c st).1.1 ((capP fE i).eval D c st).2 := by
  have hS := h.ctl.stage i
  have hy := hS.ctl_eq
  have hmd : fOps.modeDone (s.flags i) = fE.modeDone (c.2.2 i) := fE.rep_modeDone _ _ _ (h.flg i).1
  have hfl := flags_stack mE fE h i
  set t := s.stages i with ht
  set x := capCtl fE i c (view D st) with hx
  have hdone : x.rel = ((t.pending || t.release) && fOps.modeDone (s.flags i)) := by
    rw [hx, hmd]; simp only [capCtl, hy]; rfl
  have hbatch : (x.stg i).batch = t.batch := by
    rw [hx]; simp only [capCtl, Ctl.setStg_stg_self, hy]; rfl
  set st' := if x.rel then Function.update st (cI (.res i t.batch)) (st (fI i fE.flagsIdx))
    else st with hst'
  have heval : (capP fE i).eval D c st = ((x, c.2), st') := by
    simp only [capP, eval_seq, eval_cctl, hst']
    rw [eval_iteSkip]
    split
    · rw [onBatch_eval]
      show ((x, c.2), Function.update st (cI (.res i (x.stg i).batch)) (st (fI i fE.flagsIdx))) = _
      rw [hbatch]
    · rfl
  have hcap : capS fOps i s = { s with
      stages := Function.update s.stages i
        (capture t (fOps.modeDone (s.flags i)) (fOps.flags (s.flags i))), fault := s.fault } :=
    rfl
  rw [heval, hcap]
  dsimp only
  refine CRep.stageUpd h.ctl i _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ h.ctl.fault
    (fun j hj => Ctl.setStg_stg_ne _ _ hj) ?_ ?_
  · intro y hy'
    obtain ⟨_, _, h3⟩ := CStack.not_ofStage hy'
    simp only [hst']
    split
    · rw [Function.update_of_ne (by simpa using h3 _)]
    · rfl
  · have hxs : x.stg i = StageCtl.ofState
        (capture t (fOps.modeDone (s.flags i)) (fOps.flags (s.flags i))) := by
      rw [hx, hmd]; simp only [capCtl, Ctl.setStg_stg_self, hy]; rfl
    rw [hxs]
    refine SRep.of_ofState ?_ ?_ fun r => ?_
    · simp only [hst']
      split
      · rw [Function.update_of_ne (by simp)]; exact hS.half
      · exact hS.half
    · simp only [hst']
      split
      · rw [Function.update_of_ne (by simp)]; exact hS.clock
      · exact hS.clock
    · simp only [hst', capture]
      by_cases hd : x.rel = true
      · rw [if_pos hd]
        rw [hdone] at hd
        by_cases hr : t.batch = r
        · subst hr
          simp [hd, hfl]
        · rw [Function.update_of_ne (by simpa using Ne.symm hr)]
          simp only [hd, Bool.true_and, beq_iff_eq, hr, if_false]
          exact hS.results r
      · rw [if_neg hd]
        rw [hdone] at hd
        simp only [Bool.not_eq_true] at hd
        simp only [hd, Bool.false_and, Bool.false_eq_true, if_false]
        exact hS.results r

/-- The finite part of the end of `tick`: the stage-count check and the output. -/
def finCtl (a : Fin 2) (c : Ctrl Cm Cf) (_ : Fin (KK Km Kf) → List (Γm ⊕ Γf)) : Ctl :=
  { c.1 with
    fault := c.1.fault || (c.1.small.val == 4 &&
      !(((c.1.stg 0).answering || (c.1.stg 1).answering) &&
        !((c.1.stg 0).answering && (c.1.stg 1).answering)))
    output := if c.1.small.val == 4 then
        ((c.1.stg 0).answering && (c.1.stg 0).middle && mE.output (c.2.1 0)) ||
        ((c.1.stg 1).answering && (c.1.stg 1).middle && mE.output (c.2.1 1))
      else c.1.small.val == 1 ||
        ((c.1.small.val == 2 || c.1.small.val == 3) &&
          (if (a == 1) = true then c.1.first else !c.1.first)) }

/-- The end of `tick` (ScaffoldWindowPal.scala:129-137). -/
def finishP (a : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) := cctl (finCtl mE a)

theorem ctlOnly_finishP (a : Fin 2) :
    CtlOnly (finishP (Γf := Γf) (Cf := Cf) (Kf := Kf) mE a) := ctlOnly_cctl _

theorem crep_finish (a : Fin 2) (s : PalState Wm Wf) (c : Ctrl Cm Cf)
    (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) (h : Rep mE fE s c st) :
    CRep (encR fE) (finishS mOps a s) ((finishP mE a).eval D c st).1.1
      ((finishP mE a).eval D c st).2 := by
  have hA0 := (h.ctl.stage 0).answering
  have hA1 := (h.ctl.stage 1).answering
  have hM0 := (h.ctl.stage 0).middle
  have hM1 := (h.ctl.stage 1).middle
  have hO0 : mOps.output (s.matchers 0) = mE.output (c.2.1 0) := mE.rep_output _ _ _ (h.mat 0).1
  have hO1 : mOps.output (s.matchers 1) = mE.output (c.2.1 1) := mE.rep_output _ _ _ (h.mat 1).1
  refine ⟨h.ctl.powerReady, h.ctl.slot, h.ctl.small, h.ctl.first, ?_, ?_, h.ctl.history,
    h.ctl.power, h.ctl.nextBirth, h.ctl.stage⟩
  · simp only [finishP, eval_cctl, finCtl, finishS, h.ctl.fault, h.ctl.small, hA0, hA1]
  · simp only [finishP, eval_cctl, finCtl, finishS, h.ctl.small, h.ctl.first, hA0, hA1, hM0, hM1,
      hO0, hO1]

end Capture

/-! ## The letter program and its simulation -/

section Letter
variable {Wm Wf Γm Γf Cm Cf : Type} [Inhabited Γm] [Inhabited Γf] {Km Kf D : ℕ}
  {mOps : WorkerOps Wm} {fOps : WorkerOps Wf}
  (mE : WorkerEnc Wm mOps Γm Cm Km D) (fE : WorkerEnc Wf fOps Γf Cf Kf D)

/-- The part of `tick` before the stage loop (ScaffoldWindowPal.scala:102-115). -/
def headP (a : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (.seq (.seq (preP a) (advP 0)) (advP 1)) postP

theorem ctlOnly_headP (a : Fin 2) :
    CtlOnly (headP (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) (Km := Km) (Kf := Kf) a) :=
  ⟨⟨⟨ctlOnly_preP a, ctlOnly_advP 0⟩, ctlOnly_advP 1⟩, ctlOnly_postP⟩

theorem crep_head (hD : 1 ≤ D) (a : Fin 2) {enc : Bool → Γm ⊕ Γf} (s : PalState Wm Wf)
    (c : Ctrl Cm Cf) (st : Fin (KK Km Kf) → List (Γm ⊕ Γf)) (h : CRep enc s c.1 st) :
    CRep enc (preS s a) ((headP a).eval D c st).1.1 ((headP a).eval D c st).2 := by
  obtain ⟨h1, hfr1, hb1⟩ := crep_pre1 hD a s c st h
  set c1 := (preP (Γf := Γf) (Cm := Cm) (Cf := Cf) (Km := Km) (Kf := Kf) a).eval D c st
  have h2 := crep_adv hD 0 (birthOf s) (pre1 s a) c1.1 c1.2 h1 hb1
  obtain ⟨hb2, hfr2⟩ := advP_ctl (D := D) 0 c1.1 c1.2
  set c2 := (advP (Γm := Γm) (Γf := Γf) 0).eval D c1.1 c1.2
  have h3 := crep_adv hD 1 (birthOf s) (advS 0 (birthOf s) (pre1 s a)) c2.1 c2.2 h2
    (hb2.trans hb1)
  obtain ⟨hb3, hfr3⟩ := advP_ctl (D := D) 1 c2.1 c2.2
  set c3 := (advP (Γm := Γm) (Γf := Γf) 1).eval D c2.1 c2.2
  exact crep_post (!s.powerReady) (birthOf s) _ c3.1 c3.2 h3 (hfr3.trans (hfr2.trans hfr1))
    (hb3.trans (hb2.trans hb1))

theorem sim_head (hD : 1 ≤ D) (a : Fin 2) :
    Sim mE fE (fun s => preS s a) (headP (Γm := Γm) (Γf := Γf) (Cm := Cm) (Cf := Cf) a) :=
  sim_ctlOnly mE fE _ (ctlOnly_headP a) _ (fun _ => rfl) (fun _ => rfl)
    fun s c st h => crep_head hD a s c st h.ctl

/-- One stage round (ScaffoldWindowPal.scala:117-128). -/
def roundP (a i : Fin 2) : Prog (Γm ⊕ Γf) (Ctrl Cm Cf) (KK Km Kf) :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (mOp i (mE.arrive a))
    (fOp i (fE.arrive a)))
    (fSel i (·.birth) fE.resetFlags))
    (mSel i (·.birth) mE.start))
    (fSel i (·.release) fE.start))
    (fSel i (·.release) fE.mark))
    (consP fE i))
    (mOp i mE.service))
    (fOp i fE.service))
    (capP fE i)

include mE fE in
theorem keeps_roundS (a i : Fin 2) : Keeps mOps fOps (roundS mOps fOps a i) := by
  have k := Keeps.comp (Keeps.comp (Keeps.comp (Keeps.comp (Keeps.comp (Keeps.comp (Keeps.comp
    (Keeps.comp (Keeps.comp
    (keeps_updM i (fun _ => mOps.arrive a) fun _ => mE.sticky_arrive a)
    (keeps_updF i (fun _ => fOps.arrive a) fun _ => fE.sticky_arrive a))
    (keeps_updF i (fun t => fOps.resetFlags t.birth)
      fun t => fE.sticky_resetFlags t.birth))
    (keeps_updM i (fun t => mOps.start t.birth)
      fun t => mE.sticky_start t.birth))
    (keeps_updF i (fun t => fOps.start t.release)
      fun t => fE.sticky_start t.release))
    (keeps_updF i (fun t => fOps.mark t.release)
      fun t => fE.sticky_mark t.release))
    (Keeps.of_workers (consS i) (fun _ => rfl) (fun _ => rfl)))
    (keeps_updM i (fun _ => mOps.service) fun _ => mE.sticky_service))
    (keeps_updF i (fun _ => fOps.service) fun _ => fE.sticky_service))
    (Keeps.of_workers (capS fOps i) (fun _ => rfl) (fun _ => rfl))
  exact k

theorem sim_round (hD : 1 ≤ D) (a i : Fin 2) :
    Sim mE fE (roundS mOps fOps a i) (roundP mE fE a i) := by
  have hs := Sim.seq mE fE (Sim.seq mE fE (Sim.seq mE fE (Sim.seq mE fE (Sim.seq mE fE (Sim.seq mE fE
    (Sim.seq mE fE (Sim.seq mE fE (Sim.seq mE fE
    (sim_mOp mE fE i _ _ (mE.rep_arrive a))
    (sim_fOp mE fE i _ _ (fE.rep_arrive a))
    (keeps_updF i (fun _ => fOps.arrive a) fun _ => fE.sticky_arrive a))
    (sim_fSel mE fE i (·.birth) (·.birth) (fun _ _ _ _ _ hS => hS.birth) _ _ fE.rep_resetFlags)
    (keeps_updF i (fun t => fOps.resetFlags t.birth)
      fun t => fE.sticky_resetFlags t.birth))
    (sim_mSel mE fE i (·.birth) (·.birth) (fun _ _ _ _ _ hS => hS.birth) _ _ mE.rep_start)
    (keeps_updM i (fun t => mOps.start t.birth)
      fun t => mE.sticky_start t.birth))
    (sim_fSel mE fE i (·.release) (·.release) (fun _ _ _ _ _ hS => hS.release) _ _
      fE.rep_start)
    (keeps_updF i (fun t => fOps.start t.release)
      fun t => fE.sticky_start t.release))
    (sim_fSel mE fE i (·.release) (·.release) (fun _ _ _ _ _ hS => hS.release) _ _
      fE.rep_mark)
    (keeps_updF i (fun t => fOps.mark t.release)
      fun t => fE.sticky_mark t.release))
    (sim_ctlOnly mE fE _ (ctlOnly_consP fE i) (consS i) (fun _ => rfl) (fun _ => rfl)
      fun s c st h => crep_consS fE hD i s c st h.ctl)
    (Keeps.of_workers (consS i) (fun _ => rfl) (fun _ => rfl)))
    (sim_mOp mE fE i _ _ (fun w c st h hf => mE.rep_service w c st h hf))
    (keeps_updM i (fun _ => mOps.service) fun _ => mE.sticky_service))
    (sim_fOp mE fE i _ _ (fun w c st h hf => fE.rep_service w c st h hf))
    (keeps_updF i (fun _ => fOps.service) fun _ => fE.sticky_service))
    (sim_ctlOnly mE fE _ (ctlOnly_capP fE i) (capS fOps i) (fun _ => rfl) (fun _ => rfl)
      fun s c st h => crep_capS mE fE i s c st h)
    (Keeps.of_workers (capS fOps i) (fun _ => rfl) (fun _ => rfl))
  exact hs

end Letter

end PalPeg.ScaWindowEncode
