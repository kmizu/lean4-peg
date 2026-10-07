import Shallot.Peg.Undecidable.MachSpec
import Complexity.NMacros
import Complexity.Univ.Load

/-!
# A kit for the printing stage

The printing stage uses ten of the 40 stacks; a state is a record `PS` of these ten stacks (`PS.L`, every other
stack empty), and the stacks are named by `Fld`. Programs are proven on records (`Rn`): the primitives, pushing
constants, moving a whole stack, and three loops — consuming a stack (`rn_consume`), counting down while consuming
another stack (`rn_count`), and repeating a body a number of times (`rn_iter`).
-/

namespace Shallot

open Complexity
open Complexity.Univ

/-- The ten stacks the printing stage uses. -/
structure PS where
  o : List Nat
  f : List Nat
  r : List Nat
  r2 : List Nat
  m : List Nat
  i : List Nat
  c : List Nat
  x : List Nat
  t : List Nat
  t2 : List Nat

/-- Names of the stacks. -/
inductive Fld where
  | o | f | r | r2 | m | i | c | x | t | t2
  deriving DecidableEq

def Fld.n : Fld → Nat
  | .o => 0 | .f => 1 | .r => 2 | .r2 => 3 | .m => 4 | .i => 5 | .c => 6 | .x => 7 | .t => 8 | .t2 => 9

def Fld.idx (g : Fld) : Fin UK := ⟨g.n, by cases g <;> decide⟩

theorem Fld.idx_ne {g h : Fld} (hgh : g ≠ h) : g.idx ≠ h.idx := by
  intro e
  have : g.n = h.n := congrArg Fin.val e
  cases g <;> cases h <;> simp_all [Fld.n]

def PS.get (s : PS) : Fld → List Nat
  | .o => s.o | .f => s.f | .r => s.r | .r2 => s.r2 | .m => s.m | .i => s.i | .c => s.c | .x => s.x
  | .t => s.t | .t2 => s.t2

def PS.upd (s : PS) : Fld → List Nat → PS
  | .o, l => { s with o := l }
  | .f, l => { s with f := l }
  | .r, l => { s with r := l }
  | .r2, l => { s with r2 := l }
  | .m, l => { s with m := l }
  | .i, l => { s with i := l }
  | .c, l => { s with c := l }
  | .x, l => { s with x := l }
  | .t, l => { s with t := l }
  | .t2, l => { s with t2 := l }

/-- The stacks of a record. -/
def PS.L (s : PS) : Lists UK := fun j =>
  if j.val = 0 then s.o else if j.val = 1 then s.f else if j.val = 2 then s.r else if j.val = 3 then s.r2
  else if j.val = 4 then s.m else if j.val = 5 then s.i else if j.val = 6 then s.c else if j.val = 7 then s.x
  else if j.val = 8 then s.t else if j.val = 9 then s.t2 else []

/-- The empty record. -/
def PS.e : PS := ⟨[], [], [], [], [], [], [], [], [], []⟩

theorem PS.L_get (s : PS) (g : Fld) : s.L g.idx = s.get g := by
  cases g <;> rfl

theorem PS.L_set (s : PS) (g : Fld) (l : List Nat) : s.L.set g.idx l = (s.upd g l).L := by
  funext j
  rcases j with ⟨j, hj⟩
  cases g <;> rcases j with _|_|_|_|_|_|_|_|_|_|j <;> simp [Lists.set, PS.L, PS.upd, Fld.idx, Fld.n, Fin.ext_iff]

@[simp] theorem PS.get_upd_same (s : PS) (g : Fld) (l : List Nat) : (s.upd g l).get g = l := by cases g <;> rfl

theorem PS.get_upd_ne (s : PS) {g h : Fld} (hgh : g ≠ h) (l : List Nat) : (s.upd g l).get h = s.get h := by
  cases g <;> cases h <;> simp_all [PS.upd, PS.get]

@[simp] theorem PS.upd_upd (s : PS) (g : Fld) (a b : List Nat) : (s.upd g a).upd g b = s.upd g b := by
  cases g <;> rfl

theorem PS.upd_comm (s : PS) {g h : Fld} (hgh : g ≠ h) (a b : List Nat) :
    (s.upd g a).upd h b = (s.upd h b).upd g a := by
  cases g <;> cases h <;> simp_all [PS.upd]

@[simp] theorem PS.upd_get (s : PS) (g : Fld) : s.upd g (s.get g) = s := by cases g <;> rfl

/-! ## Runs on records -/

/-- `p` takes the record `s` to `s'`. -/
def Rn (p : NProg UK) (s s' : PS) : Prop := ∃ c, NRuns p s.L s'.L c

theorem Rn.seq {p q : NProg UK} {s s₁ s₂ : PS} (h₁ : Rn p s s₁) (h₂ : Rn q s₁ s₂) : Rn (.seq p q) s s₂ :=
  let ⟨_, a⟩ := h₁; let ⟨_, b⟩ := h₂; ⟨_, a.seq b⟩

theorem Rn.eq {p : NProg UK} {s s₁ s₂ : PS} (h : Rn p s s₁) (e : s₁ = s₂) : Rn p s s₂ := e ▸ h

theorem Rn.iteT {g : Fld} {c : NTest} {p q : NProg UK} {s s' : PS} (hc : c.eval (s.get g) = true) (h : Rn p s s') :
    Rn (.ite g.idx c p q) s s' := by
  obtain ⟨_, a⟩ := h
  exact ⟨_, NRuns.iteT (by rw [PS.L_get]; exact hc) a⟩

theorem Rn.iteF {g : Fld} {c : NTest} {p q : NProg UK} {s s' : PS} (hc : c.eval (s.get g) = false) (h : Rn q s s') :
    Rn (.ite g.idx c p q) s s' := by
  obtain ⟨_, a⟩ := h
  exact ⟨_, NRuns.iteF (by rw [PS.L_get]; exact hc) a⟩

theorem Rn.loopF {g : Fld} {c : NTest} {p : NProg UK} {s : PS} (hc : c.eval (s.get g) = false) :
    Rn (.loop g.idx c p) s s :=
  ⟨1, nruns_loop_exit (by rw [PS.L_get]; exact hc)⟩

theorem Rn.loopC {g : Fld} {c : NTest} {p : NProg UK} {s s₁ s₂ : PS} (hc : c.eval (s.get g) = true)
    (h : Rn p s s₁) (h' : Rn (.loop g.idx c p) s₁ s₂) : Rn (.loop g.idx c p) s s₂ := by
  obtain ⟨_, t₁, _, x₁⟩ := h
  obtain ⟨_, t₂, _, x₂⟩ := h'
  exact ⟨t₁ + 1 + t₂, t₁ + 1 + t₂, Nat.le_refl _, .loopC trivial (by rw [PS.L_get]; exact hc) x₁ x₂⟩

/-! ## Primitives -/

theorem rn_prim (a : NPrim UK) (s s' : PS) (h : a.apply s.L = s'.L) : Rn (.prim a) s s' :=
  ⟨1, h ▸ nruns_prim a s.L⟩

theorem rn_pushZ (g : Fld) (s : PS) : Rn (.prim (.pushZ g.idx)) s (s.upd g (s.get g ++ [0])) :=
  rn_prim _ _ _ (by simp only [NPrim.apply, PS.L_get, PS.L_set])

theorem rn_inc (g : Fld) (s : PS) : Rn (.prim (.inc g.idx)) s (s.upd g (mapTop (· + 1) (s.get g))) :=
  rn_prim _ _ _ (by simp only [NPrim.apply, PS.L_get, PS.L_set])

theorem rn_dec (g : Fld) (s : PS) {l : List Nat} {v : Nat} (h : s.get g = l ++ [v]) :
    Rn (.prim (.dec g.idx)) s (s.upd g (l ++ [v - 1])) :=
  rn_prim _ _ _ (by simp only [NPrim.apply, PS.L_get, PS.L_set, h, mapTop_snoc])

theorem rn_pop (g : Fld) (s : PS) {l : List Nat} {v : Nat} (h : s.get g = l ++ [v]) :
    Rn (.prim (.pop g.idx)) s (s.upd g l) :=
  rn_prim _ _ _ (by simp only [NPrim.apply, PS.L_get, PS.L_set, h, List.dropLast_concat])

/-- Push a copy of the top of `g` onto `h`. -/
def pdup (g h : Fld) (hgh : g ≠ h) : NProg UK := .prim (.dup g.idx h.idx (Fld.idx_ne hgh))

theorem rn_dup {g h : Fld} (hgh : g ≠ h) (s : PS) {l : List Nat} {v : Nat} (hs : s.get g = l ++ [v]) :
    Rn (pdup g h hgh) s (s.upd h (s.get h ++ [v])) :=
  rn_prim _ _ _ (by simp only [NPrim.apply, PS.L_get, PS.L_set, hs, List.getLast?_concat, Option.toList_some])

/-- Move the top of `g` onto `h`. -/
def pmv (g h : Fld) (hgh : g ≠ h) : NProg UK := .seq (pdup g h hgh) (.prim (.pop g.idx))

theorem rn_mv {g h : Fld} (hgh : g ≠ h) (s : PS) {l : List Nat} {v : Nat} (hs : s.get g = l ++ [v]) :
    Rn (pmv g h hgh) s ((s.upd h (s.get h ++ [v])).upd g l) :=
  (rn_dup hgh s hs).seq (rn_pop g _ (by rw [PS.get_upd_ne _ (Ne.symm hgh)]; exact hs))

theorem rn_pushC (g : Fld) (s : PS) (v : Nat) : Rn (npushC g.idx v) s (s.upd g (s.get g ++ [v])) := by
  have := nruns_pushC g.idx s.L v
  rw [PS.L_get, PS.L_set] at this
  exact ⟨_, this⟩

theorem rn_load (g : Fld) (s : PS) (l : List Nat) : Rn (nloadP g.idx l) s (s.upd g (s.get g ++ l)) := by
  have := nruns_load g.idx l s.L
  rw [PS.L_get, PS.L_set] at this
  exact ⟨_, this⟩

/-- Move all of `g` onto `h` (reversing it). -/
def pmvAll (g h : Fld) (hgh : g ≠ h) : NProg UK := nmvAll g.idx h.idx (Fld.idx_ne hgh)

theorem rn_mvAll {g h : Fld} (hgh : g ≠ h) (s : PS) :
    Rn (pmvAll g h hgh) s ((s.upd h (s.get h ++ (s.get g).reverse)).upd g []) := by
  have := nruns_mvAll g.idx h.idx (Fld.idx_ne hgh) s.L
  rw [PS.L_get, PS.L_get, PS.L_set, PS.L_set] at this
  exact ⟨_, this⟩

theorem rn_clr (g : Fld) (s : PS) : Rn (nclr g.idx) s (s.upd g []) := by
  have := nruns_clr g.idx s.L
  rw [PS.L_set] at this
  exact ⟨_, this⟩

/-! ## Loops -/

/-- **Consuming a stack**: the body pops the top `v` of `x` and acts by `φ v`. -/
theorem rn_consume (x : Fld) (body : NProg UK) (φ : Nat → PS → PS)
    (hb : ∀ s v l, Rn body (s.upd x (l ++ [v])) ((φ v s).upd x l)) :
    ∀ (L : List Nat) (s : PS), Rn (.loop x.idx .nonempty body) (s.upd x L.reverse)
      ((L.foldl (fun s v => φ v s) s).upd x [])
  | [], s => by
    refine Rn.loopF ?_
    simp [NTest.eval]
  | v :: L, s => by
    have e : (v :: L).reverse = L.reverse ++ [v] := List.reverse_cons
    rw [e]
    exact Rn.loopC (by simp) (hb s v L.reverse) (rn_consume x body φ hb L (φ v s))

/-- **Counting down `x` from the length of a word on `r`**, the body consuming the next symbol `v` of `r` and acting
by `φ v`. -/
theorem rn_count (x r : Fld) (hxr : x ≠ r) (body : NProg UK) (φ : Nat → PS → PS) (l : List Nat)
    (hb : ∀ s v u rest, Rn body ((s.upd x (l ++ [u])).upd r (rest ++ [v])) (((φ v s).upd x (l ++ [u])).upd r rest)) :
    ∀ (w : List Nat) (s : PS) (rest : List Nat),
      Rn (.loop x.idx .pos (.seq (.prim (.dec x.idx)) body)) ((s.upd x (l ++ [w.length])).upd r (rest ++ w.reverse))
        (((w.foldl (fun s v => φ v s) s).upd x (l ++ [0])).upd r rest)
  | [], s, rest => by
    simp only [List.length_nil, List.reverse_nil, List.append_nil, List.foldl_nil]
    refine Rn.loopF ?_
    rw [PS.get_upd_ne _ (Ne.symm hxr)]; simp
  | v :: w, s, rest => by
    have hg : ((s.upd x (l ++ [(v :: w).length])).upd r (rest ++ (v :: w).reverse)).get x = l ++ [w.length + 1] := by
      rw [PS.get_upd_ne _ (Ne.symm hxr)]; simp
    refine Rn.loopC (by rw [hg]; simp) ((rn_dec x _ hg).seq ?_) (rn_count x r hxr body φ l hb w (φ v s) rest)
    have e : (((s.upd x (l ++ [(v :: w).length])).upd r (rest ++ (v :: w).reverse)).upd x (l ++ [w.length + 1 - 1]))
        = (s.upd x (l ++ [w.length])).upd r ((rest ++ w.reverse) ++ [v]) := by
      rw [PS.upd_comm _ (Ne.symm hxr), PS.upd_upd]
      simp
    rw [e]
    exact hb s v w.length (rest ++ w.reverse)

/-- `φ` applied `v` times. -/
def iterP (φ : PS → PS) : Nat → PS → PS
  | 0, s => s
  | v + 1, s => iterP φ v (φ s)

/-- **Repeating a body** `v` times, counting `x` down. -/
theorem rn_iter (x : Fld) (body : NProg UK) (φ : PS → PS) (l : List Nat)
    (hb : ∀ s u, Rn body (s.upd x (l ++ [u])) ((φ s).upd x (l ++ [u]))) :
    ∀ (v : Nat) (s : PS), Rn (.loop x.idx .pos (.seq (.prim (.dec x.idx)) body)) (s.upd x (l ++ [v]))
      ((iterP φ v s).upd x (l ++ [0]))
  | 0, s => by
    refine Rn.loopF ?_
    simp
  | v + 1, s => by
    refine Rn.loopC (by simp) ((rn_dec x _ (PS.get_upd_same _ _ _)).seq ?_) (rn_iter x body φ l hb v (φ s))
    rw [PS.upd_upd, Nat.add_sub_cancel]
    exact hb s v

/-! ## Repeated pushes and additions -/

/-- Pop the top `v` of `x` and push `v` copies of `c` onto `g`. -/
def repPush (x g : Fld) (c : Nat) : NProg UK :=
  .seq (.loop x.idx .pos (.seq (.prim (.dec x.idx)) (npushC g.idx c))) (.prim (.pop x.idx))

theorem iter_push (g : Fld) (c : Nat) : ∀ (v : Nat) (s : PS),
    iterP (fun s : PS => s.upd g (s.get g ++ [c])) v s = s.upd g (s.get g ++ List.replicate v c)
  | 0, s => by simp [iterP]
  | v + 1, s => by
    rw [iterP, iter_push g c v]
    simp [List.replicate_succ]

theorem rn_repPush {x g : Fld} (hxg : x ≠ g) (c : Nat) (s : PS) {l : List Nat} {v : Nat} (hs : s.get x = l ++ [v]) :
    Rn (repPush x g c) s ((s.upd g (s.get g ++ List.replicate v c)).upd x l) := by
  have h := rn_iter x (npushC g.idx c) (fun s : PS => s.upd g (s.get g ++ [c])) l
    (fun s u => by
      refine (rn_pushC g _ c).eq ?_
      rw [PS.get_upd_ne _ hxg, PS.upd_comm _ hxg]) v s
  rw [iter_push] at h
  have e : s.upd x (l ++ [v]) = s := by rw [← hs, PS.upd_get]
  rw [e] at h
  refine h.seq ((rn_pop x _ (by rw [PS.get_upd_same])).eq ?_)
  rw [PS.upd_upd]

theorem mapTop_add : ∀ (a b : Nat) (l : List Nat), mapTop (· + b) (mapTop (· + a) l) = mapTop (· + (a + b)) l := by
  intro a b l
  rcases List.eq_nil_or_concat l with rfl | ⟨l', v, rfl⟩
  · rfl
  · rw [List.concat_eq_append, mapTop_snoc, mapTop_snoc, mapTop_snoc, Nat.add_assoc]

/-- Pop the top `v` of `x` and add it to the top of `g`. -/
def addInto (x g : Fld) : NProg UK :=
  .seq (.loop x.idx .pos (.seq (.prim (.dec x.idx)) (.prim (.inc g.idx)))) (.prim (.pop x.idx))

theorem iter_inc (g : Fld) : ∀ (v : Nat) (s : PS),
    iterP (fun s : PS => s.upd g (mapTop (· + 1) (s.get g))) v s = s.upd g (mapTop (· + v) (s.get g))
  | 0, s => by
    have : mapTop (· + 0) (s.get g) = s.get g := by
      rcases List.eq_nil_or_concat (s.get g) with h | ⟨l', w, h⟩
      · rw [h]; rfl
      · rw [h, List.concat_eq_append, mapTop_snoc]; rfl
    show s = _
    rw [this, PS.upd_get]
  | v + 1, s => by
    rw [iterP, iter_inc g v]
    simp only [PS.get_upd_same, PS.upd_upd]
    rw [mapTop_add, Nat.add_comm 1 v]

theorem rn_addInto {x g : Fld} (hxg : x ≠ g) (s : PS) {l : List Nat} {v : Nat} (hs : s.get x = l ++ [v]) :
    Rn (addInto x g) s ((s.upd g (mapTop (· + v) (s.get g))).upd x l) := by
  have h := rn_iter x (.prim (.inc g.idx)) (fun s : PS => s.upd g (mapTop (· + 1) (s.get g))) l
    (fun s u => by
      refine (rn_inc g _).eq ?_
      rw [PS.get_upd_ne _ hxg, PS.upd_comm _ hxg]) v s
  rw [iter_inc] at h
  have e : s.upd x (l ++ [v]) = s := by rw [← hs, PS.upd_get]
  rw [e] at h
  refine h.seq ((rn_pop x _ (by rw [PS.get_upd_same])).eq ?_)
  rw [PS.upd_upd]

end Shallot
