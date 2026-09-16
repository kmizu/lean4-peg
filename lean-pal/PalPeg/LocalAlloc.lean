import PalPeg.LocalTick2

/-!
# 局所化計画, piece 8: slot **allocation** — closing the `RolesInjective` gap of §9

`LocalTick2` §9 lists, among what it could not discharge:

> Tape *reuse*: a commit abandons the tapes its repointed roles used to own, and
> nothing here shows the bank of `P` tapes suffices.  `RolesInjective` is
> assumed of the pre-state and is **not** re-established for the post-state;
> freshness of `jL`/`jW`/`jD`/`jR`/`jF` is assumed, not allocated.

This file closes exactly that gap, and nothing else.

The idea is the textbook one: pair the state with an explicit **free pool** of
physical slots, and make every commit *trade* — it takes the slots it repoints
out of the pool and releases into the pool the slots its roles used to own.
Since a commit repoints `k` roles and abandons `k` slots, `free.length` is an
**invariant**, so a pool that starts with `S` slots always has `S` slots.
Freshness is then not a hypothesis but a consequence (`alloc_fresh`): a slot in
the pool is owned by no role, because that is the pool invariant.

* `Alloc P` = a `GalilVML P` together with `free : List (Fin P)`;
* `AllocInv` = `RolesInjective` ∧ roles avoid the pool ∧ the pool is duplicate-free;
* `take` = the single allocation primitive (`setRole` + pool trade), and
  `allocInv_take` / `free_length_take` are its two laws;
* the four commits of `LocalTick2` are each a `mapState` (the tape/control part,
  which never touches `roles`) followed by `k` `take`s, with

  | commit | `k` |
  |---|---|
  | `commitRestart` | `3` (`.lower`, `.work`, `.debt`) |
  | `commitReplay`  | `0` (`moveRoles` is a *permutation*: it reuses the dead replay tape) |
  | `commitShift`   | `1` (`.remaining`) |
  | `commitFallback`| `1` (`.fppWork`) |

  so `S := 3` spare slots suffice, and `P := Fintype.card Ctr + 3 = 13`.

The "mirror slots are disjoint" clause of the plan is **not** a field of the
invariant here: in `GalilVML` a mirror bank carries tape *values*
(`LocalMirror.Mirrored`), pinned by `MirrorsAttached` to the slot its own role
owns, so the mirrored slots are `roles .radius`, `roles .lower`, `roles .length`
and their pairwise disjointness — and their disjointness from the pool — is a
*theorem* (`mirrorSlots_nodup`, `mirrorSlots_disjoint_free`), not an assumption.

What is still **not** here: the staging content conditions
(`RestartStaged.lowerSrc`/`.workSlot`/`.debtSlot`, `hstaged`, `hslot`) say
*which value* a fresh slot must already carry; allocation only says the slot is
unowned.  Those remain obligations on the chain's and the mirrors' own layers.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalAlloc

open PalPeg.LocalState
open PalPeg.LocalTick2

variable {P : ℕ}

/-! ## 1. The pool and its invariant -/

/-- The allocation-relevant part of the invariant, stated on the role
assignment alone: distinct roles on distinct slots, roles never on a free slot,
no slot free twice. -/
def RolesFree (roles : Ctr → Fin P) (free : List (Fin P)) : Prop :=
  Function.Injective roles ∧ (∀ c, roles c ∉ free) ∧ free.Nodup

/-- The state of the counter bank together with its pool of unowned slots. -/
structure Alloc (P : ℕ) where
  /-- The localized Galil state. -/
  x : GalilVML P
  /-- The physical slots owned by no logical counter. -/
  free : List (Fin P)

/-- The allocator's invariant. -/
def AllocInv (a : Alloc P) : Prop := RolesFree a.x.roles a.free

theorem AllocInv.inj {a : Alloc P} (h : AllocInv a) : RolesInjective a.x := h.1

theorem AllocInv.disj {a : Alloc P} (h : AllocInv a) (c : Ctr) : a.x.roles c ∉ a.free := h.2.1 c

theorem AllocInv.nodup {a : Alloc P} (h : AllocInv a) : a.free.Nodup := h.2.2

/-- **Freshness is a consequence, not a hypothesis.**  A slot in the pool is
owned by no logical counter. -/
theorem alloc_fresh {a : Alloc P} (h : AllocInv a) {j : Fin P} (hj : j ∈ a.free) (c : Ctr) :
    a.x.roles c ≠ j := fun he => h.disj c (he ▸ hj)

/-- The symmetric form, in the shape the `LocalTick2` freshness hypotheses want
(`RestartStaged.freshL` etc.). -/
theorem fresh_ne {a : Alloc P} (h : AllocInv a) {j : Fin P} (hj : j ∈ a.free) (c : Ctr) :
    j ≠ a.x.roles c := (alloc_fresh h hj c).symm

/-! ### The mirrored slots -/

/-- The three slots carrying a mirror bank: those of `radius`, `lower` and
`length` (cf. `MirrorsAttached`). -/
def mirrorSlots (a : Alloc P) : List (Fin P) :=
  [a.x.roles .radius, a.x.roles .lower, a.x.roles .length]

theorem mirrorSlots_nodup {a : Alloc P} (h : AllocInv a) : (mirrorSlots a).Nodup := by
  have hinj := h.inj
  have h1 : a.x.roles Ctr.radius ≠ a.x.roles Ctr.lower := fun hh => absurd (hinj hh) (by decide)
  have h2 : a.x.roles Ctr.radius ≠ a.x.roles Ctr.length := fun hh => absurd (hinj hh) (by decide)
  have h3 : a.x.roles Ctr.lower ≠ a.x.roles Ctr.length := fun hh => absurd (hinj hh) (by decide)
  simp [mirrorSlots, h1, h2, h3]

theorem mirrorSlots_disjoint_free {a : Alloc P} (h : AllocInv a) {j : Fin P} (hj : j ∈ a.free) :
    j ∉ mirrorSlots a := by
  have h1 : j ≠ a.x.roles Ctr.radius := fresh_ne h hj _
  have h2 : j ≠ a.x.roles Ctr.lower := fresh_ne h hj _
  have h3 : j ≠ a.x.roles Ctr.length := fresh_ne h hj _
  simp [mirrorSlots, h1, h2, h3]

/-! ## 2. `setRole` re-establishes `RolesInjective` on a fresh slot -/

/-- The gap of §9, in its raw form: repointing one role at a slot owned by no
role preserves injectivity. -/
theorem rolesInjective_setRole {x : GalilVML P} (hinj : RolesInjective x) (c : Ctr) {j : Fin P}
    (hj : ∀ d, x.roles d ≠ j) (b : Bool) : RolesInjective (setRole c j b x) := by
  intro d e hde
  have hde' : Function.update x.roles c j d = Function.update x.roles c j e := hde
  by_cases hd : d = c <;> by_cases he : e = c
  · rw [hd, he]
  · rw [hd, Function.update_self, Function.update_of_ne he] at hde'
    exact absurd hde'.symm (hj e)
  · rw [he, Function.update_self, Function.update_of_ne hd] at hde'
    exact absurd hde' (hj d)
  · rw [Function.update_of_ne hd, Function.update_of_ne he] at hde'
    exact hinj hde'

/-! ## 3. The allocation primitive -/

/-- **Take** slot `j` out of the pool for role `c`, **releasing** the slot `c`
used to own.  Exactly `setRole` on the state, plus the pool trade. -/
def take (c : Ctr) (j : Fin P) (b : Bool) (a : Alloc P) : Alloc P :=
  { x := setRole c j b a.x, free := a.x.roles c :: a.free.erase j }

@[simp] theorem take_x (c : Ctr) (j : Fin P) (b : Bool) (a : Alloc P) :
    (take c j b a).x = setRole c j b a.x := rfl

@[simp] theorem take_free (c : Ctr) (j : Fin P) (b : Bool) (a : Alloc P) :
    (take c j b a).free = a.x.roles c :: a.free.erase j := rfl

/-- **Law 1**: taking a slot out of the pool preserves the invariant. -/
theorem allocInv_take {a : Alloc P} {c : Ctr} {j : Fin P} {b : Bool}
    (h : AllocInv a) (hj : j ∈ a.free) : AllocInv (take c j b a) := by
  have hfresh : ∀ d, a.x.roles d ≠ j := fun d => alloc_fresh h hj d
  refine ⟨rolesInjective_setRole h.inj c hfresh b, ?_, ?_⟩
  · intro d
    have hval : (take c j b a).x.roles d = Function.update a.x.roles c j d := rfl
    rw [hval]
    by_cases hd : d = c
    · subst hd
      rw [Function.update_self]
      simp only [take_free, List.mem_cons, not_or]
      refine ⟨fun hh => hfresh d hh.symm, fun hh => ?_⟩
      exact h.nodup.not_mem_erase hh
    · rw [Function.update_of_ne hd]
      simp only [take_free, List.mem_cons, not_or]
      exact ⟨fun hh => hd (h.inj hh), fun hh => h.disj d (List.erase_subset hh)⟩
  · refine List.nodup_cons.mpr ⟨fun hh => h.disj c (List.erase_subset hh), h.nodup.erase j⟩

/-- **Law 2**: the pool's size is unchanged — `k` slots in, `k` slots out. -/
theorem free_length_take {a : Alloc P} (c : Ctr) {j : Fin P} (b : Bool) (hj : j ∈ a.free) :
    (take c j b a).free.length = a.free.length := by
  have hpos : 0 < a.free.length := List.length_pos_of_mem hj
  simp only [take_free, List.length_cons, List.length_erase_of_mem hj]
  omega

/-- Chaining: a *different* free slot is still free after a `take`. -/
theorem mem_free_take {a : Alloc P} (c : Ctr) {j j' : Fin P} (b : Bool)
    (hne : j' ≠ j) (hj' : j' ∈ a.free) : j' ∈ (take c j b a).free :=
  List.mem_cons_of_mem _ ((List.mem_erase_of_ne hne).mpr hj')

/-! ## 4. The tape/control part of a commit is allocation-neutral -/

/-- Apply a state transformation that does not touch `roles`. -/
def mapState (f : GalilVML P → GalilVML P) (a : Alloc P) : Alloc P := ⟨f a.x, a.free⟩

@[simp] theorem mapState_free (f : GalilVML P → GalilVML P) (a : Alloc P) :
    (mapState f a).free = a.free := rfl

theorem allocInv_mapState {a : Alloc P} {f : GalilVML P → GalilVML P}
    (h : AllocInv a) (hf : (f a.x).roles = a.x.roles) : AllocInv (mapState f a) := by
  refine ⟨?_, ?_, h.nodup⟩
  · show Function.Injective (f a.x).roles
    rw [hf]; exact h.inj
  · intro c
    show (f a.x).roles c ∉ a.free
    rw [hf]; exact h.disj c

/-! ## 5. `commitRestart`: `k = 3` -/

/-- The tape/control part of `commitRestart` (verbatim from `LocalTick2`). -/
def restartBase (entry : ℕ) (x : GalilVML P) : GalilVML P :=
  { x with phys := resetSlots [x.roles .span] x.phys
           chain := .idle
           searchMode := .grow
           searchFinalStage := false
           searchQuarter := 0
           dpBuf := LocalBuffers.resetL x.dpBuf
           dpPc := entry
           dpDone := true }

@[simp] theorem restartBase_roles (entry : ℕ) (x : GalilVML P) :
    (restartBase entry x).roles = x.roles := rfl

/-- `commitRestart` as an allocator action: three slots taken, three released. -/
def allocRestart (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (a : Alloc P) : Alloc P :=
  take .debt jD (!a.x.pol .radius)
    (take .work jW bL (take .lower jL bL (mapState (restartBase entry) a)))

theorem allocRestart_x (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (a : Alloc P) :
    (allocRestart entry jL jW jD bL a).x = commitRestart entry jL jW jD bL a.x := rfl

theorem allocInv_commitRestart {a : Alloc P} {jL jW jD : Fin P} {bL : Bool} {entry : ℕ}
    (h : AllocInv a) (hL : jL ∈ a.free) (hW : jW ∈ a.free) (hD : jD ∈ a.free)
    (hWL : jW ≠ jL) (hDL : jD ≠ jL) (hDW : jD ≠ jW) :
    AllocInv (allocRestart entry jL jW jD bL a) ∧
      (allocRestart entry jL jW jD bL a).free.length = a.free.length := by
  have h0 : AllocInv (mapState (restartBase entry) a) :=
    allocInv_mapState h (restartBase_roles entry a.x)
  have hL0 : jL ∈ (mapState (restartBase entry) a).free := hL
  have hW0 : jW ∈ (mapState (restartBase entry) a).free := hW
  have hD0 : jD ∈ (mapState (restartBase entry) a).free := hD
  have h1 := allocInv_take (c := Ctr.lower) (b := bL) h0 hL0
  have hW1 := mem_free_take Ctr.lower bL hWL hW0
  have hD1 := mem_free_take Ctr.lower bL hDL hD0
  have h2 := allocInv_take (c := Ctr.work) (b := bL) h1 hW1
  have hD2 := mem_free_take Ctr.work bL hDW hD1
  have h3 := allocInv_take (c := Ctr.debt) (b := !a.x.pol .radius) h2 hD2
  refine ⟨h3, ?_⟩
  show (take Ctr.debt jD (!a.x.pol Ctr.radius)
    (take Ctr.work jW bL (take Ctr.lower jL bL (mapState (restartBase entry) a)))).free.length
      = a.free.length
  rw [free_length_take Ctr.debt (!a.x.pol .radius) hD2,
    free_length_take Ctr.work bL hW1, free_length_take Ctr.lower bL hL0]
  rfl

/-- The §9 obligation itself, for the restart commit. -/
theorem rolesInjective_commitRestart {a : Alloc P} {jL jW jD : Fin P} {bL : Bool} {entry : ℕ}
    (h : AllocInv a) (hL : jL ∈ a.free) (hW : jW ∈ a.free) (hD : jD ∈ a.free)
    (hWL : jW ≠ jL) (hDL : jD ≠ jL) (hDW : jD ≠ jW) :
    RolesInjective (commitRestart entry jL jW jD bL a.x) :=
  (allocInv_commitRestart h hL hW hD hWL hDL hDW).1.inj

/-- The three `RestartStaged` freshness fields, discharged by allocation. -/
theorem restart_fresh {a : Alloc P} {jL jW jD : Fin P}
    (h : AllocInv a) (hL : jL ∈ a.free) (hW : jW ∈ a.free) (hD : jD ∈ a.free) :
    jL ≠ a.x.roles .span ∧ jW ≠ a.x.roles .span ∧ jD ≠ a.x.roles .span :=
  ⟨fresh_ne h hL .span, fresh_ne h hW .span, fresh_ne h hD .span⟩

/-! ## 6. `commitReplay`: `k = 0` (a permutation, not an allocation) -/

/-- `commitReplay` as an allocator action: the pool is untouched, because the
role move is a transposition — `replay` inherits the radius tape and the dead
replay tape becomes the new `radius`. -/
def allocReplay (entry : ℕ) (a : Alloc P) : Alloc P := ⟨commitReplay entry a.x, a.free⟩

theorem allocReplay_x (entry : ℕ) (a : Alloc P) :
    (allocReplay entry a).x = commitReplay entry a.x := rfl

theorem allocInv_commitReplay {a : Alloc P} {entry : ℕ} (h : AllocInv a) :
    AllocInv (allocReplay entry a) ∧ (allocReplay entry a).free.length = a.free.length := by
  refine ⟨⟨?_, ?_, h.nodup⟩, rfl⟩
  · show Function.Injective (LocalRoles.moveRoles Ctr.radius Ctr.replay a.x.roles)
    exact h.inj.comp (LocalRoles.swapAt_injective _ _)
  · intro c
    show a.x.roles (LocalRoles.swapAt Ctr.radius Ctr.replay c) ∉ a.free
    exact h.disj _

theorem rolesInjective_commitReplay {a : Alloc P} {entry : ℕ} (h : AllocInv a) :
    RolesInjective (commitReplay entry a.x) := (allocInv_commitReplay (entry := entry) h).1.inj

/-! ## 7. `commitShift`: `k = 1` -/

/-- The tape/control part of `commitShift` (verbatim from `LocalTick2`). -/
def shiftBase (w : GalilScaffoldChainWatch.State) (x : GalilVML P) : GalilVML P :=
  { x with phys := pushSlots [x.roles Ctr.length]
             (pushSlots [x.roles Ctr.length] (resetSlots [x.roles Ctr.cycle] x.phys))
           chain := .watch (GalilScaffoldChainWatch.immediate w)
           periodOnly := true }

@[simp] theorem shiftBase_roles (w : GalilScaffoldChainWatch.State) (x : GalilVML P) :
    (shiftBase w x).roles = x.roles := rfl

/-- `commitShift` as an allocator action: one slot taken, one released. -/
def allocShift (jR : Fin P) (bR : Bool) (w : GalilScaffoldChainWatch.State) (a : Alloc P) :
    Alloc P :=
  take Ctr.remaining jR bR (mapState (shiftBase w) a)

theorem allocShift_x (jR : Fin P) (bR : Bool) (w : GalilScaffoldChainWatch.State) (a : Alloc P) :
    (allocShift jR bR w a).x = commitShift jR bR w a.x := rfl

theorem allocInv_commitShift {a : Alloc P} {jR : Fin P} {bR : Bool}
    {w : GalilScaffoldChainWatch.State} (h : AllocInv a) (hR : jR ∈ a.free) :
    AllocInv (allocShift jR bR w a) ∧ (allocShift jR bR w a).free.length = a.free.length := by
  have h0 : AllocInv (mapState (shiftBase w) a) := allocInv_mapState h (shiftBase_roles w a.x)
  have hR0 : jR ∈ (mapState (shiftBase w) a).free := hR
  exact ⟨allocInv_take (c := Ctr.remaining) (b := bR) h0 hR0,
    free_length_take Ctr.remaining bR hR0⟩

theorem rolesInjective_commitShift {a : Alloc P} {jR : Fin P} {bR : Bool}
    {w : GalilScaffoldChainWatch.State} (h : AllocInv a) (hR : jR ∈ a.free) :
    RolesInjective (commitShift jR bR w a.x) := (allocInv_commitShift h hR).1.inj

/-! ## 8. `commitFallback`: `k = 1` -/

/-- The tape/control part of `commitFallback` (verbatim from `LocalTick2`). -/
def fallbackBase (jF : Fin P) (x : GalilVML P) : GalilVML P :=
  { x with phys := pushSlots [jF] x.phys
           fppBuf := LocalBuffers.stepL (fun ts i => fppWriteAt i (ts i))
                       (LocalBuffers.resetL x.fppBuf)
           fppPc := 320
           fppDone := true
           fppMode := .copy
           fppFinalStage := false }

@[simp] theorem fallbackBase_roles (jF : Fin P) (x : GalilVML P) :
    (fallbackBase jF x).roles = x.roles := rfl

/-- `commitFallback` as an allocator action: one slot taken, one released. -/
def allocFallback (jF : Fin P) (bF : Bool) (a : Alloc P) : Alloc P :=
  take Ctr.fppWork jF bF (mapState (fallbackBase jF) a)

theorem allocFallback_x (jF : Fin P) (bF : Bool) (a : Alloc P) :
    (allocFallback jF bF a).x = commitFallback jF bF a.x := rfl

theorem allocInv_commitFallback {a : Alloc P} {jF : Fin P} {bF : Bool}
    (h : AllocInv a) (hF : jF ∈ a.free) :
    AllocInv (allocFallback jF bF a) ∧ (allocFallback jF bF a).free.length = a.free.length := by
  have h0 : AllocInv (mapState (fallbackBase jF) a) :=
    allocInv_mapState h (fallbackBase_roles jF a.x)
  have hF0 : jF ∈ (mapState (fallbackBase jF) a).free := hF
  exact ⟨allocInv_take (c := Ctr.fppWork) (b := bF) h0 hF0,
    free_length_take Ctr.fppWork bF hF0⟩

theorem rolesInjective_commitFallback {a : Alloc P} {jF : Fin P} {bF : Bool}
    (h : AllocInv a) (hF : jF ∈ a.free) :
    RolesInjective (commitFallback jF bF a.x) := (allocInv_commitFallback h hF).1.inj

/-! ## 9. How many spare slots: `S = 3` -/

/-- Enough free slots are available for every commit. -/
def Ready (a : Alloc P) : Prop := 3 ≤ a.free.length

/-- The three fresh slots a restart needs. -/
theorem exists_three_fresh {a : Alloc P} (h : AllocInv a) (hr : Ready a) :
    ∃ jL jW jD : Fin P, jL ∈ a.free ∧ jW ∈ a.free ∧ jD ∈ a.free ∧
      jW ≠ jL ∧ jD ≠ jL ∧ jD ≠ jW := by
  have hn := h.nodup
  have hr' : 3 ≤ a.free.length := hr
  match hf : a.free with
  | [] => rw [hf] at hr'; simp at hr'
  | [_] => rw [hf] at hr'; simp at hr'
  | [_, _] => rw [hf] at hr'; simp at hr'
  | j1 :: j2 :: j3 :: t =>
    rw [hf] at hn
    simp only [List.nodup_cons, List.mem_cons] at hn
    refine ⟨j1, j2, j3, by simp, by simp, by simp, ?_, ?_, ?_⟩
    · exact fun hh => hn.1 (Or.inl hh.symm)
    · exact fun hh => hn.1 (Or.inr (Or.inl hh.symm))
    · exact fun hh => hn.2.1 (Or.inl hh.symm)

/-- The one fresh slot a shift or a fallback needs. -/
theorem exists_fresh {a : Alloc P} (hr : Ready a) : ∃ j : Fin P, j ∈ a.free := by
  have hr' : 3 ≤ a.free.length := hr
  match hf : a.free with
  | [] => rw [hf] at hr'; simp at hr'
  | j :: t => exact ⟨j, by simp⟩

/-- `Ready` is preserved by every commit, because each one is size-neutral. -/
theorem ready_of_length_eq {a b : Alloc P} (hr : Ready a) (hlen : b.free.length = a.free.length) :
    Ready b := by
  unfold Ready at *; omega

theorem ready_commitRestart {a : Alloc P} {jL jW jD : Fin P} {bL : Bool} {entry : ℕ}
    (h : AllocInv a) (hr : Ready a) (hL : jL ∈ a.free) (hW : jW ∈ a.free) (hD : jD ∈ a.free)
    (hWL : jW ≠ jL) (hDL : jD ≠ jL) (hDW : jD ≠ jW) :
    Ready (allocRestart entry jL jW jD bL a) :=
  ready_of_length_eq hr (allocInv_commitRestart h hL hW hD hWL hDL hDW).2

theorem ready_commitReplay {a : Alloc P} {entry : ℕ} (hr : Ready a) :
    Ready (allocReplay entry a) := hr

theorem ready_commitShift {a : Alloc P} {jR : Fin P} {bR : Bool}
    {w : GalilScaffoldChainWatch.State} (h : AllocInv a) (hr : Ready a) (hR : jR ∈ a.free) :
    Ready (allocShift jR bR w a) := ready_of_length_eq hr (allocInv_commitShift h hR).2

theorem ready_commitFallback {a : Alloc P} {jF : Fin P} {bF : Bool}
    (h : AllocInv a) (hr : Ready a) (hF : jF ∈ a.free) :
    Ready (allocFallback jF bF a) := ready_of_length_eq hr (allocInv_commitFallback h hF).2

/-! ### The concrete bank -/

/-- `S`: the number of spare slots.  `3` = the largest `k` over the four
commits, attained by `commitRestart`. -/
def nSpare : ℕ := 3

/-- `P`: one slot per logical counter plus the spares. -/
def nSlots : ℕ := 13

theorem card_Ctr : Fintype.card Ctr = 10 := by decide

/-- `P = Fintype.card Ctr + S`. -/
theorem nSlots_eq : nSlots = Fintype.card Ctr + nSpare := by decide

/-- Index of a logical counter in the bank. -/
def ctrIndex : Ctr → Fin 10
  | .cycle => 0 | .remaining => 1 | .radius => 2 | .length => 3 | .replay => 4
  | .lower => 5 | .span => 6 | .work => 7 | .debt => 8 | .fppWork => 9

/-- The initial role assignment: counter `c` owns slot `ctrIndex c`. -/
def initRoles : Ctr → Fin nSlots := fun c => (ctrIndex c).castLE (by decide)

/-- The initial pool: the `nSpare` slots above the counters. -/
def initFree : List (Fin nSlots) := [⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩]

theorem initFree_length : initFree.length = nSpare := by decide

/-- The bank starts out well-allocated. -/
theorem rolesFree_init : RolesFree initRoles initFree := by
  refine ⟨?_, ?_, ?_⟩
  · intro c d hcd
    revert hcd; revert c d; decide
  · decide
  · decide

/-- **`S = 3` suffices**: a bank of `Fintype.card Ctr + 3 = 13` tapes, started
with the three spares in the pool, satisfies the allocator invariant and is
`Ready`; and `Ready` together with `AllocInv` is preserved by all four commits
(`ready_commitRestart`/`_Replay`/`_Shift`/`_Fallback` above), so every commit
always finds the pairwise-distinct fresh slots it repoints. -/
theorem spare_bound (x : GalilVML nSlots) (hx : x.roles = initRoles) :
    AllocInv (⟨x, initFree⟩ : Alloc nSlots) ∧ Ready (⟨x, initFree⟩ : Alloc nSlots) := by
  refine ⟨?_, ?_⟩
  · show RolesFree x.roles initFree
    rw [hx]; exact rolesFree_init
  · show 3 ≤ initFree.length
    decide

end PalPeg.LocalAlloc

#print axioms PalPeg.LocalAlloc.alloc_fresh
#print axioms PalPeg.LocalAlloc.rolesInjective_setRole
#print axioms PalPeg.LocalAlloc.allocInv_take
#print axioms PalPeg.LocalAlloc.free_length_take
#print axioms PalPeg.LocalAlloc.mirrorSlots_nodup
#print axioms PalPeg.LocalAlloc.mirrorSlots_disjoint_free
#print axioms PalPeg.LocalAlloc.allocRestart_x
#print axioms PalPeg.LocalAlloc.allocInv_commitRestart
#print axioms PalPeg.LocalAlloc.rolesInjective_commitRestart
#print axioms PalPeg.LocalAlloc.restart_fresh
#print axioms PalPeg.LocalAlloc.allocInv_commitReplay
#print axioms PalPeg.LocalAlloc.rolesInjective_commitReplay
#print axioms PalPeg.LocalAlloc.allocInv_commitShift
#print axioms PalPeg.LocalAlloc.rolesInjective_commitShift
#print axioms PalPeg.LocalAlloc.allocInv_commitFallback
#print axioms PalPeg.LocalAlloc.rolesInjective_commitFallback
#print axioms PalPeg.LocalAlloc.exists_three_fresh
#print axioms PalPeg.LocalAlloc.rolesFree_init
#print axioms PalPeg.LocalAlloc.spare_bound
