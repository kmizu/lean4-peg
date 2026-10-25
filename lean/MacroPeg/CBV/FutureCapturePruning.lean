import MacroPeg.CBV.FutureCaptureViews

/-! Exact removal of bindings longer than the remaining suffix. The mask
keeps parameter indices, but discards dead payloads; static failure views
prevent an erased value from turning into an empty successful replay.
This is a bound/environment-dependent representation theorem, not a uniform
Par-to-Seq grammar transformation. -/
namespace Shallot.MacroPeg.CBV.FutureCapturePruning

def mask (bound : Nat) (W : List (List Char)) : List (List Char) :=
  W.map (fun w => if bound<w.length then [] else w)

def selectFrom (bound : Nat) : Nat → List (List Char) → List MExp
  | _,[] => []
  | off,w::ws => (if bound<w.length then MExp.failAlways else .param off)::selectFrom bound (off+1) ws

def views (bound : Nat) (W : List (List Char)) := selectFrom bound 0 W

theorem mask_length (bound : Nat) (W : List (List Char)) : (mask bound W).length=W.length := by
  simp [mask]

theorem payload_bounded (bound : Nat) (W : List (List Char)) :
    ∀ w∈mask bound W, w.length≤bound := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  by_cases hh : bound<v.length
  · simp only [if_pos hh,List.length_nil]; omega
  · simp only [if_neg hh]; omega

theorem selectFrom_lookup (bound off : Nat) : ∀ W i,
    argAt (selectFrom bound off W) i=(W[i]?).map
      (fun w => if bound<w.length then MExp.failAlways else .param (off+i))
  | [],_ => rfl
  | w::ws,0 => by simp [selectFrom,argAt]
  | w::ws,i+1 => by
    simp only [selectFrom,argAt,List.getElem?_cons_succ]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using selectFrom_lookup bound (off+1) ws i

theorem too_long_fails (x w : List Char) (bound p : Nat) (hb : bound≤x.length)
    (hp : p≤bound) (hw : bound<w.length) : Shallot.stripPrefix? w (sfx x p)=none := by
  cases h : Shallot.stripPrefix? w (sfx x p) with
  | none => rfl
  | some rest =>
    have he := congrArg List.length ((CBVtoCBN.stripPrefix_exact _ _ _).mp h)
    rw [length_sfx x (Nat.le_trans hp hb),List.length_append] at he
    omega

theorem parameter_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (bound : Nat) (hb : bound≤x.length)
    (W : List (List Char)) (i p : Nat) (hp : p≤bound) :
    evV g x s T (mask bound W) (MExp.subst (views bound W) (.param i)) p=
      evV g x s T W (.param i) p := by
  have hm : (mask bound W)[i]?=(W[i]?).map (fun w => if bound<w.length then [] else w) := by
    simp only [mask,List.getElem?_map]
  cases hw : W[i]? with
  | none => simp [MExp.subst,views,selectFrom_lookup,hw,evV,MExp.failAlways]
  | some w =>
    by_cases hh : bound<w.length
    · simp [MExp.subst,views,selectFrom_lookup,hw,hh,evV,MExp.failAlways,
        too_long_fails x w bound p hb hp hh]
    · simp only [MExp.subst,views,selectFrom_lookup,hw,Option.map_some,if_neg hh,Nat.zero_add,evV,hm]

/-- The unchanged original grammar/table can execute any first-order body
or nested argument with all oversized retained payloads discarded. -/
theorem expression (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (hs : s≠.callByName) (hT : SoundTV g x s T)
    (bound : Nat) (hb : bound≤x.length) (W : List (List Char))
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤bound) :
    evV g x s T (mask bound W) (MExp.subst (views bound W) e) p=
      evV g x s T W e p :=
  FutureCaptureViews.evV_rebind hs hT hb _ _ (parameter_view g x s T bound hb W) e he p hp

theorem physical (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (k bound : Nat) (hb : bound≤x.length) (W : List (List Char))
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤bound) :
    evV g x s (tblV g x s k) (mask bound W) (MExp.subst (views bound W) e) p=
      evV g x s (tblV g x s k) W e p :=
  expression g x s _ hs (tblV_sound hg hs k) bound hb W e he p hp

/-- If every retained word is now too long, no retained environment is
needed at all, even by arbitrary parameterized recursive continuations. -/
theorem forget_all (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (hs : s≠.callByName) (hT : SoundTV g x s T)
    (bound : Nat) (hb : bound≤x.length) (W : List (List Char))
    (hW : ∀ w∈W, bound<w.length) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤bound) :
    evV g x s T [] e p=evV g x s T W e p := by
  have hparam (i q : Nat) (hq : q≤bound) : evV g x s T [] (MExp.subst [] (.param i)) q=
      evV g x s T W (.param i) q := by
    cases hw : W[i]? with
    | none => simp [MExp.subst,argAt,MExp.failAlways,evV,hw]
    | some w => simp [MExp.subst,argAt,MExp.failAlways,evV,hw,
        too_long_fails x w bound q hb hq (hW w (List.mem_of_getElem? hw))]
  have h := FutureCaptureViews.evV_rebind hs hT hb [] W hparam e he p hp
  have hsubst : evV g x s T [] (MExp.subst [] e) p=evV g x s T [] e p :=
    evV_subst [] e he p
  exact hsubst.symm.trans h

/-- An exact, local criterion, stronger than the inexpensive length test. -/
def DeadAfter (x : List Char) (bound : Nat) (W : List (List Char)) : Prop :=
  ∀ w∈W, ∀ p, p≤bound → Shallot.stripPrefix? w (sfx x p)=none

def deadCheck (x : List Char) (bound : Nat) (W : List (List Char)) : Bool :=
  W.all (fun w => (List.range (bound+1)).all (fun p => (Shallot.stripPrefix? w (sfx x p)).isNone))

theorem deadCheck_iff (x : List Char) (bound : Nat) (W : List (List Char)) :
    deadCheck x bound W=true ↔ DeadAfter x bound W := by
  constructor
  · intro h w hw p hp
    have h := List.all_eq_true.mp (List.all_eq_true.mp h w hw) p (List.mem_range.mpr (by omega))
    exact Option.isNone_iff_eq_none.mp h
  · intro h
    apply List.all_eq_true.mpr
    intro w hw
    apply List.all_eq_true.mpr
    intro p hp
    simp only [h w hw p (by have := List.mem_range.mp hp; omega),Option.isNone_none]

theorem forget_dead (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (hs : s≠.callByName) (hT : SoundTV g x s T)
    (bound : Nat) (hb : bound≤x.length) (W : List (List Char)) (hW : DeadAfter x bound W)
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤bound) :
    evV g x s T [] e p=evV g x s T W e p := by
  have hparam (i q : Nat) (hq : q≤bound) : evV g x s T [] (MExp.subst [] (.param i)) q=
      evV g x s T W (.param i) q := by
    cases hw : W[i]? with
    | none => simp [MExp.subst,argAt,MExp.failAlways,evV,hw]
    | some w => simp [MExp.subst,argAt,MExp.failAlways,evV,hw,hW w (List.mem_of_getElem? hw) q hq]
  have h := FutureCaptureViews.evV_rebind hs hT hb [] W hparam e he p hp
  have hsubst : evV g x s T [] (MExp.subst [] e) p=evV g x s T [] e p := evV_subst [] e he p
  exact hsubst.symm.trans h

/-- Forgetting all values preserves every first-order continuation at every
future position exactly when none of those values can replay there. -/
theorem forget_iff (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (hs : s≠.callByName) (hT : SoundTV g x s T)
    (bound : Nat) (hb : bound≤x.length) (W : List (List Char)) :
    (∀ e : MExp, e.FirstOrder → ∀ p, p≤bound → evV g x s T [] e p=evV g x s T W e p) ↔
      DeadAfter x bound W := by
  constructor
  · intro h w hw p hp
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hw
    have hlookup : W[i]?=some w := by rw [List.getElem?_eq_getElem hi,he]
    have h := h (.param i) True.intro p hp
    simp only [evV,List.getElem?_nil,hlookup] at h
    cases ht : Shallot.stripPrefix? w (sfx x p) with
    | none => rfl
    | some rest => simp [ht] at h
  · intro h e he p hp
    exact forget_dead g x s T hs hT bound hb W h e he p hp

/-- A prefix may advance past the point at which old captures matter.
No replay or anchor shape is required of this prefix or its continuation. -/
theorem after_prefix (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (hs : s≠.callByName) (hT : SoundTV g x s T)
    (W : List (List Char)) (prefixBody tail : MExp) (hprefix : prefixBody.FirstOrder) (htail : tail.FirstOrder)
    (p q : Nat) (hp : p≤x.length) (hv : evV g x s T W prefixBody p=some (some q)) :
    evV g x s T W (.seq prefixBody tail) p=
      evV g x s T (mask q W) (MExp.subst (views q W) tail) q := by
  rw [evV_seq_ok hv]
  exact (expression g x s T hs hT q (Nat.le_trans (FutureCaptureViews.success_le hs hT W prefixBody hprefix p q hp hv) hp)
    W tail htail q (Nat.le_refl _)).symm

end Shallot.MacroPeg.CBV.FutureCapturePruning
