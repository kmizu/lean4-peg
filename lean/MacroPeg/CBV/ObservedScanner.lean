import MacroPeg.CBV.StatefulScannerProduct
import MacroPeg.CBV.CaptureTransitionProfile

namespace Shallot.MacroPeg.CBV.ObservedScanner
open StatefulScanner
open StatefulScannerProduct (pack left right left_pack right_pack pack_eq_iff)
abbrev Observer := RegularCaptureProduct.Machine

/-- The scanner's actual consumed word; observation never changes its stop. -/
def consumed {n : Nat} (M : Machine n) : Fin n → List Char → List Char
  | _, [] => []
  | q, c::xs => match next (M.arcs q) c with
    | none => []
    | some r => c::consumed M r xs

theorem consumed_split {n : Nat} (M : Machine n) (q : Fin n) (xs : List Char) :
    xs=consumed M q xs++(run M q xs).2 := by
  induction xs generalizing q with
  | nil => rfl
  | cons c xs ih =>
    cases h : next (M.arcs q) c with
    | none => simp [consumed,run,h]
    | some r => simpa only [consumed,run,h,List.cons_append] using congrArg (List.cons c) (ih r)

theorem consumed_pre {n : Nat} (M : Machine n) (q : Fin n) (x : List Char)
    (p : Nat) (hp : p≤x.length) :
    pre x p (run M q (sfx x p)).2.length=consumed M q (sfx x p) := by
  have he := consumed_split M q (sfx x p)
  have hj : (run M q (sfx x p)).2.length≤x.length :=
    Nat.le_trans (run_length M q _) (by rw [length_sfx x hp]; exact hp)
  have hr : sfx x (run M q (sfx x p)).2.length=(run M q (sfx x p)).2 :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨consumed M q (sfx x p),he⟩).choose_spec
  simpa only [length_sfx x hp,length_sfx x hj,hr] using pre_eq (sfx_is_suffix x p) (hr.symm ▸ he)

def step (D : Observer) (hD : D.Valid) (q : Fin D.width) (c : Char) : Fin D.width :=
  ⟨D.step q.val c,hD.2 q.val q.isLt c⟩

def arcs {n : Nat} (D : Observer) (hD : D.Valid) (q : Fin D.width)
    (A : List (Char × Fin n)) : List (Char × Fin (n*D.width)) :=
  A.map (fun (c,r) => (c,pack r (step D hD q c)))

theorem next_arcs {n : Nat} (D : Observer) (hD : D.Valid) (q : Fin D.width)
    (A : List (Char × Fin n)) (c : Char) :
    next (arcs D hD q A) c=(next A c).map (fun r => pack r (step D hD q c)) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    obtain ⟨d,r⟩ := a
    by_cases hd : Shallot.beqChar d c=true
    · have he : d=c := by
        have h : d.toNat=c.toNat := by simpa only [Shallot.beqChar,beq_iff_eq] using hd
        exact Char.toNat_inj.mp h
      subst c
      simp [arcs,next,Shallot.beqChar]
    · simpa [arcs,next,hd] using ih

def machine {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid) : Machine (n*D.width) :=
  ⟨fun q => arcs D hD (right hD.1 q) (M.arcs (left hD.1 q))⟩

theorem machine_next {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (q : Fin n) (a : Fin D.width) (c : Char) :
    next ((machine M D hD).arcs (pack q a)) c=
      (next (M.arcs q) c).map (fun r => pack r (step D hD a c)) := by
  simp only [machine,left_pack,right_pack,next_arcs]

def finish (D : Observer) (hD : D.Valid) (q : Fin D.width) (w : List Char) : Fin D.width :=
  ⟨RegularCaptureProduct.run D q.val w,RegularCaptureProduct.run_bound hD q.val q.isLt w⟩

/-- A total observer follows every consumed character, even after reaching
an absorbing failure state. Only the original scanner controls the frontier. -/
theorem run_observed {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (q : Fin n) (a : Fin D.width) (xs : List Char) :
    run (machine M D hD) (pack q a) xs=
      (pack (run M q xs).1 (finish D hD a (consumed M q xs)),(run M q xs).2) := by
  induction xs generalizing q a with
  | nil => rfl
  | cons c xs ih =>
    rw [run,machine_next]
    cases hc : next (M.arcs q) c with
    | none => simp only [Option.map_none,run,consumed,hc]; rfl
    | some r =>
      simpa only [Option.map_some,run,consumed,hc,finish,RegularCaptureProduct.run,List.foldl_cons,step]
        using ih r (step D hD a c)

/-- The observer advances through the whole actual capture, including all
starting-state behavior needed by a later replay or residual product row. -/
theorem advance_observed {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (q : Fin n) (a : Fin D.width) (w : List Char) :
    advance (machine M D hD) (pack q a) w=
      (advance M q w).map (fun r => pack r (finish D hD a w)) := by
  induction w generalizing q a with
  | nil => rfl
  | cons c w ih =>
    rw [advance,machine_next]
    cases hc : next (M.arcs q) c with
    | none => simp [hc,advance]
    | some r =>
      simpa only [hc,Option.map_some,Option.bind_some,advance,finish,RegularCaptureProduct.run,List.foldl_cons,step]
        using ih r (step D hD a c)

theorem residual_run {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (q r : Fin n) (a : Fin D.width) (w suffix : List Char)
    (h : advance M q w=some r) :
    run (machine M D hD) (pack q a) (w++suffix)=
      run (machine M D hD) (pack r (finish D hD a w)) suffix := by
  apply run_after_prefix
  rw [advance_observed,h,Option.map_some]

abbrev grammar {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid) :=
  StatefulScannerFamily.grammar (machine M D hD)

def entry {n : Nat} {D : Observer} (q target : Fin n) (a b : Fin D.width) : MExp :=
  StatefulScannerFamily.entry (pack q a) (pack target b)

theorem entry_eval {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (q target : Fin n) (a b : Fin D.width) (x : List Char) (s : Strategy)
    (E : List (List Char)) (p clock : Nat) (hp : p≤x.length) (hclock : p+1≤clock) :
    evV (grammar M D hD) x s (tblV (grammar M D hD) x s clock) E (entry q target a b) p =
      some (if (run M q (sfx x p)).1=target ∧
          RegularCaptureProduct.run D a.val (pre x p (run M q (sfx x p)).2.length)=b.val
        then some (run M q (sfx x p)).2.length else none) := by
  rw [entry,StatefulScannerFamily.entry_eval _ x s _ _ E p clock hp hclock,run_observed]
  simp only [pack_eq_iff hD.1,consumed_pre M q x p hp,finish,Fin.ext_iff]

def states (n : Nat) : List (Fin n) := List.ofFn id

def filter {n : Nat} {D : Observer} (q : Fin n) (a b : Fin D.width) : MExp :=
  RegularCaptureProduct.choice ((states n).map (fun target => entry q target a b))

theorem filter_eval {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (q : Fin n) (a b : Fin D.width) (x : List Char) (s : Strategy)
    (E : List (List Char)) (p clock : Nat) (hp : p≤x.length) (hclock : p+1≤clock) :
    evV (grammar M D hD) x s (tblV (grammar M D hD) x s clock) E (filter q a b) p =
      RegularCaptureProduct.filtered D x a.val b.val p
        (some (some (run M q (sfx x p)).2.length)) := by
  unfold filter
  rw [CaptureTransitionProfile.choice_unique (chosen := (run M q (sfx x p)).1)
    (v := RegularCaptureProduct.filtered D x a.val b.val p
      (some (some (run M q (sfx x p)).2.length)))]
  · rw [if_pos (by simp [states])]
  · intro target _
    rw [entry_eval M D hD q target a b x s E p clock hp hclock]
    by_cases ht : target=(run M q (sfx x p)).1
    · subst target
      by_cases he : RegularCaptureProduct.run D a.val (pre x p (run M q (sfx x p)).2.length)=b.val
      all_goals simp [RegularCaptureProduct.filtered,he]
    · simp [ht,Ne.symm ht]

end Shallot.MacroPeg.CBV.ObservedScanner
