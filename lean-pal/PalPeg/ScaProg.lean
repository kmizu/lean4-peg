import PalPeg.ScaLocal

/-!
# Stack programs

A small language of persistent-stack operations, mirroring the Scala circuit's `push` / `drop` /
`copyFrom` / `clear` and `select` on finite values. Every program is a local update, with depth
and width computed from its structure, so one input letter's program compiles into one scaffold
node.
-/
set_option autoImplicit false
namespace PalPeg.ScaProg
open PalPeg.ScaLocal

variable {Γ C : Type} {K : ℕ}

/-- Stack programs. Tests and pushed values read the control and the top `peek` elements. -/
inductive Prog (Γ C : Type) (K : ℕ) where
  | skip
  | ctl (g : C → (Fin K → List Γ) → C)
  | push (k : Fin K) (x : C → (Fin K → List Γ) → Γ)
  | pop (k : Fin K)
  | copy (src dst : Fin K)
  | clear (k : Fin K)
  | seq (p q : Prog Γ C K)
  | ite (b : C → (Fin K → List Γ) → Bool) (p q : Prog Γ C K)

/-- How deep a program reads. `peek` bounds how far tests and pushed values look. -/
def Prog.depth (peek : ℕ) : Prog Γ C K → ℕ
  | .skip => 0
  | .ctl _ => peek
  | .push _ _ => peek
  | .pop _ => max peek 1
  | .copy _ _ => 0
  | .clear _ => 0
  | .seq p q => p.depth peek + q.depth peek
  | .ite _ p q => max peek (max (p.depth peek) (q.depth peek))

/-- How many elements a program pushes onto one stack at most. -/
def Prog.width : Prog Γ C K → ℕ
  | .skip => 0
  | .ctl _ => 0
  | .push _ _ => 1
  | .pop _ => 1
  | .copy _ _ => 1
  | .clear _ => 1
  | .seq p q => p.width + q.width
  | .ite _ p q => max p.width q.width

/-- What a program does. Tests and values see the top `peek` elements only. -/
def Prog.eval (peek : ℕ) : Prog Γ C K → C → (Fin K → List Γ) → C × (Fin K → List Γ)
  | .skip, c, st => (c, st)
  | .ctl g, c, st => (g c (view peek st), st)
  | .push k x, c, st => (c, Function.update st k (x c (view peek st) :: st k))
  | .pop k, c, st => (c, Function.update st k (st k).tail)
  | .copy src dst, c, st => (c, Function.update st dst (st src))
  | .clear k, c, st => (c, Function.update st k [])
  | .seq p q, c, st => q.eval peek (p.eval peek c st).1 (p.eval peek c st).2
  | .ite b p q, c, st => if b c (view peek st) then p.eval peek c st else q.eval peek c st

/-- One stack operation as a local rule. -/
theorem op_isLocal (D : ℕ) (k : Fin K) (r : C → (Fin K → List Γ) → Rewrite Γ K)
    (hpre : ∀ c v, (r c v).pre.length ≤ 1) (hdrop : ∀ c v, (r c v).drop ≤ D)
    (Φ : C → (Fin K → List Γ) → C × (Fin K → List Γ))
    (hΦ : ∀ c st, Φ c st = (c, Function.update st k (apply st (r c (view D st))))) :
    IsLocal D 1 Φ :=
  ⟨Rule.op D (fun c _ => c) k r hpre hdrop, fun c st =>
    (hΦ c st).trans (Rule.run_op D (fun c _ => c) k r hpre hdrop c st).symm⟩

/-- **Every stack program is local.** -/
theorem Prog.isLocal (peek : ℕ) :
    ∀ p : Prog Γ C K, IsLocal (p.depth peek) p.width (p.eval peek)
  | .skip => ⟨Rule.control (fun c _ => c) 0, fun c st =>
      (Rule.run_control (fun c _ => c) 0 c st).symm⟩
  | .ctl g => ⟨Rule.control g peek, fun c st => (Rule.run_control g peek c st).symm⟩
  | .push k x => op_isLocal peek k (fun c v => pushRw (x c v) k) (fun _ _ => le_of_eq rfl)
      (fun _ _ => Nat.zero_le _) _ (fun c st => by rw [apply_push]; rfl)
  | .pop k => op_isLocal (max peek 1) k (fun _ _ => popRw k) (fun _ _ => Nat.zero_le _)
      (fun _ _ => le_max_right _ _) _ (fun c st => by rw [apply_pop]; rfl)
  | .copy src dst => op_isLocal 0 dst (fun _ _ => copyRw src) (fun _ _ => Nat.zero_le _)
      (fun _ _ => le_rfl) _ (fun c st => by rw [apply_copy]; rfl)
  | .clear k => op_isLocal 0 k (fun _ _ => clearRw) (fun _ _ => Nat.zero_le _)
      (fun _ _ => le_rfl) _ (fun c st => by rw [apply_clear]; rfl)
  | .seq p q => (Prog.isLocal peek p).comp (Prog.isLocal peek q)
  | .ite b p q => by
    show IsLocal (max peek (max (p.depth peek) (q.depth peek))) (max p.width q.width)
      (Prog.eval peek (.ite b p q))
    have hp := (Prog.isLocal peek p).mono
      ((le_max_left (p.depth peek) (q.depth peek)).trans (le_max_right peek _))
      (le_max_left p.width q.width)
    have hq := (Prog.isLocal peek q).mono
      ((le_max_right (p.depth peek) (q.depth peek)).trans (le_max_right peek _))
      (le_max_right p.width q.width)
    obtain ⟨R, hR⟩ := IsLocal.ite (fun c v => b c (view peek v)) hp hq
    refine ⟨R, fun c st => ?_⟩
    rw [← hR]
    have hv : view peek (view (max peek (max (p.depth peek) (q.depth peek))) st) = view peek st := by
      funext k; simp only [view, List.take_take]; congr 1; omega
    show (if b c (view peek st) then _ else _) = _
    beta_reduce
    rw [hv]

end PalPeg.ScaProg
