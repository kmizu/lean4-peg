import MacroPeg.CBV.RetainedPatternSyntax

namespace Shallot.MacroPeg.CBV.RetainedCaptureEffects
open RetainedPatternSyntax
open NestedScannerArguments (accepts)
open MaskedScannerAbsorption (enabled)
open ClockFreezing (Table)
abbrev Term := RetainedPatternSyntax.Expr

/-- Consumed output stays in A. Incoming parent words need satisfy A only
when the expression positively replays them. Client calls replay their
actual and then execute a separately checked alpha-preserving tail. -/
def safeCheck (bodies : List MExp) (clients : List Term) (effects : List Bool) (A : List Char) (parentFree : Bool) : Term → Bool
  | .eps | .notP _ => true
  | .parent => parentFree
  | .chr c => accepts A c
  | .lit w => w.all (accepts A)
  | .helper i => enabled (MaskedScannerAbsorption.mask bodies A) i
  | .user i a => (decide (i<clients.length) && enabled effects i) && safeCheck bodies clients effects A parentFree a
  | .seq a b | .alt a b => safeCheck bodies clients effects A parentFree a && safeCheck bodies clients effects A parentFree b
  | .star a => safeCheck bodies clients effects A parentFree a
  | .any | .range _ _ | .copy _ => false

def prune (bodies : List MExp) (clients : List Term) (A : List Char) : Nat → List Bool
  | 0 => List.replicate clients.length true
  | k+1 => clients.map (safeCheck bodies clients (prune bodies clients A k) A true)
def effects (bodies : List MExp) (clients : List Term) (A : List Char) := prune bodies clients A clients.length

def Valid (bodies : List MExp) (clients : List Term) (A : List Char) : Prop :=
  (∀ i, enabled (effects bodies clients A) i=true → i<clients.length) ∧
    ∀ i e, clients[i]?=some e → enabled (effects bodies clients A) i=true → safeCheck bodies clients (effects bodies clients A) A true e=true

def check (bodies : List MExp) (clients : List Term) (A : List Char) : Bool :=
  decide ((effects bodies clients A).length=clients.length) && clients.zipIdx.all (fun (e,i) =>
    !enabled (effects bodies clients A) i || safeCheck bodies clients (effects bodies clients A) A true e)

theorem checked (bodies : List MExp) (clients : List Term) (A : List Char) (hc : check bodies clients A=true) : Valid bodies clients A := by
  obtain ⟨hlen,hc⟩ := Bool.and_eq_true_iff.mp hc
  have hlen := of_decide_eq_true hlen
  constructor
  · intro i hi
    by_cases hn : i<clients.length
    · exact hn
    have hh : (effects bodies clients A)[i]?=none := List.getElem?_eq_none (by omega)
    simp [enabled,hh] at hi
  · intro i e hi he
    have hm : (e,i)∈clients.zipIdx := List.mem_of_getElem? (show clients.zipIdx[i]?=some (e,i) from by simp [List.getElem?_zipIdx,hi])
    have hh := List.all_eq_true.mp hc (e,i) hm
    simpa only [he,Bool.not_true,Bool.false_or] using hh

def EnvSafe (A : List Char) (parentFree : Bool) (E : List (List Char)) : Prop :=
  parentFree=true → ∀ w, E[0]?=some w → w.all (accepts A)=true

def RowsSafe (bodies : List MExp) (clients : List Term) (A x : List Char) (T : Table) : Prop :=
  ∀ i e, clients[i]?=some e → enabled (effects bodies clients A) i=true → ∀ w,
    w.all (accepts A)=true → ∀ p q, p≤x.length → valAt (T (bodies.length+i) [w]) p=some (some q) →
      (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A)

private theorem base_safe (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (pattern : List Nat)
    (A x : List Char) (T : Table)
    (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies A) A)
    (hbase : MaskedScannerAbsorption.RowsSafe (MaskedScannerAbsorption.mask bodies A) A x T) (hOk : OkTV x.length T)
    (E : List (List Char)) (e : MExp) (he : MaskedScannerAbsorption.Safe (MaskedScannerAbsorption.mask bodies A) A e)
    (p q : Nat) (hp : p≤x.length) (hv : evV (source bodies clients arity d pattern) x .callByValuePar T E e p=some (some q)) :
    (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A) := by
  apply MaskedScannerAbsorption.evaluator_safe (MaskedScannerAbsorption.mask bodies A) _ A x .callByValuePar T hbase hOk E e he p q hp hv
  intro i hi
  exact ⟨bodies[i]'(hmask.1 i hi),source_installed bodies clients arity d pattern i _ (List.getElem?_eq_getElem (hmask.1 i hi))⟩

/-- Every successful positive path is alpha-preserving, including real
parameterized client calls. No termination premise is used. -/
theorem evaluator_safe (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (pattern : List Nat)
    (A x : List Char) (T : Table)
    (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies A) A)
    (hbase : MaskedScannerAbsorption.RowsSafe (MaskedScannerAbsorption.mask bodies A) A x T)
    (hrows : RowsSafe bodies clients A x T) (hOk : OkTV x.length T)
    (hT : SoundTV (source bodies clients arity d pattern) x .callByValuePar T)
    (parentFree : Bool) (E : List (List Char)) (hE : EnvSafe A parentFree E) :
    ∀ e, safeCheck bodies clients (effects bodies clients A) A parentFree e=true → ∀ p q, p≤x.length →
      evV (source bodies clients arity d pattern) x .callByValuePar T E (render bodies.length clients.length true e) p=some (some q) →
        (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A)
  | .parent,hf,p,q,hp,hv => by
    cases hw : E[0]? with
    | none => simp [render,evV,hw] at hv
    | some w =>
      exact ScannerAbsorption.literal_safe x A w (hE hf w hw) p q (by cases hs : Shallot.stripPrefix? w (sfx x p) <;> simpa only [render,evV,hw,hs] using hv)
  | .user i a,hc,p,q,hp,hv => by
    obtain ⟨hh,ha⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hi,he⟩ := Bool.and_eq_true_iff.mp hh
    have hi : i<clients.length := of_decide_eq_true hi
    have hr := source_user bodies clients arity d pattern i clients[i] (List.getElem?_eq_getElem hi)
    rw [render,evV_call_par hr rfl (by decide)] at hv
    cases harg : evV (source bodies clients arity d pattern) x .callByValuePar T E (render bodies.length clients.length true a) p with
    | none => rw [evPar_cons_none harg] at hv; cases hv
    | some v => cases v with
      | none => rw [evPar_cons_fail harg] at hv; cases hv
      | some j =>
        rw [evPar_cons_ok harg,evPar_nil] at hv
        have hs := (ReplayFusion.success_prefix hT E _ (render_firstOrder _ _ _ _) p j hp harg).2
        have hd := evaluator_safe bodies clients arity d pattern A x T hmask hbase hrows hOk hT parentFree E hE a ha p j hp harg
        rw [hs] at hd
        have hw := CaptureDelimiterSafety.all_of_drop_eq A (pre x p j) (sfx x j) hd
        exact hrows i clients[i] (List.getElem?_eq_getElem hi) he (pre x p j) hw p q hp hv
  | .seq a b,hc,p,q,hp,hv => by
    cases ha : evV (source bodies clients arity d pattern) x .callByValuePar T E (render bodies.length clients.length true a) p with
    | none => rw [render,evV_seq_none ha] at hv; cases hv
    | some v => cases v with
      | none => rw [render,evV_seq_fail ha] at hv; cases hv
      | some j =>
        rw [render,evV_seq_ok ha] at hv
        exact (evaluator_safe bodies clients arity d pattern A x T hmask hbase hrows hOk hT parentFree E hE a (Bool.and_eq_true_iff.mp hc).1 p j hp ha).trans
          (evaluator_safe bodies clients arity d pattern A x T hmask hbase hrows hOk hT parentFree E hE b (Bool.and_eq_true_iff.mp hc).2 j q (evV_ok hOk _ p hp j ha) hv)
  | .alt a b,hc,p,q,hp,hv => by
    cases ha : evV (source bodies clients arity d pattern) x .callByValuePar T E (render bodies.length clients.length true a) p with
    | none => rw [render,evV_alt_none ha] at hv; cases hv
    | some v => cases v with
      | none =>
        rw [render,evV_alt_fail ha] at hv
        exact evaluator_safe bodies clients arity d pattern A x T hmask hbase hrows hOk hT parentFree E hE b (Bool.and_eq_true_iff.mp hc).2 p q hp hv
      | some j =>
        rw [render,evV_alt_ok ha] at hv
        cases hv
        exact evaluator_safe bodies clients arity d pattern A x T hmask hbase hrows hOk hT parentFree E hE a (Bool.and_eq_true_iff.mp hc).1 p q hp ha
  | .star a,hc,p,q,hp,hv => by
    have hh : ∀ p, p≤x.length → evStar (fun z => evV (source bodies clients arity d pattern) x .callByValuePar T E (render bodies.length clients.length true a) z) p=some (some q) →
        (sfx x p).dropWhile (accepts A)=(sfx x q).dropWhile (accepts A) := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro hp hv
        cases ha : evV (source bodies clients arity d pattern) x .callByValuePar T E (render bodies.length clients.length true a) p with
        | none => rw [evStar_none ha] at hv; cases hv
        | some v => cases v with
          | none => rw [evStar_fail ha] at hv; cases hv; rfl
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at hv
              exact (evaluator_safe bodies clients arity d pattern A x T hmask hbase hrows hOk hT parentFree E hE a hc p j hp ha).trans
                (ih j hj (by omega) hv)
            · rw [evStar_stuck ha hj] at hv; cases hv
    exact hh p hp hv
  | .eps,_,p,q,hp,hv => base_safe bodies clients arity d pattern A x T hmask hbase hOk E .eps True.intro p q hp hv
  | .chr c,hc,p,q,hp,hv => base_safe bodies clients arity d pattern A x T hmask hbase hOk E (.chr c) hc p q hp hv
  | .lit w,hc,p,q,hp,hv => base_safe bodies clients arity d pattern A x T hmask hbase hOk E (.lit w) hc p q hp hv
  | .helper i,hc,p,q,hp,hv => base_safe bodies clients arity d pattern A x T hmask hbase hOk E (.call i []) hc p q hp hv
  | .notP a,_,p,q,hp,hv => base_safe bodies clients arity d pattern A x T hmask hbase hOk E (.notP (render bodies.length clients.length true a)) True.intro p q hp hv
  | .any,h,_,_,_,_ | .range _ _,h,_,_,_,_ | .copy _,h,_,_,_,_ => by cases h

/-- Finite effect closure is valid for every actual physical source row. -/
theorem physical_rows (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (pattern : List Nat)
    (hb : RecursiveParserStability.Valid bodies) (A : List Char)
    (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies A) A)
    (heff : Valid bodies clients A) (x : List Char) (k : Nat) :
    RowsSafe bodies clients A x (tblV (source bodies clients arity d pattern) x .callByValuePar k) := by
  induction k with
  | zero => intro i e hi he w hw p q hp hv; cases hv
  | succ k ih =>
    intro i e hi he w hw p q hp hv
    rw [valAt_tblV_succ (source_user bodies clients arity d pattern i e hi) [w] hp] at hv
    cases hfirst : evV (source bodies clients arity d pattern) x .callByValuePar
        (tblV (source bodies clients arity d pattern) x .callByValuePar k) [w] (.param 0) p with
    | none => rw [evV_seq_none hfirst] at hv; cases hv
    | some v => cases v with
      | none => rw [evV_seq_fail hfirst] at hv; cases hv
      | some j =>
        rw [evV_seq_ok hfirst] at hv
        have hhead := ScannerAbsorption.literal_safe x A w hw p j (by cases hs : Shallot.stripPrefix? w (sfx x p) <;> simpa only [evV,List.getElem?_cons_zero,hs] using hfirst)
        have htail := evaluator_safe bodies clients arity d pattern A x _ hmask
          (MaskedScannerAbsorption.physical_rows (source_installed bodies clients arity d pattern) _ A hmask x .callByValuePar k)
          ih (tblV_ok _ _ _ k) (tblV_sound (source_firstOrder bodies clients arity d pattern hb) (by decide) k) true [w]
          (fun _ v hv => by
            have hh : w=v := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hv
            subst v
            exact hw) e (heff.2 i e hi he)
          j q (evV_ok (tblV_ok _ _ _ k) _ p hp j hfirst) hv
        exact hhead.trans htail

theorem captured_alpha (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (pattern : List Nat)
    (hb : RecursiveParserStability.Valid bodies) (A : List Char)
    (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies A) A) (heff : Valid bodies clients A)
    (x : List Char) (k : Nat) (parentFree : Bool) (E : List (List Char)) (hE : EnvSafe A parentFree E)
    (e : Term) (he : safeCheck bodies clients (effects bodies clients A) A parentFree e=true)
    (p q : Nat) (hp : p≤x.length)
    (hv : evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) E (render bodies.length clients.length true e) p=some (some q)) :
    (pre x p q).all (accepts A)=true := by
  have hd := evaluator_safe bodies clients arity d pattern A x _ hmask
    (MaskedScannerAbsorption.physical_rows (source_installed bodies clients arity d pattern) _ A hmask x .callByValuePar k)
    (physical_rows bodies clients arity d pattern hb A hmask heff x k) (tblV_ok _ _ _ k)
    (tblV_sound (source_firstOrder bodies clients arity d pattern hb) (by decide) k) parentFree E hE e he p q hp hv
  have hs := (ReplayFusion.success_prefix (tblV_sound (source_firstOrder bodies clients arity d pattern hb) (by decide) k) E _ (render_firstOrder _ _ _ _) p q hp hv).2
  rw [hs] at hd
  exact CaptureDelimiterSafety.all_of_drop_eq A _ _ hd

end Shallot.MacroPeg.CBV.RetainedCaptureEffects
