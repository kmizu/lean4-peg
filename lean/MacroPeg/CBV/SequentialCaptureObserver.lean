import MacroPeg.CBV.ProfileControl

namespace Shallot.MacroPeg.CBV.SequentialCaptureObserver
open RegularCaptureProduct (Machine filtered)
open CaptureTransitionProfile (profile profiles)
open ClockFreezing (Table)

/-- The parameter's full profile and the observer's entry/exit states are
finite rule indices. The retained parameter remains the actual whole word. -/
def keys (D : Machine) : List (List Nat × Nat × Nat) :=
  (profiles D).flatMap (fun P => (List.range D.width).flatMap (fun q =>
    (List.range D.width).map (fun r => (P,q,r))))

def address (D : Machine) (base : Nat) (P : List Nat) (q r : Nat) : Nat :=
  base+(keys D).idxOf (P,q,r)

def rules (D : Machine) (B : List Nat → Nat → Nat → MExp) : List MRule :=
  (keys D).map (fun (P,q,r) => ⟨1,B P q r⟩)

def grammar (D : Machine) (original : List MRule) (B : List Nat → Nat → Nat → MExp) : MGrammar :=
  ⟨original++rules D B⟩

theorem key_mem (D : Machine) (P : List Nat) (hP : P∈profiles D) (q r : Nat)
    (hq : q<D.width) (hr : r<D.width) : (P,q,r)∈keys D :=
  List.mem_flatMap.mpr ⟨P,hP,List.mem_flatMap.mpr ⟨q,List.mem_range.mpr hq,
    List.mem_map.mpr ⟨r,List.mem_range.mpr hr,rfl⟩⟩⟩

theorem product_rule (D : Machine) (original : List MRule) (B : List Nat → Nat → Nat → MExp)
    (P : List Nat) (hP : P∈profiles D) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    ruleAtM (grammar D original B).rules (address D original.length P q r)=some ⟨1,B P q r⟩ := by
  have hk := DependentProfileCall.index_correct (P,q,r) (keys D) (key_mem D P hP q r hq hr)
  simp only [grammar,address,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,rules,List.getElem?_map,hk,Option.map_some]

theorem grammar_firstOrder (D : Machine) (original : List MRule) (B : List Nat → Nat → Nat → MExp)
    (hOriginal : ∀ r∈original, r.body.FirstOrder) (hB : ∀ P q r, (B P q r).FirstOrder) :
    (grammar D original B).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hOriginal r hr
  · obtain ⟨⟨P,q,r⟩,_,rfl⟩ := List.mem_map.mp hr
    exact hB P q r

/-- An argument is evaluated in the original caller environment. Its
whole profile moves the observer before the actual unary callee begins. -/
def call (D : Machine) (base : Nat) (a : MExp) (F : Nat → Nat → MExp) (q r : Nat) : MExp :=
  ProfileControl.select D a F (fun P => .call (address D base P (P[q]?.getD 0) r) [a])

theorem call_firstOrder (D : Machine) (base : Nat) (a : MExp) (ha : a.FirstOrder)
    (F : Nat → Nat → MExp) (hF : ∀ q r, (F q r).FirstOrder) (q r : Nat) :
    (call D base a F q r).FirstOrder :=
  ProfileControl.select_firstOrder D a F ha hF _ (fun _ _ => ⟨ha,True.intro⟩)

/-- The one-call induction step for observer products of parameterized
Seq rules. Rows concern the callee body only; the observer advancement across
the actual argument is generated here, including failure and undefinedness. -/
theorem call_correct (D : Machine) (hD : D.Valid) (original : List MRule)
    (B : List Nat → Nat → Nat → MExp) (i : Nat) (body : MExp)
    (hi : ruleAtM (grammar D original B).rules i=some ⟨1,body⟩)
    (x : List Char) (T : Table) (hT : SoundTV (grammar D original B) x .callByValueSeq T)
    (E : List (List Char)) (a : MExp) (ha : a.FirstOrder) (F : Nat → Nat → MExp)
    (p : Nat) (hp : p≤x.length)
    (hF : ∀ q r, q<D.width → r<D.width →
      evV (grammar D original B) x .callByValueSeq T E (F q r) p=
        filtered D x q r p (evV (grammar D original B) x .callByValueSeq T E a p))
    (hRows : ∀ w j q r, j≤x.length → q<D.width → r<D.width →
      valAt (T (address D original.length (profile D w) q r) [w]) j=
        filtered D x q r j (valAt (T i [w]) j))
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (grammar D original B) x .callByValueSeq T E (call D original.length a F q r) p=
      filtered D x q r p (evV (grammar D original B) x .callByValueSeq T E (.call i [a]) p) := by
  unfold call
  rw [ProfileControl.select_correct D hD _ x .callByValueSeq T E a F p hF,
    evV_call_seq hi rfl]
  simp only [evSeqArgs]
  cases hv : evV (grammar D original B) x .callByValueSeq T E a p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := DependentCaptureFilter.success_prefix (by decide) hT E a ha p j hp hv
      have ht := RegularCaptureProduct.run_bound hD q hq (pre x p j)
      dsimp only []
      rw [CaptureTransitionProfile.profile_get D (pre x p j) q hq,Option.getD_some,
        evV_call_seq (product_rule D original B _ (CaptureTransitionProfile.profile_mem D hD _) _ r ht hr) rfl]
      simp only [evSeqArgs,hv]
      rw [hRows _ j _ r hj.1 ht hr]
      exact (CapturePrefixRows.filter_prefix D x (pre x p j) p j q r hp hj.1 hj.2
        (valAt (T i [pre x p j]) j)
        (fun z hz => CapturePrefixRows.row_success_prefix _ x .callByValueSeq T hT i _ hi
          [pre x p j] rfl j z hj.1 hz)).symm

/-- Full metadata for a parameterized call observes the argument and the
callee together. It is the whole call's capture, not the callee parameter's
profile, that may subsequently be retained as a fresh argument. -/
def select (D : Machine) (base i : Nat) (a : MExp) (F : Nat → Nat → MExp)
    (K : List Nat → MExp) : MExp :=
  ProfileControl.select D (.call i [a]) (fun q r => call D base a F q r) K

theorem select_result (D : Machine) (hD : D.Valid) (original : List MRule)
    (B : List Nat → Nat → Nat → MExp) (i : Nat) (body : MExp)
    (hi : ruleAtM (grammar D original B).rules i=some ⟨1,body⟩)
    (x : List Char) (T : Table) (hT : SoundTV (grammar D original B) x .callByValueSeq T)
    (E : List (List Char)) (a : MExp) (ha : a.FirstOrder) (F : Nat → Nat → MExp)
    (p : Nat) (hp : p≤x.length)
    (hF : ∀ q r, q<D.width → r<D.width →
      evV (grammar D original B) x .callByValueSeq T E (F q r) p=
        filtered D x q r p (evV (grammar D original B) x .callByValueSeq T E a p))
    (hRows : ∀ w j q r, j≤x.length → q<D.width → r<D.width →
      valAt (T (address D original.length (profile D w) q r) [w]) j=
        filtered D x q r j (valAt (T i [w]) j))
    (K : List Nat → MExp) :
    evV (grammar D original B) x .callByValueSeq T E (select D original.length i a F K) p=
      match evV (grammar D original B) x .callByValueSeq T E (.call i [a]) p with
      | some (some j) => evV (grammar D original B) x .callByValueSeq T E (K (profile D (pre x p j))) p
      | other => other := by
  exact ProfileControl.select_correct D hD _ x .callByValueSeq T E (.call i [a]) _ p
    (fun q r hq hr => call_correct D hD original B i body hi x T hT E a ha F p hp hF hRows q r hq hr) K

end Shallot.MacroPeg.CBV.SequentialCaptureObserver
