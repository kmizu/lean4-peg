import MacroPeg.CBV.CaptureOrbit

/-! Grouped repetition stays in the current evaluation environment. -/
namespace Shallot.MacroPeg.CBV.InlineRepeat

inductive Trace (f : Nat → Res) : Nat → Nat → Nat → Prop
  | zero (p : Nat) : Trace f p 0 p
  | succ {p z n j : Nat} (hv : f p=some (some z)) (hz : z<p) (tail : Trace f z n j) : Trace f p (n+1) j

def steps (f : Nat → Res) : Nat → Nat → Res
  | 0, p => some (some p)
  | n+1, p => match f p with | some (some z) => steps f n z | other => other

theorem trace_le {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) : j≤p := by
  induction h with
  | zero => omega
  | succ hv hz tail ih => omega

theorem trace_lt {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) (hn : 0<n) : j<p := by
  cases h with
  | zero => omega
  | succ hv hz tail => have := trace_le tail; omega

theorem trace_steps {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) : steps f n p=some (some j) := by
  induction h with
  | zero => rfl
  | succ hv _ _ ih => simp only [steps,hv]; exact ih

theorem trace_split {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) :
    ∀ k, k≤n → ∃ z, Trace f p k z ∧ Trace f z (n-k) j := by
  induction h with
  | zero p =>
    intro k hk
    have he : k=0 := by omega
    subst k
    exact ⟨p,.zero p,.zero p⟩
  | @succ p z n j hv hz tail ih =>
    intro k hk
    cases k with
    | zero => exact ⟨p,.zero p,by simpa using Trace.succ hv hz tail⟩
    | succ k =>
      obtain ⟨v,hv',ht⟩ := ih k (by omega)
      exact ⟨v,.succ hv hz hv',by simpa using ht⟩

theorem overrun {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) (hf : f j=some none) :
    ∀ k, n<k → steps f k p=some none := by
  induction h with
  | zero p => intro k hk; cases k with
    | zero => omega
    | succ k => simp only [steps,hf]
  | succ hv _ _ ih => intro k hk; cases k with
    | zero => omega
    | succ k => simpa only [steps,hv] using ih hf k (by omega)

theorem star_trace (f : Nat → Res) : ∀ p j, evStar f p=some (some j) →
    ∃ n, Trace f p n j ∧ f j=some none := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro j hv
    cases hf : f p with
    | none => rw [evStar_none hf] at hv; cases hv
    | some r => cases r with
      | none => rw [evStar_fail hf] at hv; cases hv; exact ⟨0,.zero p,hf⟩
      | some z =>
        by_cases hz : z<p
        · rw [evStar_ok hf hz] at hv
          obtain ⟨n,ht,hend⟩ := ih z hz j hv
          exact ⟨n+1,.succ hf hz ht,hend⟩
        · rw [evStar_stuck hf hz] at hv; cases hv

theorem trace_star {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) (hf : f j=some none) :
    evStar f p=some (some j) := by
  induction h with
  | zero => exact evStar_fail hf
  | succ hv hz _ ih => rw [evStar_ok hv hz]; exact ih hf

/-- n copies, inline; no call discards or re-evaluates the environment. -/
def copies (e : MExp) : Nat → MExp
  | 0 => .eps
  | n+1 => .seq e (copies e n)

def pattern (e : MExp) (k l : Nat) : MExp :=
  .seq (copies e k) (.seq (if l=0 then .eps else .star (copies e l)) (.notP e))

theorem copies_firstOrder (e : MExp) (he : e.FirstOrder) : ∀ k, (copies e k).FirstOrder
  | 0 => True.intro
  | n+1 => ⟨he,copies_firstOrder e he n⟩

theorem pattern_firstOrder (e : MExp) (he : e.FirstOrder) (k l : Nat) :
    (pattern e k l).FirstOrder := by
  refine ⟨copies_firstOrder e he k,?_,he⟩
  split
  · trivial
  · exact copies_firstOrder e he l

theorem copies_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) : ∀ k p,
    evV g x s T E (copies e k) p=steps (fun z => evV g x s T E e z) k p
  | 0, _ => rfl
  | k+1, p => by
    change (match evV g x s T E e p with | some (some z) => evV g x s T E (copies e k) z | other => other)=_
    simp only [steps]
    cases evV g x s T E e p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some z => exact copies_eval g x s T E e k z

def finish (f : Nat → Res) : Res → Res
  | some (some j) => match f j with | some (some _) => some none | some none => some (some j) | none => none
  | other => other

theorem finish_trace {f : Nat → Res} {p n j : Nat} (h : Trace f p n j) (hf : f j=some none) :
    finish f (some (some p))=if n=0 then some (some j) else some none := by
  cases h with
  | zero => simp [finish,hf]
  | succ hv _ _ => simp [finish,hv]

/-- Grouped greedy repetition followed by the original stopping test
accepts exactly when the original iteration count is divisible by l. -/
theorem grouped_finish (f : Nat → Res) (l : Nat) (hl : 0<l) :
    ∀ n p j, Trace f p n j → f j=some none →
      finish f (evStar (steps f l) p)=if n%l=0 then some (some j) else some none := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p j ht hf
    by_cases hn : n<l
    · rw [evStar_fail (overrun ht hf l hn),finish_trace ht hf,Nat.mod_eq_of_lt hn]
    · obtain ⟨z,hhead,htail⟩ := trace_split ht l (by omega)
      rw [evStar_ok (trace_steps hhead) (trace_lt hhead hl),
        ih (n-l) (by omega) z j htail hf,←Nat.mod_eq_sub_mod (by omega : n≥l)]

def evaluatePattern (f : Nat → Res) (k l p : Nat) : Res :=
  match steps f k p with
  | some (some z) => finish f (if l=0 then some (some z) else evStar (steps f l) z)
  | other => other

theorem pattern_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (k l p : Nat) :
    evV g x s T E (pattern e k l) p=evaluatePattern (fun z => evV g x s T E e z) k l p := by
  unfold pattern evaluatePattern
  change (match evV _ _ _ _ E (copies e k) p with
    | some (some z) => evV _ _ _ _ E (.seq (if l=0 then .eps else .star (copies e l)) (.notP e)) z
    | other => other)=_
  rw [copies_eval]
  cases hv : steps (fun z => evV g x s T E e z) k p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some z =>
      dsimp only []
      by_cases hz : l=0
      · simp only [if_pos hz]
        change (match evV g x s T E e z with
          | some (some _) => some none | some none => some (some z) | none => none)=_
        simp only [finish]
      · rw [if_neg hz,if_neg hz]
        change (match evStar (fun v => evV g x s T E (copies e l) v) z with
          | some (some j) => evV g x s T E (.notP e) j | other => other)=_
        have he : evStar (fun v => evV g x s T E (copies e l) v) z=evStar (steps (fun v => evV g x s T E e v) l) z :=
          evStar_congr z (fun v _ => copies_eval g x s T E e l v)
        simp only [he]
        cases evStar (steps (fun v => evV g x s T E e v) l) z with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some j =>
            change (match evV g x s T E e j with
              | some (some _) => some none | some none => some (some j) | none => none)=_
            simp only [finish]

theorem fits_iff (n k l : Nat) :
    CaptureOrbit.Fits n k l ↔ k≤n ∧ (if l=0 then n=k else (n-k)%l=0) := by
  by_cases hl : l=0
  · simp [CaptureOrbit.Fits,hl]; omega
  · simp only [CaptureOrbit.Fits,if_neg hl]
    constructor
    · rintro ⟨m,rfl⟩
      exact ⟨by omega,by simp⟩
    · rintro ⟨hk,hn⟩
      exact ⟨(n-k)/l,by have := Nat.mod_add_div (n-k) l; omega⟩

/-- Inline candidate parsing has an exact count specification on any
successful strictly consuming source repetition, not just on literals. -/
theorem evaluatePattern_trace (f : Nat → Res) (k l : Nat) {p n j : Nat}
    (ht : Trace f p n j) (hf : f j=some none) :
    evaluatePattern f k l p=
      if k≤n ∧ (if l=0 then n=k else (n-k)%l=0) then some (some j) else some none := by
  by_cases hk : k≤n
  · obtain ⟨z,hhead,htail⟩ := trace_split ht k hk
    simp only [evaluatePattern,trace_steps hhead,hk,true_and]
    by_cases hl : l=0
    · simp only [hl,ite_true,finish_trace htail hf]
      have he : n-k=0 ↔ n=k := by omega
      simp only [he]
    · simp only [hl,ite_false,grouped_finish f l (by omega) (n-k) z j htail hf]
  · simp only [evaluatePattern,overrun ht hf k (by omega),hk,false_and,ite_false]

theorem pattern_ok (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (k l p n j : Nat)
    (ht : Trace (fun z => evV g x s T E e z) p n j) (hf : evV g x s T E e j=some none)
    (hn : CaptureOrbit.Fits n k l) : evV g x s T E (pattern e k l) p=some (some j) := by
  rw [pattern_eval,evaluatePattern_trace _ k l ht hf,if_pos ((fits_iff n k l).mp hn)]

theorem pattern_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (k l p n j : Nat)
    (ht : Trace (fun z => evV g x s T E e z) p n j) (hf : evV g x s T E e j=some none)
    (hn : ¬CaptureOrbit.Fits n k l) : evV g x s T E (pattern e k l) p=some none := by
  rw [pattern_eval,evaluatePattern_trace _ k l ht hf,if_neg (fun h => hn ((fits_iff n k l).mpr h))]

theorem choice_success (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (e : MExp) (p n j : Nat)
    (ht : Trace (fun z => evV g x s T E e z) p n j) (hf : evV g x s T E e j=some none) :
    ∀ ds : List (Nat × Nat), (∃ k l, (k,l)∈ds ∧ CaptureOrbit.Fits n k l) →
      evV g x s T E (RegularCaptureProduct.choice (ds.map (fun (k,l) => pattern e k l))) p=some (some j)
  | [], h => by simp at h
  | (k,l)::ds, h => by
    simp only [List.map_cons,RegularCaptureProduct.choice]
    by_cases hn : CaptureOrbit.Fits n k l
    · exact evV_alt_ok (pattern_ok g x s T E e k l p n j ht hf hn)
    · rw [evV_alt_fail (pattern_fail g x s T E e k l p n j ht hf hn)]
      apply choice_success g x s T E e p n j ht hf ds
      obtain ⟨a,b,hab,hf⟩ := h
      rcases List.mem_cons.mp hab with he | hab
      · cases he; exact False.elim (hn hf)
      · exact ⟨a,b,hab,hf⟩

end Shallot.MacroPeg.CBV.InlineRepeat
