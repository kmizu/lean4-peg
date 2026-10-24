import MacroPeg.CBV.RegularCaptureCorrectness

/-! A finite phase machine for arbitrary fixed nonempty replay shifts. -/
namespace Shallot.MacroPeg.CBV.PeriodicCaptureMachine
open RegularCaptureProduct (Machine run)
open BlockCapture (copies)

def phase (u : List Char) (q : Nat) : List Char := u.drop q++u.take q

def next (u : List Char) (q : Nat) : Nat := if q+1<u.length then q+1 else 0

def step (u : List Char) (q : Nat) (c : Char) : Nat :=
  if q<u.length ∧ u[q]?=some c then next u q else u.length

def machine (u : List Char) : Machine := ⟨u.length+1,step u⟩

theorem next_bound (u : List Char) (hu : 0<u.length) (q : Nat) : next u q<u.length := by
  unfold next
  split <;> omega

theorem valid (u : List Char) (hu : u≠[]) : (machine u).Valid := by
  have hlen := List.length_pos_iff.mpr hu
  refine ⟨by simp [machine],?_⟩
  intro q _ c
  change step u q c<u.length+1
  unfold step
  split
  · have := next_bound u hlen q; omega
  · omega

theorem step_sink (u : List Char) (c : Char) : step u u.length c=u.length := by simp [step]

theorem run_sink (u w : List Char) : run (machine u) u.length w=u.length := by
  induction w with
  | nil => rfl
  | cons c w ih => simpa only [run,List.foldl_cons,machine,step_sink] using ih

/-- A consumed matching character rotates the residual by one place. -/
theorem phase_step (u : List Char) (q : Nat) (c : Char)
    (hq : q<u.length) (hc : u[q]?=some c) :
    phase u q++[c]=c::phase u (next u q) := by
  have he : u[q]=c := (List.getElem?_eq_some_iff.mp hc).2
  have hd := List.drop_eq_getElem_cons hq
  have ht : u.take (q+1)=u.take q++[c] := by rw [List.take_add_one,hc]; rfl
  have hstep : phase u q++[c]=c::phase u (q+1) := by
    simp only [phase,hd,he,List.cons_append,List.append_assoc,ht]
  rw [hstep]
  congr 1
  unfold next
  split
  · rfl
  · have hlen : q+1=u.length := by omega
    simp [phase,hlen]

/-- Any nonsink execution supplies the unique actual rotation equation. -/
theorem run_rotation (u : List Char) (hu : u≠[]) :
    ∀ (w : List Char) (q : Nat), q<u.length → run (machine u) q w<u.length →
      phase u q++w=w++phase u (run (machine u) q w)
  | [], q, hq, _ => by simp [run]
  | c::w, q, hq, hv => by
    have hs : step u q c<u.length := by
      have hb := (valid u hu).2 q (by change q<u.length+1; omega) c
      change step u q c<u.length+1 at hb
      by_cases hn : step u q c<u.length
      · exact hn
      have he : step u q c=u.length := by omega
      change run (machine u) (step u q c) w<u.length at hv
      rw [he,run_sink] at hv
      omega
    have hc : u[q]?=some c := by
      by_cases hn : u[q]?=some c
      · exact hn
      simp [step,hn] at hs
    have he : step u q c=next u q := by rw [step,if_pos ⟨hq,hc⟩]
    have ih := run_rotation u hu w (step u q c) hs hv
    have hp := phase_step u q c hq hc
    calc
      phase u q++(c::w) = (phase u q++[c])++w := by simp
      _ = (c::phase u (step u q c))++w := by rw [he,hp]
      _ = (c::w)++phase u (run (machine u) (step u q c) w) := by
        simpa only [List.cons_append] using congrArg (c :: ·) ih

/-- Reading an initial segment of the shift gives its exact phase, with the
whole shift returning to phase zero. -/
theorem run_take (u : List Char) (hu : u≠[]) : ∀ n, n≤u.length →
    run (machine u) 0 (u.take n)=if n<u.length then n else 0 := by
  have hlen := List.length_pos_iff.mpr hu
  intro n
  induction n with
  | zero => intro _; simp [run,hlen]
  | succ n ih =>
    intro hn
    have hn' : n<u.length := by omega
    rw [List.take_add_one,List.getElem?_eq_getElem hn']
    rw [RegularCaptureProduct.run_append,ih (by omega),if_pos hn']
    simp only [Option.toList_some,run,List.foldl_cons,List.foldl_nil,machine]
    simp only [step,hn',List.getElem?_eq_getElem hn',and_self,ite_true,next]

theorem run_copies (u : List Char) (hu : u≠[]) (n : Nat) : run (machine u) 0 (copies u n)=0 := by
  have hb : run (machine u) 0 u=0 := by
    simpa using run_take u hu u.length (by omega)
  induction n with
  | zero => rfl
  | succ n ih => rw [copies,RegularCaptureProduct.run_append,hb,ih]

/-- A prefix forced by shifted replay always reaches a nonsink phase. -/
theorem prefix_run (u w : List Char) (hu : u≠[]) (hw : w.IsPrefix (u++w)) :
    run (machine u) 0 w<u.length := by
  obtain ⟨n,left,right,hs,he,hlen⟩ := OverlapNecessity.prefix_periodic u hu w hw
  have hl : left=u.take left.length := List.prefix_iff_eq_take.mp ⟨right,hs.symm⟩
  rw [he,RegularCaptureProduct.run_append,run_copies u hu,hl]
  rw [run_take u hu left.length (by omega),if_pos hlen]
  exact hlen

/-- This finite machine tests exactly the necessary periodic capture
condition, rather than accepting arbitrary captures with a rotation guess. -/
theorem prefix_iff_nonsink (u w : List Char) (hu : u≠[]) :
    w.IsPrefix (u++w) ↔ run (machine u) 0 w<u.length := by
  refine ⟨prefix_run u w hu,?_⟩
  intro h
  have he := run_rotation u hu w 0 (List.length_pos_iff.mpr hu) h
  exact ⟨phase u (run (machine u) 0 w),by simpa [phase] using he.symm⟩

end Shallot.MacroPeg.CBV.PeriodicCaptureMachine
