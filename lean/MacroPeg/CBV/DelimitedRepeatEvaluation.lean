import MacroPeg.CBV.RepeatedWordPattern
import MacroPeg.CBV.InlineRepeat

namespace Shallot.MacroPeg.CBV.DelimitedRepeatEvaluation
open DelimiterTemplate ClockFreezing Classical

def copies (ps : List Part) : Nat → List Part
  | 0 => []
  | n+1 => ps++copies ps n

def fullStar (d : Char) (ps : List Part) : MExp :=
  .seq (.star (compile d ps)) (.notP .any)

def Accept (d : Char) (E : List (List Char)) (ps : List Part) (x : List Char) : Prop :=
  ∃ n, run d E (copies ps n) x=some []

theorem copies_firstOrder (d : Char) (ps : List Part) : (fullStar d ps).FirstOrder :=
  ⟨compile_firstOrder d ps,True.intro⟩

/-- A template's successful runs always return a suffix. -/
theorem run_suffix (d : Char) (E : List (List Char)) : ∀ ps x rest,
    run d E ps x=some rest → ∃ headPart, x=headPart++rest
  | [],x,rest,h => ⟨[],by simpa [run] using h⟩
  | p::ps,x,rest,h => by
    cases hp : action d E p x with
    | none => simp [run,hp] at h
    | some y =>
      exact suffix_trans (action_suffix d E p x y hp)
        (run_suffix d E ps y rest (by simpa [run,hp] using h))

theorem copies_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (d : Char) (ps : List Part) :
    ∀ n p, p≤x.length →
    InlineRepeat.steps (fun q => evV g x s T E (compile d ps) q) n p=
      some ((run d E (copies ps n) (sfx x p)).map List.length)
  | 0,p,hp => by simp [InlineRepeat.steps,copies,run,length_sfx x hp]
  | n+1,p,hp => by
    rw [InlineRepeat.steps,compile_eval g x s T E d ps p hp]
    cases hr : run d E ps (sfx x p) with
    | none => simp [copies,CopyBodyEvaluation.run_append,hr]
    | some rest =>
      have hv : evV g x s T E (compile d ps) p=some (some rest.length) := by
        simpa only [hr,Option.map_some] using compile_eval g x s T E d ps p hp
      have hq := evV_ok hT _ p hp _ hv
      have hs : sfx x rest.length=rest :=
        sfx_suffix (suffix_trans (sfx_is_suffix x p) (run_suffix d E ps (sfx x p) rest hr)).choose_spec
      simp only [Option.map_some]
      rw [copies_eval g x s T hT E d ps n rest.length hq]
      simp [copies,CopyBodyEvaluation.run_append,hr,hs]

theorem steps_trace (f : Nat → Res) (limit : Nat)
    (hstep : ∀ p, p≤limit → ∀ q, f p=some (some q) → q<p) :
    ∀ n p, p≤limit → ∀ q, InlineRepeat.steps f n p=some (some q) → InlineRepeat.Trace f p n q
  | 0,p,_,q,h => by cases h; exact .zero p
  | n+1,p,hp,q,h => by
    cases hf : f p with
    | none => simp [InlineRepeat.steps,hf] at h
    | some r => cases r with
      | none => simp [InlineRepeat.steps,hf] at h
      | some z =>
        have hz := hstep p hp z hf
        exact .succ hf hz (steps_trace f limit hstep n z (by omega) q (by simpa [InlineRepeat.steps,hf] using h))

theorem star_total (f : Nat → Res) (limit : Nat)
    (ht : ∀ p, p≤limit → ∃ r, f p=some r)
    (hstep : ∀ p, p≤limit → ∀ q, f p=some (some q) → q<p) :
    ∀ p, p≤limit → ∃ q, q≤p ∧ evStar f p=some (some q) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    obtain ⟨r,hr⟩ := ht p hp
    cases r with
    | none => exact ⟨p,Nat.le_refl _,evStar_fail hr⟩
    | some z =>
      have hz := hstep p hp z hr
      obtain ⟨q,hq,he⟩ := ih z hz (by omega)
      exact ⟨q,by omega,(evStar_ok hr hz).trans he⟩

theorem star_zero_iff (f : Nat → Res) (limit : Nat)
    (hstep : ∀ p, p≤limit → ∀ q, f p=some (some q) → q<p)
    (hend : f 0=some none) (p : Nat) (hp : p≤limit) :
    evStar f p=some (some 0) ↔ ∃ n, InlineRepeat.steps f n p=some (some 0) := by
  constructor
  · intro h
    obtain ⟨n,ht,_⟩ := InlineRepeat.star_trace f p 0 h
    exact ⟨n,InlineRepeat.trace_steps ht⟩
  · rintro ⟨n,hn⟩
    exact InlineRepeat.trace_star (steps_trace f limit hstep n p hp 0 hn) hend

theorem physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (d : Char) (ps : List Part)
    (hprogress : ∀ y rest, run d E ps y=some rest → rest.length<y.length)
    (hend : run d E ps []=none) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (fullStar d ps) p=
      some (if Accept d E ps (sfx x p) then some 0 else none) := by
  classical
  let f := fun q => evV g x s T E (compile d ps) q
  have hstep : ∀ q, q≤x.length → ∀ r, f q=some (some r) → r<q := by
    intro q hq r hr
    rw [show f q=some ((run d E ps (sfx x q)).map List.length) from compile_eval g x s T E d ps q hq] at hr
    cases hv : run d E ps (sfx x q) with
    | none => simp [hv] at hr
    | some rest =>
      have he : rest.length=r := by simpa [hv] using hr
      have hh := hprogress (sfx x q) rest hv
      simpa [he,length_sfx x hq] using hh
  have ht : ∀ q, q≤x.length → ∃ r, f q=some r :=
    fun q hq => ⟨_,compile_eval g x s T E d ps q hq⟩
  have hz : f 0=some none := by simp [f,compile_eval,hend,sfx]
  have he : evStar f p=some (some 0) ↔ Accept d E ps (sfx x p) := by
    rw [star_zero_iff f x.length hstep hz p hp]
    unfold Accept
    apply exists_congr
    intro n
    rw [copies_eval g x s T hT E d ps n p hp]
    cases hr : run d E (copies ps n) (sfx x p) with
    | none => simp
    | some rest => simp
  obtain ⟨q,hq,hstar⟩ := star_total f x.length ht hstep p hp
  have heof : evV g x s T E (.notP .any) q=some (if q=0 then some 0 else none) := by
    cases hs : sfx x q with
    | nil =>
      have h0 : q=0 := by have := length_sfx x (show q≤x.length by omega); rw [hs] at this; simpa using this.symm
      simp [evV,h0,sfx]
    | cons c rest =>
      have hn : q≠0 := by have := length_sfx x (show q≤x.length by omega); rw [hs] at this; simp only [List.length_cons] at this; omega
      simp [evV,hs,hn]
  have hstarV : evV g x s T E (.star (compile d ps)) p=some (some q) := by
    rw [evV_star]; exact hstar
  rw [fullStar,evV_seq_ok hstarV,heof]
  have hiff : q=0 ↔ Accept d E ps (sfx x p) := by simpa [hstar] using he
  simp only [hiff]

end Shallot.MacroPeg.CBV.DelimitedRepeatEvaluation
