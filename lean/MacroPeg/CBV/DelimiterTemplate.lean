import MacroPeg.CBV.DelimitedCopyProjection

namespace Shallot.MacroPeg.CBV.DelimiterTemplate
open ClockFreezing (Table)
open DelimitedCopyProjection (Free)

inductive Part where
  | lit (w : List Char) | param (i : Nat) | gap | eof
  deriving Repr

def pred (d c : Char) := decide (c≠d)
def gap (d : Char) : MExp := .star (.seq (.notP (.chr d)) .any)
def exp (d : Char) : Part → MExp
  | .lit w => .lit w | .param i => .param i | .gap => gap d | .eof => .notP .any
def compile (d : Char) : List Part → MExp
  | [] => .eps | p::ps => .seq (exp d p) (compile d ps)
def action (d : Char) (E : List (List Char)) : Part → List Char → Option (List Char)
  | .lit w,x => Shallot.stripPrefix? w x
  | .param i,x => E[i]?.bind (fun w => Shallot.stripPrefix? w x)
  | .gap,x => some (x.dropWhile (pred d))
  | .eof,x => if x=[] then some [] else none

def run (d : Char) (E : List (List Char)) : List Part → List Char → Option (List Char)
  | [],x => some x
  | p::ps,x => (action d E p x).bind (run d E ps)

def full (d : Char) (ps : List Part) := compile d (ps++[.eof])
def Accept (d : Char) (E : List (List Char)) (ps : List Part) (x : List Char) : Prop := run d E (ps++[.eof]) x=some []

instance (d : Char) (E : List (List Char)) (ps : List Part) (x : List Char) : Decidable (Accept d E ps x) :=
  inferInstanceAs (Decidable (run d E (ps++[.eof]) x=some []))

theorem exp_firstOrder (d : Char) : ∀ p, (exp d p).FirstOrder
  | .lit _ | .param _ | .eof => True.intro
  | .gap => ⟨True.intro,True.intro⟩

theorem compile_firstOrder (d : Char) : ∀ ps, (compile d ps).FirstOrder
  | [] => True.intro
  | p::ps => ⟨exp_firstOrder d p,compile_firstOrder d ps⟩

theorem gap_step (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char)) (d : Char) (p : Nat) :
    evV g x s T E (.seq (.notP (.chr d)) .any) p=
      match sfx x p with
      | [] => some none
      | c::rest => if c=d then some none else some (some rest.length) := by
  cases hx : sfx x p with
  | nil => simp [evV,hx]
  | cons c rest =>
    by_cases hc : c=d
    · subst c
      simp [evV,hx,Shallot.beqChar]
    · have hb : Shallot.beqChar d c=false := Bool.eq_false_iff.mpr (fun h => hc ((FiniteSuffixObservedAtoms.beq_char_iff _ _).mp h).symm)
      simp [evV,hx,hb,hc]

theorem gap_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char)) (d : Char) :
    ∀ p, p≤x.length → evV g x s T E (gap d) p=some (some ((sfx x p).dropWhile (pred d)).length) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    rw [gap,evV_star]
    cases hx : sfx x p with
    | nil =>
      rw [evStar_fail (by rw [gap_step,hx])]
      have hl := length_sfx x hp
      rw [hx] at hl
      simp only [List.length_nil] at hl
      simp [hl]
    | cons c rest =>
      have hl := length_sfx x hp
      rw [hx,List.length_cons] at hl
      by_cases hc : c=d
      · rw [evStar_fail (by simp only [gap_step,hx]; simp [hc])]
        simp [pred,hc,hl]
      · rw [evStar_ok (j := rest.length) (by simp only [gap_step,hx]; simp [hc]) (by omega)]
        have hs : sfx x rest.length=rest := by
          obtain ⟨headPart,he⟩ := sfx_is_suffix x p
          apply sfx_suffix (pre := headPart++[c])
          rw [hx] at he
          simpa [List.append_assoc] using he
        have hh := ih rest.length (by omega) (by omega)
        change evStar (fun q => evV g x s T E (.seq (.notP (.chr d)) .any) q) rest.length=_ at hh ⊢
        rw [hs] at hh
        simpa [pred,hc] using hh

theorem action_suffix (d : Char) (E : List (List Char)) (p : Part) (x rest : List Char)
    (h : action d E p x=some rest) : ∃ a, x=a++rest := by
  cases p with
  | lit w => exact ⟨w,(CBVtoCBN.stripPrefix_exact _ _ _).mp h⟩
  | param i =>
    cases hw : E[i]? with
    | none => simp [action,hw] at h
    | some w => exact ⟨w,(CBVtoCBN.stripPrefix_exact _ _ _).mp (by simpa [action,hw] using h)⟩
  | gap =>
    have hr : rest=x.dropWhile (pred d) := by simpa [action] using h.symm
    exact ⟨x.takeWhile (pred d),hr ▸ (List.takeWhile_append_dropWhile).symm⟩
  | eof =>
    by_cases hx : x=[]
    · simp [action,hx] at h; subst rest; exact ⟨[],hx⟩
    · simp [action,hx] at h

theorem action_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (d : Char) (a : Part) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (exp d a) p=some ((action d E a (sfx x p)).map List.length) := by
  cases a with
  | lit w => cases h : Shallot.stripPrefix? w (sfx x p) <;> simp [exp,action,evV,h]
  | param i =>
    cases h : E[i]? with
    | none => simp [exp,action,evV,h]
    | some w => cases hs : Shallot.stripPrefix? w (sfx x p) <;> simp [exp,action,evV,h,hs]
  | gap => exact gap_eval g x s T E d p hp
  | eof =>
    cases hx : sfx x p with
    | nil =>
      have hl := length_sfx x hp
      rw [hx] at hl
      simp only [List.length_nil] at hl
      simp [exp,action,evV,hx,hl]
    | cons c rest => simp [exp,action,evV,hx]

theorem compile_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (d : Char) : ∀ ps p, p≤x.length →
    evV g x s T E (compile d ps) p=some ((run d E ps (sfx x p)).map List.length)
  | [],p,hp => by simp [compile,run,evV,length_sfx x hp]
  | a::ps,p,hp => by
    have hh := action_eval g x s T E d a p hp
    cases ha : action d E a (sfx x p) with
    | none => simp only [ha,Option.map_none] at hh; rw [compile,evV_seq_fail hh]; simp [run,ha]
    | some rest =>
      simp only [ha,Option.map_some] at hh
      have hs : ∃ prefixPart, x=prefixPart++rest := suffix_trans (sfx_is_suffix x p) (action_suffix d E a (sfx x p) rest ha)
      have hp' : rest.length≤x.length := by obtain ⟨a,ha⟩ := hs; rw [ha,List.length_append]; omega
      rw [compile,evV_seq_ok hh,compile_eval g x s T E d ps rest.length hp',sfx_suffix hs.choose_spec]
      simp [run,ha]

theorem run_full_results (d : Char) (E : List (List Char)) : ∀ ps x rest,
    run d E (ps++[.eof]) x=some rest → rest=[]
  | [],x,rest,h => by
    by_cases hx : x=[]
    · simpa [run,action,hx] using h.symm
    · simp [run,action,hx] at h
  | a::ps,x,rest,h => by
    cases ha : action d E a x with
    | none => simp [run,ha] at h
    | some z => exact run_full_results d E ps z rest (by simpa [run,ha] using h)

theorem full_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (d : Char) (ps : List Part) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (full d ps) p=if Accept d E ps (sfx x p) then some (some 0) else some none := by
  rw [full,compile_eval g x s T E d _ p hp]
  cases h : run d E (ps++[.eof]) (sfx x p) with
  | none => simp [Accept,h]
  | some rest =>
    have hr := run_full_results d E ps _ rest h
    subst rest
    simp [Accept,h]

end Shallot.MacroPeg.CBV.DelimiterTemplate
