import MacroPeg.CBV.ExactWordCaptureMachine

namespace Shallot.MacroPeg.CBV.FiniteSuffixReplay
open ClockFreezing (Table)

def prefixes : List Char → List (List Char)
  | [] => [[]]
  | c::w => []::(prefixes w).map (List.cons c)

theorem mem_prefixes (u v : List Char) : u∈prefixes v ↔ u.IsPrefix v := by
  induction v generalizing u with
  | nil => cases u <;> simp [prefixes]
  | cons c v ih =>
    cases u with
    | nil => simp [prefixes]
    | cons d u =>
      by_cases he : c=d
      · subst d; simp [prefixes,ih,List.cons_prefix_cons]
      · simp [prefixes,List.cons_prefix_cons,he,Ne.symm he]

def palette (R : List (List Char)) := (R.flatMap prefixes).eraseDups

theorem prefix_mem (R : List (List Char)) (u v : List Char) (hv : v∈R) (hu : u.IsPrefix v) : u∈palette R :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨v,hv,(mem_prefixes u v).mpr hu⟩)

def observe (R : List (List Char)) (w : List Char) : Option (List Char) := if w∈palette R then some w else none
def views (R : List (List Char)) (E : List (List Char)) := E.map (observe R)

def probe (w : List Char) : MExp := .andP (.seq (.lit w) (.notP .any))
def guard : List (List Char) → MExp
  | [] => MExp.failAlways
  | w::R => .alt (probe w) (guard R)

theorem probe_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (w : List Char) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (probe w) p=if sfx x p=w then some (some p) else some none := by
  cases hv : Shallot.stripPrefix? w (sfx x p) with
  | none =>
    have hn : sfx x p≠w := by
      intro he
      have hh : Shallot.stripPrefix? w (sfx x p)=some [] := (CBVtoCBN.stripPrefix_exact _ _ _).mpr (by simpa using he)
      rw [hv] at hh; cases hh
    rw [probe,CallLookahead.evV_peek,evV_seq_fail (show evV g x s T E (.lit w) p=some none from by simp [evV,hv])]
    simp [CallLookahead.peek,hn]
  | some rest =>
    have hs := (CBVtoCBN.stripPrefix_exact _ _ _).mp hv
    have hr := suffix_trans (sfx_is_suffix x p) ⟨w,hs⟩
    have hsf : sfx x rest.length=rest := sfx_suffix hr.choose_spec
    have hl : evV g x s T E (.lit w) p=some (some rest.length) := by simp [evV,hv]
    rw [probe,CallLookahead.evV_peek,evV_seq_ok hl]
    cases rest with
    | nil =>
      simp only [List.length_nil] at hsf
      simp [evV,hsf,CallLookahead.peek,hs]
    | cons c rest =>
      simp only [List.length_cons] at hsf
      have hn : sfx x p≠w := by
        intro he
        have hh := congrArg List.length hs
        rw [he,List.length_append,List.length_cons] at hh
        omega
      simp [evV,hsf,CallLookahead.peek,hn]

theorem guard_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (R : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (guard R) p=if sfx x p∈R then some (some p) else some none := by
  induction R with
  | nil => simp [guard,MExp.failAlways,evV]
  | cons w R ih =>
    have hh := probe_eval g x s T E w p hp
    by_cases he : sfx x p=w
    · rw [if_pos he] at hh
      rw [guard,evV_alt_ok hh]; simp [he]
    · rw [if_neg he] at hh
      rw [guard,evV_alt_fail hh,ih]; simp [he]

theorem outside_cannot_match (R : List (List Char)) (w v : List Char)
    (hw : w∉palette R) (hv : v∈R) : Shallot.stripPrefix? w v=none := by
  cases he : Shallot.stripPrefix? w v with
  | none => rfl
  | some rest =>
    have hh := (CBVtoCBN.stripPrefix_exact _ _ _).mp he
    exact False.elim (hw (prefix_mem R w v hv ⟨rest,hh.symm⟩))

def literal (V : List (Option (List Char))) (i : Nat) : MExp :=
  match V[i]?.join with | none => MExp.failAlways | some w => .lit w

/-- Arbitrary retained words are permitted. Only replays whose current
remaining input is one of the fixed suffixes are abstracted. -/
theorem replay_eval (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table) (E : List (List Char))
    (R : List (List Char)) (i p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (guard R) (.param i)) p=
      evV h x t U [] (.seq (guard R) (literal (views R E) i)) p := by
  have hg := guard_eval g x s T E R p hp
  have hh := guard_eval h x t U [] R p hp
  by_cases hv : sfx x p∈R
  · rw [if_pos hv] at hg hh
    rw [evV_seq_ok hg,evV_seq_ok hh]
    cases he : E[i]? with
    | none => simp [evV,literal,views,List.getElem?_map,he,MExp.failAlways]
    | some w =>
      by_cases hw : w∈palette R
      · simp [evV,literal,views,List.getElem?_map,he,observe,hw]
      · have hn := outside_cannot_match R w (sfx x p) hw hv
        simp [evV,literal,views,List.getElem?_map,he,observe,hw,hn,MExp.failAlways]
  · rw [if_neg hv] at hg hh
    rw [evV_seq_fail hg,evV_seq_fail hh]

theorem probe_firstOrder (w : List Char) : (probe w).FirstOrder := by trivial

theorem guard_firstOrder : ∀ R, (guard R).FirstOrder
  | [] => True.intro
  | w::R => ⟨probe_firstOrder w,guard_firstOrder R⟩

theorem literal_firstOrder (V : List (Option (List Char))) (i : Nat) : (literal V i).FirstOrder := by
  unfold literal
  split <;> trivial


def suffixes (alphabet : List Char) (bound : Nat) :=
  (List.range (bound+1)).flatMap (fun k => words alphabet k)

theorem mem_suffixes (alphabet : List Char) (bound : Nat) (w : List Char) :
    w∈suffixes alphabet bound ↔ w.length≤bound ∧ ∀ c∈w, c∈alphabet := by
  constructor
  · intro hw
    obtain ⟨k,hk,hw⟩ := List.mem_flatMap.mp hw
    have hh := (mem_words _ _ _).mp hw
    exact ⟨by have hk := List.mem_range.mp hk; omega,hh.2⟩
  · rintro ⟨hl,hw⟩
    exact List.mem_flatMap.mpr ⟨w.length,List.mem_range.mpr (by omega),(mem_words _ _ _).mpr ⟨rfl,hw⟩⟩

theorem bounded_guard_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (alphabet : List Char) (bound p : Nat) (hp : p≤x.length) :
    evV g x s T E (guard (suffixes alphabet bound)) p=
      if p≤bound ∧ (∀ c∈sfx x p, c∈alphabet) then some (some p) else some none := by
  rw [guard_eval g x s T E _ p hp]
  simp only [mem_suffixes,length_sfx x hp]


theorem palette_length_bound (R : List (List Char)) (bound : Nat)
    (hR : ∀ v∈R, v.length≤bound) (w : List Char) (hw : w∈palette R) : w.length≤bound := by
  obtain ⟨v,hv,hw⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hw)
  exact Nat.le_trans ((mem_prefixes w v).mp hw).length_le (hR v hv)

theorem long_word_is_other (R : List (List Char)) (bound : Nat)
    (hR : ∀ v∈R, v.length≤bound) (w : List Char) (hw : bound<w.length) : observe R w=none := by
  have hn : w∉palette R := fun h => Nat.not_lt_of_le (palette_length_bound R bound hR w h) hw
  simp [observe,hn]

end Shallot.MacroPeg.CBV.FiniteSuffixReplay
