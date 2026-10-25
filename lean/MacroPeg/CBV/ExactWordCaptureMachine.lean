import MacroPeg.CBV.CaptureMachineFamily

/-! Exact finite-word output observations. Unlike periodic phase summaries,
finishing the word is not an accepting loop: one extra character goes dead. -/
namespace Shallot.MacroPeg.CBV.ExactWordCaptureMachine
open RegularCaptureProduct (Machine run)

def step (u : List Char) (q : Nat) (c : Char) : Nat :=
  if q<u.length ∧ u[q]?=some c then q+1 else u.length+1

def machine (u : List Char) : Machine := ⟨u.length+2,step u⟩

theorem valid (u : List Char) : (machine u).Valid := by
  refine ⟨by simp [machine],?_⟩
  intro q hq c
  simp only [machine,step]
  split <;> omega

theorem run_sink (u w : List Char) : run (machine u) (u.length+1) w=u.length+1 := by
  induction w with
  | nil => rfl
  | cons c w ih => simpa [run,List.foldl_cons,machine,step] using ih

/-- Every nonsink state records the number of matched literal characters. -/
theorem run_prefix (u : List Char) : ∀ w q, q≤u.length →
    run (machine u) q w=if w.IsPrefix (u.drop q) then q+w.length else u.length+1
  | [],q,hq => by simp [run]
  | c::w,q,hq => by
    simp only [run,List.foldl_cons,machine]
    by_cases hl : q<u.length
    · have hd := List.drop_eq_getElem_cons hl
      by_cases hc : u[q]=c
      · have hg : u[q]?=some c := by simp [List.getElem?_eq_getElem hl,hc]
        rw [step,if_pos ⟨hl,hg⟩]
        change run (machine u) (q+1) w=_
        rw [run_prefix u w (q+1) (by omega)]
        simp only [hd,hc,List.cons_prefix_cons,true_and,List.length_cons]
        split <;> omega
      · have hg : u[q]?≠some c := by
          intro he
          have hh : u[q]=c := by simpa only [List.getElem?_eq_getElem hl,Option.some.injEq] using he
          exact hc hh
        rw [step,if_neg (by simp [hg])]
        change run (machine u) (u.length+1) w=_
        rw [run_sink]
        have hh : ¬(c::w).IsPrefix (u.drop q) := by
          rw [hd,List.cons_prefix_cons]
          exact fun h => hc h.1.symm
        simp [hh]
    · have he : q=u.length := by omega
      subst q
      rw [step,if_neg (by omega)]
      change run (machine u) (u.length+1) w=_
      rw [run_sink]
      simp

theorem run_exact (u w : List Char) : run (machine u) 0 w=u.length ↔ w=u := by
  rw [run_prefix u w 0 (by omega)]
  simp only [List.drop_zero,Nat.zero_add]
  by_cases hp : w.IsPrefix u
  · rw [if_pos hp]
    constructor
    · intro hl
      obtain ⟨tail,he⟩ := hp
      have hh := congrArg List.length he
      rw [List.length_append] at hh
      have ht : tail=[] := List.length_eq_zero_iff.mp (by omega)
      simpa [ht] using he
    · intro he; simp [he]
  · rw [if_neg hp]
    constructor
    · omega
    · intro he; subst w; exact False.elim (hp (List.prefix_refl _))

/-- A disjoint family exposes one equality bit for each finite candidate.
The actual captured word is not assumed to belong to the candidate list. -/
def machines (ws : List (List Char)) := ws.map machine
def observer (ws : List (List Char)) := CaptureMachineFamily.combine (machines ws)
def start (ws : List (List Char)) (i : Nat) := CaptureMachineFamily.offset (machines ws) i

theorem machines_valid (ws : List (List Char)) : ∀ D∈machines ws, D.Valid := by
  intro D hD
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hD
  exact valid u

theorem observer_valid (ws : List (List Char)) : (observer ws).Valid :=
  CaptureMachineFamily.combine_valid _ (machines_valid ws)

theorem start_bound (ws : List (List Char)) (i : Nat) (u : List Char) (hi : ws[i]?=some u) :
    start ws i<(observer ws).width := by
  simpa only [start,observer,Nat.add_zero] using CaptureMachineFamily.offset_bound (machines ws) (machines_valid ws) i (machine u)
    (by simp [machines,List.getElem?_map,hi]) 0 (by simp [machine])

theorem accept_bound (ws : List (List Char)) (i : Nat) (u : List Char) (hi : ws[i]?=some u) :
    start ws i+u.length<(observer ws).width := by
  exact CaptureMachineFamily.offset_bound (machines ws) (machines_valid ws) i (machine u)
    (by simp [machines,List.getElem?_map,hi]) u.length (by simp [machine])

theorem observes_exact (ws : List (List Char)) (i : Nat) (u w : List Char) (hi : ws[i]?=some u) :
    run (observer ws) (start ws i) w=start ws i+u.length ↔ w=u := by
  have hh := CaptureMachineFamily.run_component (machines ws) (machines_valid ws) i (machine u)
    (by simp [machines,List.getElem?_map,hi]) 0 (by simp [machine]) w
  simp only [Nat.add_zero] at hh
  simp only [observer,start]
  rw [hh]
  exact (Nat.add_left_cancel_iff).trans (run_exact u w)

end Shallot.MacroPeg.CBV.ExactWordCaptureMachine
