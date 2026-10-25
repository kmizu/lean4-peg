import MacroPeg.CBV.FiniteSuffixObservedCompiler

/-! Metadata for output filtering while keeping the actual unbounded words.
Exact prefix views alone do not determine a word DFA's transfer from an
intermediate state. Exact substring views do. -/
namespace Shallot.MacroPeg.CBV.SubstringCaptureView
open RegularCaptureProduct (run)
open ExactWordCaptureMachine (machine)

/-- Finite suffix closure; its prefix palette contains all seed substrings. -/
def region (seeds : List (List Char)) := seeds.flatMap (fun w =>
  (List.range (w.length+1)).map (fun k => w.drop k))
def dictionary (seeds : List (List Char)) := FiniteSuffixReplay.palette (region seeds)
def observe (seeds : List (List Char)) := FiniteSuffixReplay.observe (region seeds)

theorem mem_dictionary (seeds : List (List Char)) (w : List Char) :
    w∈dictionary seeds ↔ ∃ v∈seeds, ∃ a b, v=a++w++b := by
  constructor
  · intro hw
    obtain ⟨s,hs,hp⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hw)
    obtain ⟨v,hv,hm⟩ := List.mem_flatMap.mp hs
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    obtain ⟨b,hb⟩ := (FiniteSuffixReplay.mem_prefixes w (v.drop k)).mp hp
    refine ⟨v,hv,v.take k,b,?_⟩
    rw [List.append_assoc,hb]
    exact (List.take_append_drop k v).symm
  · rintro ⟨v,hv,a,b,he⟩
    apply List.mem_eraseDups.mpr
    apply List.mem_flatMap.mpr
    refine ⟨v.drop a.length,?_,(FiniteSuffixReplay.mem_prefixes _ _).mpr ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨v,hv,List.mem_map.mpr ⟨a.length,List.mem_range.mpr ?_,rfl⟩⟩
      rw [he,List.length_append,List.length_append]
      omega
    · rw [he,List.append_assoc,List.drop_left]
      exact ⟨b,rfl⟩

/-- Substrings of candidates stay in the same finite dictionary. -/
theorem substring_closed (seeds : List (List Char)) (u : List Char) (hu : u∈dictionary seeds)
    (w : List Char) (q : Nat) (hw : w.IsPrefix (u.drop q)) : w∈dictionary seeds := by
  obtain ⟨v,hv,a,b,hvab⟩ := (mem_dictionary seeds u).mp hu
  obtain ⟨tail,ht⟩ := hw
  apply (mem_dictionary seeds w).mpr
  refine ⟨v,hv,a++u.take q,tail++b,?_⟩
  calc
    v = a++(u.take q++u.drop q)++b := by rw [List.take_append_drop,hvab]
    _ = (a++u.take q)++w++(tail++b) := by rw [←ht]; simp [List.append_assoc]

theorem outside_run_sink (seeds : List (List Char)) (u : List Char) (hu : u∈dictionary seeds)
    (w : List Char) (hw : w∉dictionary seeds) (q : Nat) (hq : q<(machine u).width) :
    run (machine u) q w=u.length+1 := by
  by_cases hl : q≤u.length
  · rw [ExactWordCaptureMachine.run_prefix u w q hl]
    exact if_neg (fun hp => hw (substring_closed seeds u hu w q hp))
  · have hq' : q=u.length+1 := by simp only [machine] at hq; omega
    rw [hq',ExactWordCaptureMachine.run_sink]

def advance (u : List Char) (q : Nat) : Option (List Char) → Nat
  | some w => run (machine u) q w
  | none => u.length+1

/-- Finite metadata determines every DFA transition while the actual word
remains available for unrestricted replay at arbitrary input positions. -/
theorem advance_observe (seeds : List (List Char)) (u : List Char) (hu : u∈dictionary seeds)
    (w : List Char) (q : Nat) (hq : q<(machine u).width) :
    advance u q (observe seeds w)=run (machine u) q w := by
  change advance u q (if w∈dictionary seeds then some w else none)=_
  by_cases hw : w∈dictionary seeds
  · rw [if_pos hw]; rfl
  · rw [if_neg hw]
    exact (outside_run_sink seeds u hu w hw q hq).symm

end Shallot.MacroPeg.CBV.SubstringCaptureView
