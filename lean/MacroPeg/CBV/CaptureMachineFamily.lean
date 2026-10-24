import MacroPeg.CBV.MutualProfiledRecursion

/-! A disjoint union lets one captured-word profile retain the transitions
of every phase machine in a finite family. -/
namespace Shallot.MacroPeg.CBV.CaptureMachineFamily
open RegularCaptureProduct (Machine run)
open CaptureTransitionProfile (profile)

def sum (D E : Machine) : Machine :=
  ⟨D.width+E.width,fun q c => if q<D.width then D.step q c else D.width+E.step (q-D.width) c⟩

theorem sum_valid (D E : Machine) (hD : D.Valid) (hE : E.Valid) : (sum D E).Valid := by
  refine ⟨by have := hD.1; simp only [sum]; omega,?_⟩
  intro q hq c
  change (if q<D.width then D.step q c else D.width+E.step (q-D.width) c)<D.width+E.width
  split
  · have := hD.2 q (by assumption) c; omega
  · have hb : q-D.width<E.width := by change q<D.width+E.width at hq; omega
    have := hE.2 (q-D.width) hb c; omega

theorem run_left (D E : Machine) (hD : D.Valid) (q : Nat) (hq : q<D.width) (w : List Char) :
    run (sum D E) q w=run D q w := by
  induction w generalizing q with
  | nil => rfl
  | cons c w ih =>
    simp only [run,List.foldl_cons]
    change run (sum D E) (if q<D.width then D.step q c else D.width+E.step (q-D.width) c) w=_
    rw [if_pos hq]
    exact ih _ (hD.2 q hq c)

theorem run_right (D E : Machine) (hE : E.Valid) (q : Nat) (hq : q<E.width) (w : List Char) :
    run (sum D E) (D.width+q) w=D.width+run E q w := by
  induction w generalizing q with
  | nil => rfl
  | cons c w ih =>
    simp only [run,List.foldl_cons]
    change run (sum D E) (if D.width+q<D.width then D.step (D.width+q) c else D.width+E.step (D.width+q-D.width) c) w=_
    rw [if_neg (by omega),Nat.add_sub_cancel_left]
    exact ih _ (hE.2 q hq c)

def combine : List Machine → Machine
  | [] => ⟨1,fun _ _ => 0⟩
  | D::Ds => sum D (combine Ds)
def offset : List Machine → Nat → Nat
  | [], _ => 0
  | _::_, 0 => 0
  | D::Ds, i+1 => D.width+offset Ds i

theorem combine_valid : ∀ Ds, (∀ D∈Ds, D.Valid) → (combine Ds).Valid
  | [], _ => ⟨by decide,by intro q _ c; exact Nat.zero_lt_succ 0⟩
  | D::Ds, hs => sum_valid D _ (hs D (by simp)) (combine_valid Ds (fun E hE => hs E (by simp [hE])))

theorem offset_bound : ∀ Ds, (∀ D∈Ds, D.Valid) → ∀ i D, Ds[i]?=some D → ∀ q, q<D.width →
    offset Ds i+q<(combine Ds).width
  | [], _, i, D, hi, _, _ => by simp at hi
  | H::Ds, hs, 0, D, hi, q, hq => by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
    subst D
    have := (combine_valid Ds (fun E hE => hs E (by simp [hE]))).1
    change 0+q<H.width+(combine Ds).width
    omega
  | H::Ds, hs, i+1, D, hi, q, hq => by
    have hb := offset_bound Ds (fun E hE => hs E (by simp [hE])) i D hi q hq
    change H.width+offset Ds i+q<H.width+(combine Ds).width
    omega

theorem run_component : ∀ Ds, (∀ D∈Ds, D.Valid) → ∀ i D, Ds[i]?=some D → ∀ q, q<D.width → ∀ w,
    run (combine Ds) (offset Ds i+q) w=offset Ds i+run D q w
  | [], _, i, D, hi, _, _, _ => by simp at hi
  | H::Ds, hs, 0, D, hi, q, hq, w => by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
    subst D
    simpa only [combine,offset,Nat.zero_add] using run_left H (combine Ds) (hs H (by simp)) q hq w
  | H::Ds, hs, i+1, D, hi, q, hq, w => by
    have ht : ∀ E∈Ds, E.Valid := fun E hE => hs E (by simp [hE])
    change run (sum H (combine Ds)) (H.width+offset Ds i+q) w=H.width+offset Ds i+run D q w
    rw [Nat.add_assoc,run_right H (combine Ds) (combine_valid Ds ht) _ (offset_bound Ds ht i D hi q hq) w,
      run_component Ds ht i D hi q hq w,Nat.add_assoc]

/-- Reading the union profile at a component's embedded start state gives
that component's real transition, without inspecting the captured word. -/
theorem profile_component (Ds : List Machine) (hs : ∀ D∈Ds, D.Valid)
    (i : Nat) (D : Machine) (hi : Ds[i]?=some D) (q : Nat) (hq : q<D.width) (w : List Char) :
    ((profile (combine Ds) w)[offset Ds i+q]?.getD 0)-offset Ds i=run D q w := by
  rw [CaptureTransitionProfile.profile_get _ _ _ (offset_bound Ds hs i D hi q hq),Option.getD_some,
    run_component Ds hs i D hi q hq,Nat.add_sub_cancel_left]

def machines (shifts : List (List Char)) : List Machine := shifts.map PeriodicCaptureMachine.machine
abbrev machine (shifts : List (List Char)) := combine (machines shifts)
abbrev start (shifts : List (List Char)) (i : Nat) := offset (machines shifts) i

theorem phase_valid (u : List Char) : (PeriodicCaptureMachine.machine u).Valid := by
  by_cases hu : u=[]
  · subst u
    exact ⟨by decide,by intro q hq c; simp [PeriodicCaptureMachine.machine,PeriodicCaptureMachine.step]⟩
  · exact PeriodicCaptureMachine.valid u hu

theorem machines_valid (shifts : List (List Char)) : ∀ D∈machines shifts, D.Valid := by
  intro D hD
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hD
  exact phase_valid u

theorem valid (shifts : List (List Char)) : (machine shifts).Valid := combine_valid _ (machines_valid shifts)

theorem phase_profile (shifts : List (List Char)) (i : Nat) (u : List Char) (hi : shifts[i]?=some u) (w : List Char) :
    ((profile (machine shifts) w)[start shifts i]?.getD 0)-start shifts i=
      run (PeriodicCaptureMachine.machine u) 0 w := by
  have hm : (machines shifts)[i]?=some (PeriodicCaptureMachine.machine u) := by simp [machines,hi]
  simpa only [Nat.add_zero] using profile_component (machines shifts) (machines_valid shifts) i _ hm 0
    (phase_valid u).1 w

end Shallot.MacroPeg.CBV.CaptureMachineFamily
