import MacroPeg.CBV.TotalCaptureSafety
import MacroPeg.CBV.ObservedScanner

namespace Shallot.MacroPeg.CBV.ScannerLanguageSafety
open StatefulScanner
abbrev Relation (n : Nat) := Fin n → Fin n → Bool

/-- One finite simulation refinement: every outgoing source arc must have
an actual matching transition from the other state. -/
def refine {n : Nat} (M : Machine n) (R : Relation n) : Relation n := fun q r =>
  (M.arcs q).all (fun (c,t) => (next (M.arcs r) c).any (fun u => R t u))

def rounds {n : Nat} (M : Machine n) : Nat → Relation n
  | 0 => fun _ _ => true
  | k+1 => refine M (rounds M k)

def certificate {n : Nat} (M : Machine n) : Relation n := rounds M (n*n)

/-- Soundness is checked explicitly; no convergence assumption is used. -/
def simulationCheck {n : Nat} (M : Machine n) (R : Relation n) : Bool :=
  (List.finRange n).all (fun q => (List.finRange n).all (fun r => !R q r || refine M R q r))

def safe {n : Nat} (M : Machine n) (q : Fin n) : Bool :=
  simulationCheck M (certificate M) && (List.finRange n).all (fun r => certificate M q r)

private theorem next_mem {Q : Type} (arcs : List (Char × Q)) (c : Char) (t : Q)
    (h : next arcs c=some t) : (c,t)∈arcs := by
  induction arcs with
  | nil => simp [next] at h
  | cons arc arcs ih =>
    obtain ⟨a,r⟩ := arc
    cases hb : Shallot.beqChar a c with
    | false => exact List.mem_cons_of_mem _ (ih (by simpa [next,hb] using h))
    | true =>
      have he : a=c := Char.toNat_inj.mp (by simpa [Shallot.beqChar] using hb)
      subst a
      have hr : r=t := by simpa [next,hb] using h
      subst r
      exact List.mem_cons_self

theorem simulation_step {n : Nat} (M : Machine n) (R : Relation n)
    (hR : simulationCheck M R=true) (q r t : Fin n) (hqr : R q r=true)
    (c : Char) (hstep : next (M.arcs q) c=some t) :
    ∃ u, next (M.arcs r) c=some u ∧ R t u=true := by
  have h := (List.all_eq_true.mp ((List.all_eq_true.mp hR) q (List.mem_finRange q))) r (List.mem_finRange r)
  have hf : refine M R q r=true := by simpa [hqr] using h
  have hh := (List.all_eq_true.mp hf) (c,t) (next_mem (M.arcs q) c t hstep)
  cases hs : next (M.arcs r) c with
  | none => simp [hs] at hh
  | some u => exact ⟨u,rfl,by simpa [hs] using hh⟩

theorem advance_simulation {n : Nat} (M : Machine n) (R : Relation n)
    (hR : simulationCheck M R=true) (w : List Char) (q r t : Fin n)
    (hqr : R q r=true) (h : advance M q w=some t) :
    ∃ u, advance M r w=some u ∧ R t u=true := by
  induction w generalizing q r with
  | nil => cases h; exact ⟨r,rfl,hqr⟩
  | cons c w ih =>
    cases hs : next (M.arcs q) c with
    | none => simp [advance,hs] at h
    | some v =>
      obtain ⟨u,hu,hvu⟩ := simulation_step M R hR q r v hqr c hs
      obtain ⟨z,hz,htz⟩ := ih v u hvu (by simpa [advance,hs] using h)
      exact ⟨z,by simpa [advance,hu] using hz,htz⟩

theorem safe_sound {n : Nat} (M : Machine n) (q : Fin n) (hq : safe M q=true)
    (w : List Char) (t : Fin n) (h : advance M q w=some t) : TotalCaptureSafety.Total M w := by
  have hh := Bool.and_eq_true_iff.mp hq
  intro r hr
  obtain ⟨u,hu,_⟩ := advance_simulation M (certificate M) hh.1 w q r t
    ((List.all_eq_true.mp hh.2) r (List.mem_finRange r)) h
  rw [hr] at hu
  cases hu

theorem advance_consumed {n : Nat} (M : Machine n) (q : Fin n) (xs : List Char) :
    advance M q (ObservedScanner.consumed M q xs)=some (run M q xs).1 := by
  induction xs generalizing q with
  | nil => rfl
  | cons c xs ih =>
    cases hs : next (M.arcs q) c with
    | none => simp [ObservedScanner.consumed,run,advance,hs]
    | some r => simpa [ObservedScanner.consumed,run,advance,hs] using ih r

theorem consumed_total {n : Nat} (M : Machine n) (q : Fin n) (hq : safe M q=true)
    (xs : List Char) : TotalCaptureSafety.Total M (ObservedScanner.consumed M q xs) :=
  safe_sound M q hq _ _ (advance_consumed M q xs)

end Shallot.MacroPeg.CBV.ScannerLanguageSafety
