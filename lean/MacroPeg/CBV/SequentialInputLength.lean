import MacroPeg.CBV.SequentialSeedMachine

/-! Recover the original input length by counting numeric field markers, then
restore the complete input encoding before initializing the evaluator. -/
namespace Shallot.MacroPeg.CBV.SequentialInputLength
open Complexity Complexity.BinaryWord

def state (X R : List Nat) (w : Nat) : Lists 20 := fun i =>
  if i=11 then X else if i=0 then R else if i=13 then List.replicate w 1 else []

def mark (v : Nat) : Nat := if v=2 then 1 else 0

def body : LProg 20 := .seq (.ite 11 (· == 6) (.push 13 1) (skipP 13)) (moveTop 11 0)
def scan : LProg 20 := .loop 11 nonEmpty body

def program : LProg 20 := .seq scan (moveAll 0 11)

private theorem fits {X R : List Nat} {w B : Nat}
    (hX : X.length+2 ≤ B) (hR : R.length+2 ≤ B) (hw : w+2 ≤ B) : LenOK B (state X R w) := by
  intro i
  by_cases h11 : i=11 <;> by_cases h0 : i=0 <;> by_cases h13 : i=13 <;>
    simp_all [state] <;> omega

private theorem count_cons (v : Nat) (vs : List Nat) :
    (v::vs).count 2 = vs.count 2+mark v := by
  by_cases hv : v=2 <;> simp [mark,hv,Nat.add_comm]

private theorem body_runs (v : Nat) (vs R : List Nat) (w : Nat) {B : Nat}
    (hR : R.length+vs.length+3 ≤ B) (hw : w+(v::vs).count 2+3 ≤ B) :
    Complexity.Runs (LenOK B) body (state (vs.reverse++[v]) R w)
      (state vs.reverse (R++[v]) (w+mark v)) 4 := by
  let S := state (vs.reverse++[v]) R w
  let M := state (vs.reverse++[v]) R (w+mark v)
  have hc := count_cons v vs
  have hS : LenOK B S := fits (by simp; omega) (by omega) (by omega)
  have hM : LenOK B M := fits (by simp; omega) (by omega) (by omega)
  have ht : lastSym (S 11) = v+4 := by simp [S,state,lastSym]
  have hguard : Complexity.Runs (LenOK B) (.ite 11 (· == 6) (.push 13 1) (skipP 13)) S M 2 := by
    by_cases hv : v=2
    · have he : S.set 13 (S 13++[1]) = M := by
        funext i
        by_cases h13 : i=13 <;> simp_all [S,M,state,mark,Lists.set,← List.replicate_append_replicate]
      have hp := runs_push (i := 13) (e := 1) hS (by rw [he]; exact hM)
      rw [he] at hp
      exact hp.iteT hS (by simp [ht,hv])
    · have he : M=S := by simp [M,S,mark,hv]
      rw [he]
      exact (runs_skip 13 hS).iteF hS (by simp [ht]; omega)
  have hh := lenOK_moveTop (i := (11 : Fin 20)) (j := 0) hM (by decide) (by simp [M,state]; omega)
  have hm := runs_moveTop (i := (11 : Fin 20)) (j := 0) (by decide) hM hh.1 hh.2
  have he : M.moveTop 11 0 = state vs.reverse (R++[v]) (w+mark v) := by
    funext i
    by_cases h11 : i=11 <;> by_cases h0 : i=0 <;> by_cases h13 : i=13 <;>
      simp_all [M,state,Lists.moveTop,Lists.set]
  rw [he] at hm
  exact hguard.seq hm

theorem scan_runs (vs R : List Nat) (w : Nat) {B : Nat}
    (hR : R.length+vs.length+2 ≤ B) (hw : w+vs.count 2+3 ≤ B) :
    ∃ T, Complexity.Runs (LenOK B) scan (state vs.reverse R w)
      (state [] (R++vs) (w+vs.count 2)) T := by
  induction vs generalizing R w with
  | nil =>
    have hh : LenOK B (state [] R w) := fits (by omega) (by simpa using hR) (by simpa using Nat.le_trans (Nat.le_succ _) hw)
    exact ⟨1,by simpa using (show Complexity.Runs (LenOK B) scan (state [] R w) (state [] R w) 1 from
      ⟨1,Nat.le_refl _,.loopF hh rfl⟩)⟩
  | cons v vs ih =>
    have hc := count_cons v vs
    have hb := body_runs v vs R w (by simpa [Nat.add_assoc] using hR) hw
    obtain ⟨U,hu⟩ := ih (R++[v]) (w+mark v) (by simp; simp at hR; omega) (by omega)
    have he : state [] ((R++[v])++vs) (w+mark v+vs.count 2) = state [] (R++(v::vs)) (w+(v::vs).count 2) := by
      have hn : w+mark v+vs.count 2 = w+(v::vs).count 2 := by omega
      simp [hn,List.append_assoc]
    rw [he] at hu
    obtain ⟨t,_,hx⟩ := hb
    obtain ⟨u,_,hy⟩ := hu
    have ht : nonEmpty (lastSym (state (vs.reverse++[v]) R w 11)) = true := by simp [state,lastSym,nonEmpty]
    exact ⟨t+1+u,t+1+u,Nat.le_refl _,by simpa only [List.reverse_cons,scan] using LExec.loopC hx.q_start ht hx hy⟩

def space (X : List Nat) : Nat := X.length+4

theorem runs (X : List Nat) :
    ∃ T, Complexity.Runs (LenOK (space X)) program (state X [] 0)
      (SequentialInitializationNumbers.seed (X.count 2) X) T := by
  have hc := List.count_le_length (a := 2) (l := X)
  obtain ⟨T,hr⟩ := scan_runs X.reverse [] 0 (B := space X) (by simp [space]) (by simp [space]; omega)
  simp only [List.reverse_reverse,List.count_reverse,List.nil_append,Nat.zero_add] at hr
  have hS : LenOK (space X) (state [] X.reverse (X.count 2)) := by
    obtain ⟨_,_,he⟩ := hr
    exact he.q_end _ (Or.inl rfl)
  have hm := moveAll_runs_bounded (src := (0 : Fin 20)) (dst := 11) (by decide) hS (by simp [state,space])
  have he : ((state [] X.reverse (X.count 2)).set 11
      (state [] X.reverse (X.count 2) 11++(state [] X.reverse (X.count 2) 0).reverse)).set 0 [] =
      SequentialInitializationNumbers.seed (X.count 2) X := by
    funext i
    by_cases h11 : i=11 <;> by_cases h0 : i=0 <;> by_cases h13 : i=13 <;>
      simp_all [state,SequentialInitializationNumbers.seed,Lists.set]
  rw [he] at hm
  exact ⟨_,hr.seq hm⟩

theorem encS_count (vs : List Nat) : (Complexity.encS vs).count 2 = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [Complexity.encS,encN,List.count_append,List.count_replicate] using congrArg Nat.succ ih

theorem original_runs (x : List Char) :
    ∃ T, Complexity.Runs (LenOK (space (Complexity.encS (SequentialInputRead.codes x)))) program
      (state (Complexity.encS (SequentialInputRead.codes x)) [] 0)
      (SequentialInitializationNumbers.seed x.length (Complexity.encS (SequentialInputRead.codes x))) T := by
  simpa only [encS_count,SequentialInputRead.codes,List.length_map] using runs (Complexity.encS (SequentialInputRead.codes x))

theorem space_linear (x : List Char) :
    space (Complexity.encS (SequentialInputRead.codes x)) ≤ (2^32+5)*(x.length+1) := by
  have hh := SequentialInputRead.encoded_length x
  unfold space
  omega

end Shallot.MacroPeg.CBV.SequentialInputLength
