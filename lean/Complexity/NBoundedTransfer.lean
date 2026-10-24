import Complexity.NShrinkingCompare

/-! Transfers annotated directly with their intermediate space bound.
A long input traversal does not need a time-to-space growth estimate. -/
namespace Complexity.NBoundedTransfer
variable {K B : Nat}

abbrev FitsRuns (B : Nat) (p : NProg K) (S S' : Lists K) (T : Nat) :=
  ∃ t, t ≤ T ∧ NExec (NFits B) p S t (.cont S')

theorem FitsRuns.seq {p q : NProg K} {S S₁ S₂ : Lists K} {T U : Nat}
    (h : FitsRuns B p S S₁ T) (h' : FitsRuns B q S₁ S₂ U) : FitsRuns B (.seq p q) S S₂ (T+U) := by
  obtain ⟨t,ht,h⟩ := h
  obtain ⟨u,hu,h'⟩ := h'
  exact ⟨t+u,by omega,.seqC h h'⟩

theorem replace {S : Lists K} (h : NFits B S) (i : Fin K) (l : List Nat)
    (hl : (encS l).length+2 ≤ B) : NFits B (S.set i l) := by
  refine ⟨h.1,fun j => ?_⟩
  by_cases hj : j=i
  · subst j; simpa using hl
  · rw [Lists.set_ne _ _ hj]; exact h.2 j

theorem reverse_length (l : List Nat) : (encS l.reverse).length = (encS l).length := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [List.reverse_cons,length_encS_snoc,ih]
    simp [encS,encN]
    omega

theorem take_length_le (l : List Nat) (n : Nat) : (encS (l.take n)).length ≤ (encS l).length := by
  have hh := length_encS_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at hh
  omega

theorem drop_length_le (l : List Nat) (n : Nat) : (encS (l.drop n)).length ≤ (encS l).length := by
  have hh := length_encS_append (l.take n) (l.drop n)
  rw [List.take_append_drop] at hh
  omega

theorem move_runs (i j : Fin K) (hij : i ≠ j) (S : Lists K) (l : List Nat) (v : Nat)
    (hi : S i = l ++ [v]) (hS : NFits B S)
    (hF : NFits B ((S.set j (S j ++ [v])).set i l)) :
    FitsRuns B (nmv i j hij) S ((S.set j (S j ++ [v])).set i l) 2 := by
  let A := S.set j (S j ++ [v])
  have hA : NFits B A := replace hS j _ (by simpa [Lists.set_ne _ _ (Ne.symm hij)] using hF.2 j)
  have hdup : NExec (NFits B) (.prim (.dup i j hij)) S 1 (.cont A) := by
    simpa [NPrim.apply,hi,A] using (NExec.prim hS (show NFits B ((NPrim.dup i j hij).apply S) by
      simpa [NPrim.apply,hi,A] using hA))
  have hpop : (NPrim.pop i).apply A = A.set i l := by simp [NPrim.apply,A,Lists.set_ne _ _ hij,hi]
  have hx : NExec (NFits B) (.prim (.pop i)) A 1 (.cont (A.set i l)) := by
    rw [← hpop]
    exact .prim hA (by rwa [hpop])
  exact ⟨2,by omega,.seqC hdup hx⟩

theorem family {i : Fin K} {c : NTest} {p : NProg K} (F : Nat → Lists K) (n T : Nat)
    (hQ : ∀ m, m ≤ n → NFits B (F m))
    (htest : ∀ m, m < n → c.eval (F m i) = true) (hstop : c.eval (F n i) = false)
    (hbody : ∀ m, m < n → FitsRuns B p (F m) (F (m+1)) T) :
    ∀ r m, m+r=n → FitsRuns B (.loop i c p) (F m) (F n) (r*(T+1)+1)
  | 0,m,he => by
    obtain rfl : m=n := by omega
    exact ⟨1,by simp,.loopF (hQ m (by omega)) hstop⟩
  | r+1,m,he => by
    obtain ⟨t,ht,hb⟩ := hbody m (by omega)
    obtain ⟨u,hu,hr⟩ := family F n T hQ htest hstop hbody r (m+1) (by omega)
    exact ⟨t+1+u,by rw [Nat.succ_mul]; omega,.loopC (hQ m (by omega)) (htest m (by omega)) hb hr⟩

def moveCount (i j c : Fin K) (hij : i ≠ j) : NProg K :=
  .loop c .pos (.seq (nmv i j hij) (.prim (.dec c)))

theorem counted_runs (i j c : Fin K) (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c)
    (vs R D C : List Nat) (S : Lists K)
    (hi : S i = R ++ vs.reverse) (hj : S j = D) (hc : S c = C ++ [vs.length])
    (hS : NFits B S) (hEnd : NFits B (((S.set i R).set j (D ++ vs)).set c (C ++ [0]))) :
    FitsRuns B (moveCount i j c hij) S (((S.set i R).set j (D ++ vs)).set c (C ++ [0])) (4*vs.length+1) := by
  let F := fun m => ((S.set i (R ++ (vs.drop m).reverse)).set j (D ++ vs.take m)).set c (C ++ [vs.length-m])
  have h0 : F 0 = S := by
    funext x
    by_cases hx : x=c
    · subst x; simp [F,hc]
    · by_cases hy : x=j
      · subst x; simp [F,Lists.set,hjc,hj]
      · by_cases hz : x=i
        · subst x; simp [F,Lists.set,hic,hij,hi]
        · simp [F,Lists.set,hx,hy,hz]
  have hn : F vs.length = ((S.set i R).set j (D ++ vs)).set c (C ++ [0]) := by simp [F]
  have hQ : ∀ m, m ≤ vs.length → NFits B (F m) := by
    intro m hm
    refine ⟨hS.1,fun x => ?_⟩
    by_cases hx : x=c
    · subst x
      have hh := hS.2 c
      rw [hc,length_encS_snoc] at hh
      simp only [F,Lists.set_same,length_encS_snoc]
      omega
    · by_cases hy : x=j
      · subst x
        have hh := hEnd.2 j
        have ht := take_length_le vs m
        simp only [Lists.set_ne _ _ hjc,Lists.set_same,length_encS_append] at hh
        simp only [F,Lists.set_ne _ _ hjc,Lists.set_same,length_encS_append]
        omega
      · by_cases hz : x=i
        · subst x
          have hh := hS.2 i
          rw [hi,length_encS_append,reverse_length] at hh
          have hd := drop_length_le vs m
          simp only [F,Lists.set_ne _ _ hic,Lists.set_ne _ _ hij,Lists.set_same,length_encS_append,reverse_length]
          omega
        · simpa [F,Lists.set,hx,hy,hz] using hS.2 x
  have hrun := family (i := c) (c := .pos) (p := .seq (nmv i j hij) (.prim (.dec c))) F vs.length 3 hQ
    (fun m hm => by
      simp only [F,Lists.set_same]
      have he : vs.length-m = (vs.length-m-1)+1 := by omega
      rw [he]
      exact eval_pos_succ C _) (by
      simp only [F,Lists.set_same,Nat.sub_self]
      exact eval_pos_zero C) (fun m hm => by
      have hd : vs.drop m = vs[m] :: vs.drop (m+1) := List.drop_eq_getElem_cons hm
      have ht : vs.take (m+1) = vs.take m ++ [vs[m]] := List.take_succ_eq_append_getElem hm
      let G := ((F m).set j (F m j ++ [vs[m]])).set i (R ++ (vs.drop (m+1)).reverse)
      have heG : G = (F (m+1)).set c (C ++ [vs.length-m]) := by
        funext x
        by_cases hx : x=c
        · subst x
          simp only [G,Lists.set_ne _ _ (Ne.symm hic),Lists.set_ne _ _ (Ne.symm hjc),F,Lists.set_same]
        · by_cases hy : x=j
          · subst x
            simp only [G,Lists.set_ne _ _ (Ne.symm hij),Lists.set_same,F,Lists.set_ne _ _ hjc,Lists.set_same]
            rw [ht,List.append_assoc]
          · by_cases hz : x=i
            · subst x
              simp only [G,Lists.set_same,F,Lists.set_ne _ _ hic,Lists.set_ne _ _ hij]
            · simp only [G,F,Lists.set_ne _ _ hx,Lists.set_ne _ _ hy,Lists.set_ne _ _ hz]
      have hG : NFits B G := by
        rw [heG]
        exact replace (hQ (m+1) (by omega)) c _ (by simpa [F] using (hQ m (by omega)).2 c)
      have hmove := move_runs i j hij (F m) (R ++ (vs.drop (m+1)).reverse) vs[m]
        (by
          simp only [F,Lists.set_ne _ _ hic,Lists.set_ne _ _ hij,Lists.set_same]
          rw [hd,List.reverse_cons]
          simp only [List.append_assoc]) (hQ m (by omega)) hG
      have heDec : (NPrim.dec c).apply G = F (m+1) := by
        rw [heG]
        simp only [NPrim.apply,Lists.set_same,mapTop_snoc,Lists.set_set_u]
        have hh : vs.length-m-1 = vs.length-(m+1) := by omega
        rw [hh]
        simp only [F,Lists.set_set_u]
      have hdec : NExec (NFits B) (.prim (.dec c)) G 1 (.cont (F (m+1))) := by
        rw [← heDec]
        exact .prim hG (by rw [heDec]; exact hQ (m+1) (by omega))
      exact hmove.seq (show FitsRuns B (.prim (.dec c)) G (F (m+1)) 1 from ⟨1,Nat.le_refl _,hdec⟩)) vs.length 0 (by omega)
  rw [h0,hn] at hrun
  simpa only [moveCount,Nat.mul_comm] using hrun
end Complexity.NBoundedTransfer
