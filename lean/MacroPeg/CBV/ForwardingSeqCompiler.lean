import MacroPeg.CBV.ForwardingHeadNormalization

namespace Shallot.MacroPeg.CBV.ForwardingSeqCompiler
open MultiplyingPrefixCompiler (Spec arity view modes address render prefixCall origin_mode
  arity_positive view_word view_value render_firstOrder firstOrder_replicate)
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

def Valid (rs : List Spec) : Prop := ∀ r∈rs, 1≤r.factor ∧ r.tail.FirstOrder ∧ r.fallback.FirstOrder
abbrev source (rs : List Spec) := ForwardingHeadNormalization.normalized rs

def rebound (rs : List Spec) (m : Nat) (e : MExp) := MExp.subst [view m] (render rs.length e)
def code (rs : List Spec) : Nat → Nat → List Nat → Nat → MExp
  | 0,_,_,_ => MExp.failAlways
  | fuel+1,i,seen,m =>
    if i∈seen then .star (.lit []) else
    match rs[i]? with
    | none => MExp.failAlways
    | some r =>
      if r.factor=1 then
        match rs[r.callee]? with
        | none => rebound rs m r.fallback
        | some _ => .alt (.seq (code rs fuel r.callee (i::seen) m) (rebound rs m r.tail)) (rebound rs m r.fallback)
      else MultiplyingPrefixCompiler.targetBody rs i m r

def targetBody (rs : List Spec) (i m : Nat) (_r : Spec) := code rs (rs.length+1) i [] m
def block (rs : List Spec) (m : Nat) : List MRule := rs.mapIdx (fun i r => ⟨arity m,targetBody rs i m r⟩)
def blocks (rs : List Spec) (ms : List Nat) := ms.flatMap (block rs)
def target (rs : List Spec) : MGrammar := ⟨blocks rs (modes rs)⟩
abbrev sourceTable (rs : List Spec) (x : List Char) (k : Nat) := tblV (source rs) x .callByValuePar k
abbrev targetTable (rs : List Spec) (x : List Char) (k : Nat) := tblV (target rs) x .callByValueSeq k

theorem raw_firstOrder (rs : List Spec) (hv : Valid rs) : (MultiplyingPrefixCompiler.source rs).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨⟨WordArguments.word_firstOrder _ (RepeatedWordArguments.expression_word (.param 0) True.intro s.factor),True.intro⟩,
    (hv s hs).2.1⟩,True.intro,(hv s hs).2.2⟩
theorem source_firstOrder (rs : List Spec) (hv : Valid rs) : (source rs).FirstOrder :=
  ForwardingHeadNormalization.firstOrder rs (raw_firstOrder rs hv)
theorem mode_positive (rs : List Spec) (hv : Valid rs) (q m : Nat) (h : (modes rs)[q]?=some m) : 1≤m := by
  have hh := List.mem_of_getElem? h
  rcases List.mem_cons.mp hh with hh|hh
  · omega
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp hh
    have := (hv r hr).1
    omega

theorem rebound_firstOrder (rs : List Spec) (m : Nat) (e : MExp) : (rebound rs m e).FirstOrder :=
  firstOrder_subst (args := [view m]) ⟨WordArguments.word_firstOrder _ (view_word m),True.intro⟩ _ (render_firstOrder _ _)
theorem leaf_firstOrder (rs : List Spec) (i m : Nat) (r : Spec) :
    (MultiplyingPrefixCompiler.targetBody rs i m r).FirstOrder := by
  have hview := WordArguments.word_firstOrder _ (view_word m)
  have hp : (prefixCall rs i m r).FirstOrder := by
    unfold prefixCall
    split
    · exact firstOrder_replicate _ hview _
    · trivial
  exact ⟨⟨hp,rebound_firstOrder rs m r.tail⟩,rebound_firstOrder rs m r.fallback⟩
theorem code_firstOrder (rs : List Spec) (fuel i : Nat) (seen : List Nat) (m : Nat) : (code rs fuel i seen m).FirstOrder := by
  induction fuel generalizing i seen with
  | zero => trivial
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp only [code,if_pos hi]; trivial
    · cases hr : rs[i]? with
      | none => simp only [code,if_neg hi,hr]; trivial
      | some r =>
        by_cases hf : r.factor=1
        · cases hc : rs[r.callee]? with
          | none => simpa only [code,if_neg hi,hr,if_pos hf,hc] using rebound_firstOrder rs m r.fallback
          | some child =>
            simp only [code,if_neg hi,hr,if_pos hf,hc]
            exact ⟨⟨ih _ _,rebound_firstOrder _ _ _⟩,rebound_firstOrder _ _ _⟩
        · simpa only [code,if_neg hi,hr,if_neg hf] using leaf_firstOrder rs i m r
theorem target_firstOrder (rs : List Spec) : (target rs).FirstOrder := by
  intro r hr
  obtain ⟨m,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
  subst r
  exact code_firstOrder rs (rs.length+1) i [] m

theorem block_length (rs : List Spec) (m : Nat) : (block rs m).length=rs.length := by simp [block]
theorem blocks_length (rs : List Spec) (ms : List Nat) : (blocks rs ms).length=rs.length*ms.length := by
  induction ms with
  | nil => simp [blocks]
  | cons m ms ih => simp only [blocks,List.flatMap_cons,List.length_append,block_length] at *; simp_all [Nat.mul_succ,Nat.add_comm]
theorem rule_count (rs : List Spec) : (target rs).rules.length=rs.length*(rs.length+1) := by
  simp only [target,blocks_length,modes,List.length_cons,List.length_map]

theorem blocks_rule (rs : List Spec) (ms : List Nat) (q m i : Nat) (r : Spec)
    (hq : ms[q]?=some m) (hi : rs[i]?=some r) :
    (blocks rs ms)[rs.length*q+i]?=some ⟨arity m,targetBody rs i m r⟩ := by
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  induction ms generalizing q with
  | nil => simp at hq
  | cons a ms ih =>
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hq
      subst a
      simp [blocks,List.getElem?_append_left,block,hib,(List.getElem?_eq_some_iff.mp hi).2]
    | succ q =>
      simp only [List.getElem?_cons_succ] at hq
      simp only [blocks,List.flatMap_cons]
      rw [List.getElem?_append_right (by rw [block_length,Nat.mul_succ]; omega),block_length]
      have hn : rs.length*(q+1)+i-rs.length=rs.length*q+i := by rw [Nat.mul_succ]; omega
      rw [hn]
      exact ih q hq

theorem source_rule (rs : List Spec) (i : Nat) :
    ruleAtM (source rs).rules i=(rs[i]?).map (fun _ => ⟨1,ForwardingHeadExpansion.expanded rs i⟩) := ForwardingHeadNormalization.rule rs i
theorem target_rule (rs : List Spec) (q m i : Nat) (r : Spec)
    (hq : (modes rs)[q]?=some m) (hi : rs[i]?=some r) :
    ruleAtM (target rs).rules (address rs q i)=some ⟨arity m,targetBody rs i m r⟩ :=
  by simpa only [target,address,ruleAtM_eq_getElem?] using blocks_rule rs (modes rs) q m i r hq hi

def Rows (rs : List Spec) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ q m, (modes rs)[q]?=some m → ∀ v p j,
    Aligned x (copies v m) p j →
    valAt (sourceTable rs x k i [copies v m]) p=
      valAt (targetTable rs x k (address rs q i) (List.replicate (arity m) v)) j

end Shallot.MacroPeg.CBV.ForwardingSeqCompiler
