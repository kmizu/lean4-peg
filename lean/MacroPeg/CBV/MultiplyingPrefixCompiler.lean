import MacroPeg.CBV.RepeatedWordArguments
import MacroPeg.CBV.GuardedReplayAlignment

namespace Shallot.MacroPeg.CBV.MultiplyingPrefixCompiler
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

structure Spec where
  callee : Nat
  factor : Nat
  tail : MExp
  fallback : MExp

def sourceBody (r : Spec) : MExp :=
  .alt (.seq (.call r.callee [expression (.param 0) r.factor]) r.tail) (.seq (.param 0) r.fallback)
def source (rs : List Spec) : MGrammar := ⟨rs.map (fun r => ⟨1,sourceBody r⟩)⟩
def Valid (rs : List Spec) : Prop := ∀ r∈rs, 2≤r.factor ∧ r.tail.FirstOrder ∧ r.fallback.FirstOrder

def render (n : Nat) : MExp → MExp
  | .call i [a] => if i<n then .call i [render n a] else MExp.failAlways
  | .call _ _ => MExp.failAlways
  | .seq a b => .seq (render n a) (render n b)
  | .alt a b => .alt (render n a) (render n b)
  | .notP a => .notP (render n a)
  | .star a => .star (render n a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .param k => .param k
  | _ => MExp.failAlways

def arity (m : Nat) := if m=1 then 1 else m-1
def view (m : Nat) := expression (.param 0) m
def modes (rs : List Spec) := 1::rs.map Spec.factor
def address (rs : List Spec) (mode i : Nat) := rs.length*mode+i
def prefixCall (rs : List Spec) (origin m : Nat) (r : Spec) : MExp :=
  if r.callee<rs.length then
    .call (address rs (origin+1) r.callee) (List.replicate (r.factor-1) (view m))
  else MExp.failAlways
def targetBody (rs : List Spec) (origin m : Nat) (r : Spec) : MExp :=
  .alt (.seq (prefixCall rs origin m r) (MExp.subst [view m] (render rs.length r.tail)))
    (MExp.subst [view m] (render rs.length r.fallback))
def block (rs : List Spec) (m : Nat) : List MRule :=
  rs.mapIdx (fun i r => ⟨arity m,targetBody rs i m r⟩)
def blocks (rs : List Spec) (ms : List Nat) := ms.flatMap (block rs)
def target (rs : List Spec) : MGrammar := ⟨blocks rs (modes rs)⟩
abbrev sourceTable (rs : List Spec) (x : List Char) (k : Nat) := tblV (source rs) x .callByValuePar k
abbrev targetTable (rs : List Spec) (x : List Char) (k : Nat) := tblV (target rs) x .callByValueSeq k

theorem arity_positive (m : Nat) (hm : 1≤m) : 0<arity m := by unfold arity; split <;> omega
theorem mode_positive (rs : List Spec) (hv : Valid rs) (q m : Nat) (h : (modes rs)[q]?=some m) : 1≤m := by
  have hh := List.mem_of_getElem? h
  rcases List.mem_cons.mp hh with hh|hh
  · omega
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp hh
    have := (hv r hr).1
    omega
theorem view_word (m : Nat) : WordArguments.Word (view m) := RepeatedWordArguments.expression_word (.param 0) True.intro m
theorem view_value (m : Nat) (hm : 1≤m) (v : List Char) :
    WordArguments.value (List.replicate (arity m) v) (view m)=some (copies v m) := by
  apply RepeatedWordArguments.expression_value
  simp only [WordArguments.value]
  exact List.getElem?_replicate_of_lt (arity_positive m hm)

theorem render_firstOrder (n : Nat) : ∀ e, (render n e).FirstOrder
  | .call i [a] => by
    simp only [render]
    split
    · exact ⟨render_firstOrder n a,True.intro⟩
    · trivial
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder n a,render_firstOrder n b⟩
  | .star a | .notP a => render_firstOrder n a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem firstOrder_replicate (a : MExp) (ha : a.FirstOrder) (n : Nat) :
    MExp.FirstOrderArgs (List.replicate n a) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ha,ih⟩
theorem source_firstOrder (rs : List Spec) (hv : Valid rs) : (source rs).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨⟨WordArguments.word_firstOrder _ (RepeatedWordArguments.expression_word (.param 0) True.intro s.factor),True.intro⟩,
    (hv s hs).2.1⟩,True.intro,(hv s hs).2.2⟩
theorem target_firstOrder (rs : List Spec) : (target rs).FirstOrder := by
  have hb (origin m : Nat) (r : Spec) : (targetBody rs origin m r).FirstOrder := by
    have hview := WordArguments.word_firstOrder _ (view_word m)
    have hp : (prefixCall rs origin m r).FirstOrder := by
      unfold prefixCall
      split
      · exact firstOrder_replicate _ hview _
      · trivial
    exact ⟨⟨hp,firstOrder_subst (args := [view m]) ⟨hview,True.intro⟩ _ (render_firstOrder _ _)⟩,
      firstOrder_subst (args := [view m]) ⟨hview,True.intro⟩ _ (render_firstOrder _ _)⟩
  intro r hr
  obtain ⟨m,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
  subst r
  exact hb i m _

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
    ruleAtM (source rs).rules i=(rs[i]?).map (fun r => ⟨1,sourceBody r⟩) := by simp [source,ruleAtM_eq_getElem?]
theorem target_rule (rs : List Spec) (q m i : Nat) (r : Spec)
    (hq : (modes rs)[q]?=some m) (hi : rs[i]?=some r) :
    ruleAtM (target rs).rules (address rs q i)=some ⟨arity m,targetBody rs i m r⟩ :=
  by simpa only [target,address,ruleAtM_eq_getElem?] using blocks_rule rs (modes rs) q m i r hq hi
theorem origin_mode (rs : List Spec) (i : Nat) (r : Spec) (hi : rs[i]?=some r) :
    (modes rs)[i+1]?=some r.factor := by simp [modes,hi]

def Rows (rs : List Spec) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ q m, (modes rs)[q]?=some m → ∀ v p j,
    Aligned x (copies v m) p j →
    valAt (sourceTable rs x k i [copies v m]) p=
      valAt (targetTable rs x k (address rs q i) (List.replicate (arity m) v)) j

end Shallot.MacroPeg.CBV.MultiplyingPrefixCompiler
