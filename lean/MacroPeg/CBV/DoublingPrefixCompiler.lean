import MacroPeg.CBV.WordCallUnfolding
import MacroPeg.CBV.GuardedReplayAlignment

namespace Shallot.MacroPeg.CBV.DoublingPrefixCompiler
open GuardedReplayControl (Aligned)

/-- A real call with a doubled value precedes the first whole replay.
Both continuations may contain arbitrary first-order recursive calls. -/
structure Spec where
  callee : Nat
  tail : MExp
  fallback : MExp

def sourceBody (r : Spec) : MExp :=
  .alt (.seq (.call r.callee [.seq (.param 0) (.param 0)]) r.tail) (.seq (.param 0) r.fallback)
def source (rs : List Spec) : MGrammar := ⟨rs.map (fun r => ⟨1,sourceBody r⟩)⟩
def Valid (rs : List Spec) : Prop := ∀ r∈rs, r.tail.FirstOrder ∧ r.fallback.FirstOrder

def render (rs : List Spec) : MExp → MExp
  | .call i [a] => if i<rs.length then .call i [render rs a] else MExp.failAlways
  | .call _ _ => MExp.failAlways
  | .seq a b => .seq (render rs a) (render rs b)
  | .alt a b => .alt (render rs a) (render rs b)
  | .notP a => .notP (render rs a)
  | .star a => .star (render rs a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .param k => .param k
  | _ => MExp.failAlways

def view (half : Bool) : MExp := if half then .seq (.param 0) (.param 0) else .param 0
def word (half : Bool) (v : List Char) : List Char := if half then v++v else v
def address (rs : List Spec) (half : Bool) (i : Nat) := if half then rs.length+i else i
def targetBody (rs : List Spec) (half : Bool) (r : Spec) : MExp :=
  .alt (.seq (.call (address rs true r.callee) [view half]) (MExp.subst [view half] (render rs r.tail)))
    (MExp.subst [view half] (render rs r.fallback))
def target (rs : List Spec) : MGrammar :=
  ⟨rs.map (fun r => ⟨1,targetBody rs false r⟩) ++ rs.map (fun r => ⟨1,targetBody rs true r⟩)⟩
abbrev sourceTable (rs : List Spec) (x : List Char) (k : Nat) := tblV (source rs) x .callByValuePar k
abbrev targetTable (rs : List Spec) (x : List Char) (k : Nat) := tblV (target rs) x .callByValueSeq k

theorem view_word (half : Bool) : WordArguments.Word (view half) := by cases half <;> trivial
theorem view_value (half : Bool) (v : List Char) : WordArguments.value [v] (view half)=some (word half v) := by
  cases half <;> simp [view,word,WordArguments.value]
theorem view_firstOrder (half : Bool) : (view half).FirstOrder := WordArguments.word_firstOrder _ (view_word half)

theorem render_firstOrder (rs : List Spec) : ∀ e, (render rs e).FirstOrder
  | .call i [a] => by
    simp only [render]
    split
    · exact ⟨render_firstOrder rs a,True.intro⟩
    · trivial
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder rs a,render_firstOrder rs b⟩
  | .star a | .notP a => render_firstOrder rs a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (rs : List Spec) (hv : Valid rs) : (source rs).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨⟨⟨True.intro,True.intro⟩,True.intro⟩,(hv s hs).1⟩,True.intro,(hv s hs).2⟩

theorem target_firstOrder (rs : List Spec) : (target rs).FirstOrder := by
  have hb (half : Bool) (r : Spec) : (targetBody rs half r).FirstOrder :=
    ⟨⟨⟨view_firstOrder half,True.intro⟩,
      firstOrder_subst (args := [view half]) ⟨view_firstOrder half,True.intro⟩ _ (render_firstOrder rs r.tail)⟩,
      firstOrder_subst (args := [view half]) ⟨view_firstOrder half,True.intro⟩ _ (render_firstOrder rs r.fallback)⟩
  intro r hr
  rcases List.mem_append.mp hr with hr|hr <;>
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hr
  · exact hb false s
  · exact hb true s

theorem rule_count (rs : List Spec) : (source rs).rules.length=rs.length ∧ (target rs).rules.length=2*rs.length := by
  simp [source,target]; omega

theorem source_rule (rs : List Spec) (i : Nat) :
    ruleAtM (source rs).rules i=(rs[i]?).map (fun r => ⟨1,sourceBody r⟩) := by
  simp [source,ruleAtM_eq_getElem?]

theorem target_rule (rs : List Spec) (half : Bool) (i : Nat) (r : Spec) (hi : rs[i]?=some r) :
    ruleAtM (target rs).rules (address rs half i)=some ⟨1,targetBody rs half r⟩ := by
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  have hir := (List.getElem?_eq_some_iff.mp hi).2
  cases half <;> simp [target,address,ruleAtM_eq_getElem?,List.getElem?_append_left,
    List.getElem?_append_right,List.length_map,hib,hi,hir]

theorem target_missing (rs : List Spec) (i : Nat) (hi : rs[i]?=none) :
    ruleAtM (target rs).rules (address rs true i)=none := by
  simp only [target,address,if_true,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp only [List.length_map]; omega)]
  simp only [List.length_map,Nat.add_sub_cancel_left,List.getElem?_map,hi,Option.map_none]

def Rows (rs : List Spec) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ half v p j, Aligned x (word half v) p j →
    valAt (sourceTable rs x k i [word half v]) p=
      valAt (targetTable rs x k (address rs half i) [v]) j

end Shallot.MacroPeg.CBV.DoublingPrefixCompiler
