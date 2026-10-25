import MacroPeg.CBV.MultiplyingPrefixCalls
import MacroPeg.CBV.ReplayControlFusion

namespace Shallot.MacroPeg.CBV.MixedGrowthCompiler
open MultiplyingPrefixCompiler (Spec arity view modes view_word view_value firstOrder_replicate)
open ReplayControlFusion (Part Plan)
open GuardedReplayControl (Aligned)
open RepeatedWordArguments (copies expression)

inductive Entry where
  | growth : Spec → Entry
  | origin : Plan → Entry

def metadata (es : List Entry) : List Spec := es.map (fun e => match e with
  | .growth r => r
  | .origin _ => ⟨0,2,.eps,.eps⟩)
def body (parts : List Part) : Entry → MExp
  | .growth r => MultiplyingPrefixCompiler.sourceBody r
  | .origin P => P.exp (ReplayControlFusion.sourceLeaf parts)
def source (parts : List Part) (es : List Entry) : MGrammar := ⟨es.map (fun e => ⟨1,body parts e⟩)⟩
def Valid (parts : List Part) (es : List Entry) : Prop :=
  (∀ r∈parts, ReplayControlFusion.ValidPart r) ∧
  ∀ e∈es, match e with
    | .growth r => 2≤r.factor ∧ r.tail.FirstOrder ∧ r.fallback.FirstOrder ∧
        (∀ child, es[r.callee]?=some child → ∃ s, child=Entry.growth s)
    | .origin P => ReplayControlFusion.ValidPlan parts P

def offset (es : List Entry) := es.length*(es.length+1)
def leaf (parts : List Part) (es : List Entry) (a : MExp) (i : Nat) : MExp := match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.replay then .call (offset es+i) [a] else .call (offset es+i) []
def render (parts : List Part) (es : List Entry) : MExp → MExp
  | .call i [a] => match es[i]? with
    | none => MExp.failAlways
    | some (.growth _) => .call i [render parts es a]
    | some (.origin P) => .seq (.andP (render parts es a)) (P.exp (leaf parts es (render parts es a)))
  | .call _ _ => MExp.failAlways
  | .seq a b => .seq (render parts es a) (render parts es b)
  | .alt a b => .alt (render parts es a) (render parts es b)
  | .star a => .star (render parts es a)
  | .notP a => .notP (render parts es a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .param k => .param k
  | _ => MExp.failAlways

def rebound (parts : List Part) (es : List Entry) (m : Nat) (e : MExp) := MExp.subst [view m] (render parts es e)
def address (es : List Entry) (q i : Nat) := es.length*q+i
def prefixCall (es : List Entry) (i m : Nat) (r : Spec) : MExp :=
  if r.callee<es.length then .call (address es (i+1) r.callee) (List.replicate (r.factor-1) (view m)) else MExp.failAlways
def growthBody (parts : List Part) (es : List Entry) (i m : Nat) (r : Spec) : MExp :=
  .alt (.seq (prefixCall es i m r) (rebound parts es m r.tail)) (rebound parts es m r.fallback)
def block (parts : List Part) (es : List Entry) (m : Nat) : List MRule :=
  es.mapIdx (fun i e => ⟨arity m,match e with
    | .growth r => growthBody parts es i m r
    | .origin _ => MExp.failAlways⟩)
def blocks (parts : List Part) (es : List Entry) (ms : List Nat) := ms.flatMap (block parts es)
def helper (parts : List Part) (es : List Entry) (r : Part) : MRule :=
  ⟨if r.replay then 1 else 0,render parts es r.body⟩
def target (parts : List Part) (es : List Entry) : MGrammar :=
  ⟨blocks parts es (modes (metadata es))++parts.map (helper parts es)⟩
abbrev sourceTable (parts : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (source parts es) x .callByValuePar k
abbrev targetTable (parts : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (target parts es) x .callByValueSeq k

theorem leaf_firstOrder (parts : List Part) (es : List Entry) (a : MExp) (ha : a.FirstOrder) (i : Nat) :
    (leaf parts es a i).FirstOrder := by
  unfold leaf
  cases parts[i]? with
  | none => trivial
  | some r => dsimp only []; split; exact ⟨ha,True.intro⟩; trivial

theorem render_firstOrder (parts : List Part) (es : List Entry) : ∀ e, (render parts es e).FirstOrder
  | .call i [a] => by
    simp only [render]
    cases es[i]? with
    | none => trivial
    | some e => cases e with
      | growth r => exact ⟨render_firstOrder parts es a,True.intro⟩
      | origin P => exact ⟨render_firstOrder parts es a,Plan.exp_firstOrder (leaf_firstOrder parts es _ (render_firstOrder parts es a)) P⟩
  | .call _ [] | .call _ (_::_::_) => trivial
  | .seq a b | .alt a b => ⟨render_firstOrder parts es a,render_firstOrder parts es b⟩
  | .notP a | .star a => render_firstOrder parts es a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (parts : List Part) (es : List Entry) (hv : Valid parts es) : (source parts es).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  have h := hv.2 e he
  cases e with
  | origin P => exact Plan.exp_firstOrder (ReplayControlFusion.sourceLeaf_firstOrder hv.1) P
  | growth r => exact ⟨⟨⟨WordArguments.word_firstOrder _ (RepeatedWordArguments.expression_word (.param 0) True.intro _),True.intro⟩,h.2.1⟩,True.intro,h.2.2.1⟩

theorem source_rule (parts : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (source parts es).rules i=(es[i]?).map (fun e => ⟨1,body parts e⟩) := by simp [source,ruleAtM_eq_getElem?]

theorem blocks_length (parts : List Part) (es : List Entry) (ms : List Nat) :
    (blocks parts es ms).length=es.length*ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [blocks,List.flatMap_cons,List.length_append,block,List.length_mapIdx] at *; rw [ih]; simp [Nat.mul_succ,Nat.add_comm]

theorem blocks_rule (parts : List Part) (es : List Entry) (ms : List Nat) (q m i : Nat) (r : Spec)
    (hq : ms[q]?=some m) (hi : es[i]?=some (.growth r)) :
    (blocks parts es ms)[address es q i]?=some ⟨arity m,growthBody parts es i m r⟩ := by
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  induction ms generalizing q with
  | nil => simp at hq
  | cons a ms ih =>
    cases q with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hq
      subst a
      simp [blocks,address,List.getElem?_append_left,block,hib,(List.getElem?_eq_some_iff.mp hi).2]
    | succ q =>
      simp only [List.getElem?_cons_succ] at hq
      simp only [blocks,List.flatMap_cons]
      rw [List.getElem?_append_right (by simp [block,address,Nat.mul_succ]; omega)]
      have hn : address es (q+1) i-(block parts es a).length=address es q i := by simp [block,address,Nat.mul_succ]; omega
      rw [hn]
      exact ih q hq

theorem target_rule (parts : List Part) (es : List Entry) (q m i : Nat) (r : Spec)
    (hq : (modes (metadata es))[q]?=some m) (hi : es[i]?=some (.growth r)) :
    ruleAtM (target parts es).rules (address es q i)=some ⟨arity m,growthBody parts es i m r⟩ := by
  rw [target,ruleAtM_eq_getElem?,List.getElem?_append_left]
  · exact blocks_rule parts es _ q m i r hq hi
  · have hqi := (List.getElem?_eq_some_iff.mp hq).1
    have hii := (List.getElem?_eq_some_iff.mp hi).1
    rw [blocks_length]
    unfold address
    exact Nat.lt_of_lt_of_le (by simpa only [Nat.mul_succ] using Nat.add_lt_add_left hii (es.length*q))
      (Nat.mul_le_mul_left es.length hqi)

theorem helper_rule (parts : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (target parts es).rules (offset es+i)=(parts[i]?).map (helper parts es) := by
  have hl : (blocks parts es (modes (metadata es))).length=offset es := by simp [blocks_length,modes,metadata,offset]
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right,hl]

theorem origin_mode (es : List Entry) (i : Nat) (r : Spec) (hi : es[i]?=some (.growth r)) :
    (modes (metadata es))[i+1]?=some r.factor := by simp [modes,metadata,hi]

theorem mode_positive (parts : List Part) (es : List Entry) (hv : Valid parts es)
    (q m : Nat) (hq : (modes (metadata es))[q]?=some m) : 1≤m := by
  have hh := List.mem_of_getElem? hq
  rcases List.mem_cons.mp hh with hh|hh
  · omega
  · obtain ⟨r,hr,he⟩ := List.mem_map.mp hh
    obtain ⟨e,heIn,hr⟩ := List.mem_map.mp hr
    subst r
    cases e with
    | growth r => have hf := (hv.2 (.growth r) heIn).1; simp only [] at he; omega
    | origin P => simp only [] at he; omega

theorem rebound_firstOrder (parts : List Part) (es : List Entry) (m : Nat) (e : MExp) :
    (rebound parts es m e).FirstOrder :=
  firstOrder_subst (args := [view m]) ⟨WordArguments.word_firstOrder _ (view_word m),True.intro⟩ _ (render_firstOrder _ _ _)

theorem growth_firstOrder (parts : List Part) (es : List Entry) (i m : Nat) (r : Spec) :
    (growthBody parts es i m r).FirstOrder := by
  have hp : (prefixCall es i m r).FirstOrder := by
    unfold prefixCall
    split
    · exact firstOrder_replicate _ (WordArguments.word_firstOrder _ (view_word m)) _
    · trivial
  exact ⟨⟨hp,rebound_firstOrder parts es m r.tail⟩,rebound_firstOrder parts es m r.fallback⟩

theorem target_firstOrder (parts : List Part) (es : List Entry) : (target parts es).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨m,_,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
    subst r
    cases es[i] with
    | growth r => exact growth_firstOrder parts es i m r
    | origin P => trivial
  · obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
    exact render_firstOrder _ _ _

theorem rule_count (parts : List Part) (es : List Entry) :
    (target parts es).rules.length=es.length*(es.length+1)+parts.length := by
  simp [target,blocks_length,modes,metadata]

def leafRows (parts : List Part) (es : List Entry) (U : Nat → List (List Char) → Val)
    (w : List Char) (p q i : Nat) : Res := match parts[i]? with
  | none => some none
  | some r => if r.replay then valAt (U (offset es+i) [w]) q else valAt (U (offset es+i) []) p

def Rows (parts : List Part) (es : List Entry) (x : List Char) (k : Nat) : Prop :=
  (∀ i r, es[i]?=some (.growth r) → ∀ q m, (modes (metadata es))[q]?=some m → ∀ v p j,
    Aligned x (copies v m) p j → valAt (sourceTable parts es x k i [copies v m]) p=
      valAt (targetTable parts es x k (address es q i) (List.replicate (arity m) v)) j) ∧
  (∀ i P, es[i]?=some (.origin P) → ∀ w p q, Aligned x w p q →
    valAt (sourceTable parts es x k i [w]) p=P.eval (leafRows parts es (targetTable parts es x k) w p q) p)

end Shallot.MacroPeg.CBV.MixedGrowthCompiler
