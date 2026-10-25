import MacroPeg.CBV.MixedGrowthChecks
import MacroPeg.CBV.SelectedForwardingNormalization

namespace Shallot.MacroPeg.CBV.MixedForwardingCompiler
open MultiplyingPrefixCompiler (Spec arity view modes view_word view_value firstOrder_replicate)
open ReplayControlFusion (Part Plan)
open GuardedReplayControl (Aligned)
open RepeatedWordArguments (copies expression)

export MixedGrowthCompiler (Entry metadata body offset leaf render rebound address prefixCall growthBody helper leafRows render_firstOrder rebound_firstOrder growth_firstOrder)
abbrev original := MixedGrowthCompiler.source

def Valid (parts : List Part) (es : List Entry) : Prop :=
  (∀ r∈parts, ReplayControlFusion.ValidPart r) ∧
  ∀ e∈es, match e with
    | .growth r => 1≤r.factor ∧ r.tail.FirstOrder ∧ r.fallback.FirstOrder ∧
        (∀ child, es[r.callee]?=some child → ∃ s, child=MixedGrowthCompiler.Entry.growth s)
    | .origin P => ReplayControlFusion.ValidPlan parts P

def selected (es : List Entry) := (List.range es.length).filter (fun i => match es[i]? with
  | some (.growth _) => true | _ => false)
def source (parts : List Part) (es : List Entry) :=
  SelectedForwardingNormalization.normalized (original parts es) (metadata es) (selected es)

def code (parts : List Part) (es : List Entry) : Nat → Nat → List Nat → Nat → MExp
  | 0,_,_,_ => MExp.failAlways
  | fuel+1,i,seen,m =>
    if i∈seen then .star (.lit []) else
    match (metadata es)[i]? with
    | none => MExp.failAlways
    | some r =>
      if r.factor=1 then
        match (metadata es)[r.callee]? with
        | none => rebound parts es m r.fallback
        | some _ => .alt (.seq (code parts es fuel r.callee (i::seen) m) (rebound parts es m r.tail)) (rebound parts es m r.fallback)
      else growthBody parts es i m r

def targetBody (parts : List Part) (es : List Entry) (i m : Nat) (_r : Spec) := code parts es (es.length+1) i [] m

def block (parts : List Part) (es : List Entry) (m : Nat) : List MRule :=
  es.mapIdx (fun i e => ⟨arity m,match e with
    | .growth r => targetBody parts es i m r
    | .origin _ => MExp.failAlways⟩)
def blocks (parts : List Part) (es : List Entry) (ms : List Nat) := ms.flatMap (block parts es)
def target (parts : List Part) (es : List Entry) : MGrammar :=
  ⟨blocks parts es (modes (metadata es))++parts.map (helper parts es)⟩
abbrev sourceTable (parts : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (source parts es) x .callByValuePar k
abbrev targetTable (parts : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (target parts es) x .callByValueSeq k

theorem selected_iff (es : List Entry) (i : Nat) : i∈selected es ↔ ∃ r, es[i]?=some (.growth r) := by
  constructor
  · intro h
    have hh := (List.mem_filter.mp h).2
    cases he : es[i]? with
    | none => simp [he] at hh
    | some e => cases e with
      | growth r => exact ⟨r,rfl⟩
      | origin P => simp [he] at hh
  · rintro ⟨r,hr⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr (List.getElem?_eq_some_iff.mp hr).1,by simp [hr]⟩

theorem original_rule (parts : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (original parts es).rules i=(es[i]?).map (fun e => ⟨1,body parts e⟩) := MixedGrowthCompiler.source_rule parts es i

theorem selected_valid (parts : List Part) (es : List Entry) (hv : Valid parts es) :
    SelectedForwardingContext.Valid (original parts es) (metadata es) (selected es) := by
  refine ⟨by simp [original,MixedGrowthCompiler.source,metadata,MixedGrowthCompiler.metadata],?_,?_⟩
  · intro i hi r hr
    obtain ⟨s,hs⟩ := (selected_iff es i).mp hi
    have he : s=r := by simpa [metadata,MixedGrowthCompiler.metadata,hs] using hr
    subst s
    rw [original_rule,hs]; rfl
  · intro i hi r hr hf child hc
    obtain ⟨s,hs⟩ := (selected_iff es i).mp hi
    have he : s=r := by simpa [metadata,MixedGrowthCompiler.metadata,hs] using hr
    subst s
    cases hn : es[r.callee]? with
    | none => simp [metadata,MixedGrowthCompiler.metadata,hn] at hc
    | some e =>
      obtain ⟨s,rfl⟩ := (hv.2 (.growth r) (List.mem_of_getElem? hs)).2.2.2 e hn
      exact (selected_iff es r.callee).mpr ⟨s,hn⟩

theorem source_rule (parts : List Part) (es : List Entry) (i : Nat) :
    ruleAtM (source parts es).rules i=(es[i]?).map (fun e => ⟨1,match e with
      | .growth _ => ForwardingHeadExpansion.expanded (metadata es) i
      | .origin P => P.exp (ReplayControlFusion.sourceLeaf parts)⟩) := by
  rw [source,SelectedForwardingNormalization.rule,original_rule]
  cases he : es[i]? with
  | none => rfl
  | some e =>
    cases e with
    | growth r => simp [SelectedForwardingNormalization.body,(selected_iff es i).mpr ⟨r,he⟩]
    | origin P =>
      have hn : i∉selected es := by rw [selected_iff]; simp [he]
      simp [SelectedForwardingNormalization.body,hn,body,MixedGrowthCompiler.body]

theorem original_firstOrder (parts : List Part) (es : List Entry) (hv : Valid parts es) : (original parts es).FirstOrder := by
  intro r hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  have h := hv.2 e he
  cases e with
  | origin P => exact Plan.exp_firstOrder (ReplayControlFusion.sourceLeaf_firstOrder hv.1) P
  | growth r => exact ⟨⟨⟨WordArguments.word_firstOrder _ (RepeatedWordArguments.expression_word (.param 0) True.intro _),True.intro⟩,h.2.1⟩,True.intro,h.2.2.1⟩


theorem source_firstOrder (parts : List Part) (es : List Entry) (hv : Valid parts es) : (source parts es).FirstOrder :=
  SelectedForwardingNormalization.firstOrder _ (original_firstOrder parts es hv) _ _ (selected_valid parts es hv)

theorem metadata_firstOrder (parts : List Part) (es : List Entry) (hv : Valid parts es) :
    (MultiplyingPrefixCompiler.source (metadata es)).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
  have hh := hv.2 e he
  cases e with
  | origin P => trivial
  | growth r => exact ⟨⟨⟨WordArguments.word_firstOrder _ (RepeatedWordArguments.expression_word (.param 0) True.intro _),True.intro⟩,hh.2.1⟩,True.intro,hh.2.2.1⟩

theorem blocks_length (parts : List Part) (es : List Entry) (ms : List Nat) :
    (blocks parts es ms).length=es.length*ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [blocks,List.flatMap_cons,List.length_append,block,List.length_mapIdx] at *; rw [ih]; simp [Nat.mul_succ,Nat.add_comm]

theorem blocks_rule (parts : List Part) (es : List Entry) (ms : List Nat) (q m i : Nat) (r : Spec)
    (hq : ms[q]?=some m) (hi : es[i]?=some (.growth r)) :
    (blocks parts es ms)[address es q i]?=some ⟨arity m,targetBody parts es i m r⟩ := by
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
    ruleAtM (target parts es).rules (address es q i)=some ⟨arity m,targetBody parts es i m r⟩ := by
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

theorem code_firstOrder (parts : List Part) (es : List Entry) (fuel i : Nat) (seen : List Nat) (m : Nat) :
    (code parts es fuel i seen m).FirstOrder := by
  induction fuel generalizing i seen with
  | zero => trivial
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp only [code,if_pos hi]; trivial
    · cases hr : (metadata es)[i]? with
      | none => simp only [code,if_neg hi,hr]; trivial
      | some r =>
        by_cases hf : r.factor=1
        · cases hc : (metadata es)[r.callee]? with
          | none => simpa only [code,if_neg hi,hr,if_pos hf,hc] using rebound_firstOrder parts es m r.fallback
          | some child =>
            simp only [code,if_neg hi,hr,if_pos hf,hc]
            exact ⟨⟨ih _ _,rebound_firstOrder _ _ _ _⟩,rebound_firstOrder _ _ _ _⟩
        · simpa only [code,if_neg hi,hr,if_neg hf] using growth_firstOrder parts es i m r

theorem target_firstOrder (parts : List Part) (es : List Entry) : (target parts es).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨m,_,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hr
    subst r
    cases es[i] with
    | growth r => exact code_firstOrder parts es (es.length+1) i [] m
    | origin P => trivial
  · obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
    exact render_firstOrder _ _ _

theorem rule_count (parts : List Part) (es : List Entry) :
    (target parts es).rules.length=es.length*(es.length+1)+parts.length := by
  simp [target,blocks_length,modes,metadata]

def Rows (parts : List Part) (es : List Entry) (x : List Char) (k : Nat) : Prop :=
  (∀ i r, es[i]?=some (.growth r) → ∀ q m, (modes (metadata es))[q]?=some m → ∀ v p j,
    Aligned x (copies v m) p j → valAt (sourceTable parts es x k i [copies v m]) p=
      valAt (targetTable parts es x k (address es q i) (List.replicate (arity m) v)) j) ∧
  (∀ i P, es[i]?=some (.origin P) → ∀ w p q, Aligned x w p q →
    valAt (sourceTable parts es x k i [w]) p=P.eval (leafRows parts es (targetTable parts es x k) w p q) p)


end Shallot.MacroPeg.CBV.MixedForwardingCompiler
