import MacroPeg.CBV.MixedBodySyntax
import MacroPeg.CBV.MixedOriginSyntax
import MacroPeg.CBV.ContinuationGrammar

/-! Compile nested consuming bodies over both runtime shifted and ordinary
replay leaves. Generated plans and leaf addresses are computed from source
syntax; no body equivalence or row relation is supplied as an input. -/
namespace Shallot.MacroPeg.CBV.MixedBodyCompiler
open AdjacentCallsiteRecursive (Header)
open MixedAdjacentRecursive (Body)
open MixedOriginControl (Part Spec render)
open MixedBodySyntax (Expression normalize)
open ReplayControlFusion (Plan)
open ContinuationFamily (shift)
variable {H : Header}

structure User (H : Header) where
  split : Bool
  body : Expression H

def parts (users : List (User H)) : List (Part H) := users.flatMap (fun u => (normalize u.body).leaves)
def emit (offset : Nat) : List (User H) → List Spec
  | [] => []
  | u::us => ⟨u.split,shift offset (normalize u.body).plan⟩::emit (offset+(normalize u.body).leaves.length) us
def specs (users : List (User H)) := emit 0 users

def source (H : Header) (users : List (User H)) : MGrammar :=
  ⟨⟨1,.param 0⟩::users.map (fun u => ⟨1,render H (specs users) u.body.body⟩)⟩
abbrev normalized (H : Header) (users : List (User H)) := MixedOriginControl.source H (parts users) (specs users)
abbrev target (H : Header) (users : List (User H)) := MixedOriginControl.target H (parts users) (specs users)
abbrev sourceRender (H : Header) (users : List (User H)) := render H (specs users)
abbrev targetRender (H : Header) (users : List (User H)) := MixedOriginControl.targetRender H (parts users) (specs users)
/-- A finite check on generated leaf existence and callee entry kinds. -/
def Valid (H : Header) (users : List (User H)) := MixedOriginControl.Valid H (parts users) (specs users)

theorem emit_length (offset : Nat) : ∀ users : List (User H), (emit offset users).length=users.length
  | [] => rfl
  | u::us => by simp only [emit,List.length_cons,emit_length (offset+(normalize u.body).leaves.length) us]

theorem placed_leaf (H : Header) (ambient : List (Part H)) (ps : List Spec)
    (pre group post : List (Part H)) (ha : ambient=pre++group++post) (i : Nat) (hi : i<group.length) :
    MixedOriginControl.sourceLeaf H ambient ps (pre.length+i)=render H ps (MixedBodyLeaves.lookup group i) := by
  unfold MixedOriginControl.sourceLeaf MixedBodyLeaves.lookup
  have hg := List.getElem?_eq_getElem hi
  rw [ha,List.getElem?_append_left (by simp only [List.length_append]; omega : pre.length+i<(pre++group).length),
    List.getElem?_append_right (by omega : pre.length≤pre.length+i)]
  simp only [Nat.add_sub_cancel_left,hg]
  exact (MixedBodyLeaves.raw_render H ps group[i]).symm

theorem normalized_bodies (H : Header) (ambient : List (Part H)) (ps : List Spec)
    (users : List (User H)) (pre post : List (Part H)) (ha : ambient=pre++parts users++post)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table)
    (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    (emit pre.length users).map (fun z => evV g x s T E (z.plan.exp (MixedOriginControl.sourceLeaf H ambient ps)) p)=
    users.map (fun u => evV g x s T E (render H ps u.body.body) p) := by
  induction users generalizing pre with
  | nil => rfl
  | cons u us ih =>
    simp only [emit,List.map_cons]
    congr 1
    · calc
        _ = evV g x s T E (render H ps (normalize u.body).syntax) p := by
          rw [MixedBodyForm.Form.syntax,MixedBodyLeaves.control,MixedBodyLeaves.render_expand,
            Plan.exp_eval,ContinuationFamily.shift_eval,Plan.exp_eval]
          apply Plan.eval_congr
          apply Plan.all_imp _ _ (normalize u.body).bounded
          intro i hi
          exact congrArg (fun e => evV g x s T E e p)
            (placed_leaf H ambient ps pre (normalize u.body).leaves (parts us++post)
              (by simpa only [parts,List.flatMap_cons,List.append_assoc] using ha) i hi)
        _ = _ := (MixedBodySyntax.evaluator_eq H ps g x s hs T hT E u.body p hp).symm
    · have h := ih (pre++(normalize u.body).leaves)
        (by simpa only [parts,List.flatMap_cons,List.append_assoc] using ha)
      simpa only [List.length_append] using h

theorem headers (H : Header) (users : List (User H)) (i : Nat) :
    (ruleAtM (source H users).rules i).map MRule.arity=
    (ruleAtM (normalized H users).rules i).map MRule.arity := by
  have h : (source H users).rules.map MRule.arity=(normalized H users).rules.map MRule.arity := by
    simp only [source,normalized,MixedOriginControl.source,List.map_cons,List.map_map]
    congr 1
    simp only [Function.comp_def,List.map_const',specs,emit_length]
  have hi := congrArg (fun l => l[i]?) h
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using hi

theorem body_results (H : Header) (users : List (User H)) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    (source H users).rules.map (fun r => evV g x s T E r.body p)=
    (normalized H users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [source,normalized,MixedOriginControl.source,List.map_cons,List.map_map,Function.comp_def]
  congr 1
  exact (normalized_bodies H (parts users) (specs users) users [] [] (by simp) g x s hs T hT E p hp).symm

theorem tables_eq (H : Header) (users : List (User H)) (x : List Char) (s : Strategy) (hs : s≠.callByName) :
    ∀ k, tblV (source H users) x s k=tblV (normalized H users) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hh := headers H users i
    simp only [tblV]
    cases hsrc : ruleAtM (source H users).rules i with
    | none =>
      cases hn : ruleAtM (normalized H users).rules i with
      | none => rfl
      | some r => simp [hsrc,hn] at hh
    | some r =>
      cases hn : ruleAtM (normalized H users).rules i with
      | none => simp [hsrc,hn] at hh
      | some t =>
        apply List.map_congr_left
        intro p hp
        have hpn : p≤x.length := by have := List.mem_range.mp hp; omega
        rw [ih]
        have hb := congrArg (fun l => l[i]?)
          (body_results H users (normalized H users) x s hs (tblV (normalized H users) x s k)
            (tblV_sound (MixedOriginControl.source_firstOrder H (parts users) (specs users)) hs k) E p hpn)
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hsrc,hn,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (source H users) (normalized H users)
          (headers H users) x s _ E r.body p).trans hb

theorem evaluator_eq (H : Header) (users : List (User H)) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source H users) x s (tblV (source H users) x s k) E e p=
    evV (normalized H users) x s (tblV (normalized H users) x s k) E e p := by
  rw [tables_eq H users x s hs k]
  exact ContinuationGrammar.eval_headers (source H users) (normalized H users) (headers H users) x s _ E e p

theorem source_firstOrder (H : Header) (users : List (User H)) : (source H users).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    exact MixedOriginControl.render_firstOrder H _ _

theorem normalized_observations_iff (H : Header) (users : List (User H)) (e : Body H)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H users) .callByValuePar (sourceRender H users e) x r ↔
    SObs (normalized H users) .callByValuePar (sourceRender H users e) x r := by
  rw [←decideObsV_iff (source_firstOrder H users) (by decide) (MixedOriginControl.render_firstOrder H _ _),
    ←decideObsV_iff (MixedOriginControl.source_firstOrder H _ _) (by decide) (MixedOriginControl.render_firstOrder H _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source H users) (normalized H users) x .callByValuePar .callByValuePar
    (sourceRender H users e) (sourceRender H users e)
    (fun k => evaluator_eq H users x .callByValuePar (by decide) k [] _ x.length)]

theorem observations_iff (H : Header) (users : List (User H)) (hv : Valid H users) (e : Body H)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H users) .callByValuePar (sourceRender H users e) x r ↔
    SObs (target H users) .callByValueSeq (targetRender H users e) x r :=
  (normalized_observations_iff H users e x r).trans
    (MixedOriginControl.observations_iff H (parts users) (specs users) hv e x r)

theorem language_translation (H : Header) (users : List (User H)) (hv : Valid H users) (e : Body H) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source H users) .callByValuePar (sourceRender H users e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨target H users,targetRender H users e,MixedAdjacentRecursive.target_firstOrder H _,
    MixedAdjacentRecursive.render_firstOrder H _ false false _,fun x => observations_iff H users hv e x (some [])⟩

/-- Ordinary source calls with their original actual arguments, and the
original nested consuming source body before any normalization. -/
def original (H : Header) (users : List (User H)) : MGrammar :=
  ⟨⟨1,.param 0⟩::users.map (fun u => ⟨1,MixedOriginSyntax.sourceExpr u.body.body⟩)⟩

theorem source_eq_original (H : Header) (users : List (User H))
    (ht : ∀ u∈users, MixedOriginSyntax.WellTyped (specs users) u.body.body) : source H users=original H users := by
  unfold source original
  congr 2
  apply List.map_congr_left
  intro u hu
  rw [MixedOriginSyntax.source_syntax H _ _ (ht u hu)]

theorem original_language_translation (H : Header) (users : List (User H)) (hv : Valid H users)
    (ht : ∀ u∈users, MixedOriginSyntax.WellTyped (specs users) u.body.body)
    (e : Body H) (he : MixedOriginSyntax.WellTyped (specs users) e) :
    (original H users).FirstOrder ∧ (MixedOriginSyntax.sourceExpr e).FirstOrder ∧
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (original H users) .callByValuePar (MixedOriginSyntax.sourceExpr e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) := by
  rw [←source_eq_original H users ht,←MixedOriginSyntax.source_syntax H _ e he]
  exact ⟨source_firstOrder H users,MixedOriginControl.render_firstOrder H _ e,language_translation H users hv e⟩

theorem shift_all {P : Nat → Prop} (offset : Nat) : ∀ Q,
    Q.All (fun i => P (offset+i)) → (shift offset Q).All P
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => ⟨shift_all offset a h.1,shift_all offset b h.2⟩
  | .notP a, h => shift_all offset a h

def Kinds (users : List (User H)) : Prop := ∀ u∈users, u.split=false →
  ∀ r∈(normalize u.body).leaves, r.split=false ∨ r.stuck=true

theorem emit_valid (H : Header) (ambient : List (Part H)) (users : List (User H)) (hk : Kinds users)
    (pre post : List (Part H)) (ha : ambient=pre++parts users++post) :
    MixedOriginControl.Valid H ambient (emit pre.length users) := by
  induction users generalizing pre with
  | nil => simp [MixedOriginControl.Valid,emit]
  | cons u us ih =>
    intro z hz
    simp only [emit,List.mem_cons] at hz
    rcases hz with rfl | hz
    · apply shift_all
      apply Plan.all_imp _ _ (normalize u.body).bounded
      intro j hj
      refine ⟨(normalize u.body).leaves[j],?_,?_⟩
      · rw [ha,List.getElem?_append_left (by simp only [parts,List.flatMap_cons,List.length_append]; omega),
          List.getElem?_append_right (by omega : pre.length≤pre.length+j)]
        simp only [Nat.add_sub_cancel_left,parts,List.flatMap_cons,List.getElem?_append_left hj,List.getElem?_eq_getElem hj]
      · intro hs
        exact hk u (by simp) hs _ (List.getElem_mem hj)
    · have hv := ih (fun v hm => hk v (by simp [hm])) (pre++(normalize u.body).leaves)
        (by simpa only [parts,List.flatMap_cons,List.append_assoc] using ha)
      apply hv z
      simpa only [List.length_append] using hz

theorem valid_of_kinds (H : Header) (users : List (User H)) (hk : Kinds users) : Valid H users := by
  exact emit_valid H (parts users) users hk [] [] (by simp)

/-- Source-only entry-kind checking suffices, even for nullable nested stars. -/
theorem valid_of_source_kinds (H : Header) (users : List (User H))
    (hk : ∀ u∈users, u.split=false → MixedBodySyntax.Ordinary u.body) : Valid H users := by
  apply valid_of_kinds
  intro u hu hs
  exact MixedBodySyntax.normalize_ordinary u.body (hk u hu hs)

theorem embed_typed (H : Header) (ps : List Spec) : ∀ e, HelperArgument.Syntax 0 e →
    MixedOriginSyntax.WellTyped ps (MixedOriginControl.embed H e)
  | .seq a b, h | .alt a b, h => ⟨embed_typed H ps a h.1,embed_typed H ps b h.2⟩
  | .star a, h | .notP a, h => embed_typed H ps a h
  | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .call i [], h => by simp [HelperArgument.Syntax] at h
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem raw_typed (H : Header) (ps : List Spec) (r : Part H)
    (ht : MixedOriginSyntax.WellTyped ps r.body) : MixedOriginSyntax.WellTyped ps (MixedBodyLeaves.raw r) := by
  cases hd : r.stuck <;> simp only [MixedBodyLeaves.raw,hd,Bool.false_eq_true,ite_false,ite_true]
  · cases hk : r.split <;> simp only [Bool.false_eq_true,ite_false,ite_true,MixedOriginSyntax.WellTyped]
    · exact ⟨True.intro,ht⟩
    · exact ⟨⟨embed_typed H ps _ (LastCodewordGrammar.pure_syntax _ H.pure),True.intro⟩,ht⟩
  · trivial

/-- Final source-only interface: source leaf entry kinds and ordinary call
well-typedness imply unchanged-string translation, without supplying a
normal form, generated leaf layout, or semantic correspondence proof. -/
theorem source_language_translation (H : Header) (users : List (User H))
    (hk : ∀ u∈users, u.split=false → MixedBodySyntax.Ordinary u.body)
    (ht : ∀ u∈users, MixedOriginSyntax.WellTyped (specs users) u.body.body)
    (e : Body H) (he : MixedOriginSyntax.WellTyped (specs users) e) :
    (original H users).FirstOrder ∧ (MixedOriginSyntax.sourceExpr e).FirstOrder ∧
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (original H users) .callByValuePar (MixedOriginSyntax.sourceExpr e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  original_language_translation H users (valid_of_source_kinds H users hk) ht e he

end Shallot.MacroPeg.CBV.MixedBodyCompiler
